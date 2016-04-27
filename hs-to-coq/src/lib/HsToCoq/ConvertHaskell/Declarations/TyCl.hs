{-# LANGUAGE RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.TyCl (
  convertTyClDecls,
  -- * Convert single declarations
  ConvertedDeclaration(..), convDeclName,
  convertTyClDecl,
  -- * Mutually-recursive declaration groups
  DeclarationGroup(..), singletonDeclarationGroup,
  -- * Converting 'DeclarationGroup's
  convertDeclarationGroup, groupTyClDecls
  ) where

import Data.Semigroup (Semigroup(..))
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

import Control.Arrow ((&&&))
import Control.Monad

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name)

import HsToCoq.Util.Functor
import HsToCoq.Util.Containers
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import Data.Generics hiding (Fixity(..))

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Declarations.TypeSynonym
import HsToCoq.ConvertHaskell.Declarations.DataType
import HsToCoq.ConvertHaskell.Declarations.Class

--------------------------------------------------------------------------------

data ConvertedDeclaration = ConvData  IndBody
                          | ConvSyn   SynBody
                          | ConvClass ClassBody
                          deriving (Eq, Ord, Show, Read)

instance FreeVars ConvertedDeclaration where
  freeVars (ConvData  ind) = freeVars ind
  freeVars (ConvSyn   syn) = freeVars syn
  freeVars (ConvClass cls) = freeVars cls

convDeclName :: ConvertedDeclaration -> Ident
convDeclName (ConvData  (IndBody                    tyName  _ _ _))    = tyName
convDeclName (ConvSyn   (SynBody                    synName _ _ _))    = synName
convDeclName (ConvClass (ClassBody (ClassDefinition clsName _ _ _) _)) = clsName

convertTyClDecl :: ConversionMonad m => TyClDecl RdrName -> m ConvertedDeclaration
convertTyClDecl FamDecl{}     = convUnsupported "type/data families"
convertTyClDecl SynDecl{..}   = ConvSyn   <$> convertSynDecl   tcdLName tcdTyVars tcdRhs
convertTyClDecl DataDecl{..}  = ConvData  <$> convertDataDecl  tcdLName tcdTyVars tcdDataDefn
convertTyClDecl ClassDecl{..} = ConvClass <$> convertClassDecl tcdCtxt  tcdLName  tcdTyVars   tcdFDs tcdSigs tcdMeths tcdATs tcdATDefs

--------------------------------------------------------------------------------

data DeclarationGroup = DeclarationGroup { dgInductives :: [IndBody]
                                         , dgSynonyms   :: [SynBody]
                                         , dgClasses    :: [ClassBody] }
                      deriving (Eq, Ord, Show, Read)

instance Semigroup DeclarationGroup where
  DeclarationGroup ind1 syn1 cls1 <> DeclarationGroup ind2 syn2 cls2 = DeclarationGroup (ind1 <> ind2) (syn1 <> syn2) (cls1 <> cls2)

instance Monoid DeclarationGroup where
  mempty  = DeclarationGroup [] [] []
  mappend = (<>)

singletonDeclarationGroup :: ConvertedDeclaration -> DeclarationGroup
singletonDeclarationGroup (ConvData  ind) = DeclarationGroup [ind] []    []
singletonDeclarationGroup (ConvSyn   syn) = DeclarationGroup []    [syn] []
singletonDeclarationGroup (ConvClass cls) = DeclarationGroup []    []    [cls]

--------------------------------------------------------------------------------

convertDeclarationGroup :: DeclarationGroup -> Either String [Sentence]
convertDeclarationGroup DeclarationGroup{..} = case (nonEmpty dgInductives, nonEmpty dgSynonyms, nonEmpty dgClasses) of
  (Just inds, Nothing, Nothing) ->
    Right [InductiveSentence $ Inductive inds []]
  
  (Nothing, Just (SynBody name args oty def :| []), Nothing) ->
    Right [DefinitionSentence $ DefinitionDef Global name args oty def]
  
  (Just inds, Just syns, Nothing) ->
    Right $  foldMap recSynType syns
          ++ [InductiveSentence $ Inductive inds (map (recSynDef $ foldMap indParams inds) $ toList syns)]

  (Nothing, Nothing, Just (ClassBody cdef nots :| [])) ->
    Right $ ClassSentence cdef : map NotationSentence nots
  
  (Nothing, Just (_ :| _ : _), Nothing)           -> Left "mutually-recursive type synonyms"
  (Nothing, Nothing,           Just (_ :| _ : _)) -> Left "mutually-recursive type classes"
  (Just _,  Nothing,           Just _)            -> Left "mutually-recursive type classes and data types"
  (Nothing, Just _,            Just _)            -> Left "mutually-recursive type classes and type synonyms"
  (Just _,  Just _,            Just _)            -> Left "mutually-recursive type classes, data types, and type synonyms"
  (Nothing, Nothing,           Nothing)           -> Left "[internal] invalid empty declaration group"
  
  (Nothing, Just (_ :| _),     Nothing)           -> error "GHC BUG WORKAROUND: `OverloadedLists` confuses the exhaustiveness checker"
  (Nothing, Nothing,           Just (_  :| _))    -> error "GHC BUG WORKAROUND: `OverloadedLists` confuses the exhaustiveness checker"
  
  where
    synName = (<> "__raw")
    
    recSynType :: SynBody -> [Sentence] -- Otherwise GHC infers a type containing @~@.
    recSynType (SynBody name _ _ _) =
      [ InductiveSentence $ Inductive [IndBody (synName name) [] (Sort Type) []] []
      , NotationSentence $ ReservedNotationIdent name ]
    
    indParams (IndBody _ params _ _) = S.fromList $ foldMap binderIdents params

    avoidParams params = until (`S.notMember` params) (<> "_")
    
    recSynDef params (SynBody name args oty def) =
      let mkFun    = maybe id Fun . nonEmpty
          withType = maybe id (flip HasType)
      in NotationIdentBinding name . App (Var "Synonym")
                                   $ fmap PosArg [ Var (synName name)
                                                 , everywhere (mkT $ avoidParams params) . -- FIXME use real substitution
                                                     mkFun args $ withType oty def ]

--------------------------------------------------------------------------------

groupTyClDecls :: ConversionMonad m => [TyClDecl RdrName] -> m [DeclarationGroup]
groupTyClDecls decls = do
  bodies <- traverse convertTyClDecl decls <&>
              M.fromList . map (convDeclName &&& id)
  -- The order is correct – later declarations refer only to previous ones –
  -- since 'stronglyConnComp'' returns its outputs in topologically sorted
  -- order.
  let mutuals = stronglyConnComp' . M.toList $ (S.toList . getFreeVars) <$> bodies
  pure $ map (foldMap $ singletonDeclarationGroup . (bodies M.!)) mutuals

convertTyClDecls :: ConversionMonad m => [TyClDecl RdrName] -> m [Sentence]
convertTyClDecls =   either convUnsupported (pure . fold)
                 .   traverse convertDeclarationGroup
                 <=< groupTyClDecls
