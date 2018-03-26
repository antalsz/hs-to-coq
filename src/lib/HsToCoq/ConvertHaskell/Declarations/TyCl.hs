{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts, ScopedTypeVariables #-}

module HsToCoq.ConvertHaskell.Declarations.TyCl (
  convertTyClDecls, convertModuleTyClDecls,
  -- * Convert single declarations
  ConvertedDeclaration(..), convDeclName,
  convertTyClDecl,
  -- * Mutually-recursive declaration groups
  DeclarationGroup(..), singletonDeclarationGroup,
  -- * Converting 'DeclarationGroup's
  convertDeclarationGroup, groupTyClDecls,
  -- * Argument specifiers
  generateArgumentSpecifiers, generateGroupArgumentSpecifiers,
  -- * Record accessors
  generateRecordAccessors, generateGroupRecordAccessors
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Bifunctor
import Data.Foldable
import Data.Traversable
import HsToCoq.Util.Traversable
import HsToCoq.Util.Function
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

import Control.Arrow ((&&&))
import Control.Monad

import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import HsToCoq.Util.Containers

import GHC hiding (Name, HsString)
import qualified GHC

import HsToCoq.Coq.Gallina      as Coq
import HsToCoq.Coq.Gallina.Util as Coq
import HsToCoq.Coq.FreeVars

import Data.Generics hiding (Fixity(..))

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Axiomatize
import HsToCoq.ConvertHaskell.Declarations.TypeSynonym
import HsToCoq.ConvertHaskell.Declarations.DataType
import HsToCoq.ConvertHaskell.Declarations.Class

import Exception

--------------------------------------------------------------------------------

data ConvertedDeclaration = ConvData  Bool IndBody
                          | ConvSyn   SynBody
                          | ConvClass ClassBody
                          | ConvFailure Qualid Sentence
                          deriving (Eq, Ord, Show, Read)

instance FreeVars ConvertedDeclaration where
  freeVars (ConvData  _ ind)   = freeVars ind
  freeVars (ConvSyn     syn)   = freeVars syn
  freeVars (ConvClass   cls)   = freeVars cls
  freeVars (ConvFailure _ sen) = freeVars (NoBinding sen)

convDeclName :: ConvertedDeclaration -> Qualid
convDeclName (ConvData _ (IndBody                    tyName  _ _ _))    = tyName
convDeclName (ConvSyn    (SynBody                    synName _ _ _))    = synName
convDeclName (ConvClass  (ClassBody (ClassDefinition clsName _ _ _) _)) = clsName
convDeclName (ConvFailure n _)                                         = n

failTyClDecl :: ConversionMonad m => Qualid -> GhcException -> m (Maybe ConvertedDeclaration)
failTyClDecl name e = pure $ Just $
    ConvFailure name $ translationFailedComment (qualidBase name) e

convertTyClDecl :: ConversionMonad m => TyClDecl GHC.Name -> m (Maybe ConvertedDeclaration)
convertTyClDecl decl = do
  coqName <- var TypeNS . unLoc $ tyClDeclLName decl
  let isCoind = use (edits.coinductiveTypes.contains coqName)
  ghandle (failTyClDecl coqName) $ do
    use (edits.skipped.contains coqName) >>= \case
      True  -> pure Nothing
      False -> use (edits.redefinitions.at coqName) >>= fmap Just . \case
        Nothing -> case decl of
          FamDecl{}     -> convUnsupported "type/data families"
          SynDecl{..}   -> ConvSyn              <$> convertSynDecl   tcdLName (hsq_explicit tcdTyVars) tcdRhs
          DataDecl{..}  -> ConvData <$> isCoind <*> convertDataDecl  tcdLName (hsq_explicit tcdTyVars) tcdDataDefn
          ClassDecl{..} -> ConvClass            <$> convertClassDecl tcdCtxt  tcdLName (hsq_explicit tcdTyVars) tcdFDs tcdSigs tcdMeths tcdATs tcdATDefs

        Just redef -> do
          case (decl, redef) of
            (SynDecl{},  CoqDefinitionDef def) ->
              pure . ConvSyn $ case def of
                DefinitionDef _ name args oty body -> SynBody name args oty body
                LetDef          name args oty body -> SynBody name args oty body

            (DataDecl{}, CoqInductiveDef ind) ->
              case ind of
                Inductive   (body :| [])  []    -> pure $ ConvData False body
                CoInductive (body :| [])  []    -> pure $ ConvData True body
                Inductive   (_    :| _:_) _     -> editFailure $ "cannot redefine data type to mutually-recursive types"
                Inductive   _             (_:_) -> editFailure $ "cannot redefine data type to include notations"
                CoInductive _             _     -> editFailure $ "cannot redefine data type to be coinductive"

            (FamDecl{}, _) ->
              editFailure "cannot redefine type/data families"

            (ClassDecl{}, _) ->
              editFailure "cannot redefine type class declarations"

            _ ->
              let from = case decl of
                           FamDecl{}   -> "a type/data family"
                           SynDecl{}   -> "a type synonym"
                           DataDecl{}  -> "a data type"
                           ClassDecl{} -> "a type class"
                  to   = case redef of
                           CoqDefinitionDef       _ -> "a Definition"
                           CoqFixpointDef         _ -> "a Fixpoint"
                           CoqInductiveDef        _ -> "an Inductive"
                           CoqInstanceDef         _ -> "an Instance Definition"
              in editFailure $ "cannot redefine " ++ from ++ " to be " ++ to

--------------------------------------------------------------------------------

data DeclarationGroup = DeclarationGroup { dgInductives   :: [IndBody]
                                         , dgCoInductives :: [IndBody]
                                         , dgSynonyms     :: [SynBody]
                                         , dgClasses      :: [ClassBody]
                                         , dgFailures     :: [Sentence]}
                      deriving (Eq, Ord, Show, Read)

instance Semigroup DeclarationGroup where
  DeclarationGroup ind1 coi1 syn1 cls1 fail1 <>
   DeclarationGroup ind2 coi2 syn2 cls2 fail2 =
    DeclarationGroup (ind1 <> ind2) (coi1 <> coi2) (syn1 <> syn2) (cls1 <> cls2) (fail1 <> fail2)

instance Monoid DeclarationGroup where
  mempty  = DeclarationGroup [] [] [] [] []
  mappend = (<>)

singletonDeclarationGroup :: ConvertedDeclaration -> DeclarationGroup
singletonDeclarationGroup (ConvData False ind)     = DeclarationGroup [ind] []    []    []    []
singletonDeclarationGroup (ConvData True  coi)     = DeclarationGroup []    [coi] []    []    []
singletonDeclarationGroup (ConvSyn   syn)          = DeclarationGroup []    []    [syn] []    []
singletonDeclarationGroup (ConvClass cls)          = DeclarationGroup []    []    []    [cls] []
singletonDeclarationGroup (ConvFailure _ sen)      = DeclarationGroup []    []    []    []    [sen]

--------------------------------------------------------------------------------

convertDeclarationGroup :: DeclarationGroup -> Either String [Sentence]
convertDeclarationGroup DeclarationGroup{..} =
    (dgFailures ++) <$>
    case (nonEmpty dgInductives, nonEmpty dgCoInductives, nonEmpty dgSynonyms, nonEmpty dgClasses) of
  (Just inds, Nothing, Nothing, Nothing) ->
    Right [InductiveSentence $ Inductive inds []]

  (Nothing, Just coinds, Nothing, Nothing) ->
    Right [InductiveSentence $ CoInductive coinds []]

  (Nothing, Nothing, Just (SynBody name args oty def :| []), Nothing) ->
    Right [DefinitionSentence $ DefinitionDef Global name args oty def]

  (Just inds, Nothing, Just syns, Nothing) ->
    Right $  foldMap recSynType syns
          ++ [InductiveSentence $ Inductive inds (orderRecSynDefs $ recSynDefs inds syns)]

  (Nothing, Nothing, Nothing, Just (classDef :| [])) ->
    Right $ classSentences classDef

  (Nothing, Nothing, Nothing, Nothing) ->
    Right []

  (_, _, _, _) ->
    Left "too much mutual recursion"

  where
    synName = qualidExtendBase "__raw"

    recSynType :: SynBody -> [Sentence] -- Otherwise GHC infers a type containing @~@.
    recSynType (SynBody name _ _ _) =
      [ InductiveSentence $ Inductive [IndBody (synName name) [] (Sort Type) []] []
      , NotationSentence $ ReservedNotationIdent (qualidBase name) ]

    indParams (IndBody _ params _ _) = S.fromList $ foldMap (toListOf binderIdents) params

    -- FIXME use real substitution
    avoidParams params = until (`S.notMember` params) (qualidExtendBase "_")

    recSynMapping params (SynBody name args oty def) =
      let mkFun    = maybe id Fun . nonEmpty
          withType = maybe id (flip HasType)
      in (name, App "GHC.Base.Synonym"
                  $ fmap PosArg [ Qualid (synName name)
                                , everywhere (mkT $ avoidParams params) .
                                    mkFun args $ withType oty def ])

    recSynDefs inds = M.fromList . toList . fmap (recSynMapping $ foldMap indParams inds)

    orderRecSynDefs synDefs =
      [ NotationIdentBinding (qualidBase syn) $ synDefs M.! syn
      | syn <- foldMap toList $ topoSortEnvironment synDefs ]

--------------------------------------------------------------------------------

-- We expect to be in the presence of
--
-- @
-- Set Implicit Arguments.
-- Unset Strict Implicit.
-- Unset Printing Implicit Defensive.
-- @
--
-- which creates implicit arguments correctly for most constructors.  The
-- exception are constructors which don't mention some parameters in their
-- arguments; any missing parameters are not made implicit.  Thus, for those
-- cases, we add the argument specifiers manually.

-- TODO: May be buggy with mixed parameters/indices (which can only arise via
-- edits).
-- TODO: GADTs.
-- TODO: Keep the argument specifiers with the data types.
generateArgumentSpecifiers :: ConversionMonad m => IndBody -> m [Arguments]
generateArgumentSpecifiers (IndBody _ params _resTy cons)
  | null params = pure []
  | otherwise   = catMaybes <$> traverse setImplicits cons
  where
    setImplicits (con,_,_) = use (constructorFields.at con) >>= \case
        -- Ignore cons we do not know anythings about
        -- (e.g. because they are skipped or redefined)
        Nothing -> pure Nothing
        Just fields -> do
          let fieldCount = case fields of NonRecordFields count -> count
                                          RecordFields conFields -> length conFields

          pure . Just . Arguments Nothing con
                   $  replicate paramCount (underscoreArg ArgMaximal)
                   ++ replicate fieldCount (underscoreArg ArgExplicit)

    paramCount = length params

    underscoreArg eim = ArgumentSpec eim UnderscoreName Nothing

generateGroupArgumentSpecifiers :: ConversionMonad m => DeclarationGroup -> m [Sentence]
generateGroupArgumentSpecifiers = fmap (fmap ArgumentsSentence)
                                . foldTraverse generateArgumentSpecifiers
                                . (\x -> dgInductives x ++ dgCoInductives x)

--------------------------------------------------------------------------------

generateRecordAccessors :: ConversionMonad m => IndBody -> m [Definition]
generateRecordAccessors (IndBody tyName params resTy cons) = do
  let conNames = view _1 <$> cons

  let restrict = M.filterWithKey $ \k _ -> k `elem` conNames
  allFields <- uses (constructorFields.to restrict.folded._RecordFields) (S.toAscList . S.fromList)
  filteredFields <- filterM (\field -> not <$> use (edits.skipped.contains field)) allFields
  for filteredFields $ \(field :: Qualid) -> do
    equations <- for conNames $ \con -> do
      (args, hasField) <- use (constructorFields.at con) >>= \case
        Just (NonRecordFields count) ->
          pure (replicate count UnderscorePat, False)
        Just (RecordFields conFields0) ->
          pure $ go conFields0 where
            go [] = ([], False)
            go (conField : conFields)
              | field == conField  = (Coq.VarPat (qualidBase field) : map (const UnderscorePat) conFields, True)
              | otherwise               = first (UnderscorePat :) $ go conFields

        Nothing -> throwProgramError $  "internal error: unknown constructor `"
                                     <> show con <> "' for type `"
                                     <> show tyName <> "'"
      pure . Equation [MultPattern [ArgsPat con args]] $
                      if hasField
                      then Qualid field
                      else App1 "GHC.Err.error"
                                (HsString $  "Partial record selector: field `"
                                          <> qualidBase field <> "' has no match in constructor `"
                                          <> qualidBase con <> "' of type `"
                                          <> qualidBase tyName <> "'")

    arg <- genqid "arg"

    let indices (Forall bs t)  = toList bs ++ indices t
        indices (Arrow  t1 t2) = Typed Ungeneralizable Coq.Explicit [UnderscoreName] t1 : indices t2
        indices _              = []

        deunderscore UnderscoreName = Ident <$> genqid "ty"
        deunderscore name           = pure name

    typeArgs <- for (params ++ indices resTy) $ \case
                  Inferred ei name           -> Inferred ei <$> deunderscore name
                  Typed    gen ex names kind -> (Typed gen ex ?? kind) <$> traverse deunderscore names
                  binder                     -> pure binder

    let implicitArgs = typeArgs & mapped.binderExplicitness .~ Coq.Implicit
        argBinder    = Typed Ungeneralizable Coq.Explicit
                               [Ident arg] (appList (Qualid tyName) $ binderArgs typeArgs)

    pure . DefinitionDef Global field (implicitArgs ++ [argBinder]) Nothing $
      Coq.Match [MatchItem (Qualid arg) Nothing Nothing] Nothing equations

generateGroupRecordAccessors :: ConversionMonad m => DeclarationGroup -> m [Sentence]
generateGroupRecordAccessors = fmap (fmap DefinitionSentence)
                             . foldTraverse generateRecordAccessors
                             . dgInductives

--------------------------------------------------------------------------------

groupTyClDecls :: ConversionMonad m
               => [(Maybe ModuleName, TyClDecl GHC.Name)] -> m [DeclarationGroup]
groupTyClDecls decls = do
  bodies <- traverse (maybeWithCurrentModule .*^ convertTyClDecl) decls <&>
              M.fromList . map (convDeclName &&& id) . catMaybes

  -- Might be overgenerous
  ctypes <- use constructorTypes

  pure . map (foldMap $ singletonDeclarationGroup . (bodies M.!))
       . flip topoSortEnvironmentWith bodies
       $ \decl -> let vars = getFreeVars decl
                  in vars <> setMapMaybe (M.lookup ?? ctypes) vars

convertModuleTyClDecls :: ConversionMonad m
                       => [(Maybe ModuleName, TyClDecl GHC.Name)] -> m [Sentence]
convertModuleTyClDecls =   forkM3 (either convUnsupported pure
                                    . foldTraverse convertDeclarationGroup)
                                  (foldTraverse generateGroupArgumentSpecifiers)
                                  (foldTraverse generateGroupRecordAccessors)
                       <=< groupTyClDecls
  where forkM3 l m r i = (<>) <$> ((<>) <$> l i <*> m i) <*> r i

convertTyClDecls :: ConversionMonad m => [TyClDecl GHC.Name] -> m [Sentence]
convertTyClDecls = convertModuleTyClDecls . map (Nothing,)
