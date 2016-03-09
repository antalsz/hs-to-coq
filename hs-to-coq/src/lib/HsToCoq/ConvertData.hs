{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards, PatternSynonyms,
             OverloadedLists, OverloadedStrings #-}

module HsToCoq.ConvertData (
  -- * Conversion
  -- ** Declarations
  convertTyClDecls, convertTyClDecl, convertDataDecl, convertSynDecl,
  -- ** Terms
  convertType, convertLType,
  convertLHsTyVarBndrs,
  -- ** Names
  showRdrName, showName,
  -- ** Declaration groups
  DeclarationGroup(..), addDeclaration,
  groupConvDecls, groupTyClDecls, convertDeclarationGroup,
  -- ** Backing types
  SynBody(..), ConvertedDeclaration(..),
  -- ** Internal
  convertDataDefn, convertConDecl,
  -- * Coq construction
  pattern Var, pattern App1, appList
  ) where

import Data.Semigroup ((<>))
import Data.Foldable
import Data.Traversable
import Data.List.NonEmpty (NonEmpty(..), (<|), nonEmpty)
import Data.Text (Text)

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.IO.Class

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name)
import qualified GHC
import RdrName
import OccName
import Panic

import HsToCoq.Util.Functor
import HsToCoq.Util.Containers
import HsToCoq.Util.Patterns
import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.FreeVars

import Data.Generics

showRdrName :: GhcMonad m => RdrName -> m Text
showRdrName = ghcSDoc . pprOccName . rdrNameOcc

showName :: GhcMonad m => GHC.Name -> m Text
showName = showRdrName . nameRdrName

-- Module-local
conv_unsupported :: MonadIO m => String -> m a
conv_unsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"

pattern Var  x   = Qualid (Bare x)
pattern App1 f x = App f (PosArg x :| Nil)

appList :: Term -> [Arg] -> Term
appList f xs = case nonEmpty xs of
                 Nothing  -> f
                 Just xs' -> App f xs'

convertType :: GhcMonad m => HsType RdrName -> m Term
convertType (HsForAllTy _explicit _ _tvs _ctx _ty) =
  conv_unsupported "forall" -- FIXME

convertType (HsTyVar tv) =
  Var <$> ghcPpr tv -- TODO Check module part?

convertType (HsAppTy ty1 ty2) =
  App1 <$> convertLType ty1 <*> convertLType ty2

convertType (HsFunTy ty1 ty2) =
  Arrow <$> convertLType ty1 <*> convertLType ty2

convertType (HsListTy ty) =
  App1 (Var "list") <$> convertLType ty

convertType (HsPArrTy _ty) =
  conv_unsupported "parallel arrays (`[:a:]')"

convertType (HsTupleTy tupTy tys) = do
  case tupTy of
    HsUnboxedTuple           -> conv_unsupported "unboxed tuples"
    HsBoxedTuple             -> pure ()
    HsConstraintTuple        -> conv_unsupported "constraint tuples"
    HsBoxedOrConstraintTuple -> pure () -- Sure, it's boxed, why not
  case tys of
    []   -> pure $ Var "unit"
    [ty] -> convertLType ty
    _    -> foldl1 (\x t -> App (Var "prod") [PosArg x, PosArg t]) <$> traverse convertLType tys

convertType (HsOpTy _ty1 _op _ty2) =
  conv_unsupported "binary operators" -- FIXME

convertType (HsParTy ty) =
  Parens <$> convertLType ty

convertType (HsIParamTy _ _) =
  conv_unsupported "implicit parameters"

convertType (HsEqTy _ty1 _ty2) =
  conv_unsupported "type equality" -- FIXME

convertType (HsKindSig ty k) =
  HasType <$> convertLType ty <*> convertLType k

convertType (HsQuasiQuoteTy _) =
  conv_unsupported "quasiquoters"

convertType (HsSpliceTy _ _) =
  conv_unsupported "Template Haskell"

convertType (HsDocTy ty _doc) =
  convertLType ty

convertType (HsBangTy _bang ty) =
  convertLType ty -- Strictness annotations are ignored

convertType (HsRecTy _fields) =
  conv_unsupported "record types" -- FIXME

convertType (HsCoreTy _) =
  conv_unsupported "[internal] embedded core types"

convertType (HsExplicitListTy PlaceHolder tys) =
  foldr (\ty l -> App (Var "cons") [PosArg ty, PosArg l]) (Var "nil") <$> traverse convertLType tys

convertType (HsExplicitTupleTy _PlaceHolders tys) =
  case tys of
    []   -> pure $ Var "tt"
    [ty] -> convertLType ty
    _    -> foldl1 (\x t -> App (Var "pair") [PosArg x, PosArg t]) <$> traverse convertLType tys

convertType (HsTyLit lit) =
  case lit of
    HsNumTy _ int | int >= 0  -> pure . Num $ fromInteger int
                  | otherwise -> conv_unsupported "negative type-level integers"
    HsStrTy _ _               -> conv_unsupported "type-level strings"

convertType (HsWrapTy _ _) =
  conv_unsupported "[internal] wrapped types" 

convertType HsWildcardTy =
  pure Underscore

convertType (HsNamedWildcardTy _) =
  conv_unsupported "named wildcards"

convertLType :: GhcMonad m => LHsType RdrName -> m Term
convertLType = convertType . unLoc

type Constructor = (Ident, [Binder], Maybe Term)

convertLHsTyVarBndrs :: GhcMonad m => LHsTyVarBndrs RdrName -> m [Binder]
convertLHsTyVarBndrs (HsQTvs kvs tvs) = do
  kinds <- traverse (fmap (Inferred . Ident) . ghcPpr) kvs
  types <- for (map unLoc tvs) $ \case
             UserTyVar   tv   -> Inferred . Ident <$> ghcPpr tv
             KindedTyVar tv k -> Typed <$> (pure . Ident <$> ghcPpr tv) <*> convertLType k
  pure $ kinds ++ types

convertConDecl :: GhcMonad m => Term -> ConDecl RdrName -> m [Constructor]
convertConDecl curType (ConDecl lnames _explicit lqvs lcxt ldetails lres _doc _old) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "constructor contexts"
  names  <- traverse (ghcPpr . unLoc) lnames
  params <- convertLHsTyVarBndrs lqvs
  resTy  <- case lres of
              ResTyH98       -> pure curType
              ResTyGADT _ ty -> convertLType ty
  args   <- traverse convertLType $ hsConDeclArgTys ldetails
  pure $ map ((, params, Just $ foldr Arrow resTy args) . ("Mk_" <>)) names
  
convertDataDefn :: GhcMonad m => Term -> HsDataDefn RdrName -> m (Term, [Constructor])
convertDataDefn curType (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (concat <$> traverse (convertConDecl curType . unLoc) cons)

convertDataDecl :: GhcMonad m
                => Located RdrName -> LHsTyVarBndrs RdrName -> HsDataDefn RdrName
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName <- ghcPpr $ unLoc name
  params  <- convertLHsTyVarBndrs tvs
  let nameArgs    = map $ PosArg . \case
                      Ident x        -> Var x
                      UnderscoreName -> Underscore
      curType     = appList (Var coqName) . nameArgs $ foldMap binderNames params
  (resTy, cons) <- convertDataDefn curType defn
  pure $ IndBody coqName params resTy cons

data SynBody = SynBody Ident [Binder] (Maybe Term) Term
             deriving (Eq, Ord, Read, Show)

convertSynDecl :: GhcMonad m
               => Located RdrName -> LHsTyVarBndrs RdrName -> LHsType RdrName
               -> m SynBody
convertSynDecl name args def  = SynBody <$> ghcPpr (unLoc name)
                                        <*> convertLHsTyVarBndrs args
                                        <*> pure Nothing
                                        <*> convertLType def

instance FreeVars SynBody where
  freeVars (SynBody _name args oty def) = binding args $ freeVars oty *> freeVars def
       
data ConvertedDeclaration = ConvData IndBody
                          | ConvSyn  SynBody
                          deriving (Eq, Ord, Show, Read)

instance FreeVars ConvertedDeclaration where
  freeVars (ConvData ind) = freeVars ind
  freeVars (ConvSyn  syn) = freeVars syn

convDeclName :: ConvertedDeclaration -> Ident
convDeclName (ConvData (IndBody tyName  _ _ _)) = tyName
convDeclName (ConvSyn  (SynBody synName _ _ _)) = synName

convertTyClDecl :: GhcMonad m => TyClDecl RdrName -> m ConvertedDeclaration
convertTyClDecl FamDecl{}    = conv_unsupported "type/data families"
convertTyClDecl SynDecl{..}  = ConvSyn  <$> convertSynDecl  tcdLName tcdTyVars tcdRhs
convertTyClDecl DataDecl{..} = ConvData <$> convertDataDecl tcdLName tcdTyVars tcdDataDefn
convertTyClDecl ClassDecl{}  = conv_unsupported "type classes"

data DeclarationGroup = Inductives (NonEmpty IndBody)
                      | Synonym    SynBody
                      | Synonyms   SynBody (NonEmpty SynBody)
                      | Mixed      (NonEmpty IndBody) (NonEmpty SynBody)
                      deriving (Eq, Ord, Show, Read)

addDeclaration :: ConvertedDeclaration -> DeclarationGroup -> DeclarationGroup
---------------------------------------------------------------------------------------------
addDeclaration (ConvData ind) (Inductives inds)      = Inductives (ind <| inds)
addDeclaration (ConvData ind) (Synonym    syn)       = Mixed      (ind :| [])   (syn :| [])
addDeclaration (ConvData ind) (Synonyms   syn syns)  = Mixed      (ind :| [])   (syn <| syns)
addDeclaration (ConvData ind) (Mixed      inds syns) = Mixed      (ind <| inds) syns
---------------------------------------------------------------------------------------------
addDeclaration (ConvSyn  syn) (Inductives inds)      = Mixed      inds          (syn :| [])
addDeclaration (ConvSyn  syn) (Synonym    syn')      = Synonyms                 syn (syn' :| [])
addDeclaration (ConvSyn  syn) (Synonyms   syn' syns) = Synonyms                 syn (syn' <| syns)
addDeclaration (ConvSyn  syn) (Mixed      inds syns) = Mixed      inds          (syn <| syns)

groupConvDecls :: NonEmpty ConvertedDeclaration -> DeclarationGroup
groupConvDecls (cd :| cds) = flip (foldr addDeclaration) cds $ case cd of
                               ConvData ind -> Inductives (ind :| [])
                               ConvSyn  syn -> Synonym    syn

groupTyClDecls :: GhcMonad m => [TyClDecl RdrName] -> m [DeclarationGroup]
groupTyClDecls decls = do
  bodies <- traverse convertTyClDecl decls <&>
              M.fromList . map (convDeclName &&& id)
  -- The order is correct – later declarationss refer only to previous ones –
  -- since 'stronglyConnComp'' returns its outputs in topologically sorted
  -- order.
  let mutuals = stronglyConnComp' . M.toList $ (S.toList . getFreeVars) <$> bodies
  pure $ map (groupConvDecls . fmap (bodies M.!)) mutuals

convertDeclarationGroup :: DeclarationGroup -> Either String [Sentence]
convertDeclarationGroup = \case
  Inductives ind ->
    Right [InductiveSentence $ Inductive ind []]
  
  Synonym (SynBody name args oty def) ->
    Right [DefinitionSentence $ DefinitionDef Global name args oty def]
  
  Synonyms _ _ ->
    Left "mutually-recursive type synonyms"
  
  Mixed inds syns ->
    Right $  foldMap recSynType syns
          ++ [InductiveSentence $ Inductive inds (map (recSynDef $ foldMap indParams inds) $ toList syns)]
  
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

convertTyClDecls :: GhcMonad m => [TyClDecl RdrName] -> m [Sentence]
convertTyClDecls =   either conv_unsupported (pure . fold)
                 .   traverse convertDeclarationGroup
                 <=< groupTyClDecls
