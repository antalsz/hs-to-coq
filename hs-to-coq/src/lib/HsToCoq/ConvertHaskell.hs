{-# LANGUAGE TupleSections, LambdaCase, MultiWayIf, RecordWildCards, PatternSynonyms,
             OverloadedLists, OverloadedStrings,
             ConstraintKinds, FlexibleContexts #-}

module HsToCoq.ConvertHaskell (
  -- * Conversion
  -- ** Types
  ConversionMonad, Renaming, HsNamespace(..), evalConversion,
  -- *** Variable renaming
  rename, var, freeVar, freeVar',
  localRenamings,
  -- *** Utility
  tryEscapeReservedWord, escapeReservedNames,
  -- ** Local bindings
  convertLocalBinds,
  -- ** Declarations
  convertTyClDecls, convertValDecls,
  convertTyClDecl, convertDataDecl, convertSynDecl,
  -- ** General bindings
  convertTypedBindings, convertTypedBinding,
  ConvertedDefinition(..), withConvertedDefinition, withConvertedDefinitionDef, withConvertedDefinitionOp,
  -- ** Terms
  convertType, convertLType,
  convertExpr, convertLExpr,
  convertPat,  convertLPat,
  convertLHsTyVarBndrs,
  -- ** Case/match bodies
  convertMatchGroup, convertMatch,
  convertGRHSs, convertGRHS,
  ConvertedGuard(..), convertGuards, convertGuard,
  -- ** Functions
  convertFunction,
  -- ** Literals
  convertInteger, convertString, convertFastString,
  -- ** Declaration groups
  DeclarationGroup(..), addDeclaration,
  groupConvDecls, groupTyClDecls, convertDeclarationGroup,
  -- ** Backing types
  SynBody(..), ConvertedDeclaration(..),
  -- ** Internal
  convertDataDefn, convertConDecl, convertFixity,
  identIsVariable, identIsOperator, infixToPrefix,
  -- * Coq construction
  pattern Var, pattern App1, pattern App2, appList,
  pattern CoqVarPat
  ) where

import Prelude hiding (Num)

import Data.Semigroup ((<>))
import Data.Monoid hiding ((<>))
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Traversable
import Data.Maybe
import Data.Either
import Data.Char
import Data.List.NonEmpty (NonEmpty(..), (<|), nonEmpty)
import qualified Data.List.NonEmpty as NEL
import Data.Text (Text)
import qualified Data.Text as T

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State

import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag
import Encoding (zEncodeString)
import BasicTypes
import HsToCoq.Util.GHC.FastString
import RdrName
import Outputable (OutputableBndr)
import Panic
import HsToCoq.Util.GHC.Exception

import HsToCoq.Util.Functor
import HsToCoq.Util.List
import HsToCoq.Util.Containers
import HsToCoq.Util.Patterns
import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina
import qualified HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.FreeVars

import Data.Generics hiding (Fixity(..))

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

type Renaming = Map HsNamespace Ident

type ConversionMonad m = (GhcMonad m, MonadState (Map Ident Renaming) m)

evalConversion :: GhcMonad m => StateT (Map Ident Renaming) m a -> m a
evalConversion = flip evalStateT $ build
                   [ typ "Int" ~> "Z"

                   , typ "Bool"  ~> "bool"
                   , val "True"  ~> "true"
                   , val "False" ~> "false"

                   , typ "String" ~> "string"

                   , typ "Maybe"   ~> "option"
                   , val "Just"    ~> "Some"
                   , val "Nothing" ~> "None" ]
  where
    val hs = (hs,) . M.singleton ExprNS
    typ hs = (hs,) . M.singleton TypeNS
    (~>)   = ($)

    build = M.fromListWith M.union

rename :: ConversionMonad m => HsNamespace -> Ident -> Ident -> m ()
rename ns x x' = modify' . flip M.alter x $ Just . \case
                   Just m  -> M.insert    ns x' m
                   Nothing -> M.singleton ns x'

localRenamings :: ConversionMonad m => m a -> m a
localRenamings action = get >>= ((action <*) . put)

tryEscapeReservedWord :: Ident -> Ident -> Maybe Ident
tryEscapeReservedWord reserved name = do
  suffix <- T.stripPrefix reserved name
  guard $ T.all (== '_') suffix
  pure $ name <> "_"

escapeReservedNames :: Ident -> Ident
escapeReservedNames x =
  fromMaybe x . getFirst $
    foldMap (First . flip tryEscapeReservedWord x) (T.words "Set Type Prop fun fix forall") <>
    if | T.all (== '.') x -> pure $ T.map (const '∘') x
       | T.all (== '∘') x -> pure $ "⟨" <> x <> "⟩"
       | otherwise        -> mempty

freeVar' :: Ident -> Ident
freeVar' = escapeReservedNames

freeVar :: (GhcMonad m, OutputableBndr name) => name -> m Ident
freeVar = fmap freeVar' . ghcPpr
                                        
var :: (ConversionMonad m, OutputableBndr name) => HsNamespace -> name -> m Ident
var ns x = do
  x' <- ghcPpr x -- TODO Check module part?
  gets $ fromMaybe (escapeReservedNames x') . (M.lookup ns <=< M.lookup x')

identIsVariable :: Text -> Bool
identIsVariable = T.uncons <&> \case
  Just (h,t) -> (isAlpha h || h == '_') && T.all (\c -> isAlphaNum c || c == '_' || c == '\'') t
  Nothing    -> False

identIsOperator :: Text -> Bool
identIsOperator = not . identIsVariable

infixToPrefix :: Op -> Ident
infixToPrefix = ("_" <>) . (<> "_")

-- Module-local
conv_unsupported :: MonadIO m => String -> m a
conv_unsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"

pattern Var  x       = Qualid (Bare x)
pattern App1 f x     = App f (PosArg x :| Nil)
pattern App2 f x1 x2 = App f (PosArg x1 :| PosArg x2 : Nil)

appList :: Term -> [Arg] -> Term
appList f xs = case nonEmpty xs of
                 Nothing  -> f
                 Just xs' -> App f xs'

pattern CoqVarPat x = QualidPat (Bare x)

-- Module-local
is_noSyntaxExpr :: HsExpr id -> Bool
is_noSyntaxExpr (HsLit (HsString "" str)) = str == fsLit "noSyntaxExpr"
is_noSyntaxExpr _                         = False

convertInteger :: MonadIO f => String -> Integer -> f Num
convertInteger what int | int >= 0  = pure $ fromInteger int
                        | otherwise = conv_unsupported $ "negative " ++ what

convertFastString :: FastString -> Term
convertFastString = String . T.pack . unpackFS

convertString :: String -> Term
convertString = String . T.pack

convertExpr :: ConversionMonad m => HsExpr RdrName -> m Term
convertExpr (HsVar hsX) = do
  x <- var ExprNS hsX
  pure . Var $ if identIsVariable x
               then x
               else infixToPrefix x

convertExpr (HsIPVar _) =
  conv_unsupported "implicit parameters"

-- FIXME actually handle overloading
convertExpr (HsOverLit OverLit{..}) =
  case ol_val of
    HsIntegral   _src int -> Num <$> convertInteger "integer literals" int
    HsFractional _        -> conv_unsupported "fractional literals"
    HsIsString   _src str -> pure . String $ fsToText str

convertExpr (HsLit lit) =
  case lit of
    HsChar       _ _       -> conv_unsupported "`Char' literals"
    HsCharPrim   _ _       -> conv_unsupported "`Char#' literals"
    HsString     _ fs      -> pure . String $ fsToText fs
    HsStringPrim _ _       -> conv_unsupported "`Addr#' literals"
    HsInt        _ _       -> conv_unsupported "`Int' literals"
    HsIntPrim    _ _       -> conv_unsupported "`Int#' literals"
    HsWordPrim   _ _       -> conv_unsupported "`Word#' literals"
    HsInt64Prim  _ _       -> conv_unsupported "`Int64#' literals"
    HsWord64Prim _ _       -> conv_unsupported "`Word64#' literals"
    HsInteger    _ int _ty -> Num <$> convertInteger "`Integer' literals" int
    HsRat        _ _       -> conv_unsupported "`Rational' literals"
    HsFloatPrim  _         -> conv_unsupported "`Float#' literals"
    HsDoublePrim _         -> conv_unsupported "`Double#' literals"

convertExpr (HsLam mg) =
  uncurry Fun <$> convertFunction mg

convertExpr (HsLamCase PlaceHolder mg) =
  uncurry Fun <$> convertFunction mg

convertExpr (HsApp e1 e2) =
  App1 <$> convertLExpr e1 <*> convertLExpr e2

convertExpr (OpApp el eop PlaceHolder er) =
  case eop of
    L _ (HsVar hsOp) -> do
      op <- var ExprNS hsOp
      l  <- convertLExpr el
      r  <- convertLExpr er
      pure $ if identIsOperator op
             then Infix l op r
             else App2 (Var op) l r
    _ ->
      conv_unsupported "non-variable infix operators"

convertExpr (NegApp _ _) =
  conv_unsupported "negation"

convertExpr (HsPar e) =
  Parens <$> convertLExpr e

convertExpr (SectionL l opE) =
  convert_section (Just l) opE Nothing

convertExpr (SectionR opE r) =
  convert_section Nothing opE (Just r)

convertExpr (ExplicitTuple _ _) =
  conv_unsupported "tuples"

convertExpr (HsCase e mg) =
  Coq.Match <$> (fmap pure $ MatchItem <$> convertLExpr e <*> pure Nothing <*> pure Nothing)
            <*> pure Nothing
            <*> convertMatchGroup mg

convertExpr (HsIf overloaded c t f) =
  if maybe True is_noSyntaxExpr overloaded
  then If <$> convertLExpr c <*> pure Nothing <*> convertLExpr t <*> convertLExpr f
  else conv_unsupported "overloaded if-then-else"

convertExpr (HsMultiIf _ _) =
  conv_unsupported "multi-way if"

convertExpr (HsLet binds body) =
  convertLocalBinds binds $ convertLExpr body

convertExpr (HsDo _ _ _) =
  conv_unsupported "`do' expressions"

convertExpr (ExplicitList _ _ _) =
  conv_unsupported "explicit lists"

convertExpr (ExplicitPArr _ _) =
  conv_unsupported "explicit parallel arrays"

convertExpr (RecordCon _ _ _) =
  conv_unsupported "record constructors"

convertExpr (RecordUpd _ _ _ _ _) =
  conv_unsupported "record updates"

convertExpr (ExprWithTySig e ty PlaceHolder) =
  HasType <$> convertLExpr e <*> convertLType ty

convertExpr (ExprWithTySigOut _ _) =
  conv_unsupported "`ExprWithTySigOut' constructor"

convertExpr (ArithSeq _ _ _) =
  conv_unsupported "arithmetic sequences"

convertExpr (PArrSeq _ _) =
  conv_unsupported "parallel array arithmetic sequences"

convertExpr (HsSCC _ _ e) =
  convertLExpr e

convertExpr (HsCoreAnn _ _ e) =
  convertLExpr e

convertExpr (HsBracket _) =
  conv_unsupported "Template Haskell brackets"

convertExpr (HsRnBracketOut _ _) =
  conv_unsupported "`HsRnBracketOut' constructor"

convertExpr (HsTcBracketOut _ _) =
  conv_unsupported "`HsTcBracketOut' constructor"

convertExpr (HsSpliceE _ _) =
  conv_unsupported "Template Haskell expression splices"

convertExpr (HsQuasiQuoteE _) =
  conv_unsupported "expression quasiquoters"

convertExpr (HsProc _ _) =
  conv_unsupported "`proc' expressions"

convertExpr (HsStatic _) =
  conv_unsupported "static pointers"

convertExpr (HsArrApp _ _ _ _ _) =
  conv_unsupported "arrow application command"

convertExpr (HsArrForm _ _ _) =
  conv_unsupported "arrow command formation"

convertExpr (HsTick _ e) =
  convertLExpr e

convertExpr (HsBinTick _ _ e) =
  convertLExpr e

convertExpr (HsTickPragma _ _ e) =
  convertLExpr e

convertExpr EWildPat =
  conv_unsupported "wildcard pattern in expression"

convertExpr (EAsPat _ _) =
  conv_unsupported "as-pattern in expression"

convertExpr (EViewPat _ _) =
  conv_unsupported "view-pattern in expression"

convertExpr (ELazyPat _) =
  conv_unsupported "lazy pattern in expression"

convertExpr (HsType ty) =
  convertLType ty

convertExpr (HsWrap _ _) =
  conv_unsupported "`HsWrap' constructor"

convertExpr (HsUnboundVar x) =
  Var <$> freeVar x

convertLExpr :: ConversionMonad m => LHsExpr RdrName -> m Term
convertLExpr = convertExpr . unLoc

-- Module-local
convert_section :: (ConversionMonad m) => Maybe (LHsExpr RdrName) -> LHsExpr RdrName -> Maybe (LHsExpr RdrName) -> m Term
convert_section  ml opE mr =
  let arg = "__arg__"
      
      hs  = HsVar . mkVarUnqual . fsLit
      coq = Inferred Coq.Explicit . Ident . T.pack
      
      orArg = fromMaybe (noLoc $ hs arg)
  in Fun [coq arg] <$> convertExpr (OpApp (orArg ml) opE PlaceHolder (orArg mr))

convertPat :: ConversionMonad m => Pat RdrName -> m Pattern
convertPat (WildPat PlaceHolder) =
  pure UnderscorePat

convertPat (GHC.VarPat x) =
  CoqVarPat <$> freeVar x

convertPat (LazyPat p) =
  convertLPat p

convertPat (GHC.AsPat x p) =
  Coq.AsPat <$> convertLPat p <*> freeVar (unLoc x)

convertPat (ParPat p) =
  convertLPat p

convertPat (BangPat p) =
  convertLPat p

convertPat (ListPat _ _ _) =
  conv_unsupported "list patterns"

convertPat (TuplePat _ _ _) =
  conv_unsupported "tuple patterns"

convertPat (PArrPat _ _) =
  conv_unsupported "parallel array patterns"

convertPat (ConPatIn con conVariety) =
  case conVariety of
    PrefixCon args' -> do
      conVar <- Bare <$> var ExprNS (unLoc con)
      case nonEmpty args' of
        Just args -> ArgsPat conVar <$> traverse convertLPat args
        Nothing   -> pure $ QualidPat conVar
    RecCon    _    ->
      conv_unsupported "record constructor patterns"
    InfixCon  _ _  ->
      conv_unsupported "infix constructor patterns"

convertPat (ConPatOut{}) =
  conv_unsupported "[internal?] `ConPatOut' constructor"

convertPat (ViewPat _ _ _) =
  conv_unsupported "view patterns"

convertPat (SplicePat _) =
  conv_unsupported "pattern splices"

convertPat (QuasiQuotePat _) =
  conv_unsupported "pattern quasiquoters"

convertPat (LitPat lit) =
  case lit of
    HsChar       _ _       -> conv_unsupported "`Char' literal patterns"
    HsCharPrim   _ _       -> conv_unsupported "`Char#' literal patterns"
    HsString     _ fs      -> pure . StringPat $ fsToText fs
    HsStringPrim _ _       -> conv_unsupported "`Addr#' literal patterns"
    HsInt        _ _       -> conv_unsupported "`Int' literal patterns"
    HsIntPrim    _ _       -> conv_unsupported "`Int#' literal patterns"
    HsWordPrim   _ _       -> conv_unsupported "`Word#' literal patterns"
    HsInt64Prim  _ _       -> conv_unsupported "`Int64#' literal patterns"
    HsWord64Prim _ _       -> conv_unsupported "`Word64#' literal patterns"
    HsInteger    _ int _ty -> NumPat <$> convertInteger "`Integer' literal patterns" int
    HsRat        _ _       -> conv_unsupported "`Rational' literal patterns"
    HsFloatPrim  _         -> conv_unsupported "`Float#' literal patterns"
    HsDoublePrim _         -> conv_unsupported "`Double#' literal patterns"

convertPat (NPat (L _ OverLit{..}) _negate _eq) = -- And strings
  case ol_val of
    HsIntegral   _src int -> NumPat <$> convertInteger "integer literal patterns" int
    HsFractional _        -> conv_unsupported "fractional literal patterns"
    HsIsString   _src str -> pure . StringPat $ fsToText str

convertPat (NPlusKPat _ _ _ _) =
  conv_unsupported "n+k-patterns"

convertPat (SigPatIn _ _) =
  conv_unsupported "`SigPatIn' constructor"

convertPat (SigPatOut _ _) =
  conv_unsupported "`SigPatOut' constructor"

convertPat (CoPat _ _ _) =
  conv_unsupported "coercion patterns"

convertLPat :: ConversionMonad m => LPat RdrName -> m Pattern
convertLPat = convertPat . unLoc

data ConvertedDefinition = ConvertedDefinition { convDefName  :: !Ident
                                               , convDefArgs  :: ![Binder]
                                               , convDefType  :: !(Maybe Term)
                                               , convDefBody  :: !Term
                                               , convDefInfix :: !(Maybe Op) }
                         deriving (Eq, Ord, Read, Show)

withConvertedDefinition :: Monoid m
                        => (Ident -> [Binder] -> Maybe Term -> Term -> a) -> (a -> m)
                        -> (Op -> Ident -> b)                             -> (b -> m)
                        -> (ConvertedDefinition -> m)
withConvertedDefinition withDef wrapDef withOp wrapOp ConvertedDefinition{..} =
  mappend (wrapDef $ withDef convDefName convDefArgs convDefType convDefBody)
          (maybe mempty (wrapOp . flip withOp convDefName) convDefInfix)

withConvertedDefinitionDef :: (Ident -> [Binder] -> Maybe Term -> Term -> a) -> (ConvertedDefinition -> a)
withConvertedDefinitionDef f ConvertedDefinition{..} = f convDefName convDefArgs convDefType convDefBody

withConvertedDefinitionOp :: (Op -> Ident -> a) -> (ConvertedDefinition -> Maybe a)
withConvertedDefinitionOp f ConvertedDefinition{..} = fmap (flip f convDefName) convDefInfix

convertLocalBinds :: ConversionMonad m => HsLocalBinds RdrName -> m Term -> m Term
convertLocalBinds (HsValBinds (ValBindsIn binds sigs)) body = localRenamings $ do
  convDefs <- convertTypedBindings (map unLoc . bagToList $ binds) (map unLoc sigs) pure Nothing
  sequence_ $ mapMaybe (withConvertedDefinitionOp $ rename ExprNS) convDefs
  flip (foldr $ withConvertedDefinitionDef Let) convDefs <$> body
convertLocalBinds (HsValBinds (ValBindsOut _ _)) _ =
  conv_unsupported "post-renaming `ValBindsOut' bindings"
convertLocalBinds (HsIPBinds _) _ =
  conv_unsupported "local implicit parameter bindings"
convertLocalBinds EmptyLocalBinds body =
  body

-- TODO mutual recursion :-(
convertTypedBindings :: ConversionMonad m
                     => [HsBind RdrName] -> [Sig RdrName]
                     -> (ConvertedDefinition -> m a)
                     -> Maybe (HsBind RdrName -> GhcException -> m a)
                     -> m [a]
convertTypedBindings defns allSigs build mhandler =
  let sigs = M.fromList $ [(name,ty) | TypeSig lnames (L _ ty) PlaceHolder <- allSigs
                                     , L _ name <- lnames ]
      
      getType FunBind{..} = M.lookup (unLoc fun_id) sigs
      getType _           = Nothing

      processed defn = maybe id (ghandle . ($ defn)) mhandler . (build =<<)
      
  in traverse (processed <*> (convertTypedBinding =<< getType)) defns

convertTypedBinding :: ConversionMonad m => Maybe (HsType RdrName) -> HsBind RdrName -> m ConvertedDefinition
convertTypedBinding _hsTy PatBind{}    = conv_unsupported "pattern bindings"
convertTypedBinding _hsTy VarBind{}    = conv_unsupported "[internal] `VarBind'"
convertTypedBinding _hsTy AbsBinds{}   = conv_unsupported "[internal?] `AbsBinds'"
convertTypedBinding _hsTy PatSynBind{} = conv_unsupported "pattern synonym bindings"
convertTypedBinding  hsTy FunBind{..}  = do
  (name, opName) <- freeVar (unLoc fun_id) <&> \case
                      name | identIsVariable name -> (name, Nothing)
                           | otherwise            -> ("__op_" <> T.pack (zEncodeString $ T.unpack name) <> "__", Just name)
  
  (tvs, coqTy) <-
    -- The @forall@ed arguments need to be brought into scope
    let peelForall (Forall tvs body) = first (NEL.toList tvs ++) $ peelForall body
        peelForall ty                = ([], ty)
    in maybe ([], Nothing) (second Just . peelForall) <$> traverse convertType hsTy
  
  defn <-
    if all (null . m_pats . unLoc) $ mg_alts fun_matches
    then case mg_alts fun_matches of
           [L _ (GHC.Match _ [] mty grhss)] ->
             maybe (pure id) (fmap (flip HasType) . convertLType) mty <*> convertGRHSs grhss
           _ ->
             conv_unsupported "malformed multi-match variable definitions"
    else do
      (argBinders, match) <- convertFunction fun_matches
      pure $ let bodyVars = getFreeVars match
             in if name `S.member` bodyVars || maybe False (`S.member` bodyVars) opName
                then Fix . FixOne $ FixBody name argBinders Nothing Nothing match -- TODO recursion and binary operators
                else Fun argBinders match
  
  pure $ ConvertedDefinition name tvs coqTy defn opName

convertMatchGroup :: ConversionMonad m => MatchGroup RdrName (LHsExpr RdrName) -> m [Equation]
convertMatchGroup (MG alts _ _ _) = traverse (convertMatch . unLoc) alts

convertMatch :: ConversionMonad m => Match RdrName (LHsExpr RdrName) -> m Equation
convertMatch GHC.Match{..} = do
  pats <- maybe (conv_unsupported "no-pattern case arms") pure . nonEmpty
            =<< traverse convertLPat m_pats
  oty  <- traverse convertLType m_type
  rhs  <- convertGRHSs m_grhss
  pure . Equation [MultPattern pats] $ maybe id (flip HasType) oty rhs

convertFunction :: ConversionMonad m => MatchGroup RdrName (LHsExpr RdrName) -> m (Binders, Term)
convertFunction mg = do
  eqns <- convertMatchGroup mg
  let argCount   = case eqns of
                     Equation (MultPattern args :| _) _ : _ -> length args
                     _                                      -> 0
      args       = NEL.fromList ["__arg_" <> T.pack (show n) <> "__" | n <- [1..argCount]]
      argBinders = (Inferred Coq.Explicit . Ident) <$> args
      match      = Coq.Match (args <&> \arg -> MatchItem (Var arg) Nothing Nothing) Nothing eqns
  pure (argBinders, match)

convertGRHSs :: ConversionMonad m => GRHSs RdrName (LHsExpr RdrName) -> m Term
convertGRHSs GRHSs{..} =
  convertLocalBinds grhssLocalBinds
    $ convertGuards =<< traverse (convertGRHS . unLoc) grhssGRHSs

data ConvertedGuard = NoGuard
                    | BoolGuard Term
                    deriving (Eq, Ord, Show, Read)

convertGuards :: ConversionMonad m => [(ConvertedGuard,Term)] -> m Term
convertGuards []            = conv_unsupported "empty lists of guarded statements"
convertGuards [(NoGuard,t)] = pure t
convertGuards gts           = case traverse (\case (BoolGuard g,t) -> Just (g,t) ; _ -> Nothing) gts of
  Just bts -> case assertUnsnoc bts of
                (bts', (Var "true", lastTerm)) ->
                  pure $ foldr (\(c,t) f -> If c Nothing t f) lastTerm bts'
                _ ->
                  conv_unsupported "possibly-incomplete guards"
  Nothing  -> conv_unsupported "malformed guards"

convertGuard :: ConversionMonad m => [GuardLStmt RdrName] -> m ConvertedGuard
convertGuard [] = pure NoGuard
convertGuard gs = BoolGuard . foldr1 (App2 $ Var "andb") <$> traverse toCond gs where
  toCond (L _ (BodyStmt e _bind _guard _PlaceHolder)) =
    is_True_expr e >>= \case
      True  -> pure $ Var "true"
      False -> convertLExpr e
  toCond (L _ (LetStmt _)) =
    conv_unsupported "`let' statements in guards"
  toCond (L _ (BindStmt _ _ _ _)) =
    conv_unsupported "pattern guards"
  toCond _ =
    conv_unsupported "impossibly fancy guards"

convertGRHS :: ConversionMonad m => GRHS RdrName (LHsExpr RdrName) -> m (ConvertedGuard,Term)
convertGRHS (GRHS gs rhs) = (,) <$> convertGuard gs <*> convertLExpr rhs

-- Module-local
-- Based on `DsGRHSs.isTrueLHsExpr'
is_True_expr :: GhcMonad m => LHsExpr RdrName -> m Bool
is_True_expr (L _ (HsVar x))         = ((||) <$> (== "otherwise") <*> (== "True")) <$> ghcPpr x
is_True_expr (L _ (HsTick _ e))      = is_True_expr e
is_True_expr (L _ (HsBinTick _ _ e)) = is_True_expr e
is_True_expr (L _ (HsPar e))         = is_True_expr e
is_True_expr _                       = pure False

convertType :: ConversionMonad m => HsType RdrName -> m Term
convertType (HsForAllTy explicitness _ tvs ctx ty) =
  case unLoc ctx of
    [] -> do explicitTVs <- convertLHsTyVarBndrs Coq.Implicit tvs
             tyBody      <- convertLType ty
             implicitTVs <- case explicitness of
               GHC.Implicit -> do
                 -- We need to find all the unquantified type variables.  Since
                 -- Haskell never introduces a type variable name beginning with
                 -- an upper-case letter, we look for those; however, if we've
                 -- renamed a Coq value into one, we need to exclude that too.
                 -- (Also, we only keep "nonuppercase-first" names, not
                 -- "lowercase-first" names, as names beginning with @_@ are
                 -- also variables.)
                 bindings <- gets $ S.fromList . foldMap toList . toList
                 let fvs = S.filter (maybe False (not . isUpper . fst) . T.uncons) $
                             getFreeVars tyBody S.\\ bindings
                 pure . map (Inferred Coq.Implicit . Ident) $ S.toList fvs
               _ ->
                 pure []
             pure . maybe tyBody (flip Forall tyBody)
                  . nonEmpty $ explicitTVs ++ implicitTVs
    _ -> conv_unsupported "type class contexts"

convertType (HsTyVar tv) =
  Var <$> var TypeNS tv

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
    _    -> foldl1 (App2 $ Var "prod") <$> traverse convertLType tys

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
  conv_unsupported "type quasiquoters"

convertType (HsSpliceTy _ _) =
  conv_unsupported "Template Haskell type splices"

convertType (HsDocTy ty _doc) =
  convertLType ty

convertType (HsBangTy _bang ty) =
  convertLType ty -- Strictness annotations are ignored

convertType (HsRecTy _fields) =
  conv_unsupported "record types" -- FIXME

convertType (HsCoreTy _) =
  conv_unsupported "[internal] embedded core types"

convertType (HsExplicitListTy PlaceHolder tys) =
  foldr (App2 $ Var "cons") (Var "nil") <$> traverse convertLType tys

convertType (HsExplicitTupleTy _PlaceHolders tys) =
  case tys of
    []   -> pure $ Var "tt"
    [ty] -> convertLType ty
    _    -> foldl1 (App2 $ Var "pair") <$> traverse convertLType tys

convertType (HsTyLit lit) =
  case lit of
    HsNumTy _src int -> Num <$> convertInteger "type-level integers" int
    HsStrTy _src str -> pure $ convertFastString str

convertType (HsWrapTy _ _) =
  conv_unsupported "[internal] wrapped types" 

convertType HsWildcardTy =
  pure Underscore

convertType (HsNamedWildcardTy _) =
  conv_unsupported "named wildcards"

convertLType :: ConversionMonad m => LHsType RdrName -> m Term
convertLType = convertType . unLoc

type Constructor = (Ident, [Binder], Maybe Term)

convertLHsTyVarBndrs :: ConversionMonad m => Explicitness -> LHsTyVarBndrs RdrName -> m [Binder]
convertLHsTyVarBndrs ex (HsQTvs kvs tvs) = do
  kinds <- traverse (fmap (Inferred ex . Ident) . freeVar) kvs
  types <- for (map unLoc tvs) $ \case
             UserTyVar   tv   -> Inferred ex . Ident <$> freeVar tv
             KindedTyVar tv k -> Typed ex <$> (pure . Ident <$> freeVar (unLoc tv)) <*> convertLType k
  pure $ kinds ++ types

convertConDecl :: ConversionMonad m
               => Term -> ConDecl RdrName -> m [Constructor]
convertConDecl curType (ConDecl lnames _explicit lqvs lcxt ldetails lres _doc _old) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "constructor contexts"
  names   <- for lnames $ \lname -> do
               name <- ghcPpr $ unLoc lname -- We use 'ghcPpr' because we munge the name here ourselves
               let name' = "Mk_" <> name
               name' <$ rename ExprNS name name'
  params  <- convertLHsTyVarBndrs Coq.Implicit lqvs
  resTy   <- case lres of
               ResTyH98       -> pure curType
               ResTyGADT _ ty -> convertLType ty
  args    <- traverse convertLType $ hsConDeclArgTys ldetails
  pure $ map (, params, Just $ foldr Arrow resTy args) names
  
convertDataDefn :: ConversionMonad m
                => Term -> HsDataDefn RdrName
                -> m (Term, [Constructor])
convertDataDefn curType (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (concat <$> traverse (convertConDecl curType . unLoc) cons)


convertDataDecl :: ConversionMonad m
                => Located RdrName -> LHsTyVarBndrs RdrName -> HsDataDefn RdrName
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName <- freeVar $ unLoc name
  params  <- convertLHsTyVarBndrs Coq.Explicit tvs
  let nameArgs = map $ PosArg . \case
                   Ident x        -> Var x
                   UnderscoreName -> Underscore
      curType  = appList (Var coqName) . nameArgs $ foldMap binderNames params
  (resTy, cons) <- convertDataDefn curType defn
  pure $ IndBody coqName params resTy cons

data SynBody = SynBody Ident [Binder] (Maybe Term) Term
             deriving (Eq, Ord, Read, Show)

convertSynDecl :: ConversionMonad m
               => Located RdrName -> LHsTyVarBndrs RdrName -> LHsType RdrName
               -> m SynBody
convertSynDecl name args def  = SynBody <$> freeVar (unLoc name)
                                        <*> convertLHsTyVarBndrs Coq.Explicit args
                                        <*> pure Nothing
                                        <*> convertLType def

instance FreeVars SynBody where
  freeVars (SynBody _name args oty def) = binding' args $ freeVars oty *> freeVars def
       
data ConvertedDeclaration = ConvData IndBody
                          | ConvSyn  SynBody
                          deriving (Eq, Ord, Show, Read)

instance FreeVars ConvertedDeclaration where
  freeVars (ConvData ind) = freeVars ind
  freeVars (ConvSyn  syn) = freeVars syn

convDeclName :: ConvertedDeclaration -> Ident
convDeclName (ConvData (IndBody tyName  _ _ _)) = tyName
convDeclName (ConvSyn  (SynBody synName _ _ _)) = synName

convertTyClDecl :: ConversionMonad m => TyClDecl RdrName -> m ConvertedDeclaration
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

groupTyClDecls :: ConversionMonad m => [TyClDecl RdrName] -> m [DeclarationGroup]
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

convertTyClDecls :: ConversionMonad m => [TyClDecl RdrName] -> m [Sentence]
convertTyClDecls =   either conv_unsupported (pure . fold)
                 .   traverse convertDeclarationGroup
                 <=< groupTyClDecls

convertFixity :: Fixity -> (Associativity, Level)
convertFixity (Fixity hsLevel dir) = (assoc, coqLevel) where
  assoc = case dir of
            InfixL -> LeftAssociativity
            InfixR -> RightAssociativity
            InfixN -> NoAssociativity
  
  -- TODO These don't all line up between Coq and Haskell; for instance, Coq's
  -- @_ || _@ is at level 50 (Haskell 6), whereas Haskell's @(||)@ is at level 2
  -- (Coq 80).
  coqLevel = Level $ case (hsLevel, dir) of
               (0, InfixL) -> 90
               (0, InfixR) -> 91
               (0, InfixN) -> 92
               
               (1, InfixL) -> 86
               (1, InfixR) -> 85
               (1, InfixN) -> 87
               
               (2, InfixL) -> 81
               (2, InfixR) -> 80
               (2, InfixN) -> 82
               
               (3, InfixL) -> 76
               (3, InfixR) -> 75
               (3, InfixN) -> 77
               
               (4, InfixL) -> 71
               (4, InfixR) -> 72
               (4, InfixN) -> 70
               
               (5, InfixL) -> 60
               (5, InfixR) -> 61
               (5, InfixN) -> 62
               
               (6, InfixL) -> 50
               (6, InfixR) -> 51
               (6, InfixN) -> 52
               
               (7, InfixL) -> 40
               (7, InfixR) -> 41
               (7, InfixN) -> 42
               
               (8, InfixL) -> 31
               (8, InfixR) -> 30
               (8, InfixN) -> 32

               (_, _)      -> 99

convertValDecls :: ConversionMonad m => [HsDecl RdrName] -> m [Sentence]
convertValDecls args = do
  let (defns, sigs) = partitionEithers . flip mapMaybe args $ \case
                        ValD def -> Just $ Left def
                        SigD sig -> Just $ Right sig
                        _        -> Nothing
      
  fixities <- M.fromList <$> traverse (bitraverse (var ExprNS) pure)
                [(op, fixity) | FixSig (FixitySig lops fixity) <- sigs, L _ op <- lops]
  
  let toInfix :: Op -> Ident -> [Notation]
      toInfix op def = [ uncurry (InfixDefinition op (Var def))
                           . maybe (Nothing, Level 99) (first Just . convertFixity)
                           $ M.lookup op fixities
                       , NotationBinding $ NotationIdentBinding (infixToPrefix op) (Var def) ]
      
      axiomatize :: GhcMonad m => HsBind RdrName -> GhcException -> m [Sentence]
      axiomatize FunBind{..} exn = do
        name <- freeVar $ unLoc fun_id
        pure [ CommentSentence . Comment
                 $ "Translating `" <> name <> "' failed: " <> T.pack (show exn)
             , AssumptionSentence . Assumption Axiom . UnparenthesizedAssums [name]
                 $ Forall [Typed Coq.Implicit [Ident "A"] $ Sort Type] (Var "A") ]
      axiomatize _ exn =
        liftIO $ throwGhcExceptionIO exn
  
  fold <$> convertTypedBindings defns sigs
             (pure . withConvertedDefinition (DefinitionDef Global) (pure . DefinitionSentence)
                                             toInfix                (map    NotationSentence))
             (Just axiomatize)

{-
  32 record constructor patterns
  14 pattern guards
  13 pattern bindings
  10 tuple patterns
   9 tuples
   7 explicit lists
   5 possibly-incomplete guards
   4 infix constructor patterns
   4 `do' expressions
   2 list patterns
   1 type class contexts
   1 record updates
   1 `Char' literals
-}
