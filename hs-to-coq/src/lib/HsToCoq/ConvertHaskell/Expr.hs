{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Expr (
  -- * Expressions
  convertExpr, convertLExpr,
  -- * Bindings
  convertLocalBinds,
  -- ** Generic
  convertTypedBindings, convertTypedBinding,
  -- * Functions, matches, and guards
  -- ** Functions
  convertFunction,
  -- ** Matches
  convertMatchGroup, convertMatch,
  -- ** `do' blocks and similar
  convertDoBlock, convertListComprehension,
  convertPatternBinding,
  -- ** Guards
  ConvertedGuard(..), convertGuard, guardTerm,
  convertLGRHSList, convertGRHSs, convertGRHS, convertGuards
  ) where

import Control.Lens

import Data.Bifunctor
import Data.Foldable
import Data.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Text as T

import Control.Monad.Except
import Control.Monad.Writer

import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag
import BasicTypes
import HsToCoq.Util.GHC.FastString
import RdrName
import HsToCoq.Util.GHC.Exception

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.HsExpr
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Literals
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Pattern
import HsToCoq.ConvertHaskell.Sigs

--------------------------------------------------------------------------------

convertExpr :: ConversionMonad m => HsExpr RdrName -> m Term
convertExpr (HsVar x) =
  Var . toPrefix <$> var ExprNS x

convertExpr (HsIPVar _) =
  convUnsupported "implicit parameters"

-- FIXME actually handle overloading
convertExpr (HsOverLit OverLit{..}) =
  case ol_val of
    HsIntegral   _src int -> Num <$> convertInteger "integer literals" int
    HsFractional _        -> convUnsupported "fractional literals"
    HsIsString   _src str -> pure . String $ fsToText str

convertExpr (HsLit lit) =
  case lit of
    HsChar       _ c       -> pure $ InScope (String $ T.singleton c) "char"
    HsCharPrim   _ _       -> convUnsupported "`Char#' literals"
    HsString     _ fs      -> pure . String $ fsToText fs
    HsStringPrim _ _       -> convUnsupported "`Addr#' literals"
    HsInt        _ _       -> convUnsupported "`Int' literals"
    HsIntPrim    _ _       -> convUnsupported "`Int#' literals"
    HsWordPrim   _ _       -> convUnsupported "`Word#' literals"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literals"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literals"
    HsInteger    _ int _ty -> Num <$> convertInteger "`Integer' literals" int
    HsRat        _ _       -> convUnsupported "`Rational' literals"
    HsFloatPrim  _         -> convUnsupported "`Float#' literals"
    HsDoublePrim _         -> convUnsupported "`Double#' literals"

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
      convUnsupported "non-variable infix operators"

convertExpr (NegApp _ _) =
  convUnsupported "negation"

convertExpr (HsPar e) =
  Parens <$> convertLExpr e

convertExpr (SectionL l opE) =
  convert_section (Just l) opE Nothing

convertExpr (SectionR opE r) =
  convert_section Nothing opE (Just r)

convertExpr (ExplicitTuple exprs boxity) =
  case boxity of
    Boxed -> do
      -- TODO A tuple constructor in the Gallina grammar?
      (tuple, args) <- runWriterT
                    .  fmap (foldl1 . App2 $ Var "pair")
                    .  for exprs $ unLoc <&> \case
                         Present e           -> lift $ convertLExpr e
                         Missing PlaceHolder -> do arg <- lift $ gensym "arg"
                                                   Var arg <$ tell [arg]
      pure $ maybe id Fun (nonEmpty $ map (Inferred Coq.Explicit . Ident) args) tuple
    Unboxed -> convUnsupported "unboxed tuples"

convertExpr (HsCase e mg) =
  Coq.Match <$> (fmap pure $ MatchItem <$> convertLExpr e <*> pure Nothing <*> pure Nothing)
            <*> pure Nothing
            <*> convertMatchGroup mg

convertExpr (HsIf overloaded c t f) =
  if maybe True isNoSyntaxExpr overloaded
  then If <$> convertLExpr c <*> pure Nothing <*> convertLExpr t <*> convertLExpr f
  else convUnsupported "overloaded if-then-else"

convertExpr (HsMultiIf PlaceHolder lgrhsList) =
  convertLGRHSList lgrhsList

convertExpr (HsLet binds body) =
  convertLocalBinds binds $ convertLExpr body

convertExpr (HsDo sty stmts PlaceHolder) =
  case sty of
    ListComp        -> convertListComprehension stmts
    DoExpr          -> convertDoBlock stmts
    
    MonadComp       -> convUnsupported "monad comprehensions"
    PArrComp        -> convUnsupported "parallel array comprehensions"
    MDoExpr         -> convUnsupported "`mdo' expressions"
    ArrowExpr       -> convUnsupported "arrow expressions"
    GhciStmtCtxt    -> convUnsupported "GHCi statement expressions"
    PatGuard _      -> convUnsupported "pattern guard expressions"
    ParStmtCtxt _   -> convUnsupported "parallel statement expressions"
    TransStmtCtxt _ -> convUnsupported "transform statement expressions"

convertExpr (ExplicitList PlaceHolder overloaded exprs) =
  if maybe True isNoSyntaxExpr overloaded
  then foldr (Infix ?? "::") (Var "nil") <$> traverse convertLExpr exprs
  else convUnsupported "overloaded lists"

convertExpr (ExplicitPArr _ _) =
  convUnsupported "explicit parallel arrays"

-- TODO: Unify with the `RecCon` case in `ConPatIn` for `convertPat` (in
-- `HsToCoq.ConvertHaskell.Pattern`)
convertExpr (RecordCon (L _ hsCon) _postTc HsRecFields{..}) = do
  let recConUnsupported what = do
        hsConStr <- ghcPpr hsCon
        convUnsupported $  "creating a record with the " ++ what
                        ++ " constructor `" ++ T.unpack hsConStr ++ "'"
  
  con <- var ExprNS hsCon
  
  use (constructorFields . at con) >>= \case
    Just (RecordFields conFields) -> do
      let defaultVal field | isJust rec_dotdot = Var field
                           | otherwise         = MissingValue
      
      vals <- fmap M.fromList . for rec_flds $ \(L _ (HsRecField (L _ hsField) hsVal pun)) -> do
                field <- var ExprNS hsField
                val   <- if pun
                         then pure $ Var field
                         else convertLExpr hsVal
                pure (field, val)
      pure . appList (Var con)
           $ map (\field -> PosArg $ M.findWithDefault (defaultVal field) field vals) conFields
    
    Just (NonRecordFields count)
      | null rec_flds && isNothing rec_dotdot ->
        pure . appList (Var con) $ replicate count (PosArg MissingValue)
      
      | otherwise ->
        recConUnsupported "non-record"
    
    Nothing -> recConUnsupported "unknown"

convertExpr (RecordUpd recVal HsRecFields{..} _cons _PlaceHolders1 _PlaceHolders2) = do
  when (isJust rec_dotdot) $ convUnsupported "invalid wildcard in record updates"
  when (null rec_flds)     $ convUnsupported "invalid empty record updates"
  
  updates <- fmap M.fromList . for rec_flds $ \(L _ HsRecField{..}) -> do
               field <- var ExprNS $ unLoc hsRecFieldId
               pure (field, if hsRecPun then Nothing else Just hsRecFieldArg)
  
  recType <- S.minView . S.fromList <$> traverse (\field -> use $ recordFieldTypes . at field) (M.keys updates) >>= \case
               Just (Just recType, []) -> pure recType
               Just (Nothing,      []) -> convUnsupported "invalid non-record-field record updates"
               _                       -> convUnsupported "invalid mixed-data-type record updates"
  
  ctors   <- maybe (convUnsupported "invalid unknown record type") pure =<< use (constructors . at recType)
  
  let loc  = mkGeneralLocated "generated"
      toHs = mkVarUnqual . fsLit . T.unpack

  let partialUpdateError con =
        GHC.Match { m_fun_id_infix = Nothing
                  , m_pats         = [ loc . ConPatIn (loc $ toHs con)
                                           . RecCon $ HsRecFields { rec_flds = []
                                                                  , rec_dotdot = Nothing } ]
                  , m_type         = Nothing
                  , m_grhss        = GRHSs { grhssGRHSs = [ loc . GRHS [] . loc $
                                                            -- TODO: A special variable which is special-cased to desugar to `MissingValue`?
                                                            HsApp (loc . HsVar . mkVarUnqual $ fsLit "error")
                                                                  (loc . HsLit . HsString "" $ fsLit "Partial record update") ]
                                           , grhssLocalBinds = EmptyLocalBinds } }
  
  matches <- for ctors $ \con ->
    use (constructorFields . at con) >>= \case
      Just (RecordFields fields) | all (`elem` fields) $ M.keysSet updates -> do
        let useFields fields = HsRecFields {rec_flds = fields, rec_dotdot = Nothing}
        (fieldPats, fieldVals) <- fmap (bimap useFields useFields . unzip) . for fields $ \field -> do
          fieldVar <- gensym field
          let mkField arg = loc $ HsRecField { hsRecFieldId  = loc $ toHs field
                                             , hsRecFieldArg = arg
                                             , hsRecPun      = False }
           
          pure ( mkField . loc . GHC.VarPat $ toHs fieldVar
               , mkField . fromMaybe (loc . HsVar $ toHs field) -- NOT `fieldVar` – this was punned
                         $ M.findWithDefault (Just . loc . HsVar $ toHs fieldVar) field updates )
        
        pure GHC.Match { m_fun_id_infix = Nothing
                       , m_pats         = [ loc . ConPatIn (loc $ toHs con) $ RecCon fieldPats ]
                       , m_type         = Nothing
                       , m_grhss        = GRHSs { grhssGRHSs = [ loc . GRHS [] . loc $
                                                                 RecordCon (loc $ toHs con)
                                                                           (error "Forced fake `PostTcExpr'!")
                                                                           fieldVals ]
                                                , grhssLocalBinds = EmptyLocalBinds } }
        
      Just _ ->
        pure $ partialUpdateError con
      Nothing ->
        convUnsupported "invalid unknown constructor in record update"
  
  convertExpr . HsCase recVal $ MG { mg_alts    = map loc matches
                                   , mg_arg_tys = []
                                   , mg_res_ty  = PlaceHolder
                                   , mg_origin  = Generated }


convertExpr (ExprWithTySig e ty PlaceHolder) =
  HasType <$> convertLExpr e <*> convertLType ty

convertExpr (ExprWithTySigOut _ _) =
  convUnsupported "`ExprWithTySigOut' constructor"

convertExpr (ArithSeq _ _ _) =
  convUnsupported "arithmetic sequences"

convertExpr (PArrSeq _ _) =
  convUnsupported "parallel array arithmetic sequences"

convertExpr (HsSCC _ _ e) =
  convertLExpr e

convertExpr (HsCoreAnn _ _ e) =
  convertLExpr e

convertExpr (HsBracket _) =
  convUnsupported "Template Haskell brackets"

convertExpr (HsRnBracketOut _ _) =
  convUnsupported "`HsRnBracketOut' constructor"

convertExpr (HsTcBracketOut _ _) =
  convUnsupported "`HsTcBracketOut' constructor"

convertExpr (HsSpliceE _ _) =
  convUnsupported "Template Haskell expression splices"

convertExpr (HsQuasiQuoteE _) =
  convUnsupported "expression quasiquoters"

convertExpr (HsProc _ _) =
  convUnsupported "`proc' expressions"

convertExpr (HsStatic _) =
  convUnsupported "static pointers"

convertExpr (HsArrApp _ _ _ _ _) =
  convUnsupported "arrow application command"

convertExpr (HsArrForm _ _ _) =
  convUnsupported "arrow command formation"

convertExpr (HsTick _ e) =
  convertLExpr e

convertExpr (HsBinTick _ _ e) =
  convertLExpr e

convertExpr (HsTickPragma _ _ e) =
  convertLExpr e

convertExpr EWildPat =
  convUnsupported "wildcard pattern in expression"

convertExpr (EAsPat _ _) =
  convUnsupported "as-pattern in expression"

convertExpr (EViewPat _ _) =
  convUnsupported "view-pattern in expression"

convertExpr (ELazyPat _) =
  convUnsupported "lazy pattern in expression"

convertExpr (HsType ty) =
  convertLType ty

convertExpr (HsWrap _ _) =
  convUnsupported "`HsWrap' constructor"

convertExpr (HsUnboundVar x) =
  Var <$> freeVar x

--------------------------------------------------------------------------------

-- Module-local
convert_section :: (ConversionMonad m) => Maybe (LHsExpr RdrName) -> LHsExpr RdrName -> Maybe (LHsExpr RdrName) -> m Term
convert_section  ml opE mr = do
  let hs  = HsVar . mkVarUnqual . fsLit . T.unpack
      coq = Inferred Coq.Explicit . Ident
  
  arg <- gensym "arg"
  let orArg = fromMaybe (noLoc $ hs arg)
  Fun [coq arg] <$> convertExpr (OpApp (orArg ml) opE PlaceHolder (orArg mr))

--------------------------------------------------------------------------------

convertLExpr :: ConversionMonad m => LHsExpr RdrName -> m Term
convertLExpr = convertExpr . unLoc

--------------------------------------------------------------------------------

convertFunction :: ConversionMonad m => MatchGroup RdrName (LHsExpr RdrName) -> m (Binders, Term)
convertFunction mg = do
  eqns <- convertMatchGroup mg
  args <- case eqns of
            Equation (MultPattern args :| _) _ : _ ->
              traverse (const $ gensym "arg") args
            _ ->
              convUnsupported "empty `MatchGroup' in function"
  let argBinders = (Inferred Coq.Explicit . Ident) <$> args
      match      = Coq.Match (args <&> \arg -> MatchItem (Var arg) Nothing Nothing) Nothing eqns
  pure (argBinders, match)

--------------------------------------------------------------------------------

isTrueLExpr :: GhcMonad m => LHsExpr RdrName -> m Bool
isTrueLExpr (L _ (HsVar x))         = ((||) <$> (== "otherwise") <*> (== "True")) <$> ghcPpr x
isTrueLExpr (L _ (HsTick _ e))      = isTrueLExpr e
isTrueLExpr (L _ (HsBinTick _ _ e)) = isTrueLExpr e
isTrueLExpr (L _ (HsPar e))         = isTrueLExpr e
isTrueLExpr _                       = pure False

--------------------------------------------------------------------------------

-- TODO: Unify `buildTrivial` and `buildNontrivial`?
convertPatternBinding :: ConversionMonad m
                      => LPat RdrName -> LHsExpr RdrName
                      -> (Term -> (Term -> Term) -> m a)
                      -> (Term -> Ident -> (Term -> Term -> Term) -> m a)
                      -> Term
                      -> m a
convertPatternBinding hsPat hsExp buildTrivial buildNontrivial fallback = do
  pat <- convertLPat  hsPat
  exp <- convertLExpr hsExp
  
  refutability pat >>= \case
    Trivial tpat ->
      buildTrivial exp $ Fun [Inferred Coq.Explicit $ maybe UnderscoreName Ident tpat]
    
    nontrivial -> do
      cont <- gensym "cont"
      arg  <- gensym "arg"
      
      -- TODO: Use SSReflect's `let:` in the `SoleConstructor` case?
      -- (Involves adding a constructor to `Term`.)
      let fallbackMatches
            | SoleConstructor <- nontrivial = []
            | otherwise                     = [ Equation [MultPattern [UnderscorePat]] fallback ]

      buildNontrivial exp cont $ \body rest ->
        Let cont [Inferred Coq.Explicit $ Ident arg] Nothing
                 (Coq.Match [MatchItem (Var arg) Nothing Nothing] Nothing $ 
                   Equation [MultPattern [pat]] rest : fallbackMatches)
          body

convertDoBlock :: ConversionMonad m => [ExprLStmt RdrName] -> m Term
convertDoBlock allStmts = case fmap unLoc <$> unsnoc allStmts of
  Just (stmts, BodyStmt e _ _ _) -> foldMap (Endo . toExpr . unLoc) stmts `appEndo` convertLExpr e
  Just _                         -> convUnsupported "invalid malformed `do' block"
  Nothing                        -> convUnsupported "invalid empty `do' block"
  where
    toExpr (BodyStmt e _bind _guard _PlaceHolder) rest =
      Infix <$> convertLExpr e <*> pure ">>" <*> rest
    
    toExpr (BindStmt pat exp _bind _fail) rest =
      convertPatternBinding
        pat exp
        (\exp' fun          -> Infix exp' ">>=" . fun <$> rest)
        (\exp' cont letCont -> letCont (Infix exp' ">>=" (Var cont)) <$> rest)
        (Var "fail" `App1` String "Partial pattern match in `do' notation")
    
    toExpr (LetStmt binds) rest =
      convertLocalBinds binds rest
    
    toExpr (RecStmt{}) _ =
      convUnsupported "`rec' statements in `do` blocks"
    
    toExpr _ _ =
      convUnsupported "impossibly fancy `do' block statements"

convertListComprehension :: ConversionMonad m => [ExprLStmt RdrName] -> m Term
convertListComprehension allStmts = case fmap unLoc <$> unsnoc allStmts of
  Just (stmts, LastStmt e _) -> foldMap (Endo . toExpr . unLoc) stmts `appEndo`
                                  (Infix <$> (convertLExpr e) <*> pure "::" <*> pure (Var "nil"))
  Just _                     -> convUnsupported "invalid malformed list comprehensions"
  Nothing                    -> convUnsupported "invalid empty list comprehension"
  where
    toExpr (BodyStmt e _bind _guard _PlaceHolder) rest =
      isTrueLExpr e >>= \case
        True  -> rest
        False -> If <$> convertLExpr e <*> pure Nothing
                    <*> rest
                    <*> pure (Var "nil")
    
    toExpr (BindStmt pat exp _bind _fail) rest =
      convertPatternBinding
        pat exp
        (\exp' fun          -> App2 (Var "concatMap") <$> (fun <$> rest) <*> pure exp')
        (\exp' cont letCont -> letCont (App2 (Var "concatMap") (Var cont) exp') <$> rest)
        (Var "nil")
    
    toExpr (LetStmt binds) rest =
      convertLocalBinds binds rest
    
    toExpr _ _ =
      convUnsupported "impossibly fancy list comprehension conditions"

--------------------------------------------------------------------------------

convertMatchGroup :: ConversionMonad m => MatchGroup RdrName (LHsExpr RdrName) -> m [Equation]
convertMatchGroup (MG alts _ _ _) = traverse (convertMatch . unLoc) alts

convertMatch :: ConversionMonad m => Match RdrName (LHsExpr RdrName) -> m Equation
convertMatch GHC.Match{..} = do
  pats <- maybe (convUnsupported "no-pattern case arms") pure . nonEmpty
            =<< traverse convertLPat m_pats
  oty  <- traverse convertLType m_type
  rhs  <- convertGRHSs m_grhss
  pure . Equation [MultPattern pats] $ maybe id (flip HasType) oty rhs

--------------------------------------------------------------------------------

data ConvertedGuard m = OtherwiseGuard
                      | BoolGuard      Term
                      | PatternGuard   Pattern Term
                      | LetGuard       (m Term -> m Term)

convertGuard :: ConversionMonad m => [GuardLStmt RdrName] -> m [ConvertedGuard m]
convertGuard [] = pure []
convertGuard gs = collapseGuards <$> traverse (toCond . unLoc) gs where
  toCond (BodyStmt e _bind _guard _PlaceHolder) =
    isTrueLExpr e >>= \case
      True  -> pure OtherwiseGuard
      False -> BoolGuard <$> convertLExpr e
  toCond (LetStmt binds) =
    pure . LetGuard $ convertLocalBinds binds
  toCond (BindStmt pat exp _bind _fail) =
    PatternGuard <$> convertLPat pat <*> convertLExpr exp
  toCond _ =
    convUnsupported "impossibly fancy guards"

  -- TODO: Add multi-pattern-guard case
  addGuard g [] =
    [g]
  addGuard (BoolGuard cond') (BoolGuard cond : gs) =
    BoolGuard (App2 (Var "andb") cond' cond) : gs
  addGuard g' (g:gs) =
    g':g:gs
  addGuard _ _ =
    error "GHC BUG WORKAROUND: `OverloadedLists` confuses the exhaustiveness checker"
  
  collapseGuards = foldr addGuard []

-- Returns a function waiting for the next guard
guardTerm :: ConversionMonad m => [ConvertedGuard m] -> Term -> (Term -> m Term)
guardTerm gs guarded unguarded = go gs where
  go [] =
    pure guarded
  go (OtherwiseGuard : []) =
    pure guarded
  go (OtherwiseGuard : (_:_)) =
    convUnsupported "unused guards after an `otherwise' (or similar)"
  go (BoolGuard cond : gs) =
    If cond Nothing <$> go gs <*> pure unguarded
  go (PatternGuard pat exp : gs) = do
    guarded' <- go gs
    pure $ Coq.Match [MatchItem exp Nothing Nothing] Nothing
                     [ Equation [MultPattern [pat]] guarded'
                     , Equation [MultPattern [UnderscorePat]] unguarded ]
  go (LetGuard bind : gs) =
    bind $ go gs
  go _ =
    error "GHC BUG WORKAROUND: `OverloadedLists` confuses the exhaustiveness checker"

--------------------------------------------------------------------------------

convertGuards :: ConversionMonad m => [([ConvertedGuard m],Term)] -> m Term
convertGuards [] = convUnsupported "empty lists of guarded statements"
convertGuards gs = foldrM (uncurry guardTerm) MissingValue gs
-- TODO: We could support enhanced fallthrough if we detected more
-- `MissingValue` cases, e.g.
--
--     foo (Con1 x y) | rel x y = rhs1
--     foo other                = rhs2
--
-- Right now, this doesn't catch the fallthrough.  Oh well!

convertGRHS :: ConversionMonad m => GRHS RdrName (LHsExpr RdrName) -> m ([ConvertedGuard m],Term)
convertGRHS (GRHS gs rhs) = (,) <$> convertGuard gs <*> convertLExpr rhs

convertLGRHSList :: ConversionMonad m => [LGRHS RdrName (LHsExpr RdrName)] -> m Term
convertLGRHSList = convertGuards <=< traverse (convertGRHS . unLoc)

convertGRHSs :: ConversionMonad m => GRHSs RdrName (LHsExpr RdrName) -> m Term
convertGRHSs GRHSs{..} = convertLocalBinds grhssLocalBinds $ convertLGRHSList grhssGRHSs

--------------------------------------------------------------------------------

convertTypedBinding :: ConversionMonad m => Maybe Term -> HsBind RdrName -> m ConvertedBinding
convertTypedBinding _convHsTy VarBind{}    = convUnsupported "[internal] `VarBind'"
convertTypedBinding _convHsTy AbsBinds{}   = convUnsupported "[internal?] `AbsBinds'"
convertTypedBinding _convHsTy PatSynBind{} = convUnsupported "pattern synonym bindings"
convertTypedBinding _convHsTy PatBind{..}  = -- TODO use `_convHsTy`?
  ConvertedPatternBinding <$> convertLPat pat_lhs <*> convertGRHSs pat_rhs
convertTypedBinding  convHsTy FunBind{..}  = do
  (name, opName) <- freeVar (unLoc fun_id) <&> \case
                      name | identIsVariable name -> (name,            Nothing)
                           | otherwise            -> (infixToCoq name, Just name)
  
  let (tvs, coqTy) =
        -- The @forall@ed arguments need to be brought into scope
        let peelForall (Forall tvs body) = first (NEL.toList tvs ++) $ peelForall body
            peelForall ty                = ([], ty)
        in maybe ([], Nothing) (second Just . peelForall) convHsTy
  
  defn <-
    if all (null . m_pats . unLoc) $ mg_alts fun_matches
    then case mg_alts fun_matches of
           [L _ (GHC.Match _ [] mty grhss)] ->
             maybe (pure id) (fmap (flip HasType) . convertLType) mty <*> convertGRHSs grhss
           _ ->
             convUnsupported "malformed multi-match variable definitions"
    else do
      (argBinders, match) <- convertFunction fun_matches
      pure $ let bodyVars = getFreeVars match
             in if name `S.member` bodyVars || maybe False (`S.member` bodyVars) opName
                then Fix . FixOne $ FixBody name argBinders Nothing Nothing match -- TODO recursion and binary operators
                else Fun argBinders match
  
  pure . ConvertedDefinitionBinding $ ConvertedDefinition name tvs coqTy defn opName

--------------------------------------------------------------------------------

-- TODO mutual recursion :-(
convertTypedBindings :: ConversionMonad m
                     => [HsBind RdrName] -> Map Ident Signature
                     -> (ConvertedBinding -> m a)
                     -> Maybe (HsBind RdrName -> GhcException -> m a)
                     -> m [a]
convertTypedBindings defns sigs build mhandler =
  let processed defn = maybe id (ghandle . ($ defn)) mhandler . (build =<<)
  in for defns $ \defn -> do
       ty <- case defn of
               FunBind{fun_id = L _ hsName} ->
                 fmap sigType . (`M.lookup` sigs) <$> var ExprNS hsName
               _ ->
                 pure Nothing
       processed defn $ convertTypedBinding ty defn

--------------------------------------------------------------------------------

convertLocalBinds :: ConversionMonad m => HsLocalBinds RdrName -> m Term -> m Term
convertLocalBinds (HsValBinds (ValBindsIn binds lsigs)) body = localizeConversionState $ do
  sigs     <- convertLSigs lsigs
  convDefs <- convertTypedBindings (map unLoc . bagToList $ binds) sigs pure Nothing
  sequence_ $ mapMaybe (withConvertedBinding (withConvertedDefinitionOp $ rename ExprNS)
                                             (\_ _ -> Nothing))
                       convDefs
  let matchLet pat term body = Coq.Match [MatchItem term Nothing Nothing] Nothing
                                         [Equation [MultPattern [pat]] body]
  (foldr (withConvertedBinding (withConvertedDefinitionDef Let) matchLet) ?? convDefs) <$> body
convertLocalBinds (HsValBinds (ValBindsOut _ _)) _ =
  convUnsupported "post-renaming `ValBindsOut' bindings"
convertLocalBinds (HsIPBinds _) _ =
  convUnsupported "local implicit parameter bindings"
convertLocalBinds EmptyLocalBinds body =
  body
