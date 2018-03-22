{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             FlexibleContexts, RankNTypes, ScopedTypeVariables,
             ViewPatterns, MultiWayIf  #-}

module HsToCoq.ConvertHaskell.Expr (
  -- * Expressions
  convertExpr, convertLExpr,
  -- * Bindings
  convertLocalBinds,
  -- ** Generic
  convertTypedBindings, convertTypedModuleBindings, convertTypedBinding,
  -- * Functions, matches, and guards
  -- ** Functions
  convertFunction,
  -- ** Matches
  convertMatchGroup, convertMatch,
  -- ** `do' blocks and similar
  convertDoBlock, convertListComprehension,
  convertPatternBinding,
  ) where

import Control.Lens

import Data.Bifunctor
import Data.Traversable
import Data.Maybe
import Data.List (intercalate)
import HsToCoq.Util.List hiding (unsnoc)
import Data.List.NonEmpty (nonEmpty, NonEmpty)
import qualified Data.List.NonEmpty as NEL
import qualified HsToCoq.Util.List as NEL ((|>))
import Data.Text (Text)
import qualified Data.Text as T

import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Monad.Writer

import           Data.Map.Strict (Map)
import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import GHC hiding (Name, HsChar, HsString, AsPat)
import qualified GHC
import Bag
import BasicTypes
import HsToCoq.Util.GHC.FastString
import RdrName
import HsToCoq.Util.GHC.Exception

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.Name hiding (Name)
import HsToCoq.Util.GHC.HsExpr
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Rewrite as Coq
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Literals
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Pattern
import HsToCoq.ConvertHaskell.Sigs

--------------------------------------------------------------------------------

convertExpr :: ConversionMonad m => HsExpr GHC.Name -> m Term
convertExpr hsExpr = do
  rws <- use (edits.rewrites)
  Coq.rewrite rws <$> convertExpr' hsExpr

convertExpr' :: ConversionMonad m => HsExpr GHC.Name -> m Term
convertExpr' (HsVar (L _ x)) =
  Qualid <$> var ExprNS x

convertExpr' (HsUnboundVar x) =
  Var <$> freeVar (unboundVarOcc x)

convertExpr' (HsRecFld fld) =
  Qualid <$> recordField fld

convertExpr' (HsOverLabel _) =
  convUnsupported "overloaded labels"

convertExpr' (HsIPVar _) =
  convUnsupported "implicit parameters"

convertExpr' (HsOverLit OverLit{..}) =
  case ol_val of
    HsIntegral   _src int -> App1 "GHC.Num.fromInteger" . Num <$> convertInteger "integer literals" int
    HsFractional fr  -> convertFractional fr
    HsIsString   _src str -> pure $ convertFastString str

convertExpr' (HsLit lit) =
  case lit of
    GHC.HsChar   _ c       -> pure $ HsChar c
    HsCharPrim   _ _       -> convUnsupported "`Char#' literals"
    GHC.HsString _ fs      -> pure $ convertFastString fs
    HsStringPrim _ _       -> convUnsupported "`Addr#' literals"
    HsInt        _ int     -> Num <$> convertInteger "`Integer' literals" int
    HsIntPrim    _ int     -> Num <$> convertInteger "`Integer' literals" int
    HsWordPrim   _ _       -> convUnsupported "`Word#' literals"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literals"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literals"
    HsInteger    _ int _ty -> Num <$> convertInteger "`Integer' literals" int
    HsRat        _ _       -> convUnsupported "`Rational' literals"
    HsFloatPrim  _         -> convUnsupported "`Float#' literals"
    HsDoublePrim _         -> convUnsupported "`Double#' literals"

convertExpr' (HsLam mg) =
  uncurry Fun <$> convertFunction mg

convertExpr' (HsLamCase PlaceHolder mg) =
  uncurry Fun <$> convertFunction mg

convertExpr' (HsApp e1 e2) =
  App1 <$> convertLExpr e1 <*> convertLExpr e2

convertExpr' (HsAppType e1 _) =
  convertLExpr e1
--  convUnsupported "type applications"
--  SCW: just ignore them for now, and let the user figure it out.

convertExpr' (HsAppTypeOut _ _) =
  convUnsupported "`HsAppTypeOut' constructor"

convertExpr' (OpApp el eop _fixity er) =
  case eop of
    L _ (HsVar (L _ hsOp)) -> do
      op <- var ExprNS hsOp
      l  <- convertLExpr el
      r  <- convertLExpr er
      pure $ if
        | qualidIsOp op -> Infix l op r
        | otherwise     -> App2 (Qualid op) l r
    _ ->
      convUnsupported "non-variable infix operators"

convertExpr' (NegApp e1 _) =
  App1 <$> pure "GHC.Num.negate" <*> convertLExpr e1

convertExpr' (HsPar e) =
  Parens <$> convertLExpr e

convertExpr' (SectionL l opE) =
  convert_section (Just l) opE Nothing

convertExpr' (SectionR opE r) =
  convert_section Nothing opE (Just r)

-- TODO: Mark converted unboxed tuples specially?
convertExpr' (ExplicitTuple exprs _boxity) = do
  -- TODO A tuple constructor in the Gallina grammar?
  (tuple, args) <- runWriterT
                .  fmap (foldl1 . App2 $ "pair")
                .  for exprs $ unLoc <&> \case
                     Present e           -> lift $ convertLExpr e
                     Missing PlaceHolder -> do arg <- lift (genqid "arg")
                                               Qualid arg <$ tell [arg]
  pure $ maybe id Fun (nonEmpty $ map (Inferred Coq.Explicit . Ident) args) tuple

convertExpr' (HsCase e mg) = do
  scrut <- convertLExpr e
  bindIn "scrut" scrut $ \scrut -> convertMatchGroup [scrut] mg

convertExpr' (HsIf overloaded c t f) =
  if maybe True isNoSyntaxExpr overloaded
  then ifThenElse <*> convertLExpr c <*> convertLExpr t <*> convertLExpr f
  else convUnsupported "overloaded if-then-else"

convertExpr' (HsMultiIf PlaceHolder lgrhsList) =
  convertLGRHSList [] lgrhsList patternFailure

convertExpr' (HsLet (L _ binds) body) =
  convertLocalBinds binds $ convertLExpr body

convertExpr' (HsDo sty (L _ stmts) PlaceHolder) =
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

convertExpr' (ExplicitList PlaceHolder overloaded exprs) =
  if maybe True isNoSyntaxExpr overloaded
  then foldr (App2 "cons") "nil" <$> traverse convertLExpr exprs
  else convUnsupported "overloaded lists"

convertExpr' (ExplicitPArr _ _) =
  convUnsupported "explicit parallel arrays"

-- TODO: Unify with the `RecCon` case in `ConPatIn` for `convertPat` (in
-- `HsToCoq.ConvertHaskell.Pattern`)
convertExpr' (RecordCon (L _ hsCon) PlaceHolder conExpr HsRecFields{..}) = do
  unless (isNoPostTcExpr conExpr) $
    convUnsupported "unexpected post-typechecker record constructor"

  let recConUnsupported what = do
        hsConStr <- ghcPpr hsCon
        convUnsupported $  "creating a record with the " ++ what
                        ++ " constructor `" ++ T.unpack hsConStr ++ "'"

  con <- var ExprNS hsCon

  use (constructorFields . at con) >>= \case
    Just (RecordFields conFields) -> do
      let defaultVal field | isJust rec_dotdot = Qualid field
                           | otherwise         = missingValue

      vals <- fmap M.fromList . for rec_flds $ \(L _ (HsRecField (L _ (FieldOcc _userField hsField)) hsVal pun)) -> do
                field <- var ExprNS hsField
                val   <- if pun
                         then pure $ Qualid field
                         else convertLExpr hsVal
                pure (field, val)
      pure . appList (Qualid con)
           $ map (\field -> PosArg $ M.findWithDefault (defaultVal field) field vals) conFields

    Just (NonRecordFields count)
      | null rec_flds && isNothing rec_dotdot ->
        pure . appList (Qualid con) $ replicate count (PosArg missingValue)

      | otherwise ->
        recConUnsupported "non-record"

    Nothing -> recConUnsupported "unknown"

convertExpr' (RecordUpd recVal fields PlaceHolder PlaceHolder PlaceHolder PlaceHolder) = do
  updates <- fmap M.fromList . for fields $ \(L _ HsRecField{..}) -> do
               field <- recordField $ unLoc hsRecFieldLbl
               pure (field, if hsRecPun then Nothing else Just hsRecFieldArg)

  let updFields       = M.keys updates
      prettyUpdFields what =
        let quote f = "`" ++ T.unpack (qualidToIdent f) ++ "'"
        in what ++ case assertUnsnoc updFields of
                     ([],   f)  -> " "  ++ quote f
                     ([f1], f2) -> "s " ++ quote f1                        ++ " and "  ++ quote f2
                     (fs,   f') -> "s " ++ intercalate ", " (map quote fs) ++ ", and " ++ quote f'

  recType <- S.minView . S.fromList <$> traverse (\field -> use $ recordFieldTypes . at field) updFields >>= \case
               Just (Just recType, []) -> pure recType
               Just (Nothing,      []) -> convUnsupported $ "invalid record update with " ++ prettyUpdFields "non-record-field"
               _                       -> convUnsupported $ "invalid mixed-data-type record updates with " ++ prettyUpdFields "the given field"

  ctors :: [Qualid]  <- maybe (convUnsupported "invalid unknown record type") pure =<< use (constructors . at recType)

  let loc  = mkGeneralLocated "generated"
      toHs = freshInternalName . T.unpack

  let partialUpdateError con = do
        hsCon   <- toHs (qualidToIdent con)
        hsError <- freshInternalName "error" -- TODO RENAMER this shouldn't be fresh
        pure $ GHC.Match
          { m_fixity = NonFunBindMatch
          , m_pats   = [ loc . ConPatIn (loc hsCon)
                             . RecCon $ HsRecFields { rec_flds = []
                                                    , rec_dotdot = Nothing } ]
          , m_type   = Nothing
          , m_grhss  = GRHSs { grhssGRHSs = [ loc . GRHS [] . loc $
                                              -- TODO: A special variable which is special-cased to desugar to `missingValue`?
                                              HsApp (loc . HsVar . loc $ hsError)
                                                    (loc . HsLit . GHC.HsString "" $ fsLit "Partial record update") ]
                             , grhssLocalBinds = loc EmptyLocalBinds } }

  matches <- for ctors $ \con ->
    use (constructorFields . at con) >>= \case
      Just (RecordFields fields) | all (`elem` fields) $ M.keysSet updates -> do
        let addFieldOcc :: HsRecField' GHC.Name arg -> HsRecField GHC.Name arg
            addFieldOcc field@HsRecField{hsRecFieldLbl = L s lbl} =
              let rdrLbl     = mkOrig <$> nameModule <*> nameOccName $ lbl
              in field{hsRecFieldLbl = L s $ FieldOcc (L s rdrLbl) lbl}
            useFields fields = HsRecFields { rec_flds   = map (fmap addFieldOcc) fields
                                           , rec_dotdot = Nothing }
        (fieldPats, fieldVals) <- fmap (bimap useFields useFields . unzip) . for fields $ \field -> do
          fieldVar   <- gensym (qualidBase field)
          hsField    <- toHs (qualidToIdent field)
          hsFieldVar <- toHs fieldVar
          let mkField arg = loc $ HsRecField { hsRecFieldLbl = loc hsField
                                             , hsRecFieldArg = arg
                                             , hsRecPun      = False }
          pure ( mkField . loc . GHC.VarPat . loc $ hsFieldVar
               , mkField . fromMaybe (loc . HsVar $ loc hsField) -- NOT `fieldVar` – this was punned
                         $ M.findWithDefault (Just . loc . HsVar $ loc hsFieldVar) field updates )

        hsCon <- toHs (qualidToIdent con)
        pure GHC.Match { m_fixity = NonFunBindMatch
                       , m_pats   = [ loc . ConPatIn (loc hsCon) $ RecCon fieldPats ]
                       , m_type   = Nothing
                       , m_grhss  = GRHSs { grhssGRHSs = [ loc . GRHS [] . loc $
                                                           RecordCon (loc hsCon)
                                                                     PlaceHolder
                                                                     noPostTcExpr
                                                                     fieldVals ]
                                          , grhssLocalBinds = loc EmptyLocalBinds } }

      Just _ ->
        partialUpdateError con
      Nothing ->
        convUnsupported "invalid unknown constructor in record update"

  convertExpr . HsCase recVal $ MG { mg_alts    = loc $ map loc matches
                                   , mg_arg_tys = []
                                   , mg_res_ty  = PlaceHolder
                                   , mg_origin  = Generated }


convertExpr' (ExprWithTySig e sigWcTy) =
  HasType <$> convertLExpr e <*> convertLHsSigWcType sigWcTy

convertExpr' (ExprWithTySigOut e sigWcTy) =
  HasType <$> convertLExpr e <*> convertLHsSigWcType sigWcTy

convertExpr' (ArithSeq _postTc _overloadedLists info) =
  -- TODO: Special-case infinite lists?
  -- TODO: `enumFrom{,Then}{,To}` is really…?
  -- TODO: Add Coq syntax sugar?  Something like
  --
  --     Notation "[ :: from        '..' ]"    := (enumFrom       from).
  --     Notation "[ :: from , next '..' ]"    := (enumFromThen   from next).
  --     Notation "[ :: from        '..' to ]" := (enumFromTo     from      to).
  --     Notation "[ :: from , next '..' to ]" := (enumFromThenTo from next to).
  --
  -- Only `'..'` doesn't work for some reason.
  case info of
    From       low           -> App1 "enumFrom"       <$> convertLExpr low
    FromThen   low next      -> App2 "enumFromThen"   <$> convertLExpr low <*> convertLExpr next
    FromTo     low      high -> App2 "enumFromTo"     <$> convertLExpr low                       <*> convertLExpr high
    FromThenTo low next high -> App3 "enumFromThenTo" <$> convertLExpr low <*> convertLExpr next <*> convertLExpr high

convertExpr' (PArrSeq _ _) =
  convUnsupported "parallel array arithmetic sequences"

convertExpr' (HsSCC _ _ e) =
  convertLExpr e

convertExpr' (HsCoreAnn _ _ e) =
  convertLExpr e

convertExpr' (HsBracket _) =
  convUnsupported "Template Haskell brackets"

convertExpr' (HsRnBracketOut _ _) =
  convUnsupported "`HsRnBracketOut' constructor"

convertExpr' (HsTcBracketOut _ _) =
  convUnsupported "`HsTcBracketOut' constructor"

convertExpr' (HsSpliceE _) =
  convUnsupported "Quasiquoters and Template Haskell splices"

convertExpr' (HsProc _ _) =
  convUnsupported "`proc' expressions"

convertExpr' (HsStatic _) =
  convUnsupported "static pointers"

convertExpr' (HsArrApp _ _ _ _ _) =
  convUnsupported "arrow application command"

convertExpr' (HsArrForm _ _ _) =
  convUnsupported "arrow command formation"

convertExpr' (HsTick _ e) =
  convertLExpr e

convertExpr' (HsBinTick _ _ e) =
  convertLExpr e

convertExpr' (HsTickPragma _ _ _ e) =
  convertLExpr e

convertExpr' EWildPat =
  convUnsupported "wildcard pattern in expression"

convertExpr' (EAsPat _ _) =
  convUnsupported "as-pattern in expression"

convertExpr' (EViewPat _ _) =
  convUnsupported "view-pattern in expression"

convertExpr' (ELazyPat _) =
  convUnsupported "lazy pattern in expression"

convertExpr' (HsWrap _ _) =
  convUnsupported "`HsWrap' constructor"

--------------------------------------------------------------------------------

-- Module-local
convert_section :: ConversionMonad m => Maybe (LHsExpr GHC.Name) -> LHsExpr GHC.Name -> Maybe (LHsExpr GHC.Name) -> m Term
convert_section  ml opE mr = do
  let -- We need this type signature, and I think it's because @let@ isn't being
      -- generalized.
      hs :: ConversionMonad m => Qualid -> m (HsExpr GHC.Name)
      hs  = fmap (HsVar . mkGeneralLocated "generated") . freshInternalName . T.unpack . qualidToIdent
      coq = Inferred Coq.Explicit . Ident

  arg <- Bare <$> gensym "arg"
  let orArg = maybe (fmap noLoc $ hs arg) pure
  l <- orArg ml
  r <- orArg mr
  -- TODO RENAMER look up fixity?
  Fun [coq arg] <$> convertExpr (OpApp l opE defaultFixity r)

--------------------------------------------------------------------------------

convertLExpr :: ConversionMonad m => LHsExpr GHC.Name -> m Term
convertLExpr = convertExpr . unLoc

--------------------------------------------------------------------------------

convertFunction :: ConversionMonad m => MatchGroup GHC.Name (LHsExpr GHC.Name) -> m (Binders, Term)
convertFunction mg | Just alt <- isTrivialMatch mg = convTrivialMatch alt
convertFunction mg = do
  let n_args = matchGroupArity mg
  args <- replicateM n_args (genqid "arg") >>= maybe err pure . nonEmpty
  let argBinders = (Inferred Coq.Explicit . Ident) <$> args
  match <- convertMatchGroup (Qualid <$> args) mg
  pure (argBinders, match)
 where
   err = convUnsupported "convertFunction: Empty argument list"

isTrivialMatch :: MatchGroup GHC.Name (LHsExpr GHC.Name) -> Maybe (Match GHC.Name (LHsExpr GHC.Name))
isTrivialMatch (MG (L _ [L _ alt]) _ _ _) = trivMatch alt where

  trivMatch :: Match GHC.Name (LHsExpr GHC.Name) ->
    Maybe (Match GHC.Name (LHsExpr GHC.Name))
  trivMatch alt = if all trivPat (m_pats alt) then Just alt else Nothing

  trivPat :: LPat GHC.Name -> Bool
  trivPat (L _ (GHC.WildPat _)) = False
  trivPat (L _ (GHC.VarPat _))  = True
  trivPat (L _ (GHC.BangPat p)) = trivPat p
  trivPat (L _ (GHC.LazyPat p)) = trivPat p
  trivPat (L _ (GHC.ParPat  p)) = trivPat p
  trivPat _                     = False
isTrivialMatch _ = Nothing

convTrivialMatch ::  ConversionMonad m =>
  Match GHC.Name (LHsExpr GHC.Name) ->  m (Binders, Term)
convTrivialMatch alt = do
  (MultPattern pats, _, rhs) <- convertMatch alt
  names <- mapM patToName pats
  let argBinders = (Inferred Coq.Explicit) <$> names
  body <- rhs patternFailure
  return (argBinders, body)


patToName :: ConversionMonad m => Pattern -> m Name
patToName UnderscorePat    = return UnderscoreName
patToName (QualidPat qid)  = return $ Ident qid
patToName _                = convUnsupported "patToArg: not a trivial pat"

--------------------------------------------------------------------------------

isTrueLExpr :: GhcMonad m => LHsExpr GHC.Name -> m Bool
isTrueLExpr (L _ (HsVar x))         = ((||) <$> (== "otherwise") <*> (== "True")) <$> ghcPpr x
isTrueLExpr (L _ (HsTick _ e))      = isTrueLExpr e
isTrueLExpr (L _ (HsBinTick _ _ e)) = isTrueLExpr e
isTrueLExpr (L _ (HsPar e))         = isTrueLExpr e
isTrueLExpr _                       = pure False

--------------------------------------------------------------------------------

-- TODO: Unify `buildTrivial` and `buildNontrivial`?
convertPatternBinding :: ConversionMonad m
                      => LPat GHC.Name -> LHsExpr GHC.Name
                      -> (Term -> (Term -> Term) -> m a)
                      -> (Term -> Qualid -> (Term -> Term -> Term) -> m a)
                      -> Term
                      -> m a
convertPatternBinding hsPat hsExp buildTrivial buildNontrivial fallback = do
  (pat, guards) <- runWriterT $ convertLPat hsPat
  exp <- convertLExpr hsExp

  ib <- ifThenElse

  refutability pat >>= \case
    Trivial tpat | null guards ->
      buildTrivial exp $ Fun [Inferred Coq.Explicit $ maybe UnderscoreName Ident tpat]

    nontrivial -> do
      cont <- genqid "cont"
      arg  <- genqid "arg"

      -- TODO: Use SSReflect's `let:` in the `SoleConstructor` case?
      -- (Involves adding a constructor to `Term`.)
      let fallbackMatches
            | SoleConstructor <- nontrivial = []
            | otherwise                     = [ Equation [MultPattern [UnderscorePat]] fallback ]
          guarded tm | null guards = tm
                     | otherwise   = ib (foldr1 (App2 "andb") guards) tm fallback

      buildNontrivial exp cont $ \body rest ->
        Let cont [Inferred Coq.Explicit $ Ident arg] Nothing
                 (Coq.Match [MatchItem (Qualid arg) Nothing Nothing] Nothing $
                   Equation [MultPattern [pat]] (guarded rest) : fallbackMatches)
          body

convertDoBlock :: ConversionMonad m => [ExprLStmt GHC.Name] -> m Term
convertDoBlock allStmts = do
    case fmap unLoc <$> unsnoc allStmts of
      Just (stmts, lastStmt -> Just e) -> foldMap (Endo . toExpr . unLoc) stmts `appEndo` convertLExpr e
      Just _                           -> convUnsupported "invalid malformed `do' block"
      Nothing                          -> convUnsupported "invalid empty `do' block"
  where
    lastStmt (BodyStmt e _ _ _) = Just e
    lastStmt (LastStmt e _ _)   = Just e
    lastStmt _                  = Nothing

    toExpr (BodyStmt e _bind _guard _PlaceHolder) rest =
      monThen <$> convertLExpr e <*> rest

    toExpr (BindStmt pat exp _bind _fail PlaceHolder) rest =
      convertPatternBinding
        pat exp
        (\exp' fun          -> monBind exp' . fun <$> rest)
        (\exp' cont letCont -> letCont (monBind exp' (Qualid cont)) <$> rest)
        (missingValue `App1` HsString "Partial pattern match in `do' notation")

    toExpr (LetStmt (L _ binds)) rest =
      convertLocalBinds binds rest

    toExpr (RecStmt{}) _ =
      convUnsupported "`rec' statements in `do` blocks"

    toExpr _ _ =
      convUnsupported "impossibly fancy `do' block statements"

    monBind e1 e2 = Infix e1 "GHC.Base.>>=" e2
    monThen e1 e2 = Infix e1 "GHC.Base.>>"  e2

convertListComprehension :: ConversionMonad m => [ExprLStmt GHC.Name] -> m Term
convertListComprehension allStmts = case fmap unLoc <$> unsnoc allStmts of
  Just (stmts, LastStmt e _applicativeDoInfo _returnInfo) ->
    foldMap (Endo . toExpr . unLoc) stmts `appEndo`
      (App2 (Var "cons") <$> convertLExpr e <*> pure (Var "nil"))
  Just _ ->
    convUnsupported "invalid malformed list comprehensions"
  Nothing ->
    convUnsupported "invalid empty list comprehension"
  where
    toExpr (BodyStmt e _bind _guard _PlaceHolder) rest =
      isTrueLExpr e >>= \case
        True  -> rest
        False -> ifThenElse <*> convertLExpr e
                            <*> rest
                            <*> pure (Var "nil")

    -- TODO: `concatMap` is really…?
    toExpr (BindStmt pat exp _bind _fail PlaceHolder) rest =
      convertPatternBinding
        pat exp
        (\exp' fun          -> App2 concatMapT <$> (fun <$> rest) <*> pure exp')
        (\exp' cont letCont -> letCont (App2 concatMapT (Qualid cont) exp') <$> rest)
        (Var "nil")

    toExpr (LetStmt (L _ binds)) rest =
      convertLocalBinds binds rest

    toExpr _ _ =
      convUnsupported "impossibly fancy list comprehension conditions"

    concatMapT :: Term
    concatMapT = "Coq.Lists.List.flat_map"

--------------------------------------------------------------------------------

-- Could this pattern be considered a 'catch all' or exhaustive pattern?
isWildCoq :: Pattern -> Bool
isWildCoq UnderscorePat     = True
isWildCoq (QualidPat _)     = True
isWildCoq (AsPat p _)       = isWildCoq p
isWildCoq (ArgsPat qid nep) = qid == (Bare "pair") && all isWildCoq nep
isWildCoq _ = False


{-
  = ArgsPat Qualid (NE.NonEmpty Pattern)
  | ExplicitArgsPat Qualid (NE.NonEmpty Pattern)
  | InfixPat Pattern Op Pattern
  | AsPat Pattern Ident
  | InScopePat Pattern Ident
  | QualidPat Qualid
  | UnderscorePat
  | NumPat HsToCoq.Coq.Gallina.Num
  | StringPat T.Text
  | OrPats (NE.NonEmpty OrPattern)
-}

-- This function, used by both convertMatchGroup for the various matches,
-- as well as in convertMatch for the various guarded RHS, implements
-- fall-though semantics, by binding each item to a jump point and passing
-- the right failure jump target to the prevoius item.
chainFallThroughs :: ConversionMonad m =>
    [Term -> m Term] -> -- The matches, in syntax order
    Term -> -- The final failure value
    m Term
chainFallThroughs cases failure = go (reverse cases) failure where
   go (m:ls) next_case = do
      this_match <- m next_case
      bindIn "j" this_match $ \failure -> go ls failure
   go [] failure = pure failure


-- A match group contains multiple alternatives, and each can have guards, and
-- there is fall-through semantics. But often we know that if one pattern fall-through,
-- then the next pattern will not match. In that case, we want to bind them in the same
-- match-with clause, in the hope of obtaining a full pattern match
--
-- The plan is:
-- * Convert each alternative individually into a pair of a pattern and a RHS.
--   The RHS is a (shallow) function that takes the fall-through target.
--   This is done by convertMatch
-- * Group patterns that are mutually exclusive, and put them in match-with clauses.
--   Add a catch-all case if that group is not complete already.
-- * Chain these groups.
convertMatchGroup :: ConversionMonad m =>
    NonEmpty Term ->
    MatchGroup GHC.Name (LHsExpr GHC.Name) ->
    m Term
convertMatchGroup args (MG (L _ alts) _ _ _) = do
    convAlts <- mapM (convertMatch . unLoc) alts
    -- TODO: Group
    convGroups <- groupMatches convAlts

    let scrut = args <&> \arg -> MatchItem arg Nothing Nothing
    let matches = buildMatch scrut <$> convGroups

    chainFallThroughs matches patternFailure

data HasGuard = HasGuard | HasNoGuard

groupMatches :: forall m a. ConversionMonad m =>
    [(MultPattern, HasGuard, a)] -> m [[(MultPattern, a)]]
groupMatches pats = map (map snd) . go <$> mapM summarize pats
  where
    -- Gather some summary information on the alternatives
    --  - do they have guards
    --  - what is their PatternSummary
    summarize :: (MultPattern, HasGuard, a) -> m ([PatternSummary], HasGuard, (MultPattern, a))
    summarize (mp,hg,x) = do
        s <- multPatternSummary mp
        return (s,hg,(mp,x))

    go :: forall x. [([PatternSummary], HasGuard, x)] -> [[([PatternSummary], x)]]
    go [] = pure []
    go ((ps,hg,x):xs) = case go xs of
        -- Append to a group if it has no guard
        (g:gs) | HasNoGuard <- hg          -> ((ps,x):g)  : gs
        -- Append to a group, if mutually exclusive with all members
               | all (mutExcls ps . fst) g -> ((ps,x):g)  : gs
        -- Otherwise, start a new group
        gs                                 -> ((ps,x):[]) : gs


convertMatch :: ConversionMonad m =>
    Match GHC.Name (LHsExpr GHC.Name) -> -- the match
    m (MultPattern, HasGuard, Term -> m Term) -- the pattern, hasGuards, the right-hand side
convertMatch GHC.Match{..} = do
  (pats, guards) <- runWriterT $
    maybe (convUnsupported "no-pattern case arms") pure . nonEmpty
      =<< traverse convertLPat m_pats

  let extraGuards = map BoolGuard guards
  let rhs = convertGRHSs extraGuards m_grhss

  let hg | null extraGuards = hasGuards m_grhss
         | otherwise        = HasGuard

  return (MultPattern pats, hg, rhs)

buildMatch :: ConversionMonad m =>
    NonEmpty MatchItem -> [(MultPattern, Term -> m Term)] -> Term -> m Term
-- This short-cuts wildcard matches (avoid introducing a match-with alltogether)
buildMatch _ [(pats,mkRhs)] failure
    | isUnderscoreMultPattern pats = mkRhs failure
buildMatch scruts eqns failure = do
    -- Pass the failure
    eqns' <- forM eqns $ \(pat,mkRhs) -> (pat,) <$> mkRhs failure
    isComplete <- isCompleteMultiPattern (map fst eqns')
    pure $ Coq.Match scruts Nothing $
      [ Equation [pats] rhs | (pats, rhs) <- eqns' ] ++
      [ Equation [MultPattern (UnderscorePat <$ scruts)] failure | not isComplete ]
    -- Only add a catch-all clause if the the patterns can fail


--------------------------------------------------------------------------------

hasGuards :: GRHSs b e -> HasGuard
hasGuards (GRHSs [ L _ (GRHS [] _) ] _) = HasNoGuard
hasGuards _                             = HasGuard

convertGRHS :: ConversionMonad m
            => [ConvertedGuard m]
            -> GRHS GHC.Name (LHsExpr GHC.Name)
            -> Term -- failure
            -> m Term
convertGRHS extraGuards (GRHS gs rhs) failure = do
    convGuards <- (extraGuards ++) <$> convertGuard gs
    rhs <- convertLExpr rhs
    guardTerm convGuards rhs failure

convertLGRHSList :: ConversionMonad m
                 => [ConvertedGuard m]
                 -> [LGRHS GHC.Name (LHsExpr GHC.Name)]
                 -> Term
                 -> m Term
convertLGRHSList extraGuards lgrhs failure  = do
    let rhss = unLoc <$> lgrhs
    chainFallThroughs (convertGRHS extraGuards <$> rhss) failure

convertGRHSs :: ConversionMonad m
             => [ConvertedGuard m]
             -> GRHSs GHC.Name (LHsExpr GHC.Name)
             -> Term
             -> m Term
convertGRHSs extraGuards GRHSs{..} failure =
    convertLocalBinds (unLoc grhssLocalBinds) $
      convertLGRHSList extraGuards grhssGRHSs failure
--------------------------------------------------------------------------------

data ConvertedGuard m = OtherwiseGuard
                      | BoolGuard      Term
                      | PatternGuard   Pattern Term
                      | LetGuard       (m Term -> m Term)

convertGuard :: ConversionMonad m =>
    [GuardLStmt GHC.Name] -> m [ConvertedGuard m]
convertGuard [] = pure []
convertGuard gs = collapseGuards <$> traverse (toCond . unLoc) gs where
  toCond (BodyStmt e _bind _guard _PlaceHolder) =
    isTrueLExpr e >>= \case
      True  -> pure [OtherwiseGuard]
      False -> (:[]) . BoolGuard <$> convertLExpr e
  toCond (LetStmt (L _ binds)) =
    pure . (:[]) . LetGuard $ convertLocalBinds binds
  toCond (BindStmt pat exp _bind _fail PlaceHolder) = do
    (pat', guards) <- runWriterT $ convertLPat pat
    exp'           <- convertLExpr exp
    pure $ PatternGuard pat' exp' : map BoolGuard guards
  toCond _ =
    convUnsupported "impossibly fancy guards"

  -- We optimize the code a bit, and combine
  -- successive boolean guards with andb
  collapseGuards = foldr addGuard [] . concat

  -- TODO: Add multi-pattern-guard case
  addGuard g [] =
    [g]
  addGuard (BoolGuard cond') (BoolGuard cond : gs) =
    BoolGuard (App2 (Var "andb") cond' cond) : gs
  addGuard g' (g:gs) =
    g':g:gs


-- Returns a function waiting for the "else case"
guardTerm :: ConversionMonad m =>
    [ConvertedGuard m] ->
    Term -> -- The guarded expression
    Term -> -- the failure expression
    m Term
guardTerm gs rhs failure = go gs where
  go [] =
    pure rhs
  go (OtherwiseGuard : gs) =
    go gs

  -- A little innocent but useful hack: Detect the pattern
  --     | foo `seq` False = …
  -- And hard-code that it fails
  go (BoolGuard (App2 "GHC.Prim.seq" _ p) : gs) = go (BoolGuard p : gs)
  go (BoolGuard "false" : _) = pure failure

  go (BoolGuard cond : gs) =
    ifThenElse <*> pure cond <*> go gs <*> pure failure
  -- if the pattern is exhaustive, don't include an otherwise case
  go (PatternGuard pat exp : gs) | isWildCoq pat = do
    guarded' <- go gs
    pure $ Coq.Match [MatchItem exp Nothing Nothing] Nothing
                     [ Equation [MultPattern [pat]] guarded' ]
  go (PatternGuard pat exp : gs) = do
    guarded' <- go gs
    pure $ Coq.Match [MatchItem exp Nothing Nothing] Nothing
                     [ Equation [MultPattern [pat]] guarded'
                     , Equation [MultPattern [UnderscorePat]] failure ]
  go (LetGuard bind : gs) =
    bind $ go gs

--------------------------------------------------------------------------------

withCurrentDefinitionIfTopLevel :: ConversionMonad m => TopLevelFlag -> Qualid -> m a -> m a
withCurrentDefinitionIfTopLevel TopLevel name  = withCurrentDefinition name
withCurrentDefinitionIfTopLevel NotTopLevel _  = id

convertTypedBinding :: ConversionMonad m => TopLevelFlag -> Maybe Term -> HsBind GHC.Name -> m (Maybe ConvertedBinding)
convertTypedBinding _ _convHsTy VarBind{}     = convUnsupported "[internal] `VarBind'"
convertTypedBinding _ _convHsTy AbsBinds{}    = convUnsupported "[internal?] `AbsBinds'"
convertTypedBinding _ _convHsTy AbsBindsSig{} = convUnsupported "[internal?] `AbsBindsSig'"
convertTypedBinding _ _convHsTy PatSynBind{}  = convUnsupported "pattern synonym bindings"
convertTypedBinding _ _convHsTy PatBind{..}   = do -- TODO use `_convHsTy`?
  -- TODO: Respect `skipped'?
  -- TODO: what if we need to rename this definition? (i.e. for a class member)
  (pat, guards) <- runWriterT $ convertLPat pat_lhs
  Just . ConvertedPatternBinding pat <$> convertGRHSs (map BoolGuard guards) pat_rhs patternFailure
convertTypedBinding toplvl convHsTy FunBind{..}   = runMaybeT $ do
  name <- var ExprNS (unLoc fun_id)

  -- Skip it?
  guard . not =<< use (edits.skipped.contains name)

  withCurrentDefinitionIfTopLevel toplvl name $ do
    let (tvs, coqTy) =
          -- The @forall@ed arguments need to be brought into scope
          let peelForall (Forall tvs body) = first (NEL.toList tvs ++) $ peelForall body
              peelForall ty                = ([], ty)
          in maybe ([], Nothing) (second Just . peelForall) convHsTy

    defn <-
      if all (null . m_pats . unLoc) . unLoc $ mg_alts fun_matches
      then case unLoc $ mg_alts fun_matches of
             [L _ (GHC.Match _ [] mty grhss)] ->
               maybe (pure id) (fmap (flip HasType) . convertLType) mty <*> convertGRHSs [] grhss patternFailure
             _ ->
               convUnsupported "malformed multi-match variable definitions"
      else do
        whichFix <- use currentDefinition >>= \case
            Nothing -> pure $ Fix . FixOne
            Just n -> do
                use (edits.local_termination.at n.non M.empty.at (qualidBase name)) >>= \case
                    Just order -> pure $ wfFix order
                    Nothing    -> use (edits.termination.at n) >>= \case
                        Just Deferred |  n == name -> pure $ wfFix Deferred
                        _ -> pure $ Fix . FixOne
        (argBinders, match) <- convertFunction fun_matches
        pure $ let bodyVars = getFreeVars match
               in if name `S.member` bodyVars
                  then whichFix $ FixBody name argBinders Nothing Nothing match
                  else Fun argBinders match

    addScope <- maybe id (flip InScope) <$> use (edits.additionalScopes.at (SPValue, name))

    pure . ConvertedDefinitionBinding $ ConvertedDefinition name tvs coqTy (addScope defn)

wfFix :: TerminationArgument -> FixBody -> Term
wfFix Deferred (FixBody ident argBinders Nothing Nothing rhs)
 = App1 (Qualid deferredFixN) $ Fun (Inferred Explicit (Ident ident) NEL.<| argBinders ) rhs
  where
    deferredFixN = qualidMapBase (<> T.pack (show (NEL.length argBinders)))
        "GHC.DeferredFix.deferredFix"

wfFix (WellFounded order) (FixBody ident argBinders Nothing Nothing rhs)
 = appList (Qualid wfFixN) $ map PosArg
    [ rel
    , Fun argBinders measure
    , Underscore
    , Fun (argBinders NEL.|> Inferred Explicit (Ident ident)) rhs
    ]
  where
    wfFixN = qualidMapBase (<> T.pack (show (NEL.length argBinders)))
        "GHC.Wf.wfFix"
    (rel, measure) = case order of
        StructOrder _                   -> error "wfFix cannot handle structural recursion"
        MeasureOrder measure Nothing    -> ("Coq.Init.Peano.lt", measure)
        MeasureOrder measure (Just rel) -> (rel, measure)
        WFOrder rel arg                 -> (rel, Qualid arg)
wfFix _ _ = error "wfFix: cannot handle annotations or types"

--------------------------------------------------------------------------------

-- TODO mutual recursion :-(
convertTypedModuleBindings :: ConversionMonad m
                           => TopLevelFlag
                           -> [(Maybe ModuleName, HsBind GHC.Name)]
                           -> Map Qualid Signature
                           -> (ConvertedBinding -> m a)
                           -> Maybe (HsBind GHC.Name -> GhcException -> m a)
                           -> m [a]
convertTypedModuleBindings toplvl defns sigs build mhandler =
  fmap catMaybes . for defns $ \(mname, defn) ->
    maybeWithCurrentModule mname $ runMaybeT $ do
       let wrap = case mhandler of Just handler -> ghandle (\e ->  lift $ handler defn e)
                                   Nothing      -> id
       wrap $ do
         ty <- case defn of
                 FunBind{fun_id = L _ hsName} ->
                   fmap sigType . (`M.lookup` sigs) <$> var ExprNS hsName
                 _ ->
                   pure Nothing
         conv_bind <- MaybeT (convertTypedBinding toplvl ty defn)
         lift $ build conv_bind

convertTypedBindings :: ConversionMonad m
                     => TopLevelFlag
                     -> [HsBind GHC.Name] -> Map Qualid Signature
                     -> (ConvertedBinding -> m a)
                     -> Maybe (HsBind GHC.Name -> GhcException -> m a)
                     -> m [a]
convertTypedBindings toplvl =
  convertTypedModuleBindings toplvl . map (Nothing,)

--------------------------------------------------------------------------------

convertLocalBinds :: ConversionMonad m => HsLocalBinds GHC.Name -> m Term -> m Term
convertLocalBinds (HsValBinds (ValBindsIn _ _)) _ =
  convUnsupported "Unexpected ValBindsIn in post-renamer AST"

convertLocalBinds (HsValBinds (ValBindsOut recBinds lsigs)) body = do
  sigs     <- convertLSigs lsigs
  -- We are not actually using the rec_flag from GHC, because due to renamings
  -- or `redefinition` edits, maybe the group is no longer recursive.
  convDefss <- for recBinds $ \(_rec_flag, mut_group) ->
    convertTypedBindings NotTopLevel (map unLoc . bagToList $ mut_group) sigs pure Nothing
  let convDefs = concat convDefss

  let matchLet pat term body = Coq.Match [MatchItem term Nothing Nothing] Nothing
                                         [Equation [MultPattern [pat]] body]
  let toLet ConvertedDefinition{..} = Let convDefName convDefArgs convDefType convDefBody
  (foldr (withConvertedBinding toLet matchLet) ?? convDefs) <$> body

convertLocalBinds (HsIPBinds _) _ =
  convUnsupported "local implicit parameter bindings"
convertLocalBinds EmptyLocalBinds body =
  body


--------------------------------------------------------------------------------

-- Create `let x := rhs in genBody x`
-- Unless the rhs is very small, in which case it creates `genBody rhs`
bindIn :: ConversionMonad m => Text -> Term -> (Term -> m Term) -> m Term
bindIn _ rhs@(Qualid _) genBody = genBody rhs
bindIn tmpl rhs genBody = do
  j <- genqid tmpl
  body <- genBody (Qualid j)
  pure $ smartLet j rhs body


-- This prevents the pattern conversion code to create
-- `let j_24__ := … in j_24__`
-- and a few other common and obviously stupid forms
--
-- Originally, we avoided pushing the `rhs` past a binder. But it turned out
-- that we need to do that to get useful termination proof obligations out of
-- program fixpoint. So now we move the `rhs` past a binder if that binder is fresh (i.e. cannot be captured).
-- Let’s cross our fingers that we calculate all free variables properly.
smartLet :: Qualid -> Term -> Term -> Term
-- Move into the else branch
smartLet ident rhs (IfBool c t e)
    | ident `S.notMember` getFreeVars c
    , ident `S.notMember` getFreeVars t
    = IfBool c t (smartLet ident rhs e)
-- Move into the else branch
smartLet ident rhs (IfCase c t e)
    | ident `S.notMember` getFreeVars c
    , ident `S.notMember` getFreeVars t
    = IfCase c t (smartLet ident rhs e)
-- Move into the scrutinee
smartLet ident rhs
    (Coq.Match [MatchItem t Nothing Nothing] Nothing eqns)
    | ident `S.notMember` getFreeVars eqns
    = Coq.Match [MatchItem (smartLet ident rhs t) Nothing Nothing] Nothing eqns
-- Move into the last equation
-- (only if not mentioned in any earlier equation and only if no matched
-- variables is caught)
smartLet ident rhs
    (Coq.Match scruts Nothing eqns)
    | ident `S.notMember` getFreeVars (NoBinding scruts)
    , let intoEqns [] = Just []
          intoEqns [Equation pats body] = do
            let bound = S.fromList $ definedBy pats
            guard $ ident `S.notMember` bound
            guard $ S.null $ bound `S.intersection` getFreeVars rhs
            return [Equation pats (smartLet ident rhs body)]
          intoEqns (e:es) = do
            guard $ ident `S.notMember` getFreeVars e
            (e:) <$> intoEqns es
    , Just eqns' <- intoEqns eqns
    = Coq.Match scruts Nothing eqns'
smartLet ident rhs (Qualid v) | ident == v = rhs
smartLet ident rhs body = Let ident [] Nothing rhs body

patternFailure :: Term
patternFailure = "GHC.Err.patternFailure"

missingValue :: Term
missingValue = "missingValue"

-- | Program does not work nicely with if-then-else, so if we believe we are
-- producing a term that ends up in a Program Fixpoint or Program Definition,
-- then desguar if-then-else using case statements.
ifThenElse :: ConversionMonad m => m (Term -> Term -> Term -> Term)
ifThenElse =
    use useProgramHere >>= \case
        False -> pure $ IfBool
        True ->  pure $ IfCase

