{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module StructuralIsomorphism.TH.Util (
  -- * Manipulating 'Type's
  outerNormalizeType, headType,
  isTypeSynonym, expandTypeSynonyms,
  subst,
  tyVarBndrName,
  
  -- * Pretty-printing
  quoted,
  
  -- * Debugging
  thPutStrLn, thPrint, thPpr
) where

import Data.Bifunctor
import GHC.Exts (Constraint)
import StructuralIsomorphism.Util
import Language.Haskell.TH.Syntax
import Language.Haskell.TH

--------------------------------------------------------------------------------

outerNormalizeType :: Type -> Type
outerNormalizeType (SigT ty _k)      = outerNormalizeType ty
outerNormalizeType (TupleT n)        = ConT $ tupleTypeName n
outerNormalizeType (UnboxedTupleT n) = ConT $ unboxedTupleTypeName n
outerNormalizeType ArrowT            = ConT ''(->)
outerNormalizeType ListT             = ConT ''[]
outerNormalizeType ty                = ty

headType :: Type -> Type
headType (ForallT _tvs _cxt ty) = headType ty
headType (SigT ty _k)           = headType ty
headType (AppT l _r)            = headType l
headType ty                     = outerNormalizeType ty

isTypeSynonym :: Quasi m => Name -> m (Maybe ([TyVarBndr],Type))
isTypeSynonym syn | nameSpace syn == Just TcClsName =
  qReify syn <&> \case
    TyConI (TySynD _name params body) -> Just (params, body)
    _                                 -> Nothing
isTypeSynonym _ = pure Nothing

data AppStep = AppStep    Type
             | SigStep    Kind
             | ParensStep
             deriving (Eq, Ord, Show)

data InfixType = Resolved | Unresolved
               deriving (Eq, Ord, Enum, Bounded, Show, Read)

expandTypeSynonyms :: Quasi m => Type -> m Type
expandTypeSynonyms = top where
  top con@(ConT _)             = app      con []
  top (ty1 `AppT` ty2)         = app      ty1 [AppStep ty2]
  top (InfixT l i r)           = appInfix i   Resolved   l r []
  top (UInfixT l i r)          = appInfix i   Unresolved l r []
  top (ForallT binders cxt ty) = ForallT binders <$> traverse top cxt <*> top ty
  top (SigT ty k)              = SigT <$> top ty <*> top k
  top (ParensT ty)             = ParensT <$> top ty
  top ty                       = pure ty

  app (ConT name)              args = isTypeSynonym name >>= \case
                                        Just (params, body) -> expand name body params args
                                        Nothing             -> rebuild (pure $ ConT name) args
  app (ty1 `AppT` ty2)         args = app      ty1 (AppStep    ty2 : args)
  app (InfixT l i r)           args = appInfix i   Resolved    l r   args
  app (UInfixT l i r)          args = appInfix i   Unresolved  l r   args
  app (SigT ty k)              args = app      ty  (SigStep    k   : args)
  app (ParensT ty)             args = app      ty  (ParensStep     : args)
  app ty                       args = rebuild (top ty) args
  
  appInfix i infixType l r args =
    isTypeSynonym i >>= \case
      Just (params, body) -> expand i body params (AppStep r : AppStep l : args)
      _                   ->
        let infixT = case infixType of
                       Resolved   -> InfixT
                       Unresolved -> UInfixT
        in rebuild (infixT <$> top l <*> pure i <*> top r) args
  
  rebuild getTy [] = getTy
  rebuild getTy (arg:args) = do
    ty <- getTy                         
    case arg of
      AppStep    ty' -> rebuild (AppT ty <$> top ty') args
      SigStep    k   -> rebuild (SigT ty <$> top k)   args
      ParensStep     -> rebuild (pure $ ParensT ty)   args
  
  expand _name  body []             args                = rebuild (top body) args
  expand  name  body params         (SigStep _k : args) = expand name body params args
  expand  name  body params         (ParensStep : args) = expand name body params args
  expand  name  body (param:params) (AppStep ty : args) = expand name
                                                                 (subst
                                                                   (tyVarBndrName param) ty
                                                                   body)
                                                                 params args
  expand  name _body (_:_)          []                  =
    fail $ "Too few arguments when applying the type synonym " ++ quoted name

subst :: Name -> Type -> Type -> Type
subst x s = go where
  go (ForallT binders cxt ty)     = goForall binders cxt ty
  go (AppT ty1 ty2)               = AppT (go ty1) (go ty2)
  go (SigT ty k)                  = SigT (go ty) (go k)
  go (VarT y)
    | x == y                      = s
    | otherwise                   = VarT y
  go (ConT con)
    | x == con                    = s
    | otherwise                   = ConT con
  go (PromotedT p)
    | x == p                      = s
    | otherwise                   = PromotedT p
  go (InfixT l i r)
    | x == i                      = AppT (AppT s (go l)) (go r)
    | otherwise                   = InfixT (go l) i (go r)
  go (UInfixT l i r)
    | x == i                      = AppT (AppT s (go l)) (go r)
    | otherwise                   = UInfixT (go l) i (go r)
  go (ParensT ty)                 = ParensT (go ty)
  go (TupleT n)
    | x == tupleTypeName n        = s
    | otherwise                   = TupleT n
  go (UnboxedTupleT n)
    | x == unboxedTupleTypeName n = s
    | otherwise                   = TupleT n
  go ArrowT
    | x == ''(->)                 = s
    | otherwise                   = ArrowT
  go EqualityT
    | x == ''(~)                  = s
    | otherwise                   = EqualityT
  go ListT
    | x == ''[]                   = s
    | otherwise                   = ListT
  go (PromotedTupleT n)
    | x == tupleDataName n        = s
    | otherwise                   = PromotedTupleT n
  go PromotedNilT
    | x == '[]                    = s
    | otherwise                   = PromotedNilT
  go PromotedConsT
    | x == '(:)                   = s
    | otherwise                   = PromotedConsT
  go StarT                        = StarT -- Doesn't seem to have an (easily-accessible) name
  go ConstraintT
    | x == ''Constraint           = s
    | otherwise                   = StarT
  go lit@(LitT _)                 = lit
  go WildCardT                    = WildCardT

  goBinders []             =
    (True, [])
  goBinders (tv : binders) =
    let (tv',y) = case tv of
                    PlainTV  y   -> (tv,                y)
                    KindedTV y k -> (KindedTV y (go k), y)
    in second (tv' :) $
         if x == y
         then (False, binders)
         else goBinders binders
  
  goForall binders cxt ty =
    let (keepGoing, binders') = goBinders binders
        go' | keepGoing = go
            | otherwise = id
    in ForallT binders' (map go' cxt) (go ty)

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV  tv)    = tv
tyVarBndrName (KindedTV tv _k) = tv

--------------------------------------------------------------------------------

quoted :: Ppr a => a -> String
quoted x = "`" ++ pprint x ++ "'"

--------------------------------------------------------------------------------

-- Example usage
--
-- >>> $(thPrint =<< [|(Just 42 ==)|])
-- InfixE (Just (AppE (ConE GHC.Base.Just) (LitE (IntegerL 42)))) (VarE GHC.Classes.==) Nothing
--
-- >>> $(thPpr =<< reify 'fst)
-- Data.Tuple.fst :: forall (a_0 :: *) (b_1 :: *) . (a_0, b_1) -> a_0

thPutStrLn :: String -> ExpQ
thPutStrLn str = [|putStrLn $(stringE str)|]

thPrint :: Show a => a -> ExpQ
thPrint = thPutStrLn . show

thPpr :: Ppr a => a -> ExpQ
thPpr = thPutStrLn . pprint
