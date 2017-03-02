{-# LANGUAGE TemplateHaskell #-}

module StructuralIsomorphism.TH.Util (
  -- * Manipulating 'Type's
  outerNormalizeType, headType,
  tyVarBndrName,
  
  -- * Pretty-printing
  quoted,
  
  -- * Debugging
  thPutStrLn, thPrint, thPpr
) where

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
