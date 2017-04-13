{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module StructuralIsomorphism.Class (StructurallyIsomorphic(..)) where

class StructurallyIsomorphic a b where
  to   :: a -> b
  from :: b -> a

instance StructurallyIsomorphic a a where
  to   = id
  from = id

instance (StructurallyIsomorphic a b, StructurallyIsomorphic a' b') =>
         StructurallyIsomorphic (a -> a') (b -> b') where
  to   f = to   . f . from
  from f = from . f . to

-- Everything else is autogeneratable
