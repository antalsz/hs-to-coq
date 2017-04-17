{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module StructuralIsomorphism.Class (StructurallyIsomorphic(..)) where

class StructurallyIsomorphic a b where
  to   :: a -> b
  from :: b -> a

instance {-# INCOHERENT #-} StructurallyIsomorphic a a where
  to   = id
  from = id
-- This needs to be INCOHERENT to support instances like
-- @StructurallyIsomorphic a b => StructurallyIsomorphic [a] [b]@; I don't know
-- why OVERLAPPABLE isn't enough

instance StructurallyIsomorphic a b => StructurallyIsomorphic [a] [b] where
  to = map to
  from = map from

instance (StructurallyIsomorphic a b, StructurallyIsomorphic a' b') =>
         StructurallyIsomorphic (a -> a') (b -> b') where
  to   f = to   . f . from
  from f = from . f . to

-- Everything else is autogeneratable
