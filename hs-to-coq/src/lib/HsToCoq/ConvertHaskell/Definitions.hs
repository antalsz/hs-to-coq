{-# LANGUAGE RecordWildCards #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..), withConvertedDefinition, withConvertedDefinitionDef, withConvertedDefinitionOp,
  ConvertedBinding(..), withConvertedBinding
  ) where

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------

data ConvertedDefinition = ConvertedDefinition { convDefName  :: !Ident
                                               , convDefArgs  :: ![Binder]
                                               , convDefType  :: !(Maybe Term)
                                               , convDefBody  :: !Term
                                               , convDefInfix :: !(Maybe Op) }
                         deriving (Eq, Ord, Show, Read)

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

--------------------------------------------------------------------------------

data ConvertedBinding = ConvertedDefinitionBinding ConvertedDefinition
                      | ConvertedPatternBinding    Pattern Term
                      deriving (Eq, Ord, Show, Read)

withConvertedBinding :: (ConvertedDefinition -> a) -> (Pattern -> Term -> a) -> ConvertedBinding -> a
withConvertedBinding  withDef _withPat (ConvertedDefinitionBinding cdef)    = withDef cdef
withConvertedBinding _withDef  withPat (ConvertedPatternBinding    pat def) = withPat pat def
