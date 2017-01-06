{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Module (module Module) where

import Module

instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)
