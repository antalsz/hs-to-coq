{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.Module (module Module, moduleNameText, mkModuleNameT) where

import Module

import Data.Text (Text)
import qualified Data.Text as T

instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)

moduleNameText :: ModuleName -> Text
moduleNameText = T.pack . moduleNameString

mkModuleNameT :: Text -> ModuleName
mkModuleNameT = mkModuleName . T.unpack
