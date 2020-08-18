{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell #-}

module HsToCoq.Util.GHC.Module (module Module, ModuleData(..), moduleNameText, mkModuleNameT, modName, modExports) where

import Module

import Data.Text (Text)
import qualified Data.Text as T

import qualified GHC

import Control.Lens

-- Note: the names in the list of module exports are from before any renaming
-- has occurred.
data ModuleData = ModuleData { _modName     :: ModuleName
                             , _modExports  :: [GHC.Name]
                             } deriving (Eq)
makeLenses ''ModuleData

instance Ord ModuleData where
  (<=) d1 d2 = _modName d1 <= _modName d2


instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)

-- should this have ModuleData as a parameter instead of ModuleName?
moduleNameText :: ModuleName -> Text
moduleNameText = T.pack . moduleNameString

mkModuleNameT :: Text -> ModuleName
mkModuleNameT = mkModuleName . T.unpack
