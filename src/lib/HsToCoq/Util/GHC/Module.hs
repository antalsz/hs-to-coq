{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell #-}

module HsToCoq.Util.GHC.Module (module Module, ModuleData(..), moduleNameText, mkModuleNameT, modName, modExports) where

import Module

import Data.Text (Text)
import qualified Data.Text as T

import qualified GHC

import Control.Lens

data ModuleData = ModuleData { _modName     :: ModuleName
                             , _modExports  :: [GHC.Name]
                             } deriving (Eq)
makeLenses ''ModuleData


instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)

-- should this have ModuleData as a parameter instead of ModuleName?
moduleNameText :: ModuleName -> Text
moduleNameText = T.pack . moduleNameString

mkModuleNameT :: Text -> ModuleName
mkModuleNameT = mkModuleName . T.unpack
