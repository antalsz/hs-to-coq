{-# LANGUAGE CPP #-}
module Config where

import GhcPrelude

#include "ghc_boot_platform.h"

data IntegerLibrary = IntegerGMP
                    | IntegerSimple
                    deriving Eq

cBuildPlatformString :: String
cBuildPlatformString = BuildPlatform_NAME
cHostPlatformString :: String
cHostPlatformString = HostPlatform_NAME
cTargetPlatformString :: String
cTargetPlatformString = TargetPlatform_NAME

cProjectName          :: String
cProjectName          = "The Glorious Glasgow Haskell Compilation System"
cProjectGitCommitId   :: String
cProjectGitCommitId   = "f31c40efdc918bc9da8a325327ba5a472bd6ea9e"
cProjectVersion       :: String
cProjectVersion       = "8.4.1"
cProjectVersionInt    :: String
cProjectVersionInt    = "804"
cProjectPatchLevel    :: String
cProjectPatchLevel    = "1"
cProjectPatchLevel1   :: String
cProjectPatchLevel1   = "1"
cProjectPatchLevel2   :: String
cProjectPatchLevel2   = ""
cBooterVersion        :: String
cBooterVersion        = "8.0.2"
cStage                :: String
cStage                = show (STAGE :: Int)
cIntegerLibrary       :: String
cIntegerLibrary       = "integer-gmp"
cIntegerLibraryType   :: IntegerLibrary
cIntegerLibraryType   = IntegerGMP
cSupportsSplitObjs    :: String
cSupportsSplitObjs    = "YES"
cGhcWithInterpreter   :: String
cGhcWithInterpreter   = "YES"
cGhcWithNativeCodeGen :: String
cGhcWithNativeCodeGen = "YES"
cGhcWithSMP           :: String
cGhcWithSMP           = "YES"
cGhcRTSWays           :: String
cGhcRTSWays           = "l debug thr thr_debug thr_l thr_p dyn debug_dyn thr_dyn thr_debug_dyn l_dyn thr_l_dyn"
cGhcRtsWithLibdw      :: Bool
cGhcRtsWithLibdw      = False
cGhcEnableTablesNextToCode :: String
cGhcEnableTablesNextToCode = "YES"
cLeadingUnderscore    :: String
cLeadingUnderscore    = "NO"
cGHC_UNLIT_PGM        :: String
cGHC_UNLIT_PGM        = "unlit"
cGHC_SPLIT_PGM        :: String
cGHC_SPLIT_PGM        = "ghc-split"
cLibFFI               :: Bool
cLibFFI               = False
cGhcThreaded :: Bool
cGhcThreaded = True
cGhcDebugged :: Bool
cGhcDebugged = False
