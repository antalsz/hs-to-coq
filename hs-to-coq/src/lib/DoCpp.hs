--------------------------------------------------------------------------------
-- This file's contents were largely copied out of GHC, from                  --
-- compiler/main/DriverPipeline.hs, and is under GHC's license.  The three    --
-- function definitions are from said file, with macros/similar definitions   --
-- expanded; the module header and imports are not.                           --
--------------------------------------------------------------------------------

module DoCpp (doCpp) where

import Control.Monad

import System.Directory
import System.FilePath

import DynFlags
import SysTools
import Packages
import Panic
import Module

-- | Find out path to @ghcversion.h@ file
getGhcVersionPathName :: DynFlags -> IO FilePath
getGhcVersionPathName dflags = do
  dirs <- getPackageIncludePath dflags [rtsPackageKey]

  found <- filterM doesFileExist (map (</> "ghcversion.h") dirs)
  case found of
      []    -> throwGhcExceptionIO (InstallationError ("ghcversion.h missing"))
      (x:_) -> return x

getBackendDefs :: DynFlags -> IO [String]
getBackendDefs dflags | hscTarget dflags == HscLlvm = do
    llvmVer <- figureLlvmVersion dflags
    return $ case llvmVer of
               Just n -> [ "-D__GLASGOW_HASKELL_LLVM__="++show n ]
               _      -> []

getBackendDefs _ =
    return []

doCpp :: DynFlags -> Bool -> FilePath -> FilePath -> IO ()
doCpp dflags raw input_fn output_fn = do
    let hscpp_opts = picPOpts dflags
    let cmdline_include_paths = includePaths dflags

    pkg_include_dirs <- getPackageIncludePath dflags []
    let include_paths = foldr (\ x xs -> "-I" : x : xs) []
                          (cmdline_include_paths ++ pkg_include_dirs)

    let verbFlags = getVerbFlags dflags

    let cpp_prog args | raw       = SysTools.runCpp dflags args
                      | otherwise = SysTools.runCc dflags (SysTools.Option "-E" : args)

    let target_defs =
          [ "-D" ++ "darwin"     ++ "_BUILD_OS=1",
            "-D" ++ "x86_64"   ++ "_BUILD_ARCH=1",
            "-D" ++ "darwin"   ++ "_HOST_OS=1",
            "-D" ++ "x86_64" ++ "_HOST_ARCH=1" ]
        -- remember, in code we *compile*, the HOST is the same our TARGET,
        -- and BUILD is the same as our HOST.

    let sse_defs =
          [ "-D__SSE__=1"    | isSseEnabled    dflags ] ++
          [ "-D__SSE2__=1"   | isSse2Enabled   dflags ] ++
          [ "-D__SSE4_2__=1" | isSse4_2Enabled dflags ]

    let avx_defs =
          [ "-D__AVX__=1"  | isAvxEnabled  dflags ] ++
          [ "-D__AVX2__=1" | isAvx2Enabled dflags ] ++
          [ "-D__AVX512CD__=1" | isAvx512cdEnabled dflags ] ++
          [ "-D__AVX512ER__=1" | isAvx512erEnabled dflags ] ++
          [ "-D__AVX512F__=1"  | isAvx512fEnabled  dflags ] ++
          [ "-D__AVX512PF__=1" | isAvx512pfEnabled dflags ]

    backend_defs <- getBackendDefs dflags

    let th_defs = [ "-D__GLASGOW_HASKELL_TH__=YES" ]
    -- Default CPP defines in Haskell source
    ghcVersionH <- getGhcVersionPathName dflags
    let hsSourceCppOpts =
          [ "-D__GLASGOW_HASKELL__="++"710"
          , "-include", ghcVersionH
          ]

    cpp_prog       (   map SysTools.Option verbFlags
                    ++ map SysTools.Option include_paths
                    ++ map SysTools.Option hsSourceCppOpts
                    ++ map SysTools.Option target_defs
                    ++ map SysTools.Option backend_defs
                    ++ map SysTools.Option th_defs
                    ++ map SysTools.Option hscpp_opts
                    ++ map SysTools.Option sse_defs
                    ++ map SysTools.Option avx_defs
        -- Set the language mode to assembler-with-cpp when preprocessing. This
        -- alleviates some of the C99 macro rules relating to whitespace and the hash
        -- operator, which we tend to abuse. Clang in particular is not very happy
        -- about this.
                    ++ [ SysTools.Option     "-x"
                       , SysTools.Option     "assembler-with-cpp"
                       , SysTools.Option     input_fn
        -- We hackily use Option instead of FileOption here, so that the file
        -- name is not back-slashed on Windows.  cpp is capable of
        -- dealing with / in filenames, so it works fine.  Furthermore
        -- if we put in backslashes, cpp outputs #line directives
        -- with *double* backslashes.   And that in turn means that
        -- our error messages get double backslashes in them.
        -- In due course we should arrange that the lexer deals
        -- with these \\ escapes properly.
                       , SysTools.Option     "-o"
                       , SysTools.FileOption "" output_fn
                       ])
