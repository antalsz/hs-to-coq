--------------------------------------------------------------------------------
-- This file's contents were almonst entirely copied out of GHC, from         --
-- compiler/main/DriverPipeline.hs, and so this file is under GHC's license   --
-- (available in the file "GHC_LICENSE" at the top level of this project).    --
-- The portions of this file that were added (not copied) are:                --
--   * This header comment;                                                   --
--   * The @module@ header; and                                               --
--   * The definitions of some configuration macros, which were placed        --
--     between "{- BEGIN ADDED hs-to-coq -}" and "{- END ADDED hs-to-coq -}"  --
--     comments.                                                              --
--------------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-cse #-}
-- -fno-cse is needed for GLOBAL_VAR's to behave properly

module HsToCoq.Util.GHC.DoCpp (doCpp) where

import Packages
import SysTools
import Module
import DynFlags
import Config
import Panic

import System.Directory
import System.FilePath
import Control.Monad
import Data.Maybe
import Data.Version

{- BEGIN ADDED hs-to-coq -}
import qualified System.Info

-- We assume the host and target are the system we're currently running on;
-- ideally, this won't actually matter, since we probably can't convert any
-- files that meaningfully depend on this information.
#define HOST_OS     System.Info.os
#define HOST_ARCH   System.Info.arch
#define TARGET_OS   System.Info.os
#define TARGET_ARCH System.Info.arch
{- END ADDED hs-to-coq -}

-- -----------------------------------------------------------------------------
-- Running CPP

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
          [ "-D" ++ HOST_OS     ++ "_BUILD_OS=1",
            "-D" ++ HOST_ARCH   ++ "_BUILD_ARCH=1",
            "-D" ++ TARGET_OS   ++ "_HOST_OS=1",
            "-D" ++ TARGET_ARCH ++ "_HOST_ARCH=1" ]
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

#ifdef GHCI
    let th_defs = [ "-D__GLASGOW_HASKELL_TH__=1" ]
#else
    let th_defs = [ "-D__GLASGOW_HASKELL_TH__=0" ]
#endif
    -- Default CPP defines in Haskell source
    ghcVersionH <- getGhcVersionPathName dflags
    let hsSourceCppOpts =
          [ "-D__GLASGOW_HASKELL__="++cProjectVersionInt
          , "-include", ghcVersionH
          ]

    -- MIN_VERSION macros
    let uids = explicitPackages (pkgState dflags)
        pkgs = catMaybes (map (lookupPackage dflags) uids)
    mb_macro_include <-
        if not (null pkgs) && gopt Opt_VersionMacros dflags
            then do macro_stub <- newTempName dflags "h"
                    writeFile macro_stub (generatePackageVersionMacros pkgs)
                    -- Include version macros for every *exposed* package.
                    -- Without -hide-all-packages and with a package database
                    -- size of 1000 packages, it takes cpp an estimated 2
                    -- milliseconds to process this file. See Trac #10970
                    -- comment 8.
                    return [SysTools.FileOption "-include" macro_stub]
            else return []

    cpp_prog       (   map SysTools.Option verbFlags
                    ++ map SysTools.Option include_paths
                    ++ map SysTools.Option hsSourceCppOpts
                    ++ map SysTools.Option target_defs
                    ++ map SysTools.Option backend_defs
                    ++ map SysTools.Option th_defs
                    ++ map SysTools.Option hscpp_opts
                    ++ map SysTools.Option sse_defs
                    ++ map SysTools.Option avx_defs
                    ++ mb_macro_include
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

getBackendDefs :: DynFlags -> IO [String]
getBackendDefs dflags | hscTarget dflags == HscLlvm = do
    llvmVer <- figureLlvmVersion dflags
    return $ case llvmVer of
               Just n -> [ "-D__GLASGOW_HASKELL_LLVM__=" ++ format n ]
               _      -> []
  where
    format (major, minor)
      | minor >= 100 = error "getBackendDefs: Unsupported minor version"
      | otherwise = show $ (100 * major + minor :: Int) -- Contract is Int

getBackendDefs _ =
    return []

-- ---------------------------------------------------------------------------
-- Macros (cribbed from Cabal)

generatePackageVersionMacros :: [PackageConfig] -> String
generatePackageVersionMacros pkgs = concat
  -- Do not add any C-style comments. See Trac #3389.
  [ generateMacros "" pkgname version
  | pkg <- pkgs
  , let version = packageVersion pkg
        pkgname = map fixchar (packageNameString pkg)
  ]

fixchar :: Char -> Char
fixchar '-' = '_'
fixchar c   = c

generateMacros :: String -> String -> Version -> String
generateMacros prefix name version =
  concat
  ["#define ", prefix, "VERSION_",name," ",show (showVersion version),"\n"
  ,"#define MIN_", prefix, "VERSION_",name,"(major1,major2,minor) (\\\n"
  ,"  (major1) <  ",major1," || \\\n"
  ,"  (major1) == ",major1," && (major2) <  ",major2," || \\\n"
  ,"  (major1) == ",major1," && (major2) == ",major2," && (minor) <= ",minor,")"
  ,"\n\n"
  ]
  where
    (major1:major2:minor:_) = map show (versionBranch version ++ repeat 0)

-- | Find out path to @ghcversion.h@ file
getGhcVersionPathName :: DynFlags -> IO FilePath
getGhcVersionPathName dflags = do
  dirs <- getPackageIncludePath dflags [rtsUnitId]

  found <- filterM doesFileExist (map (</> "ghcversion.h") dirs)
  case found of
      []    -> throwGhcExceptionIO (InstallationError ("ghcversion.h missing"))
      (x:_) -> return x

-- Note [-fPIC for assembler]
-- When compiling .c source file GHC's driver pipeline basically
-- does the following two things:
--   1. ${CC}              -S 'PIC_CFLAGS' source.c
--   2. ${CC} -x assembler -c 'PIC_CFLAGS' source.S
--
-- Why do we need to pass 'PIC_CFLAGS' both to C compiler and assembler?
-- Because on some architectures (at least sparc32) assembler also chooses
-- the relocation type!
-- Consider the following C module:
--
--     /* pic-sample.c */
--     int v;
--     void set_v (int n) { v = n; }
--     int  get_v (void)  { return v; }
--
--     $ gcc -S -fPIC pic-sample.c
--     $ gcc -c       pic-sample.s -o pic-sample.no-pic.o # incorrect binary
--     $ gcc -c -fPIC pic-sample.s -o pic-sample.pic.o    # correct binary
--
--     $ objdump -r -d pic-sample.pic.o    > pic-sample.pic.o.od
--     $ objdump -r -d pic-sample.no-pic.o > pic-sample.no-pic.o.od
--     $ diff -u pic-sample.pic.o.od pic-sample.no-pic.o.od
--
-- Most of architectures won't show any difference in this test, but on sparc32
-- the following assembly snippet:
--
--    sethi   %hi(_GLOBAL_OFFSET_TABLE_-8), %l7
--
-- generates two kinds or relocations, only 'R_SPARC_PC22' is correct:
--
--       3c:  2f 00 00 00     sethi  %hi(0), %l7
--    -                       3c: R_SPARC_PC22        _GLOBAL_OFFSET_TABLE_-0x8
--    +                       3c: R_SPARC_HI22        _GLOBAL_OFFSET_TABLE_-0x8

{- Note [Don't normalise input filenames]

Summary
  We used to normalise input filenames when starting the unlit phase. This
  broke hpc in `--make` mode with imported literate modules (#2991).

Introduction
  1) --main
  When compiling a module with --main, GHC scans its imports to find out which
  other modules it needs to compile too. It turns out that there is a small
  difference between saying `ghc --make A.hs`, when `A` imports `B`, and
  specifying both modules on the command line with `ghc --make A.hs B.hs`. In
  the former case, the filename for B is inferred to be './B.hs' instead of
  'B.hs'.

  2) unlit
  When GHC compiles a literate haskell file, the source code first needs to go
  through unlit, which turns it into normal Haskell source code. At the start
  of the unlit phase, in `Driver.Pipeline.runPhase`, we call unlit with the
  option `-h` and the name of the original file. We used to normalise this
  filename using System.FilePath.normalise, which among other things removes
  an initial './'. unlit then uses that filename in #line directives that it
  inserts in the transformed source code.

  3) SrcSpan
  A SrcSpan represents a portion of a source code file. It has fields
  linenumber, start column, end column, and also a reference to the file it
  originated from. The SrcSpans for a literate haskell file refer to the
  filename that was passed to unlit -h.

  4) -fhpc
  At some point during compilation with -fhpc, in the function
  `deSugar.Coverage.isGoodTickSrcSpan`, we compare the filename that a
  `SrcSpan` refers to with the name of the file we are currently compiling.
  For some reason I don't yet understand, they can sometimes legitimally be
  different, and then hpc ignores that SrcSpan.

Problem
  When running `ghc --make -fhpc A.hs`, where `A.hs` imports the literate
  module `B.lhs`, `B` is inferred to be in the file `./B.lhs` (1). At the
  start of the unlit phase, the name `./B.lhs` is normalised to `B.lhs` (2).
  Therefore the SrcSpans of `B` refer to the file `B.lhs` (3), but we are
  still compiling `./B.lhs`. Hpc thinks these two filenames are different (4),
  doesn't include ticks for B, and we have unhappy customers (#2991).

Solution
  Do not normalise `input_fn` when starting the unlit phase.

Alternative solution
  Another option would be to not compare the two filenames on equality, but to
  use System.FilePath.equalFilePath. That function first normalises its
  arguments. The problem is that by the time we need to do the comparison, the
  filenames have been turned into FastStrings, probably for performance
  reasons, so System.FilePath.equalFilePath can not be used directly.

Archeology
  The call to `normalise` was added in a commit called "Fix slash
  direction on Windows with the new filePath code" (c9b6b5e8). The problem
  that commit was addressing has since been solved in a different manner, in a
  commit called "Fix the filename passed to unlit" (1eedbc6b). So the
  `normalise` is no longer necessary.
-}
