{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts,
             TemplateHaskell,
             ScopedTypeVariables,
             RankNTypes #-}

module HsToCoq.CLI (
  -- * General main-action creator
  processFilesMain,
  -- * Specific application processors
  printConvertedModules,
  convertAndPrintModules,
  WithModulePrinter,
  -- * CLI configuration, parameters, etc.
  Config(..),
  outputFile, preambleFile, midambleFile, editsFiles, processingMode,
  modulesFiles, modulesRoot, directInputFiles, ifaceDirs,
  processArgs,
  ProgramArgs(..),
  argParser, argParserInfo,
  -- * Utility functions
  prettyPrint, hPrettyPrint
  ) where

import Control.Lens hiding ((<.>))

import Data.Foldable
import Data.List (intersperse, isSuffixOf)
import Data.List.NonEmpty (NonEmpty(..))

import Data.Functor
import HsToCoq.Util.Traversable
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except

import System.FilePath
import System.Directory
import qualified Data.Text.IO as T
import System.IO
import System.Exit

import GHC hiding (outputFile)
import DynFlags hiding (outputFile)
import HsToCoq.Util.GHC.Exception
import Module
import CmdLineParser (Warn(..))

import Control.Monad.Parse
import HsToCoq.ConvertHaskell.Parameters.Parsers

import HsToCoq.Util.Monad
import HsToCoq.Util.Messages
import HsToCoq.Util.GHC.Module
import HsToCoq.PrettyPrint hiding ((</>))
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Util.FVs
import HsToCoq.Coq.Pretty
import HsToCoq.Coq.Preamble
import HsToCoq.ProcessFiles
import HsToCoq.ConvertHaskell
import HsToCoq.ConvertHaskell.TypeInfo
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.CLI.FileTree
import HsToCoq.CLI.FileTree.Parser

import Options.Applicative

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = hPrettyPrint stdout

data ProgramArgs = ProgramArgs { outputFileArg        :: Maybe FilePath
                               , preambleFileArg      :: Maybe FilePath
                               , midambleFileArg      :: Maybe FilePath
                               , editsFilesArgs       :: [FilePath]
                               , processingModeArg    :: ProcessingMode
                               , modulesFilesArgs     :: [FilePath]
                               , modulesRootArg       :: Maybe FilePath
                               , ifaceDirsArgs        :: [FilePath]
                               , importDirsArgs       :: [FilePath]
                               , includeDirsArgs      :: [FilePath]
                               , ghcTreeDirsArgs      :: [FilePath]
                               , ghcOptionsArgs       :: [String]
                               , directInputFilesArgs :: [FilePath]
                               }
                 deriving (Eq, Ord, Show, Read)

argParser :: Parser ProgramArgs
argParser = ProgramArgs <$> optional (strOption       $  long    "output"
                                                      <> short   'o'
                                                      <> metavar "FILE"
                                                      <> help    "File to write the translated Coq code to (defaults to stdout)")

                        <*> optional (strOption       $  long    "preamble"
                                                      <> short   'p'
                                                      <> metavar "FILE"
                                                      <> help    "File containing code that goes at the top of the Coq output")

                        <*> optional (strOption       $  long    "midamble"
                                                      <> short   'm'
                                                      <> metavar "FILE"
                                                      <> help    "File containing code that goes after the type declarations")

                        <*> many     (strOption       $  long    "edits"
                                                      <> short   'e'
                                                      <> metavar "FILE"
                                                      <> help    "File with extra Haskell -> Coq edits")

                        <*> asum [ flag' Recursive    $  long    "recursive"
                                                      <> short   'R'
                                                      <> help    "Translate dependencies of the given modules (default)"
                                 , flag' NonRecursive $  long    "nonrecursive"
                                                      <> short   'N'
                                                      <> help    "Only translate the given modules, and not their dependencies"
                                 , pure  Recursive ]

                        <*> many     (strOption       $  long    "modules"
                                                      <> short   'm'
                                                      <> metavar "FILE"
                                                      <> help    "File listing Haskell files to translate into Coq, in an indented tree structure")

                        <*> optional (strOption       $  long    "modules-dir"
                                                      <> short   'd'
                                                      <> metavar "DIR"
                                                      <> help    "The directory the module tree files' contents are rooted at")

                        <*> many     (strOption       $  long    "iface-dir"
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for hs-to-coq interface files (.h2ci)" )

                        <*> many     (strOption       $  long    "import-dir"
                                                      <> short   'i'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for Haskell modules")

                        <*> many     (strOption       $  long    "include-dir"
                                                      <> short   'I'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for CPP `#include's")

                        <*> many     (strOption       $  long    "ghc-tree"
                                                      <> metavar "DIR"
                                                      <> help    "Add the usual ghc build tree subdirectories rooted atDIR to the module search path")

                        <*> many     (strOption       $  long    "ghc"
                                                      <> metavar "ARGUMENT"
                                                      <> help    "Option to pass through to GHC")

                        <*> many     (strArgument     $  metavar "FILES"
                                                      <> help    "Haskell files to translate into Coq")

argParserInfo :: ParserInfo ProgramArgs
argParserInfo = info (helper <*> argParser) $  fullDesc
                                            <> progDesc "Convert Haskell source files to Coq"

data Config = Config { _outputFile       :: !(Maybe FilePath)
                     , _preambleFile     :: !(Maybe FilePath)
                     , _midambleFile     :: !(Maybe FilePath)
                     , _editsFiles       :: ![FilePath]
                     , _processingMode   :: !ProcessingMode
                     , _modulesFiles     :: ![FilePath]
                     , _modulesRoot      :: !(Maybe FilePath)
                     , _directInputFiles :: ![FilePath]
                     , _ifaceDirs        :: ![FilePath]
                     }
            deriving (Eq, Ord, Show, Read)
makeLenses ''Config

ghcInputDirs :: FilePath -> [FilePath]
ghcInputDirs base = map ((base </> "compiler") </>) $ words
    "backpack basicTypes cmm codeGen coreSyn deSugar ghci \
    \hsSyn iface llvmGen main nativeGen parser prelude \
    \profiling rename simplCore simplStg specialise stgSyn \
    \stranal typecheck types utils vectorise stage2/build"

processArgs :: GhcMonad m => m Config
processArgs = do
  ProgramArgs{..} <- liftIO $ customExecParser defaultPrefs{prefMultiSuffix="..."} argParserInfo

  let defaultArgs = map (mkGeneralLocated "defaultArgs") $ words "-hidir=.ghc-tmp -odir=.ghc-tmp"

  let ghcArgs = let locate opt = mkGeneralLocated $ "command line (" ++ opt ++ ")"
                in defaultArgs ++
                   map (locate "-i"         . ("-i" ++)) importDirsArgs ++
                   map (locate "-I"         . ("-I" ++)) includeDirsArgs ++
                   map (locate "--ghc-tree" . ("-i" ++)) (concatMap ghcInputDirs ghcTreeDirsArgs) ++
                   map (locate "--ghc")                  ghcOptionsArgs

  (dflags, ghcRest, warnings) <- (parseDynamicFlagsCmdLine ?? ghcArgs) =<< getSessionDynFlags
  printAllIfPresent unLoc "Command-line argument warning" (map warnMsg warnings)
  printAllIfPresent unLoc "Ignored GHC arguments"         ghcRest

  void $ setSessionDynFlags dflags

  pure $ Config { _outputFile       = if outputFileArg == Just "-"
                                      then Nothing
                                      else outputFileArg
                , _preambleFile     = preambleFileArg
                , _midambleFile     = midambleFileArg
                , _editsFiles       = editsFilesArgs
                , _processingMode   = processingModeArg
                , _modulesFiles     = modulesFilesArgs
                , _modulesRoot      = modulesRootArg
                , _directInputFiles = directInputFilesArgs
                , _ifaceDirs        = ifaceDirsArgs
                }

parseModulesFiles :: (MonadIO m, MonadError String m)
                  => FilePath -> [FilePath] -> m [FilePath]
parseModulesFiles root files =
  let fullName name = root </> if ".hs" `isSuffixOf` name
                               then name
                               else name <.> "hs"
  in fmap (map fullName . resolveFileTrees) . forFold files $ \file ->
       exceptEither . parseFileTrees (Just file) =<< liftIO (readFile file)

--------------------------------------------------------------------------------

type WithModulePrinter m =
    ModuleName ->
    (Handle -> m ()) -> -- print type declarations
    (Handle -> m ()) -> -- print rest
    m ()

processFilesMain ::
    forall m . GhcMonad m
    => (forall r m. GlobalMonad r m => WithModulePrinter m -> [TypecheckedModule] -> m ())
    -> m ()
processFilesMain process = do
  conf <- processArgs

  let parseConfigFiles files builder parser =
        liftIO . forFold (conf^.files) $ \filename ->
          (evalNewlinesParse parser <$> T.readFile filename) >>= \case
            Left  err -> die $ "Could not parse " ++ filename ++ ": " ++ err
            Right res -> either die pure $ builder res

  edits      <- parseConfigFiles editsFiles     buildEdits     parseEditList

  inputFiles <- either (liftIO . die) pure <=< runExceptT $
                  (++) <$> parseModulesFiles (conf^.modulesRoot.non "") (conf^.modulesFiles)
                       <*> pure (conf^.directInputFiles)

  preambles <- liftIO $ traverse readFile (conf^.preambleFile)
  let printPreambles hOut = liftIO $ do
        T.hPutStr hOut staticPreamble
        hPutStrLn hOut ""
        unless (null preambles) $ do
          hPutStrLn hOut "(* Preamble *)"
          hPutStrLn hOut ""
        for_ preambles $ \contents -> do
            hPutStr   hOut contents
            hPutStrLn hOut ""
            hFlush    hOut

  midambles <- liftIO $ traverse readFile (conf^.midambleFile)
  let printMidambles hOut = liftIO $ do
        unless (null midambles) $ do
          hPutStrLn hOut "(* Midamble *)"
          hPutStrLn hOut ""
        for_ midambles $ \contents -> do
            hPutStr   hOut contents
            hPutStrLn hOut ""
            hFlush    hOut

  let withModulePrinter :: forall r m. GlobalMonad r m => WithModulePrinter m
      withModulePrinter = case conf^.outputFile of
        Nothing  -> \mod act1 act2 -> do
            liftIO . putStrLn $ "(* " ++ moduleNameString mod ++ " *)"
            liftIO $ putStrLn ""
            printPreambles stdout
            void $ act1 stdout
            printMidambles stdout
            void $ act2 stdout
        Just outDir -> \mod act1 act2 -> do
          let path = outDir </> moduleNameSlashes mod <.> "v"
          liftIO . createDirectoryIfMissing True $ takeDirectory path
          gWithFile path WriteMode $ \hOut -> do
            printPreambles hOut
            void $ act1 hOut
            printMidambles hOut
            void $ act2 hOut
          let ifacepath = outDir </> moduleNameSlashes mod <.> "h2ci"
          gWithFile ifacepath WriteMode $ \hOut -> do
            iface <- serializeIfaceFor (moduleNameText mod)
            liftIO $ hPutStr hOut iface


  runGlobalMonad edits (conf^.ifaceDirs) $
    traverse_ (process withModulePrinter) =<< processFiles (conf^.processingMode) inputFiles

printConvertedModule :: GlobalMonad r m
                     => WithModulePrinter m
                     -> ConvertedModule
                     -> m ()
printConvertedModule withModulePrinter cmod@ConvertedModule{..} = do
  (convModDecls1, convModDecls2) <- moduleDeclarations cmod

  let printUnbound out = do
          let fvs = toList $ getFVs $ foldScopes bvOf (convModDecls1 ++ convModDecls2) mempty
          unless (null fvs) $ do
              hPrettyPrint out $
                line <> "(*" <+> hang 2
                  ("External variables:" <!> fillSep (map (text . qualidToIdent) fvs))
                <!> "*)" <> line
              hFlush out

      part1 out = liftIO $ do
          printThe out "imports"            mempty convModImports <* gap out
          printThe out "type declarations"  line   convModDecls1  <* hFlush out
      part2 out = liftIO $ do
          printThe out "value declarations" line   convModDecls2  <* hFlush out
          printUnbound out

  withModulePrinter convModName part1 part2
 where
  gap out = hPutStrLn out "" >> hFlush out

  printThe out what _   [] = hPutStrLn out $ "(* No " ++ what ++ " to convert. *)"
  printThe out what sep ds = do hPutStrLn out $ "(* Converted " ++ what ++ ": *)"
                                gap out
                                traverse_ (hPrettyPrint out) . intersperse sep $
                                  map ((<> line) . renderGallina) ds

printConvertedModules :: GlobalMonad r m
                      => WithModulePrinter m
                      -> [NonEmpty ConvertedModule]
                      -> m ()
printConvertedModules withModulePrinter =
  traverse_ (printConvertedModule withModulePrinter) . foldMap toList

convertAndPrintModules :: GlobalMonad r m => WithModulePrinter m -> [TypecheckedModule] -> m ()
convertAndPrintModules p = printConvertedModules p <=< convertModules <=< traverse toRenamed
  where
    toRenamed tcm
        | Just rn <- tm_renamed_source tcm = pure (mod, rn)
        | otherwise = throwProgramError $  "Renamer failed for `" ++ moduleNameString mod ++ "'"
      where mod = ms_mod_name . pm_mod_summary $ tm_parsed_module tcm
