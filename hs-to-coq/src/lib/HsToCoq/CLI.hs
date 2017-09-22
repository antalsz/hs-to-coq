{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.CLI (
  -- * General main-action creator
  processFilesMain,
  -- * Specific application processors
  printConvertedModules,
  convertAndPrintModules,
  WithModulePrinter,
  -- * CLI configuration, parameters, etc.
  Config(..), outputFile, preambleFile, renamingsFile, editsFile, modulesFiles, modulesRoot, directInputFiles,
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

import Control.Monad.Trans.Parse
import HsToCoq.ConvertHaskell.Parameters.Parsers

import HsToCoq.Util.Monad
import HsToCoq.Util.Messages
import HsToCoq.PrettyPrint hiding ((</>))
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.FreeVars
import HsToCoq.ProcessFiles
import HsToCoq.ConvertHaskell
import HsToCoq.ConvertHaskell.Parameters.Renamings
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
                               , renamingsFileArg     :: Maybe FilePath
                               , editsFileArg         :: Maybe FilePath
                               , processingModeArg    :: ProcessingMode
                               , modulesFilesArgs     :: [FilePath]
                               , modulesRootArg       :: Maybe FilePath
                               , importDirsArgs       :: [FilePath]
                               , includeDirsArgs      :: [FilePath]
                               , ghcOptionsArgs       :: [String]
                               , directInputFilesArgs :: [FilePath] }
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
                        
                        <*> optional (strOption       $  long    "renamings"
                                                      <> short   'r'
                                                      <> metavar "FILE"
                                                      <> help    "File with Haskell -> Coq identifier renamings")
                        
                        <*> optional (strOption       $  long    "edits"
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
                        
                        <*> many     (strOption       $  long    "import-dir"
                                                      <> short   'i'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for Haskell modules")
                        
                        <*> many     (strOption       $  long    "include-dir"
                                                      <> short   'I'
                                                      <> metavar "DIR"
                                                      <> help    "Directory to search for CPP `#include's")
                        
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
                     , _renamingsFile    :: !(Maybe FilePath)
                     , _editsFile        :: !(Maybe FilePath)
                     , _processingMode   :: !ProcessingMode
                     , _modulesFiles     :: ![FilePath]
                     , _modulesRoot      :: !(Maybe FilePath)
                     , _directInputFiles :: ![FilePath] }
            deriving (Eq, Ord, Show, Read)
makeLenses ''Config

processArgs :: GhcMonad m => m Config
processArgs = do
  ProgramArgs{..} <- liftIO $ customExecParser defaultPrefs{prefMultiSuffix="..."} argParserInfo
  
  let ghcArgs = let locate opt = mkGeneralLocated $ "command line (" ++ opt ++ ")"
                in map (locate "-i" . ("-i" ++)) importDirsArgs ++
                   map (locate "-I" . ("-I" ++)) includeDirsArgs ++
                   map (locate "--ghc")          ghcOptionsArgs
  
  (dflags, ghcRest, warnings) <- (parseDynamicFlagsCmdLine ?? ghcArgs) =<< getSessionDynFlags
  printAllIfPresent unLoc "Command-line argument warning" warnings
  printAllIfPresent unLoc "Ignored GHC arguments"         ghcRest
  
  void $ setSessionDynFlags dflags
  
  pure $ Config { _outputFile       = if outputFileArg == Just "-"
                                      then Nothing
                                      else outputFileArg
                , _preambleFile     = preambleFileArg
                , _renamingsFile    = renamingsFileArg
                , _editsFile        = editsFileArg
                , _processingMode   = processingModeArg
                , _modulesFiles     = modulesFilesArgs
                , _modulesRoot      = modulesRootArg
                , _directInputFiles = directInputFilesArgs }

parseModulesFiles :: (MonadIO m, MonadError String m)
                  => FilePath -> [FilePath] -> m [FilePath]
parseModulesFiles root files =
  let fullName name = root </> if ".hs" `isSuffixOf` name
                               then name
                               else name <.> "hs"
  in fmap (map fullName . resolveFileTrees) . forFold files $ \file ->
       exceptEither . parseFileTrees (Just file) =<< liftIO (readFile file)

--------------------------------------------------------------------------------

type WithModulePrinter m a = ModuleName -> (Handle -> m a) -> m a

processFilesMain :: GhcMonad m
                 => (WithModulePrinter (ConversionT m) () -> [TypecheckedModule] -> ConversionT m ())
                 -> m ()
processFilesMain process = do
  conf <- processArgs
  
  let parseConfigFile file builder parser =
        maybe (pure mempty) ?? (conf^.file) $ \filename -> liftIO $
          (evalParse parser <$> T.readFile filename) >>= \case
            Left  err -> die $ "Could not parse " ++ filename ++ ": " ++ err
            Right res -> either die pure $ builder res
  
  renamings  <- parseConfigFile renamingsFile buildRenamings parseRenamingList
  edits      <- parseConfigFile editsFile     buildEdits     parseEditList
  
  inputFiles <- either (liftIO . die) pure <=< runExceptT $
                  (++) <$> parseModulesFiles (conf^.modulesRoot.non "") (conf^.modulesFiles)
                       <*> pure (conf^.directInputFiles)
  
  preamble <- liftIO $ traverse readFile (conf^.preambleFile)
  let printPreamble hOut = liftIO . for_ preamble $ \contents -> do
        hPutStrLn hOut "(* Preamble *)"
        hPutStr   hOut contents
        hPutStrLn hOut ""
        hFlush    hOut
  
  withModulePrinter <- case conf^.outputFile of
    Nothing  -> printPreamble stdout $> \mod act -> do
        liftIO . putStrLn $ "(* " ++ moduleNameString mod ++ " *)"
        liftIO $ putStrLn ""
        act stdout
    Just outDir -> pure $ \mod act -> do
      let path = outDir </> moduleNameSlashes mod <.> "v"
      liftIO . createDirectoryIfMissing True $ takeDirectory path
      gWithFile path WriteMode $ \hOut -> do
        printPreamble hOut
        act hOut

  evalConversion renamings edits $
    traverse_ (process withModulePrinter) =<< processFiles (conf^.processingMode) inputFiles

printConvertedModule :: MonadIO m
                     => WithModulePrinter m ()
                     -> ConvertedModule
                     -> m ()
printConvertedModule withModulePrinter ConvertedModule{..} =
  withModulePrinter convModName $ \out -> liftIO $ do
    let flush    = hFlush out
        printGap = hPutStrLn out ""
        
        printThe what [] = hPutStrLn out $ "(* No " ++ what ++ " to convert. *)"
        printThe what ds = do hPutStrLn out $ "(* Converted " ++ what ++ ": *)"
                              traverse_ (hPrettyPrint out) . intersperse line $
                                map ((<> line) . renderGallina) ds
    
    printThe "imports"                          convModImports      <* printGap <* flush
    printThe "data type declarations"           convModTyClDecls    <* printGap <* flush
    printThe "value declarations"               convModValDecls     <* printGap <* flush
    printThe "type class instance declarations" convModClsInstDecls <*             flush
     
    case toList . getFreeVars . NoBinding $
           (convModTyClDecls ++ convModValDecls ++ convModClsInstDecls) of
      []  -> pure ()
      fvs -> do hPrettyPrint out $
                  line <> "(*" <+> hang 2
                    ("Unbound variables:" <!> fillSep (map text fvs))
                  <!> "*)" <> line
                flush

printConvertedModules :: MonadIO m
                      => WithModulePrinter m ()
                      -> [NonEmpty ConvertedModule]
                      -> m ()
printConvertedModules withModulePrinter =
  traverse_ (printConvertedModule withModulePrinter) . foldMap toList

convertAndPrintModules :: ConversionMonad m => WithModulePrinter m () -> [TypecheckedModule] -> m ()
convertAndPrintModules p = printConvertedModules p <=< convertModules <=< traverse toRenamed
  where toRenamed tcm
          | Just rn <- tm_renamed_source tcm = pure (mod, rn)
          | otherwise = throwProgramError $  "Renamer failed for `"
                                          ++ moduleNameString mod ++ "'"
          where mod = ms_mod_name . pm_mod_summary $ tm_parsed_module tcm
