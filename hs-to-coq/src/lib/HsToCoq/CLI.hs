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
  -- * CLI configuration, parameters, etc.
  Config(..), outputFile, preambleFile, renamingsFile, editsFile, modulesFiles, modulesRoot, directInputFiles,
  processArgs,
  ProgramArgs(..),
  argParser, argParserInfo,
  -- * Utility functions
  prettyPrint, hPrettyPrint,
  -- * Renamer
  processFilesMainRn, convertAndPrintModulesRn
  ) where

import Control.Lens

import Data.Foldable
import Data.Traversable
import Data.List (intersperse, isSuffixOf)

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Except

import System.FilePath
import qualified Data.Text.IO as T
import System.IO
import System.Exit

import GHC hiding (outputFile)
import DynFlags hiding (outputFile)
import HsToCoq.Util.GHC.Exception

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
                               , modulesFilesArgs     :: [FilePath]
                               , modulesRootArg       :: Maybe FilePath
                               , includeDirsArgs      :: [FilePath]
                               , ghcOptionsArgs       :: [String]
                               , directInputFilesArgs :: [FilePath] }
                 deriving (Eq, Ord, Show, Read)

argParser :: Parser ProgramArgs
argParser = ProgramArgs <$> optional (strOption   $  long    "output"
                                                  <> short   'o'
                                                  <> metavar "FILE"
                                                  <> help    "File to write the translated Coq code to (defaults to stdout)")
                        
                        <*> optional (strOption   $  long    "preamble"
                                                  <> short   'p'
                                                  <> metavar "FILE"
                                                  <> help    "File containing code that goes at the top of the Coq output")
                        
                        <*> optional (strOption   $  long    "renamings"
                                                  <> short   'r'
                                                  <> metavar "FILE"
                                                  <> help    "File with Haskell -> Coq identifier renamings")
                        
                        <*> optional (strOption   $  long    "edits"
                                                  <> short   'e'
                                                  <> metavar "FILE"
                                                  <> help    "File with extra Haskell -> Coq edits")
                        
                        <*> many     (strOption   $  long    "modules"
                                                  <> short   'm'
                                                  <> metavar "FILE"
                                                  <> help    "File listing Haskell files to translate into Coq, in an indented tree structure")
                        
                        <*> optional (strOption   $  long    "modules-dir"
                                                  <> short   'd'
                                                  <> metavar "DIR"
                                                  <> help    "The directory the module tree files' contents are rooted at")
                        
                        <*> many     (strOption   $  long    "include-dir"
                                                  <> short   'I'
                                                  <> metavar "DIR"
                                                  <> help    "Directory to search for CPP `#include's")
                        
                        <*> many     (strOption   $  long    "ghc"
                                                  <> metavar "ARGUMENT"
                                                  <> help    "Option to pass through to GHC")
                        
                        <*> many     (strArgument $  metavar "FILES"
                                                  <> help    "Haskell files to translate into Coq")

argParserInfo :: ParserInfo ProgramArgs
argParserInfo = info (helper <*> argParser) $  fullDesc
                                            <> progDesc "Convert Haskell source files to Coq"

data Config = Config { _outputFile       :: !(Maybe FilePath)
                     , _preambleFile     :: !(Maybe FilePath)
                     , _renamingsFile    :: !(Maybe FilePath)
                     , _editsFile        :: !(Maybe FilePath)
                     , _modulesFiles     :: ![FilePath]
                     , _modulesRoot      :: !(Maybe FilePath)
                     , _directInputFiles :: ![FilePath] }
            deriving (Eq, Ord, Show, Read)
makeLenses ''Config

processArgs :: GhcMonad m => m (DynFlags, Config)
processArgs = do
  ProgramArgs{..} <- liftIO $ customExecParser defaultPrefs{prefMultiSuffix="..."} argParserInfo
  
  let ghcArgs = let locate opt = mkGeneralLocated $ "command line (" ++ opt ++ ")"
                in map (locate "-I" . ("-I" ++)) includeDirsArgs ++
                   map (locate "--ghc")          ghcOptionsArgs
  
  (dflags, ghcRest, warnings) <- (parseDynamicFlagsCmdLine ?? ghcArgs) =<< getSessionDynFlags
  printAllIfPresent unLoc "Command-line argument warning" warnings
  printAllIfPresent unLoc "Ignored GHC arguments"         ghcRest
  
  void $ setSessionDynFlags dflags
  
  pure (dflags, Config { _outputFile       = if outputFileArg == Just "-"
                                             then Nothing
                                             else outputFileArg
                       , _preambleFile     = preambleFileArg
                       , _renamingsFile    = renamingsFileArg
                       , _editsFile        = editsFileArg
                       , _modulesFiles     = modulesFilesArgs
                       , _modulesRoot      = modulesRootArg
                       , _directInputFiles = directInputFilesArgs })

parseModulesFiles :: (MonadIO m, MonadError String m)
                  => FilePath -> [FilePath] -> m [FilePath]
parseModulesFiles root files =
  let fullName name = root </> if ".hs" `isSuffixOf` name
                               then name
                               else name ++ ".hs"
  in fmap (map fullName . resolveFileTrees . concat) . for files $ \file ->
       exceptEither . parseFileTrees (Just file) =<< liftIO (readFile file)

processFilesMain :: GhcMonad m
                 => (Handle -> [Located (HsModule RdrName)] -> ConversionT m ())
                 -> m ()
processFilesMain process = do
  (dflags, conf) <- processArgs
  
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
  
  evalConversion renamings edits .
    maybe ($ stdout) (flip gWithFile WriteMode) (conf^.outputFile) $ \hOut -> do
      for_ (conf^.preambleFile) $ \file -> liftIO $ do
        hPutStrLn hOut "(* Preamble *)"
        hPutStr   hOut =<< readFile file
        hPutStrLn hOut ""
        hFlush    hOut
      
      traverse_ (process hOut) =<< processFiles dflags inputFiles
      liftIO $ hFlush hOut

processFilesMainRn :: GhcMonad m
                   => (Handle -> [TypecheckedModule] -> ConversionT m ())
                   -> m ()
processFilesMainRn process = do
  (dflags, conf) <- processArgs
  
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
  
  evalConversion renamings edits .
    maybe ($ stdout) (flip gWithFile WriteMode) (conf^.outputFile) $ \hOut -> do
      for_ (conf^.preambleFile) $ \file -> liftIO $ do
        hPutStrLn hOut "(* Preamble *)"
        hPutStr   hOut =<< readFile file
        hPutStrLn hOut ""
        hFlush    hOut
      
      traverse_ (process hOut) =<< tcRnFiles dflags inputFiles
      liftIO $ hFlush hOut

printConvertedModules :: MonadIO m => Handle -> ConvertedModules -> m ()
printConvertedModules out ConvertedModules{..} = liftIO $ do
  let flush    = hFlush out
      printGap = hPutStrLn out ""
      
      printThe what [] = hPutStrLn out $ "(* No " ++ what ++ " to convert. *)"
      printThe what ds = do hPutStrLn out $ "(* Converted " ++ what ++ ": *)"
                            traverse_ (hPrettyPrint out) . intersperse line $
                              map ((<> line) . renderGallina) ds
  
  printThe "data type declarations"           convertedTyClDecls    <* printGap <* flush
  printThe "value declarations"               convertedValDecls     <* printGap <* flush
  printThe "type class instance declarations" convertedClsInstDecls <*             flush
  
  case toList . getFreeVars . NoBinding $
         (convertedTyClDecls ++ convertedValDecls ++ convertedClsInstDecls) of
    []  -> pure ()
    fvs -> do hPrettyPrint out $
                line <> "(*" <+> hang 2
                  ("Unbound variables:" <!> fillSep (map text fvs))
                <!> "*)" <> line
              flush

convertAndPrintModules :: ConversionMonad m => Handle -> [Located (HsModule RdrName)] -> m ()
convertAndPrintModules h = printConvertedModules h <=< convertLModules

convertAndPrintModulesRn :: ConversionMonad m => Handle -> [TypecheckedModule] -> m ()
convertAndPrintModulesRn h =   printConvertedModules h
                           <=< convertHsGroups
                           <=< traverse toModGroup
  where toModGroup tcm
          | Just (grp,_,_,_) <- tm_renamed_source tcm = pure (mod, grp)
          | otherwise = throwProgramError $  "Renamer failed for `"
                                          ++ moduleNameString mod ++ "'"
          where mod = moduleName . ms_mod . pm_mod_summary $ tm_parsed_module tcm
              
