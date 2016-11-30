{-# LANGUAGE LambdaCase, RecordWildCards,
             OverloadedStrings,
             FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.CLI (
  processFilesMain,
  convertDecls,
  Config(..), outputFile, preambleFile, renamingsFile, editsFile, inputFiles,
  processArgs,
  ProgramArgs(..),
  argParser, argParserInfo,
  prettyPrint, hPrettyPrint
  ) where

import Control.Lens

import Data.Foldable
import Data.List (intersperse)

import Control.Monad
import Control.Monad.IO.Class

import Data.Data

import qualified Data.Text.IO as T
import System.IO
import System.Exit

import GHC hiding (outputFile)
import DynFlags hiding (outputFile)
import HsToCoq.Util.GHC.Exception

import Control.Monad.Trans.Parse
import HsToCoq.ConvertHaskell.Parameters.Parsers

import HsToCoq.Util.Functor
import HsToCoq.Util.Generics
import HsToCoq.Util.Messages
import HsToCoq.PrettyPrint
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.FreeVars
import HsToCoq.ProcessFiles
import HsToCoq.ConvertHaskell
import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits

import Options.Applicative hiding ((<>))
import HsToCoq.Util.Options.Applicative.Instances ()

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = hPrettyPrint stdout

data ProgramArgs = ProgramArgs { outputFileArg    :: Maybe FilePath
                               , preambleFileArg  :: Maybe FilePath
                               , renamingsFileArg :: Maybe FilePath
                               , editsFileArg     :: Maybe FilePath
                               , includeDirsArgs  :: [FilePath]
                               , ghcOptionsArgs   :: [String]
                               , inputFilesArgs   :: [FilePath] }
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
                        
                        <*> many     (strOption   $  long    "include-dir"
                                                  <> short   'I'
                                                  <> metavar "DIR"
                                                  <> help    "Directory to search for CPP `#include's")
                        
                        <*> many     (strOption   $  long    "ghc"
                                                  <> metavar "ARGUMENT"
                                                  <> help    "Option to pass through to GHC")
                        
                        <*> some     (strArgument $  metavar "FILES"
                                                  <> help    "Haskell files to translate into Coq")

argParserInfo :: ParserInfo ProgramArgs
argParserInfo = info (helper <*> argParser) $  fullDesc
                                            <> progDesc "Convert Haskell source files to Coq"

data Config = Config { _outputFile    :: !(Maybe FilePath)
                     , _preambleFile  :: !(Maybe FilePath)
                     , _renamingsFile :: !(Maybe FilePath)
                     , _editsFile     :: !(Maybe FilePath)
                     , _inputFiles    :: ![FilePath] }
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
  
  pure (dflags, Config { _outputFile    = if outputFileArg == Just "-"
                                          then Nothing
                                          else outputFileArg
                       , _preambleFile  = preambleFileArg
                       , _renamingsFile = renamingsFileArg
                       , _editsFile     = editsFileArg
                       , _inputFiles    = inputFilesArgs })

convertDecls :: (Data a, ConversionMonad m) => Handle -> a -> m ()
convertDecls out lmod = do
  let flush    = liftIO $ hFlush out
      printGap = liftIO $ hPutStrLn out ""
      
      doConversion what convert =
        convert (everythingOfType_ lmod) >>= liftIO .<$ \case
          [] -> hPutStrLn out $ "(* No " ++ what ++ " to convert. *)"
          ds -> do hPutStrLn out $ "(* Converted " ++ what ++ ": *)"
                   traverse_ (hPrettyPrint out) . intersperse line $
                     map ((<> line) . renderGallina) ds
  
  types <- doConversion "data type declarations"           convertTyClDecls    <* printGap <* flush
  funcs <- doConversion "function declarations"            convertValDecls     <* printGap <* flush
  insts <- doConversion "type class instance declarations" convertClsInstDecls <*             flush
  
  case toList . getFreeVars . NoBinding $ types ++ funcs ++ insts of
    []  -> pure ()
    fvs -> do hPrettyPrint out $
                line <> "(*" <+> hang 2
                  ("Unbound variables:" <!> fillSep (map text fvs))
                <!> "*)" <> line
              flush

processFilesMain :: GhcMonad m
                 => (Handle -> [Located (HsModule RdrName)] -> ConversionT m ())
                 -> m ()
processFilesMain process = do
  (dflags, conf) <- processArgs
  
  let die msg = hPutStrLn stderr msg *> exitFailure
      
      parseConfigFile file builder parser =
        maybe (pure mempty) ?? (conf^.file) $ \filename -> liftIO $
          (evalParse parser <$> T.readFile filename) >>= \case
            Left  err -> die $ "Could not parse " ++ filename ++ ": " ++ err
            Right res -> either die pure $ builder res
  
  renamings <- parseConfigFile renamingsFile buildRenamings parseRenamingList
  edits     <- parseConfigFile editsFile     buildEdits     parseEditList
  
  evalConversion renamings edits .
    maybe ($ stdout) (flip gWithFile WriteMode) (conf^.outputFile) $ \hOut -> do
      for_ (conf^.preambleFile) $ \file -> liftIO $ do
        hPutStrLn hOut "(* Preamble *)"
        hPutStr   hOut =<< readFile file
        hPutStrLn hOut ""
        hFlush    hOut
       
      traverse_ (process hOut) =<< processFiles dflags (conf^.inputFiles)
      liftIO $ hFlush hOut
