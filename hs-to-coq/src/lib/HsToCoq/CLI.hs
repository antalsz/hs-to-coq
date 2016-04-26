{-# LANGUAGE LambdaCase, FlexibleContexts, OverloadedStrings #-}

module HsToCoq.CLI (
  processFilesMain,
  convertDecls,
  processArgs,
  prettyPrint
  ) where

import Data.Foldable
import Data.List (intersperse)

import Control.Monad
import Control.Monad.IO.Class

import Data.Data

import System.IO
import System.Environment

import GHC
import DynFlags

import HsToCoq.Util.Functor
import HsToCoq.Util.Generics
import HsToCoq.Util.Messages
import HsToCoq.PrettyPrint
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.FreeVars
import HsToCoq.ProcessFiles
import HsToCoq.ConvertHaskell

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = liftIO . displayIO stdout . renderPretty 0.67 120

processArgs :: GhcMonad m => m (DynFlags, [FilePath])
processArgs = do
  (dflags, files, warnings) <- join $
    parseDynamicFlagsCmdLine
      <$> getSessionDynFlags
      <*> (map (mkGeneralLocated "command line") <$> liftIO getArgs)
  printAllIfPresent unLoc "Command-line argument warning" warnings
  void $ setSessionDynFlags dflags
  pure (dflags, map unLoc files)

convertDecls :: (Data a, ConversionMonad m) => a -> m ()
convertDecls lmod = do
  let doConversion what convert =
        convert (everythingOfType_ lmod) >>= liftIO .<$ \case
          [] -> putStrLn $ "(* No " ++ what ++ " to convert. *)"
          ds -> do putStrLn $ "(* Converted " ++ what ++ ": *)"
                   traverse_ prettyPrint . intersperse line $
                     map ((<> line) . renderGallina) ds
  
  types <- doConversion "data type declarations"           convertTyClDecls    <* liftIO (putStrLn "")
  funcs <- doConversion "function declarations"            convertValDecls     <* liftIO (putStrLn "")
  insts <- doConversion "type class instance declarations" convertClsInstDecls
  
  case toList . getFreeVars . NoBinding $ types ++ funcs ++ insts of
    []  -> pure ()
    fvs -> prettyPrint $
             line <> "(*" <+> hang 2
               ("Unbound variables:" <!> fillSep (map text fvs))
             <!> "*)" <> line

processFilesMain :: GhcMonad m => ([Located (HsModule RdrName)] -> m a) -> m ()
processFilesMain f = traverse_ f =<< uncurry processFiles =<< processArgs
