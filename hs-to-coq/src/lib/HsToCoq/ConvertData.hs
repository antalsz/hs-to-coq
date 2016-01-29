{-# LANGUAGE RecordWildCards #-}

module HsToCoq.ConvertData (showName, readDataDecls, convert) where

import Data.Foldable
import Data.List

import Control.Monad.IO.Class
import Control.Monad.Writer

import GHC
import RdrName
import OccName
import Panic

import HsToCoq.Util.GHC
import HsToCoq.DataDecl
import HsToCoq.ProcessFiles

showName :: GhcMonad m => RdrName -> m String
showName = ghcSDoc . pprOccName . rdrNameOcc

readDataDecls :: GhcMonad m => DynFlags -> FilePath -> m [DataDecl' RdrName]
readDataDecls dflags file =   processFile (pure . getDataDecls) dflags file
                          >>= maybe ( liftIO . throwGhcExceptionIO
                                    . ProgramError $ file ++ ": no parse" )
                                    pure

data Type' = Type
          deriving (Eq, Ord, Show)

data Binder = Plain { bName :: String }
            | Typed { bName :: String, bType :: Type' }
            deriving (Eq, Ord, Show)

data Inductive = Inductive { iName   :: String
                           , iParams :: [Binder]
                           , iType   :: Type'
                           , iCons   :: [Constructor] }

data Constructor = Constructor { cName :: String
                               , cType :: Type' }

convert :: GhcMonad m => DataDecl' RdrName -> m String
convert DataDecl'{tcdDataDefn' = HsDataDefn{..}, ..} = execWriterT $ do
  let lname = lift . showName . unLoc
  dname <- lname tcdLName'
  tell $ "Inductive " ++ dname ++ " :=\n"
  for_ dd_cons $ \(L _ ConDecl{..}) -> do
    tell "  | "
    tell . intercalate ", " =<< traverse lname con_names
    tell " : \n"
  tell ".\n"
