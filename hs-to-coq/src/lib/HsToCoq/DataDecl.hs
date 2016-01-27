{-# LANGUAGE RecordWildCards,
             FlexibleContexts, UndecidableInstances,
             DeriveDataTypeable, StandaloneDeriving #-}

module HsToCoq.DataDecl (
  DataDecl'(..),
  toDataDecl', fromDataDecl',
  castDataDecl,
  getDataDecls
  ) where

import Data.Maybe

import Data.Data
import Data.Generics

import GHC
import NameSet

data DataDecl' id = DataDecl' { tcdLName'    :: Located id
                              , tcdTyVars'   :: LHsTyVarBndrs id
                              , tcdDataDefn' :: HsDataDefn id
                              , tcdFVs'      :: PostRn id NameSet }
                  deriving (Typeable)
deriving instance (DataId id) => Data (DataDecl' id)

toDataDecl' :: TyClDecl id -> Maybe (DataDecl' id)
toDataDecl' DataDecl{..} = Just $ DataDecl' { tcdLName'    = tcdLName
                                            , tcdTyVars'   = tcdTyVars
                                            , tcdDataDefn' = tcdDataDefn
                                            , tcdFVs'      = tcdFVs }
toDataDecl' _            = Nothing

fromDataDecl' :: DataDecl' id -> TyClDecl id
fromDataDecl' DataDecl'{..} = DataDecl { tcdLName    = tcdLName'
                                       , tcdTyVars   = tcdTyVars'
                                       , tcdDataDefn = tcdDataDefn'
                                       , tcdFVs      = tcdFVs' }

castDataDecl :: (Typeable a, Typeable id) => a -> Maybe (DataDecl' id)
castDataDecl d = toDataDecl' =<< cast d

getDataDecls :: (Data a, Typeable id) => a -> [DataDecl' id]
getDataDecls = everything (++) $ maybeToList . castDataDecl
