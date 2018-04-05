{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module maintains the TypeInfo data structure, which contains
-- the information about the type and type classes that we need throughout
-- the conversion of code where they are used.
module HsToCoq.ConvertHaskell.TypeInfo
    ( -- * Types
      TypeInfo
    , constructors, constructorTypes, constructorFields
    , recordFieldTypes, classDefns, defaultMethods
    , ConstructorFields(..)
    , _RecordFields
    -- * The Monad
    , runTypeInfoMonad
    , TypeInfoMonad(..)
    -- * Derived utility functions
    , isConstructor
    ) where

import Control.Lens
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Counter
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer
import HsToCoq.Util.GHC.Monad
import HsToCoq.Util.GHC.Exception
import HsToCoq.Util.GHC.DynFlags
import Data.Maybe

import HsToCoq.Coq.Gallina (Qualid, ClassDefinition(..), Term, Qualid(..))
import HsToCoq.ConvertHaskell.BuiltIn


data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Qualid]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

type TypeName        = Qualid
type ConstructorName = Qualid
type ClassName       = Qualid
type MethodName      = Qualid

type DefaultMethods = Map MethodName Term

data TypeInfo = TypeInfo
    { _constructors      :: !(Map TypeName [ConstructorName])
    , _constructorTypes  :: !(Map ConstructorName TypeName)
    , _constructorFields :: !(Map ConstructorName ConstructorFields)
    , _recordFieldTypes  :: !(Map ConstructorName TypeName)
    , _classDefns        :: !(Map ClassName ClassDefinition)
    , _defaultMethods    :: !(Map ClassName DefaultMethods)
    }

makeLenses ''TypeInfo

newtype TypeInfoT m a = TypeInfoT (StateT TypeInfo m a)
  deriving ( Functor, Applicative, Monad, MonadIO, ExceptionMonad
           , HasDynFlags, MonadTrans)

-- | This type class provides an interface to look up type and type class
-- information, and to register such information.
--
-- It will eventually implement, nicely hidden, interface loading and writing
class Monad m => TypeInfoMonad m where
    lookupConstructors      :: TypeName        -> m (Maybe [ConstructorName])
    lookupConstructorType   :: ConstructorName -> m (Maybe TypeName)
    lookupConstructorFields :: ConstructorName -> m (Maybe ConstructorFields)
    lookupRecordFieldType   :: ConstructorName -> m (Maybe TypeName)
    lookupClassDefn         :: ClassName       -> m (Maybe ClassDefinition)
    lookupDefaultMethods    :: ClassName       -> m (Maybe (Map MethodName Term))

    storeConstructors       :: TypeName        -> [ConstructorName]   -> m ()
    storeConstructorType    :: ConstructorName -> TypeName            -> m ()
    storeConstructorFields  :: ConstructorName -> ConstructorFields   -> m ()
    storeRecordFieldType    :: ConstructorName -> TypeName            -> m ()
    storeClassDefn          :: ClassName       -> ClassDefinition     -> m ()
    storeDefaultMethods     :: ClassName       -> Map MethodName Term -> m ()

instance Monad m => TypeInfoMonad (TypeInfoT m) where
    lookupConstructors      ty = TypeInfoT $ use $ constructors      . at ty
    lookupConstructorType   cn = TypeInfoT $ use $ constructorTypes  . at cn
    lookupConstructorFields cn = TypeInfoT $ use $ constructorFields . at cn
    lookupRecordFieldType   cn = TypeInfoT $ use $ recordFieldTypes  . at cn
    lookupClassDefn         cl = TypeInfoT $ use $ classDefns        . at cl
    lookupDefaultMethods    cl = TypeInfoT $ use $ defaultMethods    . at cl

    storeConstructors      ty x = TypeInfoT $ constructors      . at ty ?= x
    storeConstructorType   cn x = TypeInfoT $ constructorTypes  . at cn ?= x
    storeConstructorFields cn x = TypeInfoT $ constructorFields . at cn ?= x
    storeRecordFieldType   cn x = TypeInfoT $ recordFieldTypes  . at cn ?= x
    storeClassDefn         cl x = TypeInfoT $ classDefns        . at cl ?= x
    storeDefaultMethods    cl x = TypeInfoT $ defaultMethods    . at cl ?= x

runTypeInfoMonad :: Monad m => TypeInfoT m a -> m a
runTypeInfoMonad (TypeInfoT act) = evalStateT act TypeInfo{..}
  where
    _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
    _constructorTypes  = M.fromList [ (d, t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
    _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
    _recordFieldTypes  = M.empty
    _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
--    _memberSigs        = M.empty
    _defaultMethods    =   builtInDefaultMethods


isConstructor :: TypeInfoMonad m => Qualid -> m Bool
isConstructor con = isJust <$> lookupConstructorType con

-- Boiler plate instances

instance TypeInfoMonad m => TypeInfoMonad (ReaderT s m) where
    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance TypeInfoMonad m => TypeInfoMonad (CounterT m) where
    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance (TypeInfoMonad m, Monoid s) => TypeInfoMonad (WriterT s m) where
    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance TypeInfoMonad m => TypeInfoMonad (MaybeT m) where
    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance GhcMonad m => GhcMonad (TypeInfoT m) where
  getSession = lift   getSession
  setSession = lift . setSession


