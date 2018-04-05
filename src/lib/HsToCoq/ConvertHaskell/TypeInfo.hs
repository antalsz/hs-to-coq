{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}

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
    -- * Derived utility functions
    , isConstructor
    ) where

import Control.Lens
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Control.Monad.State
import Data.Maybe

import HsToCoq.Coq.Gallina (Qualid, ClassDefinition(..), Term, Qualid(..))
import HsToCoq.ConvertHaskell.BuiltIn


data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Qualid]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

data TypeInfo = TypeInfo
    { _constructors      :: !(Map Qualid [Qualid])
    , _constructorTypes  :: !(Map Qualid Qualid)
    , _constructorFields :: !(Map Qualid ConstructorFields)
    , _recordFieldTypes  :: !(Map Qualid Qualid)
    , _classDefns        :: !(Map Qualid ClassDefinition)
    , _defaultMethods    :: !(Map Qualid (Map Qualid Term))
    }

makeLenses ''TypeInfo


runTypeInfoMonad :: Monad m => StateT TypeInfo m a -> m a
runTypeInfoMonad = evalStateT ?? TypeInfo{..}
  where
    _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
    _constructorTypes  = M.fromList [ (d, t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
    _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
    _recordFieldTypes  = M.empty
    _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
--    _memberSigs        = M.empty
    _defaultMethods    =   builtInDefaultMethods


isConstructor :: MonadState TypeInfo m => Qualid -> m Bool
isConstructor con = isJust <$> (use $ constructorTypes . at con)

