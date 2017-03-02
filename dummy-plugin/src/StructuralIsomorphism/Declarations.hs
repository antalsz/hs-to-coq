{-# LANGUAGE RecordWildCards #-}

module StructuralIsomorphism.Declarations (
  -- * Types
  Constructor(..), DataType(..),
  -- * Map from Template Haskell to these simpler types
  constructor, dataType
) where

import Language.Haskell.TH.Syntax

data Constructor = Constructor { conName      :: !Name
                               , conArguments :: ![StrictType] }
                 deriving (Eq, Ord, Show)

constructor :: Con -> Constructor
constructor (NormalC conName conArguments) = Constructor{..}
constructor (RecC    conName fields)       = Constructor{ conArguments =
                                                            [(s,ty) | (_,s,ty) <- fields]
                                                        , .. }
constructor (InfixC   arg1 conName arg2)   = Constructor{ conArguments = [arg1, arg2]
                                                        , .. }
constructor (ForallC  _tvs _cxt con)       = constructor con
  -- Let GHC error later if we have incompatible existentials

data DataType = DataType { dtContext      :: !Cxt
                         , dtName         :: !Name
                         , dtParameters   :: ![TyVarBndr]
                         , dtConstructors :: ![Con]
                         , dtDeriving     :: ![Name] }
              deriving (Eq, Ord, Show)

dataType :: Dec -> Maybe DataType
dataType (DataD dtContext dtName dtParameters dtConstructors dtDeriving) =
  Just $ DataType{..}
dataType (NewtypeD dtContext dtName dtParameters dtConstructor dtDeriving) =
  Just $ DataType{dtConstructors = [dtConstructor], ..}
dataType _ =
  Nothing
