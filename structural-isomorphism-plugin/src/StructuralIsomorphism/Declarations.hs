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

constructor :: Con -> Maybe Constructor
constructor (NormalC conName conArguments) = Just Constructor{..}
constructor (RecC    conName fields)       = Just Constructor{ conArguments =
                                                                 [(s,ty) | (_,s,ty) <- fields]
                                                             , .. }
constructor (InfixC   arg1 conName arg2)   = Just Constructor{ conArguments = [arg1, arg2]
                                                             , .. }
constructor (ForallC  _tvs _cxt _con)      = Nothing
constructor (GadtC    _names _tys    _res) = Nothing
constructor (RecGadtC _names _fields _res) = Nothing

data DataType = DataType { dtContext      :: !Cxt
                         , dtName         :: !Name
                         , dtParameters   :: ![TyVarBndr]
                         , dtKind         :: !(Maybe Kind)
                         , dtConstructors :: ![Constructor]
                         , dtDeriving     :: !Cxt }
              deriving (Eq, Ord, Show)

dataType :: Dec -> Maybe DataType
dataType (DataD dtContext dtName dtParameters dtKind dtCons dtDeriving) = do
  dtConstructors <- traverse constructor dtCons
  Just DataType{..}
dataType (NewtypeD dtContext dtName dtParameters dtKind dtCon dtDeriving) = do
  dtConstructors <- pure <$> constructor dtCon
  Just DataType{..}
dataType _ =
  Nothing
