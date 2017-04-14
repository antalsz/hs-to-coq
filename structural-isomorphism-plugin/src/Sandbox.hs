{-# LANGUAGE MultiParamTypeClasses,
             RecordWildCards,
             ViewPatterns, LambdaCase,
             TemplateHaskell, MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-orphans #-}

module Sandbox where

import StructuralIsomorphism.Generate

import qualified DataCon     as GHC

import qualified SrcLoc      as GHC

import qualified Unique      as GHC
import qualified Name        as GHC
import qualified CoreSyn     as GHC
import qualified CoqCoreBind as Coq

structurallyIsomorphic ''GHC.Unique ''Coq.Unique
structurallyIsomorphic ''GHC.OccName ''Coq.OccName
structurallyIsomorphic ''GHC.SrcSpan ''Coq.SrcSpan

type Z a = [a]
                       
-- data X = X (Z Char)
-- data Y = Y String
data X = X Char
data Y = Y Char

structurallyIsomorphic ''X ''Y
--structurallyIsomorphic ''GHC.Name    ''Coq.Name
-- structurallyIsomorphic ''GHC.DataCon ''Coq.DataCon
