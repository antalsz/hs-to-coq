{-# LANGUAGE MultiParamTypeClasses,
             RecordWildCards,
             ViewPatterns, LambdaCase,
             TemplateHaskell, MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-orphans #-}

module Sandbox where

import StructuralIsomorphism.Generate

import qualified Var         as GHC
import qualified CoreSyn     as GHC
import qualified CoqCoreBind as Coq

structurallyIsomorphic ''GHC.Var  ''Coq.Var
structurallyIsomorphic ''GHC.Bind ''Coq.Bind
