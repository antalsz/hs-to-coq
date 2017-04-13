{-# LANGUAGE MultiParamTypeClasses,
             RecordWildCards,
             ViewPatterns, LambdaCase,
             TemplateHaskell, MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-imports -fno-warn-orphans #-}

module Sandbox where

import GHC.Exts

import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

import StructuralIsomorphism.TH.Util
import StructuralIsomorphism.Util
import StructuralIsomorphism.Class
import StructuralIsomorphism.Declarations
import StructuralIsomorphism.Isomorphizing
import StructuralIsomorphism.Generate

import qualified DataCon     as GHC

import qualified SrcLoc      as GHC

import qualified Unique      as GHC
import qualified Name        as GHC
import qualified CoreSyn     as GHC
import qualified CoqCoreBind as Coq

data U    = UU           deriving Show
data Loob = Eslaf | Eurt deriving Show

data Mix = Zero | One () | Two Bool | Three () Bool | Also () Bool | Inf [Mix] deriving Show
data Xim = Orez | Eno U  | Owt Loob | Eerht U  Loob | Osla U  Loob | Fni [Xim] deriving Show
         
$(structurallyIsomorphic ''Mix ''Xim)

instance StructurallyIsomorphic GHC.Unique Coq.Unique where
   to   unique                = Coq.Mk_MkUnique (GHC.getKey unique)
   from (Coq.Mk_MkUnique int) = GHC.mkUniqueGrimily int

instance StructurallyIsomorphic Coq.Unique GHC.Unique where to = from ; from = to

$(structurallyIsomorphic ''GHC.OccName ''Coq.OccName)
-- $(structurallyIsomorphic ''GHC.SrcSpan ''Coq.SrcSpan)

-- do ghcName <- TH.reify ''GHC.Name >>= \case
--                 TH.TyConI (dataType ->
--                              Just DataType{dtConstructors =
--                                              [constructor -> Constructor{..}]}) ->
--                   pure conName
--                 _ ->
--                   fail "Could not find `Name.Name' constructor"
--    sort <- TH.newName "sort"
--    occ  <- TH.newName "occ"
--    uniq <- TH.newName "uniq"
--    loc  <- TH.newName "loc"
--    [d| instance StructurallyIsomorphic GHC.Name Coq.Name where
--          to $(TH.conP ghcName $ map TH.varP [sort,occ,uniq,loc]) =
--            Coq.Mk_Name (to $(TH.varE sort))
--                        (to $(TH.varE occ))
--                        (I# $(TH.varE uniq))
--                        (to $(TH.varE loc))  |]

-- [d|instance StructurallyIsomorphic GHC.Name Coq.Name where
--      to    = Coq.Mk_Name sort occ uniq loc
--      from (Coq.Mk_Name sort occ uniq loc) = GHC.Name    sort occ uniq loc|]

-- instance StructurallyIsomorphic Coq.Name GHC.Name where to = from ; from = to

-- $(structurallyIsomorphic ''GHC.DataCon ''Coq.DataCon)
