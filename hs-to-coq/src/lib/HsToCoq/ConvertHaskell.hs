module HsToCoq.ConvertHaskell (module ConvertHaskell) where

import HsToCoq.ConvertHaskell.Monad                    as ConvertHaskell
import HsToCoq.ConvertHaskell.InfixNames               as ConvertHaskell
import HsToCoq.ConvertHaskell.Variables                as ConvertHaskell
import HsToCoq.ConvertHaskell.Definitions              as ConvertHaskell
import HsToCoq.ConvertHaskell.Literals                 as ConvertHaskell
import HsToCoq.ConvertHaskell.Type                     as ConvertHaskell
import HsToCoq.ConvertHaskell.Expr                     as ConvertHaskell
import HsToCoq.ConvertHaskell.Pattern                  as ConvertHaskell
import HsToCoq.ConvertHaskell.Sigs                     as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.Notations   as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.TypeSynonym as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.DataType    as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.Class       as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.Instances   as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.TyCl        as ConvertHaskell
import HsToCoq.ConvertHaskell.Declarations.Value       as ConvertHaskell
import HsToCoq.ConvertHaskell.Axiomatize               as ConvertHaskell

{-
Translating `basicTypes/{BasicTypes,Var,DataCon,ConLike,VarSet,VarEnv,SrcLoc}.hs`,
`types/{TyCon,Class,Coercion,TyCoRep,CoAxiom}.hs`, coreSyn/CoreSyn.hs, and
`profiling/CostCentre.hs`:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  39 pattern guards
  28 `do' expressions
  28 record constructors
  25 record updates
  18 possibly-incomplete guards
   5 pattern-matching on unknown record constructor `Mk_Refl'
   4 pattern-matching on unknown record constructor `Mk_Anon'
   3 pattern-matching on unknown record constructor `Mk_AbstractTyCon'
   3 pattern-matching on unknown record constructor `Mk_ActiveBefore'
   3 pattern-matching on unknown record constructor `Mk_LitTy'
   3 pattern-matching on unknown record constructor `Mk_VanillaAlgTyCon'
   2 pattern-matching on unknown record constructor `Mk_OneOcc'
   2 pattern-matching on unknown record constructor `Mk_Type'
   1 multi-way if
   1 pattern-matching on unknown record constructor `Mk_ClassTyCon'
   1 pattern-matching on unknown record constructor `Mk_DataFamInstTyCon'
   1 pattern-matching on unknown record constructor `Mk_DataFamilyTyCon'
   1 pattern-matching on unknown record constructor `Mk_ForAllTy'
   1 pattern-matching on unknown record constructor `Mk_GenericDM'
   1 pattern-matching on unknown record constructor `Mk_HsUnpack'
   1 pattern-matching on unknown record constructor `Mk_LocalId'
   1 pattern-matching on unknown record constructor `Mk_NS_Step'
   1 pattern-matching on unknown record constructor `Mk_Named'
   1 pattern-matching on unknown record constructor `Mk_NotOrphan'
   1 pattern-matching on unknown record constructor `Mk_PatSynCon'
   1 pattern-matching on unknown record constructor `Mk_UnhelpfulSpan'
-------------------------------------------------------------------------
 176 TOTAL
-}
