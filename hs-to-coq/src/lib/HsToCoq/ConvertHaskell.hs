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
   5 pattern matching on unknown record constructor `Refl'
   4 pattern matching on unknown record constructor `Anon'
   3 pattern matching on unknown record constructor `AbstractTyCon'
   3 pattern matching on unknown record constructor `ActiveBefore'
   3 pattern matching on unknown record constructor `LitTy'
   3 pattern matching on unknown record constructor `VanillaAlgTyCon'
   2 pattern matching on unknown record constructor `OneOcc'
   2 pattern matching on unknown record constructor `Type'
   1 multi-way if
   1 pattern matching on unknown record constructor `ClassTyCon'
   1 pattern matching on unknown record constructor `DataFamInstTyCon'
   1 pattern matching on unknown record constructor `DataFamilyTyCon'
   1 pattern matching on unknown record constructor `ForAllTy'
   1 pattern matching on unknown record constructor `GenericDM'
   1 pattern matching on unknown record constructor `HsUnpack'
   1 pattern matching on unknown record constructor `LocalId'
   1 pattern matching on unknown record constructor `NS_Step'
   1 pattern matching on unknown record constructor `Named'
   1 pattern matching on unknown record constructor `NotOrphan'
   1 pattern matching on unknown record constructor `PatSynCon'
   1 pattern matching on unknown record constructor `UnhelpfulSpan'
----------------------------------------------------------------------
 176 TOTAL
-}
