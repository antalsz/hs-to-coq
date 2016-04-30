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

 193 record constructor patterns
  30 pattern guards
  25 `do' expressions
  21 record constructors
  21 record updates
  15 possibly-incomplete guards
   1 multi-way if
--------------------------------
 306 TOTAL
-}
