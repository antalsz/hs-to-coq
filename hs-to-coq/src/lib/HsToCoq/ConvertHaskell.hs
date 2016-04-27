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

{-
TODO: `types/TyCoRep.hs` uses implicit parameters!
  -- Stub them out, they're only for `error`!

Translating `basicTypes/{BasicTypes,Var,DataCon,ConLike,VarSet,VarEnv,SrcLoc}.hs`,
`types/{TyCon,Class,Coercion,CoAxiom}.hs`, coreSyn/CoreSyn.hs, and
`profiling/CostCentre.hs`:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

 181 record constructor patterns
  22 pattern guards
  21 record constructors
  21 record updates
  14 `do' expressions
  11 possibly-incomplete guards
--------------------------------
 270 TOTAL
-}
