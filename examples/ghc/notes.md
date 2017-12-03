First goal is to produce *some* part of as many modules related to call-arity
analysis as possible.  Then, we will go back to fill in the details.


HANDMOD
=======
- Panic

To account for some partial functions, define a "default value" type class and
then add that constraint to "Panic.panic". The default value is evidence that
we *could* return an answer, but the panic is a note that we don't want to do
so.

- FastString

This module redefines FastString as String (axiomatizing all of the operations).

- Util

This is a huge grab-bag. Should add definitions to this file on demand.

- Maybes

Should go back and generate this. Needs mtl though.


Generated Modules
=================

-  MonadUtils

IO stuff, partial function

-  Pair
-  Bag
-  SrcLoc
-  BasicTypes

char constants
show instances
outputtable

-  Unique
-  UniqSupply
-  UniqFM
-  CmmType

derive instance issue
recursive eq definition
show instances
Word8
platform constants (shouldn't ever need these)

-  BooleanFormula

some definitions in midamble because of termination issue

-  UniqSet
-  OccName

outputtable/show dependencies

needs Util.dropWhileEndLE GHC.Unicode.isDigit
character constants

cannot derive Ord for OccName (TODO: define by hand)

-  Module

axiomatized
still needs Data.Map.Base, FiniteMap
skip FilePath related stuff
Ord instances for module type guess wrong

-  DynFlags

axiomatized
some types "stubbed out" so that they don't bring in irrelevant information

DynFlags.Settings : Type := Mk_Settings.
DynFlags.FlushOut : Type := Mk_FlushOut.
DynFlags.FlushErr : Type := Mk_FlushErr.
DynFlags.DynFlags : Type := Mk_DynFlags.
DynFlags.FlagSpec (flag:Type) : Type := Mk_FlagSpec.

needs mtl for part of it

-  UniqDFM
-  UniqDSet
-  Name

Stubbed out the "TyCoRep.TyThing" component of the Name.Name type to resolve
the mutual definition.


-  NameEnv

Partial function (NameEnv.lookupNameEnv_NF), cannot process error message
TODO: Not obviously terminating function (NameEnv.depAnal)

-  Var

Stubbed out IdInfo/IdDetails/Type/Kind/TcTyVarDetails components of
Var so that this module is not mutual.

The partial record selectors are troublesome. This module redefines error ->
Panic.panic in the preamble as a workaround.
However, redefine/skip edits don't work with record selectors.

-  VarSet

Some operations are not obviously terminating (i.e. fixpoint calculations)
fixVarSet, transCloDVarSet, transCloVarSet

TODO: needs UniqSet.partitionUniqSet

-  VarEnv

TODO: needs Util.zipEqual, Util.foldl2

-  FastStringEnv

skip partial lookup function (uses show in error message)

-  FieldLabel

- Literal

Ignoring type component of literal

rename type TyCoRep.Type_   = unit

Big mutual type
================

#  Name    -- Name, NameSort
  refers to IdInfo, IdDetails
#  Var, refers to Type/Kind, TcTyVarDetails, IdDetails, IdInfo (currently stubbed)

#  TyCon    -- AlgTyConFlav, TyCon, AlgTyConRhs
#  Class    -- Class, ClassATItem
#  CoAxiom  -- CoAxiom, Branches, CoAxBranch
#  TyCoRep  -- TyThing, TyBinder, UnivCoProvenance
#  DataCon  -- DataCon, DataConRep, HsImplBang, EqSpec
#  Coercion -- Coercion
#  Type     -- Type_
#  CoercionHole -- TcEvidence
