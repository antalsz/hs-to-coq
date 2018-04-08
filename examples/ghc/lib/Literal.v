(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require BasicTypes.
Require Data.Maybe.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Enum.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Require Panic.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Literal : Type
  := MachChar : GHC.Char.Char -> Literal
  |  MachStr : GHC.Base.String -> Literal
  |  MachNullAddr : Literal
  |  MachInt : GHC.Num.Integer -> Literal
  |  MachInt64 : GHC.Num.Integer -> Literal
  |  MachWord : GHC.Num.Integer -> Literal
  |  MachWord64 : GHC.Num.Integer -> Literal
  |  MachFloat : GHC.Real.Rational -> Literal
  |  MachDouble : GHC.Real.Rational -> Literal
  |  MachLabel
   : FastString.FastString ->
     (option GHC.Num.Int) -> BasicTypes.FunctionOrData -> Literal
  |  LitInteger : GHC.Num.Integer -> unit -> Literal.

Instance Default__Literal : GHC.Err.Default Literal :=
  GHC.Err.Build_Default _ MachNullAddr.
(* Midamble *)


Parameter absent_lits :  UniqFM.UniqFM Literal.

Parameter inCharRange : GHC.Char.Char -> bool.

(* Converted value declarations: *)

(* Skipping instance Binary__Literal of class Binary *)

(* Skipping instance Outputable__Literal of class Outputable *)

(* Skipping instance Data__Literal of class Data *)

Definition char2IntLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachChar c => MachInt (GHC.Real.toInteger (GHC.Base.ord c))
    | l => Panic.panicStr (GHC.Base.hs_string__ "char2IntLit") (Panic.noString l)
    end.

Definition double2FloatLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachDouble d => MachFloat d
    | l =>
        Panic.panicStr (GHC.Base.hs_string__ "double2FloatLit") (Panic.noString l)
    end.

Definition float2DoubleLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachFloat f => MachDouble f
    | l =>
        Panic.panicStr (GHC.Base.hs_string__ "float2DoubleLit") (Panic.noString l)
    end.

Definition inIntRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool :=
  fun dflags x =>
    andb (x GHC.Base.>= DynFlags.tARGET_MIN_INT dflags) (x GHC.Base.<=
          DynFlags.tARGET_MAX_INT dflags).

Definition litIsDupable : DynFlags.DynFlags -> Literal -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, MachStr _ => false
    | dflags, LitInteger i _ => inIntRange dflags i
    | _, _ => true
    end.

Definition inWordRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool :=
  fun dflags x =>
    andb (x GHC.Base.>= #0) (x GHC.Base.<= DynFlags.tARGET_MAX_WORD dflags).

Definition int2CharLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachInt i => MachChar (GHC.Char.chr (GHC.Num.fromInteger i))
    | l => Panic.panicStr (GHC.Base.hs_string__ "int2CharLit") (Panic.noString l)
    end.

Definition int2DoubleLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachInt i => MachDouble (GHC.Num.fromInteger i)
    | l => Panic.panicStr (GHC.Base.hs_string__ "int2DoubleLit") (Panic.noString l)
    end.

Definition int2FloatLit : Literal -> Literal :=
  fun arg_0__ =>
    match arg_0__ with
    | MachInt i => MachFloat (GHC.Num.fromInteger i)
    | l => Panic.panicStr (GHC.Base.hs_string__ "int2FloatLit") (Panic.noString l)
    end.

Definition int2WordLit : DynFlags.DynFlags -> Literal -> Literal :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, MachInt i =>
        if i GHC.Base.< #0 : bool
        then MachWord ((#1 GHC.Num.+ DynFlags.tARGET_MAX_WORD dflags) GHC.Num.+ i) else
        MachWord i
    | _, _ =>
        match arg_0__, arg_1__ with
        | _, l => Panic.panicStr (GHC.Base.hs_string__ "int2WordLit") (Panic.noString l)
        end
    end.

Definition isLitValue_maybe : Literal -> option GHC.Num.Integer :=
  fun arg_0__ =>
    match arg_0__ with
    | MachChar c => Some (GHC.Real.toInteger (GHC.Base.ord c))
    | MachInt i => Some i
    | MachInt64 i => Some i
    | MachWord i => Some i
    | MachWord64 i => Some i
    | LitInteger i _ => Some i
    | _ => None
    end.

Definition litValue : Literal -> GHC.Num.Integer :=
  fun l =>
    match isLitValue_maybe l with
    | Some x => x
    | None => Panic.panicStr (GHC.Base.hs_string__ "litValue") (Panic.noString l)
    end.

Definition isLitValue : Literal -> bool :=
  Data.Maybe.isJust GHC.Base.∘ isLitValue_maybe.

Definition isZeroLit : Literal -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | MachInt num_1__ => if num_1__ GHC.Base.== #0 : bool then true else false
    | MachInt64 num_2__ => if num_2__ GHC.Base.== #0 : bool then true else false
    | MachWord num_3__ => if num_3__ GHC.Base.== #0 : bool then true else false
    | MachWord64 num_4__ => if num_4__ GHC.Base.== #0 : bool then true else false
    | MachFloat num_5__ => if num_5__ GHC.Base.== #0 : bool then true else false
    | MachDouble num_6__ => if num_6__ GHC.Base.== #0 : bool then true else false
    | _ => false
    end.

Definition litFitsInChar : Literal -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | MachInt i =>
        andb (i GHC.Base.>= GHC.Real.toInteger (GHC.Base.ord GHC.Enum.minBound)) (i
              GHC.Base.<=
              GHC.Real.toInteger (GHC.Base.ord GHC.Enum.maxBound))
    | _ => false
    end.

Definition litIsLifted : Literal -> bool :=
  fun arg_0__ => match arg_0__ with | LitInteger _ _ => true | _ => false end.

Definition litIsTrivial : Literal -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | MachStr _ => false
    | LitInteger _ _ => false
    | _ => true
    end.

Definition litTag : Literal -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | MachChar _ => #1
    | MachStr _ => #2
    | MachNullAddr => #3
    | MachInt _ => #4
    | MachWord _ => #5
    | MachInt64 _ => #6
    | MachWord64 _ => #7
    | MachFloat _ => #8
    | MachDouble _ => #9
    | MachLabel _ _ _ => #10
    | LitInteger _ _ => #11
    end.

Definition cmpLit : Literal -> Literal -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MachChar a, MachChar b => GHC.Base.compare a b
    | MachStr a, MachStr b => GHC.Base.compare a b
    | MachNullAddr, MachNullAddr => Eq
    | MachInt a, MachInt b => GHC.Base.compare a b
    | MachWord a, MachWord b => GHC.Base.compare a b
    | MachInt64 a, MachInt64 b => GHC.Base.compare a b
    | MachWord64 a, MachWord64 b => GHC.Base.compare a b
    | MachFloat a, MachFloat b => GHC.Base.compare a b
    | MachDouble a, MachDouble b => GHC.Base.compare a b
    | MachLabel a _ _, MachLabel b _ _ => GHC.Base.compare a b
    | LitInteger a _, LitInteger b _ => GHC.Base.compare a b
    | lit1, lit2 => if litTag lit1 GHC.Base.< litTag lit2 : bool then Lt else Gt
    end.

Local Definition Ord__Literal_compare : Literal -> Literal -> comparison :=
  fun a b => cmpLit a b.

Local Definition Ord__Literal_op_zg__ : Literal -> Literal -> bool :=
  fun a b =>
    match (Ord__Literal_compare a b) with
    | Lt => false
    | Eq => false
    | Gt => true
    end.

Local Definition Ord__Literal_op_zgze__ : Literal -> Literal -> bool :=
  fun a b =>
    match (Ord__Literal_compare a b) with
    | Lt => false
    | Eq => true
    | Gt => true
    end.

Local Definition Ord__Literal_op_zl__ : Literal -> Literal -> bool :=
  fun a b =>
    match (Ord__Literal_compare a b) with
    | Lt => true
    | Eq => false
    | Gt => false
    end.

Local Definition Ord__Literal_op_zlze__ : Literal -> Literal -> bool :=
  fun a b =>
    match (Ord__Literal_compare a b) with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

Local Definition Ord__Literal_max : Literal -> Literal -> Literal :=
  fun x y => if Ord__Literal_op_zlze__ x y : bool then y else x.

Local Definition Ord__Literal_min : Literal -> Literal -> Literal :=
  fun x y => if Ord__Literal_op_zlze__ x y : bool then x else y.

Local Definition Eq___Literal_op_zeze__ : Literal -> Literal -> bool :=
  fun a b => match cmpLit a b with | Eq => true | _ => false end.

Local Definition Eq___Literal_op_zsze__ : Literal -> Literal -> bool :=
  fun a b => match cmpLit a b with | Eq => false | _ => true end.

Program Instance Eq___Literal : GHC.Base.Eq_ Literal :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Literal_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Literal_op_zsze__ |}.

Program Instance Ord__Literal : GHC.Base.Ord Literal :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Literal_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Literal_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Literal_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Literal_op_zgze__ ;
         GHC.Base.compare__ := Ord__Literal_compare ;
         GHC.Base.max__ := Ord__Literal_max ;
         GHC.Base.min__ := Ord__Literal_min |}.

Definition mkLitInteger : GHC.Num.Integer -> unit -> Literal :=
  LitInteger.

Definition mkMachChar : GHC.Char.Char -> Literal :=
  MachChar.

Definition mkMachDouble : GHC.Real.Rational -> Literal :=
  MachDouble.

Definition mkMachFloat : GHC.Real.Rational -> Literal :=
  MachFloat.

Definition mkMachString : GHC.Base.String -> Literal :=
  fun s =>
    MachStr (FastString.fastStringToByteString (FastString.mkFastString s)).

Definition nullAddrLit : Literal :=
  MachNullAddr.

Definition word2IntLit : DynFlags.DynFlags -> Literal -> Literal :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, MachWord w =>
        if w GHC.Base.> DynFlags.tARGET_MAX_INT dflags : bool
        then MachInt ((w GHC.Num.- DynFlags.tARGET_MAX_WORD dflags) GHC.Num.- #1) else
        MachInt w
    | _, _ =>
        match arg_0__, arg_1__ with
        | _, l => Panic.panicStr (GHC.Base.hs_string__ "word2IntLit") (Panic.noString l)
        end
    end.

(* External variables:
     Eq Gt Lt None Some andb bool comparison false option true unit
     BasicTypes.FunctionOrData Data.Maybe.isJust DynFlags.DynFlags
     DynFlags.tARGET_MAX_INT DynFlags.tARGET_MAX_WORD DynFlags.tARGET_MIN_INT
     FastString.FastString FastString.fastStringToByteString FastString.mkFastString
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__
     GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zsze____ GHC.Base.ord GHC.Char.Char
     GHC.Char.chr GHC.Enum.maxBound GHC.Enum.minBound GHC.Err.Build_Default
     GHC.Err.Default GHC.Num.Int GHC.Num.Integer GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Real.Rational GHC.Real.toInteger Panic.noString
     Panic.panicStr
*)
