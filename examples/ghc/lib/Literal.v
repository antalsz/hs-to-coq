(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Literal : Type := MachChar : GHC.Char.Char -> Literal
                         |  MachStr : GHC.Base.String -> Literal
                         |  MachNullAddr : Literal
                         |  MachInt : GHC.Num.Integer -> Literal
                         |  MachInt64 : GHC.Num.Integer -> Literal
                         |  MachWord : GHC.Num.Integer -> Literal
                         |  MachWord64 : GHC.Num.Integer -> Literal
                         |  MachFloat : GHC.Real.Rational -> Literal
                         |  MachDouble : GHC.Real.Rational -> Literal
                         |  MachLabel : FastString.FastString -> (option
                                        GHC.Num.Int) -> BasicTypes.FunctionOrData -> Literal
                         |  LitInteger : GHC.Num.Integer -> unit -> Literal.
(* Midamble *)

Instance Default_Literal : Panic.Default Literal :=
  Panic.Build_Default _ MachNullAddr.

Parameter absent_lits :  UniqFM.UniqFM Literal.

Parameter inCharRange : GHC.Char.Char -> bool.

(* Converted value declarations: *)

(* Translating `instance Binary.Binary Literal.Literal' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable.Outputable Literal.Literal' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Data.Data.Data Literal.Literal' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Definition char2IntLit : Literal -> Literal :=
  fun arg_70__ =>
    match arg_70__ with
      | MachChar c => MachInt (GHC.Real.toInteger (GHC.Char.ord c))
      | l => Panic.panicStr (GHC.Base.hs_string__ "char2IntLit") (Panic.noString l)
    end.

Definition double2FloatLit : Literal -> Literal :=
  fun arg_50__ =>
    match arg_50__ with
      | MachDouble d => MachFloat d
      | l => Panic.panicStr (GHC.Base.hs_string__ "double2FloatLit") (Panic.noString
                                                                     l)
    end.

Definition float2DoubleLit : Literal -> Literal :=
  fun arg_54__ =>
    match arg_54__ with
      | MachFloat f => MachDouble f
      | l => Panic.panicStr (GHC.Base.hs_string__ "float2DoubleLit") (Panic.noString
                                                                     l)
    end.

Definition hashFS : FastString.FastString -> GHC.Num.Int :=
  fun s => FastString.uniqueOfFS s.

Definition hashInteger : GHC.Num.Integer -> GHC.Num.Int :=
  fun i =>
    GHC.Num.fromInteger 1 GHC.Num.+ GHC.Num.abs (GHC.Num.fromInteger (GHC.Real.rem i
                                                                                   (GHC.Num.fromInteger 10000))).

Definition hashRational : GHC.Real.Rational -> GHC.Num.Int :=
  fun r => hashInteger (GHC.Real.numerator r).

Definition hashLiteral : Literal -> GHC.Num.Int :=
  fun arg_3__ =>
    match arg_3__ with
      | MachChar c => GHC.Char.ord c GHC.Num.+ GHC.Num.fromInteger 1000
      | MachStr s => FastString.hashByteString s
      | MachNullAddr => GHC.Num.fromInteger 0
      | MachInt i => hashInteger i
      | MachInt64 i => hashInteger i
      | MachWord i => hashInteger i
      | MachWord64 i => hashInteger i
      | MachFloat r => hashRational r
      | MachDouble r => hashRational r
      | MachLabel s _ _ => hashFS s
      | LitInteger i _ => hashInteger i
    end.

Definition inIntRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool :=
  fun dflags x =>
    andb (x GHC.Base.>= DynFlags.tARGET_MIN_INT dflags) (x GHC.Base.<=
         DynFlags.tARGET_MAX_INT dflags).

Definition litIsDupable : DynFlags.DynFlags -> Literal -> bool :=
  fun arg_108__ arg_109__ =>
    match arg_108__ , arg_109__ with
      | _ , MachStr _ => false
      | dflags , LitInteger i _ => inIntRange dflags i
      | _ , _ => true
    end.

Definition inWordRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool :=
  fun dflags x =>
    andb (x GHC.Base.>= GHC.Num.fromInteger 0) (x GHC.Base.<=
         DynFlags.tARGET_MAX_WORD dflags).

Definition int2CharLit : Literal -> Literal :=
  fun arg_66__ =>
    match arg_66__ with
      | MachInt i => MachChar (GHC.Char.chr (GHC.Num.fromInteger i))
      | l => Panic.panicStr (GHC.Base.hs_string__ "int2CharLit") (Panic.noString l)
    end.

Definition int2DoubleLit : Literal -> Literal :=
  fun arg_58__ =>
    match arg_58__ with
      | MachInt i => MachDouble (GHC.Num.fromInteger i)
      | l => Panic.panicStr (GHC.Base.hs_string__ "int2DoubleLit") (Panic.noString l)
    end.

Definition int2FloatLit : Literal -> Literal :=
  fun arg_62__ =>
    match arg_62__ with
      | MachInt i => MachFloat (GHC.Num.fromInteger i)
      | l => Panic.panicStr (GHC.Base.hs_string__ "int2FloatLit") (Panic.noString l)
    end.

Definition int2WordLit : DynFlags.DynFlags -> Literal -> Literal :=
  fun arg_74__ arg_75__ =>
    let j_77__ :=
      match arg_74__ , arg_75__ with
        | _ , l => Panic.panicStr (GHC.Base.hs_string__ "int2WordLit") (Panic.noString
                                                                       l)
      end in
    match arg_74__ , arg_75__ with
      | dflags , MachInt i => let j_78__ := MachWord i in
                              if i GHC.Base.< GHC.Num.fromInteger 0 : bool
                              then MachWord ((GHC.Num.fromInteger 1 GHC.Num.+ DynFlags.tARGET_MAX_WORD dflags)
                                            GHC.Num.+ i)
                              else j_78__
      | _ , _ => j_77__
    end.

Definition isZeroLit : Literal -> bool :=
  fun arg_92__ =>
    match arg_92__ with
      | MachInt num_93__ => if num_93__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                            then true
                            else false
      | MachInt64 num_94__ => if num_94__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                              then true
                              else false
      | MachWord num_95__ => if num_95__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                             then true
                             else false
      | MachWord64 num_96__ => if num_96__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                               then true
                               else false
      | MachFloat num_97__ => if num_97__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                              then true
                              else false
      | MachDouble num_98__ => if num_98__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                               then true
                               else false
      | _ => false
    end.

Definition litFitsInChar : Literal -> bool :=
  fun arg_45__ =>
    match arg_45__ with
      | MachInt i => andb (i GHC.Base.>= GHC.Real.toInteger (GHC.Char.ord
                                                            GHC.Enum.minBound)) (i GHC.Base.<= GHC.Real.toInteger
                          (GHC.Char.ord GHC.Enum.maxBound))
      | _ => false
    end.

Definition litIsLifted : Literal -> bool :=
  fun arg_43__ => match arg_43__ with | LitInteger _ _ => true | _ => false end.

Definition litIsTrivial : Literal -> bool :=
  fun arg_48__ =>
    match arg_48__ with
      | MachStr _ => false
      | LitInteger _ _ => false
      | _ => true
    end.

Definition litTag : Literal -> GHC.Num.Int :=
  fun arg_16__ =>
    match arg_16__ with
      | MachChar _ => GHC.Num.fromInteger 1
      | MachStr _ => GHC.Num.fromInteger 2
      | MachNullAddr => GHC.Num.fromInteger 3
      | MachInt _ => GHC.Num.fromInteger 4
      | MachWord _ => GHC.Num.fromInteger 5
      | MachInt64 _ => GHC.Num.fromInteger 6
      | MachWord64 _ => GHC.Num.fromInteger 7
      | MachFloat _ => GHC.Num.fromInteger 8
      | MachDouble _ => GHC.Num.fromInteger 9
      | MachLabel _ _ _ => GHC.Num.fromInteger 10
      | LitInteger _ _ => GHC.Num.fromInteger 11
    end.

Definition cmpLit : Literal -> Literal -> comparison :=
  fun arg_29__ arg_30__ =>
    match arg_29__ , arg_30__ with
      | MachChar a , MachChar b => GHC.Base.compare a b
      | MachStr a , MachStr b => GHC.Base.compare a b
      | MachNullAddr , MachNullAddr => Eq
      | MachInt a , MachInt b => GHC.Base.compare a b
      | MachWord a , MachWord b => GHC.Base.compare a b
      | MachInt64 a , MachInt64 b => GHC.Base.compare a b
      | MachWord64 a , MachWord64 b => GHC.Base.compare a b
      | MachFloat a , MachFloat b => GHC.Base.compare a b
      | MachDouble a , MachDouble b => GHC.Base.compare a b
      | MachLabel a _ _ , MachLabel b _ _ => GHC.Base.compare a b
      | LitInteger a _ , LitInteger b _ => GHC.Base.compare a b
      | lit1 , lit2 => if litTag lit1 GHC.Base.< litTag lit2 : bool
                       then Lt
                       else Gt
    end.

Local Definition Ord__Literal_compare : Literal -> Literal -> comparison :=
  fun a b => cmpLit a b.

Local Definition Ord__Literal_op_zg__ : Literal -> Literal -> bool :=
  fun a b =>
    let scrut_124__ := (Ord__Literal_compare a b) in
    match scrut_124__ with
      | Lt => false
      | Eq => false
      | Gt => true
    end.

Local Definition Ord__Literal_op_zgze__ : Literal -> Literal -> bool :=
  fun a b =>
    let scrut_121__ := (Ord__Literal_compare a b) in
    match scrut_121__ with
      | Lt => false
      | Eq => true
      | Gt => true
    end.

Local Definition Ord__Literal_op_zl__ : Literal -> Literal -> bool :=
  fun a b =>
    let scrut_118__ := (Ord__Literal_compare a b) in
    match scrut_118__ with
      | Lt => true
      | Eq => false
      | Gt => false
    end.

Local Definition Ord__Literal_op_zlze__ : Literal -> Literal -> bool :=
  fun a b =>
    let scrut_115__ := (Ord__Literal_compare a b) in
    match scrut_115__ with
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

Program Instance Eq___Literal : GHC.Base.Eq_ Literal := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Literal_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Literal_op_zsze__ |}.

Program Instance Ord__Literal : GHC.Base.Ord Literal := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Literal_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Literal_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Literal_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Literal_op_zgze__ ;
      GHC.Base.compare__ := Ord__Literal_compare ;
      GHC.Base.max__ := Ord__Literal_max ;
      GHC.Base.min__ := Ord__Literal_min |}.

Definition litValue : Literal -> GHC.Num.Integer :=
  fun arg_88__ =>
    match arg_88__ with
      | MachChar c => GHC.Real.toInteger GHC.Base.$ GHC.Char.ord c
      | MachInt i => i
      | MachInt64 i => i
      | MachWord i => i
      | MachWord64 i => i
      | LitInteger i _ => i
      | l => Panic.panicStr (GHC.Base.hs_string__ "litValue") (Panic.noString l)
    end.

Definition mkLitInteger : GHC.Num.Integer -> unit -> Literal :=
  LitInteger.

Definition mkMachChar : GHC.Char.Char -> Literal :=
  MachChar.

Definition mkMachDouble : GHC.Real.Rational -> Literal :=
  MachDouble.

Definition mkMachFloat : GHC.Real.Rational -> Literal :=
  MachFloat.

Definition mkMachInt64 : GHC.Num.Integer -> Literal :=
  fun x => MachInt64 x.

Definition mkMachString : GHC.Base.String -> Literal :=
  fun s =>
    MachStr (FastString.fastStringToByteString GHC.Base.$ FastString.mkFastString
            s).

Definition mkMachWord64 : GHC.Num.Integer -> Literal :=
  fun x => MachWord64 x.

Definition nullAddrLit : Literal :=
  MachNullAddr.

Definition word2IntLit : DynFlags.DynFlags -> Literal -> Literal :=
  fun arg_81__ arg_82__ =>
    let j_84__ :=
      match arg_81__ , arg_82__ with
        | _ , l => Panic.panicStr (GHC.Base.hs_string__ "word2IntLit") (Panic.noString
                                                                       l)
      end in
    match arg_81__ , arg_82__ with
      | dflags , MachWord w => let j_85__ := MachInt w in
                               if w GHC.Base.> DynFlags.tARGET_MAX_INT dflags : bool
                               then MachInt ((w GHC.Num.- DynFlags.tARGET_MAX_WORD dflags) GHC.Num.-
                                            GHC.Num.fromInteger 1)
                               else j_85__
      | _ , _ => j_84__
    end.

(* Unbound variables:
     Eq Gt Lt andb bool comparison false option true unit BasicTypes.FunctionOrData
     DynFlags.DynFlags DynFlags.tARGET_MAX_INT DynFlags.tARGET_MAX_WORD
     DynFlags.tARGET_MIN_INT FastString.FastString FastString.fastStringToByteString
     FastString.hashByteString FastString.mkFastString FastString.uniqueOfFS
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Char.Char GHC.Char.chr GHC.Char.ord GHC.Enum.maxBound
     GHC.Enum.minBound GHC.Num.Int GHC.Num.Integer GHC.Num.abs GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Real.Rational GHC.Real.numerator
     GHC.Real.rem GHC.Real.toInteger Panic.noString Panic.panicStr
*)
