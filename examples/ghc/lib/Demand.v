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
Require BinInt.
Require Coq.Init.Datatypes.
Require Coq.Init.Peano.
Require Coq.Lists.List.
Require Core.
Require Data.Foldable.
Require DynFlags.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Wf.
Require Maybes.
Require Nat.
Require Panic.
Require UniqFM.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive TypeShape : Type
  := TsFun : TypeShape -> TypeShape
  |  TsProd : list TypeShape -> TypeShape
  |  TsUnk : TypeShape.

Inductive Termination r : Type
  := Diverges : Termination r
  |  ThrowsExn : Termination r
  |  Dunno : r -> Termination r.

Inductive KillFlags : Type := Mk_KillFlags : bool -> bool -> bool -> KillFlags.

Inductive JointDmd s u : Type := JD : s -> u -> JointDmd s u.

Inductive ExnStr : Type := VanStr : ExnStr |  Mk_ExnStr : ExnStr.

Inductive Str s : Type := Lazy : Str s |  Mk_Str : ExnStr -> s -> Str s.

Inductive Count : Type := One : Count |  Many : Count.

Inductive Use u : Type := Abs : Use u |  Mk_Use : Count -> u -> Use u.

Definition DmdShell :=
  (JointDmd (Str unit) (Use unit))%type.

Inductive CPRResult : Type
  := NoCPR : CPRResult
  |  RetProd : CPRResult
  |  RetSum : BasicTypes.ConTag -> CPRResult.

Definition DmdResult :=
  (Termination CPRResult)%type.

Inductive ArgUse__raw : Type :=.

Reserved Notation "'ArgUse'".

Inductive UseDmd : Type
  := UCall : Count -> UseDmd -> UseDmd
  |  UProd : list ArgUse -> UseDmd
  |  UHead : UseDmd
  |  Used : UseDmd
where "'ArgUse'" := (GHC.Base.Synonym ArgUse__raw (Use UseDmd)%type).

Inductive ArgStr__raw : Type :=.

Reserved Notation "'ArgStr'".

Inductive StrDmd : Type
  := HyperStr : StrDmd
  |  SCall : StrDmd -> StrDmd
  |  SProd : list ArgStr -> StrDmd
  |  HeadStr : StrDmd
where "'ArgStr'" := (GHC.Base.Synonym ArgStr__raw (Str StrDmd)%type).

Definition Demand :=
  (JointDmd ArgStr ArgUse)%type.

Definition DmdEnv :=
  (Core.VarEnv Demand)%type.

Definition BothDmdArg :=
  (DmdEnv * Termination unit)%type%type.

Inductive DmdType : Type
  := Mk_DmdType : DmdEnv -> list Demand -> DmdResult -> DmdType.

Inductive StrictSig : Type := Mk_StrictSig : DmdType -> StrictSig.

Definition CleanDemand :=
  (JointDmd StrDmd UseDmd)%type.

Arguments Diverges {_}.

Arguments ThrowsExn {_}.

Arguments Dunno {_} _.

Arguments JD {_} {_} _ _.

Arguments Lazy {_}.

Arguments Mk_Str {_} _ _.

Arguments Abs {_}.

Arguments Mk_Use {_} _ _.

Instance Default__TypeShape : GHC.Err.Default TypeShape :=
  GHC.Err.Build_Default _ TsUnk.

Instance Default__ExnStr : GHC.Err.Default ExnStr :=
  GHC.Err.Build_Default _ VanStr.

Instance Default__Count : GHC.Err.Default Count := GHC.Err.Build_Default _ One.

Instance Default__CPRResult : GHC.Err.Default CPRResult :=
  GHC.Err.Build_Default _ NoCPR.

Instance Default__UseDmd : GHC.Err.Default UseDmd :=
  GHC.Err.Build_Default _ UHead.

Instance Default__StrDmd : GHC.Err.Default StrDmd :=
  GHC.Err.Build_Default _ HyperStr.

Definition kf_abs (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags kf_abs _ _ := arg_0__ in
  kf_abs.

Definition kf_called_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ _ kf_called_once := arg_0__ in
  kf_called_once.

Definition kf_used_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ kf_used_once _ := arg_0__ in
  kf_used_once.

Definition sd {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD sd _ := arg_0__ in
  sd.

Definition ud {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD _ ud := arg_0__ in
  ud.
(* Midamble *)

Instance Num_nat : GHC.Num.Num nat := {
     op_zp__ := Nat.add;
     op_zm__ := Nat.sub;
     op_zt__ := Nat.mul;
     abs     := fun x => x;
     fromInteger := BinIntDef.Z.to_nat;
     negate  := fun x => x;
     signum  :=  fun x => x; }.

Instance Eq_nat : GHC.Base.Eq_ nat :=
  fun _ k => k {| GHC.Base.op_zeze____ := fun x y => (Nat.eqb x y);
               GHC.Base.op_zsze____ := fun x y => negb (Nat.eqb x y);
            |}.

Instance Ord_nat : GHC.Base.Ord nat :=
  GHC.Base.ord_default Nat.compare.

Require Import Omega.
Ltac solve_not_zero := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] => 
    unfold GHC.Base.op_zeze__, Eq_nat in H; simpl in H; apply EqNat.beq_nat_false in H
end; omega.



Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.

Instance Default_Termination {r} : GHC.Err.Default (Termination r) :=
  GHC.Err.Build_Default _ Diverges.

Instance Default_DmdResult : GHC.Err.Default DmdType :=
  GHC.Err.Build_Default _ (Mk_DmdType GHC.Err.default GHC.Err.default GHC.Err.default).

(* Definitions that we cannot process, see edits file for details. *)

Axiom lubUse : UseDmd -> UseDmd -> UseDmd.
Axiom lubArgUse :  Use UseDmd ->  Use UseDmd ->  Use UseDmd.
Axiom bothUse : UseDmd -> UseDmd -> UseDmd.
Axiom bothArgUse :  Use UseDmd ->  Use UseDmd ->  Use UseDmd.

(*
Axiom bothStr : StrDmd -> StrDmd -> StrDmd.
Axiom lubStr : StrDmd -> StrDmd -> StrDmd.
Axiom splitFVs : bool -> DmdEnv -> (DmdEnv * DmdEnv)%type.
Axiom postProcessDmdEnv : DmdShell -> DmdEnv -> DmdEnv.
Axiom peelManyCalls : GHC.Num.Int -> CleanDemand -> DmdShell.
Axiom toCleanDmd : Demand -> unit -> (DmdShell * CleanDemand)%type.
Axiom trimToType : Demand -> TypeShape -> Demand.
Axiom dmdTransformDictSelSig : StrictSig -> CleanDemand -> DmdType.
Axiom strictifyDictDmd : unit -> Demand -> Demand.
Axiom dmdTransformDataConSig  : BasicTypes.Arity -> StrictSig -> CleanDemand -> DmdType.
Axiom addCaseBndrDmd : Demand -> list Demand -> list Demand.
Axiom bothUse : UseDmd -> UseDmd -> UseDmd.
Axiom zap_usg : KillFlags -> UseDmd -> UseDmd.
*)

(* Example of successful mutual recursion. Not sure that we can automate this *)
(*
Definition isUsedMU' isUsedU (au : ArgUse) : bool :=
    match au with
      | Abs => true
      | Mk_Use One _ => false
      | Mk_Use Many u => isUsedU u
    end.

Fixpoint isUsedU (ud : UseDmd) : bool :=
    match ud with
      | Used => true
      | UHead => true
      | UProd us => Data.Foldable.all (isUsedMU' isUsedU) us
      | UCall One _ => false
      | UCall Many _ => true
    end.

Definition isUsedMU := isUsedMU' isUsedU.

Definition markReusedDmd' markReused : ArgUse -> ArgUse :=
  fun arg_258__ =>
    match arg_258__ with
      | Abs => Abs
      | Mk_Use _ a => Mk_Use Many (markReused a)
    end.

Fixpoint markReused (x : UseDmd) : UseDmd :=
    match x with
      | UCall _ u => UCall Many u
      | UProd ux => UProd (GHC.Base.map (markReusedDmd' markReused) ux)
      | u => u
    end.
Definition markReusedDmd := markReusedDmd' markReused.
*)

(* size metric, incase it is useful *)

Definition Str_size {a} (f : a -> nat) (x : Str a) : nat :=
  match x with
  | Lazy => 0
  | Mk_Str _ s => f s
  end.

Fixpoint StrDmd_size (s1 : StrDmd): nat :=
  match s1 with
  | HyperStr => 0
  | SCall s => Nat.add 1 (StrDmd_size s)
  | SProd ss => List.fold_left Nat.add (List.map (Str_size StrDmd_size) ss) 1
  | HeadStr => 0
  end.

Definition ArgStrDmd_size := Str_size StrDmd_size.

(* Converted value declarations: *)

(* Skipping instance Outputable__StrictSig of class Outputable *)

(* Skipping instance Binary__StrictSig of class Binary *)

(* Skipping instance Outputable__DmdType of class Outputable *)

(* Skipping instance Binary__DmdType of class Binary *)

(* Skipping instance Binary__DmdResult of class Binary *)

(* Skipping instance Outputable__CPRResult of class Outputable *)

(* Skipping instance Binary__CPRResult of class Binary *)

(* Skipping instance Outputable__Termination of class Outputable *)

(* Skipping instance Outputable__TypeShape of class Outputable *)

(* Skipping instance Outputable__ArgUse of class Outputable *)

(* Skipping instance Outputable__UseDmd of class Outputable *)

(* Skipping instance Binary__ArgUse of class Binary *)

(* Skipping instance Binary__UseDmd of class Binary *)

(* Skipping instance Outputable__Count of class Outputable *)

(* Skipping instance Binary__Count of class Binary *)

(* Skipping instance Outputable__StrDmd of class Outputable *)

(* Skipping instance Outputable__ArgStr of class Outputable *)

(* Skipping instance Binary__StrDmd of class Binary *)

(* Skipping instance Binary__ArgStr of class Binary *)

(* Skipping instance Binary__ExnStr of class Binary *)

(* Skipping instance Outputable__JointDmd of class Outputable *)

(* Skipping instance Binary__JointDmd of class Binary *)

(* Skipping instance Show__CPRResult of class Show *)

Local Definition Eq___CPRResult_op_zeze__ : CPRResult -> CPRResult -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoCPR, NoCPR => true
    | RetProd, RetProd => true
    | RetSum a1, RetSum b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___CPRResult_op_zsze__ : CPRResult -> CPRResult -> bool :=
  fun x y => negb (Eq___CPRResult_op_zeze__ x y).

Program Instance Eq___CPRResult : GHC.Base.Eq_ CPRResult :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___CPRResult_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___CPRResult_op_zsze__ |}.

(* Skipping instance Show__Termination of class Show *)

Local Definition Eq___Termination_op_zeze__ {inst_r} `{GHC.Base.Eq_ inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Diverges, Diverges => true
    | ThrowsExn, ThrowsExn => true
    | Dunno a1, Dunno b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Termination_op_zsze__ {inst_r} `{GHC.Base.Eq_ inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun x y => negb (Eq___Termination_op_zeze__ x y).

Program Instance Eq___Termination {r} `{GHC.Base.Eq_ r}
   : GHC.Base.Eq_ (Termination r) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Termination_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Termination_op_zsze__ |}.

(* Skipping instance Show__UseDmd of class Show *)

(* Skipping instance Show__Use of class Show *)

(* Skipping instance Show__Count of class Show *)

Local Definition Eq___Count_op_zeze__ : Count -> Count -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | One, One => true
    | Many, Many => true
    | _, _ => false
    end.

Local Definition Eq___Count_op_zsze__ : Count -> Count -> bool :=
  fun x y => negb (Eq___Count_op_zeze__ x y).

Program Instance Eq___Count : GHC.Base.Eq_ Count :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Count_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Count_op_zsze__ |}.

Local Definition Eq___Use_op_zeze__ {inst_u} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Abs, Abs => true
    | Mk_Use a1 a2, Mk_Use b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Use_op_zsze__ {inst_u} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun x y => negb (Eq___Use_op_zeze__ x y).

Program Instance Eq___Use {u} `{GHC.Base.Eq_ u} : GHC.Base.Eq_ (Use u) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Use_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Use_op_zsze__ |}.

Local Definition Eq___UseDmd_op_zeze__ : UseDmd -> UseDmd -> bool :=
  fix UseDmd_eq x y
        := let eq' : GHC.Base.Eq_ UseDmd := GHC.Base.eq_default UseDmd_eq in
           match x, y with
           | UCall a1 a2, UCall b1 b2 => andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)
           | UProd a1, UProd b1 => a1 GHC.Base.== b1
           | UHead, UHead => true
           | Used, Used => true
           | _, _ => false
           end.

Local Definition Eq___UseDmd_op_zsze__ : UseDmd -> UseDmd -> bool :=
  fun x y => negb (Eq___UseDmd_op_zeze__ x y).

Program Instance Eq___UseDmd : GHC.Base.Eq_ UseDmd :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___UseDmd_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___UseDmd_op_zsze__ |}.

(* Skipping instance Show__StrDmd of class Show *)

(* Skipping instance Show__Str of class Show *)

(* Skipping instance Show__ExnStr of class Show *)

Local Definition Eq___ExnStr_op_zeze__ : ExnStr -> ExnStr -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => true
    | Mk_ExnStr, Mk_ExnStr => true
    | _, _ => false
    end.

Local Definition Eq___ExnStr_op_zsze__ : ExnStr -> ExnStr -> bool :=
  fun x y => negb (Eq___ExnStr_op_zeze__ x y).

Program Instance Eq___ExnStr : GHC.Base.Eq_ ExnStr :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ExnStr_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ExnStr_op_zsze__ |}.

Local Definition Eq___Str_op_zeze__ {inst_s} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, Lazy => true
    | Mk_Str a1 a2, Mk_Str b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Str_op_zsze__ {inst_s} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun x y => negb (Eq___Str_op_zeze__ x y).

Program Instance Eq___Str {s} `{GHC.Base.Eq_ s} : GHC.Base.Eq_ (Str s) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Str_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Str_op_zsze__ |}.

Local Definition Eq___StrDmd_op_zeze__ : StrDmd -> StrDmd -> bool :=
  fix StrDmd_eq x y
        := let eq' : GHC.Base.Eq_ StrDmd := GHC.Base.eq_default StrDmd_eq in
           match x, y with
           | HyperStr, HyperStr => true
           | SCall a1, SCall b1 => a1 GHC.Base.== b1
           | SProd a1, SProd b1 => a1 GHC.Base.== b1
           | HeadStr, HeadStr => true
           | _, _ => false
           end.

Local Definition Eq___StrDmd_op_zsze__ : StrDmd -> StrDmd -> bool :=
  fun x y => negb (Eq___StrDmd_op_zeze__ x y).

Program Instance Eq___StrDmd : GHC.Base.Eq_ StrDmd :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___StrDmd_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___StrDmd_op_zsze__ |}.

(* Skipping instance Show__JointDmd of class Show *)

Local Definition Eq___JointDmd_op_zeze__ {inst_s} {inst_u} `{GHC.Base.Eq_
  inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD a1 a2, JD b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___JointDmd_op_zsze__ {inst_s} {inst_u} `{GHC.Base.Eq_
  inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun x y => negb (Eq___JointDmd_op_zeze__ x y).

Program Instance Eq___JointDmd {s} {u} `{GHC.Base.Eq_ s} `{GHC.Base.Eq_ u}
   : GHC.Base.Eq_ (JointDmd s u) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___JointDmd_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___JointDmd_op_zsze__ |}.

Local Definition Eq___DmdType_op_zeze__ : DmdType -> DmdType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv1 ds1 res1, Mk_DmdType fv2 ds2 res2 =>
        andb (UniqFM.nonDetUFMToList fv1 GHC.Base.== UniqFM.nonDetUFMToList fv2) (andb
              (ds1 GHC.Base.== ds2) (res1 GHC.Base.== res2))
    end.

Local Definition Eq___DmdType_op_zsze__ : DmdType -> DmdType -> bool :=
  fun x y => negb (Eq___DmdType_op_zeze__ x y).

Program Instance Eq___DmdType : GHC.Base.Eq_ DmdType :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___DmdType_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___DmdType_op_zsze__ |}.

Local Definition Eq___StrictSig_op_zeze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___StrictSig_op_zsze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___StrictSig : GHC.Base.Eq_ StrictSig :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___StrictSig_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___StrictSig_op_zsze__ |}.

Definition absDmd : Demand :=
  JD Lazy Abs.

Definition addDemand : Demand -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dmd, Mk_DmdType fv ds res => Mk_DmdType fv (cons dmd ds) res
    end.

Definition argOneShots : Demand -> list BasicTypes.OneShotInfo :=
  fun '(JD _ usg) =>
    let fix go arg_1__
              := match arg_1__ with
                 | UCall One u => cons BasicTypes.OneShotLam (go u)
                 | UCall Many u => cons BasicTypes.NoOneShotInfo (go u)
                 | _ => nil
                 end in
    match usg with
    | Mk_Use _ arg_usg => go arg_usg
    | _ => nil
    end.

Definition argsOneShots
   : StrictSig -> nat -> list (list BasicTypes.OneShotInfo) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ arg_ds _), n_val_args =>
        let cons_ :=
          fun arg_2__ arg_3__ =>
            match arg_2__, arg_3__ with
            | nil, nil => nil
            | a, as_ => cons a as_
            end in
        let fix go arg_6__
                  := match arg_6__ with
                     | nil => nil
                     | cons arg_d arg_ds => cons_ (argOneShots arg_d) (go arg_ds)
                     end in
        let unsaturated_call :=
          Util.lengthExceeds arg_ds (BinInt.Z.of_nat n_val_args) in
        if unsaturated_call : bool then nil else
        go arg_ds
    end.

Definition botRes : DmdResult :=
  Diverges.

Definition bothDmdResult : DmdResult -> Termination unit -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Diverges => Diverges
    | r, ThrowsExn => match r with | Diverges => r | _ => ThrowsExn end
    | r, Dunno _ => r
    end.

Definition bothExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ExnStr, Mk_ExnStr => Mk_ExnStr
    | _, _ => VanStr
    end.

Definition catchArgDmd : Demand :=
  JD (Mk_Str Mk_ExnStr (SCall HeadStr)) (Mk_Use One (UCall One Used)).

Definition cleanEvalDmd : CleanDemand :=
  JD HeadStr Used.

Definition cleanUseDmd_maybe : Demand -> option UseDmd :=
  fun arg_0__ => match arg_0__ with | JD _ (Mk_Use _ u) => Some u | _ => None end.

Definition cprProdRes : list DmdType -> DmdResult :=
  fun _arg_tys => Dunno RetProd.

Definition cprSumRes : BasicTypes.ConTag -> DmdResult :=
  fun tag => Dunno (RetSum tag).

Definition emptyDmdEnv : Core.VarEnv Demand :=
  Core.emptyVarEnv.

Definition botDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil botRes.

Definition botSig : StrictSig :=
  Mk_StrictSig botDmdType.

Definition exnRes : DmdResult :=
  ThrowsExn.

Definition exnDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil exnRes.

Definition exnSig : StrictSig :=
  Mk_StrictSig exnDmdType.

Definition getStrDmd {s} {u} : JointDmd s u -> s :=
  sd.

Definition getUseDmd {s} {u} : JointDmd s u -> u :=
  ud.

Definition hasDemandEnvSig : StrictSig -> bool :=
  fun '(Mk_StrictSig (Mk_DmdType env _ _)) => negb (Core.isEmptyVarEnv env).

Definition isAbsDmd : Demand -> bool :=
  fun arg_0__ => match arg_0__ with | JD _ Abs => true | _ => false end.

Definition isBotRes : DmdResult -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Diverges => true
    | ThrowsExn => true
    | Dunno _ => false
    end.

Definition isBottomingSig : StrictSig -> bool :=
  fun '(Mk_StrictSig (Mk_DmdType _ _ res)) => isBotRes res.

Definition appIsBottom : StrictSig -> nat -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ ds res), n =>
        if isBotRes res : bool
        then negb (Util.lengthExceeds ds (BinInt.Z.of_nat n)) else
        false
    end.

Definition isHyperStr : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Str _ HyperStr => true | _ => false end.

Definition isLazy : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Lazy => true | Mk_Str _ _ => false end.

Definition mkSProd : list ArgStr -> StrDmd :=
  fun sx =>
    if Data.Foldable.any isHyperStr sx : bool then HyperStr else
    if Data.Foldable.all isLazy sx : bool then HeadStr else
    SProd sx.

Definition bothStr : StrDmd -> StrDmd -> StrDmd :=
  fix bothStr arg_0__ arg_1__
        := let bothArgStr arg_0__ arg_1__ :=
             match arg_0__, arg_1__ with
             | Lazy, s => s
             | s, Lazy => s
             | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (bothExnStr x1 x2) (bothStr s1 s2)
             end in
           match arg_0__, arg_1__ with
           | HyperStr, _ => HyperStr
           | HeadStr, s => s
           | SCall _, HyperStr => HyperStr
           | SCall s1, HeadStr => SCall s1
           | SCall s1, SCall s2 => SCall (bothStr s1 s2)
           | SCall _, SProd _ => HyperStr
           | SProd _, HyperStr => HyperStr
           | SProd s1, HeadStr => SProd s1
           | SProd s1, SProd s2 =>
               if Util.equalLength s1 s2 then mkSProd (GHC.List.zipWith bothArgStr s1 s2) else
                  HyperStr
           | SProd _, SCall _ => HyperStr
           end.

Definition bothCleanDmd : CleanDemand -> CleanDemand -> CleanDemand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (bothStr s1 s2) (bothUse a1 a2)
    end.

Definition bothArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, s => s
    | s, Lazy => s
    | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (bothExnStr x1 x2) (bothStr s1 s2)
    end.

Definition bothDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (bothArgStr s1 s2) (bothArgUse a1 a2)
    end.

Definition isSeqDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD (Mk_Str VanStr HeadStr) (Mk_Use _ UHead) => true
    | _ => false
    end.

Definition isStrictDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD _ Abs => false
    | JD Lazy _ => false
    | _ => true
    end.

Definition isTopDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD Lazy (Mk_Use Many Used) => true
    | _ => false
    end.

Definition isTopRes : DmdResult -> bool :=
  fun arg_0__ => match arg_0__ with | Dunno NoCPR => true | _ => false end.

Definition isTopDmdType : DmdType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_DmdType env nil res =>
        if andb (isTopRes res) (Core.isEmptyVarEnv env) : bool then true else
        false
    | _ => false
    end.

Definition isTopSig : StrictSig -> bool :=
  fun '(Mk_StrictSig ty) => isTopDmdType ty.

Definition isUsedU : UseDmd -> bool :=
  fix isUsedU arg_0__
        := let isUsedMU arg_0__ :=
             match arg_0__ with
             | Abs => true
             | Mk_Use One _ => false
             | Mk_Use Many u => isUsedU u
             end in
           match arg_0__ with
           | Used => true
           | UHead => true
           | UProd us => Data.Foldable.all isUsedMU us
           | UCall One _ => false
           | UCall Many _ => true
           end.

Definition isUsedMU : ArgUse -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => true
    | Mk_Use One _ => false
    | Mk_Use Many u => isUsedU u
    end.

Definition isWeakDmd : Demand -> bool :=
  fun '(JD s a) => andb (isLazy s) (isUsedMU a).

Definition splitFVs : bool -> DmdEnv -> (DmdEnv * DmdEnv)%type :=
  fun is_thunk rhs_fvs =>
    let add :=
      fun arg_0__ arg_1__ arg_2__ =>
        match arg_0__, arg_1__, arg_2__ with
        | uniq, (JD s u as dmd), pair lazy_fv sig_fv =>
            match s with
            | Lazy => pair (UniqFM.addToUFM_Directly lazy_fv uniq dmd) sig_fv
            | _ =>
                pair (UniqFM.addToUFM_Directly lazy_fv uniq (JD Lazy u))
                     (UniqFM.addToUFM_Directly sig_fv uniq (JD s Abs))
            end
        end in
    if is_thunk : bool
    then UniqFM.nonDetFoldUFM_Directly add (pair Core.emptyVarEnv Core.emptyVarEnv)
         rhs_fvs else
    Core.partitionVarEnv isWeakDmd rhs_fvs.

Definition killFlags : DynFlags.DynFlags -> option KillFlags :=
  fun dflags =>
    let kf_used_once := DynFlags.gopt DynFlags.Opt_KillOneShot dflags in
    let kf_called_once := kf_used_once in
    let kf_abs := DynFlags.gopt DynFlags.Opt_KillAbsence dflags in
    if andb (negb kf_abs) (negb kf_used_once) : bool then None else
    Some (Mk_KillFlags kf_abs kf_used_once kf_called_once).

Definition lazyApply1Dmd : Demand :=
  JD Lazy (Mk_Use One (UCall One Used)).

Definition lazyApply2Dmd : Demand :=
  JD Lazy (Mk_Use One (UCall One (UCall One Used))).

Definition lubCPR : CPRResult -> CPRResult -> CPRResult :=
  fun arg_0__ arg_1__ =>
    let j_2__ :=
      match arg_0__, arg_1__ with
      | RetProd, RetProd => RetProd
      | _, _ => NoCPR
      end in
    match arg_0__, arg_1__ with
    | RetSum t1, RetSum t2 => if t1 GHC.Base.== t2 : bool then RetSum t1 else j_2__
    | _, _ => j_2__
    end.

Definition lubDmdResult : DmdResult -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Diverges, r => r
    | ThrowsExn, Diverges => ThrowsExn
    | ThrowsExn, r => r
    | Dunno c1, Diverges => Dunno c1
    | Dunno c1, ThrowsExn => Dunno c1
    | Dunno c1, Dunno c2 => Dunno (lubCPR c1 c2)
    end.

Definition lubCount : Count -> Count -> Count :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Many => Many
    | Many, _ => Many
    | x, _ => x
    end.

Definition lubExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => VanStr
    | _, _ => Mk_ExnStr
    end.

Definition lubStr : StrDmd -> StrDmd -> StrDmd :=
  fix lubStr arg_0__ arg_1__
        := let lubArgStr arg_0__ arg_1__ :=
             match arg_0__, arg_1__ with
             | Lazy, _ => Lazy
             | _, Lazy => Lazy
             | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (lubExnStr x1 x2) (lubStr s1 s2)
             end in
           match arg_0__, arg_1__ with
           | HyperStr, s => s
           | SCall s1, HyperStr => SCall s1
           | SCall _, HeadStr => HeadStr
           | SCall s1, SCall s2 => SCall (lubStr s1 s2)
           | SCall _, SProd _ => HeadStr
           | SProd sx, HyperStr => SProd sx
           | SProd _, HeadStr => HeadStr
           | SProd s1, SProd s2 =>
               if Util.equalLength s1 s2 then mkSProd (GHC.List.zipWith lubArgStr s1 s2) else
                  HeadStr
           | SProd _, SCall _ => HeadStr
           | HeadStr, _ => HeadStr
           end.

Definition lubArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, _ => Lazy
    | _, Lazy => Lazy
    | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (lubExnStr x1 x2) (lubStr s1 s2)
    end.

Definition lubDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (lubArgStr s1 s2) (lubArgUse a1 a2)
    end.

Definition markExnStr : ArgStr -> ArgStr :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Str VanStr s => Mk_Str Mk_ExnStr s
    | s => s
    end.

Definition markReused : UseDmd -> UseDmd :=
  fix markReused arg_0__
        := let markReusedDmd arg_0__ :=
             match arg_0__ with
             | Abs => Abs
             | Mk_Use _ a => Mk_Use Many (markReused a)
             end in
           match arg_0__ with
           | UCall _ u => UCall Many u
           | UProd ux => UProd (GHC.Base.map markReusedDmd ux)
           | u => u
           end.

Definition markReusedDmd : ArgUse -> ArgUse :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => Abs
    | Mk_Use _ a => Mk_Use Many (markReused a)
    end.

Definition postProcessDmd : DmdShell -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD ss us, JD s a =>
        let a' :=
          match us with
          | Abs => Abs
          | Mk_Use Many _ => markReusedDmd a
          | Mk_Use One _ => a
          end in
        let s' :=
          match ss with
          | Lazy => Lazy
          | Mk_Str Mk_ExnStr _ => markExnStr s
          | Mk_Str VanStr _ => s
          end in
        JD s' a'
    end.

Definition reuseEnv : DmdEnv -> DmdEnv :=
  Core.mapVarEnv (postProcessDmd (JD (Mk_Str VanStr tt) (Mk_Use Many tt))).

Definition postProcessDmdEnv : DmdShell -> DmdEnv -> DmdEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss us as ds), env =>
        match us with
        | Abs => emptyDmdEnv
        | _ =>
            let j_2__ := Core.mapVarEnv (postProcessDmd ds) env in
            match ss with
            | Mk_Str VanStr _ => match us with | Mk_Use One _ => env | _ => j_2__ end
            | _ => j_2__
            end
        end
    end.

Definition mkBothDmdArg : DmdEnv -> BothDmdArg :=
  fun env => pair env (Dunno tt).

Definition mkDmdType : DmdEnv -> list Demand -> DmdResult -> DmdType :=
  fun fv ds res => Mk_DmdType fv ds res.

Definition mkHeadStrict : CleanDemand -> CleanDemand :=
  fun '(JD sd_0__ ud_1__) => JD HeadStr ud_1__.

Definition mkJointDmd {s} {u} : s -> u -> JointDmd s u :=
  fun s u => JD s u.

Definition mkJointDmds {s} {u} : list s -> list u -> list (JointDmd s u) :=
  fun ss as_ =>
    Util.zipWithEqual (GHC.Base.hs_string__ "mkJointDmds") mkJointDmd ss as_.

Definition mkManyUsedDmd : CleanDemand -> Demand :=
  fun '(JD s a) => JD (Mk_Str VanStr s) (Mk_Use Many a).

Definition mkOnceUsedDmd : CleanDemand -> Demand :=
  fun '(JD s a) => JD (Mk_Str VanStr s) (Mk_Use One a).

Definition mkSCall : StrDmd -> StrDmd :=
  fun arg_0__ => match arg_0__ with | HyperStr => HyperStr | s => SCall s end.

Definition mkStrictSig : DmdType -> StrictSig :=
  fun dmd_ty => Mk_StrictSig dmd_ty.

Definition mkClosedStrictSig : list Demand -> DmdResult -> StrictSig :=
  fun ds res => mkStrictSig (Mk_DmdType emptyDmdEnv ds res).

Definition zapUsageEnvSig : StrictSig -> StrictSig :=
  fun '(Mk_StrictSig (Mk_DmdType _ ds r)) => mkClosedStrictSig ds r.

Definition mkUCall : Count -> UseDmd -> UseDmd :=
  fun c a => UCall c a.

Program Definition mkWorkerDemand : nat -> Demand :=
          fun n =>
            let go :=
              GHC.Wf.wfFix1 Coq.Init.Peano.lt (fun arg_0__ => arg_0__) _ (fun arg_0__ go =>
                               let 'num_1__ := arg_0__ in
                               if Bool.Sumbool.sumbool_of_bool (num_1__ GHC.Base.== #0) then Used else
                               let 'n := arg_0__ in
                               mkUCall One (go (Nat.pred n))) in
            JD Lazy (Mk_Use One (go n)).
Admit Obligations.

Definition mkCallDmd : CleanDemand -> CleanDemand :=
  fun '(JD d u) => JD (mkSCall d) (mkUCall One u).

Definition mkUProd : list ArgUse -> UseDmd :=
  fun ux =>
    if Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.== Abs) ux : bool
    then UHead else
    UProd ux.

Definition mkProdDmd : list Demand -> CleanDemand :=
  fun dx =>
    JD (mkSProd (GHC.Base.map getStrDmd dx)) (mkUProd (GHC.Base.map getUseDmd dx)).

Definition oneifyDmd : Demand -> Demand :=
  fun arg_0__ =>
    match arg_0__ with
    | JD s (Mk_Use _ a) => JD s (Mk_Use One a)
    | jd => jd
    end.

Definition peelCallDmd : CleanDemand -> (CleanDemand * DmdShell)%type :=
  fun '(JD s u) =>
    let 'pair u' us := (match u with
                          | UCall c u' => pair u' (Mk_Use c tt)
                          | _ => pair Used (Mk_Use Many tt)
                          end) in
    let 'pair s' ss := (match s with
                          | SCall s' => pair s' (Mk_Str VanStr tt)
                          | HyperStr => pair HyperStr (Mk_Str VanStr tt)
                          | _ => pair HeadStr Lazy
                          end) in
    pair (JD s' u') (JD ss us).

Definition peelManyCalls : nat -> CleanDemand -> DmdShell :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, JD str abs =>
        let go_abs : nat -> UseDmd -> Use unit :=
          fix go_abs arg_2__ arg_3__
                := match arg_2__, arg_3__ with
                   | num_4__, _ =>
                       if num_4__ GHC.Base.== #0 : bool then Mk_Use One tt else
                       match arg_2__, arg_3__ with
                       | n, UCall One d' => go_abs (Nat.pred n) d'
                       | _, _ => Mk_Use Many tt
                       end
                   end in
        let go_str : nat -> StrDmd -> Str unit :=
          fix go_str arg_10__ arg_11__
                := match arg_10__, arg_11__ with
                   | num_12__, _ =>
                       if num_12__ GHC.Base.== #0 : bool then Mk_Str VanStr tt else
                       match arg_10__, arg_11__ with
                       | _, HyperStr => Mk_Str VanStr tt
                       | n, SCall d' => go_str (Nat.pred n) d'
                       | _, _ => Lazy
                       end
                   end in
        JD (go_str n str) (go_abs n abs)
    end.

Definition peelUseCall : UseDmd -> option (Count * UseDmd)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | UCall c u => Some (pair c u)
    | _ => None
    end.

Definition retCPR_maybe : CPRResult -> option BasicTypes.ConTag :=
  fun arg_0__ =>
    match arg_0__ with
    | RetSum t => Some t
    | RetProd => Some BasicTypes.fIRST_TAG
    | NoCPR => None
    end.

Definition returnsCPR_maybe : DmdResult -> option BasicTypes.ConTag :=
  fun arg_0__ => match arg_0__ with | Dunno c => retCPR_maybe c | _ => None end.

Definition saturatedByOneShots : nat -> Demand -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, JD _ usg =>
        let fix go arg_2__ arg_3__
                  := match arg_2__, arg_3__ with
                     | num_4__, _ =>
                         if num_4__ GHC.Base.== #0 : bool then true else
                         match arg_2__, arg_3__ with
                         | n, UCall One u => go (Nat.pred n) u
                         | _, _ => false
                         end
                     end in
        match usg with
        | Mk_Use _ arg_usg => go n arg_usg
        | _ => false
        end
    end.

Definition seqArgStr : ArgStr -> unit :=
  fun x => tt.

Definition seqArgUse : ArgUse -> unit :=
  fun x => tt.

Definition seqArgUseList : list ArgUse -> unit :=
  fun x => tt.

Definition seqCPRResult : CPRResult -> unit :=
  fun x => tt.

Definition seqDemand : Demand -> unit :=
  fun x => tt.

Definition seqDemandList : list Demand -> unit :=
  fun x => tt.

Definition seqDmd : Demand :=
  JD (Mk_Str VanStr HeadStr) (Mk_Use One UHead).

Definition seqDmdEnv : DmdEnv -> unit :=
  fun x => tt.

Definition seqDmdResult : DmdResult -> unit :=
  fun x => tt.

Definition seqDmdType : DmdType -> unit :=
  fun x => tt.

Definition seqStrDmd : StrDmd -> unit :=
  fun x => tt.

Definition seqStrDmdList : list ArgStr -> unit :=
  fun x => tt.

Definition seqStrictSig : StrictSig -> unit :=
  fun x => tt.

Definition seqUseDmd : UseDmd -> unit :=
  fun x => tt.

Definition splitStrictSig : StrictSig -> (list Demand * DmdResult)%type :=
  fun '(Mk_StrictSig (Mk_DmdType _ dmds res)) => pair dmds res.

Definition strBot : ArgStr :=
  Mk_Str VanStr HyperStr.

Definition strTop : ArgStr :=
  Lazy.

Definition splitStrProdDmd : nat -> StrDmd -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, HyperStr => Some (Coq.Lists.List.repeat strBot n)
    | n, HeadStr => Some (Coq.Lists.List.repeat strTop n)
    | n, SProd ds =>
        Panic.warnPprTrace (negb (Util.lengthIs ds (BinInt.Z.of_nat n)))
                           (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Demand.hs") #359 (Panic.someSDoc)
        (Some ds)
    | _, SCall _ => None
    end.

Definition splitArgStrProdDmd : nat -> ArgStr -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Lazy => Some (Coq.Lists.List.repeat Lazy n)
    | n, Mk_Str _ s => splitStrProdDmd n s
    end.

Definition strictApply1Dmd : Demand :=
  JD (Mk_Str VanStr (SCall HeadStr)) (Mk_Use Many (UCall One Used)).

Definition strictSigDmdEnv : StrictSig -> DmdEnv :=
  fun '(Mk_StrictSig (Mk_DmdType env _ _)) => env.

Definition strictenDmd : Demand -> CleanDemand :=
  fun '(JD s u) =>
    let poke_u :=
      fun arg_1__ => match arg_1__ with | Abs => UHead | Mk_Use _ u => u end in
    let poke_s :=
      fun arg_3__ => match arg_3__ with | Lazy => HeadStr | Mk_Str _ s => s end in
    JD (poke_s s) (poke_u u).

Definition toBothDmdArg : DmdType -> BothDmdArg :=
  fun '(Mk_DmdType fv _ r) =>
    let go :=
      fun arg_1__ =>
        match arg_1__ with
        | Dunno _ => Dunno tt
        | ThrowsExn => ThrowsExn
        | Diverges => Diverges
        end in
    pair fv (go r).

Definition trimCPRInfo : bool -> bool -> DmdResult -> DmdResult :=
  fun trim_all trim_sums res =>
    let trimC :=
      fun arg_0__ =>
        match arg_0__ with
        | RetSum n => if orb trim_all trim_sums : bool then NoCPR else RetSum n
        | RetProd => if trim_all : bool then NoCPR else RetProd
        | NoCPR => NoCPR
        end in
    let trimR :=
      fun arg_5__ =>
        match arg_5__ with
        | Dunno c => Dunno (trimC c)
        | res => res
        end in
    trimR res.

Definition useBot : ArgUse :=
  Abs.

Definition botDmd : Demand :=
  JD strBot useBot.

Definition defaultDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => absDmd | _ => botDmd end.

Definition bothDmdType : DmdType -> BothDmdArg -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv1 ds1 r1, pair fv2 t2 =>
        Mk_DmdType (Core.plusVarEnv_CD bothDmd fv1 (defaultDmd r1) fv2 (defaultDmd t2))
        ds1 (bothDmdResult r1 t2)
    end.

Definition findIdDemand : DmdType -> Core.Var -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv _ res, id =>
        Maybes.orElse (Core.lookupVarEnv fv id) (defaultDmd res)
    end.

Definition peelFV : DmdType -> Core.Var -> (DmdType * Demand)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv ds res, id =>
        let dmd := Maybes.orElse (Core.lookupVarEnv fv id) (defaultDmd res) in
        let fv' := Core.delVarEnv fv id in pair (Mk_DmdType fv' ds res) dmd
    end.

Definition useCount {u} : Use u -> Count :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => One
    | Mk_Use One _ => One
    | _ => Many
    end.

Definition isUsedOnce : Demand -> bool :=
  fun '(JD _ a) => match useCount a with | One => true | Many => false end.

Definition useTop : ArgUse :=
  Mk_Use Many Used.

Definition topDmd : Demand :=
  JD Lazy useTop.

Definition increaseStrictSigArity : nat -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | arity_increase, Mk_StrictSig (Mk_DmdType env dmds res) =>
        Mk_StrictSig (Mk_DmdType env (Coq.Init.Datatypes.app (Coq.Lists.List.repeat
                                                              topDmd arity_increase) dmds) res)
    end.

Definition resTypeArgDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => topDmd | _ => botDmd end.

Definition topRes : DmdResult :=
  Dunno NoCPR.

Definition postProcessDmdResult : Str unit -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, _ => topRes
    | Mk_Str Mk_ExnStr _, ThrowsExn => topRes
    | _, res => res
    end.

Definition postProcessDmdType : DmdShell -> DmdType -> BothDmdArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss _ as du), Mk_DmdType fv _ res_ty =>
        let term_info :=
          match postProcessDmdResult ss res_ty with
          | Dunno _ => Dunno tt
          | ThrowsExn => ThrowsExn
          | Diverges => Diverges
          end in
        pair (postProcessDmdEnv du fv) term_info
    end.

Definition postProcessUnsat : DmdShell -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss _ as ds), Mk_DmdType fv args res_ty =>
        Mk_DmdType (postProcessDmdEnv ds fv) (GHC.Base.map (postProcessDmd ds) args)
        (postProcessDmdResult ss res_ty)
    end.

Definition dmdTransformSig : StrictSig -> CleanDemand -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ arg_ds _ as dmd_ty), cd =>
        postProcessUnsat (peelManyCalls (Coq.Lists.List.length arg_ds) cd) dmd_ty
    end.

Definition nopDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil topRes.

Definition nopSig : StrictSig :=
  Mk_StrictSig nopDmdType.

Definition dmdTypeDepth : DmdType -> nat :=
  fun '(Mk_DmdType _ ds _) => Coq.Lists.List.length ds.

Definition ensureArgs : nat -> DmdType -> DmdType :=
  fun n d =>
    let 'Mk_DmdType fv ds r := d in
    let ds' :=
      Coq.Lists.List.skipn n (app ds (Coq.Lists.List.repeat (resTypeArgDmd r) n)) in
    let r' := match r with | Dunno _ => topRes | _ => r end in
    let depth := dmdTypeDepth d in
    if n GHC.Base.== depth : bool then d else
    Mk_DmdType fv ds' r'.

Definition removeDmdTyArgs : DmdType -> DmdType :=
  ensureArgs #0.

Definition lubDmdType : DmdType -> DmdType -> DmdType :=
  fun d1 d2 =>
    let n := GHC.Base.max (dmdTypeDepth d1) (dmdTypeDepth d2) in
    let 'Mk_DmdType fv1 ds1 r1 := ensureArgs n d1 in
    let 'Mk_DmdType fv2 ds2 r2 := ensureArgs n d2 in
    let lub_fv :=
      Core.plusVarEnv_CD lubDmd fv1 (defaultDmd r1) fv2 (defaultDmd r2) in
    let lub_ds :=
      Util.zipWithEqual (GHC.Base.hs_string__ "lubDmdType") lubDmd ds1 ds2 in
    let lub_res := lubDmdResult r1 r2 in Mk_DmdType lub_fv lub_ds lub_res.

Definition deferAfterIO : DmdType -> DmdType :=
  fun '((Mk_DmdType _ _ res as d)) =>
    let defer_res :=
      fun arg_1__ => match arg_1__ with | (Dunno _ as r) => r | _ => topRes end in
    let 'Mk_DmdType fv ds _ := lubDmdType d nopDmdType in
    Mk_DmdType fv ds (defer_res res).

Definition splitDmdTy : DmdType -> (Demand * DmdType)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_DmdType fv (cons dmd dmds) res_ty => pair dmd (Mk_DmdType fv dmds res_ty)
    | (Mk_DmdType _ nil res_ty as ty) => pair (resTypeArgDmd res_ty) ty
    end.

Definition splitUseProdDmd : nat -> UseDmd -> option (list ArgUse) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Used => Some (Coq.Lists.List.repeat useTop n)
    | n, UHead => Some (Coq.Lists.List.repeat Abs n)
    | n, UProd ds =>
        Panic.warnPprTrace (negb (Util.lengthIs ds (BinInt.Z.of_nat n)))
                           (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Demand.hs") #645 (Panic.someSDoc)
        (Some ds)
    | _, UCall _ _ => None
    end.

Definition splitProdDmd_maybe : Demand -> option (list Demand) :=
  fun '(JD s u) =>
    let scrut_1__ := pair s u in
    let j_3__ :=
      match scrut_1__ with
      | pair Lazy (Mk_Use _ (UProd ux)) =>
          Some (mkJointDmds (Coq.Lists.List.repeat Lazy (Coq.Lists.List.length ux)) ux)
      | _ => None
      end in
    let j_5__ :=
      match scrut_1__ with
      | pair (Mk_Str _ s) (Mk_Use _ (UProd ux)) =>
          match splitStrProdDmd (Coq.Lists.List.length ux) s with
          | Some sx => Some (mkJointDmds sx ux)
          | _ => j_3__
          end
      | _ => j_3__
      end in
    match scrut_1__ with
    | pair (Mk_Str _ (SProd sx)) (Mk_Use _ u) =>
        match splitUseProdDmd (Coq.Lists.List.length sx) u with
        | Some ux => Some (mkJointDmds sx ux)
        | _ => j_5__
        end
    | _ => j_5__
    end.

Definition dmdTransformDictSelSig : StrictSig -> CleanDemand -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ (cons dict_dmd nil) _), cd =>
        let enhance :=
          fun cd old => if isAbsDmd old : bool then old else mkOnceUsedDmd cd in
        let 'pair cd' defer_use := peelCallDmd cd in
        match splitProdDmd_maybe dict_dmd with
        | Some jds =>
            postProcessUnsat defer_use (Mk_DmdType emptyDmdEnv (cons (mkOnceUsedDmd
                                                                      (mkProdDmd (GHC.Base.map (enhance cd') jds))) nil)
                                                   topRes)
        | _ => nopDmdType
        end
    | _, _ => Panic.panic (GHC.Base.hs_string__ "dmdTransformDictSelSig: no args")
    end.

Program Definition dmdTransformDataConSig
           : nat -> StrictSig -> CleanDemand -> DmdType :=
          fun arg_0__ arg_1__ arg_2__ =>
            match arg_0__, arg_1__, arg_2__ with
            | arity, Mk_StrictSig (Mk_DmdType _ _ con_res), JD str abs =>
                let fix go_abs arg_3__ arg_4__
                          := match arg_3__, arg_4__ with
                             | num_5__, dmd =>
                                 if Bool.Sumbool.sumbool_of_bool (num_5__ GHC.Base.== #0)
                                 then splitUseProdDmd arity dmd else
                                 match arg_3__, arg_4__ with
                                 | n, UCall One u' => go_abs (Nat.pred n) u'
                                 | _, _ => None
                                 end
                             end in
                let go_str :=
                  GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_10__ arg_11__ => arg_10__) _
                                (fun arg_10__ arg_11__ go_str =>
                                   match arg_10__, arg_11__ with
                                   | num_12__, dmd =>
                                       if Bool.Sumbool.sumbool_of_bool (num_12__ GHC.Base.== #0)
                                       then splitStrProdDmd arity dmd else
                                       match arg_10__, arg_11__ with
                                       | n, SCall s' => go_str (Nat.pred n) s'
                                       | n, HyperStr => go_str (Nat.pred n) HyperStr
                                       | _, _ => None
                                       end
                                   end) in
                match go_str arity str with
                | Some str_dmds =>
                    match go_abs arity abs with
                    | Some abs_dmds =>
                        Mk_DmdType emptyDmdEnv (mkJointDmds str_dmds abs_dmds) con_res
                    | _ => nopDmdType
                    end
                | _ => nopDmdType
                end
            end.
Admit Obligations.

Definition evalDmd : Demand :=
  JD (Mk_Str VanStr HeadStr) useTop.

Definition cleanEvalProdDmd : nat -> CleanDemand :=
  fun n => JD HeadStr (UProd (Coq.Lists.List.repeat useTop n)).

Definition vanillaCprProdRes : nat -> DmdResult :=
  fun _arity => Dunno RetProd.

Definition cprProdDmdType : nat -> DmdType :=
  fun arity => Mk_DmdType emptyDmdEnv nil (vanillaCprProdRes arity).

Definition cprProdSig : nat -> StrictSig :=
  fun arity => Mk_StrictSig (cprProdDmdType arity).

Definition zap_usg : KillFlags -> UseDmd -> UseDmd :=
  fix zap_usg arg_0__ arg_1__
        := let zap_musg arg_0__ arg_1__ :=
             match arg_0__, arg_1__ with
             | kfs, Abs => if kf_abs kfs then useTop else Abs
             | kfs, Mk_Use c u =>
                 if kf_used_once kfs then Mk_Use Many (zap_usg kfs u) else Mk_Use c (zap_usg kfs
                                                                                             u)
             end in
           match arg_0__, arg_1__ with
           | kfs, UCall c u =>
               if kf_called_once kfs then UCall Many (zap_usg kfs u) else UCall c (zap_usg kfs
                                                                                           u)
           | _, _ =>
               match arg_0__, arg_1__ with
               | kfs, UProd us => UProd (GHC.Base.map (zap_musg kfs) us)
               | _, u => u
               end
           end.

Definition zap_musg : KillFlags -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, Abs => if kf_abs kfs then useTop else Abs
    | kfs, Mk_Use c u =>
        if kf_used_once kfs then Mk_Use Many (zap_usg kfs u) else Mk_Use c (zap_usg kfs
                                                                                    u)
    end.

Definition kill_usage : KillFlags -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, JD s u => JD s (zap_musg kfs u)
    end.

Definition zapUsageDemand : Demand -> Demand :=
  kill_usage (Mk_KillFlags true true true).

Definition zapUsedOnceDemand : Demand -> Demand :=
  kill_usage (Mk_KillFlags false true false).

Definition zapUsedOnceSig : StrictSig -> StrictSig :=
  fun '(Mk_StrictSig (Mk_DmdType env ds r)) =>
    Mk_StrictSig (Mk_DmdType env (GHC.Base.map zapUsedOnceDemand ds) r).

Definition killUsageDemand : DynFlags.DynFlags -> Demand -> Demand :=
  fun dflags dmd =>
    match killFlags dflags with
    | Some kfs => kill_usage kfs dmd
    | _ => dmd
    end.

Definition killUsageSig : DynFlags.DynFlags -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, (Mk_StrictSig (Mk_DmdType env ds r) as sig) =>
        match killFlags dflags with
        | Some kfs => Mk_StrictSig (Mk_DmdType env (GHC.Base.map (kill_usage kfs) ds) r)
        | _ => sig
        end
    end.

(* External variables:
     ArgStr ArgUse Bool.Sumbool.sumbool_of_bool None Some andb app bool bothArgUse
     bothUse cons else false if list lubArgUse nat negb nil op_zt__ option orb pair
     then true tt unit BasicTypes.ConTag BasicTypes.NoOneShotInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.fIRST_TAG
     BinInt.Z.of_nat Coq.Init.Datatypes.app Coq.Init.Peano.lt Coq.Lists.List.length
     Coq.Lists.List.repeat Coq.Lists.List.skipn Core.Var Core.VarEnv Core.delVarEnv
     Core.emptyVarEnv Core.isEmptyVarEnv Core.lookupVarEnv Core.mapVarEnv
     Core.partitionVarEnv Core.plusVarEnv_CD Data.Foldable.all Data.Foldable.any
     DynFlags.DynFlags DynFlags.Opt_KillAbsence DynFlags.Opt_KillOneShot
     DynFlags.gopt GHC.Base.Eq_ GHC.Base.Synonym GHC.Base.eq_default GHC.Base.map
     GHC.Base.max GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default GHC.List.zipWith
     GHC.Num.fromInteger GHC.Prim.coerce GHC.Wf.wfFix1 GHC.Wf.wfFix2 Maybes.orElse
     Nat.pred Panic.panic Panic.someSDoc Panic.warnPprTrace UniqFM.addToUFM_Directly
     UniqFM.nonDetFoldUFM_Directly UniqFM.nonDetUFMToList Util.equalLength
     Util.lengthExceeds Util.lengthIs Util.zipWithEqual
*)
