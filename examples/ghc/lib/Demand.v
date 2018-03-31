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
Require Coq.Init.Datatypes.
Require CoreType.
Require Data.Foldable.
Require DynFlags.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require Maybes.
Require Panic.
Require UniqFM.
Require Util.
Require VarEnv.
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

Inductive KillFlags : Type := KillFlags : bool -> bool -> bool -> KillFlags.

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
  (VarEnv.VarEnv Demand)%type.

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

Definition kf_abs (arg_0__ : KillFlags) :=
  let 'KillFlags kf_abs _ _ := arg_0__ in
  kf_abs.

Definition kf_called_once (arg_1__ : KillFlags) :=
  let 'KillFlags _ _ kf_called_once := arg_1__ in
  kf_called_once.

Definition kf_used_once (arg_2__ : KillFlags) :=
  let 'KillFlags _ kf_used_once _ := arg_2__ in
  kf_used_once.

Definition sd {s} {u} (arg_3__ : JointDmd s u) :=
  let 'JD sd _ := arg_3__ in
  sd.

Definition ud {s} {u} (arg_4__ : JointDmd s u) :=
  let 'JD _ ud := arg_4__ in
  ud.
(* Midamble *)

Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.

(* Definitions that we cannot process, see edits file for details. *)

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
Axiom lubUse : UseDmd -> UseDmd -> UseDmd.
Axiom bothUse : UseDmd -> UseDmd -> UseDmd.
Axiom zap_usg : KillFlags -> UseDmd -> UseDmd.


(* Example of successful mutual recursion. Not sure that we can automate this *)
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

(* Translating `instance Outputable__StrictSig' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__StrictSig' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__DmdType' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__DmdType' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary__DmdResult' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__CPRResult' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__CPRResult' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__Termination' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TypeShape' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__ArgUse' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__UseDmd' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__ArgUse' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary__UseDmd' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__Count' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__Count' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__StrDmd' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__ArgStr' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__StrDmd' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary__ArgStr' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary__ExnStr' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__JointDmd' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__JointDmd' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Show__CPRResult' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

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

(* Translating `instance Show__Termination' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

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

(* Translating `instance Show__UseDmd' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Show__Use' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Show__Count' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

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

(* Translating `instance Show__StrDmd' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Show__Str' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Show__ExnStr' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

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

(* Translating `instance Show__JointDmd' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

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
  fun arg_0__ =>
    let 'JD _ usg := arg_0__ in
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
   : StrictSig -> BasicTypes.Arity -> list (list BasicTypes.OneShotInfo) :=
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
        let unsaturated_call := Util.lengthExceeds arg_ds n_val_args in
        if unsaturated_call : bool then nil else
        go arg_ds
    end.

Definition botRes : DmdResult :=
  Diverges.

Definition bothArgUse : ArgUse -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Abs, x => x
    | x, Abs => x
    | Mk_Use _ a1, Mk_Use _ a2 => Mk_Use Many (bothUse a1 a2)
    end.

Definition bothCleanDmd : CleanDemand -> CleanDemand -> CleanDemand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (bothStr s1 s2) (bothUse a1 a2)
    end.

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

Definition emptyDmdEnv : VarEnv.VarEnv Demand :=
  VarEnv.emptyVarEnv.

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
  fun arg_0__ =>
    let 'Mk_StrictSig (Mk_DmdType env _ _) := arg_0__ in
    negb (VarEnv.isEmptyVarEnv env).

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
  fun arg_0__ =>
    let 'Mk_StrictSig (Mk_DmdType _ _ res) := arg_0__ in
    isBotRes res.

Definition appIsBottom : StrictSig -> GHC.Num.Int -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ ds res), n =>
        if isBotRes res : bool then negb (Util.lengthExceeds ds n) else
        false
    end.

Definition isHyperStr : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Str _ HyperStr => true | _ => false end.

Definition isLazy : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Lazy => true | Mk_Str _ _ => false end.

Definition isWeakDmd : Demand -> bool :=
  fun arg_0__ => let 'JD s a := arg_0__ in andb (isLazy s) (isUsedMU a).

Definition mkSProd : list ArgStr -> StrDmd :=
  fun sx =>
    if Data.Foldable.any isHyperStr sx : bool then HyperStr else
    if Data.Foldable.all isLazy sx : bool then HeadStr else
    SProd sx.

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
        if andb (isTopRes res) (VarEnv.isEmptyVarEnv env) : bool then true else
        false
    | _ => false
    end.

Definition isTopSig : StrictSig -> bool :=
  fun arg_0__ => let 'Mk_StrictSig ty := arg_0__ in isTopDmdType ty.

Definition killFlags : DynFlags.DynFlags -> option KillFlags :=
  fun dflags =>
    let kf_used_once := DynFlags.gopt DynFlags.Opt_KillOneShot dflags in
    let kf_called_once := kf_used_once in
    let kf_abs := DynFlags.gopt DynFlags.Opt_KillAbsence dflags in
    if andb (negb kf_abs) (negb kf_used_once) : bool then None else
    Some (KillFlags kf_abs kf_used_once kf_called_once).

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

Definition lubArgUse : ArgUse -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Abs, x => x
    | x, Abs => x
    | Mk_Use c1 a1, Mk_Use c2 a2 => Mk_Use (lubCount c1 c2) (lubUse a1 a2)
    end.

Definition lubExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => VanStr
    | _, _ => Mk_ExnStr
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
  VarEnv.mapVarEnv (postProcessDmd (JD (Mk_Str VanStr tt) (Mk_Use Many tt))).

Definition mkBothDmdArg : DmdEnv -> BothDmdArg :=
  fun env => pair env (Dunno tt).

Definition mkDmdType : DmdEnv -> list Demand -> DmdResult -> DmdType :=
  fun fv ds res => Mk_DmdType fv ds res.

Definition mkHeadStrict : CleanDemand -> CleanDemand :=
  fun cd => let 'JD sd_0__ ud_1__ := cd in JD HeadStr ud_1__.

Definition mkJointDmd {s} {u} : s -> u -> JointDmd s u :=
  fun s u => JD s u.

Definition mkJointDmds {s} {u} : list s -> list u -> list (JointDmd s u) :=
  fun ss as_ =>
    Util.zipWithEqual (GHC.Base.hs_string__ "mkJointDmds") mkJointDmd ss as_.

Definition mkManyUsedDmd : CleanDemand -> Demand :=
  fun arg_0__ => let 'JD s a := arg_0__ in JD (Mk_Str VanStr s) (Mk_Use Many a).

Definition mkOnceUsedDmd : CleanDemand -> Demand :=
  fun arg_0__ => let 'JD s a := arg_0__ in JD (Mk_Str VanStr s) (Mk_Use One a).

Definition mkSCall : StrDmd -> StrDmd :=
  fun arg_0__ => match arg_0__ with | HyperStr => HyperStr | s => SCall s end.

Definition mkStrictSig : DmdType -> StrictSig :=
  fun dmd_ty => Mk_StrictSig dmd_ty.

Definition mkClosedStrictSig : list Demand -> DmdResult -> StrictSig :=
  fun ds res => mkStrictSig (Mk_DmdType emptyDmdEnv ds res).

Definition zapUsageEnvSig : StrictSig -> StrictSig :=
  fun arg_0__ =>
    let 'Mk_StrictSig (Mk_DmdType _ ds r) := arg_0__ in
    mkClosedStrictSig ds r.

Definition mkUCall : Count -> UseDmd -> UseDmd :=
  fun c a => UCall c a.

Definition mkWorkerDemand : GHC.Num.Int -> Demand :=
  fun n =>
    let fix go arg_0__
              := let 'num_1__ := arg_0__ in
                 if num_1__ GHC.Base.== #0 : bool then Used else
                 let 'n := arg_0__ in
                 mkUCall One (go (n GHC.Num.- #1)) in
    JD Lazy (Mk_Use One (go n)).

Definition mkCallDmd : CleanDemand -> CleanDemand :=
  fun arg_0__ => let 'JD d u := arg_0__ in JD (mkSCall d) (mkUCall One u).

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
  fun arg_0__ =>
    let 'JD s u := arg_0__ in
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

Definition saturatedByOneShots : GHC.Num.Int -> Demand -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, JD _ usg =>
        let fix go arg_2__ arg_3__
                  := match arg_2__, arg_3__ with
                     | num_4__, _ =>
                         if num_4__ GHC.Base.== #0 : bool then true else
                         match arg_2__, arg_3__ with
                         | n, UCall One u => go (n GHC.Num.- #1) u
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
  fun arg_0__ =>
    let 'Mk_StrictSig (Mk_DmdType _ dmds res) := arg_0__ in
    pair dmds res.

Definition strBot : ArgStr :=
  Mk_Str VanStr HyperStr.

Definition strTop : ArgStr :=
  Lazy.

Definition splitStrProdDmd : GHC.Num.Int -> StrDmd -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, HyperStr => Some (GHC.List.replicate n strBot)
    | n, HeadStr => Some (GHC.List.replicate n strTop)
    | n, SProd ds =>
        Panic.warnPprTrace (negb (Util.lengthIs ds n)) (GHC.Base.hs_string__
                            "ghc/compiler/basicTypes/Demand.hs") #359 ((id (GHC.Base.hs_string__
                                                                            "splitStrProdDmd") Outputable.$$
                             Panic.noString n) Outputable.$$
                            Panic.noString ds) (Some ds)
    | _, SCall _ => None
    end.

Definition splitArgStrProdDmd : GHC.Num.Int -> ArgStr -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Lazy => Some (GHC.List.replicate n Lazy)
    | n, Mk_Str _ s => splitStrProdDmd n s
    end.

Definition strictApply1Dmd : Demand :=
  JD (Mk_Str VanStr (SCall HeadStr)) (Mk_Use Many (UCall One Used)).

Definition strictSigDmdEnv : StrictSig -> DmdEnv :=
  fun arg_0__ => let 'Mk_StrictSig (Mk_DmdType env _ _) := arg_0__ in env.

Definition strictenDmd : Demand -> CleanDemand :=
  fun arg_0__ =>
    let 'JD s u := arg_0__ in
    let poke_u :=
      fun arg_1__ => match arg_1__ with | Abs => UHead | Mk_Use _ u => u end in
    let poke_s :=
      fun arg_3__ => match arg_3__ with | Lazy => HeadStr | Mk_Str _ s => s end in
    JD (poke_s s) (poke_u u).

Definition toBothDmdArg : DmdType -> BothDmdArg :=
  fun arg_0__ =>
    let 'Mk_DmdType fv _ r := arg_0__ in
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
        Mk_DmdType (VarEnv.plusVarEnv_CD bothDmd fv1 (defaultDmd r1) fv2 (defaultDmd
                                                                          t2)) ds1 (bothDmdResult r1 t2)
    end.

Definition findIdDemand : DmdType -> CoreType.Var -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv _ res, id =>
        Maybes.orElse (VarEnv.lookupVarEnv fv id) (defaultDmd res)
    end.

Definition peelFV : DmdType -> CoreType.Var -> (DmdType * Demand)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv ds res, id =>
        let dmd := Maybes.orElse (VarEnv.lookupVarEnv fv id) (defaultDmd res) in
        let fv' := VarEnv.delVarEnv fv id in pair (Mk_DmdType fv' ds res) dmd
    end.

Definition useCount {u} : Use u -> Count :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => One
    | Mk_Use One _ => One
    | _ => Many
    end.

Definition isUsedOnce : Demand -> bool :=
  fun arg_0__ =>
    let 'JD _ a := arg_0__ in
    match useCount a with
    | One => true
    | Many => false
    end.

Definition useTop : ArgUse :=
  Mk_Use Many Used.

Definition zap_musg : KillFlags -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, Abs => if kf_abs kfs : bool then useTop else Abs
    | kfs, Mk_Use c u =>
        if kf_used_once kfs : bool then Mk_Use Many (zap_usg kfs u) else
        Mk_Use c (zap_usg kfs u)
    end.

Definition kill_usage : KillFlags -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, JD s u => JD s (zap_musg kfs u)
    end.

Definition zapUsageDemand : Demand -> Demand :=
  kill_usage (KillFlags true true true).

Definition zapUsedOnceDemand : Demand -> Demand :=
  kill_usage (KillFlags false true false).

Definition zapUsedOnceSig : StrictSig -> StrictSig :=
  fun arg_0__ =>
    let 'Mk_StrictSig (Mk_DmdType env ds r) := arg_0__ in
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

Definition topDmd : Demand :=
  JD Lazy useTop.

Definition increaseStrictSigArity : GHC.Num.Int -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | arity_increase, Mk_StrictSig (Mk_DmdType env dmds res) =>
        Mk_StrictSig (Mk_DmdType env (Coq.Init.Datatypes.app (GHC.List.replicate
                                                              arity_increase topDmd) dmds) res)
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
        postProcessUnsat (peelManyCalls (Data.Foldable.length arg_ds) cd) dmd_ty
    end.

Definition nopDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil topRes.

Definition nopSig : StrictSig :=
  Mk_StrictSig nopDmdType.

Definition dmdTypeDepth : DmdType -> BasicTypes.Arity :=
  fun arg_0__ => let 'Mk_DmdType _ ds _ := arg_0__ in Data.Foldable.length ds.

Definition ensureArgs (n : BasicTypes.Arity) (d : DmdType) : DmdType :=
  let 'Mk_DmdType fv ds r := d in
  let ds' :=
    GHC.List.take n (Coq.Init.Datatypes.app ds (GHC.List.replicate
                                             (GHC.Num.fromInteger n) (resTypeArgDmd r))) in
  if _GHC.Base.==_ n (dmdTypeDepth d) then d else Mk_DmdType fv ds' (match r with
      | Dunno _ => topRes
      | _ => r
      end).

Definition removeDmdTyArgs : DmdType -> DmdType :=
  ensureArgs #0.

Definition lubDmdType : DmdType -> DmdType -> DmdType :=
  fun d1 d2 =>
    let n := GHC.Base.max (dmdTypeDepth d1) (dmdTypeDepth d2) in
    let 'Mk_DmdType fv1 ds1 r1 := ensureArgs n d1 in
    let 'Mk_DmdType fv2 ds2 r2 := ensureArgs n d2 in
    let lub_fv :=
      VarEnv.plusVarEnv_CD lubDmd fv1 (defaultDmd r1) fv2 (defaultDmd r2) in
    let lub_ds :=
      Util.zipWithEqual (GHC.Base.hs_string__ "lubDmdType") lubDmd ds1 ds2 in
    let lub_res := lubDmdResult r1 r2 in Mk_DmdType lub_fv lub_ds lub_res.

Definition deferAfterIO : DmdType -> DmdType :=
  fun arg_0__ =>
    let '(Mk_DmdType _ _ res as d) := arg_0__ in
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

Definition splitUseProdDmd (n : GHC.Num.Int) (u : UseDmd)
   : option (list ArgUse) :=
  match u with
  | Used => Some (GHC.List.replicate n useTop)
  | UHead => Some (GHC.List.replicate n Abs)
  | UProd ds => Some ds
  | UCall _ _ => None
  end.

Definition splitProdDmd_maybe : Demand -> option (list Demand) :=
  fun arg_0__ =>
    let 'JD s u := arg_0__ in
    let scrut_1__ := pair s u in
    let j_3__ :=
      match scrut_1__ with
      | pair Lazy (Mk_Use _ (UProd ux)) =>
          Some (mkJointDmds (GHC.List.replicate (Data.Foldable.length ux) Lazy) ux)
      | _ => None
      end in
    let j_5__ :=
      match scrut_1__ with
      | pair (Mk_Str _ s) (Mk_Use _ (UProd ux)) =>
          match splitStrProdDmd (Data.Foldable.length ux) s with
          | Some sx => Some (mkJointDmds sx ux)
          | _ => j_3__
          end
      | _ => j_3__
      end in
    match scrut_1__ with
    | pair (Mk_Str _ (SProd sx)) (Mk_Use _ u) =>
        match splitUseProdDmd (Data.Foldable.length sx) u with
        | Some ux => Some (mkJointDmds sx ux)
        | _ => j_5__
        end
    | _ => j_5__
    end.

Definition evalDmd : Demand :=
  JD (Mk_Str VanStr HeadStr) useTop.

Definition cleanEvalProdDmd : BasicTypes.Arity -> CleanDemand :=
  fun n => JD HeadStr (UProd (GHC.List.replicate n useTop)).

Definition vanillaCprProdRes : BasicTypes.Arity -> DmdResult :=
  fun _arity => Dunno RetProd.

Definition cprProdDmdType : BasicTypes.Arity -> DmdType :=
  fun arity => Mk_DmdType emptyDmdEnv nil (vanillaCprProdRes arity).

Definition cprProdSig : BasicTypes.Arity -> StrictSig :=
  fun arity => Mk_StrictSig (cprProdDmdType arity).

(* Unbound variables:
     ArgStr ArgUse None Some andb bool bothStr bothUse cons else false id if isUsedMU
     list lubStr lubUse markReusedDmd negb nil op_zt__ option orb pair peelManyCalls
     postProcessDmdEnv then true tt unit zap_usg BasicTypes.Arity BasicTypes.ConTag
     BasicTypes.NoOneShotInfo BasicTypes.OneShotInfo BasicTypes.OneShotLam
     BasicTypes.fIRST_TAG Coq.Init.Datatypes.app CoreType.Var Data.Foldable.all
     Data.Foldable.any Data.Foldable.length DynFlags.DynFlags
     DynFlags.Opt_KillAbsence DynFlags.Opt_KillOneShot DynFlags.gopt GHC.Base.Eq_
     GHC.Base.Synonym GHC.Base.eq_default GHC.Base.map GHC.Base.max
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.List.replicate GHC.List.take
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Prim.coerce Maybes.orElse
     Outputable.op_zdzd__ Panic.noString Panic.warnPprTrace UniqFM.nonDetUFMToList
     Util.lengthExceeds Util.lengthIs Util.zipWithEqual VarEnv.VarEnv
     VarEnv.delVarEnv VarEnv.emptyVarEnv VarEnv.isEmptyVarEnv VarEnv.lookupVarEnv
     VarEnv.mapVarEnv VarEnv.plusVarEnv_CD
*)
