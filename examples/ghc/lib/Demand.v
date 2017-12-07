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
Require Var.
Require VarEnv.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive TypeShape : Type := TsFun : TypeShape -> TypeShape
                           |  TsProd : list TypeShape -> TypeShape
                           |  TsUnk : TypeShape.

Inductive Termination r : Type := Diverges : Termination r
                               |  ThrowsExn : Termination r
                               |  Dunno : r -> Termination r.

Definition KillFlags :=
  (bool * bool)%type%type.

Inductive JointDmd s u : Type := JD : s -> u -> JointDmd s u.

Inductive ExnStr : Type := VanStr : ExnStr
                        |  Mk_ExnStr : ExnStr.

Inductive Str s : Type := Lazy : Str s
                       |  Mk_Str : ExnStr -> s -> Str s.

Inductive Count : Type := One : Count
                       |  Many : Count.

Inductive Use u : Type := Abs : Use u
                       |  Mk_Use : Count -> u -> Use u.

Definition DmdShell :=
  (JointDmd (Str unit) (Use unit))%type.

Inductive CPRResult : Type := NoCPR : CPRResult
                           |  RetProd : CPRResult
                           |  RetSum : BasicTypes.ConTag -> CPRResult.

Definition DmdResult :=
  (Termination CPRResult)%type.

Inductive ArgUse__raw : Type :=.

Reserved Notation "'ArgUse'".

Inductive UseDmd : Type := UCall : Count -> UseDmd -> UseDmd
                        |  UProd : list ArgUse -> UseDmd
                        |  UHead : UseDmd
                        |  Used : UseDmd
where "'ArgUse'" := (GHC.Base.Synonym ArgUse__raw (Use UseDmd)%type).

Inductive ArgStr__raw : Type :=.

Reserved Notation "'ArgStr'".

Inductive StrDmd : Type := HyperStr : StrDmd
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

Inductive DmdType : Type := Mk_DmdType : DmdEnv -> list
                                         Demand -> DmdResult -> DmdType.

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

Definition sd {s} {u} (arg_0__ : JointDmd s u) :=
  match arg_0__ with
    | JD sd _ => sd
  end.

Definition ud {s} {u} (arg_1__ : JointDmd s u) :=
  match arg_1__ with
    | JD _ ud => ud
  end.
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

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

(* Translating `instance forall {s} {u}, forall `{Outputable.Outputable s}
   `{Outputable.Outputable u}, Outputable.Outputable (Demand.JointDmd s u)' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.StrDmd' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.ArgStr' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.ArgUse' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.UseDmd' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.Count' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.TypeShape' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance forall {r}, forall `{Outputable.Outputable r},
   Outputable.Outputable (Demand.Termination r)' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Demand.CPRResult' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.DmdType' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable Demand.StrictSig' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary Demand.StrDmd' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.ExnStr' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.ArgStr' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.Count' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.ArgUse' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.UseDmd' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance forall {s} {u}, forall `{Binary.Binary s}
   `{Binary.Binary u}, Binary.Binary (Demand.JointDmd s u)' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.StrictSig' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.DmdType' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.DmdResult' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary Demand.CPRResult' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance GHC.Show.Show Demand.CPRResult' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___CPRResult_op_zeze__ : CPRResult -> CPRResult -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NoCPR , NoCPR => true
      | RetProd , RetProd => true
      | RetSum a1 , RetSum b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___CPRResult_op_zsze__ : CPRResult -> CPRResult -> bool :=
  fun a b => negb (Eq___CPRResult_op_zeze__ a b).

Program Instance Eq___CPRResult : GHC.Base.Eq_ CPRResult := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CPRResult_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CPRResult_op_zsze__ |}.

(* Translating `instance forall {r}, forall `{GHC.Show.Show r}, GHC.Show.Show
   (Demand.Termination r)' failed: OOPS! Cannot find information for class
   Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___Termination_op_zeze__ {inst_r} `{GHC.Base.Eq_ inst_r}
    : Termination inst_r -> Termination inst_r -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Diverges , Diverges => true
      | ThrowsExn , ThrowsExn => true
      | Dunno a1 , Dunno b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___Termination_op_zsze__ {inst_r} `{GHC.Base.Eq_ inst_r}
    : Termination inst_r -> Termination inst_r -> bool :=
  fun a b => negb (Eq___Termination_op_zeze__ a b).

Program Instance Eq___Termination {r} `{GHC.Base.Eq_ r} : GHC.Base.Eq_
                                                          (Termination r) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Termination_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Termination_op_zsze__ |}.

(* Translating `instance GHC.Show.Show Demand.UseDmd' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {u}, forall `{GHC.Show.Show u}, GHC.Show.Show
   (Demand.Use u)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Show.Show Demand.Count' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___Count_op_zeze__ : Count -> Count -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | One , One => true
      | Many , Many => true
      | _ , _ => false
    end.

Local Definition Eq___Count_op_zsze__ : Count -> Count -> bool :=
  fun a b => negb (Eq___Count_op_zeze__ a b).

Program Instance Eq___Count : GHC.Base.Eq_ Count := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Count_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Count_op_zsze__ |}.

Local Definition Eq___Use_op_zeze__ {inst_u} `{GHC.Base.Eq_ inst_u} : Use
                                                                      inst_u -> Use inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Abs , Abs => true
      | Mk_Use a1 a2 , Mk_Use b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.==
                                             b2)))
      | _ , _ => false
    end.

Local Definition Eq___Use_op_zsze__ {inst_u} `{GHC.Base.Eq_ inst_u} : Use
                                                                      inst_u -> Use inst_u -> bool :=
  fun a b => negb (Eq___Use_op_zeze__ a b).

Program Instance Eq___Use {u} `{GHC.Base.Eq_ u} : GHC.Base.Eq_ (Use u) := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___Use_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Use_op_zsze__ |}.

Local Definition Eq___UseDmd_op_zeze__ : UseDmd -> UseDmd -> bool :=
  fix UseDmd_eq x y
        := let eq' : GHC.Base.Eq_ UseDmd := GHC.Base.eq_default UseDmd_eq in
           match x , y with
             | UCall a1 a2 , UCall b1 b2 => andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)
             | UProd a1 , UProd b1 => a1 GHC.Base.== b1
             | UHead , UHead => true
             | Used , Used => true
             | _ , _ => false
           end.

Local Definition Eq___UseDmd_op_zsze__ : UseDmd -> UseDmd -> bool :=
  fun a b => negb (Eq___UseDmd_op_zeze__ a b).

Program Instance Eq___UseDmd : GHC.Base.Eq_ UseDmd := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___UseDmd_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___UseDmd_op_zsze__ |}.

(* Translating `instance GHC.Show.Show Demand.StrDmd' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance forall {s}, forall `{GHC.Show.Show s}, GHC.Show.Show
   (Demand.Str s)' failed: OOPS! Cannot find information for class Qualified
   "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Show.Show Demand.ExnStr' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___ExnStr_op_zeze__ : ExnStr -> ExnStr -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | VanStr , VanStr => true
      | Mk_ExnStr , Mk_ExnStr => true
      | _ , _ => false
    end.

Local Definition Eq___ExnStr_op_zsze__ : ExnStr -> ExnStr -> bool :=
  fun a b => negb (Eq___ExnStr_op_zeze__ a b).

Program Instance Eq___ExnStr : GHC.Base.Eq_ ExnStr := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ExnStr_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ExnStr_op_zsze__ |}.

Local Definition Eq___Str_op_zeze__ {inst_s} `{GHC.Base.Eq_ inst_s} : Str
                                                                      inst_s -> Str inst_s -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Lazy , Lazy => true
      | Mk_Str a1 a2 , Mk_Str b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.==
                                             b2)))
      | _ , _ => false
    end.

Local Definition Eq___Str_op_zsze__ {inst_s} `{GHC.Base.Eq_ inst_s} : Str
                                                                      inst_s -> Str inst_s -> bool :=
  fun a b => negb (Eq___Str_op_zeze__ a b).

Program Instance Eq___Str {s} `{GHC.Base.Eq_ s} : GHC.Base.Eq_ (Str s) := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___Str_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Str_op_zsze__ |}.

Local Definition Eq___StrDmd_op_zeze__ : StrDmd -> StrDmd -> bool :=
  fix StrDmd_eq x y
        := let eq' : GHC.Base.Eq_ StrDmd := GHC.Base.eq_default StrDmd_eq in
           match x , y with
             | HyperStr , HyperStr => true
             | SCall a1 , SCall b1 => a1 GHC.Base.== b1
             | SProd a1 , SProd b1 => a1 GHC.Base.== b1
             | HeadStr , HeadStr => true
             | _ , _ => false
           end.

Local Definition Eq___StrDmd_op_zsze__ : StrDmd -> StrDmd -> bool :=
  fun a b => negb (Eq___StrDmd_op_zeze__ a b).

Program Instance Eq___StrDmd : GHC.Base.Eq_ StrDmd := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___StrDmd_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___StrDmd_op_zsze__ |}.

(* Translating `instance forall {s} {u}, forall `{GHC.Show.Show u}
   `{GHC.Show.Show s}, GHC.Show.Show (Demand.JointDmd s u)' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___JointDmd_op_zeze__ {inst_s} {inst_u} `{GHC.Base.Eq_
                                         inst_u} `{GHC.Base.Eq_ inst_s} : JointDmd inst_s inst_u -> JointDmd inst_s
                                                                          inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | JD a1 a2 , JD b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___JointDmd_op_zsze__ {inst_s} {inst_u} `{GHC.Base.Eq_
                                         inst_u} `{GHC.Base.Eq_ inst_s} : JointDmd inst_s inst_u -> JointDmd inst_s
                                                                          inst_u -> bool :=
  fun a b => negb (Eq___JointDmd_op_zeze__ a b).

Program Instance Eq___JointDmd {s} {u} `{GHC.Base.Eq_ u} `{GHC.Base.Eq_ s}
  : GHC.Base.Eq_ (JointDmd s u) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___JointDmd_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___JointDmd_op_zsze__ |}.

Local Definition Eq___DmdType_op_zeze__ : DmdType -> DmdType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_DmdType fv1 ds1 res1 , Mk_DmdType fv2 ds2 res2 => andb (UniqFM.ufmToList
                                                                  fv1 GHC.Base.== UniqFM.ufmToList fv2) (andb (ds1
                                                                                                              GHC.Base.==
                                                                                                              ds2) (res1
                                                                                                              GHC.Base.==
                                                                                                              res2))
    end.

Local Definition Eq___DmdType_op_zsze__ : DmdType -> DmdType -> bool :=
  fun x y => negb (Eq___DmdType_op_zeze__ x y).

Program Instance Eq___DmdType : GHC.Base.Eq_ DmdType := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___DmdType_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___DmdType_op_zsze__ |}.

Local Definition Eq___StrictSig_op_zeze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___StrictSig_op_zsze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___StrictSig : GHC.Base.Eq_ StrictSig := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___StrictSig_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___StrictSig_op_zsze__ |}.

Definition absDmd : Demand :=
  JD missingValue missingValue.

Definition addDemand : Demand -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | dmd , Mk_DmdType fv ds res => Mk_DmdType fv (cons dmd ds) res
    end.

Definition argOneShots : BasicTypes.OneShotInfo -> Demand -> list
                         BasicTypes.OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | one_shot_info , JD _ usg => let go :=
                                      fix go arg_2__
                                            := match arg_2__ with
                                                 | UCall One u => cons one_shot_info (go u)
                                                 | UCall Many u => cons BasicTypes.NoOneShotInfo (go u)
                                                 | _ => nil
                                               end in
                                    match usg with
                                      | Mk_Use _ arg_usg => go arg_usg
                                      | _ => nil
                                    end
    end.

Definition argsOneShots : StrictSig -> BasicTypes.Arity -> list (list
                                                                BasicTypes.OneShotInfo) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_StrictSig (Mk_DmdType _ arg_ds _) , n_val_args => let cons_ :=
                                                               fun arg_2__ arg_3__ =>
                                                                 match arg_2__ , arg_3__ with
                                                                   | nil , nil => nil
                                                                   | a , as_ => cons a as_
                                                                 end in
                                                             let unsaturated_call :=
                                                               Util.lengthExceeds arg_ds n_val_args in
                                                             let good_one_shot :=
                                                               if unsaturated_call : bool
                                                               then BasicTypes.ProbOneShot
                                                               else BasicTypes.OneShotLam in
                                                             let go :=
                                                               fix go arg_8__
                                                                     := match arg_8__ with
                                                                          | nil => nil
                                                                          | cons arg_d arg_ds => cons_ (argOneShots
                                                                                                       good_one_shot
                                                                                                       arg_d) (go
                                                                                                       arg_ds)
                                                                        end in
                                                             go arg_ds
    end.

Definition botDmd : Demand :=
  JD missingValue missingValue.

Definition defaultDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => absDmd | _ => botDmd end.

Definition findIdDemand : DmdType -> Var.Var -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_DmdType fv _ res , id => Maybes.orElse (VarEnv.lookupVarEnv fv id)
                                                  (defaultDmd res)
    end.

Definition peelFV : DmdType -> Var.Var -> (DmdType * Demand)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_DmdType fv ds res , id => let dmd :=
                                       Maybes.orElse (VarEnv.lookupVarEnv fv id) (defaultDmd res) in
                                     let fv' := VarEnv.delVarEnv fv id in pair (Mk_DmdType fv' ds res) dmd
    end.

Definition botRes : DmdResult :=
  Diverges.

Definition bothArgUse : ArgUse -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Abs , x => x
      | x , Abs => x
      | Mk_Use _ a1 , Mk_Use _ a2 => Mk_Use Many (bothUse a1 a2)
    end.

Definition bothCleanDmd : CleanDemand -> CleanDemand -> CleanDemand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | JD s1 a1 , JD s2 a2 => JD missingValue missingValue
    end.

Definition bothDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | JD s1 a1 , JD s2 a2 => JD missingValue missingValue
    end.

Definition bothDmdResult : DmdResult -> Termination unit -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , Diverges => Diverges
      | r , ThrowsExn => match r with
                           | Diverges => r
                           | _ => ThrowsExn
                         end
      | r , Dunno _ => r
    end.

Definition bothDmdType : DmdType -> BothDmdArg -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_DmdType fv1 ds1 r1 , pair fv2 t2 => Mk_DmdType (VarEnv.plusVarEnv_CD
                                                          bothDmd fv1 (defaultDmd r1) fv2 (defaultDmd t2)) ds1
                                               (bothDmdResult r1 t2)
    end.

Definition bothExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_ExnStr , Mk_ExnStr => Mk_ExnStr
      | _ , _ => VanStr
    end.

Definition bothArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Lazy , s => s
      | s , Lazy => s
      | Mk_Str x1 s1 , Mk_Str x2 s2 => Mk_Str (bothExnStr x1 x2) (bothStr s1 s2)
    end.

Definition catchArgDmd : Demand :=
  JD missingValue missingValue.

Definition cleanEvalDmd : CleanDemand :=
  JD missingValue missingValue.

Definition cleanEvalProdDmd : BasicTypes.Arity -> CleanDemand :=
  fun n => JD missingValue missingValue.

Definition cleanUseDmd_maybe : Demand -> option UseDmd :=
  fun arg_0__ => match arg_0__ with | JD _ (Mk_Use _ u) => Some u | _ => None end.

Definition countMany : Count :=
  Many.

Definition countOnce : Count :=
  One.

Definition cprProdRes : list DmdType -> DmdResult :=
  fun _arg_tys => Dunno GHC.Base.$ RetProd.

Definition cprSumRes : BasicTypes.ConTag -> DmdResult :=
  fun tag => Dunno GHC.Base.$ RetSum tag.

Definition emptyDmdEnv : VarEnv.VarEnv Demand :=
  VarEnv.emptyVarEnv.

Definition botDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil botRes.

Definition botSig : StrictSig :=
  Mk_StrictSig botDmdType.

Definition evalDmd : Demand :=
  JD missingValue missingValue.

Definition exnRes : DmdResult :=
  ThrowsExn.

Definition getStrDmd {s} {u} : JointDmd s u -> s :=
  sd.

Definition getUseDmd {s} {u} : JointDmd s u -> u :=
  ud.

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
    match arg_0__ with
      | Mk_StrictSig (Mk_DmdType _ _ res) => isBotRes res
    end.

Definition appIsBottom : StrictSig -> GHC.Num.Int -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_StrictSig (Mk_DmdType _ ds res) , n => if isBotRes res : bool
                                                  then negb GHC.Base.$ Util.lengthExceeds ds n
                                                  else false
    end.

Definition isHyperStr : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Str _ HyperStr => true | _ => false end.

Definition isLazy : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Lazy => true | Mk_Str _ _ => false end.

Definition isWeakDmd : Demand -> bool :=
  fun arg_0__ => match arg_0__ with | JD s a => andb (isLazy s) (isUsedMU a) end.

Definition mkSProd : list ArgStr -> StrDmd :=
  fun sx =>
    let j_0__ := SProd sx in
    let j_1__ := if Data.Foldable.all isLazy sx : bool then HeadStr else j_0__ in
    if Data.Foldable.any isHyperStr sx : bool
    then HyperStr
    else j_1__.

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

Definition isNopDmdType : DmdType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_DmdType env nil res => if andb (isTopRes res) (VarEnv.isEmptyVarEnv
                                          env) : bool
                                  then true
                                  else false
      | _ => false
    end.

Definition isNopSig : StrictSig -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_StrictSig ty => isNopDmdType ty end.

Definition killFlags : DynFlags.DynFlags -> option KillFlags :=
  fun dflags =>
    let kill_one_shot := DynFlags.gopt DynFlags.Opt_KillOneShot dflags in
    let kill_abs := DynFlags.gopt DynFlags.Opt_KillAbsence dflags in
    let j_2__ := Some (pair kill_abs kill_one_shot) in
    if andb (negb kill_abs) (negb kill_one_shot) : bool
    then None
    else j_2__.

Definition kill_usage : KillFlags -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | kfs , JD s u => JD missingValue missingValue
    end.

Definition zapUsageDemand : Demand -> Demand :=
  kill_usage (pair true true).

Definition killUsageDemand : DynFlags.DynFlags -> Demand -> Demand :=
  fun dflags dmd =>
    match killFlags dflags with
      | Some kfs => kill_usage kfs dmd
      | _ => dmd
    end.

Definition killUsageSig : DynFlags.DynFlags -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | dflags , (Mk_StrictSig (Mk_DmdType env ds r) as sig) => match killFlags
                                                                        dflags with
                                                                  | Some kfs => Mk_StrictSig (Mk_DmdType env
                                                                                             (GHC.Base.map (kill_usage
                                                                                                           kfs) ds) r)
                                                                  | _ => sig
                                                                end
    end.

Definition lazyApply1Dmd : Demand :=
  JD missingValue missingValue.

Definition lazyApply2Dmd : Demand :=
  JD missingValue missingValue.

Definition lubCPR : CPRResult -> CPRResult -> CPRResult :=
  fun arg_0__ arg_1__ =>
    let j_2__ :=
      match arg_0__ , arg_1__ with
        | RetProd , RetProd => RetProd
        | _ , _ => NoCPR
      end in
    match arg_0__ , arg_1__ with
      | RetSum t1 , RetSum t2 => if t1 GHC.Base.== t2 : bool
                                 then RetSum t1
                                 else j_2__
      | _ , _ => j_2__
    end.

Definition lubDmdResult : DmdResult -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Diverges , r => r
      | ThrowsExn , Diverges => ThrowsExn
      | ThrowsExn , r => r
      | Dunno c1 , Diverges => Dunno c1
      | Dunno c1 , ThrowsExn => Dunno c1
      | Dunno c1 , Dunno c2 => Dunno (lubCPR c1 c2)
    end.

Definition lubCount : Count -> Count -> Count :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , Many => Many
      | Many , _ => Many
      | x , _ => x
    end.

Definition lubArgUse : ArgUse -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Abs , x => x
      | x , Abs => x
      | Mk_Use c1 a1 , Mk_Use c2 a2 => Mk_Use (lubCount c1 c2) (lubUse a1 a2)
    end.

Definition lubDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | JD s1 a1 , JD s2 a2 => JD missingValue missingValue
    end.

Definition lubExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | VanStr , VanStr => VanStr
      | _ , _ => Mk_ExnStr
    end.

Definition lubArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Lazy , _ => Lazy
      | _ , Lazy => Lazy
      | Mk_Str x1 s1 , Mk_Str x2 s2 => Mk_Str (lubExnStr x1 x2) (lubStr s1 s2)
    end.

Definition markExnStr : ArgStr -> ArgStr :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Str VanStr s => Mk_Str Mk_ExnStr s
      | s => s
    end.

Definition postProcessDmd : DmdShell -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | JD ss us , JD s a => let a' :=
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
                             JD missingValue missingValue
    end.

Definition reuseEnv : DmdEnv -> DmdEnv :=
  VarEnv.mapVarEnv (postProcessDmd (JD missingValue missingValue)).

Definition mkBothDmdArg : DmdEnv -> BothDmdArg :=
  fun env => pair env (Dunno tt).

Definition mkCallDmd : CleanDemand -> CleanDemand :=
  fun arg_0__ => match arg_0__ with | JD d u => JD missingValue missingValue end.

Definition mkDmdType : DmdEnv -> list Demand -> DmdResult -> DmdType :=
  fun fv ds res => Mk_DmdType fv ds res.

Definition mkHeadStrict : CleanDemand -> CleanDemand :=
  fun cd => match cd with | JD sd_0__ ud_1__ => JD HeadStr ud_1__ end.

Definition mkJointDmd {s} {u} : s -> u -> JointDmd s u :=
  fun s u => JD missingValue missingValue.

Definition mkJointDmds {s} {u} : list s -> list u -> list (JointDmd s u) :=
  fun ss as_ =>
    Util.zipWithEqual (GHC.Base.hs_string__ "mkJointDmds") mkJointDmd ss as_.

Definition mkManyUsedDmd : CleanDemand -> Demand :=
  fun arg_0__ => match arg_0__ with | JD s a => JD missingValue missingValue end.

Definition mkOnceUsedDmd : CleanDemand -> Demand :=
  fun arg_0__ => match arg_0__ with | JD s a => JD missingValue missingValue end.

Definition mkProdDmd : list Demand -> CleanDemand :=
  fun dx => JD missingValue missingValue.

Definition mkSCall : StrDmd -> StrDmd :=
  fun arg_0__ => match arg_0__ with | HyperStr => HyperStr | s => SCall s end.

Definition mkStrictSig : DmdType -> StrictSig :=
  fun dmd_ty => Mk_StrictSig dmd_ty.

Definition mkClosedStrictSig : list Demand -> DmdResult -> StrictSig :=
  fun ds res => mkStrictSig (Mk_DmdType emptyDmdEnv ds res).

Definition mkUCall : Count -> UseDmd -> UseDmd :=
  fun c a => UCall c a.

Definition mkUProd : list ArgUse -> UseDmd :=
  fun ux =>
    let j_0__ := UProd ux in
    if Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.== Abs) ux : bool
    then UHead
    else j_0__.

Definition oneifyDmd : Demand -> Demand :=
  fun arg_0__ =>
    match arg_0__ with
      | JD s (Mk_Use _ a) => JD missingValue missingValue
      | jd => jd
    end.

Definition peelCallDmd : CleanDemand -> (CleanDemand * DmdShell)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | JD s u => match match u with
                            | UCall c u' => pair u' (Mk_Use c tt)
                            | _ => pair Used (Mk_Use Many tt)
                          end with
                    | pair u' us => match match s with
                                              | SCall s' => pair s' (Mk_Str VanStr tt)
                                              | HyperStr => pair HyperStr (Mk_Str VanStr tt)
                                              | _ => pair HeadStr Lazy
                                            end with
                                      | pair s' ss => pair (JD missingValue missingValue) (JD missingValue
                                                                                              missingValue)
                                    end
                  end
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
  JD missingValue missingValue.

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
    match arg_0__ with
      | Mk_StrictSig (Mk_DmdType _ dmds res) => pair dmds res
    end.

Definition strBot : ArgStr :=
  Mk_Str VanStr HyperStr.

Definition strTop : ArgStr :=
  Lazy.

Definition splitStrProdDmd : GHC.Num.Int -> StrDmd -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | n , HyperStr => Some (GHC.List.replicate n strBot)
      | n , HeadStr => Some (GHC.List.replicate n strTop)
      | n , SProd ds => if andb Util.debugIsOn (negb (Util.lengthIs ds n)) : bool
                        then (Panic.assertPanic (GHC.Base.hs_string__
                                                "ghc/compiler/basicTypes/Demand.hs") (GHC.Num.fromInteger 304))
                        else Some ds
      | _ , SCall _ => None
    end.

Definition splitArgStrProdDmd : GHC.Num.Int -> ArgStr -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | n , Lazy => Some (GHC.List.replicate n Lazy)
      | n , Mk_Str _ s => splitStrProdDmd n s
    end.

Definition strictApply1Dmd : Demand :=
  JD missingValue missingValue.

Definition strictenDmd : Demand -> CleanDemand :=
  fun arg_0__ =>
    match arg_0__ with
      | JD s u => let poke_u :=
                    fun arg_1__ => match arg_1__ with | Abs => UHead | Mk_Use _ u => u end in
                  let poke_s :=
                    fun arg_3__ => match arg_3__ with | Lazy => HeadStr | Mk_Str _ s => s end in
                  JD missingValue missingValue
    end.

Definition toBothDmdArg : DmdType -> BothDmdArg :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_DmdType fv _ r => let go :=
                               fun arg_1__ =>
                                 match arg_1__ with
                                   | Dunno _ => Dunno tt
                                   | ThrowsExn => ThrowsExn
                                   | Diverges => Diverges
                                 end in
                             pair fv (go r)
    end.

Definition topDmd : Demand :=
  JD missingValue missingValue.

Definition increaseStrictSigArity : GHC.Num.Int -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | arity_increase , Mk_StrictSig (Mk_DmdType env dmds res) => Mk_StrictSig
                                                                   (Mk_DmdType env (Coq.Init.Datatypes.app
                                                                                   (GHC.List.replicate arity_increase
                                                                                   topDmd) dmds) res)
    end.

Definition resTypeArgDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => topDmd | _ => botDmd end.

Definition splitDmdTy : DmdType -> (Demand * DmdType)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_DmdType fv (cons dmd dmds) res_ty => pair dmd (Mk_DmdType fv dmds res_ty)
      | (Mk_DmdType _ nil res_ty as ty) => pair (resTypeArgDmd res_ty) ty
    end.

Definition topRes : DmdResult :=
  Dunno NoCPR.

Definition postProcessDmdResult : Str unit -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Lazy , _ => topRes
      | Mk_Str Mk_ExnStr _ , ThrowsExn => topRes
      | _ , res => res
    end.

Definition postProcessDmdType : DmdShell -> DmdType -> BothDmdArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (JD ss _ as du) , Mk_DmdType fv _ res_ty => let term_info :=
                                                      let scrut_2__ := postProcessDmdResult ss res_ty in
                                                      match scrut_2__ with
                                                        | Dunno _ => Dunno tt
                                                        | ThrowsExn => ThrowsExn
                                                        | Diverges => Diverges
                                                      end in
                                                    pair (postProcessDmdEnv du fv) term_info
    end.

Definition postProcessUnsat : DmdShell -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (JD ss _ as ds) , Mk_DmdType fv args res_ty => Mk_DmdType (postProcessDmdEnv
                                                                  ds fv) (GHC.Base.map (postProcessDmd ds) args)
                                                       (postProcessDmdResult ss res_ty)
    end.

Definition dmdTransformSig : StrictSig -> CleanDemand -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_StrictSig (Mk_DmdType _ arg_ds _ as dmd_ty) , cd => postProcessUnsat
                                                               (peelManyCalls (Data.Foldable.length arg_ds) cd) dmd_ty
    end.

Definition nopDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil topRes.

Definition nopSig : StrictSig :=
  Mk_StrictSig nopDmdType.

Definition dmdTypeDepth : DmdType -> BasicTypes.Arity :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_DmdType _ ds _ => Data.Foldable.length ds
    end.

Definition ensureArgs (n : BasicTypes.Arity) (d : DmdType) : DmdType :=
  match d with
    | Mk_DmdType fv ds r => let ds' :=
                              GHC.List.take n (Coq.Init.Datatypes.app ds (GHC.List.replicate
                                                                      (GHC.Num.fromInteger n) (resTypeArgDmd r))) in
                            if _GHC.Base.==_ n (dmdTypeDepth d) then d else Mk_DmdType fv ds' (match r with
                                 | Dunno _ => topRes
                                 | _ => r
                               end)
  end.

Definition removeDmdTyArgs : DmdType -> DmdType :=
  ensureArgs (GHC.Num.fromInteger 0).

Definition lubDmdType : DmdType -> DmdType -> DmdType :=
  fun d1 d2 =>
    let n := GHC.Base.max (dmdTypeDepth d1) (dmdTypeDepth d2) in
    match ensureArgs n d1 with
      | Mk_DmdType fv1 ds1 r1 => match ensureArgs n d2 with
                                   | Mk_DmdType fv2 ds2 r2 => let lub_fv :=
                                                                VarEnv.plusVarEnv_CD lubDmd fv1 (defaultDmd r1) fv2
                                                                (defaultDmd r2) in
                                                              let lub_ds :=
                                                                Util.zipWithEqual (GHC.Base.hs_string__ "lubDmdType")
                                                                lubDmd ds1 ds2 in
                                                              let lub_res := lubDmdResult r1 r2 in
                                                              Mk_DmdType lub_fv lub_ds lub_res
                                 end
    end.

Definition deferAfterIO : DmdType -> DmdType :=
  fun arg_0__ =>
    match arg_0__ with
      | (Mk_DmdType _ _ res as d) => let defer_res :=
                                       fun arg_1__ => match arg_1__ with | (Dunno _ as r) => r | _ => topRes end in
                                     let scrut_3__ := lubDmdType d nopDmdType in
                                     match scrut_3__ with
                                       | Mk_DmdType fv ds _ => Mk_DmdType fv ds (defer_res res)
                                     end
    end.

Definition trimCPRInfo : bool -> bool -> DmdResult -> DmdResult :=
  fun trim_all trim_sums res =>
    let trimC :=
      fun arg_0__ =>
        match arg_0__ with
          | RetSum n => let j_1__ := RetSum n in
                        if orb trim_all trim_sums : bool
                        then NoCPR
                        else j_1__
          | RetProd => if trim_all : bool
                       then NoCPR
                       else RetProd
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

Definition useCount {u} : Use u -> Count :=
  fun arg_0__ =>
    match arg_0__ with
      | Abs => One
      | Mk_Use One _ => One
      | _ => Many
    end.

Definition isUsedOnce : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | JD _ a => let scrut_1__ := useCount a in
                  match scrut_1__ with
                    | One => true
                    | Many => false
                  end
    end.

Definition useTop : ArgUse :=
  Mk_Use Many Used.

Definition splitUseProdDmd (n : GHC.Num.Int) (u : UseDmd) : option (list
                                                                   ArgUse) :=
  match u with
    | Used => Some (GHC.List.replicate n useTop)
    | UHead => Some (GHC.List.replicate n Abs)
    | UProd ds => Some ds
    | UCall _ _ => None
  end.

Definition splitProdDmd_maybe : Demand -> option (list Demand) :=
  fun arg_0__ =>
    match arg_0__ with
      | JD s u => let scrut_1__ := pair s u in
                  let j_3__ :=
                    match scrut_1__ with
                      | pair Lazy (Mk_Use _ (UProd ux)) => Some (mkJointDmds (GHC.List.replicate
                                                                             (Data.Foldable.length ux) Lazy) ux)
                      | _ => None
                    end in
                  let j_5__ :=
                    match scrut_1__ with
                      | pair (Mk_Str _ s) (Mk_Use _ (UProd ux)) => match splitStrProdDmd
                                                                           (Data.Foldable.length ux) s with
                                                                     | Some sx => Some (mkJointDmds sx ux)
                                                                     | _ => j_3__
                                                                   end
                      | _ => j_3__
                    end in
                  match scrut_1__ with
                    | pair (Mk_Str _ (SProd sx)) (Mk_Use _ u) => match splitUseProdDmd
                                                                         (Data.Foldable.length sx) u with
                                                                   | Some ux => Some (mkJointDmds sx ux)
                                                                   | _ => j_5__
                                                                 end
                    | _ => j_5__
                  end
    end.

Definition vanillaCprProdRes : BasicTypes.Arity -> DmdResult :=
  fun _arity => Dunno GHC.Base.$ RetProd.

Definition cprProdDmdType : BasicTypes.Arity -> DmdType :=
  fun arity => Mk_DmdType emptyDmdEnv nil (vanillaCprProdRes arity).

Definition cprProdSig : BasicTypes.Arity -> StrictSig :=
  fun arity => Mk_StrictSig (cprProdDmdType arity).

Definition zap_count : KillFlags -> Count -> Count :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | pair _ kill_one_shot , c => if kill_one_shot : bool
                                    then Many
                                    else c
    end.

Definition zap_musg : KillFlags -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | pair kill_abs _ , Abs => if kill_abs : bool
                                 then useTop
                                 else Abs
      | kfs , Mk_Use c u => Mk_Use (zap_count kfs c) (zap_usg kfs u)
    end.

(* Unbound variables:
     ArgStr ArgUse None Some andb bool bothStr bothUse cons else false if isUsedMU
     list lubStr lubUse markReusedDmd negb nil op_zt__ option orb pair peelManyCalls
     postProcessDmdEnv then true tt unit zap_usg BasicTypes.Arity BasicTypes.ConTag
     BasicTypes.NoOneShotInfo BasicTypes.OneShotInfo BasicTypes.OneShotLam
     BasicTypes.ProbOneShot BasicTypes.fIRST_TAG Coq.Init.Datatypes.app
     Data.Foldable.all Data.Foldable.any Data.Foldable.length DynFlags.DynFlags
     DynFlags.Opt_KillAbsence DynFlags.Opt_KillOneShot DynFlags.gopt GHC.Base.Eq_
     GHC.Base.Synonym GHC.Base.eq_default GHC.Base.map GHC.Base.max GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.List.replicate GHC.List.take
     GHC.Num.Int GHC.Num.fromInteger GHC.Prim.coerce Maybes.orElse Panic.assertPanic
     UniqFM.ufmToList Util.debugIsOn Util.lengthExceeds Util.lengthIs
     Util.zipWithEqual Var.Var VarEnv.VarEnv VarEnv.delVarEnv VarEnv.emptyVarEnv
     VarEnv.isEmptyVarEnv VarEnv.lookupVarEnv VarEnv.mapVarEnv VarEnv.plusVarEnv_CD
*)
