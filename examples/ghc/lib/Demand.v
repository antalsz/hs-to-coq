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
Require GHC.Base.
Require GHC.Prim.
Require UniqFM.
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
(* Converted value declarations: *)

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
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
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
  fun arg_37__ arg_38__ =>
    match arg_37__ , arg_38__ with
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
  fun arg_22__ arg_23__ =>
    match arg_22__ , arg_23__ with
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
  fun arg_26__ arg_27__ =>
    match arg_26__ , arg_27__ with
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
  fun arg_7__ arg_8__ =>
    match arg_7__ , arg_8__ with
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
  fun arg_11__ arg_12__ =>
    match arg_11__ , arg_12__ with
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
  fun arg_2__ arg_3__ =>
    match arg_2__ , arg_3__ with
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
  fun arg_49__ arg_50__ =>
    match arg_49__ , arg_50__ with
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

Axiom strictifyDictDmd : forall {A : Type}, A.

Axiom dmdTransformDictSelSig : forall {A : Type}, A.

Axiom mkProdDmd : forall {A : Type}, A.

Axiom getStrDmd : forall {A : Type}, A.

Axiom getUseDmd : forall {A : Type}, A.

Axiom dmdTransformDataConSig : forall {A : Type}, A.

Axiom splitProdDmd_maybe : forall {A : Type}, A.

Axiom addCaseBndrDmd : forall {A : Type}, A.

Axiom mkJointDmds : forall {A : Type}, A.

Axiom mkJointDmd : forall {A : Type}, A.

Axiom splitDmdTy : forall {A : Type}, A.

Axiom removeDmdTyArgs : forall {A : Type}, A.

Axiom deferAfterIO : forall {A : Type}, A.

Axiom lubDmdType : forall {A : Type}, A.

Axiom ensureArgs : forall {A : Type}, A.

Axiom resTypeArgDmd : forall {A : Type}, A.

Axiom findIdDemand : forall {A : Type}, A.

Axiom peelFV : forall {A : Type}, A.

Axiom bothDmdType : forall {A : Type}, A.

Axiom defaultDmd : forall {A : Type}, A.

Axiom botDmd : forall {A : Type}, A.

Axiom splitArgStrProdDmd : forall {A : Type}, A.

Axiom splitStrProdDmd : forall {A : Type}, A.

Axiom strBot : forall {A : Type}, A.

Axiom strTop : forall {A : Type}, A.

Axiom mkCallDmd : forall {A : Type}, A.

Axiom mkSCall : forall {A : Type}, A.

Axiom bothCleanDmd : forall {A : Type}, A.

Axiom bothDmd : forall {A : Type}, A.

Axiom bothArgStr : forall {A : Type}, A.

Axiom bothStr : forall {A : Type}, A.

Axiom lubDmd : forall {A : Type}, A.

Axiom lubArgStr : forall {A : Type}, A.

Axiom lubStr : forall {A : Type}, A.

Axiom mkSProd : forall {A : Type}, A.

Axiom splitFVs : forall {A : Type}, A.

Axiom isWeakDmd : forall {A : Type}, A.

Axiom isLazy : forall {A : Type}, A.

Axiom isHyperStr : forall {A : Type}, A.

Axiom lubExnStr : forall {A : Type}, A.

Axiom bothExnStr : forall {A : Type}, A.

Axiom seqStrictSig : forall {A : Type}, A.

Axiom seqDmdType : forall {A : Type}, A.

Axiom seqDmdEnv : forall {A : Type}, A.

Axiom seqDemandList : forall {A : Type}, A.

Axiom seqDemand : forall {A : Type}, A.

Axiom seqArgStr : forall {A : Type}, A.

Axiom seqStrDmdList : forall {A : Type}, A.

Axiom seqStrDmd : forall {A : Type}, A.

Axiom countOnce : forall {A : Type}, A.

Axiom countMany : forall {A : Type}, A.

Axiom useBot : forall {A : Type}, A.

Axiom killUsageSig : forall {A : Type}, A.

Axiom killUsageDemand : forall {A : Type}, A.

Axiom zapUsageDemand : forall {A : Type}, A.

Axiom kill_usage : forall {A : Type}, A.

Axiom zap_usg : forall {A : Type}, A.

Axiom zap_musg : forall {A : Type}, A.

Axiom increaseStrictSigArity : forall {A : Type}, A.

Axiom topDmd : forall {A : Type}, A.

Axiom cleanEvalProdDmd : forall {A : Type}, A.

Axiom evalDmd : forall {A : Type}, A.

Axiom splitUseProdDmd : forall {A : Type}, A.

Axiom bothArgUse : forall {A : Type}, A.

Axiom bothUse : forall {A : Type}, A.

Axiom lubArgUse : forall {A : Type}, A.

Axiom lubUse : forall {A : Type}, A.

Axiom useTop : forall {A : Type}, A.

Axiom mkUCall : forall {A : Type}, A.

Axiom mkUProd : forall {A : Type}, A.

Axiom lubCount : forall {A : Type}, A.

Axiom peelUseCall : forall {A : Type}, A.

Axiom dmdTransformSig : forall {A : Type}, A.

Axiom postProcessUnsat : forall {A : Type}, A.

Axiom reuseEnv : forall {A : Type}, A.

Axiom postProcessDmdType : forall {A : Type}, A.

Axiom postProcessDmdEnv : forall {A : Type}, A.

Axiom postProcessDmd : forall {A : Type}, A.

Axiom markReused : forall {A : Type}, A.

Axiom markReusedDmd : forall {A : Type}, A.

Axiom isUsedU : forall {A : Type}, A.

Axiom isUsedMU : forall {A : Type}, A.

Axiom seqArgUse : forall {A : Type}, A.

Axiom seqArgUseList : forall {A : Type}, A.

Axiom seqUseDmd : forall {A : Type}, A.

Axiom isUsedOnce : forall {A : Type}, A.

Axiom useCount : forall {A : Type}, A.

Axiom mkHeadStrict : forall {A : Type}, A.

Axiom mkOnceUsedDmd : forall {A : Type}, A.

Axiom mkManyUsedDmd : forall {A : Type}, A.

Axiom cleanEvalDmd : forall {A : Type}, A.

Axiom strictApply1Dmd : forall {A : Type}, A.

Axiom catchArgDmd : forall {A : Type}, A.

Axiom lazyApply1Dmd : forall {A : Type}, A.

Axiom lazyApply2Dmd : forall {A : Type}, A.

Axiom absDmd : forall {A : Type}, A.

Axiom seqDmd : forall {A : Type}, A.

Axiom oneifyDmd : forall {A : Type}, A.

Axiom isTopDmd : forall {A : Type}, A.

Axiom isAbsDmd : forall {A : Type}, A.

Axiom isSeqDmd : forall {A : Type}, A.

Axiom isStrictDmd : forall {A : Type}, A.

Axiom cleanUseDmd_maybe : forall {A : Type}, A.

Axiom trimToType : forall {A : Type}, A.

Axiom lubDmdResult : forall {A : Type}, A.

Axiom lubCPR : forall {A : Type}, A.

Axiom bothDmdResult : forall {A : Type}, A.

Axiom seqDmdResult : forall {A : Type}, A.

Axiom seqCPRResult : forall {A : Type}, A.

Axiom postProcessDmdResult : forall {A : Type}, A.

Axiom nopSig : forall {A : Type}, A.

Axiom nopDmdType : forall {A : Type}, A.

Axiom topRes : forall {A : Type}, A.

Axiom exnRes : forall {A : Type}, A.

Axiom botSig : forall {A : Type}, A.

Axiom botDmdType : forall {A : Type}, A.

Axiom botRes : forall {A : Type}, A.

Axiom cprSumRes : forall {A : Type}, A.

Axiom cprProdRes : forall {A : Type}, A.

Axiom cprProdSig : forall {A : Type}, A.

Axiom cprProdDmdType : forall {A : Type}, A.

Axiom vanillaCprProdRes : forall {A : Type}, A.

Axiom isNopSig : forall {A : Type}, A.

Axiom isNopDmdType : forall {A : Type}, A.

Axiom isTopRes : forall {A : Type}, A.

Axiom appIsBottom : forall {A : Type}, A.

Axiom isBottomingSig : forall {A : Type}, A.

Axiom isBotRes : forall {A : Type}, A.

Axiom trimCPRInfo : forall {A : Type}, A.

Axiom returnsCPR_maybe : forall {A : Type}, A.

Axiom retCPR_maybe : forall {A : Type}, A.

Axiom mkBothDmdArg : forall {A : Type}, A.

Axiom toBothDmdArg : forall {A : Type}, A.

Axiom mkClosedStrictSig : forall {A : Type}, A.

Axiom emptyDmdEnv : forall {A : Type}, A.

Axiom mkDmdType : forall {A : Type}, A.

Axiom dmdTypeDepth : forall {A : Type}, A.

Axiom strictenDmd : forall {A : Type}, A.

Axiom toCleanDmd : forall {A : Type}, A.

Axiom markExnStr : forall {A : Type}, A.

Axiom peelCallDmd : forall {A : Type}, A.

Axiom peelManyCalls : forall {A : Type}, A.

Axiom addDemand : forall {A : Type}, A.

Axiom pprIfaceStrictSig : forall {A : Type}, A.

Axiom mkStrictSig : forall {A : Type}, A.

Axiom splitStrictSig : forall {A : Type}, A.

Axiom argsOneShots : forall {A : Type}, A.

Axiom argOneShots : forall {A : Type}, A.

Axiom killFlags : forall {A : Type}, A.

Axiom zap_count : forall {A : Type}, A.

(* Unbound variables:
     ArgStr ArgUse andb bool false list negb op_zt__ true unit BasicTypes.ConTag
     GHC.Base.Eq_ GHC.Base.Synonym GHC.Base.eq_default GHC.Base.op_zeze__
     GHC.Base.op_zsze__ GHC.Prim.coerce UniqFM.ufmToList VarEnv.VarEnv
*)
