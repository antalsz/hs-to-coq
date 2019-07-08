(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Bag.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreArity.
Require CoreUtils.
Require Data.Foldable.
Require Data.OldList.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require IntMap.
Require MkCore.
Require Panic.
Require SetLevels.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition MinorEnv :=
  (IntMap.IntMap (Bag.Bag MkCore.FloatBind))%type.

Definition MajorEnv :=
  (IntMap.IntMap MinorEnv)%type.

Inductive FloatStats : Type := | FlS : nat -> nat -> nat -> FloatStats.

Definition FloatLet :=
  Core.CoreBind%type.

Inductive FloatBinds : Type
  := | FB
   : (Bag.Bag FloatLet) -> (Bag.Bag MkCore.FloatBind) -> MajorEnv -> FloatBinds.

(* Midamble *)

Instance Default_FloatStats : GHC.Err.Default FloatStats := 
  GHC.Err.Build_Default _ (FlS GHC.Err.default GHC.Err.default GHC.Err.default).


(* Converted value declarations: *)

Definition zeroStats : FloatStats :=
  FlS #0 #0 #0.

Definition wrapTick : Core.Tickish Core.Id -> FloatBinds -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | t, FB tops ceils defns =>
        let maybe_tick := fun e => if CoreUtils.exprIsHNF e : bool then e else e in
        let wrap_bind :=
          fun arg_3__ =>
            match arg_3__ with
            | Core.NonRec binder rhs => Core.NonRec binder (maybe_tick rhs)
            | Core.Rec pairs => Core.Rec (Util.mapSnd maybe_tick pairs)
            end in
        let wrap_one :=
          fun arg_7__ =>
            match arg_7__ with
            | MkCore.FloatLet bind => MkCore.FloatLet (wrap_bind bind)
            | MkCore.FloatCase e b c bs => MkCore.FloatCase (maybe_tick e) b c bs
            end in
        let wrap_defns := Bag.mapBag wrap_one in
        FB (Bag.mapBag wrap_bind tops) (wrap_defns ceils) (IntMap.map (IntMap.map
                                                                       wrap_defns) defns)
    end.

Definition unitLetFloat : SetLevels.Level -> FloatLet -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (SetLevels.Mk_Level major minor t as lvl), b =>
        let floats := Bag.unitBag (MkCore.FloatLet b) in
        if SetLevels.isTopLvl lvl : bool
        then FB (Bag.unitBag b) Bag.emptyBag IntMap.empty else
        if t GHC.Base.== SetLevels.JoinCeilLvl : bool
        then FB Bag.emptyBag floats IntMap.empty else
        FB Bag.emptyBag Bag.emptyBag (IntMap.singleton major (IntMap.singleton minor
                                                              floats))
    end.

Definition unitCaseFloat
   : SetLevels.Level ->
     Core.CoreExpr -> Core.Id -> Core.AltCon -> list Core.Var -> FloatBinds :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | SetLevels.Mk_Level major minor t, e, b, con, bs =>
        let floats := Bag.unitBag (MkCore.FloatCase e b con bs) in
        if t GHC.Base.== SetLevels.JoinCeilLvl : bool
        then FB Bag.emptyBag floats IntMap.empty else
        FB Bag.emptyBag Bag.emptyBag (IntMap.singleton major (IntMap.singleton minor
                                                              floats))
    end.

Definition splitRecFloats
   : Bag.Bag MkCore.FloatBind ->
     (list (Core.Id * Core.CoreExpr)%type * list (Core.Id * Core.CoreExpr)%type *
      Bag.Bag MkCore.FloatBind)%type :=
  fun fs =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | ul_prs, prs, cons (MkCore.FloatLet (Core.NonRec b r)) fs =>
                     if andb (@Core.isUnliftedType tt (Id.idType b)) (negb (Id.isJoinId b)) : bool
                     then go (cons (pair b r) ul_prs) prs fs else
                     go ul_prs (cons (pair b r) prs) fs
                 | _, _, _ =>
                     match arg_0__, arg_1__, arg_2__ with
                     | ul_prs, prs, cons (MkCore.FloatLet (Core.Rec prs')) fs =>
                         go ul_prs (Coq.Init.Datatypes.app prs' prs) fs
                     | ul_prs, prs, fs =>
                         pair (pair (GHC.List.reverse ul_prs) prs) (Bag.listToBag fs)
                     end
                 end in
    go nil nil (Bag.bagToList fs).

Definition plusMinor : MinorEnv -> MinorEnv -> MinorEnv :=
  IntMap.unionWith Bag.unionBags.

Definition plusMajor : MajorEnv -> MajorEnv -> MajorEnv :=
  IntMap.unionWith plusMinor.

Definition plusFloats : FloatBinds -> FloatBinds -> FloatBinds :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FB t1 c1 l1, FB t2 c2 l2 =>
        FB (Bag.unionBags t1 t2) (Bag.unionBags c1 c2) (plusMajor l1 l2)
    end.

Axiom partitionByLevel : SetLevels.Level ->
                         FloatBinds -> (FloatBinds * Bag.Bag MkCore.FloatBind)%type.

Definition partitionAtJoinCeiling
   : FloatBinds -> (FloatBinds * Bag.Bag MkCore.FloatBind)%type :=
  fun '(FB tops ceils defs) => pair (FB tops Bag.emptyBag defs) ceils.

Definition install
   : Bag.Bag MkCore.FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun defn_groups expr => Bag.foldrBag MkCore.wrapFloat expr defn_groups.

Definition installUnderLambdas
   : Bag.Bag MkCore.FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun floats e =>
    let fix go arg_0__
              := match arg_0__ with
                 | Core.Lam b e => Core.Lam b (go e)
                 | e => install floats e
                 end in
    if Bag.isEmptyBag floats : bool then e else
    go e.

Definition get_stats : FloatStats -> (nat * nat * nat)%type :=
  fun '(FlS a b c) => pair (pair a b) c.

Axiom floatExpr : SetLevels.LevelledExpr ->
                  (FloatStats * FloatBinds * Core.CoreExpr)%type.

Definition floatBody
   : SetLevels.Level ->
     SetLevels.LevelledExpr -> (FloatStats * FloatBinds * Core.CoreExpr)%type :=
  fun lvl arg =>
    let 'pair (pair fsa floats) arg' := (floatExpr arg) in
    let 'pair floats' heres := (partitionByLevel lvl floats) in
    pair (pair fsa floats') (install heres arg').

Definition flattenMinor : MinorEnv -> Bag.Bag MkCore.FloatBind :=
  IntMap.foldr Bag.unionBags Bag.emptyBag.

Definition flattenMajor : MajorEnv -> Bag.Bag MkCore.FloatBind :=
  IntMap.foldr (Bag.unionBags GHC.Base.∘ flattenMinor) Bag.emptyBag.

Definition flattenTopFloats : FloatBinds -> Bag.Bag Core.CoreBind :=
  fun '(FB tops ceils defs) =>
    if andb Util.debugIsOn (negb (Bag.isEmptyBag (flattenMajor defs))) : bool
    then (GHC.Err.error Panic.someSDoc)
    else if andb Util.debugIsOn (negb (Bag.isEmptyBag ceils)) : bool
         then (GHC.Err.error Panic.someSDoc)
         else tops.

Definition emptyFloats : FloatBinds :=
  FB Bag.emptyBag Bag.emptyBag IntMap.empty.

Definition atJoinCeiling
   : (FloatStats * FloatBinds * Core.CoreExpr)%type ->
     (FloatStats * FloatBinds * Core.CoreExpr)%type :=
  fun '(pair (pair fs floats) expr') =>
    let 'pair floats' ceils := partitionAtJoinCeiling floats in
    pair (pair fs floats') (install ceils expr').

Definition floatRhs
   : Core.CoreBndr ->
     SetLevels.LevelledExpr -> (FloatStats * FloatBinds * Core.CoreExpr)%type :=
  fun bndr rhs =>
    let fix try_collect arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | num_3__, expr, acc =>
                     if num_3__ GHC.Base.== #0 : bool
                     then Some (pair (GHC.List.reverse acc) expr) else
                     match arg_0__, arg_1__, arg_2__ with
                     | n, Core.Lam b e, acc => try_collect (n GHC.Num.- #1) e (cons b acc)
                     | _, _, _ => None
                     end
                 end in
    let j_17__ := atJoinCeiling (floatExpr rhs) in
    match Id.isJoinId_maybe bndr with
    | Some join_arity =>
        match try_collect join_arity rhs nil with
        | Some (pair bndrs body) =>
            match bndrs with
            | nil => floatExpr rhs
            | cons (Core.TB _ lam_spec) _ =>
                let lvl := SetLevels.floatSpecLevel lam_spec in
                let 'pair (pair fs floats) body' := floatBody lvl body in
                pair (pair fs floats) (Core.mkLams (let cont_11__ arg_12__ :=
                                                      let 'Core.TB b _ := arg_12__ in
                                                      cons b nil in
                                                    Coq.Lists.List.flat_map cont_11__ bndrs) body')
            end
        | _ => j_17__
        end
    | _ => j_17__
    end.

Definition add_to_stats : FloatStats -> FloatBinds -> FloatStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FlS a b c, FB tops ceils others =>
        FlS (a GHC.Num.+ Bag.lengthBag tops) ((b GHC.Num.+ Bag.lengthBag ceils)
                                              GHC.Num.+
                                              Bag.lengthBag (flattenMajor others)) (c GHC.Num.+ #1)
    end.

Definition add_stats : FloatStats -> FloatStats -> FloatStats :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FlS a1 b1 c1, FlS a2 b2 c2 =>
        FlS (a1 GHC.Num.+ a2) (b1 GHC.Num.+ b2) (c1 GHC.Num.+ c2)
    end.

Definition floatList {a} {b}
   : (a -> (FloatStats * FloatBinds * b)%type) ->
     list a -> (FloatStats * FloatBinds * list b)%type :=
  fix floatList (arg_0__ : (a -> (FloatStats * FloatBinds * b)%type)) (arg_1__
                  : list a) : (FloatStats * FloatBinds * list b)%type
        := match arg_0__, arg_1__ with
           | _, nil => pair (pair zeroStats emptyFloats) nil
           | f, cons a as_ =>
               let 'pair (pair fs_a binds_a) b := f a in
               let 'pair (pair fs_as binds_as) bs := floatList f as_ in
               pair (pair (add_stats fs_a fs_as) (plusFloats binds_a binds_as)) (cons b bs)
           end.

Definition sum_stats : list FloatStats -> FloatStats :=
  fun xs => Data.Foldable.foldr add_stats zeroStats xs.

Definition addTopFloatPairs
   : Bag.Bag Core.CoreBind ->
     list (Core.Id * Core.CoreExpr)%type -> list (Core.Id * Core.CoreExpr)%type :=
  fun float_bag prs =>
    let add :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | Core.NonRec b r, prs => cons (pair b r) prs
        | Core.Rec prs1, prs2 => Coq.Init.Datatypes.app prs1 prs2
        end in
    Bag.foldrBag add prs float_bag.

Definition floatBind
   : SetLevels.LevelledBind ->
     (FloatStats * FloatBinds * list Core.CoreBind)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec (Core.TB var _) rhs =>
        let 'pair (pair fs rhs_floats) rhs' := (floatRhs var rhs) in
        let rhs'' :=
          if Id.isBottomingId var : bool
          then CoreArity.etaExpand (Id.idArity var) rhs' else
          rhs' in
        pair (pair fs rhs_floats) (cons (Core.NonRec var rhs'') nil)
    | Core.Rec pairs =>
        let do_pair
         : (SetLevels.LevelledBndr * SetLevels.LevelledExpr)%type ->
           (FloatStats * FloatBinds *
            (list (Core.Id * Core.CoreExpr)%type *
             list (Core.Id * Core.CoreExpr)%type)%type)%type :=
          fun '(pair (Core.TB name spec) rhs) =>
            let dest_lvl := SetLevels.floatSpecLevel spec in
            if SetLevels.isTopLvl dest_lvl : bool
            then let 'pair (pair fs rhs_floats) rhs' := (floatRhs name rhs) in
                 pair (pair fs emptyFloats) (pair nil (addTopFloatPairs (flattenTopFloats
                                                                         rhs_floats) (cons (pair name rhs') nil))) else
            let 'pair (pair fs rhs_floats) rhs' := (floatRhs name rhs) in
            let 'pair rhs_floats' heres := (partitionByLevel dest_lvl rhs_floats) in
            let 'pair (pair ul_pairs pairs) case_heres := (splitRecFloats heres) in
            let pairs' := cons (pair name (installUnderLambdas case_heres rhs')) pairs in
            pair (pair fs rhs_floats') (pair ul_pairs pairs') in
        let 'pair (pair fs rhs_floats) new_pairs := floatList do_pair pairs in
        let 'pair new_ul_pairss new_other_pairss := GHC.List.unzip new_pairs in
        let 'pair new_join_pairs new_l_pairs := Data.OldList.partition (Id.isJoinId
                                                                        GHC.Base.∘
                                                                        Data.Tuple.fst) (Data.Foldable.concat
                                                                                         new_other_pairss) in
        let new_rec_binds :=
          if Data.Foldable.null new_join_pairs : bool
          then cons (Core.Rec new_l_pairs) nil else
          if Data.Foldable.null new_l_pairs : bool
          then cons (Core.Rec new_join_pairs) nil else
          cons (Core.Rec new_l_pairs) (cons (Core.Rec new_join_pairs) nil) in
        let new_non_rec_binds :=
          let cont_30__ arg_31__ :=
            let 'pair b e := arg_31__ in
            cons (Core.NonRec b e) nil in
          Coq.Lists.List.flat_map cont_30__ (Data.Foldable.concat new_ul_pairss) in
        pair (pair fs rhs_floats) (Coq.Init.Datatypes.app new_non_rec_binds
                                                          new_rec_binds)
    end.

Definition floatTopBind
   : SetLevels.LevelledBind -> (FloatStats * Bag.Bag Core.CoreBind)%type :=
  fun bind =>
    let 'pair (pair fs floats) bind' := (floatBind bind) in
    let float_bag := flattenTopFloats floats in
    match bind' with
    | cons (Core.Rec prs) nil =>
        pair fs (Bag.unitBag (Core.Rec (addTopFloatPairs float_bag prs)))
    | cons (Core.NonRec b e) nil =>
        pair fs (Bag.snocBag float_bag (Core.NonRec b e))
    | _ => Panic.panicStr (GHC.Base.hs_string__ "floatTopBind") (Panic.someSDoc)
    end.

(* Skipping all instances of class `Outputable.Outputable', including
   `FloatOut.Outputable__FloatBinds' *)

(* External variables:
     None Some andb bool cons list nat negb nil op_zt__ pair tt Bag.Bag Bag.bagToList
     Bag.emptyBag Bag.foldrBag Bag.isEmptyBag Bag.lengthBag Bag.listToBag Bag.mapBag
     Bag.snocBag Bag.unionBags Bag.unitBag Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Core.AltCon Core.CoreBind Core.CoreBndr Core.CoreExpr
     Core.Id Core.Lam Core.NonRec Core.Rec Core.TB Core.Tickish Core.Var
     Core.isUnliftedType Core.mkLams CoreArity.etaExpand CoreUtils.exprIsHNF
     Data.Foldable.concat Data.Foldable.foldr Data.Foldable.null
     Data.OldList.partition Data.Tuple.fst GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Err.error GHC.List.reverse GHC.List.unzip GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idArity Id.idType Id.isBottomingId
     Id.isJoinId Id.isJoinId_maybe IntMap.IntMap IntMap.empty IntMap.foldr IntMap.map
     IntMap.singleton IntMap.unionWith MkCore.FloatBind MkCore.FloatCase
     MkCore.FloatLet MkCore.wrapFloat Panic.panicStr Panic.someSDoc
     SetLevels.JoinCeilLvl SetLevels.Level SetLevels.LevelledBind
     SetLevels.LevelledBndr SetLevels.LevelledExpr SetLevels.Mk_Level
     SetLevels.floatSpecLevel SetLevels.isTopLvl Util.debugIsOn Util.mapSnd
*)
