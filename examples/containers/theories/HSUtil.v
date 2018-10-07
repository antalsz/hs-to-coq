(******************************************************************************)
(** Imports **)

(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* SSReflect *)
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Permutations *)
Require Import Coq.Sorting.Permutation.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.List      Proofs.GHC.List.
Require Import GHC.Enum.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.

(* Other utility libraries *)
Require Import OrdTactic BitUtils.

(******************************************************************************)
(** Name dismabiguation -- MUST BE COPIED LOCALLY **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.
  (* Why do I need `reflect`?  What other `reflect` is in scope? *)

(******************************************************************************)
(** Notation disambiguation **)

Infix "=="  := op_zeze__ : bool_scope.
Infix "===" := eq_op (at level 70, no associativity) : bool_scope.

Notation "x == y :> A"  := (op_zeze__ (x : A) (y : A)) : bool_scope.
Notation "x === y :> A" := (eq_op     (x : A) (y : A)) (at level 70, y at next level, no associativity) : bool_scope.

(******************************************************************************)
(** Easier simplification **)

Global Arguments "$"          {_ _}     / _ _.
Global Arguments id           {_}       / _.
Global Arguments Datatypes.id {_}       / _.
Global Arguments "∘"          {_ _}     _ _ _ /.
Global Arguments flip         {_ _ _}   _ _ _ /.

(******************************************************************************)
(** bool **)

Theorem bool_eq_iff (b1 b2 : bool) : b1 = b2 <-> (b1 <-> b2).
Proof.
  move: b1 b2 => [] [] //.
  all: split; try solve[discriminate | case=> *; exfalso; auto].
Qed.  

(******************************************************************************)
(** EqTypes **)

(* EqType <-> EqExact translation *)

Theorem eqType_EqExact {A : eqType} `{EqExact A} (x y : A) : (x === y) = (x == y).
Proof. by case E: (x === y); case E': (x == y)=> //; move: E E' => /eqP ? /Eq_eq ?. Qed.

Theorem EqExact_eqType {A : eqType} `{EqExact A} (x y : A) : (x == y) = (x === y).
Proof. by rewrite eqType_EqExact. Qed.

(* EqExact decidability *)

Theorem EqExact_cases {A} `{EqExact A} (x y : A) :
  {x == y /\ x = y} + {x /= y /\ x <> y}.
Proof.
  rewrite Neq_inv; case CMP: (x == y).
  - by left; split=> //; apply/Eq_eq.
  - by right; split=> //; move=> /Eq_eq; rewrite CMP.
Qed.

Corollary EqExact_dec {A} `{EqExact A} (x y : A) :
  {x = y} + {x <> y}.
Proof. generalize (EqExact_cases x y); tauto. Qed.

(* Int is an EqType *)

Lemma Int_eqbP : Equality.axiom (_==_ : Int -> Int -> bool).
Proof. exact Eq_eq. Qed.

Canonical Int_eqMixin := EqMixin Int_eqbP.
Canonical Int_eqType := Eval hnf in EqType Int Int_eqMixin.

(******************************************************************************)
(** Ordering **)

Theorem Ord_le_ge {A} `{OrdLaws A} (x y : A) :
  (x <= y) = (y >= x).
Proof. order A. Qed.

Theorem Ord_lt_gt {A} `{OrdLaws A} (x y : A) :
  (x < y) = (y > x).
Proof. order A. Qed.

Theorem Ord_gt_lt {A} `{OrdLaws A} (x y : A) :
  (x > y) = (y < x).
Proof. order A. Qed.

Theorem Ord_lt_not_gt {A} `{OrdLaws A} (x y : A) :
  (x < y) -> ~~ (x > y).
Proof. order A. Qed.

Theorem Ord_antisym_le_le {A} `{OrdLaws A} (x y : A) :
  (x == y) = (x <= y) && (y <= x).
Proof. order A. Qed.

Theorem Ord_gt_not_lt {A} `{OrdLaws A} (x y : A) : (x > y) -> ~~ (x < y).
Proof. order A. Qed.

Theorem Ord_le_le_antisym {A} `{OrdLaws A} (x y : A) : (x == y) = (x <= y) && (y <= x).
Proof. order A. Qed.

Theorem Ord_le_ge_antisym {A} `{OrdLaws A} (x y : A) : (x == y) = (x <= y) && (x >= y).
Proof. order A. Qed.

Theorem Ord_ge_le_antisym {A} `{OrdLaws A} (x y : A) : (x == y) = (x >= y) && (x <= y).
Proof. order A. Qed.

Theorem Ord_ge_ge_antisym {A} `{OrdLaws A} (x y : A) : (x == y) = (x >= y) && (y >= x).
Proof. order A. Qed.

Theorem Ord_lt_lt_antisym {A} `{OrdLaws A} (x y : A) : (x /= y) = (x < y) || (y < x).
Proof. case: (Ord_total x y); order A. Qed.

Theorem Ord_lt_gt_antisym {A} `{OrdLaws A} (x y : A) : (x /= y) = (x < y) || (x > y).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_gt_lt_antisym {A} `{OrdLaws A} (x y : A) : (x /= y) = (x > y) || (x < y).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_gt_gt_antisym {A} `{OrdLaws A} (x y : A) : (x /= y) = (x > y) || (y > x).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_le_le_antisym' {A} `{OrdLaws A} (x y : A) : (x == y) = (y <= x) && (x <= y).
Proof. order A. Qed.

Theorem Ord_le_ge_antisym' {A} `{OrdLaws A} (x y : A) : (x == y) = (y <= x) && (y >= x).
Proof. order A. Qed.

Theorem Ord_ge_le_antisym' {A} `{OrdLaws A} (x y : A) : (x == y) = (y >= x) && (y <= x).
Proof. order A. Qed.

Theorem Ord_ge_ge_antisym' {A} `{OrdLaws A} (x y : A) : (x == y) = (y >= x) && (x >= y).
Proof. order A. Qed.

Theorem Ord_lt_lt_antisym' {A} `{OrdLaws A} (x y : A) : (x /= y) = (y < x) || (x < y).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_lt_gt_antisym' {A} `{OrdLaws A} (x y : A) : (x /= y) = (y < x) || (y > x).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_gt_lt_antisym' {A} `{OrdLaws A} (x y : A) : (x /= y) = (y > x) || (y < x).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

Theorem Ord_gt_gt_antisym' {A} `{OrdLaws A} (x y : A) : (x /= y) = (y > x) || (x > y).
Proof. rewrite Ord_lt_lt_antisym; order A. Qed.

(******************************************************************************)
(** List membership (`elem`, `In`, `\in`) **)

Theorem elemN {A} `{Eq_ A} (a : A) : elem a [::] = false.
Proof. done. Qed.

Theorem elemC {A} `{Eq_ A} (a x : A) (xs : list A) : elem a (x :: xs) = (a == x) || elem a xs.
Proof. done. Qed.

Theorem elem_in {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  elem a xs = (a \in xs).
Proof. by elim: xs => [|x xs IH] //=; rewrite inE -IH eqType_EqExact. Qed.

Theorem in_elem {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  a \in xs = elem a xs.
Proof. symmetry; apply elem_in. Qed.

Theorem elem_elem_by {A} `{EqLaws A} :
  elem =2 elem_by _==_.
Proof.
  move=> a; elim=> [|x xs IH] //=.
  by rewrite elemC IH Eq_sym.
Qed.

Theorem elemP {A} `{EqExact A} (x : A) (xs : list A) :
  reflect (In x xs) (elem x xs).
Proof.
  elim: xs => [|y ys IH] //=; first by constructor.
  rewrite elemC; case CMP: (x == y) => /=.
  - by constructor; left; apply/Eq_eq; rewrite Eq_sym.
  - apply/equivP; first exact IH.
    split; first by right.
    case=> // ?; subst.
    by move: CMP; rewrite Eq_refl.
Qed.

Theorem elem_byP {A} `{EqExact A} (xs : list A) (x : A) :
  reflect (In x xs) (elem_by _==_ x xs).
Proof.
  elim: xs => [|x' xs IH] /=; first by constructor.
  apply iff_reflect; split;
    try move=> /orP;
    move=> [? | ?];
    try apply/orP;
    solve [by left; apply/Eq_eq | by right; apply/IH].
Qed.

Theorem elem_app {A} `{Eq_ A} (a : A) (xs ys : list A) :
  elem a (xs ++ ys) = elem a xs || elem a ys.
Proof. by elim: xs => [|x xs] //=; rewrite !elemC -orbA => ->. Qed.

Theorem elem_by_resp_eq {A} `{EqLaws A} (xs : list A) (a b : A) :
  a == b ->
  elem_by _==_ a xs ->
  elem_by _==_ b xs.
Proof.
  move=> EQab; elim: xs => [|x xs IH] //=.
  case EQxa: (x == a) => //=; case EQxb: (x == b) => //=.
  have: (x == b) by eapply Eq_trans with a.
  by rewrite EQxb.
Qed.

Theorem elem_resp_eq {A} `{EqLaws A} (xs : list A) (a b : A) :
  a == b ->
  elem a xs ->
  elem b xs.
Proof. rewrite !elem_elem_by; apply elem_by_resp_eq. Qed.

Theorem elem_Permutation {A} `{Eq_ A} (xs ys : list A) :
  Permutation xs ys ->
  forall a, elem a xs = elem a ys.
Proof.
  elim=> {xs ys}
         [
         | x xs ys PERM IH
         | x y xs
         | xs ys zs PERM_xs_ys IH_xs_ys PERM_ys_zs IH_ys_zs ]
         //= a.
  - by rewrite !elemC IH.
  - by rewrite !elemC !orbA (orbC (_ == _) (_ == _)).
  - eapply etrans; [apply IH_xs_ys | apply IH_ys_zs].
Qed.

(* Non-Haskell theorems about In *)

Theorem InP {A : eqType} (x : A) (xs : list A) :
  reflect (In x xs) (x \in xs).
Proof.
  elim: xs => [|y ys IH] //=.
  - by rewrite seq.in_nil; constructor.
  - rewrite inE; case CMP: (x === y) => /=.
    + by constructor; left; apply/eqP; rewrite eq_sym.
    + apply/equivP; first exact IH.
      split; first by right.
      case=> // ?; subst.
      by move: CMP; rewrite eq_refl.
Qed.

Theorem In_split {A} (x : A) (xs : list A) :
  In x xs <->
  exists pre post, xs = pre ++ x :: post.
Proof.
  split.
  - elim: xs => [|x' xs IH] //= [? | IN]; first subst x'.
    + by exists [::], xs.
    + move: (IH IN) => [pre [post ->]].
      by exists (x' :: pre), post.
  - move=> [pre [post ->]].
    by elim: pre => [|p pre IH] //=; [left | right].
Qed.

(******************************************************************************)
(** Foldable and lists **)

Theorem Foldable_list_all {A} :
  all =2 @GHC.List.all A.
Proof.
  rewrite /all /compose /foldMap /Foldable__list /=
          /Data.Foldable.Foldable__list_foldMap /Data.Foldable.Foldable__list_foldr /=.
  move=> p; elim=> [|x xs IH] //=.
  rewrite -IH.
  rewrite {1}/mappend /Data.SemigroupInternal.Monoid__All /=.
  case: (GHC.Base.foldr _ _ _) => //=.
Qed.

Theorem Foldable_and_all {F} `{Foldable F} :
  and (t := F) =1 all id.
Proof. done. Qed.

Lemma Foldable_all_forallb {A} :
  all =2 forallb (A := A).
Proof. by move=> p xs; rewrite Foldable_list_all; elim: xs => //= x xs <-. Qed.

Theorem Foldable_all_ssreflect {A} :
  all =2 seq.all (T := A).
Proof. by move=> *; rewrite Foldable_all_forallb. Qed.

Theorem Foldable_list_any {A} :
  Data.Foldable.any =2 @GHC.List.any A.
Proof.
  rewrite /Data.Foldable.any /compose /foldMap /Foldable__list /=
          /Data.Foldable.Foldable__list_foldMap /Data.Foldable.Foldable__list_foldr /=.
  move=> p; elim=> [|x xs IH] //=.
  rewrite -IH.
  rewrite {1}/mappend /Data.SemigroupInternal.Monoid__Any /=.
  case: (GHC.Base.foldr _ _ _) => //=.
Qed.

Theorem Foldable_any_or {F} `{Foldable F} :
  or (t := F) =1 any id.
Proof. done. Qed.

Theorem Foldable_any_existsb {A} :
  any =2 existsb (A := A).
Proof. by move=> p xs; rewrite Foldable_list_any; elim: xs => //= x xs <-. Qed.

Theorem Foldable_any_ssreflect {A} :
  any =2 seq.has (T := A).
Proof. by move=> *; rewrite Foldable_any_existsb. Qed.

Theorem Foldable_list_null {A} :
  null =1 GHC.List.null (a := A). 
Proof. done. Qed.

Theorem List_null_none {A} (xs : list A) :
  GHC.List.null xs <-> forall x, ~ In x xs.
Proof.
  case: xs => [|x xs] /=; split; try by intuition.
  by move=> /(_ x (or_introl erefl)).
Qed.

Theorem List_null_no_elems {A} `{EqLaws A} (xs : list A) :
  GHC.List.null xs <-> forall x, ~~ elem x xs.
Proof.
  case: xs => [|x xs] /=; split; try by intuition.
  by move=> /(_ x); rewrite elemC Eq_refl.
Qed.

Theorem null_list_none {A} (xs : list A) :
  null xs <-> forall x, ~ In x xs.
Proof. apply List_null_none. Qed.

Theorem null_list_no_elems {A} `{EqLaws A} (xs : list A) :
  null xs <-> forall x, ~~ elem x xs.
Proof. apply List_null_no_elems. Qed.

Theorem hs_coq_reverse_rev {A} :
  reverse =1 rev (A := A).
Proof.
  rewrite /reverse => xs.
  replace (rev xs) with (rev xs ++ [::]) by rewrite app_nil_r //.
  elim: xs [::] => [|x xs IH] //= acc.
  by rewrite IH -app_assoc.
Qed.

(******************************************************************************)
(** Element-based list function semantics **)

(* reverse and rev *)

Theorem rev_elem {A} `{EqLaws A} (xs : list A) (a : A) :
  elem a (rev xs) = elem a xs.
Proof.
  elim: xs => [|x xs IH] //=.
  by rewrite elem_app !elemC elemN orbF IH orbC.
Qed.

Theorem reverse_elem {A} `{EqLaws A} (xs : list A) (a : A) :
  elem a (reverse xs) = elem a xs.
Proof. rewrite hs_coq_reverse_rev; apply rev_elem. Qed.

(* nub *)

Theorem nub_elem {A} `{EqLaws A} (xs : list A) (a : A) :
  elem a (nub xs) = elem a xs.
Proof.
  rewrite /nub /nubBy !elem_elem_by;
    match goal with |- context[?F xs [::]] => set nubBy' := F end.
  replace (elem_by _==_ a xs) with (elem_by _==_ a xs && ~~ elem_by _==_ a [::])
    by rewrite /= andbT //.
  move: [::].
  elim: xs => [|x xs IH] //= acc.
  case ELEM_x: (elem_by _==_ x acc) => /=; last rename ELEM_x into NELEM_x.
  - rewrite IH.
    case NELEM_a: (elem_by _==_ a acc) => /=; rewrite ?andbT ?andbF //.
    case EQxa: (x == a) => //=.
    by rewrite (elem_by_resp_eq _ _ _ EQxa ELEM_x) in NELEM_a.
  - rewrite IH /= negb_orb orb_andr.
    case EQxa: (x == a) => //=.
    symmetry; apply/negP => ELEM_a.
    by rewrite Eq_sym in EQxa; rewrite (elem_by_resp_eq _ _ _ EQxa ELEM_a) in NELEM_x.
Qed.

(* delete and deleteBy *)

Theorem deleteBy_only_elem {A} `{Eq_ A} (xs : list A) (a b : A) :
  elem b (deleteBy _==_ a xs) -> elem b xs.
Proof.
  elim: xs => [|x xs IH] //=.
  rewrite elemC; case NEQbx: (b == x) => //=.
  case NEQax: (a == x) => //=.
  rewrite elemC NEQbx orFb; apply IH.
Qed.

Theorem delete_only_elem {A} `{Eq_ A} (xs : list A) (a b : A) :
  elem b (delete a xs) -> elem b xs.
Proof. apply deleteBy_only_elem. Qed.

Theorem deleteBy_NoDup_elem {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a b, elem b (deleteBy _==_ a xs) = elem b xs && (a /= b).
Proof.
  elim: xs => [|x xs IH] //= ND' a b.
  inversion ND' as [|x' xs' NIN ND]; subst x' xs'.
  rewrite elemC; case EQbx: (b == x) => //=; last rename EQbx into NEQbx.
  - move/Eq_eq in EQbx; subst x.
    rewrite Neq_inv; case EQab: (a == b) => //=; last rename EQab into NEQab.
    + by apply/elemP.
    + by rewrite elemC Eq_refl orTb.
  - case EQax: (a == x) => //=; last rename EQax into NEQax.
    + have: (a /= b). {
        rewrite Neq_inv Eq_sym; apply/negP => EQba.
        by rewrite (Eq_trans _ _ _ EQba EQax) in NEQbx.
      }
      by move=> ->; rewrite andbT.
    + by rewrite elemC NEQbx orFb; apply IH.
Qed.

Theorem delete_NoDup_elem {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a b, elem b (delete a xs) = elem b xs && (a /= b).
Proof. apply deleteBy_NoDup_elem. Qed.

Theorem deleteBy_NoDup_removes {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a, ~~ elem a (deleteBy _==_ a xs).
Proof. by move=> ND a; rewrite deleteBy_NoDup_elem // Neq_irrefl andbF. Qed.

Theorem delete_NoDup_removes {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a, ~~ elem a (delete a xs).
Proof. apply deleteBy_NoDup_removes. Qed.

Theorem deleteBy_preserves_NoDup {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a, NoDup (deleteBy _==_ a xs).
Proof.
  elim: xs => [|x xs IH] //= ND' a.
  inversion ND' as [|x' xs' NIN ND]; subst x' xs'.
  case NEQax: (a == x) => //.
  constructor; last by apply IH.
  apply/elemP/negP => ELEM.
  by apply deleteBy_only_elem in ELEM; move/elemP in ELEM.
Qed.

Theorem delete_preserves_NoDup {A} `{EqExact A} (xs : list A) :
  NoDup xs -> forall a, NoDup (delete a xs).
Proof. apply deleteBy_preserves_NoDup. Qed.

(* Filter *)

Theorem filter_In {A} (p : A -> bool) (xs : list A) :
  forall a, In a (filter p xs) <-> In a xs /\ p a.
Proof.
  move=> a; elim: xs => [|x xs IH] //=; first tauto.
  case Hpx: (p x) => //=; rewrite IH; intuition congruence.
Qed.

Theorem filter_elem {A} `{EqExact A} (p : A -> bool) (xs : list A) :
  forall a, elem a (filter p xs) = elem a xs && p a.
Proof.
  move=> a; apply/bool_eq_iff.
  rewrite -(rwP andP) -!(rwP (elemP _ _)); apply filter_In.
Qed.

Theorem filter_preserves_NoDup {A} `{EqExact A} (p : A -> bool) (xs : list A) :
  NoDup xs -> NoDup (filter p xs).
Proof.
  elim: xs => [|x xs IH] //= ND'.
  inversion ND' as [|x' xs' NIN ND]; subst x' xs'.
  case: (p x); first constructor; try by apply IH.
  rewrite filter_In; contradict NIN; tauto.
Qed.

(* List intersection (intersect) *)

Theorem intersectBy_flat_map {A} (eq : A -> A -> bool) (xs ys : list A) :
  intersectBy eq xs ys = flat_map (fun x => if GHC.List.any (eq x) ys then [:: x] else [::]) xs.
Proof.
  move: xs ys => [|x xs] [|y ys] //=.
  elim: xs => [|x' xs IH] //=.
Qed.

Theorem intersectBy_filter {A} (eq : A -> A -> bool) (xs ys : list A) :
  intersectBy eq xs ys = filter (fun x => any (eq x) ys) xs.
Proof.
  rewrite intersectBy_flat_map.
  elim: xs => [|x xs IH] => //=.
  rewrite -Foldable_list_any IH.
  by case: (any _ _).
Qed.

Theorem intersectBy_elem {A} `{EqExact A} (xs ys : list A) (a : A) :
  elem a (intersectBy _==_ xs ys) = elem a xs && elem a ys.
Proof.
  rewrite intersectBy_filter filter_elem Foldable_list_any; f_equal.
  elim: ys => [|y ys IH] //=.
  by rewrite IH elemC.
Qed.

Theorem intersect_elem {A} `{EqExact A} (xs ys : list A) (a : A) :
  elem a (intersect xs ys) = elem a xs && elem a ys.
Proof. apply intersectBy_elem. Qed.

Theorem intersectBy_preserves_NoDup {A} `{EqExact A} (xs ys : list A) :
  NoDup xs -> NoDup (intersectBy _==_ xs ys).
Proof. rewrite intersectBy_filter; apply filter_preserves_NoDup. Qed.

Theorem intersect_preserves_NoDup {A} `{EqExact A} (xs ys : list A) :
  NoDup xs -> NoDup (intersect xs ys).
Proof. rewrite /intersect intersectBy_filter; apply filter_preserves_NoDup. Qed.

(* List difference (\\) *)

Theorem diff_NoDup_elem {A} `{EqExact A} (xs ys : list A) :
  NoDup xs -> forall a, elem a (xs \\ ys) = elem a xs && ~~ elem a ys.
Proof.
  unfold "\\"; elim: ys xs => [|y ys IH] //= xs ND a; first by rewrite andbT.
  rewrite elemC negb_orb IH; last by apply delete_preserves_NoDup.
  by rewrite andbA delete_NoDup_elem // Neq_inv Eq_sym.
Qed.

Theorem diff_only_elem {A} `{Eq_ A} (xs ys : list A) (a : A) :
  elem a (xs \\ ys) -> elem a xs.
Proof. by unfold "\\"; elim: ys xs => [|y ys IH] //= xs /IH; apply delete_only_elem. Qed.

Theorem diff_preserves_NoDup {A} `{EqExact A} (xs ys : list A) :
  NoDup xs -> NoDup (xs \\ ys).
Proof.
  unfold "\\"; elim: ys xs => [|y ys IH] //= xs ND.
  by apply IH, delete_preserves_NoDup.
Qed.

(******************************************************************************)
(** Bit manipulation **)

Theorem Z_eq_testbits_pos (m n : Z) :
  m = n <-> (forall ix, (0 <= ix)%Z -> Z.testbit m ix = Z.testbit n ix).
Proof.
  split => [? | bits]; first by subst.
  apply Z.bits_inj_iff => ix.
  case: (Z_le_dec 0 ix) => [POS | NEG]; first by apply bits.
  rewrite !Z.testbit_neg_r //; omega.
Qed.

Theorem Z_negb_testbit_iff (m n : Z) :
  ~~ Z.testbit m n <-> (Z.land m (Z.shiftl 1 n) = 0)%Z.
Proof.
  rewrite Z_eq_testbits_pos; split => [nbit ix POS_ix | bits].
  - rewrite Z.bits_0 Z.land_spec Z.shiftl_spec // testbit_1.
    case SUB: (ix - n =? 0)%Z.
    + by move: SUB => /Z.eqb_spec/Z.sub_move_0_r ->; rewrite (negbTE nbit) andFb.
    + by rewrite andbF.
  - case: (Z_le_dec 0 n) => [POS | NEG].
    + move: bits => /(_ n POS).
      by rewrite Z.bits_0 Z.land_spec Z.shiftl_spec // testbit_1 Z.sub_diag /= andbT => ->.
    + rewrite Z.testbit_neg_r //; omega.
Qed.

Theorem Z_negb_testbit_eq (m n : Z) :
  ~~ Z.testbit m n = (Z.land m (Z.shiftl 1 n) =? 0)%Z.
Proof.
  apply/bool_eq_iff; rewrite Z_negb_testbit_iff; apply (rwP (Z.eqb_spec _ _)).
Qed.

Theorem Z_testbit_iff (m n : Z) :
  Z.testbit m n <-> (Z.land m (Z.shiftl 1 n) <> 0)%Z.
Proof.
  by rewrite -Z_negb_testbit_iff; split => [-> | /negP]; last rewrite negbK.
Qed.

Theorem Z_testbit_eq (m n : Z) :
  Z.testbit m n = ~~ (Z.land m (Z.shiftl 1 n) =? 0)%Z.
Proof.
  by apply/bool_eq_iff; rewrite Z_testbit_iff (rwP (Z.eqb_spec _ _)) (rwP negP).
Qed.
