From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import GHC.Base.     Import GHC.Base.Notations.
Require Import Data.Functor. Import Data.Functor.Notations.
Require Import Data.Maybe.

Require Import TrieMap.

Require UniqDFM.
Require Core.

(** * Don't unfold TrieMap operations. *)

Arguments Key      : simpl never.
Arguments alterTM  : simpl never.
Arguments emptyTM  : simpl never.
Arguments foldTM   : simpl never.
Arguments lookupTM : simpl never.
Arguments mapTM    : simpl never.
Arguments insertTM : simpl never.
Arguments deleteTM : simpl never.

(** * [TrieMapLaws] *)

Class TrieMapLaws (m : Type -> Type) `{TM : TrieMap m} : Prop :=
  { tml_empty {a} k :
      lookupTM k emptyTM = None :> option a
  
  ; tml_alter_here {a} k (f : XT a) tm :
      lookupTM k (alterTM k f tm) = f (lookupTM k tm)
  
  ; tml_alter_there {a} k (f : XT a) tm k' :
      k <> k' -> lookupTM k' (alterTM k f tm) = lookupTM k' tm
  
  ; tml_map {a b} (f : a -> b) k tm :
      (f <$> lookupTM k tm) = lookupTM k (mapTM f tm)

  ; tml_fold_in {a} (tm : m a) v :
      In v (foldTM cons tm nil) <-> exists k, lookupTM k tm = Some v
  
  ; tml_fold_via_list {a b} (f : a -> b -> b) tm z :
      foldTM f tm z = foldr f z (foldTM cons tm nil) }.

Theorem tml_insert_here `{TML : TrieMapLaws m} {a} k v (tm : m a) :
  lookupTM k (insertTM k v tm) = Some v.
Proof. by rewrite /insertTM tml_alter_here. Qed.

Theorem tml_insert_there `{TML : TrieMapLaws m} {a} k v (tm : m a) k' :
  k <> k' ->
  lookupTM k' (insertTM k v tm) = lookupTM k' tm.
Proof. by move=> NEQ; rewrite /insertTM tml_alter_there. Qed.

Theorem tml_delete_here `{TML : TrieMapLaws m} {a} k (tm : m a) :
  lookupTM k (deleteTM k tm) = None.
Proof. by rewrite /deleteTM tml_alter_here. Qed.

Theorem tml_delete_there `{TML : TrieMapLaws m} {a} k (tm : m a) k' :
  k <> k' ->
  lookupTM k' (deleteTM k tm) = lookupTM k' tm.
Proof. by move=> NEQ; rewrite /deleteTM tml_alter_there. Qed.

Instance TrieMapLaws__Map          {k} `{GHC.Base.Ord k}                        : TrieMapLaws (Data.Map.Internal.Map k).   Admitted.
Instance TrieMapLaws__IntMap                                                    : TrieMapLaws IntMap.IntMap.               Admitted.
Instance TrieMapLaws__MaybeMap     {m} `{TrieMapLaws m}                         : TrieMapLaws (MaybeMap m).                Admitted.
Instance TrieMapLaws__ListMap      {m} `{TrieMapLaws m}                         : TrieMapLaws (ListMap m).                 Admitted.
Instance TrieMapLaws__UniqDFM                                                   : TrieMapLaws UniqDFM.UniqDFM.             Admitted.

Instance TrieMapLaws__TypeMapX                                                  : TrieMapLaws TypeMapX.                    Admitted.
Instance TrieMapLaws__CoreMapX                                                  : TrieMapLaws CoreMapX.                    Admitted.
Instance TrieMapLaws__CoercionMapX                                              : TrieMapLaws CoercionMapX.                Admitted.

Instance TrieMapLaws__GenMap       {m} `{TrieMapLaws m} `{GHC.Base.Eq_ (Key m)} : TrieMapLaws (GenMap m).                  Admitted.

Instance TrieMapLaws__TypeMap                                                   : TrieMapLaws TypeMap.                     Admitted.
Instance TrieMapLaws__CoreMap                                                   : TrieMapLaws CoreMap.                     Admitted.
Instance TrieMapLaws__CoercionMap                                               : TrieMapLaws CoercionMap.                 Admitted.
Instance TrieMapLaws__AltMap                                                    : TrieMapLaws AltMap.                      Admitted.

Instance TrieMapLaws__VarMap                                                    : TrieMapLaws VarMap.                      Admitted.
Instance TrieMapLaws__LooseTypeMap                                              : TrieMapLaws LooseTypeMap.                Admitted.

Instance TrieMapLaws__CoreMapG                                                  : TrieMapLaws CoreMapG                     := TrieMapLaws__GenMap.
Instance TrieMapLaws__TypeMapG                                                  : TrieMapLaws TypeMapG                     := TrieMapLaws__GenMap.
Instance TrieMapLaws__CoercionMapG                                              : TrieMapLaws CoercionMapG                 := TrieMapLaws__GenMap.

Instance TrieMapLaws__TyLitMap                                                  : TrieMapLaws TyLitMap.                    Admitted.


(** * [TrieMap_AllKV] *)

Definition TrieMap_AllKV `{TrieMap M} {A} P (m : M A) : Prop :=
  forall k, maybe True (P k) (lookupTM k m).

Theorem TrieMap_AllKV_nil `{TrieMapLaws M} {A} (P : Key M -> A -> Prop) : TrieMap_AllKV P emptyTM.
Proof. by red=> k; rewrite tml_empty. Qed.

Theorem TrieMap_AllKV_lookup_Some `{TrieMap M} {A} P (m : M A) k v :
  TrieMap_AllKV P m ->
  lookupTM k m = Some v ->
  P k v.
Proof.
  rewrite /TrieMap_AllKV => /(_ k) ALL SOME.
  by move: ALL; rewrite SOME.
Qed.

Theorem TrieMap_AllKV_alter_lookup `{TrieMapLaws M} {A} (P : Key M -> A -> Prop) k f m :
  comparable (Key M) ->
  (forall k, maybe True (P k) (lookupTM k m) -> maybe True (P k) (f (lookupTM k m))) ->
  TrieMap_AllKV P m ->
  TrieMap_AllKV P (alterTM k f m).
Proof.
  move=> dec preservation All_m.
  red=> k'; case: (dec k k') => [<-{k'}|NEQ].
  - rewrite tml_alter_here /=.
    by apply preservation.
  - by rewrite tml_alter_there.
Qed.

Theorem TrieMap_AllKV_alter `{TrieMapLaws M} {A} (P : Key M -> A -> Prop) k f m :
  comparable (Key M) ->
  (forall k mv, maybe True (P k) mv -> maybe True (P k) (f mv)) ->
  TrieMap_AllKV P m ->
  TrieMap_AllKV P (alterTM k f m).
Proof.
  move=> dec preservation.
  by apply TrieMap_AllKV_alter_lookup => // k' /(preservation _).
Qed.

Theorem TrieMap_AllKV_map `{TrieMapLaws M} {A B} P (f : A -> B) (m : M A) :
  TrieMap_AllKV P (mapTM f m) <-> TrieMap_AllKV (fun k => P k ∘ f) m.
Proof.
  rewrite /TrieMap_AllKV; split.
  all: move=> Hyp k; move: {Hyp} (Hyp k).
  all: rewrite -tml_map.
  all: by case: (lookupTM k m).
Qed.

Theorem TrieMap_AllKV_insert `{TrieMapLaws M} {A} (P : Key M -> A -> Prop) k v m :
  comparable (Key M) ->
  P k v ->
  TrieMap_AllKV P m ->
  TrieMap_AllKV P (insertTM k v m).
Proof.
  move=> dec P_k_v All_m k'.
  case: (dec k k') => [<-{k'}|NEQ].
  - by rewrite tml_insert_here.
  - by rewrite tml_insert_there.
Qed.

Theorem TrieMap_AllKV_delete `{TrieMapLaws M} {A} P k (m : M A) :
  comparable (Key M) ->
  TrieMap_AllKV P m ->
  TrieMap_AllKV P (deleteTM k m).
Proof. by move=> dec; apply TrieMap_AllKV_alter. Qed.

Theorem TrieMap_AllKV_inv `{TrieMapLaws M} {A} P k v (m : M A) :
  TrieMap_AllKV P (insertTM k v m) -> P k v.
Proof. by move=> /(_ k); rewrite tml_insert_here. Qed.

Theorem TrieMap_AllKV_insert_iff `{TrieMapLaws M} {A} P k v (m : M A) :
  comparable (Key M) ->
  TrieMap_AllKV P (insertTM k v m) <-> P k v /\ TrieMap_AllKV P (deleteTM k m).
Proof.
  move=> dec.
  split.
  - move=> All_m; split; first by apply TrieMap_AllKV_inv in All_m.
    move=> k'; move: (All_m k').
    case: (dec k k') => [<-{k'}|NEQ].
    + by rewrite tml_delete_here.
    + by rewrite tml_insert_there // tml_delete_there //.
  - move=> [Pv All_del] k'; move: (All_del k').
    case: (dec k k') => [<-{k'}|NEQ].
    + by rewrite tml_insert_here.
    + by rewrite tml_delete_there // tml_insert_there //.
Qed.
  
Theorem TrieMap_AllKV_impl_lookup `{TrieMapLaws M} {A} (P Q : Key M -> A -> Prop) m :
  (forall k v, lookupTM k m = Some v -> P k v -> Q k v) ->
  TrieMap_AllKV P m -> TrieMap_AllKV Q m.
Proof.
  move=> impl All_P k.
  move: (All_P k).
  case def_v: (lookupTM k m) => [v|] //=.
  by apply impl.
Qed.

Theorem TrieMap_AllKV_impl `{TrieMapLaws M} {A} (P Q : Key M -> A -> Prop) :
  (forall k v, P k v -> Q k v) ->
  forall m, TrieMap_AllKV P m -> TrieMap_AllKV Q m.
Proof.
  move=> impl m; apply TrieMap_AllKV_impl_lookup.
  by move=> *; apply impl.
Qed.

(** * [TrieMap_All] *)

Definition TrieMap_All `{TrieMap M} {A} P (m : M A) : Prop :=
  forall k, maybe True P (lookupTM k m).

Theorem TrieMap_All_AllKV `{TrieMap M} {A} P (m : M A) :
  TrieMap_All P m <-> TrieMap_AllKV (const P) m.
Proof. reflexivity. Qed.

Theorem TrieMap_All_nil `{TrieMapLaws M} {A} (P : A -> Prop) : TrieMap_All P emptyTM.
Proof. apply TrieMap_AllKV_nil. Qed.

Theorem TrieMap_All_lookup_Some `{TrieMap M} {A} P (m : M A) k v :
  TrieMap_All P m ->
  lookupTM k m = Some v ->
  P v.
Proof. apply TrieMap_AllKV_lookup_Some. Qed.

Theorem TrieMap_All_alter_lookup `{TrieMapLaws M} {A} (P : A -> Prop) k f (m : M A) :
  comparable (Key M) ->
  (forall k, maybe True P (lookupTM k m) -> maybe True P (f (lookupTM k m))) ->
  TrieMap_All P m ->
  TrieMap_All P (alterTM k f m).
Proof. apply TrieMap_AllKV_alter_lookup. Qed.

Theorem TrieMap_All_alter `{TrieMapLaws M} {A} (P : A -> Prop) k f (m : M A) :
  comparable (Key M) ->
  (forall mv, maybe True P mv -> maybe True P (f mv)) ->
  TrieMap_All P m ->
  TrieMap_All P (alterTM k f m).
Proof. by move=> *; apply TrieMap_AllKV_alter. Qed.

Theorem TrieMap_All_map `{TrieMapLaws M} {A B} P (f : A -> B) (m : M A) :
  TrieMap_All P (mapTM f m) <-> TrieMap_All (P ∘ f) m.
Proof. apply TrieMap_AllKV_map. Qed.

Theorem TrieMap_All_fold_cons_nil `{TrieMapLaws M} {A} P (m : M A) :
  TrieMap_All P m <-> Forall P (foldTM cons m nil).
Proof.
  rewrite Forall_forall; split.
  - move=> All_m v.
    rewrite tml_fold_in; move=> [k' def_k].
    eapply TrieMap_All_lookup_Some; eassumption.
  - move=> All_fold k.
    case def_v: (lookupTM k m) => [v|] //=.
    apply All_fold; rewrite tml_fold_in.
    by exists k.
Qed.

Theorem TrieMap_All_insert `{TrieMapLaws M} {A} (P : A -> Prop) k v (m : M A) :
  comparable (Key M) ->
  P v ->
  TrieMap_All P m ->
  TrieMap_All P (insertTM k v m).
Proof. by move=> *; apply TrieMap_AllKV_insert. Qed.

Theorem TrieMap_All_delete `{TrieMapLaws M} {A} P k (m : M A) :
  comparable (Key M) ->
  TrieMap_All P m ->
  TrieMap_All P (deleteTM k m).
Proof. apply TrieMap_AllKV_delete. Qed.

Theorem TrieMap_All_inv `{TrieMapLaws M} {A} P k v (m : M A) : 
  TrieMap_All P (insertTM k v m) -> P v.
Proof. apply TrieMap_AllKV_inv. Qed.

Theorem TrieMap_All_insert_iff `{TrieMapLaws M} {A} P k v (m : M A) :
  comparable (Key M) ->
  TrieMap_All P (insertTM k v m) <-> P v /\ TrieMap_All P (deleteTM k m).
Proof. apply TrieMap_AllKV_insert_iff. Qed.
  
Theorem TrieMap_All_impl_lookup `{TrieMapLaws M} {A} (P Q : A -> Prop) (m : M A) :
  (forall k v, lookupTM k m = Some v -> P v -> Q v) ->
  TrieMap_All P m -> TrieMap_All Q m.
Proof. apply TrieMap_AllKV_impl_lookup. Qed.

Theorem TrieMap_All_impl_lookup_exists `{TrieMapLaws M} {A} (P Q : A -> Prop) (m : M A) :
  (forall v, (exists k, lookupTM k m = Some v) -> P v -> Q v) ->
  TrieMap_All P m -> TrieMap_All Q m.
Proof.
  move=> impl. apply TrieMap_All_impl_lookup => k v def_v.
  by apply impl; exists k.
Qed.

Theorem TrieMap_All_impl `{TrieMapLaws M} {A} (P Q : A -> Prop) :
  (forall v, P v -> Q v) ->
  forall m : M A, TrieMap_All P m -> TrieMap_All Q m.
Proof. by move=> *; apply (TrieMap_AllKV_impl (const P) (const Q)). Qed.

(** * hs_simpl *)

Lemma Key_CoreMap : Key CoreMap = Core.Expr Core.Var.
Proof. done. Qed.
Hint Rewrite Key_CoreMap : hs_simpl.
