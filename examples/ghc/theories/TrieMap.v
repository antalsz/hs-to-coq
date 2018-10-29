Require Import GHC.Base.     Import GHC.Base.Notations.
Require Import Data.Functor. Import Data.Functor.Notations.

Require Import TrieMap.

Require UniqDFM.
Require Data.IntMap.Internal.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

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

Instance TrieMapLaws__UniqDFM                                      : TrieMapLaws UniqDFM.UniqDFM.             Admitted.
Instance TrieMapLaws__IntMap                                       : TrieMapLaws Data.IntMap.Internal.IntMap. Admitted.
Instance TrieMapLaws__VarMap                                       : TrieMapLaws VarMap.                      Admitted.
Instance TrieMapLaws__TyLitMap                                     : TrieMapLaws TyLitMap.                    Admitted.
Instance TrieMapLaws__LooseTypeMap                                 : TrieMapLaws LooseTypeMap.                Admitted.
Instance TrieMapLaws__TypeMapX                                     : TrieMapLaws TypeMapX.                    Admitted.
Instance TrieMapLaws__CoercionMapX                                 : TrieMapLaws CoercionMapX.                Admitted.
Instance TrieMapLaws__CoercionMap                                  : TrieMapLaws CoercionMap.                 Admitted.
Instance TrieMapLaws__AltMap                                       : TrieMapLaws AltMap.                      Admitted.
Instance TrieMapLaws__TypeMap                                      : TrieMapLaws TypeMap.                     Admitted.
Instance TrieMapLaws__CoreMap                                      : TrieMapLaws CoreMap.                     Admitted.
Instance TrieMapLaws__CoreMapX                                     : TrieMapLaws CoreMapX.                    Admitted.
Instance TrieMapLaws__ListMap      `{TrieMapLaws m}                : TrieMapLaws (ListMap m).                 Admitted.
Instance TrieMapLaws__MaybeMap     `{TrieMapLaws m}                : TrieMapLaws (MaybeMap m).                Admitted.
Instance TrieMapLaws__GenMap       `{TrieMapLaws m} `{Eq_ (Key m)} : TrieMapLaws (GenMap m).                  Admitted.
