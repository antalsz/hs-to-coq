Lemma ptrEq_spec :
  {ptrEq : forall a, a -> a -> bool | forall a (x:a)(y:a), ptrEq _ x y = true -> x = y}.
Proof.  apply (exist _ (fun _ _ _ => false)). intros; congruence. Qed.

Definition ptrEq : forall {a}, a -> a -> bool := proj1_sig ptrEq_spec.
Lemma  ptrEq_eq : forall {a} (x:a)(y:a), ptrEq x y = true -> x = y.
Proof. exact (proj2_sig ptrEq_spec). Qed.

Lemma hetPtrEq_spec :
  {hetPtrEq : forall a b, a -> b -> bool
  | forall a b (x:a)(y:a), hetPtrEq _ _ x y = true -> a = b /\ x = y}.
Proof.  apply (exist _ (fun _ _ _ _ => false)). intros; congruence. Qed.

Definition hetPtrEq : forall {a b}, a -> b -> bool := proj1_sig hetPtrEq_spec.
Lemma  hetPtrEq_eq :forall {a b} (x:a)(y:a), hetPtrEq x y = true -> a = b /\ x = y.
Proof. exact (proj2_sig hetPtrEq_spec). Qed.
