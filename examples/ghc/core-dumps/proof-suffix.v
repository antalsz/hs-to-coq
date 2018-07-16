Require Import Proofs.ScopeInvariant.
Opaque N.to_nat N.of_nat.

Goal WellScopedProgram program.
repeat (match goal with
  | |- WellScopedProgram _ => constructor
  | |- Forall.Forall' _ _ => constructor
  | |- List.Forall _ _ => constructor
  | |- WellScoped (Mk_Var _) _ => cbv beta fix match delta [WellScoped]
  | |- WellScoped (App _ _) _ => constructor
  | |- WellScoped (Lit _) _ => constructor
  | |- WellScoped (Lam _ _) _ => constructor
  | |- WellScoped (Case _ _ _ _) _ => constructor
  | |- GoodLocalVar _ => constructor
  | |- GoodVar _ => constructor
  | |- _ /\ _ => constructor
end; unfold id, snd, pair3).
all: try timeout 1 reflexivity.
all: try match goal with |- List.NoDup _ =>
   repeat (cbv; rewrite ?Nnat.N2Nat.id; constructor);
   rewrite ?IntSetProofs.In_cons_iff; intuition congruence end.
all: try timeout 1 (repeat (cbv; rewrite ?Nnat.N2Nat.id; constructor)).
all : try
  (unfold WellScopedVar, isLocalVar, isGlobalId, negb, program;
   simpl; rewrite ?Nnat.N2Nat.id;
   cbv; constructor).
Qed.