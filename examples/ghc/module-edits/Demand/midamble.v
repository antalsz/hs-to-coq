(* DEMAND midamble file. Termination defs and tactics . *)

Require Import GHC.Nat.
Require Import Omega.

Ltac solve_not_zero_N := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] => 
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    omega.
Ltac simpl_not_zero := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
  unfold GHC.Base.op_zeze__ in H;
    unfold Eq_nat in H;
    simpl in H;
  apply Nat.eqb_neq in H end.
Ltac solve_error_sub :=
  unfold error_sub;
  let Hltb := fresh in
  let HeqHltb := fresh in
  match goal with 
    [ |- context[ Nat.ltb ?x (Pos.to_nat 1) ] ] =>
    remember (Nat.ltb x (Pos.to_nat 1)) as Hltb eqn:HeqHltb; 
      destruct Hltb;
      symmetry in HeqHltb;
      try (rewrite Nat.ltb_lt in HeqHltb);
      try (rewrite Nat.ltb_ge in HeqHltb);
      try solve [zify; omega]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.


Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.


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
