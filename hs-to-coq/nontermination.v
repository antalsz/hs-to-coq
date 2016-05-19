Require Import Ssreflect.ssreflect Ssreflect.ssrfun.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation "f '$' x" := (f x) (left associativity, at level 99, only parsing).
Notation "g '∘' f" := (g \o f) (left associativity, at level 50).
Notation "'_∘_'"   := (fun g f => g ∘ f).

Notation "n1 ≤ n2" := (n1 <= n2) (at level 70) : nat_scope.

Inductive Answer (A : Type) : Type :=
  | Value of A
  | Error of string
  | Incomplete.
Arguments Value      {A} _.
Arguments Error      {A} _.
Arguments Incomplete {A}.

Reserved Notation "ans1 ⊑ ans2 :> A" (at level 70, ans2 at next level).
Reserved Notation "ans1 ⊑ ans2" (at level 70).
Inductive Compatible {A : Type} : Answer A -> Answer A -> Type :=
  | CValues     : forall (v    : A),              Value v    ⊑ Value v
  | CErrors     : forall (err  : string),         Error err  ⊑ Error err :> A
  | CIncomplete : forall (ans2 : Answer A),       Incomplete ⊑ ans2
  where "ans1 ⊑ ans2 :> A" := (@Compatible A ans1 ans2)
  and   "ans1 ⊑ ans2"      := (ans1 ⊑ ans2 :> _).
Hint Constructors Compatible.

Definition Fuel : Type := nat.
Bind Scope nat_scope with Fuel.

Record Continuous {A : Type} (f : Fuel -> Answer A) : Type :=
  IsContinuous { cmap : forall (k k' : Fuel), k ≤ k' -> f k ⊑ f k' }.

Record HS (A : Type) : Type := MkHS { compute    : Fuel -> Answer A
                                    ; continuity : Continuous compute }.
Notation "⟪| f_ans |⟫" :=
  {| compute := f_ans; continuity := _ |}
  (at level 0, format "⟪| f_ans |⟫").

Notation "⟪ k → ans ⟫" := ⟪| fun k => ans |⟫
  (at level 0, k at level 99, format "⟪ k  →  ans ⟫").

Record EqHS {A : Type} (h1 h2 : HS A) : Type :=
  EqCompute { equivalent : forall (k : Fuel), compute h1 k = compute h2 k }.
Notation "h1 '≈' h2 :> A" := (@EqHS A h1 h2) (at level 70, h2 at next level).
Notation "h1 '≈' h2"      := (h1 ≈ h2 :> _)  (at level 70).

Definition EqHSFun {A B : Type}   (f g : B      -> HS A) : Type :=  forall x,   f x   ≈ g x.
Definition EqHSRel {A B C : Type} (r s : C -> B -> HS A) : Type :=  forall x y, r x y ≈ s x y.

Notation "f1 '≈1' f2 ':>' A" := (EqHSFun f1 (f2 : A)) (at level 70, f2 at next level, A at level 90).
Notation "f1 '≈1' f2"        := (EqHSFun f1 f2)       (at level 70).

Notation "r1 '≈2' r2 ':>' A" := (EqHSRel r1 (r2 : A)) (at level 70, r2 at next level, A at level 90).
Notation "r1 '≈2' r2"        := (EqHSRel r1 r2)       (at level 70).

Ltac continuity :=
  match goal with
    | [|- Continuous ?f] =>
      let k    := fresh "k"    in
      let k'   := fresh "k'"   in
      let desc := fresh "desc" in
      constructor=> k k' desc;
      let case_continuity h := (move: (cmap (continuity h) desc);
                                let v := fresh "v" in let v' := fresh "v'" in
                                let e := fresh "e" in let e' := fresh "e'" in
                                case: (compute h k) => [v|e|]; case: (compute h k') => [v'|e'|];
                                inversion 1; subst; simpl) in
      repeat match goal with
        | [h : HS _ |- context[compute ?h k]]  => case_continuity h
        | [h : HS _ |- context[compute ?h k']] => case_continuity h
      end;
      try done
  end.

Definition hs_map {A B : Type} (f : A -> B) (h : HS A) : HS B.
  refine ⟪k → match compute h k with
                | Value a    => Value (f a)
                | Error e    => Error e
                | Incomplete => Incomplete
              end⟫;
  abstract continuity.
Defined.
Notation "f ⟪$⟫ h" := (hs_map f h) (left associativity, at level 61).
Arguments hs_map {A B} f !h /.

Definition hs_pure {A : Type} (a : A) : HS A.
  refine ⟪_ → Value a⟫;
  abstract continuity.
Defined.
Arguments hs_pure {A} / a.

Definition hs_ap {A B : Type} (hf : HS (A -> B)) (ha : HS A) : HS B.
  refine ⟪k → match compute hf k with
                | Value f    => compute (f ⟪$⟫ ha) k
                | Error e    => Error e
                | Incomplete => Incomplete
              end⟫;
  abstract continuity.
Defined.
Notation "hf ⟪*⟫ ha" := (hs_ap hf ha) (left associativity, at level 61).
Arguments hs_ap {A B} !hf !ha /.

Definition hs_join {A : Type} (hha : HS (HS A)) : HS A.
  refine ⟪k → match compute hha k with
                | Value ha   => compute ha k
                | Error e    => Error e
                | Incomplete => Incomplete
              end⟫;
  abstract continuity.
Defined.
Arguments hs_join {A} !hha /.

Definition hs_bind {A B : Type} (ha : HS A) (f : A -> HS B) : HS B.
  refine ⟪k → match compute ha k with
                | Value a    => compute (f a) k
                | Error e    => Error e
                | Incomplete => Incomplete
              end⟫;
  abstract continuity.
Defined.
Notation "h >>≈ f" := (hs_bind h f) (right associativity, at level 90).
Arguments hs_bind {A B} !ha f /.

Definition hs_rbind {A B : Type} (f : A -> HS B) (ha : HS A) : HS B := ha >>≈ f.
Notation "f ≈<< h" := (hs_rbind f h) (left associativity, at level 91).
Arguments hs_rbind {A B} f !ha /.

Theorem Compatible_refl {A : Type} (ans : Answer A) : ans ⊑ ans.
Proof. by case: ans. Qed.
Hint Resolve Compatible_refl.

Theorem Compatible_asym {A : Type} (ans1 ans2 : Answer A) :
  ans1 ⊑ ans2 -> ans2 ⊑ ans1 -> ans1 = ans2.
Proof. by inversion 1; subst; try done; inversion 1. Qed.

Theorem Compatible_trans {A : Type} (ans1 ans2 ans3 : Answer A) :
  ans1 ⊑ ans2 -> ans2 ⊑ ans3 -> ans1 ⊑ ans3.
Proof. by inversion 1; subst. Qed.

Theorem EqHS_refl {A : Type} (h : HS A) : h ≈ h.
Proof. done. Qed.

Theorem EqHS_sym {A : Type} (h1 h2 : HS A) : h1 ≈ h2 -> h2 ≈ h1.
Proof. by move=> [equiv]; constructor=> k. Qed.

Theorem EqHS_trans {A : Type} (h1 h2 h3 : HS A) : h1 ≈ h2 -> h2 ≈ h3 -> h1 ≈ h3.
Proof.
  move=> [equiv12] [equiv23]; constructor=> k.
  exact (etrans (equiv12 k) (equiv23 k)).
Qed.

Section RelationClasses.
  Require Import Coq.Classes.RelationClasses.
  Generalizable Variable A.
   
  Global Instance EqHS_PreOrder : `(PreOrder (@EqHS A)) :=
    {| PreOrder_Reflexive  := EqHS_refl
     ; PreOrder_Transitive := EqHS_trans |}.
  Global Instance EqHS_PER : `(PER (@EqHS A)) :=
    {| PER_Symmetric  := EqHS_sym
     ; PER_Transitive := EqHS_trans |}.
  Global Instance EqHS_Equivalence : (Equivalence (@EqHS A)) :=
    {| Equivalence_Reflexive  := EqHS_refl
     ; Equivalence_Symmetric  := EqHS_sym
     ; Equivalence_Transitive := EqHS_trans |}.
  Global Instance EqHS_Rewrite : `(@RewriteRelation (HS A) EqHS) :=
    {| |}.
End RelationClasses.

Ltac EqHS_solve :=
  let k := fresh "k" in
  rewrite /= ?/EqHSFun ?/EqHSRel;
  repeat match goal with
    [|- forall (_ : HS _), _] => let h := fresh "h"
                                 in move=> h
  end;
  repeat match goal with
    [h : HS _ |- _] => let hf := fresh "hf" in
                       let hc := fresh "hc"
                       in case: h => [hf hc]
  end;
  match goal with
    [|- _ ≈ _] => constructor=> k /=
  end;
  repeat match goal with
    [hf : Fuel -> Answer _ |- _] =>
      match goal with
        [|- context[match hf k with _ => _ end]] => case: (hf k) => //=
      end
  end;
  try done.

Theorem hs_map_id {A : Type} (h : HS A) : id ⟪$⟫ h ≈ h.
Proof. EqHS_solve. Qed.

Theorem hs_map_comp {A B C : Type} (f : B -> C) (g : A -> B) : hs_map (f ∘ g) ≈1 hs_map f ∘ hs_map g.
Proof. EqHS_solve. Qed.

Lemma hs_map_eta {A B : Type} (f : A -> B) : hs_map ([eta f]) ≈1 hs_map f.
Proof. EqHS_solve. Qed.

Theorem hs_ap_id {A : Type} (v : HS A) : hs_pure id ⟪*⟫ v ≈ v.
Proof. EqHS_solve. Qed.

Theorem hs_ap_comp {A B C : Type} (u : HS (B -> C)) (v : HS (A -> B)) (w : HS A) :
  hs_pure _∘_ ⟪*⟫ u ⟪*⟫ v ⟪*⟫ w ≈ u ⟪*⟫ (v ⟪*⟫ w).
Proof. EqHS_solve. Qed.

Theorem hs_ap_hom {A B : Type} (f : A -> B) (x : A) :
  hs_pure f ⟪*⟫ hs_pure x ≈ hs_pure (f x).
Proof. EqHS_solve. Qed.

Theorem hs_ap_interchange {A B : Type} (u : HS (A -> B)) (y : A) :
  u ⟪*⟫ hs_pure y ≈ hs_pure (@^~ y) ⟪*⟫ u.
Proof. EqHS_solve. Qed.

Theorem hs_ap_fmap {A B C : Type} (f : A -> B) (ha : HS A) :
  f ⟪$⟫ ha ≈ hs_pure f ⟪*⟫ ha.
Proof. EqHS_solve. Qed.

Unset Elimination Schemes.
Inductive stream' (A : Type) : Type :=
  | snil  : stream' A
  | scons : A -> (Fuel -> Answer (stream' A)) -> stream' A.
Arguments snil  {A}.
Arguments scons {A} _ _.
Set Elimination Schemes.

Fixpoint stream'_rect {A : Type} (P : stream' A -> Type)
                      (P_snil  : P snil)
                      (P_scons : forall (a : A) (f : Fuel -> Answer (stream' A)),
                                   (forall k, match f k return Type with
                                                | Value s' => P s'
                                                | _        => unit
                                              end)
                                   -> P (scons a f))
                      (s : stream' A) : P s :=
  match s with
    | snil        =>
        P_snil
    | scons a fs' =>
        P_scons a fs' (fun k => match fs' k as ans' return match ans' return Type with
                                                             | Value s' => P s'
                                                             | _        => unit
                                                           end
                                with
                                  | Value s' => stream'_rect P_snil P_scons s'
                                  | _        => tt
                                end)
  end.

Fixpoint stream'_ind {A : Type} (P : stream' A -> Prop)
                     (P_snil  : P snil)
                     (P_scons : forall (a : A) (f : Fuel -> Answer (stream' A)),
                                  (forall k, match f k return Prop with
                                               | Value s' => P s'
                                               | _        => True
                                             end)
                                  -> P (scons a f))
                     (s : stream' A) : P s :=
  match s with
    | snil        =>
        P_snil
    | scons a fs' =>
        P_scons a fs' (fun k => match fs' k as ans' return match ans' return Prop with
                                                             | Value s' => P s'
                                                             | _        => True
                                                           end
                                with
                                  | Value s' => stream'_ind P_snil P_scons s'
                                  | _        => I
                                end)
  end.

Fixpoint stream'_rec {A : Type} (P : stream' A -> Set)
                     (P_snil  : P snil)
                     (P_scons : forall (a : A) (f : Fuel -> Answer (stream' A)),
                                  (forall k, match f k return Type with
                                               | Value s' => P s'
                                               | _        => unit
                                             end)
                                  -> P (scons a f))
                     (s : stream' A) : P s :=
  match s with
    | snil        =>
        P_snil
    | scons a fs' =>
        P_scons a fs' (fun k => match fs' k as ans' return match ans' return Type with
                                                             | Value s' => P s'
                                                             | _        => unit
                                                           end
                                with
                                  | Value s' => stream'_rect P_snil P_scons s'
                                  | _        => tt
                                end)
  end.

Fixpoint stream'_wf (A : Type) (s : stream' A) {struct s} : Type :=
  match s with
    | snil => unit
    | scons _ compute_tail =>
      Continuous compute_tail *
      forall n,
        match compute_tail n with
          | Value s' => stream'_wf s'
          | _        => unit
        end
  end%type.

Record stream (A : Type) : Type :=
  WFStream { contents    : stream' A
           ; well_formed : stream'_wf contents }.

Fixpoint stream'_to_list {A : Type} (s : stream' A) : stream'_wf s -> Fuel -> Answer (list A) :=
  match s return stream'_wf s -> Fuel -> Answer (list A) with
    | snil        => fun _  _ =>
        Value nil
    | scons a fs' => fun wf k =>
        match fs' k as ans' return match ans' with
                                     | Value s' => stream'_wf s'
                                     | _        => unit
                                   end -> Answer (list A)
        with
          | Value s'   => fun wf' => @stream'_to_list A s' wf' k
          | Error e    => fun _   => Error e
          | Incomplete => fun _   => Incomplete
        end (wf.2 k)
  end.
Arguments stream'_to_list {A} !s !wf / k.

Lemma stream'_to_list_irrel {A : Type} (s : stream' A) (wf1 wf2 : stream'_wf s) :
  stream'_to_list s wf1 =1 stream'_to_list s wf2.
Proof.
  elim: s wf1 wf2 => //= a fs' IH [cont1 all_wf1'] [cont2 all_wf2'] /= k.
  move: (all_wf1' k) (all_wf2' k) (IH k).
  by case: (fs' k) => //= s' wf1' wf2' /(_ wf1' wf2').
Qed.

Theorem stream'_to_list_continuous {A : Type} (s : stream' A) (wf : stream'_wf s) :
  Continuous (stream'_to_list s wf).
Proof.
  elim: s wf => //= a fs' IH [cont wf_all] /=.
  constructor=> k k' desc.
  move: (cmap cont desc);
    case: (fs' k)  (wf_all k)  (IH k)  => [s'1 wf'1 | e1 [] | []] IH1;
    case: (fs' k') (wf_all k') (IH k') => [s'2 wf'2 | e2 [] | []] IH2;
    move=> compat; inversion compat; subst; try done.
  rewrite (stream'_to_list_irrel wf'1 wf'2).
  apply (cmap (IH1 wf'2) desc).
Qed.

Definition stream_to_list {A : Type} (s : stream A) : HS (list A).
  destruct s as [s wf].
  refine ⟪|stream'_to_list s wf|⟫.
  exact (stream'_to_list_continuous wf).
Qed.
