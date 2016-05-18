Require Import Ssreflect.ssreflect Ssreflect.ssrfun.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Notation "f '$' x" := (f x) (left associativity, at level 99, only parsing).
Notation "g '∘' f" := (g \o f) (left associativity, at level 50).
Notation "'_∘_'"   := (fun g f => g ∘ f).

CoInductive HS (A : Type) : Type :=
  | Value of A
  | Step  of HS A
  | Error of string.

Arguments Value {A} _.
Arguments Step  {A} _.
Arguments Error {A} _.

Reserved Notation "h1 '≈' h2 ':>' A" (at level 70, h2 at next level).
Reserved Notation "h1 '≈' h2"        (at level 70).
CoInductive EqHS {A : Type} : HS A -> HS A -> Prop :=
  | EqHS_Value : forall (a1 a2 : A),      a1 = a2 -> Value a1 ≈ Value a2
  | EqHS_Step  : forall (h1 h2 : HS A),   h1 ≈ h2 -> Step  h1 ≈ Step  h2
  | EqHS_Error : forall (e1 e2 : string), e1 = e2 -> Error e1 ≈ Error e2 :> A
  where "h1 '≈' h2 :> A" := (@EqHS A h1 h2)
  and   "h1 '≈' h2"      := (h1 ≈ h2 :> _).

Definition EqHSFun {A B : Type}   (f g : B      -> HS A) : Prop :=  forall x,   f x   ≈ g x.
Definition EqHSRel {A B C : Type} (r s : C -> B -> HS A) : Prop :=  forall x y, r x y ≈ s x y.

Notation "f1 '≈1' f2 ':>' A" := (EqHSFun f1 (f2 : A)) (at level 70, f2 at next level, A at level 90).
Notation "f1 '≈1' f2"        := (EqHSFun f1 f2)       (at level 70).

Notation "r1 '≈2' r2 ':>' A" := (EqHSRel r1 (r2 : A)) (at level 70, r2 at next level, A at level 90).
Notation "r1 '≈2' r2"        := (EqHSRel r1 r2)       (at level 70).

Definition hs_compute {A : Type} (h : HS A) : HS A :=
  match h with
    | Value a  => Value a
    | Step  h' => Step h'
    | Error e  => Error e
  end.

Fixpoint hs_eval {A : Type} (n : nat) (h : HS A) : HS A :=
  match n , h with
    | O    , _        => h
    | S _  , Value a  => Value a
    | S n' , Step  h' => Step (hs_eval n' h')
    | S _  , Error e  => Error e
  end.

Reserved Notation "f ⟪$⟫ h" (left associativity, at level 61).
CoFixpoint hs_map {A B : Type} (f : A -> B) (h : HS A) : HS B :=
  match h with
    | Value a  => Value (f a)
    | Step  h' => Step (f ⟪$⟫ h')
    | Error e  => Error e
  end
where "f ⟪$⟫ h" := (hs_map f h).

Definition hs_pure {A : Type} : A -> HS A := Value.

Reserved Notation "f ⟪*⟫ h" (left associativity, at level 61).
CoFixpoint hs_ap {A B : Type} (hf : HS (A -> B)) (ha : HS A) : HS B :=
  match hf with
    | Value f   => hs_map f ha
    | Step  hf' => Step (hf' ⟪*⟫ ha)
    | Error ef  => Error ef
  end
where "hf ⟪*⟫ ha" := (hs_ap hf ha).

CoFixpoint hs_join {A : Type} (hha : HS (HS A)) : HS A :=
  match hha with
    | Value ha   => ha
    | Step  hha' => Step (hs_join hha')
    | Error e    => Error e
  end.

Reserved Notation "h >>≈ f" (right associativity, at level 90).
CoFixpoint hs_bind {A B : Type} (ha : HS A) (f : A -> HS B) : HS B :=
  match ha with
    | Value a   => f a
    | Step  ha' => Step (ha' >>≈ f)
    | Error e   => Error e
  end
where "h >>≈ f" := (hs_bind h f).

Definition hs_rbind {A B : Type} (f : A -> HS B) (ha : HS A) : HS B := hs_bind ha f.
Notation "f ≈<< h" := (hs_rbind f h) (left associativity, at level 91).

Theorem hs_compute_eq {A : Type} (h : HS A) : hs_compute h = h.
Proof. by case: h. Qed.

Theorem EqHS_inv_Value {A : Type} {a1 a2 : A} : Value a1 ≈ Value a2 -> a1 = a2.
Proof. by inversion 1; subst. Qed.

Theorem EqHS_inv_Step {A : Type} {h1 h2 : HS A} : Step h1 ≈ Step h2 -> h1 ≈ h2.
Proof. by inversion 1; subst. Qed.

Theorem EqHS_inv_Error {A : Type} {e1 e2 : string} : Error e1 ≈ Error e2 :> A -> e1 = e2.
Proof. by inversion 1; subst. Qed.

Theorem EqHS_refl {A : Type} : forall (h : HS A), h ≈ h.
Proof. by cofix; case; constructor. Qed.

Ltac compute_EqHS :=
  match goal with
    | |- ?f1 ?x1 ≈ ?f2 ?x2 =>
      rewrite -(hs_compute_eq (f1 x1)) -(hs_compute_eq (f2 x2))
    | |- ?f1 ?x1 ≈ _ =>
      rewrite -(hs_compute_eq (f1 x1))
    | |- _ ≈ ?f2 ?x2 =>
      rewrite -(hs_compute_eq (f2 x2))
  end.

Ltac finish_EqHS :=
  try (by move=> *; apply EqHS_refl);
  try constructor; try done; try assumption;
  try repeat match goal with
    | H : _ ≈  _ |- _ => apply H
    | H : _ ≈1 _ |- _ => apply H
    | H : _ ≈2 _ |- _ => apply H
  end.

Ltac cofix_EqHS h :=
  cofix => h;
  compute_EqHS;
  case: h => /=;
  finish_EqHS.

Theorem hs_map_id {A : Type} : forall (h : HS A), id ⟪$⟫ h ≈ h.
Proof. cofix_EqHS h. Qed.

Theorem hs_map_comp {A B C : Type} (f : B -> C) (g : A -> B) : hs_map (f ∘ g) ≈1 hs_map f ∘ hs_map g.
Proof. cofix_EqHS h. Qed.

Lemma hs_map_eta {A B : Type} (f : A -> B) : hs_map ([eta f]) ≈1 hs_map f.
Proof. cofix_EqHS h. Qed.

Theorem hs_ap_id {A : Type} : forall (v : HS A), hs_pure id ⟪*⟫ v ≈ v.
Proof. cofix_EqHS h; apply hs_map_id. Qed.

(* Theorem hs_ap_comp {A B C : Type} : forall (u : HS (B -> C)) (v : HS (A -> B)) (w : HS A), *)
(*   hs_pure _∘_ ⟪*⟫ u ⟪*⟫ v ⟪*⟫ w ≈ u ⟪*⟫ (v ⟪*⟫ w). *)
(* Proof. *)
(*   cofix=> u v w; compute_EqHS; case: u => [fu|u'|eu] /=; finish_EqHS. *)
(*   - case: v => [fv|v'|ev] /=; finish_EqHS. *)
(*     + case: w => [aw|w'|ew] /=; finish_EqHS. *)
(*       apply hs_map_comp. *)
(*     + rewrite hs_map_eta. *)
(*   - move: hs *)

(* Notation "'〖' f '@' x1 ',' .. ',' xN '〗'" := *)
(*   (hs_ap .. (hs_ap (hs_map f x1) ..) xN). *)

(* SubClass HSFn A B := HS (A -> B). *)
(* Definition hsfn_ap {A B : Type} (hf : HSFn A B) (ha : HS A) : HS B := hs_ap hf ha. *)
(* Coercion hsfn_ap : HSFn >-> Funclass. *)

(* (******************************************************************************) *)

(* Inductive HSList (A : Type) : Type := *)
(*   | HNil  : HSList A *)
(*   | HCons : A -> HS (HSList A) -> HSList A. *)

(* Arguments HNil  {A}. *)
(* Arguments HCons {A} _ _. *)

(* CoFixpoint force_list {A : Type} (hl : HSList A) : HS (list A) := *)
(*   match hl with *)
(*     | HNil         => Value nil *)
(*     | HCons a hhl' => hs_bind hhl' force_list *)
(*   end. *).

   f : ddd -> (a ->    b) ->    ddd
HS_f : ddd -> (a -> HS b) -> HS ddd

(* (******************************************************************************) *)

CoInductive stream (A : Type) : Type :=
  | snil  : stream A
  | scons : A -> stream A -> stream A.

(* (* CoFixpoint hs_map  {A B : Type} (f : A -> B) (h : HS A) : HS B := *) *)
(* (*   match h with *) *)
(* (*     | Value a  => Value (f a) *) *)
(* (*     | Step  h' => Step (hs_map f h') *) *)
(* (*     | Error e  => Error e *) *)
(* (*   end *) *)
(* (* with *) *)
(* (* stream_to_list {A : Type} (s : stream A) : HS (list A) := *) *)
(* (*   match s with *) *)
(* (*     | snil       => Value nil *) *)
(* (*     | scons a s' => Step (hs_map (cons a) (Step (stream_to_list s'))) *) *)
(* (*   end. *) *)

Fixpoint stream_to_list' {A : Type} (n : nat) (s : stream A) : HS (list A) :=
  match n , s with
    | O    , _          => Error "list exhausted"
    | S n' , snil       => Value nil
    | S n' , scons a s' => hs_map (cons a) (Step (stream_to_list' n' s'))
  end.

CoFixpoint stream_to_list {A : Type} (s : stream A) : HS (list A) :=
  match s with
    | snil       => Value nil
    | scons a s' => hs_map (cons a) (stream_to_list s'))
  end.
