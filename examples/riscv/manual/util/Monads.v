Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.

Class Monad(M: Type -> Type) := mkMonad {
  Bind: forall {A B}, M A -> (A -> M B) -> M B;
  Return: forall {A}, A -> M A;

  left_identity: forall {A B} (a: A) (f: A -> M B),
    Bind (Return a) f = f a;
  right_identity: forall {A} (m: M A),
    Bind m Return = m;
  associativity: forall {A B C} (m: M A) (f: A -> M B) (g: B -> M C),
    Bind (Bind m f) g = Bind m (fun x => Bind (f x) g)
}.


Notation "x <- m1 ; m2" := (Bind m1 (fun x => m2))
  (right associativity, at level 60) : monad_scope.
Notation "m1 ;; m2" := (Bind m1 (fun _ => m2))
  (right associativity, at level 60) : monad_scope.

Open Scope monad_scope.

Instance option_Monad: Monad option := {|
  Bind := fun {A B: Type} (o: option A) (f: A -> option B) => match o with
          | Some x => f x
          | None => None
          end;
  Return := fun {A: Type} (a: A) => Some a
|}.
- intros. reflexivity.
- intros. destruct m; reflexivity.
- intros. destruct m; reflexivity.
Defined.


(* Monad which also supports failure (mzero) and choice (mplus), typically used to chose
   the first successful one *)
Class MonadPlus(M: Type -> Type){MM: Monad M} := mkMonadPlus {
  mzero: forall {A}, M A;
  mplus: forall {A}, M A -> M A -> M A;

  mzero_left: forall {A} (f: A -> M A), Bind mzero f = mzero;
  mzero_right: forall {A B} (v: M A), Bind v (fun (_: A) => @mzero B) = @mzero B;
  mplus_assoc: forall {A} (m1 m2 m3: M A), mplus m1 (mplus m2 m3) = mplus (mplus m1 m2) m3;
}.

Definition msum{A}{M: Type -> Type}{MM: Monad M}{MP: MonadPlus M}: list (M A) -> M A :=
  fold_right mplus mzero.


Instance OptionMonadPlus: MonadPlus option := {|
  mzero := @None;
  mplus A m1 m2 := match m1 with
                   | Some x => m1
                   | None => m2
                   end;
|}.
- intros. reflexivity.
- intros. destruct v; reflexivity.
- intros. destruct m1; reflexivity.
Defined.


Definition State(S A: Type) := S -> (A * S).

Instance State_Monad(S: Type): Monad (State S) := {|
  Bind := fun {A B: Type} (m: State S A) (f: A -> State S B) =>
            fun (s: S) => let (a, s') := m s in f a s' ;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => (a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
- intros. extensionality s. destruct (m s). reflexivity.
Defined.

Module StateM.
Definition get{S: Type}: State S S := fun (s: S) => (s, s).
Definition gets{S A: Type}(f: S -> A): State S A := fun (s: S) => (f s, s).
Definition put{S: Type}(s: S): State S unit := fun _ => (tt, s).
End StateM.

Definition OState(S A: Type) := S -> option (A * S).

Instance OState_Monad(S: Type): Monad (OState S) := {|
  Bind := fun {A B: Type} (m: OState S A) (f: A -> OState S B) =>
            fun (s: S) => match m s with
            | Some (a, s') => f a s'
            | None => None
            end;
  Return := fun {A: Type} (a: A) =>
              fun (s: S) => Some (a, s)
|}.
- intros. reflexivity.
- intros. extensionality s. destruct (m s); [|reflexivity]. destruct p. reflexivity.
- intros. extensionality s. destruct (m s); [|reflexivity]. destruct p. reflexivity.
Defined.

Instance OState_MonadPlus(S: Type): MonadPlus (OState S) := {|
  mzero A s := @None (A * S);
  mplus A m1 m2 s := match m1 s with
    | Some p => Some p
    | None => m2 s
    end;
|}.
- intros. reflexivity.
- intros. simpl. extensionality s. destruct (v s); [|reflexivity]. destruct p. reflexivity.
- intros. extensionality s. destruct (m1 s); reflexivity.
Defined.

Definition get{S: Type}: OState S S := fun (s: S) => Some (s, s).
Definition gets{S A: Type}(f: S -> A): OState S A := fun (s: S) => Some (f s, s).
Definition put{S: Type}(s: S): OState S unit := fun _ => Some (tt, s).


(* T for transformer, corresponds to Haskell's MaybeT: *)
Definition optionT(M: Type -> Type)(A: Type) := M (option A).

Instance OptionT_is_Monad(M: Type -> Type){MM: Monad M}: Monad (optionT M) := {|
  Bind{A}{B}(m: M (option A))(f: A -> M (option B)) :=
    Bind m (fun (o: option A) =>
      match o with
      | Some a => f a
      | None => Return None
      end);
  Return{A}(a: A) := Return (Some a);
|}.
- intros. rewrite left_identity. reflexivity.
- intros. rewrite <- right_identity. f_equal. extensionality o. destruct o; reflexivity.
- intros. rewrite associativity. f_equal. extensionality o. destruct o.
  + reflexivity.
  + rewrite left_identity. reflexivity.
Defined.

Lemma discard_left: forall {M : Type -> Type} {MM : Monad M} {A B : Type} (m: M A) (b: B),
  Bind m (fun _  => Return b) = Return b.
Proof.
  intros. (* Note: This does not hold for the state monad! *)
Admitted.

Definition OpSt(S: Type): Type -> Type := optionT (State S).

Definition OpSt_Monad(S: Type): Monad (OpSt S).
  unfold OpSt. apply OptionT_is_Monad. apply State_Monad.
Defined.

Goal forall (S: Type), False. intro S. set (b := @Bind (OpSt S) (OpSt_Monad S)).
Abort.

Instance optionT_is_MonadPlus(M: Type -> Type){MM: Monad M}: MonadPlus (optionT M) := {|
  mzero A := Return None : M (option A);
  mplus A m1 m2 := @Bind _ _ (option A) _ m1 (fun (o1: option A) => match o1 with
    | Some a1 => Return (Some a1)
    | None => m2
    end) : M (option A);
|}.
- intros. simpl. rewrite left_identity. reflexivity.
- intros. simpl.
  transitivity (Bind v (fun o : option A => Return (@None B))).
  + f_equal. extensionality o. destruct o; reflexivity.
  + apply discard_left.
- intros.
  rewrite associativity. f_equal. extensionality o1. destruct o1.
  + rewrite left_identity. reflexivity.
  + reflexivity.
Defined.

Class MonadTrans(T: (Type -> Type) -> (Type -> Type)) := mkMonadTrans {
  lift{M: Type -> Type}{MM: Monad M}{A: Type}: M A -> T M A;
  transformed_monad{M: Type -> Type}{MM: Monad M}: Monad (T M);
  lift_return{M: Type -> Type}{MM: Monad M}{A: Type}:
    forall a: A, lift (Return a) = Return a;
  lift_bind{M: Type -> Type}{MM: Monad M}{A B: Type}:
    forall (m: M A) (f: A -> M B), lift (Bind m f) = Bind (lift m) (fun x => lift (f x));
}.

(* Promote a function to a monad. *)
Definition liftM{M: Type -> Type}{MM: Monad M}{A B: Type}(f: A -> B): M A -> M B :=
  fun m => x <- m; Return (f x).

Instance optionT_is_MonadTrans: MonadTrans optionT := {|
  lift M MM A := liftM Some;
  transformed_monad := OptionT_is_Monad;
|}.
- intros. unfold liftM. simpl. rewrite left_identity. reflexivity.
- intros. unfold liftM. simpl. rewrite? associativity. f_equal. extensionality a.
  rewrite left_identity. reflexivity.
Defined.
