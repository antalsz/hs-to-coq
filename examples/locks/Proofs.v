Require Import GHC.Num.
Require Import GHC.MVar.
Require Import Control.Concurrent.MVar.
Require Import Proofs.Control.Concurrency.Interp.

Require Import Locks.

Require Import Psatz Logic.FunctionalExtensionality.

Axiom decode_encode_word : forall (w : Word),
    decode (encode w) = Some w.

Ltac forward := first
                  [apply SafeFinished; reflexivity |
                   eapply SafeRunning; [try reflexivity |] |
                   apply DeadlockBlocked; reflexivity |
                   eapply DeadlockRunning; [try reflexivity |]
                  ].
                   
Theorem example_prog_safe : safe_single_prog example.
Proof.
  do 3 forward.
  - simpl; rewrite decode_encode_word. reflexivity.
  - forward.
Qed.

Lemma deadlock_prog_deadlock : deadlock_single_prog deadlock.
Proof.
  do 2 forward.
Qed.

Theorem deadlock_prog_unsafe : ~ safe_single_prog deadlock.
Proof.
  apply deadlock_unsafe. apply deadlock_prog_deadlock.
Qed.

Definition access_heap { A } (h : heap) (loc : GHC.Num.Word) : option A :=
  match content h loc with
  | Some w => decode w
  | None => None
  end.

Ltac forward_rg :=
  let h := fresh "h" in
  let h' := fresh "h" in
  let p := fresh "p" in
  let HR := fresh "HR" in
  let HP := fresh "HP" in
  apply RgStep;
  intros h h' p HR HP.

Theorem example_prog_spec : forall h,
    let mloc := max_loc h + 1 in
    let h' :=
        {| max_loc := mloc;
           content := fun n => if n =? mloc then None else content h n |} in
    h ⊨
      {{ fun _ => True }}
      [[ fun h1 h2 =>
           max_loc h1 = max_loc h2 /\
           content h1 mloc = content h2 mloc ]]
      example
      [[ fun _ _ => True ]]
      {{ fun h =>
           content h mloc = content h' mloc }}.
Proof.
  intros. subst mloc.

  forward_rg.
  destruct HR as [HR1 HR2].
  simpl. destruct h0 as [max_loc0 content0].
  simpl in HR1. inversion 1.
  exists (fun h => content h (max_loc0 + 1) = None).
  intuition.
  simpl. rewrite N.eqb_refl. reflexivity.

  forward_rg.
  subst. simpl. destruct HR as [HR3 HR4].
  rewrite <- HR4. simpl. rewrite N.eqb_refl.
  destruct h0 as [max_loc1 content1]. simpl in HR3. inversion 1.
  exists (fun h => content h max_loc1 = Some (encode 42)).
  intuition.
  subst. simpl. rewrite N.eqb_refl. reflexivity.

  forward_rg.
  subst. simpl. destruct HR as [HR5 HR6].
  rewrite <- HR6. simpl. rewrite N.eqb_refl, decode_encode_word.
  destruct h0 as [max_loc2 content2]. simpl in HR5. inversion 1.
  exists (fun h => content h max_loc2 = content h' max_loc2).
  intuition.
  unfold h'. simpl.
  rewrite HR5, N.eqb_refl. reflexivity.

  apply RgFinished.
  intros; subst. simpl. intuition.
  rewrite <- H4. simpl. rewrite N.eqb_refl. reflexivity.
Qed.

(** The rest is going to break! *)

Require Import ZArith.

Open Scope Z_scope.

Axiom decode_encode_int : forall (w : Int),
    decode (encode w) = Some w.

Definition R1 bloc : rely :=
  fun h1 h2 =>
    @access_heap Int h1 bloc = access_heap h2 bloc.

Definition G1 bloc : guarantee :=
  fun h1 h2 =>
    forall bal,
      access_heap h2 bloc = Some bal ->
      bal >= 1000.

Ltac prove_guarantee :=
  let H := fresh "H" in
  intros ? H; unfold access_heap in H; simpl in H;
  rewrite N.eqb_refl in H;
  first [rewrite decode_encode_int in H; inversion H; lia |
         discriminate].

Ltac split_g :=
  split; [| prove_guarantee].

Ltac destruct_match :=
  match goal with
  | |- context[match ?a with _ => _ end] =>
    let Hm := fresh "Hmatch" in
    destruct a eqn:Hm
  end.

Ltac use_rely Hb :=
  unfold access_heap in Hb; simpl in Hb;
  try rewrite N.eqb_refl in Hb; simpl;
  destruct_match; try discriminate;
  try (rewrite decode_encode_int in Hb);
  try rewrite <- Hb; destruct_match; inversion 1.

Definition inv_t1 bloc : pre :=
  fun h => exists bal : Int, access_heap h bloc = Some bal /\ bal >= 1000.

Lemma t1_spec : forall h bloc cloc,
    let bm := MkMV bloc in
    let cm := MkMV cloc in
    h ⊨
      {{ inv_t1 bloc }}
      [[ R1 bloc ]]
      (t1 bm cm)
      [[ G1 bloc ]]
      {{ inv_t1 bloc }}.
Proof.
  intros.
  unfold R1, G1, inv_t1.
  
  forward_rg.
  destruct HP as [bal [HP1 HP2] ].
  rewrite HP1 in HR.
  use_rely HR.
  exists (fun h => h = h1). split; [reflexivity |].
  split_g.
  
  forward_rg.
  use_rely Hb0.
  split_g.

  forward_rg.
  use_rely Hb1.
  split_g.

  forward_rg.
  use_rely Hb2.
  split_g.

  forward_rg.
  use_rely Hb3.
  split_g.

  forward_rg.
  use_rely Hb4.
  split_g.

  eapply RgFinished. simpl.
  intros. intuition.
  unfold Int in H17.
  rewrite <- H17 in H20. unfold access_heap in H20.
  simpl in H20. rewrite N.eqb_refl in H20.
  rewrite decode_encode_int in H20. inversion H20.
  lia.
Qed.
