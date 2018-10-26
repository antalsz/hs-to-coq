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
  simpl. destruct h0 as [max_loc0 content0]. simpl.
  unfold access_heap in HP1. simpl in HP1.
  destruct (content0 bloc); [| discriminate].
  rewrite HP1. inversion 1.
  exists (fun h => content h bloc = None).
  split.
  simpl. rewrite N.eqb_refl. reflexivity.
  split_g.
  
  forward_rg.
  simpl. rewrite HP.
  destruct h0 as [max_loc1 content1]. inversion 1.
  exists (inv_t1 bloc).
  split.
  unfold inv_t1.
  exists (bal + 5000). unfold access_heap. simpl.
  rewrite N.eqb_refl. rewrite decode_encode_int. intuition.
  split_g.

  forward_rg.
  simpl. unfold inv_t1, access_heap in HP0.
  destruct HP0 as [bal1 [HP3 HP4] ]. 
  destruct (content h0 bloc); [| discriminate].
  rewrite HP3. destruct h0 as [max_loc2 content2]. inversion 1.
  exists (fun h => content h bloc = None).
  split.
  simpl. rewrite N.eqb_refl. reflexivity.
  split_g.

  forward_rg.
  simpl. rewrite HP0.
  destruct h0 as [max_loc3 content3]. inversion 1.
  exists (inv_t1 bloc).
  split.
  unfold inv_t1.
  exists (bal1 + 1000). unfold access_heap. simpl.
  rewrite N.eqb_refl. rewrite decode_encode_int. intuition.
  split_g.

  forward_rg.
  simpl. unfold inv_t1, access_heap in HP5.
  destruct HP5 as [bal2 [HP5 HP6] ]. 
  destruct (content h0 bloc); [| discriminate].
  rewrite HP5. destruct h0 as [max_loc4 content4]. inversion 1.
  exists (fun h => content h bloc = None).
  split.
  simpl. rewrite N.eqb_refl. reflexivity.
  split_g.

  forward_rg.
  simpl. rewrite HP7.
  destruct h0 as [max_loc5 content5]. inversion 1.
  exists (inv_t1 bloc).
  split.
  unfold inv_t1.
  exists (bal2 * 2). unfold access_heap. simpl.
  rewrite N.eqb_refl. rewrite decode_encode_int. intuition.
  split_g.

  eapply RgFinished. simpl.
  intros. intuition.
  unfold Int in H15.
  rewrite <- H15 in H19. unfold access_heap in H19.
  simpl in H19. rewrite N.eqb_refl, decode_encode_int in H19.
  inversion H19.
  lia.
Qed.
