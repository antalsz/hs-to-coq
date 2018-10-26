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

Ltac forward_rg :=
  let h := fresh "h" in
  let h' := fresh "h" in
  let p := fresh "p" in
  let HR := fresh "HR" in
  let HP := fresh "HP" in
  apply RgStep;
  intros h h' p HR HP.

Theorem example_prog_spec : forall h,
    let max_loc' := max_loc h + 1 in
    let h' :=
        {| max_loc := max_loc';
           content := fun n => if n =? max_loc' then None else content h n |} in
    h ⊨ {{ fun _ => True }} [[ fun h1 h2 => h1 = h2 ]] example [[ fun _ _ => True ]] {{ fun h => h = h' }}.
Proof.
  intros.

  forward_rg.
  simpl. destruct h0. inversion 1.
  exists (fun h => h =
           {|
             max_loc := max_loc + 1;
             content := fun n : Word => if n =? max_loc + 1 then None else content n |}).
  intuition.

  forward_rg.
  subst. simpl.
  rewrite N.eqb_refl. inversion 1.
  exists (fun h => h =
           {|
             max_loc := max_loc + 1;
             content := fun n : Word =>
                          if n =? max_loc + 1
                          then Some (encode 42)
                          else if n =? max_loc + 1 then None else content n |}).
  intuition.

  forward_rg.
  subst. simpl.
  rewrite N.eqb_refl, decode_encode_word. inversion 1.
  exists (fun h => h = h').
  intuition.
  unfold h', max_loc'. simpl. f_equal.
  apply functional_extensionality; intros.
  destruct (x =? max_loc + 1); reflexivity.

  apply RgFinished.
  intros; subst. simpl. intuition.
Qed.

(** The rest is going to break! *)

Require Import ZArith.

Open Scope Z_scope.

Axiom decode_encode_int : forall (w : Int),
    decode (encode w) = Some w.

Definition access_heap { A } (h : heap) (loc : GHC.Num.Word) : option A :=
  match content h loc with
  | Some w => decode w
  | None => None
  end.

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

Lemma inv_t1 : forall h bloc cloc (bal : Int),
    let bm := MkMV bloc in
    let cm := MkMV cloc in
    access_heap h bloc = Some bal ->
    bal >= 1000 ->
    h ⊨ {{ R1 bloc }} (t1 bm cm) {{ G1 bloc }}.
Proof.
  intros.
  unfold R1, G1.
  
  forward_rg.
  rewrite H in Hb.
  use_rely Hb.
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
