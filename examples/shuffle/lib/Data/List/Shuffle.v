(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Coq.Arith.Wf_nat.

Local Obligation Tactic := idtac.

Local Ltac solve_riffle :=
  solve [ apply Wf.measure_wf, Wf_nat.lt_wf
        | Tactics.program_simpl; simpl; rewrite PeanoNat.Nat.add_succ_r; auto ].

Ltac solve_shuffleLength_start halve length_halve solve1 solve2 :=
  try solve [apply Wf.measure_wf, Wf_nat.lt_wf];
  Tactics.program_simpl; try easy;
  match goal with H : (?half1,?half2) = halve _ ?arg_0__ |- _ =>
    generalize (length_halve _ arg_0__);
    rewrite <-H;
    intros [def_length1 def_length2];
    (* (rewrite def_length1 || rewrite def_length2); simpl; *)
    solve [solve1 arg_0__ def_length1 | solve2 arg_0__ def_length2]
  end.

Ltac solve_shuffleLength_half1 arg_0__ def_length1 :=
  rewrite def_length1; simpl;
  destruct arg_0__ as [|head0 tail0]; simpl; try easy;
  apply Lt.lt_n_S, PeanoNat.Nat.lt_div2;
  destruct tail0; simpl; [|apply PeanoNat.Nat.lt_0_succ];
  match goal with H : forall x, (cons x nil) <> (cons ?h nil) |- _ => specialize (H h) end;
  contradiction.

Ltac solve_shuffleLength_half2 arg_0__ def_length2 :=
  rewrite def_length2;
  apply PeanoNat.Nat.lt_div2;
  now destruct arg_0__; simpl; [|apply PeanoNat.Nat.lt_0_succ].

Ltac solve_shuffleLength halve length_halve :=
  solve_shuffleLength_start halve length_halve solve_shuffleLength_half1 solve_shuffleLength_half2.

(* Converted imports: *)

Require Control.Monad.Random.Class.
Require Data.Functor.
Require Data.Tuple.
Require GHC.Base.
Require GHC.Num.
Require Nat.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Program Fixpoint riffle {m} {a} `{Control.Monad.Random.Class.MonadRandom m}
                        (arg_0__ : list a) (arg_1__ : GHC.Num.Int) (arg_2__ : list a) (arg_3__
                          : GHC.Num.Int) {measure (length arg_0__ + length arg_2__)} : m (list a)
                   := match arg_0__, arg_1__, arg_2__, arg_3__ with
                      | xs, _, nil, _ => GHC.Base.pure xs
                      | nil, _, ys, _ => GHC.Base.pure ys
                      | cons x xs, nx, cons y ys, ny =>
                          Control.Monad.Random.Class.getRandomR (pair #1 (nx GHC.Num.+ ny)) GHC.Base.>>=
                          (fun k =>
                             if Bool.Sumbool.sumbool_of_bool (k GHC.Base.<= nx)
                             then (fun arg_6__ => cons x arg_6__) Data.Functor.<$>
                                  riffle xs (nx GHC.Num.- #1) (cons y ys) ny
                             else (fun arg_7__ => cons y arg_7__) Data.Functor.<$>
                                  riffle (cons x xs) nx ys (ny GHC.Num.- #1))
                      end.
Solve Obligations with (solve_riffle).

Definition halve {a} : list a -> (list a * list a)%type :=
  fix halve arg_0__
        := match arg_0__ with
           | nil => pair nil nil
           | cons z zs => let 'pair xs ys := halve zs in pair (cons z ys) xs
           end.

Theorem length_halve {a} (zs : list a) : let 'pair xs ys := halve zs in
  length xs = Nat.div2 (S (length zs)) /\ length ys = Nat.div2 (length zs).
Proof.
  induction zs as [|z zs IHzs]; simpl; try easy.
  destruct (halve zs) as [xs ys]; simpl.
  destruct IHzs as [IHxs IHys].
  split.
  - f_equal; apply IHys.
  - now rewrite IHxs; simpl.
Qed.

Program Fixpoint shuffleLength {m} {a} `{Control.Monad.Random.Class.MonadRandom
                               m} (arg_0__ : list a) {measure (length arg_0__)} : m (list a * GHC.Num.Int)%type
                   := match arg_0__ with
                      | nil => GHC.Base.pure (pair nil #0)
                      | cons x nil => GHC.Base.pure (pair (cons x nil) #1)
                      | xs =>
                          let 'pair half1 half2 := halve xs in
                          let cont_4__ arg_5__ :=
                            let 'pair shuffled1 length1 := arg_5__ in
                            let cont_6__ arg_7__ :=
                              let 'pair shuffled2 length2 := arg_7__ in
                              riffle shuffled1 length1 shuffled2 length2 GHC.Base.>>=
                              (fun shuffled => GHC.Base.pure (pair shuffled (length1 GHC.Num.+ length2))) in
                            shuffleLength half2 GHC.Base.>>= cont_6__ in
                          shuffleLength half1 GHC.Base.>>= cont_4__
                      end.
Solve Obligations with (solve_shuffleLength @halve @length_halve).

Definition shuffle {m} {a} `{Control.Monad.Random.Class.MonadRandom m}
   : list a -> m (list a) :=
  GHC.Base.fmap Data.Tuple.fst GHC.Base.∘ shuffleLength.

(* External variables:
     Bool.Sumbool.sumbool_of_bool S cons length list nil op_ze__ op_zp__ op_zszr__
     op_zt__ pair Control.Monad.Random.Class.MonadRandom
     Control.Monad.Random.Class.getRandomR Data.Functor.op_zlzdzg__ Data.Tuple.fst
     GHC.Base.fmap GHC.Base.op_z2218U__ GHC.Base.op_zgzgze__ GHC.Base.op_zlze__
     GHC.Base.pure GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     Nat.div2
*)
