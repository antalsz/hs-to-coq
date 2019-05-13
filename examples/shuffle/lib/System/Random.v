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

Require GHC.Base.
Require GHC.Enum.
Require GHC.Num.
Require GHC.Real.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record RandomGen__Dict g := RandomGen__Dict_Build {
  genRange__ : g -> (GHC.Num.Int * GHC.Num.Int)%type ;
  next__ : g -> (GHC.Num.Int * g)%type ;
  split__ : g -> (g * g)%type }.

Definition RandomGen g :=
  forall r__, (RandomGen__Dict g -> r__) -> r__.

Existing Class RandomGen.

Definition genRange `{g__0__ : RandomGen g}
   : g -> (GHC.Num.Int * GHC.Num.Int)%type :=
  g__0__ _ (genRange__ g).

Definition next `{g__0__ : RandomGen g} : g -> (GHC.Num.Int * g)%type :=
  g__0__ _ (next__ g).

Definition split `{g__0__ : RandomGen g} : g -> (g * g)%type :=
  g__0__ _ (split__ g).

Record Random__Dict a := Random__Dict_Build {
  random__ : forall {g}, forall `{RandomGen g}, g -> (a * g)%type ;
  randomR__ : forall {g},
  forall `{RandomGen g}, (a * a)%type -> g -> (a * g)%type }.

Definition Random a :=
  forall r__, (Random__Dict a -> r__) -> r__.

Existing Class Random.

Definition random `{g__0__ : Random a}
   : forall {g}, forall `{RandomGen g}, g -> (a * g)%type :=
  g__0__ _ (random__ a).

Definition randomR `{g__0__ : Random a}
   : forall {g}, forall `{RandomGen g}, (a * a)%type -> g -> (a * g)%type :=
  g__0__ _ (randomR__ a).

(* Converted value declarations: *)

Definition stdRange : (GHC.Num.Int * GHC.Num.Int)%type :=
  pair #1 #2147483562.

Axiom randomIvalInteger : forall {g} {a},
                          forall `{RandomGen g} `{GHC.Num.Num a},
                          (GHC.Num.Integer * GHC.Num.Integer)%type -> g -> (a * g)%type.

Definition randomIvalIntegral {g} {a} `{RandomGen g} `{GHC.Real.Integral a}
   : (a * a)%type -> g -> (a * g)%type :=
  fun '(pair l h) =>
    randomIvalInteger (pair (GHC.Real.toInteger l) (GHC.Real.toInteger h)).

Definition randomBounded {g} {a} `{RandomGen g} `{Random a} `{GHC.Enum.Bounded
  a}
   : g -> (a * g)%type :=
  randomR (pair GHC.Enum.minBound GHC.Enum.maxBound).

(* Skipping all instances of class `GHC.Read.Read', including
   `System.Random.Read__StdGen' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `System.Random.Show__StdGen' *)

(* Skipping instance `System.Random.RandomGen__StdGen' of class
   `System.Random.RandomGen' *)

(* Skipping instance `System.Random.Random__CDouble' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CFloat' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Float' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Double' of class
   `System.Random.Random' *)

Local Definition Random__bool_randomR
   : forall {g},
     forall `{RandomGen g}, (bool * bool)%type -> g -> (bool * g)%type :=
  fun {g} `{RandomGen g} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | pair a b, g =>
          let int2Bool : GHC.Num.Int -> bool :=
            fun '(num_3__) => if num_3__ GHC.Base.== #0 : bool then false else true in
          let bool2Int : bool -> GHC.Num.Integer :=
            fun arg_6__ => match arg_6__ with | false => #0 | true => #1 end in
          let 'pair x g' := (randomIvalInteger (pair (bool2Int a) (bool2Int b)) g) in
          pair (int2Bool x) g'
      end.

Local Definition Random__bool_random
   : forall {g}, forall `{RandomGen g}, g -> (bool * g)%type :=
  fun {g} `{RandomGen g} =>
    fun g => Random__bool_randomR (pair GHC.Enum.minBound GHC.Enum.maxBound) g.

Program Instance Random__bool : Random bool :=
  fun _ k__ =>
    k__ {| random__ := fun {g} `{RandomGen g} => Random__bool_random ;
           randomR__ := fun {g} `{RandomGen g} => Random__bool_randomR |}.

(* Skipping instance `System.Random.Random__Char' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CUIntMax' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CIntMax' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CUIntPtr' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CIntPtr' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CULLong' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CLLong' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CSigAtomic' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CWchar' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CSize' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CPtrdiff' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CULong' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CLong' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CUInt' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CInt' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CUShort' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CShort' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CUChar' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CSChar' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__CChar' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Word64' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Word32' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Word16' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Word8' of class
   `System.Random.Random' *)

Local Definition Random__Word_randomR
   : forall {g},
     forall `{RandomGen g},
     (GHC.Num.Word * GHC.Num.Word)%type -> g -> (GHC.Num.Word * g)%type :=
  fun {g} `{RandomGen g} => randomIvalIntegral.

Local Definition Random__Word_random
   : forall {g}, forall `{RandomGen g}, g -> (GHC.Num.Word * g)%type :=
  fun {g} `{RandomGen g} =>
    Random__Word_randomR (pair GHC.Enum.minBound GHC.Enum.maxBound).

Program Instance Random__Word : Random GHC.Num.Word :=
  fun _ k__ =>
    k__ {| random__ := fun {g} `{RandomGen g} => Random__Word_random ;
           randomR__ := fun {g} `{RandomGen g} => Random__Word_randomR |}.

(* Skipping instance `System.Random.Random__Int64' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Int32' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Int16' of class
   `System.Random.Random' *)

(* Skipping instance `System.Random.Random__Int8' of class
   `System.Random.Random' *)

Local Definition Random__Int_randomR
   : forall {g},
     forall `{RandomGen g},
     (GHC.Num.Int * GHC.Num.Int)%type -> g -> (GHC.Num.Int * g)%type :=
  fun {g} `{RandomGen g} => randomIvalIntegral.

Local Definition Random__Int_random
   : forall {g}, forall `{RandomGen g}, g -> (GHC.Num.Int * g)%type :=
  fun {g} `{RandomGen g} =>
    Random__Int_randomR (pair GHC.Enum.minBound GHC.Enum.maxBound).

Program Instance Random__Int : Random GHC.Num.Int :=
  fun _ k__ =>
    k__ {| random__ := fun {g} `{RandomGen g} => Random__Int_random ;
           randomR__ := fun {g} `{RandomGen g} => Random__Int_randomR |}.

Local Definition Random__Integer_randomR
   : forall {g},
     forall `{RandomGen g},
     (GHC.Num.Integer * GHC.Num.Integer)%type -> g -> (GHC.Num.Integer * g)%type :=
  fun {g} `{RandomGen g} => fun ival g => randomIvalInteger ival g.

Local Definition Random__Integer_random
   : forall {g}, forall `{RandomGen g}, g -> (GHC.Num.Integer * g)%type :=
  fun {g} `{RandomGen g} =>
    fun g =>
      Random__Integer_randomR (pair (GHC.Real.toInteger
                                     (GHC.Enum.minBound : GHC.Num.Int)) (GHC.Real.toInteger
                                     (GHC.Enum.maxBound : GHC.Num.Int))) g.

Program Instance Random__Integer : Random GHC.Num.Integer :=
  fun _ k__ =>
    k__ {| random__ := fun {g} `{RandomGen g} => Random__Integer_random ;
           randomR__ := fun {g} `{RandomGen g} => Random__Integer_randomR |}.

(* External variables:
     bool false op_zt__ pair true GHC.Base.op_zeze__ GHC.Enum.Bounded
     GHC.Enum.maxBound GHC.Enum.minBound GHC.Num.Int GHC.Num.Integer GHC.Num.Num
     GHC.Num.Word GHC.Num.fromInteger GHC.Real.Integral GHC.Real.toInteger
*)
