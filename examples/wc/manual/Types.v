(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Bits.
Require Import GHC.Base.
Require Import GHC.Char.
Require GHC.Err.
Require Import GHC.Num.
Require GHC.Unicode.

Locate newline.


(* Converted type declarations: *)

Inductive Pair a : Type := | Mk_Pair : a -> a -> Pair a.

Inductive CharType : Type := | IsSpace : CharType |  NotSpace : CharType.

Inductive Flux : Type
  := | Mk_Flux : CharType -> Int -> CharType -> Flux
     |  Unknown : Flux.

Inductive Counts : Type
  := | Mk_Counts (charCount : Int) (wordCount : Flux) (lineCount : Int) : Counts.

Arguments Mk_Pair {_} _ _.

Instance Default__CharType : GHC.Err.Default CharType :=
  GHC.Err.Build_Default _ IsSpace.

Instance Default__Flux : GHC.Err.Default Flux :=
  GHC.Err.Build_Default _ Unknown.

Instance Default__Counts : GHC.Err.Default Counts :=
  GHC.Err.Build_Default _ (Mk_Counts GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Definition charCount (arg_0__ : Counts) :=
  let 'Mk_Counts charCount _ _ := arg_0__ in
  charCount.

Definition lineCount (arg_0__ : Counts) :=
  let 'Mk_Counts _ _ lineCount := arg_0__ in
  lineCount.

Definition wordCount (arg_0__ : Counts) :=
  let 'Mk_Counts _ wordCount _ := arg_0__ in
  wordCount.

Axiom c2w : Char -> N.

(* Converted value declarations: *)

Definition getFlux : Flux -> Int :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Flux _ n _ => n
    | _ => fromInteger 0
    end.

Definition toTuple : Counts -> (Int * Int * Int)%type :=
  fun '(Mk_Counts charCount wordCount lineCount) =>
    pair (pair charCount (getFlux wordCount)) lineCount.

Definition fromTuple : (Int * Int * Int)%type -> Counts :=
  fun '(pair (pair cs ws) ls) => Mk_Counts cs (Mk_Flux IsSpace ws IsSpace) ls.



Definition flux : Char -> Flux :=
  fun c =>
    if Unicode.isSpace c : bool then Mk_Flux IsSpace (fromInteger 0) IsSpace else
    Mk_Flux NotSpace (fromInteger 1) NotSpace.

Definition countChar : Char -> Counts :=
  fun c =>
    Mk_Counts (fromInteger 1) (flux c) (if (c == Char.newline) : bool
               then fromInteger 1
               else fromInteger 0).

Definition countByte : Char -> Counts :=
  fun c =>
    Mk_Counts (fromInteger 1) (flux c) (if (c == Char.newline) : bool
               then fromInteger 1
               else fromInteger 0).

(* Skipping all instances of class `GHC.Show.Show', including
   `Types.Show__Pair' *)

Local Definition Eq___Pair_op_zeze__ {inst_a} `{Eq_ inst_a}
   : Pair inst_a -> Pair inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Pair a1 a2, Mk_Pair b1 b2 => (andb ((a1 == b1)) ((a2 == b2)))
    end.

Local Definition Eq___Pair_op_zsze__ {inst_a} `{Eq_ inst_a}
   : Pair inst_a -> Pair inst_a -> bool :=
  fun x y => negb (Eq___Pair_op_zeze__ x y).

Program Instance Eq___Pair {a} `{Eq_ a} : Eq_ (Pair a) :=
  fun _ k__ =>
    k__ {| op_zeze____ := Eq___Pair_op_zeze__ ;
           op_zsze____ := Eq___Pair_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Types.Show__CharType' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Types.Show__Flux' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Types.Show__Counts' *)

Local Definition Semigroup__Flux_op_zlzlzgzg__ : Flux -> Flux -> Flux :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Unknown, x => x
    | x, Unknown => x
    | Mk_Flux l n NotSpace, Mk_Flux NotSpace n' r =>
        Mk_Flux l (n + n' - fromInteger 1) r
    | Mk_Flux l n _, Mk_Flux _ n' r => Mk_Flux l (n + n') r
    end.

Program Instance Semigroup__Flux : Semigroup Flux :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__Flux_op_zlzlzgzg__ |}.

Local Definition Monoid__Flux_mappend : Flux -> Flux -> Flux :=
  _<<>>_.

Local Definition Monoid__Flux_mempty : Flux := Unknown.

Local Definition Monoid__Flux_mconcat : list Flux -> Flux :=
  foldr Monoid__Flux_mappend Monoid__Flux_mempty.

Program Instance Monoid__Flux : Monoid Flux :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__Flux_mappend ;
           mconcat__ := Monoid__Flux_mconcat ;
           mempty__ := Monoid__Flux_mempty |}.

Local Definition Semigroup__Counts_op_zlzlzgzg__ : Counts -> Counts -> Counts :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Counts a b c, Mk_Counts a' b' c' => Mk_Counts (a + a') (b <<>> b') (c + c')
    end.

Program Instance Semigroup__Counts : Semigroup Counts :=
  fun _ k__ => k__ {| op_zlzlzgzg____ := Semigroup__Counts_op_zlzlzgzg__ |}.

Local Definition Monoid__Counts_mappend : Counts -> Counts -> Counts :=
  _<<>>_.

Local Definition Monoid__Counts_mempty : Counts :=
  Mk_Counts (fromInteger 0) mempty (fromInteger 0).

Local Definition Monoid__Counts_mconcat : list Counts -> Counts :=
  foldr Monoid__Counts_mappend Monoid__Counts_mempty.

Program Instance Monoid__Counts : Monoid Counts :=
  fun _ k__ =>
    k__ {| mappend__ := Monoid__Counts_mappend ;
           mconcat__ := Monoid__Counts_mconcat ;
           mempty__ := Monoid__Counts_mempty |}.


Definition countByteUTF8 : Char -> Counts :=
  fun c =>
    let bitAt := Data.Bits.testBit (c2w c) in
    let isContinutation :=
      andb (bitAt (fromInteger 7)) (negb (bitAt (fromInteger 6))) in
    if isContinutation  then mempty else
    Mk_Counts (if isContinutation 
               then fromInteger 0
               else fromInteger 1) 
              (if isContinutation 
               then mempty
               else flux c) 
              (if (c == Char.newline) 
               then fromInteger 1
               else fromInteger 0).


(* External variables:
     Char Eq_ Int Monoid N Semigroup andb bool foldr fromInteger list mappend__
     mconcat__ mempty mempty__ negb op_zeze__ op_zeze____ op_zlzlzgzg__
     op_zlzlzgzg____ op_zm__ op_zp__ op_zsze____ op_zt__ pair Data.Bits.testBit
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.default GHC.Err.patternFailure
*)
