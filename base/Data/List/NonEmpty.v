(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Functor.
Require Data.OldList.
Require Data.Ord.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Midamble *)

Definition NonEmpty_foldr1 {a} (f : a -> a -> a) (x: GHC.Base.NonEmpty a) : a :=
  match x with
    | GHC.Base.NEcons a as_ => List.fold_right f a as_
  end.

Definition NonEmpty_maximum {a} `{GHC.Base.Ord a} (x:GHC.Base.NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.max x.

Definition NonEmpty_minimum {a} `{GHC.Base.Ord a} (x:GHC.Base.NonEmpty a) : a :=
  NonEmpty_foldr1 GHC.Base.min x.

Definition toList {a} : GHC.Base.NonEmpty a -> list a :=
  fun arg_0__ => match arg_0__ with | GHC.Base.NEcons a as_ => cons a as_ end.


Definition List_size {a} : list a -> nat :=
List.fold_right (fun x y => S y) O .
Definition NonEmpty_size {a} : GHC.Base.NonEmpty a -> nat :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons _ xs => 1 + List_size xs
    end.

Program Fixpoint insertBy {a} (cmp: a -> a -> comparison) (x : a)
        (xs : GHC.Base.NonEmpty a) {measure (NonEmpty_size xs)} : GHC.Base.NonEmpty a :=
  match xs with
  | GHC.Base.NEcons x nil => GHC.Base.NEcons x nil
  | (GHC.Base.NEcons y ((cons y1 ys') as ys)) =>
    match cmp x y with
    | Gt  => GHC.Base.NEcons y (toList (insertBy cmp x (GHC.Base.NEcons y1 ys')))
    | _   => GHC.Base.NEcons x ys
    end
  end.

Program Fixpoint insertBy' {a} (cmp: a -> a -> comparison) (x : a)
        (xs : list a) {measure (List_size xs)} : GHC.Base.NonEmpty a :=
  match xs with
  | nil => GHC.Base.NEcons x nil
  | cons x nil => GHC.Base.NEcons x nil
  | (cons y ((cons y1 ys') as ys)) =>
    match cmp x y with
    | Gt  => GHC.Base.NEcons y (toList (insertBy' cmp x (cons y1 ys')))
    | _   => GHC.Base.NEcons x ys
    end
  end.


Definition insert {a} `{GHC.Base.Ord a} : a ->  GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  insertBy GHC.Base.compare.

Definition sortBy {a} : (a -> a -> comparison) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  fun f ne => match ne with
           | GHC.Base.NEcons x xs => insertBy' f x (Data.OldList.sortBy f xs)
           end.

Definition sort {a} `{GHC.Base.Ord a} : GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
             sortBy GHC.Base.compare.

(* Converted value declarations: *)

Definition length {a} : GHC.Base.NonEmpty a -> GHC.Num.Int :=
  fun '(GHC.Base.NEcons _ xs) => #1 GHC.Num.+ Data.Foldable.length xs.

Definition xor : GHC.Base.NonEmpty bool -> bool :=
  fun '(GHC.Base.NEcons x xs) =>
    let xor' :=
      fun arg_1__ arg_2__ =>
        match arg_1__, arg_2__ with
        | true, y => negb y
        | false, y => y
        end in
    Data.Foldable.foldr xor' x xs.

(* Skipping definition `Data.List.NonEmpty.unfold' *)

Definition nonEmpty {a} : list a -> option (GHC.Base.NonEmpty a) :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons a as_ => Some (GHC.Base.NEcons a as_)
    end.

Definition uncons {a}
   : GHC.Base.NonEmpty a -> (a * option (GHC.Base.NonEmpty a))%type :=
  fun '(GHC.Base.NEcons a as_) => pair a (nonEmpty as_).

(* Skipping definition `Data.List.NonEmpty.unfoldr' *)

Definition head {a} : GHC.Base.NonEmpty a -> a :=
  fun '(GHC.Base.NEcons a _) => a.

Definition tail {a} : GHC.Base.NonEmpty a -> list a :=
  fun '(GHC.Base.NEcons _ as_) => as_.

(* Skipping definition `Data.List.NonEmpty.last' *)

(* Skipping definition `Data.List.NonEmpty.init' *)

Definition op_zlzb__ {a} : a -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | a, GHC.Base.NEcons b bs => GHC.Base.NEcons a (cons b bs)
    end.

Notation "'_<|_'" := (op_zlzb__).

Infix "<|" := (_<|_) (at level 99).

Definition cons_ {a} : a -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  _<|_.

(* Skipping definition `Data.List.NonEmpty.sort' *)

(* Skipping definition `Data.List.NonEmpty.fromList' *)

(* Skipping definition `Data.List.NonEmpty.toList' *)

(* Skipping definition `Data.List.NonEmpty.lift' *)

Definition map {a} {b}
   : (a -> b) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, GHC.Base.NEcons a as_ => GHC.Base.NEcons (f a) (GHC.Base.fmap f as_)
    end.

(* Skipping definition `Data.List.NonEmpty.inits' *)

(* Skipping definition `Data.List.NonEmpty.tails' *)

(* Skipping definition `Data.List.NonEmpty.insert' *)

(* Skipping definition `Data.List.NonEmpty.some1' *)

(* Skipping definition `Data.List.NonEmpty.scanl' *)

(* Skipping definition `Data.List.NonEmpty.scanr' *)

(* Skipping definition `Data.List.NonEmpty.scanl1' *)

(* Skipping definition `Data.List.NonEmpty.scanr1' *)

(* Skipping definition `Data.List.NonEmpty.intersperse' *)

(* Skipping definition `Data.List.NonEmpty.iterate' *)

(* Skipping definition `Data.List.NonEmpty.cycle' *)

(* Skipping definition `Data.List.NonEmpty.reverse' *)

(* Skipping definition `Data.List.NonEmpty.repeat' *)

Definition take {a} : GHC.Num.Int -> GHC.Base.NonEmpty a -> list a :=
  fun n => GHC.List.take n GHC.Base.∘ toList.

Definition drop {a} : GHC.Num.Int -> GHC.Base.NonEmpty a -> list a :=
  fun n => GHC.List.drop n GHC.Base.∘ toList.

Definition splitAt {a}
   : GHC.Num.Int -> GHC.Base.NonEmpty a -> (list a * list a)%type :=
  fun n => GHC.List.splitAt n GHC.Base.∘ toList.

Definition takeWhile {a} : (a -> bool) -> GHC.Base.NonEmpty a -> list a :=
  fun p => GHC.List.takeWhile p GHC.Base.∘ toList.

Definition dropWhile {a} : (a -> bool) -> GHC.Base.NonEmpty a -> list a :=
  fun p => GHC.List.dropWhile p GHC.Base.∘ toList.

Definition span {a}
   : (a -> bool) -> GHC.Base.NonEmpty a -> (list a * list a)%type :=
  fun p => GHC.List.span p GHC.Base.∘ toList.

Definition break {a}
   : (a -> bool) -> GHC.Base.NonEmpty a -> (list a * list a)%type :=
  fun p => span (negb GHC.Base.∘ p).

Definition filter {a} : (a -> bool) -> GHC.Base.NonEmpty a -> list a :=
  fun p => GHC.List.filter p GHC.Base.∘ toList.

Definition partition {a}
   : (a -> bool) -> GHC.Base.NonEmpty a -> (list a * list a)%type :=
  fun p => Data.OldList.partition p GHC.Base.∘ toList.

(* Skipping definition `Data.List.NonEmpty.group' *)

(* Skipping definition `Data.List.NonEmpty.groupBy' *)

(* Skipping definition `Data.List.NonEmpty.groupWith' *)

(* Skipping definition `Data.List.NonEmpty.groupAllWith' *)

(* Skipping definition `Data.List.NonEmpty.group1' *)

(* Skipping definition `Data.List.NonEmpty.groupBy1' *)

(* Skipping definition `Data.List.NonEmpty.groupWith1' *)

(* Skipping definition `Data.List.NonEmpty.groupAllWith1' *)

Definition isPrefixOf {a} `{GHC.Base.Eq_ a}
   : list a -> GHC.Base.NonEmpty a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => true
    | cons y ys, GHC.Base.NEcons x xs =>
        andb (y GHC.Base.== x) (Data.OldList.isPrefixOf ys xs)
    end.

(* Skipping definition `Data.List.NonEmpty.op_znzn__' *)

Definition zip {a} {b}
   : GHC.Base.NonEmpty a ->
     GHC.Base.NonEmpty b -> GHC.Base.NonEmpty (a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | GHC.Base.NEcons x xs, GHC.Base.NEcons y ys =>
        GHC.Base.NEcons (pair x y) (GHC.List.zip xs ys)
    end.

Definition zipWith {a} {b} {c}
   : (a -> b -> c) ->
     GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b -> GHC.Base.NonEmpty c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, GHC.Base.NEcons x xs, GHC.Base.NEcons y ys =>
        GHC.Base.NEcons (f x y) (GHC.List.zipWith f xs ys)
    end.

Definition unzip {f} {a} {b} `{GHC.Base.Functor f}
   : f (a * b)%type -> (f a * f b)%type :=
  fun xs =>
    pair (Data.Tuple.fst Data.Functor.<$> xs) (Data.Tuple.snd Data.Functor.<$> xs).

Definition nubBy {a}
   : (a -> a -> bool) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | eq, GHC.Base.NEcons a as_ =>
        GHC.Base.NEcons a (Data.OldList.nubBy eq (GHC.List.filter (fun b =>
                                                                     negb (eq a b)) as_))
    end.

Definition nub {a} `{GHC.Base.Eq_ a}
   : GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  nubBy _GHC.Base.==_.

(* Skipping definition `Data.List.NonEmpty.transpose' *)

(* Skipping definition `Data.List.NonEmpty.sortBy' *)

Definition sortWith {o} {a} `{GHC.Base.Ord o}
   : (a -> o) -> GHC.Base.NonEmpty a -> GHC.Base.NonEmpty a :=
  sortBy GHC.Base.∘ Data.Ord.comparing.

Module Notations.
Notation "'_Data.List.NonEmpty.<|_'" := (op_zlzb__).
Infix "Data.List.NonEmpty.<|" := (_<|_) (at level 99).
End Notations.

(* External variables:
     None Some andb bool cons false list negb nil op_zt__ option pair sortBy toList
     true Data.Foldable.foldr Data.Foldable.length Data.Functor.op_zlzdzg__
     Data.OldList.isPrefixOf Data.OldList.nubBy Data.OldList.partition
     Data.Ord.comparing Data.Tuple.fst Data.Tuple.snd GHC.Base.Eq_ GHC.Base.Functor
     GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.Ord GHC.Base.fmap
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.List.drop GHC.List.dropWhile
     GHC.List.filter GHC.List.span GHC.List.splitAt GHC.List.take GHC.List.takeWhile
     GHC.List.zip GHC.List.zipWith GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__
*)
