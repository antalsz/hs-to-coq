(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require Data.Functor.Const.
Require GHC.Base.
Require GHC.Tuple.

(* Converted type declarations: *)

Record Bifunctor__Dict p := Bifunctor__Dict_Build {
  bimap__ : forall {a} {b} {c} {d}, (a -> b) -> (c -> d) -> p a c -> p b d ;
  first__ : forall {a} {b} {c}, (a -> b) -> p a c -> p b c ;
  second__ : forall {b} {c} {a}, (b -> c) -> p a b -> p a c }.

Definition Bifunctor p :=
  forall r__, (Bifunctor__Dict p -> r__) -> r__.
Existing Class Bifunctor.

Definition bimap `{g__0__ : Bifunctor p}
   : forall {a} {b} {c} {d}, (a -> b) -> (c -> d) -> p a c -> p b d :=
  g__0__ _ (bimap__ p).

Definition first `{g__0__ : Bifunctor p}
   : forall {a} {b} {c}, (a -> b) -> p a c -> p b c :=
  g__0__ _ (first__ p).

Definition second `{g__0__ : Bifunctor p}
   : forall {b} {c} {a}, (b -> c) -> p a b -> p a c :=
  g__0__ _ (second__ p).

(* Converted value declarations: *)

Local Definition Bifunctor__pair_type_bimap
   : forall {a} {b} {c} {d},
     (a -> b) -> (c -> d) -> GHC.Tuple.pair_type a c -> GHC.Tuple.pair_type b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair a b => pair (f a) (g b)
      end.

Local Definition Bifunctor__pair_type_first
   : forall {a} {b} {c},
     (a -> b) -> GHC.Tuple.pair_type a c -> GHC.Tuple.pair_type b c :=
  fun {a} {b} {c} => fun f => Bifunctor__pair_type_bimap f GHC.Base.id.

Local Definition Bifunctor__pair_type_second
   : forall {b} {c} {a},
     (b -> c) -> GHC.Tuple.pair_type a b -> GHC.Tuple.pair_type a c :=
  fun {b} {c} {a} => Bifunctor__pair_type_bimap GHC.Base.id.

Program Instance Bifunctor__pair_type : Bifunctor GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__pair_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__pair_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__pair_type_second |}.

Local Definition Bifunctor__triple_type_bimap {inst_x1}
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) ->
     (GHC.Tuple.triple_type inst_x1) a c -> (GHC.Tuple.triple_type inst_x1) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair x1 a) b => pair (pair x1 (f a)) (g b)
      end.

Local Definition Bifunctor__triple_type_first {inst_x1}
   : forall {a} {b} {c},
     (a -> b) ->
     (GHC.Tuple.triple_type inst_x1) a c -> (GHC.Tuple.triple_type inst_x1) b c :=
  fun {a} {b} {c} => fun f => Bifunctor__triple_type_bimap f GHC.Base.id.

Local Definition Bifunctor__triple_type_second {inst_x1}
   : forall {b} {c} {a},
     (b -> c) ->
     (GHC.Tuple.triple_type inst_x1) a b -> (GHC.Tuple.triple_type inst_x1) a c :=
  fun {b} {c} {a} => Bifunctor__triple_type_bimap GHC.Base.id.

Program Instance Bifunctor__triple_type {x1}
   : Bifunctor (GHC.Tuple.triple_type x1) :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__triple_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__triple_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__triple_type_second |}.

Local Definition Bifunctor__quad_type_bimap {inst_x1} {inst_x2}
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) a c ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair x1 x2) a) b => pair (pair (pair x1 x2) (f a)) (g b)
      end.

Local Definition Bifunctor__quad_type_first {inst_x1} {inst_x2}
   : forall {a} {b} {c},
     (a -> b) ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) a c ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) b c :=
  fun {a} {b} {c} => fun f => Bifunctor__quad_type_bimap f GHC.Base.id.

Local Definition Bifunctor__quad_type_second {inst_x1} {inst_x2}
   : forall {b} {c} {a},
     (b -> c) ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) a b ->
     (GHC.Tuple.quad_type inst_x1 inst_x2) a c :=
  fun {b} {c} {a} => Bifunctor__quad_type_bimap GHC.Base.id.

Program Instance Bifunctor__quad_type {x1} {x2}
   : Bifunctor (GHC.Tuple.quad_type x1 x2) :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__quad_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__quad_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__quad_type_second |}.

Local Definition Bifunctor__quint_type_bimap {inst_x1} {inst_x2} {inst_x3}
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) a c ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair x1 x2) x3) a) b =>
          pair (pair (pair (pair x1 x2) x3) (f a)) (g b)
      end.

Local Definition Bifunctor__quint_type_first {inst_x1} {inst_x2} {inst_x3}
   : forall {a} {b} {c},
     (a -> b) ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) a c ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) b c :=
  fun {a} {b} {c} => fun f => Bifunctor__quint_type_bimap f GHC.Base.id.

Local Definition Bifunctor__quint_type_second {inst_x1} {inst_x2} {inst_x3}
   : forall {b} {c} {a},
     (b -> c) ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) a b ->
     (GHC.Tuple.quint_type inst_x1 inst_x2 inst_x3) a c :=
  fun {b} {c} {a} => Bifunctor__quint_type_bimap GHC.Base.id.

Program Instance Bifunctor__quint_type {x1} {x2} {x3}
   : Bifunctor (GHC.Tuple.quint_type x1 x2 x3) :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__quint_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__quint_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__quint_type_second |}.

Local Definition Bifunctor__sext_type_bimap {inst_x1} {inst_x2} {inst_x3}
  {inst_x4}
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) a c ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair x1 x2) x3) x4) a) b =>
          pair (pair (pair (pair (pair x1 x2) x3) x4) (f a)) (g b)
      end.

Local Definition Bifunctor__sext_type_first {inst_x1} {inst_x2} {inst_x3}
  {inst_x4}
   : forall {a} {b} {c},
     (a -> b) ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) a c ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) b c :=
  fun {a} {b} {c} => fun f => Bifunctor__sext_type_bimap f GHC.Base.id.

Local Definition Bifunctor__sext_type_second {inst_x1} {inst_x2} {inst_x3}
  {inst_x4}
   : forall {b} {c} {a},
     (b -> c) ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) a b ->
     (GHC.Tuple.sext_type inst_x1 inst_x2 inst_x3 inst_x4) a c :=
  fun {b} {c} {a} => Bifunctor__sext_type_bimap GHC.Base.id.

Program Instance Bifunctor__sext_type {x1} {x2} {x3} {x4}
   : Bifunctor (GHC.Tuple.sext_type x1 x2 x3 x4) :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__sext_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__sext_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__sext_type_second |}.

Local Definition Bifunctor__sept_type_bimap {inst_x1} {inst_x2} {inst_x3}
  {inst_x4} {inst_x5}
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a c ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair (pair x1 x2) x3) x4) x5) a) b =>
          pair (pair (pair (pair (pair (pair x1 x2) x3) x4) x5) (f a)) (g b)
      end.

Local Definition Bifunctor__sept_type_first {inst_x1} {inst_x2} {inst_x3}
  {inst_x4} {inst_x5}
   : forall {a} {b} {c},
     (a -> b) ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a c ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) b c :=
  fun {a} {b} {c} => fun f => Bifunctor__sept_type_bimap f GHC.Base.id.

Local Definition Bifunctor__sept_type_second {inst_x1} {inst_x2} {inst_x3}
  {inst_x4} {inst_x5}
   : forall {b} {c} {a},
     (b -> c) ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a b ->
     (GHC.Tuple.sept_type inst_x1 inst_x2 inst_x3 inst_x4 inst_x5) a c :=
  fun {b} {c} {a} => Bifunctor__sept_type_bimap GHC.Base.id.

Program Instance Bifunctor__sept_type {x1} {x2} {x3} {x4} {x5}
   : Bifunctor (GHC.Tuple.sept_type x1 x2 x3 x4 x5) :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__sept_type_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__sept_type_first ;
           second__ := fun {b} {c} {a} => Bifunctor__sept_type_second |}.

Local Definition Bifunctor__Either_bimap
   : forall {a} {b} {c} {d},
     (a -> b) -> (c -> d) -> Data.Either.Either a c -> Data.Either.Either b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Either.Left a => Data.Either.Left (f a)
      | _, g, Data.Either.Right b => Data.Either.Right (g b)
      end.

Local Definition Bifunctor__Either_first
   : forall {a} {b} {c},
     (a -> b) -> Data.Either.Either a c -> Data.Either.Either b c :=
  fun {a} {b} {c} => fun f => Bifunctor__Either_bimap f GHC.Base.id.

Local Definition Bifunctor__Either_second
   : forall {b} {c} {a},
     (b -> c) -> Data.Either.Either a b -> Data.Either.Either a c :=
  fun {b} {c} {a} => Bifunctor__Either_bimap GHC.Base.id.

Program Instance Bifunctor__Either : Bifunctor Data.Either.Either :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__Either_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__Either_first ;
           second__ := fun {b} {c} {a} => Bifunctor__Either_second |}.

Local Definition Bifunctor__Const_bimap
   : forall {a} {b} {c} {d},
     (a -> b) ->
     (c -> d) -> Data.Functor.Const.Const a c -> Data.Functor.Const.Const b d :=
  fun {a} {b} {c} {d} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Functor.Const.Mk_Const a => Data.Functor.Const.Mk_Const (f a)
      end.

Local Definition Bifunctor__Const_first
   : forall {a} {b} {c},
     (a -> b) -> Data.Functor.Const.Const a c -> Data.Functor.Const.Const b c :=
  fun {a} {b} {c} => fun f => Bifunctor__Const_bimap f GHC.Base.id.

Local Definition Bifunctor__Const_second
   : forall {b} {c} {a},
     (b -> c) -> Data.Functor.Const.Const a b -> Data.Functor.Const.Const a c :=
  fun {b} {c} {a} => Bifunctor__Const_bimap GHC.Base.id.

Program Instance Bifunctor__Const : Bifunctor Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| bimap__ := fun {a} {b} {c} {d} => Bifunctor__Const_bimap ;
           first__ := fun {a} {b} {c} => Bifunctor__Const_first ;
           second__ := fun {b} {c} {a} => Bifunctor__Const_second |}.

(* Skipping instance `Data.Bifunctor.Bifunctor__K1' of class
   `Data.Bifunctor.Bifunctor' *)

(* External variables:
     pair Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const GHC.Base.id
     GHC.Tuple.pair_type GHC.Tuple.quad_type GHC.Tuple.quint_type GHC.Tuple.sept_type
     GHC.Tuple.sext_type GHC.Tuple.triple_type
*)
