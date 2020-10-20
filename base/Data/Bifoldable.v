(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Either.
Require Data.Functor.Const.
Require Data.Monoid.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Record Bifoldable__Dict p := Bifoldable__Dict_Build {
  bifold__ : forall {m}, forall `{GHC.Base.Monoid m}, p m m -> m ;
  bifoldMap__ : forall {m} {a} {b},
  forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> p a b -> m ;
  bifoldl__ : forall {c} {a} {b},
  (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c ;
  bifoldr__ : forall {a} {c} {b},
  (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c }.

Definition Bifoldable p :=
  forall r__, (Bifoldable__Dict p -> r__) -> r__.
Existing Class Bifoldable.

Definition bifold `{g__0__ : Bifoldable p}
   : forall {m}, forall `{GHC.Base.Monoid m}, p m m -> m :=
  g__0__ _ (bifold__ p).

Definition bifoldMap `{g__0__ : Bifoldable p}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m}, (a -> m) -> (b -> m) -> p a b -> m :=
  g__0__ _ (bifoldMap__ p).

Definition bifoldl `{g__0__ : Bifoldable p}
   : forall {c} {a} {b}, (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c :=
  g__0__ _ (bifoldl__ p).

Definition bifoldr `{g__0__ : Bifoldable p}
   : forall {a} {c} {b}, (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c :=
  g__0__ _ (bifoldr__ p).

(* Converted value declarations: *)

Local Definition Bifoldable__pair_type_bifoldMap
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> GHC.Tuple.pair_type a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair a b => GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__pair_type_bifold
   : forall {m}, forall `{GHC.Base.Monoid m}, GHC.Tuple.pair_type m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__pair_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__pair_type_bifoldl
   : forall {c} {a} {b},
     (c -> a -> c) -> (c -> b -> c) -> c -> GHC.Tuple.pair_type a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__pair_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__pair_type_bifoldr
   : forall {a} {c} {b},
     (a -> c -> c) -> (b -> c -> c) -> c -> GHC.Tuple.pair_type a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__pair_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__pair_type : Bifoldable GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__pair_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__pair_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__pair_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__pair_type_bifoldr |}.

Local Definition Bifoldable__Const_bifoldMap
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> Data.Functor.Const.Const a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Functor.Const.Mk_Const a => f a
      end.

Local Definition Bifoldable__Const_bifold
   : forall {m}, forall `{GHC.Base.Monoid m}, Data.Functor.Const.Const m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__Const_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__Const_bifoldl
   : forall {c} {a} {b},
     (c -> a -> c) -> (c -> b -> c) -> c -> Data.Functor.Const.Const a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Const_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                    (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                     GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                        GHC.Base.∘
                                                                                        (Data.SemigroupInternal.Mk_Endo
                                                                                         GHC.Base.∘
                                                                                         GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__Const_bifoldr
   : forall {a} {c} {b},
     (a -> c -> c) -> (b -> c -> c) -> c -> Data.Functor.Const.Const a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Const_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__Const : Bifoldable Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} => Bifoldable__Const_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__Const_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__Const_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__Const_bifoldr |}.

(* Skipping instance `Data.Bifoldable.Bifoldable__K1' of class
   `Data.Bifoldable.Bifoldable' *)

Local Definition Bifoldable__triple_type_bifoldMap {inst_x}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> (GHC.Tuple.triple_type inst_x) a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair _ a) b => GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__triple_type_bifold {inst_x}
   : forall {m},
     forall `{GHC.Base.Monoid m}, (GHC.Tuple.triple_type inst_x) m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__triple_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__triple_type_bifoldl {inst_x}
   : forall {c} {a} {b},
     (c -> a -> c) ->
     (c -> b -> c) -> c -> (GHC.Tuple.triple_type inst_x) a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__triple_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                          (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                           GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__triple_type_bifoldr {inst_x}
   : forall {a} {c} {b},
     (a -> c -> c) ->
     (b -> c -> c) -> c -> (GHC.Tuple.triple_type inst_x) a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__triple_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__triple_type {x}
   : Bifoldable (GHC.Tuple.triple_type x) :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__triple_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__triple_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__triple_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__triple_type_bifoldr |}.

Local Definition Bifoldable__quad_type_bifoldMap {inst_x} {inst_y}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> (GHC.Tuple.quad_type inst_x inst_y) a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair _ _) a) b => GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__quad_type_bifold {inst_x} {inst_y}
   : forall {m},
     forall `{GHC.Base.Monoid m}, (GHC.Tuple.quad_type inst_x inst_y) m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__quad_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__quad_type_bifoldl {inst_x} {inst_y}
   : forall {c} {a} {b},
     (c -> a -> c) ->
     (c -> b -> c) -> c -> (GHC.Tuple.quad_type inst_x inst_y) a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__quad_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__quad_type_bifoldr {inst_x} {inst_y}
   : forall {a} {c} {b},
     (a -> c -> c) ->
     (b -> c -> c) -> c -> (GHC.Tuple.quad_type inst_x inst_y) a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__quad_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__quad_type {x} {y}
   : Bifoldable (GHC.Tuple.quad_type x y) :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__quad_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__quad_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__quad_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__quad_type_bifoldr |}.

Local Definition Bifoldable__quint_type_bifoldMap {inst_x} {inst_y} {inst_z}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> (GHC.Tuple.quint_type inst_x inst_y inst_z) a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair _ _) _) a) b => GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__quint_type_bifold {inst_x} {inst_y} {inst_z}
   : forall {m},
     forall `{GHC.Base.Monoid m},
     (GHC.Tuple.quint_type inst_x inst_y inst_z) m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__quint_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__quint_type_bifoldl {inst_x} {inst_y} {inst_z}
   : forall {c} {a} {b},
     (c -> a -> c) ->
     (c -> b -> c) -> c -> (GHC.Tuple.quint_type inst_x inst_y inst_z) a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__quint_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                         (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                          GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__quint_type_bifoldr {inst_x} {inst_y} {inst_z}
   : forall {a} {c} {b},
     (a -> c -> c) ->
     (b -> c -> c) -> c -> (GHC.Tuple.quint_type inst_x inst_y inst_z) a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__quint_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__quint_type {x} {y} {z}
   : Bifoldable (GHC.Tuple.quint_type x y z) :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__quint_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__quint_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__quint_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__quint_type_bifoldr |}.

Local Definition Bifoldable__sext_type_bifoldMap {inst_x} {inst_y} {inst_z}
  {inst_w}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) ->
     (b -> m) -> (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair _ _) _) _) a) b =>
          GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__sext_type_bifold {inst_x} {inst_y} {inst_z}
  {inst_w}
   : forall {m},
     forall `{GHC.Base.Monoid m},
     (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__sext_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__sext_type_bifoldl {inst_x} {inst_y} {inst_z}
  {inst_w}
   : forall {c} {a} {b},
     (c -> a -> c) ->
     (c -> b -> c) ->
     c -> (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__sext_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__sext_type_bifoldr {inst_x} {inst_y} {inst_z}
  {inst_w}
   : forall {a} {c} {b},
     (a -> c -> c) ->
     (b -> c -> c) ->
     c -> (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__sext_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__sext_type {x} {y} {z} {w}
   : Bifoldable (GHC.Tuple.sext_type x y z w) :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__sext_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__sext_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__sext_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__sext_type_bifoldr |}.

Local Definition Bifoldable__sept_type_bifoldMap {inst_x} {inst_y} {inst_z}
  {inst_w} {inst_v}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) ->
     (b -> m) -> (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair (pair _ _) _) _) _) a) b =>
          GHC.Base.mappend (f a) (g b)
      end.

Local Definition Bifoldable__sept_type_bifold {inst_x} {inst_y} {inst_z}
  {inst_w} {inst_v}
   : forall {m},
     forall `{GHC.Base.Monoid m},
     (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__sept_type_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__sept_type_bifoldl {inst_x} {inst_y} {inst_z}
  {inst_w} {inst_v}
   : forall {c} {a} {b},
     (c -> a -> c) ->
     (c -> b -> c) ->
     c -> (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__sept_type_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                         GHC.Base.flip f))
                                       (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                        (Data.SemigroupInternal.Mk_Endo GHC.Base.∘ GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__sept_type_bifoldr {inst_x} {inst_y} {inst_z}
  {inst_w} {inst_v}
   : forall {a} {c} {b},
     (a -> c -> c) ->
     (b -> c -> c) ->
     c -> (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__sept_type_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__sept_type {x} {y} {z} {w} {v}
   : Bifoldable (GHC.Tuple.sept_type x y z w v) :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} =>
             Bifoldable__sept_type_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__sept_type_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__sept_type_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__sept_type_bifoldr |}.

Local Definition Bifoldable__Either_bifoldMap
   : forall {m} {a} {b},
     forall `{GHC.Base.Monoid m},
     (a -> m) -> (b -> m) -> Data.Either.Either a b -> m :=
  fun {m} {a} {b} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Either.Left a => f a
      | _, g, Data.Either.Right b => g b
      end.

Local Definition Bifoldable__Either_bifold
   : forall {m}, forall `{GHC.Base.Monoid m}, Data.Either.Either m m -> m :=
  fun {m} `{GHC.Base.Monoid m} =>
    Bifoldable__Either_bifoldMap GHC.Base.id GHC.Base.id.

Local Definition Bifoldable__Either_bifoldl
   : forall {c} {a} {b},
     (c -> a -> c) -> (c -> b -> c) -> c -> Data.Either.Either a b -> c :=
  fun {c} {a} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Bifoldable__Either_bifoldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                     (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                      GHC.Base.flip f)) (Data.SemigroupInternal.Mk_Dual
                                                                                         GHC.Base.∘
                                                                                         (Data.SemigroupInternal.Mk_Endo
                                                                                          GHC.Base.∘
                                                                                          GHC.Base.flip g)) t)) z.

Local Definition Bifoldable__Either_bifoldr
   : forall {a} {c} {b},
     (a -> c -> c) -> (b -> c -> c) -> c -> Data.Either.Either a b -> c :=
  fun {a} {c} {b} =>
    fun f g z t =>
      Data.SemigroupInternal.appEndo (Bifoldable__Either_bifoldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f)
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo g) t) z.

Program Instance Bifoldable__Either : Bifoldable Data.Either.Either :=
  fun _ k__ =>
    k__ {| bifold__ := fun {m} `{GHC.Base.Monoid m} => Bifoldable__Either_bifold ;
           bifoldMap__ := fun {m} {a} {b} `{GHC.Base.Monoid m} =>
             Bifoldable__Either_bifoldMap ;
           bifoldl__ := fun {c} {a} {b} => Bifoldable__Either_bifoldl ;
           bifoldr__ := fun {a} {c} {b} => Bifoldable__Either_bifoldr |}.

Definition bifoldr' {t} {a} {c} {b} `{Bifoldable t}
   : (a -> c -> c) -> (b -> c -> c) -> c -> t a b -> c :=
  fun f g z0 xs =>
    let g' := fun k x z => k (g x z) in
    let f' := fun k x z => k (f x z) in bifoldl f' g' GHC.Base.id xs z0.

(* Skipping definition `Data.Bifoldable.bifoldr1' *)

Definition bifoldrM {t} {m} {a} {c} {b} `{Bifoldable t} `{GHC.Base.Monad m}
   : (a -> c -> m c) -> (b -> c -> m c) -> c -> t a b -> m c :=
  fun f g z0 xs =>
    let g' := fun k x z => g x z GHC.Base.>>= k in
    let f' := fun k x z => f x z GHC.Base.>>= k in
    bifoldl f' g' GHC.Base.return_ xs z0.

Definition bifoldl' {t} {a} {b} {c} `{Bifoldable t}
   : (a -> b -> a) -> (a -> c -> a) -> a -> t b c -> a :=
  fun f g z0 xs =>
    let g' := fun x k z => k (g z x) in
    let f' := fun x k z => k (f z x) in bifoldr f' g' GHC.Base.id xs z0.

(* Skipping definition `Data.Bifoldable.bifoldl1' *)

Definition bifoldlM {t} {m} {a} {b} {c} `{Bifoldable t} `{GHC.Base.Monad m}
   : (a -> b -> m a) -> (a -> c -> m a) -> a -> t b c -> m a :=
  fun f g z0 xs =>
    let g' := fun x k z => g z x GHC.Base.>>= k in
    let f' := fun x k z => f z x GHC.Base.>>= k in
    bifoldr f' g' GHC.Base.return_ xs z0.

Definition bitraverse_ {t} {f} {a} {c} {b} {d} `{Bifoldable t}
  `{GHC.Base.Applicative f}
   : (a -> f c) -> (b -> f d) -> t a b -> f unit :=
  fun f g =>
    bifoldr (_GHC.Base.*>_ GHC.Base.∘ f) (_GHC.Base.*>_ GHC.Base.∘ g) (GHC.Base.pure
                                                                       tt).

Definition bifor_ {t} {f} {a} {b} {c} {d} `{Bifoldable t} `{GHC.Base.Applicative
  f}
   : t a b -> (a -> f c) -> (b -> f d) -> f unit :=
  fun t f g => bitraverse_ f g t.

Definition bimapM_ {t} {f} {a} {c} {b} {d} `{Bifoldable t}
  `{GHC.Base.Applicative f}
   : (a -> f c) -> (b -> f d) -> t a b -> f unit :=
  bitraverse_.

Definition biforM_ {t} {f} {a} {b} {c} {d} `{Bifoldable t}
  `{GHC.Base.Applicative f}
   : t a b -> (a -> f c) -> (b -> f d) -> f unit :=
  bifor_.

Definition bisequence_ {t} {f} {a} {b} `{Bifoldable t} `{GHC.Base.Applicative f}
   : t (f a) (f b) -> f unit :=
  bifoldr _GHC.Base.*>_ _GHC.Base.*>_ (GHC.Base.pure tt).

Definition bisequenceA_ {t} {f} {a} {b} `{Bifoldable t} `{GHC.Base.Applicative
  f}
   : t (f a) (f b) -> f unit :=
  bisequence_.

(* Skipping definition `Data.Bifoldable.biasum' *)

(* Skipping definition `Data.Bifoldable.bimsum' *)

Definition biList {t} {a} `{Bifoldable t} : t a a -> list a :=
  bifoldr cons cons nil.

Definition binull {t} {a} {b} `{Bifoldable t} : t a b -> bool :=
  bifoldr (fun arg_0__ arg_1__ => false) (fun arg_2__ arg_3__ => false) true.

Definition bilength {t} {a} {b} `{Bifoldable t} : t a b -> GHC.Num.Int :=
  bifoldl' (fun arg_0__ arg_1__ =>
              match arg_0__, arg_1__ with
              | c, _ => c GHC.Num.+ #1
              end) (fun arg_4__ arg_5__ =>
                      match arg_4__, arg_5__ with
                      | c, _ => c GHC.Num.+ #1
                      end) #0.

Definition biany {t} {a} {b} `{Bifoldable t}
   : (a -> bool) -> (b -> bool) -> t a b -> bool :=
  fun p q =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getAny (bifoldMap
                                (Data.SemigroupInternal.Mk_Any GHC.Base.∘ p) (Data.SemigroupInternal.Mk_Any
                                 GHC.Base.∘
                                 q)).

Definition bielem {t} {a} `{Bifoldable t} `{GHC.Base.Eq_ a}
   : a -> t a a -> bool :=
  fun x =>
    biany (fun arg_0__ => arg_0__ GHC.Base.== x) (fun arg_1__ =>
                                                    arg_1__ GHC.Base.== x).

Definition biconcat {t} {a} `{Bifoldable t} : t (list a) (list a) -> list a :=
  bifold.

(* Skipping definition `Data.Bifoldable.bimaximum' *)

(* Skipping definition `Data.Bifoldable.biminimum' *)

Definition bisum {t} {a} `{Bifoldable t} `{GHC.Num.Num a} : t a a -> a :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getSum (bifoldMap
                              Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.Mk_Sum).

Definition biproduct {t} {a} `{Bifoldable t} `{GHC.Num.Num a} : t a a -> a :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getProduct (bifoldMap
                              Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Product).

Definition biconcatMap {t} {a} {c} {b} `{Bifoldable t}
   : (a -> list c) -> (b -> list c) -> t a b -> list c :=
  bifoldMap.

Definition biand {t} `{Bifoldable t} : t bool bool -> bool :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getAll (bifoldMap
                              Data.SemigroupInternal.Mk_All Data.SemigroupInternal.Mk_All).

Definition bior {t} `{Bifoldable t} : t bool bool -> bool :=
  Coq.Program.Basics.compose Data.SemigroupInternal.getAny (bifoldMap
                              Data.SemigroupInternal.Mk_Any Data.SemigroupInternal.Mk_Any).

Definition biall {t} {a} {b} `{Bifoldable t}
   : (a -> bool) -> (b -> bool) -> t a b -> bool :=
  fun p q =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getAll (bifoldMap
                                (Data.SemigroupInternal.Mk_All GHC.Base.∘ p) (Data.SemigroupInternal.Mk_All
                                 GHC.Base.∘
                                 q)).

(* Skipping definition `Data.Bifoldable.bimaximumBy' *)

(* Skipping definition `Data.Bifoldable.biminimumBy' *)

Definition binotElem {t} {a} `{Bifoldable t} `{GHC.Base.Eq_ a}
   : a -> t a a -> bool :=
  fun x => negb GHC.Base.∘ bielem x.

Definition bifind {t} {a} `{Bifoldable t} : (a -> bool) -> t a a -> option a :=
  fun p =>
    let finder :=
      fun x => Data.Monoid.Mk_First (if p x : bool then Some x else None) in
    Data.Monoid.getFirst GHC.Base.∘ bifoldMap finder finder.

(* External variables:
     None Some bool cons false list negb nil option pair true tt unit
     Coq.Program.Basics.compose Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const Data.Monoid.Mk_First
     Data.Monoid.getFirst Data.SemigroupInternal.Mk_All Data.SemigroupInternal.Mk_Any
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getAll
     Data.SemigroupInternal.getAny Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad GHC.Base.Monoid GHC.Base.flip
     GHC.Base.id GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zgzgze__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_
     GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Tuple.pair_type
     GHC.Tuple.quad_type GHC.Tuple.quint_type GHC.Tuple.sept_type GHC.Tuple.sext_type
     GHC.Tuple.triple_type
*)
