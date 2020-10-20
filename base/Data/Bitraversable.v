(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Bifoldable.
Require Data.Bifunctor.
Require Data.Either.
Require Data.Functor.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require Data.Functor.Utils.
Require GHC.Base.
Require GHC.Prim.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Bitraversable__Dict t := Bitraversable__Dict_Build {
  bitraverse__ : forall {f} {a} {c} {b} {d},
  forall `{GHC.Base.Applicative f},
  (a -> f c) -> (b -> f d) -> t a b -> f (t c d) }.

Definition Bitraversable t `{Data.Bifunctor.Bifunctor t}
  `{Data.Bifoldable.Bifoldable t} :=
  forall r__, (Bitraversable__Dict t -> r__) -> r__.
Existing Class Bitraversable.

Definition bitraverse `{g__0__ : Bitraversable t}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) -> (b -> f d) -> t a b -> f (t c d) :=
  g__0__ _ (bitraverse__ t).

(* Converted value declarations: *)

Local Definition Bitraversable__pair_type_bitraverse
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) -> GHC.Tuple.pair_type a b -> f (GHC.Tuple.pair_type c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair a b => GHC.Base.liftA2 GHC.Tuple.pair2 (f a) (g b)
      end.

Program Instance Bitraversable__pair_type : Bitraversable GHC.Tuple.pair_type :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__pair_type_bitraverse |}.

Local Definition Bitraversable__triple_type_bitraverse {inst_x}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     (GHC.Tuple.triple_type inst_x) a b -> f ((GHC.Tuple.triple_type inst_x) c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair x a) b => GHC.Base.liftA2 (GHC.Tuple.pair3 x) (f a) (g b)
      end.

Program Instance Bitraversable__triple_type {x}
   : Bitraversable (GHC.Tuple.triple_type x) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__triple_type_bitraverse |}.

Local Definition Bitraversable__quad_type_bitraverse {inst_x} {inst_y}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     (GHC.Tuple.quad_type inst_x inst_y) a b ->
     f ((GHC.Tuple.quad_type inst_x inst_y) c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair x y) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair4 x y) (f a) (g b)
      end.

Program Instance Bitraversable__quad_type {x} {y}
   : Bitraversable (GHC.Tuple.quad_type x y) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__quad_type_bitraverse |}.

Local Definition Bitraversable__quint_type_bitraverse {inst_x} {inst_y} {inst_z}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     (GHC.Tuple.quint_type inst_x inst_y inst_z) a b ->
     f ((GHC.Tuple.quint_type inst_x inst_y inst_z) c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair x y) z) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair5 x y z) (f a) (g b)
      end.

Program Instance Bitraversable__quint_type {x} {y} {z}
   : Bitraversable (GHC.Tuple.quint_type x y z) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__quint_type_bitraverse |}.

Local Definition Bitraversable__sext_type_bitraverse {inst_x} {inst_y} {inst_z}
  {inst_w}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     (GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) a b ->
     f ((GHC.Tuple.sext_type inst_x inst_y inst_z inst_w) c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair x y) z) w) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair6 x y z w) (f a) (g b)
      end.

Program Instance Bitraversable__sext_type {x} {y} {z} {w}
   : Bitraversable (GHC.Tuple.sext_type x y z w) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__sext_type_bitraverse |}.

Local Definition Bitraversable__sept_type_bitraverse {inst_x} {inst_y} {inst_z}
  {inst_w} {inst_v}
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     (GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) a b ->
     f ((GHC.Tuple.sept_type inst_x inst_y inst_z inst_w inst_v) c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, g, pair (pair (pair (pair (pair (pair x y) z) w) v) a) b =>
          GHC.Base.liftA2 (GHC.Tuple.pair7 x y z w v) (f a) (g b)
      end.

Program Instance Bitraversable__sept_type {x} {y} {z} {w} {v}
   : Bitraversable (GHC.Tuple.sept_type x y z w v) :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__sept_type_bitraverse |}.

Local Definition Bitraversable__Either_bitraverse
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) -> Data.Either.Either a b -> f (Data.Either.Either c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Either.Left a => Data.Either.Left Data.Functor.<$> f a
      | _, g, Data.Either.Right b => Data.Either.Right Data.Functor.<$> g b
      end.

Program Instance Bitraversable__Either : Bitraversable Data.Either.Either :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__Either_bitraverse |}.

Local Definition Bitraversable__Const_bitraverse
   : forall {f} {a} {c} {b} {d},
     forall `{GHC.Base.Applicative f},
     (a -> f c) ->
     (b -> f d) ->
     Data.Functor.Const.Const a b -> f (Data.Functor.Const.Const c d) :=
  fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, _, Data.Functor.Const.Mk_Const a =>
          Data.Functor.Const.Mk_Const Data.Functor.<$> f a
      end.

Program Instance Bitraversable__Const
   : Bitraversable Data.Functor.Const.Const :=
  fun _ k__ =>
    k__ {| bitraverse__ := fun {f} {a} {c} {b} {d} `{GHC.Base.Applicative f} =>
             Bitraversable__Const_bitraverse |}.

(* Skipping instance `Data.Bitraversable.Bitraversable__K1' of class
   `Data.Bitraversable.Bitraversable' *)

Definition bisequence {t} {f} {a} {b} `{Bitraversable t} `{GHC.Base.Applicative
  f}
   : t (f a) (f b) -> f (t a b) :=
  bitraverse GHC.Base.id GHC.Base.id.

Definition bisequenceA {t} {f} {a} {b} `{Bitraversable t} `{GHC.Base.Applicative
  f}
   : t (f a) (f b) -> f (t a b) :=
  bisequence.

Definition bimapM {t} {f} {a} {c} {b} {d} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : (a -> f c) -> (b -> f d) -> t a b -> f (t c d) :=
  bitraverse.

Definition bifor {t} {f} {a} {b} {c} {d} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : t a b -> (a -> f c) -> (b -> f d) -> f (t c d) :=
  fun t f g => bitraverse f g t.

Definition biforM {t} {f} {a} {b} {c} {d} `{Bitraversable t}
  `{GHC.Base.Applicative f}
   : t a b -> (a -> f c) -> (b -> f d) -> f (t c d) :=
  bifor.

Definition bimapAccumL {t} {a} {b} {c} {d} {e} `{Bitraversable t}
   : (a -> b -> (a * c)%type) ->
     (a -> d -> (a * e)%type) -> a -> t b d -> (a * t c e)%type :=
  fun f g s t =>
    Data.Functor.Utils.runStateL (bitraverse (Data.Functor.Utils.Mk_StateL
                                              GHC.Base.∘
                                              GHC.Base.flip f) (Data.Functor.Utils.Mk_StateL GHC.Base.∘ GHC.Base.flip g)
                                  t) s.

Definition bimapAccumR {t} {a} {b} {c} {d} {e} `{Bitraversable t}
   : (a -> b -> (a * c)%type) ->
     (a -> d -> (a * e)%type) -> a -> t b d -> (a * t c e)%type :=
  fun f g s t =>
    Data.Functor.Utils.runStateR (bitraverse (Data.Functor.Utils.Mk_StateR
                                              GHC.Base.∘
                                              GHC.Base.flip f) (Data.Functor.Utils.Mk_StateR GHC.Base.∘ GHC.Base.flip g)
                                  t) s.

Definition bimapDefault {t} {a} {b} {c} {d} `{Bitraversable t}
   : (a -> b) -> (c -> d) -> t a c -> t b d :=
  GHC.Prim.coerce (bitraverse : (a -> Data.Functor.Identity.Identity b) ->
                   (c -> Data.Functor.Identity.Identity d) ->
                   t a c -> Data.Functor.Identity.Identity (t b d)).

Definition bifoldMapDefault {t} {m} {a} {b} `{Bitraversable t} `{GHC.Base.Monoid
  m}
   : (a -> m) -> (b -> m) -> t a b -> m :=
  GHC.Prim.coerce (bitraverse : (a -> Data.Functor.Const.Const m unit) ->
                   (b -> Data.Functor.Const.Const m unit) ->
                   t a b -> Data.Functor.Const.Const m (t unit unit)).

(* External variables:
     op_zt__ pair unit Data.Bifoldable.Bifoldable Data.Bifunctor.Bifunctor
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Functor.op_zlzdzg__
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Utils.Mk_StateL
     Data.Functor.Utils.Mk_StateR Data.Functor.Utils.runStateL
     Data.Functor.Utils.runStateR GHC.Base.Applicative GHC.Base.Monoid GHC.Base.flip
     GHC.Base.id GHC.Base.liftA2 GHC.Base.op_z2218U__ GHC.Prim.coerce GHC.Tuple.pair2
     GHC.Tuple.pair3 GHC.Tuple.pair4 GHC.Tuple.pair5 GHC.Tuple.pair6 GHC.Tuple.pair7
     GHC.Tuple.pair_type GHC.Tuple.quad_type GHC.Tuple.quint_type GHC.Tuple.sept_type
     GHC.Tuple.sext_type GHC.Tuple.triple_type
*)
