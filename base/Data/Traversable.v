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
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require Data.Functor.Utils.
Require Data.Proxy.
Require Data.SemigroupInternal.
Require GHC.Base.
Require GHC.Prim.
Require GHC.Tuple.
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record Traversable__Dict t := Traversable__Dict_Build {
  mapM__ : forall {m} {a} {b},
  forall `{GHC.Base.Monad m}, (a -> m b) -> t a -> m (t b) ;
  sequence__ : forall {m} {a}, forall `{GHC.Base.Monad m}, t (m a) -> m (t a) ;
  sequenceA__ : forall {f} {a},
  forall `{GHC.Base.Applicative f}, t (f a) -> f (t a) ;
  traverse__ : forall {f} {a} {b},
  forall `{GHC.Base.Applicative f}, (a -> f b) -> t a -> f (t b) }.

Definition Traversable t `{GHC.Base.Functor t} `{Data.Foldable.Foldable t} :=
  forall r__, (Traversable__Dict t -> r__) -> r__.
Existing Class Traversable.

Definition mapM `{g__0__ : Traversable t}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> t a -> m (t b) :=
  g__0__ _ (mapM__ t).

Definition sequence `{g__0__ : Traversable t}
   : forall {m} {a}, forall `{GHC.Base.Monad m}, t (m a) -> m (t a) :=
  g__0__ _ (sequence__ t).

Definition sequenceA `{g__0__ : Traversable t}
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, t (f a) -> f (t a) :=
  g__0__ _ (sequenceA__ t).

Definition traverse `{g__0__ : Traversable t}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> t a -> f (t b) :=
  g__0__ _ (traverse__ t).

(* Converted value declarations: *)

(* Skipping instance `Data.Traversable.Traversable__URec__Word' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__URec__Int' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__URec__Float' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__URec__Double' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__URec__Char' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__URec__Ptr__unit' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__op_ZCziZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__op_ZCztZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__op_ZCzpZC__' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__M1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__K1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Rec1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Par1' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__V1' of class
   `Data.Traversable.Traversable' *)

Local Definition Traversable__Identity_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.Functor.Identity.Identity a -> f (Data.Functor.Identity.Identity b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Functor.Identity.Mk_Identity a1 =>
          GHC.Base.fmap (fun b1 => Data.Functor.Identity.Mk_Identity b1) (f a1)
      end.

Local Definition Traversable__Identity_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.Functor.Identity.Identity a -> m (Data.Functor.Identity.Identity b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Identity_traverse.

Local Definition Traversable__Identity_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     Data.Functor.Identity.Identity (f a) -> f (Data.Functor.Identity.Identity a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Identity_traverse GHC.Base.id.

Local Definition Traversable__Identity_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     Data.Functor.Identity.Identity (m a) -> m (Data.Functor.Identity.Identity a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Identity_sequenceA.

Program Instance Traversable__Identity
   : Traversable Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Identity_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__Identity_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Identity_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Identity_traverse |}.

Local Definition Traversable__option_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> option a -> f (option b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, None => GHC.Base.pure None
      | f, Some x => Some Data.Functor.<$> f x
      end.

Local Definition Traversable__option_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> option a -> m (option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__option_traverse.

Local Definition Traversable__option_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f}, option (f a) -> f (option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__option_traverse GHC.Base.id.

Local Definition Traversable__option_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, option (m a) -> m (option a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__option_sequenceA.

Program Instance Traversable__option : Traversable option :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__option_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__option_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__option_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__option_traverse |}.

Local Definition Traversable__list_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> list a -> f (list b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f =>
      let cons_f := fun x ys => GHC.Base.liftA2 cons (f x) ys in
      GHC.Base.foldr cons_f (GHC.Base.pure nil).

Local Definition Traversable__list_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m}, (a -> m b) -> list a -> m (list b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__list_traverse.

Local Definition Traversable__list_sequenceA
   : forall {f} {a}, forall `{GHC.Base.Applicative f}, list (f a) -> f (list a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__list_traverse GHC.Base.id.

Local Definition Traversable__list_sequence
   : forall {m} {a}, forall `{GHC.Base.Monad m}, list (m a) -> m (list a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__list_sequenceA.

Program Instance Traversable__list : Traversable list :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__list_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__list_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__list_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__list_traverse |}.

Local Definition Traversable__NonEmpty_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> GHC.Base.NonEmpty a -> f (GHC.Base.NonEmpty b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, GHC.Base.NEcons a as_ =>
          GHC.Base.liftA2 GHC.Base.NEcons (f a) (traverse f as_)
      end.

Local Definition Traversable__NonEmpty_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> GHC.Base.NonEmpty a -> m (GHC.Base.NonEmpty b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__NonEmpty_traverse.

Local Definition Traversable__NonEmpty_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     GHC.Base.NonEmpty (f a) -> f (GHC.Base.NonEmpty a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__NonEmpty_traverse GHC.Base.id.

Local Definition Traversable__NonEmpty_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     GHC.Base.NonEmpty (m a) -> m (GHC.Base.NonEmpty a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__NonEmpty_sequenceA.

Program Instance Traversable__NonEmpty : Traversable GHC.Base.NonEmpty :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__NonEmpty_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__NonEmpty_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__NonEmpty_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__NonEmpty_traverse |}.

Local Definition Traversable__Either_traverse {inst_a}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     (Data.Either.Either inst_a) a -> f ((Data.Either.Either inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Either.Left x => GHC.Base.pure (Data.Either.Left x)
      | f, Data.Either.Right y => Data.Either.Right Data.Functor.<$> f y
      end.

Local Definition Traversable__Either_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     (Data.Either.Either inst_a) a -> m ((Data.Either.Either inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Either_traverse.

Local Definition Traversable__Either_sequenceA {inst_a}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Data.Either.Either inst_a) (f a) -> f ((Data.Either.Either inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Either_traverse GHC.Base.id.

Local Definition Traversable__Either_sequence {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Data.Either.Either inst_a) (m a) -> m ((Data.Either.Either inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Either_sequenceA.

Program Instance Traversable__Either {a} : Traversable (Data.Either.Either a) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Either_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Either_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Either_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Either_traverse |}.

Local Definition Traversable__pair_type_traverse {inst_a}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     (GHC.Tuple.pair_type inst_a) a -> f ((GHC.Tuple.pair_type inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair x y => GHC.Tuple.pair2 x Data.Functor.<$> f y
      end.

Local Definition Traversable__pair_type_mapM {inst_a}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     (GHC.Tuple.pair_type inst_a) a -> m ((GHC.Tuple.pair_type inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__pair_type_traverse.

Local Definition Traversable__pair_type_sequenceA {inst_a}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (GHC.Tuple.pair_type inst_a) (f a) -> f ((GHC.Tuple.pair_type inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__pair_type_traverse GHC.Base.id.

Local Definition Traversable__pair_type_sequence {inst_a}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (GHC.Tuple.pair_type inst_a) (m a) -> m ((GHC.Tuple.pair_type inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__pair_type_sequenceA.

Program Instance Traversable__pair_type {a}
   : Traversable (GHC.Tuple.pair_type a) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__pair_type_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
             Traversable__pair_type_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__pair_type_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__pair_type_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__Array' of class
   `Data.Traversable.Traversable' *)

Local Definition Traversable__Proxy_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Data.Proxy.Proxy a -> m (Data.Proxy.Proxy b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m}, Data.Proxy.Proxy (m a) -> m (Data.Proxy.Proxy a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     Data.Proxy.Proxy (f a) -> f (Data.Proxy.Proxy a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Data.Proxy.Proxy a -> f (Data.Proxy.Proxy b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Program Instance Traversable__Proxy : Traversable Data.Proxy.Proxy :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Proxy_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Proxy_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Proxy_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Proxy_traverse |}.

Local Definition Traversable__Const_traverse {inst_m}
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     (Data.Functor.Const.Const inst_m) a ->
     f ((Data.Functor.Const.Const inst_m) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Functor.Const.Mk_Const m =>
          GHC.Base.pure (Data.Functor.Const.Mk_Const m)
      end.

Local Definition Traversable__Const_mapM {inst_m}
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     (Data.Functor.Const.Const inst_m) a ->
     m ((Data.Functor.Const.Const inst_m) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Const_traverse.

Local Definition Traversable__Const_sequenceA {inst_m}
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     (Data.Functor.Const.Const inst_m) (f a) ->
     f ((Data.Functor.Const.Const inst_m) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Const_traverse GHC.Base.id.

Local Definition Traversable__Const_sequence {inst_m}
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     (Data.Functor.Const.Const inst_m) (m a) ->
     m ((Data.Functor.Const.Const inst_m) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Const_sequenceA.

Program Instance Traversable__Const {m}
   : Traversable (Data.Functor.Const.Const m) :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Const_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Const_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Const_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Const_traverse |}.

Local Definition Traversable__Dual_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Dual a -> f (Data.SemigroupInternal.Dual b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Dual x =>
          Data.SemigroupInternal.Mk_Dual Data.Functor.<$> f x
      end.

Local Definition Traversable__Dual_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Dual a -> m (Data.SemigroupInternal.Dual b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Dual_traverse.

Local Definition Traversable__Dual_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Dual (f a) -> f (Data.SemigroupInternal.Dual a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Dual_traverse GHC.Base.id.

Local Definition Traversable__Dual_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Dual (m a) -> m (Data.SemigroupInternal.Dual a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Dual_sequenceA.

Program Instance Traversable__Dual : Traversable Data.SemigroupInternal.Dual :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Dual_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Dual_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Dual_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Dual_traverse |}.

Local Definition Traversable__Sum_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Sum a -> f (Data.SemigroupInternal.Sum b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Sum x =>
          Data.SemigroupInternal.Mk_Sum Data.Functor.<$> f x
      end.

Local Definition Traversable__Sum_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Sum a -> m (Data.SemigroupInternal.Sum b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_traverse.

Local Definition Traversable__Sum_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Sum (f a) -> f (Data.SemigroupInternal.Sum a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Sum_traverse GHC.Base.id.

Local Definition Traversable__Sum_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Sum (m a) -> m (Data.SemigroupInternal.Sum a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequenceA.

Program Instance Traversable__Sum : Traversable Data.SemigroupInternal.Sum :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Sum_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Sum_traverse |}.

Local Definition Traversable__Product_traverse
   : forall {f} {a} {b},
     forall `{GHC.Base.Applicative f},
     (a -> f b) ->
     Data.SemigroupInternal.Product a -> f (Data.SemigroupInternal.Product b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.SemigroupInternal.Mk_Product x =>
          Data.SemigroupInternal.Mk_Product Data.Functor.<$> f x
      end.

Local Definition Traversable__Product_mapM
   : forall {m} {a} {b},
     forall `{GHC.Base.Monad m},
     (a -> m b) ->
     Data.SemigroupInternal.Product a -> m (Data.SemigroupInternal.Product b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Product_traverse.

Local Definition Traversable__Product_sequenceA
   : forall {f} {a},
     forall `{GHC.Base.Applicative f},
     Data.SemigroupInternal.Product (f a) -> f (Data.SemigroupInternal.Product a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Product_traverse GHC.Base.id.

Local Definition Traversable__Product_sequence
   : forall {m} {a},
     forall `{GHC.Base.Monad m},
     Data.SemigroupInternal.Product (m a) -> m (Data.SemigroupInternal.Product a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Product_sequenceA.

Program Instance Traversable__Product
   : Traversable Data.SemigroupInternal.Product :=
  fun _ k__ =>
    k__ {| mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
             Traversable__Product_mapM ;
           sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Product_sequence ;
           sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
             Traversable__Product_sequenceA ;
           traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
             Traversable__Product_traverse |}.

(* Skipping instance `Data.Traversable.Traversable__First' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__Last' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__ZipList' of class
   `Data.Traversable.Traversable' *)

(* Skipping instance `Data.Traversable.Traversable__U1' of class
   `Data.Traversable.Traversable' *)

Definition for_ {t} {f} {a} {b} `{Traversable t} `{GHC.Base.Applicative f}
   : t a -> (a -> f b) -> f (t b) :=
  GHC.Base.flip traverse.

Definition forM {t} {m} {a} {b} `{Traversable t} `{GHC.Base.Monad m}
   : t a -> (a -> m b) -> m (t b) :=
  GHC.Base.flip mapM.

Definition mapAccumL {t} {a} {b} {c} `{Traversable t}
   : (a -> b -> (a * c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t =>
    Data.Functor.Utils.runStateL (traverse (Data.Functor.Utils.Mk_StateL GHC.Base.∘
                                            GHC.Base.flip f) t) s.

Definition mapAccumR {t} {a} {b} {c} `{Traversable t}
   : (a -> b -> (a * c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t =>
    Data.Functor.Utils.runStateR (traverse (Data.Functor.Utils.Mk_StateR GHC.Base.∘
                                            GHC.Base.flip f) t) s.

Definition fmapDefault {t} {a} {b} `{Traversable t} : (a -> b) -> t a -> t b :=
  GHC.Prim.coerce (traverse : (a -> Data.Functor.Identity.Identity b) ->
                   t a -> Data.Functor.Identity.Identity (t b)).

(* Skipping definition `Data.Traversable.foldMapDefault' *)

(* External variables:
     None Some cons list nil op_zt__ option pair Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.Foldable Data.Functor.op_zlzdzg__
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity
     Data.Functor.Utils.Mk_StateL Data.Functor.Utils.Mk_StateR
     Data.Functor.Utils.runStateL Data.Functor.Utils.runStateR Data.Proxy.Mk_Proxy
     Data.Proxy.Proxy Data.SemigroupInternal.Dual Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.Product Data.SemigroupInternal.Sum GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.NEcons GHC.Base.NonEmpty GHC.Base.flip
     GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.op_z2218U__
     GHC.Base.pure GHC.Prim.coerce GHC.Tuple.pair2 GHC.Tuple.pair_type
*)
