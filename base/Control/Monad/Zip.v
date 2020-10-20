(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Functor.Identity.
Require Data.List.NonEmpty.
Require Data.Monoid.
Require Data.Proxy.
Require Data.SemigroupInternal.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Tuple.

(* Converted type declarations: *)

Record MonadZip__Dict m := MonadZip__Dict_Build {
  munzip__ : forall {a} {b}, m (a * b)%type -> (m a * m b)%type ;
  mzip__ : forall {a} {b}, m a -> m b -> m (a * b)%type ;
  mzipWith__ : forall {a} {b} {c}, (a -> b -> c) -> m a -> m b -> m c }.

Definition MonadZip m `{GHC.Base.Monad m} :=
  forall r__, (MonadZip__Dict m -> r__) -> r__.
Existing Class MonadZip.

Definition munzip `{g__0__ : MonadZip m}
   : forall {a} {b}, m (a * b)%type -> (m a * m b)%type :=
  g__0__ _ (munzip__ m).

Definition mzip `{g__0__ : MonadZip m}
   : forall {a} {b}, m a -> m b -> m (a * b)%type :=
  g__0__ _ (mzip__ m).

Definition mzipWith `{g__0__ : MonadZip m}
   : forall {a} {b} {c}, (a -> b -> c) -> m a -> m b -> m c :=
  g__0__ _ (mzipWith__ m).

(* Converted value declarations: *)

Local Definition MonadZip__list_munzip
   : forall {a} {b}, list (a * b)%type -> (list a * list b)%type :=
  fun {a} {b} => GHC.List.unzip.

Local Definition MonadZip__list_mzip
   : forall {a} {b}, list a -> list b -> list (a * b)%type :=
  fun {a} {b} => GHC.List.zip.

Local Definition MonadZip__list_mzipWith
   : forall {a} {b} {c}, (a -> b -> c) -> list a -> list b -> list c :=
  fun {a} {b} {c} => GHC.List.zipWith.

Program Instance MonadZip__list : MonadZip list :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__list_munzip ;
           mzip__ := fun {a} {b} => MonadZip__list_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__list_mzipWith |}.

Local Definition MonadZip__NonEmpty_munzip
   : forall {a} {b},
     GHC.Base.NonEmpty (a * b)%type ->
     (GHC.Base.NonEmpty a * GHC.Base.NonEmpty b)%type :=
  fun {a} {b} => Data.List.NonEmpty.unzip.

Local Definition MonadZip__NonEmpty_mzip
   : forall {a} {b},
     GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b -> GHC.Base.NonEmpty (a * b)%type :=
  fun {a} {b} => Data.List.NonEmpty.zip.

Local Definition MonadZip__NonEmpty_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     GHC.Base.NonEmpty a -> GHC.Base.NonEmpty b -> GHC.Base.NonEmpty c :=
  fun {a} {b} {c} => Data.List.NonEmpty.zipWith.

Program Instance MonadZip__NonEmpty : MonadZip GHC.Base.NonEmpty :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__NonEmpty_munzip ;
           mzip__ := fun {a} {b} => MonadZip__NonEmpty_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__NonEmpty_mzipWith |}.

Local Definition MonadZip__Identity_munzip
   : forall {a} {b},
     Data.Functor.Identity.Identity (a * b)%type ->
     (Data.Functor.Identity.Identity a * Data.Functor.Identity.Identity b)%type :=
  fun {a} {b} =>
    fun '(Data.Functor.Identity.Mk_Identity (pair a b)) =>
      pair (Data.Functor.Identity.Mk_Identity a) (Data.Functor.Identity.Mk_Identity
            b).

Local Definition MonadZip__Identity_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.Functor.Identity.Identity a ->
     Data.Functor.Identity.Identity b -> Data.Functor.Identity.Identity c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__Identity_mzip
   : forall {a} {b},
     Data.Functor.Identity.Identity a ->
     Data.Functor.Identity.Identity b ->
     Data.Functor.Identity.Identity (a * b)%type :=
  fun {a} {b} => MonadZip__Identity_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Identity : MonadZip Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Identity_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Identity_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Identity_mzipWith |}.

Local Definition MonadZip__Dual_munzip
   : forall {a} {b},
     Data.SemigroupInternal.Dual (a * b)%type ->
     (Data.SemigroupInternal.Dual a * Data.SemigroupInternal.Dual b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Dual_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.SemigroupInternal.Dual a ->
     Data.SemigroupInternal.Dual b -> Data.SemigroupInternal.Dual c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__Dual_mzip
   : forall {a} {b},
     Data.SemigroupInternal.Dual a ->
     Data.SemigroupInternal.Dual b -> Data.SemigroupInternal.Dual (a * b)%type :=
  fun {a} {b} => MonadZip__Dual_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Dual : MonadZip Data.SemigroupInternal.Dual :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Dual_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Dual_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Dual_mzipWith |}.

Local Definition MonadZip__Sum_munzip
   : forall {a} {b},
     Data.SemigroupInternal.Sum (a * b)%type ->
     (Data.SemigroupInternal.Sum a * Data.SemigroupInternal.Sum b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Sum_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.SemigroupInternal.Sum a ->
     Data.SemigroupInternal.Sum b -> Data.SemigroupInternal.Sum c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__Sum_mzip
   : forall {a} {b},
     Data.SemigroupInternal.Sum a ->
     Data.SemigroupInternal.Sum b -> Data.SemigroupInternal.Sum (a * b)%type :=
  fun {a} {b} => MonadZip__Sum_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Sum : MonadZip Data.SemigroupInternal.Sum :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Sum_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Sum_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Sum_mzipWith |}.

Local Definition MonadZip__Product_munzip
   : forall {a} {b},
     Data.SemigroupInternal.Product (a * b)%type ->
     (Data.SemigroupInternal.Product a * Data.SemigroupInternal.Product b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Product_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.SemigroupInternal.Product a ->
     Data.SemigroupInternal.Product b -> Data.SemigroupInternal.Product c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__Product_mzip
   : forall {a} {b},
     Data.SemigroupInternal.Product a ->
     Data.SemigroupInternal.Product b ->
     Data.SemigroupInternal.Product (a * b)%type :=
  fun {a} {b} => MonadZip__Product_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Product : MonadZip Data.SemigroupInternal.Product :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Product_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Product_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Product_mzipWith |}.

Local Definition MonadZip__option_munzip
   : forall {a} {b}, option (a * b)%type -> (option a * option b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__option_mzipWith
   : forall {a} {b} {c}, (a -> b -> c) -> option a -> option b -> option c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__option_mzip
   : forall {a} {b}, option a -> option b -> option (a * b)%type :=
  fun {a} {b} => MonadZip__option_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__option : MonadZip option :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__option_munzip ;
           mzip__ := fun {a} {b} => MonadZip__option_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__option_mzipWith |}.

Local Definition MonadZip__First_munzip
   : forall {a} {b},
     Data.Monoid.First (a * b)%type ->
     (Data.Monoid.First a * Data.Monoid.First b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__First_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.Monoid.First a -> Data.Monoid.First b -> Data.Monoid.First c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__First_mzip
   : forall {a} {b},
     Data.Monoid.First a -> Data.Monoid.First b -> Data.Monoid.First (a * b)%type :=
  fun {a} {b} => MonadZip__First_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__First : MonadZip Data.Monoid.First :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__First_munzip ;
           mzip__ := fun {a} {b} => MonadZip__First_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__First_mzipWith |}.

Local Definition MonadZip__Last_munzip
   : forall {a} {b},
     Data.Monoid.Last (a * b)%type ->
     (Data.Monoid.Last a * Data.Monoid.Last b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Last_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.Monoid.Last a -> Data.Monoid.Last b -> Data.Monoid.Last c :=
  fun {a} {b} {c} => GHC.Base.liftM2.

Local Definition MonadZip__Last_mzip
   : forall {a} {b},
     Data.Monoid.Last a -> Data.Monoid.Last b -> Data.Monoid.Last (a * b)%type :=
  fun {a} {b} => MonadZip__Last_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Last : MonadZip Data.Monoid.Last :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Last_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Last_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Last_mzipWith |}.

Local Definition MonadZip__Alt_munzip {inst_f} `{MonadZip inst_f}
   : forall {a} {b},
     (Data.SemigroupInternal.Alt inst_f) (a * b)%type ->
     ((Data.SemigroupInternal.Alt inst_f) a *
      (Data.SemigroupInternal.Alt inst_f) b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Alt_mzipWith {inst_f} `{MonadZip inst_f}
   : forall {a} {b} {c},
     (a -> b -> c) ->
     (Data.SemigroupInternal.Alt inst_f) a ->
     (Data.SemigroupInternal.Alt inst_f) b ->
     (Data.SemigroupInternal.Alt inst_f) c :=
  fun {a} {b} {c} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, Data.SemigroupInternal.Mk_Alt ma, Data.SemigroupInternal.Mk_Alt mb =>
          Data.SemigroupInternal.Mk_Alt (mzipWith f ma mb)
      end.

Local Definition MonadZip__Alt_mzip {inst_f} `{MonadZip inst_f}
   : forall {a} {b},
     (Data.SemigroupInternal.Alt inst_f) a ->
     (Data.SemigroupInternal.Alt inst_f) b ->
     (Data.SemigroupInternal.Alt inst_f) (a * b)%type :=
  fun {a} {b} => MonadZip__Alt_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Alt {f} `{MonadZip f}
   : MonadZip (Data.SemigroupInternal.Alt f) :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Alt_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Alt_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Alt_mzipWith |}.

Local Definition MonadZip__Proxy_munzip
   : forall {a} {b},
     Data.Proxy.Proxy (a * b)%type ->
     (Data.Proxy.Proxy a * Data.Proxy.Proxy b)%type :=
  fun {a} {b} =>
    fun mab =>
      pair (GHC.Base.liftM Data.Tuple.fst mab) (GHC.Base.liftM Data.Tuple.snd mab).

Local Definition MonadZip__Proxy_mzipWith
   : forall {a} {b} {c},
     (a -> b -> c) ->
     Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> Data.Proxy.Proxy c :=
  fun {a} {b} {c} => fun arg_0__ arg_1__ arg_2__ => Data.Proxy.Mk_Proxy.

Local Definition MonadZip__Proxy_mzip
   : forall {a} {b},
     Data.Proxy.Proxy a -> Data.Proxy.Proxy b -> Data.Proxy.Proxy (a * b)%type :=
  fun {a} {b} => MonadZip__Proxy_mzipWith GHC.Tuple.pair2.

Program Instance MonadZip__Proxy : MonadZip Data.Proxy.Proxy :=
  fun _ k__ =>
    k__ {| munzip__ := fun {a} {b} => MonadZip__Proxy_munzip ;
           mzip__ := fun {a} {b} => MonadZip__Proxy_mzip ;
           mzipWith__ := fun {a} {b} {c} => MonadZip__Proxy_mzipWith |}.

(* Skipping instance `Control.Monad.Zip.MonadZip__U1' of class
   `Control.Monad.Zip.MonadZip' *)

(* Skipping instance `Control.Monad.Zip.MonadZip__Par1' of class
   `Control.Monad.Zip.MonadZip' *)

(* Skipping instance `Control.Monad.Zip.MonadZip__Rec1' of class
   `Control.Monad.Zip.MonadZip' *)

(* Skipping instance `Control.Monad.Zip.MonadZip__M1' of class
   `Control.Monad.Zip.MonadZip' *)

(* Skipping instance `Control.Monad.Zip.MonadZip__op_ZCztZC__' of class
   `Control.Monad.Zip.MonadZip' *)

(* External variables:
     list op_zt__ option pair Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.List.NonEmpty.unzip
     Data.List.NonEmpty.zip Data.List.NonEmpty.zipWith Data.Monoid.First
     Data.Monoid.Last Data.Proxy.Mk_Proxy Data.Proxy.Proxy Data.SemigroupInternal.Alt
     Data.SemigroupInternal.Dual Data.SemigroupInternal.Mk_Alt
     Data.SemigroupInternal.Product Data.SemigroupInternal.Sum Data.Tuple.fst
     Data.Tuple.snd GHC.Base.Monad GHC.Base.NonEmpty GHC.Base.liftM GHC.Base.liftM2
     GHC.List.unzip GHC.List.zip GHC.List.zipWith GHC.Tuple.pair2
*)
