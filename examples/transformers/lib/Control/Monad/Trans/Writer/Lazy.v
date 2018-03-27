(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Import Data.Functor.Classes.
Require Import Data.Functor.Identity.
Require Import Data.Monoid.
Require Data.Traversable.
Require Data.Tuple.
Require Import GHC.Base.
Require GHC.Num.

(* Converted type declarations: *)

Inductive WriterT (w : Type) (m : Type -> Type) a : Type
  := Mk_WriterT : m (a * w)%type -> WriterT w m a.

Definition Writer w :=
  (WriterT w Identity)%type.

Arguments Mk_WriterT {_} {_} {_} _.

Definition runWriterT {w : Type} {m : Type -> Type} {a} (arg_0__
    : WriterT w m a) :=
  let 'Mk_WriterT runWriterT := arg_0__ in
  runWriterT.
(* Midamble *)

Import Notations.

Local Definition Monad__WriterT_tmp {inst_w} {inst_m} `{GHC.Base.Monoid
  inst_w} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) a ->
     (a -> (WriterT inst_w inst_m) b) -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_WriterT (let cont_0__ arg_1__ :=
                    let 'pair a1 w := arg_1__ in
                    let cont_2__ arg_3__ :=
                      let 'pair b1 w' := arg_3__ in
                      GHC.Base.return_ (pair b1 (GHC.Base.mappend w w')) in
                    runWriterT (k a1) GHC.Base.>>= cont_2__ in
                  runWriterT m GHC.Base.>>= cont_0__). 

(* Converted value declarations: *)

Local Definition Eq1__WriterT_liftEq {inst_w} {inst_m} `{Eq_ inst_w} `{Eq1
  inst_m}
   : forall {a} {b},
     (a -> b -> bool) ->
     (WriterT inst_w inst_m) a -> (WriterT inst_w inst_m) b -> bool :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_WriterT m1, Mk_WriterT m2 => liftEq (liftEq2 eq _==_) m1 m2
      end.

Program Instance Eq1__WriterT {w} {m} `{Eq_ w} `{Eq1 m} : Eq1 (WriterT w m) :=
  fun _ k => k {| liftEq__ := fun {a} {b} => Eq1__WriterT_liftEq |}.

Local Definition Ord1__WriterT_liftCompare {inst_w} {inst_m} `{Ord inst_w}
  `{Ord1 inst_m}
   : forall {a} {b},
     (a -> b -> comparison) ->
     (WriterT inst_w inst_m) a -> (WriterT inst_w inst_m) b -> comparison :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_WriterT m1, Mk_WriterT m2 =>
          liftCompare (liftCompare2 comp compare) m1 m2
      end.

Program Instance Ord1__WriterT {w} {m} `{Ord w} `{Ord1 m}
   : Ord1 (WriterT w m) :=
  fun _ k => k {| liftCompare__ := fun {a} {b} => Ord1__WriterT_liftCompare |}.

(* Translating `instance Read1__WriterT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Read1" unsupported *)

(* Translating `instance Show1__WriterT' failed: OOPS! Cannot find information
   for class Qualified "Data.Functor.Classes" "Show1" unsupported *)

Local Definition Eq___WriterT_op_zeze__ {inst_w} {inst_m} {inst_a} `{Eq_ inst_w}
  `{Eq1 inst_m} `{Eq_ inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  eq1.

Local Definition Eq___WriterT_op_zsze__ {inst_w} {inst_m} {inst_a} `{Eq_ inst_w}
  `{Eq1 inst_m} `{Eq_ inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  fun x y => negb (Eq___WriterT_op_zeze__ x y).

Program Instance Eq___WriterT {w} {m} {a} `{Eq_ w} `{Eq1 m} `{Eq_ a}
   : Eq_ (WriterT w m a) :=
  fun _ k =>
    k {| op_zeze____ := Eq___WriterT_op_zeze__ ;
         op_zsze____ := Eq___WriterT_op_zsze__ |}.

Local Definition Ord__WriterT_compare {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) ->
     (WriterT inst_w inst_m inst_a) -> comparison :=
  compare1.

Local Definition Ord__WriterT_op_zg__ {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  fun x y => _==_ (Ord__WriterT_compare x y) Gt.

Local Definition Ord__WriterT_op_zgze__ {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  fun x y => _/=_ (Ord__WriterT_compare x y) Lt.

Local Definition Ord__WriterT_op_zl__ {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  fun x y => _==_ (Ord__WriterT_compare x y) Lt.

Local Definition Ord__WriterT_op_zlze__ {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) -> bool :=
  fun x y => _/=_ (Ord__WriterT_compare x y) Gt.

Local Definition Ord__WriterT_max {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) ->
     (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) :=
  fun x y => if Ord__WriterT_op_zlze__ x y : bool then y else x.

Local Definition Ord__WriterT_min {inst_w} {inst_m} {inst_a} `{Ord inst_w}
  `{Ord1 inst_m} `{Ord inst_a}
   : (WriterT inst_w inst_m inst_a) ->
     (WriterT inst_w inst_m inst_a) -> (WriterT inst_w inst_m inst_a) :=
  fun x y => if Ord__WriterT_op_zlze__ x y : bool then x else y.

Program Instance Ord__WriterT {w} {m} {a} `{Ord w} `{Ord1 m} `{Ord a}
   : Ord (WriterT w m a) :=
  fun _ k =>
    k {| op_zl____ := Ord__WriterT_op_zl__ ;
         op_zlze____ := Ord__WriterT_op_zlze__ ;
         op_zg____ := Ord__WriterT_op_zg__ ;
         op_zgze____ := Ord__WriterT_op_zgze__ ;
         compare__ := Ord__WriterT_compare ;
         max__ := Ord__WriterT_max ;
         min__ := Ord__WriterT_min |}.

(* Translating `instance Read__WriterT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Read" "Read" unsupported *)

(* Translating `instance Show__WriterT' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Foldable__WriterT_foldMap {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m} {a},
     forall `{Monoid m}, (a -> m) -> (WriterT inst_w inst_f) a -> m :=
  fun {m} {a} `{Monoid m} =>
    fun f => Data.Foldable.foldMap (f ∘ Data.Tuple.fst) ∘ runWriterT.

Local Definition Foldable__WriterT_foldl {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (WriterT inst_w inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_19__ arg_20__ arg_21__ =>
      match arg_19__, arg_20__, arg_21__ with
      | f, z, t =>
          appEndo (getDual (Foldable__WriterT_foldMap (Coq.Program.Basics.compose Mk_Dual
                                                                                  (Coq.Program.Basics.compose Mk_Endo
                                                                                                              (flip f)))
                            t)) z
      end.

Local Definition Foldable__WriterT_foldr' {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (WriterT inst_w inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_9__ arg_10__ arg_11__ =>
      match arg_9__, arg_10__, arg_11__ with
      | f, z0, xs =>
          let f' :=
            fun arg_12__ arg_13__ arg_14__ =>
              match arg_12__, arg_13__, arg_14__ with
              | k, x, z => _$!_ k (f x z)
              end in
          Foldable__WriterT_foldl f' id xs z0
      end.

Local Definition Foldable__WriterT_foldr {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a} {b}, (a -> b -> b) -> b -> (WriterT inst_w inst_f) a -> b :=
  fun {a} {b} =>
    fun arg_4__ arg_5__ arg_6__ =>
      match arg_4__, arg_5__, arg_6__ with
      | f, z, t =>
          appEndo (Foldable__WriterT_foldMap (Data.Foldable.hash_compose Mk_Endo f) t) z
      end.

Local Definition Foldable__WriterT_foldl' {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b} {a}, (b -> a -> b) -> b -> (WriterT inst_w inst_f) a -> b :=
  fun {b} {a} =>
    fun arg_24__ arg_25__ arg_26__ =>
      match arg_24__, arg_25__, arg_26__ with
      | f, z0, xs =>
          let f' :=
            fun arg_27__ arg_28__ arg_29__ =>
              match arg_27__, arg_28__, arg_29__ with
              | x, k, z => _$!_ k (f z x)
              end in
          Foldable__WriterT_foldr f' id xs z0
      end.

Local Definition Foldable__WriterT_toList {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (WriterT inst_w inst_f) a -> list a :=
  fun {a} =>
    fun arg_54__ =>
      let 't := arg_54__ in
      build (fun _ arg_55__ arg_56__ =>
               match arg_55__, arg_56__ with
               | c, n => Foldable__WriterT_foldr c n t
               end).

Local Definition Foldable__WriterT_product {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (WriterT inst_w inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getProduct (Foldable__WriterT_foldMap Mk_Product).

Local Definition Foldable__WriterT_sum {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{GHC.Num.Num a}, (WriterT inst_w inst_f) a -> a :=
  fun {a} `{GHC.Num.Num a} =>
    Data.Foldable.hash_compose getSum (Foldable__WriterT_foldMap Mk_Sum).

Local Definition Foldable__WriterT_fold {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m}, forall `{Monoid m}, (WriterT inst_w inst_f) m -> m :=
  fun {m} `{Monoid m} => Foldable__WriterT_foldMap id.

Local Definition Foldable__WriterT_elem {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, forall `{Eq_ a}, a -> (WriterT inst_w inst_f) a -> bool :=
  fun {a} `{Eq_ a} =>
    Coq.Program.Basics.compose (fun arg_69__ =>
                                  let 'p := arg_69__ in
                                  Coq.Program.Basics.compose getAny (Foldable__WriterT_foldMap
                                                              (Coq.Program.Basics.compose Mk_Any p))) _==_.

Local Definition Foldable__WriterT_length {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (WriterT inst_w inst_f) a -> GHC.Num.Int :=
  fun {a} =>
    fun arg_0__ => let 'Mk_WriterT t := arg_0__ in Data.Foldable.length t.

Local Definition Foldable__WriterT_null {inst_f} {inst_w}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a}, (WriterT inst_w inst_f) a -> bool :=
  fun {a} => fun arg_0__ => let 'Mk_WriterT t := arg_0__ in Data.Foldable.null t.

Program Instance Foldable__WriterT {f} {w} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (WriterT w f) :=
  fun _ k =>
    k {| Data.Foldable.elem__ := fun {a} `{Eq_ a} => Foldable__WriterT_elem ;
         Data.Foldable.fold__ := fun {m} `{Monoid m} => Foldable__WriterT_fold ;
         Data.Foldable.foldMap__ := fun {m} {a} `{Monoid m} =>
           Foldable__WriterT_foldMap ;
         Data.Foldable.foldl__ := fun {b} {a} => Foldable__WriterT_foldl ;
         Data.Foldable.foldl'__ := fun {b} {a} => Foldable__WriterT_foldl' ;
         Data.Foldable.foldr__ := fun {a} {b} => Foldable__WriterT_foldr ;
         Data.Foldable.foldr'__ := fun {a} {b} => Foldable__WriterT_foldr' ;
         Data.Foldable.length__ := fun {a} => Foldable__WriterT_length ;
         Data.Foldable.null__ := fun {a} => Foldable__WriterT_null ;
         Data.Foldable.product__ := fun {a} `{GHC.Num.Num a} =>
           Foldable__WriterT_product ;
         Data.Foldable.sum__ := fun {a} `{GHC.Num.Num a} => Foldable__WriterT_sum ;
         Data.Foldable.toList__ := fun {a} => Foldable__WriterT_toList |}.

Local Definition Traversable__WriterT_traverse {inst_f} {inst_w}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a} {b},
     forall `{Applicative f},
     (a -> f b) -> (WriterT inst_w inst_f) a -> f ((WriterT inst_w inst_f) b) :=
  fun {f} {a} {b} `{Applicative f} =>
    fun f =>
      let f' :=
        fun arg_0__ => let 'pair a b := arg_0__ in fmap (fun c => pair c b) (f a) in
      fmap Mk_WriterT ∘ (Data.Traversable.traverse f' ∘ runWriterT).

Local Definition Traversable__WriterT_sequenceA {inst_f} {inst_w}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f} {a},
     forall `{Applicative f},
     (WriterT inst_w inst_f) (f a) -> f ((WriterT inst_w inst_f) a) :=
  fun {f} {a} `{Applicative f} => Traversable__WriterT_traverse id.

Local Definition Traversable__WriterT_sequence {inst_f} {inst_w}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a},
     forall `{Monad m},
     (WriterT inst_w inst_f) (m a) -> m ((WriterT inst_w inst_f) a) :=
  fun {m} {a} `{Monad m} => Traversable__WriterT_sequenceA.

Local Definition Traversable__WriterT_mapM {inst_f} {inst_w}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m} {a} {b},
     forall `{Monad m},
     (a -> m b) -> (WriterT inst_w inst_f) a -> m ((WriterT inst_w inst_f) b) :=
  fun {m} {a} {b} `{Monad m} => Traversable__WriterT_traverse.

Local Definition Applicative__WriterT_op_zlztzg__ {inst_w} {inst_m} `{Monoid
  inst_w} `{Applicative inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) (a -> b) ->
     (WriterT inst_w inst_m) a -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun f v =>
      let k :=
        fun arg_0__ arg_1__ =>
          match arg_0__, arg_1__ with
          | pair a w, pair b w' => pair (a b) (mappend w w')
          end in
      Mk_WriterT (liftA2 k (runWriterT f) (runWriterT v)).

(* Translating `instance Alternative__WriterT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "Alternative" unsupported *)

Definition Monad__WriterT_op_zgzgze__ {inst_w} {inst_m} `{_ : Monoid inst_w} `{_
   : Monad inst_m}
   : forall {a} {b},
     WriterT inst_w inst_m a ->
     (a -> WriterT inst_w inst_m b) -> WriterT inst_w inst_m b :=
  fun {a} {b} => Monad__WriterT_tmp.

(* Translating `instance MonadFail__WriterT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fail" "MonadFail" unsupported *)

(* Translating `instance MonadPlus__WriterT' failed: OOPS! Cannot find
   information for class Qualified "GHC.Base" "MonadPlus" unsupported *)

(* Translating `instance MonadFix__WriterT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Fix" "MonadFix" unsupported *)

Local Definition MonadTrans__WriterT_lift {inst_w} `{(Monoid inst_w)}
   : forall {m} {a} `{Monad m}, m a -> (WriterT inst_w) m a :=
  fun {m} {a} `{Monad m} =>
    fun m => Mk_WriterT (_>>=_ m (fun a => return_ (pair a mempty))).

Program Instance MonadTrans__WriterT {w} `{(Monoid w)}
   : Control.Monad.Trans.Class.MonadTrans (WriterT w) :=
  fun _ k =>
    k {| Control.Monad.Trans.Class.lift__ := fun {m} {a} `{Monad m} =>
           MonadTrans__WriterT_lift |}.

(* Translating `instance MonadIO__WriterT' failed: OOPS! Cannot find information
   for class Qualified "Control.Monad.IO.Class" "MonadIO" unsupported *)

(* Translating `instance MonadZip__WriterT' failed: OOPS! Cannot find
   information for class Qualified "Control.Monad.Zip" "MonadZip" unsupported *)

Definition censor {m} {w} {a} `{(Monad m)}
   : (w -> w) -> WriterT w m a -> WriterT w m a :=
  fun f m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  return_ (pair a (f w)) in
                runWriterT m >>= cont_0__).

Definition execWriterT {m} {w} {a} `{(Monad m)} : WriterT w m a -> m w :=
  fun m =>
    let cont_0__ arg_1__ := let 'pair _ w := arg_1__ in return_ w in
    runWriterT m >>= cont_0__.

Definition liftCallCC {w} {m} {a} {b} `{(Monoid w)}
   : Control.Monad.Signatures.CallCC m (a * w)%type (b * w)%type ->
     Control.Monad.Signatures.CallCC (WriterT w m) a b :=
  fun callCC f =>
    Mk_WriterT (callCC (fun c =>
                          runWriterT (f (fun a => Mk_WriterT (c (pair a mempty)))))).

Definition listen {m} {w} {a} `{(Monad m)}
   : WriterT w m a -> WriterT w m (a * w)%type :=
  fun m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  return_ (pair (pair a w) w) in
                runWriterT m >>= cont_0__).

Definition listens {m} {w} {b} {a} `{(Monad m)}
   : (w -> b) -> WriterT w m a -> WriterT w m (a * b)%type :=
  fun f m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair a w := arg_1__ in
                  return_ (pair (pair a (f w)) w) in
                runWriterT m >>= cont_0__).

Definition mapWriterT {m} {a} {w} {n} {b} {w'}
   : (m (a * w)%type -> n (b * w')%type) -> WriterT w m a -> WriterT w' n b :=
  fun f m => Mk_WriterT (f (runWriterT m)).

Definition mapWriter {a} {w} {b} {w'}
   : ((a * w)%type -> (b * w')%type) -> Writer w a -> Writer w' b :=
  fun f => mapWriterT (Mk_Identity ∘ (f ∘ runIdentity)).

Local Definition Functor__WriterT_fmap {inst_m} {inst_w} `{(Functor inst_m)}
   : forall {a} {b},
     (a -> b) -> (WriterT inst_w inst_m) a -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun f =>
      mapWriterT (fmap (fun arg_0__ => let 'pair a w := arg_0__ in pair (f a) w)).

Local Definition Functor__WriterT_op_zlzd__ {inst_m} {inst_w} `{(Functor
   inst_m)}
   : forall {a} {b},
     a -> (WriterT inst_w inst_m) b -> (WriterT inst_w inst_m) a :=
  fun {a} {b} => fun x => Functor__WriterT_fmap (const x).

Program Instance Functor__WriterT {m} {w} `{(Functor m)}
   : Functor (WriterT w m) :=
  fun _ k =>
    k {| op_zlzd____ := fun {a} {b} => Functor__WriterT_op_zlzd__ ;
         fmap__ := fun {a} {b} => Functor__WriterT_fmap |}.

Local Definition Applicative__WriterT_pure {inst_w} {inst_m} `{Monoid inst_w}
  `{Applicative inst_m}
   : forall {a}, a -> (WriterT inst_w inst_m) a :=
  fun {a} => fun a => Mk_WriterT (pure (pair a mempty)).

Local Definition Applicative__WriterT_op_ztzg__ {inst_w} {inst_m} `{Monoid
  inst_w} `{Applicative inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) a ->
     (WriterT inst_w inst_m) b -> (WriterT inst_w inst_m) b :=
  fun {a} {b} =>
    fun x y => Applicative__WriterT_op_zlztzg__ (fmap (const id) x) y.

Program Instance Applicative__WriterT {w} {m} `{Monoid w} `{Applicative m}
   : Applicative (WriterT w m) :=
  fun _ k =>
    k {| op_ztzg____ := fun {a} {b} => Applicative__WriterT_op_ztzg__ ;
         op_zlztzg____ := fun {a} {b} => Applicative__WriterT_op_zlztzg__ ;
         pure__ := fun {a} => Applicative__WriterT_pure |}.

Local Definition Monad__WriterT_op_zgzg__ {inst_w} {inst_m} `{Monoid inst_w}
  `{Monad inst_m}
   : forall {a} {b},
     (WriterT inst_w inst_m) a ->
     (WriterT inst_w inst_m) b -> (WriterT inst_w inst_m) b :=
  fun {a} {b} => _*>_.

Local Definition Monad__WriterT_return_ {inst_w} {inst_m} `{Monoid inst_w}
  `{Monad inst_m}
   : forall {a}, a -> (WriterT inst_w inst_m) a :=
  fun {a} => pure.

Program Instance Monad__WriterT {w} {m} `{Monoid w} `{Monad m}
   : Monad (WriterT w m) :=
  fun _ k =>
    k {| op_zgzg____ := fun {a} {b} => Monad__WriterT_op_zgzg__ ;
         op_zgzgze____ := fun {a} {b} => Monad__WriterT_op_zgzgze__ ;
         return___ := fun {a} => Monad__WriterT_return_ |}.

Program Instance Traversable__WriterT {f} {w} `{(Data.Traversable.Traversable
   f)}
   : Data.Traversable.Traversable (WriterT w f) :=
  fun _ k =>
    k {| Data.Traversable.mapM__ := fun {m} {a} {b} `{Monad m} =>
           Traversable__WriterT_mapM ;
         Data.Traversable.sequence__ := fun {m} {a} `{Monad m} =>
           Traversable__WriterT_sequence ;
         Data.Traversable.sequenceA__ := fun {f} {a} `{Applicative f} =>
           Traversable__WriterT_sequenceA ;
         Data.Traversable.traverse__ := fun {f} {a} {b} `{Applicative f} =>
           Traversable__WriterT_traverse |}.

Definition pass {m} {w} {a} `{(Monad m)}
   : WriterT w m (a * (w -> w))%type -> WriterT w m a :=
  fun m =>
    Mk_WriterT (let cont_0__ arg_1__ :=
                  let 'pair (pair a f) w := arg_1__ in
                  return_ (pair a (f w)) in
                runWriterT m >>= cont_0__).

Definition runWriter {w} {a} : Writer w a -> (a * w)%type :=
  runIdentity ∘ runWriterT.

Definition execWriter {w} {a} : Writer w a -> w :=
  fun m => Data.Tuple.snd (runWriter m).

Definition writer {m} {a} {w} `{(Monad m)} : (a * w)%type -> WriterT w m a :=
  Mk_WriterT ∘ return_.

Definition tell {m} {w} `{(Monad m)} : w -> WriterT w m unit :=
  fun w => writer (pair tt w).

(* Unbound variables:
     Applicative Eq1 Eq_ Functor Gt Identity Lt Mk_Any Mk_Dual Mk_Endo Mk_Identity
     Mk_Product Mk_Sum Monad Monad__WriterT_tmp Monoid Ord Ord1 Type appEndo bool
     build compare compare1 comparison const eq1 flip fmap getAny getDual getProduct
     getSum id liftA2 liftCompare liftCompare2 liftEq liftEq2 list mappend mempty
     negb op_z2218U__ op_zdzn__ op_zeze__ op_zgzgze__ op_zsze__ op_zt__ op_ztzg__
     pair pure return_ runIdentity tt unit Control.Monad.Signatures.CallCC
     Control.Monad.Trans.Class.MonadTrans Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.hash_compose
     Data.Foldable.length Data.Foldable.null Data.Traversable.Traversable
     Data.Traversable.traverse Data.Tuple.fst Data.Tuple.snd GHC.Num.Int GHC.Num.Num
*)
