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
Require Data.Monoid.
Require Data.Proxy.
Require GHC.Base.
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
  forall r, (Traversable__Dict t -> r) -> r.

Existing Class Traversable.

Definition mapM `{g : Traversable t} : forall {m} {a} {b},
                                         forall `{GHC.Base.Monad m}, (a -> m b) -> t a -> m (t b) :=
  g _ (mapM__ t).

Definition sequence `{g : Traversable t} : forall {m} {a},
                                             forall `{GHC.Base.Monad m}, t (m a) -> m (t a) :=
  g _ (sequence__ t).

Definition sequenceA `{g : Traversable t} : forall {f} {a},
                                              forall `{GHC.Base.Applicative f}, t (f a) -> f (t a) :=
  g _ (sequenceA__ t).

Definition traverse `{g : Traversable t} : forall {f} {a} {b},
                                             forall `{GHC.Base.Applicative f}, (a -> f b) -> t a -> f (t b) :=
  g _ (traverse__ t).

Inductive StateR s a : Type := Mk_StateR : (s -> (s * a)%type) -> StateR s a.

Inductive StateL s a : Type := Mk_StateL : (s -> (s * a)%type) -> StateL s a.

Inductive Id a : Type := Mk_Id : a -> Id a.

Arguments Mk_StateR {_} {_} _.

Arguments Mk_StateL {_} {_} _.

Arguments Mk_Id {_} _.

Definition runStateR {s} {a} (arg_0__ : StateR s a) :=
  match arg_0__ with
    | Mk_StateR runStateR => runStateR
  end.

Definition runStateL {s} {a} (arg_1__ : StateL s a) :=
  match arg_1__ with
    | Mk_StateL runStateL => runStateL
  end.

Definition getId {a} (arg_2__ : Id a) :=
  match arg_2__ with
    | Mk_Id getId => getId
  end.
(* Converted value declarations: *)

Local Definition Traversable__option_traverse : forall {f} {a} {b},
                                                  forall `{GHC.Base.Applicative f},
                                                    (a -> f b) -> option a -> f (option b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , None => GHC.Base.pure None
        | f , Some x => Some Data.Functor.<$> f x
      end.

Local Definition Traversable__option_sequenceA : forall {f} {a},
                                                   forall `{GHC.Base.Applicative f}, option (f a) -> f (option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__option_traverse GHC.Base.id.

Local Definition Traversable__option_sequence : forall {m} {a},
                                                  forall `{GHC.Base.Monad m}, option (m a) -> m (option a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__option_sequenceA.

Local Definition Traversable__option_mapM : forall {m} {a} {b},
                                              forall `{GHC.Base.Monad m}, (a -> m b) -> option a -> m (option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__option_traverse.

Program Instance Traversable__option : Traversable option := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__option_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__option_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__option_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__option_traverse |}.

Local Definition Traversable__list_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f}, (a -> f b) -> list a -> f (list b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f =>
      let cons_f := fun x ys => (cons Data.Functor.<$> f x) GHC.Base.<*> ys in
      GHC.Base.foldr cons_f (GHC.Base.pure nil).

Local Definition Traversable__list_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f}, list (f a) -> f (list a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__list_traverse GHC.Base.id.

Local Definition Traversable__list_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m}, list (m a) -> m (list a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__list_sequenceA.

Local Definition Traversable__list_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m}, (a -> m b) -> list a -> m (list b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__list_traverse.

Program Instance Traversable__list : Traversable list := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__list_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__list_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__list_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__list_traverse |}.

Local Definition Traversable__Either_traverse {inst_a} : forall {f} {a} {b},
                                                           forall `{GHC.Base.Applicative f},
                                                             (a -> f b) -> (Data.Either.Either inst_a) a -> f
                                                             ((Data.Either.Either inst_a) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , Data.Either.Left x => GHC.Base.pure (Data.Either.Left x)
        | f , Data.Either.Right y => Data.Either.Right Data.Functor.<$> f y
      end.

Local Definition Traversable__Either_sequenceA {inst_a} : forall {f} {a},
                                                            forall `{GHC.Base.Applicative f},
                                                              (Data.Either.Either inst_a) (f a) -> f
                                                              ((Data.Either.Either inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Either_traverse GHC.Base.id.

Local Definition Traversable__Either_sequence {inst_a} : forall {m} {a},
                                                           forall `{GHC.Base.Monad m},
                                                             (Data.Either.Either inst_a) (m a) -> m ((Data.Either.Either
                                                                                                    inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Either_sequenceA.

Local Definition Traversable__Either_mapM {inst_a} : forall {m} {a} {b},
                                                       forall `{GHC.Base.Monad m},
                                                         (a -> m b) -> (Data.Either.Either inst_a) a -> m
                                                         ((Data.Either.Either inst_a) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Either_traverse.

Program Instance Traversable__Either {a} : Traversable (Data.Either.Either a) :=
  fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Either_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Either_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Either_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Either_traverse |}.

(* Skipping instance Traversable__pair_type *)

(* Skipping instance Traversable__Array *)

Local Definition Traversable__Proxy_mapM : forall {m} {a} {b},
                                             forall `{GHC.Base.Monad m},
                                               (a -> m b) -> Data.Proxy.Proxy a -> m (Data.Proxy.Proxy b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_sequence : forall {m} {a},
                                                 forall `{GHC.Base.Monad m},
                                                   Data.Proxy.Proxy (m a) -> m (Data.Proxy.Proxy a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_sequenceA : forall {f} {a},
                                                  forall `{GHC.Base.Applicative f},
                                                    Data.Proxy.Proxy (f a) -> f (Data.Proxy.Proxy a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    fun arg_0__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition Traversable__Proxy_traverse : forall {f} {a} {b},
                                                 forall `{GHC.Base.Applicative f},
                                                   (a -> f b) -> Data.Proxy.Proxy a -> f (Data.Proxy.Proxy b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Program Instance Traversable__Proxy : Traversable Data.Proxy.Proxy := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Proxy_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Proxy_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Proxy_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Proxy_traverse |}.

Local Definition Traversable__Const_traverse {inst_m} : forall {f} {a} {b},
                                                          forall `{GHC.Base.Applicative f},
                                                            (a -> f b) -> (Data.Functor.Const.Const inst_m) a -> f
                                                            ((Data.Functor.Const.Const inst_m) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | _ , Data.Functor.Const.Mk_Const m => GHC.Base.pure GHC.Base.$
                                               Data.Functor.Const.Mk_Const m
      end.

Local Definition Traversable__Const_sequenceA {inst_m} : forall {f} {a},
                                                           forall `{GHC.Base.Applicative f},
                                                             (Data.Functor.Const.Const inst_m) (f a) -> f
                                                             ((Data.Functor.Const.Const inst_m) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Const_traverse GHC.Base.id.

Local Definition Traversable__Const_sequence {inst_m} : forall {m} {a},
                                                          forall `{GHC.Base.Monad m},
                                                            (Data.Functor.Const.Const inst_m) (m a) -> m
                                                            ((Data.Functor.Const.Const inst_m) a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Const_sequenceA.

Local Definition Traversable__Const_mapM {inst_m} : forall {m} {a} {b},
                                                      forall `{GHC.Base.Monad m},
                                                        (a -> m b) -> (Data.Functor.Const.Const inst_m) a -> m
                                                        ((Data.Functor.Const.Const inst_m) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Const_traverse.

Program Instance Traversable__Const {m} : Traversable (Data.Functor.Const.Const
                                                      m) := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Const_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Const_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Const_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Const_traverse |}.

Local Definition Traversable__Dual_traverse : forall {f} {a} {b},
                                                forall `{GHC.Base.Applicative f},
                                                  (a -> f b) -> Data.Monoid.Dual a -> f (Data.Monoid.Dual b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Data.Monoid.Mk_Dual x => Data.Monoid.Mk_Dual Data.Functor.<$> f x
      end.

Local Definition Traversable__Dual_sequenceA : forall {f} {a},
                                                 forall `{GHC.Base.Applicative f},
                                                   Data.Monoid.Dual (f a) -> f (Data.Monoid.Dual a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Dual_traverse GHC.Base.id.

Local Definition Traversable__Dual_sequence : forall {m} {a},
                                                forall `{GHC.Base.Monad m},
                                                  Data.Monoid.Dual (m a) -> m (Data.Monoid.Dual a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Dual_sequenceA.

Local Definition Traversable__Dual_mapM : forall {m} {a} {b},
                                            forall `{GHC.Base.Monad m},
                                              (a -> m b) -> Data.Monoid.Dual a -> m (Data.Monoid.Dual b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Dual_traverse.

Program Instance Traversable__Dual : Traversable Data.Monoid.Dual := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Dual_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Dual_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Dual_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Dual_traverse |}.

Local Definition Traversable__Sum_traverse : forall {f} {a} {b},
                                               forall `{GHC.Base.Applicative f},
                                                 (a -> f b) -> Data.Monoid.Sum a -> f (Data.Monoid.Sum b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Data.Monoid.Mk_Sum x => Data.Monoid.Mk_Sum Data.Functor.<$> f x
      end.

Local Definition Traversable__Sum_sequenceA : forall {f} {a},
                                                forall `{GHC.Base.Applicative f},
                                                  Data.Monoid.Sum (f a) -> f (Data.Monoid.Sum a) :=
  fun {f} {a} `{GHC.Base.Applicative f} => Traversable__Sum_traverse GHC.Base.id.

Local Definition Traversable__Sum_sequence : forall {m} {a},
                                               forall `{GHC.Base.Monad m},
                                                 Data.Monoid.Sum (m a) -> m (Data.Monoid.Sum a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequenceA.

Local Definition Traversable__Sum_mapM : forall {m} {a} {b},
                                           forall `{GHC.Base.Monad m},
                                             (a -> m b) -> Data.Monoid.Sum a -> m (Data.Monoid.Sum b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_traverse.

Program Instance Traversable__Sum : Traversable Data.Monoid.Sum := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Sum_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Sum_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Sum_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Sum_traverse |}.

Local Definition Traversable__Product_traverse : forall {f} {a} {b},
                                                   forall `{GHC.Base.Applicative f},
                                                     (a -> f b) -> Data.Monoid.Product a -> f (Data.Monoid.Product b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Data.Monoid.Mk_Product x => Data.Monoid.Mk_Product Data.Functor.<$> f x
      end.

Local Definition Traversable__Product_sequenceA : forall {f} {a},
                                                    forall `{GHC.Base.Applicative f},
                                                      Data.Monoid.Product (f a) -> f (Data.Monoid.Product a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    Traversable__Product_traverse GHC.Base.id.

Local Definition Traversable__Product_sequence : forall {m} {a},
                                                   forall `{GHC.Base.Monad m},
                                                     Data.Monoid.Product (m a) -> m (Data.Monoid.Product a) :=
  fun {m} {a} `{GHC.Base.Monad m} => Traversable__Product_sequenceA.

Local Definition Traversable__Product_mapM : forall {m} {a} {b},
                                               forall `{GHC.Base.Monad m},
                                                 (a -> m b) -> Data.Monoid.Product a -> m (Data.Monoid.Product b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Product_traverse.

Program Instance Traversable__Product : Traversable Data.Monoid.Product := fun _
                                                                               k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} => Traversable__Product_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} => Traversable__Product_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        Traversable__Product_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        Traversable__Product_traverse |}.

(* Skipping instance Traversable__First *)

(* Skipping instance Traversable__Last *)

(* Skipping instance Traversable__ZipList *)

(* Skipping instance Traversable__U1 *)

Local Definition Functor__StateL_fmap {inst_s} : forall {a} {b},
                                                   (a -> b) -> (StateL inst_s) a -> (StateL inst_s) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_StateL k => Mk_StateL GHC.Base.$ (fun s =>
                               match k s with
                                 | pair s' v => pair s' (f v)
                               end)
      end.

Local Definition Functor__StateL_op_zlzd__ {inst_s} : forall {a} {b},
                                                        a -> (StateL inst_s) b -> (StateL inst_s) a :=
  fun {a} {b} => fun x => Functor__StateL_fmap (GHC.Base.const x).

Program Instance Functor__StateL {s} : GHC.Base.Functor (StateL s) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__StateL_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__StateL_fmap |}.

Local Definition Applicative__StateL_op_zlztzg__ {inst_s} : forall {a} {b},
                                                              (StateL inst_s) (a -> b) -> (StateL inst_s) a -> (StateL
                                                              inst_s) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | Mk_StateL kf , Mk_StateL kv => Mk_StateL GHC.Base.$ (fun s =>
                                           match kf s with
                                             | pair s' f => match kv s' with
                                                              | pair s'' v => pair s'' (f v)
                                                            end
                                           end)
      end.

Local Definition Applicative__StateL_op_ztzg__ {inst_s} : forall {a} {b},
                                                            (StateL inst_s) a -> (StateL inst_s) b -> (StateL inst_s)
                                                            b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__StateL_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                      y.

Local Definition Applicative__StateL_pure {inst_s} : forall {a},
                                                       a -> (StateL inst_s) a :=
  fun {a} => fun x => Mk_StateL (fun s => pair s x).

Program Instance Applicative__StateL {s} : GHC.Base.Applicative (StateL s) :=
  fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__StateL_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__StateL_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__StateL_pure |}.

Local Definition Functor__StateR_fmap {inst_s} : forall {a} {b},
                                                   (a -> b) -> (StateR inst_s) a -> (StateR inst_s) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_StateR k => Mk_StateR GHC.Base.$ (fun s =>
                               match k s with
                                 | pair s' v => pair s' (f v)
                               end)
      end.

Local Definition Functor__StateR_op_zlzd__ {inst_s} : forall {a} {b},
                                                        a -> (StateR inst_s) b -> (StateR inst_s) a :=
  fun {a} {b} => fun x => Functor__StateR_fmap (GHC.Base.const x).

Program Instance Functor__StateR {s} : GHC.Base.Functor (StateR s) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__StateR_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__StateR_fmap |}.

Local Definition Applicative__StateR_op_zlztzg__ {inst_s} : forall {a} {b},
                                                              (StateR inst_s) (a -> b) -> (StateR inst_s) a -> (StateR
                                                              inst_s) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | Mk_StateR kf , Mk_StateR kv => Mk_StateR GHC.Base.$ (fun s =>
                                           match kv s with
                                             | pair s' v => match kf s' with
                                                              | pair s'' f => pair s'' (f v)
                                                            end
                                           end)
      end.

Local Definition Applicative__StateR_op_ztzg__ {inst_s} : forall {a} {b},
                                                            (StateR inst_s) a -> (StateR inst_s) b -> (StateR inst_s)
                                                            b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__StateR_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                      y.

Local Definition Applicative__StateR_pure {inst_s} : forall {a},
                                                       a -> (StateR inst_s) a :=
  fun {a} => fun x => Mk_StateR (fun s => pair s x).

Program Instance Applicative__StateR {s} : GHC.Base.Applicative (StateR s) :=
  fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__StateR_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__StateR_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__StateR_pure |}.

Local Definition Functor__Id_fmap : forall {a} {b}, (a -> b) -> Id a -> Id b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , Mk_Id x => Mk_Id (f x)
      end.

Local Definition Functor__Id_op_zlzd__ : forall {a} {b}, a -> Id b -> Id a :=
  fun {a} {b} => fun x => Functor__Id_fmap (GHC.Base.const x).

Program Instance Functor__Id : GHC.Base.Functor Id := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__Id_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__Id_fmap |}.

Local Definition Applicative__Id_op_zlztzg__ : forall {a} {b},
                                                 Id (a -> b) -> Id a -> Id b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | Mk_Id f , Mk_Id x => Mk_Id (f x)
      end.

Local Definition Applicative__Id_op_ztzg__ : forall {a} {b},
                                               Id a -> Id b -> Id b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__Id_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition Applicative__Id_pure : forall {a}, a -> Id a :=
  fun {a} => Mk_Id.

Program Instance Applicative__Id : GHC.Base.Applicative Id := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__Id_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__Id_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__Id_pure |}.

(* Skipping instance Traversable__V1 *)

(* Skipping instance Traversable__Par1 *)

(* Skipping instance Traversable__Rec1 *)

(* Skipping instance Traversable__K1 *)

(* Skipping instance Traversable__M1 *)

(* Skipping instance Traversable__op_ZCzpZC__ *)

(* Skipping instance Traversable__op_ZCztZC__ *)

(* Skipping instance Traversable__op_ZCziZC__ *)

(* Skipping instance Traversable__URec *)

(* Skipping instance Traversable__URec *)

(* Skipping instance Traversable__URec *)

(* Skipping instance Traversable__URec *)

(* Skipping instance Traversable__URec *)

(* Skipping instance Traversable__URec *)

Definition fmapDefault {t} {a} {b} `{Traversable t} : (a -> b) -> t a -> t b :=
  fun f => getId GHC.Base.∘ traverse (Mk_Id GHC.Base.∘ f).

Definition forM {t} {m} {a} {b} `{Traversable t} `{GHC.Base.Monad m} : t
                                                                       a -> (a -> m b) -> m (t b) :=
  GHC.Base.flip mapM.

Definition for_ {t} {f} {a} {b} `{Traversable t} `{GHC.Base.Applicative f} : t
                                                                             a -> (a -> f b) -> f (t b) :=
  GHC.Base.flip traverse.

Definition mapAccumL {t} {a} {b} {c} `{Traversable t} : (a -> b -> (a *
                                                        c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t => runStateL (traverse (Mk_StateL GHC.Base.∘ GHC.Base.flip f) t) s.

Definition mapAccumR {t} {a} {b} {c} `{Traversable t} : (a -> b -> (a *
                                                        c)%type) -> a -> t b -> (a * t c)%type :=
  fun f s t => runStateR (traverse (Mk_StateR GHC.Base.∘ GHC.Base.flip f) t) s.

(* Unbound variables:
     None Some cons list nil op_zt__ option pair Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.Foldable Data.Functor.op_zlzdzg__
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const Data.Monoid.Dual
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Product Data.Monoid.Mk_Sum
     Data.Monoid.Product Data.Monoid.Sum Data.Proxy.Mk_Proxy Data.Proxy.Proxy
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zlztzg__ GHC.Base.pure
*)
