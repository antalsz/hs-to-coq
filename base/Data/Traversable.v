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

Inductive StateR s a : Type := Mk_StateR : (s -> s * a) -> StateR s a.

Inductive StateL s a : Type := Mk_StateL : (s -> s * a) -> StateL s a.

Inductive Id a : Type := Mk_Id : a -> Id a.

Arguments Mk_StateR {_} {_} _.

Arguments Mk_StateL {_} {_} _.

Arguments Mk_Id {_} _.

Definition runStateR {s} {a} (arg_2__ : StateR s a) :=
  match arg_2__ with
    | Mk_StateR runStateR => runStateR
  end.

Definition runStateL {s} {a} (arg_3__ : StateL s a) :=
  match arg_3__ with
    | Mk_StateL runStateL => runStateL
  end.

Definition getId {a} (arg_4__ : Id a) :=
  match arg_4__ with
    | Mk_Id getId => getId
  end.
(* Converted value declarations: *)

Local Definition instance_Data_Traversable_Traversable_option_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f}, (a -> f b) -> option a -> f (option b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_177__ arg_178__ =>
      match arg_177__ , arg_178__ with
        | _ , None => GHC.Base.pure None
        | f , Some x => Data.Functor.op_zlzdzg__ Some (f x)
      end.

Local Definition instance_Data_Traversable_Traversable_option_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f}, option (f a) -> f (option a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_option_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_option_sequence
    : forall {m} {a}, forall `{GHC.Base.Monad m}, option (m a) -> m (option a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_option_sequenceA.

Local Definition instance_Data_Traversable_Traversable_option_mapM : forall {m}
                                                                            {a}
                                                                            {b},
                                                                       forall `{GHC.Base.Monad m},
                                                                         (a -> m b) -> option a -> m (option b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_option_traverse.

Program Instance instance_Data_Traversable_Traversable_option : Traversable
                                                                option := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_option_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_option_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_option_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_option_traverse |}.

Local Definition instance_Data_Traversable_Traversable_list_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f}, (a -> f b) -> list a -> f (list b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun f =>
      let cons_f :=
        fun x ys => GHC.Base.op_zlztzg__ (Data.Functor.op_zlzdzg__ cons (f x)) ys in
      GHC.Base.foldr cons_f (GHC.Base.pure nil).

Local Definition instance_Data_Traversable_Traversable_list_sequenceA
    : forall {f} {a}, forall `{GHC.Base.Applicative f}, list (f a) -> f (list a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_list_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_list_sequence
    : forall {m} {a}, forall `{GHC.Base.Monad m}, list (m a) -> m (list a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_list_sequenceA.

Local Definition instance_Data_Traversable_Traversable_list_mapM : forall {m}
                                                                          {a}
                                                                          {b},
                                                                     forall `{GHC.Base.Monad m},
                                                                       (a -> m b) -> list a -> m (list b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_list_traverse.

Program Instance instance_Data_Traversable_Traversable_list : Traversable
                                                              list := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_list_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_list_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_list_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_list_traverse |}.

Local Definition instance_Data_Traversable_Traversable__Data_Either_Either_a__traverse {inst_a}
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> (Data.Either.Either inst_a) a -> f ((Data.Either.Either inst_a)
                                                           b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_170__ arg_171__ =>
      match arg_170__ , arg_171__ with
        | _ , Data.Either.Mk_Left x => GHC.Base.pure (Data.Either.Mk_Left x)
        | f , Data.Either.Mk_Right y => Data.Functor.op_zlzdzg__ Data.Either.Mk_Right (f
                                                                 y)
      end.

Local Definition instance_Data_Traversable_Traversable__Data_Either_Either_a__sequenceA {inst_a}
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          (Data.Either.Either inst_a) (f a) -> f ((Data.Either.Either inst_a) a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable__Data_Either_Either_a__traverse
    GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable__Data_Either_Either_a__sequence {inst_a}
    : forall {m} {a},
        forall `{GHC.Base.Monad m},
          (Data.Either.Either inst_a) (m a) -> m ((Data.Either.Either inst_a) a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable__Data_Either_Either_a__sequenceA.

Local Definition instance_Data_Traversable_Traversable__Data_Either_Either_a__mapM {inst_a}
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> (Data.Either.Either inst_a) a -> m ((Data.Either.Either inst_a)
                                                           b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable__Data_Either_Either_a__traverse.

Program Instance instance_Data_Traversable_Traversable__Data_Either_Either_a_ {a}
  : Traversable (Data.Either.Either a) := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable__Data_Either_Either_a__mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable__Data_Either_Either_a__sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable__Data_Either_Either_a__sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable__Data_Either_Either_a__traverse |}.

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Tuple_pair_type_a_ *)

(* Skipping instance
   instance_forall___GHC_Arr_Ix_i___Data_Traversable_Traversable__GHC_Arr_Array_i_ *)

Local Definition instance_Data_Traversable_Traversable_Data_Proxy_Proxy_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> Data.Proxy.Proxy a -> m (Data.Proxy.Proxy b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    fun arg_158__ arg_159__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition instance_Data_Traversable_Traversable_Data_Proxy_Proxy_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, Data.Proxy.Proxy (m a) -> m (Data.Proxy.Proxy a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    fun arg_162__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition instance_Data_Traversable_Traversable_Data_Proxy_Proxy_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          Data.Proxy.Proxy (f a) -> f (Data.Proxy.Proxy a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    fun arg_155__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Local Definition instance_Data_Traversable_Traversable_Data_Proxy_Proxy_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> Data.Proxy.Proxy a -> f (Data.Proxy.Proxy b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_151__ arg_152__ => GHC.Base.pure Data.Proxy.Mk_Proxy.

Program Instance instance_Data_Traversable_Traversable_Data_Proxy_Proxy
  : Traversable Data.Proxy.Proxy := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Proxy_Proxy_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Proxy_Proxy_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Proxy_Proxy_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Proxy_Proxy_traverse |}.

Local Definition instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__traverse {inst_m}
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> (Data.Functor.Const.Const inst_m) a -> f
          ((Data.Functor.Const.Const inst_m) b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_147__ arg_148__ =>
      match arg_147__ , arg_148__ with
        | _ , Data.Functor.Const.Mk_Const m => GHC.Base.op_zd__ GHC.Base.pure
                                                                (Data.Functor.Const.Mk_Const m)
      end.

Local Definition instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__sequenceA {inst_m}
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          (Data.Functor.Const.Const inst_m) (f a) -> f ((Data.Functor.Const.Const inst_m)
                                                       a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__traverse
    GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__sequence {inst_m}
    : forall {m} {a},
        forall `{GHC.Base.Monad m},
          (Data.Functor.Const.Const inst_m) (m a) -> m ((Data.Functor.Const.Const inst_m)
                                                       a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__sequenceA.

Local Definition instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__mapM {inst_m}
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> (Data.Functor.Const.Const inst_m) a -> m
          ((Data.Functor.Const.Const inst_m) b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__traverse.

Program Instance instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m_ {m}
  : Traversable (Data.Functor.Const.Const m) := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable__Data_Functor_Const_Const_m__traverse |}.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Dual_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> Data.Monoid.Dual a -> f (Data.Monoid.Dual b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_143__ arg_144__ =>
      match arg_143__ , arg_144__ with
        | f , Data.Monoid.Mk_Dual x => Data.Functor.op_zlzdzg__ Data.Monoid.Mk_Dual (f
                                                                x)
      end.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Dual_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          Data.Monoid.Dual (f a) -> f (Data.Monoid.Dual a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Dual_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Dual_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, Data.Monoid.Dual (m a) -> m (Data.Monoid.Dual a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Dual_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Dual_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> Data.Monoid.Dual a -> m (Data.Monoid.Dual b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Dual_traverse.

Program Instance instance_Data_Traversable_Traversable_Data_Monoid_Dual
  : Traversable Data.Monoid.Dual := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Dual_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Dual_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Dual_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Dual_traverse |}.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Sum_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> Data.Monoid.Sum a -> f (Data.Monoid.Sum b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_139__ arg_140__ =>
      match arg_139__ , arg_140__ with
        | f , Data.Monoid.Mk_Sum x => Data.Functor.op_zlzdzg__ Data.Monoid.Mk_Sum (f x)
      end.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Sum_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          Data.Monoid.Sum (f a) -> f (Data.Monoid.Sum a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Sum_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Sum_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m}, Data.Monoid.Sum (m a) -> m (Data.Monoid.Sum a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Sum_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Sum_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> Data.Monoid.Sum a -> m (Data.Monoid.Sum b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Sum_traverse.

Program Instance instance_Data_Traversable_Traversable_Data_Monoid_Sum
  : Traversable Data.Monoid.Sum := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Sum_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Sum_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Sum_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Sum_traverse |}.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Product_traverse
    : forall {f} {a} {b},
        forall `{GHC.Base.Applicative f},
          (a -> f b) -> Data.Monoid.Product a -> f (Data.Monoid.Product b) :=
  fun {f} {a} {b} `{GHC.Base.Applicative f} =>
    fun arg_135__ arg_136__ =>
      match arg_135__ , arg_136__ with
        | f , Data.Monoid.Mk_Product x => Data.Functor.op_zlzdzg__
                                          Data.Monoid.Mk_Product (f x)
      end.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Product_sequenceA
    : forall {f} {a},
        forall `{GHC.Base.Applicative f},
          Data.Monoid.Product (f a) -> f (Data.Monoid.Product a) :=
  fun {f} {a} `{GHC.Base.Applicative f} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Product_traverse GHC.Base.id.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Product_sequence
    : forall {m} {a},
        forall `{GHC.Base.Monad m},
          Data.Monoid.Product (m a) -> m (Data.Monoid.Product a) :=
  fun {m} {a} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Product_sequenceA.

Local Definition instance_Data_Traversable_Traversable_Data_Monoid_Product_mapM
    : forall {m} {a} {b},
        forall `{GHC.Base.Monad m},
          (a -> m b) -> Data.Monoid.Product a -> m (Data.Monoid.Product b) :=
  fun {m} {a} {b} `{GHC.Base.Monad m} =>
    instance_Data_Traversable_Traversable_Data_Monoid_Product_traverse.

Program Instance instance_Data_Traversable_Traversable_Data_Monoid_Product
  : Traversable Data.Monoid.Product := fun _ k =>
    k {|mapM__ := fun {m} {a} {b} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Product_mapM ;
      sequence__ := fun {m} {a} `{GHC.Base.Monad m} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Product_sequence ;
      sequenceA__ := fun {f} {a} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Product_sequenceA ;
      traverse__ := fun {f} {a} {b} `{GHC.Base.Applicative f} =>
        instance_Data_Traversable_Traversable_Data_Monoid_Product_traverse |}.

(* Skipping instance instance_Data_Traversable_Traversable_Data_Monoid_First *)

(* Skipping instance instance_Data_Traversable_Traversable_Data_Monoid_Last *)

(* Skipping instance
   instance_Data_Traversable_Traversable_Control_Applicative_ZipList *)

(* Skipping instance instance_Data_Traversable_Traversable_GHC_Generics_U1 *)

Local Definition instance_GHC_Base_Functor__Data_Traversable_StateL_s__fmap {inst_s}
    : forall {a} {b}, (a -> b) -> (StateL inst_s) a -> (StateL inst_s) b :=
  fun {a} {b} =>
    fun arg_103__ arg_104__ =>
      match arg_103__ , arg_104__ with
        | f , Mk_StateL k => GHC.Base.op_zd__ Mk_StateL (fun s =>
                                                match k s with
                                                  | pair s' v => pair s' (f v)
                                                end)
      end.

Local Definition instance_GHC_Base_Functor__Data_Traversable_StateL_s__op_zlzd__ {inst_s}
    : forall {a} {b}, a -> (StateL inst_s) b -> (StateL inst_s) a :=
  fun {a} {b} =>
    fun x =>
      instance_GHC_Base_Functor__Data_Traversable_StateL_s__fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor__Data_Traversable_StateL_s_ {s}
  : GHC.Base.Functor (StateL s) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Traversable_StateL_s__op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Traversable_StateL_s__fmap |}.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateL_s__op_zlztzg__ {inst_s}
    : forall {a} {b},
        (StateL inst_s) (a -> b) -> (StateL inst_s) a -> (StateL inst_s) b :=
  fun {a} {b} =>
    fun arg_96__ arg_97__ =>
      match arg_96__ , arg_97__ with
        | Mk_StateL kf , Mk_StateL kv => GHC.Base.op_zd__ Mk_StateL (fun s =>
                                                            match kf s with
                                                              | pair s' f => match kv s' with
                                                                               | pair s'' v => pair s'' (f v)
                                                                             end
                                                            end)
      end.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateL_s__op_ztzg__ {inst_s}
    : forall {a} {b}, (StateL inst_s) a -> (StateL inst_s) b -> (StateL inst_s) b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__Data_Traversable_StateL_s__op_zlztzg__
      (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateL_s__pure {inst_s}
    : forall {a}, a -> (StateL inst_s) a :=
  fun {a} => fun x => Mk_StateL (fun s => pair s x).

Program Instance instance_GHC_Base_Applicative__Data_Traversable_StateL_s_ {s}
  : GHC.Base.Applicative (StateL s) := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateL_s__op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateL_s__op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateL_s__pure |}.

Local Definition instance_GHC_Base_Functor__Data_Traversable_StateR_s__fmap {inst_s}
    : forall {a} {b}, (a -> b) -> (StateR inst_s) a -> (StateR inst_s) b :=
  fun {a} {b} =>
    fun arg_88__ arg_89__ =>
      match arg_88__ , arg_89__ with
        | f , Mk_StateR k => GHC.Base.op_zd__ Mk_StateR (fun s =>
                                                match k s with
                                                  | pair s' v => pair s' (f v)
                                                end)
      end.

Local Definition instance_GHC_Base_Functor__Data_Traversable_StateR_s__op_zlzd__ {inst_s}
    : forall {a} {b}, a -> (StateR inst_s) b -> (StateR inst_s) a :=
  fun {a} {b} =>
    fun x =>
      instance_GHC_Base_Functor__Data_Traversable_StateR_s__fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor__Data_Traversable_StateR_s_ {s}
  : GHC.Base.Functor (StateR s) := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Traversable_StateR_s__op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor__Data_Traversable_StateR_s__fmap |}.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateR_s__op_zlztzg__ {inst_s}
    : forall {a} {b},
        (StateR inst_s) (a -> b) -> (StateR inst_s) a -> (StateR inst_s) b :=
  fun {a} {b} =>
    fun arg_81__ arg_82__ =>
      match arg_81__ , arg_82__ with
        | Mk_StateR kf , Mk_StateR kv => GHC.Base.op_zd__ Mk_StateR (fun s =>
                                                            match kv s with
                                                              | pair s' v => match kf s' with
                                                                               | pair s'' f => pair s'' (f v)
                                                                             end
                                                            end)
      end.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateR_s__op_ztzg__ {inst_s}
    : forall {a} {b}, (StateR inst_s) a -> (StateR inst_s) b -> (StateR inst_s) b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__Data_Traversable_StateR_s__op_zlztzg__
      (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative__Data_Traversable_StateR_s__pure {inst_s}
    : forall {a}, a -> (StateR inst_s) a :=
  fun {a} => fun x => Mk_StateR (fun s => pair s x).

Program Instance instance_GHC_Base_Applicative__Data_Traversable_StateR_s_ {s}
  : GHC.Base.Applicative (StateR s) := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateR_s__op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateR_s__op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative__Data_Traversable_StateR_s__pure |}.

Local Definition instance_GHC_Base_Functor_Data_Traversable_Id_fmap : forall {a}
                                                                             {b},
                                                                        (a -> b) -> Id a -> Id b :=
  fun {a} {b} =>
    fun arg_75__ arg_76__ =>
      match arg_75__ , arg_76__ with
        | f , Mk_Id x => Mk_Id (f x)
      end.

Local Definition instance_GHC_Base_Functor_Data_Traversable_Id_op_zlzd__
    : forall {a} {b}, a -> Id b -> Id a :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_Data_Traversable_Id_fmap (GHC.Base.const x).

Program Instance instance_GHC_Base_Functor_Data_Traversable_Id
  : GHC.Base.Functor Id := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Traversable_Id_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} =>
        instance_GHC_Base_Functor_Data_Traversable_Id_fmap |}.

Local Definition instance_GHC_Base_Applicative_Data_Traversable_Id_op_zlztzg__
    : forall {a} {b}, Id (a -> b) -> Id a -> Id b :=
  fun {a} {b} =>
    fun arg_71__ arg_72__ =>
      match arg_71__ , arg_72__ with
        | Mk_Id f , Mk_Id x => Mk_Id (f x)
      end.

Local Definition instance_GHC_Base_Applicative_Data_Traversable_Id_op_ztzg__
    : forall {a} {b}, Id a -> Id b -> Id b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative_Data_Traversable_Id_op_zlztzg__ (GHC.Base.fmap
                                                                    (GHC.Base.const GHC.Base.id) x) y.

Local Definition instance_GHC_Base_Applicative_Data_Traversable_Id_pure
    : forall {a}, a -> Id a :=
  fun {a} => Mk_Id.

Program Instance instance_GHC_Base_Applicative_Data_Traversable_Id
  : GHC.Base.Applicative Id := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Traversable_Id_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} =>
        instance_GHC_Base_Applicative_Data_Traversable_Id_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} =>
        instance_GHC_Base_Applicative_Data_Traversable_Id_pure |}.

(* Skipping instance instance_Data_Traversable_Traversable_GHC_Generics_V1 *)

(* Skipping instance instance_Data_Traversable_Traversable_GHC_Generics_Par1 *)

(* Skipping instance
   instance_forall___Data_Traversable_Traversable_f___Data_Traversable_Traversable__GHC_Generics_Rec1_f_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_K1_i_c_ *)

(* Skipping instance
   instance_forall___Data_Traversable_Traversable_f___Data_Traversable_Traversable__GHC_Generics_M1_i_c_f_ *)

(* Skipping instance
   instance_forall___Data_Traversable_Traversable_f____Data_Traversable_Traversable_g___Data_Traversable_Traversable__GHC_Generics_op_ZCzpZC___f_g_ *)

(* Skipping instance
   instance_forall___Data_Traversable_Traversable_f____Data_Traversable_Traversable_g___Data_Traversable_Traversable__GHC_Generics_op_ZCztZC___f_g_ *)

(* Skipping instance
   instance_forall___Data_Traversable_Traversable_f____Data_Traversable_Traversable_g___Data_Traversable_Traversable__GHC_Generics_op_ZCziZC___f_g_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec__GHC_Ptr_Ptr_unit__ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec_GHC_Char_Char_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec_GHC_Types_Double_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec_GHC_Types_Float_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec_GHC_Num_Int_ *)

(* Skipping instance
   instance_Data_Traversable_Traversable__GHC_Generics_URec_GHC_Num_Word_ *)

Definition fmapDefault {t} {a} {b} `{Traversable t} : (a -> b) -> t a -> t b :=
  fun f => GHC.Base.op_z2218U__ getId (traverse (GHC.Base.op_z2218U__ Mk_Id f)).

Definition forM {t} {m} {a} {b} `{Traversable t} `{GHC.Base.Monad m} : t
                                                                       a -> (a -> m b) -> m (t b) :=
  GHC.Base.flip mapM.

Definition for_ {t} {f} {a} {b} `{Traversable t} `{GHC.Base.Applicative f} : t
                                                                             a -> (a -> f b) -> f (t b) :=
  GHC.Base.flip traverse.

Definition mapAccumL {t} {a} {b} {c} `{Traversable t} : (a -> b -> a *
                                                        c) -> a -> t b -> a * t c :=
  fun f s t =>
    runStateL (traverse (GHC.Base.op_z2218U__ Mk_StateL (GHC.Base.flip f)) t) s.

Definition mapAccumR {t} {a} {b} {c} `{Traversable t} : (a -> b -> a *
                                                        c) -> a -> t b -> a * t c :=
  fun f s t =>
    runStateR (traverse (GHC.Base.op_z2218U__ Mk_StateR (GHC.Base.flip f)) t) s.

(* Unbound variables:
     * Some cons list nil option pair Data.Either.Either Data.Either.Mk_Left
     Data.Either.Mk_Right Data.Foldable.Foldable Data.Functor.op_zlzdzg__
     Data.Functor.Const.Const Data.Functor.Const.Mk_Const Data.Monoid.Dual
     Data.Monoid.Mk_Dual Data.Monoid.Mk_Product Data.Monoid.Mk_Sum
     Data.Monoid.Product Data.Monoid.Sum Data.Proxy.Mk_Proxy Data.Proxy.Proxy
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.foldr GHC.Base.id GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zlztzg__ GHC.Base.pure
*)
