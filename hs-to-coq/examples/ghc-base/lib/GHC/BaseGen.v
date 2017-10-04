(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Export Prim.

(* Converted imports: *)

Require GHC.Types.
Require GHC.Classes.
Require GHC.CString.
Require GHC.Magic.
Require GHC.Prim.
Require GHC.Err.
Require GHC.IO.
Require GHC.Tuple.
Require GHC.Integer.
Require Coq.Lists.List.

(* Converted declarations: *)

Local Definition instance_Monoid_unit_mappend : unit -> unit -> unit :=
  fun arg_213__ arg_214__ => tt.

Local Definition instance_Monoid_unit_mconcat : list unit -> unit :=
  fun arg_215__ => tt.

Local Definition instance_Monoid_unit_mempty : unit :=
  tt.

Local Definition instance_Monoid_comparison_mappend
    : comparison -> comparison -> comparison :=
  fun arg_190__ arg_191__ =>
    match arg_190__ , arg_191__ with
      | Lt , _ => Lt
      | Eq , y => y
      | Gt , _ => Gt
    end.

Local Definition instance_Monoid_comparison_mempty : comparison :=
  Eq.

Local Definition instance_Functor_option_fmap : forall {a} {b},
                                                  (a -> b) -> option a -> option b :=
  fun {a} {b} =>
    fun arg_182__ arg_183__ =>
      match arg_182__ , arg_183__ with
        | _ , None => None
        | f , (Some a) => Some (f a)
      end.

Local Definition instance_Applicative_option_op_ztzg__ : forall {a} {b},
                                                           option a -> option b -> option b :=
  fun {a} {b} =>
    fun arg_179__ arg_180__ =>
      match arg_179__ , arg_180__ with
        | (Some _m1) , m2 => m2
        | None , _m2 => None
      end.

Local Definition instance_Applicative_option_pure : forall {a}, a -> option a :=
  fun {a} => Some.

Local Definition instance_Monad_option_op_zgzgze__ : forall {a} {b},
                                                       option a -> (a -> option b) -> option b :=
  fun {a} {b} =>
    fun arg_170__ arg_171__ =>
      match arg_170__ , arg_171__ with
        | (Some x) , k => k x
        | None , _ => None
      end.

(* Skipping instance instance_Alternative_option *)

(* Skipping instance instance_MonadPlus_option *)

Local Definition instance_Applicative_list_op_zlztzg__ : forall {a} {b},
                                                           list (a -> b) -> list a -> list b :=
  fun {a} {b} =>
    fun arg_159__ arg_160__ =>
      match arg_159__ , arg_160__ with
        | fs , xs => Coq.Lists.List.flat_map (fun f =>
                                               Coq.Lists.List.flat_map (fun x => cons (f x) nil) xs) fs
      end.

Local Definition instance_Applicative_list_op_ztzg__ : forall {a} {b},
                                                         list a -> list b -> list b :=
  fun {a} {b} =>
    fun arg_163__ arg_164__ =>
      match arg_163__ , arg_164__ with
        | xs , ys => Coq.Lists.List.flat_map (fun _ =>
                                               Coq.Lists.List.flat_map (fun y => cons y nil) ys) xs
      end.

Local Definition instance_Applicative_list_pure : forall {a}, a -> list a :=
  fun {a} => fun arg_156__ => match arg_156__ with | x => cons x nil end.

Local Definition instance_Monad_list_op_zgzgze__ : forall {a} {b},
                                                     list a -> (a -> list b) -> list b :=
  fun {a} {b} =>
    fun arg_151__ arg_152__ =>
      match arg_151__ , arg_152__ with
        | xs , f => Coq.Lists.List.flat_map (fun x =>
                                              Coq.Lists.List.flat_map (fun y => cons y nil) (f x)) xs
      end.

(* Skipping instance instance_Alternative_list *)

(* Skipping instance instance_MonadPlus_list *)

(* Skipping instance instance_Functor_GHC_Types_IO *)

(* Skipping instance instance_Applicative_GHC_Types_IO *)

(* Skipping instance instance_Monad_GHC_Types_IO *)

(* Skipping instance instance_Alternative_GHC_Types_IO *)

(* Skipping instance instance_MonadPlus_GHC_Types_IO *)

Definition assert {a} : bool -> a -> a :=
  fun arg_49__ arg_50__ => match arg_49__ , arg_50__ with | _pred , r => r end.

Definition breakpoint {a} : a -> a :=
  fun arg_47__ => match arg_47__ with | r => r end.

Definition breakpointCond {a} : bool -> a -> a :=
  fun arg_44__ arg_45__ => match arg_44__ , arg_45__ with | _ , r => r end.

Definition const {a} {b} : a -> b -> a :=
  fun arg_41__ arg_42__ => match arg_41__ , arg_42__ with | x , _ => x end.

Definition asTypeOf {a} : a -> a -> a :=
  const.

Definition foldr {a} {b} : (a -> b -> b) -> b -> list a -> b :=
  fun arg_66__ arg_67__ =>
    match arg_66__ , arg_67__ with
      | k , z => let go :=
                   fix go arg_68__
                         := match arg_68__ with
                              | nil => z
                              | (cons y ys) => k y (go ys)
                            end in
                 go
    end.

Local Definition instance_Monoid_comparison_mconcat : list
                                                      comparison -> comparison :=
  foldr instance_Monoid_comparison_mappend instance_Monoid_comparison_mempty.

Definition id {a} : a -> a :=
  fun arg_52__ => match arg_52__ with | x => x end.

Axiom ifThenElse : forall {A : Type}, A.

(* Translating `ifThenElse' failed: overloaded if-then-else unsupported *)

Definition map {a} {b} : (a -> b) -> list a -> list b :=
  fix map arg_62__ arg_63__
        := match arg_62__ , arg_63__ with
             | _ , nil => nil
             | f , (cons x xs) => cons (f x) (map f xs)
           end.

Local Definition instance_Functor_list_fmap : forall {a} {b},
                                                (a -> b) -> list a -> list b :=
  fun {a} {b} => map.

Definition mapFB {elt} {lst} {a}
    : (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst :=
  fun arg_54__ arg_55__ =>
    match arg_54__ , arg_55__ with
      | c , f => fun arg_56__ arg_57__ =>
                   match arg_56__ , arg_57__ with
                     | x , ys => c (f x) ys
                   end
    end.

Definition op_z2218U__ {b} {c} {a} : (b -> c) -> (a -> b) -> a -> c :=
  fun arg_34__ arg_35__ =>
    match arg_34__ , arg_35__ with
      | f , g => fun arg_36__ => match arg_36__ with | x => f (g x) end
    end.

Infix "∘" := (op_z2218U__) (left associativity, at level 40).

Notation "'_∘_'" := (op_z2218U__).

Local Definition instance_Functor_list_op_zlzd__ : forall {a} {b},
                                                     a -> list b -> list a :=
  fun {a} {b} => op_z2218U__ instance_Functor_list_fmap const.

Local Definition instance_Functor_option_op_zlzd__ : forall {a} {b},
                                                       a -> option b -> option a :=
  fun {a} {b} => op_z2218U__ instance_Functor_option_fmap const.

Definition op_zd__ {a} {b} : (a -> b) -> a -> b :=
  fun arg_30__ arg_31__ => match arg_30__ , arg_31__ with | f , x => f x end.

Infix "$" := (op_zd__) (at level 99).

Notation "'_$_'" := (op_zd__).

Definition op_zdzn__ {a} {b} : (a -> b) -> a -> b :=
  fun arg_26__ arg_27__ =>
    match arg_26__ , arg_27__ with
      | f , x => match x with
                   | vx => f vx
                 end
    end.

Infix "$!" := (op_zdzn__) (at level 99).

Notation "'_$!_'" := (op_zdzn__).

Definition otherwise : bool :=
  true.

Axiom when : forall {A : Type}, A.

(* Translating `when' failed: overloaded if-then-else unsupported *)

Class Functor f := {
  op_zlzd__ : forall {a} {b}, a -> f b -> f a ;
  fmap : forall {a} {b}, (a -> b) -> f a -> f b }.

Infix "<$" := (op_zlzd__) (at level 99).

Notation "'_<$_'" := (op_zlzd__).

Class Applicative f `{Functor f} := {
  op_ztzg__ : forall {a} {b}, f a -> f b -> f b ;
  op_zlzt__ : forall {a} {b}, f a -> f b -> f a ;
  op_zlztzg__ : forall {a} {b}, f (a -> b) -> f a -> f b ;
  pure : forall {a}, a -> f a }.

Infix "*>" := (op_ztzg__) (at level 99).

Notation "'_*>_'" := (op_ztzg__).

Infix "<*" := (op_zlzt__) (at level 99).

Notation "'_<*_'" := (op_zlzt__).

Infix "<*>" := (op_zlztzg__) (at level 99).

Notation "'_<*>_'" := (op_zlztzg__).

Class Monad m `{Applicative m} := {
  op_zgzg__ : forall {a} {b}, m a -> m b -> m b ;
  op_zgzgze__ : forall {a} {b}, m a -> (a -> m b) -> m b ;
  return_ : forall {a}, a -> m a }.

Infix ">>" := (op_zgzg__) (at level 99).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>=" := (op_zgzgze__) (at level 99).

Notation "'_>>=_'" := (op_zgzgze__).

Definition op_zezlzl__ {m} {a} {b} `{Monad m} : (a -> m b) -> m a -> m b :=
  fun arg_115__ arg_116__ =>
    match arg_115__ , arg_116__ with
      | f , x => op_zgzgze__ x f
    end.

Infix "=<<" := (op_zezlzl__) (at level 99).

Notation "'_=<<_'" := (op_zezlzl__).

Definition liftM5 {m} {a1} {a2} {a3} {a4} {a5} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> a5 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m
      r :=
  fun arg_76__ arg_77__ arg_78__ arg_79__ arg_80__ arg_81__ =>
    match arg_76__ , arg_77__ , arg_78__ , arg_79__ , arg_80__ , arg_81__ with
      | f , m1 , m2 , m3 , m4 , m5 => (m1 >>= fun x1 =>
                                        (m2 >>= fun x2 =>
                                          (m3 >>= fun x3 =>
                                            (m4 >>= fun x4 => (m5 >>= fun x5 => return_ (f x1 x2 x3 x4 x5))))))
    end.

Definition liftM4 {m} {a1} {a2} {a3} {a4} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m r :=
  fun arg_84__ arg_85__ arg_86__ arg_87__ arg_88__ =>
    match arg_84__ , arg_85__ , arg_86__ , arg_87__ , arg_88__ with
      | f , m1 , m2 , m3 , m4 => (m1 >>= fun x1 =>
                                   (m2 >>= fun x2 =>
                                     (m3 >>= fun x3 => (m4 >>= fun x4 => return_ (f x1 x2 x3 x4)))))
    end.

Definition liftM3 {m} {a1} {a2} {a3} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> r) -> m a1 -> m a2 -> m a3 -> m r :=
  fun arg_91__ arg_92__ arg_93__ arg_94__ =>
    match arg_91__ , arg_92__ , arg_93__ , arg_94__ with
      | f , m1 , m2 , m3 => (m1 >>= fun x1 =>
                              (m2 >>= fun x2 => (m3 >>= fun x3 => return_ (f x1 x2 x3))))
    end.

Definition liftM2 {m} {a1} {a2} {r} `{(Monad m)} : (a1 -> a2 -> r) -> m a1 -> m
                                                   a2 -> m r :=
  fun arg_97__ arg_98__ arg_99__ =>
    match arg_97__ , arg_98__ , arg_99__ with
      | f , m1 , m2 => (m1 >>= fun x1 => (m2 >>= fun x2 => return_ (f x1 x2)))
    end.

Definition liftM {m} {a1} {r} `{(Monad m)} : (a1 -> r) -> m a1 -> m r :=
  fun arg_102__ arg_103__ =>
    match arg_102__ , arg_103__ with
      | f , m1 => (m1 >>= fun x1 => return_ (f x1))
    end.

Definition join {m} {a} `{(Monad m)} : m (m a) -> m a :=
  fun arg_119__ => match arg_119__ with | x => op_zgzgze__ x id end.

Definition mapM {m} {a} {b} `{Monad m} : (a -> m b) -> list a -> m (list b) :=
  fun arg_106__ arg_107__ =>
    match arg_106__ , arg_107__ with
      | f , as_ => let k :=
                     fun arg_108__ arg_109__ =>
                       match arg_108__ , arg_109__ with
                         | a , r => (f a >>= fun x => (r >>= fun xs => return_ (cons x xs)))
                       end in
                   foldr k (return_ nil) as_
    end.

Definition sequence {m} {a} `{Monad m} : list (m a) -> m (list a) :=
  mapM id.

Definition ap {m} {a} {b} `{(Monad m)} : m (a -> b) -> m a -> m b :=
  fun arg_72__ arg_73__ =>
    match arg_72__ , arg_73__ with
      | m1 , m2 => (m1 >>= fun x1 => (m2 >>= fun x2 => return_ (x1 x2)))
    end.

Class Alternative f `{Applicative f} := {
  op_zlzbzg__ : forall {a}, f a -> f a -> f a ;
  empty : forall {a}, f a ;
  many : forall {a}, f a -> f (list a) ;
  some : forall {a}, f a -> f (list a) }.

Infix "<|>" := (op_zlzbzg__) (at level 99).

Notation "'_<|>_'" := (op_zlzbzg__).

Class MonadPlus m `{Alternative m} `{Monad m} := {
  mplus : forall {a}, m a -> m a -> m a ;
  mzero : forall {a}, m a }.

Definition liftA {f} {a} {b} `{Applicative f} : (a -> b) -> f a -> f b :=
  fun arg_133__ arg_134__ =>
    match arg_133__ , arg_134__ with
      | f , a => op_zlztzg__ (pure f) a
    end.

Definition liftA3 {f} {a} {b} {c} {d} `{Applicative f} : (a -> b -> c -> d) -> f
                                                         a -> f b -> f c -> f d :=
  fun arg_122__ arg_123__ arg_124__ arg_125__ =>
    match arg_122__ , arg_123__ , arg_124__ , arg_125__ with
      | f , a , b , c => op_zlztzg__ (op_zlztzg__ (fmap f a) b) c
    end.

Definition liftA2 {f} {a} {b} {c} `{Applicative f} : (a -> b -> c) -> f a -> f
                                                     b -> f c :=
  fun arg_128__ arg_129__ arg_130__ =>
    match arg_128__ , arg_129__ , arg_130__ with
      | f , a , b => op_zlztzg__ (fmap f a) b
    end.

Definition op_zlztztzg__ {f} {a} {b} `{Applicative f} : f a -> f (a -> b) -> f
                                                        b :=
  liftA2 (flip op_zd__).

Infix "<**>" := (op_zlztztzg__) (at level 99).

Notation "'_<**>_'" := (op_zlztztzg__).

Instance instance_Functor_list : !Functor list := {
  fmap := fun {a} {b} => instance_Functor_list_fmap ;
  op_zlzd__ := fun {a} {b} => instance_Functor_list_op_zlzd__ }.

Local Definition instance_Applicative_list_op_zlzt__ : forall {a} {b},
                                                         list a -> list b -> list a :=
  fun {a} {b} =>
    fun arg_6__ arg_7__ =>
      match arg_6__ , arg_7__ with
        | a , b => instance_Applicative_list_op_zlztzg__ (fmap const a) b
      end.

Instance instance_Applicative_list : !Applicative list := {
  op_zlzt__ := fun {a} {b} => instance_Applicative_list_op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} => instance_Applicative_list_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_Applicative_list_op_ztzg__ ;
  pure := fun {a} => instance_Applicative_list_pure }.

Local Definition instance_Monad_list_op_zgzg__ : forall {a} {b},
                                                   list a -> list b -> list b :=
  fun {a} {b} => op_ztzg__.

Local Definition instance_Monad_list_return_ : forall {a}, a -> list a :=
  fun {a} => pure.

Instance instance_Monad_list : !Monad list := {
  op_zgzg__ := fun {a} {b} => instance_Monad_list_op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} => instance_Monad_list_op_zgzgze__ ;
  return_ := fun {a} => instance_Monad_list_return_ }.

Instance instance_Functor_option : !Functor option := {
  fmap := fun {a} {b} => instance_Functor_option_fmap ;
  op_zlzd__ := fun {a} {b} => instance_Functor_option_op_zlzd__ }.

Local Definition instance_Applicative_option_op_zlztzg__ : forall {a} {b},
                                                             option (a -> b) -> option a -> option b :=
  fun {a} {b} =>
    fun arg_175__ arg_176__ =>
      match arg_175__ , arg_176__ with
        | (Some f) , m => fmap f m
        | None , _m => None
      end.

Local Definition instance_Applicative_option_op_zlzt__ : forall {a} {b},
                                                           option a -> option b -> option a :=
  fun {a} {b} =>
    fun arg_6__ arg_7__ =>
      match arg_6__ , arg_7__ with
        | a , b => instance_Applicative_option_op_zlztzg__ (fmap const a) b
      end.

Instance instance_Applicative_option : !Applicative option := {
  op_zlzt__ := fun {a} {b} => instance_Applicative_option_op_zlzt__ ;
  op_zlztzg__ := fun {a} {b} => instance_Applicative_option_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_Applicative_option_op_ztzg__ ;
  pure := fun {a} => instance_Applicative_option_pure }.

Local Definition instance_Monad_option_op_zgzg__ : forall {a} {b},
                                                     option a -> option b -> option b :=
  fun {a} {b} => op_ztzg__.

Local Definition instance_Monad_option_return_ : forall {a}, a -> option a :=
  fun {a} => pure.

Instance instance_Monad_option : !Monad option := {
  op_zgzg__ := fun {a} {b} => instance_Monad_option_op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} => instance_Monad_option_op_zgzgze__ ;
  return_ := fun {a} => instance_Monad_option_return_ }.

Class Monoid a := {
  mappend : a -> a -> a ;
  mconcat : list a -> a ;
  mempty : a }.

Local Definition instance_forall___Monoid_a___Monoid__option_a__mempty `{Monoid
                                                                       a} : (option a) :=
  None.

Local Definition instance_forall___Monoid_a___Monoid__option_a__mappend `{Monoid
                                                                        a} : (option a) -> (option a) -> (option a) :=
  fun arg_186__ arg_187__ =>
    match arg_186__ , arg_187__ with
      | None , m => m
      | m , None => m
      | (Some m1) , (Some m2) => Some (mappend m1 m2)
    end.

Local Definition instance_forall___Monoid_a___Monoid__option_a__mconcat `{Monoid
                                                                        a} : list (option a) -> (option a) :=
  foldr instance_forall___Monoid_a___Monoid__option_a__mappend
  instance_forall___Monoid_a___Monoid__option_a__mempty.

Instance instance_forall___Monoid_a___Monoid__option_a_ : !forall `{Monoid a},
                                                            Monoid (option a) := {
  mappend := instance_forall___Monoid_a___Monoid__option_a__mappend ;
  mconcat := instance_forall___Monoid_a___Monoid__option_a__mconcat ;
  mempty := instance_forall___Monoid_a___Monoid__option_a__mempty }.

Instance instance_Monoid_comparison : !Monoid comparison := {
  mappend := instance_Monoid_comparison_mappend ;
  mconcat := instance_Monoid_comparison_mconcat ;
  mempty := instance_Monoid_comparison_mempty }.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mempty `{Monoid
                                                                                                                                a}
                                                                                                                                `{Monoid
                                                                                                                                b}
                                                                                                                                `{Monoid
                                                                                                                                c}
                                                                                                                                `{Monoid
                                                                                                                                d}
                                                                                                                                `{Monoid
                                                                                                                                e}
    : a * b * c * d * e :=
  pair (pair (pair (pair mempty mempty) mempty) mempty) mempty.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mappend `{Monoid
                                                                                                                                 a}
                                                                                                                                 `{Monoid
                                                                                                                                 b}
                                                                                                                                 `{Monoid
                                                                                                                                 c}
                                                                                                                                 `{Monoid
                                                                                                                                 d}
                                                                                                                                 `{Monoid
                                                                                                                                 e}
    : a * b * c * d * e -> a * b * c * d * e -> a * b * c * d * e :=
  fun arg_194__ arg_195__ =>
    match arg_194__ , arg_195__ with
      | (pair (pair (pair (pair a1 b1) c1) d1) e1) , (pair (pair (pair (pair a2 b2)
                                                                       c2) d2) e2) => pair (pair (pair (pair (mappend a1
                                                                                                                      a2)
                                                                                                             (mappend b1
                                                                                                                      b2))
                                                                                                       (mappend c1 c2))
                                                                                                 (mappend d1 d2))
                                                                                           (mappend e1 e2)
    end.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mconcat `{Monoid
                                                                                                                                 a}
                                                                                                                                 `{Monoid
                                                                                                                                 b}
                                                                                                                                 `{Monoid
                                                                                                                                 c}
                                                                                                                                 `{Monoid
                                                                                                                                 d}
                                                                                                                                 `{Monoid
                                                                                                                                 e}
    : list (a * b * c * d * e) -> a * b * c * d * e :=
  foldr
  instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mappend
  instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mempty.

Instance instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e_
  : !forall `{Monoid a} `{Monoid b} `{Monoid c} `{Monoid d} `{Monoid e},
      Monoid (a * b * c * d * e) := {
  mappend := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mappend ;
  mconcat := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mconcat ;
  mempty := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d____Monoid_e___Monoid__a___b___c___d___e__mempty }.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mempty `{Monoid
                                                                                                                a}
                                                                                                                `{Monoid
                                                                                                                b}
                                                                                                                `{Monoid
                                                                                                                c}
                                                                                                                `{Monoid
                                                                                                                d} : a *
                                                                                                                     b *
                                                                                                                     c *
                                                                                                                     d :=
  pair (pair (pair mempty mempty) mempty) mempty.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mappend `{Monoid
                                                                                                                 a}
                                                                                                                 `{Monoid
                                                                                                                 b}
                                                                                                                 `{Monoid
                                                                                                                 c}
                                                                                                                 `{Monoid
                                                                                                                 d} : a
                                                                                                                      *
                                                                                                                      b
                                                                                                                      *
                                                                                                                      c
                                                                                                                      *
                                                                                                                      d -> a
                                                                                                                      *
                                                                                                                      b
                                                                                                                      *
                                                                                                                      c
                                                                                                                      *
                                                                                                                      d -> a
                                                                                                                      *
                                                                                                                      b
                                                                                                                      *
                                                                                                                      c
                                                                                                                      *
                                                                                                                      d :=
  fun arg_199__ arg_200__ =>
    match arg_199__ , arg_200__ with
      | (pair (pair (pair a1 b1) c1) d1) , (pair (pair (pair a2 b2) c2) d2) => pair
                                                                               (pair (pair (mappend a1 a2) (mappend b1
                                                                                                                    b2))
                                                                                     (mappend c1 c2)) (mappend d1 d2)
    end.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mconcat `{Monoid
                                                                                                                 a}
                                                                                                                 `{Monoid
                                                                                                                 b}
                                                                                                                 `{Monoid
                                                                                                                 c}
                                                                                                                 `{Monoid
                                                                                                                 d}
    : list (a * b * c * d) -> a * b * c * d :=
  foldr
  instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mappend
  instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mempty.

Instance instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d_
  : !forall `{Monoid a} `{Monoid b} `{Monoid c} `{Monoid d},
      Monoid (a * b * c * d) := {
  mappend := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mappend ;
  mconcat := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mconcat ;
  mempty := instance_forall___Monoid_a____Monoid_b____Monoid_c____Monoid_d___Monoid__a___b___c___d__mempty }.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mempty `{Monoid
                                                                                                a} `{Monoid b} `{Monoid
                                                                                                c} : a * b * c :=
  pair (pair mempty mempty) mempty.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mappend `{Monoid
                                                                                                 a} `{Monoid b} `{Monoid
                                                                                                 c} : a * b * c -> a * b
                                                                                                      * c -> a * b *
                                                                                                      c :=
  fun arg_204__ arg_205__ =>
    match arg_204__ , arg_205__ with
      | (pair (pair a1 b1) c1) , (pair (pair a2 b2) c2) => pair (pair (mappend a1 a2)
                                                                      (mappend b1 b2)) (mappend c1 c2)
    end.

Local Definition instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mconcat `{Monoid
                                                                                                 a} `{Monoid b} `{Monoid
                                                                                                 c} : list (a * b *
                                                                                                           c) -> a * b *
                                                                                                      c :=
  foldr
  instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mappend
  instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mempty.

Instance instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c_
  : !forall `{Monoid a} `{Monoid b} `{Monoid c}, Monoid (a * b * c) := {
  mappend := instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mappend ;
  mconcat := instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mconcat ;
  mempty := instance_forall___Monoid_a____Monoid_b____Monoid_c___Monoid__a___b___c__mempty }.

Local Definition instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mempty `{Monoid
                                                                                a} `{Monoid b} : a * b :=
  pair mempty mempty.

Local Definition instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mappend `{Monoid
                                                                                 a} `{Monoid b} : a * b -> a * b -> a *
                                                                                                  b :=
  fun arg_209__ arg_210__ =>
    match arg_209__ , arg_210__ with
      | (pair a1 b1) , (pair a2 b2) => pair (mappend a1 a2) (mappend b1 b2)
    end.

Local Definition instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mconcat `{Monoid
                                                                                 a} `{Monoid b} : list (a * b) -> a *
                                                                                                  b :=
  foldr instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mappend
  instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mempty.

Instance instance_forall___Monoid_a____Monoid_b___Monoid__a___b_
  : !forall `{Monoid a} `{Monoid b}, Monoid (a * b) := {
  mappend := instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mappend ;
  mconcat := instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mconcat ;
  mempty := instance_forall___Monoid_a____Monoid_b___Monoid__a___b__mempty }.

Instance instance_Monoid_unit : !Monoid unit := {
  mappend := instance_Monoid_unit_mappend ;
  mconcat := instance_Monoid_unit_mconcat ;
  mempty := instance_Monoid_unit_mempty }.

(* Unbound variables:
     * Coq.Lists.List.flat_map Eq None Some bool comparison cons e flip list nil
     option pair true tt unit
*)
