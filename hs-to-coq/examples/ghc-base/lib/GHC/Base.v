(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

(* This includes everything that should be defined in GHC/Base.hs, but cannot
   be generated from Base.hs.

The types defined in GHC.Base:

  list, (), Int, Bool, Ordering, Char, String

are all mapped to corresponding Coq types. Therefore, the Eq/Ord classes must
be defined in this module so that we can create instances for these types.

 *)

(* SSreflect library *)
Require Export mathcomp.ssreflect.ssreflect.

Generalizable All Variables.
Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(********************* Types ************************)

(* List notation *)
Require Export Coq.Lists.List.

(* Booleans *)
Require Export Bool.Bool.

(* Int and Integer types *)
Require Export GHC.Num.

(* Char type *)
Require Export GHC.Char.


(* Strings *)
Require Coq.Strings.String.
Definition String := list Char.

Bind Scope string_scope with String.string.
Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").

(* IO --- PUNT *)
Definition FilePath := String.

(* ASZ: I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.
Inductive IOError : Type :=.

(****************************************************)

(* function composition *)
Require Export Coq.Program.Basics.

Notation "[,]"  := (fun x y => (x,y)).
Notation "[,,]" := (fun x0 y1 z2 => (x0, y1, z2)).
Notation "[,,,]" := (fun x0 x1 x2 x3 => (x0,x1,x2,x3)).
Notation "[,,,,]" := (fun x0 x1 x2 x3 x4 => (x0,x1,x2,x3,x4)).
Notation "[,,,,,]" := (fun x0 x1 x2 x3 x4 x5 => (x0,x1,x2,x3,x4,x5)).
Notation "[,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 => (x0,x1,x2,x3,x4,x5,x6)).
Notation "[,,,,,,,]" := (fun x0 x1 x2 x3 x4 x5 x6 x7 => (x0,x1,x2,x3,x4,x5,x6,x7)).

Notation "'_++_'"   := (fun x y => x ++ y).
Notation "'_::_'"   := (fun x y => x :: y).

Notation "[->]"  := (fun x y => x -> y).

(* Configure type argument to be maximally inserted *)
Arguments List.app {_} _ _.

(****************************************************)


Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(****************************************************)

Axiom errorWithoutStackTrace : forall {A : Type}, String -> A.


(*********** built in classes Eq & Ord **********************)

(* Don't clash with Eq constructor for the comparison type. *)
Class Eq_ a := {
  op_zsze__ : (a -> (a -> bool)) ;
  op_zeze__ : (a -> (a -> bool)) }.

Infix "/=" := (op_zsze__) (no associativity, at level 70).

Notation "'_/=_'" := (op_zsze__).

Infix "==" := (op_zeze__) (no associativity, at level 70).

Notation "'_==_'" := (op_zeze__).

Class Ord a `{((Eq_ a))} := {
  op_zl__ : (a -> (a -> bool)) ;
  op_zlze__ : (a -> (a -> bool)) ;
  op_zg__ : (a -> (a -> bool)) ;
  op_zgze__ : (a -> (a -> bool)) ;
  compare : (a -> (a -> comparison)) ;
  max : (a -> (a -> a)) ;
  min : (a -> (a -> a)) }.

(* Don't clash with Coq's standard ordering predicates. *)
Infix "<?" := (op_zl__) (no associativity, at level 70).

Notation "'_<?_'" := (op_zl__).

Infix "<=?" := (op_zlze__) (no associativity, at level 70).

Notation "'_<=?_'" := (op_zlze__).

Infix ">?" := (op_zg__) (no associativity, at level 70).

Notation "'_>?_'" := (op_zg__).

Infix ">=?" := (op_zgze__) (no associativity, at level 70).

Notation "'_>=?_'" := (op_zgze__).

(*********** Eq/Ord for primitive types **************************)

Instance Eq_Int___ : Eq_ Int := {
                               op_zsze__ := fun x y => (x =? y)%Z;
                               op_zeze__ := fun x y => negb (x =? y)%Z;
                             }.

Instance Ord_Int___ : !Ord Int := {
  op_zl__   := fun x y => (x <? y)%Z;
  op_zlze__ := fun x y => (x <=? y)%Z;
  op_zg__   := fun x y => (y <? x)%Z;
  op_zgze__ := fun x y => (y <=? x)%Z;
  compare   := Z.compare%Z ;
  max       := Z.max%Z;
  min       := Z.min%Z;
}.

Instance Eq_Integer___ : Eq_ Integer := {
                               op_zsze__ := fun x y => (x =? y)%Z;
                               op_zeze__ := fun x y => negb (x =? y)%Z;
                             }.

Instance Ord_Integer___ : !Ord Int := {
  op_zl__   := fun x y => (x <? y)%Z;
  op_zlze__ := fun x y => (x <=? y)%Z;
  op_zg__   := fun x y => (y <? x)%Z;
  op_zgze__ := fun x y => (y <=? x)%Z;
  compare   := Z.compare%Z ;
  max       := Z.max%Z;
  min       := Z.min%Z;
}.

Instance Eq_Word___ : Eq_ Word := {
                               op_zsze__ := fun x y => (x =? y)%N;
                               op_zeze__ := fun x y => negb (x =? y)%N;
                             }.

Instance Ord_Word___ : !Ord Word := {
  op_zl__   := fun x y => (x <? y)%N;
  op_zlze__ := fun x y => (x <=? y)%N;
  op_zg__   := fun x y => (y <? x)%N;
  op_zgze__ := fun x y => (y <=? x)%N;
  compare   := N.compare%N ;
  max       := N.max%N;
  min       := N.min%N;
}.

Instance Eq_Char___ : Eq_ Char := {
                               op_zsze__ := fun x y => (x =? y)%N;
                               op_zeze__ := fun x y => negb (x =? y)%N;
                             }.

Instance Ord_Char___ : !Ord Char := {
  op_zl__   := fun x y => (x <? y)%N;
  op_zlze__ := fun x y => (x <=? y)%N;
  op_zg__   := fun x y => (y <? x)%N;
  op_zgze__ := fun x y => (y <=? x)%N;
  compare   := N.compare%N ;
  max       := N.max%N;
  min       := N.min%N;
}.

Instance Eq_bool___ : Eq_ bool := {
                               op_zsze__ := eqb;
                               op_zeze__ := fun x y => negb (eqb x y);
                             }.

Definition compare_bool (b1:bool)(b2:bool) : comparison :=
  match b1 , b2 with
  | true , true => Eq
  | false, false => Eq
  | true , false => Lt
  | false , true => Gt
  end.


Instance Ord_bool___ : !Ord bool := {
  op_zl__   := fun x y => andb (negb x) y;
  op_zlze__ := fun x y => orb (negb x) y;
  op_zg__   := fun x y => orb (negb y) x;
  op_zgze__ := fun x y => andb (negb y) x;
  compare   := compare_bool;
  max       := orb;
  min       := andb
}.

Instance Eq_unit___ : Eq_ unit := {
                               op_zsze__ := fun x y => true;
                               op_zeze__ := fun x y => false;
                             }.

Instance Ord_unit___ : !Ord unit := {
  op_zl__   := fun x y => false;
  op_zlze__ := fun x y => true;
  op_zg__   := fun x y => false;
  op_zgze__ := fun x y => true;
  compare   := fun x y => Eq ;
  max       := fun x y => tt;
  min       := fun x y => tt;
}.

Definition eq_comparison (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => true
  | Gt, Gt => true
  | Lt, Lt => true
  | _ , _  => false
end.

Instance Eq_comparison___ : Eq_ comparison :=
{
  op_zsze__ := eq_comparison;
  op_zeze__ := fun x y => negb (eq_comparison x y);
}.

Definition compare_comparison  (x : comparison) (y: comparison) :=
  match x , y with
  | Eq, Eq => Eq
  | _, Eq  => Gt
  | Eq, _  => Lt
  | Lt, Lt => Eq
  | _, Lt  => Lt
  | Lt, _  => Gt
  | Gt, Gt => Eq
end.

Definition ord_default {a} (comp : a -> a -> comparison) `{Eq_ a} :=
  Build_Ord _
  (fun x y => (comp x y) == Lt)
  ( fun x y => negb ((comp x y) == Lt))
  (fun x y => (comp y x) == Lt)
  (fun x y => negb ((comp x y) == Lt))
  comp
  (fun x y =>
     match comp x y with
     | Lt => y
     | _  => x
     end)
  (fun x y =>   match comp x y with
             | Gt => y
             | _  => x
             end).

Instance Ord_comparison___ : !Ord comparison := ord_default compare_comparison.


(* TODO: are these available in a library somewhere? *)
Fixpoint eqlist {a} `{Eq_ a} (xs :  list a) (ys : list a) : bool :=
    match xs , ys with
    | nil , nil => true
    | x :: xs' , y :: ys' => andb (x == y) (eqlist xs' ys')
    | _ ,  _ => false
    end.

Fixpoint compare_list {a} `{Ord a} (xs :  list a) (ys : list a) : comparison :=
    match xs , ys with
    | nil , nil => Eq
    | nil , _   => Lt
    | _   , nil => Gt
    | x :: xs' , y :: ys' =>
      match compare x y with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare_list xs' ys'
      end
    end.

Instance Eq_list {a} `{Eq_ a} : Eq_ (list a) :=
  { op_zsze__ := fun x y => true;
    op_zeze__ := fun x y => false;
  }.

Instance Ord_list {a} `{Ord a}: !Ord (list a) :=
  ord_default compare_list.


Instance Eq_option {a} `{Eq_ a} : Eq_ (option a) := {
   op_zsze__ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 == y0
                  | None, None => true
                  | _,_ => false
                  end ;
   op_zeze__ := fun x y =>
                  match x,y with
                  | Some x0, Some y0 => x0 /= y0
                  | None, None => false
                  | _,_ => true
                  end
}.

Definition compare_option {a} `{Ord a} (xs : option a) (ys : option a) : comparison :=
  match xs, ys with
  | None, None => Eq
  | None, _    => Lt
  | _   , None => Gt
  | Some x , Some y => compare x y
  end.

Instance Ord_option {a} `{Ord a} : !Ord (option a) := ord_default compare_option.


(* ********************************************************* *)
(* Some Haskell functions we cannot translate (yet)          *)


(* Pattern guards, ugh. *)
Fixpoint take {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if Z.leb n #0 then nil else (y :: take (n - #1) ys)
  end.

Fixpoint drop {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if Z.leb n #0 then (y :: ys) else drop (n - #1) ys
  end.

(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr {a b:Type} (f : a -> b -> b) (q0 : b) (xs : list a) : list b :=
  match xs with
  | nil => q0 :: nil
  | y :: ys => match scanr f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

(* The inner nil case is impossible. So it is left out of the Haskell version. *)
Fixpoint scanr1 {a :Type} (f : a -> a -> a) (q0 : a) (xs : list a) : list a :=
  match xs with
  | nil => q0 :: nil
  | y :: nil => y :: nil
  | y :: ys => match scanr1 f q0 ys with
              | q :: qs =>  f y q :: (q :: qs)
              | nil => nil
              end
end.

(* ?? why doesn't this work? the infix variable k ? Or needed for foldl and foldl' below *)
(* Yes, We need foldr for foldl and foldl' *)

Fixpoint foldr {a}{b} (f: a -> b -> b) (z:b) (xs: list a) : b :=
  match xs with
  | nil => z
  | y :: ys => f y (foldr f z ys)
  end.


Definition foldl {a}{b} k z0 xs :=
  foldr (fun (v:a) (fn:b->b) => (fun (z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition foldl' {a}{b} k z0 xs :=
  foldr (fun(v:a) (fn:b->b) => (fun(z:b) => fn (k z v))) (id : b -> b) xs z0.

Definition build {a} : (forall {b},(a -> b -> b) -> b -> b) -> list a :=
  fun g => g _ (fun x y => x :: y) nil.

(********************************************************************)

Definition seq {A} {B} (a : A) (b:B) := b.

Definition oneShot {a} (x:a) := x.

(* Converted imports: *)

Require Coq.Lists.List.
Require Coq.Program.Basics.

(* Converted declarations: *)

Local Definition instance_Monoid_unit_mappend : unit -> unit -> unit :=
  fun arg_210__ arg_211__ => tt.

Local Definition instance_Monoid_unit_mconcat : list unit -> unit :=
  fun arg_212__ => tt.

Local Definition instance_Monoid_unit_mempty : unit :=
  tt.

Local Definition instance_Monoid_comparison_mappend
    : comparison -> comparison -> comparison :=
  fun arg_187__ arg_188__ =>
    match arg_187__ , arg_188__ with
      | Lt , _ => Lt
      | Eq , y => y
      | Gt , _ => Gt
    end.

Local Definition instance_Monoid_comparison_mempty : comparison :=
  Eq.

Local Definition instance_Monoid_comparison_mconcat : list
                                                      comparison -> comparison :=
  foldr instance_Monoid_comparison_mappend instance_Monoid_comparison_mempty.

Local Definition instance_Functor_option_fmap : forall {a} {b},
                                                  (a -> b) -> option a -> option b :=
  fun {a} {b} =>
    fun arg_179__ arg_180__ =>
      match arg_179__ , arg_180__ with
        | _ , None => None
        | f , (Some a) => Some (f a)
      end.

Local Definition instance_Applicative_option_op_ztzg__ : forall {a} {b},
                                                           option a -> option b -> option b :=
  fun {a} {b} =>
    fun arg_176__ arg_177__ =>
      match arg_176__ , arg_177__ with
        | (Some _m1) , m2 => m2
        | None , _m2 => None
      end.

Local Definition instance_Applicative_option_pure : forall {a}, a -> option a :=
  fun {a} => Some.

Local Definition instance_Monad_option_op_zgzgze__ : forall {a} {b},
                                                       option a -> (a -> option b) -> option b :=
  fun {a} {b} =>
    fun arg_167__ arg_168__ =>
      match arg_167__ , arg_168__ with
        | (Some x) , k => k x
        | None , _ => None
      end.

(* Skipping instance instance_Alternative_option *)

(* Skipping instance instance_MonadPlus_option *)

Local Definition instance_Applicative_list_op_zlztzg__ : forall {a} {b},
                                                           list (a -> b) -> list a -> list b :=
  fun {a} {b} =>
    fun arg_156__ arg_157__ =>
      match arg_156__ , arg_157__ with
        | fs , xs => Coq.Lists.List.flat_map (fun f =>
                                               Coq.Lists.List.flat_map (fun x => cons (f x) nil) xs) fs
      end.

Local Definition instance_Applicative_list_op_ztzg__ : forall {a} {b},
                                                         list a -> list b -> list b :=
  fun {a} {b} =>
    fun arg_160__ arg_161__ =>
      match arg_160__ , arg_161__ with
        | xs , ys => Coq.Lists.List.flat_map (fun _ =>
                                               Coq.Lists.List.flat_map (fun y => cons y nil) ys) xs
      end.

Local Definition instance_Applicative_list_pure : forall {a}, a -> list a :=
  fun {a} => fun arg_153__ => match arg_153__ with | x => cons x nil end.

Local Definition instance_Monad_list_op_zgzgze__ : forall {a} {b},
                                                     list a -> (a -> list b) -> list b :=
  fun {a} {b} =>
    fun arg_148__ arg_149__ =>
      match arg_148__ , arg_149__ with
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
  fun arg_54__ arg_55__ => match arg_54__ , arg_55__ with | _pred , r => r end.

Definition breakpoint {a} : a -> a :=
  fun arg_52__ => match arg_52__ with | r => r end.

Definition breakpointCond {a} : bool -> a -> a :=
  fun arg_49__ arg_50__ => match arg_49__ , arg_50__ with | _ , r => r end.

Definition const {a} {b} : a -> b -> a :=
  fun arg_46__ arg_47__ => match arg_46__ , arg_47__ with | x , _ => x end.

Definition asTypeOf {a} : a -> a -> a :=
  const.

Local Definition instance_Functor_option_op_zlzd__ : forall {a} {b},
                                                       a -> option b -> option a :=
  fun {a} {b} => Coq.Program.Basics.compose instance_Functor_option_fmap const.

Definition flip {a} {b} {c} : (a -> b -> c) -> b -> a -> c :=
  fun arg_34__ arg_35__ arg_36__ =>
    match arg_34__ , arg_35__ , arg_36__ with
      | f , x , y => f y x
    end.

Definition id {a} : a -> a :=
  fun arg_57__ => match arg_57__ with | x => x end.

Axiom ifThenElse : forall {A : Type}, A.

(* Translating `ifThenElse' failed: overloaded if-then-else unsupported *)

Definition map {a} {b} : (a -> b) -> list a -> list b :=
  fix map arg_67__ arg_68__
        := match arg_67__ , arg_68__ with
             | _ , nil => nil
             | f , (cons x xs) => cons (f x) (map f xs)
           end.

Local Definition instance_Functor_list_fmap : forall {a} {b},
                                                (a -> b) -> list a -> list b :=
  fun {a} {b} => map.

Local Definition instance_Functor_list_op_zlzd__ : forall {a} {b},
                                                     a -> list b -> list a :=
  fun {a} {b} => Coq.Program.Basics.compose instance_Functor_list_fmap const.

Definition mapFB {elt} {lst} {a}
    : (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst :=
  fun arg_59__ arg_60__ =>
    match arg_59__ , arg_60__ with
      | c , f => fun arg_61__ arg_62__ =>
                   match arg_61__ , arg_62__ with
                     | x , ys => c (f x) ys
                   end
    end.

Definition op_z2218U__ {b} {c} {a} : (b -> c) -> (a -> b) -> a -> c :=
  fun arg_39__ arg_40__ =>
    match arg_39__ , arg_40__ with
      | f , g => fun arg_41__ => match arg_41__ with | x => f (g x) end
    end.

Infix "∘" := (op_z2218U__) (left associativity, at level 40).

Notation "'_∘_'" := (op_z2218U__).

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
  fun arg_114__ arg_115__ =>
    match arg_114__ , arg_115__ with
      | f , x => op_zgzgze__ x f
    end.

Infix "=<<" := (op_zezlzl__) (at level 99).

Notation "'_=<<_'" := (op_zezlzl__).

Definition mapM {m} {a} {b} `{Monad m} : (a -> m b) -> list a -> m (list b) :=
  fun arg_105__ arg_106__ =>
    match arg_105__ , arg_106__ with
      | f , as_ => let k :=
                     fun arg_107__ arg_108__ =>
                       match arg_107__ , arg_108__ with
                         | a , r => op_zgzgze__ (f a) (fun x =>
                                                  op_zgzgze__ r (fun xs => return_ (cons x xs)))
                       end in
                   foldr k (return_ nil) as_
    end.

Definition liftM5 {m} {a1} {a2} {a3} {a4} {a5} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> a5 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m
      r :=
  fun arg_75__ arg_76__ arg_77__ arg_78__ arg_79__ arg_80__ =>
    match arg_75__ , arg_76__ , arg_77__ , arg_78__ , arg_79__ , arg_80__ with
      | f , m1 , m2 , m3 , m4 , m5 => op_zgzgze__ m1 (fun x1 =>
                                                    op_zgzgze__ m2 (fun x2 =>
                                                                  op_zgzgze__ m3 (fun x3 =>
                                                                                op_zgzgze__ m4 (fun x4 =>
                                                                                              op_zgzgze__ m5 (fun x5 =>
                                                                                                            return_ (f
                                                                                                                    x1
                                                                                                                    x2
                                                                                                                    x3
                                                                                                                    x4
                                                                                                                    x5))))))
    end.

Definition liftM4 {m} {a1} {a2} {a3} {a4} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> a4 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m r :=
  fun arg_83__ arg_84__ arg_85__ arg_86__ arg_87__ =>
    match arg_83__ , arg_84__ , arg_85__ , arg_86__ , arg_87__ with
      | f , m1 , m2 , m3 , m4 => op_zgzgze__ m1 (fun x1 =>
                                               op_zgzgze__ m2 (fun x2 =>
                                                             op_zgzgze__ m3 (fun x3 =>
                                                                           op_zgzgze__ m4 (fun x4 =>
                                                                                         return_ (f x1 x2 x3 x4)))))
    end.

Definition liftM3 {m} {a1} {a2} {a3} {r} `{(Monad m)}
    : (a1 -> a2 -> a3 -> r) -> m a1 -> m a2 -> m a3 -> m r :=
  fun arg_90__ arg_91__ arg_92__ arg_93__ =>
    match arg_90__ , arg_91__ , arg_92__ , arg_93__ with
      | f , m1 , m2 , m3 => op_zgzgze__ m1 (fun x1 =>
                                          op_zgzgze__ m2 (fun x2 => op_zgzgze__ m3 (fun x3 => return_ (f x1 x2 x3))))
    end.

Definition liftM2 {m} {a1} {a2} {r} `{(Monad m)} : (a1 -> a2 -> r) -> m a1 -> m
                                                   a2 -> m r :=
  fun arg_96__ arg_97__ arg_98__ =>
    match arg_96__ , arg_97__ , arg_98__ with
      | f , m1 , m2 => op_zgzgze__ m1 (fun x1 =>
                                     op_zgzgze__ m2 (fun x2 => return_ (f x1 x2)))
    end.

Definition liftM {m} {a1} {r} `{(Monad m)} : (a1 -> r) -> m a1 -> m r :=
  fun arg_101__ arg_102__ =>
    match arg_101__ , arg_102__ with
      | f , m1 => op_zgzgze__ m1 (fun x1 => return_ (f x1))
    end.

Definition join {m} {a} `{(Monad m)} : m (m a) -> m a :=
  fun arg_118__ => match arg_118__ with | x => op_zgzgze__ x id end.

Definition sequence {m} {a} `{Monad m} : list (m a) -> m (list a) :=
  mapM id.

Definition ap {m} {a} {b} `{(Monad m)} : m (a -> b) -> m a -> m b :=
  fun arg_71__ arg_72__ =>
    match arg_71__ , arg_72__ with
      | m1 , m2 => op_zgzgze__ m1 (fun x1 =>
                                 op_zgzgze__ m2 (fun x2 => return_ (x1 x2)))
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
  fun arg_132__ arg_133__ =>
    match arg_132__ , arg_133__ with
      | f , a => op_zlztzg__ (pure f) a
    end.

Definition liftA3 {f} {a} {b} {c} {d} `{Applicative f} : (a -> b -> c -> d) -> f
                                                         a -> f b -> f c -> f d :=
  fun arg_121__ arg_122__ arg_123__ arg_124__ =>
    match arg_121__ , arg_122__ , arg_123__ , arg_124__ with
      | f , a , b , c => op_zlztzg__ (op_zlztzg__ (fmap f a) b) c
    end.

Definition liftA2 {f} {a} {b} {c} `{Applicative f} : (a -> b -> c) -> f a -> f
                                                     b -> f c :=
  fun arg_127__ arg_128__ arg_129__ =>
    match arg_127__ , arg_128__ , arg_129__ with
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
    fun arg_172__ arg_173__ =>
      match arg_172__ , arg_173__ with
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
  fun arg_183__ arg_184__ =>
    match arg_183__ , arg_184__ with
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
  fun arg_191__ arg_192__ =>
    match arg_191__ , arg_192__ with
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
  fun arg_196__ arg_197__ =>
    match arg_196__ , arg_197__ with
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
  fun arg_201__ arg_202__ =>
    match arg_201__ , arg_202__ with
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
  fun arg_206__ arg_207__ =>
    match arg_206__ , arg_207__ with
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
     * Coq.Lists.List.flat_map Coq.Program.Basics.compose Eq None Some bool
     comparison cons e foldr list nil option pair true tt unit
*)
