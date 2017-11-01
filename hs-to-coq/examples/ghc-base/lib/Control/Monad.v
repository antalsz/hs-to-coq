(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Base.   (* bind notation *)
Open Scope type_scope. (* resolve  (a * b) types *)
(* Converted imports: *)

Require Data.Foldable.
Require Data.Functor.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Prim.

(* Converted declarations: *)

Definition filterM {m} {a} `{(GHC.Base.Applicative m)} : (a -> m bool) -> list
                                                         a -> m (list a) :=
  fun arg_40__ =>
    match arg_40__ with
      | p => GHC.Base.foldr (fun arg_41__ =>
                              match arg_41__ with
                                | x => GHC.Base.liftA2 (fun arg_42__ =>
                                                         match arg_42__ with
                                                           | flg => if flg : bool
                                                                    then (fun arg_43__ => cons x arg_43__)
                                                                    else GHC.Base.id
                                                         end) (p x)
                              end) (GHC.Base.pure nil)
    end.

Definition foldM {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad m}
    : (b -> a -> m b) -> b -> t a -> m b :=
  Data.Foldable.foldlM.

Definition foldM_ {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad
                  m} : (b -> a -> m b) -> b -> t a -> m unit :=
  fun arg_13__ arg_14__ arg_15__ =>
    match arg_13__ , arg_14__ , arg_15__ with
      | f , a , xs => GHC.Base.op_zgzg__ (Data.Foldable.foldlM f a xs)
                                         (GHC.Base.return_ tt)
    end.

Definition guard {f} `{(GHC.Base.Alternative f)} : bool -> f unit :=
  fun arg_50__ =>
    match arg_50__ with
      | true => GHC.Base.pure tt
      | false => GHC.Base.empty
    end.

Definition mapAndUnzipM {m} {a} {b} {c} `{(GHC.Base.Applicative m)} : (a -> m (b
                                                                              * c)) -> list a -> m (list b * list c) :=
  fun arg_28__ arg_29__ =>
    match arg_28__ , arg_29__ with
      | f , xs => Data.Functor.op_zlzdzg__ GHC.List.unzip (Data.Traversable.traverse f
                                           xs)
    end.

Definition mfilter {m} {a} `{(GHC.Base.MonadPlus m)} : (a -> bool) -> m a -> m
                                                       a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | p , ma => GHC.Base.op_zgzgze__ ma (fun a =>
                                         if p a : bool
                                         then GHC.Base.return_ a
                                         else GHC.Base.mzero)
    end.

Definition op_zgzezg__ {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m
                                                             b) -> (b -> m c) -> (a -> m c) :=
  fun arg_32__ arg_33__ =>
    match arg_32__ , arg_33__ with
      | f , g => fun arg_34__ =>
                   match arg_34__ with
                     | x => GHC.Base.op_zgzgze__ (f x) g
                   end
    end.

Infix ">=>" := (op_zgzezg__) (at level 99).

Notation "'_>=>_'" := (op_zgzezg__).

Definition op_zlzezl__ {m} {b} {c} {a} `{GHC.Base.Monad m} : (b -> m
                                                             c) -> (a -> m b) -> (a -> m c) :=
  GHC.Base.flip op_zgzezg__.

Infix "<=<" := (op_zlzezl__) (at level 99).

Notation "'_<=<_'" := (op_zlzezl__).

Definition op_zlzdznzg__ {m} {a} {b} `{GHC.Base.Monad m} : (a -> b) -> m a -> m
                                                           b :=
  fun arg_4__ arg_5__ =>
    match arg_4__ , arg_5__ with
      | f , m => GHC.Base.op_zgzgze__ m (fun x =>
                                        let z := f x in GHC.Prim.seq z (GHC.Base.return_ z))
    end.

Infix "<$!>" := (op_zlzdznzg__) (at level 99).

Notation "'_<$!>_'" := (op_zlzdznzg__).

Definition unless {f} `{(GHC.Base.Applicative f)} : bool -> f unit -> f unit :=
  fun arg_9__ arg_10__ =>
    match arg_9__ , arg_10__ with
      | p , s => if p : bool
                 then GHC.Base.pure tt
                 else s
    end.

Definition zipWithM {m} {a} {b} {c} `{(GHC.Base.Applicative m)} : (a -> b -> m
                                                                  c) -> list a -> list b -> m (list c) :=
  fun arg_23__ arg_24__ arg_25__ =>
    match arg_23__ , arg_24__ , arg_25__ with
      | f , xs , ys => Data.Traversable.sequenceA (GHC.List.zipWith f xs ys)
    end.

Definition zipWithM_ {m} {a} {b} {c} `{(GHC.Base.Applicative m)} : (a -> b -> m
                                                                   c) -> list a -> list b -> m unit :=
  fun arg_18__ arg_19__ arg_20__ =>
    match arg_18__ , arg_19__ , arg_20__ with
      | f , xs , ys => Data.Foldable.sequenceA_ (GHC.List.zipWith f xs ys)
    end.

(* Unbound variables:
     * Data.Foldable.Foldable Data.Foldable.foldlM Data.Foldable.sequenceA_
     Data.Functor.op_zlzdzg__ Data.Traversable.sequenceA Data.Traversable.traverse
     GHC.Base.Alternative GHC.Base.Applicative GHC.Base.Monad GHC.Base.MonadPlus
     GHC.Base.empty GHC.Base.flip GHC.Base.foldr GHC.Base.id GHC.Base.liftA2
     GHC.Base.mzero GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.pure
     GHC.Base.return_ GHC.List.unzip GHC.List.zipWith GHC.Prim.seq bool cons list nil
     tt unit
*)
