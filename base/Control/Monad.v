(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
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

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition filterM {m} {a} `{(GHC.Base.Applicative m)} : (a -> m bool) -> list
                                                         a -> m (list a) :=
  fun p =>
    GHC.Base.foldr (fun x =>
                     GHC.Base.liftA2 (fun flg =>
                                       if flg : bool
                                       then (fun arg_11__ => cons x arg_11__)
                                       else GHC.Base.id) (p x)) (GHC.Base.pure nil).

Definition foldM {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad m}
    : (b -> a -> m b) -> b -> t a -> m b :=
  Data.Foldable.foldlM.

Definition foldM_ {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad
                  m} : (b -> a -> m b) -> b -> t a -> m unit :=
  fun f a xs =>
    GHC.Base.op_zgzg__ (Data.Foldable.foldlM f a xs) (GHC.Base.return_ tt).

Definition guard {f} `{(GHC.Base.Alternative f)} : bool -> f unit :=
  fun arg_15__ =>
    match arg_15__ with
      | true => GHC.Base.pure tt
      | false => GHC.Base.empty
    end.

Definition mapAndUnzipM {m} {a} {b} {c} `{(GHC.Base.Applicative m)} : (a -> m (b
                                                                              * c)) -> list a -> m (list b * list c) :=
  fun f xs =>
    Data.Functor.op_zlzdzg__ GHC.List.unzip (Data.Traversable.traverse f xs).

Definition mfilter {m} {a} `{(GHC.Base.MonadPlus m)} : (a -> bool) -> m a -> m
                                                       a :=
  fun p ma =>
    GHC.Base.op_zgzgze__ ma (fun a =>
                           if p a : bool
                           then GHC.Base.return_ a
                           else GHC.Base.mzero).

Definition op_zgzezg__ {m} {a} {b} {c} `{GHC.Base.Monad m} : (a -> m
                                                             b) -> (b -> m c) -> (a -> m c) :=
  fun f g => fun x => GHC.Base.op_zgzgze__ (f x) g.

Infix ">=>" := (op_zgzezg__) (at level 99).

Notation "'_>=>_'" := (op_zgzezg__).

Definition op_zlzezl__ {m} {b} {c} {a} `{GHC.Base.Monad m} : (b -> m
                                                             c) -> (a -> m b) -> (a -> m c) :=
  GHC.Base.flip op_zgzezg__.

Infix "<=<" := (op_zlzezl__) (at level 99).

Notation "'_<=<_'" := (op_zlzezl__).

Definition op_zlzdznzg__ {m} {a} {b} `{GHC.Base.Monad m} : (a -> b) -> m a -> m
                                                           b :=
  fun f m =>
    GHC.Base.op_zgzgze__ m (fun x =>
                           let z := f x in GHC.Prim.seq z (GHC.Base.return_ z)).

Infix "<$!>" := (op_zlzdznzg__) (at level 99).

Notation "'_<$!>_'" := (op_zlzdznzg__).

Definition unless {f} `{(GHC.Base.Applicative f)} : bool -> f unit -> f unit :=
  fun p s => if p : bool then GHC.Base.pure tt else s.

Definition zipWithM {m} {a} {b} {c} `{_ : GHC.Base.Applicative m} : (a -> b -> m
                                                                    c) -> list a -> list b -> m (list c) :=
  fun f xs ys =>
    (@Data.Traversable.sequenceA _ _ _ _ m _ _ _ (GHC.List.zipWith f xs ys)).

Definition zipWithM_ {m} {a} {b} {c} `{(GHC.Base.Applicative m)} : (a -> b -> m
                                                                   c) -> list a -> list b -> m unit :=
  fun f xs ys => Data.Foldable.sequenceA_ (GHC.List.zipWith f xs ys).

Module Notations.
Infix "Control.Monad.>=>" := (op_zgzezg__) (at level 99).
Notation "'_Control.Monad.>=>_'" := (op_zgzezg__).
Infix "Control.Monad.<=<" := (op_zlzezl__) (at level 99).
Notation "'_Control.Monad.<=<_'" := (op_zlzezl__).
Infix "Control.Monad.<$!>" := (op_zlzdznzg__) (at level 99).
Notation "'_Control.Monad.<$!>_'" := (op_zlzdznzg__).
End Notations.

(* Unbound variables:
     bool cons list nil op_zt__ tt unit Data.Foldable.Foldable Data.Foldable.foldlM
     Data.Foldable.sequenceA_ Data.Functor.op_zlzdzg__ Data.Traversable.sequenceA
     Data.Traversable.traverse GHC.Base.Alternative GHC.Base.Applicative
     GHC.Base.Monad GHC.Base.MonadPlus GHC.Base.empty GHC.Base.flip GHC.Base.foldr
     GHC.Base.id GHC.Base.liftA2 GHC.Base.mzero GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.pure GHC.Base.return_ GHC.List.unzip
     GHC.List.zipWith GHC.Prim.seq
*)
