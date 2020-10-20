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
Import Data.Functor.Notations.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `Control.Monad.guard' *)

Definition filterM {m} {a} `{(GHC.Base.Applicative m)}
   : (a -> m bool) -> list a -> m (list a) :=
  fun p =>
    GHC.Base.foldr (fun x =>
                      GHC.Base.liftA2 (fun flg =>
                                         if flg : bool
                                         then (fun arg_0__ => cons x arg_0__)
                                         else GHC.Base.id) (p x)) (GHC.Base.pure nil).

Definition op_zgzezg__ {m} {a} {b} {c} `{GHC.Base.Monad m}
   : (a -> m b) -> (b -> m c) -> (a -> m c) :=
  fun f g => fun x => f x GHC.Base.>>= g.

Notation "'_>=>_'" := (op_zgzezg__).

Infix ">=>" := (_>=>_) (at level 99).

Definition op_zlzezl__ {m} {b} {c} {a} `{GHC.Base.Monad m}
   : (b -> m c) -> (a -> m b) -> (a -> m c) :=
  GHC.Base.flip _>=>_.

Notation "'_<=<_'" := (op_zlzezl__).

Infix "<=<" := (_<=<_) (at level 99).

(* Skipping definition `Control.Monad.forever' *)

Definition mapAndUnzipM {m} {a} {b} {c} `{(GHC.Base.Applicative m)}
   : (a -> m (b * c)%type) -> list a -> m (list b * list c)%type :=
  fun f xs => GHC.List.unzip Data.Functor.<$> Data.Traversable.traverse f xs.

Definition zipWithM {m} {a} {b} {c} `{_ : GHC.Base.Applicative m}
   : (a -> b -> m c) -> list a -> list b -> m (list c) :=
  fun f xs ys =>
    (@Data.Traversable.sequenceA _ _ _ _ m _ _ _ (GHC.List.zipWith f xs ys)).

Definition zipWithM_ {m} {a} {b} {c} `{(GHC.Base.Applicative m)}
   : (a -> b -> m c) -> list a -> list b -> m unit :=
  fun f xs ys => Data.Foldable.sequenceA_ (GHC.List.zipWith f xs ys).

Definition foldM {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad m}
   : (b -> a -> m b) -> b -> t a -> m b :=
  Data.Foldable.foldlM.

Definition foldM_ {t} {m} {b} {a} `{Data.Foldable.Foldable t} `{GHC.Base.Monad
  m}
   : (b -> a -> m b) -> b -> t a -> m unit :=
  fun f a xs => Data.Foldable.foldlM f a xs GHC.Base.>> GHC.Base.return_ tt.

(* Skipping definition `Control.Monad.replicateM' *)

(* Skipping definition `Control.Monad.replicateM_' *)

Definition unless {f} `{(GHC.Base.Applicative f)} : bool -> f unit -> f unit :=
  fun p s => if p : bool then GHC.Base.pure tt else s.

Definition op_zlzdznzg__ {m} {a} {b} `{GHC.Base.Monad m}
   : (a -> b) -> m a -> m b :=
  fun f m =>
    m GHC.Base.>>= (fun x => let z := f x in GHC.Prim.seq z (GHC.Base.return_ z)).

Notation "'_<$!>_'" := (op_zlzdznzg__).

Infix "<$!>" := (_<$!>_) (at level 99).

(* Skipping definition `Control.Monad.mfilter' *)

Module Notations.
Notation "'_Control.Monad.>=>_'" := (op_zgzezg__).
Infix "Control.Monad.>=>" := (_>=>_) (at level 99).
Notation "'_Control.Monad.<=<_'" := (op_zlzezl__).
Infix "Control.Monad.<=<" := (_<=<_) (at level 99).
Notation "'_Control.Monad.<$!>_'" := (op_zlzdznzg__).
Infix "Control.Monad.<$!>" := (_<$!>_) (at level 99).
End Notations.

(* External variables:
     bool cons list nil op_zt__ tt unit Data.Foldable.Foldable Data.Foldable.foldlM
     Data.Foldable.sequenceA_ Data.Functor.op_zlzdzg__ Data.Traversable.sequenceA
     Data.Traversable.traverse GHC.Base.Applicative GHC.Base.Monad GHC.Base.flip
     GHC.Base.foldr GHC.Base.id GHC.Base.liftA2 GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.pure GHC.Base.return_ GHC.List.unzip
     GHC.List.zipWith GHC.Prim.seq
*)
