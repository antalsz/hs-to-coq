(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

(*
Require Control.Exception.Base.
Require Control.Monad.Trans.Maybe.
Require Coq.Init.Datatypes. *)
Require Data.Foldable.
Require Data.Maybe.
Require GHC.Base.
(* Require GHC.Err.
Require GHC.Exception.
Require GHC.Types. *)
(* Converted declarations: *)

Instance instance_alternative_option : Alternative option.
Admitted.
Instance instance_monadplus_option: MonadPlus option.
Admitted.

Definition firstJusts {a} : list (option a) -> option a :=
  Data.Foldable.msum.

Definition firstJust {a} : option a -> option a -> option a :=
  fun arg_24__ arg_25__ =>
    match arg_24__ , arg_25__ with
      | a , b => firstJusts (cons a (cons b nil))
    end.

(*  Need transformers library
Definition liftMaybeT {m} {a} `{GHC.Base.Monad m} : m
                                                    a -> Control.Monad.Trans.Maybe.MaybeT m a :=
  fun arg_11__ =>
    match arg_11__ with
      | act => GHC.Base.op_zd__ Control.Monad.Trans.Maybe.MaybeT (GHC.Base.liftM Some
                                                                                 act)
    end.
*)
Definition orElse {a} : option a -> a -> a :=
  GHC.Base.flip Data.Maybe.fromMaybe.

(*  IO
Definition tryMaybeT {a} : GHC.Types.IO a -> Control.Monad.Trans.Maybe.MaybeT
                           GHC.Types.IO a :=
  fun arg_5__ =>
    match arg_5__ with
      | action => let handler :=
                    fun arg_6__ =>
                      match arg_6__ with
                        | GHC.Exception.SomeException _ => GHC.Base.return_ None
                      end in
                  GHC.Base.op_zd__ Control.Monad.Trans.Maybe.MaybeT (Control.Exception.Base.catch
                                   (GHC.Base.fmap Some action) handler)
    end.
*)

Definition whenIsJust {m} {a} `{GHC.Base.Monad m} : option a -> (a -> m
                                                    unit) -> m unit :=
  fun arg_15__ arg_16__ =>
    match arg_15__ , arg_16__ with
      | Some x , f => f x
      | None , _ => GHC.Base.return_ tt
    end.

Inductive MaybeErr err val : Type := Mk_Succeeded : val -> MaybeErr err val
                                  |  Mk_Failed : err -> MaybeErr err val.

Arguments Mk_Succeeded {_} {_} _.

Arguments Mk_Failed {_} {_} _.

Definition isSuccess {err} {val} : MaybeErr err val -> bool :=
  fun arg_3__ =>
    match arg_3__ with
      | Mk_Succeeded _ => true
      | Mk_Failed _ => false
    end.

Definition failME {err} {val} : err -> MaybeErr err val :=
  fun arg_0__ => match arg_0__ with | e => Mk_Failed e end.

Local Definition instance_GHC_Base_Applicative__MaybeErr_err__pure {inst_err}
    : forall {a}, a -> (MaybeErr inst_err) a :=
  fun {a} => Mk_Succeeded.

Local Definition instance_GHC_Base_Monad__MaybeErr_err__return_ {inst_err}
    : forall {a}, a -> (MaybeErr inst_err) a :=
  fun {a} => instance_GHC_Base_Applicative__MaybeErr_err__pure.

Local Definition instance_GHC_Base_Monad__MaybeErr_err__op_zgzgze__ {inst_err}
    : forall {a} {b},
        (MaybeErr inst_err) a -> (a -> (MaybeErr inst_err) b) -> (MaybeErr inst_err)
        b :=
  fun {a} {b} =>
    fun arg_28__ arg_29__ =>
      match arg_28__ , arg_29__ with
        | Mk_Succeeded v , k => k v
        | Mk_Failed e , _ => Mk_Failed e
      end.

Local Definition instance_GHC_Base_Functor__MaybeErr_err__fmap {inst_err}
    : forall {a} {b}, (a -> b) -> (MaybeErr inst_err) a -> (MaybeErr inst_err) b :=
  fun {a} {b} f me => match me with
                   | Mk_Succeeded v => Mk_Succeeded (f v)
                   | Mk_Failed e     => Mk_Failed e
                   end.



Local Definition instance_GHC_Base_Functor__MaybeErr_err__op_zlzd__ {inst_err}
    : forall {a} {b}, b -> (MaybeErr inst_err) a -> (MaybeErr inst_err) b :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor__MaybeErr_err__fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor__MaybeErr_err_ {err} :
  GHC.Base.Functor (MaybeErr err) := fun _ k => k {|
  fmap__ := fun {a} {b} => instance_GHC_Base_Functor__MaybeErr_err__fmap ;
  op_zlzd____ := fun {a} {b} => instance_GHC_Base_Functor__MaybeErr_err__op_zlzd__ |}.


Local Definition instance_GHC_Base_Applicative__MaybeErr_err__op_zlztzg__ {inst_err}
    : forall {a} {b},
        (MaybeErr inst_err) (a -> b) -> (MaybeErr inst_err) a -> (MaybeErr inst_err)
        b :=
 fun {a} {b} mf ma => match mf , ma  with
                   | Mk_Succeeded f , Mk_Succeeded v => Mk_Succeeded (f v)
                   | Mk_Failed e , _     => Mk_Failed e
                   | _ , Mk_Failed e     => Mk_Failed e
                   end.

Local Definition instance_GHC_Base_Applicative__MaybeErr_err__op_ztzg__ {inst_err}
    : forall {a} {b},
        (MaybeErr inst_err) a -> (MaybeErr inst_err) b -> (MaybeErr inst_err) b :=
  fun {a} {b} =>
    fun x y =>
      instance_GHC_Base_Applicative__MaybeErr_err__op_zlztzg__ (GHC.Base.fmap
                                                               (GHC.Base.const GHC.Base.id) x) y.

Instance instance_GHC_Base_Applicative__MaybeErr_err_
  {err} : GHC.Base.Applicative (MaybeErr err) := fun _ k => k (
    GHC.Base.Applicative__Dict_Build (MaybeErr err)
      (fun {a} {b} => instance_GHC_Base_Applicative__MaybeErr_err__op_ztzg__)
      (fun {a} {b} => instance_GHC_Base_Applicative__MaybeErr_err__op_zlztzg__)
      (fun {a} => instance_GHC_Base_Applicative__MaybeErr_err__pure)
    ).


Local Definition instance_GHC_Base_Monad__MaybeErr_err__op_zgzg__ {inst_err}
    : forall {a} {b},
        (MaybeErr inst_err) a -> (MaybeErr inst_err) b -> (MaybeErr inst_err) b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Instance instance_GHC_Base_Monad__MaybeErr_err_ {err} :
  GHC.Base.Monad (MaybeErr err) := fun _ k => k {|
  op_zgzg____ := fun {a} {b} => instance_GHC_Base_Monad__MaybeErr_err__op_zgzg__ ;
  op_zgzgze____ := fun {a} {b} =>
    instance_GHC_Base_Monad__MaybeErr_err__op_zgzgze__ ;
  return___ := fun {a} => instance_GHC_Base_Monad__MaybeErr_err__return_ |}.


(* Unbound variables:
     Control.Exception.Base.catch Control.Monad.Trans.Maybe.MaybeT
     Coq.Init.Datatypes.app Data.Foldable.msum Data.Maybe.fromMaybe
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.String GHC.Base.ap
     GHC.Base.const GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.liftM
     GHC.Base.op_zd__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_ GHC.Err.error
     GHC.Exception.SomeException GHC.Types.IO None Some bool cons false list nil
     option true tt unit
*)
