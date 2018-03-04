(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Maybe.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive MaybeErr err val : Type := Succeeded : val -> MaybeErr err val
                                  |  Failed : err -> MaybeErr err val.

Arguments Succeeded {_} {_} _.

Arguments Failed {_} {_} _.
(* Midamble *)

Require GHC.Err.

Definition expectJust {a}`{_:GHC.Err.Default a} :
			GHC.Base.String -> ((option a) -> a) :=
  fun arg_14__ arg_15__ =>
    match arg_14__ , arg_15__ with
      | _ , Some x => x
      | err , None => GHC.Err.error (GHC.Base.hs_string__ "expectJust ")
    end.

(* Converted value declarations: *)

Local Definition Functor__MaybeErr_fmap {inst_err} : forall {a} {b},
                                                       (a -> b) -> MaybeErr inst_err a -> MaybeErr inst_err b :=
  fun {a} {b} =>
    fun f x =>
      match x with
      | Succeeded x => Succeeded (f x)
      | Failed e => Failed e
      end.

Local Definition Functor__MaybeErr_op_zlzd__ {inst_err} : forall {a} {b},
                                                            a -> (MaybeErr inst_err) b -> (MaybeErr inst_err) a :=
  fun {a} {b} => fun x => Functor__MaybeErr_fmap (GHC.Base.const x).

Program Instance Functor__MaybeErr {err} : GHC.Base.Functor (MaybeErr err) :=
  fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__MaybeErr_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__MaybeErr_fmap |}.
Admit Obligations.

Local Definition Applicative__MaybeErr_op_zlztzg__ {inst_err} : forall {a} {b},
                                                                  MaybeErr inst_err (a -> b) -> MaybeErr inst_err
                                                                  a -> MaybeErr inst_err b :=
  fun {a} {b} =>
    fun mf mx =>
      match mf with
      | Succeeded f =>
          match mx with
          | Succeeded x => Succeeded (f x)
          | Failed e => Failed e
          end
      | Failed e => Failed e
      end.

Local Definition Applicative__MaybeErr_op_ztzg__ {inst_err} : forall {a} {b},
                                                                (MaybeErr inst_err) a -> (MaybeErr inst_err)
                                                                b -> (MaybeErr inst_err) b :=
  fun {a} {b} =>
    fun x y =>
      Applicative__MaybeErr_op_zlztzg__ (GHC.Base.fmap (GHC.Base.const GHC.Base.id) x)
                                        y.

Local Definition Applicative__MaybeErr_pure {inst_err} : forall {a},
                                                           a -> (MaybeErr inst_err) a :=
  fun {a} => Succeeded.

Program Instance Applicative__MaybeErr {err} : GHC.Base.Applicative (MaybeErr
                                                                    err) := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__MaybeErr_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__MaybeErr_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__MaybeErr_pure |}.
Admit Obligations.

Local Definition Monad__MaybeErr_op_zgzg__ {inst_err} : forall {a} {b},
                                                          (MaybeErr inst_err) a -> (MaybeErr inst_err) b -> (MaybeErr
                                                          inst_err) b :=
  fun {a} {b} => _GHC.Base.*>_.

Local Definition Monad__MaybeErr_op_zgzgze__ {inst_err} : forall {a} {b},
                                                            (MaybeErr inst_err) a -> (a -> (MaybeErr inst_err)
                                                            b) -> (MaybeErr inst_err) b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
      | Succeeded v , k => k v
      | Failed e , _ => Failed e
      end.

Local Definition Monad__MaybeErr_return_ {inst_err} : forall {a},
                                                        a -> (MaybeErr inst_err) a :=
  fun {a} => GHC.Base.pure.

Program Instance Monad__MaybeErr {err} : GHC.Base.Monad (MaybeErr err) := fun _
                                                                              k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__MaybeErr_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__MaybeErr_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__MaybeErr_return_ |}.
Admit Obligations.

Definition failME {err} {val} : err -> MaybeErr err val :=
  fun e => Failed e.

Definition isSuccess {err} {val} : MaybeErr err val -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded _ => true | Failed _ => false end.

Definition orElse {a} : option a -> a -> a :=
  GHC.Base.flip Data.Maybe.fromMaybe.

Definition whenIsJust {m} {a} `{GHC.Base.Monad m} : option a -> (a -> m
                                                    unit) -> m unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
    | Some x , f => f x
    | None , _ => GHC.Base.return_ tt
    end.

(* Unbound variables:
     None Some bool false option true tt unit Data.Maybe.fromMaybe
     GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad GHC.Base.const
     GHC.Base.flip GHC.Base.fmap GHC.Base.id GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Base.return_
*)
