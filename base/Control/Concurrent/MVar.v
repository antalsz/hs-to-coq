(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.MVar.
Import GHC.Base.Notations.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition withMVarMasked {a} {b}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO b) -> GHC.MVar.IO b :=
  fun m io =>
    GHC.IO.mask_ (GHC.MVar.takeMVar m GHC.Base.>>=
                  (fun a =>
                     GHC.IO.onException (io a) (GHC.MVar.putMVar m a) GHC.Base.>>=
                     (fun b => GHC.MVar.putMVar m a GHC.Base.>> GHC.Base.return_ b))).

Definition withMVar {a} {b}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO b) -> GHC.MVar.IO b :=
  fun m io =>
    GHC.IO.mask (fun restore =>
                   GHC.MVar.takeMVar m GHC.Base.>>=
                   (fun a =>
                      GHC.IO.onException (restore (io a)) (GHC.MVar.putMVar m a) GHC.Base.>>=
                      (fun b => GHC.MVar.putMVar m a GHC.Base.>> GHC.Base.return_ b))).

Definition swapMVar {a} : GHC.MVar.MVar a -> a -> GHC.MVar.IO a :=
  fun mvar new =>
    GHC.IO.mask_ (GHC.MVar.takeMVar mvar GHC.Base.>>=
                  (fun old => GHC.MVar.putMVar mvar new GHC.Base.>> GHC.Base.return_ old)).

Definition modifyMVar_ {a}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO a) -> GHC.MVar.IO unit :=
  fun m io =>
    GHC.IO.mask (fun restore =>
                   GHC.MVar.takeMVar m GHC.Base.>>=
                   (fun a =>
                      GHC.IO.onException (restore (io a)) (GHC.MVar.putMVar m a) GHC.Base.>>=
                      (fun a' => GHC.MVar.putMVar m a'))).

Definition modifyMVarMasked_ {a}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO a) -> GHC.MVar.IO unit :=
  fun m io =>
    GHC.IO.mask_ (GHC.MVar.takeMVar m GHC.Base.>>=
                  (fun a =>
                     GHC.IO.onException (io a) (GHC.MVar.putMVar m a) GHC.Base.>>=
                     (fun a' => GHC.MVar.putMVar m a'))).

Definition modifyMVarMasked {a} {b}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO (a * b)%type) -> GHC.MVar.IO b :=
  fun m io =>
    GHC.IO.mask_ (GHC.MVar.takeMVar m GHC.Base.>>=
                  (fun a =>
                     let cont_0__ arg_1__ :=
                       let 'pair a' b := arg_1__ in
                       GHC.MVar.putMVar m a' GHC.Base.>> GHC.Base.return_ b in
                     GHC.IO.onException (io a GHC.Base.>>= GHC.MVar.evaluate) (GHC.MVar.putMVar m a)
                     GHC.Base.>>=
                     cont_0__)).

Definition modifyMVar {a} {b}
   : GHC.MVar.MVar a -> (a -> GHC.MVar.IO (a * b)%type) -> GHC.MVar.IO b :=
  fun m io =>
    GHC.IO.mask (fun restore =>
                   GHC.MVar.takeMVar m GHC.Base.>>=
                   (fun a =>
                      let cont_0__ arg_1__ :=
                        let 'pair a' b := arg_1__ in
                        GHC.MVar.putMVar m a' GHC.Base.>> GHC.Base.return_ b in
                      GHC.IO.onException (restore (io a GHC.Base.>>= GHC.MVar.evaluate))
                                         (GHC.MVar.putMVar m a) GHC.Base.>>=
                      cont_0__)).

(* External variables:
     op_zt__ pair unit GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.IO.mask GHC.IO.mask_ GHC.IO.onException GHC.MVar.IO GHC.MVar.MVar
     GHC.MVar.evaluate GHC.MVar.putMVar GHC.MVar.takeMVar
*)
