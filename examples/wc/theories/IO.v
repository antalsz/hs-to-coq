Require Import GHC.Base.
  
Require Export IO.
Require Export Control.Concurrent.Async.

Reserved Notation "R ;; G ⊨ {{ Pre }} C {{ Post }}" (at level 42).

Record File :=
  MkFile { open : bool ;
           content : String
         }.

Definition State : Type := File.

Definition StateChange : Type := State -> State -> Prop.

Definition Rely := StateChange.

Definition Guarantee := StateChange.

Axiom intersection : StateChange -> StateChange -> StateChange.

Axiom union : StateChange -> StateChange -> StateChange.

Axiom refines : StateChange -> StateChange -> Prop.

Definition Pre := State -> Prop.

Definition Post (A : Type) := A -> State -> Prop.

Inductive RGHoare : forall {A : Type}, Rely -> Guarantee -> Pre -> Post A -> IO A -> Prop :=
| OpenFdRule : forall p om of off,
    RGHoare (fun _ _ => True)
            (fun _ _ => True)
            (fun s => open s = false)
            (fun a s => open s = true)
            (openFd p om of off)
| ConcurrentlyRule : forall A B (c1 : IO A) G1 pre1 post1 (c2 : IO B) G2 pre2 post2 R,
    RGHoare (union R G2) G1 pre1 post1 c1 ->
    RGHoare (union R G1) G2 pre2 post2 c2 ->
    RGHoare R (union G1 G2)
            (fun s => pre1 s /\ pre2 s)
            (fun '(a, b) s => post1 a s /\ post2 b s)
            (concurrently c1 c2)
| SeqRule : forall A B (c1 : IO A) (c2 : A -> IO B) R G pre mid post,
    RGHoare R G pre mid c1 ->
    (forall a, RGHoare R G (mid a) post (c2 a)) ->
    RGHoare R G pre post (c1 >>= c2) 
| RelaxRule : forall A (c : IO A) R G R' G' pre post,
    refines R R' ->
    refines G' G ->
    RGHoare R' G' pre post c ->
    RGHoare R G pre post c.
            
