(* Test file for Certicoq by Olivier Belanger *)
(* UNCOMMENT THESE FOR INTERACTIVE *)
Add LoadPath "base".
 Add LoadPath "lib". 
Require Import Data.IntSet.Internal.
Require Import  Coq.Numbers.BinNums.
Require Import BinNat.
Import Coq.Lists.List.
Open Scope list_scope. 

Fixpoint generateList' {A} (succ: A -> A) (geq: A -> A -> bool) (curr:A) (l:list A) (max:A) (fuel:nat) := 
         if geq curr max then l
         else
           (match fuel with
            | 0 => l
            | S fuel => 
              generateList' succ geq (succ curr) (curr::l) max fuel
            end
           ).
         
Definition generateList {A} (succ: A -> A) (geq: A -> A -> bool) (start:A) (max:A) (fuel:nat) :=
  List.reverse (generateList' succ geq start nil max fuel).

(* so that the shrink-reducer doesn't start running the benchmark...*)
Fixpoint apply {A B} (n:nat) (function:A -> B) (arg:A) :=
  match n with
  | S n =>
    (match n with
     | S n' =>    
       apply' n' function arg
     | _ =>
       apply' n function arg
     end)
  | _ =>
    function arg
  end
with apply' {A B} (n:nat) (f:A -> B) (a:A) :=
       match n with
       | S n =>
         @apply A B n f a
       | _ =>
         f a
       end.        


Definition size := 4096.


Definition geb (x: N) (y:N): bool := BinNat.N.ltb x y.

Definition elems := generateList BinNat.N.succ geb 0%N (BinNat.N.of_nat size) size.
Definition elems_even := generateList (fun x => N.succ (N.succ x))  geb 0%N (BinNat.N.of_nat size) size.
Definition elems_odd := generateList (fun x => N.succ (N.succ x))  geb 1%N (BinNat.N.of_nat size) size.


Definition s := fromList elems.
Definition s_even := fromList elems_even.
Definition s_odd := fromList elems_odd.



Definition bench_bool (f:Key -> IntSet -> bool) (l:list Key) (s:IntSet) :=
  fold_left (fun b k => andb b (f k s))  l true.


Definition b_member (_:unit) := apply 0 (bench_bool member elems) s.




Definition b_filter (_:unit) := negb (equal (Internal.empty) (apply 0 (Internal.filter N.even) s)).

Definition b_insert (_:unit) :=
  negb (equal (Internal.empty) (apply 0 (fold_left (fun s a => Internal.insert a s) elems) Internal.empty)).

Definition b_partition (_:unit) :=
  negb (equal (fst (apply 0 (Internal.partition (fun k => N.eqb (N.modulo k 2) 0)%N) s)) empty).
  

Definition b_map (_:unit) :=
  negb (equal (apply 0 (Internal.map (fun k => k + 1)%N) s) empty).


Definition b_fold (_:unit) :=
  negb (Nat.eqb (length (apply 0 (Internal.fold (fun k l => k::l) nil) s))  0).


Definition b_delete (_:unit) :=
  equal (apply 0 (fold_left (fun s k => Internal.delete k s) elems) s) empty.


Definition b_unions (_:unit) :=
  negb (equal (apply 0 Internal.unions (s_even::s_odd::nil)) empty).

Definition b_union (_:unit) :=
  negb (equal (apply 0 (Internal.union s_even) s_odd) empty).


Definition b_difference (_ : unit) :=
  negb (equal (apply 0 (Internal.difference s) s_even) empty).

Definition b_fromList (_: unit) :=
  negb (equal (apply 0 (Internal.fromList) elems) empty).

SearchAbout bool.

Definition b_disjoint_false (_:unit) :=
  Bool.eqb (apply 0 (Internal.disjoint s) s_even) false.

Definition b_disjoint_true (_:unit) :=
  Bool.eqb (apply 0 (Internal.disjoint s_odd) s_even) true.


Definition b_intersection_false (_:unit) :=
  negb (equal (apply 0 (Internal.intersection s) s_even) empty).

 
Definition b_intersection_true (_: unit) :=
  (equal (apply 0 (Internal.intersection s_odd) s_even) empty).

Definition no_b (a:unit) :=
  apply 0 (fun (a:unit) => false) a.


Definition bench_list :=  no_b::b_member::b_insert::b_filter::no_b::b_partition::b_map::b_fold::b_delete::b_fromList::no_b::nil.  (* b_unions::b_union::nil b_difference::b_fromList:: nil. *)
 
(* does not compile *)
Definition bench_list2 := b_unions::b_union::b_difference::b_intersection_true::b_intersection_false::b_disjoint_false::b_disjoint_true::nil.


Definition main := 
  apply 0 (List.map (fun f => f tt )) bench_list.


Definition main_fail := 
  List.map (fun f => f tt ) bench_list.

 Extraction "intset_test" main.


Require Import Arith.
Add LoadPath "../plugin" as CertiCoq.Plugin.
Require Import CertiCoq.Plugin.CertiCoq.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf.




                     
 
CertiCoq Compile main.
