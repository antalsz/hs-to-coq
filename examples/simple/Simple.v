(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive Weekday : Type := Monday : Weekday
                         |  Tuesday : Weekday
                         |  Wednesday : Weekday
                         |  Thursday : Weekday
                         |  Friday : Weekday
                         |  Saturday : Weekday
                         |  Sunday : Weekday.
(* Converted value declarations: *)

(* Translating `instance GHC.Show.Show Simple.Weekday' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Definition isWeekend : Weekday -> bool :=
  fun arg_6__ =>
    match arg_6__ with
      | Saturday => true
      | Sunday => true
      | _ => false
    end.

Definition lazyApply {a} {b} : Weekday -> (a -> b) -> a -> option b :=
  fun day f x =>
    let j_8__ := Some (f x) in if isWeekend day : bool then None else j_8__.

Definition map {a} {b} : (a -> b) -> list a -> list b :=
  fix map arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , nil => nil
             | f , cons x xs => cons (f x) (map f xs)
           end.

Definition not : bool -> bool :=
  fun arg_4__ => match arg_4__ with | true => false | false => true end.

(* Unbound variables:
     None Some bool cons false list option true
*)
