(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require Coq.Lists.List.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition catMaybes {a} : list (option a) -> list a :=
  fun ls =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Some x => cons x nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ ls.

Definition fromMaybe {a} : a -> option a -> a :=
  fun d x => match x with | None => d | Some v => v end.

Definition isJust {a} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => false | _ => true end.

Definition isNothing {a} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

Definition listToMaybe {a} : list a -> option a :=
  fun arg_0__ => match arg_0__ with | nil => None | cons a _ => Some a end.

Definition mapMaybe {a} {b} : (a -> option b) -> list a -> list b :=
  fix mapMaybe arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
           | _ , nil => nil
           | f , cons x xs =>
               let rs := mapMaybe f xs in match f x with | None => rs | Some r => cons r rs end
           end.

Definition mapMaybeFB {b} {r} {a} : (b -> r -> r) -> (a -> option
                                    b) -> a -> r -> r :=
  fun cons_ f x next =>
    match f x with
    | None => next
    | Some r => cons_ r next
    end.

Definition maybe {b} {a} : b -> (a -> b) -> option a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
    | n , _ , None => n
    | _ , f , Some x => f x
    end.

Definition maybeToList {a} : option a -> list a :=
  fun arg_0__ => match arg_0__ with | None => nil | Some x => cons x nil end.

(* Unbound variables:
     None Some bool cons false list nil option true Coq.Lists.List.flat_map
*)
