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
    let cont_12__ arg_13__ :=
      match arg_13__ with
        | Some x => cons x nil
        | _ => nil
      end in
    Coq.Lists.List.flat_map cont_12__ ls.

Definition fromMaybe {a} : a -> option a -> a :=
  fun d x => match x with | None => d | Some v => v end.

Definition isJust {a} : option a -> bool :=
  fun arg_25__ => match arg_25__ with | None => false | _ => true end.

Definition isNothing {a} : option a -> bool :=
  fun arg_23__ => match arg_23__ with | None => true | _ => false end.

Definition listToMaybe {a} : list a -> option a :=
  fun arg_15__ => match arg_15__ with | nil => None | cons a _ => Some a end.

Definition mapMaybe {a} {b} : (a -> option b) -> list a -> list b :=
  fix mapMaybe arg_4__ arg_5__
        := match arg_4__ , arg_5__ with
             | _ , nil => nil
             | f , cons x xs => let rs := mapMaybe f xs in
                                let scrut_7__ := f x in
                                match scrut_7__ with
                                  | None => rs
                                  | Some r => cons r rs
                                end
           end.

Definition mapMaybeFB {b} {r} {a} : (b -> r -> r) -> (a -> option
                                    b) -> a -> r -> r :=
  fun cons_ f x next =>
    let scrut_0__ := f x in
    match scrut_0__ with
      | None => next
      | Some r => cons_ r next
    end.

Definition maybe {b} {a} : b -> (a -> b) -> option a -> b :=
  fun arg_27__ arg_28__ arg_29__ =>
    match arg_27__ , arg_28__ , arg_29__ with
      | n , _ , None => n
      | _ , f , Some x => f x
    end.

Definition maybeToList {a} : option a -> list a :=
  fun arg_18__ => match arg_18__ with | None => nil | Some x => cons x nil end.

(* Unbound variables:
     Coq.Lists.List.flat_map None Some bool cons false list nil option true
*)
