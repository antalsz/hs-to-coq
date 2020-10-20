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
Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition maybe {b} {a} : b -> (a -> b) -> option a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | n, _, None => n
    | _, f, Some x => f x
    end.

Definition isJust {a} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => false | _ => true end.

Definition isNothing {a} : option a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

(* Skipping definition `Data.Maybe.fromJust' *)

Definition fromMaybe {a} : a -> option a -> a :=
  fun d x => match x with | None => d | Some v => v end.

Definition maybeToList {a} : option a -> list a :=
  fun arg_0__ => match arg_0__ with | None => nil | Some x => cons x nil end.

Definition listToMaybe {a} : list a -> option a :=
  GHC.Base.foldr (GHC.Base.const GHC.Base.∘ Some) None.

Definition catMaybes {a} : list (option a) -> list a :=
  fun ls =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Some x => cons x nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ ls.

Fixpoint mapMaybe {a} {b} (arg_0__ : (a -> option b)) (arg_1__ : list a) : list
                                                                           b
           := match arg_0__, arg_1__ with
              | _, nil => nil
              | f, cons x xs =>
                  let rs := mapMaybe f xs in match f x with | None => rs | Some r => cons r rs end
              end.

Definition mapMaybeFB {b} {r} {a}
   : (b -> r -> r) -> (a -> option b) -> a -> r -> r :=
  fun cons_ f x next =>
    match f x with
    | None => next
    | Some r => cons_ r next
    end.

(* External variables:
     None Some bool cons false list nil option true Coq.Lists.List.flat_map
     GHC.Base.const GHC.Base.foldr GHC.Base.op_z2218U__
*)
