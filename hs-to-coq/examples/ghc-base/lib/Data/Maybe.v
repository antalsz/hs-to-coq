(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Let us be a bit explicit by having multiple axoims around *)
(* This one is for untranslatable expressions: *)
Local Axiom missingValue : forall {a}, a.
(* This one is for pattern match failures: *)
Local Axiom patternFailure : forall {a}, a.

(* Preamble *)

Require Import GHC.Prim.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Prim.

(* Converted declarations: *)

Definition catMaybes {a} : (list (option a)) -> (list a) :=
  fun arg_20__ =>
    match arg_20__ with
      | ls => let cont_21__ arg_22__ :=
                match arg_22__ with
                  | (Some x) => (x :: nil)
                  | _ => nil
                end in
              concatMap cont_21__ ls
    end.

Definition fromJust {a} : (option a) -> a :=
  fun arg_39__ =>
    let j_40__ := match arg_39__ with | (Some x) => x | _ => patternFailure end in
    match arg_39__ with
      | None => GHC.Prim.errorWithoutStackTrace &"Maybe.fromJust: Nothing"
      | _ => j_40__
    end.

Definition fromMaybe {a} : a -> ((option a) -> a) :=
  fun arg_33__ arg_34__ =>
    match arg_33__ , arg_34__ with
      | d , x => let j_35__ :=
                   match x with
                     | (Some v) => v
                     | _ => patternFailure
                   end in
                 match x with
                   | None => d
                   | _ => j_35__
                 end
    end.

Definition isJust {a} : (option a) -> bool :=
  fun arg_45__ => match arg_45__ with | None => false | _ => true end.

Definition isNothing {a} : (option a) -> bool :=
  fun arg_43__ => match arg_43__ with | None => true | _ => false end.

Definition listToMaybe {a} : (list a) -> (option a) :=
  fun arg_25__ =>
    let j_27__ :=
      match arg_25__ with
        | (cons a _) => Some a
        | _ => patternFailure
      end in
    match arg_25__ with
      | nil => None
      | _ => j_27__
    end.

Definition mapMaybe {a} {b} : (a -> (option b)) -> ((list a) -> (list b)) :=
  fix mapMaybe arg_10__ arg_11__
        := let j_18__ :=
             match arg_10__ , arg_11__ with
               | f , (cons x xs) => let rs := mapMaybe f xs in
                                    let scrut_13__ := f x in
                                    let j_15__ :=
                                      match scrut_13__ with
                                        | (Some r) => cons r rs
                                        | _ => patternFailure
                                      end in
                                    match scrut_13__ with
                                      | None => rs
                                      | _ => j_15__
                                    end
               | _ , _ => patternFailure
             end in
           match arg_10__ , arg_11__ with
             | _ , nil => nil
             | _ , _ => j_18__
           end.

Definition mapMaybeFB {b} {r} {a} : (b -> (r -> r)) -> ((a -> (option
                                    b)) -> (a -> (r -> r))) :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | cons_ , f , x , next => let scrut_4__ := f x in
                                let j_6__ :=
                                  match scrut_4__ with
                                    | (Some r) => cons_ r next
                                    | _ => patternFailure
                                  end in
                                match scrut_4__ with
                                  | None => next
                                  | _ => j_6__
                                end
    end.

Definition maybe {b} {a} : b -> ((a -> b) -> ((option a) -> b)) :=
  fun arg_47__ arg_48__ arg_49__ =>
    let j_51__ :=
      match arg_47__ , arg_48__ , arg_49__ with
        | _ , f , (Some x) => f x
        | _ , _ , _ => patternFailure
      end in
    match arg_47__ , arg_48__ , arg_49__ with
      | n , _ , None => n
      | _ , _ , _ => j_51__
    end.

Definition maybeToList {a} : (option a) -> (list a) :=
  fun arg_29__ =>
    let j_31__ :=
      match arg_29__ with
        | (Some x) => (x :: nil)
        | _ => patternFailure
      end in
    match arg_29__ with
      | None => nil
      | _ => j_31__
    end.

(* Unbound variables:
     :: GHC.Prim.errorWithoutStackTrace None Some bool concatMap cons false list nil
     option true
*)
