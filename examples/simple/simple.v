(* Preamble *)
Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

Require Coq.Lists.List.
Open Scope list_scope.

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted data type declarations: *)
Inductive Weekday : Type := Mk_Monday : Weekday
                         |  Mk_Tuesday : Weekday
                         |  Mk_Wednesday : Weekday
                         |  Mk_Thursday : Weekday
                         |  Mk_Friday : Weekday
                         |  Mk_Saturday : Weekday
                         |  Mk_Sunday : Weekday.

Inductive Maybe a : Type := Mk_Nothing : (Maybe a)
                         |  Mk_Just : (a -> (Maybe a)).

Definition Option := (Maybe%type).

Arguments Mk_Nothing {_}.

(* Converted value declarations: *)
Definition not : (bool -> bool) := (fun __arg_4__ =>
                                     (match __arg_4__ with
                                       | true => false
                                       | false => true
                                     end)).

Definition map {a} {b} : (((a -> b)) -> ((list a) -> (list b))) := (fix map
                                                                          __arg_5__ __arg_6__ := (match __arg_5__
                                                                                                      , __arg_6__ with
                                                                                                   | _ , nil => nil
                                                                                                   | f , (x :: xs) =>
                                                                                                     ((f x) :: ((map f)
                                                                                                     xs))
                                                                                                 end)).

Definition isWeekend : (Weekday -> bool) := (fun __arg_0__ =>
                                              (match __arg_0__ with
                                                | Mk_Saturday => true
                                                | Mk_Sunday => true
                                                | _ => false
                                              end)).

Definition lazyApply {a} {b} : (Weekday -> (((a -> b)) -> (a -> (Maybe b)))) :=
  (fun __arg_1__
       __arg_2__
       __arg_3__ =>
    (match __arg_1__ , __arg_2__ , __arg_3__ with
      | day , f , x => (if (isWeekend day)
                       then Mk_Nothing
                       else (Mk_Just ((f x))))
    end)).

(* No type class instance declarations to convert. *)

(* Unbound variables:
     :: bool false list true
*)
