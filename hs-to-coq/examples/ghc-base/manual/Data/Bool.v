(* Preamble *)

(* No data type declarations to convert. *)

(* Converted value declarations: *)
Definition mk_bool {a} : a -> (a -> (bool -> a)) := fun arg_0__
                                                     arg_1__
                                                     arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , _ , false => f
      | _ , t , true => t
    end.

(* No type class instance declarations to convert. *)

(* Unbound variables:
     bool
*)
