Require Import GHC.Prim.
Instance Unpeel_WrappedMonoid a : Unpeel (WrappedMonoid a) a := Build_Unpeel _ _ unwrapMonoid WrapMonoid.
Instance Unpeel_Last  a : Unpeel (Last a) a := Build_Unpeel _ _ getLast Mk_Last.
Instance Unpeel_First  a : Unpeel (First a) a := Build_Unpeel _ _ getFirst Mk_First.
Instance Unpeel_Max  a : Unpeel (Max a) a := Build_Unpeel _ _ getMax Mk_Max.
Instance Unpeel_Min  a : Unpeel (Min a) a := Build_Unpeel _ _ getMin Mk_Min.
Instance Unpeel_Option  a : Unpeel (Option a) (option a) := Build_Unpeel _ _ getOption Mk_Option.

(* ------------------------- *)

(* These two instances are here because we don't mangle the instance names
   enough. This file creates instances for Monoid.First and Semigroup.First
   (which are different types.) But we produce the same names for them.
*)

Local Definition Semigroup__SFirst_op_zlzg__ {inst_a} : (First inst_a) -> (First
                                                       inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | a , _ => a end.

Local Definition Semigroup__SFirst_sconcat {inst_a} : Data.List.NonEmpty.NonEmpty
                                                     (First inst_a) -> (First inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SFirst_op_zlzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.



Program Instance Semigroup__SFirst {a} : Semigroup (First a) := fun _ k =>
    k {|op_zlzg____ := Semigroup__SFirst_op_zlzg__ ;
      sconcat__ := Semigroup__SFirst_sconcat |}.

Local Definition Semigroup__SLast_op_zlzg__ {inst_a} : (Last inst_a) -> (Last
                                                      inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | _ , b => b end.

Local Definition Semigroup__SLast_sconcat {inst_a} : Data.List.NonEmpty.NonEmpty
                                                    (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | Data.List.NonEmpty.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SLast_op_zlzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.


Program Instance Semigroup__SLast {a} : Semigroup (Last a) := fun _ k =>
    k {|op_zlzg____ := Semigroup__SLast_op_zlzg__ ;
      sconcat__ := Semigroup__SLast_sconcat |}.

(* ------------------------- *)