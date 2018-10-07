Require Data.List.NonEmpty.

Definition sconcat {a} `{GHC.Base.Semigroup a} : GHC.Base.NonEmpty a -> a :=
  Data.List.NonEmpty.NonEmpty_foldr1 (@GHC.Base.op_zlzlzgzg__ a _).

(* ------------------------- *)

(* These two instances are here because we don't mangle the instance names
   enough. This file creates instances for Monoid.First and Semigroup.First
   (which are different types.) But we produce the same names for them.
*)

Local Definition Semigroup__SFirst_op_zlzlzgzg__ {inst_a} : (First inst_a) -> (First
                                                       inst_a) -> (First inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | a , _ => a end.

Local Definition Semigroup__SFirst_sconcat {inst_a} : GHC.Base.NonEmpty
                                                     (First inst_a) -> (First inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SFirst_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.



Program Instance Semigroup__SFirst {a} : GHC.Base.Semigroup (First a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SFirst_op_zlzlzgzg__ |}.

Local Definition Semigroup__SLast_op_zlzlzgzg__ {inst_a} : (Last inst_a) -> (Last
                                                      inst_a) -> (Last inst_a) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | _ , b => b end.

Local Definition Semigroup__SLast_sconcat {inst_a} : GHC.Base.NonEmpty
                                                    (Last inst_a) -> (Last inst_a) :=
  fun arg_0__ =>
    match arg_0__ with
      | GHC.Base.NEcons a as_ => let fix go arg_1__ arg_2__
                                                     := match arg_1__ , arg_2__ with
                                                          | b , cons c cs => Semigroup__SLast_op_zlzlzgzg__ b (go c cs)
                                                          | b , nil => b
                                                        end in
                                           go a as_
    end.


Program Instance Semigroup__SLast {a} : GHC.Base.Semigroup (Last a) := fun _ k =>
    k {| GHC.Base.op_zlzlzgzg____ := Semigroup__SLast_op_zlzlzgzg__ |}.

(* ------------------------- *)
