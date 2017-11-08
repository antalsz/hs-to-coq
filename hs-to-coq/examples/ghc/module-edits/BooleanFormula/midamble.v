Local Fixpoint size {a} (bf: BooleanFormula a) : nat :=
  match bf with
    | Mk_Var a => 0
    | Mk_And xs => fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.Mk_L _ f => S (size f) end) xs)
    | Mk_Or xs => fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.Mk_L _ f => S (size f) end) xs)
    | Mk_Parens (SrcLoc.Mk_L _ bf) => S (size bf)
  end.

Fixpoint BooleanFormula_eq {a} `{GHC.Base.Eq_ a} (bf1 : BooleanFormula a) (bf2 : BooleanFormula a) {struct bf1} : bool :=
  let eq' := (@Build_Eq_ (BooleanFormula a) BooleanFormula_eq (fun a b => negb (BooleanFormula_eq a b))) in
  let leq' := (@Build_Eq_ (LBooleanFormula a) SrcLoc.instance_forall___GHC_Base_Eq__e____GHC_Base_Eq__l___GHC_Base_Eq___GenLocated_l_e__op_zeze__ (fun a b => negb (SrcLoc.instance_forall___GHC_Base_Eq__e____GHC_Base_Eq__l___GHC_Base_Eq___GenLocated_l_e__op_zeze__ a b))) in
  let listleq' := (@Build_Eq_ (list (LBooleanFormula a)) eqlist (fun a b => negb (eqlist a b))) in
    match bf1 , bf2 with
      | Mk_Var a1 , Mk_Var b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_And a1 , Mk_And b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_Or a1 , Mk_Or b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_Parens a1 , Mk_Parens b1 => GHC.Base.op_zeze__  a1 b1
      | _ , _ => false
    end.

Instance instance_forall___GHC_Base_Eq__a___GHC_Base_Eq___BooleanFormula_a_
  : forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (BooleanFormula a) := {
  op_zeze__ := BooleanFormula_eq ;
  op_zsze__ := fun a b => negb (BooleanFormula_eq a b) }.


(* We can fmap below once we cont'ified the Functor type class *)
Local Definition BooleanFormula_fmap
   : forall {a} {b}, (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  fun {a} {b} => fix BooleanFormula_fmap arg_114__ arg_115__ :=
      match arg_114__ , arg_115__ with
        | f , Mk_Var a1 => Mk_Var (f a1)
        | f , Mk_And a1 => Mk_And (GHC.Base.map (SrcLoc.instance_GHC_Base_Functor__GenLocated_l__fmap (BooleanFormula_fmap f)) a1)
        | f , Mk_Or a1 => Mk_Or (GHC.Base.map (SrcLoc.instance_GHC_Base_Functor__GenLocated_l__fmap (BooleanFormula_fmap f)) a1)
        | f , Mk_Parens a1 => Mk_Parens (SrcLoc.instance_GHC_Base_Functor__GenLocated_l__fmap (BooleanFormula_fmap f) a1)
      end.
