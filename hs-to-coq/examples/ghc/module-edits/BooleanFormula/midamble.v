Local Fixpoint size {a} (bf: BooleanFormula a) : nat :=
  match bf with
    | Mk_Var a => 0
    | Mk_And xs => fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.Mk_L _ f => S (size f) end) xs)
    | Mk_Or xs => fold_right Nat.add 0 (Coq.Lists.List.map
        (fun lbf => match lbf with SrcLoc.Mk_L _ f => S (size f) end) xs)
    | Mk_Parens (SrcLoc.Mk_L _ bf) => S (size bf)
  end.

Fixpoint BooleanFormula_eq {a} `{GHC.Base.Eq_ a} (bf1 : BooleanFormula a) (bf2 : BooleanFormula a) : bool :=
  let eq' : Eq_ (BooleanFormula a) := GHC.Base.eq_default BooleanFormula_eq in
    match bf1 , bf2 with
      | Mk_Var a1 , Mk_Var b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_And a1 , Mk_And b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_Or a1 , Mk_Or b1 => GHC.Base.op_zeze__ a1 b1
      | Mk_Parens a1 , Mk_Parens b1 => GHC.Base.op_zeze__  a1 b1
      | _ , _ => false
    end.

Instance Eq_BooleanFormula {a} `{GHC.Base.Eq_ a} : GHC.Base.Eq_ (BooleanFormula a) :=
  GHC.Base.eq_default BooleanFormula_eq.

(* We can fmap below once we cont'ified the Functor type class *)
Local Definition BooleanFormula_fmap
   : forall {a} {b}, (a -> b) -> BooleanFormula a -> BooleanFormula b :=
  fun {a} {b} => fix BooleanFormula_fmap arg_114__ arg_115__ :=
      match arg_114__ , arg_115__ with
        | f , Mk_Var a1 => Mk_Var (f a1)
        | f , Mk_And a1 => Mk_And (GHC.Base.fmap (GHC.Base.fmap (BooleanFormula_fmap f)) a1)
        | f , Mk_Or a1 => Mk_Or (GHC.Base.fmap (GHC.Base.fmap (BooleanFormula_fmap f)) a1)
        | f , Mk_Parens a1 => Mk_Parens (GHC.Base.fmap (BooleanFormula_fmap f) a1)
      end.
