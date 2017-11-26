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

Local Definition BooleanFormula_traverse
    : forall {f} {a} {b},   forall `{GHC.Base.Applicative f}, (a -> f b) -> BooleanFormula a -> f (BooleanFormula b) :=
  fun {f0} {a} {b} `{GHC.Base.Applicative f0} => fix BooleanFormula_traverse arg_144__ arg_145__ :=
      match arg_144__ , arg_145__ with
        | f , Mk_Var a1 => GHC.Base.fmap  Mk_Var (f a1)
        | f , Mk_And a1 => GHC.Base.fmap Mk_And (Data.Traversable.traverse (Data.Traversable.traverse
                                                                           (BooleanFormula_traverse f)) a1)
        | f , Mk_Or a1 => GHC.Base.fmap Mk_Or
                        (@Data.Traversable.traverse _ _ _ _ f0 _ _ _ _ (Data.Traversable.traverse
                                                                          (BooleanFormula_traverse f)) a1)
        | f , Mk_Parens a1 => GHC.Base.fmap Mk_Parens
                             (@Data.Traversable.traverse _ _ _ _ f0 _ _ _ _  (BooleanFormula_traverse f) a1)
      end.

Local Definition BooleanFormula_foldMap
    : forall {m} {a},
        forall `{GHC.Base.Monoid m}, (a -> m) -> BooleanFormula a -> m :=
  fun {m} {a} `{GHC.Base.Monoid m} => fix foldMap arg_137__ arg_138__ :=
      match arg_137__ , arg_138__ with
        | f , Mk_Var a1 => f a1
        | f , Mk_And a1 => Data.Foldable.foldMap (Data.Foldable.foldMap
                                                 (foldMap f)) a1
        | f , Mk_Or a1 => Data.Foldable.foldMap (Data.Foldable.foldMap
                                                (foldMap f)) a1
        | f , Mk_Parens a1 => Data.Foldable.foldMap (foldMap f) a1
      end.

Local Definition BooleanFormula_foldr
    : forall {a} {b}, (a -> b -> b) -> b -> BooleanFormula a -> b :=
  fun {a} {b} => fix foldr arg_97__ arg_98__ arg_99__ :=
      match arg_97__ , arg_98__ , arg_99__ with
        | f , z , Mk_Var a1 => f a1 z
        | f , z , Mk_And a1 => (fun arg_101__ arg_102__ =>
                                 match arg_101__ , arg_102__ with
                                   | b5 , b6 => Data.Foldable.foldr (fun arg_103__ arg_104__ =>
                                                                      match arg_103__ , arg_104__ with
                                                                        | b3 , b4 => Data.Foldable.foldr (fun arg_105__
                                                                                                              arg_106__ =>
                                                                                                           match arg_105__
                                                                                                               , arg_106__ with
                                                                                                             | b1 ,
                                                                                                               b2 =>
                                                                                                               foldr
                                                                                                               f b2 b1
                                                                                                           end) b4 b3
                                                                      end) b6 b5
                                 end) a1 z
        | f , z , Mk_Or a1 => (fun arg_114__ arg_115__ =>
                                match arg_114__ , arg_115__ with
                                  | b5 , b6 => Data.Foldable.foldr (fun arg_116__ arg_117__ =>
                                                                     match arg_116__ , arg_117__ with
                                                                       | b3 , b4 => Data.Foldable.foldr (fun arg_118__
                                                                                                             arg_119__ =>
                                                                                                          match arg_118__
                                                                                                              , arg_119__ with
                                                                                                            | b1 , b2 =>
                                                                                                              foldr
                                                                                                              f b2 b1
                                                                                                          end) b4 b3
                                                                     end) b6 b5
                                end) a1 z
        | f , z , Mk_Parens a1 => (fun arg_127__ arg_128__ =>
                                    match arg_127__ , arg_128__ with
                                      | b3 , b4 => Data.Foldable.foldr (fun arg_129__ arg_130__ =>
                                                                         match arg_129__ , arg_130__ with
                                                                           | b1 , b2 => foldr f b2 b1
                                                                         end) b4 b3
                                    end) a1 z
      end.
