(* records field accesses are not fully qualified. *)
Require Import Module.

Instance Uniquable_OccName : Unique.Uniquable OccName := {}.
Admitted.


Definition compare_Namespace : NameSpace -> NameSpace -> comparison :=
  fun x y => match x , y with
          | VarName   , VarName   => Eq
          | VarName   , _         => Lt
          | _         , VarName   => Gt
          | DataName  , DataName  => Eq
          | _         , DataName  => Lt
          | DataName  , _         => Gt
          | TvName    , TvName    => Eq
          | _         , TvName    => Lt
          | TvName    , _         => Gt
          | TcClsName , TcClsName => Eq
          end.

Local Definition NameSpace_op_zg__ : NameSpace -> NameSpace -> bool :=
  fun x y => match compare_Namespace x y with
            | Gt => true
            | _  => false
          end.

Local Definition NameSpace_op_zgze__ : NameSpace -> NameSpace -> bool :=
  fun x y => match compare_Namespace x y with
            | Gt => true
            | Eq => true
            | _  => false
          end.

Local Definition NameSpace_op_zl__ : NameSpace -> NameSpace -> bool :=
  fun x y => match compare_Namespace x y with
            | Lt => true
            | _  => false
          end.
Local Definition NameSpace_op_zlze__ : NameSpace -> NameSpace -> bool :=
  fun x y => match compare_Namespace x y with
            | Lt => true
            | Eq => true
            | _  => false
          end.

(* Axioms for operations that we cannot yet translate *)

Axiom isDataSymOcc : OccName -> bool.
Axiom isSymOcc : OccName -> bool.
Axiom chooseUniqueOcc : NameSpace -> GHC.Base.String -> OccSet -> OccName.
Axiom startsWithUnderscore : OccName -> bool.
Axiom isDerivedOccName : OccName -> bool.
Axiom mkGenS : Module.Module -> OccName -> GHC.Num.Int -> GHC.Num.Int -> OccName.
Axiom mkGenC : Module.Module -> OccName -> GHC.Num.Int -> OccName .
Axiom tidyOccName : TidyOccEnv -> OccName -> (TidyOccEnv * OccName)%type.
Axiom mkSuperDictAuxOcc : GHC.Num.Int -> OccName -> OccName.
Axiom mkSuperDictSelOcc : GHC.Num.Int -> OccName -> OccName.
Axiom mkLocalOcc : Unique.Unique -> OccName -> OccName.

(* Default values *)
Require Import GHC.Err.
Instance Default__OccName : Default OccName := Build_Default _ (Mk_OccName default default).
