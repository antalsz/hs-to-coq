Parameter TcTyVarDetails : Type.  (* From TcType *)
Parameter CoercionHole : Type.
Parameter CType : Type.
Parameter RuntimeRepInfo : Type.

(* From Var *)
Inductive ExportFlag : Type := NotExported : ExportFlag
                            |  Exported : ExportFlag.
Inductive IdScope : Type := GlobalId : IdScope
                         |  LocalId : ExportFlag -> IdScope.


(* From TyCon *)
Definition TyConRepName := Name.Name%type.

Inductive Injectivity : Type := NotInjective : Injectivity
                             |  Injective : list bool -> Injectivity.
