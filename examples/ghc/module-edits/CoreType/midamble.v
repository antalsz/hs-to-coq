(* Primitive types *)
(* From TysPrim *)
Parameter addrPrimTy   : Type_.
Parameter charPrimTy   : Type_.
Parameter intPrimTy    : Type_.
Parameter wordPrimTy   : Type_.
Parameter int64PrimTy  : Type_.
Parameter word64PrimTy : Type_.
Parameter floatPrimTy  : Type_.
Parameter doublePrimTy : Type_.

(* From DataCon *)
Parameter dataConWorkId       : DataCon.DataCon -> Var.
Parameter dataConExTyVars     : DataCon.DataCon -> list TyVar.

(* From PatSyn *)
Parameter patSynExTyVars     : PatSyn.PatSyn -> list TyVar.

(* From ConLike *)
Definition conLikeExTyVars : ConLike.ConLike -> list TyVar :=
  fun arg_0__ =>
    match arg_0__ with
      | ConLike.RealDataCon dcon1 => dataConExTyVars dcon1
      | ConLike.PatSynCon psyn1 => patSynExTyVars psyn1
    end.

(* From Class *)
Parameter classTyVars : Class.Class -> list TyVar.
Parameter classMethods : Class.Class -> list Var.
Parameter classAllSelIds : Class.Class -> list Var.
Definition classArity : Class.Class -> BasicTypes.Arity :=
  fun clas => Data.Foldable.length (classTyVars clas).
