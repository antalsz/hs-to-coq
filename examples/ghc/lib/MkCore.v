(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.Num.
Require Id.
Require Literal.
Require Name.
Require Panic.
Require PrelNames.
Require Type.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive FloatBind : Type
  := | FloatLet : Core.CoreBind -> FloatBind
  |  FloatCase
   : Core.CoreExpr -> Core.Id -> Core.AltCon -> list Core.Var -> FloatBind.

(* Converted value declarations: *)

Definition wrapFloat : FloatBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FloatLet defns, body => Core.Let defns body
    | FloatCase e b con bs, body =>
        Core.Case e b (CoreUtils.exprType body) (cons (pair (pair con bs) body) nil)
    end.

Axiom unitDataConId : Core.Id.

Definition unitExpr : Core.CoreExpr :=
  Core.Mk_Var unitDataConId.

Axiom tYPE_ERROR_ID : Core.Id.

Axiom sortQuantVars : list Core.Var -> list Core.Var.

Axiom runtimeErrorTy : AxiomatizedTypes.Type_.

Axiom rUNTIME_ERROR_ID : Core.Id.

Axiom rEC_SEL_ERROR_ID : Core.Id.

Axiom rEC_CON_ERROR_ID : Core.Id.

Axiom pAT_ERROR_ID : Core.Id.

Axiom nO_METHOD_BINDING_ERROR_ID : Core.Id.

Axiom nON_EXHAUSTIVE_GUARDS_ERROR_ID : Core.Id.

Axiom mkWordExprWord : DynFlags.DynFlags -> GHC.Num.Word -> Core.CoreExpr.

Axiom mkWordExpr : DynFlags.DynFlags -> GHC.Num.Integer -> Core.CoreExpr.

Definition mkWildValBinder : AxiomatizedTypes.Type_ -> Core.Id :=
  fun ty => Id.mkLocalIdOrCoVar PrelNames.wildCardName ty.

Definition mk_val_app
   : Core.CoreExpr ->
     Core.CoreExpr ->
     AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun fun_ arg arg_ty res_ty =>
    let arg_id := mkWildValBinder arg_ty in
    if negb (CoreUtils.needsCaseBinding arg_ty arg) : bool
    then Core.App fun_ arg else
    Core.Case arg arg_id res_ty (cons (pair (pair Core.DEFAULT nil) (Core.App fun_
                                             (Core.Mk_Var arg_id))) nil).

Definition mkWildEvBinder : AxiomatizedTypes.PredType -> Core.EvVar :=
  fun pred => mkWildValBinder pred.

Definition mkWildCase
   : Core.CoreExpr ->
     AxiomatizedTypes.Type_ ->
     AxiomatizedTypes.Type_ -> list Core.CoreAlt -> Core.CoreExpr :=
  fun scrut scrut_ty res_ty alts =>
    Core.Case scrut (mkWildValBinder scrut_ty) res_ty alts.

Axiom tupleDataCon : BasicTypes.Boxity -> nat -> Core.DataCon.

Definition mkSmallTupleSelector1
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    if andb Util.debugIsOn (negb (Util.notNull vars)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/MkCore.hs")
          #487)
    else Core.Case scrut scrut_var (Id.idType the_var) (cons (pair (pair
                                                                    (Core.DataAlt (tupleDataCon BasicTypes.Boxed
                                                                                   (Coq.Lists.List.length vars))) vars)
                                                                   (Core.Mk_Var the_var)) nil).

Definition mkSmallTupleSelector
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | cons var nil, should_be_the_same_var, _, scrut =>
        if andb Util.debugIsOn (negb (var GHC.Base.== should_be_the_same_var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/MkCore.hs")
              #479)
        else scrut
    | vars, the_var, scrut_var, scrut =>
        mkSmallTupleSelector1 vars the_var scrut_var scrut
    end.

Axiom chunkify : list Core.Id -> list (list Core.Id).

Axiom mkBoxedTupleTy : list unit -> unit.

Definition mkTupleSelector
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    let mk_tup_sel :=
      GHC.DeferredFix.deferredFix2 (fun mk_tup_sel arg_0__ arg_1__ =>
                                      match arg_0__, arg_1__ with
                                      | cons vars nil, the_var => mkSmallTupleSelector vars the_var scrut_var scrut
                                      | vars_s, the_var =>
                                          let tpl_tys :=
                                            Coq.Lists.List.flat_map (fun gp =>
                                                                       cons (mkBoxedTupleTy (GHC.Base.map Id.idType gp))
                                                                            nil) vars_s in
                                          let tpl_vs := Id.mkTemplateLocals tpl_tys in
                                          match (let cont_5__ arg_6__ :=
                                                     let 'pair tpl gp := arg_6__ in
                                                     if Data.Foldable.elem the_var gp : bool
                                                     then cons (pair tpl gp) nil else
                                                     nil in
                                                   Coq.Lists.List.flat_map cont_5__ (Util.zipEqual (GHC.Base.hs_string__
                                                                                                    "mkTupleSelector")
                                                                            tpl_vs vars_s)) with
                                          | cons (pair tpl_v group) nil =>
                                              mkSmallTupleSelector group the_var tpl_v (mk_tup_sel (chunkify tpl_vs)
                                                                                                   tpl_v)
                                          | _ => GHC.Err.patternFailure
                                          end
                                      end) in
    mk_tup_sel (chunkify vars) the_var.

Definition mkTupleSelector1
   : list Core.Id -> Core.Id -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun vars the_var scrut_var scrut =>
    match vars with
    | cons _ nil => mkSmallTupleSelector1 vars the_var scrut_var scrut
    | _ => mkTupleSelector vars the_var scrut_var scrut
    end.

Definition mkSmallTupleCase
   : list Core.Id -> Core.CoreExpr -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | cons var nil, body, _scrut_var, scrut => CoreUtils.bindNonRec var scrut body
    | vars, body, scrut_var, scrut =>
        Core.Case scrut scrut_var (CoreUtils.exprType body) (cons (pair (pair
                                                                         (Core.DataAlt (tupleDataCon BasicTypes.Boxed
                                                                                        (Coq.Lists.List.length vars)))
                                                                         vars) body) nil)
    end.

Definition mkTupleCase
   : UniqSupply.UniqSupply ->
     list Core.Id -> Core.CoreExpr -> Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun uniqs vars body scrut_var scrut =>
    let one_tuple_case :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | chunk_vars, pair (pair us vs) body =>
            let 'pair uniq us' := UniqSupply.takeUniqFromSupply us in
            let scrut_var :=
              Id.mkSysLocal (FastString.fsLit (GHC.Base.hs_string__ "ds")) uniq
              (mkBoxedTupleTy (GHC.Base.map Id.idType chunk_vars)) in
            let body' :=
              mkSmallTupleCase chunk_vars body scrut_var (Core.Mk_Var scrut_var) in
            pair (pair us' (cons scrut_var vs)) body'
        end in
    let mk_tuple_case :=
      GHC.DeferredFix.deferredFix3 (fun mk_tuple_case arg_7__ arg_8__ arg_9__ =>
                                      match arg_7__, arg_8__, arg_9__ with
                                      | _, cons vars nil, body => mkSmallTupleCase vars body scrut_var scrut
                                      | us, vars_s, body =>
                                          let 'pair (pair us' vars') body' := Data.Foldable.foldr one_tuple_case (pair
                                                                                                                  (pair
                                                                                                                   us
                                                                                                                   nil)
                                                                                                                  body)
                                                                                vars_s in
                                          mk_tuple_case us' (chunkify vars') body'
                                      end) in
    mk_tuple_case uniqs (chunkify vars) body.

Axiom mkRuntimeErrorId : Name.Name -> Core.Id.

Definition mkRuntimeErrorApp
   : Core.Id -> AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr :=
  fun err_id res_ty err_msg =>
    let err_string := Core.Lit (Literal.mkMachString err_msg) in
    Core.mkApps (Core.Mk_Var err_id) (cons (Core.Type_ (Type.getRuntimeRep res_ty))
                                           (cons (Core.Type_ res_ty) (cons err_string nil))).

Axiom nothingDataCon : Core.DataCon.

Definition mkNothingExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun ty => Core.mkConApp nothingDataCon (cons (Core.Type_ ty) nil).

Axiom justDataCon : Core.DataCon.

Definition mkJustExpr
   : AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr :=
  fun ty val => Core.mkConApp justDataCon (cons (Core.Type_ ty) (cons val nil)).

Axiom mkIntExprInt : DynFlags.DynFlags -> nat -> Core.CoreExpr.

Axiom mkIntExpr : DynFlags.DynFlags -> GHC.Num.Integer -> Core.CoreExpr.

Definition mkImpossibleExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun res_ty =>
    mkRuntimeErrorApp rUNTIME_ERROR_ID res_ty (GHC.Base.hs_string__
                                               "Impossible case alternative").

Axiom boolTy : unit.

Axiom falseDataCon : Core.DataCon.

Axiom trueDataCon : Core.DataCon.

Definition mkIfThenElse
   : Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun guard then_expr else_expr =>
    mkWildCase guard boolTy (CoreUtils.exprType then_expr) (cons (pair (pair
                                                                        (Core.DataAlt falseDataCon) nil) else_expr)
                                                                 (cons (pair (pair (Core.DataAlt trueDataCon) nil)
                                                                             then_expr) nil)).

Definition mkCoreVarTupTy : list Core.Id -> AxiomatizedTypes.Type_ :=
  fun ids => mkBoxedTupleTy (GHC.Base.map Id.idType ids).

Definition mkCoreLet : Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    let j_3__ :=
      match arg_0__, arg_1__ with
      | bind, body => Core.Let bind body
      end in
    match arg_0__, arg_1__ with
    | Core.NonRec bndr rhs, body =>
        if andb (CoreUtils.needsCaseBinding (Id.idType bndr) rhs) (negb (Id.isJoinId
                                                                         bndr)) : bool
        then Core.Case rhs bndr (CoreUtils.exprType body) (cons (pair (pair Core.DEFAULT
                                                                            nil) body) nil) else
        j_3__
    | _, _ => j_3__
    end.

Definition mkCoreLets : list Core.CoreBind -> Core.CoreExpr -> Core.CoreExpr :=
  fun binds body => Data.Foldable.foldr mkCoreLet body binds.

Definition mkCoreLams : list Core.CoreBndr -> Core.CoreExpr -> Core.CoreExpr :=
  Core.mkLams.

Definition mkCoreAppTyped
   : GHC.Base.String ->
     (Core.CoreExpr * AxiomatizedTypes.Type_)%type ->
     Core.CoreExpr -> (Core.CoreExpr * AxiomatizedTypes.Type_)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, pair fun_ fun_ty, Core.Type_ ty =>
        pair (Core.App fun_ (Core.Type_ ty)) (Type.piResultTy fun_ty ty)
    | _, pair fun_ fun_ty, Core.Coercion co =>
        let 'pair _ res_ty := Type.splitFunTy fun_ty in
        pair (Core.App fun_ (Core.Coercion co)) res_ty
    | d, pair fun_ fun_ty, arg =>
        let 'pair arg_ty res_ty := Type.splitFunTy fun_ty in
        if andb Util.debugIsOn (negb (Type.isFunTy fun_ty)) : bool
        then (GHC.Err.error Panic.someSDoc)
        else pair (mk_val_app fun_ arg arg_ty res_ty) res_ty
    end.

Definition mkCoreApps : Core.CoreExpr -> list Core.CoreExpr -> Core.CoreExpr :=
  fun fun_ args =>
    let fun_ty := CoreUtils.exprType fun_ in
    let doc_string := Panic.someSDoc in
    Data.Tuple.fst (Data.Foldable.foldl' (mkCoreAppTyped doc_string) (pair fun_
                                                                           fun_ty) args).

Definition mkCoreConApps
   : Core.DataCon -> list Core.CoreExpr -> Core.CoreExpr :=
  fun con args => mkCoreApps (Core.Mk_Var (Core.dataConWorkId con)) args.

Definition mkCoreTup : list Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Core.Mk_Var unitDataConId
    | cons c nil => c
    | cs =>
        mkCoreConApps (tupleDataCon BasicTypes.Boxed (Coq.Lists.List.length cs))
        (Coq.Init.Datatypes.app (GHC.Base.map (Core.Type_ GHC.Base.∘ CoreUtils.exprType)
                                 cs) cs)
    end.

Definition mkCoreVarTup : list Core.Id -> Core.CoreExpr :=
  fun ids => mkCoreTup (GHC.Base.map Core.Mk_Var ids).

Definition mkCoreUbxTup
   : list AxiomatizedTypes.Type_ -> list Core.CoreExpr -> Core.CoreExpr :=
  fun tys exps =>
    if andb Util.debugIsOn (negb (Util.equalLength tys exps)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/MkCore.hs")
          #372)
    else mkCoreConApps (tupleDataCon BasicTypes.Unboxed (Coq.Lists.List.length tys))
         (Coq.Init.Datatypes.app (GHC.Base.map (Core.Type_ GHC.Base.∘ Type.getRuntimeRep)
                                  tys) (Coq.Init.Datatypes.app (GHC.Base.map Core.Type_ tys) exps)).

Definition mkCoreTupBoxity
   : BasicTypes.Boxity -> list Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BasicTypes.Boxed, exps => mkCoreTup exps
    | BasicTypes.Unboxed, exps =>
        mkCoreUbxTup (GHC.Base.map CoreUtils.exprType exps) exps
    end.

Axiom nilDataCon : Core.DataCon.

Definition mkNilExpr : AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun ty => mkCoreConApps nilDataCon (cons (Core.Type_ ty) nil).

Axiom charTy : unit.

Definition mkStringExprFSWith {m} `{GHC.Base.Monad m}
   : (Name.Name -> m Core.Id) -> FastString.FastString -> m Core.CoreExpr :=
  fun lookupM str =>
    let lit := Core.Lit (Literal.MachStr (FastString.fastStringToByteString str)) in
    let safeChar :=
      fun c =>
        andb (GHC.Base.ord c GHC.Base.>= #1) (GHC.Base.ord c GHC.Base.<= #127) in
    let chars := FastString.unpackFS str in
    if FastString.nullFS str : bool then GHC.Base.return_ (mkNilExpr charTy) else
    if Data.Foldable.all safeChar chars : bool
    then lookupM PrelNames.unpackCStringName GHC.Base.>>=
         (fun unpack_id => GHC.Base.return_ (Core.App (Core.Mk_Var unpack_id) lit)) else
    lookupM PrelNames.unpackCStringUtf8Name GHC.Base.>>=
    (fun unpack_utf8_id =>
       GHC.Base.return_ (Core.App (Core.Mk_Var unpack_utf8_id) lit)).

Definition mkCoreApp
   : GHC.Base.String -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun s fun_ arg =>
    Data.Tuple.fst (mkCoreAppTyped s (pair fun_ (CoreUtils.exprType fun_)) arg).

Axiom consDataCon : Core.DataCon.

Definition mkConsExpr
   : AxiomatizedTypes.Type_ -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr :=
  fun ty hd tl =>
    mkCoreConApps consDataCon (cons (Core.Type_ ty) (cons hd (cons tl nil))).

Definition mkListExpr
   : AxiomatizedTypes.Type_ -> list Core.CoreExpr -> Core.CoreExpr :=
  fun ty xs => Data.Foldable.foldr (mkConsExpr ty) (mkNilExpr ty) xs.

Axiom charDataCon : Core.DataCon.

Definition mkCharExpr : GHC.Char.Char -> Core.CoreExpr :=
  fun c => mkCoreConApps charDataCon (cons (Core.mkCharLit c) nil).

Axiom mkBigCoreVarTupTy : list Core.Id -> AxiomatizedTypes.Type_.

Axiom mkBigCoreTupTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkBigCoreTup : list Core.CoreExpr -> Core.CoreExpr.

Definition mkBigCoreVarTup : list Core.Id -> Core.CoreExpr :=
  fun ids => mkBigCoreTup (GHC.Base.map Core.Mk_Var ids).

Definition mkBigCoreVarTup1 : list Core.Id -> Core.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | cons id nil =>
        mkCoreConApps (tupleDataCon BasicTypes.Boxed #1) (cons (Core.Type_ (Id.idType
                                                                            id)) (cons (Core.Mk_Var id) nil))
    | ids => mkBigCoreTup (GHC.Base.map Core.Mk_Var ids)
    end.

Axiom iRREFUT_PAT_ERROR_ID : Core.Id.

Axiom err_nm : GHC.Base.String -> Unique.Unique -> Core.Id -> Name.Name.

Definition irrefutPatErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "irrefutPatError") PrelNames.irrefutPatErrorIdKey
  iRREFUT_PAT_ERROR_ID.

Definition noMethodBindingErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "noMethodBindingError")
  PrelNames.noMethodBindingErrorIdKey nO_METHOD_BINDING_ERROR_ID.

Definition nonExhaustiveGuardsErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "nonExhaustiveGuardsError")
  PrelNames.nonExhaustiveGuardsErrorIdKey nON_EXHAUSTIVE_GUARDS_ERROR_ID.

Definition patErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "patError") PrelNames.patErrorIdKey pAT_ERROR_ID.

Definition recConErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "recConError") PrelNames.recConErrorIdKey
  rEC_CON_ERROR_ID.

Definition recSelErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "recSelError") PrelNames.recSelErrorIdKey
  rEC_SEL_ERROR_ID.

Definition runtimeErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "runtimeError") PrelNames.runtimeErrorIdKey
  rUNTIME_ERROR_ID.

Definition typeErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "typeError") PrelNames.typeErrorIdKey
  tYPE_ERROR_ID.

Definition castBottomExpr
   : Core.CoreExpr -> AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun e res_ty =>
    let e_ty := CoreUtils.exprType e in
    if Type.eqType e_ty res_ty : bool then e else
    Core.Case e (mkWildValBinder e_ty) res_ty nil.

Axiom aBSENT_SUM_FIELD_ERROR_ID : Core.Id.

Definition absentSumFieldErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "absentSumFieldError")
  PrelNames.absentSumFieldErrorIdKey aBSENT_SUM_FIELD_ERROR_ID.

Axiom aBSENT_ERROR_ID : Core.Id.

Definition absentErrorName : Name.Name :=
  err_nm (GHC.Base.hs_string__ "absentError") PrelNames.absentErrorIdKey
  aBSENT_ERROR_ID.

Definition errorIds : list Core.Id :=
  cons rUNTIME_ERROR_ID (cons iRREFUT_PAT_ERROR_ID (cons
                               nON_EXHAUSTIVE_GUARDS_ERROR_ID (cons nO_METHOD_BINDING_ERROR_ID (cons
                                                                     pAT_ERROR_ID (cons rEC_CON_ERROR_ID (cons
                                                                                         rEC_SEL_ERROR_ID (cons
                                                                                          aBSENT_ERROR_ID (cons
                                                                                           tYPE_ERROR_ID nil)))))))).

Definition mkAbsentErrorApp
   : AxiomatizedTypes.Type_ -> GHC.Base.String -> Core.CoreExpr :=
  fun res_ty err_msg =>
    let err_string := Core.Lit (Literal.mkMachString err_msg) in
    Core.mkApps (Core.Mk_Var aBSENT_ERROR_ID) (cons (Core.Type_ res_ty) (cons
                                                     err_string nil)).

(* Skipping all instances of class `Outputable.Outputable', including
   `MkCore.Outputable__FloatBind' *)

Axiom wordDataCon : Core.DataCon.

Axiom floatDataCon : Core.DataCon.

Axiom intDataCon : Core.DataCon.

Axiom doubleDataCon : Core.DataCon.

(* External variables:
     andb bool cons list nat negb nil op_zt__ pair unit AxiomatizedTypes.PredType
     AxiomatizedTypes.Type_ BasicTypes.Boxed BasicTypes.Boxity BasicTypes.Unboxed
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Coq.Lists.List.length Core.AltCon
     Core.App Core.Case Core.Coercion Core.CoreAlt Core.CoreBind Core.CoreBndr
     Core.CoreExpr Core.DEFAULT Core.DataAlt Core.DataCon Core.EvVar Core.Id Core.Let
     Core.Lit Core.Mk_Var Core.NonRec Core.Type_ Core.Var Core.dataConWorkId
     Core.mkApps Core.mkCharLit Core.mkConApp Core.mkLams CoreUtils.bindNonRec
     CoreUtils.exprType CoreUtils.needsCaseBinding Data.Foldable.all
     Data.Foldable.elem Data.Foldable.foldl' Data.Foldable.foldr Data.Tuple.fst
     DynFlags.DynFlags FastString.FastString FastString.fastStringToByteString
     FastString.fsLit FastString.nullFS FastString.unpackFS GHC.Base.Monad
     GHC.Base.String GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zlze__ GHC.Base.ord
     GHC.Base.return_ GHC.Char.Char GHC.DeferredFix.deferredFix2
     GHC.DeferredFix.deferredFix3 GHC.Err.error GHC.Err.patternFailure
     GHC.Num.Integer GHC.Num.Word GHC.Num.fromInteger Id.idType Id.isJoinId
     Id.mkLocalIdOrCoVar Id.mkSysLocal Id.mkTemplateLocals Literal.MachStr
     Literal.mkMachString Name.Name Panic.assertPanic Panic.someSDoc
     PrelNames.absentErrorIdKey PrelNames.absentSumFieldErrorIdKey
     PrelNames.irrefutPatErrorIdKey PrelNames.noMethodBindingErrorIdKey
     PrelNames.nonExhaustiveGuardsErrorIdKey PrelNames.patErrorIdKey
     PrelNames.recConErrorIdKey PrelNames.recSelErrorIdKey
     PrelNames.runtimeErrorIdKey PrelNames.typeErrorIdKey PrelNames.unpackCStringName
     PrelNames.unpackCStringUtf8Name PrelNames.wildCardName Type.eqType
     Type.getRuntimeRep Type.isFunTy Type.piResultTy Type.splitFunTy
     UniqSupply.UniqSupply UniqSupply.takeUniqFromSupply Unique.Unique Util.debugIsOn
     Util.equalLength Util.notNull Util.zipEqual
*)
