(*
Fixpoint deAnnotate' {bndr} {annot} (ae : AnnExpr' bndr annot)
         {struct ae} : Expr bndr :=
    match ae with
      | AnnType t => Type_ t
      | AnnCoercion co => Coercion co
      | AnnVar v => Var v
      | AnnLit lit => Lit lit
      | AnnLam binder body => Lam binder (deAnnotate body)
      | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
      | AnnCast e (pair _ co) => Cast (deAnnotate e) co
      | AnnTick tick body => Tick tick (deAnnotate body)
      | AnnLet bind body =>
        Let (deAnnBind bind) (deAnnotate body)
      | AnnCase scrut v t alts =>
        Case (deAnnotate scrut) v t
             (List.map deAnnAlt alts)
    end
with deAnnotate {bndr} {annot} (ae : AnnExpr bndr annot) {struct ae} : Expr bndr :=
   match ae with | pair _ e => deAnnotate' e end
with deAnnAlt {bndr} {annot} (ae : AnnAlt bndr annot) {struct ae}: Alt bndr :=
   match ae with
      | pair (pair con args) rhs => pair (pair con args) (deAnnotate rhs)
    end
with deAnnBind {bndr} {annot} (ae : AnnBind bndr annot) {struct ae} : Bind bndr :=
       match ae with
       | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
       | AnnRec pairs => Rec (Coq.Lists.List.flat_map
                               ( fun arg_53__ =>
                                   match arg_53__ with
                                   | pair v rhs => cons (pair v (deAnnotate rhs)) nil
                                   end )
                               pairs)
       end.
*)