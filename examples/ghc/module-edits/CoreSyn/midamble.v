Parameter tickishCounts : forall {id}, Tickish id -> bool.
Parameter tickishIsCode : forall {id}, Tickish id -> bool.




Fixpoint deAnnotate' {bndr} {annot} (arg_0__ : AnnExpr' bndr annot) : Expr bndr :=
  let deAnnotate {bndr} {annot} : AnnExpr bndr annot -> Expr bndr :=
       fun arg_0__ =>  match arg_0__ with | pair _ e => deAnnotate' e end in
  let deAnnAlt {bndr} {annot} : AnnAlt bndr annot -> Alt bndr :=
      fun arg_0__ =>
        match arg_0__ with
        | pair (pair con args) rhs => pair (pair con args) (deAnnotate rhs)
        end in
    match arg_0__ with
      | AnnType t => Type_ t
      | AnnCoercion co => Coercion co
      | AnnVar v => Var v
      | AnnLit lit => Lit lit
      | AnnLam binder body => Lam binder (deAnnotate body)
      | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
      | AnnCast e (pair _ co) => Cast (deAnnotate e) co
      | AnnTick tick body => Tick tick (deAnnotate body)
      | AnnLet bind body =>
        let deAnnBind :=
            fun arg_9__ =>
              match arg_9__ with
              | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
              | AnnRec pairs => Rec (let cont_11__ arg_12__ :=
                                        match arg_12__ with
                                        | pair v rhs => cons (pair v (deAnnotate rhs)) nil
                                        end in
                                    Coq.Lists.List.flat_map cont_11__ pairs)
              end in
        Let (deAnnBind bind) (deAnnotate body)
      | AnnCase scrut v t alts => Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt
                                                                           alts)
    end.


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

(* One way to resolve the fixpoint *)

Fixpoint collectAnnArgs_go {b}{a}(expr : AnnExpr' b a) g as_ :=
  match expr with
    | AnnApp f a => collectAnnArgs_go (snd f) (fst f) (cons a as_)
    | e          => ((g,e), as_)
  end.

Definition collectAnnArgs {b}{a} :
  AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a))%type :=
  fun expr => collectAnnArgs_go (snd expr) (fst expr) nil.


Fixpoint deTagExpr {t} (arg_0__ : TaggedExpr t) : CoreExpr :=
  let deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun arg_0__ =>
    match arg_0__ with
      | pair (pair con bndrs) rhs =>
        pair (pair con (let cont_1__ arg_2__ :=
                            match arg_2__ with
                            | TB b _ => cons b nil
                            end in
                        Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs)
    end in
  let deTagBind {t} : TaggedBind t -> CoreBind :=
      fun arg_0__ =>
        match arg_0__ with
        | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
        | Rec prs => Rec (let cont_2__ arg_3__ :=
                             match arg_3__ with
                             | pair (TB b _) rhs => cons (pair b (deTagExpr rhs)) nil
                             end in
                         Coq.Lists.List.flat_map cont_2__ prs)
        end
  in match arg_0__ with
     | Var v => Var v
     | Lit l => Lit l
     | Type_ ty => Type_ ty
     | Coercion co => Coercion co
     | App e1 e2 => App (deTagExpr e1) (deTagExpr e2)
     | Lam (TB b _) e => Lam b (deTagExpr e)
     | Let bind body => Let (deTagBind bind) (deTagExpr body)
     | Case e (TB b _) ty alts => Case (deTagExpr e) b ty (GHC.Base.map deTagAlt
                                                                       alts)
     | Tick t e => Tick t (deTagExpr e)
     | Cast e co => Cast (deTagExpr e) co
     end.

Definition exprToType : CoreExpr -> Core.Type_ :=
  fun arg_0__ =>
    match arg_0__ with
      | Type_ ty => ty
      | _bad => GHC.Err.error (GHC.Base.hs_string__ "exprToType")
    end.

Definition applyTypeToArg : Core.Type_ -> (CoreExpr -> Core.Type_) :=
  fun fun_ty arg => TyCoRep.piResultTy fun_ty (exprToType arg).

Instance Default__Expr {b} : GHC.Err.Default (Expr b).
Admitted.
