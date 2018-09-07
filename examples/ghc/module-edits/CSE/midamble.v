Axiom cseExpr_rec   : CSEnv -> Core.InExpr -> Core.OutExpr.
Axiom cseBind_rec   : BasicTypes.TopLevelFlag -> CSEnv -> Core.CoreBind -> CSEnv * Core.CoreBind.
Axiom cse_bind_rec  : BasicTypes.TopLevelFlag -> CSEnv -> Core.InId * Core.InExpr -> Core.OutId -> CSEnv * (Core.OutId * Core.OutExpr).
Axiom tryForCSE_rec : CSEnv -> Core.InExpr -> Core.OutExpr.
Axiom cseCase_rec   : CSEnv -> Core.InExpr -> Core.InId -> Core.InType -> list Core.InAlt -> Core.OutExpr.

(* default = emptyCSEnv *)
Instance Default__CSEnv : GHC.Err.Default CSEnv := {| GHC.Err.default := CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap |}.
