Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
Instance Default__CSEnv : GHC.Err.Default CSEnv := {| GHC.Err.default := CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap |}.
