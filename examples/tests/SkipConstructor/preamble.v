(* Replace Haskell strings *)
Require Coq.Strings.String.
Open Scope string_scope.
Definition String : Type := Coq.Strings.String.string.

Module GHC.
  Module Skip.
    (* From GHC.Skip in base, since we don't link against it *)

    (* For use when skipping a pattern guard because of `skip constructor` *)
    Definition impossible_skipped (_skipped : String) : bool := false.
    
    (* For use when skipping a list constructor binding because of `skip constructor` *)
    Definition nil_skipped {a} (_skipped : String) : list a := nil.
  End Skip.
End GHC.
