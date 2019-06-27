Require Import GHC.Base.

(* For use when skipping a pattern guard because of `skip constructor` *)
Definition impossible_skipped (_skipped : String) : bool := false.

(* For use when skipping a list constructor binding because of `skip constructor` *)
Definition nil_skipped {a} (_skipped : String) : list a := nil.
