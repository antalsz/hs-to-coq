Require Import GHC.Base.

(* For use when skipping a list comprehension binding because of `skip constructor` *)
Definition nil_skipped {a} (_skipped : String) : list a := nil.
