(* Fix the type parameter of Const *)
Implicit Type b : Type.

(* A hack to make a few kind-polymorpic definitions go through *)
Local Class unit_class.
Local Instance unit_class_instance : unit_class.
Implicit Type inst_k: unit_class.
