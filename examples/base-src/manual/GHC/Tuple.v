Open Scope type_scope.

Definition pair_type   := (fun (x y :Type) => (x * y)).
Definition triple_type := (fun (x y z :Type) => (x * y * z)).
Definition quad_type   := (fun (x y z w:Type) => (x * y * z * w)).
Definition quint_type  := (fun (x y z w v:Type) => (x * y * z * w * v)).
Definition sext_type   := (fun (x y z w v u :Type) => (x * y * z * w * v * u)).
Definition sept_type   := (fun (x y z w v u t :Type) => (x * y * z * w * v * u * t)).


Definition pair2 := (fun {a} {b} (x:a) (y:b) => (x, y)).
Definition pair3 := (fun {a} {b} {c} (x:a) (y:b) (z:c) => (x, y, z)).
Definition pair4 := (fun {a} {b} {c} {d} (x:a) (y:b) (z:c) (w:d) => (x, y, z, w)).
Definition pair5 := (fun {a} {b} {c} {d} {e}
                          (x:a) (y:b) (z:c) (w:d) (v:e) => (x, y, z, w,v)).
Definition pair6 := (fun {a} {b} {c} {d} {e} {f}
                          (x:a) (y:b) (z:c) (w:d) (v:e) (u:f) => (x, y, z, w, v,u)).
Definition pair7 := (fun {a} {b} {c} {d} {e} {f} {g}
                          (x:a) (y:b) (z:c) (w:d) (v:e) (u:f) (t:g) =>
                          (x, y, z, w, v, u, t)).

