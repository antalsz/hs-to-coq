Open Scope type_scope.

Definition pair_type   := (fun (x y :Type) => (x * y)).
Definition triple_type := (fun (x y z :Type) => (x * y * z)).
Definition quad_type   := (fun (x y z w:Type) => (x * y * z * w)).
Definition quint_type  := (fun (x y z w v:Type) => (x * y * z * w * v)).
Definition sext_type   := (fun (x y z w v u :Type) => (x * y * z * w * v * u)).
Definition sept_type   := (fun (x y z w v u t :Type) => (x * y * z * w * v * u * t)).


Definition op_Z2T__ := (fun {a} {b} (x:a) (y:b) => (x, y)).
Definition op_Z3T__ := (fun {a} {b} {c} (x:a) (y:b) (z:c) => (x, y, z)).
Definition op_Z4T__ := (fun {a} {b} {c} {d} (x:a) (y:b) (z:c) (w:d) => (x, y, z, w)).
Definition op_Z5T__ := (fun {a} {b} {c} {d} {e}
                          (x:a) (y:b) (z:c) (w:d) (v:e) => (x, y, z, w,v)).
Definition op_Z6T__ := (fun {a} {b} {c} {d} {e} {f}
                          (x:a) (y:b) (z:c) (w:d) (v:e) (u:f) => (x, y, z, w, v,u)).
Definition op_Z7T__ := (fun {a} {b} {c} {d} {e} {f} {g}
                          (x:a) (y:b) (z:c) (w:d) (v:e) (u:f) (t:g) =>
                          (x, y, z, w, v, u, t)).
