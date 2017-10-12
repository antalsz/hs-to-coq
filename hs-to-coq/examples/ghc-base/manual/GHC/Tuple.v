Open Scope type_scope.

Definition pair_type   := (fun (x y :Type) => (x * y)).

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
