Instance instance_Down_Eq {a} `(Eq_ a) : Eq_ (Down a) := fun _ k => k {|
  op_zeze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 == y0
                end);
  op_zsze____ := (fun x y =>
                match x, y with
                | Mk_Down x0, Mk_Down y0 => x0 /= y0
                end)
|}.
