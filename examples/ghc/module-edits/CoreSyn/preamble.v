Require Import Core.
Definition error {a} `{Panic.Default a} := Panic.panic.
