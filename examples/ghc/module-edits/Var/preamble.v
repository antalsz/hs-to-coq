Require Import Core.
Require Import Panic.

Definition error {a:Type}`{Panic.Default a} := Panic.panic.
