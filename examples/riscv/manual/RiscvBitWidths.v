Require Import Coq.omega.Omega.
Require Import bbv.NatLib.

Inductive RiscvBitWidth := Bitwidth32 | Bitwidth64.

Class RiscvBitWidths := mkRiscvBitWidths {
  bitwidth: RiscvBitWidth;

(* TODO add these back if needed:

  log2wXLEN: nat;
  log2wXLEN_spec: pow2 log2wXLEN = wXLEN;

  (* Bit width of an instruction, will be 32 *)
  wInstr: nat;

  (* bit width of most immediates, will equal 12 *)
  wimm: nat;

  (* bit width of "upper" bits to complete 12-bit immediates, will equal 20 *)
  wupper: nat;

  w_eq: wimm + wupper = wInstr;

  wimm_nonzero: wimm <> 0;

  (* need to encode signed immediates: need at least 1 bit for sign, 1 bit for value *)
  wimm_lbound: wimm >= 2;

  (* we express statement size bounds with wimm, but JAL uses wupper, which is more *)
  wimm_wupper: wimm <= wupper;

  wupper_nonzero: wupper <> 0;

  wXLEN_lbound: wXLEN >= wInstr;

  wXLEN_ge_32: wXLEN >= 32;
*)
}.

Section Widths.

  Context {B: RiscvBitWidths}.

  Definition wXLEN: nat :=
    match bitwidth with
    | Bitwidth32 => 32
    | Bitwidth64 => 64
    end.

End Widths.

(*
Ltac bitwidth_omega :=
  match goal with
  | B: RiscvBitWidths |- _ => abstract (destruct B; simpl in *; omega)
  end.
*)
