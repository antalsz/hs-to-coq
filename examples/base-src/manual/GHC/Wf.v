(**
Utility definitions for well-founded recursion
*)

Require Import Coq.Program.Wf.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Init.Specif.

Definition wfFix1 {a n r}
  (R : n -> n -> Prop)
  (m : a -> n)
  (Hwf : well_founded R)
  (F : forall x : a, ({x' : a | R (m x') (m x)} -> r) -> r)
  : a -> r :=
       @Wf.Fix_sub a _ (wf_inverse_image _ _ R m Hwf) (fun _ => r)  F.

Definition wfFix2 {a b n r}
  (R : n -> n -> Prop)
  (m : a -> b -> n)
  (Hwf : well_founded R)
  (F : forall (x : a) (y : b), (forall (x' : a), {y' : b | R (m x' y') (m x y)} -> r) -> r)
  (x : a)
  (y : b)
  : r :=
      let m' (p : a * b) : n := m (fst p) (snd p) in
      let F' (p : a * b) (rec : {p' : a * b | R (m' p') (m' p)} -> r) : r
             := let x := fst p in let y := snd p in
                let rec' (x' : a) (yH' : {y' : b | R (m x' y') (m x y)})
                  := let y' := proj1_sig yH' in
                     let H  := proj2_sig yH' in
                     rec (exist _ (x',y') H)
                in F x y rec'
      in wfFix1 R m' Hwf F' (x, y).

Definition wfFix3 {a b c n r}
  (R : n -> n -> Prop)
  (m : a -> b -> c -> n)
  (Hwf : well_founded R)
  (F : forall (x : a) (y : b) (z : c), (forall (x' : a) (y' : b), {z' : c | R (m x' y' z') (m x y z)} -> r) -> r)
  (x : a)
  (y : b)
  (z : c)
  : r :=
      let m' (p : a * b * c) : n := m (fst (fst p)) (snd (fst p)) (snd p) in
      let F' (p : a * b * c) (rec : {p' : a * b * c | R (m' p') (m' p)} -> r) : r
             := let x := fst (fst p) in let y := snd (fst p) in let z := snd p in
                let rec' (x' : a) (y' : b) (zH' : {z' : c | R (m x' y' z') (m x y z)})
                  := let z' := proj1_sig zH' in
                     let H  := proj2_sig zH' in
                     rec (exist _ (x',y',z') H)
                in F x y z rec'
      in wfFix1 R m' Hwf F' (x, y, z).
