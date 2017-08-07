Require Import GHC.Prim.
Require Import GHC.Char.
Require Import GHC.Enum.
Require Import GHC.Real.

(* These are all C functions in GHC *)
Parameter  iswalpha : Int -> Int.
Parameter  iswalnum : Int -> Int.
Parameter  iswcntrl : Int -> Int.
Parameter  iswspace : Int -> Int.
Parameter  iswprint : Int -> Int.
Parameter  iswlower : Int -> Int.
Parameter  iswupper : Int -> Int.
Parameter  towlower : Int -> Int.
Parameter  towupper : Int -> Int.
Parameter  towtitle : Int -> Int.
Parameter  wgencat : Int -> Int.
