(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.

(* Converted imports: *)

Require BL.
Require Import Control.Monad.
Require Import Data.Foldable.
Require Import Data.Functor.
Require Import Data.Traversable.
Require Import GHC.Base.
Require Import GHC.Enum.
Require Import GHC.Num.
Require Import GHC.Real.
Require Import IO.
Require Import Types.

(* No type declarations to convert. *)

(* Midamble *)

Axiom show : Int -> String.

(* Converted value declarations: *)

Axiom forConcurrently : forall {t} {a} {b},
                        forall `{Traversable t}, t a -> (a -> IO b) -> IO (t b).

Definition countBytes : BL.ByteString -> Counts :=
  BL.foldl' (fun a b => a <<>> countChar b) mempty.

Definition multiCoreCount : String -> IO Counts :=
  fun fp =>
    putStrLn (GHC.Base.hs_string__ "Using available cores: " <<>>
              show numCapabilities) >>
    (((fromIntegral ∘ fileSize) <$> getFileStatus fp) >>=
     (fun size =>
        let chunkSize := fromIntegral (div size numCapabilities) in
        fold <$!>
        (forConcurrently (enumFromTo (fromInteger 0) (numCapabilities - fromInteger 1))
         (fun n =>
            let limiter :=
              if n == numCapabilities - fromInteger 1 : bool
              then id
              else BL.take (fromIntegral chunkSize) in
            let offset := fromIntegral (n * chunkSize) in
            openBinaryFile fp ReadMode >>=
            (fun fileHandle =>
               hSeek fileHandle AbsoluteSeek offset >>
               ((countBytes ∘ limiter) <$!> BL.hGetContents fileHandle)))))).

(* External variables:
     AbsoluteSeek Counts IO ReadMode String Traversable bool countChar div enumFromTo
     fileSize fold fromInteger fromIntegral getFileStatus hSeek id mempty
     numCapabilities op_z2218U__ op_zeze__ op_zgzg__ op_zgzgze__ op_zlzdzg__
     op_zlzdznzg__ op_zlzlzgzg__ op_zm__ op_zt__ openBinaryFile putStrLn show
     BL.ByteString BL.foldl' BL.hGetContents BL.take
*)
