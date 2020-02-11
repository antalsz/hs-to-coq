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
Require Control.Concurrent.Async.
Require Import Control.Monad.
Require Import Data.Foldable.
Require Import Data.Functor.
Require Import Data.Traversable.
Require Import GHC.Base.
Require Import GHC.Enum.
Require Import GHC.Num.
Require Import GHC.Real.
Require IO.
Require Types.

(* No type declarations to convert. *)

(* Midamble *)

Axiom show : Int -> String.

(* Converted value declarations: *)

Definition countBytes : BL.ByteString -> Types.Counts :=
  BL.foldl' (fun acc next => acc <<>> Types.countChar next) mempty.

Definition filesplit
   : list String -> IO.IO (list (String * Types.Counts)%type) :=
  fun paths =>
    for_ paths (fun fp =>
                  IO.openFd fp IO.ReadOnly None IO.defaultFileFlags >>=
                  (fun fd =>
                     ((fromIntegral ∘ IO.fileSize) <$> IO.getFileStatus fp) >>=
                     (fun size =>
                        IO.putStrLn (GHC.Base.hs_string__ "Using available cores: " <<>>
                                     show IO.numCapabilities) >>
                        (let chunkSize := div size IO.numCapabilities in
                         (fold <$!>
                          (Control.Concurrent.Async.forConcurrently (enumFromTo (fromInteger 0)
                                                                                (IO.numCapabilities - fromInteger 1))
                           (fun n =>
                              let readAmount :=
                                fromIntegral (if n == (IO.numCapabilities - fromInteger 1) : bool
                                              then size - (n * chunkSize)
                                              else chunkSize) in
                              let offset := fromIntegral (n * chunkSize) in
                              countBytes <$!> BL.fdPRead fd readAmount offset))) >>=
                         (fun result => IO.closeFd fd $> pair fp result))))).

(* External variables:
     None String bool div enumFromTo fold for_ fromInteger fromIntegral list mempty
     op_z2218U__ op_zdzg__ op_zeze__ op_zgzg__ op_zgzgze__ op_zlzdzg__ op_zlzdznzg__
     op_zlzlzgzg__ op_zm__ op_zt__ pair show BL.ByteString BL.fdPRead BL.foldl'
     Control.Concurrent.Async.forConcurrently IO.IO IO.ReadOnly IO.closeFd
     IO.defaultFileFlags IO.fileSize IO.getFileStatus IO.numCapabilities IO.openFd
     IO.putStrLn Types.Counts Types.countChar
*)
