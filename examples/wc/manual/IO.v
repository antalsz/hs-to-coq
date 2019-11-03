Require Import GHC.Base.

Axiom numCapabilities : Int.
Axiom FileStatus : Type.

Definition FileOffset := Int.

Axiom getFileStatus : FilePath -> IO FileStatus.
Axiom fileSize : FileStatus -> FileOffset.


Axiom Handle : Type.

Inductive SeekMode : Type := 
  | AbsoluteSeek : SeekMode 
  | RelativeSeek : SeekMode 
  | SeekFromEnd  : SeekMode.

Inductive IOMode : Type :=
  | ReadMode      : IOMode
  | WriteMode     : IOMode
  | AppendMode    : IOMode
  | ReadWriteMode : IOMode.

Axiom openBinaryFile : FilePath -> IOMode -> IO Handle.

Axiom hSeek : Handle -> SeekMode -> Integer -> IO unit.

Axiom putStrLn : String -> IO unit.

Axiom show : Int -> String.

Instance Functor_IO : Functor IO. Admitted.
Instance Applicative_IO : Applicative IO. Admitted.
Instance Monad_IO : Monad IO. Admitted.
