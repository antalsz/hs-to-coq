Require Import GHC.Base.

Require Import ITree.ITree.
From ExtLib.Structures Require Functor Applicative Monad.

Require Import Monads.

Axiom numCapabilities : Int.
Axiom FileStatus : Type.

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

(** Originally [Word32]: defined as [HTYPE_MODE_T] at
   [https://hackage.haskell.org/package/base-4.1.0.0/src/include/HsBaseConfig.h]
   *)
Definition CMode : Type := Word.

(** Originally [Int32]: defined as [HTYPE_INT] at
   [https://hackage.haskell.org/package/base-4.1.0.0/src/include/HsBaseConfig.h]
   *)
Definition CInt : Type := Int.

(** Originally [Word32]: defined as [HTYPE_SIZE_T] at
   [https://hackage.haskell.org/package/base-4.1.0.0/src/include/HsBaseConfig.h]
   *)
Definition CSize : Type := Word.

(** Originally [Int64]: defined as [HTYPE_OFF_T] at
   [https://hackage.haskell.org/package/base-4.1.0.0/src/include/HsBaseConfig.h]
   *)
Definition COff : Type := Int.

(** [System.Posix.Types] from [base] *)
Definition FileMode : Type := CMode.
Definition Fd : Type := CInt.
Definition ByteCount : Type := CSize.
Definition FileOffset : Type := COff.

Inductive IOE : Type -> Type :=
| OpenFd : FilePath -> IOMode -> option FileMode -> IOE Fd
| CloseFd : Fd -> IOE unit
| FdRead : Fd -> ByteCount -> IOE (String * ByteCount)
| FdPRead : Fd -> ByteCount -> FileOffset -> IOE (String * ByteCount)
| GetFdStatus : Fd -> IOE FileStatus
(** In real Haskell implementation, [concurrently] is implemented using [forkIO]
    and [MVar]. I put [Concurrently] here as an effect simply for convenience
    and it should be changed to use the actual underlying operations when there
    is time. *)
| Concurrently {a b}: itree IOE a -> itree IOE b -> IOE (a * b).

Definition IO := itree IOE.

Definition openFd : FilePath -> IOMode -> option FileMode -> IO Fd := embed OpenFd.
  
Definition closeFd : Fd -> IO unit := embed CloseFd.

Definition fdRead : Fd -> ByteCount -> IO (String * ByteCount) := embed FdRead.

(** [fdPRead] is defined in [BL.v]. *)

(** [concurrently] is defined in [Async.v]. *)

Definition getFdStatus : Fd -> IO FileStatus := embed GetFdStatus.

Instance Functor_IO : Functor IO := Functor_Functor IO.

Instance Applicative_IO : Applicative IO := Applicative_Applicative IO.

Instance Monad_IO : Monad IO := Monad_Monad IO.

(** This is not a REAL implementation! *)
Definition getFileStatus (f : FilePath) : IO FileStatus :=
  openFd f ReadMode None >>=
         (fun fd => getFdStatus fd >>=
                             (fun st => closeFd fd >> return_ st)).

Axiom fileSize : FileStatus -> FileOffset.

(** This is not a REAL implementation! *)
Definition readFile (f : FilePath) : IO String :=
  openFd f ReadMode None >>=
         (fun fd => getFdStatus fd >>=
                             (fun st => fdRead fd (Z.to_N (fileSize st)) >>=
                                            (fun '(s, _) => closeFd fd >> return_ s))).


Axiom openBinaryFile : FilePath -> IOMode -> IO Handle.

Axiom hSeek : Handle -> SeekMode -> Integer -> IO unit.

Axiom putStrLn : String -> IO unit.

Axiom show : Int -> String.

