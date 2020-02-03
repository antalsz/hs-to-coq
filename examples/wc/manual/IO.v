Require Import GHC.Base.

Require Import ITree.ITree.
From ExtLib.Structures Require Functor Applicative Monad.

Axiom numCapabilities : Int.
Axiom FileStatus : Type.

Inductive IOE : Type -> Type :=
| ReadFile : FilePath -> IOE String.

Definition IO := itree IOE.

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

Instance Functor_IO : Functor IO :=
  fun _ X =>
    X {| fmap__ := fun a b : Type => Functor.fmap;
         op_zlzd____ := fun a b : Type => Functor.fmap ∘ const
      |}.

Instance Applicative_IO : Applicative IO :=
  fun _ X =>
    X {| liftA2__ := fun a b c f x y => Applicative.ap (fmap f x) y;
         op_zlztzg____ := fun a b => Applicative.ap ;
         op_ztzg____ := fun a b x y => Applicative.ap (id <$ x) y;
         pure__ := fun a => Applicative.pure
      |}.

Instance Monad_IO : Monad IO :=
  fun _ X =>
    X {| op_zgzg____ := fun a b x y => Monad.bind x (fun _ => y);
         op_zgzgze____ := fun a b => Monad.bind ;
         return___ := fun a => Monad.ret
      |}.

Definition readFile : FilePath -> IO String := embed ReadFile.
  
