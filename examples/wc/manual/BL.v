Require GHC.Char.
Require Import GHC.Base.

From ITree.Core Require Import ITreeDefinition Subevent.

Require Import IO.

Axiom ByteString : Type.

Axiom pack : String -> ByteString.

Axiom length : ByteString -> Int.

Axiom foldr  : forall {a}, (Char -> a -> a) -> a -> ByteString -> a.
Axiom foldl' : forall {a}, (a -> Char -> a) -> a -> ByteString -> a.

Axiom take : Int -> ByteString -> ByteString.

Axiom hGetContents : Handle -> IO ByteString.
Axiom readFile : FilePath -> IO ByteString.

Definition fdPRead (fd : Fd) (bc : ByteCount) (off : FileOffset) : IO ByteString :=
  Vis (FdPRead fd bc off) (fun '(s, _) => Ret (pack s)).

Axiom c2w : GHC.Char.Char -> N.
Axiom isSpaceChar8 : GHC.Char.Char -> bool.

Axiom ByteString_foldl_nil  : forall {B} (f: B -> Char -> B) (b:B) , foldl' f b (pack nil) = b.
Axiom ByteString_foldl_cons : forall {B} (f: B -> Char -> B) (b:B) x xs,
    foldl' f b (pack (cons x xs)) = 
      foldl' f (f b x) (pack xs).

Axiom ByteString_foldr_nil  : forall {B} (f: Char -> B -> B) (b:B) , foldr f b (pack nil) = b.
Axiom ByteString_foldr_cons : forall {B} (f: Char -> B -> B) (b:B) x xs,
    foldr f b (pack (cons x xs)) = f x (foldr f b (pack xs)).

Axiom foldl_foldr:
  forall {b} (f : b -> Char -> b) (x : b) xs,
    foldl' f x (pack xs) = foldr (fun x g a => g (f a x)) id (pack xs) x.
