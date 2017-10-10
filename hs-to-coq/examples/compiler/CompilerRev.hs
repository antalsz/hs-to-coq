{- |
Description : Compiler Correctness from Graham Hutton’s
              Programming in Haskell first edition,
              Section 13.7.

 Revised & more efficient compiler, called comp'
-}

module CompilerRev where

data Expr = Val Int | Add Expr Expr

eval :: Expr -> Int
eval (Val n)   = n
eval (Add x y) = eval x + eval y

type Stack = [Int]

type Code = [Op]

data Op = PUSH Int | ADD
          deriving Show

exec :: Code -> Stack -> Maybe Stack
exec [] s = Just s
exec (PUSH n : c) s = exec c (n : s)
exec (ADD : c) (m : n : s) =  exec c (n+m : s)
exec _ _ = Nothing




comp' :: Expr -> Code -> Code
comp' (Val n)   c = PUSH n:c
comp' (Add x y) c = comp' x (comp' y (ADD:c))
