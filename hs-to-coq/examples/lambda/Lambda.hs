module Lambda where

type Name = Int

data Expr
  = Var Name
  | Let Name Expr Expr
  | Lam Name Expr
  | App Expr Expr

maxVar :: Expr -> Int
maxVar (Var n) = n
maxVar (Let n e1 e2) = maximum [n, maxVar e1, maxVar e2]
maxVar (Lam n e) = maximum [n, maxVar e]
maxVar (App e1 e2) = maximum [maxVar e1, maxVar e2]

fresh :: Expr -> Int
fresh e = 1 + maxVar e

anf :: Expr -> Expr
anf (Var n) = Var n
anf (Let n rhs body) = Let n (anf rhs) (anf body)
anf (Lam n body) = Lam n (anf body)
anf (App f (Var n)) = App (anf f) (Var n)
anf (App f e) = Let v (anf e) (App (anf f) (Var v))
  where v = fresh f

