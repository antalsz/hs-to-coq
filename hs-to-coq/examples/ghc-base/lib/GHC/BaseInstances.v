Require Import GHC.Base.

(** This file contains instances that should be in GHC.Base, but cannot
    be translated *)

Instance instance_Monoid_list_a {a} : Monoid (list a) :=
  { mempty  := nil;
    mappend := (_++_);
    mconcat := fun xss => flat_map (fun xs => flat_map (fun x => x :: nil) xs) xss
  }.

Instance instance_Monoid_arrow {a}{b} `{Monoid b} : Monoid (a -> b) :=
  {
    mempty  := fun _ => (mempty : b);
    mappend := fun f g x => mappend (f x) (g x);
    mconcat := foldr (fun f g x => mappend (f x) (g x)) (fun _ => mempty)
  }.
(*
{-
-- cannot handle (,) in the instance head
instance Functor ((,) a) where
    fmap f (x,y) = (x, f y)
-}

{-
instance Monoid a => Applicative ((,) a) where
    pure x = (mempty, x)
    (u, f) <*> (v, x) = (u `mappend` v, f x)
instance Monoid a => Monad ((,) a) where
    (u, a) >>= k = case k a of (v, b) -> (u `mappend` v, b)
-}

{-

-- cannot handle (->) in the instance head
instance Functor ((->) r) where
    fmap = (.)

instance Applicative ((->) a) where
    pure = const
    (<*>) f g x = f x (g x)

instance Monad ((->) r) where
    f >>= k = \ r -> k (f r) r
-}
*)