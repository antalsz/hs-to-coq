{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, TypeSynonymInstances,
             OverloadedStrings #-}

module HsToCoq.Coq.FreeVars (
  -- * Named things
  Named(..),
  -- * Binders
  Binding(..),
  -- * Things that contain free variables
  getFreeVars, FreeVars(..),
  -- * Default type class method definitions
  bindingTelescope, foldableFreeVars
  ) where

import Prelude hiding (Num)

import Data.Semigroup ((<>))
import Data.Foldable
import Control.Monad.FreeVars.Class
import qualified Control.Monad.Trans.FreeVars as FV

import Data.List.NonEmpty (NonEmpty(), (<|))
import Data.Set (Set)

import HsToCoq.Coq.Gallina

----------------------------------------------------------------------------------------------------

class Named t where
  name :: t -> Ident

instance Named Ident where
  name = id

instance Named FixBody where
  name (FixBody f _ _ _ _) = f

instance Named CofixBody where
  name (CofixBody f _ _ _) = f

----------------------------------------------------------------------------------------------------

class Binding b where
  binding :: MonadFreeVars Ident m => b -> m a -> m a

instance Binding Ident where
  binding = bind

instance Binding Name where
  binding (Ident x)      = binding x
  binding UnderscoreName = id

instance Binding Binder where
  binding (Inferred x) getFVs =
    binding x getFVs
  binding (Typed xs ty) getFVs = do
    freeVars ty
    foldr binding getFVs xs
  binding (BindLet x oty val) getFVs = do
    freeVars oty
    freeVars val
    binding x getFVs

instance Binding Annotation where
  binding (Annotation x) = binding x

bindingTelescope :: (MonadFreeVars Ident m, Binding b, Foldable f) => f b -> m a -> m a
bindingTelescope = flip $ foldr binding

instance Binding b => Binding (Maybe b) where
  binding = bindingTelescope

instance Binding b => Binding [b] where
  binding = bindingTelescope

instance Binding b => Binding (NonEmpty b) where
  binding = bindingTelescope

----------------------------------------------------------------------------------------------------

getFreeVars :: FreeVars t => t -> Set Ident
getFreeVars = FV.execFreeVars . freeVars

class FreeVars t where
  freeVars :: MonadFreeVars Ident m => t -> m ()

instance FreeVars Num where
  freeVars _ = pure ()

instance FreeVars Term where
  freeVars (Forall xs t) =
    binding xs $ freeVars t
  
  freeVars (Fun xs t) =
    binding xs $ freeVars t
  
  freeVars (Fix fbs) =
    freeVars fbs
  
  freeVars (Cofix cbs) =
    freeVars cbs

  freeVars (Let x args oty val body) = do
    binding args $ freeVars oty *> freeVars val
    binding x    $ freeVars body
  
  freeVars (LetFix fb body) = do
    freeVars fb
    binding (name fb) $ freeVars body

  freeVars (LetCofix cb body) = do
    freeVars cb
    binding (name cb) $ freeVars body

  freeVars (LetTuple xs oret val body) = do
    freeVars oret *> freeVars val
    binding xs $ freeVars body
  
  -- freeVars (LetTick pat oin def oret body) = do
  --   freeVars oin -- TODO ??? no?
  --   freeVars def
  --   freeVars oret -- TODO ???
  --   binding pat $ freeVars body

  freeVars (If c oret t f) =
    freeVars c *> freeVars oret *> freeVars [t,f]

  freeVars (HasType tm ty) =
    freeVars [tm, ty]

  freeVars (CheckType tm ty) =
    freeVars [tm, ty]

  freeVars (ToSupportType tm) =
    freeVars tm

  freeVars (Arrow ty1 ty2) =
    freeVars [ty1, ty2]

  freeVars (App f xs) =
    freeVars f *> freeVars xs

  freeVars (ExplicitApp qid xs) =
    freeVars qid *> freeVars xs
  
  freeVars (InScope t _scope) =
    freeVars t
    -- The scope is a different sort of identifier, not a term-level variable.

  -- freeVars (Match items oret eqns) =
  --   -- TODO ???

  freeVars (Qualid qid) =
    freeVars qid

  freeVars (Sort sort) =
    freeVars sort -- Pro forma – there are none.

  freeVars (Num num) =
    freeVars num -- Pro forma – there are none.

  freeVars Underscore =
    pure ()

  freeVars (Parens t) =
    freeVars t

instance FreeVars Arg where
  freeVars (PosArg      t) = freeVars t
  freeVars (NamedArg _x t) = freeVars t
    -- The name here is the name of a function parameter; it's not an occurrence
    -- of a Gallina-level variable.

instance FreeVars Qualid where
  freeVars = occurrence . toIdent where
    toIdent (Bare x)          = x
    toIdent (Qualified mod x) = toIdent mod <> "." <> x

instance FreeVars Sort where
  freeVars Prop = pure ()
  freeVars Set  = pure ()
  freeVars Type = pure ()

instance FreeVars FixBodies where
  freeVars (FixOne fb) =
    freeVars fb
  freeVars (FixMany fb' fbs' x) =
    let fbs = fb' <| fbs'
    in binding (x <| (name <$> fbs)) $ freeVars fbs

instance FreeVars CofixBodies where
  freeVars (CofixOne cb) =
    freeVars cb
  freeVars (CofixMany cb' cbs' x) =
    let cbs = cb' <| cbs'
    in binding (x <| (name <$> cbs)) $ freeVars cbs

instance FreeVars FixBody where
  freeVars (FixBody f args annot oty def) =
    binding f . binding args . binding annot $ do
      freeVars oty
      freeVars def

instance FreeVars CofixBody where
  freeVars (CofixBody f args oty def) =
    binding f . binding args $ do
      freeVars oty
      freeVars def

instance FreeVars DepRetType where
  freeVars (DepRetType oas ret) = binding oas $ freeVars ret

instance FreeVars ReturnType where
  freeVars (ReturnType ty) = freeVars ty

-- All variables in a pattern should be bound: either they are free, in which
-- case are now bound; or they're constants, in which case they were already
-- bound.  It does mean we can't record free-ness, though.

foldableFreeVars :: (MonadFreeVars Ident m, FreeVars t, Foldable f) => f t -> m ()
foldableFreeVars = traverse_ freeVars

instance FreeVars t => FreeVars (Maybe t) where
  freeVars = foldableFreeVars

instance FreeVars t => FreeVars [t] where
  freeVars = foldableFreeVars

instance FreeVars t => FreeVars (NonEmpty t) where
  freeVars = foldableFreeVars
