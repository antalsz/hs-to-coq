{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts,
             TypeSynonymInstances, FlexibleInstances,
             OverloadedStrings #-}

module HsToCoq.Coq.FreeVars (
  -- * Things that contain free variables
  getFreeVars, FreeVars(..),
  -- * Binders
  Binding(..),
  -- * Fragments that contain name(s) to bind, but which aren't themselves
  -- 'Binders'
  Names(..),
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
import qualified Data.Set as S

import HsToCoq.Coq.Gallina

----------------------------------------------------------------------------------------------------

class Names t where
  names :: t -> Set Ident

instance Names FixBody where
  names (FixBody f _ _ _ _) = S.singleton f

instance Names CofixBody where
  names (CofixBody f _ _ _) = S.singleton f

instance Names IndBody where
  names (IndBody tyName _ _ cons) =
    S.insert tyName $ S.fromList [conName | (conName, _, _) <- cons]

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

instance Binding MatchItem where
  binding (MatchItem t oas oin) = (freeVars t *>) . binding oas . binding oin

instance Binding MultPattern where
  binding (MultPattern pats) = binding pats

-- Note [Bound variables in patterns]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- We cannot quite capture /all/ the free variables that occur in patterns.  The
-- ambiguous case is that a zero-ary constructor used unqualified looks exactly
-- like a variable used as a binder in a pattern.  So what do we do?  The answer
-- is that we treat is as a binder.  This is the right behavior: Coq has the
-- same problem, and it manages because it treats all unknown variables as
-- binders, as otherwise they'd be in scope.  What's more, treating all
-- variables as binders gives the right result in the body: even if it /wasn't/
-- a binder, it must have been bound already, so at least it will be bound in
-- the body!
--
-- We don't have to worry about module-qualified names, as they must be
-- references to existing terms; and we don't have to worry about constructors
-- /applied/ to arguments, as binders cannot be so applied.

-- See Note [Bound variables in patterns]
instance Binding Pattern where
  binding (ArgsPat con xs) =
    (freeVars con *>) . binding xs
  
  binding (ExplicitArgsPat con xs) =
    (freeVars con *>) . binding xs
  
  binding (AsPat pat x) =
    binding pat . binding x
    -- This correctly binds @x@ as the innermost binding
  
  binding (InScopePat pat _scope) =
    binding pat
    -- The scope is a different sort of identifier, not a term-level variable.

  binding (QualidPat (Bare x)) =
    binding x
    -- See [Note Bound variables in patterns]
  
  binding (QualidPat qid@(Qualified _ _)) =
    (freeVars qid *>)
  
  binding UnderscorePat =
    id
  
  binding (NumPat _num) =
    id
  
  binding (OrPats ors) =
    binding ors
    -- We don't check that all the or-patterns bind the same variables

instance Binding OrPattern where
  binding (OrPattern pats) = binding pats

-- An @in@-annotation, as found in 'LetTickDep' or 'MatchItem'.
instance Binding (Qualid, [Pattern]) where
  binding (con, pats) = (freeVars con *>) . binding pats

instance Binding Sentence where
  binding (AssumptionSentence assum)     = binding assum
  binding (DefinitionSentence def)       = binding def
  binding (InductiveSentence  ind)       = binding ind
  binding (FixpointSentence   fix)       = binding fix
  binding (AssertionSentence  assert pf) = binding assert . (freeVars pf *>)

instance Binding Assumption where
  binding (Assumption kwd assumptions) =
    (freeVars kwd *>) . binding assumptions
    -- The @kwd@ part is pro forma – there are no free variables there

instance Binding Assums where
  binding (UnparenthesizedAssums xs ty) =
    (freeVars ty *>) . binding xs
  binding (ParenthesizedAssums xsTys) = \body ->
    foldr (\(xs,ty) -> (freeVars ty *>) . binding xs) body xsTys

instance Binding Definition where
  binding (DefinitionDef isLocal x args oty def) =
    (freeVars isLocal *>)               . -- Pro forma – there are none
    binding args                        .
      (freeVars oty *> freeVars def *>) .
      binding x
  
  binding (LetDef x args oty def) =
    binding args                        .
      (freeVars oty *> freeVars def *>) .
      binding x

instance Binding Inductive where
  binding (Inductive   ibs) = binding (foldMap names ibs) . (freeVars ibs *>)
  binding (CoInductive cbs) = binding (foldMap names cbs) . (freeVars cbs *>)

instance Binding Fixpoint where
  binding (Fixpoint   fbs) = binding (foldMap names fbs) . (freeVars fbs *>)
  binding (CoFixpoint cbs) = binding (foldMap names cbs) . (freeVars cbs *>)

instance Binding Assertion where
  binding (Assertion kwd name args ty) =
    (freeVars kwd *> binding args (freeVars ty) *>) .
    binding name
    -- The @kwd@ part is pro forma – there are no free variables there

-- TODO Not all sequences of bindings should be telescopes!
bindingTelescope :: (MonadFreeVars Ident m, Binding b, Foldable f) => f b -> m a -> m a
bindingTelescope = flip $ foldr binding

instance Binding (Set Ident) where
  binding = bindAll

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
    binding (names fb) $ freeVars body

  freeVars (LetCofix cb body) = do
    freeVars cb
    binding (names cb) $ freeVars body

  freeVars (LetTuple xs oret val body) = do
    freeVars oret *> freeVars val
    binding xs $ freeVars body
  
  freeVars (LetTick pat def body) = do
    freeVars def
    binding pat $ freeVars body
  
  freeVars (LetTickDep pat oin def ret body) = do
    freeVars def
    binding oin $ freeVars ret
    binding pat $ freeVars body

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

  freeVars (Match items oret eqns) = do
    binding items $ freeVars oret
    freeVars eqns

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
    in binding (x `S.insert` foldMap names fbs) $ freeVars fbs

instance FreeVars CofixBodies where
  freeVars (CofixOne cb) =
    freeVars cb
  freeVars (CofixMany cb' cbs' x) =
    let cbs = cb' <| cbs'
    in binding (x `S.insert` foldMap names cbs) $ freeVars cbs

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

instance FreeVars Equation where
  freeVars (Equation mpats body) = binding mpats $ freeVars body

instance FreeVars AssumptionKeyword where
  freeVars Axiom      = pure ()
  freeVars Axioms     = pure ()
  freeVars Conjecture = pure ()
  freeVars Parameter  = pure ()
  freeVars Parameters = pure ()
  freeVars Variable   = pure ()
  freeVars Variables  = pure ()
  freeVars Hypothesis = pure ()
  freeVars Hypotheses = pure ()

instance FreeVars Locality where
  freeVars Global = pure ()
  freeVars Local  = pure ()

instance FreeVars IndBody where
  freeVars (IndBody tyName params indicesUniverse cons) =
    binding params $ do
      freeVars indicesUniverse
      binding tyName $ sequence_ [binding args $ freeVars oty | (_,args,oty) <- cons]

instance FreeVars AssertionKeyword where
  freeVars Theorem     = pure ()
  freeVars Lemma       = pure ()
  freeVars Remark      = pure ()
  freeVars Fact        = pure ()
  freeVars Corollary   = pure ()
  freeVars Proposition = pure ()
  freeVars Definition  = pure ()
  freeVars Example     = pure ()

instance FreeVars Proof where
  -- We don't model proofs.
  freeVars (ProofQed      _tactics) = pure ()
  freeVars (ProofDefined  _tactics) = pure ()
  freeVars (ProofAdmitted _tactics) = pure ()

foldableFreeVars :: (MonadFreeVars Ident m, FreeVars t, Foldable f) => f t -> m ()
foldableFreeVars = traverse_ freeVars

instance FreeVars t => FreeVars (Maybe t) where
  freeVars = foldableFreeVars

instance FreeVars t => FreeVars [t] where
  freeVars = foldableFreeVars

instance FreeVars t => FreeVars (NonEmpty t) where
  freeVars = foldableFreeVars
