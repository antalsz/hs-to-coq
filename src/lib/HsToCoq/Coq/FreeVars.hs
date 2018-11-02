{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts,
             TypeSynonymInstances, FlexibleInstances,
             OverloadedStrings, ConstraintKinds, DataKinds #-}

-- For TypeError
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Coq.FreeVars (
  -- * Constraint syonyms
  FreeVars,
  -- * Main query functions
  getFreeVars, getFreeVars', definedBy,
  NoBinding(..),
  -- * Utility methods
  topoSortEnvironment, topoSortEnvironmentWith, topoSortByVariablesBy, topoSortByVariables,
  ) where

import Prelude hiding (Num)

import Control.Lens hiding ((<|))

import Data.Foldable
import HsToCoq.Util.List
import HsToCoq.Util.Containers

import HsToCoq.Util.FVs

import Data.List.NonEmpty (NonEmpty(), (<|))
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import GHC.TypeLits

import HsToCoq.Coq.Gallina

----------------------------------------------------------------------------------------------------

type FreeVars = HasFV Qualid

instance TypeError ('Text "Use binder if this is a binder, use fvOf if this is an occurrence")
  => HasBV Qualid Qualid where
  bvOf _ = undefined

instance HasBV Qualid FixBody where
  bvOf (FixBody f args order oty def)
    = binder f `telescope` bindsNothing (foldScopes bvOf args
                                    (fvOf order <> fvOf oty <> fvOf def))

instance HasBV Qualid FixBodies where
  bvOf (FixOne fb)           = bvOf fb
  bvOf (FixMany fb1 fbs qid) = binder qid <>
    bindsNothing (forgetBinders (scopesMutually bvOf (fb1 <| fbs)))


instance HasBV Qualid IndBody where
  bvOf (IndBody tyName params indicesUniverse cons) =
    binder tyName `telescope`
    (bindsNothing (foldScopes bvOf params $ fvOf indicesUniverse) <>
     mconcat [ binder conName <>
               bindsNothing (foldScopes bvOf params $ foldScopes bvOf args $ fvOf oty)
             | (conName, args, oty) <- cons])

instance HasBV Qualid Name where
  bvOf (Ident x)      = binder x
  bvOf UnderscoreName = mempty

instance HasBV Qualid Binder where
  bvOf (Inferred _ex x)       = bvOf x
  bvOf (Typed _gen _ex xs ty) = foldMap bvOf xs <> fvOf' ty
  bvOf (Generalized _ex ty)   = fvOf' ty

instance HasBV Qualid MatchItem where
  bvOf (MatchItem scrut oas oin)
    = fvOf' scrut <> bvOf oas <> bvOf oin

instance HasBV Qualid MultPattern where
  bvOf (MultPattern pats) = foldMap bvOf pats

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
instance HasBV Qualid Pattern where
  bvOf (ArgsPat con xs)          = fvOf' con <> foldMap bvOf xs
  bvOf (ExplicitArgsPat con xs)  = fvOf' con <> foldMap bvOf xs
  bvOf (InfixPat l op r)         = bvOf l <> fvOf' (Bare op) <> bvOf r
  bvOf (AsPat pat x)             = bvOf pat <> binder x
  bvOf (InScopePat pat _scp)     = bvOf pat
  bvOf (QualidPat qid@(Bare _))  = binder qid
    -- See [Note Bound variables in patterns]
  bvOf (QualidPat qid)           = fvOf' qid
  bvOf UnderscorePat             = mempty
  bvOf (NumPat _num)             = mempty
  bvOf (StringPat _str)          = mempty
  bvOf (OrPats ors)              = foldMap bvOf ors
    -- We don't check that all the or-patterns bind the same variables

instance HasBV Qualid OrPattern where
  bvOf (OrPattern pats) = foldMap bvOf pats

-- An @in@-annotation, as found in 'LetTickDep' or 'MatchItem'.
instance HasBV Qualid (Qualid, [Pattern]) where
  bvOf (con, pats) = fvOf' con <> foldMap bvOf pats

instance HasBV Qualid Sentence where
  bvOf (AssumptionSentence    assum)      = bvOf   assum
  bvOf (DefinitionSentence    def)        = bvOf   def
  bvOf (InductiveSentence     ind)        = bvOf   ind
  bvOf (FixpointSentence      fix)        = bvOf   fix
  bvOf (ProgramSentence       sen _)      = bvOf   sen
  bvOf (AssertionSentence     assert _pf) = bvOf   assert
  bvOf (ModuleSentence        _mod)       = mempty
  bvOf (ClassSentence         cls)        = bvOf   cls
  bvOf (ExistingClassSentence name)       = fvOf'  name
  bvOf (RecordSentence        rcd)        = bvOf   rcd
  bvOf (InstanceSentence      ins)        = bvOf   ins
  bvOf (NotationSentence      not)        = bvOf   not
  bvOf (LocalModuleSentence   lmd)        = bvOf   lmd
  bvOf (ArgumentsSentence     _arg)       = mempty
  bvOf (CommentSentence       com)        = fvOf'  com

instance HasBV Qualid Assumption where
  bvOf (Assumption _kwd assumptions) = bvOf assumptions

instance HasBV Qualid Assums where
  bvOf (Assums xs ty) = fvOf' ty <> binders xs

instance HasBV Qualid Definition where
  bvOf (DefinitionDef _locality x args oty def)
    = binder x <> bindsNothing (foldScopes bvOf args $ fvOf oty <> fvOf def)
  bvOf (LetDef x args oty def)
    = binder x <> bindsNothing (foldScopes bvOf args $ fvOf oty <> fvOf def)

instance HasBV Qualid Inductive where
  bvOf (Inductive   ibs nots) = scopesMutually id $ (bvOf <$> ibs) ++> (bvOf <$> nots)
  bvOf (CoInductive cbs nots) = scopesMutually id $ (bvOf <$> cbs) ++> (bvOf <$> nots)

instance HasBV Qualid Fixpoint where
  bvOf (Fixpoint   fbs nots) =  scopesMutually id $ (bvOf <$> fbs) ++> (bvOf <$> nots)
  bvOf (CoFixpoint cbs nots) =  scopesMutually id $ (bvOf <$> cbs) ++> (bvOf <$> nots)

instance HasBV Qualid Assertion where
  bvOf (Assertion _kwd name args ty) =
    binder name <> bindsNothing (foldScopes bvOf args $ fvOf ty)

instance HasBV Qualid ClassDefinition where
  bvOf (ClassDefinition cl params _osort fields) =
    binder cl <>
    foldTelescope bvOf params `telescope`
        mconcat [ binder field <> fvOf' ty | (field, ty) <- fields ]

instance HasBV Qualid RecordDefinition where
  bvOf (RecordDefinition name params _osort build fields) =
    binder name <> foldMap binder build <>
    foldTelescope bvOf params `telescope`
        mconcat [ binder field <> fvOf' ty| (field, ty) <- fields ]
      -- TODO: If build is Nothing, we could synthesize the expected build name

instance HasBV Qualid InstanceDefinition where
  bvOf (InstanceDefinition inst params cl defns _mpf) =
    binder inst <>
    bindsNothing (foldScopes bvOf params $ fvOf cl <> fvOf defns)
  bvOf (InstanceTerm inst params cl term _mpf) =
    binder inst <>
    bindsNothing (foldScopes bvOf params $ fvOf cl <> fvOf term)

instance HasBV Qualid Notation where
  bvOf (ReservedNotationIdent _)     = mempty
  bvOf (NotationBinding nb)          = bvOf nb
  bvOf (InfixDefinition op defn _ _) = binder (Bare op) <> fvOf' defn

instance HasBV Qualid NotationBinding where
  bvOf (NotationIdentBinding op def) = binder (Bare op) <> fvOf' def

instance HasBV Qualid LocalModule where
  bvOf (LocalModule _name sentences) = foldTelescope bvOf sentences

-- TODO Not all sequences of bindings should be telescopes!
-- bindingTelescope :: (HasBV b, Monoid d, Foldable f)
--                  => (Qualid -> d) -> f b -> Variables Qualid d a -> Variables Qualid d a
-- bindingTelescope f xs rest = foldr (bvOf) rest xs

instance HasBV Qualid b => HasBV Qualid (Maybe b) where
  bvOf = foldMap bvOf

instance TypeError ('Text "A sequence of binders could be a telescope (use foldTelescope or foldScopes) or not (use foldMap)") => HasBV Qualid [b] where
  bvOf = undefined

instance TypeError ('Text "A sequence of binders could be a telescope (use foldTelescope or foldScopes) or not (use foldMap)") => HasBV Qualid (NonEmpty b) where
  bvOf = undefined

----------------------------------------------------------------------------------------------------

getFreeVars :: HasFV Qualid t => t -> Set Qualid
getFreeVars = getFVs . fvOf

getFreeVars' :: HasBV Qualid t => t -> Set Qualid
getFreeVars' = getFVs . forgetBinders . bvOf


definedBy :: HasBV Qualid x => x -> [Qualid]
definedBy = S.toList . getBVars . bvOf

instance HasFV Qualid Qualid where
  fvOf = occurrence

instance HasFV Qualid Term where
  fvOf (Forall xs t) = foldScopes bvOf xs $ fvOf t
  fvOf (Fun xs t)    = foldScopes bvOf xs $ fvOf t
  fvOf (Fix fbs)     = forgetBinders $ bvOf fbs -- The fixpoint name stays local
  fvOf (Cofix cbs)   = forgetBinders $ bvOf cbs
  fvOf (Let x args oty val body) =
    foldScopes bvOf args (fvOf oty <> fvOf val) <>
    binder x  `scopesOver` fvOf body

  fvOf (LetTuple xs oret val body) =
    fvOf oret <> fvOf val <> (foldScopes bvOf xs (fvOf body))

  fvOf (LetTick pat def body) =
    fvOf def <> bvOf pat `scopesOver` fvOf body

  fvOf (If _ c oret t f)       = fvOf c <> fvOf oret <> fvOf t <> fvOf f
  fvOf (HasType tm ty)         = fvOf tm <> fvOf ty
  fvOf (CheckType tm ty)       = fvOf tm <> fvOf ty
  fvOf (ToSupportType tm)      = fvOf tm
  fvOf (Arrow ty1 ty2)         = fvOf ty1 <> fvOf ty2
  fvOf (App f xs)              = fvOf f   <> fvOf xs
  fvOf (ExplicitApp qid xs)    = fvOf qid <> fvOf xs
  fvOf (InScope t _scope)      = fvOf t
  fvOf (Match items oret eqns) = foldMap bvOf items `scopesOver` (fvOf oret <> fvOf eqns)
  fvOf (Qualid qid)            = fvOf qid
  fvOf (RawQualid qid)         = fvOf qid
  fvOf (Sort _sort)            = mempty
  fvOf (Num _num)              = mempty
  fvOf (String _str)           = mempty
  fvOf (HsString _str)         = mempty
  fvOf (HsChar _char)          = mempty
  fvOf Underscore              = mempty
  fvOf (Parens t)              = fvOf t
  fvOf (Bang t)                = fvOf t
  fvOf (Record defns)          = fvOf defns

instance HasFV Qualid Arg where
  fvOf (PosArg      t) = fvOf t
  fvOf (NamedArg _x t) = fvOf t
    -- The name here is the name of a function parameter; it's not an occurrence
    -- of a Gallina-level variable.

instance HasFV Qualid Order where
  fvOf (StructOrder qid)       = fvOf qid
  fvOf (MeasureOrder expr rel) = fvOf expr <> fvOf rel
  fvOf (WFOrder rel qid)       = fvOf rel <> fvOf qid


instance HasFV Qualid DepRetType where
  fvOf (DepRetType oas ret) = bvOf oas `scopesOver` fvOf ret

instance HasFV Qualid ReturnType where
  fvOf (ReturnType ty) = fvOf ty

instance HasFV Qualid Equation where
  fvOf (Equation mpats body) = foldMap bvOf mpats `scopesOver` fvOf body

instance HasFV Qualid Comment where
  fvOf (Comment _) = mempty

instance HasFV Qualid AssumptionKeyword where
  fvOf Axiom      = mempty
  fvOf Axioms     = mempty
  fvOf Conjecture = mempty
  fvOf Parameter  = mempty
  fvOf Parameters = mempty
  fvOf Variable   = mempty
  fvOf Variables  = mempty
  fvOf Hypothesis = mempty
  fvOf Hypotheses = mempty

instance HasFV Qualid Locality where
  fvOf Global = mempty
  fvOf Local  = mempty

instance HasFV Qualid AssertionKeyword where
  fvOf Theorem     = mempty
  fvOf Lemma       = mempty
  fvOf Remark      = mempty
  fvOf Fact        = mempty
  fvOf Corollary   = mempty
  fvOf Proposition = mempty
  fvOf Definition  = mempty
  fvOf Example     = mempty

instance HasFV Qualid t => HasFV Qualid (Maybe t) where
  fvOf = foldMap fvOf

instance HasFV Qualid t => HasFV Qualid [t] where
  fvOf = foldMap fvOf

instance HasFV Qualid t => HasFV Qualid (NonEmpty t) where
  fvOf = foldMap fvOf

instance (HasFV Qualid t1, HasFV Qualid t2) => HasFV Qualid (t1,t2) where
  fvOf (x,y) = fvOf x <> fvOf y


newtype NoBinding a = NoBinding a

instance HasBV i a => HasFV i (NoBinding a) where
    fvOf (NoBinding x) = forgetBinders (bvOf x)

-- The order is correct – later identifiers refer only to previous ones – since
-- 'stronglyConnComp'' returns its outputs in topologically sorted order.
topoSortEnvironmentWith :: Foldable f => (a -> f Qualid) -> Map Qualid a -> [NonEmpty Qualid]
topoSortEnvironmentWith fvs = stronglyConnComp' . M.toList
                            . fmap (toList . fvs)

-- The order is correct – later identifiers refer only to previous ones – since
-- 'stronglyConnComp'' returns its outputs in topologically sorted order.
topoSortEnvironment :: HasFV Qualid t => Map Qualid t -> [NonEmpty Qualid]
topoSortEnvironment = topoSortEnvironmentWith getFreeVars

type ExtraFreeVars = Map Qualid (Set Qualid)

-- | Sort 'Sentence's or similar based on their free variables and the extra
-- edges provided. Tries to keep sentences in order otherwise.
topoSortByVariablesBy :: HasBV Qualid b => (a -> b) -> ExtraFreeVars -> [a] -> [a]
topoSortByVariablesBy toBV extraFVs = stableTopoSortByPlus (definedBy . toBV)
                                                           (getFreeVars' . toBV)
                                                           (M.findWithDefault S.empty ?? extraFVs)

topoSortByVariables :: HasBV Qualid a => ExtraFreeVars -> [a] -> [a]
topoSortByVariables = topoSortByVariablesBy id
