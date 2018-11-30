{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts,
             TypeSynonymInstances, FlexibleInstances,
             OverloadedStrings, OverloadedLists #-}

module HsToCoq.Coq.Subst (
  -- * Things that can be substituted
  Subst(..),
  ) where

import Prelude hiding (Num)


--import Control.Monad.Variables
--import HsToCoq.Util.Function
--import Data.List.NonEmpty (NonEmpty(), (<|))
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Map.Strict as M

import HsToCoq.Coq.Gallina

----------------------------------------------------------------------------------------------------

-- Note: this is not capture avoiding substitution (yet!)
--
-- When it comes across an operator, it searches for its 'infixToCoq' name
-- in the map, and turns the operator application into a term application
-- if necessary.

class Subst t where
  subst :: Map Qualid Term -> t -> t



instance Subst IndBody where
  subst f (IndBody tyName params indicesUnivers cons) =
    IndBody tyName params indicesUnivers (map (substCon f) cons)
       where substCon f (qid,binders, Nothing) = (qid, map (subst f) binders, Nothing)
             substCon f (qid,binders, Just t)  = (qid, map (subst f) binders, Just (subst f t))

instance Subst Binder where
  subst _f b@(Inferred _ex _x)    = b
  subst f (Typed gen ex xs ty) = Typed gen ex xs (subst f ty)
  subst f (Generalized ex ty)  = Generalized ex (subst f ty)

instance Subst MatchItem where
  subst f (MatchItem t oas oin) = MatchItem (subst f t) oas oin

instance Subst MultPattern where
  subst f (MultPattern pats) = MultPattern (subst f pats)

instance Subst Pattern where
  subst _f pat = pat
{-
  subst f (ArgsPat con xs)   = ArgsPat con (subst f xs)

  subst f (ExplicitArgsPat con xs) = ExplicitArgsPat con (subst f xs)

  subst f (InfixPat l op r) = InfixPat (subst f l) op (subst f r)

  subst f (AsPat pat x) = AsPat (subst f pat) x

  subst f (InScopePat pat _scope) =

  subst f p@(QualidPat _) = p

  subst _ p@UnderscorePat = p

  subst _ p@(NumPat _num) = p

  subst _ p@(StringPat _str) = p

  subst f (OrPats ors) = OrPats (subst f ors)

instance Subst OrPattern where
  subst f (OrPattern pats) = OrPattern (subst f pats)
-}


instance Subst Sentence where
  subst f (AssumptionSentence      assum)     = AssumptionSentence        (subst f assum)
  subst f (DefinitionSentence      def)       = DefinitionSentence        (subst f def)
  subst f (InductiveSentence       ind)       = InductiveSentence         (subst f ind)
  subst f (FixpointSentence        fix)       = FixpointSentence          (subst f fix)
  subst f (ProgramSentence         sen pf)    = ProgramSentence           (subst f sen) pf
  subst f (AssertionSentence       assert pf) = AssertionSentence         (subst f assert) pf
  subst f (ModuleSentence          mod)       = ModuleSentence            (subst f mod)
  subst f (ClassSentence           cls)       = ClassSentence             (subst f cls)
  subst f (RecordSentence          rcd)       = RecordSentence            (subst f rcd)
  subst f (InstanceSentence        ins)       = InstanceSentence          (subst f ins)
  subst f (NotationSentence        not)       = NotationSentence          (subst f not)
  subst f (LocalModuleSentence     lmd)       = LocalModuleSentence       (subst f lmd)
  subst _ s@(ExistingClassSentence  _)        = s
  subst _ s@(ArgumentsSentence  _)            = s
  subst _ s@(CommentSentence    _)            = s

instance Subst Assumption where
  subst f (Assumption kwd assumptions) =
    Assumption kwd (subst f assumptions)
    -- The @kwd@ part is pro forma – there are no free variables there

instance Subst Assums where
  subst f (Assums xs ty) = Assums xs (subst f ty)

instance Subst Definition where
  subst f (LetDef x args oty def) =
    LetDef x (subst f args) (subst f oty) (subst f def)

  subst f (DefinitionDef isL x args oty def) =
    DefinitionDef isL x (subst f args) (subst f oty) (subst f def)



instance Subst Inductive where
  subst _f (Inductive   _ibs _nots) = error "subst"
  subst _f (CoInductive _cbs _nots) = error "subst"


instance Subst Fixpoint where
  subst f (Fixpoint   fbs nots) = Fixpoint (subst f fbs) (subst f nots)
  subst f (CoFixpoint cbs nots) = CoFixpoint (subst f cbs) (subst f nots)

instance Subst Order where
  subst _f (StructOrder ident)     = StructOrder ident
  subst f  (MeasureOrder expr rel) = MeasureOrder (subst f expr) (subst f rel)
  subst f  (WFOrder rel ident)     = WFOrder      (subst f rel)  ident

instance Subst Assertion where
  subst f (Assertion kwd name args ty) = Assertion kwd name (subst f args) (subst f ty)

instance Subst ModuleSentence where
  subst _ mod = mod

instance Subst LocalModule where
  subst f (LocalModule name sentences) = LocalModule name (map (subst f) sentences)

instance Subst ClassDefinition where
  subst _f (ClassDefinition _cl _params _osrt _fields) = error "subst"

instance Subst RecordDefinition where
  subst _f _ = error "subst"

instance Subst InstanceDefinition where
  subst _f (InstanceDefinition _inst _params _cl _defns _mpf) = error "subst"
  subst _f (InstanceTerm       _inst _params _cl _term _mpf)  = error "subst"

instance Subst Notation where
  subst _f (ReservedNotationIdent _x) = error "subst"
  subst _f (NotationBinding _nb) = error "subst"
  subst _f (InfixDefinition _op _defn _oassoc _level) = error "subst"

instance Subst NotationBinding where
  subst _f _ = error "subst"

instance Subst FixBodies where
    subst f (FixOne b)        = FixOne  (subst f b)
    subst f (FixMany b neb x) = FixMany (subst f b) (subst f neb) x

instance Subst FixBody where
    subst f (FixBody n bs ma mt t) = FixBody n (subst f bs) (subst f ma) (subst f mt) (subst f t)

instance Subst Arg where
   subst f (PosArg t) = PosArg (subst f t)
   subst f (NamedArg i t) = NamedArg i (subst f t)

instance Subst DepRetType where
   subst f (DepRetType mn rt) = DepRetType mn (subst f rt)

instance Subst ReturnType where
   subst f (ReturnType t) = ReturnType (subst f t)

instance Subst Equation where
   subst f (Equation nep t) = Equation nep (subst f t)

instance Subst Term where
  subst f (Forall xs t) = Forall (subst f xs) (subst f t)

  subst f  (Fun xs t) = Fun (subst f xs) (subst f t)

  subst f  (Fix fbs) = Fix (subst f fbs)

  subst f  (Cofix cbs) = Cofix (subst f cbs)

  subst f  (Let x args oty val body) = Let x (subst f args) (subst f oty) (subst f val) (subst f body)

  subst f  (LetTuple xs oret val body) = LetTuple xs (subst f oret) (subst f val) (subst f body)

  subst f  (LetTick pat def body) = LetTick (subst f pat) (subst f def) (subst f body)

  subst f  (If is c oret t fa) = If is (subst f c) (subst f oret) (subst f t) (subst f fa)

  subst f  (HasType tm ty) = HasType (subst f tm) (subst f ty)

  subst f  (CheckType tm ty) = CheckType (subst f tm) (subst f ty)

  subst f  (ToSupportType tm) = ToSupportType (subst f tm)

  subst f  (Arrow ty1 ty2) = Arrow (subst f ty1) (subst f ty2)

  subst f  (App fu xs) = App (subst f fu) (subst f  xs)

  subst f  (ExplicitApp qid xs) = ExplicitApp qid (subst f  xs)

  subst f  (InScope t scope) =  InScope (subst f  t) scope
    -- The scope is a different sort of identifier, not a term-level variable.

  subst f (Match items oret eqns) = Match (subst f items) (subst f oret) (subst f eqns)

  subst  f x@(Qualid qid) = fromMaybe x (M.lookup qid f)

  subst  f x@(RawQualid qid) = fromMaybe x (M.lookup qid f)

  subst _f x@(Sort _sort) = x

  subst _f x@(Num _num) = x

  subst _f x@(String _str) = x

  subst _f x@(HsString _str) = x

  subst _f x@(HsChar _char) = x

  subst _f x@Underscore = x

  subst f (Parens t) = Parens (subst f  t)

  subst f (Bang t) = Bang (subst f t)

  subst f (Record defns) = Record [ (v, subst f t) | (v,t) <- defns ]

instance (Subst a, Functor f) => Subst (f a) where
  subst f = fmap (subst f)
