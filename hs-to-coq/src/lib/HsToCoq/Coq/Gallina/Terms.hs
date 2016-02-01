{-|
Module      : HsToCoq.Coq.Gallina.Terms
Description : An AST for Gallina, the surface language of Coq
Copyright   : Copyright © 2016 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental

<https://coq.inria.fr/distrib/current/refman/Reference-Manual003. Chapter 1, \"The Gallina Specification Language\", in the Coq reference manual.>
-}

module HsToCoq.Coq.Gallina.Terms (
  -- * Lexical structure
  -- $Lexical
  Ident,
  AccessIdent,
  Num,
  
  -- * Terms
  -- $Terms
  Term(..),
  Arg(..),
  Binders,
  Binder(..),
  Name(..),
  Qualid(..),
  Sort(..),
  FixBodies(..),
  CofixBodies(..),
  FixBody(..),
  CofixBody(..),
  Annotation(..),
  MatchItem(..),
  DepRetType(..),
  ReturnType(..),
  Equation(..),
  MultPattern(..),
  Pattern(..),
  OrPattern(..),
  
  -- * The vernacular
  -- $Vernacular
  Sentence(..),
  Assumption(..),
  AssumptionKeyword(..),
  Assums(..),
  Locality(..),
  Definition(..),
  Inductive(..),
  IndBody(..),
  Fixpoint(..),
  Assertion(..),
  AssertionKeyword(..),
  Tactics,
  Proof(..)
  ) where

import Prelude hiding (Num)
import Numeric.Natural
import Data.List.NonEmpty

-- $Lexical
-- §1.1, "Lexical conventions", in the Coq reference manual; available at
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#lexical>.
--
-- We don't model the lexical conventions.  Values are just strings or numbers
-- or what have you.

-- |@/ident/ ::= /first_letter/ [/subsequent_letter/ … /subsequent_letter/]@
type Ident       = String
-- |@/access_ident/ ::= . /ident/@
type AccessIdent = Ident
-- |@/num/ ::= /digit/ … /digit/@
type Num         = Natural

-- $Terms
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#term §1.2, \"Terms\", in the Coq reference manual.>

-- |@/term/ ::=@
data Term = Forall Binders Term                                            -- ^@forall /binders/, /term/@
          | Fun Binders Term                                               -- ^@fun /binders/ => /term/@
          | Fix FixBodies                                                  -- ^@fix /fix_bodies/@
          | Cofix CofixBodies                                              -- ^@cofix /cofix_bodies/@
          | Let Ident [Binder] (Maybe Term) Term Term                      -- ^@let /ident/ [/binders/] [: /term/] := /term/ in /term/@
          | LetFix FixBody Term                                            -- ^@let fix /fix_body/ in /term/@
          | LetCofix CofixBody Term                                        -- ^@let cofix /cofix_body/ in /term/@
          | LetTuple [Name] DepRetType Term Term                           -- ^@let ( [/name/ , … , /name/] ) [/dep_ret_type/] := /term/ in /term/@
          | LetTick Pattern (Maybe Term) Term (Maybe ReturnType) Term      -- ^@let ' /pattern/ [in /term/] := /term/ [/return_type/] in /term/@
          | If Term (Maybe DepRetType) Term Term                           -- ^@if /term/ [/dep_ret_type/] then /term/ else /term/@
          | HasType Term Term                                              -- ^@/term/ : /term/@
          | CheckType Term Term                                            -- ^@/term/ <: /term/@
          | ToSupportType Term                                             -- ^@/term/ :>@
          | Arrow Term Term                                                -- ^@/term/ -> /term/@
          | App Term (NonEmpty Arg)                                        -- ^@/term/ /arg/ … /arg/@
          | ExplicitApp Qualid [Term]                                      -- ^@\@ /qualid/ [/term/ … /term/]@
          | InScope Term Ident                                             -- ^@/term/ % /ident/@
          | Match (NonEmpty MatchItem) (Maybe ReturnType) [Equation]       -- ^@match /match_item/ , … , /match_item/ [/return_type/] with [[|] /equation/ | … | /equation/] end@
          | Qualid Qualid                                                  -- ^@/qualid/@
          | Sort   Sort                                                    -- ^@/sort/@
          | Num    Num                                                     -- ^@/num/@
          | Underscore                                                     -- ^@_@
          deriving (Eq, Ord, Show, Read)

-- |@/arg/ ::=@
data Arg = PosArg Term                                                     -- ^@/term/@
         | NamedArg Ident Term                                             -- ^@( /ident/ := /term/ )@
         deriving (Eq, Ord, Show, Read)

-- |@/binders/ ::= /binder/ … /binder/@
type Binders = NonEmpty Binder

-- |@/binder/ ::=@
data Binder = Inferred Name                                                -- ^@/name/@
            | Typed (NonEmpty Name) Term                                   -- ^@( /name/ … /name/ : /term/ )@
            | BindLet Name (Maybe Term) Term                               -- ^@( /name/ [: /term/] := /term/ )@
            deriving (Eq, Ord, Show, Read)

-- |@/name/ ::=@
data Name = Ident Ident                                                    -- ^@/ident/@
          | UnderscoreName                                                 -- ^@_@
          deriving (Eq, Ord, Show, Read)

-- |@/qualid/ ::=@
data Qualid = Bare Ident                                                   -- ^@/ident/@
            | Qualified Qualid AccessIdent                                 -- ^@/qualid/ /access_ident/@
            deriving (Eq, Ord, Show, Read)

-- |@/sort/ ::=@
data Sort = Prop                                                           -- ^@Prop@
          | Set                                                            -- ^@Set@
          | Type                                                           -- ^@Type@
          deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- |@/fix_bodies/ ::=@
data FixBodies = FixOne FixBody                                            -- ^@/fix_body/@
               | FixMany FixBody (NonEmpty FixBody) Ident                  -- ^@/fix_body/ with /fix_body/ with … with /fix_body/ for /ident/@
               deriving (Eq, Ord, Show, Read)

-- |@/cofix_bodies/ ::=@
data CofixBodies = CofixOne CofixBody                                      -- ^@/cofix_body/@
                 | CofixMany CofixBody (NonEmpty CofixBody) Ident          -- ^@/cofix_body/ with /cofix_body/ with … with /cofix_body/ for /ident/@
                 deriving (Eq, Ord, Show, Read)

-- |@/fix_body/ ::=@
data FixBody = FixBody Ident Binders (Maybe Annotation) (Maybe Term) Term  -- ^@/ident/ /binders/ [/annotation/] [: /term/] := /term/@
             deriving (Eq, Ord, Show, Read)

-- |@/cofix_body/ ::=@
data CofixBody = CofixBody Ident Binders (Maybe Term) Term                 -- ^@/ident/ /binders/ [: /term/] := /term/@
               deriving (Eq, Ord, Show, Read)

-- |@/annotation/ ::=@
newtype Annotation = Annotation Ident                                      -- ^@{ struct /ident/ }@
                   deriving (Eq, Ord, Show, Read)

-- |@/match_item/ ::=@
data MatchItem = MatchItem Term (Maybe Name) (Maybe (Qualid, [Pattern]))   -- ^@/term/ [as /name/] [in /qualid/ [/pattern/ … /pattern/]]@
               deriving (Eq, Ord, Show, Read)

-- |@/dep_ret_type/ ::=@
data DepRetType = DepRetType (Maybe Name) ReturnType                       -- ^@[as /name/] /return_type/@
                deriving (Eq, Ord, Show, Read)

-- |@/return_type/ ::=@
newtype ReturnType = ReturnType Term                                       -- ^@return /term/@
                   deriving (Eq, Ord, Show, Read)

-- |@/equation/ ::=@
data Equation = Equation (NonEmpty MultPattern) Term                       -- ^@/mult_pattern/ | … | /mult_pattern/ => /term/@
              deriving (Eq, Ord, Show, Read)

-- |@/mult_pattern/ ::=@
newtype MultPattern = MultPattern (NonEmpty Pattern)                       -- ^@/pattern/ , … , /pattern/@
                    deriving (Eq, Ord, Show, Read)

-- |@/pattern/ ::=@
data Pattern = ArgsPat Qualid (NonEmpty Pattern)                           -- ^@/qualid/ /pattern/ … /pattern/@
             | ExplicitArgsPat Qualid (NonEmpty Pattern)                   -- ^@\@ /qualid/ /pattern/ … /pattern/@
             | AsPat Pattern Ident                                         -- ^@/pattern/ as /ident/@
             | InScopePat Pattern Ident                                    -- ^@/pattern/ % /ident/@
             | QualidPat Qualid                                            -- ^@/qualid/@
             | UnderscorePat                                               -- ^@_@
             | NumPat Num                                                  -- ^@_@
             | OrPats (NonEmpty OrPattern)                                 -- ^@( /or_pattern/ , … , /or_pattern/ )@
             deriving (Eq, Ord, Show, Read)

-- |@/or_pattern/ ::=@
newtype OrPattern = OrPattern (NonEmpty Pattern)                           -- ^@/pattern/ | … | /pattern/@
                  deriving (Eq, Ord, Show, Read)

-- $Vernacular
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#Vernacular §1.3, \"The Vernacular\", in the Coq reference manual.>.

-- |@/sentence/ ::=@
data Sentence = AssumptionSentence Assumption                              -- ^@/assumption/@
              | DefinitionSentence Definition                              -- ^@/definition/@
              | InductiveSentence  Inductive                               -- ^@/inductive/@
              | FixpointSentence   Fixpoint                                -- ^@/fixpoint/@
              | AssertionSentence  Assertion Proof                         -- ^@/assertion/ /proof/@
              deriving (Eq, Ord, Show, Read)

-- |@/assumption/ ::=@
data Assumption = Assumption AssumptionKeyword Assums                      -- ^@/assumption_keyword/ /assums/ .@
                deriving (Eq, Ord, Show, Read)

-- |@/assumption_keyword/ ::=@
data AssumptionKeyword = Axiom                                             -- ^@Axiom@
                       | Axioms                                            -- ^@Axioms@ – not in the grammar, but accepted.
                       | Conjecture                                        -- ^@Conjecture@
                       | Parameter                                         -- ^@Parameter@
                       | Parameters                                        -- ^@Parameters@
                       | Variable                                          -- ^@Variable@
                       | Variables                                         -- ^@Variables@
                       | Hypothesis                                        -- ^@Hypothesis@
                       | Hypotheses                                        -- ^@Hypotheses@
                       deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- |@/assums/ ::=@
data Assums = UnparenthesizedAssums (NonEmpty Ident) Term                  -- ^@/ident/ … /ident/ : /term/@
            | ParethesizedAssums (NonEmpty (NonEmpty Ident, Term))         -- ^@( /ident/ … /ident/ : /term ) … ( /ident/ … /ident/ : /term)@
            deriving (Eq, Ord, Show, Read)

-- |@[Local] ::=@ – not a part of the grammar /per se/, but a common fragment
data Locality = Global                                                     -- ^@@
              | Local                                                      -- ^@Local@
              deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- |@/definition/ ::=@
data Definition = DefinitionDef Locality Ident [Binder] (Maybe Term) Term  -- ^@[Local] Definition /ident/ [/binders/] [: /term/] := /term/ .@
                | LetDef Ident [Binder] (Maybe Term) Term                  -- ^@Let /ident/ [/binders/] [: /term/] := /term/ .@
                deriving (Eq, Ord, Show, Read)

-- |@/inductive/ ::=@
data Inductive = Inductive   (NonEmpty IndBody)                            -- ^@Inductive /ind_body/ with … with /ind_body/ .@
               | CoInductive (NonEmpty IndBody)                            -- ^@CoInductive /ind_body/ with … with /ind_body/ .@
               deriving (Eq, Ord, Show, Read)

-- |@/ind_body/ ::=@
data IndBody = IndBody Ident [Binder] Term [(Ident, [Binder], Maybe Term)] -- ^@/ident/ [/binders/] : /term/ := [[|] /ident/ [/binders/] [: /term/] | … | /ident/ [/binders/] [: /term/]]@
             deriving (Eq, Ord, Show, Read)

-- |@/fixpoint/ ::=@
data Fixpoint = Fixpoint   (NonEmpty FixBody)                              -- ^@Fixpoint /fix_body/ with … with /fix_body/ .@
              | CoFixpoint (NonEmpty FixBody)                              -- ^@CoFixpoint /fix_body/ with … with /fix_body/ .@
              deriving (Eq, Ord, Show, Read)

-- |@/assertion/ ::=@
data Assertion = Assertion AssertionKeyword Ident [Binder] Term            -- ^@/assertion_keyword/ /ident/ [/binders/] : /term/ .@
               deriving (Eq, Ord, Show, Read)

-- |@/assertion_keyword/ ::=@
data AssertionKeyword = Theorem                                            -- ^@Theorem@
                      | Lemma                                              -- ^@Lemma@
                      | Remark                                             -- ^@Remark@
                      | Fact                                               -- ^@Fact@
                      | Corollary                                          -- ^@Corollary@
                      | Proposition                                        -- ^@Proposition@
                      | Definition                                         -- ^@Definition@
                      | Example                                            -- ^@Example@
                      deriving (Eq, Ord, Show, Read, Enum, Bounded)

-- |A \"representation\" of tactics; left as @…@ in the grammar
type Tactics = String

-- |@/proof/ ::=@
data Proof = ProofQed      Tactics                                         -- ^@Proof . … Qed .@
           | ProofDefined  Tactics                                         -- ^@Proof . … Defined .@
           | ProofAdmitted Tactics                                         -- ^@Proof . … Admitted .@
           deriving (Eq, Ord, Show, Read)
