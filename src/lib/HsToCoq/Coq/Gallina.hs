{-|
Module      : HsToCoq.Coq.Gallina
Description : An AST for Gallina, the surface language of Coq
Copyright   : Copyright © 2016 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental

<https://coq.inria.fr/distrib/current/refman/Reference-Manual003. Chapter 1, \"The Gallina Specification Language\", in the Coq reference manual.>
-}

{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, OverloadedLists, LambdaCase, TemplateHaskell #-}

module HsToCoq.Coq.Gallina (
  -- * Lexical structure
  -- $Lexical
  Ident,
  ModuleIdent,
  AccessIdent,
  Num,
  Op,

  -- * Terms
  -- $Terms
  Term(..),
  Arg(..),
  Binders,
  Generalizability(..),
  Explicitness(..),
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
  Comment(..),
  LocalModule(..),

  -- * Signatures
  Signature(..),

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
  ProgramFixpoint(..),
  Order(..),
  Assertion(..),
  AssertionKeyword(..),
  Tactics,
  Proof(..),
  ImportExport(..),
  ModuleSentence(..),
  ClassDefinition(..),
  RecordDefinition(..),
  InstanceDefinition(..),
  Associativity(..),
  Level(..),
  Notation(..),
  NotationBinding(..),
  Arguments(..),
  ArgumentSpec(..),
  ArgumentExplicitness(..),
  ) where

import Prelude hiding (Num)

import Data.Text (Text)
import Numeric.Natural

import Data.List.NonEmpty (NonEmpty())

import Data.Typeable
import Data.Data (Data(..))

-- $Lexical
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#lexical §1.1, \"Lexical conventions\", in the Coq reference manual.>
--
-- We don't model the lexical conventions.  Values are just strings or numbers
-- or what have you.

-- |@/ident/ ::= /first_letter/ [/subsequent_letter/ … /subsequent_letter/]@
type Ident       = Text
-- |@/module_ident/ ::= /ident/ . /ident/ . …@
type ModuleIdent = Text
-- |@/access_ident/ ::= . /ident/@
type AccessIdent = Ident
-- |@/num/ ::= /digit/ … /digit/@
type Num         = Natural

-- |@/op/ ::= /symbol/ [/symbol/ … /symbol/]@ /(extra)/
type Op          = Text

-- $Terms
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#term §1.2, \"Terms\", in the Coq reference manual.>

-- |NB: There is a bug in the Coq manual as regards the definition
-- of destructuring pattern-@let@, i.e. with @let ' /pattern/ …@.  The
-- definition is given as
--
-- @
-- let ' /pattern/ [in /term/] := /term/ [/return_type/] in /term/
-- @
--
-- However:
--
-- 1. The @in@ annotation will only parse if the @/return_type/@ is present; and
-- 2. The @in@ annotation should be @[in /qualid/ [/pattern/ … /pattern/]]@
--    instead of simply @[in /term/]@, just as for @/match_item/@.
--
-- I have thus implemented this change in the AST that follows (the 'LetTick'
-- and 'LetTickDep' cases).
--
-- @/term/ ::=@
data Term = Forall Binders Term                                                                -- ^@forall /binders/, /term/@
          | Fun Binders Term                                                                   -- ^@fun /binders/ => /term/@
          | Fix FixBodies                                                                      -- ^@fix /fix_bodies/@
          | Cofix CofixBodies                                                                  -- ^@cofix /cofix_bodies/@
          | Let Qualid [Binder] (Maybe Term) Term Term                                          -- ^@let /ident/ [/binders/] [: /term/] := /term/ in /term/@
          | LetFix FixBody Term                                                                -- ^@let fix /fix_body/ in /term/@
          | LetCofix CofixBody Term                                                            -- ^@let cofix /cofix_body/ in /term/@
          | LetTuple [Name] (Maybe DepRetType) Term Term                                       -- ^@let ( [/name/ , … , /name/] ) [/dep_ret_type/] := /term/ in /term/@
          | LetTick Pattern Term Term                                                          -- ^@let ' /pattern/ := /term/ in /term/@
          | LetTickDep Pattern (Maybe (Qualid, [Pattern])) Term ReturnType Term                -- ^@let ' /pattern/ [in /qualid/ [/pattern/ … /pattern/]] := /term/ /return_type/ in /term/@
          | If Term (Maybe DepRetType) Term Term                                               -- ^@if /term/ [/dep_ret_type/] then /term/ else /term/@
          | HasType Term Term                                                                  -- ^@/term/ : /term/@
          | CheckType Term Term                                                                -- ^@/term/ <: /term/@
          | ToSupportType Term                                                                 -- ^@/term/ :>@
          | Arrow Term Term                                                                    -- ^@/term/ -> /term/@
          | App Term (NonEmpty Arg)                                                            -- ^@/term/ /arg/ … /arg/@
          | ExplicitApp Qualid [Term]                                                          -- ^@\@ /qualid/ [/term/ … /term/]@
          | Infix Term Qualid Term                                                             -- ^@/term/ /op/ /term/@ – extra. The qualid must be of the form op_...__
          | InScope Term Ident                                                                 -- ^@/term/ % /ident/@
          | Match (NonEmpty MatchItem) (Maybe ReturnType) [Equation]                           -- ^@match /match_item/ , … , /match_item/ [/return_type/] with [[|] /equation/ | … | /equation/] end@
          | Qualid Qualid                                                                      -- ^@/qualid/@
          | RawQualid Qualid                                                                   -- ^@/qualid/@ like Qualid, but never printed with notation
          | Sort Sort                                                                          -- ^@/sort/@
          | Num Num                                                                            -- ^@/num/@
          | PolyNum Num                                                                        -- ^@# /num/@ – extra (for polymorphic number literals)
          | String Text                                                                        -- ^@/string/@ – extra (holds the value, not the source text)
          | HsString Text                                                                      -- ^@& /string/@ – extra (for Haskell string literals)
          | HsChar Char                                                                        -- ^@&# /string/@ – extra (for Haskell character literals; /string/ is a single ASCII character)
          | Underscore                                                                         -- ^@_@
          | Parens Term                                                                        -- ^@( /term/ )@
          | Bang Term                                                                          -- ^@! term - tmp suppress implicit arguments (for Instance decls)
          | Record [ (Qualid, Term) ]                                                          -- ^@{| /qualid/ := /term/; … |}@
          deriving (Eq, Ord, Show, Read, Typeable, Data)

infixr 7 `Arrow`
infixl 8 `App`

-- |@/arg/ ::=@
data Arg = PosArg Term                                                                         -- ^@/term/@
         | NamedArg Ident Term                                                                 -- ^@( /ident/ := /term/ )@
         deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/binders/ ::= /binder/ … /binder/@
type Binders = NonEmpty Binder

-- |@/generalizability/ ::=@ – not a part of the grammar /per se/, but a common fragment
data Generalizability = Ungeneralizable                                                        -- ^@@ – (nothing)
                      | Generalizable                                                          -- ^@`@
                      deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/explicitness/ ::=@ – not a part of the grammar /per se/, but a common fragment
data Explicitness = Explicit                                                                   -- ^@( ⋯ )@ – wrap in parentheses
                  | Implicit                                                                   -- ^@{ ⋯ }@ – wrap in braces
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/binder/ ::=@ – the @/explicitness/@ is extra
data Binder = Inferred Explicitness Name                                                       -- ^@/name/@ or @{ /name/ }@
            | Typed Generalizability Explicitness (NonEmpty Name) Term                         -- ^@/generalizability/@ @( /name/ … /name/ : /term/ )@ or @/generalizability/@ @{ /name/ … /name/ : /term/ }@
            | BindLet Name (Maybe Term) Term                                                   -- ^@( /name/ [: /term/] := /term/ )@
            | Generalized Explicitness Term                                                    -- ^@` ( /term/ )@ or @` { /term/ }@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/name/ ::=@
data Name = Ident Qualid                                                                       -- ^@/ident/@
          | UnderscoreName                                                                     -- ^@_@
          deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/qualid/ ::=@
data Qualid = Bare Ident                                                                       -- ^@/ident/@
            | Qualified ModuleIdent AccessIdent                                                -- ^@/module_ident/ /access_ident/@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/sort/ ::=@
data Sort = Prop                                                                               -- ^@Prop@
          | Set                                                                                -- ^@Set@
          | Type                                                                               -- ^@Type@
          deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/fix_bodies/ ::=@
data FixBodies = FixOne FixBody                                                                -- ^@/fix_body/@
               | FixMany FixBody (NonEmpty FixBody) Qualid                                     -- ^@/fix_body/ with /fix_body/ with … with /fix_body/ for /ident/@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/cofix_bodies/ ::=@
data CofixBodies = CofixOne CofixBody                                                          -- ^@/cofix_body/@
                 | CofixMany CofixBody (NonEmpty CofixBody) Qualid                             -- ^@/cofix_body/ with /cofix_body/ with … with /cofix_body/ for /ident/@
                 deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/fix_body/ ::=@
data FixBody = FixBody Qualid Binders (Maybe Annotation) (Maybe Term) Term                     -- ^@/ident/ /binders/ [/annotation/] [: /term/] := /term/@
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/cofix_body/ ::=@
data CofixBody = CofixBody Qualid Binders (Maybe Term) Term                                    -- ^@/ident/ /binders/ [: /term/] := /term/@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/annotation/ ::=@
newtype Annotation = Annotation Qualid                                                         -- ^@{ struct /ident/ }@
                   deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/match_item/ ::=@
data MatchItem = MatchItem Term (Maybe Name) (Maybe (Qualid, [Pattern]))                       -- ^@/term/ [as /name/] [in /qualid/ [/pattern/ … /pattern/]]@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/dep_ret_type/ ::=@
data DepRetType = DepRetType (Maybe Name) ReturnType                                           -- ^@[as /name/] /return_type/@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/return_type/ ::=@
newtype ReturnType = ReturnType Term                                                           -- ^@return /term/@
                   deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/equation/ ::=@
data Equation = Equation (NonEmpty MultPattern) Term                                           -- ^@/mult_pattern/ | … | /mult_pattern/ => /term/@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/mult_pattern/ ::=@
newtype MultPattern = MultPattern (NonEmpty Pattern)                                           -- ^@/pattern/ , … , /pattern/@
                    deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/pattern/ ::=@
data Pattern = ArgsPat Qualid (NonEmpty Pattern)                                               -- ^@/qualid/ /pattern/ … /pattern/@
             | ExplicitArgsPat Qualid (NonEmpty Pattern)                                       -- ^@\@ /qualid/ /pattern/ … /pattern/@
             | InfixPat Pattern Op Pattern                                                     -- ^@/pattern/ /op/ /pattern/@ – extra
             | AsPat Pattern Qualid                                                            -- ^@/pattern/ as /ident/@
             | InScopePat Pattern Ident                                                        -- ^@/pattern/ % /ident/@
             | QualidPat Qualid                                                                -- ^@/qualid/@
             | UnderscorePat                                                                   -- ^@_@
             | NumPat Num                                                                      -- ^@/num/@
             | StringPat Text                                                                  -- ^@/string/@ – extra (holds the value, not the source text)
             | OrPats (NonEmpty OrPattern)                                                     -- ^@( /or_pattern/ , … , /or_pattern/ )@
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/or_pattern/ ::=@
newtype OrPattern = OrPattern (NonEmpty Pattern)                                               -- ^@/pattern/ | … | /pattern/@
                  deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/comment/ ::=@ /(extra)/
newtype Comment = Comment Text                                                                 -- ^@(* … *)@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- $Vernacular
-- <https://coq.inria.fr/distrib/current/refman/Reference-Manual003.html#Vernacular §1.3, \"The Vernacular\", in the Coq reference manual.>.
-- Module stuff is from <https://coq.inria.fr/refman/Reference-Manual004.html#Import §2.5, \"Module system\">,
-- and @Require@ is from <https://coq.inria.fr/refman/Reference-Manual008.html#Require §6.5.1>.
--
-- We also add cases to deal with certain notation definitions and similar.

-- |@/sentence/ ::=@
data Sentence = AssumptionSentence       Assumption                                            -- ^@/assumption/@
              | DefinitionSentence       Definition                                            -- ^@/definition/@
              | InductiveSentence        Inductive                                             -- ^@/inductive/@
              | FixpointSentence         Fixpoint                                              -- ^@/fixpoint/@
              | ProgramFixpointSentence  ProgramFixpoint (Maybe Text)                          -- ^@/program fixpoint/ Solve Obligations with (/tac/). Admit Obligations.@
              | AssertionSentence        Assertion Proof                                       -- ^@/assertion/ /proof/@
              | ModuleSentence           ModuleSentence                                        -- ^@/module_sentence/@ – extra (inferred from §2.5)
              | ClassSentence            ClassDefinition                                       -- ^@/class_definition/@ – extra
              | ExistingClassSentence    Qualid                                                -- ^@/Existing Class /ident//@ – extra
              | RecordSentence           RecordDefinition                                       -- ^@/class_definition/@ – extra
              | InstanceSentence         InstanceDefinition                                    -- ^@/instance_definition/@ – extra
              | ProgramInstanceSentence  InstanceDefinition                                    -- ^@Program /instance_definition/@ – extra
              | NotationSentence         Notation                                              -- ^@/notation/@ – extra
              | ArgumentsSentence        Arguments                                             -- ^@/arguments/@ – extra
              | CommentSentence          Comment                                               -- ^@/comment/@ – extra
              | LocalModuleSentence      LocalModule
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assumption/ ::=@
data Assumption = Assumption AssumptionKeyword Assums                                          -- ^@/assumption_keyword/ /assums/ .@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assumption_keyword/ ::=@
data AssumptionKeyword = Axiom                                                                 -- ^@Axiom@
                       | Axioms                                                                -- ^@Axioms@ – not in the grammar, but accepted.
                       | Conjecture                                                            -- ^@Conjecture@
                       | Parameter                                                             -- ^@Parameter@
                       | Parameters                                                            -- ^@Parameters@
                       | Variable                                                              -- ^@Variable@
                       | Variables                                                             -- ^@Variables@
                       | Hypothesis                                                            -- ^@Hypothesis@
                       | Hypotheses                                                            -- ^@Hypotheses@
                       deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/assums/ ::=@
data Assums = UnparenthesizedAssums (NonEmpty Qualid) Term                                     -- ^@/ident/ … /ident/ : /term/@
            | ParenthesizedAssums (NonEmpty (NonEmpty Qualid, Term))                           -- ^@( /ident/ … /ident/ : /term ) … ( /ident/ … /ident/ : /term)@
            deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@[Local] ::=@ – not a part of the grammar /per se/, but a common fragment
data Locality = Global                                                                         -- ^@@ – (nothing – but sometimes @Global@)
              | Local                                                                          -- ^@Local@
              deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/definition/ ::=@
data Definition = DefinitionDef Locality Qualid [Binder] (Maybe Term) Term                     -- ^@[Local] Definition /ident/ [/binders/] [: /term/] := /term/ .@
                | LetDef Qualid [Binder] (Maybe Term) Term                                     -- ^@Let /ident/ [/binders/] [: /term/] := /term/ .@
                deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/inductive/ ::=@ – the @where@ notation bindings are extra
data Inductive = Inductive   (NonEmpty IndBody) [NotationBinding]                              -- ^@Inductive /ind_body/ with … with /ind_body/ [where /notation_binding/ and … and /notation_binding/] .@
               | CoInductive (NonEmpty IndBody) [NotationBinding]                              -- ^@CoInductive /ind_body/ with … with /ind_body/ [where /notation_binding/ and … and /notation_binding/] .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/ind_body/ ::=@
data IndBody = IndBody Qualid [Binder] Term [(Qualid, [Binder], Maybe Term)]                   -- ^@/ident/ [/binders/] : /term/ := [[|] /ident/ [/binders/] [: /term/] | … | /ident/ [/binders/] [: /term/]]@
             deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/fixpoint/ ::=@
data Fixpoint = Fixpoint   (NonEmpty FixBody)   [NotationBinding]                              -- ^@Fixpoint /fix_body/ with … with /fix_body/ [where /notation_binding/ and … and /notation_binding/] .@
              | CoFixpoint (NonEmpty CofixBody) [NotationBinding]                              -- ^@CoFixpoint /fix_body/ with … with /fix_body/ [where /notation_binding/ and … and /notation_binding/] .@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/program fixpoint/ ::=@
data ProgramFixpoint = ProgramFixpoint Qualid [Binder] Order Term Term                         -- ^@Program Fixpoint /ident/ /params/ {/order/} : /type/ := /term/.@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/order/ ::=@
data Order = MeasureOrder Term (Maybe Term)                                                    -- ^@measure /term/ (/term/)?/
           | WFOrder Term Qualid                                                               -- ^@wf /term/ /ident//
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assertion/ ::=@
data Assertion = Assertion AssertionKeyword Qualid [Binder] Term                               -- ^@/assertion_keyword/ /ident/ [/binders/] : /term/ .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/assertion_keyword/ ::=@
data AssertionKeyword = Theorem                                                                -- ^@Theorem@
                      | Lemma                                                                  -- ^@Lemma@
                      | Remark                                                                 -- ^@Remark@
                      | Fact                                                                   -- ^@Fact@
                      | Corollary                                                              -- ^@Corollary@
                      | Proposition                                                            -- ^@Proposition@
                      | Definition                                                             -- ^@Definition@
                      | Example                                                                -- ^@Example@
                      deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |A \"representation\" of tactics; left as @…@ in the grammar
type Tactics = Text

-- |@/proof/ ::=@
data Proof = ProofQed      Tactics                                                             -- ^@Proof . … Qed .@
           | ProofDefined  Tactics                                                             -- ^@Proof . … Defined .@
           | ProofAdmitted Tactics                                                             -- ^@Proof . … Admitted .@
           deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/import_export/@ ::= – extra (inferred from §2.5.8)
data ImportExport = Import                                                                     -- ^@Import@
                  | Export                                                                     -- ^@Export@
                  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

-- |@/module_sentence/@ ::= – extra (inferred from §2.5 and §6.5.1), and incomplete
data ModuleSentence = ModuleImport ImportExport (NonEmpty Qualid)                              -- ^@/import_export/ /qualid/ … /qualid/ .@
                    | Require (Maybe Qualid) (Maybe ImportExport) (NonEmpty Qualid)            -- ^@[From /qualid/] Require [/import_export/] /qualid/ … /qualid/ .@
                    | ModuleAssignment Qualid Qualid                                           -- ^@Module /qualid/ := /qualid/ .@
                    deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/class_definition/ ::=@ /(extra)/
data ClassDefinition = ClassDefinition Qualid [Binder] (Maybe Sort) [(Qualid, Term)]            -- ^@Class /ident/ [/binders/] [: /sort/] := { [/ident/ : /term/ ; … ; /ident/ : /term/] } .
                     deriving (Eq, Ord, Show, Read, Typeable, Data)
                     -- TODO: field arguments (which become @forall@ed)

-- |@/record_definition/ ::=@ /(extra)/
data RecordDefinition = RecordDefinition Qualid [Binder] (Maybe Sort) (Maybe Qualid) [(Qualid, Term)]  -- ^@Record /ident/ [/binders/] [: /sort/] := /ident/ { [/ident/ : /term/ ; … ; /ident/ : /term/] } .
                     deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/instance_definition/ ::=@ /(extra)/
data InstanceDefinition = InstanceDefinition Qualid [Binder] Term [(Qualid, Term)] (Maybe Proof) -- ^@Instance /ident/ [/binders/] : /term/ := { [/ident/ := /term/ ; … ; /ident/ := /term/] } [/proof/] .
                                                                                               -- TODO: field arguments (which become @fun@ arguments)
                        | InstanceTerm Qualid [Binder] Term Term (Maybe Proof)                  -- ^@Instance /ident/ [/binders/] : /term/ := /term/ [/proof/] .
                        deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/associativity/ ::=@ /(extra)/
data Associativity = LeftAssociativity                                                         -- ^@left@
                   | RightAssociativity                                                        -- ^@right@
                   | NoAssociativity                                                           -- ^@no@
                   deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/level/ ::=@ /(extra)/
newtype Level = Level Num                                                                      -- ^@at level /num/@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/notation/ ::=@ /(extra)/
data Notation = ReservedNotationIdent Ident                                                    -- ^@Reserved Notation "'/ident/'" .@
              | NotationBinding NotationBinding                                                -- ^@Notation /notation_binding/ .@
              | InfixDefinition Op Term (Maybe Associativity) Level                            -- ^@Infix "/op/" := ( /term/ ) ( [/associativity/ associativity ,] /level/ ) .@
              deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/notation_binding/ ::=@ /(extra)/
data NotationBinding = NotationIdentBinding Ident Term                                         -- ^@"'/ident/'" := (/term/) .@
                     deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/arguments/ ::=@ /(extra)/
data Arguments = Arguments (Maybe Locality) Qualid [ArgumentSpec]                              -- ^@[Local|Global]@ Arguments /qualid/ [/argument_spec/ … /argument_spec/] .@
               deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/argument_spec/ ::=@ /(extra)/
data ArgumentSpec = ArgumentSpec ArgumentExplicitness Name (Maybe Ident)                       -- ^@/name/ [% /ident/]@ or @[ /name/ ] [% /ident/]@ or @{ /name/ } [% /ident/]@
                  deriving (Eq, Ord, Show, Read, Typeable, Data)

-- |@/argument_explicitness/ ::=@ /(extra)/ – not a part of the grammar /per se/, but a common fragment
data ArgumentExplicitness = ArgExplicit                                                        -- ^@( ⋯ )@ – wrap in parentheses or nothing
                          | ArgImplicit                                                        -- ^@[ ⋯ ]@ – wrap in square brackets
                          | ArgMaximal                                                         -- ^@{ ⋯ }@ – wrap in braces
                          deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)


data LocalModule = LocalModule Ident [Sentence]
                      deriving (Eq, Ord, Show, Read, Typeable, Data)

-- A Coq signature
-- TODO: Move this?
data Signature = Signature { sigType   :: Term
                           , sigFixity :: Maybe (Associativity, Level) }
               deriving (Eq, Ord, Show, Read)
