{

{-# LANGUAGE TupleSections, OverloadedStrings, CPP #-}

--work around https://github.com/simonmar/happy/issues/109
#undef __GLASGOW_HASKELL__
#define __GLASGOW_HASKELL__ 709

module HsToCoq.ConvertHaskell.Parameters.Parsers (
  parseTerm, parseSentence, parseEditList
) where

import Data.Foldable
import Data.Maybe
import Data.Either
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NEL
import qualified Data.Text as T
import qualified Data.Set as S

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Parse

import HsToCoq.Util.GHC.Module (ModuleName(), mkModuleNameT)

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Orphans ()
import HsToCoq.Coq.Pretty (showP)

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing
}

-- No conflicts allowed
%expect 0

%name      parseTerm         Term
%name      parseSentence     Sentence
%name      parseEditList     Edits

%tokentype { Token }
%error     { unexpected }

%monad { Lexing }
%lexer { (=<< token) } { TokEOF }

-- Please maintain the format of this list; the token definitions and the
-- dividing comments of the form `-- Tokens: $CATEGORY` are used to generate an
-- Emacs major mode with syntax highlighting.
%token
  -- Tokens: Edits
  value           { TokWord    "value"          }
  type            { TokWord    "type"           }
  data            { TokWord    "data"           }
  synonym         { TokWord    "synonym"        }
  arguments       { TokWord    "arguments"      }
  parameters      { TokWord    "parameters"     }
  indices         { TokWord    "indices"        }
  redefine        { TokWord    "redefine"       }
  skip            { TokWord    "skip"           }
  manual          { TokWord    "manual"         }
  import          { TokWord    "import"         }
  notation        { TokWord    "notation"       }
  class           { TokWord    "class"          }
  kinds           { TokWord    "kinds"          }
  delete          { TokWord    "delete"         }
  unused          { TokWord    "unused"         }
  variables       { TokWord    "variables"      }
  axiomatize      { TokWord    "axiomatize"     }
  definition      { TokWord    "definition"     }
  unaxiomatize    { TokWord    "unaxiomatize"   }
  termination     { TokWord    "termination"    }
  'deferred'      { TokWord    "deferred"       }
  'corecursive'   { TokWord    "corecursive"    }
  coinductive     { TokWord    "coinductive"    }
  obligations     { TokWord    "obligations"    }
  method          { TokWord    "method"         }
  rename          { TokWord    "rename"         }
  rewrite         { TokWord    "rewrite"        }
  order           { TokWord    "order"          }
  module          { TokWord    "module"         }
  add             { TokWord    "add"            }
  scope           { TokWord    "scope"          }
  constructor     { TokWord    "constructor"    }
  simple          { TokWord    "simple"         }
  inline          { TokWord    "inline"         }
  mutual          { TokWord    "mutual"         }
  set             { TokWord    "set"            }
  no              { TokWord    "no"             }
  collapse        { TokWord    "collapse"       }
  equation        { TokWord    "equation"       }
  case            { TokWord    "case"           }
  pattern         { TokWord    "pattern"        }
  original        { TokWord    "original"       }
  name            { TokWord    "name"           }
  promote         { TokWord    "promote"        }
  polyrec         { TokWord    "polyrec"        }
  except          { TokWord    "except"         }
  '='             { TokOp      "="              }
  ':->'           { TokOp      ":->"            }
  -- Tokens: Coq terms
  as              { TokWord    "as"             }
  fun             { TokWord    "fun"            }
  fix             { TokWord    "fix"            }
  cofix           { TokWord    "cofix"          }
  forall          { TokWord    "forall"         }
  match           { TokWord    "match"          }
  end             { TokWord    "end"            }
  struct          { TokWord    "struct"         }
  with            { TokWord    "with"           }
  for             { TokWord    "for"            }
  'measure'       { TokWord    "measure"        }
  'wf'            { TokWord    "wf"             }
  -- Tokens: Coq commands
  'Inductive'     { TokWord    "Inductive"      }
  'CoInductive'   { TokWord    "CoInductive"    }
  'Definition'    { TokWord    "Definition"     }
  'Instance'      { TokWord    "Instance"       }
  'Let'           { TokWord    "Let"            }
  'let'           { TokWord    "let"            }
  'in'            { TokWord    "in"             }
  'Fixpoint'      { TokWord    "Fixpoint"       }
  'CoFixpoint'    { TokWord    "CoFixpoint"     }
  'Local'         { TokWord    "Local"          }
  'Axiom'         { TokWord    "Axiom"          }
  'Theorem'       { TokWord    "Theorem"        }
  'Lemma'         { TokWord    "Lemma"          }
  'Remark'        { TokWord    "Remark"         }
  'Fact'          { TokWord    "Fact"           }
  'Corollary'     { TokWord    "Corollary"      }
  'Proposition'   { TokWord    "Proposition"    }
  'Example'       { TokWord    "Example"        }
  'Proof'         { TokWord    "Proof"          }
  -- Tokens: Coq punctuation
  ':'             { TokOp      ":"              }
  '=>'            { TokOp      "=>"             }
  ':='            { TokOp      ":="             }
  '@'             { TokOp      "@"              }
  '`'             { TokOp      "`"              }
  '.'             { TokOp      "."              }
  '|'             { TokOp      "|"              }
  ','             { TokOp      ","              }
  ';'             { TokOp      ";"              }
  -- Tokens: Ltac punctuation
  '||'            { TokOp      "||"             }
  -- Tokens: General
  '('             { TokOpen    '('              }
  ')'             { TokClose   ')'              }
  '{'             { TokOpen    '{'              }
  '}'             { TokClose   '}'              }
  '_'             { TokWord    "_"              }
  eol             { TokNewline                  }
  Word            { TokWord    $$               }
  Op              { TokOp      $$               }
  Num             { TokNat     $$               }
  StringLit       { TokString  $$               }
  Tactics         { TokTactics $$               }
  ProofEnder      { TokPfEnd   $$               }
-- Tokens: End

%nonassoc GenFixBodyOne
%nonassoc with

-- Get "f x + g y" to parse as "(f x) + (f y)"
%nonassoc Op
%nonassoc ManyR_prec

%%

--------------------------------------------------------------------------------
-- Utility parsers
--------------------------------------------------------------------------------

And(p1,p2)
  : p1 p2    { ($1, $2) }

Or(p1,p2)
  : p1    { Left  $1 }
  | p2    { Right $1 }

AndThen(p1,p2)
  : p1 p2    { $2 }

ManyR(p)
  : {- empty -}     { [] }
  | ManyR(p) p      { $2 : $1 }

Many(p)
  : ManyR(p) %prec ManyR_prec    { reverse $1 }

Some(p)
  : p Many(p)    { $1 :| $2 }

SkipMany(p)
  : {- empty -}      { () }
  | SkipMany(p) p    { () }

SkipSome(p)
  : p SkipMany(p)    { () }

EndByR(p,end)
  : {- empty -}            { [] }
  | EndByR(p,end) p end    { $2 : $1 }

EndBy(p,end) :
  EndByR(p,end)    { reverse $1 }

SepBy1R(p,sep)
  : EndByR(p,sep) p    { $2 :| $1 }

SepBy1(p,sep)
  : SepBy1R(p,sep)    { NEL.reverse $1 }

SepBy(p,sep)
  : OptionalList(SepBy1(p, sep))    { $1 }

SepByIf(intro,p,sep)
  : OptionalList(AndThen(intro, SepBy1(p, sep)))    { $1 }

-- Keep the separator
ExplicitSepBy1(p,sep)
  : p ExplicitBeginBy(p,sep) { ($1, $2) }

ExplicitBeginBy(p,sep)
  : {- empty -} { [] }
  | sep p ExplicitBeginBy(p,sep) { ($1, $2) : $3 }

Optional(p)
  : p              { Just $1 }
  | {- empty -}    { Nothing }

OptionalParens(p)
  : '(' p  ')'     { Just $2 }
  | {- empty -}    { Nothing }

OptionalList(p)
  : Optional(p)    { maybe [] toList $1 }

Lines(p)
  : SkipMany(eol) EndBy(p, SkipSome(eol))    { $2 }

WordOrOp :: { Ident }
  : Word    { $1 }
  | Op      { $1 }

--------------------------------------------------------------------------------
-- Renamings
--------------------------------------------------------------------------------

Namespace :: { HsNamespace }
  : value    { ExprNS }
  | type     { TypeNS }

NamespacedIdent :: { NamespacedIdent }
  : Namespace Qualid    { NamespacedIdent $1 $2 }

Renaming :: { (NamespacedIdent, Qualid) }
  : NamespacedIdent '=' Qualid    { ($1, $3) }

TypeAnnotationOrNot :: { Maybe Term }
  : TypeAnnotation    { Just $1 }
  | no type           { Nothing }

--------------------------------------------------------------------------------
-- Edit commands
--------------------------------------------------------------------------------

TaggedParens(tag) :: { [Qualid] }
 : '(' tag ':' Many(Qualid) ')'    { $4 }

DataTypeArguments :: { DataTypeArguments }
  : TaggedParens(parameters) Optional(TaggedParens(indices))    { DataTypeArguments $1 (fromMaybe [] $2) }
  | TaggedParens(indices)                                       { DataTypeArguments [] $1 }
  | {- empty -}                                                 { DataTypeArguments [] [] }

CoqDefinitionRaw :: { CoqDefinition }
  : Inductive                { CoqInductiveDef  $1 }
  | Definition               { CoqDefinitionDef $1 }
  | Fixpoint                 { CoqFixpointDef   $1 }
  | Instance                 { CoqInstanceDef   $1 }
  | Axiom                    { CoqAxiomDef      $1 }
  | AssertionProof           { CoqAssertionDef  $1 }

CoqDefinition :: { CoqDefinition }
  : Coq(CoqDefinitionRaw) '.'    { $1 }

ScopePlace :: { ScopePlace }
  : constructor    { SPConstructor }
  | value          { SPValue       }

Scope :: { Ident }
  : Word    { $1     }
  | type    { "type" } -- This is so common, we have to special-case it

Edit :: { Edit }
  : type synonym Word ':->' Word                          { TypeSynonymTypeEdit              $3 $5                                 }
  | data type arguments Qualid DataTypeArguments          { DataTypeArgumentsEdit            $4 $5                                 }
  | redefine CoqDefinition                                { RedefinitionEdit                 $2                                    }
  | add type Word CoqDefinition                           { AddEdit                          (mkModuleNameT $3) $4 PhaseTyCl       }
  | add Word CoqDefinition                                { AddEdit                          (mkModuleNameT $2) $3 PhaseTerm       }
  | skip Qualid                                           { SkipEdit                         $2                                    }
  | skip constructor Qualid                               { SkipConstructorEdit              $3                                    }
  | skip class Qualid                                     { SkipClassEdit                    $3                                    }
  | skip method Qualid Word                               { SkipMethodEdit                   $3 $4                                 }
  | skip equation Qualid Some(AtomicPattern)              { SkipEquationEdit                 $3 $4                                 }
  | skip case pattern Pattern                             { SkipCasePatternEdit              $4                                    }
  | skip module Word                                      { SkipModuleEdit                   (mkModuleNameT $3)                    }
  | import module Word                                    { ImportModuleEdit                 (mkModuleNameT $3)                    }
  | manual notation Word                                  { HasManualNotationEdit            (mkModuleNameT $3)                    }
  | termination Qualid TerminationArgument                { TerminationEdit                  $2 $3                                 }
  | obligations Qualid TrivialLtac                        { ObligationsEdit                  $2 $3                                 }
  | rename Renaming                                       { RenameEdit                       (fst $2) (snd $2)                     }
  | axiomatize module Word                                { AxiomatizeModuleEdit             (mkModuleNameT $3)                    }
  | axiomatize original module name Word                  { AxiomatizeOriginalModuleNameEdit (mkModuleNameT $5)                    }
  | axiomatize definition Qualid                          { AxiomatizeDefinitionEdit         $3                                    }
  | unaxiomatize definition Qualid                        { UnaxiomatizeDefinitionEdit       $3                                    }
  | add scope Scope for ScopePlace Qualid                 { AdditionalScopeEdit              $5 $6 $3                              }
  | order Some(Qualid)                                    { OrderEdit                        $2                                    }
  | class kinds Qualid SepBy1(Term,',')                   { ClassKindEdit                    $3 $4                                 }
  | data  kinds Qualid SepBy1(Term,',')                   { DataKindEdit                     $3 $4                                 }
  | delete unused type variables Qualid                   { DeleteUnusedTypeVariablesEdit    $5                                    }
  | coinductive Qualid                                    { CoinductiveEdit                  $2                                    }
  | rewrite Rewrite                                       { RewriteEdit                      $2                                    }
  | rename module Word Word                               { RenameModuleEdit                 (mkModuleNameT $3) (mkModuleNameT $4) }
  | simple class Qualid                                   { SimpleClassEdit                  $3                                    }
  | inline mutual Qualid                                  { InlineMutualEdit                 $3                                    }
  | set type Qualid TypeAnnotationOrNot                   { SetTypeEdit                      $3 $4                                 }
  | collapse 'let' Qualid                                 { CollapseLetEdit                  $3                                    }
  | 'in' Qualid Edit                                      { InEdit                           $2 $3                                 }
  | promote Qualid                                        { PromoteEdit                      $2                                    }
  | polyrec Qualid                                        { PolyrecEdit                      $2                                    }
  | except 'in' SepBy1(Qualid, ',') Edit                  { ExceptInEdit                     $3 $4                                 }

Edits :: { [Edit] }
  : Lines(Edit)    { $1 }

--------------------------------------------------------------------------------
-- Gallina
--------------------------------------------------------------------------------

-- TODO: parse operator names a la _*_
-- TODO: *sometimes* parse () and [] (Haskell) (fixed?)
-- TODO: split qualified and unqualified names

-- Wrap all references to Coq parsing with `Coq(...)` at the top level in order to
-- ignore newlines inside them
Coq(p)
  : EnterCoqParsing p ExitCoqParsing    { $2 }

-- This production is just for side effects
EnterCoqParsing :: { () }
  : {- empty -}    {% put NewlineWhitespace }

-- This production is just for side effects
ExitCoqParsing :: { () }
  : {- empty -}    {% put NewlineSeparators }

Qualid :: { Qualid }
  : WordOrOp   { forceIdentToQualid $1 }

QualOp :: { Qualid }
  : Op   { forceIdentToQualid $1  }
  | '='  { forceIdentToQualid "=" }

EqlessQualOp :: { Qualid }
  : Op   { forceIdentToQualid $1 }

EqlessTerm :: { Term }
  : MediumTerm(EqlessQualOp, EqlessTerm)    { $1 }

Term :: { Term }
  : LargeTerm    { $1 }
  | MediumTerm(QualOp, Term)    { $1 }

LargeTerm :: { Term }
  : fun   Binders '=>' Term     { Fun $2 $4 }
  | fix   FixBodies             { Fix   $2 }
  | cofix FixBodies             { Cofix $2 }
  | forall Binders ',' Term     { Forall $2 $4 }

-- Lets us implement EqlessTerm
MediumTerm(Binop, RTerm) :: { Term }
  : 'let' Qualid Many(Binder) Optional(TypeAnnotation) ':=' Term 'in' RTerm     { Let $2 $3 $4 $6 $8 }
  | SmallishTerm(Binop) ':' RTerm { HasType $1 $3 }
  | SmallishTerm(Binop) { $1 }

-- SmallTerms separated by binary operators
SmallishTerm(Binop) :: { Term }
  : ExplicitSepBy1(SmallTerm, Binop)
    {% uncurry buildSTB $1 }

SmallTerm :: { Term }
  : Atom Many(Arg)           { appList     $1 $2 } -- App or Atom
  | '@' Qualid Many(Atom)    { ExplicitApp $2 $3 }

Arg :: { Arg }
  : '(' Word ':=' Term ')'    { NamedArg $2 $4 }
  | Atom                      { PosArg   $1 }

Atom :: { Term }
  : '(' Term ')'    { $2 }
  | Qualid          { Qualid $1 }
  | Num             { Num $1 }
  | '_'             { Underscore }
  | StringLit       { String $1 }
  | match SepBy1(MatchItem, ',') with Many(Equation) end
                    { Match $2 Nothing $4 }

TypeAnnotation :: { Term }
  : ':' Term    { $2 }

Binders :: { Binders }
  : Some(Binder)    { $1 }

Plicitly(p)
  : '(' p ')'    { (Explicit, $2) }
  | '{' p '}'    { (Implicit, $2) }

-- GenFixBodiesTail(body)
--   : body for Word                       { Right ($1,$3) }
--   | body with GenFixBodiesTail(body)    { Right ($1,$3) }

GenFixBodies(body)
  : body                                    %prec GenFixBodyOne { Left $1 }
  | body with SepBy1(body,with) for Qualid                      { Right ($1,$3,$5) }

FixBodies :: { FixBodies }
  : GenFixBodies(FixBody)    { either FixOne (uncurry3 FixMany) $1 }

FixBody :: { FixBody }
  : Qualid FixBinders Optional(TypeAnnotation) ':=' Term    { uncurry (FixBody $1) $2 $3 $5 }

-- There is an ambiguity between @{implicitVar : ty}@ and @{struct x}@.  Our
-- options are either (a) use right-recursion and incur stack space blowup, or
-- (b) parse any mix of binders and annotations, then parse them out.  I chose
-- option (b).
FixBinders :: { (NonEmpty Binder, Maybe Order) }
  : Some(Or(Binder,Order))
      {% case partitionEithers $ toList $1 of
           (b : bs, [ann]) | isRight (NEL.last $1) -> pure (b :| bs, Just ann)
                           | otherwise             -> parseError "decreasing argument for fixpoint specified too early"
           (b : bs, [])                            -> pure (b :| bs, Nothing)
           ([],     _)                             -> parseError "no binders given for fixpoint"
           (_,      _:_:_)                         -> parseError "too many decreasing arguments given for fixpoint" }

BinderName :: { Name }
  : Qualid    { Ident $1 }
  | '_'     { UnderscoreName }

ExplicitBinderGuts :: { Binder }
  : Some(BinderName) TypeAnnotation   { mkBinders Explicit $1 $2 }

ImplicitBinderGuts :: { Binder }
  : Some(BinderName)                  { ImplicitBinders $1 }
  | Some(BinderName) TypeAnnotation   { mkBinders Implicit $1 $2 }

-- Generalizable binders have an ambiguous syntax:
--
-- > `{ x : t }
--
-- where x is a single variable or an underscore, and t is a term; or:
--
-- > `{ t }
--
-- where t is a term (which should be a type class, possibly with quantifiers in front).
--
-- Below, we just parse the more general syntax @`{ t }@, and fix the special case
-- afterwards, since it gets parsed as a type annotation (@HasType@).
GeneralizableBinderGuts :: { Explicitness -> Binder }
  : Term
    { \ei -> case $1 of
        { HasType (Qualid name) t -> Typed Generalizable ei (pure (Ident name))   t
        ; HasType Underscore    t -> Typed Generalizable ei (pure UnderscoreName) t
        ; t -> Generalized ei t
        }
    }

Binder :: { Binder }
  : BinderName                        { ExplicitBinder $1 }
  | '(' ExplicitBinderGuts ')'        { $2 }
  | '{' ImplicitBinderGuts '}'        { $2 }
  | '`' '(' GeneralizableBinderGuts ')'    { $3 Explicit }
  | '`' '{' GeneralizableBinderGuts '}'    { $3 Implicit }

MutualDefinitions(p)
  : SepBy1(p, with)    { ($1, []) }

MatchItem :: { MatchItem }
  : Term                 { MatchItem $1 Nothing Nothing }

Equation :: { Equation }
  : Some(MultPattern) '=>' Term  { Equation $1 $3 }

MultPattern :: { MultPattern }
  : '|' SepBy1(Pattern,',')           { MultPattern $2 }

-- There is some code-smell here: It parses constructors without
-- arguments as variables. We could hard-code common nullary constructors.
-- But can we do better?
Pattern :: { Pattern }
  : Qualid Some(AtomicPattern)        { ArgsPat $1 (NEL.toList $2) }
  | '@' Qualid Some(AtomicPattern)    { ExplicitArgsPat $2 $3 }
  | Pattern as Qualid                 { AsPat $1 $3 }
  | AtomicPattern                     { $1 }

AtomicPattern :: { Pattern }
  : '_'                { UnderscorePat }
  | Num                { NumPat $1 }
  | Qualid             { QualidPat $1  }
  | '(' Pattern ')'    { $2 }

Rewrite :: { Rewrite }
  : forall Many(Word) ',' EqlessTerm '=' Term    { Rewrite $2 $4 $6 }

--------------------------------------------------------------------------------
-- Vernacular
--------------------------------------------------------------------------------

Sentence :: { Sentence }
  : SentenceBody '.'    { $1 }

SentenceBody :: { Sentence }
  : Inductive    { InductiveSentence $1 }

Inductive :: { Inductive }
  : 'Inductive'   MutualDefinitions(IndBody)    { uncurry Inductive   $2 }
  | 'CoInductive' MutualDefinitions(IndBody)    { uncurry CoInductive $2 }

IndBody :: { IndBody }
  : Qualid Many(Binder) Optional(TypeAnnotation) ':=' Constructors    { IndBody $1 $2 (fromMaybe (Sort Type) $3) $5 }

Constructors :: { [(Qualid, [Binder], Maybe Term)] }
  : SepByIf(Optional('|'), Constructor, '|')    { $1 }

Constructor :: { (Qualid, [Binder], Maybe Term) }
  : Qualid Many(Binder) Optional(TypeAnnotation)    { ($1, $2, $3) }

Locality :: { Locality }
  : Optional('Local')    { ifMaybe $1 Local Global }

Definition :: { Definition }
  : Locality 'Definition' Qualid Many(Binder) Optional(TypeAnnotation) ':=' Term    { DefinitionDef $1 $3 $4 $5 $7 NotExistingClass }
  |          'Let'        Qualid Many(Binder) Optional(TypeAnnotation) ':=' Term    { LetDef           $2 $3 $4 $6 }

Fixpoint :: { Fixpoint }
  : 'Fixpoint'   MutualDefinitions(FixBody)    { uncurry Fixpoint   $2 }
  | 'CoFixpoint' MutualDefinitions(FixBody)    { uncurry CoFixpoint $2 }

Order :: { Order }
  : '{' struct Qualid '}'                          { StructOrder $3 }
  | '{' 'measure' Atom OptionalParens(Term) '}'    { MeasureOrder $3 $4 }
  | '{' 'wf' Atom Qualid '}'                       { WFOrder $3 $4 }

TerminationArgument :: { TerminationArgument }
  : 'deferred'    { Deferred }
  | 'corecursive' { Corecursive }
  | Order         { fromOrder $1 }
  | '{' struct Num '}' { StructOrderTA (StructPos_ (fromIntegral $3)) }

Instance :: { InstanceDefinition }
  : 'Instance' Qualid Many(Binder) TypeAnnotation ':=' '{' SepBy(FieldDefinition, ';')  '}'
  { InstanceDefinition $2 $3 $4 $7 Nothing }
  | 'Instance' Qualid Many(Binder) TypeAnnotation ':=' Term
  { InstanceTerm $2 $3 $4 $6 Nothing }

FieldDefinition :: { (Qualid,Term) }
  : Qualid ':=' Term  { ($1 , $3) }

Axiom :: { (Qualid, Term) }
  : 'Axiom' Qualid TypeAnnotation    { ($2, $3) }

-- We don't include 'Definition' -- it causes parsing conflicts, and really
-- isn't necessary here.
AssertionKeyword :: { AssertionKeyword }
  : 'Theorem'     { Theorem     }
  | 'Lemma'       { Lemma       }
  | 'Remark'      { Remark      }
  | 'Fact'        { Fact        }
  | 'Corollary'   { Corollary   }
  | 'Proposition' { Proposition }
  | 'Example'     { Example     }

Assertion :: { Assertion }
  : AssertionKeyword Qualid Many(Binder) TypeAnnotation    { Assertion $1 $2 $3 $4 }

AssertionProof :: { (Assertion, Proof) }
  : Assertion '.' 'Proof' RequestTactics '.'  Tactics ProofEnder     { ($1, proof (prechomp $6) $7) }
-- OK, I don't know why putting `RequestTactics` before the `'.'` works, but it does.  Lookahead?

-- This production is just for side effects
RequestTactics :: { () }
  : {- empty -}    {% requestTactics }

--------------------------------------------------------------------------------
-- Trivial tactics
--------------------------------------------------------------------------------

TrivialLtac :: { Tactics }
  : LtacCmd Many(And(LtacSep, LtacCmd))    { $1 <> T.concat (map (uncurry (<>)) $2) }

LtacCmd :: { Tactics }
  : LtacApp          { $1 }
  | LtacAtom         { $1 }

LtacApp :: { Tactics }
  : LtacAtom Some(LtacAtom)    { $1 <> " " <> T.unwords (toList $2) }

LtacAtom :: { Tactics }
  : '(' TrivialLtac ')'    { "(" <> $2 <> ")"        }
  | Qualid                 { qualidToIdent $1        }
  | '@' Qualid             { "@" <> qualidToIdent $2 }
  | Num                    { T.pack (show $1)        }
  | '_'                    { "_"                     }

LtacSep :: { Tactics }
  : ';'     { "; "   }
  | '||'    { " || " }

--------------------------------------------------------------------------------
-- Haskell code
--------------------------------------------------------------------------------

{
ifMaybe :: Maybe a -> b -> b -> b
ifMaybe (Just _)  j _n = j
ifMaybe Nothing  _j  n = n

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f = \(a,b,c) -> f a b c

unexpected :: MonadParse m => Token -> m a
unexpected tok = parseError $ "unexpected " ++ tokenDescription tok

forceIdentToQualid :: Ident -> Qualid
forceIdentToQualid x = fromMaybe (error $ "internal error: lexer produced a malformed qualid: " ++ show x) (identToQualid x)

prechomp :: T.Text -> T.Text
prechomp t = case T.stripPrefix "\n" t of
               Just t' -> t'
               Nothing -> t

buildSTB :: MonadParse m => Term -> [(Qualid, Term)] -> m Term
buildSTB t b = do
  let (ambig, t1) = buildSTB' t b
  unless (null ambig) . parseError $
    "ambiguous expression, mixing operators " ++ show (qualidToOp' <$> snub ambig) ++ ": " ++ showP t
  pure t1

qualidToOp' :: Qualid -> Op
qualidToOp' x = fromMaybe (error $ "internal error: malformed qualid (should be an op): " ++ show x) (qualidToOp x)

snub :: Ord a => [a] -> [a]
snub = S.toList . S.fromList

buildSTB' :: Term -> [(Qualid, Term)] -> ([Qualid], Term)
buildSTB' t suffix =
  case more_ of
    [] -> (ambig, t0)
    (_, tmore) : more ->
      let (ambig1, t1) = buildSTB' tmore more in
      (ambig ++ ambig1, Arrow t0 t1)
  where
    ambig = case operands of
      [] -> []
      [_] -> []
      _ : _ : _ -> fmap fst operands
    (operands, more_) = span (\(op, _) -> op /= "->") suffix
    t0 = foldl (\t0 (op, t1) -> mkInfix t0 op t1) t operands
}
