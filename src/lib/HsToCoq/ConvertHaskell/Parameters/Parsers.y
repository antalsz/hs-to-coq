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

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Parse

import GHC (mkModuleName)

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Orphans ()

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing
}

%name      parseTerm         Term
%name      parseSentence     Sentence
%name      parseEditList     Edits

%tokentype { Token }
%error     { unexpected }

%monad { NewlinesParse }
%lexer { (=<< token) } { TokEOF }

%token
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
  axiomatize      { TokWord    "axiomatize"     }
  termination     { TokWord    "termination"    }
  'deferred'      { TokWord    "deferred"       }
  'corecursive'   { TokWord    "corecursive"    }
  obligations     { TokWord    "obligations"    }
  method          { TokWord    "method"         }
  rename          { TokWord    "rename"         }
  rewrite         { TokWord    "rewrite"        }
  order           { TokWord    "order"          }
  module          { TokWord    "module"         }
  add             { TokWord    "add"            }
  scope           { TokWord    "scope"          }
  constructor     { TokWord    "constructor"    }
  fun             { TokWord    "fun"            }
  fix             { TokWord    "fix"            }
  cofix           { TokWord    "cofix"          }
  forall          { TokWord    "forall"         }
  match           { TokWord    "match"          }
  end             { TokWord    "end"            }
  struct          { TokWord    "struct"         }
  with            { TokWord    "with"           }
  for             { TokWord    "for"            }
  where           { TokWord    "where"          }
  and             { TokWord    "and"            }
  coinductive     { TokWord    "coinductive"    }
  'measure'       { TokWord    "measure"        }
  'wf'            { TokWord    "wf"             }
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
  '='             { TokOp      "="              }
  ':->'           { TokOp      ":->"            }
  ':'             { TokOp      ":"              }
  '=>'            { TokOp      "=>"             }
  ':='            { TokOp      ":="             }
  '@'             { TokOp      "@"              }
  '`'             { TokOp      "`"              }
  '.'             { TokOp      "."              }
  '|'             { TokOp      "|"              }
  '\''            { TokOp      "'"              }
  ','             { TokOp      ","              }
  ';'             { TokOp      ";"              }
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

%nonassoc GenFixBodyOne
%nonassoc with

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
  : ManyR(p)    { reverse $1 }

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
  : Inductive       { CoqInductiveDef       $1 }
  | Definition      { CoqDefinitionDef      $1 }
  | Fixpoint        { CoqFixpointDef        $1 }
  | Instance        { CoqInstanceDef        $1 }

CoqDefinition :: { CoqDefinition }
  : Coq(CoqDefinitionRaw) '.' { $1 }

ScopePlace :: { ScopePlace }
  : constructor    { SPConstructor }
  | value          { SPValue       }

Scope :: { Ident }
  : Word    { $1     }
  | type    { "type" } -- This is so common, we have to special-case it

Edit :: { Edit }
  : type synonym Word ':->' Word                     { TypeSynonymTypeEdit   $3 $5                            }
  | data type arguments Qualid DataTypeArguments     { DataTypeArgumentsEdit $4 $5                            }
  | redefine CoqDefinition                           { RedefinitionEdit      $2                               }
  | add Word CoqDefinition                           { AddEdit               (mkModuleName (T.unpack $2)) $3  }
  | skip Qualid                                      { SkipEdit              $2                               }
  | skip method Qualid Word                          { SkipMethodEdit        $3 $4                            }
  | skip module Word                                 { SkipModuleEdit        (mkModuleName (T.unpack $3))     }
  | import module Word                               { ImportModuleEdit      (mkModuleName (T.unpack $3))     }
  | manual notation Word                             { HasManualNotationEdit (mkModuleName (T.unpack $3))     }
  | termination Qualid TerminationArgument           { TerminationEdit       $2 $3                            }
  | obligations Qualid Word                          { ObligationsEdit       $2 $3 }
  | rename Renaming                                  { RenameEdit            (fst $2) (snd $2)                }
  | axiomatize module Word                           { AxiomatizeModuleEdit  (mkModuleName (T.unpack $3))     }
  | add scope Scope for ScopePlace Qualid            { AdditionalScopeEdit   $5 $6 $3                         }
  | order Some(Qualid)                               { OrderEdit             $2                               }
  | class kinds Qualid SepBy1(Term,',')              { ClassKindEdit         $3 $4                            }
  | data  kinds Qualid SepBy1(Term,',')              { DataKindEdit          $3 $4                            }
  | coinductive Qualid                               { CoinductiveEdit       $2                               }
  | rewrite Rewrite                                  { RewriteEdit           $2                               }
  | rename module Word Word                          { RenameModuleEdit      (mkModuleName (T.unpack $3))
                                                                             (mkModuleName (T.unpack $4))     }
  | 'in' Qualid Edit                                 { InEdit                $2 $3                            }

Edits :: { [Edit] }
  : Lines(Edit)    { $1 }

--------------------------------------------------------------------------------
-- Gallina
--------------------------------------------------------------------------------

-- TODO: parse operator names à la _*_
-- TODO: *sometimes* parse () and [] (Haskell) (fixed?)
-- TODO: split qualified and unqualified names

-- Wrap all references to Coq parsing with `Coq(…)` at the top level in order to
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
  : Op   { forceIdentToQualid $1 }

Term :: { Term }
  : LargeTerm    { $1 }
  | App          { $1 }
  | Atom         { $1 }

LargeTerm :: { Term }
  : fun   Binders '=>' Term    { Fun $2 $4 }
  | fix   FixBodies            { Fix   $2 }
  | cofix FixBodies            { Cofix $2 }
  | forall Binders ',' Term    { Forall $2 $4 }
  | 'let' Qualid Many(Binder) Optional(TypeAnnotation) ':=' Term 'in' Term
	 { Let $2 $3  $4 $6 $8 }
  | match SepBy1(MatchItem, ',') with Many(Equation) end { Match $2 Nothing $4 }
  | Atom QualOp Atom           { if $2 == "->" then Arrow $1 $3 else mkInfix $1 $2 $3 }

App :: { Term }
  :     Atom Some(Arg)     { App $1 $2 }
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
                           | otherwise             -> throwError "decreasing argument for fixpoint specified too early"
           (b : bs, [])                            -> pure (b :| bs, Nothing)
           ([],     _)                             -> throwError "no binders given for fixpoint"
           (_,      _:_:_)                         -> throwError "too many decreasing arguments given for fixpoint" }

BinderName :: { Name }
  : Qualid    { Ident $1 }
  | '_'     { UnderscoreName }

ExplicitBinderGuts :: { Binder }
  : BinderName                                        { Inferred Explicit $1 }
  | BinderName Some(BinderName) TypeAnnotation        { Typed Ungeneralizable Explicit ($1 <| $2) $3 }
  | BinderName TypeAnnotation                         { Typed Ungeneralizable Explicit ($1 :| []) $2 }

BinderColonEq
  : ':=' Term    { $2 }

ImplicitBinderGuts :: { Binder }
  : BinderName                         { Inferred Implicit $1 }
  | Some(BinderName) TypeAnnotation    { Typed Ungeneralizable Implicit $1 $2 }

GeneralizableBinderGuts :: { Explicitness -> Binder }
  : '(' Term ')'                    { \ei -> Generalized ei $2 }
  | Some(BinderName) TypeAnnotation { \ei -> Typed Generalizable ei $1 $2 }

Binder :: { Binder }
  : BinderName                        { Inferred Explicit $1 }
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
  : Qualid Some(AtomicPattern) { ArgsPat $1 (NEL.toList $2) }
  | AtomicPattern              { $1 }

AtomicPattern :: { Pattern }
  : '_'                     { UnderscorePat }
  | Num                     { NumPat $1 }
  | Qualid                  { QualidPat $1  }
  | '(' Pattern ')'         { $2 }

Rewrite :: { Rewrite }
  : forall Many(Word) ',' Term '=' Term  { Rewrite $2 $4 $6 }

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
  : Locality 'Definition' Qualid Many(Binder) Optional(TypeAnnotation) ':=' Term    { DefinitionDef $1 $3 $4 $5 $7 }
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
  | Order         { WellFounded $1 }

Instance :: { InstanceDefinition }
  : 'Instance' Qualid Many(Binder) TypeAnnotation ':=' '{' SepBy(FieldDefinition, ';')  '}'
  { InstanceDefinition $2 $3 $4 $7 Nothing }
  | 'Instance' Qualid Many(Binder) TypeAnnotation ':=' Term
  { InstanceTerm $2 $3 $4 $6 Nothing }

FieldDefinition :: { (Qualid,Term) }
  : Qualid ':=' Term  { ($1 , $3) }

--------------------------------------------------------------------------------
-- Haskell code
--------------------------------------------------------------------------------

{
ifMaybe :: Maybe a -> b -> b -> b
ifMaybe (Just _)  j _n = j
ifMaybe Nothing  _j  n = n

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f = \(a,b,c) -> f a b c

unexpected :: Token -> NewlinesParse a
unexpected tok = throwError $ "unexpected " ++ tokenDescription tok

forceIdentToQualid :: Ident -> Qualid
forceIdentToQualid x = fromMaybe (error $ "internal error: lexer produced a malfored qualid: " ++ show x) (identToQualid x)
}
