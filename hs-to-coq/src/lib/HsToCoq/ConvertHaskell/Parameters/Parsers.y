{
{-# LANGUAGE TupleSections, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Parameters.Parsers (
  parseTerm, parseSentence, parseRenamingList, parseEditList
) where

import Data.Foldable
import Data.Maybe
import Data.Either
import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NEL

import Control.Monad.Except
import Control.Monad.Trans.Parse

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing
}

%name      parseTerm         Term
%name      parseSentence     Sentence
%name      parseRenamingList Renamings
%name      parseEditList     Edits

%tokentype { Token }
%error     { unexpected }

%monad { Parse }
%lexer { (=<< token) } { TokEOF }

%token
  value         { TokWord    "value"       }
  type          { TokWord    "type"        }
  data          { TokWord    "data"        }
  synonym       { TokWord    "synonym"     }
  arguments     { TokWord    "arguments"   }
  parameters    { TokWord    "parameters"  }
  indices       { TokWord    "indices"     }
  redefine      { TokWord    "redefine"    }
  skip          { TokWord    "skip"        }
  rename        { TokWord    "rename"      }
  module        { TokWord    "module"      }
  add           { TokWord    "add"         }
  scope         { TokWord    "scope"       }
  constructor   { TokWord    "constructor" }
  fun           { TokWord    "fun"         }
  fix           { TokWord    "fix"         }
  cofix         { TokWord    "cofix"       }
  struct        { TokWord    "struct"      }
  with          { TokWord    "with"        }
  for           { TokWord    "for"         }
  where         { TokWord    "where"       }
  and           { TokWord    "and"         }
  'Inductive'   { TokWord    "Inductive"   }
  'CoInductive' { TokWord    "CoInductive" }
  'Definition'  { TokWord    "Definition"  }
  'Let'         { TokWord    "Let"         }
  'Fixpoint'    { TokWord    "Fixpoint"    }
  'CoFixpoint'  { TokWord    "CoFixpoint"  }
  'Local'       { TokWord    "Local"       }
  '='           { TokOp      "="           }
  ':->'         { TokOp      ":->"         }
  ':'           { TokOp      ":"           }
  '=>'          { TokOp      "=>"          }
  ':='          { TokOp      ":="          }
  '@'           { TokOp      "@"           }
  '`'           { TokOp      "`"           }
  '.'           { TokOp      "."           }
  '|'           { TokOp      "|"           }
  '"'           { TokOp      "\""          }
  '\''          { TokOp      "'"           }
  '('           { TokOpen    '('           }
  ')'           { TokClose   ')'           }
  '{'           { TokOpen    '{'           }
  '}'           { TokClose   '}'           }
  eol           { TokNewline               }
  Word          { TokWord    $$            }
  Op            { TokOp      $$            }
  Num           { TokNat     $$            }

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
  : Namespace WordOrOp    { NamespacedIdent $1 $2 }

Renaming :: { (NamespacedIdent, Ident) }
  : NamespacedIdent '=' WordOrOp    { ($1, $3) }

Renamings :: { [(NamespacedIdent, Ident)] }
  : Lines(Renaming)    { $1 }

--------------------------------------------------------------------------------
-- Edit commands
--------------------------------------------------------------------------------

TaggedParens(tag) :: { [Ident] }
 : '(' tag ':' Many(Word) ')'    { $4 }

DataTypeArguments :: { DataTypeArguments }
  : TaggedParens(parameters) Optional(TaggedParens(indices))    { DataTypeArguments $1 (fromMaybe [] $2) }
  | TaggedParens(indices)                                       { DataTypeArguments [] $1 }
  | {- empty -}                                                 { DataTypeArguments [] [] }

CoqDefinition :: { CoqDefinition }
  : Inductive    { CoqInductiveDef   $1 }
  | Definition   { CoqDefinitionDef  $1 }
  | Fixpoint     { CoqFixpointDef    $1 }

ScopePlace :: { ScopePlace }
  : constructor    { SPConstructor }
  | value          { SPValue       }

Scope :: { Ident }
  : Word    { $1     }
  | type    { "type" } -- This is so common, we have to special-case it

Edit :: { Edit }
  : type synonym Word ':->' Word                  { TypeSynonymTypeEdit   $3 $5                }
  | data type arguments Word DataTypeArguments    { DataTypeArgumentsEdit $4 $5                }
  | redefine CoqDefinition Optional('.')          { RedefinitionEdit      $2                   }
  | skip Word                                     { SkipEdit              $2                   }
  | skip Op                                       { SkipEdit              $2                   }
  | rename module WordOrOp Renaming               { ModuleRenamingEdit    $3 (fst $4) (snd $4) }
  | add scope Scope for ScopePlace Word           { AdditionalScopeEdit   $5 $6 $3             }

Edits :: { [Edit] }
  : Lines(Edit)    { $1 }

--------------------------------------------------------------------------------
-- Gallina
--------------------------------------------------------------------------------

-- TODO: parse operator names à la _*_
-- TODO: *sometimes* ignore \n (Coq)
-- TODO: *sometimes* parse () and [] (Haskell) (fixed?)
-- TODO: split qualified and unqualified names

Term :: { Term }
  : LargeTerm    { $1 }
  | App          { $1 }
  | Atom         { $1 }

LargeTerm :: { Term }
  : fun   Binders '=>' Term    { Fun $2 $4 }
  | fix   FixBodies            { Fix   $2 }
  | cofix CofixBodies          { Cofix $2 }
  | Atom Op Atom               { if $2 == "->" then Arrow $1 $3 else Infix $1 $2 $3 }

App :: { Term }
  :     Atom Some(Arg)     { App $1 $2 }
  | '@' Word Many(Atom)    { ExplicitApp (forceIdentToQualid $2) $3 }

Arg :: { Arg }
  : '(' Word ':=' Term ')'    { NamedArg $2 $4 }
  | Atom                      { PosArg   $1 }

Atom :: { Term }
  : '(' Term ')'    { $2 }
  | Word            { Qualid (forceIdentToQualid $1) }
  | Num             { Num $1 }

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
  | body with SepBy1(body,with) for Word                        { Right ($1,$3,$5) }

FixBodies :: { FixBodies }
  : GenFixBodies(FixBody)    { either FixOne (uncurry3 FixMany) $1 }

CofixBodies :: { CofixBodies }
  : GenFixBodies(CofixBody)    { either CofixOne (uncurry3 CofixMany) $1 }

FixBody :: { FixBody }
  : Word FixBinders Optional(TypeAnnotation) ':=' Term    { uncurry (FixBody $1) $2 $3 $5 }

CofixBody :: { CofixBody }
  : Word Binders Optional(TypeAnnotation) ':=' Term    { CofixBody $1 $2 $3 $5 }

Annotation :: { Annotation }
  : '{' struct Word '}'    { Annotation $3 }

-- There is an ambiguity between @{implicitVar : ty}@ and @{struct x}@.  Our
-- options are either (a) use right-recursion and incur stack space blowup, or
-- (b) parse any mix of binders and annotations, then parse them out.  I chose
-- option (b).
FixBinders :: { (NonEmpty Binder, Maybe Annotation) }
  : Some(Or(Binder,Annotation))
      {% case partitionEithers $ toList $1 of
           (b : bs, [ann]) | isRight (NEL.last $1) -> pure (b :| bs, Just ann)
                           | otherwise             -> throwError "decreasing argument for fixpoint specified too early"
           (b : bs, [])                            -> pure (b :| bs, Nothing)
           ([],     _)                             -> throwError "no binders given for fixpoint"
           (_,      _:_:_)                         -> throwError "too many decreasing arguments given for fixpoint" }

-- TODO: Use a _ token?
BinderName :: { Name }
  : Word    { if $1 == "_" then UnderscoreName else Ident $1 }

ExplicitBinderGuts :: { Binder }
  : BinderName                                        { Inferred Explicit $1 }
  | BinderName Some(BinderName) TypeAnnotation        { Typed Ungeneralizable Explicit ($1 <| $2) $3 }
  | BinderName BinderColonEq                          { BindLet $1 Nothing $2 }
  | BinderName TypeAnnotation Optional(BinderColonEq)
      { case $3 of
          Just def -> BindLet $1 (Just $2) def
          Nothing  -> Typed Ungeneralizable Explicit ($1 :| []) $2 }

BinderColonEq
  : ':=' Term    { $2 }

ImplicitBinderGuts :: { Binder }
  : BinderName                         { Inferred Implicit $1 }
  | Some(BinderName) TypeAnnotation    { Typed Ungeneralizable Implicit $1 $2 }

GeneralizableBinderGuts :: { Explicitness -> Binder }
  : Atom                            { \ei -> Generalized ei $1 }
  | Some(BinderName) TypeAnnotation { \ei -> Typed Generalizable ei $1 $2 }

Binder :: { Binder }
  : BinderName                        { Inferred Explicit $1 }
  | '(' ExplicitBinderGuts ')'        { $2 }
  | '{' ImplicitBinderGuts '}'        { $2 }
  | '`' '(' GeneralizableBinderGuts ')'    { $3 Explicit }
  | '`' '{' GeneralizableBinderGuts '}'    { $3 Implicit }

MutualDefinitions(p)
  : SepBy1(p, with) SepByIf(where, NotationBinding, and)    { ($1, $2) }

NotationBinding :: { NotationBinding }
  : '"' '\'' Word '\'' '"' ':=' Term    { NotationIdentBinding $3 $7 }

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
  : Word Many(Binder) Optional(TypeAnnotation) ':=' Constructors    { IndBody $1 $2 (fromMaybe (Sort Type) $3) $5 }

Constructors :: { [(Ident, [Binder], Maybe Term)] }
  : SepByIf(Optional('|'), Constructor, '|')    { $1 }

Constructor :: { (Ident, [Binder], Maybe Term) }
  : Word Many(Binder) Optional(TypeAnnotation)    { ($1, $2, $3) }

Locality :: { Locality }
  : Optional('Local')    { ifMaybe $1 Local Global }

Definition :: { Definition }
  : Locality 'Definition' Word Many(Binder) Optional(TypeAnnotation) ':=' Term    { DefinitionDef $1 $3 $4 $5 $7 }
  |          'Let'        Word Many(Binder) Optional(TypeAnnotation) ':=' Term    { LetDef           $2 $3 $4 $6 }

Fixpoint :: { Fixpoint }
  : 'Fixpoint'   MutualDefinitions(FixBody)      { uncurry Fixpoint   $2 }
  | 'CoFixpoint' MutualDefinitions(CofixBody)    { uncurry CoFixpoint $2 }

--------------------------------------------------------------------------------
-- Haskell code
--------------------------------------------------------------------------------

{
ifMaybe :: Maybe a -> b -> b -> b
ifMaybe (Just _)  j _n = j
ifMaybe Nothing  _j  n = n

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f = \(a,b,c) -> f a b c

unexpected :: Monad m => Token -> ParseT m a
unexpected tok = throwError $ "unexpected " ++ tokenDescription tok

forceIdentToQualid :: Ident -> Qualid
forceIdentToQualid = fromMaybe (error "internal error: lexer produced a malfored qualid!") . identToQualid
}
