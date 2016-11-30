{
{-# LANGUAGE OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Parameters.Parsers (
  parseTerm, parseRenamingList, parseEditList
) where

import Data.Maybe
import Control.Monad.Except
import Control.Monad.Trans.Parse
import Data.List.NonEmpty (NonEmpty(..), (<|))

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing
}

%name      parseTerm         Term
%name      parseRenamingList Renamings
%name      parseEditList     Edits

%tokentype { Token }
%error     { unexpected }

%monad { Parse }
%lexer { (=<< token) } { TokEOF }
 
%token
  value         { TokWord    "value"      }
  type          { TokWord    "type"       }
  data          { TokWord    "data"       }
  synonym       { TokWord    "synonym"    }
  arguments     { TokWord    "arguments"  }
  parameters    { TokWord    "parameters" }
  indices       { TokWord    "indices"    }
  fun           { TokWord    "fun"        }
  '='           { TokOp      "="          }
  ':->'         { TokOp      ":->"        }
  ':'           { TokOp      ":"          }
  '=>'          { TokOp      "=>"         }
  ':='          { TokOp      ":="         }
  '@'           { TokOp      "@"          }
  '`'           { TokOp      "`"          }
  '.'           { TokOp      "."          }
  '('           { TokOpen    '('          }
  ')'           { TokClose   ')'          }
  '['           { TokOpen    '['          }
  ']'           { TokClose   ']'          }
  '{'           { TokOpen    '{'          }
  '}'           { TokClose   '}'          }
  eol           { TokNewline              }
  Word          { TokWord    $$           }
  Op            { TokOp      $$           }
  Num           { TokNat     $$           }

%%

--------------------------------------------------------------------------------
-- Utility parsers
--------------------------------------------------------------------------------

And(p1,p2)
  : p1 p2    { ($1, $2) }

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

SkipSome(p) :
  p SkipMany(p)    { () }

EndByR(p,end)
  : {- empty -}            { [] }
  | EndByR(p,end) p end    { $2 : $1 }

EndBy(p,end) :
  EndByR(p,end)    { reverse $1 }

Optional(p)
  : p              { Just $1 }
  | {- empty -}    { Nothing }

Lines(p)
  : SkipMany(eol) EndBy(p, SkipSome(eol))    { $2 }

--------------------------------------------------------------------------------
-- Renamings
--------------------------------------------------------------------------------

Namespace :: { HsNamespace }
  : value    { ExprNS }
  | type     { TypeNS }

RawHsIdent :: { Ident }
  : Qualid     { qualidToIdent $1 }
  | Op         { $1   }
  | ':'        { ":"  } -- TODO: Remove special case here?
  | '(' ')'    { "()" }
  | '[' ']'    { "[]" }

NamespacedIdent :: { NamespacedIdent }
  : Namespace RawHsIdent { NamespacedIdent $1 $2 }

Renaming :: { (NamespacedIdent, Ident) }
  : NamespacedIdent '=' Word    { ($1, $3) }
  | NamespacedIdent '=' Op      { ($1, $3) }

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

Edit :: { Edit }
  : type synonym Word ':->' Word                  { TypeSynonymTypeEdit   $3 $5 }
  | data type arguments Word DataTypeArguments    { DataTypeArgumentsEdit $4 $5 }

Edits :: { [Edit] }
  : Lines(Edit)    { $1 }

--------------------------------------------------------------------------------
-- Gallina
--------------------------------------------------------------------------------

-- TODO: parse operator names à la _*_
-- TODO: *sometimes* ignore \n (Coq)
-- TODO: *sometimes* parse () and [] (Haskell)

Term :: { Term }
  : LargeTerm    { $1 }
  | App          { $1 }
  | Atom         { $1 }

LargeTerm :: { Term }
  : fun Binders '=>' Term    { Fun $2 $4 }
  | Atom Op Atom             { if $2 == "->" then Arrow $1 $3 else Infix $1 $2 $3 }

App :: { Term }
  :     Atom   Some(Arg)     { App $1 $2 }
  | '@' Qualid Many(Atom)    { ExplicitApp $2 $3 }

Arg :: { Arg }
  : '(' Word ':=' Term ')'    { NamedArg $2 $4 }
  | Atom                      { PosArg   $1 }

Qualid :: { Qualid }
  : Word               { Bare $1 }
  | Qualid '.' Word    { Qualified $1 $3 }

Atom :: { Term }
  : '(' Term ')'    { $2 }
  | Qualid          { Qualid $1 }
  | Num             { Num $1 }

TypeAnnotation :: { Term }
  : ':' Term    { $2 }

Binders :: { Binders }
  : Some(Binder)    { $1 }

Plicitly(p)
  : '(' p ')'    { (Explicit, $2) }
  | '{' p '}'    { (Implicit, $2) }

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

{
ifMaybe :: Maybe a -> b -> b -> b
ifMaybe (Just _)  j _n = j
ifMaybe Nothing  _j  n = n

unexpected :: Monad m => Token -> ParseT m a
unexpected tok = throwError $ "unexpected " ++ tokenDescription tok
}
