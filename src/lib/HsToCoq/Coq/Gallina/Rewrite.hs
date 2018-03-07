{-|
Module      : HsToCoq.Coq.Gallina.Rewrite
Description : Rewrite rule enginge for the Gallina AST
Copyright   : Copyright © 2018 Joachim Breitner
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental

This module implements rewrite rules. So far, this is straight forward and
not very efficiently.

Efficiency of finding a rewrite rule (candidate) could be greatly improved by
 * sorting the rewrite rules into a map, based on the outermost functions.
 * implementing an actual trie
This can be relevant when the numer of rewrite rules increases.

Another improvemet would be to detect bad patterns (non-linear ones,
unsupported AST nodes) and report such errors upon parsing.
-}

{-# LANGUAGE OverloadedLists #-}
module HsToCoq.Coq.Gallina.Rewrite (Rewrite(..), Rewrites, rewrite) where

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Trans.Writer.Strict
import Control.Monad
import Data.Foldable

import HsToCoq.Coq.Subst
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

data Rewrite = Rewrite
    { patternVars :: [Ident]
    , lhs :: Term
    , rhs :: Term
    }
  deriving (Eq, Ord, Show)

-- | This could be replaced by something more efficient, if needed.
-- See comments in HsToCoq.Coq.Gallina.Rewrite.
type Rewrites = [Rewrite]

-- | Applies all rewrite rules that match at the root of the given term.
rewrite :: Rewrites -> Term -> Term
rewrite rws t = foldl' (flip rewrite1) t rws

rewrite1 :: Rewrite -> Term -> Term
rewrite1 (Rewrite patVars lhs rhs) term
    | Just s <- match patVars lhs term
    = subst s rhs
    | otherwise
    = term

-- | Normalizes the outermost constructor
-- (Maybe we should drop InFix completely)
norm :: Term -> Term
norm (HsString s) = String s
norm t | Just (f, args) <- collectArgs t = appList (Qualid f) (map PosArg args)
norm t = t

match :: [Ident] -> Term -> Term -> Maybe (M.Map Qualid Term)
match patVars lhs term = execWriterT (go lhs term)
  where
    isPatVar = (`S.member` S.fromList patVars)

    go :: Term -> Term -> WriterT (M.Map Qualid Term) Maybe ()
    go lhs term = go' (norm lhs) (norm term)

    go' :: Term -> Term -> WriterT (M.Map Qualid Term) Maybe ()
    go' (String s1) (String s2) = guard (s1 == s2)
    go' (Qualid qid@(Bare v)) t | isPatVar v = do
        tell (M.singleton qid t)
        return ()
    go' (Qualid pqid) (Qualid qid) = guard (pqid == qid)
    go' (App pf pa) (App f a) = do
        guard (length pa == length a)
        go pf f
        zipWithM_ goA (toList pa) (toList a)
    go' _lhs _term = mzero

    goA :: Arg -> Arg -> WriterT (M.Map Qualid Term) Maybe ()
    goA (PosArg pt) (PosArg p) = go pt p
    goA (NamedArg pi pt) (NamedArg i p) = do
        guard (pi == i)
        go pt p
    goA _lhs _term = mzero
