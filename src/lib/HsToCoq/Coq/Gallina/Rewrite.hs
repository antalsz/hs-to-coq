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

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Writer.Strict
import Data.Foldable

import HsToCoq.Coq.Subst
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import Debug.Trace

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
    go' (Num n1) (Num n2)       = guard (n1 == n2)
    go' (Qualid qid@(Bare v)) t | isPatVar v = do
        tell (M.singleton qid t)
        return ()
    go' (Qualid pqid) (Qualid qid) = guard (pqid == qid)
    go' (App pf pa) (App f a) = do
        go pf f
        zipWithSameLengthM_ goA (toList pa) (toList a)
    -- Simple matching of simple `match`es only – no dependent match clauses, no
    -- return types, no reordering match clauses.  We are VERY DUMB ABOUT BINDING.
    go' (Match scruts1 Nothing eqs1) (Match scruts2 Nothing eqs2) = do
        zipWithSameLengthM_ goMI scruts1 scruts2
        zipWithSameLengthM_ goE  eqs1    eqs2
    go' _lhs _term = mzero

    goA :: Arg -> Arg -> WriterT (M.Map Qualid Term) Maybe ()
    goA (PosArg pt) (PosArg p) = go pt p
    goA (NamedArg pi pt) (NamedArg i p) = do
        guard (pi == i)
        go pt p
    goA _lhs _term = mzero

    -- Handle simple `MatchItem`s only – terms without `as` or `in` clauses
    goMI (MatchItem tm1 Nothing Nothing) (MatchItem tm2 Nothing Nothing) =
      go tm1 tm2
    goMI _ _ =
      mzero

    goE (Equation mps1 tm1) (Equation mps2 tm2) = do
      zipWithSameLengthM_ goMP mps1 mps2
      go tm1 tm2

    goMP (MultPattern mps1) (MultPattern mps2) =
      zipWithSameLengthM_ goP mps1 mps2

    -- We are VERY DUMB ABOUT BINDING.
    goP UnderscorePat    UnderscorePat    = pure ()
    goP (NumPat num1)    (NumPat num2)    = guard $ num1 == num2
    goP (StringPat str1) (StringPat str2) = guard $ str1 == str2
    goP (InScopePat pat1 scope1) (InScopePat pat2 scope2) = do
      guard $ scope1 == scope2
      goP pat1 pat2
    goP (ArgsPat con1 args1) (ArgsPat con2 args2) = do
      goPQid con1 con2
      zipWithSameLengthM_ goP args1 args2
    goP (ExplicitArgsPat con1 args1) (ExplicitArgsPat con2 args2) = do
      goPQid con1 con2
      zipWithSameLengthM_ goP args1 args2
    goP (InfixPat lhs1 op1 rhs1) (InfixPat lhs2 op2 rhs2) = do
      goPQid (Bare op1) (Bare op2)
      goP lhs1 lhs2
      goP rhs1 rhs2
    goP (AsPat pat1 var1) (AsPat pat2 var2) = do
      goPQid var1 var2
      goP pat1 pat2
    goP (QualidPat qid1@(Bare v)) p | isPatVar v, Just t <- patToTerm p =
      tell $ M.singleton qid1 t
    goP (QualidPat qid1) (QualidPat qid2) =
      guard $ qid1 == qid2
    goP (OrPats pats1) (OrPats pats2) =
      zipWithSameLengthM_ goOP pats1 pats2
    goP _ _ = mzero

    patToTerm (ArgsPat con args)         = appList (Qualid con) <$> traverse (fmap PosArg . patToTerm) args
    patToTerm (ExplicitArgsPat con args) = ExplicitApp con . toList <$> traverse patToTerm args
    patToTerm (InfixPat lhs op rhs)      = App2 (Qualid $ Bare op) <$> patToTerm lhs <*> patToTerm rhs
    patToTerm (InScopePat p scope)       = InScope <$> patToTerm p <*> pure scope
    patToTerm (QualidPat qid)            = Just $ Qualid qid
    patToTerm (NumPat n)                 = Just $ Num n
    patToTerm (StringPat s)              = Just $ String s
    patToTerm (AsPat _ _)                = Nothing
    patToTerm UnderscorePat              = Nothing
    patToTerm (OrPats _)                 = Nothing
              
    goPQid lhs@(Bare v) rhs | isPatVar v = tell $ M.singleton lhs (Qualid rhs)
    goPQid lhs          rhs              = guard $ lhs == rhs

    goOP (OrPattern pats1) (OrPattern pats2) = zipWithSameLengthM_ goP pats1 pats2

    zipWithSameLengthM_ :: (Alternative f, Foldable g, Foldable h) => (a -> b -> f c) -> g a -> h b -> f ()
    zipWithSameLengthM_ f as0 bs0 =
      let zipGo (a:as) (b:bs) = f a b *> zipGo as bs
          zipGo []     []     = pure ()
          zipGo _      _      = empty
      in zipGo (toList as0) (toList bs0)
