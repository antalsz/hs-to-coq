{-# LANGUAGE CPP #-}

#include "ghc-compat.h"

module HsToCoq.Util.GHC.HsExpr (
  module HsExpr,
  isNoSyntaxExpr,
  isNoPostTcExpr,
  isGenLitString
) where

import FastString
#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Lit
import GHC.Hs.Expr as HsExpr
#else
import HsLit
import HsExpr
#endif
import TcEvidence (HsWrapper(..))

isGenLitString :: String -> HsExpr pass -> Bool
isGenLitString str (HsLit NOEXTP (HsString _ fstr)) = fsLit str == fstr
isGenLitString _   _                          = False

isNoSyntaxExpr :: SyntaxExpr pass -> Bool
isNoSyntaxExpr SyntaxExpr{ syn_expr      = expr
                         , syn_arg_wraps = []
                         , syn_res_wrap  = WpHole } =
  isGenLitString "noSyntaxExpr" expr
isNoSyntaxExpr _ =
  False

isNoPostTcExpr :: PostTcExpr -> Bool
isNoPostTcExpr = isGenLitString "noPostTcExpr"
