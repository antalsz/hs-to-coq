module HsToCoq.Util.GHC.HsExpr (module HsExpr, isNoSyntaxExpr) where

import FastString
import HsLit
import HsExpr
import TcEvidence (HsWrapper(..))

isNoSyntaxExpr :: SyntaxExpr id -> Bool
isNoSyntaxExpr SyntaxExpr{ syn_expr = HsLit (HsString "" str)
                         , syn_arg_wraps = []
                         , syn_res_wrap  = WpHole } =
  str == fsLit "noSyntaxExpr"
isNoSyntaxExpr _ =
  False
