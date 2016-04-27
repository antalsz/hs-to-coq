module HsToCoq.Util.GHC.HsExpr (module HsExpr, isNoSyntaxExpr) where

import FastString
import HsLit
import HsExpr

isNoSyntaxExpr :: HsExpr id -> Bool
isNoSyntaxExpr (HsLit (HsString "" str)) = str == fsLit "noSyntaxExpr"
isNoSyntaxExpr _                         = False
