module GHC.Proof.Translate where

import Language.Haskell.TH

typeInstance :: String -> Cxt -> Name -> [TyVarBndr] -> [Con] -> DecsQ
typeInstance =
