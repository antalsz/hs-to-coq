{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module HsToCoq.ConvertHaskell.BuiltIn where

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.Gallina.Orphans ()

import Data.Map (Map)
import qualified Data.Map as M

-- HACK: Hard-code information about some data types here
-- This needs to be solved proper, but for now this makes the test suite
-- more useful
builtInDataCons :: [(Qualid,[(Qualid,Int)])]
builtInDataCons =
    [ "option" =: [ "Some"  =: 1, "None"  =: 0 ]
    , "pair"   =: [ "pair"  =: 2]
    , "list"   =: [ "nil"   =: 1, "cons"  =: 2 ]
    , "bool"   =: [ "true"  =: 0, "false" =: 0 ]
    , "ordering" =: [ "Lt"  =: 1, "Eq" =: 1, "Gt" =: 1 ]
    ]
  where (=:) = (,)

builtInClasses :: [ClassDefinition]
builtInClasses =
    [ ClassDefinition "GHC.Base.Eq_" ["a"] Nothing
        [ "GHC.Base.op_zeze__" =: "a" `Arrow` "a" `Arrow` "bool"
        , "GHC.Base.op_zsze__" =: "a" `Arrow` "a" `Arrow` "bool"
        ]
    , ClassDefinition "GHC.Base.Ord" ["a"] Nothing
        [ "GHC.Base.op_zl__"   =: "a" `Arrow` "a" `Arrow` "bool"
        , "GHC.Base.op_zlze__" =: "a" `Arrow` "a" `Arrow` "bool"
        , "GHC.Base.op_zg__"   =: "a" `Arrow` "a" `Arrow` "bool"
        , "GHC.Base.op_zgze__" =: "a" `Arrow` "a" `Arrow` "bool"
        , "GHC.Base.compare"   =: "a" `Arrow` "a" `Arrow` "comparison"
        , "GHC.Base.max"       =: "a" `Arrow` "a" `Arrow` "a"
        , "GHC.Base.min"       =: "a" `Arrow` "a" `Arrow` "a"
        ]
    {-
    -- This is essentially a class for co-inductive types. 
    , ClassDefinition "GHC.Base.Alternative" 
        [ "f"
        , Generalized Implicit (App1 "GHC.Base.Applicative" "f")
        ]
        Nothing
        [ "GHC.Base.empty" =:
          (Forall [ Inferred Implicit (Ident "a") ] $
           App1 "f" "a")
        , "GHC.Base.op_zgzbzl__" =:
          (Forall [ Inferred Implicit (Ident "a") ] $
           App1 "f" "a" `Arrow` App1 "f" "a" `Arrow` App1 "f" "a")
        ]
    -}


    , ClassDefinition "Control.Monad.Trans.Class.MonadTrans" ["t"] Nothing
        [ "Control.Monad.Trans.Class.lift" =:
          (Forall [ Inferred Implicit (Ident "m")
                  , Inferred Implicit (Ident "a")
                  , Generalized Implicit (App1 "GHC.Base.Monad" "m")
                  ] $
            (App1 "m" "a" `Arrow` App2 "t" "m" "a"))
          ]
    ]
  where
   (=:) = (,)
   infix 0 =:

builtInDefaultMethods :: Map Qualid (Map Qualid Term)
builtInDefaultMethods = fmap M.fromList $ M.fromList $
    [ "GHC.Base.Eq_" =:
        [ "GHC.Base.==" ~> Fun ["x", "y"] (App1 "negb" $ App2 "GHC.Base./=" "x" "y")
        , "GHC.Base./=" ~> Fun ["x", "y"] (App1 "negb" $ App2 "GHC.Base.==" "x" "y")
        ]
    , "GHC.Base.Ord" =:
        [ "GHC.Base.max" ~> Fun ["x", "y"] (IfBool SymmetricIf (App2 "GHC.Base.op_zlze__" "x" "y") "y" "x")
        , "GHC.Base.min" ~> Fun ["x", "y"] (IfBool SymmetricIf (App2 "GHC.Base.op_zlze__" "x" "y") "x" "y")

{-  x <= y  = compare x y /= GT
    x <  y  = compare x y == LT
    x >= y  = compare x y /= LT
    x >  y  = compare x y == GT   -}

        , "GHC.Base.op_zlze__" ~> Fun  ["x", "y"] (App2 "GHC.Base.op_zsze__" (App2 "GHC.Base.compare" "x" "y") "Gt")
        , "GHC.Base.op_zl__"   ~> Fun  ["x", "y"] (App2 "GHC.Base.op_zeze__" (App2 "GHC.Base.compare" "x" "y") "Lt")
        , "GHC.Base.op_zgze__" ~> Fun  ["x", "y"] (App2 "GHC.Base.op_zsze__" (App2 "GHC.Base.compare" "x" "y") "Lt")
        , "GHC.Base.op_zg__"   ~> Fun  ["x", "y"] (App2 "GHC.Base.op_zeze__" (App2 "GHC.Base.compare" "x" "y") "Gt")
        ]

    ]
  where
   (=:) = (,)
   infix 0 =:
   m ~> d  = (m, d)
