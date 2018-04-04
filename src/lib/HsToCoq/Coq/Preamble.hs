{-|
Module      : HsToCoq.Coq.Preamble
Description : Static preamble for all hs-to-coq output
Copyright   : Copyright © 2017 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}

module HsToCoq.Coq.Preamble
    ( staticPreamble
    , builtInAxioms
    ) where

import Data.Text (Text)
import qualified Data.Text as T
import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Orphans ()
import qualified Data.Map as M
import Data.Bifunctor

staticPreamble :: Text
staticPreamble = T.unlines
 [ "(* Default settings (from HsToCoq.Coq.Preamble) *)"
 , ""
 , "Generalizable All Variables."
 , ""
 , "Unset Implicit Arguments."
 , "Set Maximal Implicit Insertion."
 , "Unset Strict Implicit."
 , "Unset Printing Implicit Defensive."
 , ""
 , "Require Coq.Program.Tactics."
 , "Require Coq.Program.Wf."
 ]

-- | When a free variable of this name appears in the output,
-- an axiom of the type given here is added to the preamble
builtInAxioms :: M.Map Qualid Term
builtInAxioms = M.fromList $ map (first Bare)
    [ "missingValue"   =: Forall [ Inferred Implicit (Ident (Bare "a")) ] a
    ]
  where
   a = "a"
   (=:) = (,)
   infix 0 =:
