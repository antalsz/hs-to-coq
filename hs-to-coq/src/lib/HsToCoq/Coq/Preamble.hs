{-|
Module      : HsToCoq.Coq.Preamble
Description : Static preamble for all hs-to-coq output
Copyright   : Copyright © 2017 Antal Spector-Zabusky, University of Pennsylvania
License     : MIT
Maintainer  : antal.b.sz@gmail.com
Stability   : experimental
-}

{-# LANGUAGE OverloadedStrings #-}

module HsToCoq.Coq.Preamble (staticPreamble) where

import Data.Text (Text)
import qualified Data.Text as T

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
