{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}
module Irrefutable where

data Option a = Some a | None

constTrue :: Option a -> Bool
constTrue ~(Some _) = True
constTrue _ = False
