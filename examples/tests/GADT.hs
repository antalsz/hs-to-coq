{-# LANGUAGE GADTs #-}
module GADT where

data O
data C
data MaybeO ex t where
  JustO    :: t -> MaybeO O t
  NothingO ::      MaybeO C t


