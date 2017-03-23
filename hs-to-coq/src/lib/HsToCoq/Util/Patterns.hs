{-# LANGUAGE PatternSynonyms #-}

module HsToCoq.Util.Patterns (pattern Nil) where

-- Because @OverloadedLists@ and @PatternSynonyms@ don't play nice together.
pattern Nil :: [a]
pattern Nil = []
