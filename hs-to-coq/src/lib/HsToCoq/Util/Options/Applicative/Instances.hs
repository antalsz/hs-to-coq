{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.Options.Applicative.Instances () where

import Data.Semigroup
import Options.Applicative.Types
import Options.Applicative.Builder hiding ((<>))
import Options.Applicative.Builder.Internal
import Options.Applicative.Help

instance                Semigroup ParseError      where (<>) = mappend
instance                Semigroup (InfoMod a)     where (<>) = mappend
instance                Semigroup PrefsMod        where (<>) = mappend
instance                Semigroup (Mod f a)       where (<>) = mappend
instance                Semigroup Completer       where (<>) = mappend
instance                Semigroup (DefaultProp a) where (<>) = mappend
instance                Semigroup ParserHelp      where (<>) = mappend
instance Semigroup a => Semigroup (Chunk a)       where (<>) = chunked (<>)
