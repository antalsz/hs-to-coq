{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.PrettyPrint (
  -- * The base module
  module Text.PrettyPrint.ANSI.Leijen,
  -- * Don't use operators with existing meanings
  (<>), (<!>),
  -- * '[]' -> 'Foldable'
  encloseSep,
  list, tupled, semiBraces,
  hsep, vsep, fillSep, sep,
  hcat, vcat, fillCat, cat,
  punctuate,
  -- * Utility functions
  spacedSepPre, spacedSepPost, (</?>), spaceIf
  ) where

import Text.PrettyPrint.ANSI.Leijen hiding ( (<>), (<$>)
                                           , encloseSep
                                           , list
                                           , tupled
                                           , semiBraces
                                           , hsep
                                           , vsep
                                           , fillSep
                                           , sep
                                           , hcat
                                           , vcat
                                           , fillCat
                                           , cat
                                           , punctuate )
import qualified Text.PrettyPrint.ANSI.Leijen as T
import qualified Data.Monoid as Monoid
import Data.Semigroup (Semigroup(..))
import Data.Foldable

instance Semigroup Doc where
  (<>) = (Monoid.<>)

(<!>) :: Doc -> Doc -> Doc
(<!>) = (T.<$>)
infixr 5 <!>
{-# INLINABLE (<!>) #-}

encloseSep :: Foldable f => Doc -> Doc -> Doc -> f Doc -> Doc
encloseSep left right sep = T.encloseSep left right sep . toList
{-# INLINABLE encloseSep #-}

list :: Foldable f => f Doc -> Doc
list = T.list . toList
{-# INLINABLE list #-}

tupled :: Foldable f => f Doc -> Doc
tupled = T.tupled . toList
{-# INLINABLE tupled #-}

semiBraces :: Foldable f => f Doc -> Doc
semiBraces = T.semiBraces . toList
{-# INLINABLE semiBraces #-}

hsep :: Foldable f => f Doc -> Doc
hsep = T.hsep . toList
{-# INLINABLE hsep #-}

vsep :: Foldable f => f Doc -> Doc
vsep = T.vsep . toList
{-# INLINABLE vsep #-}

fillSep :: Foldable f => f Doc -> Doc
fillSep = T.fillSep . toList
{-# INLINABLE fillSep #-}

sep :: Foldable f => f Doc -> Doc
sep = T.sep . toList
{-# INLINABLE sep #-}

hcat :: Foldable f => f Doc -> Doc
hcat = T.hcat . toList
{-# INLINABLE hcat #-}

vcat :: Foldable f => f Doc -> Doc
vcat = T.vcat . toList
{-# INLINABLE vcat #-}

fillCat :: Foldable f => f Doc -> Doc
fillCat = T.fillCat . toList
{-# INLINABLE fillCat #-}

cat :: Foldable f => f Doc -> Doc
cat = T.cat . toList
{-# INLINABLE cat #-}

punctuate :: Foldable f => Doc -> f Doc -> [Doc]
punctuate p = T.punctuate p . toList
{-# INLINABLE punctuate #-}

generic_spaced_sep :: Foldable f
                   => (Doc -> Doc -> Doc) -> (Doc -> Doc -> Doc)
                   -> Doc -> f Doc -> Doc
generic_spaced_sep (<&) (&>) sep docs
  | null docs = mempty
  | otherwise = foldr1 (\doc result -> doc <& sep &> result) docs
{-# INLINABLE generic_spaced_sep #-}
                
spacedSepPre :: Foldable f => Doc -> f Doc -> Doc
spacedSepPre = generic_spaced_sep (</>) (<+>)
                
spacedSepPost :: Foldable f => Doc -> f Doc -> Doc
spacedSepPost = generic_spaced_sep (<+>) (</>)

(</?>) :: Doc -> Maybe Doc -> Doc
d1 </?> Nothing = d1
d1 </?> Just d2 = d1 </> d2
infixl 5 </?>

spaceIf :: Foldable f => f a -> Doc
spaceIf x | null x    = empty
          | otherwise = space
