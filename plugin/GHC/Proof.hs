-- |
-- Description : Let GHC prove program equations
-- Copyright   : (c) Joachim Breitner, 2017
-- License     : MIT
-- Maintainer  : mail@joachim-breitner.de
-- Portability : GHC specifc
--
-- This module supports the accompanying GHC plugin "GHC.Proof.Plugin" and adds
-- to GHC the ability to verify simple program equations.
--
-- = Synopis
--
-- Consider this module:
--
-- > {-# OPTIONS_GHC -O -fplugin GHC.Proof.Plugin #-}
-- > module Simple where
-- >
-- > import GHC.Proof
-- > import Data.Maybe
-- >
-- > my_proof1 :: (a -> b) -> Maybe a -> Proof
-- > my_proof1 f x = isNothing (fmap f x)
-- >             === isNothing x
-- >
-- > my_proof2 :: a -> Maybe a -> Proof
-- > my_proof2 d x = fromMaybe d x
-- >             === maybe d id x
--
-- Compiling it will result in this output:
--
-- > $ ghc Simple.hs
-- > [1 of 1] Compiling Simple           ( Simple.hs, Simple.o )
-- > GHC.Proof: Proving my_proof1 …
-- > GHC.Proof: Proving my_proof2 …
-- > GHC.Proof proved 2 equalities
--
-- = Usage
--
-- To use this plugin, you have to
--
-- *   Make sure you load the plugin @GHC.Proof.Plugin@, either by passing
--     @-fplugin GHC.Proof.Plugin@ to GHC or, more conveniently, using the
--     @OPTIONS_GHC@ pragma as above.
--
-- *   Import the @GHC.Proof@ module.
--
-- *   Define proof obligations using the 'proof' function or, equilvalently, the
--     '===' operator. Type signatures are optional.
--
--     These proof obligation must occur direclty on the
--     right-hand side of a top-level definition, where all parameters (if any)
--     are plain variables. For example, this would (currently) not work:
--
--     > not_good (f,x) = isNothing (fmap f x) === isNothing x
--
--     If your module has an explicit export list, then these functions need to
--     be exported (otherwise the compiler deletes them too quickly).
--
-- *   Compile. If all proof obligations can be proven, compilation continues as
--     usual; otherwise it aborts.
--
-- = What can I prove this way?
--
-- Who knows... but generally you can only expect interesting results when you
-- use functions that are either non-recursive, or have an extensive rewrite
-- rule setup (such as lists). See the @examples/@ directory for some examples
-- of what works.
module GHC.Proof where

-- | A dummy data type, to give 'proof' a nicely readable type signature.
data Proof = Proof

-- | Instructs the compiler to see if it can prove the two arguments to 'proof'
-- to be equivalent.
proof :: a -> a -> Proof
proof _ _ = Proof
{-# INLINE [0] proof #-}

-- | Infix operator for 'proof'.
(===) :: a -> a -> Proof
(===) = proof
infix 0 ===

-- | Instructs the compiler to try to prove the two arguments to 'proof'
-- to be equivalent, but do not abort if it fails.
--
-- This is useful to document equalities that you would like to be proven, but
-- where @ghc-proofs@ does not work well enough.
non_proof :: a -> a -> Proof
non_proof _ _ = Proof
{-# INLINE [0] non_proof #-}

-- | Infix operator for 'non_proof'.
(=/=) :: a -> a -> Proof
(=/=) = non_proof
infix 0 =/=


