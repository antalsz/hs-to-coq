module HsToCoq.ConvertHaskell.Declarations.Notations (buildInfixNotations) where

import Data.Bifunctor

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Sigs

--------------------------------------------------------------------------------

buildInfixNotations :: Map Ident Signature -> Op -> Ident -> [Notation]
buildInfixNotations sigs op def = [ uncurry (InfixDefinition op (Var def))
                                      . maybe (Nothing, Level 99) (first Just)
                                      $ sigFixity =<< M.lookup op sigs
                                  , NotationBinding $ NotationIdentBinding (infixToPrefix op) (Var def) ]
