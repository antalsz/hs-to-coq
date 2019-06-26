{-# LANGUAGE MultiWayIf, LambdaCase, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Variables (
  -- * Generate variable names
  var,
  recordField, bareName,
  freeVar', freeVar,
  -- * Avoiding reserved words/names
  tryEscapeReservedWord, escapeReservedNames
  ) where

import Control.Lens
import Data.Semigroup (Semigroup(..))
import Data.Monoid hiding ((<>))
import Data.Maybe
import HsToCoq.Util.List
import qualified Data.Set as S
import qualified Data.Text as T

import Control.Monad

import GHC (GhcMonad,AmbiguousFieldOcc(..),GhcRn)
--import GHC hiding (Name)
import qualified GHC
import Outputable (OutputableBndr)
import Name(occNameString, nameOccName, nameModule_maybe)
-- import Name hiding (Name)

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.Module

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Pretty
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.InfixNames

--------------------------------------------------------------------------------

tryEscapeReservedWord :: Ident -> Ident -> Maybe Ident
tryEscapeReservedWord reserved name = do
  suffix <- T.stripPrefix reserved name
  guard $ T.all (== '_') suffix
  pure $ name <> "_"

-- convert a haskell identifier to a Gallina identifier.
--   (a) avoiding certain Gallina reserved words and library definitions
--   (b) converting some operators into Gallina ops (such as composition)
escapeReservedNames :: Ident -> Ident
escapeReservedNames x =
  fromMaybe x . getFirst $
    foldMap (First . flip tryEscapeReservedWord x)
            (T.words "Set Type Prop fun fix forall return mod match as cons pair nil for is with left right exists inl inr")
    <> if | T.all (== '.') x  -> pure $ T.map (const '∘') x
          | T.all (== '∘') x  -> pure $ "⟨" <> x <> "⟩"
-- these type operators aren't parsed by the renaming file
          | x == "(->)"       -> pure $ ("arrow")
          | x == "#."       -> pure $ ("hash_compose")  -- Data.Foldable
-- Maybe add this as part of an Int# solution? But don't want to
-- always replace these, if we make "Int#" a notation for "Int_h"
--          | T.isInfixOf "#" x -> pure $ T.replace "#" "_h" x
          | otherwise         -> mempty

--------------------------------------------------------------------------------

freeVar' :: Ident -> Ident
freeVar' = escapeReservedNames

freeVar :: (GhcMonad m, OutputableBndr name) => name -> m Ident
freeVar = fmap freeVar' . ghcPpr

-- Does not qualify with the module, does not look it up in renamings
-- (useful for locally bound names)
bareName :: GHC.Name -> Ident
bareName = toPrefix . escapeReservedNames . specialForms .  T.pack . occNameString . nameOccName

localName :: GHC.Name -> Ident
localName = toLocalPrefix . escapeReservedNames . specialForms . T.pack . occNameString . nameOccName

specialForms :: Ident -> Ident
-- "$sel:rd:Mulw" to "rd"
specialForms name | "$sel:" `T.isPrefixOf` name = T.takeWhile (/= ':') $ T.drop 5 name
                  | otherwise                   = name

-- convert to a Qid but don't lookup renamings
toQid :: ConversionMonad r m => GHC.Name -> m Qualid
toQid name = case nameModM of
    Just m  -> pure (Qualified (moduleNameText m) (bareName name))
    Nothing -> pure (Bare (localName name))
  where
    nameModM = moduleName <$> nameModule_maybe name

rename :: ConversionMonad r m => HsNamespace -> Qualid -> m Qualid
rename ns = go S.empty
  where
    go seen qid | qid `S.member` seen =
        fail $ explainStrItems showP "no" "," "and" "Cyclic renaming" "Cyclic renamings" seen
    go seen qid = view (edits . renamed ns qid) >>= \case
        Nothing ->   return qid
            -- A self rename is also fine, it signals stopping.
        Just qid' | qid' == qid -> return qid
        Just qid' -> go (S.insert qid seen) qid'

renameModule :: ConversionMonad r m => Qualid -> m Qualid     
renameModule (Qualified mod ident) = do
  let m = mkModuleName (T.unpack mod)
  rm <- view (edits.renamedModules.at m . non m)
  pure (Qualified (moduleNameText rm) ident)
renameModule qid = pure qid


var :: ConversionMonad r m => HsNamespace -> GHC.Name -> m Qualid
var ns name = do
    qid <- toQid name
    qid1 <- rename ns qid
    renameModule qid1



recordField :: (ConversionMonad r m) => AmbiguousFieldOcc GhcRn -> m Qualid
recordField (Unambiguous _ sel) = var ExprNS sel
recordField (Ambiguous _ _)     = error "Cannot handle ambiguous record field names"
