{-# LANGUAGE TypeSynonymInstances, PatternSynonyms, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module OnOff (
  OnOff, pattern On, pattern Off,
  onOffToEither, eitherToOnOff
  ) where

import DynFlags

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

type OnOff = $(conT $ case ''DynFlags of Name _ nf -> Name (OccName "OnOff") nf)
pattern On  a = $(conP (case 'DynFlags of Name _ nf -> Name (OccName "On")  nf) [varP $ mkName "a"])
pattern Off a = $(conP (case 'DynFlags of Name _ nf -> Name (OccName "Off") nf) [varP $ mkName "a"])

onOffToEither :: OnOff a -> Either a a
onOffToEither (On  a) = Left  a
onOffToEither (Off a) = Right a
onOffToEither _       = error "impossible"

eitherToOnOff :: Either a a -> OnOff a
eitherToOnOff (Left  a) = On  a
eitherToOnOff (Right a) = Off a

instance Show a => Show (OnOff a) where
  show oo = case show (onOffToEither oo) of
              'L':'e':'f':'t':s     -> "On"  ++ s
              'R':'i':'g':'h':'t':s -> "Off" ++ s
              s                     -> "?OnOff? " ++ s
