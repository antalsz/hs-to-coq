{-# LANGUAGE TypeSynonymInstances, PatternSynonyms, ViewPatterns,
             TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToCoq.Util.GHC.OnOff {-# WARNING "Do we really need `OnOff`?" #-} (
  OnOff, pattern On, pattern Off,
  onOffToEither, eitherToOnOff
  ) where

import DynFlags

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

#define TYPE_QUOTES ''
#define VAL_QUOTES  '

#define NAME_DynFlags(con,q,name) \
  (con $ case q DynFlags of Name _ nf -> Name (OccName name) nf)

#define TYPE_DynFlags(name) NAME_DynFlags(conT, TYPE_QUOTES, name)
#define PAT_DynFlags(name)  NAME_DynFlags(conP, VAL_QUOTES,  name)
#define VAL_DynFlags(name)  NAME_DynFlags(conE, VAL_QUOTES,  name)

type OnOff = $(TYPE_DynFlags("OnOff"))

pattern On  :: a -> OnOff a
pattern Off :: a -> OnOff a

pattern On  a <- (onOffToEither -> Left  a) where On  a = eitherToOnOff (Left  a)
pattern Off a <- (onOffToEither -> Right a) where Off a = eitherToOnOff (Right a)

onOffToEither :: OnOff a -> Either a a
onOffToEither $(PAT_DynFlags("On")  [varP $ mkName "a"]) = Left  a
onOffToEither $(PAT_DynFlags("Off") [varP $ mkName "a"]) = Right a

eitherToOnOff :: Either a a -> OnOff a
eitherToOnOff (Left  a) = $(VAL_DynFlags("On"))  a
eitherToOnOff (Right a) = $(VAL_DynFlags("Off")) a

instance Show a => Show (OnOff a) where
  show oo = case show (onOffToEither oo) of
              'L':'e':'f':'t':s     -> "On"  ++ s
              'R':'i':'g':'h':'t':s -> "Off" ++ s
              s                     -> "?OnOff? " ++ s
