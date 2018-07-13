{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module GHC.Proof.Plugin (plugin) where

import Data.Maybe
import Control.Monad
import Control.Monad.IO.Class
import System.IO

import GhcPlugins hiding (vcat)
-- import Simplify
-- import CoreStats
-- import CoreMonad
-- import SimplMonad
-- import OccurAnal
-- import FamInstEnv
-- import SimplEnv
-- import CSE
import Unique
import TcType
import HsToCoq.Coq.Gallina hiding (Type, Let, App, Var, Name)
import HsToCoq.Coq.Gallina.Orphans
import HsToCoq.Coq.Gallina.Util hiding (Var)
import HsToCoq.Coq.Pretty
import HsToCoq.PrettyPrint

class ToTerm a where
    t :: a -> Term

instance ToTerm (Tickish b) where
    t _ = undefined

instance ToTerm Int where
    t n = Num (fromIntegral n)

instance ToTerm Type where
    t _ = "tt"

instance ToTerm Name where
    t _ = "tt"

n <: xs = appList n (map PosArg xs)

instance ToTerm Var where
    t v | isTyVar v =
          App3 "Mk_TyVar" (t a) (t b) (t c)
        | isTyVar v =
          "Mk_TyVar" <:
              [ t a
              , t b
              , t c
              , t (tcTyVarDetails v)
              ]
        | isId v =
          "Mk_TyVar" <:
              [ t a
              , t b
              , t c
              , if isGlobalId v
                then "GlobalId"
                else "LocalId" <: [if isExportedId v
                                   then "Exported"
                                   else "NotExported"]
              , t (idDetails v)
              , t (idInfo v) ]
      where
        a = varName v
        b = getKey (getUnique v)
        c = varType v

instance ToTerm Coercion where
    t _ = "tt"

instance ToTerm AltCon where
    t _ = "tt"

instance ToTerm Literal where
    t _ = "tt"

instance ToTerm IdInfo where
    t _ = "tt"

instance ToTerm IdDetails where
    t _ = "tt"

instance ToTerm TcType.TcTyVarDetails where
    t _ = "tt"

instance (ToTerm a, ToTerm b) => ToTerm (a, b) where
    t (x, y) = App2 "pair" (t x) (t y)

instance (ToTerm a, ToTerm b, ToTerm c) => ToTerm (a, b, c) where
    t (x, y, z) = App3 "pair3" (t x) (t y) (t z)

instance ToTerm b => ToTerm (Expr b) where
  t (Var n)        = App1 "Mk_Var" (t n)
  t (Lit l)        = App1 "Lit" (t l)
  t (App e a)      = App2 "App" (t e) (t a)
  t (Lam a e)      = App2 "Lam" (t a) (t e)
  t (Let n e)      = App2 "Let" (t n) (t e)
  t (Case e n u l) = appList "Case" [PosArg (t e), PosArg (t n), PosArg (t u), PosArg (t l)]
  t (Cast e u)     = App2 "Cast" (t e) (t u)
  t (Tick i e)     = App2 "Tick" (t i) (t e)
  t (Type u)       = App1 "Type_" (t u)
  t (Coercion u)   = App1 "Coercion" (t u)

instance ToTerm b => ToTerm (Bind b) where
    t (NonRec n e) = App2 "NonRec" (t n) (t e)
    t (Rec xs)     = App1 "Rec" (t xs)

instance ToTerm a => ToTerm [a] where
    t [] = "nil"
    t (x : xs) = App2 "cons" (t x) (t xs)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ xs = return $ pass : xs
  where pass = CoreDoPluginPass "GHC.Proof" proofPass

proofPass :: PluginPass -- ModGuts -> CoreM ModGuts
proofPass guts@ModGuts {..} = do
    liftIO $ withFile coq WriteMode $ \h ->
      hPrettyPrint h $ vcat (map renderGallina mod)
    return guts
  where
    name = moduleNameSlashes (moduleName mg_module)
    coq  = name ++ ".v"

    mod :: [Sentence]
    mod = [ ModuleSentence (Require Nothing (Just Import) ["Core"])
          , ModuleSentence (Require Nothing (Just Import) ["GHC.Tuple"])
          , DefinitionSentence
              (DefinitionDef Global "program" []
                 (Just (Qualid "CoreProgram")) body)
          ]

    body :: Term
    body = t mg_binds

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120

prettyPrint :: MonadIO m => Doc -> m ()
prettyPrint = hPrettyPrint stdout
