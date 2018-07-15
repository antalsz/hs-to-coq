{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

module HsToCoq.Plugin (plugin) where

import Data.Text (pack)
import Control.Monad.IO.Class
import System.IO

import GhcPlugins hiding (vcat)
import Unique
import TcType
import HsToCoq.Coq.Gallina hiding (Type, Let, App, Name)
import HsToCoq.Coq.Gallina.Orphans ()
import HsToCoq.Coq.Gallina.Util hiding (Var)
import HsToCoq.Coq.Pretty
import HsToCoq.PrettyPrint

-- | A more convenient Gallina application operator
(<:) :: Term -> [Term] -> Term
n <: xs = appList n (map PosArg xs)

class ToTerm a where
    t :: a -> Term

instance ToTerm (Tickish b) where
    t _ = undefined

instance ToTerm Int where
    t n = InScope (Num (fromIntegral n)) "N"

-- | Sometimes we want `nat` not `N`
as_nat :: Term -> Term
as_nat x = ("N.to_nat" <: [x])

instance ToTerm Module where
    t (Module a b) = App2 "Mk_Module" (t a) (t b)

instance ToTerm IndefUnitId where
    t _ = "default"

instance ToTerm DefUnitId where
    t _ = "default"

instance ToTerm UnitId where
    t (IndefiniteUnitId a) = "IndefiniteUnitId" <: [t a]
    t (DefiniteUnitId a)   = "DefiniteUnitId" <: [t a]

instance ToTerm ModuleName where
    t _ = "default"

instance ToTerm Type where
    t _ = "default"

instance ToTerm NameSpace where
    t _ = "default"

instance ToTerm FastString where
    t f = HsString (pack (unpackFS f))

instance ToTerm OccName where
    t o = "Mk_OccName" <: [t (occNameSpace o), t (occNameFS o)]

instance ToTerm Unique where
    t u = "MkUnique" <: [t (getKey u)]

instance ToTerm SrcSpan where
    t _ = "default"

instance ToTerm Name where
    t n = "Mk_Name"
        <: [ if | isWiredInName n  ->
                  App3 "WiredIn" (t (nameModule n)) "default"
                      (if isBuiltInSyntax n
                       then "BuiltInSyntax"
                       else "UserSyntax")
                | isExternalName n ->
                  App1 "External" (t (nameModule n))
                | isInternalName n -> "Internal"
                | isSystemName n   -> "System"
           , t (nameOccName n)
           , t (nameUnique n)
           , t (nameSrcSpan n)
           ]

instance ToTerm Var where
    t v | isTyVar v =
          "Mk_TyVar" <: [t a, t b, t c]
        | isTcTyVar v =
          "Mk_TcTyVar" <:
              [ t a
              , t b
              , t c
              , t (tcTyVarDetails v)
              ]
        | isId v =
          "Mk_Id" <:
              [ t a
              , as_nat (t b)
              , t c
              , if isGlobalId v
                then "GlobalId"
                else "LocalId" <: [if isExportedId v
                                   then "Exported"
                                   else "NotExported"]
              , t (idDetails v)
              , t (idInfo v) ]
        | otherwise = error "What kind of Var is that?"
      where
        a = varName v
        b = getKey (getUnique v)
        c = varType v

instance ToTerm Coercion where
    t _ = "default"

instance ToTerm AltCon where
    t _ = "default"

instance ToTerm Literal where
    t _ = "default"

instance ToTerm IdInfo where
    t _ = "default"

instance ToTerm IdDetails where
    t _ = "default"

instance ToTerm TcType.TcTyVarDetails where
    t _ = "default"

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
          , ModuleSentence (Require Nothing (Just Import) ["Name"])
          , ModuleSentence (Require Nothing (Just Import) ["OccName"])
          , ModuleSentence (Require Nothing (Just Import) ["Module"])
          , ModuleSentence (Require Nothing (Just Import) ["Unique"])
          , ModuleSentence (Require Nothing (Just Import) ["GHC.Tuple"])
          , ModuleSentence (Require Nothing (Just Import) ["GHC.Err"])
          , ModuleSentence (Require Nothing (Just Import) ["Coq.NArith.BinNat"])
          , DefinitionSentence
              (DefinitionDef Global "program" []
                 (Just (Qualid "CoreProgram")) body)
          ]

    body :: Term
    body = t mg_binds

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120
