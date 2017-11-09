{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, ConversionT, evalConversion,
  -- * Types
  ConversionState(),
  currentModule, currentDefinition, edits, constructors, constructorTypes, constructorFields, recordFieldTypes, classDefns, defaultMethods, fixities, typecheckerEnvironment, renamed, axioms,
  ConstructorFields(..), _NonRecordFields, _RecordFields,
  -- * Operations
  maybeWithCurrentModule, withCurrentModule, withNoCurrentModule, withCurrentModuleOrNone,
  withCurrentDefinition,
  fresh, gensym,
  rename,
  localizeConversionState,
  -- * Access to the typechecker environment ('TcGblEnv')
  lookupTyThing,
  -- * Errors
  throwProgramError, convUnsupported, editFailure,
  -- * Fixity
  getFixity, recordFixity,
  -- * Modules
  skipModules, skipModulesBy
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Control.Monad.State
import Control.Monad.Variables

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import GHC
import TcRnTypes (TcGblEnv, tcg_type_env)
import NameEnv (lookupNameEnv)

import Panic

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Parameters.Edits

--------------------------------------------------------------------------------

data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Ident]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

data ConversionState = ConversionState { __currentModule         :: !(Maybe ModuleName)
                                       , __currentDefinition     :: !(Maybe Ident)
                                       , _edits                  :: !Edits
                                       , _constructors           :: !(Map Ident [Ident])
                                       , _constructorTypes       :: !(Map Ident Ident)
                                       , _constructorFields      :: !(Map Ident ConstructorFields)
                                       , _recordFieldTypes       :: !(Map Ident Ident)
                                       -- types of class members
                                       -- , _memberSigs       :: !(Map Ident (Map Ident Signature))
                                       -- translated classes
                                       , _classDefns             :: !(Map Ident ClassDefinition)
                                       , _defaultMethods         :: !(Map Ident (Map Ident Term))
                                       , _fixities               :: !(Map Ident (Coq.Associativity, Coq.Level))
                                       , _typecheckerEnvironment :: !(Maybe TcGblEnv)
                                       , _axioms                 :: !(Map Ident Term)
                                       , __unique                :: !Natural
                                       }
makeLenses ''ConversionState
-- '_currentModule', '_currentDefinition) and '_unique' are not exported

currentModule :: Getter ConversionState (Maybe ModuleName)
currentModule = _currentModule
{-# INLINABLE currentModule #-}

currentDefinition :: Getter ConversionState (Maybe Ident)
currentDefinition = _currentDefinition
{-# INLINABLE currentDefinition #-}

renamed :: HsNamespace -> Ident -> Lens' ConversionState (Maybe Ident)
renamed ns x = edits.renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

type ConversionMonad m = (GhcMonad m, MonadState ConversionState m, MonadVariables Ident () m)
type ConversionT m = StateT ConversionState (VariablesT Ident () m)

-- HACK: Hard-code information about some data types here
-- This needs to be solved proper, but for now this makes the test suite
-- more useful
builtInDataCons :: [(Ident,[(Ident,Int)])]
builtInDataCons =
    [ "option" =: [ "Some"  =: 1, "None"  =: 0 ]
    , "pair"   =: [ "pair"  =: 2]
    , "list"   =: [ "nil"   =: 1, "cons"  =: 2 ]
    , "bool"   =: [ "true"  =: 0, "false" =: 0 ]
    , "ordering" =: [ "Lt"  =: 1, "Eq" =: 1, "Gt" =: 1 ]
    ]
  where (=:) = (,)

builtInClasses :: [ClassDefinition]
builtInClasses =
    [ ClassDefinition "GHC.Base.Eq_" [Inferred Explicit (Ident "a")] Nothing
        [ "op_zeze__" =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        , "op_zsze__" =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        ]
    , ClassDefinition "GHC.Base.Ord" [Inferred Explicit (Ident "a")] Nothing
        [ "op_zl__"   =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        , "op_zlze__" =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        , "op_zg__"   =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        , "op_zgze__" =: Var "a" `Arrow` Var "a" `Arrow` Var "bool"
        , "compare"   =: Var "a" `Arrow` Var "a" `Arrow` Var "comparison"
        , "max"       =: Var "a" `Arrow` Var "a" `Arrow` Var "a"
        , "min"       =: Var "a" `Arrow` Var "a" `Arrow` Var "a"
        ]
    , ClassDefinition "GHC.Base.Monoid" [Inferred Explicit (Ident "a")] Nothing
        [ "mappend" =: Var "a" `Arrow` Var "a" `Arrow` Var "a"
        , "mconcat" =: (Var "list" `App1` Var "a") `Arrow` Var "a"
        , "mempty"  =: Var "a"
        ]
    , ClassDefinition "GHC.Base.Functor" [Inferred Explicit (Ident "f")] Nothing
        [ "op_zlzd__" =: (Forall [ Inferred Implicit (Ident "a")
                            , Inferred Implicit (Ident "b")] $
                     (Var "a") `Arrow`
                     App1 (Var "f") (Var "b") `Arrow`
                     App1 (Var "f") (Var "a"))
        , "fmap" =: (Forall [ Inferred Implicit (Ident "a")
                            , Inferred Implicit (Ident "b")] $
                     (Var "a" `Arrow` Var "b") `Arrow`
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b"))
        ]
    , ClassDefinition "GHC.Base.Applicative"
        [ Inferred Explicit (Ident "f")
        , Generalized Implicit (App1 (Var "Functor") (Var "f"))
        ]
        Nothing
        [ "op_ztzg__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b") `Arrow`
                     App1 (Var "f") (Var "b"))
        , "op_zlztzg__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a" `Arrow` Var "b") `Arrow`
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b"))
        , "pure"  =: (Forall [Inferred Implicit (Ident "a")]  $
                      Var "a" `Arrow` App1 (Var "f") (Var "a"))
        {- skipped
        , "op_zlzt__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b") `Arrow`
                     App1 (Var "f") (Var "a"))
        -}
        ]
    , ClassDefinition "GHC.Base.Monad"
        [ Inferred Explicit (Ident "f")
        , Generalized Implicit (App1 (Var "GHC.Base.Applicative") (Var "f"))
        ]
        Nothing
        [ "op_zgzg__" =:
           (Forall [ Inferred Implicit (Ident "a")
                   , Inferred Implicit (Ident "b")] $
                    App1 (Var "f") (Var "a") `Arrow`
                    App1 (Var "f") (Var "b") `Arrow`
                    App1 (Var "f") (Var "b"))
        , "op_zgzgze__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     (Var "a" `Arrow` App1 (Var "f") (Var "b")) `Arrow`
                     App1 (Var "f") (Var "b"))
        , "return_"  =: (Forall [Inferred Implicit (Ident "a")]  $
                      Var "a" `Arrow` App1 (Var "f") (Var "a"))
        {-
        , "fail" =:
           (Forall [ Inferred Implicit (Ident "a")] $
                    Var "GHC.Prim.String" `Arrow`
                    App1 (Var "f") (Var "a"))
        -}
        ]
    , ClassDefinition "Foldable"
        [ Inferred Explicit (Ident "t")
        ]
        Nothing
        ["foldMap" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "m")
                    , Generalized Implicit (App1 (Var "Monoid") (Var "m")) ] $
                     (Var "a" `Arrow` Var "m") `Arrow`
                     App1 (Var "t") (Var "a") `Arrow`
                     Var "m")
        ]
    , ClassDefinition "Traversable"
        [ Inferred Explicit (Ident "t")
        , Generalized Implicit (App1 (Var "Functor") (Var "t"))
        , Generalized Implicit (App1 (Var "Foldable") (Var "t"))
        ]
        Nothing
        ["traverse" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")
                    , Inferred Implicit (Ident "f")
                    , Generalized Implicit (App1 (Var "Applicative") (Var "f")) ] $
                     (Var "a" `Arrow` App1 (Var "f") (Var "b")) `Arrow`
                     App1 (Var "t") (Var "a") `Arrow`
                     App1 (Var "f") (App1 (Var "t") (Var "b")))
        ]
    ]
  where
   (=:) = (,)
   infix 0 =:

builtInDefaultMethods :: Map Ident (Map Ident Term)
builtInDefaultMethods = fmap M.fromList $ M.fromList
    [ "GHC.Base.Eq_" =:
        [ "==" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "/=" (Var "y"))
        , "/=" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "==" (Var "y"))
        ]
    , "GHC.Base.Ord" =:
        [ "max" ~> Fun [arg "x", arg "y"] (ifBool (App2 (Var "op_zlze__") (Var "x") (Var "y")) (Var "y") (Var "x"))
        , "min" ~> Fun [arg "x", arg "y"] (ifBool (App2 (Var "op_zlze__") (Var "x") (Var "y")) (Var "x") (Var "y"))

{-  x <= y  = compare x y /= GT
    x <  y  = compare x y == LT
    x >= y  = compare x y /= LT
    x >  y  = compare x y == GT   -}

        , "op_zlze__" ~> Fun  [arg "x", arg "y"] (App2 (Var "op_zsze__") (App2 (Var "compare") (Var "x") (Var "y")) (Var "Gt"))
        , "op_zl__"   ~> Fun  [arg "x", arg "y"] (App2 (Var "op_zeze__") (App2 (Var "compare") (Var "x") (Var "y")) (Var "Lt"))
        , "op_zgze__" ~> Fun  [arg "x", arg "y"] (App2 (Var "op_zsze__") (App2 (Var "compare") (Var "x") (Var "y")) (Var "Lt"))
        , "op_zg__"   ~> Fun  [arg "x", arg "y"] (App2 (Var "op_zeze__") (App2 (Var "compare") (Var "x") (Var "y")) (Var "Gt"))
        ]
    , "GHC.Base.Functor" =:
        [ "op_zlzd__" ~> Fun [arg "x"] (App1 (Var "fmap") (App1 (Var "GHC.Base.const") (Var "x")))
        ]
    , "GHC.Base.Applicative" =:
        [ "op_ztzg__" ~> Fun [arg "x", arg "y"]
            (let const_id = App1 (Var "GHC.Base.const") (Var "GHC.Base.id") in
            App2 (Var "op_zlztzg__") (App2 (Var "GHC.Base.fmap") const_id (Var "x")) (Var "y"))
        {-
        , "op_zlzt__" ~> Fun [arg "x", arg "y"]
            (let const    = Var "GHC.Base.const" in
            App2 (Var "op_zlztzg__") (App2 (Var "GHC.Base.fmap") const    (Var "x")) (Var "y"))
        -}
        ]
    , "GHC.Base.Monoid" =:
        [ "mconcat" ~> App2 (Var "GHC.Base.foldr") (Var "mappend") (Var "mempty")
        ]
    , "GHC.Base.Monad" =:
        [ "return_" ~> Var "GHC.Base.pure"
        , "op_zgzg__" ~> Var "GHC.Base.op_ztzg__"
        , "fail" ~> Fun [arg "x"] (Var "missingValue")
        ]
    ]
  where
   (=:) = (,)
   infix 0 =:
   m ~> d  = (toCoqName m, d)
   arg       = Inferred Coq.Explicit . Ident

builtInAxioms :: [(Ident, Term)]
builtInAxioms =
    [ "patternFailure" =: Forall [ Inferred Implicit (Ident "a") ] a
    , "missingValue"   =: Forall [ Inferred Implicit (Ident "a") ] a
    , "unsafeFix"      =: Forall [ Inferred Implicit (Ident "a") ] ((a `Arrow` a) `Arrow` a)
    ]
  where
   a = Var "a"
   (=:) = (,)
   infix 0 =:


evalConversion :: Monad m => Edits -> ConversionT m a -> m a
evalConversion _edits = evalVariablesT . (evalStateT ?? ConversionState{..}) where
  __currentModule     = Nothing
  __currentDefinition = Nothing

  _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
  _constructorTypes  = M.fromList [ (d,t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
  _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
  _recordFieldTypes  = M.empty
  _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
--  _memberSigs        = M.empty
  _defaultMethods    =   builtInDefaultMethods
  _fixities          = M.empty
  _axioms            = M.fromList builtInAxioms

  _typecheckerEnvironment = Nothing

  __unique = 0

-- Currently, this checks the /per-module/ renamings _without_ a qualified name,
-- and the /global/ renamings _with_ a qualified name.  I think that's ok.
withCurrentModuleOrNone :: ConversionMonad m => Maybe ModuleName -> m a -> m a
withCurrentModuleOrNone newModule = gbracket setModule restoreModule . const
  where
  setModule = _currentModule <<.= newModule
  restoreModule oldModule = _currentModule .= oldModule

withNoCurrentModule :: ConversionMonad m => m a -> m a
withNoCurrentModule = withCurrentModuleOrNone Nothing

withCurrentModule :: ConversionMonad m => ModuleName -> m a -> m a
withCurrentModule = withCurrentModuleOrNone . Just

maybeWithCurrentModule :: ConversionMonad m => Maybe ModuleName -> m a -> m a
maybeWithCurrentModule = maybe id withCurrentModule

withCurrentDefinition :: ConversionMonad m => Ident -> m a -> m a
withCurrentDefinition newDef = gbracket set restore . const
  where
  set = _currentDefinition <<.= Just newDef
  restore oldDef = _currentDefinition .= oldDef

fresh :: ConversionMonad m => m Natural
fresh = _unique <<+= 1

gensym :: ConversionMonad m => Text -> m Ident
gensym name = do u <- fresh
                 pure $ name <> "_" <> T.pack (show u) <> "__"

-- Mostly for point-free use these days
rename :: ConversionMonad m => HsNamespace -> Ident -> Ident -> m ()
rename ns x x' = renamed ns x ?= x'
{-# INLINABLE rename #-}

localizeConversionState :: ConversionMonad m => m a -> m a
localizeConversionState = gbracket get
                                   (\cs -> do u <- use _unique
                                              put $ cs & _unique .~ u)
                        . const

throwProgramError :: MonadIO m => String -> m a
throwProgramError = liftIO . throwGhcExceptionIO . ProgramError

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = throwProgramError $ what ++ " unsupported"

editFailure :: MonadIO m => String -> m a
editFailure what = throwProgramError $ "Could not apply edit: " ++ what

getFixity :: ConversionMonad m => Ident -> m (Maybe (Coq.Associativity, Coq.Level))
getFixity ident = do
   state <- get
   return $ M.lookup ident (_fixities state)

recordFixity :: ConversionMonad m => Ident -> (Coq.Associativity, Coq.Level) -> m ()
recordFixity id assoc = do
   state <- get
   let m = _fixities state
   case M.lookup id m of
     Just _v  -> throwProgramError $ "Multiple fixities for " ++ show id
     Nothing -> put (state { _fixities = (M.insert id assoc m) })

lookupTyThing :: ConversionMonad m => GHC.Name -> m (Maybe TyThing)
lookupTyThing name = do
    env <- fmap tcg_type_env <$> use typecheckerEnvironment
    -- Lookup in this module
    case (lookupNameEnv ?? name) =<< env of
        Just thing -> pure $ Just thing
        Nothing    -> lookupName name

skipModulesBy :: ConversionMonad m => (a -> ModuleName) -> [a] -> m [a]
skipModulesBy f = filterM $ \a -> use $ edits.skippedModules.contains (f a).to not

skipModules :: ConversionMonad m => [ModuleName] -> m [ModuleName]
skipModules = skipModulesBy id
