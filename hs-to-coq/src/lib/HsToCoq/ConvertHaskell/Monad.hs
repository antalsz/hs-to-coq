{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, ConversionT, evalConversion,
  -- * Types
  ConversionState(),
  currentModule, renamings, edits, constructors, constructorTypes, constructorFields, recordFieldTypes, classDefns, defaultMethods, fixities, renamed,
  ConstructorFields(..), _NonRecordFields, _RecordFields,
  -- * Operations
  maybeWithCurrentModule, withCurrentModule, withNoCurrentModule, withCurrentModuleOrNone,
  fresh, gensym,
  rename,
  localizeConversionState,
  -- * Access to the TcGblEnv
  setTcGblEnv,
  lookupTyThing,
  -- * Errors
  throwProgramError, convUnsupported, editFailure,
  -- * Fixity
  getFixity, recordFixity
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Foldable
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
import HsToCoq.Util.GHC.Module ()

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits

--------------------------------------------------------------------------------

data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Ident]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

data ConversionState = ConversionState { __currentModule    :: !(Maybe ModuleName)
                                       , _renamings         :: !Renamings
                                       , _edits             :: !Edits
                                       , _constructors      :: !(Map Ident [Ident])
                                       , _constructorTypes  :: !(Map Ident Ident)
                                       , _constructorFields :: !(Map Ident ConstructorFields)
                                       , _recordFieldTypes  :: !(Map Ident Ident)
                                       -- types of class members
                                       -- , _memberSigs        :: !(Map Ident (Map Ident Signature))
                                       -- translated classes
                                       , _classDefns        :: !(Map Ident ClassDefinition)
                                       , _defaultMethods    :: !(Map Ident (Map Ident Term))
                                       , _fixities          :: !(Map Ident (Coq.Associativity, Coq.Level))
                                       , __unique           :: !Natural
                                       , _tcGblEnv          :: TcGblEnv
                                       }
makeLenses ''ConversionState
-- '_currentModule' and '_unique' are not exported

currentModule :: Getter ConversionState (Maybe ModuleName)
currentModule = _currentModule
{-# INLINABLE currentModule #-}

renamed :: HsNamespace -> Ident -> Lens' ConversionState (Maybe Ident)
renamed ns x = renamings.at (NamespacedIdent ns x)
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
    [ ClassDefinition "Monoid" [Inferred Explicit (Ident "a")] Nothing
        [ "mappend" =: Var "a" `Arrow` Var "a" `Arrow` Var "a"
        , "mempty"  =: Var "a"
        , "mconcat" =: (Var "list" `App1` Var "a") `Arrow` Var "a"
        ]
    , ClassDefinition "Functor" [Inferred Explicit (Ident "f")] Nothing
        [ "fmap" =: (Forall [ Inferred Implicit (Ident "a")
                            , Inferred Implicit (Ident "b")] $
                     (Var "a" `Arrow` Var "b") `Arrow`
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b"))
        , "op_zlzd__" =: (Forall [ Inferred Implicit (Ident "a")
                            , Inferred Implicit (Ident "b")] $
                     (Var "b") `Arrow`
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b"))
        ]
    , ClassDefinition "Applicative"
        [ Inferred Explicit (Ident "f")
        , Generalized Implicit (App1 (Var "Functor") (Var "f"))
        ]
        Nothing
        [ "pure"  =: (Forall [Inferred Implicit (Ident "a")]  $
                      Var "a" `Arrow` App1 (Var "f") (Var "a"))
        , "op_zlztzg__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a" `Arrow` Var "b") `Arrow`
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b"))
        , "op_ztzg__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b") `Arrow`
                     App1 (Var "f") (Var "b"))
        , "op_zlzt__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     App1 (Var "f") (Var "b") `Arrow`
                     App1 (Var "f") (Var "a"))
        ]
    , ClassDefinition "Monad"
        [ Inferred Explicit (Ident "f")
        , Generalized Implicit (App1 (Var "Applicative") (Var "f"))
        ]
        Nothing
        [ "return_"  =: (Forall [Inferred Implicit (Ident "a")]  $
                      Var "a" `Arrow` App1 (Var "f") (Var "a"))
        , "op_zgzgze__" =:
            (Forall [ Inferred Implicit (Ident "a")
                    , Inferred Implicit (Ident "b")] $
                     App1 (Var "f") (Var "a") `Arrow`
                     (Var "a" `Arrow` App1 (Var "f") (Var "b")) `Arrow`
                     App1 (Var "f") (Var "b"))
        , "op_zgzg__" =:
           (Forall [ Inferred Implicit (Ident "a")
                   , Inferred Implicit (Ident "b")] $
                    App1 (Var "f") (Var "a") `Arrow`
                    App1 (Var "f") (Var "b") `Arrow`
                    App1 (Var "f") (Var "b"))
        , "fail" =:
           (Forall [ Inferred Implicit (Ident "a")] $
                    Var "String" `Arrow`
                    App1 (Var "f") (Var "a"))
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
    [ "Eq" =:
        [ "==" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "/=" (Var "y"))
        , "/=" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "==" (Var "y")) 
        ]
    , "Functor" =:
        [ "op_zlzd__" ~> Fun [arg "x"] (App1 (Var "fmap") (App1 (Var "const") (Var "x")))
        ]
    , "Applicative" =:
        [ "op_ztzg__" ~> Fun [arg "x", arg "y"]
            (let const_id = App1 (Var "const") (Var "id") in
            App2 (Var "op_zlztzg__") (App2 (Var "fmap") const_id (Var "x")) (Var "y"))
        , "op_zlzt__" ~> Fun [arg "x", arg "y"]
            (let const    = Var "const" in
            App2 (Var "op_zlztzg__") (App2 (Var "fmap") const    (Var "x")) (Var "y"))
        ]
    , "Monoid" =:
        [ "mconcat" ~> App2 (Var "foldr") (Var "mappend") (Var "mempty")
        ]
    , "Monad" =:
        [ "return_" ~> Var "pure"
        , "op_zgzg__" ~> Var "op_ztzg__"
        , "fail" ~> Fun [arg "x"] (Var "patternFailure")
        ]
    ]
  where
   (=:) = (,)
   infix 0 =:
   m ~> d  = (toCoqName m, d)
   arg       = Inferred Coq.Explicit . Ident

evalConversion :: GhcMonad m => Renamings -> Edits -> ConversionT m a -> m a
evalConversion _renamings _edits = evalVariablesT . (evalStateT ?? ConversionState{..}) where
  __currentModule = Nothing

  _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
  _constructorTypes  = M.fromList [ (d,t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
  _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
  _recordFieldTypes  = M.empty
  _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
--  _memberSigs        = M.empty
  _defaultMethods =   builtInDefaultMethods
  _fixities         = M.empty
  _tcGblEnv         = error "tcGblEnv not set yet"
  __unique = 0

withCurrentModuleOrNone :: ConversionMonad m => Maybe ModuleName -> m a -> m a
withCurrentModuleOrNone newModule = gbracket setModuleAndRenamings restoreModuleAndRenamings . const where
  setModuleAndRenamings = do
    oldModule <- _currentModule <<.= newModule
    newRenamings <- use $ edits.moduleRenamings
                        . maybe (like Nothing)
                                (at . T.pack . moduleNameString)
                                newModule
                        . non M.empty
    oldRenamings <- renamings <<%= (newRenamings `M.union`) -- (2)
    let overwrittenRenamings = oldRenamings `M.intersection` newRenamings

    pure (oldModule, overwrittenRenamings, newRenamings)

  restoreModuleAndRenamings (oldModule, overwrittenRenamings, newRenamings) = do
    _currentModule .= oldModule

    finalRenamings <- use renamings
    for_ (M.toList newRenamings) $ \(hs, coq) ->
      when (M.lookup hs finalRenamings == Just coq) $
        renamings.at hs .= M.lookup hs overwrittenRenamings

withNoCurrentModule :: ConversionMonad m => m a -> m a
withNoCurrentModule = withCurrentModuleOrNone Nothing

withCurrentModule :: ConversionMonad m => ModuleName -> m a -> m a
withCurrentModule = withCurrentModuleOrNone . Just

maybeWithCurrentModule :: ConversionMonad m => Maybe ModuleName -> m a -> m a
maybeWithCurrentModule = maybe id withCurrentModule

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

-- tcGblEnv stuff

setTcGblEnv :: ConversionMonad m => TcGblEnv -> m ()
setTcGblEnv = assign tcGblEnv

lookupTyThing :: ConversionMonad m => GHC.Name -> m (Maybe GHC.TyThing)
lookupTyThing name = do
    env <- use tcGblEnv
    -- Lookup in this module
    case lookupNameEnv (tcg_type_env env) name of
        Just thing -> return (Just thing)
        Nothing    -> lookupName name
