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
import Data.Bifunctor
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

import Data.List.NonEmpty (NonEmpty(..))

--------------------------------------------------------------------------------

data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Qualid]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

data ConversionState = ConversionState { __currentModule         :: !(Maybe ModuleName)
                                       , __currentDefinition     :: !(Maybe Qualid)
                                       , _edits                  :: !Edits
                                       , _constructors           :: !(Map Qualid [Qualid])
                                       , _constructorTypes       :: !(Map Qualid Qualid)
                                       , _constructorFields      :: !(Map Qualid ConstructorFields)
                                       , _recordFieldTypes       :: !(Map Qualid Qualid)
                                       -- types of class members
                                       -- , _memberSigs       :: !(Map Ident (Map Ident Signature))
                                       -- translated classes
                                       , _classDefns             :: !(Map Qualid ClassDefinition)
                                       , _defaultMethods         :: !(Map Qualid (Map Ident Term))
                                       , _fixities               :: !(Map Ident (Coq.Associativity, Coq.Level))
                                       , _typecheckerEnvironment :: !(Maybe TcGblEnv)
                                       , _axioms                 :: !(Map Qualid Term)
                                       , __unique                :: !Natural
                                       }
makeLenses ''ConversionState
-- '_currentModule', '_currentDefinition) and '_unique' are not exported

currentModule :: Getter ConversionState (Maybe ModuleName)
currentModule = _currentModule
{-# INLINABLE currentModule #-}

currentDefinition :: Getter ConversionState (Maybe Qualid)
currentDefinition = _currentDefinition
{-# INLINABLE currentDefinition #-}

renamed :: HsNamespace -> Qualid -> Lens' ConversionState (Maybe Qualid)
renamed ns x = edits.renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

type ConversionMonad m = (GhcMonad m, MonadState ConversionState m, MonadVariables Qualid () m)
type ConversionT m = StateT ConversionState (VariablesT Qualid () m)

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
{-    , ClassDefinition "Data.Foldable"
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
        ] -}

    , ClassDefinition "Data.Foldable.Foldable" [Inferred Explicit (Ident "t")] Nothing
      [("elem",Forall (Inferred Implicit (Ident "a") :| []) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Eq_")) (PosArg (Qualid (Bare "a")) :| [])) :| []) (Arrow (Qualid (Bare "a")) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "bool")))))),
        ("fold",Forall (Inferred Implicit (Ident "m") :| []) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Monoid")) (PosArg (Qualid (Bare "m")) :| [])) :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "m")) :| [])) (Qualid (Bare "m"))))),
        ("foldMap",Forall (Inferred Implicit (Ident "m") :| [Inferred Implicit (Ident "a")]) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Monoid")) (PosArg (Qualid (Bare "m")) :| [])) :| []) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Qualid (Bare "m")))) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "m")))))),
        ("foldl",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "a")]) (Arrow (Parens (Arrow (Qualid (Bare "b")) (Arrow (Qualid (Bare "a")) (Qualid (Bare "b"))))) (Arrow (Qualid (Bare "b")) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "b")))))),
        ("foldl'",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "a")]) (Arrow (Parens (Arrow (Qualid (Bare "b")) (Arrow (Qualid (Bare "a")) (Qualid (Bare "b"))))) (Arrow (Qualid (Bare "b")) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "b")))))),
        ("foldr",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "b"))))) (Arrow (Qualid (Bare "b")) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "b")))))),
        ("foldr'",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "b"))))) (Arrow (Qualid (Bare "b")) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "b")))))),
        ("length",Forall (Inferred Implicit (Ident "a") :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "GHC.Num.Int")))),
        ("null",Forall (Inferred Implicit (Ident "a") :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "bool")))),
        ("product",Forall (Inferred Implicit (Ident "a") :| []) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Num.Num")) (PosArg (Qualid (Bare "a")) :| [])) :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "a"))))),
        ("sum",Forall (Inferred Implicit (Ident "a") :| []) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Num.Num")) (PosArg (Qualid (Bare "a")) :| [])) :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (Qualid (Bare "a"))))),
        ("toList",Forall (Inferred Implicit (Ident "a") :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (App (Qualid (Bare "list")) (PosArg (Qualid (Bare "a")) :| []))))]


{-    , ClassDefinition "Data.Traversable"
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
-}

    , ClassDefinition "Data.Traversable.Traversable"
      [Inferred Explicit (Ident "t"),
       Generalized Implicit (App (Qualid (Bare "GHC.Base.Functor"))
                              (PosArg (Qualid (Bare "t")) :| [])),
       Generalized Implicit (App (Qualid (Bare "Data.Foldable.Foldable"))
                              (PosArg (Qualid (Bare "t")) :| []))
      ]
      Nothing
      [("mapM",
         Forall (Inferred Implicit (Ident "m") :| [Inferred Implicit (Ident "a"),Inferred Implicit (Ident "b")]) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Monad")) (PosArg (Qualid (Bare "m")) :| [])) :| []) (Arrow (Parens (Arrow (Qualid (Bare "a")) (App (Qualid (Bare "m")) (PosArg (Qualid (Bare "b")) :| [])))) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (App (Qualid (Bare "m")) (PosArg (Parens (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "b")) :| []))) :| [])))))),
        ("sequence",Forall (Inferred Implicit (Ident "m") :| [Inferred Implicit (Ident "a")]) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Monad")) (PosArg (Qualid (Bare "m")) :| [])) :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Parens (App (Qualid (Bare "m")) (PosArg (Qualid (Bare "a")) :| []))) :| [])) (App (Qualid (Bare "m")) (PosArg (Parens (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| []))) :| []))))),
        ("sequenceA",Forall (Inferred Implicit (Ident "f") :| [Inferred Implicit (Ident "a")]) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Applicative")) (PosArg (Qualid (Bare "f")) :| [])) :| []) (Arrow (App (Qualid (Bare "t")) (PosArg (Parens (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "a")) :| []))) :| [])) (App (Qualid (Bare "f")) (PosArg (Parens (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| []))) :| []))))),
        ("traverse",Forall (Inferred Implicit (Ident "f") :| [Inferred Implicit (Ident "a"),Inferred Implicit (Ident "b")]) (Forall (Generalized Implicit (App (Qualid (Bare "GHC.Base.Applicative")) (PosArg (Qualid (Bare "f")) :| [])) :| []) (Arrow (Parens (Arrow (Qualid (Bare "a")) (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "b")) :| [])))) (Arrow (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "a")) :| [])) (App (Qualid (Bare "f")) (PosArg (Parens (App (Qualid (Bare "t")) (PosArg (Qualid (Bare "b")) :| []))) :| []))))))]

    , ClassDefinition "Control.Arrow.Arrow" [Typed Ungeneralizable Explicit (Ident "a" :| []) (Arrow (Qualid (Bare "Type")) (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type")))),Generalized Implicit (App (Qualid (Bare "Control.Category.Category")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("op_zazaza__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "c'")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c'")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Infix (Qualid (Bare "c")) "*" (Qualid (Bare "c'"))) :| []))))),("op_ztztzt__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "b'"),Inferred Implicit (Ident "c'")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b'")) :| [])) (PosArg (Qualid (Bare "c'")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Infix (Qualid (Bare "b")) "*" (Qualid (Bare "b'"))) :| [])) (PosArg (Infix (Qualid (Bare "c")) "*" (Qualid (Bare "c'"))) :| []))))),("arr",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c")]) (Arrow (Parens (Arrow (Qualid (Bare "b")) (Qualid (Bare "c")))) (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])))),("first",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Infix (Qualid (Bare "b")) "*" (Qualid (Bare "d"))) :| [])) (PosArg (Infix (Qualid (Bare "c")) "*" (Qualid (Bare "d"))) :| [])))),("second",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Infix (Qualid (Bare "d")) "*" (Qualid (Bare "b"))) :| [])) (PosArg (Infix (Qualid (Bare "d")) "*" (Qualid (Bare "c"))) :| []))))]

    , ClassDefinition "Control.Arrow.ArrowZero" [Typed Ungeneralizable Explicit (Ident "a" :| []) (Arrow (Qualid (Bare "Type")) (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type")))),Generalized Implicit (App (Qualid (Bare "Arrow")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("zeroArrow",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c")]) (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])))]

    ,  ClassDefinition "Control.Arrow.ArrowPlus" [Typed Ungeneralizable Explicit (Ident "a" :| []) (Arrow (Qualid (Bare "Type")) (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type")))),Generalized Implicit (App (Qualid (Bare "ArrowZero")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("op_zlzpzg__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])))))]

    ,  ClassDefinition "Control.Arrow.ArrowChoice" [Inferred Explicit (Ident "a"),Generalized Implicit (App (Qualid (Bare "Arrow")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("op_zpzpzp__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "b'"),Inferred Implicit (Ident "c'")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b'")) :| [])) (PosArg (Qualid (Bare "c'")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "b'")) :| []))) :| [])) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "c")) :| [])) (PosArg (Qualid (Bare "c'")) :| []))) :| []))))),("left",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "d")) :| []))) :| [])) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "c")) :| [])) (PosArg (Qualid (Bare "d")) :| []))) :| [])))),("right",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "d")) :| [])) (PosArg (Qualid (Bare "b")) :| []))) :| [])) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "d")) :| [])) (PosArg (Qualid (Bare "c")) :| []))) :| [])))),("op_zbzbzb__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "d"),Inferred Implicit (Ident "c")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "d")) :| [])) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "c")) :| [])) (PosArg (Qualid (Bare "d")) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Parens (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| []))) :| [])) (PosArg (Qualid (Bare "d")) :| [])))))]

    , ClassDefinition "Control.Arrow.ArrowApply" [Typed Ungeneralizable Explicit (Ident "a" :| []) (Arrow (Qualid (Bare "Type")) (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type")))),Generalized Implicit (App (Qualid (Bare "Arrow")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("app",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c")]) (App (App (Qualid (Bare "a")) (PosArg (Infix (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) "*" (Qualid (Bare "b"))) :| [])) (PosArg (Qualid (Bare "c")) :| [])))]

    , ClassDefinition "Control.Arrow. ArrowLoop" [Inferred Explicit (Ident "a"),Generalized Implicit (App (Qualid (Bare "Arrow")) (PosArg (Qualid (Bare "a")) :| []))] Nothing [("loop",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "d"),Inferred Implicit (Ident "c")]) (Arrow (App (App (Qualid (Bare "a")) (PosArg (Infix (Qualid (Bare "b")) "*" (Qualid (Bare "d"))) :| [])) (PosArg (Infix (Qualid (Bare "c")) "*" (Qualid (Bare "d"))) :| [])) (App (App (Qualid (Bare "a")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| []))))]

      , ClassDefinition "Data.Functor.Eq1" [Inferred Explicit (Ident "f")] Nothing [("liftEq",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "bool"))))) (Arrow (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "a")) :| [])) (Arrow (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "b")) :| [])) (Qualid (Bare "bool"))))))]
        , ClassDefinition "Data.Functor.Ord1" [Inferred Explicit (Ident "f"),Generalized Implicit (Parens (App (Qualid (Bare "Eq1")) (PosArg (Qualid (Bare "f")) :| [])))] Nothing [("liftCompare",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "comparison"))))) (Arrow (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "a")) :| [])) (Arrow (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "b")) :| [])) (Qualid (Bare "comparison"))))))]

        , ClassDefinition "Data.Functor.Eq2" [Inferred Explicit (Ident "f")] Nothing [("liftEq2",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b"),Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "bool"))))) (Arrow (Parens (Arrow (Qualid (Bare "c")) (Arrow (Qualid (Bare "d")) (Qualid (Bare "bool"))))) (Arrow (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "d")) :| [])) (Qualid (Bare "bool")))))))]
          , ClassDefinition "Data.Functor.Ord2" [Inferred Explicit (Ident "f"),Generalized Implicit (Parens (App (Qualid (Bare "Eq2")) (PosArg (Qualid (Bare "f")) :| [])))] Nothing [("liftCompare2",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b"),Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Arrow (Qualid (Bare "b")) (Qualid (Bare "comparison"))))) (Arrow (Parens (Arrow (Qualid (Bare "c")) (Arrow (Qualid (Bare "d")) (Qualid (Bare "comparison"))))) (Arrow (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "d")) :| [])) (Qualid (Bare "comparison")))))))]

            , ClassDefinition "Control.Category.Category" [Typed Ungeneralizable Explicit (Ident "cat" :| []) (Arrow (Qualid (Bare "Type")) (Arrow (Qualid (Bare "Type")) (Qualid (Bare "Type"))))] Nothing [("id",Forall (Inferred Implicit (Ident "a") :| []) (App (App (Qualid (Bare "cat")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "a")) :| []))),("op_z2218U__",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "a")]) (Arrow (App (App (Qualid (Bare "cat")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (Arrow (App (App (Qualid (Bare "cat")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "b")) :| [])) (App (App (Qualid (Bare "cat")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])))))]

            , ClassDefinition "Data.Bifunctor.Bifunctor" [Inferred Explicit (Ident "p")] Nothing [("bimap",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b"),Inferred Implicit (Ident "c"),Inferred Implicit (Ident "d")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Qualid (Bare "b")))) (Arrow (Parens (Arrow (Qualid (Bare "c")) (Qualid (Bare "d")))) (Arrow (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "d")) :| [])))))),("first",Forall (Inferred Implicit (Ident "a") :| [Inferred Implicit (Ident "b"),Inferred Implicit (Ident "c")]) (Arrow (Parens (Arrow (Qualid (Bare "a")) (Qualid (Bare "b")))) (Arrow (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])) (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "b")) :| [])) (PosArg (Qualid (Bare "c")) :| []))))),("second",Forall (Inferred Implicit (Ident "b") :| [Inferred Implicit (Ident "c"),Inferred Implicit (Ident "a")]) (Arrow (Parens (Arrow (Qualid (Bare "b")) (Qualid (Bare "c")))) (Arrow (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "b")) :| [])) (App (App (Qualid (Bare "p")) (PosArg (Qualid (Bare "a")) :| [])) (PosArg (Qualid (Bare "c")) :| [])))))]

    ]
  where
   (=:) = (,)
   infix 0 =:

builtInDefaultMethods :: Map Qualid (Map Ident Term)
builtInDefaultMethods = fmap M.fromList $ M.fromList $ map (first unsafeIdentToQualid) $
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

    , "Data.Traversable.Traversable" =:
      ["mapM" ~> Qualid (Bare "traverse"),
       "sequence" ~> Qualid (Bare "sequenceA"),
       "sequenceA" ~> App (Qualid (Bare "traverse")) (PosArg (Qualid (Bare "GHC.Base.id")) :| []),
       "traverse" ~> Fun (Inferred Explicit (Ident "arg_0__") :| [])
                         (Coq.Match (MatchItem (Qualid (Bare "arg_0__")) Nothing Nothing :| []) Nothing
                         [Equation (MultPattern (QualidPat (Bare "f") :| []) :| [])
                              (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "sequenceA"))
                              :| [PosArg (App (Qualid (Bare "GHC.Base.fmap")) (PosArg (Qualid (Bare "f")) :| []))]))])]


    , "Data.Foldable.Foldable" =:
      -- inline the default definition of elem. Need an edit to modify this default....
      ["elem" ~> App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Parens (Fun (Inferred Explicit (Ident "arg_69__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_69__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (QualidPat (Bare "p") :| []) :| []) (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "Data.Monoid.getAny")) :| [PosArg (App (Qualid (Bare "foldMap")) (PosArg (Parens (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Any")) :| [PosArg (Qualid (Bare "p"))]))) :| []))]))]))) :| [PosArg (Qualid (Bare "GHC.Base.op_zeze__"))]),
       ("fold" ~> App (Qualid (Bare "foldMap")) (PosArg (Qualid (Bare "GHC.Base.id")) :| [])),
       ("foldMap" ~> Fun (Inferred Explicit (Ident "arg_1__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_1__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| []) :| []) (App (App (Qualid (Bare "foldr")) (PosArg (Parens (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "GHC.Base.mappend")) :| [PosArg (Qualid (Bare "f"))]))) :| [])) (PosArg (Qualid (Bare "GHC.Base.mempty")) :| []))])),
       ("foldl" ~> Fun (Inferred Explicit (Ident "arg_19__") :| [Inferred Explicit (Ident "arg_20__"),Inferred Explicit (Ident "arg_21__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_19__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_20__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_21__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "z"),QualidPat (Bare "t")]) :| []) (App (App (Qualid (Bare "Data.Monoid.appEndo")) (PosArg (Parens (App (Qualid (Bare "Data.Monoid.getDual")) (PosArg (Parens (App (App (Qualid (Bare "foldMap")) (PosArg (Parens (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Dual")) :| [PosArg (App (Qualid (Bare "Coq.Program.Basics.compose")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Endo")) :| [PosArg (App (Qualid (Bare "GHC.Base.flip")) (PosArg (Qualid (Bare "f")) :| []))]))]))) :| [])) (PosArg (Qualid (Bare "t")) :| []))) :| []))) :| [])) (PosArg (Qualid (Bare "z")) :| []))])),
       ("foldl'"~>Fun (Inferred Explicit (Ident "arg_24__") :| [Inferred Explicit (Ident "arg_25__"),Inferred Explicit (Ident "arg_26__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_24__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_25__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_26__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "z0"),QualidPat (Bare "xs")]) :| []) (Let "f'" [] Nothing (Fun (Inferred Explicit (Ident "arg_27__") :| [Inferred Explicit (Ident "arg_28__"),Inferred Explicit (Ident "arg_29__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_27__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_28__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_29__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "x") :| [QualidPat (Bare "k"),QualidPat (Bare "z")]) :| []) (App (Qualid (Bare "GHC.Base.op_zdzn__")) (PosArg (Qualid (Bare "k")) :| [PosArg (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "z")) :| [])) (PosArg (Qualid (Bare "x")) :| []))]))])) (App (App (App (App (Qualid (Bare "foldr")) (PosArg (Qualid (Bare "f'")) :| [])) (PosArg (Qualid (Bare "GHC.Base.id")) :| [])) (PosArg (Qualid (Bare "xs")) :| [])) (PosArg (Qualid (Bare "z0")) :| [])))])),
       ("foldr"~>Fun (Inferred Explicit (Ident "arg_4__") :| [Inferred Explicit (Ident "arg_5__"),Inferred Explicit (Ident "arg_6__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_4__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_5__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_6__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "z"),QualidPat (Bare "t")]) :| []) (App (App (Qualid (Bare "Data.Monoid.appEndo")) (PosArg (Parens (App (App (Qualid (Bare "foldMap")) (PosArg (Parens (App (Qualid (Bare "Data.Foldable.hash_compose")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Endo")) :| [PosArg (Qualid (Bare "f"))]))) :| [])) (PosArg (Qualid (Bare "t")) :| []))) :| [])) (PosArg (Qualid (Bare "z")) :| []))])),
       ("foldr'"~>Fun (Inferred Explicit (Ident "arg_9__") :| [Inferred Explicit (Ident "arg_10__"),Inferred Explicit (Ident "arg_11__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_9__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_10__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_11__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "z0"),QualidPat (Bare "xs")]) :| []) (Let "f'" [] Nothing (Fun (Inferred Explicit (Ident "arg_12__") :| [Inferred Explicit (Ident "arg_13__"),Inferred Explicit (Ident "arg_14__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_12__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_13__")) Nothing Nothing,MatchItem (Qualid (Bare "arg_14__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "k") :| [QualidPat (Bare "x"),QualidPat (Bare "z")]) :| []) (App (Qualid (Bare "GHC.Base.op_zdzn__")) (PosArg (Qualid (Bare "k")) :| [PosArg (App (App (Qualid (Bare "f")) (PosArg (Qualid (Bare "x")) :| [])) (PosArg (Qualid (Bare "z")) :| []))]))])) (App (App (App (App (Qualid (Bare "foldl")) (PosArg (Qualid (Bare "f'")) :| [])) (PosArg (Qualid (Bare "GHC.Base.id")) :| [])) (PosArg (Qualid (Bare "xs")) :| [])) (PosArg (Qualid (Bare "z0")) :| [])))])),
       ("length"~>App (App (Qualid (Bare "foldl'")) (PosArg (Parens (Fun (Inferred Explicit (Ident "arg_64__") :| [Inferred Explicit (Ident "arg_65__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_64__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_65__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "c") :| [UnderscorePat]) :| []) (App (Qualid (Bare "GHC.Num.op_zp__")) (PosArg (Qualid (Bare "c")) :| [PosArg (PolyNum 1)]))]))) :| [])) (PosArg (PolyNum 0) :| [])),
       ("null"~>App (App (Qualid (Bare "foldr")) (PosArg (Parens (Fun (Inferred Explicit (Ident "arg_61__") :| [Inferred Explicit (Ident "arg_62__")]) (Qualid (Bare "false")))) :| [])) (PosArg (Qualid (Bare "true")) :| [])),
       ("product"~>App (Qualid (Bare "Data.Foldable.hash_compose")) (PosArg (Qualid (Bare "Data.Monoid.getProduct")) :| [PosArg (App (Qualid (Bare "foldMap")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Product")) :| []))])),
       ("sum"~>App (Qualid (Bare "Data.Foldable.hash_compose")) (PosArg (Qualid (Bare "Data.Monoid.getSum")) :| [PosArg (App (Qualid (Bare "foldMap")) (PosArg (Qualid (Bare "Data.Monoid.Mk_Sum")) :| []))])),
       ("toList"~>Fun (Inferred Explicit (Ident "arg_54__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_54__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (QualidPat (Bare "t") :| []) :| []) (App (Qualid (Bare "GHC.Base.build")) (PosArg (Parens (Fun (Inferred Explicit (Ident "arg_55__") :| [Inferred Explicit (Ident "arg_56__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_55__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_56__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "c") :| [QualidPat (Bare "n")]) :| []) (App (App (App (Qualid (Bare "foldr")) (PosArg (Qualid (Bare "c")) :| [])) (PosArg (Qualid (Bare "n")) :| [])) (PosArg (Qualid (Bare "t")) :| []))]))) :| []))]))]



      , "Control.Arrow.Arrow" =:
        [("first",Parens (Fun (Inferred Explicit (Ident "arg_0__") :| []) (App (Qualid (Bare "op_ztztzt__")) (PosArg (Qualid (Bare "arg_0__")) :| [PosArg (Qualid (Bare "Control.Category.id"))])))),("op_zazaza__",Fun (Inferred Explicit (Ident "arg_11__") :| [Inferred Explicit (Ident "arg_12__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_11__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_12__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "g")]) :| []) (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "arr")) (PosArg (Parens (Fun (Inferred Explicit (Ident "arg_13__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_13__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (QualidPat (Bare "b") :| []) :| []) (App (Qualid (Bare "pair")) (PosArg (Qualid (Bare "b")) :| [PosArg (Qualid (Bare "b"))]))]))) :| [])) :| [PosArg (App (Qualid (Bare "op_ztztzt__")) (PosArg (Qualid (Bare "f")) :| [PosArg (Qualid (Bare "g"))]))]))])),("op_ztztzt__",Fun (Inferred Explicit (Ident "arg_4__") :| [Inferred Explicit (Ident "arg_5__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_4__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_5__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "g")]) :| []) (Let "swap" [] Nothing (Fun (Inferred Explicit (Ident "arg_6__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_6__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (ArgsPat (Bare "pair") (QualidPat (Bare "x") :| [QualidPat (Bare "y")]) :| []) :| []) (App (Qualid (Bare "pair")) (PosArg (Qualid (Bare "y")) :| [PosArg (Qualid (Bare "x"))]))])) (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "first")) (PosArg (Qualid (Bare "f")) :| [])) :| [PosArg (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "arr")) (PosArg (Qualid (Bare "swap")) :| [])) :| [PosArg (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "first")) (PosArg (Qualid (Bare "g")) :| [])) :| [PosArg (App (Qualid (Bare "arr")) (PosArg (Qualid (Bare "swap")) :| []))]))]))])))])),("second",Parens (Fun (Inferred Explicit (Ident "arg_2__") :| []) (App (Qualid (Bare "op_ztztzt__")) (PosArg (Qualid (Bare "Control.Category.id")) :| [PosArg (Qualid (Bare "arg_2__"))]))))]
       , "Control.Arrow.ArrowZero" =: []
       , "Control.Arrow.ArrowPlus" =: []
       , "Control.Arrow.ArrowChoice" =:
         [("left",Parens (Fun (Inferred Explicit (Ident "arg_18__") :| []) (App (Qualid (Bare "op_zpzpzp__")) (PosArg (Qualid (Bare "arg_18__")) :| [PosArg (Qualid (Bare "Control.Category.id"))])))),("op_zbzbzb__",Fun (Inferred Explicit (Ident "arg_30__") :| [Inferred Explicit (Ident "arg_31__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_30__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_31__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "g")]) :| []) (Let "untag" [] Nothing (Fun (Inferred Explicit (Ident "arg_32__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_32__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (ArgsPat (Bare "inl") (QualidPat (Bare "x") :| []) :| []) :| []) (Qualid (Bare "x")),Equation (MultPattern (ArgsPat (Bare "inr") (QualidPat (Bare "y") :| []) :| []) :| []) (Qualid (Bare "y"))])) (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "op_zpzpzp__")) (PosArg (Qualid (Bare "f")) :| [PosArg (Qualid (Bare "g"))])) :| [PosArg (App (Qualid (Bare "arr")) (PosArg (Qualid (Bare "untag")) :| []))])))])),("op_zpzpzp__",Fun (Inferred Explicit (Ident "arg_22__") :| [Inferred Explicit (Ident "arg_23__")]) (Coq.Match (MatchItem (Qualid (Bare "arg_22__")) Nothing Nothing :| [MatchItem (Qualid (Bare "arg_23__")) Nothing Nothing]) Nothing [Equation (MultPattern (QualidPat (Bare "f") :| [QualidPat (Bare "g")]) :| []) (Let "mirror" [Inferred Implicit (Ident "x"),Inferred Implicit (Ident "y")] (Just (Arrow (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "x")) :| [])) (PosArg (Qualid (Bare "y")) :| [])) (App (App (Qualid (Bare "sum")) (PosArg (Qualid (Bare "y")) :| [])) (PosArg (Qualid (Bare "x")) :| [])))) (Fun (Inferred Explicit (Ident "arg_24__") :| []) (Coq.Match (MatchItem (Qualid (Bare "arg_24__")) Nothing Nothing :| []) Nothing [Equation (MultPattern (ArgsPat (Bare "inl") (QualidPat (Bare "x") :| []) :| []) :| []) (App (Qualid (Bare "inr")) (PosArg (Qualid (Bare "x")) :| [])),Equation (MultPattern (ArgsPat (Bare "inr") (QualidPat (Bare "y") :| []) :| []) :| []) (App (Qualid (Bare "inl")) (PosArg (Qualid (Bare "y")) :| []))])) (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "left")) (PosArg (Qualid (Bare "f")) :| [])) :| [PosArg (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "arr")) (PosArg (Qualid (Bare "mirror")) :| [])) :| [PosArg (App (Qualid (Bare "Control.Category.op_zgzgzg__")) (PosArg (App (Qualid (Bare "left")) (PosArg (Qualid (Bare "g")) :| [])) :| [PosArg (App (Qualid (Bare "arr")) (PosArg (Qualid (Bare "mirror")) :| []))]))]))])))])),("right",Parens (Fun (Inferred Explicit (Ident "arg_20__") :| []) (App (Qualid (Bare "op_zpzpzp__")) (PosArg (Qualid (Bare "Control.Category.id")) :| [PosArg (Qualid (Bare "arg_20__"))]))))]


    ]
  where
   (=:) = (,)
   infix 0 =:
   m ~> d  = (toCoqName m, d)
   arg       = Inferred Coq.Explicit . Ident

builtInAxioms :: [(Qualid, Term)]
builtInAxioms = map (first Bare)
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

  _constructors      = M.fromList [ (unsafeIdentToQualid t, [unsafeIdentToQualid d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
  _constructorTypes  = M.fromList [ (unsafeIdentToQualid d, unsafeIdentToQualid t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
  _constructorFields = M.fromList [ (unsafeIdentToQualid d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
  _recordFieldTypes  = M.empty
  _classDefns        = M.fromList [ (unsafeIdentToQualid i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
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

withCurrentDefinition :: ConversionMonad m => Qualid -> m a -> m a
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
rename :: ConversionMonad m => HsNamespace -> Qualid -> Qualid -> m ()
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
