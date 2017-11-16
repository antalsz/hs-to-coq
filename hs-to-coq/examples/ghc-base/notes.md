* Generated modules, what are we skipping in them and why?

  GHC/List
    - five skipped function (take,drop,replicate, scanr, splitAt)
	  are total functions but Coq can't prove easily
	  these are defined in prelude.v
    - one skipped is concatMap, mapped to Coq's flat_map (should we do this?)
	- rest are all partial functions
  Data/Tuple
    - nothing skipped
  Data/Maybe
    - fromJust (partial)
  Data/Function
    - fix_ is partial
	- on uses (.*.) as a variable name
  Data/Ord
    - cannot derive Eq instance for Down, so instance added to "midamble"
  Data/Functor
    - nothing skipped
  Data/Monoid
    - many F/A/M instances rely on Data.Coerce
	- many Monoid instances trigger tyvar issue
  Control/Monad
    - three partial functions
  Data/OldList
    - 4 partial functions
	- 9 not obviously total functions
	- 10 bugs/unimplemented stuff
	- 10 relies on one of the above
  Data/Traversable
    - 9 instances can't do due to issue 9:
	- 3 failure from other modules (functor for product/sum/dual)
	- 2 out of scope (array, generics)
	- 1 partial (applicative ziplist)
	- 2 type class instances refer to same class
	- issue with type inference
  Data/Void
    - skip 5 instances for classes we don't support (Show, Read, Data)
  Data/List
    - empty module
  Data/Bool
    - none
  GHC/Base
    - FAM instances for types with variables
	- prelude types and functions replaced with Coq versions
	- IO
	- partial functions (until)
	- unboxed types
	- Alternative/MonadPlus

  Control/Monad/Fail
    - IO instance

  Data/Foldable
    - Heavy use of Data.Coerce as type class instances

  Data/Functor/Identity
    - hash_compose, a helper function for Coercible type class
	- several type class instances (Foldable, Traversible) implicitly skipped

  Control/Applicative
	- skip ZipList because its Applicative instance is coinductive (using repeat)

  Data/Functor/Classes
	- just read and show instances


* What stops these modules from being generated?

- GHC/BaseInstances
  This is a manual part of Base.hs
  Bug in instance generation for partially applied type constructors
  (e.g. monoid instance for list).

- Data/FoldableInst
  This is the manual part of Data.Foldable
  Instances for the option type.
  One of the methods for this refers to the class. Currently resolve
  using helper function `anyWith`.

- Data/Type/Equality
  functional dependencies

- Control/Category
  Type inference: need to annotate type of cat in class definition.
  Class Category cat := {
    id : forall {a}, cat a a ;
    op_z2218U__ : forall {b} {c} {a}, cat b c -> cat a b -> cat a c }.

- Data/Functor/Const
  Type inference: need to annotate type of first argument to Const
  Deriving: most of the functionality of this module comes from
  type class deriving (Data.coerce)
  (NOTE: most of the instances are NOT available)

- Control/Arrow
  Type inference: need to annotate parameter to ArrowMonad
  Bug in instance generation

- GHC/Char
- GHC/Num
- GHC/Real
- Data/Bits
   Lots of unboxed types in these modules for primitive numeric types.
   Better to adapt by hand since we need to map the operations to Coq
   library ones anyways.

- GHC/Unicode
   I'm removing this from base. It relies on a bunch of C functions that
   we don't have, so it is not worth including. This also means we shouldn't
   generate Data.Char, which only has functions that wrap the unicode
   definitions.

- Data/Either
   Not a big file, but issue 9 interferes with its main purpose:
   functor instances for the sum type.
   Manually added Eq, Ord instances b/c of deriving

- GHC/Enum
  Lots of primitive types.

- Data/Proxy

- Prelude

------------------------------------------------------------------------------

* What features/modules are missing from Base?

- Partial modules

Control.Monad.Fix

- Modules that support imperative features

Control.Concurrent
Control.Concurrent.Chan
Control.Concurrent.MVar
Control.Concurrent.QSem
Control.Concurrent.QSemN
Control.Exception
Control.Exception.Base
Control.Monad.IO.Class
Control.Monad.ST
Control.Monad.ST.Lazy
Control.Monad.ST.Lazy.Safe
Control.Monad.ST.Lazy.Unsafe
Control.Monad.ST.Safe
Control.Monad.ST.Strict
Control.Monad.ST.Unsafe
Control.Monad.Zip
Data.IORef
Data.Ix
Data.STRef
Data.STRef.Lazy
Data.STRef.Strict
Foreign.C
Foreign.C.Error
Foreign.C.String
Foreign.C.Types
Foreign.Concurrent
Foreign.ForeignPtr
Foreign.ForeignPtr.Safe
Foreign.ForeignPtr.Unsafe
Foreign.Marshal
Foreign.Marshal.Alloc
Foreign.Marshal.Array
Foreign.Marshal.Error
Foreign.Marshal.Pool
Foreign.Marshal.Safe
Foreign.Marshal.Unsafe
Foreign.Marshal.Utils
Foreign.Ptr
Foreign.Safe
Foreign.StablePtr
Foreign.Storable
GHC.Arr
GHC.Conc
GHC.Conc.IO
GHC.Conc.Signal
GHC.Conc.Sync
GHC.Conc.Windows
GHC.ConsoleHandler
GHC.IO
GHC.IO.Buffer
GHC.IO.BufferedIO
GHC.IO.Device
GHC.IO.Encoding
GHC.IO.Encoding.CodePage
GHC.IO.Encoding.CodePage.API
GHC.IO.Encoding.CodePage.Table
GHC.IO.Encoding.Failure
GHC.IO.Encoding.Iconv
GHC.IO.Encoding.Latin1
GHC.IO.Encoding.Types
GHC.IO.Encoding.UTF16
GHC.IO.Encoding.UTF32
GHC.IO.Encoding.UTF8
GHC.IO.Exception
GHC.IO.FD
GHC.IO.Handle
GHC.IO.Handle.FD
GHC.IO.Handle.Internals
GHC.IO.Handle.Lock
GHC.IO.Handle.Text
GHC.IO.Handle.Types
GHC.IO.IOMode
GHC.IO.Unsafe
GHC.IOArray
GHC.IORef
GHC.MVar
GHC.Environment
GHC.Event
GHC.ExecutionStack
GHC.ExecutionStack.Internal
GHC.PArr
GHC.Pack
GHC.Profiling
GHC.Ptr
GHC.RTS.Flags
GHC.ST
GHC.STRef
GHC.Stack
GHC.Stack.CCS
GHC.Stack.Types
GHC.Stable
GHC.StaticPtr
System.CPUTime
GHC.Storable
GHC.TopHandler
GHC.Windows
System.Console.GetOpt
System.Environment
System.Exit
System.IO
System.IO.Error
System.IO.Unsafe
System.Info
System.Mem
System.Mem.StableName
System.Mem.Weak
System.Posix.Internals
System.Posix.Types
System.Timeout
GHC.Stats

- marshalling/unmarshalling

GHC.Read
GHC.Show
Text.Printf

- "empty" or deprecated modules

GHC.Constants
Control.Monad.Instances

- Modules that wrap GHC language features not
  found in Coq.

Data.Type.Coercion
Data.Coerce

Data.Data
Data.Dynamic
Data.Typeable
Data.Unique

Debug.Trace

GHC.Fingerprint
GHC.Fingerprint.Type

GHC.Foreign
GHC.ForeignPtr
GHC.GHCi
GHC.Generics

GHC.Exts

GHC.Weak

Type.Reflection
Type.Reflection.Unsafe
Unsafe.Coerce

- What are these?

GHC.Desugar
GHC.Err
GHC.Exception


- Modules with features we haven't implemented yet


- All other modules

X Control.Applicative
X Control.Arrow
X Control.Category
X Control.Monad
Data.Bifoldable
Data.Bifunctor
Data.Bitraversable
X Data.Bits
X Data.Bool
X Data.Char
Data.Complex   -- needs floating point
X Data.Either
X Data.Eq
Data.Fixed
X Data.Foldable
X Data.Function
X Data.Functor
X Data.Functor.Classes
Data.Functor.Compose
X Data.Functor.Const
X Data.Functor.Identity
Data.Functor.Product
Data.Functor.Sum
Data.Int
Data.Kind  -- completely ignored
X Data.List
Data.List.NonEmpty -- partial functions aren't really partial, :| constructor
X Data.Maybe
X Data.Monoid
X Data.Ord
X Data.Proxy
Data.Ratio
Data.Semigroup
Data.String
X Data.Traversable
X Data.Tuple
Data.Type.Bool -- type families
X Data.Type.Equality
Data.Version
X Data.Void
Data.Word
X GHC.Base
X GHC.Char
X GHC.Enum
GHC.Float
GHC.Float.ConversionUtils
GHC.Float.RealFracMethods
GHC.Int
X GHC.List
GHC.Natural  -- needs unboxed ints
X GHC.Num
X GHC.OldList
GHC.OverloadedLabels -- needs symbol
X GHC.Real
GHC.Records
GHC.TypeLits -- needs type families
GHC.TypeNats -- needs type families
X GHC.Unicode
GHC.Word
Numeric.Natural -- unboxed ints
Text.ParserCombinators.ReadP
Text.ParserCombinators.ReadPrec
Text.Read
Text.Read.Lex
Text.Show
Text.Show.Functions
