# hs-to-coq

This repository contains a converter from Haskell code to equivalent Coq code,
as part of the [CoreSpec] component of the [DeepSpec] project.

It it described in the CPP'18 paper [“Total Haskell is Reasonable Coq”](https://arxiv.org/abs/1711.09286) by
Antal Spector-Zabusky, Joachim Breitner, Christine Rizkallah, and Stephanie Weirich.

# Requirements

`hs-to-coq` uses GHC-8.4.1, Coq 8.7.2 and ssreflect.

# Compilation

The recommended way of building `hs-to-coq` is to use `stack`. If you have not
setup stack before, run:

    stack setup

To build `hs-to-coq`, then run

    stack build

# Building the `base` library

This repository comes with a version of (parts of the) Haskell base library
converted to Coq, which you will likely need if you want to verify Haskell
code.

You must have Coq 8.7.2 and ssreflect to build the base library. To install
these tools:

  1. `opam repo add coq-released https://coq.inria.fr/opam/released` (for
     SSReflect and MathComp)
  2. `opam update`
  3. `opam install coq.8.7.2 coq-mathcomp-ssreflect.1.6.4`

Once installed, you can build the base library with

    make -C base

Th directory `base-thy/` contains auxillary definitions and lemmas, such as
lawful type-class instances. You can build these with

    make -C base-thy

# Using the tool

To use the tool, run it (using `stack`), passing the Haskell file to be
translated and an output directory to write to:

    stack exec hs-to-coq -- -o output-directory/ Input/File.hs

Very likely you want to make use of the `base/` library. In that case, make
sure you pass `-e base/edits`.

Have a look at the example directories, e.g. `examples/successors`, for a
convenient `Makefile` based setup.

## Edits

`edits` file contains directives to `hs-to-coq` for ignoring or
transforming some Haskell constructs into proper Coq.

The following directives are available:


```
skip module <qualified module name>
```

Ignores the given module

```
skip method <typeclass> <method name>
```

Ignores given method in given typeclass, e.g. don't try to generate
Coq code from it.

```
rename type <qualified type name> = <qualified type name>
```

Renames given type. Coq does not support declaring operator-like data
types.

```
remame value <qualified constructor> = <qualified name>
```

Renames given constructor.


```termination <qualified function name> <termarg>```

If `qualid` is not structurally recursive, `termarg` can be one of 
    - `deferred`
    - `corecursive`
    - `{ struct qualid }`
    - `{ measure id ... }`
	- `{ wf id qualid }`


Edits can be localized to particular definitions. You can write

```in Foo.bar <any edit>```
and the edit will only apply during the translation of `Foo.bar`.
So if you need to rename a type or a function, or apply a rewrite rule, in
just one function, you can.



### Common Uses

It is common in Haskell to have the following code:

```
module Foo where
...
newtype SomeType = SomeType { someFiled :: Integer }
```

Coq has a single namespace for types and values hence the type name
will conflict with constructor name. One can pass `-e edit` file
containing custom directives to ensure correctness of generated code
with the following directive:

```
remame value Foo.SomeType = Foo.MkSomeType
```

# Interface files

When translating a module `Foo` that uses a type class or algebraic data type
from another file `Bar`, then `hs-to-coq` needs to know some information about
these types. Therefore, when it creates `Bar.v`, it also writes an *interface
file* `Bar.h2ci`. This interface file is loaded on demand during the translation
of `Foo`, when and if it needs the information about `Bar`.

Some notes about interface file:

 * You need to pass `--iface-dir foo/` to make `hs-to-coq` search for interface
   files in `foo/`. This flag can be used multiple times. Usually, you will
   at least passt `--iface-dir path/to/base --iface-dir output/` where `output/`
   is the argument to `-o`.

 * When it cannot find an interface file, `hs-to-coq` complains loudly (but still
   produces output). It is expected that the user will fix the problem, either
   by processing the dependent-upon file first, or by skipping the offending
   declarations.

 * `hs-to-coq` can help with figuring out the right dependency order. If you pass
   `--dependency-dir deps` to it, it will create a file `deps/Foo.mk` after processing
   module `Foo`. This will, in `Makefile` syntax, list all read interface files
   as dependencies of `Foo.v`, ensuring that from now on all files are built in
   the right order.

 * Skipping instances prevents hs-to-coq from trying to load the interface
   files of the class’es module.

 * Coq types as well as information about the type classes `Eq` and `Ord` are hard-coded
   in `src/lib/HsToCoq/ConvertHaskell/BuiltIn.hs`.

 * When you have a manual file that defines types or type classes, you may have
   to create a faux interface files. Simply create a text file that is an valid
   empty yaml file (e.g. '{}').



# Other directories

* The `examples/` directories contains a number of example translation and
  verification projects, including

  * [containers](examples/containers) Modules from the `containers` library, 
	including `Data.Set` and `Data.IntSet`
  * [bag](examples/bag) Multiset implementation from GHC's implemention
  * [successors](examples/successors) Successors Monad
  * [compiler](examples/compiler) Hutton's razor
  * [quicksort](examples/quicksort) Quicksort
  * [rle](examples/rle) Run-length encoding
  * [coinduction](examples/coinduction) Translating infinite data structures
  * [base-src](examples/base-src) The sources of the `base/` directory
  * [tests](examples/tests) Simple unit-tests
  * [base-tests](examples/base-tests) Unit-tests that require `base/` 
  
* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/
