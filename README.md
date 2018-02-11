# hs-to-coq

This repository contains a converter from Haskell code to equivalent Coq code,
as part of the [CoreSpec] component of the [DeepSpec] project.

It it described in the CPP'18 paper [“Total Haskell is Reasonable Coq”](https://arxiv.org/abs/1711.09286) by
Antal Spector-Zabusky, Joachim Breitner, Christine Rizkallah, and Stephanie Weirich.

# Requirements

`hs-to-coq` uses GHC-8.0, Coq 8.7.1 and ssreflect.

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

You must have Coq 8.7.1 and ssreflect to build the base library. To install
these tools:

  1. `opam repo add coq-released https://coq.inria.fr/opam/released` (for
     SSReflect and MathComp)
  2. `opam update`
  3. `opam install coq.8.7.1 coq-mathcomp-ssreflect.1.6.1`

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


# Other directories

* The `examples/` directories contains a number of example translation and
  verification projects, including

  * [successors](examples/successors) Successors Monad
  * [compiler](examples/compiler) Hutton's razor
  * [bag](examples/bag) Multiset implementation
  * [quicksort](examples/quicksort) Quicksort
  * [rle](examples/rle) Run-length encoding
  * [tests](examples/tests) Simple unit-tests
  * [base-src](examples/base-src) The sources of the `base/` directory

* `structural-isomorphism-plugin`: (In progress.)  A GHC plugin that connects
   the re-extracted converted code back into GHC, allowing us to run Haskell
   programs against verified/verifiable code.  Currently does not work.


[CoreSpec]: https://deepspec.org/entry/Project/Haskell+CoreSpec
[DeepSpec]: http://www.deepspec.org/
