Interface files
===============


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
