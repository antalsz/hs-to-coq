==========
Quickstart
==========

The easiest way to see how to use `hs-to-coq` is to look at the Makefiles in
the `examples` subdirectory.

Translating a single Haskell file
---------------------------------

Run `hs-to-coq` on a single Haskell module (called `Main.hs`) with the
following command.


.. code-block:: shell

     $ stack exec hs-to-coq -e <edits> Main.hs --iface-dir <base-dir> -o .

.. option:: -e <editfile> 

The `-e` command line argument tells `hs-to-coq` to use edits from the
specified edit file. In almost every case, you'll want to start with `edits
<https://github.com/antalsz/hs-to-coq/blob/master/base/edits>`_, the edit file
distributed with the base library. (You can provide multiple edit files by
repeating this flag.)

.. option:: --iface-dir <dir>

The `--iface-dir` command line argument tells `hs-to-coq` where to find the
interface files for the translated files in the `base` library. These
interface files contain extra information about the base library produced
during translation.


.. option:: -o <dir>

The `-o` argument specifies the output directory for the generated `.v` files.
In this case, it is the current directory.


An example translated in this way 
is `simple
<https://github.com/antalsz/hs-to-coq/blob/master/examples/simple>`_. Check
out the `Makefile` in the `examples/simple` subdirectory to see how
`hs-to-coq` is invoked with these arguments.

Local Edit files
----------------

Often, a particular file will require its own set of edits. These edits can be
provided with additional uses of the ``-e <editfile>`` command line argument.

An example that uses a local edit file is `intervals <https://github.com/antalsz/hs-to-coq/tree/master/examples/intervals>`_,
as described in Joachim Breitner's 
`blog post <https://www.joachim-breitner.de/blog/734-Finding_bugs_in_Haskell_code_by_proving_it>`_.

Any number of edit files may be provided to `hs-to-coq`.

Additional Coq definitions
--------------------------

Sometimes an `hs-to-coq` translation requires the addition of Coq definitions to the output.
These definitions can be specified via the `preamble` and `midamble`
arguments.

.. option:: -p <preamble-file>

Inserts the Coq definitions from the specified file at
the beginning of the output. 

For example, the `rle
<https://github.com/antalsz/hs-to-coq/blob/master/examples/rle>`_ example uses
a preamble to add additional imports to the output.

.. option:: -m <midamble-file>

Inserts the Coq definitions from the specified file in the output after the
type definitions but before any of the translated code or instance
declarations.

Only one preamble and one midamble can be provided to `hs-to-coq`.

Proofs
------

Once you have translated your module with `hs-to-coq`, you will want to 
prove stuff about it.  However, if your module includes definitions from 
`base`, you need to set up a `_CoqProject` file so that `coq` can find 
all of the necessary definitions. 

The Makefile in the rle_ example demonstrates
how this file can be constructed automatically.

[TODO: move map_map to base theory]


Translating a multi-file project
--------------------------------

Larger examples include
`containers
<https://github.com/antalsz/hs-to-coq/tree/master/examples/containers>`_  and
`transformers <https://github.com/antalsz/hs-to-coq/tree/master/examples/transformers>`_.

These examples use a `Makefile` to translate each module in the library
individually, using edit files, preambles and midambles specific to each 
module. It also includes the addition of manually written Coq files to the
library. 

For this scale of project, we recommend starting with one of the Makefiles
above and editing it to suit your application.

Avoiding `base`
---------------

`hs-to-coq` is designed to automatically use definitions from the `base`
library. However, it is sometimes possible to translate small examples so that
they are self contained, and only require definitions from Coq's standard
library.

An example project that takes this approach is:
https://github.com/mit-plv/riscv-coq

[TODO: make a general `base-free` edit file that connects as much of the
Haskell Prelude to the Coq standard library.]
