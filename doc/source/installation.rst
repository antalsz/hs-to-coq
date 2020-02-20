============
Installation
============

Latest release
--------------

Not yet released. Eventually `hs-to-coq` will be available on
`hackage <https://hackage.haskell.org/>`_.

Development version
-------------------

The source code for the development version is available via github. This
repository includes everything that you need.
 
.. code-block:: shell

    $ git clone https://github.com/antalsz/hs-to-coq.git
    $ cd hs-to-coq

The recommended way of building `hs-to-coq` is to use the `stack` tool. If you
have not setup stack before

.. code-block:: shell

   $ stack setup

To build ``hs-to-coq``

.. code-block:: shell

   $ stack build

To compile `hs-to-coq` from scratch, we recommend GHC 8.4.1.

Coq Requirements
----------------

This repository comes with a Coq version of the Haskell `base
<https://github.com/antalsz/hs-to-coq/tree/master/base>`_ library, used by the
output of ``hs-to-coq``.

You must have `Coq 8.8.1` and `ssreflect` to build the base library. You can install
these tools using `opam <https://opam.ocaml.org/>`_.

.. code-block::  shell

    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam update
    $ opam install coq.8.8.1 coq-mathcomp-ssreflect.1.6.4


Once installed, you can build the base library from the project root with

.. code-block:: shell

    $ make -C base

Th directory `base-thy
<https://github.com/antalsz/hs-to-coq/tree/master/base-thy>`_ contains auxillary
definitions and lemmas, such as lawful type-class instances. You can build
these with

.. code-block:: shell

    $ make -C base-thy

Test your hs-to-coq installation
--------------------------------

To test whether your `hs-to-coq` installation is successful, you can try to
compile the examples that are distributed with the tool.

Some examples use git submodules, so run

.. code-block:: shell

    $ git submodule update --init --recursive

once first to download all dependencies.

Then, compile all of the examples with

.. code-block:: shell

    $ cd examples
    $ ./boot.sh

The flag `noclean` will recompile everything without first deleting the old
versions.

.. code-block:: shell

    $ ./boot.sh noclean

The flag `quick` is like the above but doesn't run the tests.

.. code-block:: shell

    $ ./boot.sh quick


Troubleshooting
--------------------------------

1. lndir: command not found

On Mac OSX, you may need to install XQuartz and imake to run `examples/boot.sh`. 

If you get the error message while trying to run `./boot.sh`: 

.. code-block:: shell

    > lndir: command not found
   
The following commands will install XQuartz and imake through `brew`:

.. code-block:: shell

    $ brew cask install xquartz
    $ brew install imake
    
Depending on your `brew cask` setup, you may also need to update your $PATH
variable. 

.. code-block:: shell

    $ export PATH=$PATH:/usr/X11/bin >> ~/.bash_profile
    
2. git submodule update --init --recursive gives error fatal: Needed a single revision

Try removing the submodule directory that the error was triggered on, and run the command again. 
(i.e. If the error was on `examples/wc/wc`, a `rm -rf examples/wc/wc` followed by a
`git submodule update --init --recursive` will do the trick. 
