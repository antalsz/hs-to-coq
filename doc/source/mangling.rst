.. _mangling:

========================
Identifiers and Notation
========================

Most Haskell names can be reused as Coq names (fully qualified). However, due
to differences in parsing and keywords, ``hs-to-coq`` must sometimes modify the
generated identifiers.

Coq keywords
------------

The following Coq keywords are automatically translated with an extra ``_``
following them:

.. code-block:: Coq

     Set Type Prop fun fix forall return mod match as
     cons pair nil for is with left right exists


Operators
---------

Coq does not allow the definition of identifiers composed with punctuation.

To name these identifiers, ``hs-to-coq`` uses GHC's `z-encoding
<https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames>`_
to give textual names to operators. These textual operator names are preceded by
``op_`` and followed by two underscores.


For example, the Haskell identifier ``==`` is translated to the Coq identifier
``GHC.Base.op_zeze__``

Notation
--------

Nevertheless, we want users to be able to use the operator syntax, (e.g.
``==``) in the output. Therefore, ``hs-to-coq`` defines appropriate Coq syntax for it:

.. code-block:: Coq

  Notation "'_==_'" := (op_zeze__).
  Infix "==" := (op_zeze__) (no associativity, at level 70).

This works fine within the given module (here: ``GHC.Base``), and within every module that imports ``GHC.Base``. But in general, ``hs-to-coq`` does not *import* modules (it only *requires* them, using ``Require GHC.Base.``), so the notation is not visible.

Therefore, the translated module will contain a ``Notations`` submodule at the end:

.. code-block:: Coq

  Module Notations.
  Infix "GHC.Base.==" := (op_zeze__) (no associativity, at level 70).
  Notation "'_GHC.Base.==_'" := (op_zeze__).
  End Notations.

When a module needs to be required, and any of the imported names look like operators, then ``hs-to-coq`` imports the the contained ``Notations`` module:

.. code-block:: Coq

   Require GHC.Base.
   Import GHC.Base.Notation.

This brings the “qualified operators” into scope.

In manually written modules (e.g. those containing the proofs), the user can choose to follow that example, and use all names and operators qualified, or they can ``Require Import GHC.Base``, and use all names and operators unqualified, and ignore the ``Notations`` module.

In the rare case that you need to define operators in the preamble, then you have to manually add the ``Notations`` as shown here. You put the definition of the syntax for the qualified in a nested module ``ManualNotation`` and use the ``manual notation`` edit to make ``hs-to-coq`` include the ``ManualNotation`` module in the generated ``Notation`` module.
