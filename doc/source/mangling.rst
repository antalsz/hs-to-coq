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

