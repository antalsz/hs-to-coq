==========
Edit Files
==========

The edit files contain declarations that control the output of ``hs-to-coq`` on
various Haskell files.

.. todo:: Figure out the right domain for these declarations.

Skipping Haskell
----------------

Sometimes, ``hs-to-coq`` should ignore various Haskell declarations, because
they are not translatable, or they are out-of-scope, or for other reasons.

``skip`` – skip a function, type, class or instance
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **skip** *qualified_name*

Effect:
  During translation, ignore the declaration of the function, value, type, class or
  instance with the given *qualified_name*.

  This does not affect the translation of *uses* of the given name. This means
  that you can use other methods, e.g. a preamble. to make it available.

  The *qualified name* is the Coq name with module prefix: Reserved names have
  an underscore appended and renames have been applied.

  Skipping a type class also causes its instances to be skipped.

  Type class instances do not have names in Haskell, and ``hs-to-coq``
  generates a suitable name.  You might want to first attempt the translation
  and check the output for the precise name.


Examples:
   .. code-block:: shell

     skip Data.Function.fix_ # Note the mangled name!
     skip GHC.Base.String
     skip GHC.Real.Fractional
     skip Data.Monoid.Show__Last # an instance

``skip method`` – skip a method
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **skip** **method** *qualified_class* *method*

Effect:
  Omit the given method from the its class declaration, and also from all
  instances.

Examples:
   .. code-block:: shell

     skip method GHC.Base.Monad fail

``skip module`` – skip a module import
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **skip** **module** *module*

Effect:
  Do not generate an ``Require`` statemnt for *module*.

  This is mostly useful during development: ``hs-to-coq`` automatically requires
  the modules of all names it encounters, in the beginning of the resulting file.
  If there are names from modules that you do not intent to translate, Coq will
  already abort there. It is more convenient to have it fail when the name is actually
  encountered, to then decide how to fix it (e.g. using ``skip``, ``rename`` or ``rewrite``).

  In the end, all mentions of names in the give module ought to be gone, in
  which case ``hs-to-coq`` would not generate an ``Require`` statement anyways.
  So in complete formalizations, this edit should not be needed.

Examples:
   .. code-block:: shell

     skip module GHC.Show


Adding Coq Definitions
----------------------

add <qualified name> <coq definition>

import <modulename>

Renaming and Rewriting
----------------------

rename type <qualified type name> = <qualified type name>

remame value <qualified constructor> = <qualified name>

rename module <oldname> <newname>

rewrite forall <vars>, <expression> = <expression>

redefine <Coq Definition>

type synonym <name> :-> <name>

For example,

   redefine Definition GHC.Base.map {A B :Type} (f : A -> B) xs := Coq.Lists.List.map f xs.



Extra information
-----------------

type  kinds <qualified name> <Coq types>

class kinds <qualified name> <Coq types>

add scope <scope> for <place> <qualified name>

manual notation <name>





<Coq types> is a comma separated list of 

For example, 

    class kinds GHC.Base.MonadPlus (Type -> Type)


Termination edits
-----------------

termination <qualified name> <termarg>

coinductive <qualified name>


If qualid is not structurally recursive, termarg can be one of 
  - deferred 
  - corecursive
  - { struct qualid }
  - { measure id ... } 
  - { wf id qualid }

Order
-----

order <qualified name> ...

For example, 

    order GHC.Base.Functor__arrow GHC.Base.Applicative__arrow_op_ztzg__ GHC.Base.Applicative__arrow GHC.Base.Monad__arrow_return_ GHC.Base.Monad__arrow GHC.Base.Alternative__arrow GHC.Base.MonadPlus__arrow

Axiomatization
--------------

axiomatize <modulename>

Localizing edits
----------------

in <qualified name> <edit>
