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


Format:     
   skip `<qualified name>`

Example:    

.. code :: shell

  skip GHC.List.head

Purpose:    
  Skips any definition. The qualified name should be the Coq name produced by
  qualifying and mangling the original Haskell name.

------------------------------------------

Format:
   skip method `<typeclass>` `<method name>`

Example:

.. code-block:: shell

   skip method GHC.Base.Monad fail

Purpose: 
  Remove a method from a type class. This edit applies to both the
  definition of the class and to all instances.


------------------------------------------


.. code-block:: shell

   skip method <typeclass> <method name>


.. code-block:: shell

   skip method GHC.Base.Monad fail

to remove the partial `fail` method from the monad type class. 


.. code-block:: shell

   skip module <qualified module name>


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
