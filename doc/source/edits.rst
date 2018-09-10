==========
Edit Files
==========

The edit files contain declarations that control the output of ``hs-to-coq`` on
various Haskell files.

General format of edit files
----------------------------

... usually one edit per line, with the exception of period-terminated
multi-line edits ...

Make sure that your edit file ends with a newline.

Qualified names
^^^^^^^^^^^^^^^

A *qualified_name* is the Coq name with module prefix.
Names must always be qualified, because edit files are not bound to a specific
module (even though you may want to have a separate edit for each Haskell
module).

Reserved names have an underscore appended and renames (see below) have already
been applied.

More details about how ``hs-to-coq`` treats `identifiers <mangling.html>`_.


Gallina expressions
^^^^^^^^^^^^^^^^^^^

Some edits contain Gallina expressions (i.e. Coq code). The parser is pretty
limited. In particular, it does not know anything about operator precedence or
associativity, so add plenty of parentheses!

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


Adding Coq Commands
-------------------

``add`` – inject a definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **add** *module* *coq_definition*

Effect:
  Add a Coq definition to *module*. The
  definition can be a ``Definition``, an ``Instance``, an ``Inductive`` or a
  ``Fixpoint``.

  That the name in the definition should be fully qualified. (If it is not,
  some dependency calculations inside ``hs-to-coq`` might go wrong – not always
  critical.)

  This is a multi-line edit and needs to be terminated by a period (as is
  natural when writing a *coq_definition*).

Examples:
   .. code-block:: shell

      add Data.Foldable Definition Data.Foldable.elem {f} `{(Foldable f)} {a} `{(GHC.Base.Eq_ a)} :
        a -> ((f a) -> bool) :=
        fun x xs => Data.Foldable.any (fun y => x GHC.Base.== y) xs.

      add Data.Monoid Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
        GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.

``import`` – inject an ``Import`` statement
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **import** **module** *module*

Effect:
  Inject a ``Import`` statement into the Coq code, which makes the definitions
  from the given module available unqualified.

  ..todo::

    When is this useful?

Examples:
   .. code-block:: shell

     import module Data.Monoid


Renaming and Rewriting
----------------------

``rename type`` - rename a type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **rename type** *qualified_name* = *qualified_name*

Effect: 
  Change the name of a Haskell type, at both definition and use sites.

Examples:
   .. code-block:: shell

     rename type  GHC.Types.[]  = list
     rename type  GHC.Natural.Natural = Coq.Numbers.BinNums.N


``rename value`` - rename a value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **rename value** *qualified_name* = *qualified_name*

Effect:
  Change the name of a Haskell value (function, data constructor), at both
  definition and use sites. Note: rewriting the definition of a name to a new 
  module will not work.

Examples:

   .. code-block:: shell
 
       rename value Data.Foldable.length = Coq.Lists.List.length     # use Coq primitive
       rename value GHC.Base.++          = Coq.Init.Datatypes.app    # operators ok
       rename value Data.Monoid.First    = Data.Monoid.Mk_First      # resolve punning

``rename module`` - change a module name
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **rename module** *module* *module*

Effect:
  Change the name of a Haskell module, affecting the filename of the
  generated Coq module.

  NOTE: if two modules are renamed to the same name, they will be combined
  into a single joint module, as long as they are processed during the same
  execution of ``hs-to-coq``. This feature is useful to translate mutually
  recursive modules. 

Examples:

 .. code-block:: shell
 
     rename module Type MyType
     rename module Data.Semigroup.Internal Data.SemigroupInternal


``rewrite`` - replace Haskell subexpressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:

  | **rewrite** **forall** *vars*, *expression* = *expression*

Effect:

    Pattern matches a sub-expression and replaces it with the right-hand side
	 after substituting all variables.

Examples:

 .. code-block:: shell

    ## work around laziness
    rewrite forall xs x, (GHC.List.zip xs (GHC.List.repeat x)) = (GHC.Base.map (fun y => pair y x) xs)
    rewrite forall x, GHC.Magic.lazy x = x

    ## replace with Coq library function
    rewrite forall x y, GHC.List.replicate x y = Coq.Lists.List.repeat y x

    ## skip debugging code
    rewrite forall x, andb Util.debugIsOn x = false
 
    ## create dummy strings to ignore particular definitions
    ## note empty variable list
    rewrite forall , Outputable.empty = (GHC.Base.hs_string__ "Outputable.empty")

``redefine`` - update a generated Coq Definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **redefine** *Coq_definition*


Effect:
  Combines the **skip** and **add** edits.

Examples:

 .. code-block:: shell

     redefine Definition GHC.Base.map {A B :Type} (f : A -> B) xs := Coq.Lists.List.map f xs.
  

``type synonym`` - deprecated
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **type synonym** *name* **:->** *name*

Effect:

Examples:

 .. code-block:: shell




Extra information
-----------------

``type kinds`` - Declare kinds of type arguments to Inductive datatypes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **type kinds** *qualified_name* *Coq_types*

Effect:

Examples:
  .. code-block:: shell


``class kinds`` - Declare kinds of type arguments to Type classes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Format:
  | **class kinds** *qualified_name* *Coq_types*

Effect:

Examples:
  .. code-block:: shell


``add scope`` - 
^^^^^^^^^^^^^^^^

Format:
  | **add scope** *scope* **for** *place* *qualified_name*

Effect:

Examples:
  .. code-block:: shell


``manual notation`` -
^^^^^^^^^^^^^^^^^^^^^


Format:
  | manual notation *name*

Effect:

Examples:
  .. code-block:: shell


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
