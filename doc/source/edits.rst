==========
Edit Files
==========

The edit files contain declarations that control the output of ``hs-to-coq`` on
various Haskell files.

General format of edit files
----------------------------

Edit files are plain text files. Empty lines and lines starting with ``#`` are ignored. Otherwise, the files are consist of a sequence of *edits*. Most form of edits are exactly one line long, but some edits can span multiple lines, and must be terminated with a period.

Make sure that your edit file ends with a newline.

Qualified names
^^^^^^^^^^^^^^^

A *qualified_name* is the Coq name with module prefix.
Names must always be qualified, because edit files are not bound to a specific
module (even though you may want to have a separate edit for each Haskell
module).

Reserved names have an underscore appended and renames (see below) have already
been applied.

More details about how ``hs-to-coq`` treats see Section :ref:`mangling`.


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

.. index::
  single: skip, edit


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

.. index::
  single: skip method, edit

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

.. index::
  single: skip module, edit

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

``axiomatize module`` -- replace all definitions in a module with axioms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: axiomatize module, edit

Format:
  | **axiomatize** **module** *module*

Effect:
  Replaces all definitions in a module with axioms.

  This translates type and type class definitions, and then produces axioms for
  variable bindings and type class instances which have the translated types.
  Any types that are ``redefine``\d are correctly redefined; any bindings or
  instances that are ``skip``\ped don't have axioms generated.  If you want to
  override the axiomatization for a single definition and actually translate it,
  you can use the ``unaxiomatize definition`` edit.

  The ``axiomatize module`` edit is useful if you want to stub out a dependency
  of a module you are actually interested in.

  See also ``axiomatize definition``.

Examples:

  .. code-block:: shell

    axiomatize module TrieMap

``axiomatize definition`` -- replace a value definition with an axiom
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: axiomatize definition, edit

Format:
  | **axiomatize** **definition** *qualified_name*

Effect:
  Replaces a single definition with an axiom.

  This takes the name of a value-level definition and, when translating it,
  translates only the type and generates an axiom with that type.

  See also ``axiomatize module``, and also ``redefine Axiom`` for type-level
  axiomatization.

Examples:

  .. code-block:: shell

     axiomatize definition GHC.Prim.primitiveFunction

``unaxiomatize definition`` -- override whole-module axiomatization on a case-by-case basis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: unaxiomatize definition, edit

Format:
  | **unaxiomatize** **definition** *qualified_name*

Effect:
  Translates a single definition, ``axiomatize module`` notwithstanding.

  If the module containing the given value-level definition is being
  axiomatized, then this definition will be translated in the usual way.

  If a definition is both ``unaxiomatize``\d and ``skip``\ped, then it will
  simply be skipped.  But please don't do this :-)

Examples:

  .. code-block:: shell

     axiomatize module TrieMap
     unaxiomatize definition TrieMap.insertTM
     unaxiomatize definition TrieMap.deleteTM

Adding Coq Commands
-------------------

``add`` – inject a definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: add, edit

Format:
  | **add** *module* *coq_definition*

Effect:
  Add a Coq definition to *module*. The definition can be a ``Definition``, a ``Fixpoint``, an
  ``Inductive``, an ``Instance``, or an ``Axiom``.

  The name in the definition should be fully qualified. (If it is not, some
  dependency calculations inside ``hs-to-coq`` might go wrong – but this is not
  always critical.)

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

.. index::
  single: import, edit

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

``rename type`` -- rename a type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: rename type, edit

Format:
  | **rename type** *qualified_name* = *qualified_name*

Effect:
  Change the name of a Haskell type, at both definition and use sites.

Examples:
   .. code-block:: shell

     rename type GHC.Types.[] = list
     rename type GHC.Natural.Natural = Coq.Numbers.BinNums.N


``rename value`` -- rename a value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: rename value, edit

Format:
  | **rename value** *qualified_name* = *qualified_name*

Effect:
  Change the name of a Haskell value (function, data constructor), at both
  definition and use sites.

Note:
  When renaming a name in its definition, you should not change the
  module.

Examples:

   .. code-block:: shell

       rename value Data.Foldable.length = Coq.Lists.List.length     # use Coq primitive
       rename value GHC.Base.++          = Coq.Init.Datatypes.app    # operators ok
       rename value Data.Monoid.First    = Data.Monoid.Mk_First      # resolve punning

``rename module`` -- change a module name
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: rename module, edit

Format:
  | **rename module** *module* *module*

Effect:
  Change the name of a Haskell module, affecting the filename of the
  generated Coq module.

Note:
  If two modules are renamed to the same name, they will be combined
  into a single joint module, as long as they are processed during the same
  execution of ``hs-to-coq``. This feature is useful to translate mutually
  recursive modules.

Examples:

 .. code-block:: shell

     rename module Type MyType
     rename module Data.Semigroup.Internal Data.SemigroupInternal


``rewrite`` -- replace Haskell subexpressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: rewrite, edit

Format:

  | **rewrite** **forall** *vars*, *expression* = *expression*

Effect:

    Pattern-matches a sub-expression and replaces it with the right-hand side
    after substituting all variables.

    The pattern-matching is unhygienic: if you mention a variable ``x`` in the pattern
    but not in the list of variables (*vars*), then the rewrite rule will only match
    if there is actually is a variable named ``x``.

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

``redefine`` -- override a Coq definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: redefine, edit

Format:
  | **redefine** *Coq_definition*


Effect:
  Combines the **skip** and **add** edits.

  You can use ``redefine Axiom ...`` to replace a type-level definition with an
  axiom; for value-level definitions, please use ``axiomatize definition``
  instead.

Examples:

 .. code-block:: shell

     redefine Definition GHC.Base.map {A B :Type} (f : A -> B) xs := Coq.Lists.List.map f xs.


Extra information
-----------------

``data kinds`` -- Declare kinds of type arguments to Inductive datatypes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: data kinds, edit

Format:
  | **data kinds** *qualified_name* *Coq_types*

Effect:

  Haskell programmers rarely include kinds signatures on inductive
  datatypes. This usually isn't a problem, but for higher-order parameters, or
  phantoms (which don't appear in the datatype definition), Coq does not
  automatically infer the right types. In these cases,
  the information can be included in an edit.

Examples:
  .. code-block:: shell

     # Coq parser needs parens
     data kinds Control.Applicative.WrappedArrow (Type -> (Type -> Type))

     # multiple kinds are comma separated
     data kinds Data.Functor.Reverse.Reverse (Type -> Type),Type
     data kinds Data.Functor.Constant.Constant Type,Type


``class kinds`` -- Declare kinds of type arguments to Type classes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: class kinds, edit

Format:
  | **class kinds** *qualified_name* *Coq_types*

Effect:

   Like ``data kinds``, but for classes.

Examples:
  .. code-block:: shell

      class kinds Control.Arrow.Arrow (Type -> (Type -> Type))


``order`` -- reorder output
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: order, edit

Format:
  | **order** *qualified_name* ...

Effect:
  ``hs-to-coq`` topologically sorts definitions so that they appear in
  dependency order. However, this sorting is not always correct --- type
  classes introduce implicit dependencies that are invisible to
  ``hs-to-coq``. This edit adds a new ordering constraint into the
  topological sort so that the output definitions appear in the order indicate
  in this edit.

  You can order more than two definitions at the same time:

    .. code-block:: shell

     order Foo.foo Foo.bar Foo.baz

  is equivalent to

    .. code-block:: shell

     order Foo.foo Foo.bar
     order Foo.bar Foo.baz



Examples:
  .. code-block:: shell

    order GHC.Base.Functor__arrow GHC.Base.Applicative__arrow_op_ztzg__ GHC.Base.Applicative__arrow GHC.Base.Monad__arrow_return_ GHC.Base.Monad__arrow GHC.Base.Alternative__arrow GHC.Base.MonadPlus__arrow

``manual notation`` -- Indicate presence of manual notation
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: manual notation, edit


Format:
  | **manual notation** *name*

Effect:
  If your preamble inludes custom notation (usually for operators), you need
  to indicate this using this edit.
  See Section :ref:`mangling` for more information about
  how ``hs-to-coq`` implements custom notation.

Examples:
  .. code-block:: shell

     manual notation GHC.Base


Termination edits
-----------------

``coinductive`` -- use a coinductive instead of an inductive datatype
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: coinductive, edit


Format:
  | **coinductive** *qualified_name*

Effect:

Examples:

``termination`` -- hints for termination proofs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: termination, edit

Format:
  | **termination** *qualified_name* *termination_argument*

Effect:

  By default, ``hs-to-coq`` translates recursive definitions using Coq’s
  ``fix`` operator, which requires that the recursion is obviously structurally
  recursive. This is not always the right choice, and a ``termination`` edit tells 
  ``hs-to-coq`` to construct the recursive definition differently, where *termination_argument* is one of the following:

  * .. index::
       single: corecursive, termination argument

    **corecursive**

    This causes ``hs-to-coq`` to use ``cofix`` instead of ``fix``.

  * .. index::
       single: struct, termination argument

    **{** **struct** *qualified_name* **}**

    Coq’s ``fix`` operator usually determines the recusive argument
    automatically, but also supports the user to specify it explicitly. This
    *termination_argument* is just passed along to Coq’s ``fix``.

  * .. index::
       single: measure, termination argument
       single: wf, termination argument

    **{** **measure** *expr* **}**

    **{** **measure** *expr* **(** *relation* **)** **}**

    **{** **wf** *relation* *expr* **}**

    With one of these forms for *termination_argument*, ``hs-to-coq`` uses
    ``Program Fixpoint`` to declare the function, passing these termination arguments
    along. See the documentation of ``Program Fixpoint`` for their precise meaning.

    The *expr* is a Coq expression that mentions the parameters of the current
    functions. These often have names generated by ``hs-to-coq`` -- look at the
    generated Coq code to see what they are.

    ``Program Fixpoint`` only supports top-level declaration. When these
    termination edits are applied to local definitions, ``hs-to-coq`` therefore
    uses the fixed-point operator ``wfFix1`` defined in ``GHC.Wf`` in our
    ``base`` library.

    A side effect of these edits is that the definition (or the enclosing
    definition) is  defines using ``Program``, which leaves proof obligations
    to the user. These should be discharged using the ``obligations`` edit (see
    below).

  * .. index::
       single: deferred, termination argument

    **deferred**

    This causes ``hs-to-coq`` to use the axiom ``deferredFix`` from the module
    ``GHC.DeferredFix`` to translate the recursive definition. This defers
    the termination proof until the verification stage, where the axiom
    ``deferredFix_eq_on`` is needed to learn anything about the recursive
    function, and this axion requires an (extensional) termination proof.

    See the file ``GHC/DeferredFix.v`` for more details.


Examples:

  .. code-block:: shell

    termination Memo.mkTrie corecursive

    termination Memo.lookupTrie { measure arg_1__ (Coq.NArith.BinNat.N.lt) }
    obligations Memo.lookupTrie solve_lookupTrie

    termination Data.Set.Internal.link {measure (Nat.add (set_size arg_1__) (set_size arg_2__))}
    obligations Data.Set.Internal.link termination_by_omega

    in Data.IntSet.Internal.foldlBits  termination go  {measure (Coq.NArith.BinNat.N.to_nat arg_0__)}
    obligations Data.IntSet.Internal.foldlBits BitTerminationProofs.termination_foldl


    termination QuickSort.quicksort deferred


``obligations`` -- Proof obligations in ``Program`` mode
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: obligations, edit

Format:
  | **obligations** *qualified_name* *tactic*

Effect:
  The specified definition is now defined using ``Program``, and is followed by

  .. code-block:: coq

     Solve Obligations with (tactic).

  with the specified tactic.

  This is most commonly used with with the ``termination`` hint, but can be
  useful on its own: For example, ``Program`` mode automatically applies or
  unwraps sigma types, which may leave proof obligations.

  The ``{ measure … }`` termination argument of the ``termination`` edit alwasy
  causes the ``Program`` being used. If no ``obligations`` edit is specified, then
  all obligations are solved with ``Admit Obligations.``.

Mutual recursion edits
----------------------

``inline mutual`` -- Move mutually-recursive functions into ``let``\-bindings
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: inline mutual, edit

Format:
  | **inline mutual** *qualified_name*

Effect:
  The specified definition must be part of a mutually recursive set of
  definitions.  Instead of being defined as another mutual fixpoint, it will be
  inlined into each of the other mutual fixpoints that needs it with a
  ``let``\-binding; additionally, a top-level Coq definition is generated for
  each ``let``\-bound function that simply calls into the predefined recursive
  functions.

  This facility is useful when translating groups of mutually recursive
  functions that contain "preprocessing" or "postprocessing" functions, where
  the group is otherwise structurally recursive.  These functions are not
  "truly" mutual recursive, as they just hand along values of the type being
  recursed, and so if Coq could only see through them, everything would work
  fine.  And indeed, as ``let``\-bindings, Coq can see through them.

  As an example, consider the following pair of mutually recursive data types,
  which represent a ``Forest`` of nonempty ``Tree``\s. Each ``Branch`` of a
  ``Tree`` holds an extra boolean flag, which we can extract with ``isOK``.  In
  Haskell:

  .. code-block:: haskell

     data Forest a = Empty
                   | WithTree (Tree a) (Forest a)
     
     data Tree a = Branch Bool a (Forest a)

     isOK :: Tree a -> Bool
     isOK (Branch ok _ _) = ok

  And in cleaned-up Coq:

  .. code-block:: coq

     Inductive Forest a : Type
       := Empty    : Forest a
       |  WithTree : Tree a -> Forest a -> Forest a
     with Tree a : Type
       := Branch : bool -> a -> Forest a -> Tree a.
      
     Arguments Empty    {_}.
     Arguments WithTree {_} _ _.
     Arguments Branch   {_} _ _ _.
     
     Definition isOK {a} : Tree a -> bool :=
       fun '(Branch ok _ _) => ok.

  Now we can define a pair of mapping functions that only apply a function
  inside subtrees where the boolean flag is true.  The Haskell code is simple:

  .. code-block:: haskell

     mapForest :: (a -> a) -> Forest a -> Forest a
     mapForest f Empty           = Empty
     mapForest f (WithTree t ts) = WithTree (mapTree f t) (mapForest f ts)

     mapTree :: (a -> a) -> Tree a -> Tree a
     mapTree f t | isOK t    = mapOKTree f t
                 | otherwise = t

     mapOKTree :: (a -> a) -> Tree a -> Tree a
     mapOKTree f (Branch ok x ts) = Branch ok (f x) (mapForest f ts)

  However, the (cleaned-up) Coq translation fails:

  .. code-block:: coq

     Fail Fixpoint mapForest {a} (f : a -> a) (ts0 : Forest a) {struct ts0} : Forest a :=
       match ts0 with
       | Empty         => Empty
       | WithTree t ts => WithTree (mapTree f t) (mapForest f ts)
       end
     with mapTree {a} (f : a -> a) (t : Tree a) {struct t} : Tree a :=
       if isOK t
       then mapOKTree f t
       else t
     with mapOKTree {a} (f : a -> a) (t : Tree a) {struct t} : Tree a :=
       match t with
       | Branch ok x ts => Branch ok (f x) (mapForest f ts)
       end.

  The issue is that ``mapTree`` calls ``mapOKTree`` on the *same* term, and not
  a subterm.  But this just a preprocessing/postprocessing split – there's
  nothing *actually* recursive going on.

  But with

  .. code-block:: shell

     inline mutual mapOKTree

  we instead get working Coq code (again, cleaned up):

  .. code-block:: coq

     Fixpoint mapForest {a} (f : a -> a) (ts0 : Forest a) {struct ts0} : Forest a :=
       match ts0 with
       | Empty         => Empty
       | WithTree t ts => WithTree (mapTree f t) (mapForest f ts)
       end
     with mapTree {a} (f : a -> a) (t : Tree a) {struct t} : Tree a :=
       let mapOKTree {a} (f : a -> a) (t : Tree a) : Tree a :=
             match t with
             | Branch ok x ts => Branch ok (f x) (mapForest f ts)
             end in
       if isOK t
       then mapOKTree f t
       else t.
      
     Definition mapOKTree {a} (f : a -> a) (t : Tree a) : Tree a :=
       match t with
       | Branch ok x ts => Branch ok (f x) (mapForest f ts)
       end.

  This is the idea.  However, to be completely fair, we never produce
  ``Fixpoint`` commands; both in the failing case and in the successful case, we
  generate ``fix`` terms.  In this example, this looks like (reindented)

  .. code-block:: coq

     Definition mapForest {a} : (a -> a) -> Forest a -> Forest a :=
       fix mapTree f t :=
         let mapOKTree arg_0__ arg_1__ :=
               match arg_0__, arg_1__ with
               | f, Branch ok x ts => Branch ok (f x) (mapForest f ts)
               end in
         if isOK t : bool
         then mapOKTree f t
         else t
       with mapForest arg_0__ arg_1__ :=
         match arg_0__, arg_1__ with
         | f, Empty => Empty
         | f, WithTree t ts => WithTree (mapTree f t) (mapForest f ts)
         end
       for mapForest.
      
     Definition mapOKTree {a} : (a -> a) -> Tree a -> Tree a :=
       fun arg_0__ arg_1__ =>
         match arg_0__, arg_1__ with
         | f, Branch ok x ts => Branch ok (f x) (mapForest f ts)
         end.
      
     Definition mapTree {a} : (a -> a) -> Tree a -> Tree a :=
       fix mapTree f t :=
         let mapOKTree arg_0__ arg_1__ :=
               match arg_0__, arg_1__ with
               | f, Branch ok x ts => Branch ok (f x) (mapForest f ts)
               end in
         if isOK t : bool
         then mapOKTree f t
         else t
       with mapForest arg_0__ arg_1__ :=
         match arg_0__, arg_1__ with
         | f, Empty => Empty
         | f, WithTree t ts => WithTree (mapTree f t) (mapForest f ts)
         end
       for mapTree.

Meta-edits
----------

Localizing edits - restrict scope of an edit
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: in, edit


Format:
 | **in** *qualified_name* *edit*

Effect:

  This is a meta-edit: The given edit is only applied during the translation of
  the given definition. This is most useful to rename or rewrite only within
  a specific function, or to give termination arguments to local functions.

  While all edits are allowed, not all edits are useful when localized.

Examples:
  .. code-block:: shell

     in SrcLoc.Ord__RealSrcLoc_op_zl__ rewrite forall, SrcLoc.Ord__RealSrcLoc_compare = GHC.Base.compare
     in Util.exactLog2 termination pow2 deferred

Deprecated edits
----------------

``add scope``
^^^^^^^^^^^^^

.. index::
   single: add scope, edit


Format:
  | **add scope** *scope* **for** *place* *qualified_name*

Effect:

Examples:

``type synonym``
^^^^^^^^^^^^^^^^

.. index::
   single: type synonym, edit

Format:
  | **type synonym** *name* **:->** *name*

Effect:

Examples:
