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

``skip`` – skip a function, type, or type class instance
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: skip, edit


Format:
  | **skip** *qualified_name*

Effect:
  During translation, ignore the declaration of the function, value, type, or
  type class instance with the given *qualified_name*.  The name must be the
  translated Coq name, not the original Haskell name (if those differ).

  This does not affect the translation of *uses* of the given name. This means
  that you can use other methods, e.g. a preamble, to make it available.

  You can skip type class instances, but as they do not have names in Haskell,
  you must use the name ``hs-to-coq`` generates for them.  The name generation
  is systematic, but you might want to first attempt the translation and check
  the output for the precise name.

  To skip data type constructors, see ``skip constructor``; to skip type
  classes, see ``skip class``; to skip type class methods, see ``skip methods``.
  They are not unified here because those effects are more powerful.  You can
  also skip whole modules with ``skip module``.


Examples:
   .. code-block:: shell

     skip Data.Function.fix_ # Note the mangled name!
     skip GHC.Base.String
     skip GHC.Real.Fractional
     skip Data.Monoid.Show__Last # an instance

``skip constructor`` – skip a constructor of a data type
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: skip constructor, edit


Format:
  | **skip constructor** *qualified_name*

Effect:
  During translation, ignore the given data type constructor.  Any equation of a
  function, alternative of a case statement, or pattern guard that
  pattern-matches on that constructor is also skipped.  List comprehensions that
  bind to that constructor become ``[]``.

  As with ``skip``, this does not affect the translation of *uses* of the
  constructor.  This means that you must either make it available in a preamble
  or elide it with other edits.  Additionally, matching against the constructor
  in ``do`` notation will cause a translation failure.

  These skipped constructors are not stored in the generated metadata, so you
  need to include the ``skip constructor`` edits in all downstream modules.

Examples:
   .. code-block:: shell

     skip constructor Core.Cast
     skip constructor Core.Tick
     skip constructor Core.Type_
     skip constructor Core.Coercion


``skip class`` – skip a type class and all its instances
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: skip class edit

Format:
  | **skip** **class** *qualified_class*

Effect:

  Omit the given type class and all its instances.

  These skipped classes are not stored in the generated metadata, so you need to
  include the ``skip class`` edits in all downstream modules.

Examples:
   .. code-block:: shell

     skip class GHC.Base.Alternative
     skip class Data.Data.Data

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

``skip equation`` – skip one equation of a function definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: skip equation, edit

Format:
  | **skip equation** *qualified_function* *pattern* ...

Effect:
  Skip the equation of the function definition whose arguments are the specified
  patterns.  Guards are not considered, only the patterns themselves.

  For example, consider the following (silly) function definition:

  .. code-block:: haskell

     redundant :: Maybe Bool -> Maybe Bool -> Bool
     redundant (Just True)  _        = False
     redundant (Just False) _        = True
     redundant _            _        = True
     redundant _            (Just b) = b

  The last case is redundant, so Coq will reject this definition.  However, we
  can add the following edit:

  .. code-block:: shell

     skip equation ModuleName.redundant _ (Some b)

  And the last case will be deleted on the Coq side:

  .. code-block:: coq

     Definition redundant : option bool -> option bool -> bool :=
       fun arg_0__ arg_1__ =>
         match arg_0__, arg_1__ with
         | Some true, _ => false
         | Some false, _ => true
         | _, _ => true
         end.

  Note that you have to use the translated name (``Some`` vs. ``Just``), and
  most constructor names will be fully qualified.

  Why would you want this?  This edit is most useful in tandem with ``skip
  constructor`` (which see).  Suppose we have a function where the final catch-all
  case can only match skipped constructors, such as

  .. code-block:: haskell

     data T = TranslateMe
            | SkipMe

     function :: T -> Bool
     function TranslateMe = True
     function _           = False

  Then, on skipping ``SkipMe``, this function's ``_`` case will be redundant,
  and Coq would reject it.  We can fix this with

   .. code-block:: shell

      skip equation ModuleName.function _

  to translate just the ``TranslateMe`` case.

  See also ``skip case pattern`` for the equivalent edit for ``case`` and lambda-case
  expressions.

Examples:
   .. code-block:: shell

     skip equation ModuleName.redundant _ (Some b)
     skip equation Core.hasSomeUnfolding _

``skip case pattern`` – skip one alternative of a ``case`` expression
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: skip case pattern, edit

Format:
  | **skip case pattern** *pattern*

Effect:
  Skip any alternative of a ``case`` expression (or a lambda-case expression)
  which matches against the given pattern. Guards are not considered, only the
  pattern itself.

  For example, consider the following (silly) function definition:

  .. code-block:: haskell

     redundant :: Bool -> Bool
     redundant b = not (case b of
                          True  -> False
                          False -> True
                          _     -> True)

  The last case is redundant, so Coq will reject this definition.  However, we
  can add the following edit:

  .. code-block:: shell

     in ModuleName.redundant skip case pattern _

  And the last case will be deleted on the Coq side (reformatted):

  .. code-block:: coq

     Definition redundant : bool -> bool :=
       fun b => negb (match b with
                      | true => false
                      | false => true
                      end).

  You can use an arbitrary pattern, not simply ``_``; constructor names must be
  fully qualified and the names used must be those that appear *after* renaming.

  Why would you want this?  This edit is most useful in tandem with ``skip
  constructor`` (which see); see the discussion in ``skip equation`` for a
  worked example (with a named function).

  This edit is unusual in that you *very likely* want to use it with the ``in``
  meta-edit to scope its effects to within a specific definition.  However, this
  isn't mandatory; if, for some reason, you want to skip every ``_`` in every
  ``case``, then ``skip case pattern _`` will do what you want.

  See also ``skip equation`` for the equivalent edit for named functions.

Examples:
   .. code-block:: shell

     in ModuleName.redundant skip case pattern _


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

``axiomatize original module name`` -- replace all definitions in a module with axioms, using the pre-renaming module name
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: axiomatize original module name, edit

Format:
  | **axiomatize original module name** *module*

Effect:
  You probably do not need to use this edit; it's only important when using
  ``rename module`` to merge multiple modules into one.  If you are doing this,
  however, and wish you could use ``axiomatize module`` on *some* of the input
  modules but not others, then ``axiomatize original module name`` is the edit for you.

  The behavior of ``axiomatize original module name`` is the same as that of
  ``axiomatize module``, except for how it picks which module to axiomatize.
  While every other edit operates in terms of the Coq name after any renamings
  from the edits have been applied, ``axiomatize original module name`` checks
  the *original*, pre-``rename module``, form of the module name.  Most of the
  time, this would be confusing, and ``axiomatize module`` would be preferable.

  However, if you have used ``rename module`` to merge two (or more) modules
  into one, but you only want one of them (or some other strict subset) to be
  axiomatized, then ``axiomatize original module name`` is the only way to get
  this behavior.

Examples:

  .. code-block:: shell

    axiomatize original module name Part1
    rename module Part1 Whole
    rename module Part2 Whole

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
  ``Inductive``, an ``Instance``, an ``Axiom``, or a ``Theorem`` (with a ``Proof``).

  The name in the definition should be fully qualified. (If it is not, some
  dependency calculations inside ``hs-to-coq`` might go wrong – but this is not
  always critical.)

  Our Coq parser is dramatically incomplete, and you may need to add parentheses
  or pick a simpler syntactic representation of terms to get them to parse
  correctly or at all.  One example is that ``hs-to-coq`` does not understand
  the associativity of the function arrow when parsing: ``a -> b -> c`` will not
  parse, and needs to be given as ``a -> (b -> c)``.

  When providing a ``Theorem`` – or a ``Lemma``, a ``Remark``, a ``Fact``, a
  ``Corollary``, a ``Proposition``, or an ``Example`` – it must be immediately
  followed by ``Proof.``, some unparsed text (newlines are permitted), and then
  the word ``Qed``, ``Defined``, or ``Admitted``.

  This is a multi-line edit and needs to be terminated by a period (as is
  natural when writing a *coq_definition*).

Examples:
   .. code-block:: shell

      add Data.Foldable Definition Data.Foldable.elem {f} `{(Foldable f)} {a} `{(GHC.Base.Eq_ a)} :
        a -> (f a -> bool) :=
        fun x xs => Data.Foldable.any (fun y => x GHC.Base.== y) xs.

      add Data.Monoid Instance Unpeel_Last a : GHC.Prim.Unpeel (Last a) (option a) :=
        GHC.Prim.Build_Unpeel _ _ getLast Mk_Last.


``add type`` – inject a definition into the type component
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: add, edit

Format:
  | **add type** *module* *coq_definition*

Effect:
  Add a Coq definition to the *type* component of a *module*. The definition
  can be as above, and need not be a type definition. However, it is inserted
  before the *midamble* section and will appear grouped with the type and
  class definitions.


``import`` – inject an ``Import`` statement
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
  single: import, edit

Format:
  | **import** **module** *module*

Effect:
  Inject a ``Import`` statement into the Coq code, which makes the definitions
  from the given module available unqualified.

  When used to import the hs-to-coq base library, this makes the output look
  more like standard Haskell.

  Note, however, that Coq's module system lacks the ``import ... hiding``
  construct so all definitions from the module must be made available.

Examples:
   .. code-block:: shell

     import module Prelude


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

``collapse let`` -- if a definition is just a ``let``\-expression, inline it
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: collapse let, edit

Format:
  | **collapse let** *qualified_name*


Effect:
  If a converted definition is of the form

  .. code-block:: coq

     Definition outer := let inner := definition in inner.

  then convert it to simply

  .. code-block:: coq

     Definition outer := definition.

  Both ``outer`` and ``inner`` can have arguments; ``inner`` can have a type
  annotation, but it's ignored.

  Additionally, if ``definition`` is a non-mutual fixpoint ``fix f args :=
  body``, the recursive calls to ``f`` in ``body`` are rewritten to direct calls
  to ``outer``.

  This is particularly important for mutual recursion: if ``inner`` is mutually
  recursive with another top-level function, then if ``outer`` has no arguments,
  it would otherwise appear not to be a function and would thus cause conversion
  to fail, as Coq doesn't support recursion through non-functions.

Examples:

 .. code-block:: shell

     collapse let CoreFVs.freeVars



Extra information
-----------------

``data kinds`` -- Declare kinds of type arguments to Inductive datatypes
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: data kinds, edit

Format:
  | **data kinds** *qualified_name* *Coq_types*

Effect:

  Haskell programmers rarely include kind signatures on inductive
  datatypes. This usually isn't a problem, but for higher-order parameters, some
  phantom type parameters, or poly-kinded type parameters, Coq does not
  necessarily automatically infer the right types. In these cases, the
  information can be included in an edit.

Examples:
  .. code-block:: shell

     # The edit file's Coq parser needs parentheses
     data kinds Control.Applicative.WrappedArrow (Type -> (Type -> Type))

     # Multiple kinds are separated with commas
     data kinds Data.Functor.Reverse.Reverse   (Type -> Type), Type
     data kinds Data.Functor.Constant.Constant Type,           Type

``class kinds`` -- Declare kinds of type arguments to type classes
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

``delete unused type variables`` -- Remove unused type variables from a declaration
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: delete unused type variables, edit

Format:
  | **delete unused type variables** *qualified_name*

Effect:

  Don't translate binders for any type variables that aren't visibly used in the
  specified definition.

  An explanation: sometimes, poly-kinded Haskell data types have extra invisible
  type parameters.  For instance, in ``Data.Functor.Const``, we have the
  type

  .. code-block:: haskell

     newtype Const a b = Const { getConst :: a }

  which is secretly

  .. code-block:: haskell

     newtype Const {k} (a :: Type) (b :: k) = Const { getConst :: a }

  Often, such as here, this doesn't show up in the translated Coq code; we get

  .. code-block:: coq

     Inductive Const a b : Type := Mk_Const (getConst : a) : Const a b.

  (And, as in Haskell 2010, ``b`` is inferred to have kind ``Type``.)  Sometimes
  it does, in which case we can fix it using ``data kinds``.  But either way, we
  still introduce spurious kind variables in the translation sometimes.  For
  example, the derived ``Eq`` instance for ``Const`` is translated to

  .. code-block:: coq

     Program Instance Eq___Const {a} {k} {b} `{GHC.Base.Eq_ a}
        : GHC.Base.Eq_ (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
       fun _ k =>
         k {| GHC.Base.op_zeze____ := Eq___Const_op_zeze__ ;
              GHC.Base.op_zsze____ := Eq___Const_op_zsze__ |}.

  The implicit argument ``{k}`` isn't useful in the Coq code, and causes a
  type-checking failure when its type cannot be determined.  We can avoid this
  with

  .. code-block:: shell

     delete unused type variables Data.Functor.Const.Eq___Const

  which will drop the ``{k}`` and leave the definition with just the ``{a}`` and
  ``{b}`` it needs:

  .. code-block:: coq

     Program Instance Eq___Const {a} {b} `{GHC.Base.Eq_ a}
        : GHC.Base.Eq_ (Const a b : GHC.Prim.TYPE GHC.Types.LiftedRep) :=
       fun _ k =>
         k {| GHC.Base.op_zeze____ := Eq___Const_op_zeze__ ;
              GHC.Base.op_zsze____ := Eq___Const_op_zsze__ |}.

Examples:

  .. code-block:: shell

     delete unused type variables Data.Functor.Const.Eq___Const


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

``set type`` -- Specify a type for a binding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: set type, edit

Format:
  | **set type** *qualified_name* : *Coq_type*
  | **set type** *qualified_name* no type

Effect:
  Sets the type of the given definition to the given type, or omits the type if
  ``no type`` is specified.

Examples:
  .. code-block:: shell

     set type Example.int_to_int : Z -> Z
     set type Example.inferred no type
     in CoreUtils.stripTicksE set type go_b : (b * Core.Expr b) -> (b * Core.Expr b)

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

  The ``{ measure … }`` termination argument of the ``termination`` edit always
  causes ``Program`` to be used. If no ``obligations`` edit is specified, then
  all obligations are solved with ``Admit Obligations.``.

  The ``tactic`` is drawn from a very simple subset of Ltac, featuring
  identifiers, identifiers with ``@``, application, numbers, underscore, ``;``,
  and ``||``.  Anything richer should go in the preamble or midamble.

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

``in`` edit - restrict scope of an edit to a single definition
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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

``except in`` edit - exclude definitions from an edit
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index::
   single: except in, edit


Format:
 | **except in** *qualified_names* *edit*

Effect:

  This is essentially the opposite of an ``in`` edit. The given edit is applied
  as normal, except during the translation of the given definition(s). This is
  most useful to rename or rewrite a definition everywhere except within one or
  more functions. In addition, it can be used when there is a local function
  with the same name in multiple definitions, in order to give termination
  arguments to all occurrences of that local function except those in the
  specified definitions.

  As with ``in`` edits, while all edits are allowed, for many edits it doesn't
  make sense to apply ``except in``.


Examples:
  .. code-block:: shell

     except in SrcLoc.Ord__RealSrcLoc_op_zl__ rewrite forall, SrcLoc.Ord__RealSrcLoc_compare = GHC.Base.compare
     except in Util.exactLog2 termination pow2 deferred
     except in ModuleName.def_1 skip case pattern _

     # Multiple qualified names are separated with commas
     except in ModuleName.def_1, ModuleName.def_2 rename type GHC.Types.[] = list

Caveats:

  This edit does not currently work with data type definitions.

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
