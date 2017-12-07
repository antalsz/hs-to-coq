Set Implicit Arguments.
Unset Strict Implicit.

Require Import Data.Map.Base.

Require Import Coq.FSets.FMapInterface.

Axiom FIXME : forall {a}, a.

Module Foo (E : DecidableType) : WSfun(E).
  Local Instance Eq_t : GHC.Base.Eq_ E.t := FIXME.
  Local Instance Ord_t : GHC.Base.Ord E.t := FIXME.

  Definition key := E.t.
  Hint Transparent key.

  Section t.
    Variable elt:Type.
    
    (* Well-formedness *)
    Definition WF (m : Map key elt) := True. (* TODO. maybe simply [valid s = true]? *)
    Definition t := {m : Map key elt | WF m}.
    Definition pack (m : Map key elt) (H : WF m): t := exist _ m H.
  End t.

  Section Types.
    Variable elt:Type.

    Definition empty : t elt := FIXME.
    (** The empty map. *)

    Definition is_empty : t elt -> bool := FIXME.
    (** Test whether a map is empty or not. *)

    Definition add : key -> elt -> t elt -> t elt := FIXME.
    (** [add x y m] returns a map containing the same bindings as [m],
	plus a binding of [x] to [y]. If [x] was already bound in [m],
	its previous binding disappears. *)

    Definition find : key -> t elt -> option elt := FIXME.
    (** [find x m] returns the current binding of [x] in [m],
	or [None] if no such binding exists. *)

    Definition remove : key -> t elt -> t elt := FIXME.
    (** [remove x m] returns a map containing the same bindings as [m],
	except for [x] which is unbound in the returned map. *)

    Definition mem : key -> t elt -> bool := FIXME.
    (** [mem x m] returns [true] if [m] contains a binding for [x],
	and [false] otherwise. *)

    Variable elt' elt'' : Type.

    Definition map : (elt -> elt') -> t elt -> t elt' := FIXME.
    (** [map f m] returns a map with same domain as [m], where the associated
	value a of all bindings of [m] has been replaced by the result of the
	application of [f] to [a]. Since Coq is purely functional, the order
        in which the bindings are passed to [f] is irrelevant. *)

    Definition mapi : (key -> elt -> elt') -> t elt -> t elt' := FIXME.
    (** Same as [map], but the function receives as arguments both the
	key and the associated value for each binding of the map. *)

    Definition map2 :
     (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt'' := FIXME.
    (** [map2 f m m'] creates a new map whose bindings belong to the ones
        of either [m] or [m']. The presence and value for a key [k] is
        determined by [f e e'] where [e] and [e'] are the (optional) bindings
        of [k] in [m] and [m']. *)

    Definition elements : t elt -> list (key*elt) := FIXME.
    (** [elements m] returns an assoc list corresponding to the bindings
        of [m], in any order. *)

    Definition cardinal : t elt -> nat := FIXME.
    (** [cardinal m] returns the number of bindings in [m]. *)

    Definition fold : forall {A: Type}, (key -> elt -> A -> A) -> t elt -> A -> A := FIXME.
    (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)],
	where [k1] ... [kN] are the keys of all bindings in [m]
	(in any order), and [d1] ... [dN] are the associated data. *)

    Definition equal : (elt -> elt -> bool) -> t elt -> t elt -> bool := FIXME.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal,
      that is, contain equal keys and associate them with equal data := FIXME.
      [cmp] is the equality predicate used to compare the data associated
      with the keys. *)

    Section Spec.

      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Definition MapsTo : key -> elt -> t elt -> Prop := FIXME.

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

      Definition eq_key_elt (p p':key*elt) :=
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    (** Specification of [MapsTo] *)
      Definition MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m := FIXME.

    (** Specification of [mem] *)
      Definition mem_1 : In x m -> mem x m = true := FIXME.
      Definition mem_2 : mem x m = true -> In x m := FIXME.

    (** Specification of [empty] *)
      Definition empty_1 : Empty empty := FIXME.

    (** Specification of [is_empty] *)
      Definition is_empty_1 : Empty m -> is_empty m = true := FIXME.
      Definition is_empty_2 : is_empty m = true -> Empty m := FIXME.

    (** Specification of [add] *)
      Definition add_1 : E.eq x y -> MapsTo y e (add x e m) := FIXME.
      Definition add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m) := FIXME.
      Definition add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m := FIXME.

    (** Specification of [remove] *)
      Definition remove_1 : E.eq x y -> ~ In y (remove x m) := FIXME.
      Definition remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m) := FIXME.
      Definition remove_3 : MapsTo y e (remove x m) -> MapsTo y e m := FIXME.

    (** Specification of [find] *)
      Definition find_1 : MapsTo x e m -> find x m = Some e := FIXME.
      Definition find_2 : find x m = Some e -> MapsTo x e m := FIXME.

    (** Specification of [elements] *)
      Definition elements_1 :
        MapsTo x e m -> InA eq_key_elt (x,e) (elements m) := FIXME.
      Definition elements_2 :
        InA eq_key_elt (x,e) (elements m) -> MapsTo x e m := FIXME.
      (** When compared with ordered maps, here comes the only
         property that is really weaker: *)
      Definition elements_3w : NoDupA eq_key (elements m) := FIXME.

    (** Specification of [cardinal] *)
      Definition cardinal_1 : cardinal m = length (elements m) := FIXME.

    (** Specification of [fold] *)
      Definition fold_1 :
	forall (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i := FIXME.

    (** Equality of maps *)

    (** Caveat: there are at least three distinct equality predicates on maps.
      - The simpliest (and maybe most natural) way is to consider keys up to
        their equivalence [E.eq], but elements up to Leibniz equality, in
        the spirit of [eq_key_elt] above. This leads to predicate [Equal].
      - Unfortunately, this [Equal] predicate can't be used to describe
        the [equal] function, since this function (for compatibility with
        ocaml) expects a boolean comparison [cmp] that may identify more
        elements than Leibniz. So logical specification of [equal] is done
        via another predicate [Equivb]
      - This predicate [Equivb] is quite ad-hoc with its boolean [cmp],
        it can be generalized in a [Equiv] expecting a more general
        (possibly non-decidable) equality predicate on elements *)

     Definition Equal m m' := forall y, find y m = find y m'.
     Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
         (forall k, In k m <-> In k m') /\
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
     Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).

     (** Specification of [equal] *)

     Variable cmp : elt -> elt -> bool.

     Definition equal_1 : Equivb cmp m m' -> equal cmp m m' = true := FIXME.
     Definition equal_2 : equal cmp m m' = true -> Equivb cmp m m' := FIXME.

    End Spec.
   End Types.

    (** Specification of [map] *)
      Definition map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m) := FIXME.
      Definition map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m := FIXME.

    (** Specification of [mapi] *)
      Definition mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m) := FIXME.
      Definition mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m := FIXME.

    (** Specification of [map2] *)
      Definition map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
	In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m') := FIXME.

     Definition map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m' := FIXME.
End Foo.
