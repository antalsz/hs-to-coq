(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Set.Internal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Panic.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Assoc a b :=
  (list (a * b)%type)%type.

(* Converted value declarations: *)

Definition unionLists {a} `{GHC.Base.Eq_ a} : list a -> list a -> list a :=
  fun xs ys =>
    Panic.warnPprTrace (orb (Util.lengthExceeds xs #100) (Util.lengthExceeds ys
                             #100)) (GHC.Base.hs_string__ "ghc/compiler/utils/ListSetOps.hs") #53
                       (Panic.someSDoc) (Coq.Init.Datatypes.app (Coq.Lists.List.flat_map (fun x =>
                                                                                            if Util.isn'tIn
                                                                                               (GHC.Base.hs_string__
                                                                                                "unionLists") x
                                                                                               ys : bool
                                                                                            then cons x nil else
                                                                                            nil) xs) ys).

Definition minusList {a} `{GHC.Base.Ord a} : list a -> list a -> list a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, _ => nil
    | (cons x nil as xs), ys => if Data.Foldable.elem x ys : bool then nil else xs
    | _, _ =>
        match arg_0__, arg_1__ with
        | xs, nil => xs
        | xs, cons y nil => GHC.List.filter (fun arg_2__ => arg_2__ GHC.Base./= y) xs
        | xs, ys =>
            let yss := Data.Set.Internal.fromList ys in
            GHC.List.filter (fun arg_5__ => Data.Set.Internal.notMember arg_5__ yss) xs
        end
    end.

Definition hasNoDups {a} `{(GHC.Base.Eq_ a)} : list a -> bool :=
  fun xs =>
    let is_elem := Util.isIn (GHC.Base.hs_string__ "hasNoDups") in
    let fix f arg_1__ arg_2__
              := match arg_1__, arg_2__ with
                 | _, nil => true
                 | seen_so_far, cons x xs =>
                     if is_elem x seen_so_far : bool
                     then false
                     else f (cons x seen_so_far) xs
                 end in
    f nil xs.

Axiom equivClasses : forall {a},
                     (a -> a -> comparison) -> list a -> list (GHC.Base.NonEmpty a).

Definition removeDups {a}
   : (a -> a -> comparison) ->
     list a -> (list a * list (GHC.Base.NonEmpty a))%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, nil => pair nil nil
    | _, cons x nil => pair (cons x nil) nil
    | cmp, xs =>
        let collect_dups {a}
         : list (GHC.Base.NonEmpty a) ->
           GHC.Base.NonEmpty a -> (list (GHC.Base.NonEmpty a) * a)%type :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | dups_so_far, GHC.Base.NEcons x nil => pair dups_so_far x
            | dups_so_far, (GHC.Base.NEcons x _ as dups) => pair (cons dups dups_so_far) x
            end in
        let 'pair dups xs' := (Data.Traversable.mapAccumR collect_dups nil (equivClasses
                                                                            cmp xs)) in
        pair xs' dups
    end.

Definition assocMaybe {a} {b} `{(GHC.Base.Eq_ a)}
   : Assoc a b -> a -> option b :=
  fun alist key =>
    let fix lookup arg_0__
              := match arg_0__ with
                 | nil => None
                 | cons (pair tv ty) rest =>
                     if key GHC.Base.== tv : bool
                     then Some ty
                     else lookup rest
                 end in
    lookup alist.

Definition assocDefaultUsing {a} {b}
   : (a -> a -> bool) -> b -> Assoc a b -> a -> b :=
  fix assocDefaultUsing (arg_0__ : (a -> a -> bool)) (arg_1__ : b) (arg_2__
                          : Assoc a b) (arg_3__ : a) : b
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | _, deflt, nil, _ => deflt
           | eq, deflt, cons (pair k v) rest, key =>
               if eq k key : bool then v else
               assocDefaultUsing eq deflt rest key
           end.

Definition assocUsing {a} {b} `{GHC.Err.Default b}
   : (a -> a -> bool) -> GHC.Base.String -> Assoc a b -> a -> b :=
  fun eq crash_msg list key =>
    assocDefaultUsing eq (Panic.panic (Coq.Init.Datatypes.app (GHC.Base.hs_string__
                                                               "Failed in assoc: ") crash_msg)) list key.

Definition assocDefault {a} {b} `{(GHC.Base.Eq_ a)}
   : b -> Assoc a b -> a -> b :=
  fun deflt list key => assocDefaultUsing _GHC.Base.==_ deflt list key.

Definition assoc {a} {b} `{GHC.Base.Eq_ a} `{GHC.Err.Default b}
   : GHC.Base.String -> Assoc a b -> a -> b :=
  fun crash_msg list key =>
    assocDefaultUsing _GHC.Base.==_ (Panic.panic (Coq.Init.Datatypes.app
                                                  (GHC.Base.hs_string__ "Failed in assoc: ") crash_msg)) list key.

(* External variables:
     None Some bool comparison cons false list nil op_zt__ option orb pair true
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Foldable.elem
     Data.Set.Internal.fromList Data.Set.Internal.notMember
     Data.Traversable.mapAccumR GHC.Base.Eq_ GHC.Base.NEcons GHC.Base.NonEmpty
     GHC.Base.Ord GHC.Base.String GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.Err.Default GHC.List.filter GHC.Num.fromInteger Panic.panic Panic.someSDoc
     Panic.warnPprTrace Util.isIn Util.isn'tIn Util.lengthExceeds
*)
