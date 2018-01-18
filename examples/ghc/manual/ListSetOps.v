(* Default settings (from HsToCoq.Coq.Preamble) *)

(* SCW: I've converted this file manually for expediency. removeDups needed
   extra type annotations. Also several partial functions needed `{Default a}
   constraints.
   Finally, this module imports GHC.List.Notations, even though that module
   doesn't exist.

   TODO: proof termination obligations using properties about list length.
 *)


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
Require Data.OldList.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require Panic.
Require UniqFM.
Require Unique.
Require Util.
Import GHC.Base.Notations.
(* Import GHC.List.Notations. *)

Require Import GHC.Num.
Require Import GHC.Base.

(* Converted type declarations: *)
Definition Assoc a b := (list (a * b))%type.

(* Converted value declarations: *)

Definition assocDefaultUsing {a} {b} :
  (a -> a -> bool) -> b -> Assoc a b -> a -> b :=
  fix assocDefaultUsing eq deflt xs key
    := match xs with
       | nil => deflt
       | cons (pair k v) rest =>
         if eq k key then v
         else assocDefaultUsing eq deflt rest key
       end.

Definition assocUsing {a} {b} `{Panic.Default b}:
  (a -> a -> bool) -> String -> Assoc a b -> a -> b :=
  fun eq crash_msg list key =>
    assocDefaultUsing eq (Panic.panic (Coq.Init.Datatypes.app (hs_string__
                                                              "Failed in assoc: ") crash_msg)) list key.

Definition assocDefault {a} {b} `{(Eq_ a)} : b -> Assoc a
                                                      b -> a -> b :=
  fun deflt list key => assocDefaultUsing _==_ deflt list key.

Definition assoc {a} {b} `{(Eq_ a)}`{Panic.Default b}
 : String -> Assoc a b -> a -> b :=
  fun crash_msg list key =>
    assocDefaultUsing _==_
                           (Panic.panic (Coq.Init.Datatypes.app
                                           (hs_string__ "Failed in assoc: ")
                                           crash_msg)) list key.

Definition assocMaybe {a} {b} `{(Eq_ a)} : Assoc a b -> a -> option b :=
  fun alist key =>
    let lookup :=
      fix lookup arg_0__
            := match arg_0__ with
                 | nil => None
                 | cons (pair tv ty) rest => if key == tv : bool
                                             then Some ty
                                             else lookup rest
               end in
    lookup alist.

Definition equivClassesByUniq {a} : (a -> Unique.Unique) -> list a -> list (list
                                                                           a) :=
  fun get_uniq xs =>
    let tack_on := fun old new => Coq.Init.Datatypes.app new old in
    let add :=
      fun a ufm => UniqFM.addToUFM_C tack_on ufm (get_uniq a) (cons a nil) in
    UniqFM.eltsUFM (Data.Foldable.foldr add UniqFM.emptyUFM xs).

Program Fixpoint findDupsEq {a} (eq : (a -> a -> bool)) (arg_1__ :list a)
        {measure (length arg_1__)} : list (list a) :=
        match arg_1__ with
        | nil => nil
        |  cons x xs => match Data.OldList.partition (eq x) xs with
                       | pair eq_xs neq_xs =>
                         if Data.Foldable.null eq_xs : bool
                         then findDupsEq eq xs
                         else cons (cons x eq_xs) (findDupsEq eq neq_xs)
                       end
        end.
Next Obligation.
(* Need to show that partition returns a smaller list *)
Admitted.


Fixpoint getNth {a} `{Panic.Default a} (xs : list a) (n: Int) : a :=
  match xs with
    | nil => Panic.panic (hs_string__ "not found!")
    | cons y ys => if (n == #0) then y else
                    getNth ys (n - #1)
  end.


Definition hasNoDups {a} `{(Eq_ a)} : list a -> bool :=
  fun xs =>
    let is_elem := Util.isIn (hs_string__ "hasNoDups") in
    let f :=
      fix f arg_1__ arg_2__
            := match arg_1__ , arg_2__ with
                 | _ , nil => true
                 | seen_so_far , cons x xs => if is_elem x seen_so_far : bool
                                              then false
                                              else f (cons x seen_so_far) xs
               end in
    f nil xs.

Definition insertList {a} `{Eq_ a} : a -> list a -> list a :=
  fun x xs =>
    let j_0__ := cons x xs in
    if Util.isIn (hs_string__ "insert") x xs : bool
    then xs
    else j_0__.

Definition minusList {a} `{(Eq_ a)} : list a -> list a -> list a :=
  fun xs ys =>
    Coq.Lists.List.flat_map (fun x =>
                              if Util.isn'tIn (hs_string__ "minusList") x ys : bool
                              then cons x nil
                              else nil) xs.

Program Fixpoint runs {a} (p : a -> a -> bool) (arg_1__ : list a) {measure (length arg_1__)} : list (list a) :=
        match arg_1__ with
             | nil => nil
             | cons x xs => let scrut_2__ := (GHC.List.span (p x) xs) in
                                match scrut_2__ with
                                  | pair first rest => cons (cons x first) (runs p rest)
                                end
           end.
Next Obligation.
Admitted.

Definition equivClasses {a} : (a -> a -> comparison) -> list a -> list (list a) :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , nil => nil
      | _ , (cons _ nil as stuff) => cons stuff nil
      | cmp , items => let eq :=
                         fun a b =>
                           let scrut_3__ := cmp a b in
                           match scrut_3__ with
                             | Eq => true
                             | _ => false
                           end in
                       runs eq (Data.OldList.sortBy cmp items)
    end.


(* mapAccumR :: ([[a]] -> [a] -> ([[a]], a)) -> [[a]] -> [[a]] -> ([[a]], [a]) *)

Definition removeDups {a} (cmp : a -> a -> comparison) (l : list a)
        `{Panic.Default a}
  : (list a * list (list a))%type :=
    match l with
      | nil        => pair nil nil
      | cons x nil => pair (cons x nil) nil
      | xs         =>
        let collect_dups : list (list a) -> list a -> (list (list a) *  a) :=
            fun dups_so_far arg_5__ =>
              match arg_5__ with
              | nil => Panic.panic (hs_string__ "ListSetOps: removeDups")
              | cons x nil => pair dups_so_far x
              | (cons x _ as dups) => pair (cons dups dups_so_far) x
              end in
        let y : list (list a) := equivClasses cmp xs in
        match (Data.Traversable.mapAccumR collect_dups nil y)  with
        | pair dups xs' => pair xs' dups
        end
    end.


Definition unionLists {a} `{Eq_ a} : list a -> list a -> list a :=
  fun xs ys =>
    Coq.Init.Datatypes.app
      (Coq.Lists.List.flat_map (fun x =>
                                  if Util.isn'tIn (hs_string__ "unionLists") x
                                                  ys : bool
                                  then cons x nil
                                  else nil) xs) ys.
