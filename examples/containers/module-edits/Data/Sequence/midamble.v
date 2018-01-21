(*  ----------------------------------------------------------- *)

Record Foldable1__Dict (t : Type -> Type) := Foldable1__Dict_Build {
  foldl1__ : forall {a}, (a -> a -> a) -> t a -> a  }.

Definition Foldable1 a :=
  forall r, (Foldable1__Dict a -> r) -> r.

Existing Class Foldable1.

Definition foldl1 `{g : Foldable1 t} : forall {a}, (a -> a -> a) -> t a -> a :=
  g _ (foldl1__ t).

Definition Digit_foldl1 {a} (f : a -> a -> a) (t : Digit a) : a :=
  match t with
  | One x => x
  | Two x y => f x y
  | Three x y z => f (f x y) z
  | Four x y z w => f (f (f x y) z) w
  end.

(*  ----------------------------------------------------------- *)

Program Instance Foldable1_Digit : Foldable1 Digit := fun _ k =>
  k {| foldl1__ := fun {a} => Digit_foldl1 |}.

(*  ----------------------------------------------------------- *)

Instance Unpeel_Elem a : GHC.Prim.Unpeel (Elem a) a :=
  GHC.Prim.Build_Unpeel _ _ (fun x => match x with Mk_Elem y => y end) Mk_Elem.

(*  ----------------------------------------------------------- *)

Notation "'_:<_'" := (op_ZCzl__).

Infix ":<" := (_:<_) (at level 99).

Notation "'_:>_'" := (op_ZCzg__).

Infix ":>" := (_:>_) (at level 99).

Notation "'_:&_'" := (op_ZCza__).

Infix ":&" := (_:&_) (at level 99).


(*  ----------------------------------------------------------- *)
(* CHANGE to Default.panic *)

Parameter error : forall {a}, a.

(* Move to base: missing record selectors *)
Definition runIdentity {a} (x: Data.Functor.Identity.Identity a) : a :=
  match x with
  | Data.Functor.Identity.Mk_Identity y => y
  end.

Definition unwrapMonad {m}{a} (x: Control.Applicative.WrappedMonad m a) :=
  match x with
  | Control.Applicative.WrapMonad y => y
  end.

(*  ----------------------------------------------------------- *)
(* Needs a termination argument *)

Definition map_elem {a} : list a -> list (Elem a) := fun xs => GHC.Prim.coerce xs.
Definition getNodes {a} : GHC.Num.Int -> a -> list a -> (list (Node a) * Digit a)%type :=
    fix getNodes arg_1__ arg_2__ arg_3__
          := let j_9__ :=
               match arg_1__ , arg_2__ , arg_3__ with
                 | _ , x1 , nil => pair nil (One x1)
                 | _ , x1 , cons x2 nil => pair nil (Two x1 x2)
                 | _ , x1 , cons x2 (cons x3 nil) => pair nil (Three x1 x2 x3)
                 | s , x1 , cons x2 (cons x3 (cons x4 xs)) =>
                   match getNodes s x4 xs with
                   | pair ns d => pair (cons (Node3 s x1 x2 x3) ns) d
                   end
               end in
             match arg_1__ , arg_2__ , arg_3__ with
             | arg , _ , _ => j_9__
             end.

(*
Require Import Omega.
Program Fixpoint  mkTree {a} `{(Sized a)} (s: GHC.Num.Int) (x : list a) {measure (length x)} : FingerTree a :=
    match x with
    | nil => Empty
    | cons x1 nil => Single x1
    | cons x1 (cons x2 nil) => Deep (GHC.Num.fromInteger 2 GHC.Num.* s) (One x1)
                                   Empty (One x2)
    | cons x1 (cons x2 (cons x3 nil)) => Deep (GHC.Num.fromInteger 3 GHC.Num.*
                                                                  s) (One x1) Empty (Two x2 x3)
    | cons x1 (cons x2 (cons x3 (cons x4 xs))) =>
      match getNodes (GHC.Num.fromInteger 3 GHC.Num.* s) x4 xs with
      | pair ns sf => match mkTree (GHC.Num.fromInteger 3 GHC.Num.* s) ns with
                     | m => GHC.Prim.seq m (Deep (((GHC.Num.fromInteger 3 GHC.Num.* size x1)
                                                    GHC.Num.+ size m)
                                                   GHC.Num.+ size sf)
                                                (Three x1 x2 x3) m sf)
                     end
      end
    end.
Obligation 1.
admit.
Admitted.

Definition fromList {a} : list a -> Seq a :=
  Mk_Seq GHC.Base.∘ ((@mkTree (Elem a) _ (GHC.Num.fromInteger 1)) GHC.Base.∘ map_elem). *)

(*  ----------------------------------------------------------- *)

Definition  mapWithIndexNode {a} {b} `{Sized a}
                             : (GHC.Num.Int -> a -> b) -> GHC.Num.Int -> Node a -> Node b :=
                             fun arg_2__ arg_3__ arg_4__ =>
                               match arg_2__ , arg_3__ , arg_4__ with
                                 | f , s , Node2 ns a b => let sPsa := s GHC.Num.+ size a in
                                                           GHC.Prim.seq sPsa (Node2 ns (f s a) (f sPsa b))
                                 | f , s , Node3 ns a b c => let sPsa := s GHC.Num.+ size a in
                                                             let sPsab := sPsa GHC.Num.+ size b in
                                                             GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (Node3 ns (f s a) (f
                                                                                                                     sPsa
                                                                                                                     b)
                                                                                             (f sPsab c)))
                               end.

Definition  mapWithIndexDigit {a} {b} `{Sized a}
  : (GHC.Num.Int -> a -> b) -> GHC.Num.Int -> Digit a -> Digit b :=
  fun arg_11__ arg_12__ arg_13__ =>
    match arg_11__ , arg_12__ , arg_13__ with
    | f , s , One a => One (f s a)
    | f , s , Two a b => let sPsa := s GHC.Num.+ size a in
                        GHC.Prim.seq sPsa (Two (f s a) (f sPsa b))
    | f , s , Three a b c => let sPsa := s GHC.Num.+ size a in
                            let sPsab := sPsa GHC.Num.+ size b in
                            GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (Three (f s a) (f sPsa
                                                                                    b) (f
                                                                                          sPsab
                                                                                          c)))
    | f , s , Four a b c d => let sPsa := s GHC.Num.+ size a in
                             let sPsab := sPsa GHC.Num.+ size b in
                             let sPsabc := sPsab GHC.Num.+ size c in
                             GHC.Prim.seq sPsa (GHC.Prim.seq sPsab (GHC.Prim.seq sPsabc
                                                                                 (Four (f
                                                                                          s
                                                                                          a)
                                                                                       (f sPsa
                                                                                          b) (f
                                                                                                sPsab
                                                                                                c) (f
                                                                                                      sPsabc
                                                                                                      d))))
    end.

(*
Fixpoint mapWithIndexTree {a} {b} `{Sized a} (f : GHC.Num.Int -> a -> b) (s : GHC.Num.Int) (ft: FingerTree a) : FingerTree b :=
  match ft with
  | Empty => GHC.Prim.seq s Empty
  | Single xs => Single GHC.Base.$ f s xs
  | Deep n pr m sf => let sPsprm := (s GHC.Num.+ n) GHC.Num.- size sf in
                             let sPspr := s GHC.Num.+ size pr in
                             GHC.Prim.seq sPspr (GHC.Prim.seq sPsprm (Deep n
                                                                           (mapWithIndexDigit
                                                                              f s pr)
                                                                           (mapWithIndexTree
                                                                              (mapWithIndexNode
                                                                                 f) sPspr m)
                                                                           (mapWithIndexDigit
                                                                              f sPsprm sf)))
  end.

Definition mapWithIndex {a} {b} : (GHC.Num.Int -> a -> b) -> Seq a -> Seq b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f' , Mk_Seq xs' =>  Mk_Seq GHC.Base.$ mapWithIndexTree (fun arg_34__ arg_35__ =>
                                                                match arg_34__ , arg_35__ with
                                                                  | s , Mk_Elem a => Mk_Elem (f' s a)
                                                                end) (GHC.Num.fromInteger 0) xs'
    end.
*)

(* ---------------------------------------- *)

Parameter viewLTree : forall {a} `{Sized a}, (FingerTree a) -> Maybe2 a (FingerTree a).
(*
Fixpoint viewLTree {a} `{Sized a} ( arg_0__ : FingerTree a) : Maybe2 a (FingerTree a) :=
  let pullL {a} : GHC.Num.Int -> FingerTree (Node a) -> Digit
                       a -> FingerTree a :=
  fun s m sf =>
    match viewLTree m with
      | Nothing2 => digitToTree' s sf
      | Just2 pr m' => Deep s (nodeToDigit pr) m' sf
    end in

    match arg_0__ with
      | Empty => Nothing2
      | Single a => Just2 a Empty
      | Deep s (One a) m sf => Just2 a (pullL (s GHC.Num.- size a) m sf)
      | Deep s (Two a b) m sf => Just2 a (Deep (s GHC.Num.- size a) (One b) m sf)
      | Deep s (Three a b c) m sf => Just2 a (Deep (s GHC.Num.- size a) (Two b c) m
                                             sf)
      | Deep s (Four a b c d) m sf => Just2 a (Deep (s GHC.Num.- size a) (Three b c d)
                                              m sf)
    end. *)

Parameter viewRTree : forall {a} `{Sized a}, (FingerTree a) -> Maybe2 (FingerTree a) a.

(*
Fixpoint viewRTree {a} `{Sized a} (arg_0__ : FingerTree a) : Maybe2 (FingerTree a) a :=
  let pullR {a} : GHC.Num.Int -> Digit a -> FingerTree (Node
                                                            a) -> FingerTree a :=
  fun s pr m =>
    match viewRTree m with
      | Nothing2 => digitToTree' s pr
      | Just2 m' sf => Deep s pr m' (nodeToDigit sf)
    end in

    match arg_0__ with
      | Empty => Nothing2
      | Single z => Just2 Empty z
      | Deep s pr m (One z) => Just2 (pullR (s GHC.Num.- size z) pr m) z
      | Deep s pr m (Two y z) => Just2 (Deep (s GHC.Num.- size z) pr m (One y)) z
      | Deep s pr m (Three x y z) => Just2 (Deep (s GHC.Num.- size z) pr m (Two x y))
                                     z
      | Deep s pr m (Four w x y z) => Just2 (Deep (s GHC.Num.- size z) pr m (Three w x
                                                                            y)) z
    end.
*)

(*
Fixpoint initsTree {a} {b} `{_:Sized a} (f : (FingerTree a) -> b) (arg_1__ : FingerTree a) : FingerTree b :=
      match arg_1__ with
             | Empty => Empty
             | Single x => Single (f (Single x))
             | Deep n pr m sf =>
                let f' := fun ms =>
                            (match viewRTree ms with
                            | Just2 m' node => GHC.Base.fmap (fun sf' => f (deep pr m' sf')) (initsNode node)
                            | Nothing2 => error
                            end) in
                Deep n (GHC.Base.fmap (f GHC.Base.∘ digitToTree) (initsDigit pr)) (initsTree f' m)
                     (GHC.Base.fmap (f GHC.Base.∘ deep pr m) (initsDigit sf))
           end. *)

Parameter applicativeTree : forall {f} {a} `{GHC.Base.Applicative f},
     GHC.Num.Int -> GHC.Num.Int -> f a -> f (FingerTree a).

Parameter cycleNMiddle : forall {c}, GHC.Num.Int -> Rigid c -> FingerTree (Node c).

Parameter initsTree : forall {a} {b} `{_:Sized a}, ((FingerTree a) -> b) -> (FingerTree a) -> FingerTree b.

(* ----------------------------------------------- *)
