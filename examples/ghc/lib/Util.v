(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Nat.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Bits.
Require Data.Either.
Require Data.Foldable.
Require Data.OldList.
Require GHC.Base.
Require GHC.Char.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require Panic.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Suffix :=
  GHC.Base.String%type.

Inductive OverridingBool : Type
  := | Auto : OverridingBool
  |  Always : OverridingBool
  |  Never : OverridingBool.

Definition HasDebugCallStack :=
  unit.

Inductive Direction : Type := | Forwards : Direction |  Backwards : Direction.

Instance Default__OverridingBool : GHC.Err.Default OverridingBool :=
  GHC.Err.Build_Default _ Auto.

Instance Default__Direction : GHC.Err.Default Direction :=
  GHC.Err.Build_Default _ Forwards.

(* Midamble *)

Definition foldl2 {acc} {a} {b} `{GHC.Err.Default acc}
   : (acc -> a -> b -> acc) -> acc -> list a -> list b -> acc :=
  fix foldl2 arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | _, z, nil, nil => z
           | k, z, cons a as_, cons b bs => foldl2 k (k z a b) as_ bs
           | _, _, _, _ => Panic.panic (GHC.Base.hs_string__ "Util: foldl2")
           end.




(* Converted value declarations: *)

Definition zipWithLazy {a} {b} {c}
   : (a -> b -> c) -> list a -> list b -> list c :=
  fix zipWithLazy (arg_0__ : (a -> b -> c)) (arg_1__ : list a) (arg_2__ : list b)
        : list c
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, _ => nil
           | f, cons a as_, cons b bs => cons (f a b) (zipWithLazy f as_ bs)
           | _, _, _ => GHC.Err.patternFailure
           end.

Definition zipWithEqual {a} {b} {c}
   : GHC.Base.String -> (a -> b -> c) -> list a -> list b -> list c :=
  fun arg_0__ => GHC.List.zipWith.

Definition zipWithAndUnzip {a} {b} {c} {d}
   : (a -> b -> (c * d)%type) -> list a -> list b -> (list c * list d)%type :=
  fix zipWithAndUnzip (arg_0__ : (a -> b -> (c * d)%type)) (arg_1__ : list a)
                      (arg_2__ : list b) : (list c * list d)%type
        := match arg_0__, arg_1__, arg_2__ with
           | f, cons a as_, cons b bs =>
               let 'pair rs1 rs2 := zipWithAndUnzip f as_ bs in
               let 'pair r1 r2 := f a b in
               pair (cons r1 rs1) (cons r2 rs2)
           | _, _, _ => pair nil nil
           end.

Definition zipWith4Equal {a} {b} {c} {d} {e}
   : GHC.Base.String ->
     (a -> b -> c -> d -> e) -> list a -> list b -> list c -> list d -> list e :=
  fun arg_0__ => Data.OldList.zipWith4.

Definition zipWith3Lazy {a} {b} {c} {d}
   : (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fix zipWith3Lazy (arg_0__ : (a -> b -> c -> d)) (arg_1__ : list a) (arg_2__
                     : list b) (arg_3__ : list c) : list d
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | _, nil, _, _ => nil
           | f, cons a as_, cons b bs, cons c cs =>
               cons (f a b c) (zipWith3Lazy f as_ bs cs)
           | _, _, _, _ => GHC.Err.patternFailure
           end.

Definition zipWith3Equal {a} {b} {c} {d}
   : GHC.Base.String ->
     (a -> b -> c -> d) -> list a -> list b -> list c -> list d :=
  fun arg_0__ => GHC.List.zipWith3.

Definition zipLazy {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zipLazy (arg_0__ : list a) (arg_1__ : list b) : list (a * b)%type
        := match arg_0__, arg_1__ with
           | nil, _ => nil
           | cons x xs, cons y ys => cons (pair x y) (zipLazy xs ys)
           | _, _ => GHC.Err.patternFailure
           end.

Definition zipEqual {a} {b}
   : GHC.Base.String -> list a -> list b -> list (a * b)%type :=
  fun arg_0__ => GHC.List.zip.

Definition unzipWith {a} {b} {c}
   : (a -> b -> c) -> list (a * b)%type -> list c :=
  fun f pairs => GHC.Base.map (fun '(pair a b) => f a b) pairs.

Definition uncurry3 {a} {b} {c} {d}
   : (a -> b -> c -> d) -> (a * b * c)%type -> d :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => f a b c
    end.

Definition transitiveClosure {a}
   : (a -> list a) -> (a -> a -> bool) -> list a -> list a :=
  fun succ eq xs =>
    let fix is_in arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | _, nil => false
                 | x, cons y ys => if eq x y : bool then true else is_in x ys
                 end in
    let go :=
      GHC.DeferredFix.deferredFix2 (fun go arg_5__ arg_6__ =>
                                      match arg_5__, arg_6__ with
                                      | done, nil => done
                                      | done, cons x xs =>
                                          if is_in x done : bool then go done xs else
                                          go (cons x done) (Coq.Init.Datatypes.app (succ x) xs)
                                      end) in
    go nil xs.

Definition third3 {c} {d} {a} {b}
   : (c -> d) -> (a * b * c)%type -> (a * b * d)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair a b) (f c)
    end.

Definition thenCmp : comparison -> comparison -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Eq, ordering => ordering
    | ordering, _ => ordering
    end.

Definition thdOf3 {a} {b} {c} : (a * b * c)%type -> c :=
  fun '(pair (pair _ _) c) => c.

Definition takeList {b} {a} : list b -> list a -> list a :=
  fix takeList (arg_0__ : list b) (arg_1__ : list a) : list a
        := match arg_0__, arg_1__ with
           | nil, _ => nil
           | cons _ xs, ls =>
               match ls with
               | nil => nil
               | cons y ys => cons y (takeList xs ys)
               end
           end.

Definition stretchZipWith {a} {b} {c}
   : (a -> bool) -> b -> (a -> b -> c) -> list a -> list b -> list c :=
  fix stretchZipWith (arg_0__ : (a -> bool)) (arg_1__ : b) (arg_2__
                       : (a -> b -> c)) (arg_3__ : list a) (arg_4__ : list b) : list c
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | _, _, _, nil, _ => nil
           | p, z, f, cons x xs, ys =>
               if p x : bool then cons (f x z) (stretchZipWith p z f xs ys) else
               match ys with
               | nil => nil
               | cons y ys => cons (f x y) (stretchZipWith p z f xs ys)
               end
           end.

Definition splitEithers {a} {b}
   : list (Data.Either.Either a b) -> (list a * list b)%type :=
  fix splitEithers (arg_0__ : list (Data.Either.Either a b)) : (list a *
                                                                list b)%type
        := match arg_0__ with
           | nil => pair nil nil
           | cons e es =>
               let 'pair xs ys := splitEithers es in
               match e with
               | Data.Either.Left x => pair (cons x xs) ys
               | Data.Either.Right y => pair xs (cons y ys)
               end
           end.

Definition splitAtList {b} {a} : list b -> list a -> (list a * list a)%type :=
  fix splitAtList (arg_0__ : list b) (arg_1__ : list a) : (list a * list a)%type
        := match arg_0__, arg_1__ with
           | nil, xs => pair nil xs
           | _, (nil as xs) => pair xs xs
           | cons _ xs, cons y ys =>
               let 'pair ys' ys'' := splitAtList xs ys in
               pair (cons y ys') ys''
           end.

Definition split : GHC.Char.Char -> GHC.Base.String -> list GHC.Base.String :=
  GHC.DeferredFix.deferredFix2 (fun split
                                (c : GHC.Char.Char)
                                (s : GHC.Base.String) =>
                                  let 'pair chunk rest := GHC.List.break (fun arg_0__ => arg_0__ GHC.Base.== c)
                                                            s in
                                  match rest with
                                  | nil => cons chunk nil
                                  | cons _ rest => cons chunk (split c rest)
                                  end).

Definition spanEnd {a} : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p l =>
    let fix go arg_0__ arg_1__ arg_2__ arg_3__
              := match arg_0__, arg_1__, arg_2__, arg_3__ with
                 | yes, _rev_yes, rev_no, nil => pair yes (GHC.List.reverse rev_no)
                 | yes, rev_yes, rev_no, cons x xs =>
                     if p x : bool then go yes (cons x rev_yes) rev_no xs else
                     go xs nil (cons x (Coq.Init.Datatypes.app rev_yes rev_no)) xs
                 end in
    go l nil nil l.

Definition snocView {a} : list a -> option (list a * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | xs =>
        let fix go arg_1__ arg_2__
                  := match arg_1__, arg_2__ with
                     | acc, cons x nil => Some (pair (GHC.List.reverse acc) x)
                     | acc, cons x xs => go (cons x acc) xs
                     | _, nil => Panic.panic (GHC.Base.hs_string__ "Util: snocView")
                     end in
        go nil xs
    end.

Definition sndOf3 {a} {b} {c} : (a * b * c)%type -> b :=
  fun '(pair (pair _ b) _) => b.

Definition snd3 {b} {d} {a} {c}
   : (b -> d) -> (a * b * c)%type -> (a * d * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair a (f b)) c
    end.

Definition sizedComplement {bv} `{Data.Bits.Bits bv} : bv -> bv -> bv :=
  fun vector_mask vect => Data.Bits.xor vector_mask vect.

Definition singleton {a} : a -> list a :=
  fun x => cons x nil.

Definition seqList {a} {b} : list a -> b -> b :=
  fix seqList (arg_0__ : list a) (arg_1__ : b) : b
        := match arg_0__, arg_1__ with
           | nil, b => b
           | cons x xs, b => GHC.Prim.seq x (seqList xs b)
           end.

Definition partitionWith {a} {b} {c}
   : (a -> Data.Either.Either b c) -> list a -> (list b * list c)%type :=
  fix partitionWith (arg_0__ : (a -> Data.Either.Either b c)) (arg_1__ : list a)
        : (list b * list c)%type
        := match arg_0__, arg_1__ with
           | _, nil => pair nil nil
           | f, cons x xs =>
               let 'pair bs cs := partitionWith f xs in
               match f x with
               | Data.Either.Left b => pair (cons b bs) cs
               | Data.Either.Right c => pair bs (cons c cs)
               end
           end.

Definition partitionByList {a}
   : list bool -> list a -> (list a * list a)%type :=
  let fix go arg_0__ arg_1__ arg_2__ arg_3__
            := match arg_0__, arg_1__, arg_2__, arg_3__ with
               | trues, falses, cons true bs, cons x xs => go (cons x trues) falses bs xs
               | trues, falses, cons false bs, cons x xs => go trues (cons x falses) bs xs
               | trues, falses, _, _ => pair (GHC.List.reverse trues) (GHC.List.reverse falses)
               end in
  go nil nil.

Definition overrideWith : bool -> OverridingBool -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | b, Auto => b
    | _, Always => true
    | _, Never => false
    end.

Definition op_zlzbzbzg__ {f} `{GHC.Base.Applicative f}
   : f bool -> f bool -> f bool :=
  GHC.Base.liftA2 orb.

Notation "'_<||>_'" := (op_zlzbzbzg__).

Infix "<||>" := (_<||>_) (at level 99).

Definition op_zlzazazg__ {f} `{GHC.Base.Applicative f}
   : f bool -> f bool -> f bool :=
  GHC.Base.liftA2 andb.

Notation "'_<&&>_'" := (op_zlzazazg__).

Infix "<&&>" := (_<&&>_) (at level 99).

Definition notNull {a} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => false | _ => true end.

Definition neLength {a} {b} : list a -> list b -> bool :=
  fix neLength (arg_0__ : list a) (arg_1__ : list b) : bool
        := match arg_0__, arg_1__ with
           | nil, nil => false
           | cons _ xs, cons _ ys => neLength xs ys
           | _, _ => true
           end.

Definition ncgDebugIsOn : bool :=
  false.

Definition nOfThem {a} : nat -> a -> list a :=
  fun n thing => Coq.Lists.List.repeat thing n.

Definition mapSnd {b} {c} {a}
   : (b -> c) -> list (a * b)%type -> list (a * c)%type :=
  fun f xys =>
    let cont_0__ arg_1__ := let 'pair x y := arg_1__ in cons (pair x (f y)) nil in
    Coq.Lists.List.flat_map cont_0__ xys.

Definition mapFst {a} {c} {b}
   : (a -> c) -> list (a * b)%type -> list (c * b)%type :=
  fun f xys =>
    let cont_0__ arg_1__ := let 'pair x y := arg_1__ in cons (pair (f x) y) nil in
    Coq.Lists.List.flat_map cont_0__ xys.

Definition mapAndUnzip3 {a} {b} {c} {d}
   : (a -> (b * c * d)%type) -> list a -> (list b * list c * list d)%type :=
  fix mapAndUnzip3 (arg_0__ : (a -> (b * c * d)%type)) (arg_1__ : list a) : (list
                                                                             b *
                                                                             list c *
                                                                             list d)%type
        := match arg_0__, arg_1__ with
           | _, nil => pair (pair nil nil) nil
           | f, cons x xs =>
               let 'pair (pair rs1 rs2) rs3 := mapAndUnzip3 f xs in
               let 'pair (pair r1 r2) r3 := f x in
               pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3 rs3)
           end.

Definition mapAndUnzip {a} {b} {c} (f : a -> b * c)
   : list a -> list b * list c :=
  fix mapAndUnzip y
        := match y with
           | nil => pair nil nil
           | cons x xs =>
               let 'pair rs1 rs2 := mapAndUnzip xs in
               let 'pair r1 r2 := f x in
               pair (cons r1 rs1) (cons r2 rs2)
           end.

Definition makeRelativeTo
   : GHC.Base.String -> GHC.Base.String -> GHC.Base.String :=
  fun this that => this.

Definition looksLikePackageName : GHC.Base.String -> bool :=
  fun x => false.

Definition liftSnd {a} {b} {c} : (a -> b) -> (c * a)%type -> (c * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair c a => pair c (f a)
    end.

Definition liftFst {a} {b} {c} : (a -> b) -> (a * c)%type -> (b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair a c => pair (f a) c
    end.

Definition isn'tIn {a} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.notElem x ys.

Definition isWindowsHost : bool :=
  false.

Definition isSingleton {a} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | cons _ nil => true | _ => false end.

Definition isIn {a} `{GHC.Base.Eq_ a}
   : GHC.Base.String -> a -> list a -> bool :=
  fun _msg x ys => Data.Foldable.elem x ys.

Definition isEqual : comparison -> bool :=
  fun arg_0__ => match arg_0__ with | Gt => false | Eq => true | Lt => false end.

Definition ghciTablesNextToCode : bool :=
  false.

Definition ghciSupported : bool :=
  false.

Definition fstOf3 {a} {b} {c} : (a * b * c)%type -> a :=
  fun '(pair (pair a _) _) => a.

Definition fst3 {a} {d} {b} {c}
   : (a -> d) -> (a * b * c)%type -> (d * b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair a b) c => pair (pair (f a) b) c
    end.

Definition firstM {m} {a} {c} {b} `{GHC.Base.Monad m}
   : (a -> m c) -> (a * b)%type -> m (c * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair x y => GHC.Base.liftM (fun x' => pair x' y) (f x)
    end.

Definition first3M {m} {a} {d} {b} {c} `{GHC.Base.Monad m}
   : (a -> m d) -> (a * b * c)%type -> m (d * b * c)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, pair (pair x y) z => GHC.Base.liftM (fun x' => pair (pair x' y) z) (f x)
    end.

Definition filterOut {a} : (a -> bool) -> list a -> list a :=
  fix filterOut (arg_0__ : (a -> bool)) (arg_1__ : list a) : list a
        := match arg_0__, arg_1__ with
           | _, nil => nil
           | p, cons x xs => if p x : bool then filterOut p xs else cons x (filterOut p xs)
           end.

Definition filterByLists {a} : list bool -> list a -> list a -> list a :=
  fix filterByLists (arg_0__ : list bool) (arg_1__ arg_2__ : list a) : list a
        := match arg_0__, arg_1__, arg_2__ with
           | cons true bs, cons x xs, cons _ ys => cons x (filterByLists bs xs ys)
           | cons false bs, cons _ xs, cons y ys => cons y (filterByLists bs xs ys)
           | _, _, _ => nil
           end.

Definition filterByList {a} : list bool -> list a -> list a :=
  fix filterByList (arg_0__ : list bool) (arg_1__ : list a) : list a
        := match arg_0__, arg_1__ with
           | cons true bs, cons x xs => cons x (filterByList bs xs)
           | cons false bs, cons _ xs => filterByList bs xs
           | _, _ => nil
           end.

Definition exactLog2 : GHC.Num.Integer -> option GHC.Num.Integer :=
  fun x =>
    let pow2 :=
      GHC.DeferredFix.deferredFix1 (fun pow2 x =>
                                      if x GHC.Base.== #1 : bool then #0 else
                                      #1 GHC.Num.+ pow2 (Data.Bits.shiftR x #1)) in
    if (orb (x GHC.Base.<= #0) (x GHC.Base.>= #2147483648)) : bool
    then None
    else if (x Data.Bits..&.(**) (GHC.Num.negate x)) GHC.Base./= x : bool
         then None
         else Some (pow2 x).

Definition equalLength {a} {b} : list a -> list b -> bool :=
  fix equalLength (arg_0__ : list a) (arg_1__ : list b) : bool
        := match arg_0__, arg_1__ with
           | nil, nil => true
           | cons _ xs, cons _ ys => equalLength xs ys
           | _, _ => false
           end.

Definition eqMaybeBy {a} : (a -> a -> bool) -> option a -> option a -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, None, None => true
    | eq, Some x, Some y => eq x y
    | _, _, _ => false
    end.

Definition eqListBy {a} : (a -> a -> bool) -> list a -> list a -> bool :=
  fix eqListBy (arg_0__ : (a -> a -> bool)) (arg_1__ arg_2__ : list a) : bool
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, nil => true
           | eq, cons x xs, cons y ys => andb (eq x y) (eqListBy eq xs ys)
           | _, _, _ => false
           end.

Definition dropWhileEndLE {a} : (a -> bool) -> list a -> list a :=
  fun p =>
    Data.Foldable.foldr (fun x r =>
                           if andb (Data.Foldable.null r) (p x) : bool
                           then nil
                           else cons x r) nil.

Definition dropTail {a} : nat -> list a -> list a :=
  fun n xs =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | cons _ ys, cons x xs => cons x (go ys xs)
                 | _, _ => nil
                 end in
    go (Coq.Lists.List.skipn n xs) xs.

Definition dropList {b} {a} : list b -> list a -> list a :=
  fix dropList (arg_0__ : list b) (arg_1__ : list a) : list a
        := match arg_0__, arg_1__ with
           | nil, xs => xs
           | _, (nil as xs) => xs
           | cons _ xs, cons _ ys => dropList xs ys
           end.

Definition debugIsOn : bool :=
  false.

Definition count {a} : (a -> bool) -> list a -> nat :=
  fun p =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | n, nil => n
                 | n, cons x xs => if p x : bool then go (n GHC.Num.+ #1) xs else go n xs
                 end in
    go #0.

Definition compareLength {a} {b} : list a -> list b -> comparison :=
  fix compareLength (arg_0__ : list a) (arg_1__ : list b) : comparison
        := match arg_0__, arg_1__ with
           | nil, nil => Eq
           | cons _ xs, cons _ ys => compareLength xs ys
           | nil, _ => Lt
           | _, nil => Gt
           end.

Definition leLength {a} {b} : list a -> list b -> bool :=
  fun xs ys =>
    match compareLength xs ys with
    | Lt => true
    | Eq => true
    | Gt => false
    end.

Definition ltLength {a} {b} : list a -> list b -> bool :=
  fun xs ys =>
    match compareLength xs ys with
    | Lt => true
    | Eq => false
    | Gt => false
    end.

Definition cmpList {a}
   : (a -> a -> comparison) -> list a -> list a -> comparison :=
  fix cmpList (arg_0__ : (a -> a -> comparison)) (arg_1__ arg_2__ : list a)
        : comparison
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, nil => Eq
           | _, nil, _ => Lt
           | _, _, nil => Gt
           | cmp, cons a as_, cons b bs =>
               match cmp a b with
               | Eq => cmpList cmp as_ bs
               | xxx => xxx
               end
           end.

Definition chkAppend {a} : list a -> list a -> list a :=
  fun xs ys =>
    if Data.Foldable.null ys : bool then xs else
    Coq.Init.Datatypes.app xs ys.

Definition changeLast {a} : list a -> a -> list a :=
  fix changeLast (arg_0__ : list a) (arg_1__ : a) : list a
        := match arg_0__, arg_1__ with
           | nil, _ => Panic.panic (GHC.Base.hs_string__ "changeLast")
           | cons _ nil, x => cons x nil
           | cons x xs, x' => cons x (changeLast xs x')
           end.

Definition capitalise : GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ => match arg_0__ with | nil => nil | cons c cs => cons c cs end.

Definition atLength {a} {b} : (list a -> b) -> b -> list a -> nat -> b :=
  fun atLenPred atEnd ls0 n0 =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | num_2__, ls =>
                     if num_2__ GHC.Base.== #0 : bool then atLenPred ls else
                     match arg_0__, arg_1__ with
                     | _, nil => atEnd
                     | n, cons _ xs => go (n GHC.Num.- #1) xs
                     end
                 end in
    if n0 GHC.Base.< #0 : bool then atLenPred ls0 else
    go n0 ls0.

Definition lengthAtLeast {a} : list a -> nat -> bool :=
  atLength (GHC.Base.const true) false.

Definition lengthAtMost {a} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then false else
    atLength Data.Foldable.null true lst n.

Definition lengthExceeds {a} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then true else
    atLength notNull false lst n.

Definition lengthIs {a} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then false else
    atLength Data.Foldable.null false lst n.

Definition lengthIsNot {a} : list a -> nat -> bool :=
  fun lst n =>
    if n GHC.Base.< #0 : bool then true else
    atLength notNull true lst n.

Definition lengthLessThan {a} : list a -> nat -> bool :=
  atLength (GHC.Base.const false) true.

Definition listLengthCmp {a} : list a -> nat -> comparison :=
  let atLen := fun arg_0__ => match arg_0__ with | nil => Eq | _ => Gt end in
  let atEnd := Lt in atLength atLen atEnd.

Definition all2 {a} {b} : (a -> b -> bool) -> list a -> list b -> bool :=
  fix all2 (arg_0__ : (a -> b -> bool)) (arg_1__ : list a) (arg_2__ : list b)
        : bool
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, nil => true
           | p, cons x xs, cons y ys => andb (p x y) (all2 p xs ys)
           | _, _, _ => false
           end.

(* Skipping all instances of class `GHC.Show.Show', including
   `Util.Show__OverridingBool' *)

Module Notations.
Notation "'_Util.<||>_'" := (op_zlzbzbzg__).
Infix "Util.<||>" := (_<||>_) (at level 99).
Notation "'_Util.<&&>_'" := (op_zlzazazg__).
Infix "Util.<&&>" := (_<&&>_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some andb bool comparison cons false list nat nil op_zt__ option
     orb pair true unit Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Coq.Lists.List.repeat Coq.Lists.List.skipn Data.Bits.Bits Data.Bits.op_zizazi__
     Data.Bits.shiftR Data.Bits.xor Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.elem Data.Foldable.foldr Data.Foldable.notElem
     Data.Foldable.null Data.OldList.zipWith4 GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.String GHC.Base.const GHC.Base.liftA2 GHC.Base.liftM
     GHC.Base.map GHC.Base.op_zeze__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Char.Char GHC.DeferredFix.deferredFix1
     GHC.DeferredFix.deferredFix2 GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.patternFailure GHC.List.break GHC.List.reverse GHC.List.zip
     GHC.List.zipWith GHC.List.zipWith3 GHC.Num.Integer GHC.Num.fromInteger
     GHC.Num.negate GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Prim.seq Panic.panic
*)
