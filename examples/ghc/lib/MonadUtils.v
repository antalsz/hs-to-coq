(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.
Require Data.Either.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Traversable.
Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition zipWithAndUnzipM {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
   : (a -> b -> m (c * d)%type) -> list a -> list b -> m (list c * list d)%type :=
  fix zipWithAndUnzipM arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | f, cons x xs, cons y ys =>
               let cont_3__ arg_4__ :=
                 let 'pair c d := arg_4__ in
                 let cont_5__ arg_6__ :=
                   let 'pair cs ds := arg_6__ in
                   GHC.Base.return_ (pair (cons c cs) (cons d ds)) in
                 zipWithAndUnzipM f xs ys GHC.Base.>>= cont_5__ in
               f x y GHC.Base.>>= cont_3__
           | _, _, _ => GHC.Base.return_ (pair nil nil)
           end.

Definition zipWith4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m}
   : (a -> b -> c -> d -> m e) ->
     list a -> list b -> list c -> list d -> m (list e) :=
  fix zipWith4M arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | _, nil, _, _, _ => GHC.Base.return_ nil
           | _, _, nil, _, _ => GHC.Base.return_ nil
           | _, _, _, nil, _ => GHC.Base.return_ nil
           | _, _, _, _, nil => GHC.Base.return_ nil
           | f, cons x xs, cons y ys, cons z zs, cons a as_ =>
               f x y z a GHC.Base.>>=
               (fun r =>
                  zipWith4M f xs ys zs as_ GHC.Base.>>= (fun rs => GHC.Base.return_ (cons r rs)))
           end.

Definition zipWith3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
   : (a -> b -> c -> m d) -> list a -> list b -> list c -> m (list d) :=
  fix zipWith3M arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | _, nil, _, _ => GHC.Base.return_ nil
           | _, _, nil, _ => GHC.Base.return_ nil
           | _, _, _, nil => GHC.Base.return_ nil
           | f, cons x xs, cons y ys, cons z zs =>
               f x y z GHC.Base.>>=
               (fun r =>
                  zipWith3M f xs ys zs GHC.Base.>>= (fun rs => GHC.Base.return_ (cons r rs)))
           end.

Definition zipWith3M_ {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
   : (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit :=
  fun f as_ bs cs =>
    zipWith3M f as_ bs cs GHC.Base.>>= (fun _ => GHC.Base.return_ tt).

Definition whenM {m} `{GHC.Base.Monad m} : m bool -> m unit -> m unit :=
  fun mb thing => mb GHC.Base.>>= (fun b => GHC.Base.when b thing).

Definition orM {m} `{GHC.Base.Monad m} : m bool -> m bool -> m bool :=
  fun m1 m2 =>
    m1 GHC.Base.>>= (fun x => if x : bool then GHC.Base.return_ true else m2).

Definition maybeMapM {m} {a} {b} `{GHC.Base.Monad m}
   : (a -> m b) -> (option a -> m (option b)) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, None => GHC.Base.return_ None
    | m, Some x => GHC.Base.liftM Some (m x)
    end.

Definition mapSndM {m} {b} {c} {a} `{GHC.Base.Monad m}
   : (b -> m c) -> list (a * b)%type -> m (list (a * c)%type) :=
  fix mapSndM arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ nil
           | f, cons (pair a b) xs =>
               f b GHC.Base.>>=
               (fun c =>
                  mapSndM f xs GHC.Base.>>= (fun rs => GHC.Base.return_ (cons (pair a c) rs)))
           end.

Definition mapMaybeM {m} {a} {b} `{(GHC.Base.Monad m)}
   : (a -> m (option b)) -> list a -> m (list b) :=
  fun f => GHC.Base.liftM Data.Maybe.catMaybes GHC.Base.∘ Data.Traversable.mapM f.

Definition mapAndUnzip5M {m} {a} {b} {c} {d} {e} {f} `{GHC.Base.Monad m}
   : (a -> m (b * c * d * e * f)%type) ->
     list a -> m (list b * list c * list d * list e * list f)%type :=
  fix mapAndUnzip5M arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ (pair (pair (pair (pair nil nil) nil) nil) nil)
           | f, cons x xs =>
               let cont_3__ arg_4__ :=
                 let 'pair (pair (pair (pair r1 r2) r3) r4) r5 := arg_4__ in
                 let cont_5__ arg_6__ :=
                   let 'pair (pair (pair (pair rs1 rs2) rs3) rs4) rs5 := arg_6__ in
                   GHC.Base.return_ (pair (pair (pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3
                                                                                               rs3)) (cons r4 rs4))
                                          (cons r5 rs5)) in
                 mapAndUnzip5M f xs GHC.Base.>>= cont_5__ in
               f x GHC.Base.>>= cont_3__
           end.

Definition mapAndUnzip4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m}
   : (a -> m (b * c * d * e)%type) ->
     list a -> m (list b * list c * list d * list e)%type :=
  fix mapAndUnzip4M arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ (pair (pair (pair nil nil) nil) nil)
           | f, cons x xs =>
               let cont_3__ arg_4__ :=
                 let 'pair (pair (pair r1 r2) r3) r4 := arg_4__ in
                 let cont_5__ arg_6__ :=
                   let 'pair (pair (pair rs1 rs2) rs3) rs4 := arg_6__ in
                   GHC.Base.return_ (pair (pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3 rs3))
                                          (cons r4 rs4)) in
                 mapAndUnzip4M f xs GHC.Base.>>= cont_5__ in
               f x GHC.Base.>>= cont_3__
           end.

Definition mapAndUnzip3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
   : (a -> m (b * c * d)%type) -> list a -> m (list b * list c * list d)%type :=
  fix mapAndUnzip3M arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ (pair (pair nil nil) nil)
           | f, cons x xs =>
               let cont_3__ arg_4__ :=
                 let 'pair (pair r1 r2) r3 := arg_4__ in
                 let cont_5__ arg_6__ :=
                   let 'pair (pair rs1 rs2) rs3 := arg_6__ in
                   GHC.Base.return_ (pair (pair (cons r1 rs1) (cons r2 rs2)) (cons r3 rs3)) in
                 mapAndUnzip3M f xs GHC.Base.>>= cont_5__ in
               f x GHC.Base.>>= cont_3__
           end.

Definition mapAccumLM {m} {acc} {x} {y} `{GHC.Base.Monad m}
   : (acc -> x -> m (acc * y)%type) -> acc -> list x -> m (acc * list y)%type :=
  fix mapAccumLM arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, s, nil => GHC.Base.return_ (pair s nil)
           | f, s, cons x xs =>
               let cont_4__ arg_5__ :=
                 let 'pair s1 x' := arg_5__ in
                 let cont_6__ arg_7__ :=
                   let 'pair s2 xs' := arg_7__ in
                   GHC.Base.return_ (pair s2 (cons x' xs')) in
                 mapAccumLM f s1 xs GHC.Base.>>= cont_6__ in
               f s x GHC.Base.>>= cont_4__
           end.

Definition foldrM {m} {b} {a} `{(GHC.Base.Monad m)}
   : (b -> a -> m a) -> a -> list b -> m a :=
  fix foldrM arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, z, nil => GHC.Base.return_ z
           | k, z, cons x xs => foldrM k z xs GHC.Base.>>= (fun r => k x r)
           end.

Definition foldlM_ {m} {a} {b} `{(GHC.Base.Monad m)}
   : (a -> b -> m a) -> a -> list b -> m unit :=
  Control.Monad.foldM_.

Definition foldlM {m} {a} {b} `{(GHC.Base.Monad m)}
   : (a -> b -> m a) -> a -> list b -> m a :=
  Control.Monad.foldM.

Definition fmapMaybeM {m} {a} {b} `{(GHC.Base.Monad m)}
   : (a -> m b) -> option a -> m (option b) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, None => GHC.Base.return_ None
    | f, Some x => f x GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘ Some)
    end.

Definition fmapEitherM {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
   : (a -> m b) ->
     (c -> m d) -> Data.Either.Either a c -> m (Data.Either.Either b d) :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | fl, _, Data.Either.Left a =>
        fl a GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘ Data.Either.Left)
    | _, fr, Data.Either.Right b =>
        fr b GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘ Data.Either.Right)
    end.

Definition concatMapM {m} {a} {b} `{GHC.Base.Monad m}
   : (a -> m (list b)) -> list a -> m (list b) :=
  fun f xs => GHC.Base.liftM Data.Foldable.concat (Data.Traversable.mapM f xs).

Definition anyM {m} {a} `{GHC.Base.Monad m}
   : (a -> m bool) -> list a -> m bool :=
  fix anyM arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ false
           | f, cons x xs =>
               f x GHC.Base.>>=
               (fun b => if b : bool then GHC.Base.return_ true else anyM f xs)
           end.

Definition allM {m} {a} `{GHC.Base.Monad m}
   : (a -> m bool) -> list a -> m bool :=
  fix allM arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, nil => GHC.Base.return_ true
           | f, cons b bs =>
               (f b) GHC.Base.>>=
               (fun bv => if bv : bool then allM f bs else GHC.Base.return_ false)
           end.

(* External variables:
     None Some bool cons false list nil op_zt__ option pair true tt unit
     Control.Monad.foldM Control.Monad.foldM_ Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.concat Data.Maybe.catMaybes
     Data.Traversable.mapM GHC.Base.Monad GHC.Base.liftM GHC.Base.op_z2218U__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Base.when
*)
