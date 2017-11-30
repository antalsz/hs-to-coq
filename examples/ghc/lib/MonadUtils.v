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

Definition allM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> list a -> m
                                              bool :=
  fix allM arg_14__ arg_15__
        := match arg_14__ , arg_15__ with
             | _ , nil => GHC.Base.return_ true
             | f , cons b bs => (f b) GHC.Base.>>= (fun bv =>
                                  if bv : bool
                                  then allM f bs
                                  else GHC.Base.return_ false)
           end.

Definition anyM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> list a -> m
                                              bool :=
  fix anyM arg_20__ arg_21__
        := match arg_20__ , arg_21__ with
             | _ , nil => GHC.Base.return_ false
             | f , cons x xs => f x GHC.Base.>>= (fun b =>
                                  if b : bool
                                  then GHC.Base.return_ true
                                  else anyM f xs)
           end.

Definition concatMapM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m (list
                                                                b)) -> list a -> m (list b) :=
  fun f xs => GHC.Base.liftM Data.Foldable.concat (Data.Traversable.mapM f xs).

Definition fmapEitherM {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> m
                                                                 b) -> (c -> m d) -> Data.Either.Either a c -> m
                                                                 (Data.Either.Either b d) :=
  fun arg_25__ arg_26__ arg_27__ =>
    match arg_25__ , arg_26__ , arg_27__ with
      | fl , _ , Data.Either.Left a => fl a GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘
                                       Data.Either.Left)
      | _ , fr , Data.Either.Right b => fr b GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘
                                        Data.Either.Right)
    end.

Definition fmapMaybeM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> m b) -> option
                                                          a -> m (option b) :=
  fun arg_31__ arg_32__ =>
    match arg_31__ , arg_32__ with
      | _ , None => GHC.Base.return_ None
      | f , Some x => f x GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘ Some)
    end.

Definition foldlM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                      a) -> a -> list b -> m a :=
  Control.Monad.foldM.

Definition foldlM_ {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                       a) -> a -> list b -> m unit :=
  Control.Monad.foldM_.

Definition foldrM {m} {b} {a} `{(GHC.Base.Monad m)} : (b -> a -> m
                                                      a) -> a -> list b -> m a :=
  fix foldrM arg_6__ arg_7__ arg_8__
        := match arg_6__ , arg_7__ , arg_8__ with
             | _ , z , nil => GHC.Base.return_ z
             | k , z , cons x xs => foldrM k z xs GHC.Base.>>= (fun r => k x r)
           end.

Definition mapAccumLM {m} {acc} {x} {y} `{GHC.Base.Monad m} : (acc -> x -> m
                                                              (acc * y)%type) -> acc -> list x -> m (acc * list
                                                                                                    y)%type :=
  fix mapAccumLM arg_43__ arg_44__ arg_45__
        := match arg_43__ , arg_44__ , arg_45__ with
             | _ , s , nil => GHC.Base.return_ (pair s nil)
             | f , s , cons x xs => let cont_47__ arg_48__ :=
                                      match arg_48__ with
                                        | pair s1 x' => let cont_49__ arg_50__ :=
                                                          match arg_50__ with
                                                            | pair s2 xs' => GHC.Base.return_ (pair s2 (cons x' xs'))
                                                          end in
                                                        mapAccumLM f s1 xs GHC.Base.>>= cont_49__
                                      end in
                                    f s x GHC.Base.>>= cont_47__
           end.

Definition mapAndUnzip3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> m (b *
                                                                           c * d)%type) -> list a -> m (list b * list c
                                                                                                       * list d)%type :=
  fix mapAndUnzip3M arg_71__ arg_72__
        := match arg_71__ , arg_72__ with
             | _ , nil => GHC.Base.return_ (pair (pair nil nil) nil)
             | f , cons x xs => let cont_74__ arg_75__ :=
                                  match arg_75__ with
                                    | pair (pair r1 r2) r3 => let cont_76__ arg_77__ :=
                                                                match arg_77__ with
                                                                  | pair (pair rs1 rs2) rs3 => GHC.Base.return_ (pair
                                                                                                                (pair
                                                                                                                (cons r1
                                                                                                                      rs1)
                                                                                                                (cons r2
                                                                                                                      rs2))
                                                                                                                (cons r3
                                                                                                                      rs3))
                                                                end in
                                                              mapAndUnzip3M f xs GHC.Base.>>= cont_76__
                                  end in
                                f x GHC.Base.>>= cont_74__
           end.

Definition mapAndUnzip4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m} : (a -> m
                                                                       (b * c * d * e)%type) -> list a -> m (list b *
                                                                                                            list c *
                                                                                                            list d *
                                                                                                            list
                                                                                                            e)%type :=
  fix mapAndUnzip4M arg_62__ arg_63__
        := match arg_62__ , arg_63__ with
             | _ , nil => GHC.Base.return_ (pair (pair (pair nil nil) nil) nil)
             | f , cons x xs => let cont_65__ arg_66__ :=
                                  match arg_66__ with
                                    | pair (pair (pair r1 r2) r3) r4 => let cont_67__ arg_68__ :=
                                                                          match arg_68__ with
                                                                            | pair (pair (pair rs1 rs2) rs3) rs4 =>
                                                                              GHC.Base.return_ (pair (pair (pair (cons
                                                                                                                 r1 rs1)
                                                                                                                 (cons
                                                                                                                 r2
                                                                                                                 rs2))
                                                                                                           (cons r3
                                                                                                                 rs3))
                                                                                                     (cons r4 rs4))
                                                                          end in
                                                                        mapAndUnzip4M f xs GHC.Base.>>= cont_67__
                                  end in
                                f x GHC.Base.>>= cont_65__
           end.

Definition mapAndUnzip5M {m} {a} {b} {c} {d} {e} {f} `{GHC.Base.Monad m}
    : (a -> m (b * c * d * e * f)%type) -> list a -> m (list b * list c * list d *
                                                       list e * list f)%type :=
  fix mapAndUnzip5M arg_53__ arg_54__
        := match arg_53__ , arg_54__ with
             | _ , nil => GHC.Base.return_ (pair (pair (pair (pair nil nil) nil) nil) nil)
             | f , cons x xs => let cont_56__ arg_57__ :=
                                  match arg_57__ with
                                    | pair (pair (pair (pair r1 r2) r3) r4) r5 => let cont_58__ arg_59__ :=
                                                                                    match arg_59__ with
                                                                                      | pair (pair (pair (pair rs1 rs2)
                                                                                                         rs3) rs4)
                                                                                             rs5 => GHC.Base.return_
                                                                                                    (pair (pair (pair
                                                                                                                (pair
                                                                                                                (cons r1
                                                                                                                      rs1)
                                                                                                                (cons r2
                                                                                                                      rs2))
                                                                                                                (cons r3
                                                                                                                      rs3))
                                                                                                                (cons r4
                                                                                                                      rs4))
                                                                                                          (cons r5 rs5))
                                                                                    end in
                                                                                  mapAndUnzip5M f xs GHC.Base.>>=
                                                                                  cont_58__
                                  end in
                                f x GHC.Base.>>= cont_56__
           end.

Definition mapMaybeM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> m (option
                                                                 b)) -> list a -> m (list b) :=
  fun f => GHC.Base.liftM Data.Maybe.catMaybes GHC.Base.∘ Data.Traversable.mapM f.

Definition mapSndM {m} {b} {c} {a} `{GHC.Base.Monad m} : (b -> m c) -> list (a *
                                                                            b)%type -> m (list (a * c)%type) :=
  fix mapSndM arg_38__ arg_39__
        := match arg_38__ , arg_39__ with
             | _ , nil => GHC.Base.return_ nil
             | f , cons (pair a b) xs => f b GHC.Base.>>= (fun c =>
                                           mapSndM f xs GHC.Base.>>= (fun rs => GHC.Base.return_ (cons (pair a c) rs)))
           end.

Definition maybeMapM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> (option
                                                       a -> m (option b)) :=
  fun arg_1__ arg_2__ =>
    match arg_1__ , arg_2__ with
      | _ , None => GHC.Base.return_ None
      | m , Some x => GHC.Base.liftM Some GHC.Base.$ m x
    end.

Definition orM {m} `{GHC.Base.Monad m} : m bool -> m bool -> m bool :=
  fun m1 m2 =>
    m1 GHC.Base.>>= (fun x => if x : bool then GHC.Base.return_ true else m2).

Definition whenM {m} `{GHC.Base.Monad m} : m bool -> m unit -> m unit :=
  fun mb thing => mb GHC.Base.>>= (fun b => GHC.Base.when b thing).

Definition zipWith3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> b -> c -> m
                                                               d) -> list a -> list b -> list c -> m (list d) :=
  fix zipWith3M arg_101__ arg_102__ arg_103__ arg_104__
        := match arg_101__ , arg_102__ , arg_103__ , arg_104__ with
             | _ , nil , _ , _ => GHC.Base.return_ nil
             | _ , _ , nil , _ => GHC.Base.return_ nil
             | _ , _ , _ , nil => GHC.Base.return_ nil
             | f , cons x xs , cons y ys , cons z zs => f x y z GHC.Base.>>= (fun r =>
                                                          zipWith3M f xs ys zs GHC.Base.>>= (fun rs =>
                                                            GHC.Base.return_ GHC.Base.$ cons r rs))
           end.

Definition zipWith3M_ {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
    : (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit :=
  fun f as_ bs cs =>
    zipWith3M f as_ bs cs GHC.Base.>>= (fun _ => GHC.Base.return_ tt).

Definition zipWith4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m}
    : (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list
                                                                             e) :=
  fix zipWith4M arg_90__ arg_91__ arg_92__ arg_93__ arg_94__
        := match arg_90__ , arg_91__ , arg_92__ , arg_93__ , arg_94__ with
             | _ , nil , _ , _ , _ => GHC.Base.return_ nil
             | _ , _ , nil , _ , _ => GHC.Base.return_ nil
             | _ , _ , _ , nil , _ => GHC.Base.return_ nil
             | _ , _ , _ , _ , nil => GHC.Base.return_ nil
             | f , cons x xs , cons y ys , cons z zs , cons a as_ => f x y z a GHC.Base.>>=
                                                                     (fun r =>
                                                                       zipWith4M f xs ys zs as_ GHC.Base.>>= (fun rs =>
                                                                         GHC.Base.return_ GHC.Base.$ cons r rs))
           end.

Definition zipWithAndUnzipM {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
    : (a -> b -> m (c * d)%type) -> list a -> list b -> m (list c * list d)%type :=
  fix zipWithAndUnzipM arg_80__ arg_81__ arg_82__
        := match arg_80__ , arg_81__ , arg_82__ with
             | f , cons x xs , cons y ys => let cont_83__ arg_84__ :=
                                              match arg_84__ with
                                                | pair c d => let cont_85__ arg_86__ :=
                                                                match arg_86__ with
                                                                  | pair cs ds => GHC.Base.return_ (pair (cons c cs)
                                                                                                         (cons d ds))
                                                                end in
                                                              zipWithAndUnzipM f xs ys GHC.Base.>>= cont_85__
                                              end in
                                            f x y GHC.Base.>>= cont_83__
             | _ , _ , _ => GHC.Base.return_ (pair nil nil)
           end.

(* Unbound variables:
     Some bool cons false list nil op_zt__ option pair true tt unit
     Control.Monad.foldM Control.Monad.foldM_ Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Foldable.concat Data.Maybe.catMaybes
     Data.Traversable.mapM GHC.Base.Monad GHC.Base.liftM GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Base.when
*)
