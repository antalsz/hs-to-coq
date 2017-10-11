(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

Require Control.Monad.
Require Coq.Program.Basics.
Require GHC.Base.

(* Converted declarations: *)

Definition allM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> list a -> m
                                              bool :=
  fix allM arg_22__ arg_23__
        := match arg_22__ , arg_23__ with
             | _ , nil => GHC.Base.return_ true
             | f , (cons b bs) => GHC.Base.op_zgzgze__ (f b) (fun arg_25__ =>
                                                         match arg_25__ with
                                                           | bv => if bv : bool
                                                                   then allM f bs
                                                                   else GHC.Base.return_ false
                                                         end)
           end.

Definition anyM {m} {a} `{GHC.Base.Monad m} : (a -> m bool) -> list a -> m
                                              bool :=
  fix anyM arg_30__ arg_31__
        := match arg_30__ , arg_31__ with
             | _ , nil => GHC.Base.return_ false
             | f , (cons x xs) => GHC.Base.op_zgzgze__ (f x) (fun b =>
                                                         if b : bool
                                                         then GHC.Base.return_ true
                                                         else anyM f xs)
           end.

Definition fmapEitherM {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> m
                                                                 b) -> (c -> m d) -> sum a c -> m (sum b d) :=
  fun arg_35__ arg_36__ arg_37__ =>
    match arg_35__ , arg_36__ , arg_37__ with
      | fl , _ , (inl a) => GHC.Base.op_zgzgze__ (fl a) (Coq.Program.Basics.compose
                                                 GHC.Base.return_ inl)
      | _ , fr , (inr b) => GHC.Base.op_zgzgze__ (fr b) (Coq.Program.Basics.compose
                                                 GHC.Base.return_ inr)
    end.

Definition fmapMaybeM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> m b) -> option
                                                          a -> m (option b) :=
  fun arg_41__ arg_42__ =>
    match arg_41__ , arg_42__ with
      | _ , None => GHC.Base.return_ None
      | f , (Some x) => GHC.Base.op_zgzgze__ (f x) (Coq.Program.Basics.compose
                                             GHC.Base.return_ Some)
    end.

Definition foldlM {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                      a) -> a -> list b -> m a :=
  Control.Monad.foldM.

Definition foldlM_ {m} {a} {b} `{(GHC.Base.Monad m)} : (a -> b -> m
                                                       a) -> a -> list b -> m unit :=
  Control.Monad.foldM_.

Definition foldrM {m} {b} {a} `{(GHC.Base.Monad m)} : (b -> a -> m
                                                      a) -> a -> list b -> m a :=
  fix foldrM arg_9__ arg_10__ arg_11__
        := match arg_9__ , arg_10__ , arg_11__ with
             | _ , z , nil => GHC.Base.return_ z
             | k , z , (cons x xs) => GHC.Base.op_zgzgze__ (foldrM k z xs) (fun r => k x r)
           end.

Definition mapAccumLM {m} {acc} {x} {y} `{GHC.Base.Monad m} : (acc -> x -> m
                                                              (acc * y)) -> acc -> list x -> m (acc * list y) :=
  fix mapAccumLM arg_51__ arg_52__ arg_53__
        := match arg_51__ , arg_52__ , arg_53__ with
             | _ , s , nil => GHC.Base.return_ (pair s nil)
             | f , s , (cons x xs) => let cont_55__ arg_56__ :=
                                        match arg_56__ with
                                          | (pair s1 x') => let cont_57__ arg_58__ :=
                                                              match arg_58__ with
                                                                | (pair s2 xs') => GHC.Base.return_ (pair s2 (cons x'
                                                                                                                   xs'))
                                                              end in
                                                            GHC.Base.op_zgzgze__ (mapAccumLM f s1 xs) cont_57__
                                        end in
                                      GHC.Base.op_zgzgze__ (f s x) cont_55__
           end.

Definition mapAndUnzip3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> m (b *
                                                                           c * d)) -> list a -> m (list b * list c *
                                                                                                  list d) :=
  fix mapAndUnzip3M arg_79__ arg_80__
        := match arg_79__ , arg_80__ with
             | _ , nil => GHC.Base.return_ (pair (pair nil nil) nil)
             | f , (cons x xs) => let cont_82__ arg_83__ :=
                                    match arg_83__ with
                                      | (pair (pair r1 r2) r3) => let cont_84__ arg_85__ :=
                                                                    match arg_85__ with
                                                                      | (pair (pair rs1 rs2) rs3) => GHC.Base.return_
                                                                                                     (pair (pair (cons
                                                                                                                 r1 rs1)
                                                                                                                 (cons
                                                                                                                 r2
                                                                                                                 rs2))
                                                                                                           (cons r3
                                                                                                                 rs3))
                                                                    end in
                                                                  GHC.Base.op_zgzgze__ (mapAndUnzip3M f xs) cont_84__
                                    end in
                                  GHC.Base.op_zgzgze__ (f x) cont_82__
           end.

Definition mapAndUnzip4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m} : (a -> m
                                                                       (b * c * d * e)) -> list a -> m (list b * list c
                                                                                                       * list d * list
                                                                                                       e) :=
  fix mapAndUnzip4M arg_70__ arg_71__
        := match arg_70__ , arg_71__ with
             | _ , nil => GHC.Base.return_ (pair (pair (pair nil nil) nil) nil)
             | f , (cons x xs) => let cont_73__ arg_74__ :=
                                    match arg_74__ with
                                      | (pair (pair (pair r1 r2) r3) r4) => let cont_75__ arg_76__ :=
                                                                              match arg_76__ with
                                                                                | (pair (pair (pair rs1 rs2) rs3)
                                                                                        rs4) => GHC.Base.return_ (pair
                                                                                                                 (pair
                                                                                                                 (pair
                                                                                                                 (cons
                                                                                                                 r1 rs1)
                                                                                                                 (cons
                                                                                                                 r2
                                                                                                                 rs2))
                                                                                                                 (cons
                                                                                                                 r3
                                                                                                                 rs3))
                                                                                                                 (cons
                                                                                                                 r4
                                                                                                                 rs4))
                                                                              end in
                                                                            GHC.Base.op_zgzgze__ (mapAndUnzip4M f xs)
                                                                                                 cont_75__
                                    end in
                                  GHC.Base.op_zgzgze__ (f x) cont_73__
           end.

Definition mapAndUnzip5M {m} {a} {b} {c} {d} {e} {f} `{GHC.Base.Monad m}
    : (a -> m (b * c * d * e * f)) -> list a -> m (list b * list c * list d * list e
                                                  * list f) :=
  fix mapAndUnzip5M arg_61__ arg_62__
        := match arg_61__ , arg_62__ with
             | _ , nil => GHC.Base.return_ (pair (pair (pair (pair nil nil) nil) nil) nil)
             | f , (cons x xs) => let cont_64__ arg_65__ :=
                                    match arg_65__ with
                                      | (pair (pair (pair (pair r1 r2) r3) r4) r5) => let cont_66__ arg_67__ :=
                                                                                        match arg_67__ with
                                                                                          | (pair (pair (pair (pair rs1
                                                                                                                    rs2)
                                                                                                              rs3) rs4)
                                                                                                  rs5) =>
                                                                                            GHC.Base.return_ (pair (pair
                                                                                                                   (pair
                                                                                                                   (pair
                                                                                                                   (cons
                                                                                                                   r1
                                                                                                                   rs1)
                                                                                                                   (cons
                                                                                                                   r2
                                                                                                                   rs2))
                                                                                                                   (cons
                                                                                                                   r3
                                                                                                                   rs3))
                                                                                                                   (cons
                                                                                                                   r4
                                                                                                                   rs4))
                                                                                                                   (cons
                                                                                                                   r5
                                                                                                                   rs5))
                                                                                        end in
                                                                                      GHC.Base.op_zgzgze__
                                                                                      (mapAndUnzip5M f xs) cont_66__
                                    end in
                                  GHC.Base.op_zgzgze__ (f x) cont_64__
           end.

Definition mapSndM {m} {b} {c} {a} `{GHC.Base.Monad m} : (b -> m c) -> list (a *
                                                                            b) -> m (list (a * c)) :=
  fix mapSndM arg_46__ arg_47__
        := match arg_46__ , arg_47__ with
             | _ , nil => GHC.Base.return_ nil
             | f , (cons (pair a b) xs) => GHC.Base.op_zgzgze__ (f b) (fun c =>
                                                                  GHC.Base.op_zgzgze__ (mapSndM f xs) (fun rs =>
                                                                                         GHC.Base.return_ (cons (pair a
                                                                                                                      c)
                                                                                                                rs)))
           end.

Definition maybeMapM {m} {a} {b} `{GHC.Base.Monad m} : (a -> m b) -> (option
                                                       a -> m (option b)) :=
  fun arg_4__ arg_5__ =>
    match arg_4__ , arg_5__ with
      | _ , None => GHC.Base.return_ None
      | m , (Some x) => GHC.Base.op_zd__ (GHC.Base.liftM Some) (m x)
    end.

Definition orM {m} `{GHC.Base.Monad m} : m bool -> m bool -> m bool :=
  fun arg_15__ arg_16__ =>
    match arg_15__ , arg_16__ with
      | m1 , m2 => GHC.Base.op_zgzgze__ m1 (fun arg_17__ =>
                                          match arg_17__ with
                                            | x => if x : bool
                                                   then GHC.Base.return_ true
                                                   else m2
                                          end)
    end.

Definition whenM {m} `{GHC.Base.Monad m} : m bool -> m unit -> m unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | mb , thing => GHC.Base.op_zgzgze__ mb (fun b => GHC.Base.when b thing)
    end.

Definition zipWith3M {m} {a} {b} {c} {d} `{GHC.Base.Monad m} : (a -> b -> c -> m
                                                               d) -> list a -> list b -> list c -> m (list d) :=
  fix zipWith3M arg_109__ arg_110__ arg_111__ arg_112__
        := match arg_109__ , arg_110__ , arg_111__ , arg_112__ with
             | _ , nil , _ , _ => GHC.Base.return_ nil
             | _ , _ , nil , _ => GHC.Base.return_ nil
             | _ , _ , _ , nil => GHC.Base.return_ nil
             | f , (cons x xs) , (cons y ys) , (cons z zs) => GHC.Base.op_zgzgze__ (f x y z)
                                                                                   (fun r =>
                                                                                     GHC.Base.op_zgzgze__ (zipWith3M f
                                                                                                          xs ys zs)
                                                                                                          (fun rs =>
                                                                                                            GHC.Base.op_zd__
                                                                                                            GHC.Base.return_
                                                                                                            (cons r
                                                                                                                  rs)))
           end.

Definition zipWith3M_ {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
    : (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit :=
  fun arg_118__ arg_119__ arg_120__ arg_121__ =>
    match arg_118__ , arg_119__ , arg_120__ , arg_121__ with
      | f , as_ , bs , cs => GHC.Base.op_zgzgze__ (zipWith3M f as_ bs cs) (fun _ =>
                                                    GHC.Base.return_ tt)
    end.

Definition zipWith4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m}
    : (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list
                                                                             e) :=
  fix zipWith4M arg_98__ arg_99__ arg_100__ arg_101__ arg_102__
        := match arg_98__ , arg_99__ , arg_100__ , arg_101__ , arg_102__ with
             | _ , nil , _ , _ , _ => GHC.Base.return_ nil
             | _ , _ , nil , _ , _ => GHC.Base.return_ nil
             | _ , _ , _ , nil , _ => GHC.Base.return_ nil
             | _ , _ , _ , _ , nil => GHC.Base.return_ nil
             | f , (cons x xs) , (cons y ys) , (cons z zs) , (cons a as_) =>
               GHC.Base.op_zgzgze__ (f x y z a) (fun r =>
                                      GHC.Base.op_zgzgze__ (zipWith4M f xs ys zs as_) (fun rs =>
                                                             GHC.Base.op_zd__ GHC.Base.return_ (cons r rs)))
           end.

Definition zipWithAndUnzipM {m} {a} {b} {c} {d} `{GHC.Base.Monad m}
    : (a -> b -> m (c * d)) -> list a -> list b -> m (list c * list d) :=
  fix zipWithAndUnzipM arg_88__ arg_89__ arg_90__
        := match arg_88__ , arg_89__ , arg_90__ with
             | f , (cons x xs) , (cons y ys) => let cont_91__ arg_92__ :=
                                                  match arg_92__ with
                                                    | (pair c d) => let cont_93__ arg_94__ :=
                                                                      match arg_94__ with
                                                                        | (pair cs ds) => GHC.Base.return_ (pair (cons c
                                                                                                                       cs)
                                                                                                                 (cons d
                                                                                                                       ds))
                                                                      end in
                                                                    GHC.Base.op_zgzgze__ (zipWithAndUnzipM f xs ys)
                                                                                         cont_93__
                                                  end in
                                                GHC.Base.op_zgzgze__ (f x y) cont_91__
             | _ , _ , _ => GHC.Base.return_ (pair nil nil)
           end.

(* Unbound variables:
     * Control.Monad.foldM Control.Monad.foldM_ Coq.Program.Basics.compose
     GHC.Base.Monad GHC.Base.liftM GHC.Base.op_zd__ GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.Base.when Some bool cons false inl inr list nil option pair
     sum true tt unit
*)
