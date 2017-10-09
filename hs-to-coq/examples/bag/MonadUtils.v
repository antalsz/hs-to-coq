(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
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
  fix zipWith3M arg_62__ arg_63__ arg_64__ arg_65__
        := match arg_62__ , arg_63__ , arg_64__ , arg_65__ with
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
  fun arg_71__ arg_72__ arg_73__ arg_74__ =>
    match arg_71__ , arg_72__ , arg_73__ , arg_74__ with
      | f , as_ , bs , cs => GHC.Base.op_zgzgze__ (zipWith3M f as_ bs cs) (fun _ =>
                                                    GHC.Base.return_ tt)
    end.

Definition zipWith4M {m} {a} {b} {c} {d} {e} `{GHC.Base.Monad m}
    : (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list
                                                                             e) :=
  fix zipWith4M arg_51__ arg_52__ arg_53__ arg_54__ arg_55__
        := match arg_51__ , arg_52__ , arg_53__ , arg_54__ , arg_55__ with
             | _ , nil , _ , _ , _ => GHC.Base.return_ nil
             | _ , _ , nil , _ , _ => GHC.Base.return_ nil
             | _ , _ , _ , nil , _ => GHC.Base.return_ nil
             | _ , _ , _ , _ , nil => GHC.Base.return_ nil
             | f , (cons x xs) , (cons y ys) , (cons z zs) , (cons a as_) =>
               GHC.Base.op_zgzgze__ (f x y z a) (fun r =>
                                      GHC.Base.op_zgzgze__ (zipWith4M f xs ys zs as_) (fun rs =>
                                                             GHC.Base.op_zd__ GHC.Base.return_ (cons r rs)))
           end.

(* Unbound variables:
     * Control.Monad.foldM Control.Monad.foldM_ Coq.Program.Basics.compose
     GHC.Base.Monad GHC.Base.liftM GHC.Base.op_zd__ GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.Base.when Some bool cons false inl inr list option pair sum
     true tt unit
*)
