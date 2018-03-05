Definition default_elem {t : Type -> Type} {a} `{GHC.Base.Eq_ a} (foldMap : (a -> Any) -> t a -> Any) :
  a -> t a -> bool :=
   fun x xs => getAny (foldMap (fun y => Mk_Any (GHC.Base.op_zeze__ x y)) xs).

Definition default_foldable {f:Type -> Type}
  (foldMap : forall m a, forall (M : GHC.Base.Monoid m), (a -> m) -> f a -> m)
  (foldr : forall a b, (a -> b -> b) -> b -> f a -> b):=
  let foldl : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun b a =>
         fun f  z t => Data.Monoid.appEndo
                    (Data.Monoid.getDual
                       (foldMap _ _ _ (Coq.Program.Basics.compose
                                   Data.Monoid.Mk_Dual
                                   (Coq.Program.Basics.compose
                                      Data.Monoid.Mk_Endo
                                      (GHC.Base.flip f))) t)) z)
  in
  let foldl' : forall b a, (b -> a -> b) -> b -> f a -> b :=
      (fun {b} {a} =>
         fun f  z0  xs =>
           let f' :=  fun  x  k  z => GHC.Base.op_zdzn__ k (f z x)
           in foldr _ _ f' GHC.Base.id xs z0)
  in
  Foldable__Dict_Build
    f
    (fun {a} `{GHC.Base.Eq_ a} =>
       Coq.Program.Basics.compose
         (fun p => Coq.Program.Basics.compose
                  Data.Monoid.getAny
                  (foldMap _ _ _ (fun x => Data.Monoid.Mk_Any (p x))))
         GHC.Base.op_zeze__ )
    (* fold *)
    (fun m (M : GHC.Base.Monoid m) => foldMap _ _ _ GHC.Base.id)
    (* foldMap *)
    (@foldMap)
    (* foldl *)
    (@foldl)
    (* foldl' *)
    (@foldl')
    (* foldr  *)
    (@foldr)
    (* foldr' *)
    (fun a b f z0 xs =>
       let f' := fun k  x  z => GHC.Base.op_zdzn__ k (f x z)
       in
       @foldl _ _ f' GHC.Base.id xs z0)
    (* length *)
    (fun a => @foldl' _ a (fun c  _ => GHC.Num.op_zp__ c (GHC.Num.fromInteger 1))
                    (GHC.Num.fromInteger 0))
    (* null *)
    (fun a => @foldr _ _ (fun arg_61__ arg_62__ => false) true)
    (* product *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Monoid.getProduct
                                  (foldMap _ _ _ Data.Monoid.Mk_Product))
    (* sum *)
    (fun a `{GHC.Num.Num a} =>
       Coq.Program.Basics.compose Data.Monoid.getSum
                                  (foldMap _ _ _ Data.Monoid.Mk_Sum))
    (* toList *)
    (fun a => fun t => GHC.Base.build (fun _ c n => @foldr _ _ c n t)).

Definition default_foldable_foldMap {f : Type -> Type}
  (foldMap : forall {m} {a}, forall `{GHC.Base.Monoid m}, (a -> m) -> f a -> m)
 :=
  let foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b :=
  fun a b f z t =>
    Data.Monoid.appEndo
      (foldMap
         (Coq.Program.Basics.compose Data.Monoid.Mk_Endo f) t) z
  in
  default_foldable (fun {m}{a} `{GHC.Base.Monoid m} => foldMap) foldr.

Definition default_foldable_foldr (f : Type -> Type)
  (foldr : forall {a} {b}, (a -> b -> b) -> b -> f a -> b) :=
  let foldMap :  forall {m} {a} `{GHC.Base.Monoid m}, (a -> m) -> f a -> m :=
  fun m a (H : GHC.Base.Monoid m) =>
    fun f => foldr
            (Coq.Program.Basics.compose GHC.Base.mappend
                                        f) GHC.Base.mempty
  in
  default_foldable foldMap (fun {a} {b} => foldr).
