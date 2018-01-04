(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UniqSupply : Type := MkSplitUniqSupply
                              : GHC.Num.Int -> UniqSupply -> UniqSupply -> UniqSupply.

Inductive UniqSM result : Type := USM : (UniqSupply -> (result *
                                        UniqSupply)%type) -> UniqSM result.

Record MonadUnique__Dict m := MonadUnique__Dict_Build {
  getUniqueM__ : m Unique.Unique ;
  getUniqueSupplyM__ : m UniqSupply ;
  getUniquesM__ : m (list Unique.Unique) }.

Definition MonadUnique m `{GHC.Base.Monad m} :=
  forall r, (MonadUnique__Dict m -> r) -> r.

Existing Class MonadUnique.

Definition getUniqueM `{g : MonadUnique m} : m Unique.Unique :=
  g _ (getUniqueM__ m).

Definition getUniqueSupplyM `{g : MonadUnique m} : m UniqSupply :=
  g _ (getUniqueSupplyM__ m).

Definition getUniquesM `{g : MonadUnique m} : m (list Unique.Unique) :=
  g _ (getUniquesM__ m).

Arguments USM {_} _.

Definition unUSM {result} (arg_0__ : UniqSM result) :=
  match arg_0__ with
    | USM unUSM => unUSM
  end.
(* Converted value declarations: *)

Local Definition Functor__UniqSM_fmap : forall {a} {b},
                                          (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | f , USM x => USM (fun us =>
                             match x us with
                               | pair r us' => pair (f r) us'
                             end)
      end.

Local Definition Functor__UniqSM_op_zlzd__ : forall {a} {b},
                                               a -> UniqSM b -> UniqSM a :=
  fun {a} {b} => fun x => Functor__UniqSM_fmap (GHC.Base.const x).

Program Instance Functor__UniqSM : GHC.Base.Functor UniqSM := fun _ k =>
    k {|GHC.Base.op_zlzd____ := fun {a} {b} => Functor__UniqSM_op_zlzd__ ;
      GHC.Base.fmap__ := fun {a} {b} => Functor__UniqSM_fmap |}.

Local Definition Applicative__UniqSM_op_zlztzg__ : forall {a} {b},
                                                     UniqSM (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a} {b} =>
    fun arg_0__ arg_1__ =>
      match arg_0__ , arg_1__ with
        | USM f , USM x => USM GHC.Base.$ (fun us =>
                             match f us with
                               | pair ff us' => match x us' with
                                                  | pair xx us'' => pair (ff xx) us''
                                                end
                             end)
      end.

(* Translating `instance Control.Monad.Fix.MonadFix UniqSupply.UniqSM' failed:
   OOPS! Cannot find information for class Qualified "Control.Monad.Fix" "MonadFix"
   unsupported *)

Definition getUniqueSupplyM3 {m} `{MonadUnique m} : m (UniqSupply * UniqSupply *
                                                      UniqSupply)%type :=
  GHC.Base.liftM3 GHC.Tuple.pair3 getUniqueSupplyM getUniqueSupplyM
  getUniqueSupplyM.

Definition initUs {a} : UniqSupply -> UniqSM a -> (a * UniqSupply)%type :=
  fun init_us m => match unUSM m init_us with | pair r us => pair r us end.

Definition initUs_ {a} : UniqSupply -> UniqSM a -> a :=
  fun init_us m => match unUSM m init_us with | pair r _ => r end.

Definition liftUs {m} {a} `{MonadUnique m} : UniqSM a -> m a :=
  fun m =>
    getUniqueSupplyM GHC.Base.>>= (GHC.Base.return_ GHC.Base.∘ GHC.Base.flip initUs_
    m).

Definition liftUSM {a} : UniqSM a -> UniqSupply -> (a * UniqSupply)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | USM m , us => match m us with
                        | pair a us' => pair a us'
                      end
    end.

Definition lazyThenUs {a} {b} : UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun expr cont =>
    USM (fun us =>
          match liftUSM expr us with
            | pair result us' => unUSM (cont result) us'
          end).

Definition listSplitUniqSupply : UniqSupply -> list UniqSupply :=
  fix listSplitUniqSupply arg_0__
        := match arg_0__ with
             | MkSplitUniqSupply _ s1 s2 => cons s1 (listSplitUniqSupply s2)
           end.

Definition returnUs {a} : a -> UniqSM a :=
  fun result => USM (fun us => pair result us).

Definition lazyMapUs {a} {b} : (a -> UniqSM b) -> list a -> UniqSM (list b) :=
  fix lazyMapUs arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | _ , nil => returnUs nil
             | f , cons x xs => lazyThenUs (f x) (fun r =>
                                             lazyThenUs (lazyMapUs f xs) (fun rs => returnUs (cons r rs)))
           end.

Local Definition Applicative__UniqSM_pure : forall {a}, a -> UniqSM a :=
  fun {a} => returnUs.

Definition splitUniqSupply : UniqSupply -> (UniqSupply * UniqSupply)%type :=
  fun arg_0__ => match arg_0__ with | MkSplitUniqSupply _ s1 s2 => pair s1 s2 end.

Definition splitUniqSupply3 : UniqSupply -> (UniqSupply * UniqSupply *
                              UniqSupply)%type :=
  fun us =>
    match splitUniqSupply us with
      | pair us1 us' => match splitUniqSupply us' with
                          | pair us2 us3 => pair (pair us1 us2) us3
                        end
    end.

Definition splitUniqSupply4 : UniqSupply -> (UniqSupply * UniqSupply *
                              UniqSupply * UniqSupply)%type :=
  fun us =>
    match splitUniqSupply3 us with
      | pair (pair us1 us2) us' => match splitUniqSupply us' with
                                     | pair us3 us4 => pair (pair (pair us1 us2) us3) us4
                                   end
    end.

Definition getUs : UniqSM UniqSupply :=
  USM (fun us =>
        match splitUniqSupply us with
          | pair us1 us2 => pair us1 us2
        end).

Local Definition MonadUnique__UniqSM_getUniqueSupplyM : UniqSM UniqSupply :=
  getUs.

Definition takeUniqFromSupply : UniqSupply -> (Unique.Unique *
                                UniqSupply)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | MkSplitUniqSupply n s1 _ => pair (Unique.mkUniqueGrimily n) s1
    end.

Definition getUniqueUs : UniqSM Unique.Unique :=
  USM (fun us => match takeUniqFromSupply us with | pair u us' => pair u us' end).

Local Definition MonadUnique__UniqSM_getUniqueM : UniqSM Unique.Unique :=
  getUniqueUs.

Definition thenUs {a} {b} : UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | USM expr , cont => USM (fun us =>
                                 match (expr us) with
                                   | pair result us' => unUSM (cont result) us'
                                 end)
    end.

Local Definition Monad__UniqSM_op_zgzgze__ : forall {a} {b},
                                               UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun {a} {b} => thenUs.

Definition thenUs_ {a} {b} : UniqSM a -> UniqSM b -> UniqSM b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | USM expr , USM cont => USM (fun us =>
                                     match (expr us) with
                                       | pair _ us' => cont us'
                                     end)
    end.

Local Definition Applicative__UniqSM_op_ztzg__ : forall {a} {b},
                                                   UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a} {b} => thenUs_.

Program Instance Applicative__UniqSM : GHC.Base.Applicative UniqSM := fun _ k =>
    k {|GHC.Base.op_ztzg____ := fun {a} {b} => Applicative__UniqSM_op_ztzg__ ;
      GHC.Base.op_zlztzg____ := fun {a} {b} => Applicative__UniqSM_op_zlztzg__ ;
      GHC.Base.pure__ := fun {a} => Applicative__UniqSM_pure |}.

Local Definition Monad__UniqSM_return_ : forall {a}, a -> UniqSM a :=
  fun {a} => GHC.Base.pure.

Local Definition Monad__UniqSM_op_zgzg__ : forall {a} {b},
                                             UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a} {b} => _GHC.Base.*>_.

Program Instance Monad__UniqSM : GHC.Base.Monad UniqSM := fun _ k =>
    k {|GHC.Base.op_zgzg____ := fun {a} {b} => Monad__UniqSM_op_zgzg__ ;
      GHC.Base.op_zgzgze____ := fun {a} {b} => Monad__UniqSM_op_zgzgze__ ;
      GHC.Base.return___ := fun {a} => Monad__UniqSM_return_ |}.

Definition uniqFromSupply : UniqSupply -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
      | MkSplitUniqSupply n _ _ => Unique.mkUniqueGrimily n
    end.

Definition uniqsFromSupply : UniqSupply -> list Unique.Unique :=
  fix uniqsFromSupply arg_0__
        := match arg_0__ with
             | MkSplitUniqSupply n _ s2 => cons (Unique.mkUniqueGrimily n) (uniqsFromSupply
                                                s2)
           end.

Definition getUniquesUs : UniqSM (list Unique.Unique) :=
  USM (fun us =>
        match splitUniqSupply us with
          | pair us1 us2 => pair (uniqsFromSupply us1) us2
        end).

Local Definition MonadUnique__UniqSM_getUniquesM : UniqSM (list
                                                          Unique.Unique) :=
  getUniquesUs.

Program Instance MonadUnique__UniqSM : MonadUnique UniqSM := fun _ k =>
    k {|getUniqueM__ := MonadUnique__UniqSM_getUniqueM ;
      getUniqueSupplyM__ := MonadUnique__UniqSM_getUniqueSupplyM ;
      getUniquesM__ := MonadUnique__UniqSM_getUniquesM |}.

(* Unbound variables:
     cons list nil op_zt__ pair GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.const GHC.Base.flip GHC.Base.liftM3 GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zgzgze__ GHC.Base.op_ztzg__ GHC.Base.pure
     GHC.Base.return_ GHC.Num.Int GHC.Tuple.pair3 Unique.Unique
     Unique.mkUniqueGrimily
*)
