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

Require Coq.Program.Basics.
Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Require Unique.

(* Converted declarations: *)

(* Translating `instance Control.Monad.Fix.MonadFix UniqSM' failed: OOPS! Cannot
   find information for class "Control.Monad.Fix.MonadFix" unsupported *)

Inductive UniqSupply : Type := Mk_MkSplitUniqSupply
                              : GHC.Num.Int -> UniqSupply -> UniqSupply -> UniqSupply.

Inductive UniqSM result : Type := Mk_USM : (UniqSupply -> result *
                                           UniqSupply) -> UniqSM result.

Arguments Mk_USM {_} _.

Definition unUSM {result} (arg_2__ : UniqSM result) :=
  match arg_2__ with
    | Mk_USM unUSM => unUSM
  end.

Definition thenUs_ {a} {b} : UniqSM a -> UniqSM b -> UniqSM b :=
  fun arg_10__ arg_11__ =>
    match arg_10__ , arg_11__ with
      | Mk_USM expr , Mk_USM cont => Mk_USM (fun arg_12__ =>
                                              match arg_12__ with
                                                | us => let scrut_13__ := (expr us) in
                                                        match scrut_13__ with
                                                          | pair _ us' => cont us'
                                                        end
                                              end)
    end.

Definition thenUs {a} {b} : UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun arg_20__ arg_21__ =>
    match arg_20__ , arg_21__ with
      | Mk_USM expr , cont => Mk_USM (fun arg_22__ =>
                                       match arg_22__ with
                                         | us => let scrut_23__ := (expr us) in
                                                 match scrut_23__ with
                                                   | pair result us' => unUSM (cont result) us'
                                                 end
                                       end)
    end.

Definition returnUs {a} : a -> UniqSM a :=
  fun arg_4__ =>
    match arg_4__ with
      | result => Mk_USM (fun arg_5__ =>
                           match arg_5__ with
                             | us => pair result us
                           end)
    end.

Local Definition instance_GHC_Base_Applicative_UniqSM_pure : forall {a},
                                                               a -> UniqSM a :=
  fun {a} => returnUs.

Local Definition instance_GHC_Base_Applicative_UniqSM_op_ztzg__ : forall {a}
                                                                         {b},
                                                                    UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a} {b} => thenUs_.

Local Definition instance_GHC_Base_Applicative_UniqSM_op_zlztzg__ : forall {a}
                                                                           {b},
                                                                      UniqSM (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a} {b} =>
    fun arg_118__ arg_119__ =>
      match arg_118__ , arg_119__ with
        | Mk_USM f , Mk_USM x => GHC.Base.op_zd__ Mk_USM (fun arg_120__ =>
                                                    match arg_120__ with
                                                      | us => let scrut_121__ := f us in
                                                              match scrut_121__ with
                                                                | pair ff us' => let scrut_122__ := x us' in
                                                                                 match scrut_122__ with
                                                                                   | pair xx us'' => pair (ff xx) us''
                                                                                 end
                                                              end
                                                    end)
      end.

Local Definition instance_GHC_Base_Functor_UniqSM_fmap : forall {a} {b},
                                                           (a -> b) -> UniqSM a -> UniqSM b :=
  fun {a} {b} =>
    fun arg_131__ arg_132__ =>
      match arg_131__ , arg_132__ with
        | f , Mk_USM x => Mk_USM (fun arg_133__ =>
                                   match arg_133__ with
                                     | us => let scrut_134__ := x us in
                                             match scrut_134__ with
                                               | pair r us' => pair (f r) us'
                                             end
                                   end)
      end.

Local Definition instance_GHC_Base_Functor_UniqSM_op_zlzd__ : forall {a} {b},
                                                                b -> UniqSM a -> UniqSM b :=
  fun {a} {b} =>
    fun x => instance_GHC_Base_Functor_UniqSM_fmap (GHC.Base.const x).

Instance instance_GHC_Base_Functor_UniqSM : GHC.Base.Functor UniqSM := {
  fmap := fun {a} {b} => instance_GHC_Base_Functor_UniqSM_fmap ;
  op_zlzd__ := fun {a} {b} => instance_GHC_Base_Functor_UniqSM_op_zlzd__ }.

Instance instance_GHC_Base_Applicative_UniqSM : GHC.Base.Applicative UniqSM := {
  op_zlztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_UniqSM_op_zlztzg__ ;
  op_ztzg__ := fun {a} {b} => instance_GHC_Base_Applicative_UniqSM_op_ztzg__ ;
  pure := fun {a} => instance_GHC_Base_Applicative_UniqSM_pure }.

Local Definition instance_GHC_Base_Monad_UniqSM_return_ : forall {a},
                                                            a -> UniqSM a :=
  fun {a} => GHC.Base.pure.

Local Definition instance_GHC_Base_Monad_UniqSM_op_zgzgze__ : forall {a} {b},
                                                                UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun {a} {b} => thenUs.

Local Definition instance_GHC_Base_Monad_UniqSM_op_zgzg__ : forall {a} {b},
                                                              UniqSM a -> UniqSM b -> UniqSM b :=
  fun {a} {b} => GHC.Base.op_ztzg__.

Instance instance_GHC_Base_Monad_UniqSM : GHC.Base.Monad UniqSM := {
  op_zgzg__ := fun {a} {b} => instance_GHC_Base_Monad_UniqSM_op_zgzg__ ;
  op_zgzgze__ := fun {a} {b} => instance_GHC_Base_Monad_UniqSM_op_zgzgze__ ;
  return_ := fun {a} => instance_GHC_Base_Monad_UniqSM_return_ }.

Class MonadUnique m `{GHC.Base.Monad m} := {
  getUniqueM : m Unique.Unique ;
  getUniqueSupplyM : m UniqSupply ;
  getUniquesM : m (list Unique.Unique) }.

Definition uniqsFromSupply : UniqSupply -> list Unique.Unique :=
  fix uniqsFromSupply arg_82__
        := match arg_82__ with
             | Mk_MkSplitUniqSupply n _ s2 => cons (Unique.mkUniqueGrimily n)
                                                   (uniqsFromSupply s2)
           end.

Definition uniqFromSupply : UniqSupply -> Unique.Unique :=
  fun arg_85__ =>
    match arg_85__ with
      | Mk_MkSplitUniqSupply n _ _ => Unique.mkUniqueGrimily n
    end.

Definition takeUniqFromSupply : UniqSupply -> Unique.Unique * UniqSupply :=
  fun arg_72__ =>
    match arg_72__ with
      | Mk_MkSplitUniqSupply n s1 _ => pair (Unique.mkUniqueGrimily n) s1
    end.

Definition getUniqueUs : UniqSM Unique.Unique :=
  Mk_USM (fun arg_75__ =>
           match arg_75__ with
             | us => let scrut_76__ := takeUniqFromSupply us in
                     match scrut_76__ with
                       | pair u us' => pair u us'
                     end
           end).

Local Definition instance_MonadUnique_UniqSM_getUniqueM : UniqSM
                                                          Unique.Unique :=
  getUniqueUs.

Definition splitUniqSupply : UniqSupply -> UniqSupply * UniqSupply :=
  fun arg_91__ =>
    match arg_91__ with
      | Mk_MkSplitUniqSupply _ s1 s2 => pair s1 s2
    end.

Definition getUniquesUs : UniqSM (list Unique.Unique) :=
  Mk_USM (fun arg_111__ =>
           match arg_111__ with
             | us => let scrut_112__ := splitUniqSupply us in
                     match scrut_112__ with
                       | pair us1 us2 => pair (uniqsFromSupply us1) us2
                     end
           end).

Local Definition instance_MonadUnique_UniqSM_getUniquesM : UniqSM (list
                                                                  Unique.Unique) :=
  getUniquesUs.

Definition splitUniqSupply3 : UniqSupply -> UniqSupply * UniqSupply *
                              UniqSupply :=
  fun arg_94__ =>
    match arg_94__ with
      | us => match splitUniqSupply us with
                | pair us1 us' => match splitUniqSupply us' with
                                    | pair us2 us3 => pair (pair us1 us2) us3
                                  end
              end
    end.

Definition splitUniqSupply4 : UniqSupply -> UniqSupply * UniqSupply * UniqSupply
                              * UniqSupply :=
  fun arg_99__ =>
    match arg_99__ with
      | us => match splitUniqSupply3 us with
                | pair (pair us1 us2) us' => match splitUniqSupply us' with
                                               | pair us3 us4 => pair (pair (pair us1 us2) us3) us4
                                             end
              end
    end.

Definition listSplitUniqSupply : UniqSupply -> list UniqSupply :=
  fix listSplitUniqSupply arg_88__
        := match arg_88__ with
             | Mk_MkSplitUniqSupply _ s1 s2 => cons s1 (listSplitUniqSupply s2)
           end.

Definition liftUSM {a} : UniqSM a -> UniqSupply -> a * UniqSupply :=
  fun arg_30__ arg_31__ =>
    match arg_30__ , arg_31__ with
      | Mk_USM m , us => let scrut_32__ := m us in
                         match scrut_32__ with
                           | pair a us' => pair a us'
                         end
    end.

Definition lazyThenUs {a} {b} : UniqSM a -> (a -> UniqSM b) -> UniqSM b :=
  fun arg_37__ arg_38__ =>
    match arg_37__ , arg_38__ with
      | expr , cont => Mk_USM (fun arg_39__ =>
                                match arg_39__ with
                                  | us => match liftUSM expr us with
                                            | pair result us' => unUSM (cont result) us'
                                          end
                                end)
    end.

Definition lazyMapUs {a} {b} : (a -> UniqSM b) -> list a -> UniqSM (list b) :=
  fix lazyMapUs arg_45__ arg_46__
        := match arg_45__ , arg_46__ with
             | _ , nil => returnUs nil
             | f , cons x xs => lazyThenUs (f x) (fun arg_48__ =>
                                             match arg_48__ with
                                               | r => lazyThenUs (lazyMapUs f xs) (fun arg_49__ =>
                                                                   match arg_49__ with
                                                                     | rs => returnUs (cons r rs)
                                                                   end)
                                             end)
           end.

Definition initUs_ {a} : UniqSupply -> UniqSM a -> a :=
  fun arg_56__ arg_57__ =>
    match arg_56__ , arg_57__ with
      | init_us , m => let scrut_58__ := unUSM m init_us in
                       match scrut_58__ with
                         | pair r _ => r
                       end
    end.

Definition liftUs {m} {a} `{MonadUnique m} : UniqSM a -> m a :=
  fun arg_62__ =>
    match arg_62__ with
      | m => GHC.Base.op_zgzgze__ getUniqueSupplyM (Coq.Program.Basics.compose
                                  GHC.Base.return_ (GHC.Base.flip initUs_ m))
    end.

Definition initUs {a} : UniqSupply -> UniqSM a -> a * UniqSupply :=
  fun arg_65__ arg_66__ =>
    match arg_65__ , arg_66__ with
      | init_us , m => let scrut_67__ := unUSM m init_us in
                       match scrut_67__ with
                         | pair r us => pair r us
                       end
    end.

Definition getUs : UniqSM UniqSupply :=
  Mk_USM (fun arg_104__ =>
           match arg_104__ with
             | us => let scrut_105__ := splitUniqSupply us in
                     match scrut_105__ with
                       | pair us1 us2 => pair us1 us2
                     end
           end).

Definition getUniqueSupplyM3 {m} `{MonadUnique m} : m (UniqSupply * UniqSupply *
                                                      UniqSupply) :=
  GHC.Base.liftM3 GHC.Tuple.op_Z3T__ getUniqueSupplyM getUniqueSupplyM
  getUniqueSupplyM.

Local Definition instance_MonadUnique_UniqSM_getUniqueSupplyM : UniqSM
                                                                UniqSupply :=
  getUs.

Instance instance_MonadUnique_UniqSM : MonadUnique UniqSM := {
  getUniqueM := instance_MonadUnique_UniqSM_getUniqueM ;
  getUniqueSupplyM := instance_MonadUnique_UniqSM_getUniqueSupplyM ;
  getUniquesM := instance_MonadUnique_UniqSM_getUniquesM }.

(* Unbound variables:
     * Coq.Program.Basics.compose GHC.Base.Applicative GHC.Base.Functor
     GHC.Base.Monad GHC.Base.const GHC.Base.flip GHC.Base.liftM3 GHC.Base.op_zd__
     GHC.Base.op_zgzgze__ GHC.Base.op_ztzg__ GHC.Base.pure GHC.Base.return_
     GHC.Num.Int GHC.Tuple.op_Z3T__ Unique.Unique Unique.mkUniqueGrimily cons list
     pair
*)
