(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Coq.Arith.Wf_nat.

Local Obligation Tactic := idtac.

Local Ltac solve_riffle :=
  solve [ apply Wf.measure_wf, Wf_nat.lt_wf
        | Tactics.program_simpl; simpl; rewrite PeanoNat.Nat.add_succ_r; auto ].

Ltac solve_shuffleLength_start halve length_halve solve1 solve2 :=
  try solve [apply Wf.measure_wf, Wf_nat.lt_wf];
  Tactics.program_simpl; try easy;
  match goal with H : (?half1,?half2) = halve _ ?arg_0__ |- _ =>
    generalize (length_halve _ arg_0__);
    rewrite <-H;
    intros [def_length1 def_length2];
    (* (rewrite def_length1 || rewrite def_length2); simpl; *)
    solve [solve1 arg_0__ def_length1 | solve2 arg_0__ def_length2]
  end.

Ltac solve_shuffleLength_half1 arg_0__ def_length1 :=
  rewrite def_length1; simpl;
  destruct arg_0__ as [|head0 tail0]; simpl; try easy;
  apply Lt.lt_n_S, PeanoNat.Nat.lt_div2;
  destruct tail0; simpl; [|apply PeanoNat.Nat.lt_0_succ];
  match goal with H : forall x, (cons x nil) <> (cons ?h nil) |- _ => specialize (H h) end;
  contradiction.

Ltac solve_shuffleLength_half2 arg_0__ def_length2 :=
  rewrite def_length2;
  apply PeanoNat.Nat.lt_div2;
  now destruct arg_0__; simpl; [|apply PeanoNat.Nat.lt_0_succ].

Ltac solve_shuffleLength halve length_halve :=
  solve_shuffleLength_start halve length_halve solve_shuffleLength_half1 solve_shuffleLength_half2.

(* Converted imports: *)

Require Control.Monad.Trans.Class.
Require Control.Monad.Trans.Cont.
Require Control.Monad.Trans.Except.
Require Control.Monad.Trans.Identity.
Require Control.Monad.Trans.Maybe.
Require Control.Monad.Trans.RWS.Lazy.
Require Control.Monad.Trans.Reader.
Require Control.Monad.Trans.State.Lazy.
Require Control.Monad.Trans.Writer.Lazy.
Require GHC.Base.
Require System.Random.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record MonadRandom__Dict m := MonadRandom__Dict_Build {
  getRandom__ : forall {a}, forall `{(System.Random.Random a)}, m a ;
  getRandomR__ : forall {a},
  forall `{(System.Random.Random a)}, (a * a)%type -> m a ;
  getRandomRs__ : forall {a},
  forall `{(System.Random.Random a)}, (a * a)%type -> m (list a) ;
  getRandoms__ : forall {a}, forall `{(System.Random.Random a)}, m (list a) }.

Definition MonadRandom m `{(GHC.Base.Monad m)} :=
  forall r__, (MonadRandom__Dict m -> r__) -> r__.

Existing Class MonadRandom.

Definition getRandom `{g__0__ : MonadRandom m}
   : forall {a}, forall `{(System.Random.Random a)}, m a :=
  g__0__ _ (getRandom__ m).

Definition getRandomR `{g__0__ : MonadRandom m}
   : forall {a}, forall `{(System.Random.Random a)}, (a * a)%type -> m a :=
  g__0__ _ (getRandomR__ m).

Definition getRandomRs `{g__0__ : MonadRandom m}
   : forall {a}, forall `{(System.Random.Random a)}, (a * a)%type -> m (list a) :=
  g__0__ _ (getRandomRs__ m).

Definition getRandoms `{g__0__ : MonadRandom m}
   : forall {a}, forall `{(System.Random.Random a)}, m (list a) :=
  g__0__ _ (getRandoms__ m).

Record MonadInterleave__Dict (m : Type -> Type) := MonadInterleave__Dict_Build {
  interleave__ : forall {a}, m a -> m a }.

Definition MonadInterleave (m : Type -> Type) `{MonadRandom m} :=
  forall r__, (MonadInterleave__Dict m -> r__) -> r__.

Existing Class MonadInterleave.

Definition interleave `{g__0__ : MonadInterleave m} : forall {a}, m a -> m a :=
  g__0__ _ (interleave__ m).

(* Converted value declarations: *)

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__Strict_WriterT' of
   class `Control.Monad.Random.Class.MonadRandom' *)

Local Definition MonadRandom__WriterT_getRandom {inst_m} {inst_w} `{MonadRandom
  inst_m} `{GHC.Base.Monoid inst_w}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__WriterT_getRandomR {inst_m} {inst_w} `{MonadRandom
  inst_m} `{GHC.Base.Monoid inst_w}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__WriterT_getRandomRs {inst_m} {inst_w}
  `{MonadRandom inst_m} `{GHC.Base.Monoid inst_w}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type ->
     (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__WriterT_getRandoms {inst_m} {inst_w} `{MonadRandom
  inst_m} `{GHC.Base.Monoid inst_w}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__WriterT {m} {w} `{MonadRandom m} `{GHC.Base.Monoid
  w}
   : MonadRandom (Control.Monad.Trans.Writer.Lazy.WriterT w m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__WriterT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__WriterT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__WriterT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__WriterT_getRandoms |}.

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__Strict_StateT' of
   class `Control.Monad.Random.Class.MonadRandom' *)

Local Definition MonadRandom__StateT_getRandom {inst_m} {inst_s} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__StateT_getRandomR {inst_m} {inst_s} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__StateT_getRandomRs {inst_m} {inst_s}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type ->
     (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__StateT_getRandoms {inst_m} {inst_s} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__StateT {m} {s} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.State.Lazy.StateT s m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__StateT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__StateT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__StateT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__StateT_getRandoms |}.

Local Definition MonadRandom__ReaderT_getRandom {inst_m} {inst_r} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__ReaderT_getRandomR {inst_m} {inst_r}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__ReaderT_getRandomRs {inst_m} {inst_r}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__ReaderT_getRandoms {inst_m} {inst_r}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__ReaderT {m} {r} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.Reader.ReaderT r m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ReaderT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ReaderT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ReaderT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ReaderT_getRandoms |}.

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__Strict_RWST' of
   class `Control.Monad.Random.Class.MonadRandom' *)

Local Definition MonadRandom__RWST_getRandom {inst_w} {inst_m} {inst_r} {inst_s}
  `{GHC.Base.Monoid inst_w} `{MonadRandom inst_m}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__RWST_getRandomR {inst_w} {inst_m} {inst_r}
  {inst_s} `{GHC.Base.Monoid inst_w} `{MonadRandom inst_m}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type ->
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__RWST_getRandomRs {inst_w} {inst_m} {inst_r}
  {inst_s} `{GHC.Base.Monoid inst_w} `{MonadRandom inst_m}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type ->
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__RWST_getRandoms {inst_w} {inst_m} {inst_r}
  {inst_s} `{GHC.Base.Monoid inst_w} `{MonadRandom inst_m}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__RWST {w} {m} {r} {s} `{GHC.Base.Monoid w}
  `{MonadRandom m}
   : MonadRandom (Control.Monad.Trans.RWS.Lazy.RWST r w s m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__RWST_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__RWST_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__RWST_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__RWST_getRandoms |}.

Local Definition MonadRandom__MaybeT_getRandom {inst_m} `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Maybe.MaybeT inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__MaybeT_getRandomR {inst_m} `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Maybe.MaybeT inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__MaybeT_getRandomRs {inst_m} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Maybe.MaybeT inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__MaybeT_getRandoms {inst_m} `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Maybe.MaybeT inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__MaybeT {m} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.Maybe.MaybeT m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__MaybeT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__MaybeT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__MaybeT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__MaybeT_getRandoms |}.

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__ListT' of class
   `Control.Monad.Random.Class.MonadRandom' *)

Local Definition MonadRandom__IdentityT_getRandom {inst_m} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Identity.IdentityT inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__IdentityT_getRandomR {inst_m} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Identity.IdentityT inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__IdentityT_getRandomRs {inst_m} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Identity.IdentityT inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__IdentityT_getRandoms {inst_m} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Identity.IdentityT inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__IdentityT {m} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.Identity.IdentityT m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__IdentityT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__IdentityT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__IdentityT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__IdentityT_getRandoms |}.

Local Definition MonadRandom__ExceptT_getRandom {inst_m} {inst_e} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Except.ExceptT inst_e inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__ExceptT_getRandomR {inst_m} {inst_e}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Except.ExceptT inst_e inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__ExceptT_getRandomRs {inst_m} {inst_e}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Except.ExceptT inst_e inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__ExceptT_getRandoms {inst_m} {inst_e}
  `{(MonadRandom inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Except.ExceptT inst_e inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__ExceptT {m} {e} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.Except.ExceptT e m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ExceptT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ExceptT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ExceptT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ExceptT_getRandoms |}.

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__ErrorT' of class
   `Control.Monad.Random.Class.MonadRandom' *)

Local Definition MonadRandom__ContT_getRandom {inst_m} {inst_r} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Cont.ContT inst_r inst_m) a :=
  fun {a} `{(System.Random.Random a)} => Control.Monad.Trans.Class.lift getRandom.

Local Definition MonadRandom__ContT_getRandomR {inst_m} {inst_r} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Cont.ContT inst_r inst_m) a :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomR.

Local Definition MonadRandom__ContT_getRandomRs {inst_m} {inst_r} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (a * a)%type -> (Control.Monad.Trans.Cont.ContT inst_r inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift GHC.Base.∘ getRandomRs.

Local Definition MonadRandom__ContT_getRandoms {inst_m} {inst_r} `{(MonadRandom
   inst_m)}
   : forall {a},
     forall `{(System.Random.Random a)},
     (Control.Monad.Trans.Cont.ContT inst_r inst_m) (list a) :=
  fun {a} `{(System.Random.Random a)} =>
    Control.Monad.Trans.Class.lift getRandoms.

Program Instance MonadRandom__ContT {m} {r} `{(MonadRandom m)}
   : MonadRandom (Control.Monad.Trans.Cont.ContT r m) :=
  fun _ k__ =>
    k__ {| getRandom__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ContT_getRandom ;
           getRandomR__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ContT_getRandomR ;
           getRandomRs__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ContT_getRandomRs ;
           getRandoms__ := fun {a} `{(System.Random.Random a)} =>
             MonadRandom__ContT_getRandoms |}.

(* Skipping instance `Control.Monad.Random.Class.MonadRandom__IO' of class
   `Control.Monad.Random.Class.MonadRandom' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__Strict_WriterT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__WriterT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__Strict_StateT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__StateT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__ReaderT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__Strict_RWST__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__RWST__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__MaybeT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__ListT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__IdentityT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__ExceptT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__ErrorT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__ContT__5' *)

(* Skipping all instances of class `Control.Monad.Random.Class.MonadSplit',
   including `Control.Monad.Random.Class.MonadSplit__StdGen__IO' *)

(* Skipping instance
   `Control.Monad.Random.Class.MonadInterleave__Strict_WriterT' of class
   `Control.Monad.Random.Class.MonadInterleave' *)

Local Definition MonadInterleave__WriterT_interleave {inst_w} {inst_m}
  `{GHC.Base.Monoid inst_w} `{MonadInterleave inst_m}
   : forall {a},
     (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) a ->
     (Control.Monad.Trans.Writer.Lazy.WriterT inst_w inst_m) a :=
  fun {a} => Control.Monad.Trans.Writer.Lazy.mapWriterT interleave.

Program Instance MonadInterleave__WriterT {w} {m} `{GHC.Base.Monoid w}
  `{MonadInterleave m}
   : MonadInterleave (Control.Monad.Trans.Writer.Lazy.WriterT w m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__WriterT_interleave |}.

(* Skipping instance `Control.Monad.Random.Class.MonadInterleave__Strict_StateT'
   of class `Control.Monad.Random.Class.MonadInterleave' *)

Local Definition MonadInterleave__StateT_interleave {inst_m} {inst_s}
  `{(MonadInterleave inst_m)}
   : forall {a},
     (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) a ->
     (Control.Monad.Trans.State.Lazy.StateT inst_s inst_m) a :=
  fun {a} => Control.Monad.Trans.State.Lazy.mapStateT interleave.

Program Instance MonadInterleave__StateT {m} {s} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.State.Lazy.StateT s m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__StateT_interleave |}.

Local Definition MonadInterleave__ReaderT_interleave {inst_m} {inst_r}
  `{(MonadInterleave inst_m)}
   : forall {a},
     (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) a ->
     (Control.Monad.Trans.Reader.ReaderT inst_r inst_m) a :=
  fun {a} => Control.Monad.Trans.Reader.mapReaderT interleave.

Program Instance MonadInterleave__ReaderT {m} {r} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.Reader.ReaderT r m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__ReaderT_interleave |}.

(* Skipping instance `Control.Monad.Random.Class.MonadInterleave__Strict_RWST'
   of class `Control.Monad.Random.Class.MonadInterleave' *)

Local Definition MonadInterleave__RWST_interleave {inst_w} {inst_m} {inst_r}
  {inst_s} `{GHC.Base.Monoid inst_w} `{MonadInterleave inst_m}
   : forall {a},
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) a ->
     (Control.Monad.Trans.RWS.Lazy.RWST inst_r inst_w inst_s inst_m) a :=
  fun {a} => Control.Monad.Trans.RWS.Lazy.mapRWST interleave.

Program Instance MonadInterleave__RWST {w} {m} {r} {s} `{GHC.Base.Monoid w}
  `{MonadInterleave m}
   : MonadInterleave (Control.Monad.Trans.RWS.Lazy.RWST r w s m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__RWST_interleave |}.

Local Definition MonadInterleave__MaybeT_interleave {inst_m} `{(MonadInterleave
   inst_m)}
   : forall {a},
     (Control.Monad.Trans.Maybe.MaybeT inst_m) a ->
     (Control.Monad.Trans.Maybe.MaybeT inst_m) a :=
  fun {a} => Control.Monad.Trans.Maybe.mapMaybeT interleave.

Program Instance MonadInterleave__MaybeT {m} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.Maybe.MaybeT m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__MaybeT_interleave |}.

(* Skipping instance `Control.Monad.Random.Class.MonadInterleave__ListT' of
   class `Control.Monad.Random.Class.MonadInterleave' *)

Local Definition MonadInterleave__IdentityT_interleave {inst_m}
  `{(MonadInterleave inst_m)}
   : forall {a},
     (Control.Monad.Trans.Identity.IdentityT inst_m) a ->
     (Control.Monad.Trans.Identity.IdentityT inst_m) a :=
  fun {a} => Control.Monad.Trans.Identity.mapIdentityT interleave.

Program Instance MonadInterleave__IdentityT {m} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.Identity.IdentityT m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__IdentityT_interleave |}.

Local Definition MonadInterleave__ExceptT_interleave {inst_m} {inst_e}
  `{(MonadInterleave inst_m)}
   : forall {a},
     (Control.Monad.Trans.Except.ExceptT inst_e inst_m) a ->
     (Control.Monad.Trans.Except.ExceptT inst_e inst_m) a :=
  fun {a} => Control.Monad.Trans.Except.mapExceptT interleave.

Program Instance MonadInterleave__ExceptT {m} {e} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.Except.ExceptT e m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__ExceptT_interleave |}.

(* Skipping instance `Control.Monad.Random.Class.MonadInterleave__ErrorT' of
   class `Control.Monad.Random.Class.MonadInterleave' *)

Local Definition MonadInterleave__ContT_interleave {inst_m} {inst_r}
  `{(MonadInterleave inst_m)}
   : forall {a},
     (Control.Monad.Trans.Cont.ContT inst_r inst_m) a ->
     (Control.Monad.Trans.Cont.ContT inst_r inst_m) a :=
  fun {a} => Control.Monad.Trans.Cont.mapContT interleave.

Program Instance MonadInterleave__ContT {m} {r} `{(MonadInterleave m)}
   : MonadInterleave (Control.Monad.Trans.Cont.ContT r m) :=
  fun _ k__ =>
    k__ {| interleave__ := fun {a} => MonadInterleave__ContT_interleave |}.

(* External variables:
     Type list op_zt__ Control.Monad.Trans.Class.lift Control.Monad.Trans.Cont.ContT
     Control.Monad.Trans.Cont.mapContT Control.Monad.Trans.Except.ExceptT
     Control.Monad.Trans.Except.mapExceptT Control.Monad.Trans.Identity.IdentityT
     Control.Monad.Trans.Identity.mapIdentityT Control.Monad.Trans.Maybe.MaybeT
     Control.Monad.Trans.Maybe.mapMaybeT Control.Monad.Trans.RWS.Lazy.RWST
     Control.Monad.Trans.RWS.Lazy.mapRWST Control.Monad.Trans.Reader.ReaderT
     Control.Monad.Trans.Reader.mapReaderT Control.Monad.Trans.State.Lazy.StateT
     Control.Monad.Trans.State.Lazy.mapStateT Control.Monad.Trans.Writer.Lazy.WriterT
     Control.Monad.Trans.Writer.Lazy.mapWriterT GHC.Base.Monad GHC.Base.Monoid
     GHC.Base.op_z2218U__ System.Random.Random
*)
