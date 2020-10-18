(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require GHC.Base.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom zipWithAndUnzipM : forall {m} {a} {b} {c} {d},
                         forall `{GHC.Base.Monad m},
                         (a -> b -> m (c * d)%type) -> list a -> list b -> m (list c * list d)%type.

Axiom zipWith4M : forall {m} {a} {b} {c} {d} {e},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list e).

Axiom zipWith3M_ : forall {m} {a} {b} {c} {d},
                   forall `{GHC.Base.Monad m},
                   (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit.

Axiom zipWith3M : forall {m} {a} {b} {c} {d},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> m d) -> list a -> list b -> list c -> m (list d).

Axiom whenM : forall {m},
              forall `{GHC.Base.Monad m}, m bool -> m unit -> m unit.

(* Skipping definition `MonadUtils.unlessM' *)

Axiom orM : forall {m}, forall `{GHC.Base.Monad m}, m bool -> m bool -> m bool.

Axiom maybeMapM : forall {m} {a} {b},
                  forall `{GHC.Base.Monad m}, (a -> m b) -> (option a -> m (option b)).

Axiom mapSndM : forall {m} {b} {c} {a},
                forall `{GHC.Base.Monad m},
                (b -> m c) -> list (a * b)%type -> m (list (a * c)%type).

Axiom mapMaybeM : forall {m} {a} {b},
                  forall `{(GHC.Base.Monad m)}, (a -> m (option b)) -> list a -> m (list b).

Axiom mapAndUnzip5M : forall {m} {a} {b} {c} {d} {e} {f},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e * f)%type) ->
                      list a -> m (list b * list c * list d * list e * list f)%type.

Axiom mapAndUnzip4M : forall {m} {a} {b} {c} {d} {e},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e)%type) ->
                      list a -> m (list b * list c * list d * list e)%type.

Axiom mapAndUnzip3M : forall {m} {a} {b} {c} {d},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d)%type) -> list a -> m (list b * list c * list d)%type.

Axiom mapAccumLM : forall {m} {acc} {x} {y},
                   forall `{GHC.Base.Monad m},
                   (acc -> x -> m (acc * y)%type) -> acc -> list x -> m (acc * list y)%type.

(* Skipping definition `MonadUtils.liftIO4' *)

(* Skipping definition `MonadUtils.liftIO3' *)

(* Skipping definition `MonadUtils.liftIO2' *)

(* Skipping definition `MonadUtils.liftIO1' *)

Axiom foldrM : forall {m} {b} {a},
               forall `{(GHC.Base.Monad m)}, (b -> a -> m a) -> a -> list b -> m a.

Axiom foldlM_ : forall {m} {a} {b},
                forall `{(GHC.Base.Monad m)}, (a -> b -> m a) -> a -> list b -> m unit.

Axiom foldlM : forall {m} {a} {b},
               forall `{(GHC.Base.Monad m)}, (a -> b -> m a) -> a -> list b -> m a.

Axiom fmapMaybeM : forall {m} {a} {b},
                   forall `{(GHC.Base.Monad m)}, (a -> m b) -> option a -> m (option b).

Axiom fmapEitherM : forall {m} {a} {b} {c} {d},
                    forall `{GHC.Base.Monad m},
                    (a -> m b) ->
                    (c -> m d) -> Data.Either.Either a c -> m (Data.Either.Either b d).

Axiom concatMapM : forall {m} {a} {b},
                   forall `{GHC.Base.Monad m}, (a -> m (list b)) -> list a -> m (list b).

Axiom anyM : forall {m} {a},
             forall `{GHC.Base.Monad m}, (a -> m bool) -> list a -> m bool.

Axiom allM : forall {m} {a},
             forall `{GHC.Base.Monad m}, (a -> m bool) -> list a -> m bool.

(* External variables:
     bool list op_zt__ option unit Data.Either.Either GHC.Base.Monad
*)
