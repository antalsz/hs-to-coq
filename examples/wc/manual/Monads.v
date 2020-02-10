Require Import GHC.Base.
From ExtLib.Structures Require Functor Applicative Monad.

Section Functors.

  Variable f : Type -> Type.

  Context `{Functor.Functor f}.

  Global Instance Functor_Functor : Functor f :=
    fun _ X =>
      X {| fmap__ := fun a b : Type => Functor.fmap;
           op_zlzd____ := fun a b : Type => Functor.fmap ∘ const
        |}.

  Section Applicatives.

    Context `{Applicative.Applicative f}.

    Global Instance Applicative_Applicative : Applicative f :=
      fun _ X =>
        X {| liftA2__ := fun a b c f x y => Applicative.ap (fmap f x) y;
             op_zlztzg____ := fun a b => Applicative.ap ;
             op_ztzg____ := fun a b x y => Applicative.ap (id <$ x) y;
             pure__ := fun a => Applicative.pure
          |}.

    Section Monads.

      Context `{Monad.Monad f}.
      
      Global Instance Monad_Monad : Monad f :=
        fun _ X =>
          X {| op_zgzg____ := fun a b x y => Monad.bind x (fun _ => y);
               op_zgzgze____ := fun a b => Monad.bind ;
               return___ := fun a => Monad.ret
            |}.
      
    End Monads.
  End Applicatives.
End Functors.
