(* Preamble *)
Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

(*********** numbers ********************************)

Axiom Int : Type.
Axiom lte_Int : Int -> Int -> bool.

(* Integers *)
Require Import ZArith.
Definition Integer  := Z.

(* Rational numbers *)
Require QArith.
Module Q := Coq.QArith.QArith_base.
Definition Rational := Q.Q.


Class Num a := {
  __op_zp__   : a -> a -> a ;
  __op_zm__   : a -> a -> a ;
  __op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := __op_zp__ (at level 50, left associativity).
Notation "'_+_'" := __op_zp__.

Infix    "-"     := __op_zm__ (at level 50, left associativity).
Notation "'_-_'" := __op_zm__.

Infix    "*"     := __op_zt__ (at level 40, left associativity).
Notation "'_*_'" := __op_zt__.

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Instance __Num_Int__ : Num Int. Admitted.
Instance __Num_Z__ : Num Integer. Admitted.
Instance __Num_Q__ : Num Rational. Admitted.



(* List notation *)
Require Import Coq.Lists.List.


Fixpoint take {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if lte_Int n #0 then nil else (y :: take (n - #1) ys)
  end.

Fixpoint drop {a:Type} (n:Int) (xs:list a) : list a :=
  match xs with
  | nil => nil
  | y :: ys => if lte_Int n #0 then (y :: ys) else drop (n - #1) ys
  end.

(* SSreflect library *)
Require Import mathcomp.ssreflect.ssreflect.

(*********************************************************************)

Notation "'_(,)_'" := (fun x y => (x,y)).
Notation "'_(,,)_'" := (fun x y z => (x, y, z)).

(********************************************************************)

(* Characters and Strings *)

Axiom Char     : Type.
Definition String := list Char.

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").


Notation "'_++_'" := (fun x y => x ++ y).
Notation "'_::_'" := (fun x y => x :: y).

(********************************************************************)

Axiom error : forall {A : Type}, String -> A.

(********************************************************************)

(* I've been assured that this is OK *)
Inductive IO (a : Type) : Type :=.
Inductive IORef (a : Type) : Type :=.
Inductive IOError : Type :=.

Definition FilePath := String.

Axiom primIntToChar      : Int -> Char.
Axiom primCharToInt      : Char -> Int.
Axiom primUnicodeMaxChar : Char.

Axiom primPutChar   : Char -> IO unit.
Axiom primReadFile  : String -> IO String.
Axiom primWriteFile : String -> String -> IO unit.
Axiom primUserError : forall {A}, A.
Axiom primIOError   : forall {A}, A.
Axiom primGetContents : IO String.
Axiom primGetChar     : IO Char.
Axiom primCatch       : forall {a}, IO a -> (IOError -> IO a) -> IO a.
Axiom primAppendFile  : FilePath -> String -> IO unit.

Class Monad m := {
  op_zgzg__ : (forall {a} {b}, ((m a) -> ((m b) -> (m b)))) ;
  op_zgzgze__ : (forall {a} {b}, ((m a) -> (((a -> (m b))) -> (m b)))) ;
  fail : (forall {a}, (String -> (m a))) ;
  return_ : (forall {a}, (a -> (m a))) }.

Infix ">>" := (op_zgzg__) (left associativity, at level 86).

Notation "'_>>_'" := (op_zgzg__).

Infix ">>=" := (op_zgzgze__) (left associativity, at level 86).

Notation "'_>>=_'" := (op_zgzgze__).

Instance Monad__IO__ : Monad IO. Admitted.

(****************************************************************)

Axiom showSigned : Z -> String.

(*
     !! * ++ :: Char EQ GT IO Int LT None Rational Some String Z _(,)_ _(,,)_ _::_
     _Char.isSpace_ bool error list mandatory nil option optional pair primAppendFile
     primCatch primCharToInt primGetChar primGetContents primIOError primIntToChar
     primPutChar primReadFile primUnicodeMaxChar primUserError primWriteFile readDec
     readFloat readSigned showFloat showInt showLitChar showSigned tt unit xs xs'
*)

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Converted data type declarations: *)
Definition ShowS := ((String -> String)%type).

Class Show a := {
  show : (a -> String) ;
  showList : ((list a) -> ShowS) ;
  showsPrec : (Int -> (a -> ShowS)) }.

Definition ReadS a := ((String -> (list (a * String)))%type).

Class Read a := {
  readList : (ReadS (list a)) ;
  readsPrec : (Int -> (ReadS a)) }.

Inductive Ordering : Type := Mk_LT : Ordering
                          |  Mk_EQ : Ordering
                          |  Mk_GT : Ordering.

Class Functor f := {
  fmap : (forall {a} {b}, (((a -> b)) -> ((f a) -> (f b)))) }.

Class Fractional a `{((Num a))} := {
  op_zs__ : (a -> (a -> a)) ;
  fromRational : (Rational -> a) ;
  recip : (a -> a) }.

Infix "/" := (op_zs__) (left associativity, at level 40).

Notation "'_/_'" := (op_zs__).

Class Floating a `{((Fractional a))} := {
  op_ztzt__ : (a -> (a -> a)) ;
  acos : (a -> a) ;
  acosh : (a -> a) ;
  asin : (a -> a) ;
  asinh : (a -> a) ;
  atan : (a -> a) ;
  atanh : (a -> a) ;
  cos : (a -> a) ;
  cosh : (a -> a) ;
  exp : (a -> a) ;
  log : (a -> a) ;
  logBase : (a -> (a -> a)) ;
  pi : a ;
  sin : (a -> a) ;
  sinh : (a -> a) ;
  sqrt : (a -> a) ;
  tan : (a -> a) ;
  tanh : (a -> a) }.

Infix "**" := (op_ztzt__) (right associativity, at level 30).

Notation "'_**_'" := (op_ztzt__).

Class Eq a := {
  op_zsze__ : (a -> (a -> bool)) ;
  op_zeze__ : (a -> (a -> bool)) }.

Infix "/=" := (op_zsze__) (no associativity, at level 70).

Notation "'_/=_'" := (op_zsze__).

Infix "==" := (op_zeze__) (no associativity, at level 70).

Notation "'_==_'" := (op_zeze__).

Class Ord a `{((Eq a))} := {
  op_zl__ : (a -> (a -> bool)) ;
  op_zlze__ : (a -> (a -> bool)) ;
  op_zg__ : (a -> (a -> bool)) ;
  op_zgze__ : (a -> (a -> bool)) ;
  compare : (a -> (a -> Ordering)) ;
  max : (a -> (a -> a)) ;
  min : (a -> (a -> a)) }.

Infix "<" := (op_zl__) (no associativity, at level 70).

Notation "'_<_'" := (op_zl__).

Infix "<=" := (op_zlze__) (no associativity, at level 70).

Notation "'_<=_'" := (op_zlze__).

Infix ">" := (op_zg__) (no associativity, at level 70).

Notation "'_>_'" := (op_zg__).

Infix ">=" := (op_zgze__) (no associativity, at level 70).

Notation "'_>=_'" := (op_zgze__).

Class Real a `{(Num a)} `{(Ord a)} := {
  toRational : (a -> Rational) }.

Class Enum a := {
  enumFrom : (a -> (list a)) ;
  enumFromThen : (a -> (a -> (list a))) ;
  enumFromThenTo : (a -> (a -> (a -> (list a)))) ;
  enumFromTo : (a -> (a -> (list a))) ;
  fromEnum : (a -> Int) ;
  pred : (a -> a) ;
  succ : (a -> a) ;
  toEnum : (Int -> a) }.

Class Integral a `{(Real a)} `{(Enum a)} := {
  div : (a -> (a -> a)) ;
  divMod : (a -> (a -> (a * a))) ;
  mod_ : (a -> (a -> a)) ;
  quot : (a -> (a -> a)) ;
  quotRem : (a -> (a -> (a * a))) ;
  rem : (a -> (a -> a)) ;
  toInteger : (a -> Z) }.

Class RealFrac a `{(Real a)} `{(Fractional a)} := {
  ceiling : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  floor : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  properFraction : (forall {b}, (forall `{((Integral b))}, (a -> (b * a)))) ;
  round : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  truncate : (forall {b}, (forall `{((Integral b))}, (a -> b))) }.

Class RealFloat a `{(RealFrac a)} `{(Floating a)} := {
  atan2 : (a -> (a -> a)) ;
  decodeFloat : (a -> (Z * Int)) ;
  encodeFloat : (Z -> (Int -> a)) ;
  exponent : (a -> Int) ;
  floatDigits : (a -> Int) ;
  floatRadix : (a -> Z) ;
  floatRange : (a -> (Int * Int)) ;
  isDenormalized : (a -> bool) ;
  isIEEE : (a -> bool) ;
  isInfinite : (a -> bool) ;
  isNaN : (a -> bool) ;
  isNegativeZero : (a -> bool) ;
  scaleFloat : (Int -> (a -> a)) ;
  significand : (a -> a) }.

Inductive Either a b : Type := Mk_Left : (a -> (Either a b))
                            |  Mk_Right : (b -> (Either a b)).

Class Bounded a := {
  maxBound : a ;
  minBound : a }.

Arguments Mk_Left {_} {_} _.

Arguments Mk_Right {_} {_} _.

(* Converted value declarations: *)
Definition zipWith3 {a} {b} {c} {d} : (((a -> (b -> (c -> d)))) -> ((list
                                      a) -> ((list b) -> ((list c) -> (list d))))) := (fix zipWith3 arg_155__
                                                                                                    arg_156__ arg_157__
                                                                                                    arg_158__
                                                                                             := (match arg_155__
                                                                                                     , arg_156__
                                                                                                     , arg_157__
                                                                                                     , arg_158__ with
                                                                                                  | z , (a :: as_) , (b
                                                                                                    :: bs) , (c ::
                                                                                                    cs) => ((((z a) b)
                                                                                                           c) ::
                                                                                                           ((((zipWith3
                                                                                                           z) as_) bs)
                                                                                                           cs))
                                                                                                  | _ , _ , _ , _ => nil
                                                                                                end)).

Definition zipWith {a} {b} {c} : (((a -> (b -> c))) -> ((list a) -> ((list
                                 b) -> (list c)))) := (fix zipWith arg_152__ arg_153__ arg_154__
                                                             := (match arg_152__ , arg_153__ , arg_154__ with
                                                                  | z , (a :: as_) , (b :: bs) => (((z a) b) ::
                                                                                                  (((zipWith z) as_)
                                                                                                  bs))
                                                                  | _ , _ , _ => nil
                                                                end)).

Definition zip3 {a} {b} {c} : ((list a) -> ((list b) -> ((list c) -> (list ((a *
                                                                           b) * c))))) := (zipWith3 _(,,)_).

Definition zip {a} {b} : ((list a) -> ((list b) -> (list (a * b)))) := (zipWith
                                                                       _(,)_).

Definition writeFile : (FilePath -> (String -> (IO unit))) := primWriteFile.

Definition userError : (String -> IOError) := primUserError.

Definition undefined {a} : a := (error &"Prelude.undefined").

Definition tail {a} : ((list a) -> (list a)) := (fun arg_111__ =>
                                                  (match arg_111__ with
                                                    | (_ :: xs) => xs
                                                    | nil => (error &"Prelude.tail: empty list")
                                                  end)).

Definition splitAt {a} : (Int -> ((list a) -> ((list a) * (list a)))) :=
  (fun arg_131__
       arg_132__ =>
    (match arg_131__ , arg_132__ with
      | n , xs => (pair ((take n) xs) ((drop n) xs))
    end)).

Definition span {a} : (((a -> bool)) -> ((list a) -> ((list a) * (list a)))) :=
  (fix span arg_135__ arg_136__ := (match arg_135__ , arg_136__ with
                                     | p , nil => (pair nil nil)
                                     | p , ((x :: xs') as xs) => (match ((span p) xs') with
                                                                   | (pair ys zs) => (if (p x)
                                                                                     then (pair (x :: ys) zs)
                                                                                     else (pair nil xs))
                                                                 end)
                                   end)).

Definition snd {a} {b} : ((a * b) -> b) := (fun arg_98__ =>
                                             (match arg_98__ with
                                               | (pair x y) => y
                                             end)).

Definition shows {a} `{((Show a))} : (a -> ShowS) := (showsPrec #0).

Definition showString : (String -> ShowS) := _++_.

Definition showChar : (Char -> ShowS) := _::_.

Definition scanl {a} {b} : (((a -> (b -> a))) -> (a -> ((list b) -> (list
                           a)))) := (fix scanl arg_121__ arg_122__ arg_123__ := (match arg_121__
                                                                                     , arg_122__
                                                                                     , arg_123__ with
                                                                                  | f , q , xs => (q :: ((match xs with
                                                                                                    | nil => nil
                                                                                                    | (x :: xs) =>
                                                                                                      (((scanl f) (((f
                                                                                                                  q)
                                                                                                                  x)))
                                                                                                      xs)
                                                                                                  end)))
                                                                                end)).

Definition scanl1 {a} : (((a -> (a -> a))) -> ((list a) -> (list a))) :=
  (fun arg_124__
       arg_125__ =>
    (match arg_124__ , arg_125__ with
      | f , (x :: xs) => (((scanl f) x) xs)
      | _ , nil => nil
    end)).

Definition reads {a} `{((Read a))} : (ReadS a) := (readsPrec #0).

Definition readFile : (FilePath -> (IO String)) := primReadFile.

Definition read {a} `{((Read a))} : (String -> a) := (fun arg_163__ =>
                                                       (match arg_163__ with
                                                         | s => undefined
                                                       end)).

Definition putChar : (Char -> (IO unit)) := primPutChar.

Definition otherwise : bool := true.

Definition op_zezlzl__ {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((m
                                                  a) -> (m b))) := (fun arg_75__
                                                                        arg_76__ =>
                                                                     (match arg_75__ , arg_76__ with
                                                                       | f , x => (x >>= f)
                                                                     end)).

Infix "=<<" := (op_zezlzl__) (right associativity, at level 85).

Notation "'_=<<_'" := (op_zezlzl__).

Definition op_zd__ {a} {b} : (((a -> b)) -> (a -> b)) := (fun arg_86__
                                                              arg_87__ =>
                                                           (match arg_86__ , arg_87__ with
                                                             | f , x => (f x)
                                                           end)).

Infix "$" := (op_zd__) (right associativity, at level 91).

Notation "'_$_'" := (op_zd__).

Definition op_z2218U__ {a} {b} {c} : (((b -> c)) -> (((a -> b)) -> (a -> c))) :=
  (fun arg_81__
       arg_82__ =>
    (match arg_81__ , arg_82__ with
      | f , g => (fun arg_80__ => (match arg_80__ with | x => (f ((g x))) end))
    end)).

Infix "∘" := (op_z2218U__) (right associativity, at level 99).

Notation "'_∘_'" := (op_z2218U__).

Definition realToFrac {a} {b} `{(Real a)} `{(Fractional b)} : (a -> b) :=
  (fromRational ∘ toRational).

Definition showParen : (bool -> (ShowS -> ShowS)) := (fun arg_164__
                                                          arg_165__ =>
                                                       (match arg_164__ , arg_165__ with
                                                         | b , p => (if b
                                                                    then (((showChar &#"(") ∘ p) ∘ (showChar &#")"))
                                                                    else p)
                                                       end)).

Definition null {a} : ((list a) -> bool) := (fun arg_114__ =>
                                              (match arg_114__ with
                                                | nil => true
                                                | (_ :: _) => false
                                              end)).

Definition not : (bool -> bool) := (fun arg_90__ =>
                                     (match arg_90__ with
                                       | true => false
                                       | false => true
                                     end)).

Definition maybe {a} {b} : (b -> (((a -> b)) -> ((option a) -> b))) :=
  (fun arg_91__
       arg_92__
       arg_93__ =>
    (match arg_91__ , arg_92__ , arg_93__ with
      | n , f , None => n
      | n , f , (Some x) => (f x)
    end)).

Definition map {a} {b} : (((a -> b)) -> ((list a) -> (list b))) := (fix map
                                                                          arg_104__ arg_105__ := (match arg_104__
                                                                                                      , arg_105__ with
                                                                                                   | f , nil => nil
                                                                                                   | f , (x :: xs) =>
                                                                                                     ((f x) :: ((map f)
                                                                                                     xs))
                                                                                                 end)).

Definition lookup {a} {b} `{((Eq a))} : (a -> ((list (a * b)) -> (option b))) :=
  (fix lookup arg_148__ arg_149__ := (match arg_148__ , arg_149__ with
                                       | key , nil => None
                                       | key , ((pair x y) :: xys) => (if (key == x)
                                                                      then (Some y)
                                                                      else ((lookup key) xys))
                                     end)).

Definition length {a} : ((list a) -> Int) := (fix length arg_115__
                                                    := (match arg_115__ with
                                                         | nil => #0
                                                         | (_ :: l) => (#1 + (length l))
                                                       end)).

Definition last {a} : ((list a) -> a) := (fix last arg_112__
                                                := (match arg_112__ with
                                                     | (x :: nil) => x
                                                     | (_ :: xs) => (last xs)
                                                     | nil => (error &"Prelude.last: empty list")
                                                   end)).

Definition ioError {a} : (IOError -> (IO a)) := primIOError.

Definition init {a} : ((list a) -> (list a)) := (fix init arg_113__
                                                       := (match arg_113__ with
                                                            | (x :: nil) => nil
                                                            | (x :: xs) => (x :: (init xs))
                                                            | nil => (error &"Prelude.init: empty list")
                                                          end)).

Definition id {a} : (a -> a) := (fun arg_77__ =>
                                  (match arg_77__ with
                                    | x => x
                                  end)).

Definition head {a} : ((list a) -> a) := (fun arg_110__ =>
                                           (match arg_110__ with
                                             | (x :: _) => x
                                             | nil => (error &"Prelude.head: empty list")
                                           end)).

Definition getContents : (IO String) := primGetContents.

Definition getChar : (IO Char) := primGetChar.

Definition fst {a} {b} : ((a * b) -> a) := (fun arg_97__ =>
                                             (match arg_97__ with
                                               | (pair x y) => x
                                             end)).

Definition uncurry {a} {b} {c} : (((a -> (b -> c))) -> (((a * b) -> c))) :=
  (fun arg_102__
       arg_103__ =>
    (match arg_102__ , arg_103__ with
      | f , p => ((f ((fst p))) ((snd p)))
    end)).

Definition fromIntegral {a} {b} `{(Integral a)} `{(Num b)} : (a -> b) :=
  (fromInteger ∘ toInteger).

Definition foldr1 {a} : (((a -> (a -> a))) -> ((list a) -> a)) := (fix foldr1
                                                                         arg_129__ arg_130__ := (match arg_129__
                                                                                                     , arg_130__ with
                                                                                                  | f , (x :: nil) => x
                                                                                                  | f , (x :: xs) => ((f
                                                                                                                     x)
                                                                                                                     (((foldr1
                                                                                                                     f)
                                                                                                                     xs)))
                                                                                                  | _ , nil => (error
                                                                                                               &"Prelude.foldr1: empty list")
                                                                                                end)).

Definition unwords : ((list String) -> String) := (fun arg_141__ =>
                                                    (match arg_141__ with
                                                      | nil => &""
                                                      | ws => ((foldr1 ((fun arg_139__
                                                                             arg_140__ =>
                                                                         (match arg_139__ , arg_140__ with
                                                                           | w , s => (w ++ ((&#" " :: s)))
                                                                         end)))) ws)
                                                    end)).

Definition foldr {a} {b} : (((a -> (b -> b))) -> (b -> ((list a) -> b))) :=
  (fix foldr arg_126__ arg_127__ arg_128__ := (match arg_126__
                                                   , arg_127__
                                                   , arg_128__ with
                                                | f , z , nil => z
                                                | f , z , (x :: xs) => ((f x) ((((foldr f) z) xs)))
                                              end)).

Definition or : ((list bool) -> bool) := ((foldr orb) false).

Definition sequence {a} {m} `{(Monad m)} : ((list (m a)) -> (m (list a))) :=
  (let mcons :=
    (fun arg_69__
         arg_70__ =>
      (match arg_69__ , arg_70__ with
        | p , q => (p >>= (fun arg_68__ =>
                     (match arg_68__ with
                       | x => (q >>= (fun arg_67__ =>
                                (match arg_67__ with
                                  | y => (return_ ((x :: y)))
                                end)))
                     end)))
      end))
  in ((foldr mcons) ((return_ nil)))).

Definition mapM {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((list a) -> (m
                                           (list b)))) := (fun arg_71__
                                                               arg_72__ =>
                                                            (match arg_71__ , arg_72__ with
                                                              | f , as_ => (sequence (((map f) as_)))
                                                            end)).

Definition sequence_ {a} {m} `{(Monad m)} : ((list (m a)) -> (m unit)) :=
  ((foldr _>>_) ((return_ tt))).

Definition mapM_ {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((list a) -> (m
                                            unit))) := (fun arg_73__
                                                            arg_74__ =>
                                                         (match arg_73__ , arg_74__ with
                                                           | f , as_ => (sequence_ (((map f) as_)))
                                                         end)).

Definition putStr : (String -> (IO unit)) := (fun arg_166__ =>
                                               (match arg_166__ with
                                                 | s => ((mapM_ putChar) s)
                                               end)).

Definition putStrLn : (String -> (IO unit)) := (fun arg_167__ =>
                                                 (match arg_167__ with
                                                   | s => ((putStr s) >> (putStr &""))
                                                 end)).

Definition print {a} `{(Show a)} : (a -> (IO unit)) := (fun arg_168__ =>
                                                         (match arg_168__ with
                                                           | x => (putStrLn ((show x)))
                                                         end)).

Definition unzip {a} {b} : ((list (a * b)) -> ((list a) * (list b))) := ((foldr
                                                                        ((fun arg_159__
                                                                              arg_160__ =>
                                                                          (match arg_159__ , arg_160__ with
                                                                            | (pair a b) , (pair as_ bs) => (pair (a ::
                                                                                                                  as_)
                                                                                                                  (b ::
                                                                                                                  bs))
                                                                          end)))) (pair nil nil)).

Definition unzip3 {a} {b} {c} : ((list ((a * b) * c)) -> (((list a) * (list b))
                                * (list c))) := ((foldr ((fun arg_161__
                                                              arg_162__ =>
                                                          (match arg_161__ , arg_162__ with
                                                            | (pair (pair a b) c) , (pair (pair as_ bs) cs) => (pair
                                                                                                               (pair (a
                                                                                                                     ::
                                                                                                                     as_)
                                                                                                                     (b
                                                                                                                     ::
                                                                                                                     bs))
                                                                                                               (c ::
                                                                                                               cs))
                                                          end)))) (pair (pair nil nil) nil)).

Definition foldl {a} {b} : (((a -> (b -> a))) -> (a -> ((list b) -> a))) :=
  (fix foldl arg_116__ arg_117__ arg_118__ := (match arg_116__
                                                   , arg_117__
                                                   , arg_118__ with
                                                | f , z , nil => z
                                                | f , z , (x :: xs) => (((foldl f) (((f z) x))) xs)
                                              end)).

Definition foldl1 {a} : (((a -> (a -> a))) -> ((list a) -> a)) := (fun arg_119__
                                                                       arg_120__ =>
                                                                    (match arg_119__ , arg_120__ with
                                                                      | f , (x :: xs) => (((foldl f) x) xs)
                                                                      | _ , nil => (error &"Prelude.foldl1: empty list")
                                                                    end)).

Definition maximum {a} `{((Ord a))} : ((list a) -> a) := (fun arg_150__ =>
                                                           (match arg_150__ with
                                                             | nil => (error &"Prelude.maximum: empty list")
                                                             | xs => ((foldl1 max) xs)
                                                           end)).

Definition minimum {a} `{((Ord a))} : ((list a) -> a) := (fun arg_151__ =>
                                                           (match arg_151__ with
                                                             | nil => (error &"Prelude.minimum: empty list")
                                                             | xs => ((foldl1 min) xs)
                                                           end)).

Definition product {a} `{((Num a))} : ((list a) -> a) := ((foldl _*_) #1).

Definition sum {a} `{((Num a))} : ((list a) -> a) := ((foldl _+_) #0).

Definition flip {a} {b} {c} : (((a -> (b -> c))) -> (b -> (a -> c))) :=
  (fun arg_83__
       arg_84__
       arg_85__ =>
    (match arg_83__ , arg_84__ , arg_85__ with
      | f , x , y => ((f y) x)
    end)).

Definition reverse {a} : ((list a) -> (list a)) := ((foldl ((flip _::_))) nil).

Definition subtract {a} `{((Num a))} : (a -> (a -> a)) := (flip _-_).

Definition filter {a} : (((a -> bool)) -> ((list a) -> (list a))) := (fix filter
                                                                            arg_106__ arg_107__ := (match arg_106__
                                                                                                        , arg_107__ with
                                                                                                     | p , nil => nil
                                                                                                     | p , (x :: xs) =>
                                                                                                       (if (p x)
                                                                                                       then (x ::
                                                                                                            ((filter p)
                                                                                                            xs))
                                                                                                       else ((filter p)
                                                                                                            xs))
                                                                                                   end)).

Definition even {a} `{((Integral a))} : (a -> bool) := (fun arg_66__ =>
                                                         (match arg_66__ with
                                                           | n => ((rem n #2) == #0)
                                                         end)).

Definition odd {a} `{((Integral a))} : (a -> bool) := (not ∘ even).

Definition either {a} {b} {c} : (((a -> c)) -> (((b -> c)) -> ((Either a
                                                                       b) -> c))) := (fun arg_94__
                                                                                          arg_95__
                                                                                          arg_96__ =>
                                                                                       (match arg_94__
                                                                                            , arg_95__
                                                                                            , arg_96__ with
                                                                                         | f , g , (Mk_Left x) => (f x)
                                                                                         | f , g , (Mk_Right y) => (g y)
                                                                                       end)).

Definition dropWhile {a} : (((a -> bool)) -> ((list a) -> (list a))) :=
  (fix dropWhile arg_133__ arg_134__ := (match arg_133__ , arg_134__ with
                                          | p , nil => nil
                                          | p , ((x :: xs') as xs) => (if (p x)
                                                                      then ((dropWhile p) xs')
                                                                      else xs)
                                        end)).

Definition curry {a} {b} {c} : ((((a * b) -> c)) -> (a -> (b -> c))) :=
  (fun arg_99__
       arg_100__
       arg_101__ =>
    (match arg_99__ , arg_100__ , arg_101__ with
      | f , x , y => (f (pair x y))
    end)).

Definition const {a} {b} : (a -> (b -> a)) := (fun arg_78__
                                                   arg_79__ =>
                                                (match arg_78__ , arg_79__ with
                                                  | x , _ => x
                                                end)).

Definition seq {a} {b} : (a -> (b -> b)) := (flip const).

Definition op_zdzn__ {a} {b} : (((a -> b)) -> (a -> b)) := (fun arg_88__
                                                                arg_89__ =>
                                                             (match arg_88__ , arg_89__ with
                                                               | f , x => (seq x (f x))
                                                             end)).

Infix "$!" := (op_zdzn__) (right associativity, at level 91).

Notation "'_$!_'" := (op_zdzn__).

Definition concat {a} : ((list (list a)) -> (list a)) := (fun arg_108__ =>
                                                           (match arg_108__ with
                                                             | xss => (((foldr _++_) nil) xss)
                                                           end)).

Definition concatMap {a} {b} : (((a -> (list b))) -> ((list a) -> (list b))) :=
  (fun arg_109__ => (match arg_109__ with | f => (concat ∘ (map f)) end)).

Definition unlines : ((list String) -> String) := (concatMap ((fun arg_138__ =>
                                                               (arg_138__ ++ &"")))).

Definition catch {a} : ((IO a) -> (((IOError -> (IO a))) -> (IO a))) :=
  primCatch.

Definition break {a} : (((a -> bool)) -> ((list a) -> ((list a) * (list a)))) :=
  (fun arg_137__ => (match arg_137__ with | p => (span ((not ∘ p))) end)).

Definition asTypeOf {a} : (a -> (a -> a)) := const.

Definition appendFile : (FilePath -> (String -> (IO unit))) := primAppendFile.

Definition any {a} : (((a -> bool)) -> ((list a) -> bool)) := (fun arg_142__ =>
                                                                (match arg_142__ with
                                                                  | p => (or ∘ (map p))
                                                                end)).

Definition elem {a} `{((Eq a))} : (a -> ((list a) -> bool)) := (fun arg_145__ =>
                                                                 (match arg_145__ with
                                                                   | x => (any ((fun arg_144__ => (arg_144__ == x))))
                                                                 end)).

Definition and : ((list bool) -> bool) := ((foldr andb) true).

Definition all {a} : (((a -> bool)) -> ((list a) -> bool)) := (fun arg_143__ =>
                                                                (match arg_143__ with
                                                                  | p => (and ∘ (map p))
                                                                end)).

Definition notElem {a} `{((Eq a))} : (a -> ((list a) -> bool)) :=
  (fun arg_147__ =>
    (match arg_147__ with
      | x => (all ((fun arg_146__ => (arg_146__ /= x))))
    end)).

(* No type class instance declarations to convert. *)

(* Unbound variables:
     * + ++ :: >> >>= Char FilePath IO IOError Int Monad None Num Rational Some
     String Z _(,)_ _(,,)_ _*_ _++_ _+_ _-_ _::_ _>>_ andb bool drop error false
     fromInteger list nil option orb pair primAppendFile primCatch primGetChar
     primGetContents primIOError primPutChar primReadFile primUserError primWriteFile
     return_ take true tt unit
*)
