(* Converted data type declarations: *)
Definition ShowS := (string -> string).

Definition ReadS a := (string -> (list (a * string))).

Inductive Ordering : Type := Mk_LT : Ordering
                          |  Mk_EQ : Ordering
                          |  Mk_GT : Ordering.

Class Monad m := {
  __op_zgzg__ : (forall {a} {b}, ((m a) -> ((m b) -> (m b)))) ;
  __op_zgzgze__ : (forall {a} {b}, ((m a) -> (((a -> (m b))) -> (m b)))) ;
  fail : (forall {a}, (string -> (m a))) ;
  return_ : (forall {a}, (a -> (m a))) }.

Infix ">>" := (__op_zgzg__) (at level 99).

Notation "'_>>_'" := (__op_zgzg__).

Infix ">>=" := (__op_zgzgze__) (at level 99).

Notation "'_>>=_'" := (__op_zgzgze__).

Inductive Maybe a : Type := Mk_Nothing : (Maybe a)
                         |  Mk_Just : (a -> (Maybe a)).

Inductive Integer : Type :=.

Inductive Int : Type :=.

Class Read a := {
  readList : (ReadS (list a)) ;
  readsPrec : (Int -> (ReadS a)) }.

Class Show a := {
  show : (a -> string) ;
  showList : ((list a) -> ShowS) ;
  showsPrec : (Int -> (a -> ShowS)) }.

Inductive IOError : Type :=.

Inductive IO a : Type :=.

Class Functor f := {
  fmap : (forall {a} {b}, (((a -> b)) -> ((f a) -> (f b)))) }.

Inductive Float : Type :=.

Definition FilePath := string.

Class Eq a := {
  __op_zsze__ : (a -> (a -> bool)) ;
  __op_zeze__ : (a -> (a -> bool)) }.

Infix "/=" := (__op_zsze__) (at level 99).

Notation "'_/=_'" := (__op_zsze__).

Infix "==" := (__op_zeze__) (at level 99).

Notation "'_==_'" := (__op_zeze__).

Class Num a `{(Eq a)} `{(Show a)} := {
  __op_zt__ : (a -> (a -> a)) ;
  __op_zp__ : (a -> (a -> a)) ;
  __op_zm__ : (a -> (a -> a)) ;
  abs : (a -> a) ;
  fromInteger : (Z -> a) ;
  negate : (a -> a) ;
  signum : (a -> a) }.

Infix "*" := (__op_zt__) (at level 99).

Notation "'_*_'" := (__op_zt__).

Infix "+" := (__op_zp__) (at level 99).

Notation "'_+_'" := (__op_zp__).

Infix "-" := (__op_zm__) (at level 99).

Notation "'_-_'" := (__op_zm__).

Class Fractional a `{((Num a))} := {
  __op_zs__ : (a -> (a -> a)) ;
  fromRational : (Rational -> a) ;
  recip : (a -> a) }.

Infix "/" := (__op_zs__) (at level 99).

Notation "'_/_'" := (__op_zs__).

Class Floating a `{((Fractional a))} := {
  __op_ztzt__ : (a -> (a -> a)) ;
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

Infix "**" := (__op_ztzt__) (at level 99).

Notation "'_**_'" := (__op_ztzt__).

Class Ord a `{((Eq a))} := {
  __op_zl__ : (a -> (a -> bool)) ;
  __op_zlze__ : (a -> (a -> bool)) ;
  __op_zg__ : (a -> (a -> bool)) ;
  __op_zgze__ : (a -> (a -> bool)) ;
  compare : (a -> (a -> Ordering)) ;
  max : (a -> (a -> a)) ;
  min : (a -> (a -> a)) }.

Infix "<" := (__op_zl__) (at level 99).

Notation "'_<_'" := (__op_zl__).

Infix "<=" := (__op_zlze__) (at level 99).

Notation "'_<=_'" := (__op_zlze__).

Infix ">" := (__op_zg__) (at level 99).

Notation "'_>_'" := (__op_zg__).

Infix ">=" := (__op_zgze__) (at level 99).

Notation "'_>=_'" := (__op_zgze__).

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
  ceiling : (forall {b} `{((Integral b))}, (a -> b)) ;
  floor : (forall {b} `{((Integral b))}, (a -> b)) ;
  properFraction : (forall {b} `{((Integral b))}, (a -> (b * a))) ;
  round : (forall {b} `{((Integral b))}, (a -> b)) ;
  truncate : (forall {b} `{((Integral b))}, (a -> b)) }.

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

Inductive Double : Type :=.

Inductive Char : Type :=.

Definition String := (list Char).

Class Bounded a := {
  maxBound : a ;
  minBound : a }.

Inductive Bool : Type := Mk_False : Bool
                      |  Mk_True : Bool.

(* Converted function declarations: *)
Definition zipWith3 {a} {b} {c} {d} : (((a -> (b -> (c -> d)))) -> ((list
                                      a) -> ((list b) -> ((list c) -> (list d))))) := (fix zipWith3 __arg_209__
                                                                                                    __arg_210__
                                                                                                    __arg_211__
                                                                                                    __arg_212__
                                                                                             := (match __arg_209__
                                                                                                     , __arg_210__
                                                                                                     , __arg_211__
                                                                                                     , __arg_212__ with
                                                                                                  | z , (a :: as) , (b
                                                                                                    :: bs) , (c ::
                                                                                                    cs) => ((((z a) b)
                                                                                                           c) ::
                                                                                                           ((((zipWith3
                                                                                                           z) as) bs)
                                                                                                           cs))
                                                                                                  | _ , _ , _ , _ => nil
                                                                                                end)).

Definition zipWith {a} {b} {c} : (((a -> (b -> c))) -> ((list a) -> ((list
                                 b) -> (list c)))) := (fix zipWith __arg_206__ __arg_207__ __arg_208__
                                                             := (match __arg_206__ , __arg_207__ , __arg_208__ with
                                                                  | z , (a :: as) , (b :: bs) => (((z a) b) ::
                                                                                                 (((zipWith z) as) bs))
                                                                  | _ , _ , _ => nil
                                                                end)).

Definition zip3 {a} {b} {c} : ((list a) -> ((list b) -> ((list c) -> (list ((a *
                                                                           b) * c))))) := (zipWith3 _(,,)_).

Definition zip {a} {b} : ((list a) -> ((list b) -> (list (a * b)))) := (zipWith
                                                                       _(,)_).

Definition writeFile : (FilePath -> (string -> (IO unit))) := primWriteFile.

Definition userError : (string -> IOError) := primUserError.

Definition until {a} : (((a -> bool)) -> (((a -> a)) -> (a -> a))) := (fix until
                                                                             __arg_131__ __arg_132__ __arg_133__
                                                                             := (match __arg_131__
                                                                                     , __arg_132__
                                                                                     , __arg_133__ with
                                                                                  | p , f , x => (if (p x)
                                                                                                 then x
                                                                                                 else (((until p) f) ((f
                                                                                                                     x))))
                                                                                end)).

Definition takeWhile {a} : (((a -> bool)) -> ((list a) -> (list a))) :=
  (fix takeWhile __arg_182__ __arg_183__ := (match __arg_182__ , __arg_183__ with
                                              | p , nil => nil
                                              | p , (x :: xs) => (if (p x)
                                                                 then (x :: ((takeWhile p) xs))
                                                                 else nil)
                                            end)).

Definition take {a} : (Int -> ((list a) -> (list a))) :=
  (fix take __arg_176__
       __arg_177__ := (match __arg_176__ , __arg_177__ with
                       | n , _ => (if (n <= 0)
                                   then nil
                                   else _(*MissingValue*))
                       | _ , nil => nil
                       | n , (x :: xs) => (x :: ((take ((n
                                                         -
                                                         1)))
                                                   xs))
                       end)).

Definition span {a} : (((a -> bool)) -> ((list a) -> ((list a) * (list a)))) :=
  (fix span __arg_186__ __arg_187__ := (match __arg_186__ , __arg_187__ with
                                         | p , nil => (pair nil nil)
                                         | p , ((x :: xs') as xs) => (match ((span p) xs') with
                                                                       | (pair ys zs) => (if (p x)
                                                                                         then (pair (x :: ys) zs)
                                                                                         else (pair nil xs))
                                                                     end)
                                       end)).

Definition snd {a} {b} : ((a * b) -> b) := (fun __arg_125__ =>
                                             (match __arg_125__ with
                                               | (pair x y) => y
                                             end)).

Definition shows {a} `{((Show a))} : (a -> ShowS) := (showsPrec 0).

Definition showString : (string -> ShowS) := _++_.

Definition showChar : (Char -> ShowS) := _::_.

Definition showParen : (bool -> (ShowS -> ShowS)) := (fun __arg_218__
                                                          __arg_219__ =>
                                                       (match __arg_218__ , __arg_219__ with
                                                         | b , p => (if b
                                                                    then (((showChar ("("%char)) ∘ p) ∘ (showChar
                                                                         (")"%char)))
                                                                    else p)
                                                       end)).

Definition scanr1 {a} : (((a -> (a -> a))) -> ((list a) -> (list a))) :=
  (fix scanr1 __arg_168__ __arg_169__ := (match __arg_168__ , __arg_169__ with
                                           | f , nil => nil
                                           | f , (x :: nil) => (x :: nil)
                                           | f , (x :: xs) => (match ((scanr1 f) xs) with
                                                                | ((q :: _) as qs) => (((f x) q) :: qs)
                                                              end)
                                         end)).

Definition scanr {a} {b} : (((a -> (b -> b))) -> (b -> ((list a) -> (list
                           b)))) := (fix scanr __arg_165__ __arg_166__ __arg_167__ := (match __arg_165__
                                                                                           , __arg_166__
                                                                                           , __arg_167__ with
                                                                                        | f , q0 , nil => (q0 :: nil)
                                                                                        | f , q0 , (x :: xs) =>
                                                                                          (match (((scanr f) q0)
                                                                                                   xs) with
                                                                                            | ((q :: _) as qs) => (((f
                                                                                                                  x) q)
                                                                                                                  :: qs)
                                                                                          end)
                                                                                      end)).

Definition scanl {a} {b} : (((a -> (b -> a))) -> (a -> ((list b) -> (list
                           a)))) := (fix scanl __arg_155__ __arg_156__ __arg_157__ := (match __arg_155__
                                                                                           , __arg_156__
                                                                                           , __arg_157__ with
                                                                                        | f , q , xs => (q ::
                                                                                                        ((match xs with
                                                                                                          | nil => nil
                                                                                                          | (x :: xs) =>
                                                                                                            (((scanl f)
                                                                                                            (((f q) x)))
                                                                                                            xs)
                                                                                                        end)))
                                                                                      end)).

Definition scanl1 {a} : (((a -> (a -> a))) -> ((list a) -> (list a))) :=
  (fun __arg_158__
       __arg_159__ =>
    (match __arg_158__ , __arg_159__ with
      | f , (x :: xs) => (((scanl f) x) xs)
      | _ , nil => nil
    end)).

Definition repeat {a} : (a -> (list a)) := (fun __arg_172__ =>
                                             (match __arg_172__ with
                                               | x => (let xs := (x :: xs)
                                                      in xs)
                                             end)).

Definition replicate {a} : (Int -> (a -> (list a))) := (fun __arg_173__
                                                            __arg_174__ =>
                                                         (match __arg_173__ , __arg_174__ with
                                                           | n , x => ((take n) ((repeat x)))
                                                         end)).

Definition realToFrac {a} {b} `{(Real a)} `{(Fractional b)} : (a -> b) :=
  (fromRational ∘ toRational).

Definition reads {a} `{((Read a))} : (ReadS a) := (readsPrec 0).

Definition readParen {a} : (bool -> ((ReadS a) -> (ReadS a))) :=
  (fun __arg_220__
       __arg_221__ =>
    (match __arg_220__ , __arg_221__ with
      | b , g => (if b
                 then mandatory
                 else optional)
    end)).

Definition readFile : (FilePath -> (IO string)) := primReadFile.

Definition putChar : (Char -> (IO unit)) := primPutChar.

Definition otherwise : bool := Mk_True.

Definition null {a} : ((list a) -> bool) := (fun __arg_146__ =>
                                              (match __arg_146__ with
                                                | nil => Mk_True
                                                | (_ :: _) => Mk_False
                                              end)).

Definition not : (bool -> bool) := (fun __arg_105__ =>
                                     (match __arg_105__ with
                                       | Mk_True => Mk_False
                                       | Mk_False => Mk_True
                                     end)).

Definition maybe {a} {b} : (b -> (((a -> b)) -> ((option a) -> b))) :=
  (fun __arg_106__
       __arg_107__
       __arg_108__ =>
    (match __arg_106__ , __arg_107__ , __arg_108__ with
      | n , f , Mk_Nothing => n
      | n , f , (Mk_Just x) => (f x)
    end)).

Definition map {a} {b} : (((a -> b)) -> ((list a) -> (list b))) := (fix map
                                                                          __arg_134__ __arg_135__ := (match __arg_134__
                                                                                                          , __arg_135__ with
                                                                                                       | f , nil => nil
                                                                                                       | f , (x ::
                                                                                                         xs) => ((f x)
                                                                                                                :: ((map
                                                                                                                f) xs))
                                                                                                     end)).

Definition lookup {a} {b} `{((Eq a))} : (a -> ((list (a * b)) -> (option b))) :=
  (fix lookup __arg_202__ __arg_203__ := (match __arg_202__ , __arg_203__ with
                                           | key , nil => Mk_Nothing
                                           | key , ((pair x y) :: xys) => (if (key == x)
                                                                          then (Mk_Just y)
                                                                          else ((lookup key) xys))
                                         end)).

Definition length {a} : ((list a) -> Int) := (fix length __arg_147__
                                                    := (match __arg_147__ with
                                                         | nil => 0
                                                         | (_ :: l) => (1 + (length l))
                                                       end)).

Definition iterate {a} : (((a -> a)) -> (a -> (list a))) := (fix iterate
                                                                   __arg_170__ __arg_171__ := (match __arg_170__
                                                                                                   , __arg_171__ with
                                                                                                | f , x => (x ::
                                                                                                           ((iterate f)
                                                                                                           ((f x))))
                                                                                              end)).

Definition numericEnumFrom {a} `{((Fractional a))} : (a -> (list a)) := (iterate
                                                                        ((fun __arg_112__ => (__arg_112__ + 1)))).

Definition numericEnumFromTo {a} `{(Fractional a)} `{(Ord a)}
  : (a -> (a -> (list a))) := (fun __arg_117__
                                   __arg_118__ =>
                                (match __arg_117__ , __arg_118__ with
                                  | n , m => ((takeWhile ((fun __arg_116__ => (__arg_116__ <= ((m + 1) / 2)))))
                                             ((numericEnumFrom n)))
                                end)).

Definition numericEnumFromThen {a} `{((Fractional a))} : (a -> (a -> (list
                                                         a))) := (fun __arg_114__
                                                                      __arg_115__ =>
                                                                   (match __arg_114__ , __arg_115__ with
                                                                     | n , m => ((iterate ((fun __arg_113__ =>
                                                                                            (__arg_113__ + ((m - n))))))
                                                                                n)
                                                                   end)).

Definition numericEnumFromThenTo {a} `{(Fractional a)} `{(Ord a)}
  : (a -> (a -> (a -> (list a)))) := (fun __arg_121__
                                          __arg_122__
                                          __arg_123__ =>
                                       (match __arg_121__ , __arg_122__ , __arg_123__ with
                                         | n , n' , m => (let p :=
                                                           (if (n' >= n)
                                                           then ((fun __arg_119__ =>
                                                                  (__arg_119__ <= ((m + ((n' - n))) / 2))))
                                                           else ((fun __arg_120__ =>
                                                                  (__arg_120__ >= ((m + ((n' - n))) / 2)))))
                                                         in ((takeWhile p) (((numericEnumFromThen n) n'))))
                                       end)).

Definition ioError {a} : (IOError -> (IO a)) := primIOError.

Definition id {a} : (a -> a) := (fun __arg_88__ =>
                                  (match __arg_88__ with
                                    | x => x
                                  end)).

Definition getContents : (IO string) := primGetContents.

Definition getChar : (IO Char) := primGetChar.

Definition fst {a} {b} : ((a * b) -> a) := (fun __arg_124__ =>
                                             (match __arg_124__ with
                                               | (pair x y) => x
                                             end)).

Definition uncurry {a} {b} {c} : (((a -> (b -> c))) -> (((a * b) -> c))) :=
  (fun __arg_129__
       __arg_130__ =>
    (match __arg_129__ , __arg_130__ with
      | f , p => ((f ((fst p))) ((snd p)))
    end)).

Definition fromIntegral {a} {b} `{(Integral a)} `{(Num b)} : (a -> b) :=
  (fromInteger ∘ toInteger).

Definition foldr {a} {b} : (((a -> (b -> b))) -> (b -> ((list a) -> b))) :=
  (fix foldr __arg_160__ __arg_161__ __arg_162__ := (match __arg_160__
                                                         , __arg_161__
                                                         , __arg_162__ with
                                                      | f , z , nil => z
                                                      | f , z , (x :: xs) => ((f x) ((((foldr f) z) xs)))
                                                    end)).

Definition or : ((list bool) -> bool) := ((foldr _||_) Mk_False).

Definition sequence {a} {m} `{(Monad m)} : ((list (m a)) -> (m (list a))) :=
  (let mcons :=
    (fun __arg_80__
         __arg_81__ =>
      (match __arg_80__ , __arg_81__ with
        | p , q => (p >>= (fun __arg_79__ =>
                     (match __arg_79__ with
                       | x => (q >>= (fun __arg_78__ =>
                                (match __arg_78__ with
                                  | y => (return_ ((x :: y)))
                                end)))
                     end)))
      end))
  in ((foldr mcons) ((return_ nil)))).

Definition mapM {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((list a) -> (m
                                           (list b)))) := (fun __arg_82__
                                                               __arg_83__ =>
                                                            (match __arg_82__ , __arg_83__ with
                                                              | f , as => (sequence (((map f) as)))
                                                            end)).

Definition sequence_ {a} {m} `{(Monad m)} : ((list (m a)) -> (m unit)) :=
  ((foldr _>>_) ((return_ tt))).

Definition mapM_ {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((list a) -> (m
                                            unit))) := (fun __arg_84__
                                                            __arg_85__ =>
                                                         (match __arg_84__ , __arg_85__ with
                                                           | f , as => (sequence_ (((map f) as)))
                                                         end)).

Definition putStr : (string -> (IO unit)) := (fun __arg_222__ =>
                                               (match __arg_222__ with
                                                 | s => ((mapM_ putChar) s)
                                               end)).

Definition putStrLn : (string -> (IO unit)) := (fun __arg_223__ =>
                                                 (match __arg_223__ with
                                                   | s => ((putStr s) >> (putStr "
                                                                                 "))
                                                 end)).

Definition print {a} `{(Show a)} : (a -> (IO unit)) := (fun __arg_224__ =>
                                                         (match __arg_224__ with
                                                           | x => (putStrLn ((show x)))
                                                         end)).

Definition unzip {a} {b} : ((list (a * b)) -> ((list a) * (list b))) := ((foldr
                                                                        ((fun __arg_213__
                                                                              __arg_214__ =>
                                                                          (match __arg_213__ , __arg_214__ with
                                                                            | (pair a b) , (pair as bs) => (pair (a ::
                                                                                                                 as) (b
                                                                                                                 :: bs))
                                                                          end)))) (pair nil nil)).

Definition unzip3 {a} {b} {c} : ((list ((a * b) * c)) -> (((list a) * (list b))
                                * (list c))) := ((foldr ((fun __arg_215__
                                                              __arg_216__ =>
                                                          (match __arg_215__ , __arg_216__ with
                                                            | (pair (pair a b) c) , (pair (pair as bs) cs) => (pair
                                                                                                              (pair (a
                                                                                                                    ::
                                                                                                                    as)
                                                                                                                    (b
                                                                                                                    ::
                                                                                                                    bs))
                                                                                                              (c :: cs))
                                                          end)))) (pair (pair nil nil) nil)).

Definition foldl {a} {b} : (((a -> (b -> a))) -> (a -> ((list b) -> a))) :=
  (fix foldl __arg_150__ __arg_151__ __arg_152__ := (match __arg_150__
                                                         , __arg_151__
                                                         , __arg_152__ with
                                                      | f , z , nil => z
                                                      | f , z , (x :: xs) => (((foldl f) (((f z) x))) xs)
                                                    end)).

Definition product {a} `{((Num a))} : ((list a) -> a) := ((foldl _*_) 1).

Definition sum {a} `{((Num a))} : ((list a) -> a) := ((foldl _+_) 0).

Definition flip {a} {b} {c} : (((a -> (b -> c))) -> (b -> (a -> c))) :=
  (fun __arg_94__
       __arg_95__
       __arg_96__ =>
    (match __arg_94__ , __arg_95__ , __arg_96__ with
      | f , x , y => ((f y) x)
    end)).

Definition reverse {a} : ((list a) -> (list a)) := ((foldl ((flip _::_))) nil).

Definition subtract {a} `{((Num a))} : (a -> (a -> a)) := (flip _-_).

Definition filter {a} : (((a -> bool)) -> ((list a) -> (list a))) := (fix filter
                                                                            __arg_138__ __arg_139__
                                                                            := (match __arg_138__ , __arg_139__ with
                                                                                 | p , nil => nil
                                                                                 | p , (x :: xs) => (if (p x)
                                                                                                    then (x :: ((filter
                                                                                                         p) xs))
                                                                                                    else ((filter p)
                                                                                                         xs))
                                                                               end)).

Definition even {a} `{((Integral a))} : (a -> bool) := (fun __arg_62__ =>
                                                         (match __arg_62__ with
                                                           | n => ((rem n 2) == 0)
                                                         end)).

Definition odd {a} `{((Integral a))} : (a -> bool) := (not ∘ even).

Definition error {a} : (string -> a) := primError.

Definition foldl1 {a} : (((a -> (a -> a))) -> ((list a) -> a)) :=
  (fun __arg_153__
       __arg_154__ =>
    (match __arg_153__ , __arg_154__ with
      | f , (x :: xs) => (((foldl f) x) xs)
      | _ , nil => (error "Prelude.foldl1: empty list")
    end)).

Definition foldr1 {a} : (((a -> (a -> a))) -> ((list a) -> a)) := (fix foldr1
                                                                         __arg_163__ __arg_164__ := (match __arg_163__
                                                                                                         , __arg_164__ with
                                                                                                      | f , (x ::
                                                                                                        nil) => x
                                                                                                      | f , (x :: xs) =>
                                                                                                        ((f x) (((foldr1
                                                                                                               f) xs)))
                                                                                                      | _ , nil =>
                                                                                                        (error
                                                                                                        "Prelude.foldr1: empty list")
                                                                                                    end)).

Definition unwords : ((list string) -> string) := (fun __arg_195__ =>
                                                    (match __arg_195__ with
                                                      | nil => ""
                                                      | ws => ((foldr1 ((fun __arg_193__
                                                                             __arg_194__ =>
                                                                         (match __arg_193__ , __arg_194__ with
                                                                           | w , s => ((w ++ (" "%char)) :: s)
                                                                         end)))) ws)
                                                    end)).

Definition gcd {a} `{((Integral a))} : (a -> (a -> a)) := (fun __arg_65__
                                                               __arg_66__ =>
                                                            (match __arg_65__ , __arg_66__ with
                                                              | 0 , 0 => (error "Prelude.gcd: gcd 0 0 is undefined")
                                                              | x , y => (let gcd' :=
                                                                           (fix gcd' __arg_63__ __arg_64__
                                                                                  := (match __arg_63__ , __arg_64__ with
                                                                                       | x , 0 => x
                                                                                       | x , y => ((gcd' y) ((rem x y)))
                                                                                     end))
                                                                         in ((gcd' ((abs x))) ((abs y))))
                                                            end)).

Definition lcm {a} `{((Integral a))} : (a -> (a -> a)) := (fun __arg_67__
                                                               __arg_68__ =>
                                                            (match __arg_67__ , __arg_68__ with
                                                              | _ , 0 => 0
                                                              | 0 , _ => 0
                                                              | x , y => (abs ((((quot x (((gcd x) y)))) * y)))
                                                            end)).

Definition head {a} : ((list a) -> a) := (fun __arg_142__ =>
                                           (match __arg_142__ with
                                             | (x :: _) => x
                                             | nil => (error "Prelude.head: empty list")
                                           end)).

Definition init {a} : ((list a) -> (list a)) := (fix init __arg_145__
                                                       := (match __arg_145__ with
                                                            | (x :: nil) => nil
                                                            | (x :: xs) => (x :: (init xs))
                                                            | nil => (error "Prelude.init: empty list")
                                                          end)).

Definition last {a} : ((list a) -> a) := (fix last __arg_144__
                                                := (match __arg_144__ with
                                                     | (x :: nil) => x
                                                     | (_ :: xs) => (last xs)
                                                     | nil => (error "Prelude.last: empty list")
                                                   end)).

Definition maximum {a} `{((Ord a))} : ((list a) -> a) := (fun __arg_204__ =>
                                                           (match __arg_204__ with
                                                             | nil => (error "Prelude.maximum: empty list")
                                                             | xs => ((foldl1 max) xs)
                                                           end)).

Definition minimum {a} `{((Ord a))} : ((list a) -> a) := (fun __arg_205__ =>
                                                           (match __arg_205__ with
                                                             | nil => (error "Prelude.minimum: empty list")
                                                             | xs => ((foldl1 min) xs)
                                                           end)).

Definition tail {a} : ((list a) -> (list a)) := (fun __arg_143__ =>
                                                  (match __arg_143__ with
                                                    | (_ :: xs) => xs
                                                    | nil => (error "Prelude.tail: empty list")
                                                  end)).

Definition undefined {a} : a := (error "Prelude.undefined").

Definition read {a} `{((Read a))} : (string -> a) := (fun __arg_217__ =>
                                                       (match __arg_217__ with
                                                         | s => undefined
                                                       end)).

Definition either {a} {b} {c} : (((a -> c)) -> (((b -> c)) -> (((Either a)
                                b) -> c))) := (fun __arg_109__
                                                   __arg_110__
                                                   __arg_111__ =>
                                                (match __arg_109__ , __arg_110__ , __arg_111__ with
                                                  | f , g , (Mk_Left x) => (f x)
                                                  | f , g , (Mk_Right y) => (g y)
                                                end)).

Definition dropWhile {a} : (((a -> bool)) -> ((list a) -> (list a))) :=
  (fix dropWhile __arg_184__ __arg_185__ := (match __arg_184__ , __arg_185__ with
                                              | p , nil => nil
                                              | p , ((x :: xs') as xs) => (if (p x)
                                                                          then ((dropWhile p) xs')
                                                                          else xs)
                                            end)).

Definition drop {a} : (Int -> ((list a) -> (list a))) := (fix drop __arg_178__
                                                                   __arg_179__ := (match __arg_178__ , __arg_179__ with
                                                                                    | n , xs => (if (n <= 0)
                                                                                                then xs
                                                                                                else _(*MissingValue*))
                                                                                    | _ , nil => nil
                                                                                    | n , (_ :: xs) => ((drop ((n - 1)))
                                                                                                       xs)
                                                                                  end)).

Definition splitAt {a} : (Int -> ((list a) -> ((list a) * (list a)))) :=
  (fun __arg_180__
       __arg_181__ =>
    (match __arg_180__ , __arg_181__ with
      | n , xs => (pair ((take n) xs) ((drop n) xs))
    end)).

Definition cycle {a} : ((list a) -> (list a)) := (fun __arg_175__ =>
                                                   (match __arg_175__ with
                                                     | nil => (error "Prelude.cycle: empty list")
                                                     | xs => (let xs' := (xs ++ xs')
                                                             in xs')
                                                   end)).

Definition curry {a} {b} {c} : ((((a * b) -> c)) -> (a -> (b -> c))) :=
  (fun __arg_126__
       __arg_127__
       __arg_128__ =>
    (match __arg_126__ , __arg_127__ , __arg_128__ with
      | f , x , y => (f (pair x y))
    end)).

Definition const {a} {b} : (a -> (b -> a)) := (fun __arg_89__
                                                   __arg_90__ =>
                                                (match __arg_89__ , __arg_90__ with
                                                  | x , _ => x
                                                end)).

Definition seq {a} {b} : (a -> (b -> b)) := (flip const).

Definition concat {a} : ((list (list a)) -> (list a)) := (fun __arg_140__ =>
                                                           (match __arg_140__ with
                                                             | xss => (((foldr _++_) nil) xss)
                                                           end)).

Definition concatMap {a} {b} : (((a -> (list b))) -> ((list a) -> (list b))) :=
  (fun __arg_141__ => (match __arg_141__ with | f => (concat ∘ (map f)) end)).

Definition unlines : ((list string) -> string) := (concatMap
                                                  ((fun __arg_192__ => (__arg_192__ ++ " ")))).

Definition catch {a} : ((IO a) -> (((IOError -> (IO a))) -> (IO a))) :=
  primCatch.

Definition break {a} : (((a -> bool)) -> ((list a) -> ((list a) * (list a)))) :=
  (fun __arg_188__ => (match __arg_188__ with | p => (span ((not ∘ p))) end)).

Definition lines : (string -> (list string)) := (fix lines __arg_190__
                                                       := (match __arg_190__ with
                                                            | "" => nil
                                                            | s => (match ((break ((fun __arg_189__ =>
                                                                                    (__arg_189__ == ("
                                                                                    "%char))))) s) with
                                                                     | (pair l s') => (l :: (match s' with
                                                                                        | nil => nil
                                                                                        | (_ :: s'') => (lines s'')
                                                                                      end))
                                                                   end)
                                                          end)).

Definition words : (string -> (list string)) := (fix words __arg_191__
                                                       := (match __arg_191__ with
                                                            | s => (match ((dropWhile _Char.isSpace_) s) with
                                                                     | "" => nil
                                                                     | s' => (match ((break _Char.isSpace_) s') with
                                                                               | (pair w s'') => (w :: (words s''))
                                                                             end)
                                                                   end)
                                                          end)).

Definition asTypeOf {a} : (a -> (a -> a)) := const.

Definition appendFile : (FilePath -> (string -> (IO unit))) := primAppendFile.

Definition any {a} : (((a -> bool)) -> ((list a) -> bool)) :=
  (fun __arg_196__ => (match __arg_196__ with | p => (or ∘ (map p)) end)).

Definition elem {a} `{((Eq a))} : (a -> ((list a) -> bool)) :=
  (fun __arg_199__ =>
    (match __arg_199__ with
      | x => (any ((fun __arg_198__ => (__arg_198__ == x))))
    end)).

Definition and : ((list bool) -> bool) := ((foldr _&&_) Mk_True).

Definition all {a} : (((a -> bool)) -> ((list a) -> bool)) :=
  (fun __arg_197__ => (match __arg_197__ with | p => (and ∘ (map p)) end)).

Definition notElem {a} `{((Eq a))} : (a -> ((list a) -> bool)) :=
  (fun __arg_201__ =>
    (match __arg_201__ with
      | x => (all ((fun __arg_200__ => (__arg_200__ /= x))))
    end)).

Definition __op_zpzp__ {a} : ((list a) -> ((list a) -> (list a))) :=
  (fix __op_zpzp__ __arg_136__ __arg_137__ := (match __arg_136__
                                                   , __arg_137__ with
                                                | nil , ys => ys
                                                | (x :: xs) , ys => (x :: ((xs ++ ys)))
                                              end)).

Infix "++" := (__op_zpzp__) (at level 99).

Notation "'_++_'" := (__op_zpzp__).

Definition __op_znzn__ {a} : ((list a) -> (Int -> a)) := (fix __op_znzn__
                                                                __arg_148__ __arg_149__ := (match __arg_148__
                                                                                                , __arg_149__ with
                                                                                             | xs , n => (if (n < 0)
                                                                                                         then (error
                                                                                                              "Prelude.!!: negative index")
                                                                                                         else _(*MissingValue*))
                                                                                             | nil , _ => (error
                                                                                                          "Prelude.!!: index too large")
                                                                                             | (x :: _) , 0 => x
                                                                                             | (_ :: xs) , n => (xs !!
                                                                                                                ((n -
                                                                                                                1)))
                                                                                           end)).

Infix "!!" := (__op_znzn__) (at level 99).

Notation "'_!!_'" := (__op_znzn__).

Definition __op_zezlzl__ {a} {b} {m} `{(Monad m)} : (((a -> (m b))) -> ((m
                                                    a) -> (m b))) := (fun __arg_86__
                                                                          __arg_87__ =>
                                                                       (match __arg_86__ , __arg_87__ with
                                                                         | f , x => (x >>= f)
                                                                       end)).

Infix "=<<" := (__op_zezlzl__) (at level 99).

Notation "'_=<<_'" := (__op_zezlzl__).

Definition __op_zdzn__ {a} {b} : (((a -> b)) -> (a -> b)) := (fun __arg_99__
                                                                  __arg_100__ =>
                                                               (match __arg_99__ , __arg_100__ with
                                                                 | f , x => (seq x (f x))
                                                               end)).

Infix "$!" := (__op_zdzn__) (at level 99).

Notation "'_$!_'" := (__op_zdzn__).

Definition __op_zd__ {a} {b} : (((a -> b)) -> (a -> b)) := (fun __arg_97__
                                                                __arg_98__ =>
                                                             (match __arg_97__ , __arg_98__ with
                                                               | f , x => (f x)
                                                             end)).

Infix "$" := (__op_zd__) (at level 99).

Notation "'_$_'" := (__op_zd__).

Definition __op_zczc__ {a} {b} `{(Fractional a)} `{(Integral b)}
  : (a -> (b -> a)) := (fun __arg_76__
                            __arg_77__ =>
                         (match __arg_76__ , __arg_77__ with
                           | x , n => (if (n >= 0)
                                      then (x ^ n)
                                      else (recip ((x ^ ((0 - n))))))
                         end)).

Infix "^^" := (__op_zczc__) (at level 99).

Notation "'_^^_'" := (__op_zczc__).

Definition __op_zc__ {a} {b} `{(Num a)} `{(Integral b)} : (a -> (b -> a)) :=
  (fun __arg_74__
       __arg_75__ =>
    (match __arg_74__ , __arg_75__ with
      | x , 0 => 1
      | x , n => (let f :=
                   (fix f __arg_71__ __arg_72__ __arg_73__ := (match __arg_71__
                                                                   , __arg_72__
                                                                   , __arg_73__ with
                                                                | _ , 0 , y => y
                                                                | x , n , y => (let g :=
                                                                                 (fix g __arg_69__ __arg_70__
                                                                                        := (match __arg_69__
                                                                                                , __arg_70__ with
                                                                                             | x , n => (if (even n)
                                                                                                        then ((g ((x *
                                                                                                                 x)))
                                                                                                             ((quot n
                                                                                                                    2)))
                                                                                                        else (((f x) ((n
                                                                                                                     -
                                                                                                                     1)))
                                                                                                             ((x * y))))
                                                                                           end))
                                                                               in ((g x) n))
                                                              end))
                 in (if (n > 0)
                    then (((f x) ((n - 1))) x)
                    else _(*MissingValue*)))
      | _ , _ => (error "Prelude.^: negative exponent")
    end)).

Infix "^" := (__op_zc__) (at level 99).

Notation "'_^_'" := (__op_zc__).

Definition __op_zbzb__ : (bool -> (bool -> bool)) := (fun __arg_103__
                                                          __arg_104__ =>
                                                       (match __arg_103__ , __arg_104__ with
                                                         | Mk_True , _ => Mk_True
                                                         | Mk_False , x => x
                                                       end)).

Infix "||" := (__op_zbzb__) (at level 99).

Notation "'_||_'" := (__op_zbzb__).

Definition __op_zaza__ : (bool -> (bool -> bool)) := (fun __arg_101__
                                                          __arg_102__ =>
                                                       (match __arg_101__ , __arg_102__ with
                                                         | Mk_True , x => x
                                                         | Mk_False , _ => Mk_False
                                                       end)).

Infix "&&" := (__op_zaza__) (at level 99).

Notation "'_&&_'" := (__op_zaza__).

Definition __op_z2218U__ {a} {b} {c}
  : (((b -> c)) -> (((a -> b)) -> (a -> c))) := (fun __arg_92__
                                                     __arg_93__ =>
                                                  (match __arg_92__ , __arg_93__ with
                                                    | f , g => (fun __arg_91__ =>
                                                                 (match __arg_91__ with
                                                                   | x => (f ((g x)))
                                                                 end))
                                                  end)).

Infix "∘" := (__op_z2218U__) (at level 99).

Notation "'_∘_'" := (__op_z2218U__).

(* Converted type class instance declarations: *)
Instance __instance__Eq_Char__225__ : (Eq Char) := {
  __op_zeze__ := (fix __op_zeze__ __arg_226__ __arg_227__ := (match __arg_226__
                                                                  , __arg_227__ with
                                                               | c , c' => ((fromEnum c) == (fromEnum c'))
                                                             end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

Instance __instance__Ord_Char__228__ : (Ord Char) := {
  __op_zlze__ := (fix __op_zlze__ __arg_229__ __arg_230__ := (match __arg_229__
                                                                  , __arg_230__ with
                                                               | c , c' => ((fromEnum c) <= (fromEnum c'))
                                                             end)) ;
  __op_zg__ := (fun __arg_12__
                    __arg_13__ =>
    (match __arg_12__ , __arg_13__ with
      | x , y => (((compare x) y) == GT)
    end)) ;
  __op_zgze__ := (fun __arg_10__
                      __arg_11__ =>
    (match __arg_10__ , __arg_11__ with
      | x , y => (((compare x) y) /= LT)
    end)) ;
  __op_zl__ := (fun __arg_8__
                    __arg_9__ =>
    (match __arg_8__ , __arg_9__ with
      | x , y => (((compare x) y) == LT)
    end)) ;
  compare := (fun __arg_4__
                  __arg_5__ =>
    (match __arg_4__ , __arg_5__ with
      | x , y => (if (x == y)
                 then EQ
                 else (if (x <= y)
                      then LT
                      else GT))
    end)) ;
  max := (fun __arg_14__
              __arg_15__ =>
    (match __arg_14__ , __arg_15__ with
      | x , y => (if (x <= y)
                 then y
                 else x)
    end)) ;
  min := (fun __arg_16__
              __arg_17__ =>
    (match __arg_16__ , __arg_17__ with
      | x , y => (if (x <= y)
                 then x
                 else y)
    end)) }.

Instance __instance__Enum_Char__231__ : (Enum Char) := {
  toEnum := primIntToChar ;
  fromEnum := primCharToInt ;
  pred := ((toEnum ∘ ((subtract 1))) ∘ fromEnum) ;
  succ := ((toEnum ∘ ((fun __arg_18__ => (__arg_18__ + 1)))) ∘ fromEnum) }.

Instance __instance__Bounded_Char__232__ : (Bounded Char) := {
  minBound := (" "%char) ;
  maxBound := primUnicodeMaxChar }.

Instance __instance__Functor_option__233__ : (Functor option) := {
  fmap := (fun __arg_234__
               __arg_235__ =>
    (match __arg_234__ , __arg_235__ with
      | f , Mk_Nothing => Mk_Nothing
      | f , (Mk_Just x) => (Mk_Just ((f x)))
    end)) }.

Instance __instance__Monad_option__236__ : (Monad option) := {
  __op_zgzgze__ := (fun __arg_237__
                        __arg_238__ =>
    (match __arg_237__ , __arg_238__ with
      | (Mk_Just x) , k => (k x)
      | Mk_Nothing , k => Mk_Nothing
    end)) ;
  return_ := Mk_Just ;
  fail := (fun __arg_239__ => (match __arg_239__ with | s => Mk_Nothing end)) ;
  __op_zgzg__ := (fun __arg_53__
                      __arg_54__ =>
    (match __arg_53__ , __arg_54__ with
      | m , k => (m >>= (fun __arg_52__ => (match __arg_52__ with | _ => k end)))
    end)) }.

Instance __instance__Functor_IO__240__ : (Functor IO) := {
  fmap := (fun __arg_241__
               __arg_242__ =>
    (match __arg_241__ , __arg_242__ with
      | f , x => (x >>= ((return_ ∘ f)))
    end)) }.

Instance __instance__Monad_IO__243__ : (Monad IO) := {
  fail := (fun __arg_244__ =>
    (match __arg_244__ with
      | s => (ioError ((userError s)))
    end)) ;
  __op_zgzg__ := (fun __arg_53__
                      __arg_54__ =>
    (match __arg_53__ , __arg_54__ with
      | m , k => (m >>= (fun __arg_52__ => (match __arg_52__ with | _ => k end)))
    end)) }.

Instance __instance__Eq_Int__245__ : (Eq Int) := {
  __op_zeze__ := (fun __arg_2__
                      __arg_3__ =>
    (match __arg_2__ , __arg_3__ with
      | x , y => (not ((x /= y)))
    end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

Instance __instance__Ord_Int__246__ : (Ord Int) := {
  __op_zg__ := (fun __arg_12__
                    __arg_13__ =>
    (match __arg_12__ , __arg_13__ with
      | x , y => (((compare x) y) == GT)
    end)) ;
  __op_zgze__ := (fun __arg_10__
                      __arg_11__ =>
    (match __arg_10__ , __arg_11__ with
      | x , y => (((compare x) y) /= LT)
    end)) ;
  __op_zl__ := (fun __arg_8__
                    __arg_9__ =>
    (match __arg_8__ , __arg_9__ with
      | x , y => (((compare x) y) == LT)
    end)) ;
  __op_zlze__ := (fun __arg_6__
                      __arg_7__ =>
    (match __arg_6__ , __arg_7__ with
      | x , y => (((compare x) y) /= GT)
    end)) ;
  compare := (fun __arg_4__
                  __arg_5__ =>
    (match __arg_4__ , __arg_5__ with
      | x , y => (if (x == y)
                 then EQ
                 else (if (x <= y)
                      then LT
                      else GT))
    end)) ;
  max := (fun __arg_14__
              __arg_15__ =>
    (match __arg_14__ , __arg_15__ with
      | x , y => (if (x <= y)
                 then y
                 else x)
    end)) ;
  min := (fun __arg_16__
              __arg_17__ =>
    (match __arg_16__ , __arg_17__ with
      | x , y => (if (x <= y)
                 then x
                 else y)
    end)) }.

Instance __instance__Num_Int__247__ : (Num Int) := {
  __op_zm__ := (fun __arg_19__
                    __arg_20__ =>
    (match __arg_19__ , __arg_20__ with
      | x , y => (x + (negate y))
    end)) ;
  negate := (fun __arg_21__ => (match __arg_21__ with | x => (0 - x) end)) }.

Instance __instance__Real_Int__248__ : (Real Int) := {}.

Instance __instance__Integral_Int__249__ : (Integral Int) := {
  div := (fun __arg_26__
              __arg_27__ =>
    (match __arg_26__ , __arg_27__ with
      | n , d => (match ((divMod n) d) with
                   | (pair q r) => q
                 end)
    end)) ;
  divMod := (fun __arg_30__
                 __arg_31__ =>
    (match __arg_30__ , __arg_31__ with
      | n , d => (match ((quotRem n) d) with
                   | ((pair q r) as qr) => (if (((signum r) == 0) - (signum d))
                                           then (pair (q - 1) (r + d))
                                           else qr)
                 end)
    end)) ;
  mod_ := (fun __arg_28__
               __arg_29__ =>
    (match __arg_28__ , __arg_29__ with
      | n , d => (match ((divMod n) d) with
                   | (pair q r) => r
                 end)
    end)) ;
  quot := (fun __arg_22__
               __arg_23__ =>
    (match __arg_22__ , __arg_23__ with
      | n , d => (match ((quotRem n) d) with
                   | (pair q r) => q
                 end)
    end)) ;
  rem := (fun __arg_24__
              __arg_25__ =>
    (match __arg_24__ , __arg_25__ with
      | n , d => (match ((quotRem n) d) with
                   | (pair q r) => r
                 end)
    end)) }.

Instance __instance__Enum_Int__250__ : (Enum Int) := {
  pred := ((toEnum ∘ ((subtract 1))) ∘ fromEnum) ;
  succ := ((toEnum ∘ ((fun __arg_18__ => (__arg_18__ + 1)))) ∘ fromEnum) }.

Instance __instance__Bounded_Int__251__ : (Bounded Int) := {}.

Instance __instance__Eq_Z__252__ : (Eq Z) := {
  __op_zeze__ := (fun __arg_2__
                      __arg_3__ =>
    (match __arg_2__ , __arg_3__ with
      | x , y => (not ((x /= y)))
    end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

Instance __instance__Ord_Z__253__ : (Ord Z) := {
  __op_zg__ := (fun __arg_12__
                    __arg_13__ =>
    (match __arg_12__ , __arg_13__ with
      | x , y => (((compare x) y) == GT)
    end)) ;
  __op_zgze__ := (fun __arg_10__
                      __arg_11__ =>
    (match __arg_10__ , __arg_11__ with
      | x , y => (((compare x) y) /= LT)
    end)) ;
  __op_zl__ := (fun __arg_8__
                    __arg_9__ =>
    (match __arg_8__ , __arg_9__ with
      | x , y => (((compare x) y) == LT)
    end)) ;
  __op_zlze__ := (fun __arg_6__
                      __arg_7__ =>
    (match __arg_6__ , __arg_7__ with
      | x , y => (((compare x) y) /= GT)
    end)) ;
  compare := (fun __arg_4__
                  __arg_5__ =>
    (match __arg_4__ , __arg_5__ with
      | x , y => (if (x == y)
                 then EQ
                 else (if (x <= y)
                      then LT
                      else GT))
    end)) ;
  max := (fun __arg_14__
              __arg_15__ =>
    (match __arg_14__ , __arg_15__ with
      | x , y => (if (x <= y)
                 then y
                 else x)
    end)) ;
  min := (fun __arg_16__
              __arg_17__ =>
    (match __arg_16__ , __arg_17__ with
      | x , y => (if (x <= y)
                 then x
                 else y)
    end)) }.

Instance __instance__Num_Z__254__ : (Num Z) := {
  __op_zm__ := (fun __arg_19__
                    __arg_20__ =>
    (match __arg_19__ , __arg_20__ with
      | x , y => (x + (negate y))
    end)) ;
  negate := (fun __arg_21__ => (match __arg_21__ with | x => (0 - x) end)) }.

Instance __instance__Real_Z__255__ : (Real Z) := {}.

Instance __instance__Integral_Z__256__ : (Integral Z) := {
  div := (fun __arg_26__
              __arg_27__ =>
    (match __arg_26__ , __arg_27__ with
      | n , d => (match ((divMod n) d) with
                   | (pair q r) => q
                 end)
    end)) ;
  divMod := (fun __arg_30__
                 __arg_31__ =>
    (match __arg_30__ , __arg_31__ with
      | n , d => (match ((quotRem n) d) with
                   | ((pair q r) as qr) => (if (((signum r) == 0) - (signum d))
                                           then (pair (q - 1) (r + d))
                                           else qr)
                 end)
    end)) ;
  mod_ := (fun __arg_28__
               __arg_29__ =>
    (match __arg_28__ , __arg_29__ with
      | n , d => (match ((divMod n) d) with
                   | (pair q r) => r
                 end)
    end)) ;
  quot := (fun __arg_22__
               __arg_23__ =>
    (match __arg_22__ , __arg_23__ with
      | n , d => (match ((quotRem n) d) with
                   | (pair q r) => q
                 end)
    end)) ;
  rem := (fun __arg_24__
              __arg_25__ =>
    (match __arg_24__ , __arg_25__ with
      | n , d => (match ((quotRem n) d) with
                   | (pair q r) => r
                 end)
    end)) }.

Instance __instance__Enum_Z__257__ : (Enum Z) := {
  pred := ((toEnum ∘ ((subtract 1))) ∘ fromEnum) ;
  succ := ((toEnum ∘ ((fun __arg_18__ => (__arg_18__ + 1)))) ∘ fromEnum) }.

Instance __instance__Eq_Float__258__ : (Eq Float) := {
  __op_zeze__ := (fun __arg_2__
                      __arg_3__ =>
    (match __arg_2__ , __arg_3__ with
      | x , y => (not ((x /= y)))
    end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

Instance __instance__Ord_Float__259__ : (Ord Float) := {
  __op_zg__ := (fun __arg_12__
                    __arg_13__ =>
    (match __arg_12__ , __arg_13__ with
      | x , y => (((compare x) y) == GT)
    end)) ;
  __op_zgze__ := (fun __arg_10__
                      __arg_11__ =>
    (match __arg_10__ , __arg_11__ with
      | x , y => (((compare x) y) /= LT)
    end)) ;
  __op_zl__ := (fun __arg_8__
                    __arg_9__ =>
    (match __arg_8__ , __arg_9__ with
      | x , y => (((compare x) y) == LT)
    end)) ;
  __op_zlze__ := (fun __arg_6__
                      __arg_7__ =>
    (match __arg_6__ , __arg_7__ with
      | x , y => (((compare x) y) /= GT)
    end)) ;
  compare := (fun __arg_4__
                  __arg_5__ =>
    (match __arg_4__ , __arg_5__ with
      | x , y => (if (x == y)
                 then EQ
                 else (if (x <= y)
                      then LT
                      else GT))
    end)) ;
  max := (fun __arg_14__
              __arg_15__ =>
    (match __arg_14__ , __arg_15__ with
      | x , y => (if (x <= y)
                 then y
                 else x)
    end)) ;
  min := (fun __arg_16__
              __arg_17__ =>
    (match __arg_16__ , __arg_17__ with
      | x , y => (if (x <= y)
                 then x
                 else y)
    end)) }.

Instance __instance__Num_Float__260__ : (Num Float) := {
  __op_zm__ := (fun __arg_19__
                    __arg_20__ =>
    (match __arg_19__ , __arg_20__ with
      | x , y => (x + (negate y))
    end)) ;
  negate := (fun __arg_21__ => (match __arg_21__ with | x => (0 - x) end)) }.

Instance __instance__Real_Float__261__ : (Real Float) := {}.

Instance __instance__Fractional_Float__262__ : (Fractional Float) := {
  __op_zs__ := (fun __arg_33__
                    __arg_34__ =>
    (match __arg_33__ , __arg_34__ with
      | x , y => (x * (recip y))
    end)) ;
  recip := (fun __arg_32__ => (match __arg_32__ with | x => (1 / x) end)) }.

Instance __instance__Floating_Float__263__ : (Floating Float) := {
  __op_ztzt__ := (fun __arg_35__
                      __arg_36__ =>
    (match __arg_35__ , __arg_36__ with
      | x , y => (exp (((log x) * y)))
    end)) ;
  logBase := (fun __arg_37__
                  __arg_38__ =>
    (match __arg_37__ , __arg_38__ with
      | x , y => ((log y) / (log x))
    end)) ;
  sqrt := (fun __arg_39__ =>
    (match __arg_39__ with
      | x => (x ** ((1 / 2)))
    end)) ;
  tan := (fun __arg_40__ =>
    (match __arg_40__ with
      | x => ((sin x) / (cos x))
    end)) ;
  tanh := (fun __arg_41__ =>
    (match __arg_41__ with
      | x => ((sinh x) / (cosh x))
    end)) }.

Instance __instance__RealFrac_Float__264__ : (RealFrac Float) := {
  ceiling := (fun __arg_44__ =>
    (match __arg_44__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r > 0)
                               then (n + 1)
                               else n)
             end)
    end)) ;
  floor := (fun __arg_45__ =>
    (match __arg_45__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r < 0)
                               then (n - 1)
                               else n)
             end)
    end)) ;
  round := (fun __arg_43__ =>
    (match __arg_43__ with
      | x => (match (properFraction x) with
               | (pair n r) => (let m := (if (r < 0) then (n - 1) else (n + 1))
                               in (match (signum (((abs r) - ((1 / 2))))) with
                                    | 1 => n
                                    | 0 => (if (even n)
                                           then n
                                           else m)
                                    | 1 => m
                                  end))
             end)
    end)) ;
  truncate := (fun __arg_42__ =>
    (match __arg_42__ with
      | x => (match (properFraction x) with
               | (pair m _) => m
             end)
    end)) }.

Instance __instance__RealFloat_Float__265__ : (RealFloat Float) := {
  atan2 := (fix atan2 __arg_50__ __arg_51__ := (match __arg_50__ , __arg_51__ with
                                                 | y , x => (if (x > 0)
                                                            then (atan ((y / x)))
                                                            else (if (((x == 0) && y) > 0)
                                                                 then (pi / 2)
                                                                 else (if (((x < 0) && y) > 0)
                                                                      then (pi + (atan ((y / x))))
                                                                      else (if ((((((x <= 0) && y) < 0)) || (((x < 0) &&
                                                                               (isNegativeZero y)))) ||
                                                                               (((isNegativeZero x) && (isNegativeZero
                                                                               y))))
                                                                           then (0 - ((atan2 ((0 - y))) x))
                                                                           else (if ((y == 0) && (((x < 0) ||
                                                                                    (isNegativeZero x))))
                                                                                then pi
                                                                                else (if (((x == 0) && y) == 0)
                                                                                     then y
                                                                                     else (x + y)))))))
                                               end)) ;
  exponent := (fun __arg_46__ =>
    (match __arg_46__ with
      | x => (match (decodeFloat x) with
               | (pair m n) => (if (m == 0)
                               then 0
                               else (n + (floatDigits x)))
             end)
    end)) ;
  scaleFloat := (fun __arg_48__
                     __arg_49__ =>
    (match __arg_48__ , __arg_49__ with
      | k , x => (match (decodeFloat x) with
                   | (pair m n) => ((encodeFloat m) ((n + k)))
                 end)
    end)) ;
  significand := (fun __arg_47__ =>
    (match __arg_47__ with
      | x => (match (decodeFloat x) with
               | (pair m _) => ((encodeFloat m) ((0 - (floatDigits x))))
             end)
    end)) }.

Instance __instance__Eq_Double__266__ : (Eq Double) := {
  __op_zeze__ := (fun __arg_2__
                      __arg_3__ =>
    (match __arg_2__ , __arg_3__ with
      | x , y => (not ((x /= y)))
    end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

Instance __instance__Ord_Double__267__ : (Ord Double) := {
  __op_zg__ := (fun __arg_12__
                    __arg_13__ =>
    (match __arg_12__ , __arg_13__ with
      | x , y => (((compare x) y) == GT)
    end)) ;
  __op_zgze__ := (fun __arg_10__
                      __arg_11__ =>
    (match __arg_10__ , __arg_11__ with
      | x , y => (((compare x) y) /= LT)
    end)) ;
  __op_zl__ := (fun __arg_8__
                    __arg_9__ =>
    (match __arg_8__ , __arg_9__ with
      | x , y => (((compare x) y) == LT)
    end)) ;
  __op_zlze__ := (fun __arg_6__
                      __arg_7__ =>
    (match __arg_6__ , __arg_7__ with
      | x , y => (((compare x) y) /= GT)
    end)) ;
  compare := (fun __arg_4__
                  __arg_5__ =>
    (match __arg_4__ , __arg_5__ with
      | x , y => (if (x == y)
                 then EQ
                 else (if (x <= y)
                      then LT
                      else GT))
    end)) ;
  max := (fun __arg_14__
              __arg_15__ =>
    (match __arg_14__ , __arg_15__ with
      | x , y => (if (x <= y)
                 then y
                 else x)
    end)) ;
  min := (fun __arg_16__
              __arg_17__ =>
    (match __arg_16__ , __arg_17__ with
      | x , y => (if (x <= y)
                 then x
                 else y)
    end)) }.

Instance __instance__Num_Double__268__ : (Num Double) := {
  __op_zm__ := (fun __arg_19__
                    __arg_20__ =>
    (match __arg_19__ , __arg_20__ with
      | x , y => (x + (negate y))
    end)) ;
  negate := (fun __arg_21__ => (match __arg_21__ with | x => (0 - x) end)) }.

Instance __instance__Real_Double__269__ : (Real Double) := {}.

Instance __instance__Fractional_Double__270__ : (Fractional Double) := {
  __op_zs__ := (fun __arg_33__
                    __arg_34__ =>
    (match __arg_33__ , __arg_34__ with
      | x , y => (x * (recip y))
    end)) ;
  recip := (fun __arg_32__ => (match __arg_32__ with | x => (1 / x) end)) }.

Instance __instance__Floating_Double__271__ : (Floating Double) := {
  __op_ztzt__ := (fun __arg_35__
                      __arg_36__ =>
    (match __arg_35__ , __arg_36__ with
      | x , y => (exp (((log x) * y)))
    end)) ;
  logBase := (fun __arg_37__
                  __arg_38__ =>
    (match __arg_37__ , __arg_38__ with
      | x , y => ((log y) / (log x))
    end)) ;
  sqrt := (fun __arg_39__ =>
    (match __arg_39__ with
      | x => (x ** ((1 / 2)))
    end)) ;
  tan := (fun __arg_40__ =>
    (match __arg_40__ with
      | x => ((sin x) / (cos x))
    end)) ;
  tanh := (fun __arg_41__ =>
    (match __arg_41__ with
      | x => ((sinh x) / (cosh x))
    end)) }.

Instance __instance__RealFrac_Double__272__ : (RealFrac Double) := {
  ceiling := (fun __arg_44__ =>
    (match __arg_44__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r > 0)
                               then (n + 1)
                               else n)
             end)
    end)) ;
  floor := (fun __arg_45__ =>
    (match __arg_45__ with
      | x => (match (properFraction x) with
               | (pair n r) => (if (r < 0)
                               then (n - 1)
                               else n)
             end)
    end)) ;
  round := (fun __arg_43__ =>
    (match __arg_43__ with
      | x => (match (properFraction x) with
               | (pair n r) => (let m := (if (r < 0) then (n - 1) else (n + 1))
                               in (match (signum (((abs r) - ((1 / 2))))) with
                                    | 1 => n
                                    | 0 => (if (even n)
                                           then n
                                           else m)
                                    | 1 => m
                                  end))
             end)
    end)) ;
  truncate := (fun __arg_42__ =>
    (match __arg_42__ with
      | x => (match (properFraction x) with
               | (pair m _) => m
             end)
    end)) }.

Instance __instance__RealFloat_Double__273__ : (RealFloat Double) := {
  atan2 := (fix atan2 __arg_50__ __arg_51__ := (match __arg_50__ , __arg_51__ with
                                                 | y , x => (if (x > 0)
                                                            then (atan ((y / x)))
                                                            else (if (((x == 0) && y) > 0)
                                                                 then (pi / 2)
                                                                 else (if (((x < 0) && y) > 0)
                                                                      then (pi + (atan ((y / x))))
                                                                      else (if ((((((x <= 0) && y) < 0)) || (((x < 0) &&
                                                                               (isNegativeZero y)))) ||
                                                                               (((isNegativeZero x) && (isNegativeZero
                                                                               y))))
                                                                           then (0 - ((atan2 ((0 - y))) x))
                                                                           else (if ((y == 0) && (((x < 0) ||
                                                                                    (isNegativeZero x))))
                                                                                then pi
                                                                                else (if (((x == 0) && y) == 0)
                                                                                     then y
                                                                                     else (x + y)))))))
                                               end)) ;
  exponent := (fun __arg_46__ =>
    (match __arg_46__ with
      | x => (match (decodeFloat x) with
               | (pair m n) => (if (m == 0)
                               then 0
                               else (n + (floatDigits x)))
             end)
    end)) ;
  scaleFloat := (fun __arg_48__
                     __arg_49__ =>
    (match __arg_48__ , __arg_49__ with
      | k , x => (match (decodeFloat x) with
                   | (pair m n) => ((encodeFloat m) ((n + k)))
                 end)
    end)) ;
  significand := (fun __arg_47__ =>
    (match __arg_47__ with
      | x => (match (decodeFloat x) with
               | (pair m _) => ((encodeFloat m) ((0 - (floatDigits x))))
             end)
    end)) }.

Instance __instance__Enum_Float__274__ : (Enum Float) := {
  succ := (fun __arg_275__ => (match __arg_275__ with | x => (x + 1) end)) ;
  pred := (fun __arg_276__ => (match __arg_276__ with | x => (x - 1) end)) ;
  toEnum := fromIntegral ;
  fromEnum := (fromInteger ∘ truncate) ;
  enumFrom := numericEnumFrom ;
  enumFromThen := numericEnumFromThen ;
  enumFromTo := numericEnumFromTo ;
  enumFromThenTo := numericEnumFromThenTo }.

Instance __instance__Enum_Double__277__ : (Enum Double) := {
  succ := (fun __arg_278__ => (match __arg_278__ with | x => (x + 1) end)) ;
  pred := (fun __arg_279__ => (match __arg_279__ with | x => (x - 1) end)) ;
  toEnum := fromIntegral ;
  fromEnum := (fromInteger ∘ truncate) ;
  enumFrom := numericEnumFrom ;
  enumFromThen := numericEnumFromThen ;
  enumFromTo := numericEnumFromTo ;
  enumFromThenTo := numericEnumFromThenTo }.

Instance __instance__Functor_list__280__ : (Functor list) := {
  fmap := map }.

Instance __instance__Monad_list__281__ : (Monad list) := {
  __op_zgzgze__ := (fun __arg_282__
                        __arg_283__ =>
    (match __arg_282__ , __arg_283__ with
      | m , k => (concat (((map k) m)))
    end)) ;
  return_ := (fun __arg_284__ => (match __arg_284__ with | x => (x :: nil) end)) ;
  fail := (fun __arg_285__ => (match __arg_285__ with | s => nil end)) ;
  __op_zgzg__ := (fun __arg_53__
                      __arg_54__ =>
    (match __arg_53__ , __arg_54__ with
      | m , k => (m >>= (fun __arg_52__ => (match __arg_52__ with | _ => k end)))
    end)) }.

Instance __instance__Show_Int__286__ : (Show Int) := {
  showsPrec := (fix showsPrec __arg_287__ := (match __arg_287__ with
                                               | n => ((showsPrec n) ∘ toInteger)
                                             end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read_Int__288__ : (Read Int) := {}.

Instance __instance__Show_Z__289__ : (Show Z) := {
  showsPrec := (showSigned showInt) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read_Z__290__ : (Read Z) := {
  readsPrec := (fun __arg_291__ =>
    (match __arg_291__ with
      | p => (readSigned readDec)
    end)) }.

Instance __instance__Show_Float__292__ : (Show Float) := {
  showsPrec := (fun __arg_293__ =>
    (match __arg_293__ with
      | p => showFloat
    end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read_Float__294__ : (Read Float) := {
  readsPrec := (fun __arg_295__ =>
    (match __arg_295__ with
      | p => (readSigned readFloat)
    end)) }.

Instance __instance__Show_Double__296__ : (Show Double) := {
  showsPrec := (fun __arg_297__ =>
    (match __arg_297__ with
      | p => showFloat
    end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read_Double__298__ : (Read Double) := {
  readsPrec := (fun __arg_299__ =>
    (match __arg_299__ with
      | p => (readSigned readFloat)
    end)) }.

Instance __instance__Show_unit__300__ : (Show unit) := {
  showsPrec := (fun __arg_301__
                    __arg_302__ =>
    (match __arg_301__ , __arg_302__ with
      | p , tt => (showString "()")
    end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read_unit__303__ : (Read unit) := {}.

Instance __instance__Show_Char__304__ : (Show Char) := {
  showsPrec := (fun __arg_305__
                    __arg_306__ =>
    (match __arg_305__ , __arg_306__ with
      | p , ("'"%char) => (showString "'\''")
      | p , c => (((showChar ("'"%char)) ∘ (showLitChar c)) ∘ (showChar ("'"%char)))
    end)) ;
  showList := (fun __arg_308__ =>
    (match __arg_308__ with
      | cs => (let showl :=
                (fix showl __arg_307__ := (match __arg_307__ with
                                            | "" => (showChar (""""%char))
                                            | ((""""%char) :: cs) => ((showString "\""") ∘ (showl cs))
                                            | (c :: cs) => ((showLitChar c) ∘ (showl cs))
                                          end))
              in ((showChar (""""%char)) ∘ (showl cs)))
    end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) }.

Instance __instance__Read_Char__309__ : (Read Char) := {}.

Instance __instance__Show__list_a___310__ : (forall {a}
                                                    `{((Show a))},
                                              (Show (list a))) := {
  showsPrec := (fun __arg_311__ => (match __arg_311__ with | p => showList end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read__list_a___312__ : (forall {a}
                                                    `{((Read a))},
                                              (Read (list a))) := {
  readsPrec := (fun __arg_313__ =>
    (match __arg_313__ with
      | p => readList
    end)) }.

Instance __instance__Show__a___b___314__ : (forall {a}
                                                   {b}
                                                   `{(Show a)}
                                                   `{(Show b)},
                                             (Show (a * b))) := {
  showsPrec := (fun __arg_315__
                    __arg_316__ =>
    (match __arg_315__ , __arg_316__ with
      | p , (pair x y) => (((((showChar ("("%char)) ∘ (shows x)) ∘ (showChar
                          (","%char))) ∘ (shows y)) ∘ (showChar (")"%char)))
    end)) ;
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) }.

Instance __instance__Read__a___b___317__ : (forall {a}
                                                   {b}
                                                   `{(Read a)}
                                                   `{(Read b)},
                                             (Read (a * b))) := {}.

Instance __instance__Show_IOError__318__ : (Show IOError) := {
  show := (fun __arg_59__ =>
    (match __arg_59__ with
      | x => (((showsPrec 0) x) "")
    end)) ;
  showList := (fun __arg_61__ =>
    (match __arg_61__ with
      | nil => (showString "[]")
      | (x :: xs) => (let showl :=
                       (fix showl __arg_60__ := (match __arg_60__ with
                                                  | nil => (showChar ("]"%char))
                                                  | (x :: xs) => (((showChar (","%char)) ∘ (shows x)) ∘ (showl xs))
                                                end))
                     in (((showChar ("["%char)) ∘ (shows x)) ∘ (showl xs)))
    end)) ;
  showsPrec := (fun __arg_56__
                    __arg_57__
                    __arg_58__ =>
    (match __arg_56__ , __arg_57__ , __arg_58__ with
      | _ , x , s => ((show x) ++ s)
    end)) }.

Instance __instance__Eq_IOError__319__ : (Eq IOError) := {
  __op_zeze__ := (fun __arg_2__
                      __arg_3__ =>
    (match __arg_2__ , __arg_3__ with
      | x , y => (not ((x /= y)))
    end)) ;
  __op_zsze__ := (fun __arg_0__
                      __arg_1__ =>
    (match __arg_0__ , __arg_1__ with
      | x , y => (not ((x == y)))
    end)) }.

(* Unbound variables:
     !! * ++ :: EQ GT LT Rational Z ^ _&&_ _(,)_ _(,,)_ _++_ _::_ _Char.isSpace_ _||_
     bool list mandatory nil option optional pair primAppendFile primCatch
     primCharToInt primError primGetChar primGetContents primIOError primIntToChar
     primPutChar primReadFile primUnicodeMaxChar primUserError primWriteFile readDec
     readFloat readSigned showFloat showInt showLitChar showSigned string tt unit xs
     xs' ∘
*)
