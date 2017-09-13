(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Char.
Require Import GHC.Num.

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Converted data type declarations: *)
(* Note: we will only be able to make instances of this class for bounded types. *)
Class Enum a := {
  enumFrom : (a -> (list a)) ;
  enumFromThen : (a -> (a -> (list a))) ;
  enumFromThenTo : (a -> (a -> (a -> (list a)))) ;
  enumFromTo : (a -> (a -> (list a))) ;
  fromEnum : (a -> Int) ;
  pred : (a -> a) ;
  succ : (a -> a) ;
  toEnum : (Int -> a) }.

Class Bounded a := {
  maxBound : a ;
  minBound : a }.

(* Converted value declarations: *)
(*
Definition up_list : (Z -> (Z -> (Z -> (list Z)))) :=
(fun arg_134__
   arg_135__
   arg_136__ =>
   (match arg_134__ , arg_135__ , arg_136__ with
    | x0 , delta , lim => (let go :=
                              (fix go arg_133__
                               := (match arg_133__ with
                                   | x => (if (x >? lim)
                                          then nil
                                          else (x :: (go ((x
                                                           +
                                                           delta)))))
                                   end))
                          in (go ((x0 : Z))))
    end)).

Definition up_fb {a} : (((Z -> (a -> a))) -> (a -> (Z -> (Z -> (Z -> a))))) :=
  (fun arg_122__
       arg_123__
       arg_124__
       arg_125__
       arg_126__ =>
    (match arg_122__ , arg_123__ , arg_124__ , arg_125__ , arg_126__ with
      | c , n , x0 , delta , lim => (let go :=
                                      (fix go arg_121__ := (match arg_121__ with
                                                             | x => (if (x >? lim)
                                                                    then n
                                                                    else (c x (go ((x + delta)))))
                                                           end))
                                    in (go ((x0 : Z))))
    end)).


Definition toEnumError {a} {b} `{((Show a))} : (String -> (Int -> ((a *
                                               a) -> b))) := (fun arg_12__
                                                                  arg_13__
                                                                  arg_14__ =>
                                                               (match arg_12__ , arg_13__ , arg_14__ with
                                                                 | inst_ty , i , bnds => ((((((errorWithoutStackTrace $
                                                                                         &"Enum.toEnum{") ++ inst_ty) ++
                                                                                         &"}: tag (") ++ (show i)) ++
                                                                                         &") is outside of bounds ") ++
                                                                                         (show bnds))
                                                               end)).
*)
Definition succError {a} : (String -> a) :=
(fun arg_17__ =>
   (match arg_17__ with
    | inst_ty => errorWithoutStackTrace ( &"Enum.succ{" ++ inst_ty ++ &"}: tried to take `succ' of maxBound")
    end)).

Definition predError {a} : (String -> a) :=
(fun arg_18__ =>
   (match arg_18__ with
    | inst_ty => errorWithoutStackTrace ( &"Enum.pred{" ++ inst_ty ++ &"}: tried to take `pred' of minBound" )
    end)).

(* haha *)
Definition maxIntWord : N := N.pow 2%N 31%N.


(*
Definition go_up_char_list : (Int# -> (Int# -> (Int# -> String))) :=
  (fun arg_32__
       arg_33__
       arg_34__ =>
    (match arg_32__ , arg_33__ , arg_34__ with
      | x0 , delta , lim => (let go_up :=
                              (fix go_up arg_31__ := (match arg_31__ with
                                                       | x => (if (_isTrue#_ ((x >?# lim)))
                                                              then nil
                                                              else ((_C#_ ((_chr#_ x))) :: (go_up ((x +# delta)))))
                                                     end))
                            in (go_up x0))
    end)).

Definition go_up_char_fb {a}
  : (((Char -> (a -> a))) -> (a -> (Int# -> (Int# -> (Int# -> a))))) :=
  (fun arg_20__
       arg_21__
       arg_22__
       arg_23__
       arg_24__ =>
    (match arg_20__ , arg_21__ , arg_22__ , arg_23__ , arg_24__ with
      | c , n , x0 , delta , lim => (let go_up :=
                                      (fix go_up arg_19__ := (match arg_19__ with
                                                               | x => (if (_isTrue#_ ((x >?# lim)))
                                                                      then n
                                                                      else (c (_C#_ ((_chr#_ x))) (go_up ((x +#
                                                                                                         delta)))))
                                                             end))
                                    in (go_up x0))
    end)).

Definition go_dn_char_list : (Int# -> (Int# -> (Int# -> String))) :=
  (fun arg_36__
       arg_37__
       arg_38__ =>
    (match arg_36__ , arg_37__ , arg_38__ with
      | x0 , delta , lim => (let go_dn :=
                              (fix go_dn arg_35__ := (match arg_35__ with
                                                       | x => (if (_isTrue#_ ((x <# lim)))
                                                              then nil
                                                              else ((_C#_ ((_chr#_ x))) :: (go_dn ((x +# delta)))))
                                                     end))
                            in (go_dn x0))
    end)).

Definition go_dn_char_fb {a}
  : (((Char -> (a -> a))) -> (a -> (Int# -> (Int# -> (Int# -> a))))) :=
  (fun arg_26__
       arg_27__
       arg_28__
       arg_29__
       arg_30__ =>
    (match arg_26__ , arg_27__ , arg_28__ , arg_29__ , arg_30__ with
      | c , n , x0 , delta , lim => (let go_dn :=
                                      (fix go_dn arg_25__ := (match arg_25__ with
                                                               | x => (if (_isTrue#_ ((x <# lim)))
                                                                      then n
                                                                      else (c (_C#_ ((_chr#_ x))) (go_dn ((x +#
                                                                                                         delta)))))
                                                             end))
                                    in (go_dn x0))
    end)).

Definition fromEnumError {a} {b} `{((Show a))} : (String -> (a -> b)) :=
  (fun arg_15__
       arg_16__ =>
    (match arg_15__ , arg_16__ with
      | inst_ty , x => ((((((errorWithoutStackTrace $ &"Enum.fromEnum{") ++ inst_ty)
                       ++ &"}: value (") ++ (show x)) ++ &") is outside of Int's bounds ") ++ (show
                       (pair (minBound : Int) (maxBound : Int))))
    end)).
*)
(*
Definition enumDeltaToInteger1FB {a}
  : (((Z -> (a -> a))) -> (a -> (Z -> (Z -> a)))) :=
  (fun arg_111__
     arg_112__
     arg_113__
     arg_114__ =>
     (match arg_111__ , arg_112__ , arg_113__ , arg_114__ with
      | c , n , x0 , lim => (let go :=
                                (fix go arg_110__
                                 := (match arg_110__ with
                                     | x => (if (x >? lim)
                                            then n
                                            else (c x (go ((x + #1)))))
                                     end))
                            in (go ((x0 : Z))))
      end)).

Definition enumDeltaToInteger1 : (Z -> (Z -> (list Z))) := (fun arg_119__
                                                                arg_120__ =>
                                                             (match arg_119__ , arg_120__ with
                                                               | x0 , lim => (let go :=
                                                                               (fix go arg_118__
                                                                                      := (match arg_118__ with
                                                                                           | x => (if (x >? lim)
                                                                                                  then nil
                                                                                                  else (x :: (go ((x +
                                                                                                                 #1)))))
                                                                                         end))
                                                                             in (go ((x0 : Z))))
                                                             end)).

Definition enumDeltaIntegerFB {b} : (((Z -> (b -> b))) -> (Z -> (Z -> b))) :=
  (fun arg_100__
       arg_101__
       arg_102__ =>
    (match arg_100__ , arg_101__ , arg_102__ with
      | c , x0 , d => (let go :=
                        (fix go arg_99__ := (match arg_99__ with
                                              | x => (seq x ((c x (go ((x + d))))))
                                            end))
                      in (go x0))
    end)).

Definition enumDeltaInteger : (Z -> (Z -> (list Z))) := (fix enumDeltaInteger
                                                               arg_103__ arg_104__ := (match arg_103__ , arg_104__ with
                                                                                        | x , d => (seq x ((x ::
                                                                                                        ((enumDeltaInteger
                                                                                                        ((x + d))) d))))
                                                                                      end)).
*)
(*
(* Translating `eftWordFB' failed: `Word#' literals unsupported *)

Axiom eftWordFB : (forall {A : Type}, A).

(* Translating `eftWord' failed: `Word#' literals unsupported *)

Axiom eftWord : (forall {A : Type}, A).

(* Translating `eftIntFB' failed: `Int#' literals unsupported *)

Axiom eftIntFB : (forall {A : Type}, A).

(* Translating `eftInt' failed: `Int#' literals unsupported *)

Axiom eftInt : (forall {A : Type}, A).

(* Translating `eftCharFB' failed: `Int#' literals unsupported *)

Axiom eftCharFB : (forall {A : Type}, A).

(* Translating `eftChar' failed: `Int#' literals unsupported *)

Axiom eftChar : (forall {A : Type}, A).

Definition efdtWordUpFB {r}
  : (((N -> (r -> r))) -> (r -> (Word# -> (Word# -> (Word# -> r))))) :=
  (fun arg_84__
       arg_85__
       arg_86__
       arg_87__
       arg_88__ =>
    (match arg_84__ , arg_85__ , arg_86__ , arg_87__ , arg_88__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((y ltWord# x2)))
                               then (if (_isTrue#_ ((y ltWord# x1)))
                                    then n
                                    else (c (_W#_ x1) n))
                               else (match (x2 minusWord# x1) with
                                      | delta => (match (y minusWord# delta) with
                                                   | y' => (let go_up :=
                                                             (fix go_up arg_83__ := (match arg_83__ with
                                                                                      | x => (if (_isTrue#_ ((x gtWord#
                                                                                                            y')))
                                                                                             then (c (_W#_ x) n)
                                                                                             else (c (_W#_ x) (go_up ((x
                                                                                                                     plusWord#
                                                                                                                     delta)))))
                                                                                    end))
                                                           in (c (_W#_ x1) (go_up x2)))
                                                 end)
                                    end))
    end)).

Definition efdtWordUp : (Word# -> (Word# -> (Word# -> (list N)))) :=
  (fun arg_80__
       arg_81__
       arg_82__ =>
    (match arg_80__ , arg_81__ , arg_82__ with
      | x1 , x2 , y => (if (_isTrue#_ ((y ltWord# x2)))
                       then (if (_isTrue#_ ((y ltWord# x1)))
                            then nil
                            else ((_W#_ x1) :: nil))
                       else (match (x2 minusWord# x1) with
                              | delta => (match (y minusWord# delta) with
                                           | y' => (let go_up :=
                                                     (fix go_up arg_79__ := (match arg_79__ with
                                                                              | x => (if (_isTrue#_ ((x gtWord# y')))
                                                                                     then ((_W#_ x) :: nil)
                                                                                     else ((_W#_ x) :: (go_up ((x
                                                                                                              plusWord#
                                                                                                              delta)))))
                                                                            end))
                                                   in ((_W#_ x1) :: (go_up x2)))
                                         end)
                            end))
    end)).

Definition efdtWordDnFB {r}
  : (((N -> (r -> r))) -> (r -> (Word# -> (Word# -> (Word# -> r))))) :=
  (fun arg_94__
       arg_95__
       arg_96__
       arg_97__
       arg_98__ =>
    (match arg_94__ , arg_95__ , arg_96__ , arg_97__ , arg_98__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((y gtWord# x2)))
                               then (if (_isTrue#_ ((y gtWord# x1)))
                                    then n
                                    else (c (_W#_ x1) n))
                               else (match (x2 minusWord# x1) with
                                      | delta => (match (y minusWord# delta) with
                                                   | y' => (let go_dn :=
                                                             (fix go_dn arg_93__ := (match arg_93__ with
                                                                                      | x => (if (_isTrue#_ ((x ltWord#
                                                                                                            y')))
                                                                                             then (c (_W#_ x) n)
                                                                                             else (c (_W#_ x) (go_dn ((x
                                                                                                                     plusWord#
                                                                                                                     delta)))))
                                                                                    end))
                                                           in (c (_W#_ x1) (go_dn x2)))
                                                 end)
                                    end))
    end)).

Definition efdtWordFB {r}
  : (((N -> (r -> r))) -> (r -> (Word# -> (Word# -> (Word# -> r))))) :=
  (fun arg_74__
       arg_75__
       arg_76__
       arg_77__
       arg_78__ =>
    (match arg_74__ , arg_75__ , arg_76__ , arg_77__ , arg_78__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((x2 geWord# x1)))
                               then (((((efdtWordUpFB c) n) x1) x2) y)
                               else (((((efdtWordDnFB c) n) x1) x2) y))
    end)).

Definition efdtWordDn : (Word# -> (Word# -> (Word# -> (list N)))) :=
  (fun arg_90__
       arg_91__
       arg_92__ =>
    (match arg_90__ , arg_91__ , arg_92__ with
      | x1 , x2 , y => (if (_isTrue#_ ((y gtWord# x2)))
                       then (if (_isTrue#_ ((y gtWord# x1)))
                            then nil
                            else ((_W#_ x1) :: nil))
                       else (match (x2 minusWord# x1) with
                              | delta => (match (y minusWord# delta) with
                                           | y' => (let go_dn :=
                                                     (fix go_dn arg_89__ := (match arg_89__ with
                                                                              | x => (if (_isTrue#_ ((x ltWord# y')))
                                                                                     then ((_W#_ x) :: nil)
                                                                                     else ((_W#_ x) :: (go_dn ((x
                                                                                                              plusWord#
                                                                                                              delta)))))
                                                                            end))
                                                   in ((_W#_ x1) :: (go_dn x2)))
                                         end)
                            end))
    end)).

Definition efdtWord : (Word# -> (Word# -> (Word# -> (list N)))) := (fun arg_71__
                                                                        arg_72__
                                                                        arg_73__ =>
                                                                     (match arg_71__ , arg_72__ , arg_73__ with
                                                                       | x1 , x2 , y => (if (_isTrue#_ ((x2 geWord#
                                                                                                       x1)))
                                                                                        then (((efdtWordUp x1) x2) y)
                                                                                        else (((efdtWordDn x1) x2) y))
                                                                     end)).

Definition efdtIntUpFB {r}
  : (((Int -> (r -> r))) -> (r -> (Int# -> (Int# -> (Int# -> r))))) :=
  (fun arg_54__
       arg_55__
       arg_56__
       arg_57__
       arg_58__ =>
    (match arg_54__ , arg_55__ , arg_56__ , arg_57__ , arg_58__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((y <# x2)))
                               then (if (_isTrue#_ ((y <# x1)))
                                    then n
                                    else (c (_I#_ x1) n))
                               else (match (x2 -# x1) with
                                      | delta => (match (y -# delta) with
                                                   | y' => (let go_up :=
                                                             (fix go_up arg_53__ := (match arg_53__ with
                                                                                      | x => (if (_isTrue#_ ((x >?# y')))
                                                                                             then (c (_I#_ x) n)
                                                                                             else (c (_I#_ x) (go_up ((x
                                                                                                                     +#
                                                                                                                     delta)))))
                                                                                    end))
                                                           in (c (_I#_ x1) (go_up x2)))
                                                 end)
                                    end))
    end)).

Definition efdtIntUp : (Int# -> (Int# -> (Int# -> (list Int)))) := (fun arg_50__
                                                                        arg_51__
                                                                        arg_52__ =>
                                                                     (match arg_50__ , arg_51__ , arg_52__ with
                                                                       | x1 , x2 , y => (if (_isTrue#_ ((y <# x2)))
                                                                                        then (if (_isTrue#_ ((y <# x1)))
                                                                                             then nil
                                                                                             else ((_I#_ x1) :: nil))
                                                                                        else (match (x2 -# x1) with
                                                                                               | delta => (match (y -#
                                                                                                                   delta) with
                                                                                                            | y' =>
                                                                                                              (let go_up :=
                                                                                                                (fix go_up
                                                                                                                       arg_49__
                                                                                                                       := (match arg_49__ with
                                                                                                                            | x =>
                                                                                                                              (if (_isTrue#_
                                                                                                                                  ((x
                                                                                                                                  >?#
                                                                                                                                  y')))
                                                                                                                              then ((_I#_
                                                                                                                                   x)
                                                                                                                                   ::
                                                                                                                                   nil)
                                                                                                                              else ((_I#_
                                                                                                                                   x)
                                                                                                                                   ::
                                                                                                                                   (go_up
                                                                                                                                   ((x
                                                                                                                                   +#
                                                                                                                                   delta)))))
                                                                                                                          end))
                                                                                                              in ((_I#_
                                                                                                                 x1) ::
                                                                                                                 (go_up
                                                                                                                 x2)))
                                                                                                          end)
                                                                                             end))
                                                                     end)).

Definition efdtIntDnFB {r}
  : (((Int -> (r -> r))) -> (r -> (Int# -> (Int# -> (Int# -> r))))) :=
  (fun arg_64__
       arg_65__
       arg_66__
       arg_67__
       arg_68__ =>
    (match arg_64__ , arg_65__ , arg_66__ , arg_67__ , arg_68__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((y ># x2)))
                               then (if (_isTrue#_ ((y ># x1)))
                                    then n
                                    else (c (_I#_ x1) n))
                               else (match (x2 -# x1) with
                                      | delta => (match (y -# delta) with
                                                   | y' => (let go_dn :=
                                                             (fix go_dn arg_63__ := (match arg_63__ with
                                                                                      | x => (if (_isTrue#_ ((x <# y')))
                                                                                             then (c (_I#_ x) n)
                                                                                             else (c (_I#_ x) (go_dn ((x
                                                                                                                     +#
                                                                                                                     delta)))))
                                                                                    end))
                                                           in (c (_I#_ x1) (go_dn x2)))
                                                 end)
                                    end))
    end)).

Definition efdtIntFB {r}
  : (((Int -> (r -> r))) -> (r -> (Int# -> (Int# -> (Int# -> r))))) :=
  (fun arg_44__
       arg_45__
       arg_46__
       arg_47__
       arg_48__ =>
    (match arg_44__ , arg_45__ , arg_46__ , arg_47__ , arg_48__ with
      | c , n , x1 , x2 , y => (if (_isTrue#_ ((x2 >=# x1)))
                               then (((((efdtIntUpFB c) n) x1) x2) y)
                               else (((((efdtIntDnFB c) n) x1) x2) y))
    end)).

Definition efdtIntDn : (Int# -> (Int# -> (Int# -> (list Int)))) := (fun arg_60__
                                                                        arg_61__
                                                                        arg_62__ =>
                                                                     (match arg_60__ , arg_61__ , arg_62__ with
                                                                       | x1 , x2 , y => (if (_isTrue#_ ((y ># x2)))
                                                                                        then (if (_isTrue#_ ((y ># x1)))
                                                                                             then nil
                                                                                             else ((_I#_ x1) :: nil))
                                                                                        else (match (x2 -# x1) with
                                                                                               | delta => (match (y -#
                                                                                                                   delta) with
                                                                                                            | y' =>
                                                                                                              (let go_dn :=
                                                                                                                (fix go_dn
                                                                                                                       arg_59__
                                                                                                                       := (match arg_59__ with
                                                                                                                            | x =>
                                                                                                                              (if (_isTrue#_
                                                                                                                                  ((x
                                                                                                                                  <#
                                                                                                                                  y')))
                                                                                                                              then ((_I#_
                                                                                                                                   x)
                                                                                                                                   ::
                                                                                                                                   nil)
                                                                                                                              else ((_I#_
                                                                                                                                   x)
                                                                                                                                   ::
                                                                                                                                   (go_dn
                                                                                                                                   ((x
                                                                                                                                   +#
                                                                                                                                   delta)))))
                                                                                                                          end))
                                                                                                              in ((_I#_
                                                                                                                 x1) ::
                                                                                                                 (go_dn
                                                                                                                 x2)))
                                                                                                          end)
                                                                                             end))
                                                                     end)).

Definition efdtInt : (Int# -> (Int# -> (Int# -> (list Int)))) := (fun arg_41__
                                                                      arg_42__
                                                                      arg_43__ =>
                                                                   (match arg_41__ , arg_42__ , arg_43__ with
                                                                     | x1 , x2 , y => (if (_isTrue#_ ((x2 >=# x1)))
                                                                                      then (((efdtIntUp x1) x2) y)
                                                                                      else (((efdtIntDn x1) x2) y))
                                                                   end)).

(* Translating `efdtCharFB' failed: `Int#' literals unsupported *)

Axiom efdtCharFB : (forall {A : Type}, A).

(* Translating `efdtChar' failed: `Int#' literals unsupported *)

Axiom efdtChar : (forall {A : Type}, A).

Definition efdWord : (Word# -> (Word# -> (list N))) := (fun arg_69__
                                                            arg_70__ =>
                                                         (match arg_69__ , arg_70__ with
                                                           | x1 , x2 => (if (_isTrue#_ ((x2 geWord# x1)))
                                                                        then (match maxBound with
                                                                               | (W# y) => (((efdtWordUp x1) x2) y)
                                                                             end)
                                                                        else (match minBound with
                                                                               | (W# y) => (((efdtWordDn x1) x2) y)
                                                                             end))
                                                         end)).

Definition efdInt : (Int# -> (Int# -> (list Int))) := (fun arg_39__
                                                           arg_40__ =>
                                                        (match arg_39__ , arg_40__ with
                                                          | x1 , x2 => (if (_isTrue#_ ((x2 >=# x1)))
                                                                       then (match maxInt with
                                                                              | (I# y) => (((efdtIntUp x1) x2) y)
                                                                            end)
                                                                       else (match minInt with
                                                                              | (I# y) => (((efdtIntDn x1) x2) y)
                                                                            end))
                                                        end)).

(* Translating `efdCharFB' failed: `Int#' literals unsupported *)

Axiom efdCharFB : (forall {A : Type}, A).

(* Translating `efdChar' failed: `Int#' literals unsupported *)

Axiom efdChar : (forall {A : Type}, A).

Definition dn_list : (Z -> (Z -> (Z -> (list Z)))) := (fun arg_138__
                                                           arg_139__
                                                           arg_140__ =>
                                                        (match arg_138__ , arg_139__ , arg_140__ with
                                                          | x0 , delta , lim => (let go :=
                                                                                  (fix go arg_137__
                                                                                         := (match arg_137__ with
                                                                                              | x => (if (x < lim)
                                                                                                     then nil
                                                                                                     else (x :: (go ((x
                                                                                                                    +
                                                                                                                    delta)))))
                                                                                            end))
                                                                                in (go ((x0 : Z))))
                                                        end)).

Definition enumDeltaToInteger : (Z -> (Z -> (Z -> (list Z)))) := (fun arg_115__
                                                                      arg_116__
                                                                      arg_117__ =>
                                                                   (match arg_115__ , arg_116__ , arg_117__ with
                                                                     | x , delta , lim => (if (delta >= #0)
                                                                                          then (((up_list x) delta) lim)
                                                                                          else (((dn_list x) delta)
                                                                                               lim))
                                                                   end)).

Definition dn_fb {a} : (((Z -> (a -> a))) -> (a -> (Z -> (Z -> (Z -> a))))) :=
  (fun arg_128__
       arg_129__
       arg_130__
       arg_131__
       arg_132__ =>
    (match arg_128__ , arg_129__ , arg_130__ , arg_131__ , arg_132__ with
      | c , n , x0 , delta , lim => (let go :=
                                      (fix go arg_127__ := (match arg_127__ with
                                                             | x => (if (x < lim)
                                                                    then n
                                                                    else (c x (go ((x + delta)))))
                                                           end))
                                    in (go ((x0 : Z))))
    end)).

Definition enumDeltaToIntegerFB {a}
  : (((Z -> (a -> a))) -> (a -> (Z -> (Z -> (Z -> a))))) := (fun arg_105__
                                                                 arg_106__
                                                                 arg_107__
                                                                 arg_108__
                                                                 arg_109__ =>
                                                              (match arg_105__
                                                                   , arg_106__
                                                                   , arg_107__
                                                                   , arg_108__
                                                                   , arg_109__ with
                                                                | c , n , x , delta , lim => (if (delta >= #0)
                                                                                             then (((((up_fb c) n) x)
                                                                                                  delta) lim)
                                                                                             else (((((dn_fb c) n) x)
                                                                                                  delta) lim))
                                                              end)).
*)



(* Converted type class instance declarations: *)
Instance instance__Bounded_unit__141__ : (Bounded unit) := {
  minBound := tt ;
  maxBound := tt }.

Instance instance__Enum_unit__142__ : (Enum unit) := {
  succ := (fun arg_143__ =>
    (match arg_143__ with
      | _ => (errorWithoutStackTrace &"Prelude.Enum.().succ: bad argument")
    end)) ;
  pred := (fun arg_144__ =>
    (match arg_144__ with
      | _ => (errorWithoutStackTrace &"Prelude.Enum.().pred: bad argument")
    end)) ;
  toEnum := (fun arg_145__ =>
    (match arg_145__ with
      | x => (if (x == #0)
             then tt
             else (errorWithoutStackTrace &"Prelude.Enum.().toEnum: bad argument"))
    end)) ;
  fromEnum := (fun arg_146__ => (match arg_146__ with | tt => #0 end)) ;
  enumFrom := (fun arg_147__ => (match arg_147__ with | tt => (tt :: nil) end)) ;
  enumFromThen := (fun arg_148__ arg_149__ =>
    (match arg_148__ , arg_149__ with
      | tt , tt => tt :: nil
    end)) ;
  enumFromTo := (fun arg_150__ arg_151__ =>
    (match arg_150__ , arg_151__ with
      | tt , tt => (tt :: nil)
    end)) ;
  enumFromThenTo := (fun arg_152__
                         arg_153__
                         arg_154__ =>
    (match arg_152__ , arg_153__ , arg_154__ with
      | tt , tt , tt => (tt :: nil)
    end)) }.

Instance instance__forall____Bounded_a______Bounded_b_____Bounded__a___b____155__
  : (forall `{(Bounded a)} `{(Bounded b)}, (Bounded (a * b))) := {
  minBound := (pair minBound minBound) ;
  maxBound := (pair maxBound maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c_____Bounded___a___b____c____156__
  : (forall `{(Bounded a)} `{(Bounded b)} `{(Bounded c)},
                 (Bounded ((a * b) * c))) := {
                                              minBound := (pair (pair minBound minBound) minBound) ;
                                              maxBound := (pair (pair maxBound maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d_____Bounded____a___b____c____d____157__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)},
      (Bounded (((a * b) * c) * d))) := {
  minBound := (pair (pair (pair minBound minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair maxBound maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e_____Bounded_____a___b____c____d____e____158__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)},
      (Bounded ((((a * b) * c) * d) * e))) := {
  minBound := (pair (pair (pair (pair minBound minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair maxBound maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f_____Bounded______a___b____c____d____e____f____159__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)},
      (Bounded (((((a * b) * c) * d) * e) * f))) := {
  minBound := (pair (pair (pair (pair (pair minBound minBound) minBound) minBound)
                          minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair maxBound maxBound) maxBound) maxBound)
                          maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g_____Bounded_______a___b____c____d____e____f____g____160__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)},
      (Bounded ((((((a * b) * c) * d) * e) * f) * g))) := {
  minBound := (pair (pair (pair (pair (pair (pair minBound minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair maxBound maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h_____Bounded________a___b____c____d____e____f____g____h____161__
  : forall a b c d e f g h, (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)},
      (Bounded (((((((a * b) * c) * d) * e) * f) * g) * h))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair minBound minBound)
                                                  minBound) minBound) minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair maxBound maxBound)
                                                  maxBound) maxBound) maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i_____Bounded_________a___b____c____d____e____f____g____h____i____162__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)},
      (Bounded ((((((((a * b) * c) * d) * e) * f) * g) * h) * i))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair minBound minBound)
                                                        minBound) minBound) minBound) minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair maxBound maxBound)
                                                        maxBound) maxBound) maxBound) maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j_____Bounded__________a___b____c____d____e____f____g____h____i____j____163__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)},
      (Bounded (((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair minBound
                                                                    minBound) minBound) minBound) minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair maxBound
                                                                    maxBound) maxBound) maxBound) maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k_____Bounded___________a___b____c____d____e____f____g____h____i____j____k____164__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)},
      (Bounded ((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair minBound
                                                                          minBound) minBound) minBound) minBound)
                                                  minBound) minBound) minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair maxBound
                                                                          maxBound) maxBound) maxBound) maxBound)
                                                  maxBound) maxBound) maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l_____Bounded____________a___b____c____d____e____f____g____h____i____j____k____l____165__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)},
      (Bounded (((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) *
               l))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          minBound minBound) minBound) minBound)
                                                              minBound) minBound) minBound) minBound) minBound)
                                minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          maxBound maxBound) maxBound) maxBound)
                                                              maxBound) maxBound) maxBound) maxBound) maxBound)
                                maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m_____Bounded_____________a___b____c____d____e____f____g____h____i____j____k____l____m____166__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)},
      (Bounded ((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l) *
               m))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair minBound minBound) minBound) minBound)
                                                                    minBound) minBound) minBound) minBound) minBound)
                                      minBound) minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair maxBound maxBound) maxBound) maxBound)
                                                                    maxBound) maxBound) maxBound) maxBound) maxBound)
                                      maxBound) maxBound) maxBound) maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m______Bounded_n_____Bounded______________a___b____c____d____e____f____g____h____i____j____k____l____m____n____167__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)}
            `{(Bounded n)},
      (Bounded (((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l) *
               m) * n))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair minBound minBound) minBound)
                                                                          minBound) minBound) minBound) minBound)
                                                        minBound) minBound) minBound) minBound) minBound) minBound)
                    minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair maxBound maxBound) maxBound)
                                                                          maxBound) maxBound) maxBound) maxBound)
                                                        maxBound) maxBound) maxBound) maxBound) maxBound) maxBound)
                    maxBound) }.

Instance instance__forall____Bounded_a______Bounded_b______Bounded_c______Bounded_d______Bounded_e______Bounded_f______Bounded_g______Bounded_h______Bounded_i______Bounded_j______Bounded_k______Bounded_l______Bounded_m______Bounded_n______Bounded_o_____Bounded_______________a___b____c____d____e____f____g____h____i____j____k____l____m____n____o____168__
  : (forall `{(Bounded a)}
            `{(Bounded b)}
            `{(Bounded c)}
            `{(Bounded d)}
            `{(Bounded e)}
            `{(Bounded f)}
            `{(Bounded g)}
            `{(Bounded h)}
            `{(Bounded i)}
            `{(Bounded j)}
            `{(Bounded k)}
            `{(Bounded l)}
            `{(Bounded m)}
            `{(Bounded n)}
            `{(Bounded o)},
      (Bounded ((((((((((((((a * b) * c) * d) * e) * f) * g) * h) * i) * j) * k) * l)
               * m) * n) * o))) := {
  minBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair (pair minBound minBound) minBound)
                                                                                minBound) minBound) minBound) minBound)
                                                              minBound) minBound) minBound) minBound) minBound)
                                minBound) minBound) minBound) ;
  maxBound := (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                          (pair (pair (pair maxBound maxBound) maxBound)
                                                                                maxBound) maxBound) maxBound) maxBound)
                                                              maxBound) maxBound) maxBound) maxBound) maxBound)
                                maxBound) maxBound) maxBound) }.
Definition minInt := Z.opp (Z.pow 2%Z 32%Z).
Definition maxInt := Z.pow 2%Z 32%Z.
Instance instance__Bounded_Int__183__ : (Bounded Int) := {
  minBound := minInt ;
  maxBound := maxInt }.

Inductive eftInt_aux_fuel : Int -> Int -> Prop :=
  | done : forall x y, (x >? y)%Z = true -> eftInt_aux_fuel x y
  | step : forall x y, eftInt_aux_fuel (x + 1)%Z y -> eftInt_aux_fuel x y.

Program Fixpoint eftInt_aux  (x : Int) (y: Int) (d : eftInt_aux_fuel x y) {struct d} : list Int :=
  match (x >? y)%Z with
    | true => nil
    | false => @eftInt_aux (x + 1)%Z y _
  end.
Obligation 1.
destruct d. rewrite H in Heq_anonymous. done. auto. Defined.

Lemma eftInt_fuel : forall (x:Int) (y:Int), eftInt_aux_fuel x y.
Proof.
  intros x y.
Admitted.

Definition eftInt := fun x y => eftInt_aux (eftInt_fuel x y).

Inductive efdtInt_aux_fuel : Int -> Int -> Int -> Prop :=
  | efdt_done : forall x y z, (x >? z)%Z = true -> efdtInt_aux_fuel x y z
  | efdt_step : forall x y z, efdtInt_aux_fuel (x + y)%Z y z -> efdtInt_aux_fuel x y z.

Program Fixpoint efdtInt_aux  (x : Int) (y: Int) (z:Int) (d : efdtInt_aux_fuel x y z) {struct d} : list Int :=
  match (x >? z)%Z with
    | true => nil
    | false => @efdtInt_aux (x + y)%Z y z _
  end.
Obligation 1.
destruct d. rewrite H in Heq_anonymous. done. auto. Defined.

Lemma efdtInt_fuel : forall (x:Int) (y:Int) (z:Int), efdtInt_aux_fuel x y z.
Proof.
  intros x y z.
Admitted.

Definition efdtInt := fun x y z => efdtInt_aux (efdtInt_fuel x y z).


Instance instance__Enum_Int__184__ : (Enum Int) := {
  succ := (fun arg_185__ =>
    (match arg_185__ with
      | x => (if (x == maxBound)
             then (errorWithoutStackTrace
                  &"Prelude.Enum.succ{Int}: tried to take `succ' of maxBound")
             else (x + #1))
    end)) ;
  pred := (fun arg_186__ =>
    (match arg_186__ with
      | x => (if (x == minBound)
             then (errorWithoutStackTrace
                  &"Prelude.Enum.pred{Int}: tried to take `pred' of minBound")
             else (x - #1))
    end)) ;
  toEnum := (fun arg_187__ => (match arg_187__ with | x => x end)) ;
  fromEnum := (fun arg_188__ => (match arg_188__ with | x => x end)) ;
  enumFrom := (fun x => eftInt x maxInt) ;
  enumFromTo := eftInt ;
  enumFromThen := fun x y => efdtInt x y maxInt ;
  enumFromThenTo := fun x1 x2 y => (((efdtInt x1) x2) y)
}.


Definition boundedEnumFrom {a} `{(Bounded a)}
  (fromEnum : a -> Int)
  (toEnum   : Int -> a)
: (a -> (list a)) :=
  (fun arg_9__ =>
    (match arg_9__ with
      | n => ((map toEnum) (enumFromTo (fromEnum n) (fromEnum ((asTypeOf maxBound
                                                                         n)))))
    end)).


Definition boundedEnumFromThen {a} `{(Bounded a)}
  (fromEnum : a -> Int)
  (toEnum   : Int -> a)
  : (a -> (a -> (list a))) :=
  (fun arg_10__  arg_11__ =>
     (match arg_10__ , arg_11__ with
      | n1 , n2 => (let i_n1 := (fromEnum n1)
                   in (let i_n2 := (fromEnum n2)
                       in (if (i_n2 >=? i_n1)
                           then ((map toEnum) (enumFromThenTo i_n1 i_n2 (fromEnum ((asTypeOf maxBound n1)))))
                           else ((map toEnum) (enumFromThenTo i_n1 i_n2 (fromEnum ((asTypeOf minBound n1))))))))
      end)).



Instance instance__Bounded_bool__169__ : (Bounded bool) := {
  minBound := false ;
  maxBound := true }.

Definition toEnumBool : Int -> bool :=  (fun arg_173__ =>
    (match arg_173__ with
      | n => (if (n == #0)
             then false
             else (if (n == #1)
                  then true
                  else (errorWithoutStackTrace &"Prelude.Enum.Bool.toEnum: bad argument")))
    end)).
Definition fromEnumBool : bool -> Int :=
(fun arg_174__ =>
    (match arg_174__ with
      | false => #0
      | true => #1
    end)).
Instance instance__Enum_bool__170__ : (Enum bool) := {
  succ := (fun arg_171__ =>
    (match arg_171__ with
      | false => true
      | true => (errorWithoutStackTrace &"Prelude.Enum.Bool.succ: bad argument")
    end)) ;
  pred := (fun arg_172__ =>
    (match arg_172__ with
      | true => false
      | false => (errorWithoutStackTrace &"Prelude.Enum.Bool.pred: bad argument")
    end)) ;
  toEnum := toEnumBool ;
  fromEnum := fromEnumBool ;
  enumFrom := boundedEnumFrom fromEnumBool toEnumBool;
  enumFromThen := boundedEnumFromThen fromEnumBool toEnumBool ;
  enumFromThenTo := (fix enumFromThenToBool arg_6__ arg_7__ arg_8__ := (match arg_6__
                                                                        , arg_7__
                                                                        , arg_8__ with
                                                                     | x1 , x2 , y => ((map toEnumBool) (efdtInt
                                                                                                    (fromEnumBool x1)
                                                                                                    (fromEnumBool x2)
                                                                                                    (fromEnumBool y)))
                                                                   end)) ;
  enumFromTo := (fix enumFromTo arg_4__ arg_5__ := (match arg_4__ , arg_5__ with
                                                     | x , y => ((map toEnumBool) (eftInt (fromEnumBool x) (fromEnumBool y)))
                                                   end)) }.

Instance instance__Bounded_comparison__175__ : (Bounded comparison) := {
  minBound := Lt ;
  maxBound := Gt }.

Definition fromEnum_comparison : comparison -> Int:=
 (fun arg_180__ =>
    (match arg_180__ with
      | Lt => #0
      | Eq => #1
      | Gt => #2
    end)).
Definition toEnum_comparison : Int -> comparison :=
  fun n =>
    (if (n == #0)
     then Lt
     else (if (n == #1)
           then Eq
           else (if (n == #2)
                 then Gt
                 else (errorWithoutStackTrace &"Prelude.Enum.Ordering.toEnum: bad argument")
    ))).

Instance instance__Enum_comparison__176__ : (Enum comparison) := {
  succ := (fun arg_177__ =>
    (match arg_177__ with
      | Lt => Eq
      | Eq => Gt
      | Gt => (errorWithoutStackTrace &"Prelude.Enum.Ordering.succ: bad argument")
    end)) ;
  pred := (fun arg_178__ =>
    (match arg_178__ with
      | Gt => Eq
      | Eq => Lt
      | Lt => (errorWithoutStackTrace &"Prelude.Enum.Ordering.pred: bad argument")
    end)) ;
  toEnum := toEnum_comparison ;
  fromEnum := fromEnum_comparison ;
  enumFrom := boundedEnumFrom fromEnum_comparison toEnum_comparison;
  enumFromThen := boundedEnumFromThen fromEnum_comparison toEnum_comparison;
  enumFromThenTo := (fix enumFromThenTo_comparison arg_6__ arg_7__ arg_8__ := (match arg_6__
                                                                        , arg_7__
                                                                        , arg_8__ with
                                                                     | x1 , x2 , y => ((map toEnum_comparison) (enumFromThenTo
                                                                                                      (fromEnum_comparison x1)
                                                                                                      (fromEnum_comparison x2)
                                                                                                      (fromEnum_comparison y)))
                                                                   end)) ;
  enumFromTo := (fix enumFromTo_comparison arg_4__ arg_5__ := (match arg_4__ , arg_5__ with
                                                               | x , y => ((map toEnum_comparison) (enumFromTo (fromEnum_comparison x) (fromEnum_comparison y)))
                                                   end)) }.

Instance instance__Bounded_Char__181__ : (Bounded Char) := {
  minBound := &#" " ;
  maxBound := &#"255" ;
}.

Instance instance__Enum_Char__182__ : (Enum Char) := {}.
Proof.
Admitted.

(* Translating `instance (Bounded N)' failed: `Int#' literals unsupported *)

Instance instance__Bounded_N__197__ : (Bounded N) := {}.
Proof.
Admitted.


Instance instance__Enum_N__198__ : (Enum N) := {}.
Proof.
Admitted.

(*
  succ := (fun arg_199__ =>
    (match arg_199__ with
      | x => (if (x /= maxBound)
             then (x + #1)
             else (succError &"Word"))
    end)) ;
  pred := (fun arg_200__ =>
    (match arg_200__ with
      | x => (if (x /= minBound)
             then (x - #1)
             else (predError &"Word"))
    end)) ;
  toEnum := (fun arg_201__ =>
    (match arg_201__ with
      | ((I# i#) as i) => (if (i >= #0)
                          then (_W#_ ((_int2Word#_ _i#_)))
                          else (((toEnumError &"Word") i) (pair (minBound : N) (maxBound : N))))
    end)) ;
  fromEnum := (fun arg_202__ =>
    (match arg_202__ with
      | ((W# x#) as x) => (if (x <=? maxIntWord)
                          then (_I#_ ((_word2Int#_ _x#_)))
                          else ((fromEnumError &"Word") x))
    end)) ;
  enumFrom := (fun arg_203__ =>
    (match arg_203__ with
      | (W# x#) => (match maxBound with
                     | (W# maxWord#) => ((eftWord _x#_) _maxWord#_)
                   end)
    end)) ;
  enumFromTo := (fun arg_204__
                     arg_205__ =>
    (match arg_204__ , arg_205__ with
      | (W# x) , (W# y) => ((eftWord x) y)
    end)) ;
  enumFromThen := (fun arg_206__
                       arg_207__ =>
    (match arg_206__ , arg_207__ with
      | (W# x1) , (W# x2) => ((efdWord x1) x2)
    end)) ;
  enumFromThenTo := (fun arg_208__
                         arg_209__
                         arg_210__ =>
    (match arg_208__ , arg_209__ , arg_210__ with
      | (W# x1) , (W# x2) , (W# y) => (((efdtWord x1) x2) y)
    end)) }.
*)
Instance instance__Enum_Z__211__ : (Enum Z) := {}.
Proof.
Admitted.
(*
  succ := (fun arg_212__ => (match arg_212__ with | x => (x + #1) end)) ;
  pred := (fun arg_213__ => (match arg_213__ with | x => (x - #1) end)) ;
  toEnum := (fun arg_214__ =>
    (match arg_214__ with
      | (I# n) => (smallInteger n)
    end)) ;
  fromEnum := (fun arg_215__ =>
    (match arg_215__ with
      | n => (_I#_ ((integerToInt n)))
    end)) ;
  enumFrom := (fun arg_216__ =>
    (match arg_216__ with
      | x => ((enumDeltaInteger x) #1)
    end)) ;
  enumFromThen := (fun arg_217__
                       arg_218__ =>
    (match arg_217__ , arg_218__ with
      | x , y => ((enumDeltaInteger x) ((y - x)))
    end)) ;
  enumFromTo := (fun arg_219__
                     arg_220__ =>
    (match arg_219__ , arg_220__ with
      | x , lim => (((enumDeltaToInteger x) #1) lim)
    end)) ;
  enumFromThenTo := (fun arg_221__
                         arg_222__
                         arg_223__ =>
    (match arg_221__ , arg_222__ , arg_223__ with
      | x , y , lim => (((enumDeltaToInteger x) ((y - x))) lim)
    end)) }.
*)

(* Unbound variables:
     $ * + +# ++ - -# /= :: < <# <= == > ># >= >=# Char Eq Gt I# Int Int# Lt N Show
     String W# Word# Z _C#_ _I#_ _W#_ _chr#_ _i#_ _int2Word#_ _isTrue#_ _maxInt#_
     _maxWord#_ _word2Int#_ _x#_ asTypeOf bool c comparison d e
     errorWithoutStackTrace f false g geWord# gtWord# h i integerToInt j k l list
     ltWord# m many map maxInt minInt minusWord# n nil o pair plusWord# seq show
     smallInteger true tt unit
*)
