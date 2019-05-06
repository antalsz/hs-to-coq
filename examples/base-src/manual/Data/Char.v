(* Preamble *)
Require Import GHC.Base.
Require Export GHC.Char.
Require Import GHC.Real.
Require Import GHC.Num.
Require Import GHC.Unicode.

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* No data type declarations to convert. *)

(* Converted value declarations: *)
Definition isSeparator : Char -> bool := (fun arg_4__ =>
    (match arg_4__ with
      | c => (match generalCategory c with
               | Space => true
               | LineSeparator => true
               | ParagraphSeparator => true
               | _ => false
             end)
    end)).

Definition isNumber : Char -> bool := (fun arg_3__ =>
    (match arg_3__ with
      | c => (match generalCategory c with
               | DecimalNumber => true
               | LetterNumber => true
               | OtherNumber => true
               | _ => false
             end)
    end)).

Definition isMark : Char -> bool := (fun arg_2__ =>
    (match arg_2__ with
      | c => (match generalCategory c with
               | NonSpacingMark => true
               | SpacingCombiningMark => true
               | EnclosingMark => true
               | _ => false
             end)
    end)).

Definition isLetter : Char -> bool := (fun arg_1__ =>
    (match arg_1__ with
      | c => (match generalCategory c with
               | UppercaseLetter => true
               | LowercaseLetter => true
               | TitlecaseLetter => true
               | ModifierLetter => true
               | OtherLetter => true
               | _ => false
             end)
    end)).

(* Made this total by adding error value. *)

Definition digitToInt : Char -> Int := (fun arg_0__ =>
    (match arg_0__ with
      | c => (let dec : Z := ord c - ord &#"0"
             in (let hexl : Z := ord c - ord &#"a"
                in (let hexu : Z := ord c - ord &#"A"
                   in (if (((fromIntegral dec : Rational)) <= #9)
                      then dec
                      else (if (((fromIntegral hexl : Rational)) <= #5)
                           then hexl + #10
                           else (if (((fromIntegral hexu : Rational)) <= #5)
                                then hexu + #10
                                else #256))))))
    end)).
(* No type class instance declarations to convert. *)
