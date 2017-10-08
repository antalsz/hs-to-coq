(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require GHC.Char.
Require GHC.Unicode.

(* Converted declarations: *)

Definition isLetter : GHC.Char.Char -> bool :=
  fun arg_15__ =>
    match arg_15__ with
      | c => let scrut_16__ := GHC.Unicode.generalCategory c in
             match scrut_16__ with
               | GHC.Unicode.UppercaseLetter => true
               | GHC.Unicode.LowercaseLetter => true
               | GHC.Unicode.TitlecaseLetter => true
               | GHC.Unicode.ModifierLetter => true
               | GHC.Unicode.OtherLetter => true
               | _ => false
             end
    end.

Definition isMark : GHC.Char.Char -> bool :=
  fun arg_10__ =>
    match arg_10__ with
      | c => let scrut_11__ := GHC.Unicode.generalCategory c in
             match scrut_11__ with
               | GHC.Unicode.NonSpacingMark => true
               | GHC.Unicode.SpacingCombiningMark => true
               | GHC.Unicode.EnclosingMark => true
               | _ => false
             end
    end.

Definition isNumber : GHC.Char.Char -> bool :=
  fun arg_5__ =>
    match arg_5__ with
      | c => let scrut_6__ := GHC.Unicode.generalCategory c in
             match scrut_6__ with
               | GHC.Unicode.DecimalNumber => true
               | GHC.Unicode.LetterNumber => true
               | GHC.Unicode.OtherNumber => true
               | _ => false
             end
    end.

Definition isSeparator : GHC.Char.Char -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | c => let scrut_1__ := GHC.Unicode.generalCategory c in
             match scrut_1__ with
               | GHC.Unicode.Space => true
               | GHC.Unicode.LineSeparator => true
               | GHC.Unicode.ParagraphSeparator => true
               | _ => false
             end
    end.

(* Unbound variables:
     GHC.Char.Char GHC.Unicode.generalCategory bool false true
*)
