(* Preamble *)
Require Import GHC.Prim.
Require Import GHC.Char.
Require Import GHC.Enum.
Require Import GHC.Real.


Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* These are all C functions in GHC *)
Parameter  iswalpha : Int -> Int.
Parameter  iswalnum : Int -> Int.
Parameter  iswcntrl : Int -> Int.
Parameter  iswspace : Int -> Int.
Parameter  iswprint : Int -> Int.
Parameter  iswlower : Int -> Int.
Parameter  iswupper : Int -> Int.
Parameter  towlower : Int -> Int.
Parameter  towupper : Int -> Int.
Parameter  towtitle : Int -> Int.
Parameter  wgencat : Int -> Int.
(* Converted data type declarations: *)
Inductive GeneralCategory : Type := UppercaseLetter : GeneralCategory
                                 |  LowercaseLetter : GeneralCategory
                                 |  TitlecaseLetter : GeneralCategory
                                 |  ModifierLetter : GeneralCategory
                                 |  OtherLetter : GeneralCategory
                                 |  NonSpacingMark : GeneralCategory
                                 |  SpacingCombiningMark : GeneralCategory
                                 |  EnclosingMark : GeneralCategory
                                 |  DecimalNumber : GeneralCategory
                                 |  LetterNumber : GeneralCategory
                                 |  OtherNumber : GeneralCategory
                                 |  ConnectorPunctuation : GeneralCategory
                                 |  DashPunctuation : GeneralCategory
                                 |  OpenPunctuation : GeneralCategory
                                 |  ClosePunctuation : GeneralCategory
                                 |  InitialQuote : GeneralCategory
                                 |  FinalQuote : GeneralCategory
                                 |  OtherPunctuation : GeneralCategory
                                 |  MathSymbol : GeneralCategory
                                 |  CurrencySymbol : GeneralCategory
                                 |  ModifierSymbol : GeneralCategory
                                 |  OtherSymbol : GeneralCategory
                                 |  Space : GeneralCategory
                                 |  LineSeparator : GeneralCategory
                                 |  ParagraphSeparator : GeneralCategory
                                 |  Control : GeneralCategory
                                 |  Format : GeneralCategory
                                 |  Surrogate : GeneralCategory
                                 |  PrivateUse : GeneralCategory
                                 |  NotAssigned : GeneralCategory.

Instance instance_Enum : Enum GeneralCategory. Admitted.

(* Converted value declarations: *)
Definition toUpper : Char -> Char := (fun arg_18__ =>
    (match arg_18__ with
      | c => chr (towupper (ord c))
    end)).

Definition toTitle : Char -> Char := (fun arg_19__ =>
    (match arg_19__ with
      | c => chr (towtitle (ord c))
    end)).

Definition toLower : Char -> Char := (fun arg_17__ =>
    (match arg_17__ with
      | c => chr (towlower (ord c))
    end)).

Definition isUpper : Char -> bool := (fun arg_15__ =>
    (match arg_15__ with
      | c => (iswupper (ord c) /= #0)
    end)).

Definition isSpace : Char -> bool := (fun arg_5__ =>
    (match arg_5__ with
      | c => (let uc := (fromIntegral (ord c) : Word)
             in (if (uc <=? #887)
                then (orb (orb (uc == #32) ((uc - #9) <=? #4)) (uc == #160))
                else (iswspace (ord c) /= #0)))
    end)).

Definition isPrint : Char -> bool := (fun arg_14__ =>
    (match arg_14__ with
      | c => (iswprint (ord c) /= #0)
    end)).

Definition isOctDigit : Char -> bool := (fun arg_7__ =>
    (match arg_7__ with
      | c => (((fromIntegral (ord c - ord &#"0") : Word)) <=? #7)
    end)).

Definition isLower : Char -> bool := (fun arg_16__ =>
    (match arg_16__ with
      | c => (iswlower (ord c) /= #0)
    end)).

Definition isLatin1 : Char -> bool := (fun arg_2__ =>
    (match arg_2__ with
      | c => (c <=? #152)  (* "ÿ" *)
    end)).

Definition isDigit : Char -> bool := (fun arg_6__ =>
    (match arg_6__ with
      | c => (((fromIntegral (ord c - ord &#"0") : Word)) <=? #9)
    end)).

Definition isHexDigit : Char -> bool := (fun arg_8__ =>
    (match arg_8__ with
      | c => (orb (orb (isDigit c) (((fromIntegral (ord c - ord &#"A") : Word)) <=? #5))
                  (((fromIntegral (ord c - ord &#"a") : Word)) <=? #5))
    end)).

Definition isControl : Char -> bool := (fun arg_13__ =>
    (match arg_13__ with
      | c => (iswcntrl (ord c) /= #0)
    end)).

Definition isAsciiUpper : Char -> bool := (fun arg_4__ =>
    (match arg_4__ with
      | c => (andb (c >=? &#"A") (c <=? &#"Z"))
    end)).

Definition isAsciiLower : Char -> bool := (fun arg_3__ =>
    (match arg_3__ with
      | c => (andb (c >=? &#"a") (c <=? &#"z"))
    end)).

Definition isAscii : Char -> bool := (fun arg_1__ =>
    (match arg_1__ with
      | c => (c <? #200)  (* &#"" *)
    end)).

Definition isAlphaNum : Char -> bool := (fun arg_12__ =>
    (match arg_12__ with
      | c => (iswalnum (ord c) /= #0)
    end)).

Definition isAlpha : Char -> bool := (fun arg_11__ =>
    (match arg_11__ with
      | c => (iswalpha (ord c) /= #0)
    end)).

Definition generalCategory : Char -> GeneralCategory := (fun arg_0__ =>
    (match arg_0__ with
      | c => toEnum (fromIntegral (wgencat (fromIntegral (ord c))))
    end)).

Definition isPunctuation : Char -> bool := (fun arg_9__ =>
    (match arg_9__ with
      | c => (match generalCategory c with
               | ConnectorPunctuation => true
               | DashPunctuation => true
               | OpenPunctuation => true
               | ClosePunctuation => true
               | InitialQuote => true
               | FinalQuote => true
               | OtherPunctuation => true
               | _ => false
             end)
    end)).

Definition isSymbol : Char -> bool := (fun arg_10__ =>
    (match arg_10__ with
      | c => (match generalCategory c with
               | MathSymbol => true
               | CurrencySymbol => true
               | ModifierSymbol => true
               | OtherSymbol => true
               | _ => false
             end)
    end)).

(* No type class instance declarations to convert. *)

(* Unbound variables:
     $ - /= <=? <? == >=? Char Word andb bool chr false fromIntegral iswalnum
     iswalpha iswcntrl iswlower iswprint iswspace iswupper orb ord toEnum towlower
     towtitle towupper true wgencat
*)
