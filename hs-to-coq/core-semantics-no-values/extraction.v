Extraction Language Haskell.
Set Extraction KeepSingleton.

Require Import Bool.
Require Import BinNums.
Require Import BinPos.
Require Import BinNat.

Extract Inductive unit => "()" ["()"].

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].
Extract Inductive sigT2 => "(,,)" ["(,,)"].
Extract Constant prod_rect    => "Prelude.uncurry".
Extract Constant prod_uncurry => "Prelude.curry".
Extract Constant sigT_rect    => "Prelude.uncurry".
Extract Constant fst          => "Prelude.fst".
Extract Constant snd          => "Prelude.snd".
Extract Constant projT1       => "Prelude.fst".
Extract Constant projT2       => "Prelude.snd".

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Constant andb        => "(Prelude.&&)".
Extract Constant orb         => "(Prelude.||)".
Extract Constant xorb        => "(Prelude./=)".
Extract Constant negb        => "Prelude.not".
Extract Constant bool_choice => "Prelude.id".
Extract Constant bool_dec    => "(Prelude.==)".
Extract Constant eqb         => "(Prelude.==)".
Extract Constant iff_reflect => "Prelude.id".
Extract Constant reflect_dec => "Prelude.flip Prelude.const".

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Constant option_rect    => "Prelude.flip Prelude.maybe".
Extract Constant option_map     => "Prelude.fmap".

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].
Extract Constant sum_rect => "Prelude.either".

Extract Inductive list => "[]" ["[]" "(:)"].
Extract Constant length  => "Data.List.genericLength".
Extract Constant app     => "(Prelude.++)".
(* seq *)
Extract Constant length  => "Data.List.genericLength".

Extract Inductive comparison  => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive CompareSpec => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
  (* Like `comparison`, but with proofs -- except those have been erased *)

Extract Inductive nat => "Prelude.Integer" ["(0 :: Prelude.Integer)" "(Prelude.+ 1)"]
                         "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Constant pred  => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant plus  => "(Prelude.+)".
Extract Constant minus => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant mult  => "(Prelude.*)".
Extract Constant max   => "Prelude.max".
Extract Constant min   => "Prelude.min".

Extract Inductive positive =>
  "Prelude.Integer"
  ["((Prelude.+ 1) Prelude.. (2 Prelude.*))"
   "(2 Prelude.*)"
   "(1 :: Prelude.Integer)"]
  "(\fxI fxO fxH p -> if p Prelude.== 1 then fxH p else (if Data.Bits.testBit p 0 then fxI else fxO) (p `Data.Bits.shiftR` 1))".
Extract Inductive N =>
  "Prelude.Integer" ["(0 :: Prelude.Integer)" "Prelude.id"]
  "(\fN0 fNpos n -> if n Prelude.== 0 then fN0 () else fNpos n)".
Extract Inductive Z =>
  "Prelude.Integer" ["(0 :: Prelude.Integer)" "Prelude.id" "Prelude.negate"]
  "(\fZ0 fZpos fZneg z -> case z `Prelude.compare` 0 of { Prelude.GT -> fZpos z ; Prelude.EQ -> fZ0 () ; Prelude.LT -> fZneg (- z) })".

Extract Constant Pos.succ         => "(Prelude.+ 1)".
Extract Constant Pos.add          => "(Prelude.+)".
Extract Constant Pos.add_carry    => "\x y -> x Prelude.+ y Prelude.+ 1".
Extract Constant Pos.pred_double  => "\x -> (2 Prelude.* x) Prelude.- 1".
Extract Constant Pos.pred         => "\x -> Prelude.max (x Prelude.- 1) 1".
Extract Constant Pos.pred_N       => "Prelude.subtract 1".
Extract Constant Pos.sub          => "\x y -> Prelude.max (x Prelude.- y) 1".
Extract Constant Pos.mul          => "(Prelude.*)".
Extract Constant Pos.pow          => "(Prelude.^)".
Extract Constant Pos.square       => "(Prelude.^ 2)".
Extract Constant Pos.div2         => "\x -> Prelude.max (x `Prelude.quot` 2) 1".
Extract Constant Pos.div2_up      => "\x -> (x Prelude.+ 1) `Prelude.quot` 2".
Extract Constant Pos.compare      => "Prelude.compare".
Extract Constant Pos.min          => "Prelude.min".
Extract Constant Pos.max          => "Prelude.max".
Extract Constant Pos.eqb          => "(Prelude.==)".
Extract Constant Pos.leb          => "(Prelude.<=)".
Extract Constant Pos.ltb          => "(Prelude.<)".
Extract Constant Pos.gcd          => "Prelude.gcd".
Extract Constant Pos.Nsucc_double => "\x -> 2 Prelude.* x Prelude.+ 1".
Extract Constant Pos.Ndouble      => "(2 Prelude.*)".
Extract Constant Pos.lor          => "(Data.Bits..|.)".
Extract Constant Pos.land         => "(Data.Bits..&.)".
Extract Constant Pos.ldiff        => "\x y -> x Data.Bits..&. Data.Bits.complement y".
Extract Constant Pos.lxor         => "Data.Bits.xor".
Extract Constant Pos.shiftl_nat   => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant Pos.shiftr_nat   => "\x s -> Prelude.max (x `Data.Bits.shiftR` (Prelude.fromInteger s)) 1".
Extract Constant Pos.shiftl       => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant Pos.shiftr       => "\x s -> Prelude.max (x `Data.Bits.shiftR` (Prelude.fromInteger s)) 1".
Extract Constant Pos.testbit_nat  => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant Pos.testbit      => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant Pos.to_nat       => "Prelude.id".
Extract Constant Pos.of_nat       => "Prelude.max 1".
Extract Constant Pos.of_succ_nat  => "(Prelude.+ 1)".
Extract Constant Pos.eq_dec       => "(Prelude.==)".

Extract Constant N.zero         => "0 :: Prelude.Integer".
Extract Constant N.one          => "1 :: Prelude.Integer".
Extract Constant N.two          => "2 :: Prelude.Integer".
Extract Constant N.succ_double  => "\x -> 2 Prelude.* x Prelude.+ 1".
Extract Constant N.double       => "(2 Prelude.*)".
Extract Constant N.succ         => "(Prelude.+ 1)".
Extract Constant N.pred         => "\x -> Prelude.max (x Prelude.- 1) 0".
Extract Constant N.succ_pos     => "(Prelude.+ 1)".
Extract Constant N.add          => "(Prelude.+)".
Extract Constant N.sub          => "\x y -> Prelude.max (x Prelude.- y) 0".
Extract Constant N.mul          => "(Prelude.*)".
Extract Constant N.compare      => "Prelude.compare".
Extract Constant N.eqb          => "(Prelude.==)".
Extract Constant N.leb          => "(Prelude.<=)".
Extract Constant N.ltb          => "(Prelude.<)".
Extract Constant N.min          => "Prelude.min".
Extract Constant N.max          => "Prelude.max".
Extract Constant N.div2         => "(`Prelude.quot` 2)".
Extract Constant N.even         => "Prelude.even".
Extract Constant N.odd          => "Prelude.odd".
Extract Constant N.pow          => "(Prelude.^)".
Extract Constant N.square       => "(Prelude.^ 2)".
Extract Constant N.pos_div_eucl => "\x y -> if y Prelude.== 0 then (0,x) else x `Prelude.quotRem` y".
Extract Constant N.div_eucl     => "\x y -> if y Prelude.== 0 then (0,x) else x `Prelude.quotRem` y".
Extract Constant N.div          => "Prelude.quot".
Extract Constant N.modulo       => "Prelude.rem".
Extract Constant N.gcd          => "Prelude.gcd".
Extract Constant N.lor          => "(Data.Bits..|.)".
Extract Constant N.land         => "(Data.Bits..&.)".
Extract Constant N.ldiff        => "\x y -> x Data.Bits..&. Data.Bits.complement y".
Extract Constant N.lxor         => "Data.Bits.xor".
Extract Constant N.shiftl_nat   => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant N.shiftr_nat   => "\x s -> x `Data.Bits.shiftR` (Prelude.fromInteger s)".
Extract Constant N.shiftl       => "\x s -> x `Data.Bits.shiftL` (Prelude.fromInteger s)".
Extract Constant N.shiftr       => "\x s -> x `Data.Bits.shiftR` (Prelude.fromInteger s)".
Extract Constant N.testbit_nat  => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant N.testbit      => "\x b -> Data.Bits.testBit x (Prelude.fromInteger b)".
Extract Constant N.to_nat       => "Prelude.id".
Extract Constant N.of_nat       => "Prelude.id".
Extract Constant N.eq_dec       => "(Prelude.==)".
Extract Constant N.lcm          => "Prelude.lcm".
Extract Constant N.setbit       => "\x b -> Data.Bits.setBit x (Prelude.fromInteger b)".
Extract Constant N.clearbit     => "\x b -> Data.Bits.clearBit x (Prelude.fromInteger b)".

Require Import core.

(* Axioms *)
Extract Inlined Constant Char       => "Prelude.Char".
Extract Inlined Constant Int        => "Prelude.Int".
Extract Inlined Constant Rational   => "Prelude.Rational".
Extract Inlined Constant ByteString => "Data.ByteString.ByteString".

(* Synonyms/replacements from Haskell libraries *)
Extract Inlined Constant FastString => "FastString.FastString".
Extract Inlined Constant String => "Prelude.String".
Extract Inductive IntMap => "Data.IntMap.IntMap"
                            ["error ""IntMap is abstract"" (constructor)"]
                            "error ""IntMap is abstract"" (case)".
Extract Inductive Array => "Data.Array.Array"
                           ["error ""Array is abstract"" (constructor)"]
                           "error ""Array is abstract"" (case)".

Recursive Extraction CoreBind.
