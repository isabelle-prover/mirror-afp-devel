(*  Title:      Code_Target_Word_Base.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Common base for target language implementations of word types\<close>

theory Code_Target_Word
  imports "HOL-Library.Word"
begin

section \<open>SML\<close>

text \<open>
  The separate code target \<open>SML_word\<close> collects setups for the
  code generator that PolyML does not provide.
\<close>

setup \<open>Code_Target.add_derived_target ("SML_word", [(Code_ML.target_SML, I)])\<close>


section \<open>Haskell\<close>

text \<open>
  In the \<^text>\<open>Data.Bits.Bits\<close> type class, shifts and bit indices are given as
  \<^text>\<open>Int\<close> rather than \<^text>\<open>Integer\<close>.

  Additional constants take only parameters of type @{typ integer} rather than @{typ nat}
  and check the preconditions as far as possible (e.g., being non-negative) in a portable way.
\<close>

code_printing code_module Data_Bits \<rightharpoonup> (Haskell)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The ...Bounded functions assume that the Integer argument for the shift
  or bit index fits into an Int, is non-negative and (for types of fixed bit width)
  less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitUnbounded x b
  | b <= toInteger (Prelude.maxBound :: Int) = Data.Bits.testBit x (fromInteger b)
  | otherwise = error ("Bit index too large: " ++ show b)
;

testBitBounded :: Data.Bits.Bits a => a -> Integer -> Bool;
testBitBounded x b = Data.Bits.testBit x (fromInteger b);

shiftlUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlUnbounded x n
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftL x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftlBounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftlBounded x n = Data.Bits.shiftL x (fromInteger n);

shiftrUnbounded :: Data.Bits.Bits a => a -> Integer -> a;
shiftrUnbounded x n
  | n <= toInteger (Prelude.maxBound :: Int) = Data.Bits.shiftR x (fromInteger n)
  | otherwise = error ("Shift operand too large: " ++ show n)
;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Integer -> a;
shiftrBounded x n = Data.Bits.shiftR x (fromInteger n);

}\<close>

  and \<comment> \<open>@{theory HOL.Quickcheck_Narrowing} maps @{typ integer} to
            Haskell's \<^text>\<open>Prelude.Int\<close> type instead of Integer. For compatibility
            with the Haskell target, we nevertheless provide bounded and
            unbounded functions.\<close>
  (Haskell_Quickcheck)
\<open>
module Data_Bits where {

import qualified Data.Bits;

{-
  The functions assume that the Int argument for the shift or bit index is
  non-negative and (for types of fixed bit width) less than bitSize
-}

infixl 7 .&.;
infixl 6 `xor`;
infixl 5 .|.;

(.&.) :: Data.Bits.Bits a => a -> a -> a;
(.&.) = (Data.Bits..&.);

xor :: Data.Bits.Bits a => a -> a -> a;
xor = Data.Bits.xor;

(.|.) :: Data.Bits.Bits a => a -> a -> a;
(.|.) = (Data.Bits..|.);

complement :: Data.Bits.Bits a => a -> a;
complement = Data.Bits.complement;

testBitUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitUnbounded = Data.Bits.testBit;

testBitBounded :: Data.Bits.Bits a => a -> Prelude.Int -> Bool;
testBitBounded = Data.Bits.testBit;

shiftlUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlUnbounded = Data.Bits.shiftL;

shiftlBounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftlBounded = Data.Bits.shiftL;

shiftrUnbounded :: Data.Bits.Bits a => a -> Prelude.Int -> a;
shiftrUnbounded = Data.Bits.shiftR;

shiftrBounded :: (Ord a, Data.Bits.Bits a) => a -> Prelude.Int -> a;
shiftrBounded = Data.Bits.shiftR;

}\<close>

code_reserved (Haskell) Data_Bits


end
