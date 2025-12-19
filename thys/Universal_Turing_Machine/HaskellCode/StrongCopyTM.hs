{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  StrongCopyTM(tm_erase_right_then_dblBk_left, tm_skip_first_arg,
                tm_check_for_one_arg, tm_strong_copy)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified WeakCopyTM;
import qualified ComposedTMs;
import qualified Turing;
import qualified Arith;

tm_erase_right_then_dblBk_left :: [(Turing.Action, Arith.Nat)];
tm_erase_right_then_dblBk_left =
  [(Turing.L, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Zero_nat), (Turing.R, Arith.Zero_nat),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.WB,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.WB,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit1 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.WB, Arith.Zero_nat),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One))))];

tm_skip_first_arg :: [(Turing.Action, Arith.Nat)];
tm_skip_first_arg =
  [(Turing.L, Arith.Zero_nat),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.WO, Arith.Zero_nat),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Zero_nat),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One)))];

tm_check_for_one_arg :: [(Turing.Action, Arith.Nat)];
tm_check_for_one_arg =
  ComposedTMs.seq_tm tm_skip_first_arg tm_erase_right_then_dblBk_left;

tm_strong_copy :: [(Turing.Action, Arith.Nat)];
tm_strong_copy =
  ComposedTMs.seq_tm tm_check_for_one_arg WeakCopyTM.tm_weak_copy;

}
