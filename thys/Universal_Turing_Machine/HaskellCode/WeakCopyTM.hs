{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  WeakCopyTM(tm_copy_begin_orig, tm_copy_loop_orig, tm_copy_end_new,
              tm_weak_copy)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified ComposedTMs;
import qualified Turing;
import qualified Arith;

tm_copy_begin_orig :: [(Turing.Action, Arith.Nat)];
tm_copy_begin_orig =
  [(Turing.WB, Arith.Zero_nat),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Zero_nat)];

tm_copy_loop_orig :: [(Turing.Action, Arith.Nat)];
tm_copy_loop_orig =
  [(Turing.R, Arith.Zero_nat),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.L, Arith.Nat_of_num Arith.One)];

tm_copy_end_new :: [(Turing.Action, Arith.Nat)];
tm_copy_end_new =
  [(Turing.R, Arith.Zero_nat),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Zero_nat),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One)))];

tm_weak_copy :: [(Turing.Action, Arith.Nat)];
tm_weak_copy =
  ComposedTMs.seq_tm (ComposedTMs.seq_tm tm_copy_begin_orig tm_copy_loop_orig)
    tm_copy_end_new;

}
