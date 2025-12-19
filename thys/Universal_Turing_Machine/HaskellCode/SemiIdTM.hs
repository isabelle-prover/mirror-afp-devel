{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SemiIdTM(tm_semi_id_eq0, tm_semi_id_gt0) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Turing;
import qualified Arith;

tm_semi_id_eq0 :: [(Turing.Action, Arith.Nat)];
tm_semi_id_eq0 =
  [(Turing.WB, Arith.Nat_of_num Arith.One),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Zero_nat), (Turing.L, Arith.Nat_of_num Arith.One)];

tm_semi_id_gt0 :: [(Turing.Action, Arith.Nat)];
tm_semi_id_gt0 =
  [(Turing.WB, Arith.Nat_of_num Arith.One),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L, Arith.Nat_of_num Arith.One), (Turing.L, Arith.Zero_nat)];

}
