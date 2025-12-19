{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module OneStrokeTM(tm_onestroke) where {

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

tm_onestroke :: [(Turing.Action, Arith.Nat)];
tm_onestroke =
  [(Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num Arith.One),
    (Turing.R, Arith.Nat_of_num Arith.One), (Turing.WO, Arith.Zero_nat),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 Arith.One))];

}
