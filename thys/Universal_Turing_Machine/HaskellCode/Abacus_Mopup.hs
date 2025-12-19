{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Abacus_Mopup(mopup_n_tm) where {

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

mopup_a :: Arith.Nat -> [(Turing.Action, Arith.Nat)];
mopup_a n =
  (if Arith.equal_nat n Arith.Zero_nat then []
    else mopup_a (Arith.minus_nat n (Arith.Nat_of_num Arith.One)) ++
           [(Turing.R,
              Arith.plus_nat
                (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                  (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                (Arith.Nat_of_num (Arith.Bit1 Arith.One))),
             (Turing.WB,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num (Arith.Bit0 Arith.One))),
             (Turing.R,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num Arith.One)),
             (Turing.WO,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num (Arith.Bit0 Arith.One)))]);

mopup_b :: [(Turing.Action, Arith.Nat)];
mopup_b =
  [(Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.R, Arith.Nat_of_num Arith.One),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.R, Arith.Zero_nat),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One)))];

mopup_n_tm :: Arith.Nat -> [(Turing.Action, Arith.Nat)];
mopup_n_tm n =
  mopup_a n ++
    ComposedTMs.shift mopup_b
      (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n);

}
