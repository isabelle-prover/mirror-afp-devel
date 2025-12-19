{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Numerals(tape_of_nat, Tape, tape_of_list) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;
import qualified Turing;
import qualified Arith;

tape_of_nat :: Arith.Nat -> [Turing.Cell];
tape_of_nat n = List.replicate (Arith.suc n) Turing.Oc;

class Tape a where {
  tape_of :: a -> [Turing.Cell];
};

instance Tape Arith.Nat where {
  tape_of = tape_of_nat;
};

tape_of_nat_list :: forall a. (Tape a) => [a] -> [Turing.Cell];
tape_of_nat_list [] = [];
tape_of_nat_list [n] = tape_of n;
tape_of_nat_list (n : v : va) =
  tape_of n ++ Turing.Bk : tape_of_nat_list (v : va);

tape_of_list :: forall a. (Tape a) => [a] -> [Turing.Cell];
tape_of_list = tape_of_nat_list;

}
