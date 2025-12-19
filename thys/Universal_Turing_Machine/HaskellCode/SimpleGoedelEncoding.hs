{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  SimpleGoedelEncoding(nat_list_to_tm, nat_to_tm, tm_to_nat_list, tm_to_nat)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;
import qualified Nat_Bijection;
import qualified Turing;
import qualified Arith;

nat_list_to_tm :: [Arith.Nat] -> [(Turing.Action, Arith.Nat)];
nat_list_to_tm [] = [];
nat_list_to_tm [ac] = [(Turing.Nop, Arith.Zero_nat)];
nat_list_to_tm (ac : s : ns) =
  (if Arith.less_nat ac (Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One)))
    then (List.nth [Turing.WB, Turing.WO, Turing.L, Turing.R, Turing.Nop] ac,
           s) :
           nat_list_to_tm ns
    else [(Turing.Nop, Arith.Zero_nat)]);

nat_to_tm :: Arith.Nat -> [(Turing.Action, Arith.Nat)];
nat_to_tm = nat_list_to_tm . Nat_Bijection.list_decode;

tm_to_nat_list :: [(Turing.Action, Arith.Nat)] -> [Arith.Nat];
tm_to_nat_list [] = [];
tm_to_nat_list ((Turing.WB, s) : is) = Arith.Zero_nat : s : tm_to_nat_list is;
tm_to_nat_list ((Turing.WO, s) : is) =
  Arith.Nat_of_num Arith.One : s : tm_to_nat_list is;
tm_to_nat_list ((Turing.L, s) : is) =
  Arith.Nat_of_num (Arith.Bit0 Arith.One) : s : tm_to_nat_list is;
tm_to_nat_list ((Turing.R, s) : is) =
  Arith.Nat_of_num (Arith.Bit1 Arith.One) : s : tm_to_nat_list is;
tm_to_nat_list ((Turing.Nop, s) : is) =
  Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One)) : s : tm_to_nat_list is;

tm_to_nat :: [(Turing.Action, Arith.Nat)] -> Arith.Nat;
tm_to_nat = Nat_Bijection.list_encode . tm_to_nat_list;

}
