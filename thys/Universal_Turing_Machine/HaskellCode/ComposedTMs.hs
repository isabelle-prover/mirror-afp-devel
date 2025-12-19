{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ComposedTMs(shift, adjust, seq_tm) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;
import qualified Product_Type;
import qualified Turing;
import qualified Arith;

shift ::
  [(Turing.Action, Arith.Nat)] -> Arith.Nat -> [(Turing.Action, Arith.Nat)];
shift p n =
  map (\ (a, s) ->
        (a, (if Arith.equal_nat s Arith.Zero_nat then Arith.Zero_nat
              else Arith.plus_nat s n)))
    p;

adjust ::
  [(Turing.Action, Arith.Nat)] -> Arith.Nat -> [(Turing.Action, Arith.Nat)];
adjust p e =
  map (\ (a, s) -> (a, (if Arith.equal_nat s Arith.Zero_nat then e else s))) p;

seq_tm ::
  [(Turing.Action, Arith.Nat)] ->
    [(Turing.Action, Arith.Nat)] -> [(Turing.Action, Arith.Nat)];
seq_tm p1 p2 =
  adjust p1
    (Arith.suc
      (Arith.divide_nat (List.size_list p1)
        (Arith.Nat_of_num (Arith.Bit0 Arith.One)))) ++
    shift p2
      (Arith.divide_nat (List.size_list p1)
        (Arith.Nat_of_num (Arith.Bit0 Arith.One)));

}
