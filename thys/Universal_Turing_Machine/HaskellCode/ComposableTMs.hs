{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module ComposableTMs(mk_composable0) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;
import qualified HOL;
import qualified Turing;
import qualified Arith;

fix_jumps ::
  Arith.Nat -> [(Turing.Action, Arith.Nat)] -> [(Turing.Action, Arith.Nat)];
fix_jumps smax [] = [];
fix_jumps smax (ins : inss) =
  (if Arith.less_eq_nat (snd ins) smax then ins : fix_jumps smax inss
    else (fst ins, Arith.Zero_nat) : fix_jumps smax inss);

mk_composable0 :: [(Turing.Action, Arith.Nat)] -> [(Turing.Action, Arith.Nat)];
mk_composable0 [] =
  [(Turing.Nop, Arith.Zero_nat), (Turing.Nop, Arith.Zero_nat)];
mk_composable0 [i1] =
  fix_jumps (Arith.Nat_of_num Arith.One) [i1, (Turing.Nop, Arith.Zero_nat)];
mk_composable0 (i1 : i2 : ins) =
  let {
    l = Arith.plus_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
          (List.size_list ins);
  } in (if Arith.equal_nat
             (Arith.modulo_nat l (Arith.Nat_of_num (Arith.Bit0 Arith.One)))
             Arith.Zero_nat
         then fix_jumps
                (Arith.divide_nat l (Arith.Nat_of_num (Arith.Bit0 Arith.One)))
                (i1 : i2 : ins)
         else fix_jumps
                (Arith.plus_nat
                  (Arith.divide_nat l (Arith.Nat_of_num (Arith.Bit0 Arith.One)))
                  (Arith.Nat_of_num Arith.One))
                ((i1 : i2 : ins) ++ [(Turing.Nop, Arith.Zero_nat)]));

}
