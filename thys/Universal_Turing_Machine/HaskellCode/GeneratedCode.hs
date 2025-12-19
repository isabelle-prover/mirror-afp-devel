{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  GeneratedCode(dummy_cellId, tape_of_nat_imp, dummy_abc_inst_Id,
                 tape_of_nat_list_imp)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Abacus;
import qualified Numerals;
import qualified Arith;
import qualified Turing;

dummy_cellId :: Turing.Cell -> Turing.Cell;
dummy_cellId Turing.Oc = Turing.Oc;
dummy_cellId Turing.Bk = Turing.Bk;

tape_of_nat_imp :: Arith.Nat -> [Turing.Cell];
tape_of_nat_imp n = Numerals.tape_of_nat n;

dummy_abc_inst_Id :: Abacus.Abc_inst -> Bool;
dummy_abc_inst_Id (Abacus.Inc n) = True;
dummy_abc_inst_Id (Abacus.Dec n s) = True;
dummy_abc_inst_Id (Abacus.Goto n) = True;

tape_of_nat_list_imp :: [Arith.Nat] -> [Turing.Cell];
tape_of_nat_list_imp ns = Numerals.tape_of_list ns;

}
