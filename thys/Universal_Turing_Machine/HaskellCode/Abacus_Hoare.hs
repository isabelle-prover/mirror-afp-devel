{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Abacus_Hoare(abc_final, app_mopup, abc_notfinal, abc_out_of_prog) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Abacus_Mopup;
import qualified ComposedTMs;
import qualified Turing;
import qualified List;
import qualified Abacus;
import qualified Arith;

abc_final :: (Arith.Nat, [Arith.Nat]) -> [Abacus.Abc_inst] -> Bool;
abc_final (s, lm) p = Arith.equal_nat s (List.size_list p);

app_mopup ::
  [(Turing.Action, Arith.Nat)] -> Arith.Nat -> [(Turing.Action, Arith.Nat)];
app_mopup tp n =
  tp ++ ComposedTMs.shift (Abacus_Mopup.mopup_n_tm n)
          (Arith.divide_nat (List.size_list tp)
            (Arith.Nat_of_num (Arith.Bit0 Arith.One)));

abc_notfinal :: (Arith.Nat, [Arith.Nat]) -> [Abacus.Abc_inst] -> Bool;
abc_notfinal (s, lm) p = Arith.less_nat s (List.size_list p);

abc_out_of_prog :: (Arith.Nat, [Arith.Nat]) -> [Abacus.Abc_inst] -> Bool;
abc_out_of_prog (s, lm) p = Arith.less_nat (List.size_list p) s;

}
