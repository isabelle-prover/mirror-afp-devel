{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Groups_List(sum_list) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified List;
import qualified Arith;

sum_list :: forall a. (Arith.Monoid_add a) => [a] -> a;
sum_list xs = List.foldr Arith.plus xs Arith.zero;

}
