{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Nat_Bijection(triangle, prod_decode, list_decode, prod_encode, list_encode)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Product_Type;
import qualified Arith;

triangle :: Arith.Nat -> Arith.Nat;
triangle n =
  Arith.divide_nat (Arith.times_nat n (Arith.suc n))
    (Arith.Nat_of_num (Arith.Bit0 Arith.One));

prod_decode_aux :: Arith.Nat -> Arith.Nat -> (Arith.Nat, Arith.Nat);
prod_decode_aux k m =
  (if Arith.less_eq_nat m k then (m, Arith.minus_nat k m)
    else prod_decode_aux (Arith.suc k) (Arith.minus_nat m (Arith.suc k)));

prod_decode :: Arith.Nat -> (Arith.Nat, Arith.Nat);
prod_decode = prod_decode_aux Arith.Zero_nat;

list_decode :: Arith.Nat -> [Arith.Nat];
list_decode n =
  (if Arith.equal_nat n Arith.Zero_nat then []
    else (case prod_decode (Arith.minus_nat n (Arith.Nat_of_num Arith.One)) of {
           (x, y) -> x : list_decode y;
         }));

prod_encode :: (Arith.Nat, Arith.Nat) -> Arith.Nat;
prod_encode = (\ (m, n) -> Arith.plus_nat (triangle (Arith.plus_nat m n)) m);

list_encode :: [Arith.Nat] -> Arith.Nat;
list_encode [] = Arith.Zero_nat;
list_encode (x : xs) = Arith.suc (prod_encode (x, list_encode xs));

}
