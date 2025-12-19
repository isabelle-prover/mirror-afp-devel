{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module List(nth, upt, take, foldr, hd, tl, replicate, list_update, size_list)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Arith;

nth :: forall a. [a] -> Arith.Nat -> a;
nth (x : xs) n =
  (if Arith.equal_nat n Arith.Zero_nat then x
    else nth xs (Arith.minus_nat n (Arith.Nat_of_num Arith.One)));

upt :: Arith.Nat -> Arith.Nat -> [Arith.Nat];
upt i j = (if Arith.less_nat i j then i : upt (Arith.suc i) j else []);

take :: forall a. Arith.Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) =
  (if Arith.equal_nat n Arith.Zero_nat then []
    else x : take (Arith.minus_nat n (Arith.Nat_of_num Arith.One)) xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

hd :: forall a. [a] -> a;
hd (x21 : x22) = x21;

tl :: forall a. [a] -> [a];
tl [] = [];
tl (x21 : x22) = x22;

replicate :: forall a. Arith.Nat -> a -> [a];
replicate n x =
  (if Arith.equal_nat n Arith.Zero_nat then []
    else x : replicate (Arith.minus_nat n (Arith.Nat_of_num Arith.One)) x);

list_update :: forall a. [a] -> Arith.Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if Arith.equal_nat i Arith.Zero_nat then y : xs
    else x : list_update xs (Arith.minus_nat i (Arith.Nat_of_num Arith.One)) y);

length_tailrec :: forall a. [a] -> Arith.Nat -> Arith.Nat;
length_tailrec [] n = n;
length_tailrec (x : xs) n = length_tailrec xs (Arith.suc n);

size_list :: forall a. [a] -> Arith.Nat;
size_list xs = length_tailrec xs Arith.Zero_nat;

}
