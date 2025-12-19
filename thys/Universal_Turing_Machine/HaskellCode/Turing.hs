{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Turing(Cell(..), Action(..), step, steps, is_final) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Product_Type;
import qualified List;
import qualified HOL;
import qualified Arith;

data Cell = Bk | Oc;

data Action = WB | WO | L | R | Nop;

update :: Action -> ([Cell], [Cell]) -> ([Cell], [Cell]);
update WB (l, r) = (l, Bk : List.tl r);
update WO (l, r) = (l, Oc : List.tl r);
update L (l, r) = (if null l then ([], Bk : r) else (List.tl l, List.hd l : r));
update R (l, r) = (if null r then (Bk : l, []) else (List.hd r : l, List.tl r));
update Nop (l, r) = (l, r);

equal_cell :: Cell -> Cell -> Bool;
equal_cell Bk Oc = False;
equal_cell Oc Bk = False;
equal_cell Oc Oc = True;
equal_cell Bk Bk = True;

fetch :: [(Action, Arith.Nat)] -> Arith.Nat -> Cell -> (Action, Arith.Nat);
fetch p n b =
  let {
    len = List.size_list p;
  } in (if Arith.equal_nat n Arith.Zero_nat then (Nop, Arith.Zero_nat)
         else (if equal_cell b Bk
                then (if Arith.less_eq_nat len
                           (Arith.minus_nat
                             (Arith.times_nat
                               (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
                             (Arith.Nat_of_num (Arith.Bit0 Arith.One)))
                       then (Nop, Arith.Zero_nat)
                       else List.nth p
                              (Arith.minus_nat
                                (Arith.times_nat
                                  (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
                                (Arith.Nat_of_num (Arith.Bit0 Arith.One))))
                else (if Arith.less_eq_nat len
                           (Arith.minus_nat
                             (Arith.times_nat
                               (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
                             (Arith.Nat_of_num Arith.One))
                       then (Nop, Arith.Zero_nat)
                       else List.nth p
                              (Arith.minus_nat
                                (Arith.times_nat
                                  (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
                                (Arith.Nat_of_num Arith.One)))));

step ::
  (Arith.Nat, ([Cell], [Cell])) ->
    ([(Action, Arith.Nat)], Arith.Nat) -> (Arith.Nat, ([Cell], [Cell]));
step (s, (l, r)) (p, off) =
  (case fetch p (Arith.minus_nat s off) (if null r then Bk else List.hd r) of {
    (a, sa) -> (sa, update a (l, r));
  });

steps ::
  (Arith.Nat, ([Cell], [Cell])) ->
    ([(Action, Arith.Nat)], Arith.Nat) ->
      Arith.Nat -> (Arith.Nat, ([Cell], [Cell]));
steps c p n =
  (if Arith.equal_nat n Arith.Zero_nat then c
    else steps (step c p) p (Arith.minus_nat n (Arith.Nat_of_num Arith.One)));

is_final :: (Arith.Nat, ([Cell], [Cell])) -> Bool;
is_final (s, (l, r)) = Arith.equal_nat s Arith.Zero_nat;

}
