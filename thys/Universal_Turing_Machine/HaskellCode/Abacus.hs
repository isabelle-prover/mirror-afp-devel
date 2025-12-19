{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Abacus(Abc_inst(..), start_of, tgoto, tinc, tdec, ci, layout_of, tpairs_of,
          tms_of, tm_of, abc_lm_s, abc_lm_v, abc_fetch, abc_step_l, abc_steps_l)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Option;
import qualified HOL;
import qualified Groups_List;
import qualified List;
import qualified Product_Type;
import qualified ComposedTMs;
import qualified Turing;
import qualified Arith;

data Abc_inst = Inc Arith.Nat | Dec Arith.Nat Arith.Nat | Goto Arith.Nat;

start_of :: [Arith.Nat] -> Arith.Nat -> Arith.Nat;
start_of ly x = Arith.suc (Groups_List.sum_list (List.take x ly));

tgoto :: Arith.Nat -> [(Turing.Action, Arith.Nat)];
tgoto n = [(Turing.Nop, n), (Turing.Nop, n)];

findnth :: Arith.Nat -> [(Turing.Action, Arith.Nat)];
findnth n =
  (if Arith.equal_nat n Arith.Zero_nat then []
    else findnth (Arith.minus_nat n (Arith.Nat_of_num Arith.One)) ++
           [(Turing.WO,
              Arith.plus_nat
                (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                  (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                (Arith.Nat_of_num Arith.One)),
             (Turing.R,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num (Arith.Bit0 Arith.One))),
             (Turing.R,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num (Arith.Bit1 Arith.One))),
             (Turing.R,
               Arith.plus_nat
                 (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One))
                   (Arith.minus_nat n (Arith.Nat_of_num Arith.One)))
                 (Arith.Nat_of_num (Arith.Bit0 Arith.One)))]);

tinc_b :: [(Turing.Action, Arith.Nat)];
tinc_b =
  [(Turing.WO, Arith.Nat_of_num Arith.One),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.WO, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.WB,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One))))];

tinc :: Arith.Nat -> Arith.Nat -> [(Turing.Action, Arith.Nat)];
tinc ss n =
  ComposedTMs.shift
    (findnth n ++
      ComposedTMs.shift tinc_b
        (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n))
    (Arith.minus_nat ss (Arith.Nat_of_num Arith.One));

tdec_b :: [(Turing.Action, Arith.Nat)];
tdec_b =
  [(Turing.WO, Arith.Nat_of_num Arith.One),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 Arith.One)),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit1 Arith.One)))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.L, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 Arith.One)),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 Arith.One))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 Arith.One))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.L, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.WB, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 Arith.One))),
    (Turing.WO,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One)))),
    (Turing.R, Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 Arith.One))),
    (Turing.WB,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit0 (Arith.Bit1 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.R,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit1 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit0 Arith.One)))),
    (Turing.R,
      Arith.Nat_of_num
        (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One))))),
    (Turing.WB,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit1 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit1 (Arith.Bit1 (Arith.Bit1 Arith.One)))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit1 Arith.One)))),
    (Turing.R,
      Arith.Nat_of_num
        (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One))))),
    (Turing.L,
      Arith.Nat_of_num (Arith.Bit0 (Arith.Bit1 (Arith.Bit1 Arith.One)))),
    (Turing.R, Arith.Zero_nat),
    (Turing.WB,
      Arith.Nat_of_num
        (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))))];

tdec :: Arith.Nat -> Arith.Nat -> Arith.Nat -> [(Turing.Action, Arith.Nat)];
tdec ss n e =
  ComposedTMs.shift (findnth n)
    (Arith.minus_nat ss (Arith.Nat_of_num Arith.One)) ++
    ComposedTMs.adjust
      (ComposedTMs.shift
        (ComposedTMs.shift tdec_b
          (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n))
        (Arith.minus_nat ss (Arith.Nat_of_num Arith.One)))
      e;

ci :: [Arith.Nat] -> Arith.Nat -> Abc_inst -> [(Turing.Action, Arith.Nat)];
ci ly ss (Inc n) = tinc ss n;
ci ly ss (Dec n e) = tdec ss n (start_of ly e);
ci ly ss (Goto n) = tgoto (start_of ly n);

length_of :: Abc_inst -> Arith.Nat;
length_of i =
  (case i of {
    Inc n ->
      Arith.plus_nat
        (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
        (Arith.Nat_of_num (Arith.Bit1 (Arith.Bit0 (Arith.Bit0 Arith.One))));
    Dec n _ ->
      Arith.plus_nat
        (Arith.times_nat (Arith.Nat_of_num (Arith.Bit0 Arith.One)) n)
        (Arith.Nat_of_num
          (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 (Arith.Bit0 Arith.One)))));
    Goto _ -> Arith.Nat_of_num Arith.One;
  });

layout_of :: [Abc_inst] -> [Arith.Nat];
layout_of ap = map length_of ap;

tpairs_of :: [Abc_inst] -> [(Arith.Nat, Abc_inst)];
tpairs_of ap =
  zip (map (start_of (layout_of ap))
        (List.upt Arith.Zero_nat (List.size_list ap)))
    ap;

tms_of :: [Abc_inst] -> [[(Turing.Action, Arith.Nat)]];
tms_of ap = map (\ (a, b) -> ci (layout_of ap) a b) (tpairs_of ap);

tm_of :: [Abc_inst] -> [(Turing.Action, Arith.Nat)];
tm_of ap = concat (tms_of ap);

abc_lm_s :: [Arith.Nat] -> Arith.Nat -> Arith.Nat -> [Arith.Nat];
abc_lm_s am n v =
  (if Arith.less_nat n (List.size_list am) then List.list_update am n v
    else am ++ List.replicate (Arith.minus_nat n (List.size_list am))
                 Arith.Zero_nat ++
                 [v]);

abc_lm_v :: [Arith.Nat] -> Arith.Nat -> Arith.Nat;
abc_lm_v lm n =
  (if Arith.less_nat n (List.size_list lm) then List.nth lm n
    else Arith.Zero_nat);

abc_fetch :: Arith.Nat -> [Abc_inst] -> Maybe Abc_inst;
abc_fetch s p =
  (if Arith.less_nat s (List.size_list p) then Just (List.nth p s)
    else Nothing);

abc_step_l ::
  (Arith.Nat, [Arith.Nat]) -> Maybe Abc_inst -> (Arith.Nat, [Arith.Nat]);
abc_step_l (s, lm) a =
  (case a of {
    Nothing -> (s, lm);
    Just (Inc n) ->
      let {
        nv = abc_lm_v lm n;
      } in (Arith.plus_nat s (Arith.Nat_of_num Arith.One),
             abc_lm_s lm n (Arith.plus_nat nv (Arith.Nat_of_num Arith.One)));
    Just (Dec n e) ->
      let {
        nv = abc_lm_v lm n;
      } in (if Arith.equal_nat nv Arith.Zero_nat
             then (e, abc_lm_s lm n Arith.Zero_nat)
             else (Arith.plus_nat s (Arith.Nat_of_num Arith.One),
                    abc_lm_s lm n
                      (Arith.minus_nat nv (Arith.Nat_of_num Arith.One))));
    Just (Goto n) -> (n, lm);
  });

abc_steps_l ::
  (Arith.Nat, [Arith.Nat]) ->
    [Abc_inst] -> Arith.Nat -> (Arith.Nat, [Arith.Nat]);
abc_steps_l (s, lm) p n =
  (if Arith.equal_nat n Arith.Zero_nat then (s, lm)
    else abc_steps_l (abc_step_l (s, lm) (abc_fetch s p)) p
           (Arith.minus_nat n (Arith.Nat_of_num Arith.One)));

}
