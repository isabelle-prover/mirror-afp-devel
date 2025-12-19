{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Arith(Num(..), Nat(..), plus_nat, Plus(..), Zero(..), Semigroup_add,
         Monoid_add, suc, num_of_nat, equal_nat, minus_nat, less_nat, times_nat,
         less_eq_nat, num_of_integer, divide_nat, modulo_nat)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified HOL;
import qualified Product_Type;
import qualified Option;

data Num = One | Bit0 Num | Bit1 Num;

plus_num :: Num -> Num -> Num;
plus_num One One = Bit0 One;
plus_num One (Bit0 n) = Bit1 n;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num (Bit0 m) One = Bit1 m;
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);

data Nat = Zero_nat | Nat_of_num Num;

plus_nat :: Nat -> Nat -> Nat;
plus_nat Zero_nat n = n;
plus_nat m Zero_nat = m;
plus_nat (Nat_of_num k) (Nat_of_num l) = Nat_of_num (plus_num k l);

class Plus a where {
  plus :: a -> a -> a;
};

instance Plus Nat where {
  plus = plus_nat;
};

class Zero a where {
  zero :: a;
};

instance Zero Nat where {
  zero = Zero_nat;
};

class (Plus a) => Semigroup_add a where {
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

instance Semigroup_add Nat where {
};

instance Monoid_add Nat where {
};

suc :: Nat -> Nat;
suc n = plus_nat n (Nat_of_num One);

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

num_of_nat :: Nat -> Num;
num_of_nat Zero_nat = One;
num_of_nat (Nat_of_num k) = k;

dup :: Nat -> Nat;
dup Zero_nat = Zero_nat;
dup (Nat_of_num k) = Nat_of_num (Bit0 k);

equal_num :: Num -> Num -> Bool;
equal_num (Bit0 x2) (Bit1 x3) = False;
equal_num (Bit1 x3) (Bit0 x2) = False;
equal_num One (Bit1 x3) = False;
equal_num (Bit1 x3) One = False;
equal_num One (Bit0 x2) = False;
equal_num (Bit0 x2) One = False;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = True;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat Zero_nat = True;
equal_nat Zero_nat (Nat_of_num l) = False;
equal_nat (Nat_of_num k) Zero_nat = False;
equal_nat (Nat_of_num k) (Nat_of_num l) = equal_num k l;

sub :: Num -> Num -> Maybe Nat;
sub One One = Just Zero_nat;
sub (Bit0 m) One = Just (Nat_of_num (bitM m));
sub (Bit1 m) One = Just (Nat_of_num (Bit0 m));
sub One (Bit0 n) = Nothing;
sub One (Bit1 n) = Nothing;
sub (Bit0 m) (Bit0 n) = Option.map_option dup (sub m n);
sub (Bit1 m) (Bit1 n) = Option.map_option dup (sub m n);
sub (Bit1 m) (Bit0 n) =
  Option.map_option (\ q -> plus_nat (dup q) (Nat_of_num One)) (sub m n);
sub (Bit0 m) (Bit1 n) =
  (case sub m n of {
    Nothing -> Nothing;
    Just q ->
      (if equal_nat q Zero_nat then Nothing
        else Just (minus_nat (dup q) (Nat_of_num One)));
  });

minus_nat :: Nat -> Nat -> Nat;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;
minus_nat (Nat_of_num k) (Nat_of_num l) = (case sub k l of {
    Nothing -> Zero_nat;
    Just j -> j;
  });

less_num :: Num -> Num -> Bool;
less_num m One = False;
less_num One (Bit0 n) = True;
less_num One (Bit1 n) = True;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit1 m) (Bit0 n) = less_num m n;

less_eq_num :: Num -> Num -> Bool;
less_eq_num One n = True;
less_eq_num (Bit0 m) One = False;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;

less_nat :: Nat -> Nat -> Bool;
less_nat m Zero_nat = False;
less_nat Zero_nat (Nat_of_num l) = True;
less_nat (Nat_of_num k) (Nat_of_num l) = less_num k l;

times_num :: Num -> Num -> Num;
times_num m One = m;
times_num One n = n;
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));

times_nat :: Nat -> Nat -> Nat;
times_nat Zero_nat n = Zero_nat;
times_nat m Zero_nat = Zero_nat;
times_nat (Nat_of_num k) (Nat_of_num l) = Nat_of_num (times_num k l);

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat Zero_nat n = True;
less_eq_nat (Nat_of_num k) Zero_nat = False;
less_eq_nat (Nat_of_num k) (Nat_of_num l) = less_eq_num k l;

divmod_step_nat :: Nat -> (Nat, Nat) -> (Nat, Nat);
divmod_step_nat l qr =
  (case qr of {
    (q, r) ->
      (if less_eq_nat l r
        then (plus_nat (times_nat (Nat_of_num (Bit0 One)) q) (Nat_of_num One),
               minus_nat r l)
        else (times_nat (Nat_of_num (Bit0 One)) q, r));
  });

divmod_nata :: Num -> Num -> (Nat, Nat);
divmod_nata m One = (Nat_of_num m, Zero_nat);
divmod_nata One (Bit0 n) = (Zero_nat, Nat_of_num One);
divmod_nata One (Bit1 n) = (Zero_nat, Nat_of_num One);
divmod_nata (Bit0 m) (Bit0 n) =
  (case divmod_nata m n of {
    (q, r) -> (q, times_nat (Nat_of_num (Bit0 One)) r);
  });
divmod_nata (Bit1 m) (Bit0 n) =
  (case divmod_nata m n of {
    (q, r) ->
      (q, plus_nat (times_nat (Nat_of_num (Bit0 One)) r) (Nat_of_num One));
  });
divmod_nata (Bit0 m) (Bit1 n) =
  (if less_eq_num m n then (Zero_nat, Nat_of_num (Bit0 m))
    else divmod_step_nat (Nat_of_num (Bit1 n))
           (divmod_nata (Bit0 m) (Bit0 (Bit1 n))));
divmod_nata (Bit1 m) (Bit1 n) =
  (if less_num m n then (Zero_nat, Nat_of_num (Bit1 m))
    else divmod_step_nat (Nat_of_num (Bit1 n))
           (divmod_nata (Bit1 m) (Bit0 (Bit1 n))));

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat Zero_nat n = (Zero_nat, Zero_nat);
divmod_nat m Zero_nat = (Zero_nat, m);
divmod_nat (Nat_of_num k) (Nat_of_num l) = divmod_nata k l;

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else Product_Type.apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

num_of_integer :: Integer -> Num;
num_of_integer k =
  (if k <= (1 :: Integer) then One
    else (case divmod_integer k (2 :: Integer) of {
           (l, j) -> let {
                       la = num_of_integer l;
                       lb = plus_num la la;
                     } in (if j == (0 :: Integer) then lb else plus_num lb One);
         }));

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = fst (divmod_nat m n);

modulo_nat :: Nat -> Nat -> Nat;
modulo_nat m n = snd (divmod_nat m n);

}
