{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module SAIS(Nat, sais) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just), Int, show, Show);
import qualified Prelude;

data Nat = Zero_nat | Suc Nat;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

nat_to_int :: Nat -> Int;
nat_to_int Zero_nat = 0;
nat_to_int (Suc n) = 1 + nat_to_int n;

nat_to_string :: Nat -> String;
nat_to_string n = show (nat_to_int n);

int_to_nat :: Int -> Nat;
int_to_nat 0 = Zero_nat;
int_to_nat n = Suc (int_to_nat ((abs n) - 1));

instance Show Nat where {
  show a = nat_to_string a;
};

instance Eq Nat where {
  a == b = equal_nat a b;
};

bot_nat :: Nat;
bot_nat = Zero_nat;

class Bot a where {
  bot :: a;
};

instance Bot Nat where {
  bot = bot_nat;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Nat where {
};

instance Order Nat where {
};

class (Order a) => Linorder a where {
};

instance Linorder Nat where {
};

class (Bot a, Order a) => Order_bot a where {
};

instance Order_bot Nat where {
};

data Set a = Set [a] | Coset [a];

data SL_types = S_type | L_type;

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) (Suc n) = nth xs n;
nth (x : xs) Zero_nat = x;

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (Suc i) j else []);

drop :: forall a. Nat -> [a] -> [a];
drop n [] = [];
drop n (x : xs) = (case n of {
                    Zero_nat -> x : xs;
                    Suc m -> drop m xs;
                  });

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) = (case n of {
                    Zero_nat -> [];
                    Suc m -> x : take m xs;
                  });

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if member xs x then remdups xs else x : remdups xs);

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member xs x) && distinct xs;

repeatatm ::
  forall a b. Nat -> (a -> b -> Bool) -> (a -> b -> a) -> a -> b -> a;
repeatatm Zero_nat uu uv acc uw = acc;
repeatatm (Suc n) f g acc obsv =
  (if f acc obsv then acc else repeatatm n f g (g acc obsv) obsv);

repeat :: forall a b. Nat -> (a -> b -> a) -> a -> b -> a;
repeat n f a b = repeatatm n (\ _ _ -> False) f a b;

replicate :: forall a. Nat -> a -> [a];
replicate Zero_nat x = [];
replicate (Suc n) x = x : replicate n x;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

card :: forall a. (Eq a) => Set a -> Nat;
card (Set xs) = size_list (remdups xs);

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update (x : xs) (Suc i) y = x : list_update xs i y;
list_update (x : xs) Zero_nat y = y : xs;
list_update [] i y = [];

bucket_upt_code ::
  forall a. (Linorder a, Order_bot a) => (a -> Nat) -> [a] -> Nat -> Set Nat;
bucket_upt_code alpha t b =
  Set (filter (\ x -> less_nat (alpha (nth t x)) b)
        (upt Zero_nat (size_list t)));

bucket_upt ::
  forall a. (Linorder a, Order_bot a) => (a -> Nat) -> [a] -> Nat -> Set Nat;
bucket_upt alpha t b = bucket_upt_code alpha t b;

bucket_end ::
  forall a. (Linorder a, Order_bot a) => (a -> Nat) -> [a] -> Nat -> Nat;
bucket_end alpha t b = card (bucket_upt alpha t (Suc b));

equal_SL_types :: SL_types -> SL_types -> Bool;
equal_SL_types S_type L_type = False;
equal_SL_types L_type S_type = False;
equal_SL_types L_type L_type = True;
equal_SL_types S_type S_type = True;

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

all_interval_nat :: (Nat -> Bool) -> Nat -> Nat -> Bool;
all_interval_nat p i j = less_eq_nat j i || p i && all_interval_nat p (Suc i) j;

list_less_ns :: forall a. (Eq a, Linorder a) => [a] -> [a] -> Bool;
list_less_ns xs ys =
  not (all_interval_nat
        (not .
          (\ n ->
            less_eq_nat n (size_list ys) &&
              all_interval_nat (\ i -> nth xs i == nth ys i) Zero_nat n &&
                (if equal_nat (size_list ys) n then less_nat n (size_list xs)
                  else True) &&
                  (if not (equal_nat (size_list ys) n)
                    then not (equal_nat (size_list xs) n) &&
                           less (nth xs n) (nth ys n)
                    else True)))
        Zero_nat (Suc (size_list xs)));

suffix_type ::
  forall a. (Eq a, Linorder a, Order_bot a) => [a] -> Nat -> SL_types;
suffix_type s i =
  (if list_less_ns (drop i s) (drop (Suc i) s) then S_type else L_type);

one_nat :: Nat;
one_nat = Suc Zero_nat;

is_lms :: forall a. (Eq a, Linorder a, Order_bot a) => [a] -> Nat -> Bool;
is_lms t i =
  (if less_nat Zero_nat i
    then (if equal_SL_types (suffix_type t i) S_type &&
               equal_SL_types (suffix_type t (minus_nat i one_nat)) L_type
           then True else False)
    else False);

bucket_start ::
  forall a. (Linorder a, Order_bot a) => (a -> Nat) -> [a] -> Nat -> Nat;
bucket_start alpha t b = card (bucket_upt alpha t b);

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

list_slice :: forall a. [a] -> Nat -> Nat -> [a];
list_slice xs i j = drop i (take j xs);

find_next_lms :: forall a. (Eq a, Linorder a, Order_bot a) => [a] -> Nat -> Nat;
find_next_lms t i = (case find (is_lms t) (upt (Suc i) (size_list t)) of {
                      Nothing -> size_list t;
                      Just j -> j;
                    });

next_lms_prefix ::
  forall a. (Eq a, Linorder a, Order_bot a) => [a] -> Nat -> [a];
next_lms_prefix t i = list_slice t i (Suc (find_next_lms t i));

rename_mappinga ::
  forall a.
    (Eq a, Linorder a, Order_bot a) => [a] -> [Nat] -> [Nat] -> Nat -> [Nat];
rename_mappinga uu [] names uv = names;
rename_mappinga uw [x] names i = list_update names x i;
rename_mappinga t (a : b : xs) names i =
  (if next_lms_prefix t a == next_lms_prefix t b
    then rename_mappinga t (b : xs) (list_update names a i) i
    else rename_mappinga t (b : xs) (list_update names a i) (Suc i));

rename_mapping ::
  forall a. (Eq a, Linorder a, Order_bot a) => [a] -> [Nat] -> [Nat];
rename_mapping t lms =
  rename_mappinga t lms (replicate (size_list t) (size_list t)) Zero_nat;

rename_string :: [Nat] -> [Nat] -> [Nat];
rename_string [] uu = [];
rename_string (x : xs) names = nth names x : rename_string xs names;

bucket_insert ::
  forall a.
    (Linorder a,
      Order_bot a) => (a -> Nat) -> [a] -> [Nat] -> [Nat] -> [Nat] -> [Nat];
bucket_insert alpha t uu sa [] = sa;
bucket_insert alpha t b sa (x : xs) =
  let {
    ba = alpha (nth t x);
    k = minus_nat (nth b ba) (Suc Zero_nat);
    saa = list_update sa k x;
    bb = list_update b ba k;
  } in bucket_insert alpha t bb saa xs;

abs_induce_s_step ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => ([Nat], ([Nat], Nat)) ->
                        (a -> Nat, [a]) -> ([Nat], ([Nat], Nat));
abs_induce_s_step (b, (sa, i)) (alpha, t) =
  (case i of {
    Zero_nat -> (b, (sa, Zero_nat));
    Suc n ->
      (if less_nat (Suc n) (size_list sa)
        then (case nth sa (Suc n) of {
               Zero_nat -> (b, (sa, n));
               Suc j ->
                 (case suffix_type t j of {
                   S_type -> let {
                               ba = alpha (nth t j);
                               k = minus_nat (nth b ba) (Suc Zero_nat);
                             } in (list_update b ba k, (list_update sa k j, n));
                   L_type -> (b, (sa, n));
                 });
             })
        else (b, (sa, n)));
  });

abs_induce_s_base ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => (a -> Nat) ->
                        [a] -> [Nat] -> [Nat] -> ([Nat], ([Nat], Nat));
abs_induce_s_base alpha t b sa =
  repeat (size_list t) abs_induce_s_step (b, (sa, size_list t)) (alpha, t);

abs_induce_s ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => (a -> Nat) -> [a] -> [Nat] -> [Nat] -> [Nat];
abs_induce_s alpha t b sa = (case abs_induce_s_base alpha t b sa of {
                              (_, (saa, _)) -> saa;
                            });

abs_induce_l_step ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => ([Nat], ([Nat], Nat)) ->
                        (a -> Nat, [a]) -> ([Nat], ([Nat], Nat));
abs_induce_l_step (b, (sa, i)) (alpha, t) =
  (if less_nat i (size_list sa) && less_nat (nth sa i) (size_list t)
    then (case nth sa i of {
           Zero_nat -> (b, (sa, Suc i));
           Suc j ->
             (case suffix_type t j of {
               S_type -> (b, (sa, Suc i));
               L_type ->
                 let {
                   k = alpha (nth t j);
                   l = nth b k;
                 } in (list_update b k (Suc l), (list_update sa l j, Suc i));
             });
         })
    else (b, (sa, Suc i)));

abs_induce_l_base ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => (a -> Nat) ->
                        [a] -> [Nat] -> [Nat] -> ([Nat], ([Nat], Nat));
abs_induce_l_base alpha t b sa =
  repeat (size_list t) abs_induce_l_step (b, (sa, Zero_nat)) (alpha, t);

abs_induce_l ::
  forall a.
    (Eq a, Linorder a,
      Order_bot a) => (a -> Nat) -> [a] -> [Nat] -> [Nat] -> [Nat];
abs_induce_l alpha t b sa = (case abs_induce_l_base alpha t b sa of {
                              (_, (saa, _)) -> saa;
                            });

maxa :: forall a. (Linorder a) => Set a -> a;
maxa (Set (x : xs)) = fold max xs x;

sa_induce ::
  forall a.
    (Eq a, Linorder a, Order_bot a) => (a -> Nat) -> [a] -> [Nat] -> [Nat];
sa_induce alpha t lms =
  let {
    b0 = map (bucket_end alpha t) (upt Zero_nat (Suc (alpha (maxa (Set t)))));
    b1 = map (bucket_start alpha t) (upt Zero_nat (Suc (alpha (maxa (Set t)))));
    sa = replicate (size_list t) (size_list t);
    saa = bucket_insert alpha t b0 sa (reverse lms);
    a = abs_induce_l alpha t b1 saa;
  } in abs_induce_s alpha t (list_update b0 Zero_nat Zero_nat) a;

order_lms :: [Nat] -> [Nat] -> [Nat];
order_lms lms [] = [];
order_lms lms (x : xs) = nth lms x : order_lms lms xs;

sais :: [Nat] -> [Nat];
sais [] = [];
sais [x] = [Zero_nat];
sais (a : b : xs) =
  let {
    t = a : b : xs;
    lMS0 = (filter . is_lms) t (upt Zero_nat (size_list t));
    sa = sa_induce id t lMS0;
    lms = (filter . is_lms) t sa;
    names = rename_mapping t lms;
    ta = rename_string lMS0 names;
    aa = (if distinct ta then lms else order_lms lMS0 (sais ta));
  } in sa_induce id t aa;

}

