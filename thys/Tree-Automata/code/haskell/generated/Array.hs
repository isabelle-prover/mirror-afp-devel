{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Array where {


import qualified Data.Array.Diff as Arr;
--import qualified Data.Array as Arr;
import Data.Array.IArray;
import Nat;

instance Ix Nat where {
    range (Nat a, Nat b) = map Nat (range (a, b));
    index (Nat a, Nat b) (Nat c) = index (a,b) c;
    inRange (Nat a, Nat b) (Nat c) = inRange (a, b) c;
    rangeSize (Nat a, Nat b) = rangeSize (a, b);
};

type ArrayType = Arr.DiffArray Nat;
--type ArrayType = Arr.Array Nat;

-- we need to start at 1 and not 0, because the empty array
-- is modelled by having s > e for (s,e) = bounds
-- and as we are in Nat, 0 is the smallest number

array_of_size :: Nat -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (1, n);

new_array :: e -> Nat -> ArrayType e;
new_array a n = array_of_size n (repeat a);

array_length :: ArrayType e -> Nat;
array_length a = let (s, e) = bounds a in if s > e then 0 else e - s + 1;
-- the `if` is actually needed, because in Nat we have s > e --> e - s + 1 = 1

array_get :: ArrayType e -> Nat -> e;
array_get a i = a ! (i + 1);

array_set :: ArrayType e -> Nat -> e -> ArrayType e;
array_set a i e = a // [(i + 1, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (fromInteger (toInteger (length xs - 1))) xs;

array_grow :: ArrayType e -> Nat -> e -> ArrayType e;
array_grow a i x = let (s, e) = bounds a in Arr.listArray (s, e+i) (Arr.elems a ++ repeat x);

array_shrink :: ArrayType e -> Nat -> ArrayType e;
array_shrink a sz = if sz > array_length a then undefined else array_of_size sz (Arr.elems a);


}
