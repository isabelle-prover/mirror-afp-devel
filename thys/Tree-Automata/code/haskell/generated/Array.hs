{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Array where {


import qualified Data.Array.Diff;
import Data.Array.IArray;

type ArrayType = Data.Array.Diff.DiffArray Int;

new_array :: e -> Int -> ArrayType e;
new_array a n = Data.Array.Diff.listArray (0, n - 1) (take n (repeat a));

array_length :: ArrayType e -> Int;
array_length a = let (s, e) = bounds a in e - s + 1;

array_get :: ArrayType e -> Int -> e;
array_get a i = a ! i;

array_set :: ArrayType e -> Int -> e -> ArrayType e;
array_set a i e = a // [(i, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = Data.Array.Diff.listArray (0, length xs - 1) xs;



}
