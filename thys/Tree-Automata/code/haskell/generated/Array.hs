module Array where {


--import qualified Data.Array.Diff as Arr;
import qualified Data.Array as Arr;

type ArrayType = Arr.Array Integer;


array_of_size :: Integer -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (0, n-1);

new_array :: e -> Integer -> ArrayType e;
new_array a n = array_of_size n (repeat a);

array_length :: ArrayType e -> Integer;
array_length a = let (s, e) = Arr.bounds a in e;

array_get :: ArrayType e -> Integer -> e;
array_get a i = a Arr.! i;

array_set :: ArrayType e -> Integer -> e -> ArrayType e;
array_set a i e = a Arr.// [(i, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (toInteger (length xs)) xs;

array_grow :: ArrayType e -> Integer -> e -> ArrayType e;
array_grow a i x = let (s, e) = Arr.bounds a in Arr.listArray (s, e+i) (Arr.elems a ++ repeat x);

array_shrink :: ArrayType e -> Integer -> ArrayType e;
array_shrink a sz = if sz > array_length a then undefined else array_of_size sz (Arr.elems a);


}
