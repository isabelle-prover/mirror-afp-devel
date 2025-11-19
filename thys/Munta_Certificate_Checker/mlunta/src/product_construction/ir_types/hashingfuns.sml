structure SimpleHash = struct
fun to_idx f x = x |> f |> Word.toIntX
fun word' (u, w) = Word.+ (u, Word.* (0w65599, w))
fun int' (i, w) = word' (Word.fromInt i, w)
fun int i = to_idx int' (i, 0w0)
fun int_vec' (v, w) = Vector.foldl int' w v
fun int_indexdict dict w = IndexDict.foldl int' w dict
fun int_arr' (arr, w) = Array.foldl int' w arr
fun int_vec v = to_idx int_vec' (v, 0w0)
fun int_arr arr = to_idx int_arr' (arr, 0w0)
end
