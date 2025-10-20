(* XXX: look at library.ML of isabelle *)
fun cp_arr arr =
    let
      val cp = Array.array (Array.length arr, Array.sub (arr, 0))
      fun copy cp =
              Array.copy ({src = arr, dst = cp, di = 0})
    in
      tap copy cp
    end

fun foldl_until stop f acc xs =
    case xs of
        [] => acc |
        (x::xs') => let val acc' = f (x, acc) in
                    if stop acc' then acc'
                    else foldl_until stop f acc' xs' end

fun --> f = curry f
fun && f = uncurry f

local
fun fold_until_sq stop f =
      foldl_until stop (swap #-> (foldl_until stop f))
in
fun fold_until_snd f =
    fold_until_sq snd f
end

fun rev_map_filter f = foldl (fn (x, acc) => case f x of
                                                 NONE => acc |
                                                 SOME x' => x'::acc) []
fun flip f x y = f y x
fun id x = x

fun find_all' _ [] acc = acc |
    find_all' p (x::xs) acc = if p x then x::acc
                             else acc
fun find_all p xs = find_all' p xs []

fun filter_index (P: int -> 'a -> bool) xs: 'a list =
  let
    fun loop i acc [] = acc
      | loop i acc (x :: xs) = loop (i + 1) (if P i x then x :: acc else acc) xs
  in loop 0 [] xs |> rev end

fun all P (x :: xs) = P x andalso all P xs
  | all P [] = true

fun exists P (x :: xs) = P x orelse exists P xs
  | exists P [] = false

fun remove i xs = take i xs @ drop (i + 1) xs

fun println msg = msg ^ "\n" |> print
fun undefined x = (println "undefined function" |> Library.undefined)
fun debug_info msg x = tap (K (println msg)) x
fun debug x = debug_info "here" x
