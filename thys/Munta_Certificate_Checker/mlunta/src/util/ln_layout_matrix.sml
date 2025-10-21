(* XXX: Add testing *)
structure LnLayoutMatrix :> MATRIX = struct
type dim = int
type 'a matrix = dim * 'a Array.array
val dim = fst
fun foldli f start m = snd m |> Array.foldli f start
fun sub_arr i (_,arr) = Array.sub (arr, i)
fun create n init =
    (n * n, init)
    |> Array.array
    |> pair n


fun fromList ls =
    ls
    |> List.foldr (fn (elem, (len, acc)) =>
                       (len + 1, elem @ acc)) (0, [])
    |> apsnd Array.fromList

fun loc n i j = i * n + j
fun sub i j (n, arr) = Array.sub (arr, loc n i j)
fun update i j x (n, arr) = Array.update (arr, loc n i j, x)
(* fun updatef i j f m = update i j (sub i j m |> f) m *)
fun modifyi f (n, mat) = (Array.modifyi f mat; (n, mat))
fun foldl f acc mat = snd mat |> Array.foldl f acc
fun appij f (n, matrix) =
    let
          fun doapp i j =
              if i = n then ()
              else if j = n then doapp (i+1) 0
              else
                    (
                      f (i, j, (sub i j (n, matrix)));
                      doapp i (j+1)
                    )
    in
          doapp 0 0
    end
fun modifij f dbm =
    appij (fn (i, j, elem) => update i j (f (i, j, elem) dbm) dbm )

fun copy mat = mat |> apsnd cp_arr
fun alli p (_, m) =
    let
      val n = Array.length m
      fun doalli i =
          if i = n then true
          else if p (i, Array.sub (m, i)) then doalli (i + 1)
          else false
    in doalli 0 end

fun cmp p l r =
    alli (fn (i, elem) => p (elem, (sub_arr i r))) l
end
