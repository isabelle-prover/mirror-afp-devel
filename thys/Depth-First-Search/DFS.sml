structure DFS =
struct

fun snd (a, b) = b;

fun fst (ba, b) = ba;

fun nexts [] n = []
  | nexts (e :: es) n =
    (if (fst e = n) then (snd e :: nexts es n) else nexts es n);

fun member x [] = false
  | member x (y :: ys) = ((x = y) orelse member x ys);

fun dfs2 g [] b = b
  | dfs2 g (x :: xs) ys =
    (if member x ys then dfs2 g xs ys
      else dfs2 g xs (dfs2 g (nexts g x) (x :: ys)));

fun append [] b = b
  | append (x :: xs) ys = (x :: append xs ys);

fun dfs g [] b = b
  | dfs g (x :: xs) ys =
    (if member x ys then dfs g xs ys
      else dfs g (append (nexts g x) xs) (x :: ys));

val dfs = (fn x => dfs x);

val dfs2 = (fn x => dfs2 x);

end;
