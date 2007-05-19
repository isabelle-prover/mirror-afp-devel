structure DFS =
struct

fun wfrec f x = f (wfrec f) x;

fun snd (a, b) = b;

fun fst (a, b) = a;

fun nexts [] n = []
  | nexts (e :: es) n =
    (if (fst e = n) then (snd e :: nexts es n) else nexts es n);

fun memberl x [] = false
  | memberl x (y :: ys) = ((x = y) orelse memberl x ys);

fun dfs2 x =
  wfrec (fn dfs2 => fn a =>
          (case a of
            (x, xa) =>
              (case xa of
                (xa, xb) =>
                  (case xa of [] => xb
                    | (xa :: xc) =>
                        (if memberl xa xb then dfs2 (x, (xc, xb))
                          else dfs2 (x, (xc,
  dfs2 (x, (nexts x xa, (xa :: xb))))))))))
    x;

fun append [] ys = ys
  | append (x :: xs) ys = (x :: append xs ys);

fun dfs x =
  wfrec (fn dfs => fn a =>
          (case a of
            (x, xa) =>
              (case xa of
                (xa, xb) =>
                  (case xa of [] => xb
                    | (xa :: xc) =>
                        (if memberl xa xb then dfs (x, (xc, xb))
                          else dfs (x, (append (nexts x xa) xc,
 (xa :: xb))))))))
    x;

val dfs = (fn x => dfs x);

val dfs2 = (fn x => dfs2 x);

end;
