structure Generated =
struct

fun op_64 [] ys = ys
  | op_64 (x :: xs) ys = (x :: op_64 xs ys);

fun Next [] n = []
  | Next (e :: es) n =
    (if (fst e = n) then (snd e :: Next es n) else Next es n);

fun op_mem x [] = false
  | op_mem x (y :: ys) = (if (y = x) then true else op_mem x ys);

fun dfs x =
  wf_rec
    (fn dfs => fn a =>
      (case a of
        (x, xa) =>
          (case xa of
            (xa, xb) =>
              (case xa of [] => xb
                | (xa :: xc) =>
                    (if op_mem xa xb then dfs (x, (xc, xb))
                      else dfs (x, (op_64 (Next x xa) xc, (xa :: xb))))))))
    x;

val dfs = (fn x => dfs x);

end;
