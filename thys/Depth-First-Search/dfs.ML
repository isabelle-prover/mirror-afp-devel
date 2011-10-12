structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure List : sig
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
end = struct

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

end; (*struct List*)

structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun fst (a, b) = a;

fun snd (a, b) = b;

end; (*struct Product_Type*)

structure DFS : sig
  val nexts : (int * int) list -> int -> int list
  val equal_node : int HOL.equal
  val dfs : (int * int) list -> int list -> int list -> int list
  val dfs2 : (int * int) list -> int list -> int list -> int list
end = struct

fun nexts [] n = []
  | nexts (e :: es) n =
    (if (((Product_Type.fst e) : int) = n) then Product_Type.snd e :: nexts es n
      else nexts es n);

val equal_node = {equal = (fn a => fn b => ((a : int) = b))} : int HOL.equal;

fun dfs g [] ys = ys
  | dfs g (x :: xs) ys =
    (if List.member equal_node ys x then dfs g xs ys
      else dfs g (nexts g x @ xs) (x :: ys));

fun dfs2 g [] ys = ys
  | dfs2 g (x :: xs) ys =
    (if List.member equal_node ys x then dfs2 g xs ys
      else dfs2 g xs (dfs2 g (nexts g x) (x :: ys)));

end; (*struct DFS*)
