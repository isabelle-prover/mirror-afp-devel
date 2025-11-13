(*  Title:      Zippy/zipper_position.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_POSITION =
sig
  (*list of x-positions starting from the root node stored from right to left;
  init=0, left=negative, right=positive*)
  type pos = int list
  val init_x : int
  val init : pos
  val left : pos -> pos
  val right : pos -> pos
  val down : pos -> pos
  val up : pos -> pos option
end

structure Zipper_Position : ZIPPER_POSITION =
struct
type pos = int list
val init_x = 0
val init = [init_x]
fun left (x :: xs) = x - 1 :: xs
fun right (x :: xs) = x + 1 :: xs
fun down xs = init_x :: xs
fun up [] = NONE
  | up (_ :: xs) = SOME xs
end