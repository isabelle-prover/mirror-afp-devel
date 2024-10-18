(*  Title:      ML_Utils/either.ML
    Author:     Kevin Kappelmann
*)
signature EITHER =
sig
  datatype ('a, 'b) either = Left of 'a | Right of 'b
  val cases : ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) either -> 'c
  val map : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) either -> ('c, 'd) either
  val map_left : ('a -> 'c) -> ('a, 'b) either -> ('c, 'b) either
  val map_right : ('b -> 'c) -> ('a, 'b) either -> ('a, 'c) either
  val of_opt : 'a option -> (unit, 'a) either
end

structure Either : EITHER =
struct
datatype ('a, 'b) either = Left of 'a | Right of 'b

fun cases f _ (Left x) = f x
  | cases _ g (Right y) = g y

fun map f _ (Left x) = Left (f x)
  | map _ g (Right x) = Right (g x)

fun map_left f (Left x) = Left (f x)
  | map_left _ (Right x) = Right x

fun map_right f (Right x) = Right (f x)
  | map_right _ (Left x) = Left x

fun of_opt NONE = Left ()
  | of_opt (SOME x) = Right x

end