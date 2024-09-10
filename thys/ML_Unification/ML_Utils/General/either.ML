(*  Title:      ML_Utils/either.ML
    Author:     Kevin Kappelmann
*)
signature EITHER =
sig
  datatype ('a, 'b) either = Left of 'a | Right of 'b
  val cases : ('a -> 'c) -> ('b -> 'c) -> ('a, 'b) either -> 'c
end

structure Either : EITHER =
struct
datatype ('a, 'b) either = Left of 'a | Right of 'b

fun cases f _ (Left x) = f x
  | cases _ g (Right y) = g y

end