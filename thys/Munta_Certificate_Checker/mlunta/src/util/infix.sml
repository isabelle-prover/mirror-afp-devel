(* Taken and extended from: http://www.mlton.org/InfixingOperators  *)


infix 3 <\ /> </ \>

signature INFIXUSE =
sig
    val <\ : 'a *('a * 'b -> 'c) -> 'b -> 'c
    val \> : ('a -> 'b) * 'a -> 'b
    val /> : ('a * 'b -> 'c) * 'b -> 'a -> 'c
    val </ : 'a * ('a -> 'b) -> 'b
    (* val <| : 'a * ('a -> 'b) -> 'b *)
end

structure Infix: INFIXUSE =
struct
(* Left section      *)
fun x <\ f = fn y => f (x, y)

(* Left application  *)
fun f \> y = f y

(* Right section     *)
fun f /> y = fn x => f (x, y)

(* Right application *)
fun x </ f = f x
(* fun x <| f = x </ f *)
end

(* For using tupled ops <\ Mod.op \> *)
(* For using binary funs as infix use </ fun_name \> *)
open Infix;
