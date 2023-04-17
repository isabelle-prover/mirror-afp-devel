(*
  File:     array_map.ML
  Author:   Manuel Eberl, University of Innsbruck 

  This file implements array maps, i.e. logically a partial function from the integers
  to some values. Note that the array in the background grows whenever it needs to, but it
  never shrinks.
*)

signature ARRAY_MAP =
sig

type 'a T

val capacity : 'a T -> int
val empty : int -> 'a T
val sub : 'a T * int -> 'a option
val update : 'a T * int * 'a option -> unit
val tabulate : int * int * (int -> 'a) -> 'a T
val fromArray : 'a option array -> 'a T
val clone : 'a T -> 'a T

end


structure Array_Map : ARRAY_MAP = struct

fun growth_factor n = (3 * n) div 2

type 'a T = 'a option array Unsynchronized.ref

fun capacity a = Array.length (!a)

fun empty cap = Unsynchronized.ref (Array.array (cap, NONE))

fun sub (a, i) =
  if i < 0 orelse i >= capacity a then NONE else Array.sub (!a, i)

fun grow a i =
  if i < capacity a then ()
  else
    let
      val cap' = growth_factor i + 1
      val a' = Array.array (cap', NONE)
      val _ = Array.copy {src = !a, dst = a', di = 0}
      val _ = a := a'
    in
      ()
    end

fun update (a, i, NONE) =
      if i >= 0 andalso i < capacity a then Array.update (!a, i, NONE) else ()
  | update (a, i, x) =
      if i < 0 then
        raise Subscript
      else
        let
          val _ = grow a i
        in
          Array.update (!a, i, x)    
        end     

fun tabulate (cap, n, f) =
  let
    fun g i = if i >= n then NONE else SOME (f i)
    val cap = if cap <= 0 then growth_factor n else cap
  in
    Unsynchronized.ref (Array.tabulate (Int.max (cap, n), g))
  end

fun fromArray a =
  let
    val a' = empty (growth_factor (Array.length a))
    val _ = Array.copy {di = 0, dst = !a', src = a}
  in
    a'
  end

fun clone a = fromArray (!a)

end
