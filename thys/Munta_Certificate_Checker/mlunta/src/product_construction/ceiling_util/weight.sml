signature WEIGHT = sig
  type t
  val add: t -> t -> t
  val max: t -> t -> t
  val zero: t
  val show: t -> string
  val from_clock_bound: int -> t option
  val from_int: int -> t
  val min: t -> t -> t
  val neg: t -> t
end

structure IntWeight : WEIGHT = struct
type t = int
val add = curry Int.+
val max = curry Int.max
val min = curry Int.min
val zero = 0
val show = Int.toString
val from_clock_bound = SOME o Int.abs
val from_int = Int.abs
val neg = ~
end

structure LowerBound : WEIGHT = struct
type t = int
val add = curry Int.+
val max = curry Int.max
val min = curry Int.min
val zero = 0
val show = Int.toString
val from_int = Int.abs
fun from_clock_bound c = if c <= 0 then SOME (Int.abs c) else NONE
val neg = ~
end

structure UpperBound : WEIGHT = struct
type t = int
val add = curry Int.+
val max = curry Int.max
val min = curry Int.min
val zero = 0
val show = Int.toString
val from_int = Int.abs
fun from_clock_bound c = if c >= 0 then SOME c else NONE
val neg = ~
end
