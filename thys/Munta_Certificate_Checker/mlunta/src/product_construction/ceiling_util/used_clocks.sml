signature USED_CLOCKS = sig
  type t
  type clock
  val empty: t
  val is_in: t -> clock -> bool
  val insert_clock: clock -> t -> t
  val insert_cconstr: ClockConstraint.t -> t -> t
end

structure UsedClocks : USED_CLOCKS = struct
type t = Inttab.set
type clock = int
val empty = Inttab.empty
val is_in = Inttab.defined
fun insert_clock clock = Inttab.insert_set clock

local
  open ClockConstraint
in
fun insert_cconstr cconstr =
    case cconstr of
        Lt (0, 0, _) => id |
        Le (0, 0, _) => id |
        Lt (0, x, c) => insert_clock x |
        Le (0, x, c) => insert_clock x |
        Lt (x, 0, c) => insert_clock x |
        Le (x, 0, c) => insert_clock x |
        Lt (x, y, c) => insert_clock x #> insert_clock y |
        Le (x, y, c) => insert_clock x #> insert_clock y

end
end
