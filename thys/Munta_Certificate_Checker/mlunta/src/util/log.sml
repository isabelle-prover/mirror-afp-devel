signature LOG = sig
  val info: string -> unit
  val log: string -> string -> unit
  val time: string -> Time.time -> unit
  val int: string -> int -> unit
end

structure Log : LOG = struct
fun info msg =
    println ("+ " ^ msg)
fun log header msg =
    info (header ^ ": " ^ msg)
fun time header time =
    log header (Time.toString time)
fun int header n =
    log header (Int.toString n)
end
