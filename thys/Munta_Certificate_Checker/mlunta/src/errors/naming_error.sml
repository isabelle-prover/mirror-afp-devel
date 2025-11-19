signature NAMING_ERROR = sig
  type t

  val unknown_clock: string -> t (* renaming *)
  val unknown_var: string -> t   (* bexps renaming *)
  val unknown_proc: string -> t  (* bexps renaming *)
  val unknown_loc: string -> t   (* bexps renaming *)
  val unknown_id: int -> t       (* renaming *)
  val unknown_label: string -> t
  val ambg_proc: string -> t     (* bexps *)
  val ambg_loc: string -> t      (* bexps *)
  val ambg_var: string -> t      (* bexps *)

  val no_initial: int -> t       (* bexps *)
  val invalid_edge: int * int -> t (* bexps *)

  val duplicate: string -> t     (* bexps *)
  val print_err: (string -> 'a) -> t -> 'a
end

structure NamingError : NAMING_ERROR = struct
datatype t =
         UnknownVariable of string |
         UnknownClock of string |
         UnknownProc of string |
         UnknownLoc of string |
         UnknownId of int |
         UnknownLabel of string |
         Duplicate of string |

         AmbgProc of string |
         AmbgLoc of string |
         AmbgVar of string |

         NoInitial of int |
         InvalidEdge of int * int

fun unknown_clock x = UnknownClock x
fun unknown_var x = UnknownVariable x
fun unknown_proc x = UnknownProc x
fun unknown_loc x = UnknownLoc x
fun unknown_id x = UnknownId x
fun unknown_label x = UnknownLabel x

fun ambg_proc x = AmbgProc x
fun ambg_loc x = AmbgLoc x
fun ambg_var x = AmbgVar x

fun duplicate x = Duplicate x

fun no_initial x = NoInitial x
fun invalid_edge x = InvalidEdge x

fun print_err logf error =
    let
      val msg =
              case error of
                  UnknownVariable name => "Unknown Variable: " ^ name |
                  UnknownClock name => "Unknown Clock: " ^ name |
                  UnknownProc name => "Unknown Process: " ^ name |
                  UnknownLoc name => "Unknown Location: " ^ name |
                  UnknownId id => "Unknown Id: " ^ (Int.toString id) |
                  UnknownLabel name => "Unknown label: " ^ name |
                  AmbgProc name => "Ambigous Process: " ^ name |
                  AmbgLoc name => "Ambigous Location: " ^ name |
                  AmbgVar name => "Ambigous Variable: " ^ name |

                  NoInitial i => "The initial " ^ (Int.toString i) ^ "does not exist" |
                  Duplicate name => name ^ " occurs more than once" |
                  InvalidEdge (l, l') => "Invalid edge from " ^
                                         (Int.toString l) ^ " to " ^ (Int.toString l')
    in
      logf msg
    end
end
