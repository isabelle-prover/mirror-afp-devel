(* XXX: Add dbg errors *)
signature COMPILATION_ERROR = sig
  type t
  val naming: NamingError.t -> t
  val constr_err: LangError.t -> t

  (* XXX: make this to debug errors *)
  val upd_out_of_bounds: int Syntax.update -> t (* funs *)
  val invalid_index: int -> t      (* funs *)

  val unsupported: t            (* constraint bexps renaming *)
  val notyetsupported: t        (* dataguard bexps *)

  val print_err: (string -> 'a) -> t -> 'a
end

structure CompilationError : COMPILATION_ERROR = struct
datatype t =
     Naming of NamingError.t |
     LangErr of LangError.t |

     (* Should only be debug erros *)
     UpdateOutOfBounds of int Syntax.update |
     InvalidIndex of int |

     NotYetSupported |
     Unsupported

fun naming x = Naming x
fun constr_err x = LangErr x

fun invalid_index x = InvalidIndex x
fun upd_out_of_bounds x = UpdateOutOfBounds x

val unsupported = Unsupported
val notyetsupported = NotYetSupported

fun print_err logf error =
    let
      fun msg error' =
          case error' of
                  UpdateOutOfBounds (Syntax.Reset (i, v)) => "Update of Variable #"
                                                                            ^ (Int.toString i) ^
                                                                            "is updated to "
                                                                            ^ (Int.toString v) ^
                                                                            " which is out of it's bounds" |
              UpdateOutOfBounds _ => Exn.impossible () |
                  InvalidIndex i => "Invalid indexing with index: " ^ (Int.toString i) |

                  NotYetSupported => "This feature is not yet supported" |
                  Unsupported => "This is not supported by mlunta" |
              Naming _ => Exn.impossible () |
              LangErr _ => Exn.impossible ()
    in
      case error of
          Naming err => NamingError.print_err logf err |
          LangErr err => LangError.print_err logf err |
          _ => msg error |> logf

    end
end
