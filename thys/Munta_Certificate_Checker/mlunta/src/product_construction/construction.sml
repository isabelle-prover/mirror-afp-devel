(* Maybe: Add better trace info *)
(* XXX: add a log for renaming *)

structure BasicSteps = struct
fun construct network =
    network
    |> RewriteBexps.network
    |> tap (K (Log.info "Renaming"))
    |> Either.bindR Renaming.network
    |> Either.mapR RewriteConstraint.network
end

functor DBMStages(E: DBM_ENTRY) = struct
structure Ceilings = IntLocalClockCeiling(E)
structure Funs = ConstructFuns(E)
structure TransSystem = ProductTransition(E)
structure NetworkSystem = TransitionComposition(E)

fun construct extra_lu network =
    network
    |> (Ceilings.network extra_lu)
    |> Funs.network
    |> Either.mapR AutomatonPreprocessing.network
    |> Either.mapR TransSystem.network
    |> Either.mapR (fn x => (
      x |> #transition_system |> NetworkSystem.gen_discrete_transitions, NetworkSystem.network extra_lu x))

end

functor Construction(E : DBM_ENTRY) = struct
structure DBMStageConstruction = DBMStages(E)

fun construct extra_lu network =
    network
    |> BasicSteps.construct
    |> Either.bindR (DBMStageConstruction.construct extra_lu)
    |> tap (K (Log.info "Running Check"))

fun parse_construct extra_lu err_log =
    Parser.parse
    #> Either.bindR (construct extra_lu)
    #> Either.mapL err_log

fun print_log errs = app Error.print_err errs

fun to_file file_name errs =
    let
      val output_strm = TextIO.openOut ("/tmp/" ^ file_name ^ ".log")
    in
      (
        app (Error.err_to_str #> (pair output_strm) #> TextIO.output) errs;
        TextIO.closeOut output_strm
      )
    end
end
