signature DIAGNOSTIC = sig
  type diagnostic
  type cert
  type passed
  val finish: (string * string) option -> diagnostic -> unit
  val make_with_cert: Time.time -> Network.info ->
                      passed -> Property.sat -> diagnostic
  val make_without_cert: Time.time -> Property.sat -> diagnostic
  val property: diagnostic -> Property.sat
end

functor Diagnostic(Passed : MONO_PASSED_SET) : DIAGNOSTIC = struct
val magic_number = 42 |> SerInt.serialize
type passed = Passed.passed_set
type essential = {
  explored_states : int,
  sat : Property.sat,
  checking_time : Time.time
}

type cert = {
  renaming : JsonP.json,
  processes : int,
  clocks : int,
  vars : int,
  passed : passed
}

type diagnostic = {
  certificate : cert option,
  result : essential
}

local open Unsynchronized in
fun get_explored cyclicity reachability =
    let
      val explored = (! cyclicity) + (! reachability)
      val reset = flip change (K 0)
      val _ = (reset cyclicity; reset reachability)
    in
      explored
    end
end

fun make_binary ({processes, clocks, vars, passed, renaming} : cert) =
    let
      fun add_int x = cons (SerInt.serialize x)
    in
      (
        JsonP.show renaming
      ,
        Passed.serialize passed
        |> single
        |> add_int vars
        |> add_int clocks
        |> add_int processes
        |> Word8Vector.concat
      )
    end

fun make_cert ({renaming, processes, clocks, vars} : Network.info) passed =
    SOME {
      renaming = renaming,
      passed =  passed,
      processes = processes,
      clocks = clocks,
      vars = vars
    }

fun make_essential prop time explored =
    {
      explored_states = explored,
      sat = prop,
      checking_time = time
    }

fun make time cert prop =
    {
      certificate = cert,
      result = make_essential
                   prop
                   time
                   (get_explored CyclicityData.explored
                                 ReachabilityData.explored)
    }

fun make_with_cert time info passed =
    make
        time
        (make_cert info passed)

fun make_without_cert time prop =
    make time NONE prop


fun log_result sat =
    Log.log "Property is" (Property.to_string sat)

fun log_model name =
    Log.log "Model" name

fun log_states states =
    Log.int "States explored" states

val log_checking_time = Log.time "Checking time"
val log_cert_time = Log.time "Certificate generation and flushing Time"

fun log_essential ({sat, explored_states, checking_time} : essential) =
    (
      log_result sat;
      log_states explored_states;
      log_checking_time checking_time
    )

fun gen_and_flush_certificate renaming_name cert_name cert =
    let
      val (renaming_str, cert) = make_binary cert
      val renaming_file_name = renaming_name
      val cert_file_name = cert_name
      val _ = BinIOUtil.save_data cert_file_name magic_number cert
    in
      TextIOUtil.save_data renaming_file_name renaming_str
    end

fun flush_cert_and_log renaming certificate =
    Benchmark.time_it (gen_and_flush_certificate renaming certificate)
    #> Benchmark.add_time (apfst log_cert_time #> snd)


fun finish (SOME (renaming_path, cert_path))
        ({certificate, result} : diagnostic) =
    (
      log_essential result;
      (certificate |> Option.app (flush_cert_and_log renaming_path cert_path))
    ) |
    finish NONE ({certificate, result} : diagnostic) = log_essential result

fun property ({result, ...} : diagnostic) =
    #sat result
end
