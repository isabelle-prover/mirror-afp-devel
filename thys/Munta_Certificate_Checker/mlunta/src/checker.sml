val usage = "Usage: $ checker " ^ "\n" ^
            "-model <json model> " ^ "\n" ^
            "-certificate <certificate path> " ^ "\n" ^
            "-renaming <renaming path> " ^ "\n" ^
            "-extra <lu | local> " ^ "\n" ^
            "[-compression <compression level>] " ^ "\n" ^
            "[-certify <certifier version>] " ^ "\n" ^
            "[-num-threads <number of threads>]"

fun dissect_arguments p args =
    let
      fun get' [] = NONE |
          get' (flag::arg::args) = if p flag then SOME (arg) else
                                   get' args |
          get' (_::_) = Exn.error usage
    in
      get' args
    end

datatype extrapolation =
         Local |
         LU

fun extra_from_str "lu" = SOME LU |
    extra_from_str "local" = SOME Local |
    extra_from_str _ = NONE

fun flags args =
    let
      val model =
          dissect_arguments
              (fn "-model" => true | "-m" => true | _ => false) args
      val renaming_path =
          dissect_arguments
              (fn "-renaming" => true | "-r" => true | _ => false) args
      val cert_path =
          dissect_arguments
              (fn "-certificate" => true | "-c" => true | _ => false) args
      val compression =
          dissect_arguments
              (fn "-compression" => true | "-cl" => true | _ => false) args
      val certification =
          dissect_arguments
              (fn "-certify" => true | "-cc" => true | _ => false) args
      val num_threads =
          dissect_arguments
              (fn "-num-threads" => true | "-n" => true | _ => false) args
      val is_extra = fn "-extra" => true | "-e" => true | _ => false
      val extra =
          case dissect_arguments is_extra args of
              NONE => (print "ok"; SOME Local) |
              SOME str => extra_from_str str
    in
      (model, extra, renaming_path, cert_path, compression, certification,
       num_threads)
    end

fun read_json json = TextIOUtil.read_file json


val log_renaming_file = Log.log "Renaming File"
val log_certificate_file = Log.log "Certificate File"
val log_model_file = Log.log "Model"
val log_compression = Log.log "Compression Level"
val log_certification = Log.log "Certification Level"
val log_num_threads = Log.log "Number of Threads"
fun log_extra Local = Log.log "Extrapolation" "local ceilings"
  | log_extra LU    = Log.log "Extrapolation" "local lu-ceilings"

fun log_config (extra, model, renaming, cert, compression, certification, num_threads) =
    (
      log_extra extra;
      log_model_file model;
      log_renaming_file renaming;
      log_certificate_file cert;
      log_compression compression;
      log_certification certification;
      log_num_threads num_threads
    )

fun check_and_cert_network extra model renaming cert compression certification
                           num_threads =
    (
      log_config (extra, model, renaming, cert, compression, certification,
                  num_threads);
      Par_List.set_num_threads (Int.fromString num_threads |> the);
      (case extra of
           Local => Mlunta.check_and_cert |
           LU => Mlunta.check_and_cert_lu)
          renaming
          cert
          (read_json model)
          (Int.fromString compression |> the)
          (Int.fromString certification |> the)
    )

fun check_network model =
    Mlunta.checking model (read_json model)
fun check_network_lu model =
    Mlunta.checking_lu model (read_json model)

fun check args =
    case args of
        (SOME model, SOME extra, SOME renaming, SOME cert, compression,
         certification, num_threads) => check_and_cert_network
                                            extra
                                            model
                                            renaming
                                            cert
                                            (the_default "0" compression)
                                            (the_default "0" certification)
                                            (the_default "1" num_threads)
      | (SOME model, NONE, NONE, NONE, NONE, NONE, NONE) => check_network model
      | (SOME model, SOME Local, NONE, NONE, NONE, NONE, NONE) => check_network model
      | (SOME model, SOME LU, NONE, NONE, NONE, NONE, NONE) => check_network_lu model
      | _ =>  Exn.error usage

fun main () =
    flags (CommandLine.arguments ())
    |> Benchmark.time_it check
    |> Benchmark.add_time (apfst (Log.time "Total Time: ") #> snd)
    handle Exn.ERROR msg => Either.fail (println msg)

val _ = main ()
