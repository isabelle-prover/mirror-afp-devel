functor MluntaFn(E : DBM_ENTRY) = struct
structure Construction = Construction(E)
structure D = MakeLinDBM(E)
structure Passed = PolyToMonoPassed(structure Zone = D
                                    structure Key = Location)

structure Setup : CHECKING_SETUP = struct
structure D = D
structure Passed = Passed
end

structure Reachability = ReachabilityChecker(Setup)
structure AEventually = AlwaysEventually(Setup)
structure Leads = LeadstoChecker(Setup)

structure Comp = Compression(Setup)

structure Certify = Certification(Setup)

structure Diagnostic = Diagnostic(Passed)

fun construct extra_lu json_str =
    json_str
    |> Construction.parse_construct extra_lu Construction.print_log

fun choose_algo f g h (n : D.t Network.system) =
    let
        open Network
        open Formula
    in
        case #formula n of
            Ex _ => Ex (f n) |
            Eg _ => Eg (g n) |
            Ax _ => Ax (g n) |
            Ag _ => Ag (f n) |
            Leadsto _ => Ag (h n)
    end

local
  open Formula
  open Property
in

fun cert compress time info result =
    let
      fun certs ht =
          Diagnostic.make_with_cert
              time info ht
      val prop =
          result |> the_formula |> just_prop
    in
      case result of
          Ex (Unsatisfied ht) => certs (compress ht) prop |
          Ag (Satisfied ht)   => certs (compress ht) prop |
          _                   => Diagnostic.make_without_cert time prop
                                 |> tap (K (Log.info "* No certificate extraction possible"))
    end
end

fun check_network net =
    net
    |> choose_algo Reachability.check AEventually.check Leads.check
    |> Formula.result Property.convert

fun construct_and_check extra_lu json_str =
    json_str
    |> construct extra_lu
    |> Either.mapR (snd #> (` Network.info))
    |> Either.mapR (apsnd check_network)

fun use_time f b =
    Benchmark.add_time (fn (time, result) => Either.mapR (f time) result) b

fun check_and_then extra_lu post json_str =
    json_str
    |> Benchmark.time_it (construct_and_check extra_lu)
    |> use_time (fn time => fn (info, prop) => post info time prop)

fun no_cert_cc time formula =
    formula
    |> Formula.the_formula
    |> Property.just_prop
    |> Diagnostic.make_without_cert time


fun just_check extra_lu json_str =
    json_str
    |> check_and_then extra_lu (Diagnostic.property ooo (K no_cert_cc))


fun certcc compress renaming_path cert_path info time =
    cert compress time info
    #> Diagnostic.finish (SOME (renaming_path, cert_path))

val log_model_file = Log.log "Model"

fun checking extra_lu model json_str =
    (
      log_model_file model;
      json_str
      |> check_and_then extra_lu ((Diagnostic.finish NONE) ooo (K no_cert_cc))
    )

fun compress extra_lu compression json_str =
    case json_str |> construct extra_lu of
        Either.Left _ => id
    |   Either.Right (net, trans) => Comp.compress compression net trans

fun certify extra_lu version json_str =
    case json_str |> construct extra_lu of
        Either.Left _ => id
    |   Either.Right (net, trans) => fn x => (
        if Certify.check version net trans x
        then print "Certificate check passed.\n"
        else print "Certificate check failed.\n";
        x)

fun check_and_cert extra_lu renaming_path cert_path json_str compression certification =
      json_str
      |> check_and_then extra_lu (
          certcc
            ((if compression > 0 then compress extra_lu compression json_str else id) o
             (if certification > 0 then certify extra_lu certification json_str else id)
            )
            renaming_path cert_path
         )

val just_check_lu = just_check true
val just_check = just_check false

val checking_lu = checking true
val checking = checking false

val check_and_cert_lu = check_and_cert true
val check_and_cert = check_and_cert false
end

structure MluntaInteger = MluntaFn(Entry)
structure Mlunta32 = MluntaFn(Entry32Bit)
structure Mlunta64 = MluntaFn(Entry64Bit)
structure Mlunta = MluntaInteger
