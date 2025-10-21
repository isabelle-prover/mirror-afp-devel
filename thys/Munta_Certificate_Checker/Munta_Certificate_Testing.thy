section \<open>Testing Infrastructure\<close>

theory Munta_Certificate_Testing
  imports Main
begin

\<comment> \<open>Produces commands for generating a certificate for a single benchmark with \mlunta, e.g.
\<^verbatim>\<open>mluntac-poly -certificate PM_all_5.cert -renaming PM_all_5.renaming -model PM_all_5.muntax\<close>
checking it with \munta, and checking the result:
\<^verbatim>\<open>./check_benchmark.sh
  muntac -certificate PM_all_5.cert -renaming PM_all_5.renaming -model PM_all_5.muntax\<close>
\<close>
ML \<open>
fun mk_cert mlunta_path name =
  let
    val benchmark = name ^ ".muntax"
    val gen_certificate = implode_space [
      mlunta_path,
      "-certificate", name ^ ".cert",
      "-renaming", name ^ ".renaming",
      "-model", benchmark
    ]
  in
    gen_certificate
  end

val it1 = mk_cert "mluntac-poly" "PM_all_5"

fun check_cert muntac_path name =
  let
    val benchmark = name ^ ".muntax"
  in
    implode_space [
      "./check_benchmark.sh",
      muntac_path,
      "-certificate", name ^ ".cert",
      "-renaming", name ^ ".renaming",
      "-model", benchmark
    ]
  end

val it2 = check_cert "muntac" "PM_all_5"

val mlunta_dir_proper = Path.append (Path.current |> File.absolute_path) (Path.explode "mlunta")

val mlunta_dir = Path.explode "mlunta" |> File.absolute_path

val library_path =
  Path.append mlunta_dir (Path.explode "src/isalib/library.sml") |> Path.implode
val basics_path =
  Path.append mlunta_dir (Path.explode "src/isalib/basics.sml") |> Path.implode

val mlunta_certificate_path = "mlunta/src/serialization/mlunta_certificate"
\<close>

end