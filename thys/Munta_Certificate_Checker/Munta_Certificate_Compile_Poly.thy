section \<open>Build and Test Exported Program With Poly/ML\<close>
text_raw \<open>\label{build-poly}\<close>

theory Munta_Certificate_Compile_Poly
  imports Simple_Network_Language_Certificate_Code Munta_Certificate_Testing
begin

paragraph \<open>Mock Compilation\<close>

text \<open>
Instead of using Poly/ML's \<open>polyc\<close>, we emulate compilation within Isabelle's Poly/ML environment.
Below we also show how \<open>polyc\<close> could be used alternatively.

We prepare a few pieces of code that will be passed to Poly/ML for mocking compilation.
This will be used for evaluating the code:\<close>
ML \<open>
\<comment> \<open>from \<open>HOL/Library/code_test.ML\<close>\<close>
val flags = {environment = ML_Env.SML, redirect = false, verbose = false, catch_all = true,
          debug = NONE, writeln = writeln, warning = warning}
fun eval cmd = ML_Context.eval flags Position.none (ML_Lex.read_text (cmd, Position.none))
\<close>

\<comment> \<open>Redirecting output to file:\<close>
ML \<open>
val mock_print = \<^verbatim>\<open>
val out_stream_ref = ref (NONE : BinIO.outstream option);
fun print s =
  BinIO.output (Option.valOf (!out_stream_ref), Byte.stringToBytes s)
\<close>
\<close>

\<comment> \<open>Mocking command line arguments:\<close>
ML \<open>
val mock_cmd = \<^verbatim>\<open>
structure CommandLine =
struct

val mock_args = ref [""]
fun arguments () = !mock_args
fun set_mock_args s =
  mock_args := String.tokens (fn c => c = #" ") s;

end
\<close>
\<close>

\<comment> \<open>Set command line arguments, run \<open>main\<close>, and capture output\<close>
ML \<open>
fun run_cmd dir args =
  let
    val out_path = dir + Path.basic "out" |> Path.expand |> Path.implode
  in \<^verbatim>\<open>
CommandLine.set_mock_args "\<close> ^ args ^ \<^verbatim>\<open>";
val out_stream = BinIO.openOut "\<close> ^ out_path ^ \<^verbatim>\<open>";
val _ = out_stream_ref := SOME out_stream;
main ();
BinIO.flushOut out_stream;
BinIO.closeOut out_stream
\<close> end
\<close>

\<comment> \<open>This is essentially the content of \<open>build_muntac.sml\<close>:\<close>
ML \<open>
val files = [
  "Unsynchronized.sml",
  "Writeln.sml",
  "basics.ML",
  "library.ML",
  "parallel_task_queue.sml"
]
val mlunta_files = [
  "prelude.sml",
  "serializable.sml",
  "certificate.sml"
]
val final_files = [
  "Util.sml",
  "Muntac.sml"
]
\<close>

\<comment> \<open>Mock compiling\<close>
ML \<open>
fun mock_compile dir file_name =
  let
    val _ = eval mock_cmd
    val _ = eval mock_print
    fun mk_path file_name = Path.append dir (Path.explode file_name)
    fun mk_mlunta_path file_name =
      dir + Path.explode mlunta_certificate_path + Path.basic file_name |> Path.expand
    val _ = app (fn x => mk_path x |> ML_Context.eval_file flags) files
    val _ = ML_Context.eval_file flags (dir + Path.basic file_name)
    val _ = app (fn x => mk_mlunta_path x |> ML_Context.eval_file flags) mlunta_files
    val _ = app (fn x => mk_path x |> ML_Context.eval_file flags) final_files
  in () end
\<close>

\<comment> \<open>Also need to mock \<open>check_cert\<close>: simply pass the captured output to \<open>check_benchmark.sh\<close>\<close>
ML \<open>
fun mock_exec_check_cert dir title muntac_path name =
  let
    fun check () =
      Generated_Files.execute dir title \<^verbatim>\<open>./check_benchmark.sh cat out\<close>
    fun mk_path name ext = dir + Path.basic name |> Path.ext ext |> Path.expand |> Path.implode
    val args = implode_space [
      muntac_path,
      "-certificate", mk_path name "cert",
      "-renaming", mk_path name "renaming",
      "-model", mk_path name "muntax"
    ]
    val cmd = run_cmd dir args
    val _ = eval cmd
  in
    check ()
  end
\<close>


paragraph \<open>Compilation and Testing\<close>

text \<open>Here is how to compile Munta Certifier with Poly/ML and then run some benchmarks:\<close>

compile_generated_files "code/Certificate.ML" (in Simple_Network_Language_Certificate_Code)
  external_files
    \<open>Writeln.sml\<close>
    \<open>Util.sml\<close>
    \<open>Muntac.sml\<close>
    \<open>Mlton_Main.sml\<close>
    \<open>Unsynchronized.sml\<close>
    \<open>sequential.sml\<close>
    \<open>parallel_task_queue.sml\<close>
    \<open>build_muntac.sml\<close>
    \<open>check_benchmark.sh\<close>
    (in "ML")
  and
    \<open>HDDI_02.muntax\<close>
    \<open>HDDI_02_broadcast.muntax\<close>
    \<open>HDDI_08_broadcast.muntax\<close>
    \<open>PM_all_1.muntax\<close>
    \<open>PM_all_2.muntax\<close>
    \<open>PM_all_3.muntax\<close>
    \<open>PM_all_4.muntax\<close>
    \<open>PM_all_5.muntax\<close>
    \<open>PM_all_6.muntax\<close>
    \<open>PM_all_urgent.muntax\<close>
    \<open>bridge.muntax\<close>
    \<open>csma_05.muntax\<close>
    \<open>csma_06.muntax\<close>
    \<open>fischer.muntax\<close>
    \<open>fischer_05.muntax\<close>
    \<open>hddi_08.muntax\<close>
    \<open>light_switch.muntax\<close> (in "benchmarks")
  export_files \<open>muntac_poly\<close> (exe)
  where \<open>fn dir =>
    let
      val mock = true \<comment> \<open>whether to eval in Poly/ML instead of using \<open>polyc\<close>\<close>

      val exec = Generated_Files.execute dir

      val _ = exec \<open>Copy MLunta\<close> ("cp -r '" ^  Path.implode mlunta_dir ^ "' .")
      val _ = exec \<open>Compile MLunta\<close> "cd mlunta && mlton=$ISABELLE_MLTON make build_checker && cd .."
      val mlunta_path = "mlunta/build/mluntac-mlton"

      val _ =
        exec \<open>Copy Isabelle library files\<close>
          ("cp '" ^ library_path ^ "' library.ML && cp '" ^ basics_path ^ "' basics.ML")

      val _ =
        exec \<open>Preparation\<close>
          "mv code/Certificate.ML Certificate.ML"
      val _ =
        exec \<open>Replace int type\<close>
          "sed -i -e 's/IntInf/Int/g' Certificate.ML"
      val _ =
        exec \<open>set\<close>
          "set -x"
      val _ =
        if mock then
          (mock_compile dir "Certificate.ML";
           exec \<open>Compilation\<close> "touch muntac_poly")
        else
          exec \<open>Compilation\<close>
            ("MLUNTA_CERT=" ^ mlunta_certificate_path ^ " " ^
             \<^verbatim>\<open>$ML_HOME\<close> ^
             "/polyc -o muntac_poly build_muntac.sml")

      val muntac_path = if mock then "" else "./muntac_poly"
      val muntac_path_n6 = muntac_path ^ " -n 6" \<comment> \<open>Parallel checking for larger certificates\<close>
      val muntac_path_dc = muntac_path ^ " -dc" \<comment> \<open>For deadlock checking\<close>

      val _ = writeln "Generating certificates."

      val _ = exec \<open>Gen HDDI_02\<close> (mk_cert mlunta_path "HDDI_02")
      val _ = exec \<open>Gen HDDI_02_broadcast\<close> (mk_cert mlunta_path "HDDI_02_broadcast")
      val _ = exec \<open>Gen HDDI_08_broadcast\<close> (mk_cert mlunta_path "HDDI_08_broadcast")
      val _ = exec \<open>Gen hddi_08\<close> (mk_cert mlunta_path "hddi_08")
      val _ = exec \<open>Gen PM_all_1\<close> (mk_cert mlunta_path "PM_all_1")
      val _ = exec \<open>Gen PM_all_2\<close> (mk_cert mlunta_path "PM_all_2")
      val _ = exec \<open>Gen PM_all_3\<close> (mk_cert mlunta_path "PM_all_3")
      val _ = exec \<open>Gen PM_all_4\<close> (mk_cert mlunta_path "PM_all_4")
      val _ = exec \<open>Gen PM_all_5\<close> (mk_cert mlunta_path "PM_all_5")
      val _ = exec \<open>Gen csma_05\<close> (mk_cert mlunta_path "csma_05")
      val _ = exec \<open>Gen csma_06\<close> (mk_cert mlunta_path "csma_06")
      val _ = exec \<open>Gen fischer_05\<close> (mk_cert mlunta_path "fischer_05")

      val _ = writeln "Finished generating certificates. Now checking.";

      fun exec_check_cert title muntac_path name =
        if mock then
          mock_exec_check_cert dir title muntac_path name
        else
          exec title (check_cert muntac_path name)

      val _ = exec_check_cert \<open>Test HDDI_02\<close> muntac_path "HDDI_02"
      val _ = exec_check_cert \<open>Test HDDI_02_broadcast\<close> muntac_path "HDDI_02_broadcast"
      val _ = exec_check_cert \<open>Test HDDI_08_broadcast\<close> muntac_path "HDDI_08_broadcast"
      val _ = exec_check_cert \<open>Test PM_all_1\<close> muntac_path "PM_all_1"
      val _ = exec_check_cert \<open>Test PM_all_2\<close> muntac_path "PM_all_2"
      val _ = exec_check_cert \<open>Test PM_all_3\<close> muntac_path "PM_all_3"
      val _ = exec_check_cert \<open>Test csma_05\<close> muntac_path_n6 "csma_05"
      \<comment> \<open>30 s on an M1 Mac\<close>
      \<^cancel>\<open>val _ = exec_check_cert \<open>Test csma_06\<close> muntac_path_n6 "csma_06"\<close>
      val _ = exec_check_cert \<open>Test fischer_05\<close> muntac_path_n6 "fischer_05"
      val _ = exec_check_cert \<open>Test hddi_08\<close> muntac_path "hddi_08"
      val _ = exec_check_cert \<open>Test PM_all_4\<close> muntac_path "PM_all_4"
      \<comment> \<open>60 s on an M1 Mac\<close>
      \<^cancel>\<open>val _ = exec_check_cert \<open>Test PM_all_5\<close> muntac_path_n6 "PM_all_5"\<close>

      val _ = exec_check_cert \<open>Test deadlock HDDI_02\<close> muntac_path_dc "HDDI_02"
    in () end\<close>

end
