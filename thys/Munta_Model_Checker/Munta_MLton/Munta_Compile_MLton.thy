section \<open>Build and Test Exported Program With MLton\<close>
text_raw \<open>\label{build-mlton}\<close>

theory Munta_Compile_MLton
  imports Munta_Model_Checker.Simple_Network_Language_Export_Code
begin

\<comment> \<open>Produces a command for checking a single benchmark, e.g.:
\<^verbatim>\<open>./check_benchmark.sh 568 "Property is not satisfied" ./munta -m benchmarks/PM_all_5.muntax\<close>
\<close>
ML \<open>
fun mk_benchmark_check_gen munta mk_prop name num_states satisfied =
  let
    val prop = mk_prop satisfied
    val benchmark = name ^ ".muntax"
  in
    \<comment> \<open>this line checks that number of states and property satisfaction are correct\<close>
    "./check_benchmark.sh " ^ string_of_int num_states ^ " " ^ prop
    \<comment> \<open>this line runs Munta on the actual benchmark\<close>
    ^ " " ^ munta ^ " " ^ benchmark
  end
val mk_benchmark_check =
  mk_benchmark_check_gen "./munta -m"
    (fn satisfied =>
      if satisfied then
        \<^verbatim>\<open>"Property is satisfied!"\<close>
      else
        \<^verbatim>\<open>"Property is not satisfied!"\<close>)
val mk_benchmark_check_dc =
  mk_benchmark_check_gen "./munta -dc -m"
    (fn satisfied =>
      if satisfied then
        \<^verbatim>\<open>"Model has a deadlock!"\<close>
      else
        \<^verbatim>\<open>"Model has no deadlock!"\<close>)
val it  = mk_benchmark_check "PM_all_5" 568 false
val it1 = mk_benchmark_check_dc "hddi_08" 466 false
\<close>

text \<open>Here is how to compile Munta with MLton and then run some benchmarks:\<close>

\<comment> \<open>Commenting this out since the AFP submission machine sandboxing somehow breaks MLton.\<close>
compile_generated_files "code/Simple_Model_Checker.ML" (in Simple_Network_Language_Export_Code)
  external_files
    \<open>Unsynchronized.sml\<close>
    \<open>Writeln.sml\<close>
    \<open>Util.sml\<close>
    \<open>Muntax.sml\<close>
    \<open>Mlton_Main.sml\<close>
    \<open>library.ML\<close>
    \<open>muntax.mlb\<close>
    \<open>check_benchmark.sh\<close>
    (in "../ML")
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
    \<open>light_switch.muntax\<close> (in "../benchmarks")
  export_files \<open>munta\<close> (exe)
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute dir
      val _ =
        exec \<open>Preparation\<close>
          "mv code/Simple_Model_Checker.ML Simple_Model_Checker.ML"
      val _ =
        exec \<open>Compilation\<close>
          (\<^cancel>\<open>\<^verbatim>\<open>"$ISABELLE_MLTON" $ISABELLE_MLTON_OPTIONS\<close> ^\<close>
           \<^verbatim>\<open>"$ISABELLE_MLTON" \<close> ^
            \<comment> \<open>these additional settings have been copied from the AFP entry \<open>PAC_Checker\<close>\<close>
            \<comment> \<open>they bring down \<open>benchmarks/PM_all_6.muntax\<close> from 1000 s to 180 s on an M1 Mac\<close>
             "-const 'MLton.safe false' -verbose 1 -inline 700 -cc-opt -O3 " ^
            \<comment> \<open>this one from \<open>PAC_Checker\<close> does not work on ARM64 though\<close>
            \<^cancel>\<open>"-codegen native " ^\<close>
            \<comment> \<open>these used to be the only setting for Munta\<close>
            "-default-type int64 " ^
            "-output munta " ^
            "muntax.mlb")
      val _ = exec \<open>Test HDDI_02\<close> (mk_benchmark_check "HDDI_02" 34 false)
      val _ = exec \<open>Test HDDI_02_broadcast\<close> (mk_benchmark_check "HDDI_02_broadcast" 34 false)
      val _ = exec \<open>Test HDDI_08_broadcast\<close> (mk_benchmark_check "HDDI_08_broadcast" 466 false)
      val _ = exec \<open>Test PM_all_1\<close> (mk_benchmark_check "PM_all_4" 529 false)
      val _ = exec \<open>Test PM_all_1\<close> (mk_benchmark_check "PM_all_1" 338 false)
      val _ = exec \<open>Test PM_all_2\<close> (mk_benchmark_check "PM_all_2" 2828 false)
      val _ = exec \<open>Test PM_all_3\<close> (mk_benchmark_check "PM_all_3" 3994 false)
      val _ = exec \<open>Test PM_all_4\<close> (mk_benchmark_check "PM_all_4" 529 false)
      val _ = exec \<open>Test PM_all_5\<close> (mk_benchmark_check "PM_all_5" 568 false)
      \<comment> \<open>180 s on an M1 Mac\<close>
      \<^cancel>\<open>val _ = exec \<open>Test PM_all_6\<close> (mk_benchmark_check "PM_all_6" 416245 false)\<close>
      val _ = exec \<open>Test PM_all_urgent\<close> (mk_benchmark_check "PM_all_urgent" 8 true)
      val _ = exec \<open>Test bridge\<close> (mk_benchmark_check "bridge" 73 true)
      val _ = exec \<open>Test csma_05\<close> (mk_benchmark_check "csma_05" 8217 false)
      val _ = exec \<open>Test csma_06\<close> (mk_benchmark_check "csma_06" 68417 false)
      val _ = exec \<open>Test fischer\<close> (mk_benchmark_check "fischer" 4500 true)
      val _ = exec \<open>Test fischer_05\<close> (mk_benchmark_check "fischer_05" 38579 false)
      val _ = exec \<open>Test hddi_08\<close> (mk_benchmark_check "hddi_08" 466 false)
      val _ = exec \<open>Test light_switch\<close> (mk_benchmark_check "light_switch" 2 true)
      \<comment> \<open>a test for the deadlock checker\<close>
      val _ = exec \<open>Test hddi_08\<close> (mk_benchmark_check_dc "hddi_08" 466 false)
    in () end\<close>

end
