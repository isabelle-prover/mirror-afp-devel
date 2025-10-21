section \<open>Build and Test Exported Program With MLton\<close>
text_raw \<open>\label{build-mlton}\<close>

theory Munta_Certificate_Compile_MLton
  imports Simple_Network_Language_Certificate_Code Munta_Certificate_Testing
begin

text \<open>Here is how to compile Munta Certifier with MLton and then run some benchmarks:\<close>

compile_generated_files "code/Certificate.ML" (in Simple_Network_Language_Certificate_Code)
  external_files
    \<open>Unsynchronized.sml\<close>
    \<open>Writeln.sml\<close>
    \<open>Util.sml\<close>
    \<open>Muntac.sml\<close>
    \<open>Mlton_Main.sml\<close>
    \<open>sequential.sml\<close>
    \<open>muntac.mlb\<close>
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
  export_files \<open>muntac\<close> (exe)
  where \<open>fn dir =>
    let
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
        \<comment> \<open>Efficient settings for ARM64 machines\<close>
        exec \<open>Compilation\<close>
          (\<^verbatim>\<open>"$ISABELLE_MLTON" $ISABELLE_MLTON_OPTIONS\<close> ^
            \<comment> \<open>these additional settings have been copied from the AFP entry \<open>PAC_Checker\<close>\<close>
            " -const 'MLton.safe false' -verbose 1 -inline 700 -cc-opt -O3 " ^
            \<comment> \<open>this one does not work on ARM64 though\<close>
            \<^cancel>\<open>"-codegen native " ^\<close>
            \<comment> \<open>these used to be the defaults for Munta\<close>
            "-default-type int64 " ^
            "-output muntac " ^
            "-mlb-path-var 'MLUNTA_CERT " ^ mlunta_certificate_path ^ "' " ^
            "muntac.mlb")
      val muntac_path = "./muntac";
      val muntac_path_dc = "./muntac -dc" \<comment> \<open>For deadlock checking\<close>

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

      val _ = exec \<open>Test HDDI_02\<close> (check_cert muntac_path "HDDI_02")
      val _ = exec \<open>Test HDDI_02_broadcast\<close> (check_cert muntac_path "HDDI_02_broadcast")
      val _ = exec \<open>Test HDDI_08_broadcast\<close> (check_cert muntac_path "HDDI_08_broadcast")
      val _ = exec \<open>Test hddi_08\<close> (check_cert muntac_path "hddi_08")
      val _ = exec \<open>Test PM_all_1\<close> (check_cert muntac_path "PM_all_1")
      val _ = exec \<open>Test PM_all_2\<close> (check_cert muntac_path "PM_all_2")
      val _ = exec \<open>Test PM_all_3\<close> (check_cert muntac_path "PM_all_3")
      val _ = exec \<open>Test csma_05\<close> (check_cert muntac_path "csma_05")
      val _ = exec \<open>Test csma_06\<close> (check_cert muntac_path "csma_06")
      val _ = exec \<open>Test fischer_05\<close> (check_cert muntac_path "fischer_05")
      val _ = exec \<open>Test PM_all_4\<close> (check_cert muntac_path "PM_all_4")
      val _ = exec \<open>Test PM_all_5\<close> (check_cert muntac_path "PM_all_5")

      val _ = exec \<open>Test deadlock HDDI_02\<close> (check_cert muntac_path_dc "HDDI_02")
    in () end\<close>

end
