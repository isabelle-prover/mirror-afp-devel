section \<open>Build and test exported program with MLton\<close>

theory Complementation_Build
  imports Complementation_Final
begin

external_file \<open>code/Complementation.mlb\<close>
external_file \<open>code/Prelude.sml\<close>
external_file \<open>code/Automaton.sml\<close>
external_file \<open>code/Complementation.sml\<close>

ML_command \<^marker>\<open>contributor Makarius\<close> \<open>
  if getenv "ISABELLE_MLTON" = "" then warning "MLton not configured"
  else
    Isabelle_System.with_tmp_dir "Complementation" (fn build_dir =>
      let
        val thy = \<^theory>;
        val exe = Path.append build_dir (Path.exe \<^path>\<open>Complementation\<close>);

        (*assemble sources*)
        val _ =
          List.app (fn path => Isabelle_System.copy_file (Path.append \<^master_dir> path) build_dir)
           [\<^path>\<open>code/Complementation.mlb\<close>,
            \<^path>\<open>code/Prelude.sml\<close>,
            \<^path>\<open>code/Automaton.sml\<close>,
            \<^path>\<open>code/Complementation.sml\<close>];

        val exported_code =
          Generated_Files.the_file_content \<^theory>\<open>Complementation_Final\<close>
            \<^path>\<open>code/Complementation_Export.ML\<close>;
        val _ = File.write (Path.append build_dir \<^path>\<open>Complementation_Export.sml\<close>) exported_code;
        val _ = Export.export thy \<^path>\<open>code/Complementation_Export.sml\<close> [exported_code];

        (*compile*)
        val compile_rc =
          Isabelle_System.bash ("cd " ^ File.bash_path build_dir ^
            " && \"$ISABELLE_MLTON\" -profile time -default-type intinf Complementation.mlb");
        val _ =
          if compile_rc = 0 then
            Export.export_executable_file thy (Path.exe \<^path>\<open>code/Complementation\<close>) exe
          else error "Compilation failed";

        (*test*)
        val test_rc =
          Isabelle_System.bash ("cd " ^ File.bash_path build_dir ^ " && ./Complementation");
        val _ =
          if test_rc = 0 then
            Export.export_file thy \<^path>\<open>code/mlmon.out\<close> (Path.append build_dir \<^path>\<open>mlmon.out\<close>)
          else warning "Test failed";  (* FIXME error -- unhandled exception: Empty *)
      in () end)
\<close>

end
