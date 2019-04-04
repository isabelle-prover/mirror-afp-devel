section \<open>Build and test exported program with MLton\<close>

theory Complementation_Build
  imports Complementation_Final
begin

external_file \<open>code/Complementation.mlb\<close>
external_file \<open>code/Prelude.sml\<close>
external_file \<open>code/Automaton.sml\<close>
external_file \<open>code/Complementation.sml\<close>

compile_generated_files \<^marker>\<open>contributor Makarius\<close>
  \<open>code/Complementation_Export.ML\<close> (in Complementation_Final)
  external_files
    \<open>code/Complementation.mlb\<close>
    \<open>code/Prelude.sml\<close>
    \<open>code/Automaton.sml\<close>
    \<open>code/Complementation.sml\<close>
  export_files \<open>code/Complementation\<close> (exe) and
    \<open>code/Complementation_Export.sml\<close>
    \<open>code/Complementation.out\<close>
    \<open>code/mlmon.out\<close>
  where \<open>fn dir0 =>
    let
      val dir = Path.append dir0 (Path.basic "code");
      fun exec title script =
        writeln (Isabelle_System.bash_output_check ("cd " ^ File.bash_path dir ^ " && " ^ script))
          handle ERROR msg =>
            let val (s, pos) = Input.source_content title
            in error (s ^ " failed" ^ Position.here pos ^ ":\n" ^ msg) end;
    in
      exec \<open>Compilation\<close>
        ("mv Complementation_Export.ML Complementation_Export.sml && " ^
          File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^
          " -profile time -default-type intinf Complementation.mlb");
      exec \<open>Test\<close> "./Complementation Complementation.out"
    end\<close>

end
