(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Generating Code for the Solver\<close>

theory Solver_Code
  imports Algorithm
begin

external_file \<open>src/Main.hs\<close>

export_code solve checking Haskell \<comment> \<open>test whether Haskell code generation works\<close>

export_code solve integer_of_nat nat_of_integer in Haskell module_name HLDE file_prefix generated

ML_command \<^marker>\<open>contributor Makarius\<close> \<open>
  if getenv "ISABELLE_GHC" = "" then warning "GHC not configured"
  else
    Isabelle_System.with_tmp_dir "HLDE" (fn build_dir =>
      let
        val thy = \<^theory>;
        val exe = Path.append build_dir (Path.exe \<^path>\<open>Main\<close>);

        (*assemble sources*)
        val _ = Isabelle_System.copy_file (Path.append \<^master_dir> \<^path>\<open>src/Main.hs\<close>) build_dir;
        val _ =
          File.write (Path.append build_dir \<^path>\<open>HLDE.hs\<close>)
            (Generated_Files.the_file_content thy \<^path>\<open>code/generated/HLDE.hs\<close>);

        (*compile*)
        val compile_rc =
          Isabelle_System.bash ("cd " ^ File.bash_path build_dir ^ " && \"$ISABELLE_GHC\" Main.hs");
        val () =
          if compile_rc = 0 then
            Export.export_executable_file thy
              (Path.map_binding Path.exe \<^path_binding>\<open>code/generated/hlde\<close>) exe
          else error "Compilation failed";

        (*test*)
        val print_coeffs = enclose "[" "]" o commas o map string_of_int;
        fun print_hlde (xs, ys) =
          let
            val test_rc =
              Isabelle_System.bash (File.bash_path exe ^
                " <<< '(" ^ print_coeffs xs ^ ", " ^ print_coeffs ys ^ ")'");
          in if test_rc = 0 then () else error "Test failed" end;
      in
        print_hlde ([3, 5, 1], [2, 7])
      end);
\<close>

end
