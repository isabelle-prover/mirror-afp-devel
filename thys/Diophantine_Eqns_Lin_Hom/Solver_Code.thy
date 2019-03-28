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

ML_command \<open>
  if getenv "ISABELLE_GHC" = "" then warning "No GHC configured"
  else
    Isabelle_System.with_tmp_dir "HLDE" (fn compile_dir =>
      let
        val exe = Path.append compile_dir (Path.basic "Main");

        (*assemble sources*)
        val _ = Isabelle_System.copy_file (Path.append \<^master_dir> \<^path>\<open>src/Main.hs\<close>) compile_dir;
        val _ =
          Generated_Files.get_files \<^theory> |> List.app (fn {path, text, ...} =>
            if path = \<^path>\<open>code/generated/HLDE.hs\<close> then
              File.write (Path.append compile_dir \<^path>\<open>HLDE.hs\<close>) text
            else ());

        (*compile*)
        val compile_rc =
          Isabelle_System.bash ("cd " ^ File.bash_path compile_dir ^
            " && \"$ISABELLE_GHC\" Main.hs 2>&1");
        val () =
          if compile_rc = 0 then Export.export \<^theory> \<^path>\<open>code/generated/hlde\<close> [File.read exe]
          else error "HLDE compilation failed";

        (*test*)
        val print_coeffs = enclose "[" "]" o commas o map string_of_int;
        fun print_hlde (xs, ys) =
          let
            val test_rc =
              Isabelle_System.bash (File.bash_path exe ^
                " <<< '(" ^ print_coeffs xs ^ ", " ^ print_coeffs ys ^ ")'");
          in if test_rc = 0 then () else error "HLDE computation failed" end;
      in
        print_hlde ([3, 5, 1], [2, 7])
      end);
\<close>

end
