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

compile_generated_files \<^marker>\<open>contributor Makarius\<close>
  \<open>code/generated/HLDE.hs\<close>
  external_files \<open>src/Main.hs\<close>
  export_files \<open>Main\<close> (exe)
  export_prefix \<open>code/generated\<close>
  where \<open>fn dir =>
    let
      fun exec title script =
        Isabelle_System.bash_output_check ("cd " ^ File.bash_path dir ^ " && " ^ script)
          handle ERROR msg =>
            let val (s, pos) = Input.source_content title
            in error (s ^ " failed" ^ Position.here pos ^ ":\n" ^ msg) end;

      val _ =
        exec \<open>Compilation\<close>
          ("mv code/generated/HLDE.hs . && " ^ File.bash_path \<^path>\<open>$ISABELLE_GHC\<close> ^ " Main.hs");

      val print_coeffs = enclose "[" "]" o commas o map string_of_int;
      fun print_hlde (xs, ys) =
        writeln (exec \<open>Test\<close> ("./Main <<< '(" ^ print_coeffs xs ^ ", " ^ print_coeffs ys ^ ")'"));
    in print_hlde ([3, 5, 1], [2, 7]) end
\<close>

end
