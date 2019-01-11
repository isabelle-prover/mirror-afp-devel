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

ML \<open>
  val exists_ghc = getenv "ISABELLE_GHC" <> "";
  val here = Resources.master_directory @{theory};
  val compile_dir = File.tmp_path (Path.basic "HLDE");
  val compile_result = Path.append compile_dir (Path.basic "Main");
  val dest_dir = Path.append here (Path.basic "generated");
  val hlde = Path.append dest_dir (Path.basic "hlde");
  Isabelle_System.mkdir compile_dir;
  Isabelle_System.mkdir dest_dir;
  Isabelle_System.copy_file (Path.append here (Path.make ["src", "Main.hs"]))
    (Path.append compile_dir (Path.basic "Main.hs"));
\<close>

export_code solve integer_of_nat nat_of_integer in Haskell module_name HLDE file \<open>$ISABELLE_TMP/HLDE\<close>

ML \<open>
  if exists_ghc then
    if Isabelle_System.bash ("cd " ^ File.bash_path compile_dir ^ " && \"$ISABELLE_GHC\" Main.hs 2>&1") = 0 then (
      Isabelle_System.copy_file compile_result hlde;
      File.rm compile_result
    ) else error "HLDE compilation failed"
  else warning "No GHC configured";
\<close>

ML \<open>
val print_coeffs =
  enclose "[" "]" o commas o map string_of_int;

fun print_hlde (xs, ys) =
  let
    val
      cmd = File.bash_path hlde ^ " <<< '("
        ^ print_coeffs xs ^ ", " ^ print_coeffs ys ^ ")'";
  in
    if Isabelle_System.bash cmd = 0 then ()
    else error "HLDE computation failed"
  end
\<close>

ML \<open>
  if exists_ghc then print_hlde ([3, 5, 1], [2, 7])
  else ()
\<close>

end
