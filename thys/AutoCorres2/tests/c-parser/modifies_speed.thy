(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory modifies_speed
imports "AutoCorres2.CTranslation"
begin

text \<open>Speed test for modifies proofs.\<close>
ML \<open>
fun write_speed_test_file thy n_globs n_funcs =
  let val filename = Resources.master_directory thy + \<^path>\<open>modifies_speed.c\<close> in
    if File.exists filename then ()
    else
      filename |> File_Stream.open_output (fn out =>
        let
          val output = File_Stream.output out;
          fun write_global n = output ("int global" ^ string_of_int n ^ ";\n")
          fun write_func_h n = output ("int\nfoo" ^ string_of_int n ^ " (int x) {\n\n")
          fun write_upd_global n = output ("  global" ^ string_of_int n ^ " = x;\n")
          fun write_fun_call n = output ("  foo" ^ string_of_int n ^ " (x);\n")
          fun write_func_t () = output ("\n  return x;\n}\n")
          fun write_func n =
            let
              val globs = filter
                (fn y => IntInf.andb (n, IntInf.<< (1, Word.fromInt y)) = 0)
                (1 upto n_globs)
              val funs = filter (fn y => n mod y = 0) (3 upto (n - 1))
            in
              write_func_h n;
              List.app write_upd_global globs;
              List.app write_fun_call funs;
              write_func_t ()
            end
        in
          List.app write_global (1 upto n_globs);
          List.app write_func (1 upto n_funcs)
        end)
  end
\<close>

ML \<open>
write_speed_test_file \<^theory> 10 40
\<close>

declare [[sorry_modifies_proofs = false]]

install_C_file "modifies_speed.c"

end
