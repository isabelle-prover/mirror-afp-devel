(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Configuring type strengthen rules.
 * Based on type_strengthen.thy.
 *)
theory type_strengthen_tricks imports
  "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "type_strengthen.c"


(* We can also specify which monads are used for type strengthening.
   Here, we exclude the read-only monad completely, and specify
   rules for some individual functions. *)
autocorres [
  ts_rules = pure option nondet,
  ts_force option = pure_f
  ] "type_strengthen.c"


context type_strengthen_all_impl begin

(* pure_f (and indirectly, pure_f2) are now lifted to the option monad. *)
thm pure_f'_def  pure_f2'_def
thm pure_g'_def pure_h'_def
    pure_i'_def pure_j'_def pure_k'_def pure_div_roundup'_def
(* gets_f and gets_g are now lifted to the option monad. *)
thm gets_f'_def gets_g'_def
thm opt_f'_def opt_g'_def opt_h'.simps opt_i'_def
    opt_j'_def opt_a'.simps opt_a2'_def
thm opt_l'_def
thm st_f'_def st_g'_def st_h'_def st_i'.simps (* hax'_def *)
thm exc_f'_def

term pure_f2' term opt_a2'
thm pure_f2'_def
(* Check the above claims. *)
term "pure_f' :: lifted_globals \<Rightarrow> unit option"
term "pure_f2' :: lifted_globals \<Rightarrow> unit option"
term "pure_g' :: ure_C ptr \<Rightarrow> ure_C ptr"
term "pure_h' :: ure_C ptr \<Rightarrow> int"
term "pure_i' :: int \<Rightarrow> int"
term "pure_j' :: ure_C \<Rightarrow> int"
term "pure_k' :: ure_C \<Rightarrow> int"
term "pure_div_roundup' :: word32 \<Rightarrow> word32 \<Rightarrow> word32"
term "gets_f' :: lifted_globals \<Rightarrow> word32 option"
term "gets_g' :: lifted_globals \<Rightarrow> word32 option"
term "opt_f' :: word32 ptr \<Rightarrow> lifted_globals \<Rightarrow> word32 option"
term "opt_g' :: int \<Rightarrow> lifted_globals \<Rightarrow> int option"
term "opt_h' :: ure_C ptr \<Rightarrow> lifted_globals \<Rightarrow> word32 option"
term "opt_i' :: (int, lifted_globals) res_monad"
term "opt_j' :: ure_C ptr \<Rightarrow> ure_C ptr \<Rightarrow> lifted_globals \<Rightarrow> int option"
term "opt_a' :: word32 \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> word32 option"
term "opt_a2' :: 32 word \<Rightarrow> lifted_globals \<Rightarrow> 32 word option"
term "opt_l' :: word32 \<Rightarrow> lifted_globals \<Rightarrow> word32 option"
term "st_f' :: ure_C ptr \<Rightarrow> ure_C ptr \<Rightarrow> (unit, lifted_globals) res_monad"
term "st_g' :: word32 ptr \<Rightarrow> (word32, lifted_globals) res_monad"
term "st_h' :: word32 \<Rightarrow> (word32, lifted_globals) res_monad"
term "st_i' :: ure_C ptr \<Rightarrow> ure_C ptr \<Rightarrow> (ure_C ptr, lifted_globals) res_monad"
term "exc_f' :: char_c ptr \<Rightarrow> 32 signed word ptr \<Rightarrow> (int, lifted_globals) res_monad"
end

end
