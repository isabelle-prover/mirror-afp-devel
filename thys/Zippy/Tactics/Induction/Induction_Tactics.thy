\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Induction\<close>
theory Induction_Tactics
  imports
    Cases_Tactics
    HOL.HOL
begin

(*FIXME: the setup is agnostic of HOL. However, we cannot load induct.ML without declaring the
print_induct_rules keyword, which in turn would prohibit us from loading HOL since it also declares
print_induct_rules*)
(* ML_file\<open>~~/src/Tools/induct.ML\<close> *)
ML_file\<open>induction_tactic.ML\<close>
ML_file\<open>induction_data.ML\<close>

ML\<open>
structure Induction_Tactic_HOL = Induction_Tactic(Induct)
structure Induction_Data_Args_Tactic_HOL = Induction_Data_Args_Tactic(Induction_Tactic_HOL)
\<close>

end