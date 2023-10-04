\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Simps To\<close>
theory Simps_To
  imports
    ML_Tactic_Utils
    ML_Theorem_Utils
    ML_Unification_Base
    Setup_Result_Commands
begin

paragraph \<open>Summary\<close>
text \<open>Simple frameworks to ask for the simp-normal form of a term on the user-level.\<close>

setup_result simps_to_base_logger = \<open>Logger.new_logger Logger.root_logger "Simps_To_Base"\<close>

paragraph \<open>Using Simplification On Left Term\<close>

definition "SIMPS_TO s t \<equiv> (s \<equiv> t)"

lemma SIMPS_TO_eq: "SIMPS_TO s t \<equiv> (s \<equiv> t)"
  unfolding SIMPS_TO_def by simp

text \<open>Prevent simplification of second/right argument\<close>
lemma SIMPS_TO_cong [cong]: "s \<equiv> s' \<Longrightarrow> SIMPS_TO s t \<equiv> SIMPS_TO s' t" by simp

lemma SIMPS_TOI: "PROP SIMPS_TO s s" unfolding SIMPS_TO_eq by simp
lemma SIMPS_TOD: "PROP SIMPS_TO s t \<Longrightarrow> s \<equiv> t" unfolding SIMPS_TO_eq by simp

ML_file\<open>simps_to.ML\<close>


paragraph \<open>Using Simplification On Left Term Followed By Unification\<close>

definition "SIMPS_TO_UNIF s t \<equiv> (s \<equiv> t)"

text \<open>Prevent simplification\<close>
lemma SIMPS_TO_UNIF_cong [cong]: "SIMPS_TO_UNIF s t \<equiv> SIMPS_TO_UNIF s t" by simp

lemma SIMPS_TO_UNIF_eq: "SIMPS_TO_UNIF s t \<equiv> (s \<equiv> t)" unfolding SIMPS_TO_UNIF_def by simp

lemma SIMPS_TO_UNIFI: "PROP SIMPS_TO s s' \<Longrightarrow> s' \<equiv> t \<Longrightarrow> PROP SIMPS_TO_UNIF s t"
  unfolding SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp
lemma SIMPS_TO_UNIFD: "PROP SIMPS_TO_UNIF s t \<Longrightarrow> s \<equiv> t"
  unfolding SIMPS_TO_UNIF_eq by simp

ML_file\<open>simps_to_unif.ML\<close>


paragraph \<open>Examples\<close>

experiment
begin
lemma
  assumes [simp]: "P \<equiv> Q"
  and [simp]: "Q \<equiv> R"
  shows "PROP SIMPS_TO P Q"
  apply simp \<comment>\<open>Note: only the left-hand side is simplified.\<close>
  ML_command\<open> \<comment>\<open>obtaining the normal form theorem for a term in ML\<close>
    Simps_To.SIMPS_TO_thm_resultsq (simp_tac @{context}) @{context} @{cterm P}
    |> Seq.list_of |> map @{print}
  \<close>
  oops

schematic_goal
  assumes [simp]: "P \<equiv> Q"
  and [simp]: "Q \<equiv> R"
  shows "PROP SIMPS_TO P ?Q"
  apply simp
  by (rule SIMPS_TOI)
end

end
