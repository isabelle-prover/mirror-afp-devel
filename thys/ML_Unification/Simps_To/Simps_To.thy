\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Simps To\<close>
theory Simps_To
  imports
    ML_Unifiers_Base
    Setup_Result_Commands
begin

paragraph \<open>Summary\<close>
text \<open>Simple frameworks to ask for the simp-normal form of a term on the user-level.\<close>

setup_result simps_to_base_logger = \<open>Logger.new_logger Logger.root "Simps_To_Base"\<close>

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

schematic_goal
  assumes [simp]: "P \<equiv> Q"
  and [simp]: "Q \<equiv> R"
  shows "PROP SIMPS_TO_UNIF P ?A"
  by (tactic \<open>Simps_To_Unif.SIMPS_TO_UNIF_tac (simp_tac @{context})
    (K all_tac) 1 @{context} 1\<close>)

end

end
