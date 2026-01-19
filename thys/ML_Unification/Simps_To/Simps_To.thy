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

open_bundle SIMPS_TO_syntax
begin
notation SIMPS_TO ("(_ \<equiv>> _)" [51,51] 50)
end

lemma SIMPS_TO_eq: "s \<equiv>> t \<equiv> (s \<equiv> t)"
  unfolding SIMPS_TO_def by simp

text \<open>Prevent simplification of second/right argument\<close>
lemma SIMPS_TO_cong [cong]: "s \<equiv> s' \<Longrightarrow> s \<equiv>> t \<equiv> s' \<equiv>> t" by simp

lemma SIMPS_TOI: "s \<equiv>> s" unfolding SIMPS_TO_eq by simp
lemma SIMPS_TOD: "s \<equiv>> t \<Longrightarrow> s \<equiv> t" unfolding SIMPS_TO_eq by simp

ML_file\<open>simps_to.ML\<close>

paragraph \<open>Using Simplification On Left Term Followed By Unification\<close>

definition "SIMPS_TO_UNIF s t \<equiv> (s \<equiv> t)"

open_bundle SIMPS_TO_UNIF_syntax
begin
notation SIMPS_TO_UNIF ("(_ \<equiv>\<^sup>?> _)" [51,51] 50)
end

text \<open>Prevent simplification\<close>
lemma SIMPS_TO_UNIF_cong [cong]: "s \<equiv>\<^sup>?> t \<equiv> s \<equiv>\<^sup>?> t" by simp

lemma SIMPS_TO_UNIF_eq: "s \<equiv>\<^sup>?> t \<equiv> (s \<equiv> t)" unfolding SIMPS_TO_UNIF_def by simp

lemma SIMPS_TO_UNIFI: "s \<equiv>> s' \<Longrightarrow> s' \<equiv> t \<Longrightarrow> s \<equiv>\<^sup>?> t"
  unfolding SIMPS_TO_UNIF_eq SIMPS_TO_eq by simp
lemma SIMPS_TO_UNIFD: "s \<equiv>\<^sup>?> t \<Longrightarrow> s \<equiv> t"
  unfolding SIMPS_TO_UNIF_eq by simp

ML_file\<open>simps_to_unif.ML\<close>


paragraph \<open>Examples\<close>

experiment
begin

schematic_goal
  assumes [simp]: "P \<equiv> Q"
  and [simp]: "Q \<equiv> R"
  shows "\<And>x. PROP U x ==> P x \<equiv>\<^sup>?> ?A x"
  apply (tactic \<open>HEADGOAL (Simps_To_Unif.SIMPS_TO_UNIF_tac (simp_tac @{context})
    (K all_tac) 1 @{context})\<close>)
  by (rule reflexive)

end

end
