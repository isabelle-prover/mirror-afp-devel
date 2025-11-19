theory Universal_Pairs
  imports Eleven_Unknowns_Z
begin

definition universal_pair_N ("'(_, _')\<^sub>\<nat>" [1000]) where
  "universal_pair_N \<nu> \<delta> \<equiv> (\<forall>A::nat set. is_diophantine_over_N A \<longrightarrow>
                               (\<exists>P::int mpoly. max_vars P \<le> \<nu> \<and> total_degree P \<le> \<delta> \<and>
                                               is_diophantine_over_N_with A P))"

definition universal_pair_Z ("'(_, _')\<^sub>\<int>" [1000]) where
  "universal_pair_Z \<nu> \<delta> \<equiv> (\<forall>A::nat set. is_diophantine_over_N A \<longrightarrow>
                               (\<exists>P::int mpoly. max_vars P \<le> \<nu> \<and> total_degree P \<le> \<delta> \<and>
                                               is_diophantine_over_Z_with A P))"

theorem universal_pairs_Z_from_N:
  assumes "(\<nu>, \<delta>)\<^sub>\<nat>"
  shows "(11, \<eta> \<nu> \<delta>)\<^sub>\<int>"
proof (unfold universal_pair_Z_def, (rule allI impI)+)
  fix A
  assume "is_diophantine_over_N A"
  then obtain P where P1: "max_vars P \<le> \<nu>" and
                      P2: "total_degree P \<le> \<delta>" and
                      P3: "is_diophantine_over_N_with A P"
    using assms unfolding universal_pair_N_def by auto

  show "\<exists>Q. max_vars Q \<le> 11 \<and> total_degree Q \<le> \<eta> \<nu> \<delta> \<and> is_diophantine_over_Z_with A Q"
  proof (cases "total_degree P > 0")
    case True
    
    define Q where "Q \<equiv> Q_tilde_poly P"

    have 1: "max_vars Q \<le> 11"
      using max_vars_Q_tilde
      unfolding Q_def by auto
    
    have 2: "total_degree Q \<le> \<eta> \<nu> \<delta>"
      using Q_tilde_degree[OF True P2 P1] Q_tilde_poly_degree_correct Q_def le_trans by blast

    have 3: "is_diophantine_over_Z_with A Q"
      unfolding is_diophantine_over_Z_with_def Q_def
      unfolding eleven_unknowns_over_Z_polynomial[OF P3]
      apply (auto, metis fun_upd_triv nth_Cons_0)
      using Q_tilde_correct by force

    then show ?thesis
      using 1 2 3 by auto
  next
    case False
    then obtain c where c: "P \<equiv> Const c" 
      using Total_Degree.total_degree_zero by blast

    have 1: "max_vars P \<le> 11" unfolding c by simp

    have 2: "total_degree P \<le> \<eta> \<nu> \<delta>" unfolding c by simp

    have 3: "is_diophantine_over_Z_with A P" 
      using P3 unfolding is_diophantine_over_N_with_def
      unfolding is_diophantine_over_Z_with_def
      unfolding c using is_nonnegative_def by auto

    show ?thesis
      by (rule exI[of _ P], auto simp: 1 2 3)
  qed
qed

theorem universal_pair_1:
  assumes "(58, 4)\<^sub>\<nat>" 
  shows "(11, 1681043235226619916301182624511918527834137733707408448335539840)\<^sub>\<int>"
  using universal_pairs_Z_from_N[of 58 4] assms unfolding \<eta>_def
  by (simp add: algebra_simps)

(* This pair is bounded above by approximately (11, 1.68105 * 10^{63})\<^sub>\<int> . *)



theorem universal_pair_2:
  assumes "(32, 12)\<^sub>\<nat>" 
  shows "(11, 950817549694171759711025515571236610412597656252821888)\<^sub>\<int>"
  using universal_pairs_Z_from_N[of 32 12] assms unfolding \<eta>_def
  by (simp add: algebra_simps)

(* This pair is bounded above by approximately (11, 9.50818 * 10^{53})\<^sub>\<int> . *)

end