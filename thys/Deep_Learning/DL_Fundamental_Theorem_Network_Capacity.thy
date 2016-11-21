(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Fundamental Theorem of Network Capacity\<close>

theory DL_Fundamental_Theorem_Network_Capacity
imports DL_Rank_CP_Rank DL_Deep_Model_Poly Lebesgue_Zero_Set DL_Rank_Submatrix "~~/src/HOL/Probability/Complete_Measure" DL_Shallow_Model
DL_Missing_Complete_Measure
begin

context deep_model_correct_params_y
begin

theorem fundamental_theorem_network_capacity_polynomial:
obtains p where "p\<noteq>0" and "vars p \<subseteq> {..<weight_space_dim}"
and "\<And>x. insertion x p \<noteq> 0 \<Longrightarrow> r ^ N_half \<le> cprank (A x)"
proof -
  assume assumption:"\<And>p. p \<noteq> 0 \<Longrightarrow> vars p \<subseteq> {..<weight_space_dim} \<Longrightarrow>
   (\<And>x. insertion x p \<noteq> 0 \<Longrightarrow> r ^ N_half \<le> cprank (A x)) \<Longrightarrow> thesis"
  obtain p where p_def:"\<And>x. insertion x p = Determinant.det (witness_submatrix y x)" and
                 vars_p:"vars p \<subseteq> {..<weight_space_dim}"
    using polyfun_det_deep_model[unfolded polyfun_def] by auto
  then have "insertion witness_weights p \<noteq> 0"
    using witness_det[unfolded Aw'_def'] witness_submatrix_def weight_space_dim_def
    by (metis p_def)
  then have "p\<noteq>0" by auto
  have "\<And>x. insertion x p \<noteq> 0 \<Longrightarrow> r ^ N_half \<le> cprank (A x)"
  proof -
    fix x assume "insertion x p \<noteq> 0"
    then have "Determinant.det (witness_submatrix y x) \<noteq> 0" using p_def by auto
    have 0:"weight_space_dim \<le> length (map x [0..<weight_space_dim])" by auto
    have "r ^ N_half \<le> mrank (A' x)"
      using vec_space.rank_gt_minor[OF mat_carrierI[OF dims_A'_pow, unfolded weight_space_dim_def]
      `Determinant.det (witness_submatrix y x) \<noteq> 0`[unfolded witness_submatrix_def]]
      card_rows_with_1[unfolded dims_Aw'_pow] by (metis (no_types, lifting) Collect_cong dims_A'_pow(1))
    also have "... \<le> cprank (A x)" using matrix_rank_le_cp_rank A'_def by auto
    finally show "r ^ N_half \<le> cprank (A x)" .
  qed
  then show ?thesis using assumption `p\<noteq>0` `vars p \<subseteq> {..<weight_space_dim}` by blast
qed

theorem fundamental_theorem_network_capacity:
"AE x in lborel_f weight_space_dim. r ^ N_half \<le> cprank (A x)"
proof -
  obtain p where "p\<noteq>0" and "vars p \<subseteq> {..<weight_space_dim}"
    and "\<And>x. insertion x p \<noteq> 0 \<Longrightarrow> r ^ N_half \<le> cprank (A x)"
    using fundamental_theorem_network_capacity_polynomial by metis
  have null_set:"{f \<in> space (lborel_f weight_space_dim). insertion f p = 0} \<in> null_sets (lborel_f weight_space_dim)"
    using lebesgue_mpoly_zero_set[OF `p\<noteq>0` `vars p \<subseteq> {..<weight_space_dim}`] by simp
  have subset:"{x \<in> space (lborel_f weight_space_dim). r ^ N_half > cprank (A x)}
    \<subseteq> {f \<in> space (lborel_f weight_space_dim). insertion f p = 0}"
  proof
    fix x assume "x\<in>{x \<in> space (lborel_f weight_space_dim). r ^ N_half > cprank (A x)}"
    then have "x\<in>space (lborel_f weight_space_dim)"  "r ^ N_half > cprank (A x)" by auto
    then have "insertion x p = 0" using `\<And>x. insertion x p \<noteq> 0 \<Longrightarrow> r ^ N_half \<le> cprank (A x)`
      HOL.contrapos_nn not_le by metis
    then show "x \<in> {f \<in> space (lborel_f weight_space_dim). insertion f p = 0}" using `x\<in>space (lborel_f weight_space_dim)` by blast
  qed
  then show ?thesis using AE_I'[OF null_set, of "\<lambda>x. r ^ N_half \<le> cprank (A x)"] leI by blast
qed


end

(*TODO: arbitrary parameters for shallow_model?*)
context deep_model_correct_params
begin

theorem null_set_tensors_equal:
shows "AE weights_deep in lborel_f weight_space_dim.
   \<not> (\<exists>weights_shallow Z. Z < r ^ N_half \<and>
tensors_from_net (insert_weights (deep_model_l rs) weights_deep)
 = tensors_from_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half -1)) weights_shallow))"
(is "almost_everywhere ?M ?P")
proof -
  have "0 < rs ! 0" using no_zeros deep by (metis length_0_conv length_greater_0_conv not_numeral_le_zero nth_mem)
  have "\<And>x. \<not> ?P x \<Longrightarrow> cprank (deep_model_correct_params_y.A rs 0 x) < r ^ N_half"
  proof -
    fix x assume "\<not> ?P x"
    obtain weights_shallow Z where "Z < r ^ N_half"
       "tensors_from_net (insert_weights (deep_model_l rs) x) =
       tensors_from_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2 * N_half - 1)) weights_shallow)"
      using `\<not> ?P x` by blast
    then have "cprank (tensors_from_net (insert_weights (deep_model_l rs) x) $ 0) < r ^ N_half"
      using cprank_shallow_model `0 < rs ! 0` remove_insert_weights by (metis not_le order_trans)
    then show "cprank (deep_model_correct_params_y.A rs 0 x) < r ^ N_half"
      by (simp add: `0 < rs ! 0` deep_model_correct_params_axioms
      deep_model_correct_params_y.A_def deep_model_correct_params_y.intro deep_model_correct_params_y_axioms.intro)
  qed
  then show ?thesis using Filter.eventually_mono  using deep_model_correct_params_y.fundamental_theorem_network_capacity[OF deep_model_correct_params_y.intro,
    OF deep_model_correct_params_axioms, unfolded deep_model_correct_params_y_axioms_def, OF `0 < rs ! 0`]
    by fastforce
qed

theorem fundamental_theorem_network_capacity_v2:
shows "AE weights_deep in lborel_f weight_space_dim.
   \<not>(\<exists>weights_shallow Z. Z < r ^ N_half \<and> (\<forall>inputs. map dim\<^sub>v inputs = input_sizes (deep_model_l rs) \<longrightarrow>
evaluate_net (insert_weights (deep_model_l rs) weights_deep) inputs
 = evaluate_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) weights_shallow) inputs))"
(is "almost_everywhere ?M ?P")
proof (rule Filter.eventually_mono)
  show "AE weights_deep in lborel_f weight_space_dim.
    \<not> (\<exists>weights_shallow Z. Z < r ^ N_half \<and>
    tensors_from_net (insert_weights (deep_model_l rs) weights_deep)
    = tensors_from_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half -1)) weights_shallow))"
    (is "almost_everywhere ?M ?P'")
    using null_set_tensors_equal by metis
  have "\<And>x. \<not>?P x \<Longrightarrow> \<not>?P' x"
  proof -
    fix weights_deep assume "\<not>?P weights_deep"
    then obtain weights_shallow Z where 0:"Z < r ^ N_half"
          and eval_eq:"\<And>inputs. map dim\<^sub>v inputs = input_sizes (deep_model_l rs) \<Longrightarrow>
            evaluate_net (insert_weights (deep_model_l rs) weights_deep) inputs
            = evaluate_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2*N_half-1)) weights_shallow) inputs"
      by blast
    have "2 \<le> length rs" using deep by linarith
    have "tensors_from_net (insert_weights (deep_model_l rs) weights_deep) =
          tensors_from_net (insert_weights (shallow_model (rs ! 0) Z (last rs) (2 * N_half - 1)) weights_shallow)"
      using tensors_from_net_eqI[OF _ _ _ eval_eq, unfolded remove_insert_weights, OF valid_deep_model valid_shallow_model]
      input_sizes_deep_model[OF `2 \<le> length rs`] input_sizes_shallow_model input_sizes_remove_weights remove_insert_weights
      by (metis (no_types, lifting) N_half_def Suc_diff_1 Suc_diff_Suc Suc_le_lessD deep numeral_2_eq_2 numeral_3_eq_3 power_Suc power_eq_0_iff zero_less_power zero_power2)
    then show "\<not>?P' weights_deep"
      using 0 by blast
  qed
  then show "\<And>x. ?P' x \<Longrightarrow> ?P x" by blast
qed

end

thm deep_model_correct_params.fundamental_theorem_network_capacity_v2
end
