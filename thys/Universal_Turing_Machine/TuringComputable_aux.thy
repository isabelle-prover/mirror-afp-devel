(* Title: thys/TuringComputable_aux.thy
   Author:  Franz Regensburger (FABR) 04/2022
 *)

theory TuringComputable_aux
  imports
    TuringComputable

begin

(* Auxiliary lemmas that are not used at the moment *)

lemma TMC_has_num_res_impl_result:
  assumes "TMC_has_num_res p ns"
  shows "\<exists>stp k n l. (steps0 (1, ([], <ns::nat list>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  using Hoare_halt_on_numeral_imp_result
  using TMC_has_num_res_def assms
  by blast

lemma TMC_has_num_res_impl_result_rev:
  assumes "\<exists>stp k n l. (steps0 (1, ([], <ns>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  shows "TMC_has_num_res p ns"
  unfolding TMC_has_num_res_def
  using Hoare_halt_on_numeral_imp_result_rev
  using assms tape_of_list_def by auto

corollary TMC_has_num_res_impl_result_iff:
  "(TMC_has_num_res p ns)
   \<longleftrightarrow>
   (\<exists>stp k n l. (steps0 (1, ([], <ns>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
  using TMC_has_num_res_impl_result TMC_has_num_res_impl_result_rev by blast


lemma TMC_has_num_res_impl_unique_result:
  assumes "TMC_has_num_res p ns"
  shows "\<exists>!n. \<exists>stp k l. steps0 (1,[], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
proof (rule ex_ex1I)
  show "\<exists>n stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    using assms TMC_has_num_res_impl_result by blast
next
  show "\<And>n y. \<lbrakk>\<exists>stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l);
               \<exists>stp k l. steps0 (1, [], <ns>) p stp = (0, Bk \<up> k, <y> @ Bk \<up> l)\<rbrakk> \<Longrightarrow> n = y"
    by (smt before_final is_final_eq le_less least_steps less_Suc_eq not_less_iff_gr_or_eq snd_conv unique_decomp_std_tap)
qed

lemma TMC_has_num_res_impl_unique_result_rev:
  assumes  "\<exists>!n. \<exists>stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  shows  "TMC_has_num_res p ns"
proof -
  from assms have "\<exists>stp n k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    by blast
  then show ?thesis using TMC_has_num_res_impl_result_rev
    by blast
qed

corollary TMC_has_num_res_impl_unique_result_iff:
  "TMC_has_num_res p ns
   \<longleftrightarrow>
   (\<exists>!n.\<exists>stp k l. (steps0 (1, ([], <ns>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
  using TMC_has_num_res_impl_unique_result TMC_has_num_res_impl_unique_result_rev
  by blast

subsection \<open>Hoare halt with single numeral result: least number of steps and uniqueness\<close>

lemma TMC_has_num_res_impl_result_least:
  assumes "TMC_has_num_res p ns"
    and "st = (LEAST m. is_final (steps0 (1, [], <ns>) p m))"
  shows "\<exists> k n l. (steps0 (1, ([], <ns>)) p st) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
proof (rule exE)
  from assms(1) show "\<exists>stp k n l. (steps0 (1, ([], <ns>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    by (rule TMC_has_num_res_impl_result)
next
  fix stp
  assume "\<exists>k n l. steps0 (1, [], <ns>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  then obtain k n l where w: "steps0 (1, [], <ns>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    by blast

  then have "\<exists> n'. (\<forall>n'' < n'. \<not> is_final (steps0 (1, ([], <ns>)) p n'')) \<and> 
               (\<forall>n'' \<ge> n'. is_final (steps0 (1, ([], <ns>)) p n''))"
    by (rule least_steps)

  then obtain ln where w_ln:" (\<forall>n'' < ln. \<not> is_final (steps0 (1, ([], <ns>)) p n'')) \<and> 
                                (\<forall>n'' \<ge> ln. is_final (steps0 (1, ([], <ns>)) p n''))" by blast
  from w_ln have F_ln: "is_final (steps0 (1, [], <ns>) p ln)" by auto

  have F_ln_eq: "(LEAST m. is_final (steps0 (1, [], <ns>) p m)) = ln"
  proof (rule Least_equality)
    from w_ln show "is_final (steps0 (1, [], <ns>) p ln)" by auto
  next
    fix y
    assume "is_final (steps0 (1, [], <ns>) p y)"
    show "ln \<le> y" 
    proof (rule ccontr)
      assume "\<not> ln \<le> y"
      then have "y < ln" by auto

      with w_ln have "\<not> is_final (steps0 (1, ([], <ns>)) p y)" by auto
      with \<open>is_final (steps0 (1, [], <ns>) p y)\<close> show False by blast
    qed
  qed
  with assms(2) have "st = ln" by auto
  with F_ln have F_st: "is_final (steps0 (1, [], <ns>) p st)" by auto

  from w have F_stp: "is_final (steps0 (1, [], <ns>) p stp)" by auto

  have "steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n> @ Bk \<up> l)"
  proof (cases "stp < st")
    case True
    then have "stp < st" .
    with F_stp and assms(2) have False using not_less_Least by auto
    then show ?thesis by auto
  next
    case False
    then have "st \<le> stp" by auto

    then show ?thesis
    proof (cases "steps0 (1, [], <ns>) p st")
      case (fields a b c)
      then have "steps0 (1, [], <ns>) p st = (a, b, c)" .
      moreover with F_st have S0: "a = 0" using is_final_eq[THEN iffD1] by auto
      ultimately have "steps0 (1, [], <ns>) p st = (0, b, c)" by auto
      from this and \<open>st \<le> stp\<close> have "steps0 (1, [], <ns>) p stp = (0, b, c)"
        by (rule stable_config_after_final_ge')
      with w have "b = Bk \<up> k \<and> c= <n> @ Bk \<up> l" by auto
      with S0 and \<open>steps0 (1, [], <ns>) p st = (a, b, c)\<close> show ?thesis by auto
    qed
  qed
  then show "\<exists>k n l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" by auto
qed


lemma TMC_has_num_res_impl_result_is_unique:
  assumes "TMC_has_num_res p ns"
    and "st = (LEAST m. is_final (steps0 (1,[], <ns>) p m))"
  shows "\<exists>!n. \<exists>k l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
proof (rule ex_ex1I)
  show "\<exists>n k l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  proof -
    from assms have "\<exists> k n l. (steps0 (1, ([], <ns>)) p st) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
      by (rule TMC_has_num_res_impl_result_least)
    then obtain k n l where w_k_n_l: "(steps0 (1, ([], <ns>)) p st) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
      by blast
    then show "\<exists>n k l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" by auto
  qed
next
  fix n::nat fix y::nat
  assume A1: "\<exists>k l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <n> @ Bk \<up> l)"
     and A2: "\<exists>k l. steps0 (1, [], <ns>) p st = (0, Bk \<up> k, <y> @ Bk \<up> l)"
  from A1 obtain k1 l1 where w_k1_l1: "steps0 (1, [], <ns>) p st = (0, Bk \<up> k1, <n> @ Bk \<up> l1)" by blast
  from A2 obtain k2 l2 where w_k2_l2: "steps0 (1, [], <ns>) p st = (0, Bk \<up> k2, <y> @ Bk \<up> l2)" by blast

  from w_k1_l1 and w_k2_l2 have "(0, Bk \<up> k1, <n> @ Bk \<up> l1) = (0, Bk \<up> k2, <y> @ Bk \<up> l2)" by auto
  then have "(Bk \<up> k1, <n> @ Bk \<up> l1) = (Bk \<up> k2, <y> @ Bk \<up> l2)" by auto
  then have "k1=k2 \<and> n=y \<and> l1=l2" by (rule unique_decomp_std_tap)
  then show "n = y" by auto
qed

end
