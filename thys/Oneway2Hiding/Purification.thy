theory Purification

imports Run_Adversary

begin
context o2h_setting
begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

section \<open>Purification of the Adversary\<close>

text \<open>Purification of composed kraus maps.\<close>

definition purify_comp_kraus :: 
  "nat \<Rightarrow> (nat \<Rightarrow> ('a::chilbert_space, 'b::chilbert_space, 'c) kraus_family) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) set" where
  "purify_comp_kraus n \<EE> = PiE {0..<n+1} (\<lambda>i. (fst ` (Rep_kraus_family (\<EE> i))))"


definition comp_upto :: "(nat \<Rightarrow> ('a::chilbert_space) \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a" where
  "comp_upto f n = fold (\<lambda>i x. f i o\<^sub>C\<^sub>L x) [0..<n+1] id_cblinfun"


text \<open>Some auxiliary lemmas on injectivity, Fst and finiteness.\<close>

lemma Rep_kf_id:
  "Rep_kraus_family kf_id = {(id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space,not_singleton},())}"
  by (simp add: kf_id_def kf_of_op.rep_eq del: kf_of_op_id)

lemma fst_Rep_kf_Fst:
  fixes \<EE> :: "('a ell2, 'b ell2, unit) kraus_family"
  shows "fst ` (Rep_kraus_family (kf_Fst \<EE>)) =  Fst ` (fst ` (Rep_kraus_family \<EE>))"
proof (transfer, safe, goal_cases)
  case (1 \<EE> x a aa)
  then have "aa \<in>fst `\<EE>" by (metis fst_conv image_eqI)
  then show ?case by (auto simp add: Fst_def)
next
  case (2 \<EE> x xa a)
  then show ?case by (auto simp add: Fst_def image_comp)
qed


lemma inj_on_Fst:
  shows "inj_on Fst A"
  unfolding Fst_def inj_on_def using inj_tensor_left[OF id_cblinfun_not_0] unfolding inj_def by auto


lemma finite_kf_Fst:
  fixes \<EE> :: "('mem ell2, 'mem ell2, unit) kraus_family"
  assumes "finite (Rep_kraus_family \<EE>)"
  shows "finite (Rep_kraus_family (kf_Fst \<EE>))"
  using assms by transfer auto

lemma finite_kf_id:
  "finite (Rep_kraus_family kf_id)"
  by (simp add: kf_of_op.rep_eq flip: kf_of_op_id)


lemma inj_on_fst_Rep_kraus_family:
  fixes \<EE> :: "('a ell2,'b ell2,unit) kraus_family"
  shows "inj_on fst (Rep_kraus_family \<EE>)"
  unfolding inj_on_def by fastforce


lemma comp_kraus_maps_set_finite:
  assumes "\<And>i. i<n+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  shows "finite (purify_comp_kraus n \<EE>)"
  unfolding purify_comp_kraus_def by (intro finite_PiE) (auto simp add: assms)


text \<open>Showing conditions of Kraus maps.\<close>


lemma norm_square_in_kraus_map:
  fixes \<EE> :: "('a ell2,'a ell2,unit) kraus_family"
  assumes "kf_bound \<EE> \<le> id_cblinfun"
  assumes "U \<in> fst ` Rep_kraus_family \<EE>"
  shows "U* o\<^sub>C\<^sub>L U \<le> id_cblinfun"
proof -
  have *: "{(U, ())} \<subseteq> Rep_kraus_family \<EE>" using assms(2) by auto
  show ?thesis using kf_bound_geq_sum[OF *] assms(1) by auto
qed

lemma norm_in_kraus_map:
  fixes \<EE> :: "('a ell2,'a ell2,unit) kraus_family"
  assumes "kf_bound \<EE> \<le> id_cblinfun"
  assumes "U \<in> fst ` Rep_kraus_family \<EE>"
  shows "norm U \<le> 1"
  using norm_square_in_kraus_map[OF assms] cond_to_norm_1 by auto

lemma purify_comp_kraus_in_kraus_family:
  assumes "UA \<in> purify_comp_kraus n \<EE>" "j<n+1"
  shows "UA j \<in> fst ` Rep_kraus_family (\<EE> j)"
proof (intro PiE_mem[of UA "{0..<n+1}"])
  show "UA \<in> (\<Pi>\<^sub>E a\<in>{0..<n+1}. fst ` Rep_kraus_family (\<EE> a))" 
    using assms(1) unfolding purify_comp_kraus_def by auto
  show "j \<in> {0..<n+1}" using assms(2) by auto
qed

lemma norm_in_purify_comp_kraus:
  fixes \<EE> :: "nat \<Rightarrow> ('a ell2, 'a ell2, unit) kraus_family"
  assumes "\<And>i. i<n+1 \<Longrightarrow> kf_bound (\<EE> i) \<le> id_cblinfun"
  assumes "UA \<in> purify_comp_kraus n \<EE>" 
  shows "\<And>i. i<n+1 \<Longrightarrow> norm (UA i) \<le> 1"
proof -
  fix i assume i: "i<n+1"
  have "UA i \<in> fst ` Rep_kraus_family (\<EE> i)"
    using purify_comp_kraus_in_kraus_family[OF assms(2) \<open>i<n+1\<close>] by auto
  then show "norm (UA i) \<le> 1" using norm_in_kraus_map assms(1) i by auto
qed


lemma run_pure_adv_tc_over:
  assumes "m > n"
  shows "run_pure_adv_tc n (UA(m := x)) UB init' X' Y' H = run_pure_adv_tc n UA UB init' X' Y' H"
  using assms by (induct n arbitrary: m x) auto

lemma run_pure_adv_tc_Fst_over:
  assumes "m > n"
  shows "run_pure_adv_tc n (Fst o UA(m := x)) UB init' X' Y' H = 
       run_pure_adv_tc n (Fst o UA) UB init' X' Y' H"
  using assms by (induct n arbitrary: m x) auto




text \<open>Purifications of the adversarial runs.\<close>

lemma purification_run_mixed_adv:
  assumes "\<And>i. i<n+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  assumes "\<And>i. i<n+1 \<Longrightarrow> fst ` Rep_kraus_family (\<EE> i) \<noteq> {}" (* Needed? *)
  shows "run_mixed_adv n \<EE> UB init' X' Y' H = 
  (\<Sum> UAs \<in> purify_comp_kraus n \<EE>. run_pure_adv_tc n UAs UB init' X' Y' H)"
  unfolding purify_comp_kraus_def using assms
proof (induct n)
  case 0
  have "kf_apply (\<EE> 0) (tc_selfbutter init') = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc E (tc_selfbutter init'))"
    unfolding kf_apply.rep_eq using assms 
    by (subst sum.reindex) (auto simp add: inj_on_fst_Rep_kraus_family d_gr_0) 
  moreover have "(\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (UAs 0) (tc_selfbutter init')) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc E (tc_selfbutter init'))"
    (is "?left = ?right")
  proof -
    have inj1: "inj_on (\<lambda>UA. UA 0) (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i))"
      by (smt (verit, best) PiE_ext inj_on_def singletonD)
    have non_empty: "(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)) \<noteq> {}" 
      by (metis (no_types, lifting) "0"(2) PiE_eq_empty_iff Suc_eq_plus1 singleton_iff zero_less_Suc)
    have "?left = (\<Sum>UA \<in> (\<lambda>UA. UA 0) ` (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc UA (tc_selfbutter init'))"
      by (subst sum.reindex) (auto simp add: inj1)
    also have "\<dots> = (\<Sum>UA \<in> fst ` Rep_kraus_family (\<EE> 0).
       sandwich_tc UA (tc_selfbutter init'))" 
      by (intro sum.cong) (auto simp add: image_projection_PiE non_empty)
    finally show ?thesis by auto
  qed
  ultimately show ?case by auto
next
  case (Suc d)
  have inj2: "inj_on (\<lambda>(y, g). g(Suc d := y))(fst ` Rep_kraus_family (\<EE> (Suc d)) \<times>
      (\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)))"
    by (metis atLeastLessThan_iff inj_combinator less_irrefl_nat)
  let ?\<Phi> = "sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB d)(run_mixed_adv d \<EE> UB init' X' Y' H)"
  let ?\<Psi> = "(\<lambda>UAs. run_pure_adv_tc d UAs UB init' X' Y' H)"
  have kraus: "kf_apply (\<EE> (Suc d)) ?\<Phi> = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> (Suc d))). sandwich_tc E ?\<Phi>)"
    unfolding kf_apply.rep_eq using assms 
    by (subst sum.reindex) (auto simp add: inj_on_fst_Rep_kraus_family Suc)
  also have "\<dots> = (\<Sum>UA\<in>fst ` Rep_kraus_family (\<EE> (Suc d)).
     (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).  sandwich_tc UA
      (sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB d) (?\<Psi> UAs))))" 
    using Suc by (intro sum.cong)(auto simp add: sandwich_tc_sum)
  also have "\<dots> = (\<Sum>(UA,UAs)\<in>fst ` Rep_kraus_family (\<EE> (Suc d))\<times> 
    (\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).
    sandwich_tc UA (sandwich_tc ((X';Y') (Uquery H) o\<^sub>C\<^sub>L UB d) (?\<Psi> UAs)))"
    by (subst sum.cartesian_product) auto 
  also have "\<dots> = (\<Sum>UAs\<in>(\<lambda>(y, g). g(Suc d := y)) ` (fst ` Rep_kraus_family (\<EE> (Suc d)) \<times> 
    (\<Pi>\<^sub>E i\<in> {0..<Suc d}. fst ` Rep_kraus_family (\<EE> i))).
    sandwich_tc (UAs (Suc d) o\<^sub>C\<^sub>L (X';Y') (Uquery H) o\<^sub>C\<^sub>L UB d)(?\<Psi> UAs))" 
    by (subst sum.reindex) (auto intro!: sum.cong simp add: o_def sandwich_tc_compose 
        run_pure_adv_tc_over inj2)
  also have "\<dots> = (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>insert (Suc d) {0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (UAs (Suc d) o\<^sub>C\<^sub>L (X';Y') (Uquery H) o\<^sub>C\<^sub>L UB d) (?\<Psi> UAs))"
    by (subst PiE_insert_eq) auto
  finally show ?case by (auto simp add: set_upt_Suc)
qed


lemma purification_run_mixed_A:
  assumes "\<And>i. i<d+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  assumes "\<And>i. i<d+1 \<Longrightarrow> fst ` Rep_kraus_family (\<EE> i) \<noteq> {}" (* Needed? *)
  shows "run_mixed_A \<EE> H = (\<Sum> UAs \<in> purify_comp_kraus d \<EE>. run_pure_A_tc UAs H)"
  unfolding run_mixed_A_def run_pure_A_tc_def using assms
  by (auto intro!: purification_run_mixed_adv)


lemma purification_run_mixed_B:
  assumes "\<And>i. i<d+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  assumes "\<And>i. i<d+1 \<Longrightarrow> fst ` Rep_kraus_family (\<EE> i) \<noteq> {}" (* Needed? *)
  shows "run_mixed_B \<EE> H S = (\<Sum> UAs \<in> purify_comp_kraus d \<EE>. run_pure_B_tc UAs H S)"
  unfolding run_mixed_B_def run_pure_B_tc_def purify_comp_kraus_def 
  using assms
proof (induct d)
  case 0
  let ?\<EE>0 = "kf_Fst (\<EE> 0)"
  have finite: "finite (Rep_kraus_family ?\<EE>0)" 
    using finite_kf_Fst assms(1)  by auto
  have inj1: "inj_on fst (Rep_kraus_family ?\<EE>0)"
    by (rule inj_on_fst_Rep_kraus_family)
  have inj2: "inj_on Fst (fst ` Rep_kraus_family (\<EE> 0))"
    using inj_on_Fst by auto
  have *: "kf_apply ?\<EE>0 (tc_selfbutter init_B) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family ?\<EE>0). sandwich_tc E (tc_selfbutter init_B))"
    unfolding kf_apply.rep_eq
    by (subst sum.reindex) (auto simp add: infsum_finite[OF finite] inj1 ) 
  have "kf_apply ?\<EE>0 (tc_selfbutter init_B) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc (Fst E) (tc_selfbutter init_B))"
    unfolding * fst_Rep_kf_Fst by (subst sum.reindex) (auto simp add: o_def inj2)
  moreover have "(\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (Fst (UAs 0)) (tc_selfbutter init_B)) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc (Fst E) (tc_selfbutter init_B))"
    (is "?left = ?right")
  proof -
    have inj1: "inj_on (\<lambda>UA. UA 0) (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i))"
      by (smt (verit, best) PiE_ext inj_on_def singletonD)
    have non_empty: "(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)) \<noteq> {}" 
      by (smt (verit, del_insts) PiE_eq_empty_iff add_is_0 assms(2) d_gr_0 emptyE insertE not_gr0)
    have "?left = (\<Sum>UA \<in> (\<lambda>UA. UA 0) ` (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (Fst UA) (tc_selfbutter init_B))"
      by (subst sum.reindex) (auto simp add: inj1)
    also have "\<dots> = (\<Sum>UA \<in> fst ` Rep_kraus_family (\<EE> 0).
       sandwich_tc (Fst UA) (tc_selfbutter init_B))" 
      by (intro sum.cong) (auto simp add: image_projection_PiE non_empty)
    finally show ?thesis by auto
  qed
  ultimately show ?case by auto
next
  case (Suc d)
  let ?\<EE> = "(\<lambda>i. kf_Fst (\<EE> i))"
  have inj1: "inj_on (\<lambda>(y, g). g(Suc d := y))(fst ` Rep_kraus_family (\<EE> (Suc d)) \<times>
      (\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)))"
    by (metis atLeastLessThan_iff inj_combinator less_irrefl_nat)
  let ?\<Phi> = "sandwich_tc ((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S d)
    (run_mixed_adv d ?\<EE> (US S) init_B X_for_B Y_for_B H)"
  let ?\<Psi> = "(\<lambda>UAs. run_pure_adv_tc d UAs (US S) init_B X_for_B Y_for_B H)"
  have finite: "finite (Rep_kraus_family (kf_Fst (\<EE> (Suc d))))"
    using Suc.prems(1) finite_kf_Fst by auto
  have "kf_apply (?\<EE> (Suc d)) ?\<Phi> = 
    (\<Sum>E\<in>fst ` Rep_kraus_family (kf_Fst (\<EE> (Suc d))). sandwich_tc E ?\<Phi>)"
    by (subst sum.reindex) (auto simp add: kf_apply.rep_eq infsum_finite[OF finite] 
        inj_on_fst_Rep_kraus_family)
  also have "\<dots> =  (\<Sum>E\<in>fst ` Rep_kraus_family (\<EE> (Suc d)). sandwich_tc (Fst E) ?\<Phi>)"
    unfolding fst_Rep_kf_Fst by (subst sum.reindex) (auto simp add: inj_on_Fst)
  also have "\<dots> = (\<Sum>UA\<in>fst ` Rep_kraus_family (\<EE> (Suc d)).
     (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).  sandwich_tc (Fst UA)
      (sandwich_tc ((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S d) (?\<Psi> (Fst o UAs)))))" 
    using Suc unfolding kf_Fst_def[symmetric] by (intro sum.cong)(auto simp add: sandwich_tc_sum o_def)
  also have "\<dots> = (\<Sum>(UA,UAs)\<in>fst ` Rep_kraus_family (\<EE> (Suc d))\<times> 
    (\<Pi>\<^sub>E i\<in>{0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).
    sandwich_tc (Fst UA) (sandwich_tc ((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S d) (?\<Psi> (Fst o UAs))))"
    by (subst sum.cartesian_product) auto 
  also have "\<dots> = (\<Sum>UAs\<in>(\<lambda>(y, g). g(Suc d := y)) ` (fst ` Rep_kraus_family (\<EE> (Suc d)) \<times> 
    (\<Pi>\<^sub>E i\<in> {0..<Suc d}. fst ` Rep_kraus_family (\<EE> i))).
    sandwich_tc (Fst (UAs (Suc d)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S d)(?\<Psi> (Fst o UAs)))" 
    by (subst sum.reindex)(use run_pure_adv_tc_Fst_over[where init' = init_B and X' = X_for_B and Y' = Y_for_B] 
        in \<open>auto intro!: sum.cong simp add: o_def sandwich_tc_compose inj1\<close>)
  also have "\<dots> = (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>insert (Suc d) {0..<Suc d}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (Fst (UAs (Suc d)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S d) (?\<Psi> (Fst o UAs)))"
    by (subst PiE_insert_eq) auto
  finally show ?case unfolding kf_Fst_def by (auto simp add: set_upt_Suc o_def)
qed


lemma purification_run_mixed_B_count_prep:
  assumes "\<And>i. i<d+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  assumes "\<And>i. i<d+1 \<Longrightarrow> fst ` Rep_kraus_family (\<EE> i) \<noteq> {}" (* Needed? *)
  assumes "n<d+1"
  shows "run_mixed_adv n (\<lambda>n. kf_Fst (\<EE> n)) (\<lambda>n. U_S' S)
     init_B_count X_for_C Y_for_C H =
    (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0..<n + 1}. fst ` Rep_kraus_family (\<EE> i)).
       run_pure_adv_tc n (Fst \<circ> UAs) (\<lambda>_. U_S' S) init_B_count X_for_C
        Y_for_C H)"
  using assms
proof (induct n)
  case 0
  let ?\<EE>0 = "kf_Fst (\<EE> 0)"
  have finite: "finite (Rep_kraus_family ?\<EE>0)" 
    using finite_kf_Fst assms by auto
  have inj1: "inj_on fst (Rep_kraus_family ?\<EE>0)"
    by (rule inj_on_fst_Rep_kraus_family)
  have inj2: "inj_on Fst (fst ` Rep_kraus_family (\<EE> 0))" using inj_on_Fst by auto
  have *: "kf_apply ?\<EE>0 (tc_selfbutter init_B_count) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family ?\<EE>0). sandwich_tc E (tc_selfbutter init_B_count))"
    unfolding kf_apply.rep_eq
    by (subst sum.reindex) (auto simp add: infsum_finite[OF finite] inj1 ) 
  have "kf_apply ?\<EE>0 (tc_selfbutter init_B_count) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc (Fst E) (tc_selfbutter init_B_count))"
    unfolding * fst_Rep_kf_Fst by (subst sum.reindex) (auto simp add: o_def inj2)
  moreover have "(\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (Fst (UAs 0)) (tc_selfbutter init_B_count)) = 
    (\<Sum>E\<in>fst ` (Rep_kraus_family (\<EE> 0)). sandwich_tc (Fst E) (tc_selfbutter init_B_count))"
    (is "?left = ?right")
  proof -
    have inj1: "inj_on (\<lambda>UA. UA 0) (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i))"
      by (smt (verit, best) PiE_ext inj_on_def singletonD)
    have non_empty: "(\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)) \<noteq> {}" 
      by (smt (verit, del_insts) PiE_eq_empty_iff add_is_0 assms(2) d_gr_0 emptyE insertE not_gr0)
    have "?left = (\<Sum>UA \<in> (\<lambda>UA. UA 0) ` (\<Pi>\<^sub>E i\<in>{0}. fst ` Rep_kraus_family (\<EE> i)).
       sandwich_tc (Fst UA) (tc_selfbutter init_B_count))"
      by (subst sum.reindex) (auto simp add: inj1)
    also have "\<dots> = (\<Sum>UA \<in> fst ` Rep_kraus_family (\<EE> 0).
       sandwich_tc (Fst UA) (tc_selfbutter init_B_count))" 
      by (intro sum.cong) (auto simp add: image_projection_PiE non_empty)
    finally show ?thesis by auto
  qed
  ultimately show ?case by auto
next
  case (Suc n)
  define \<EE>' :: "('mem\<times>nat) kraus_adv" where "\<EE>' = (\<lambda>i. kf_Fst (\<EE> i))"
  have inj1: "inj_on (\<lambda>(y, g). g(Suc n := y))(fst ` Rep_kraus_family (\<EE> (Suc n)) \<times>
      (\<Pi>\<^sub>E i\<in>{0..<Suc n}. fst ` Rep_kraus_family (\<EE> i)))"
    by (metis atLeastLessThan_iff inj_combinator less_irrefl_nat)
  let ?\<Phi> = "sandwich_tc ((X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L U_S' S)
    (run_mixed_adv n \<EE>' (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"
  define \<Psi> where "\<Psi> = (\<lambda>UAs. run_pure_adv_tc n UAs (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"

  have finite: "finite (Rep_kraus_family (kf_Fst (\<EE> (Suc n))))"
    using Suc.prems finite_kf_Fst by auto
  have "kf_apply (\<EE>' (Suc n)) ?\<Phi> = 
    (\<Sum>E\<in>fst ` Rep_kraus_family (kf_Fst (\<EE> (Suc n))). sandwich_tc E ?\<Phi>)"
    unfolding \<EE>'_def
    by (subst sum.reindex) (auto simp add: kf_apply.rep_eq infsum_finite[OF finite] 
        inj_on_fst_Rep_kraus_family)
  also have "\<dots> =  (\<Sum>E\<in>fst ` Rep_kraus_family (\<EE> (Suc n)). sandwich_tc (Fst E) ?\<Phi>)"
    unfolding fst_Rep_kf_Fst by (subst sum.reindex) (auto simp add: inj_on_Fst)
  also have "\<dots> = (\<Sum>UA\<in>fst ` Rep_kraus_family (\<EE> (Suc n)).
     (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0..<Suc n}. fst ` Rep_kraus_family (\<EE> i)).  sandwich_tc (Fst UA)
      (sandwich_tc ((X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L U_S' S) (\<Psi> (Fst o UAs)))))" 
    using Suc  unfolding kf_Fst_def[symmetric] \<Psi>_def \<EE>'_def
    by (auto simp add: sandwich_tc_sum o_def intro!: sum.cong)
  also have "\<dots> = (\<Sum>(UA,UAs)\<in>fst ` Rep_kraus_family (\<EE> (Suc n))\<times> 
    (\<Pi>\<^sub>E i\<in>{0..<Suc n}. fst ` Rep_kraus_family (\<EE> i)). sandwich_tc (Fst UA) 
    (sandwich_tc ((X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L U_S' S) (\<Psi> (Fst o UAs))))"
    by (subst sum.cartesian_product) auto 
  also have "\<dots> = (\<Sum>UAs\<in>(\<lambda>(y, g). g(Suc n := y)) ` (fst ` Rep_kraus_family (\<EE> (Suc n)) \<times> 
    (\<Pi>\<^sub>E i\<in> {0..<Suc n}. fst ` Rep_kraus_family (\<EE> i))). sandwich_tc (Fst (UAs (Suc n)) o\<^sub>C\<^sub>L 
    (X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L U_S' S)(\<Psi> (Fst o UAs)))" 
    unfolding \<Psi>_def by (subst sum.reindex) 
      (use run_pure_adv_tc_Fst_over[where init' = init_B_count and X' = X_for_C and Y' = Y_for_C] 
        in \<open>auto intro!: sum.cong simp add: o_def sandwich_tc_compose inj1\<close>)
  also have "\<dots> = (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>insert (Suc n) {0..<Suc n}. fst ` Rep_kraus_family (\<EE> i)).
    sandwich_tc (Fst (UAs (Suc n)) o\<^sub>C\<^sub>L (X_for_C;Y_for_C) (Uquery H) o\<^sub>C\<^sub>L U_S' S) 
    (\<Psi> (Fst o UAs)))"
    by (subst PiE_insert_eq) auto
  also have "\<dots> = (\<Sum>UAs\<in>(\<Pi>\<^sub>E i\<in>{0..<Suc n + 1}. fst ` Rep_kraus_family (\<EE> i)).
    run_pure_adv_tc (Suc n) (Fst \<circ> UAs) (\<lambda>_. U_S' S) init_B_count X_for_C Y_for_C H)"
    unfolding kf_Fst_def \<Psi>_def by (auto simp add: set_upt_Suc o_def intro!: sum.cong)
  finally show ?case unfolding \<EE>'_def by (auto simp add: comp_def)
qed

lemma purification_run_mixed_B_count:
  assumes "\<And>i. i<d+1 \<Longrightarrow> finite (Rep_kraus_family (\<EE> i))"
  assumes "\<And>i. i<d+1 \<Longrightarrow> fst ` Rep_kraus_family (\<EE> i) \<noteq> {}" (* Needed? *)
  shows "run_mixed_B_count \<EE> H S = (\<Sum> UAs \<in> purify_comp_kraus d \<EE>. run_pure_B_count_tc UAs H S)"
  unfolding run_mixed_B_count_def run_pure_B_count_tc_def purify_comp_kraus_def
  using purification_run_mixed_B_count_prep[where n=d, OF assms] by auto




text \<open>Purification of \<^const>\<open>kf_Fst\<close>\<close>


lemma purification_kf_Fst:
  assumes "\<And>i. i < n + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {}"
  assumes "x \<in> purify_comp_kraus n (\<lambda>n. kf_Fst (F n)::(('a \<times> 'c) ell2, ('b \<times> 'c) ell2, unit) kraus_family)"
  shows "\<exists>UA. x = (\<lambda>a. if a<n+1 then (Fst (UA a)::('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'c) ell2) else undefined)"
proof -
  have nonempty: "PiE {0..<n+1} (\<lambda>i. Fst ` fst ` Rep_kraus_family (F i)
    ::(('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'c) ell2) set) \<noteq> {}"
    by (rule ccontr) (use assms in \<open>auto simp add: PiE_eq_empty_iff\<close>)
  have "x\<in> PiE {0..<n+1} (\<lambda>i. Fst ` fst ` Rep_kraus_family (F i))"
    using assms unfolding purify_comp_kraus_def fst_Rep_kf_Fst by auto
  then have elem: "x a \<in> (\<lambda>f. f a) ` PiE {0..<n+1} (\<lambda>i. Fst ` fst ` Rep_kraus_family (F i))"
    for a by blast
  have rew: "(\<lambda>f. f a) ` PiE {0..<n+1} (\<lambda>i. Fst ` fst ` Rep_kraus_family (F i)::
    (('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'c) ell2) set) = 
    (if a\<in>{0..<n+1}then Fst ` fst ` Rep_kraus_family (F a) else {undefined})" 
    for a by (subst image_projection_PiE) (use nonempty in \<open>auto\<close>)
  have el: "x a \<in> (if a\<in>{0..<n+1} then Fst ` fst ` Rep_kraus_family (F a) else {undefined})" 
    for a using elem unfolding rew by auto
  have ins: "a\<in>{0..<n+1} \<Longrightarrow> x a \<in> Fst ` fst ` Rep_kraus_family (F a)" for a using el by meson
  then have "\<exists>v. (v \<in> Rep_kraus_family (F a) \<and> x a = Fst(fst(v)))" if "a\<in>{0..<n+1}" for a
    using that by fastforce
  then obtain v where v_in: "a\<in>{0..<n+1} \<Longrightarrow> v a \<in> Rep_kraus_family (F a)" 
    and x: "a\<in>{0..<n+1} \<Longrightarrow> x a = (Fst (fst (v a))::('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b \<times> 'c) ell2)" for a
    by metis
  have outs: "\<not>a\<in>{0..<n+1} \<Longrightarrow> x a = undefined" for a by (meson el singletonD)
  define val where "val a = (if a\<in>{0..<n+1} then v a else undefined)" for a
  have "x a = Fst (fst (val a))" if "a\<in>{0..<n+1}" for a 
    unfolding val_def using x[OF that] that by auto
  then have "x a = (if a \<in> {0..<n+1} then Fst (fst (val a)) else undefined)"
    for a by (cases "a\<in>{0..<n+1}", use outs in \<open>auto\<close>)
  then show ?thesis by (intro exI[of _ "(\<lambda>a. fst (val a))"]) auto
qed


end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax

end