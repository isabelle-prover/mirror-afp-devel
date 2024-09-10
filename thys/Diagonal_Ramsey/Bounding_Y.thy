section \<open>Bounding the Size of @{term Y}\<close>

theory Bounding_Y imports Red_Steps

begin

text \<open>yet another telescope variant, with weaker promises but a different conclusion;
as written it holds even if @{term"n=0"}\<close>

lemma prod_lessThan_telescope_mult:
  fixes f::"nat \<Rightarrow> 'a::field"
  assumes "\<And>i. i<n \<Longrightarrow> f i \<noteq> 0" 
  shows "(\<Prod>i<n. f (Suc i) / f i) * f 0 = f n"
  using assms
by (induction n) (auto simp: divide_simps)

subsection \<open>The following results together are Lemma 6.4\<close>
text \<open>Compared with the paper, all the indices are greater by one!!\<close>

context Book
begin

lemma Y_6_4_Red: 
  assumes "i \<in> Step_class {red_step}"
  shows "pee (Suc i) \<ge> pee i - alpha (hgt (pee i))"
  using assms
  by (auto simp: step_kind_defs next_state_def reddish_def pee_def
      split: if_split_asm prod.split)

lemma Y_6_4_DegreeReg: 
  assumes "i \<in> Step_class {dreg_step}" 
  shows "pee (Suc i) \<ge> pee i"
  using assms red_density_X_degree_reg_ge [OF Xseq_Yseq_disjnt, of i]
  by (auto simp: step_kind_defs degree_reg_def pee_def split: if_split_asm prod.split_asm)

lemma Y_6_4_Bblue: 
  assumes i: "i \<in> Step_class {bblue_step}"
  shows "pee (Suc i) \<ge> pee (i-1) - (eps k powr (-1/2)) * alpha (hgt (pee (i-1)))"
proof -
  define X where "X \<equiv> Xseq i" 
  define Y where "Y \<equiv> Yseq i"
  obtain A B S T
    where step: "stepper i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition X Y"
      and "odd i"
      and mb: "many_bluish X"
      and bluebook: "(S,T) = choose_blue_book (X,Y,A,B)"
    using i  
    by (simp add: X_def Y_def step_kind_defs split: if_split_asm prod.split_asm) (metis mk_edge.cases)
  then have X1_eq: "Xseq (Suc i) = T"
    by (force simp: Xseq_def next_state_def split: prod.split)
  have Y1_eq: "Yseq (Suc i) = Y"
    using i by (simp add: Y_def step_kind_defs next_state_def split: if_split_asm prod.split_asm prod.split)
  have "disjnt X Y"
    using Xseq_Yseq_disjnt X_def Y_def by blast
  obtain fin: "finite X" "finite Y"
    by (metis V_state_stepper finX finY step)
  have "X \<noteq> {}" "Y \<noteq> {}"
    using gen_density_def nonterm termination_condition_def by fastforce+
  define i' where "i' = i-1"
  then have Suci': "Suc i' = i"
    by (simp add: \<open>odd i\<close>)
  have i': "i' \<in> Step_class {dreg_step}"
    by (metis dreg_before_step Step_class_insert Suci' UnCI i)
  then have "Xseq (Suc i') = X_degree_reg (Xseq i') (Yseq i')"
            "Yseq (Suc i') = Yseq i'"
      and nonterm': "\<not> termination_condition (Xseq i') (Yseq i')"
    by (auto simp: degree_reg_def X_degree_reg_def step_kind_defs split: if_split_asm prod.split_asm)
  then have Xeq: "X = X_degree_reg (Xseq i') (Yseq i')"
       and  Yeq: "Y = Yseq i'"
    using Suci' by (auto simp: X_def Y_def)
  define pm where "pm \<equiv> (pee i' - eps k powr (-1/2) * alpha (hgt (pee i')))"
  have "T \<subseteq> X"
    using bluebook by (simp add: choose_blue_book_subset fin)
  then have T_reds: "\<And>x. x \<in> T \<Longrightarrow> pm * card Y \<le> card (Neighbours Red x \<inter> Y)"
    by (auto simp: Xeq Yeq pm_def X_degree_reg_def pee_def red_dense_def)
  have "good_blue_book X (S,T)"
    by (meson bluebook choose_blue_book_works fin)
  then have Tne: False if "card T = 0"
    using \<mu>01 \<open>X \<noteq> {}\<close> fin by (simp add: good_blue_book_def pos_prod_le that)
  have "pm * card T * card Y = (\<Sum>x\<in>T. pm * card Y)"
    by simp
  also have "\<dots> \<le> (\<Sum>x\<in>T. card (Neighbours Red x \<inter> Y))"
    using T_reds by (simp add: sum_bounded_below)
  also have "\<dots> = edge_card Red T Y"
    using \<open>disjnt X Y\<close> \<open>finite X\<close> \<open>T\<subseteq>X\<close> Red_E
    by (metis disjnt_subset1 disjnt_sym edge_card_commute edge_card_eq_sum_Neighbours finite_subset)
  also have "\<dots> = red_density T Y * card T * card Y"
    using fin \<open>T\<subseteq>X\<close> by (simp add: finite_subset gen_density_def)
  finally have "pm \<le> red_density T Y" 
    using fin \<open>Y\<noteq>{}\<close> Yeq Yseq_gt0 Tne nonterm' step_terminating_iff by fastforce
  then show ?thesis
    by (simp add: X1_eq Y1_eq i'_def pee_def pm_def)
qed


text \<open>The basic form is actually @{thm[source]Red_5_3}. This variant covers a gap of two, 
     thanks to degree regularisation\<close>
corollary Y_6_4_dbooSt:
  assumes i: "i \<in> Step_class {dboost_step}" and big: "Big_Red_5_3 \<mu> l"
  shows "pee (Suc i) \<ge> pee (i-1)"
proof -
  have  "odd i""i-1 \<in> Step_class {dreg_step}"
    using step_odd i by (auto simp: Step_class_insert_NO_MATCH dreg_before_step)
  then show ?thesis
    using Red_5_3 Y_6_4_DegreeReg assms \<open>odd i\<close> by fastforce
qed

subsection \<open>Towards Lemmas 6.3\<close>

definition "Z_class \<equiv> {i \<in> Step_class {red_step,bblue_step,dboost_step}.
                            pee (Suc i) < pee (i-1) \<and> pee (i-1) \<le> p0}"

lemma finite_Z_class: "finite (Z_class)"
  using finite_components by (auto simp: Z_class_def Step_class_insert_NO_MATCH)

lemma Y_6_3:
  assumes big53: "Big_Red_5_3 \<mu> l" and big41: "Big_Blue_4_1 \<mu> l"
  shows "(\<Sum>i \<in> Z_class. pee (i-1) - pee (Suc i)) \<le> 2 * eps k"
proof -
  define \<S> where "\<S> \<equiv> Step_class {dboost_step}" 
  define \<R> where "\<R> \<equiv> Step_class {red_step}"
  define \<B> where "\<B> \<equiv> Step_class {bblue_step}"
  { fix i
    assume i: "i \<in> \<S>"
    moreover have "odd i"
      using step_odd [of i] i  by (force simp: \<S>_def Step_class_insert_NO_MATCH)
    ultimately have "i-1 \<in> Step_class {dreg_step}"
      by (simp add: \<S>_def dreg_before_step Step_class_insert_NO_MATCH)
    then have "pee (i-1) \<le> pee i \<and> pee i \<le> pee (Suc i)"
      using big53 \<S>_def
      by (metis Red_5_3 One_nat_def Y_6_4_DegreeReg \<open>odd i\<close> i odd_Suc_minus_one)
  }        
  then have dboost: "\<S> \<inter> Z_class = {}"
    by (fastforce simp: Z_class_def)
  { fix i
    assume i: "i \<in> \<B> \<inter> Z_class" 
    then have "i-1 \<in> Step_class {dreg_step}"
      using dreg_before_step step_odd i by (force simp: \<B>_def Step_class_insert_NO_MATCH)
    have pee: "pee (Suc i) < pee (i-1)" "pee (i-1) \<le> p0" and iB: "i \<in> \<B>"
      using i by (auto simp: Z_class_def)
    have "hgt (pee (i-1)) = 1"
    proof -
      have "hgt (pee (i-1)) \<le> 1"
        by (smt (verit, del_insts) hgt_Least less_one pee(2) qfun0 qfun_strict_mono)
      then show ?thesis
        by (metis One_nat_def Suc_pred' diff_is_0_eq hgt_gt0)
    qed
    then have "pee (i-1) - pee (Suc i) \<le> eps k powr (-1/2) * alpha 1"
      using pee iB Y_6_4_Bblue \<mu>01 by (fastforce simp: \<B>_def)
    also have "\<dots> \<le> 1/k"
    proof -
      have "k powr (-1/8) \<le> 1"
        using kn0 by (simp add: ge_one_powr_ge_zero powr_minus_divide)
      then show ?thesis
        by (simp add: alpha_eq eps_def powr_powr divide_le_cancel flip: powr_add)
    qed
    finally have "pee (i-1) - pee (Suc i) \<le> 1/k" .
  }
  then have "(\<Sum>i \<in> \<B> \<inter> Z_class. pee (i-1) - pee (Suc i)) 
             \<le> card (\<B> \<inter> Z_class) * (1/k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "\<dots> \<le> card (\<B>) * (1/k)"
    using bblue_step_finite 
    by (simp add: \<B>_def divide_le_cancel card_mono)
  also have "\<dots> \<le> l powr (3/4) / k"
    using big41 by (simp add: \<B>_def kn0 frac_le bblue_step_limit)
  also have "\<dots> \<le> eps k"
  proof -
    have *: "l powr (3/4) \<le> k powr (3/4)"
      by (simp add: l_le_k powr_mono2)
    have "3/4 - (1::real) = - 1/4"
      by simp
    then show ?thesis
      using divide_right_mono [OF *, of k] 
      by (metis eps_def of_nat_0_le_iff powr_diff powr_one)
  qed
  finally have bblue: "(\<Sum>i\<in>\<B> \<inter> Z_class. pee(i-1) - pee (Suc i)) \<le> eps k" .
  { fix i
    assume i: "i \<in> \<R> \<inter> Z_class" 
    then have pee_alpha: "pee (i-1) - pee (Suc i) 
                       \<le> pee (i-1) - pee i + alpha (hgt (pee i))"
      using Y_6_4_Red by (force simp: \<R>_def)
    have pee_le: "pee (i-1) \<le> pee i"
      using dreg_before_step Y_6_4_DegreeReg[of "i-1"] i step_odd
      by (simp add: \<R>_def Step_class_insert_NO_MATCH)
    consider (1) "hgt (pee i) = 1" | (2) "hgt (pee i) > 1"
      by (metis hgt_gt0 less_one nat_neq_iff)
    then have "pee (i-1) - pee i + alpha (hgt (pee i)) \<le> eps k / k"
    proof cases
      case 1
      then show ?thesis
        by (smt (verit) Red_5_7c kn0 pee_le hgt_works) 
    next
      case 2
      then have p_gt_q: "pee i > qfun 1"
        by (meson hgt_Least not_le zero_less_one)
      have pee_le_q0: "pee (i-1) \<le> qfun 0"
        using 2 Z_class_def i by auto
      also have pee2: "\<dots> \<le> pee i"
        using alpha_eq p_gt_q by (smt (verit, best) kn0 qfun_mono zero_le_one) 
      finally have "pee (i-1) \<le> pee i" .
      then have "pee (i-1) - pee i + alpha (hgt (pee i)) 
              \<le> qfun 0 - pee i + eps k * (pee i - qfun 0 + 1/k)"
        using Red_5_7b pee_le_q0 pee2 by fastforce
      also have "\<dots> \<le> eps k / k"
        using kn0 pee2 by (simp add: algebra_simps) (smt (verit) affine_ineq eps_le1)
      finally show ?thesis .
    qed
    with pee_alpha have "pee (i-1) - pee (Suc i) \<le> eps k / k"
      by linarith
  }
  then have "(\<Sum>i \<in> \<R> \<inter> Z_class. pee (i-1) - pee (Suc i))
           \<le> card (\<R> \<inter> Z_class) * (eps k / k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "\<dots> \<le> card (\<R>) * (eps k / k)"
    using eps_ge0[of k] assms red_step_finite
    by (simp add: \<R>_def divide_le_cancel mult_le_cancel_right card_mono)
  also have "\<dots> \<le> k * (eps k / k)"
    using red_step_limit \<R>_def \<mu>01 
    by (smt (verit, best) divide_nonneg_nonneg eps_ge0 mult_mono nat_less_real_le of_nat_0_le_iff)
  also have "\<dots> \<le> eps k"
    by (simp add: eps_ge0)
  finally have red: "(\<Sum>i\<in>\<R> \<inter> Z_class. pee (i-1) - pee (Suc i)) \<le> eps k" .
  have *: "finite (\<B>)" "finite (\<R>)" "\<And>x. x \<in> \<B> \<Longrightarrow> x \<notin> \<R>"
    using finite_components  by (auto simp: \<B>_def \<R>_def Step_class_def)
  have eq: "Z_class = \<S> \<inter> Z_class  \<union> \<B> \<inter> Z_class \<union> \<R> \<inter> Z_class"
    by (auto simp: Z_class_def \<B>_def \<R>_def \<S>_def Step_class_insert_NO_MATCH)
  show ?thesis
    using bblue red
    by (subst eq) (simp add: sum.union_disjoint dboost disjoint_iff *)
qed

subsection \<open>Lemma 6.5\<close>

lemma Y_6_5_Red:
  assumes i: "i \<in> Step_class {red_step}" and "k\<ge>16"
  defines "h \<equiv> \<lambda>i. hgt (pee i)"
  shows "h (Suc i) \<ge> h i - 2"
proof (cases "h i \<le> 3")
  case True
  have "h (Suc i) \<ge> 1"
    by (simp add: h_def Suc_leI hgt_gt0)
  with True show ?thesis
    by linarith
next
  case False
  have "k>0" using assms by auto
  have "eps k \<le> 1/2"
    using \<open>k\<ge>16\<close> by (simp add: eps_eq_sqrt divide_simps real_le_rsqrt)
  moreover have "0 \<le> x \<and> x \<le> 1/2 \<Longrightarrow> x * (1 + x)\<^sup>2 + 1 \<le> (1 + x)\<^sup>2" for x::real
    by sos
  ultimately have \<section>: "eps k * (1 + eps k)\<^sup>2 + 1 \<le> (1 + eps k)\<^sup>2"
    using eps_ge0 by presburger
  have le1: "eps k + 1 / (1 + eps k)\<^sup>2 \<le> 1"
    using mult_left_mono [OF \<section>, of "inverse ((1 + eps k)\<^sup>2)"]
    by (simp add: ring_distribs inverse_eq_divide) (smt (verit))
  have 0: "0 \<le> (1 + eps k) ^ (h i - Suc 0)"
    using eps_ge0 by auto
  have lesspi: "qfun (h i - 1) < pee i"
    using False hgt_Least [of "h i - 1" "pee i"] unfolding h_def by linarith
  have A: "(1 + eps k) ^ h i = (1 + eps k) * (1 + eps k) ^ (h i - Suc 0)"
    using False power.simps by (metis h_def Suc_pred hgt_gt0)
  have B: "(1 + eps k) ^ (h i - 3) = 1 / (1 + eps k)^2 * (1 + eps k) ^ (h i - Suc 0)"
    using eps_gt0 [OF kn0] False
    by (simp add: divide_simps Suc_diff_Suc numeral_3_eq_3 flip: power_add)
  have "qfun (h i - 3) \<le> qfun (h i - 1) - (qfun (h i) - qfun (h i - 1))"
    using kn0 mult_left_mono [OF le1 0]
    by (simp add: qfun_eq A B algebra_simps divide_right_mono flip: add_divide_distrib diff_divide_distrib)
  also have "\<dots> < pee i - alpha (h i)"
    using lesspi by (simp add: alpha_def)
  also have "\<dots> \<le> pee (Suc i)"
    using Y_6_4_Red i by (force simp: h_def)
  finally have "qfun (h i - 3) < pee (Suc i)" .
  with hgt_greater show ?thesis
    unfolding h_def by force
qed

lemma Y_6_5_DegreeReg: 
  assumes "i \<in> Step_class {dreg_step}"
  shows "hgt (pee (Suc i)) \<ge> hgt (pee i)"
  using hgt_mono Y_6_4_DegreeReg assms by presburger

corollary Y_6_5_dbooSt:
  assumes "i \<in> Step_class {dboost_step}" and "Big_Red_5_3 \<mu> l" 
  shows "hgt (pee (Suc i)) \<ge> hgt (pee i)"
  using kn0 Red_5_3 assms hgt_mono by blast

text \<open>this remark near the top of page 19 only holds in the limit\<close>
lemma "\<forall>\<^sup>\<infinity>k. (1 + eps k) powr (- real (nat \<lfloor>2 * eps k powr (-1/2)\<rfloor>)) \<le> 1 - eps k powr (1/2)"
  unfolding eps_def by real_asymp

end

definition "Big_Y_6_5_Bblue \<equiv> \<lambda>l. \<forall>k\<ge>l. (1 + eps k) powr (- real (nat \<lfloor>2*(eps k powr (-1/2))\<rfloor>)) \<le> 1 - eps k powr (1/2)" 

text \<open>establishing the size requirements for Y 6.5\<close>
lemma Big_Y_6_5_Bblue:
  shows "\<forall>\<^sup>\<infinity>l. Big_Y_6_5_Bblue l"
  unfolding Big_Y_6_5_Bblue_def eps_def by (intro eventually_all_ge_at_top; real_asymp)

lemma (in Book) Y_6_5_Bblue:
  fixes \<kappa>::real
  defines "\<kappa> \<equiv> eps k powr (-1/2)"
  assumes i: "i \<in> Step_class {bblue_step}" and big: "Big_Y_6_5_Bblue l"
  defines "h \<equiv> hgt (pee (i-1))"
  shows "hgt (pee (Suc i)) \<ge> h - 2*\<kappa>"
proof (cases "h > 2*\<kappa> + 1")
  case True
  then have "0 < h - 1"
    by (smt (verit, best) \<kappa>_def one_less_of_natD powr_non_neg zero_less_diff)
  with True have "pee (i-1) > qfun (h-1)"
    by (simp add: h_def hgt_less_imp_qfun_less)
  then have "qfun (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / k < pee (i-1) - \<kappa> * alpha h"
    using \<open>0 < h-1\<close> Y_6_4_Bblue [OF i] eps_ge0
    apply (simp add: alpha_eq \<kappa>_def)
    by (smt (verit, best) field_sum_of_halves mult.assoc mult.commute powr_mult_base)
  also have "\<dots> \<le> pee (Suc i)"
    using Y_6_4_Bblue i h_def \<kappa>_def by blast
  finally have A: "qfun (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / k < pee (Suc i)" .
  have ek0: "0 < 1 + eps k"
    by (smt (verit, best) eps_ge0)
  have less_h: "nat \<lfloor>2*\<kappa>\<rfloor> < h"
    using True \<open>0 < h - 1\<close> by linarith
  have "qfun (h - nat \<lfloor>2*\<kappa>\<rfloor> - 1) = p0 + ((1 + eps k) ^ (h - nat \<lfloor>2*\<kappa>\<rfloor> - 1) - 1) / k"
    by (simp add: qfun_eq)
  also have "\<dots> \<le> p0 + ((1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1) - 1) / k"
  proof -
    have ge0: "(1 + eps k) ^ (h-1) \<ge> 0"
      using eps_ge0 by auto
    have "(1 + eps k) ^ (h - nat \<lfloor>2*\<kappa>\<rfloor> - 1) = (1 + eps k) ^ (h-1) * (1 + eps k) powr - real(nat \<lfloor>2*\<kappa>\<rfloor>)"
      using less_h ek0 by (simp add: algebra_simps flip: powr_realpow powr_add)
    also have "\<dots> \<le> (1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1)"
      using big l_le_k unfolding \<kappa>_def Big_Y_6_5_Bblue_def
      by (metis mult.commute ge0 mult_left_mono)
    finally have "(1 + eps k) ^ (h - nat \<lfloor>2*\<kappa>\<rfloor> - 1)
        \<le> (1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1)" .
    then show ?thesis
      by (intro add_left_mono divide_right_mono diff_right_mono) auto
  qed
  also have "\<dots> \<le> qfun (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / real k"
    using kn0 eps_ge0 by (simp add: qfun_eq powr_half_sqrt field_simps)
  also have "\<dots> < pee (Suc i)"
    using A by blast
  finally have "qfun (h - nat \<lfloor>2*\<kappa>\<rfloor> - 1) < pee (Suc i)" .
  then have "h - nat \<lfloor>2*\<kappa>\<rfloor> \<le> hgt (pee (Suc i))"
    using hgt_greater by force
  with less_h show ?thesis
    unfolding \<kappa>_def
    by (smt (verit) less_imp_le_nat of_nat_diff of_nat_floor of_nat_mono powr_ge_zero)
next
  case False
  then show ?thesis
    by (smt (verit, del_insts) of_nat_0 hgt_gt0 nat_less_real_le)
qed

subsection \<open>Lemma 6.2\<close>

definition "Big_Y_6_2 \<equiv> \<lambda>\<mu> l. Big_Y_6_5_Bblue l \<and> Big_Red_5_3 \<mu> l \<and> Big_Blue_4_1 \<mu> l
               \<and> (\<forall>k\<ge>l. ((1 + eps k)^2) * eps k powr (1/2) \<le> 1 
                       \<and> (1 + eps k) powr (2 * eps k powr (-1/2)) \<le> 2 \<and> k \<ge> 16)"

text \<open>establishing the size requirements for 6.2\<close>
lemma Big_Y_6_2:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_Y_6_2 \<mu> l"
  using assms Big_Y_6_5_Bblue Big_Red_5_3 Big_Blue_4_1
  unfolding Big_Y_6_2_def eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_geI1 eventually_all_ge_at_top; real_asymp)
  done

context Book
begin

text \<open>Following Bhavik in excluding the even steps (degree regularisation).
      Assuming it hasn't halted, the conclusion also holds for the even cases anyway.\<close>
proposition Y_6_2:
  defines "RBS \<equiv> Step_class {red_step,bblue_step,dboost_step}"
  assumes j: "j \<in> RBS" and big: "Big_Y_6_2 \<mu> l"
  shows "pee (Suc j) \<ge> p0 - 3 * eps k"
proof (cases "pee (Suc j) \<ge> p0")
  case True
  then show ?thesis
    by (smt (verit) eps_ge0)
next
  case False
  then have pj_less: "pee(Suc j) < p0" by linarith
  have big53: "Big_Red_5_3 \<mu> l"
    and Y63: "(\<Sum>i \<in> Z_class. pee (i-1) - pee (Suc i)) \<le> 2 * eps k"
    and Y65B: "\<And>i. i \<in> Step_class {bblue_step} \<Longrightarrow> hgt (pee (Suc i)) \<ge> hgt (pee (i-1)) - 2*(eps k powr (-1/2))"
    and big1: "((1 + eps k)^2) * eps k powr (1/2) \<le> 1" and big2: "(1 + eps k) powr (2 * eps k powr (-1/2)) \<le> 2"
    and "k\<ge>16"
    using big Y_6_5_Bblue Y_6_3 kn0 l_le_k by (auto simp: Big_Y_6_2_def)
  have Y64_S: " \<And>i. i \<in> Step_class {dboost_step} \<Longrightarrow> pee i \<le> pee (Suc i)"
    using big53 Red_5_3 by simp
  define J where "J \<equiv> {j'. j'<j \<and> pee j' \<ge> p0 \<and> even j'}"
  have "finite J"
    by (auto simp: J_def)
  have "pee 0 = p0"
    by (simp add: pee_eq_p0)
  have odd_RBS: "odd i" if "i \<in> RBS" for i
    using step_odd that unfolding RBS_def by blast
  with odd_pos j have "j>0" by auto
  have non_halted: "j \<notin> Step_class {halted}"
    using j by (auto simp: Step_class_def RBS_def)
  have exists: "J \<noteq> {}"
    using \<open>0 < j\<close> \<open>pee 0 = p0\<close> by (force simp: J_def less_eq_real_def)
  define j' where "j' \<equiv> Max J"
  have "j' \<in> J"
    using \<open>finite J\<close> exists by (force simp: j'_def)
  then have "j' < j" "even j'" and pSj': "pee j' \<ge> p0"
    by (auto simp: J_def odd_RBS)
  have maximal: "j'' \<le> j'" if "j'' \<in> J" for j''
    using \<open>finite J\<close> exists by (simp add: j'_def that)
  have "pee (j'+2) - 2 * eps k \<le> pee (j'+2) - (\<Sum>i \<in> Z_class. pee (i-1) - pee (Suc i))"
    using Y63 by simp
  also have "\<dots> \<le> pee (Suc j)"
  proof -
    define Z where "Z \<equiv> \<lambda>j. {i. pee (Suc i) < pee (i-1) \<and> j'+2 < i \<and> i\<le>j \<and> i \<in> RBS}"
    have Zsub: "Z i \<subseteq> {Suc j'<..i}" for i
      by (auto simp: Z_def)
    then have finZ: "finite (Z i)" for i
      by (meson finite_greaterThanAtMost finite_subset)
    have *: "(\<Sum>i \<in> Z j. pee (i-1) - pee (Suc i)) \<le> (\<Sum>i \<in> Z_class. pee (i-1) - pee (Suc i))"
    proof (intro sum_mono2 [OF finite_Z_class])
      show "Z j \<subseteq> Z_class" 
      proof 
        fix i
        assume i: "i \<in> Z j"
        then have dreg: "i-1 \<in> Step_class {dreg_step}" and "i\<noteq>0" "j' < i"
          by (auto simp: Z_def RBS_def dreg_before_step)
        with i dreg maximal have "pee (i-1) < p0"
          unfolding Z_def J_def
          using Suc_less_eq2 less_eq_Suc_le odd_RBS by fastforce
        then show "i \<in> Z_class"
          using i by (simp add: Z_def RBS_def Z_class_def)
      qed
      show "0 \<le> pee (i-1) - pee (Suc i)" if "i \<in> Z_class - Z j" for i
        using that by (auto simp: Z_def Z_class_def)
    qed
    then have "pee (j'+2) - (\<Sum>i\<in>Z_class. pee (i-1) - pee (Suc i))
            \<le> pee (j'+2) - (\<Sum>i \<in> Z j. pee (i-1) - pee (Suc i))"
      by auto
    also have "\<dots> \<le> pee (Suc j)"
    proof -
      have "pee (j'+2) - pee (Suc m) \<le> (\<Sum>i \<in> Z m. pee (i-1) - pee (Suc i))"
        if "m \<in> RBS" "j' < m" "m\<le>j" for m
        using that
      proof (induction m rule: less_induct)
        case (less m)
        then have "odd m"
          using odd_RBS by blast
        show ?case
        proof (cases "j'+2 < m") 
          case True
          with less.prems
          have Z_if: "Z m = (if pee (Suc m) < pee (m-1) then insert m (Z (m-2)) else Z (m-2))"
            by (auto simp: Z_def)
              (metis le_diff_conv2 Suc_leI add_2_eq_Suc' add_leE even_Suc nat_less_le odd_RBS)+
          have "m-2 \<in> RBS"
            using True \<open>m \<in> RBS\<close> step_odd_minus2 by (auto simp: RBS_def)
          then have *: "pee (j'+2) - pee (m - Suc 0) \<le> (\<Sum>i\<in>Z (m - 2). pee (i-1) - pee (Suc i))"
            using less.IH True less \<open>j' \<in> J\<close> by (force simp: J_def Suc_less_eq2)
          moreover have "m \<notin> Z (m - 2)"
            by (auto simp: Z_def)
          ultimately show ?thesis
            by (simp add: Z_if finZ)
        next
          case False
          then have [simp]: "m = Suc j'"
            using \<open>odd m\<close> \<open>j' < m\<close> \<open>even j'\<close> by presburger
          have "Z m = {}"
            by (auto simp: Z_def)
          then show ?thesis
            by simp
        qed
      qed
      then show ?thesis
        using j J_def \<open>j' \<in> J\<close> \<open>j' < j\<close> by force 
    qed
    finally show ?thesis .
  qed
  finally have p2_le_pSuc: "pee (j'+2) - 2 * eps k \<le> pee (Suc j)" .
  have "Suc j' \<in> RBS"
    unfolding RBS_def
  proof (intro not_halted_odd_RBS)
    show "Suc j' \<notin> Step_class {halted}"
      using Step_class_halted_forever Suc_leI \<open>j' < j\<close> non_halted by blast
  qed (use \<open>even j'\<close> in auto)
  then have "pee (j'+2) < p0"
    using maximal[of "j'+2"] False \<open>j' < j\<close> j odd_RBS 
    by (simp add: J_def) (smt (verit, best) Suc_lessI even_Suc)
  then have le1: "hgt (pee (j'+2)) \<le> 1"
    by (smt (verit) kn0 hgt_Least qfun0 qfun_strict_mono zero_less_one)
  moreover 
  have j'_dreg: "j' \<in> Step_class {dreg_step}"
    using RBS_def \<open>Suc j' \<in> RBS\<close> dreg_before_step by blast
  have 1: "eps k powr -(1/2) \<ge> 1"
    using kn0 by (simp add: eps_def powr_powr ge_one_powr_ge_zero)
  consider (R) "Suc j' \<in> Step_class {red_step}"
         | (B) "Suc j' \<in> Step_class {bblue_step}"
         | (S) "Suc j' \<in> Step_class {dboost_step}"
    by (metis Step_class_insert UnE \<open>Suc j' \<in> RBS\<close> RBS_def)
  note j'_cases = this
  then have hgt_le_hgt: "hgt (pee j') \<le> hgt (pee (j'+2)) + 2 * eps k powr (-1/2)"
  proof cases
    case R
    have "real (hgt (pee j')) \<le> hgt (pee (Suc j'))"
      using Y_6_5_DegreeReg[OF j'_dreg] kn0 by (simp add: eval_nat_numeral)
    also have "\<dots> \<le> hgt (pee (j'+2)) + 2 * eps k powr (-1/2)"
      using Y_6_5_Red[OF R \<open>k\<ge>16\<close>] 1 by (simp add: eval_nat_numeral)
    finally show ?thesis .
  next
    case B
    show ?thesis
      using Y65B [OF B] by simp
  next
    case S
    then show ?thesis
      using Y_6_4_DegreeReg \<open>pee (j'+2) < p0\<close> Y64_S j'_dreg pSj' by force
  qed
  ultimately have B: "hgt (pee j') \<le> 1 + 2 * eps k powr (-1/2)"
    by linarith
  have "2 \<le> real k powr (1/2)"
    using \<open>k\<ge>16\<close> by (simp add: powr_half_sqrt real_le_rsqrt)
  then have 8: "2 \<le> real k powr 1 * real k powr -(1/8)"
    unfolding powr_add [symmetric] using \<open>k\<ge>16\<close> order.trans nle_le by fastforce
  have "p0 - eps k \<le> qfun 0 - 2 * eps k powr (1/2) / k"
    using mult_left_mono [OF 8, of "k powr (-1/8)"] kn0 
    by (simp add: qfun_eq eps_def powr_powr field_simps flip: powr_add)
  also have "\<dots> \<le> pee j'  - eps k powr (-1/2) * alpha (hgt (pee j'))"
  proof -
    have 2: "(1 + eps k) ^ (hgt (pee j') - Suc 0) \<le> 2"
      using B big2 kn0 eps_ge0
      by (smt (verit) diff_Suc_less hgt_gt0 nat_less_real_le powr_mono powr_realpow)
    have *: "x \<ge> 0 \<Longrightarrow> inverse (x powr (1/2)) * x = x powr (1/2)" for x::real
      by (simp add: inverse_eq_divide powr_half_sqrt real_div_sqrt)
    have "p0 - pee j' \<le> 0"
      by (simp add: pSj')
    also have "\<dots> \<le> 2 * eps k powr (1/2) / k - (eps k powr (1/2)) * (1 + eps k) ^ (hgt (pee j') - 1) / k"
      using mult_left_mono [OF 2, of "eps k powr (1/2) / k"]
      by (simp add: field_simps diff_divide_distrib)
    finally have "p0 - 2 * eps k powr (1/2) / k 
       \<le> pee j' - (eps k powr (1/2)) * (1 + eps k) ^ (hgt (pee j') - 1) / k"
      by simp
    with * [OF eps_ge0] show ?thesis
      by (simp add: alpha_hgt_eq powr_minus) (metis mult.assoc)
  qed
  also have "\<dots> \<le> pee (j'+2)"
    using j'_cases
  proof cases
    case R
    have hs_le3: "hgt (pee (Suc j')) \<le> 3"
      using le1 Y_6_5_Red[OF R \<open>k\<ge>16\<close>] by simp
    then have h_le3: "hgt (pee j') \<le> 3"
      using Y_6_5_DegreeReg [OF j'_dreg] by simp
    have alpha1: "alpha (hgt (pee (Suc j'))) \<le> eps k * (1 + eps k) ^ 2 / k"
      by (metis alpha_Suc_eq alpha_mono hgt_gt0 hs_le3 numeral_nat(3))
    have alpha2: "alpha (hgt (pee j')) \<ge> eps k / k"
      by (simp add: Red_5_7a)
    have "pee j' - eps k powr (- 1/2) * alpha (hgt (pee j')) 
       \<le> pee (Suc j') - alpha (hgt (pee (Suc j')))"
    proof -
      have "alpha (hgt (pee (Suc j'))) \<le> (1 + eps k)\<^sup>2 * alpha (hgt (pee j'))"
        using alpha1 mult_left_mono [OF alpha2, of "(1 + eps k)\<^sup>2"]
        by (simp add: mult.commute)
      also have "\<dots> \<le> inverse (eps k powr (1/2)) * alpha (hgt (pee j'))"
        using mult_left_mono [OF big1, of "alpha (hgt (pee j'))"] eps_gt0[OF kn0] alpha_ge0
        by (simp add: divide_simps mult_ac)
      finally have "alpha (hgt (pee (Suc j')))
                 \<le> inverse (eps k powr (1/2)) * alpha (hgt (pee j'))" .
      then show ?thesis
        using Y_6_4_DegreeReg[OF j'_dreg] by (simp add: powr_minus)
    qed
    also have "\<dots> \<le> pee (j'+2)"
      by (simp add: R Y_6_4_Red)
    finally show ?thesis .
  next
    case B
    then show ?thesis
      using Y_6_4_Bblue by force
  next
    case S
    show ?thesis
      using Y_6_4_DegreeReg S \<open>pee (j'+2) < p0\<close> Y64_S j'_dreg pSj' by fastforce
  qed
  finally have "p0 - eps k \<le> pee (j'+2)" .
  then have "p0 - 3 * eps k \<le> pee (j'+2) - 2 * eps k"
    by simp
  with p2_le_pSuc show ?thesis
    by linarith
qed

corollary Y_6_2_halted:
  assumes big: "Big_Y_6_2 \<mu> l"
  shows "pee halted_point \<ge> p0 - 3 * eps k"
proof (cases "halted_point=0")
  case True
  then show ?thesis
    by (simp add: eps_ge0 pee_eq_p0)
next
  case False
  then have "halted_point-1 \<notin> Step_class {halted}"
    by (simp add: halted_point_minimal)
  then consider "halted_point-1 \<in> Step_class {red_step,bblue_step,dboost_step}"
              | "halted_point-1 \<in> Step_class {dreg_step}"
    using not_halted_even_dreg not_halted_odd_RBS by blast
  then show ?thesis
  proof cases
    case 1
    with False Y_6_2[of "halted_point-1"] big show ?thesis by simp
  next
    case m1_dreg: 2
    then have *: "pee halted_point \<ge> pee (halted_point-1)"
      using False Y_6_4_DegreeReg[of "halted_point-1"] by simp
    have "odd halted_point"
      using m1_dreg False step_even[of "halted_point-1"] by simp
    then consider "halted_point=1" | "halted_point\<ge>2"
      by (metis False less_2_cases One_nat_def not_le)
    then show ?thesis
    proof cases
      case 1
      with * eps_gt0[of k] kn0 show ?thesis 
        by (simp add: pee_eq_p0)
    next
      case 2
      then have m2: "halted_point-2 \<in> Step_class {red_step,bblue_step,dboost_step}"
        using step_before_dreg[of "halted_point-2"] m1_dreg
        by (simp flip: Suc_diff_le)
      then obtain j where j: "halted_point-1 = Suc j"
        using 2 not0_implies_Suc by fastforce
      then have "pee (Suc j) \<ge> p0 - 3 * eps k"
        by (metis m2 Suc_1 Y_6_2 big diff_Suc_1 diff_Suc_eq_diff_pred)
      with * j show ?thesis by simp
    qed
  qed
qed

end

subsection \<open>Lemma 6.1\<close>

context P0_min
begin

definition "ok_fun_61 \<equiv> \<lambda>k. (2 * real k / ln 2) * ln (1 - 2 * eps k powr (1/2) / p0_min)"

text \<open>Not actually used, but justifies the definition above\<close>
lemma ok_fun_61_works:
  assumes "k>0" "p0_min > 2 * eps k powr (1/2)"
  shows "2 powr (ok_fun_61 k) = (1 - 2 * (eps k) powr(1/2) / p0_min) ^ (2*k)"
  using eps_gt0[of k] p0_min assms
  by (simp add: powr_def ok_fun_61_def flip: powr_realpow)

lemma ok_fun_61: "ok_fun_61 \<in> o(real)"
  unfolding eps_def ok_fun_61_def
  using p0_min by real_asymp

definition 
  "Big_Y_6_1 \<equiv> 
    \<lambda>\<mu> l. Big_Y_6_2 \<mu> l \<and> (\<forall>k\<ge>l. eps k powr (1/2) \<le> 1/3 \<and> p0_min > 2 * eps k powr (1/2))"

text \<open>establishing the size requirements for 6.1\<close>
lemma Big_Y_6_1:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_Y_6_1 \<mu> l"
  using p0_min assms Big_Y_6_2
  unfolding Big_Y_6_1_def eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_ge_at_top eventually_all_geI0; real_asymp)
  done

end

lemma (in Book) Y_6_1:
  assumes big: "Big_Y_6_1 \<mu> l"
  defines "st \<equiv> Step_class {red_step,dboost_step}"
  shows "card (Yseq halted_point) / card Y0 \<ge> 2 powr (ok_fun_61 k) * p0 ^ card st"
proof -
  have big13: "eps k powr (1/2) \<le> 1/3" 
    and big_p0: "p0_min > 2 * eps k powr (1/2)"
    and big62: "Big_Y_6_2 \<mu> l"
    and big41: "Big_Blue_4_1 \<mu> l"
    using big l_le_k by (auto simp: Big_Y_6_1_def Big_Y_6_2_def)
  with l_le_k have dboost_step_limit: "card (Step_class {dboost_step}) < k"
    using bblue_dboost_step_limit by fastforce
  define p0m where "p0m \<equiv> p0 - 2 * eps k powr (1/2)"
  have "p0m > 0"
    using big_p0 p0_ge by (simp add: p0m_def)
  let ?RS = "Step_class {red_step,dboost_step}"
  let ?BD = " Step_class {bblue_step,dreg_step}"
  have not_halted_below_m: "i \<notin> Step_class {halted}" if "i < halted_point" for i
    using that 
    by (simp add:  halted_point_minimal)
  have BD_card: "card (Yseq i) = card (Yseq (Suc i))"
    if "i \<in> ?BD" for i
  proof -
    have "Yseq (Suc i) = Yseq i"
      using that
      by (auto simp: step_kind_defs next_state_def degree_reg_def split: prod.split if_split_asm)
    with p0_01 kn0 show ?thesis
      by auto
  qed
  have RS_card: "p0m * card (Yseq i) \<le> card (Yseq (Suc i))"
    if "i \<in> ?RS" for i
  proof -
    have Yeq: "Yseq (Suc i) = Neighbours Red (cvx i) \<inter> Yseq i"
      using that 
      by (auto simp: step_kind_defs next_state_def split: prod.split if_split_asm)
    have "odd i"
      using that step_odd by (auto simp: Step_class_def)
    moreover have i_not_halted: "i \<notin> Step_class {halted}"
      using that by (auto simp: Step_class_def)
    ultimately have iminus1_dreg: "i - 1 \<in> Step_class {dreg_step}"
      by (simp add: dreg_before_step not_halted_odd_RBS)
    have "p0m * card (Yseq i) \<le> (1 - eps k powr (1/2)) * pee (i-1) * card (Yseq i)"
    proof (cases "i=1")
      case True
      with p0_01 show ?thesis 
        by (simp add: p0m_def pee_eq_p0 algebra_simps mult_right_mono)
    next
      case False
      with \<open>odd i\<close> have "i>2"
        by (metis Suc_lessI dvd_refl One_nat_def odd_pos one_add_one plus_1_eq_Suc)
      have "i-2 \<in> Step_class {red_step,bblue_step,dboost_step}"
      proof (intro not_halted_odd_RBS)
        show "i - 2 \<notin> Step_class {halted}"
          using i_not_halted Step_class_not_halted diff_le_self by blast
        show "odd (i-2)"
          using \<open>2 < i\<close> \<open>odd i\<close> by auto
      qed
      then have Y62: "pee (i-1) \<ge> p0 - 3 * eps k"
        using Y_6_2 [OF _ big62] \<open>2 < i\<close> by (metis Suc_1 Suc_diff_Suc Suc_lessD)
      show ?thesis
      proof (intro mult_right_mono)
        have "eps k powr (1/2) * pee (i-1) \<le> eps k powr (1/2) * 1"
          by (metis mult.commute mult_right_mono powr_ge_zero pee_le1)
        moreover have "3 * eps k \<le> eps k powr (1/2)"
        proof -
          have "3 * eps k = 3 * (eps k powr (1/2))\<^sup>2"
            using eps_ge0 powr_half_sqrt real_sqrt_pow2 by presburger
          also have "\<dots> \<le> 3 * ((1/3) * eps k powr (1/2))"
            by (smt (verit) big13 mult_right_mono power2_eq_square powr_ge_zero)
          also have "\<dots> \<le> eps k powr (1/2)"
            by simp
          finally show ?thesis .
        qed
        ultimately show "p0m \<le> (1 - eps k powr (1/2)) * pee (i - 1)"
          using Y62 by (simp add: p0m_def algebra_simps)
      qed auto
    qed
    also have "\<dots> \<le> card (Neighbours Red (cvx i) \<inter> Yseq i)"
      using Red_5_8 [OF iminus1_dreg] cvx_in_Xseq that \<open>odd i\<close> 
        by fastforce
    finally show ?thesis
      by (simp add: Yeq)
  qed
  define ST where "ST \<equiv> \<lambda>i. ?RS \<inter> {..<i}"
  have "ST (Suc i) = (if i \<in> ?RS then insert i (ST i) else ST i)" for i
    by (auto simp: ST_def less_Suc_eq)
  then have [simp]: "card (ST (Suc i)) = (if i \<in> ?RS then Suc (card (ST i)) else card (ST i))" for i
    by (simp add: ST_def)
  have STm: "ST halted_point = st"
    by (auto simp: ST_def st_def Step_class_def simp flip: halted_point_minimal)
  have "p0m ^ card (ST i) \<le> (\<Prod>j<i. card (Yseq(Suc j)) / card (Yseq j))" if "i\<le>halted_point"for i
    using that
  proof (induction i)
    case 0
    then show ?case
      by (auto simp: ST_def)
  next
    case (Suc i)
    then have i: "i \<notin> Step_class {halted}"
      by (simp add: not_halted_below_m)
    consider (RS) "i \<in> ?RS"
           | (BD) "i \<in> ?BD \<and> i \<notin> ?RS"
      using i stepkind.exhaust by (auto simp: Step_class_def)
    then show ?case
    proof cases
      case RS
      then have "p0m ^ card (ST (Suc i)) = p0m * p0m ^ card (ST i)"
        by simp
      also have "\<dots> \<le> p0m * (\<Prod>j<i. card (Yseq(Suc j)) / card (Yseq j))"
        using Suc Suc_leD \<open>0 < p0m\<close> mult_left_mono by auto
      also have "\<dots> \<le> (card (Yseq (Suc i)) / card (Yseq i)) * (\<Prod>j<i. card (Yseq (Suc j)) / card (Yseq j))"
      proof (intro mult_right_mono)
        show "p0m \<le> card (Yseq (Suc i)) / card (Yseq i)"
          by (simp add: RS RS_card Yseq_gt0 i pos_le_divide_eq)
      qed (simp add: prod_nonneg)
      also have "\<dots> = (\<Prod>j<Suc i.  card (Yseq (Suc j)) / card (Yseq j))"
        by simp
      finally show ?thesis .
    next
      case BD
      with Yseq_gt0 [OF i] show ?thesis
        by (simp add: Suc Suc_leD BD_card)
    qed      
  qed
  then have "p0m ^ card (ST halted_point) \<le> (\<Prod>j < halted_point. card (Yseq(Suc j)) / card (Yseq j))"
    by blast
  also have "\<dots> = card (Yseq halted_point) / card (Yseq 0)"
  proof -
    have "\<And>i. i < halted_point \<Longrightarrow> card (Yseq i) \<noteq> 0"
      by (metis Yseq_gt0 less_irrefl not_halted_below_m)
    then show ?thesis
      using card_XY0 prod_lessThan_telescope_mult [of halted_point "\<lambda>i. real (card (Yseq i))"]
      by (simp add: nonzero_eq_divide_eq)
  qed
  finally have *: "(p0 - 2 * eps k powr (1/2)) ^ card st \<le> card (Yseq halted_point) / card (Y0)"
    by (simp add: STm p0m_def)
  \<comment> \<open>Asymptotic part of the argument\<close>
  have st_le_2k: "card st \<le> 2 * k"
  proof -
    have "st \<subseteq> Step_class {red_step,dboost_step}" 
      by (auto simp: st_def Step_class_insert_NO_MATCH)
    moreover have "finite (Step_class {red_step,dboost_step})"
      using finite_components by (auto simp: Step_class_insert_NO_MATCH)
    ultimately have "card st \<le> card (Step_class {red_step,dboost_step})"
      using card_mono by blast
    also have "\<dots> = card (Step_class {red_step} \<union> Step_class {dboost_step})"
      by (auto simp: Step_class_insert_NO_MATCH)
    also have "\<dots> \<le> k+k"
      by (meson add_le_mono card_Un_le dboost_step_limit le_trans less_imp_le_nat red_step_limit)
    finally show ?thesis 
      by auto
  qed
  have "2 powr (ok_fun_61 k) * p0 ^ card st \<le> (p0 - 2 * eps k powr (1/2)) ^ card st"
  proof -
    have "2 powr (ok_fun_61 k) = (1 - 2 * (eps k) powr(1/2) / p0_min) ^ (2*k)"
      using eps_gt0[of k] p0_min big_p0
      by (simp add: powr_def ok_fun_61_def flip: powr_realpow)
    also have "\<dots> \<le> (1 - 2 * (eps k) powr(1/2) / p0) ^ (2*k)"
      using p0_ge p0_min big_p0 by (intro power_mono) (auto simp: frac_le)
    also have "\<dots> \<le> (1 - 2 * (eps k) powr(1/2) / p0) ^ card st"
      using big_p0 p0_01 \<open>0 < p0m\<close>
      by (intro power_decreasing st_le_2k) (auto simp: p0m_def)
    finally have \<section>: "2 powr ok_fun_61 k \<le> (1 - 2 * eps k powr (1/2) / p0) ^ card st" .
    have "(1 - 2 * eps k powr (1/2) / p0) ^ card st * p0 ^ card st
       = ((1 - 2 * eps k powr (1/2) / p0) * p0) ^ card st"
      by (simp add: power_mult_distrib)
    also have "\<dots> = (p0 - 2 * eps k powr (1/2)) ^ card st"
      using p0_01 by (simp add: algebra_simps)
    finally show ?thesis
      using mult_right_mono [OF \<section>, of "p0 ^ card st"] p0_01 by auto 
  qed
  with * show ?thesis
    by linarith
qed

end
