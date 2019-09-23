section\<open>Material already in development version as of September 2019\<close>

theory Fourier_Aux1
  imports "HOL-Analysis.Analysis"
begin

lemma square_powr_half [simp]:
  fixes x::real shows "x\<^sup>2 powr (1/2) = \<bar>x\<bar>"
  by (simp add: powr_half_sqrt)

lemma frac_1_eq: "frac (x+1) = frac x"
  by (simp add: frac_def)

context comm_monoid_set
begin

lemma in_pairs: "F g {2*m..Suc(2*n)} = F (\<lambda>i. g(2*i) \<^bold>* g(Suc(2*i))) {m..n}"
proof (induction n)
  case 0
  show ?case
    by (cases "m=0") auto
next
  case (Suc n)
  then show ?case
    by (auto simp: assoc split: if_split_asm)
qed

lemma in_pairs_0: "F g {..Suc(2*n)} = F (\<lambda>i. g(2*i) \<^bold>* g(Suc(2*i))) {..n}"
  using in_pairs [of _ 0 n] by (simp add: atLeast0AtMost)

end

context linordered_nonzero_semiring
begin

lemma numeral_le_iff: "numeral m \<le> numeral n \<longleftrightarrow> m \<le> n"
proof -
  have "of_nat (numeral m) \<le> of_nat (numeral n) \<longleftrightarrow> m \<le> n"
    by (simp only: less_eq_num_def nat_of_num_numeral of_nat_le_iff)
  then show ?thesis by simp
qed

lemma one_le_numeral: "1 \<le> numeral n"
  using numeral_le_iff [of num.One n] by (simp add: numeral_One)

lemma numeral_le_one_iff: "numeral n \<le> 1 \<longleftrightarrow> n \<le> num.One"
  using numeral_le_iff [of n num.One] by (simp add: numeral_One)

lemma numeral_less_iff: "numeral m < numeral n \<longleftrightarrow> m < n"
proof -
  have "of_nat (numeral m) < of_nat (numeral n) \<longleftrightarrow> m < n"
    unfolding less_num_def nat_of_num_numeral of_nat_less_iff ..
  then show ?thesis by simp
qed

lemma not_numeral_less_one: "\<not> numeral n < 1"
  using numeral_less_iff [of n num.One] by (simp add: numeral_One)

lemma one_less_numeral_iff: "1 < numeral n \<longleftrightarrow> num.One < n"
  using numeral_less_iff [of num.One n] by (simp add: numeral_One)

lemma zero_le_numeral: "0 \<le> numeral n"
  using dual_order.trans one_le_numeral zero_le_one by blast

lemma zero_less_numeral: "0 < numeral n"
  using less_linear not_numeral_less_one order.strict_trans zero_less_one by blast

lemma not_numeral_le_zero: "\<not> numeral n \<le> 0"
  by (simp add: not_le zero_less_numeral)

lemma not_numeral_less_zero: "\<not> numeral n < 0"
  by (simp add: not_less zero_le_numeral)

lemmas le_numeral_extra =
  zero_le_one not_one_le_zero
  order_refl [of 0] order_refl [of 1]

lemmas less_numeral_extra =
  zero_less_one not_one_less_zero
  less_irrefl [of 0] less_irrefl [of 1]

lemmas le_numeral_simps [simp] =
  numeral_le_iff
  one_le_numeral
  numeral_le_one_iff
  zero_le_numeral
  not_numeral_le_zero

lemmas less_numeral_simps [simp] =
  numeral_less_iff
  one_less_numeral_iff
  not_numeral_less_one
  zero_less_numeral
  not_numeral_less_zero

end

lemma powr_numeral [simp]: "0 \<le> x \<Longrightarrow> x powr (numeral n :: real) = x ^ (numeral n)"
  by (metis less_le power_zero_numeral powr_0 of_nat_numeral powr_realpow)

context linordered_semidom
begin

lemma power_mono_iff [simp]:
  shows "\<lbrakk>a \<ge> 0; b \<ge> 0; n>0\<rbrakk> \<Longrightarrow> a ^ n \<le> b ^ n \<longleftrightarrow> a \<le> b"
  using power_mono [of a b] power_strict_mono [of b a] not_le by auto

end

lemma tendsto_sup[tendsto_intros]:
  fixes X :: "'a \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "(X \<longlongrightarrow> x) net" "(Y \<longlongrightarrow> y) net"
  shows "((\<lambda>i. sup (X i) (Y i)) \<longlongrightarrow> sup x y) net"
   unfolding sup_max eucl_sup by (intro assms tendsto_intros)

lemma tendsto_inf[tendsto_intros]:
  fixes X :: "'a \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "(X \<longlongrightarrow> x) net" "(Y \<longlongrightarrow> y) net"
  shows "((\<lambda>i. inf (X i) (Y i)) \<longlongrightarrow> inf x y) net"
   unfolding inf_min eucl_inf by (intro assms tendsto_intros)

lemma continuous_on_max [continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. max (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_max)

lemma continuous_on_min [continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. min (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_min)

lemma Ints_eq_abs_less1:
  fixes x:: "'a :: linordered_idom"
  shows "\<lbrakk>x \<in> Ints; y \<in> Ints\<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> abs (x-y) < 1"
  using eq_iff_diff_eq_0 by (fastforce intro: Ints_nonzero_abs_less1)

lemma indicator_times_eq_if:
  fixes f :: "'a \<Rightarrow> 'b::comm_ring_1"
  shows "indicator S x * f x = (if x \<in> S then f x else 0)" "f x * indicator S x = (if x \<in> S then f x else 0)"
  by auto

lemma indicator_scaleR_eq_if:
  fixes f :: "'a \<Rightarrow> 'b::real_vector"
  shows "indicator S x *\<^sub>R f x = (if x \<in> S then f x else 0)"
  by simp

lemma lebesgue_on_UNIV_eq: "lebesgue_on UNIV = lebesgue"
proof -
  have "measure_of UNIV (sets lebesgue) (emeasure lebesgue) = lebesgue"
    by (metis measure_of_of_measure space_borel space_completion space_lborel)
  then show ?thesis
    by (auto simp: restrict_space_def)
qed

lemma mem_limsup_iff: "x \<in> limsup A \<longleftrightarrow> (\<exists>\<^sub>F n in sequentially. x \<in> A n)"
  by (simp add: Limsup_def) (metis (mono_tags) eventually_mono not_frequently)

lemma integral_restrict_Int:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue" "T \<in> sets lebesgue"
  shows "integral\<^sup>L (lebesgue_on T) (\<lambda>x. if x \<in> S then f x else 0) = integral\<^sup>L (lebesgue_on (S \<inter> T)) f"
proof -
  have "(\<lambda>x. indicat_real T x *\<^sub>R (if x \<in> S then f x else 0)) = (\<lambda>x. indicat_real (S \<inter> T) x *\<^sub>R f x)"
    by (force simp: indicator_def)
  then show ?thesis
    by (simp add: assms sets.Int Bochner_Integration.integral_restrict_space)
qed

lemma space_lebesgue_on [simp]: "space (lebesgue_on S) = S"
  by (simp add: space_restrict_space)

corollary absolutely_integrable_on_const [simp]:
  fixes c :: "'a::euclidean_space"
  assumes "S \<in> lmeasurable"
  shows "(\<lambda>x. c) absolutely_integrable_on S"
  by (metis (full_types) assms absolutely_integrable_integrable_bound integrable_on_const order_refl)

lemma integral_restrict_UNIV:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "integral\<^sup>L lebesgue (\<lambda>x. if x \<in> S then f x else 0) = integral\<^sup>L (lebesgue_on S) f"
  using integral_restrict_Int [of S UNIV f] assms
  by (simp add: lebesgue_on_UNIV_eq)

lemma tendsto_eventually: "eventually (\<lambda>x. f x = c) F \<Longrightarrow> filterlim f (nhds c) F"
  by (simp add: eventually_mono eventually_nhds_x_imp_x filterlim_iff)

lemma content_cbox_plus:
  fixes x :: "'a::euclidean_space"
  shows "content(cbox x (x + h *\<^sub>R One)) = (if h \<ge> 0 then h ^ DIM('a) else 0)"
  by (simp add: algebra_simps content_cbox_if box_eq_empty)

lemma finite_measure_lebesgue_on: "S \<in> lmeasurable \<Longrightarrow> finite_measure (lebesgue_on S)"
  by (auto simp: finite_measureI fmeasurable_def emeasure_restrict_space)

lemma measurable_bounded_by_integrable_imp_absolutely_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f \<in> borel_measurable (lebesgue_on S)" "S \<in> sets lebesgue"
    and "g integrable_on S" and "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> (g x)"
  shows "f absolutely_integrable_on S"
  using assms absolutely_integrable_integrable_bound measurable_bounded_by_integrable_imp_integrable by blast

lemma absolutely_integrable_measurable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<in> sets lebesgue"
  shows "f absolutely_integrable_on S \<longleftrightarrow> f \<in> borel_measurable (lebesgue_on S) \<and> integrable (lebesgue_on S) (norm \<circ> f)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "f \<in> borel_measurable (lebesgue_on S)"
    by (simp add: absolutely_integrable_on_def integrable_imp_measurable)
  then show ?rhs
    using assms set_integrable_norm [of lebesgue S f] L
    by (simp add: integrable_restrict_space set_integrable_def)
next
  assume ?rhs then show ?lhs
    using assms integrable_on_lebesgue_on
    by (metis absolutely_integrable_integrable_bound comp_def eq_iff measurable_bounded_by_integrable_imp_integrable)
qed

lemma lim_const_over_n [tendsto_intros]:
  fixes a :: "'a::real_normed_field"
  shows "(\<lambda>n. a / of_nat n) \<longlonglongrightarrow> 0"
  using tendsto_mult [OF tendsto_const [of a] lim_1_over_n] by simp

lemma add_mono_ennreal: "x < ennreal y \<Longrightarrow> x' < ennreal y' \<Longrightarrow> x + x' < ennreal (y + y')"
  by (metis (full_types) add_strict_mono ennreal_less_zero_iff ennreal_plus less_le not_less zero_le)

lemma enn2real_sum:"(\<And>i. i \<in> I \<Longrightarrow> f i < top) \<Longrightarrow> enn2real (sum f I) = sum (enn2real \<circ> f) I"
  by (induction I rule: infinite_finite_induct) (auto simp: enn2real_plus)

lemma sets_lebesgue_outer_open:
  fixes e::real
  assumes S: "S \<in> sets lebesgue" and "e > 0"
  obtains T where "open T" "S \<subseteq> T" "(T - S) \<in> lmeasurable" "emeasure lebesgue (T - S) < ennreal e"
proof -
  obtain S' where S': "S \<subseteq> S'" "S' \<in> sets borel"
              and null: "S' - S \<in> null_sets lebesgue"
              and em: "emeasure lebesgue S = emeasure lborel S'"
    using completion_upper[of S lborel] S by auto
  then have f_S': "S' \<in> sets borel"
    using S by (auto simp: fmeasurable_def)
  with outer_regular_lborel[OF _ \<open>0<e\<close>]
  obtain U where U: "open U" "S' \<subseteq> U" "emeasure lborel (U - S') < e"
    by blast
  show thesis
  proof
    show "open U" "S \<subseteq> U"
      using f_S' U S' by auto
  have "(U - S) = (U - S') \<union> (S' - S)"
    using S' U by auto
  then have eq: "emeasure lebesgue (U - S) = emeasure lborel (U - S')"
    using null  by (simp add: U(1) emeasure_Un_null_set f_S' sets.Diff)
  have "(U - S) \<in> sets lebesgue"
    by (simp add: S U(1) sets.Diff)
  then show "(U - S) \<in> lmeasurable"
    unfolding fmeasurable_def using U(3) eq less_le_trans by fastforce
  with eq U show "emeasure lebesgue (U - S) < e"
    by (simp add: eq)
  qed
qed

lemma sets_lebesgue_inner_closed:
  fixes e::real
  assumes "S \<in> sets lebesgue" "e > 0"
  obtains T where "closed T" "T \<subseteq> S" "S-T \<in> lmeasurable" "emeasure lebesgue (S - T) < ennreal e"
proof -
  have "-S \<in> sets lebesgue"
    using assms by (simp add: Compl_in_sets_lebesgue)
  then obtain T where "open T" "-S \<subseteq> T"
          and T: "(T - -S) \<in> lmeasurable" "emeasure lebesgue (T - -S) < e"
    using sets_lebesgue_outer_open assms  by blast
  show thesis
  proof
    show "closed (-T)"
      using \<open>open T\<close> by blast
    show "-T \<subseteq> S"
      using \<open>- S \<subseteq> T\<close> by auto
    show "S - ( -T) \<in> lmeasurable" "emeasure lebesgue (S - (- T)) < e"
      using T by (auto simp: Int_commute)
  qed
qed

corollary eventually_ae_filter_negligible:
  "eventually P (ae_filter lebesgue) \<longleftrightarrow> (\<exists>N. negligible N \<and> {x. \<not> P x} \<subseteq> N)"
  by (auto simp: completion.AE_iff_null_sets negligible_iff_null_sets null_sets_completion_subset)


lemma borel_measurable_affine:
  fixes f :: "'a :: euclidean_space \<Rightarrow> 'b :: euclidean_space"
  assumes f: "f \<in> borel_measurable lebesgue" and "c \<noteq> 0"
  shows "(\<lambda>x. f(t + c *\<^sub>R x)) \<in> borel_measurable lebesgue"
proof -
  { fix a b
    have "{x. f x \<in> cbox a b} \<in> sets lebesgue"
      using f cbox_borel lebesgue_measurable_vimage_borel by blast
    then have "(\<lambda>x. (x - t) /\<^sub>R c) ` {x. f x \<in> cbox a b} \<in> sets lebesgue"
    proof (rule differentiable_image_in_sets_lebesgue)
      show "(\<lambda>x. (x - t) /\<^sub>R c) differentiable_on {x. f x \<in> cbox a b}"
        unfolding differentiable_on_def differentiable_def
        by (rule \<open>c \<noteq> 0\<close> derivative_eq_intros strip exI | simp)+
    qed auto
    moreover
    have "{x. f(t + c *\<^sub>R x) \<in> cbox a b} = (\<lambda>x. (x-t) /\<^sub>R c) ` {x. f x \<in> cbox a b}"
      using \<open>c \<noteq> 0\<close> by (auto simp: image_def)
    ultimately have "{x. f(t + c *\<^sub>R x) \<in> cbox a b} \<in> sets lebesgue"
      by (auto simp: borel_measurable_vimage_closed_interval) }
  then show ?thesis
    by (subst lebesgue_on_UNIV_eq [symmetric]; auto simp: borel_measurable_vimage_closed_interval)
qed


corollary lebesgue_real_affine:
  "c \<noteq> 0 \<Longrightarrow> lebesgue = density (distr lebesgue lebesgue (\<lambda>x. t + c * x)) (\<lambda>_. ennreal (abs c))"
    using lebesgue_affine_euclidean [where c= "\<lambda>x::real. c"] by simp

lemma nn_integral_real_affine_lebesgue:
  fixes c :: real assumes f[measurable]: "f \<in> borel_measurable lebesgue" and c: "c \<noteq> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>lebesgue) = ennreal\<bar>c\<bar> * (\<integral>\<^sup>+x. f(t + c * x) \<partial>lebesgue)"
proof -
  have "(\<integral>\<^sup>+x. f x \<partial>lebesgue) = (\<integral>\<^sup>+x. f x \<partial>density (distr lebesgue lebesgue (\<lambda>x. t + c * x)) (\<lambda>x. ennreal \<bar>c\<bar>))"
    using lebesgue_real_affine c by auto
  also have "\<dots> = \<integral>\<^sup>+ x. ennreal \<bar>c\<bar> * f x \<partial>distr lebesgue lebesgue (\<lambda>x. t + c * x)"
    by (subst nn_integral_density) auto
  also have "\<dots> = ennreal \<bar>c\<bar> * integral\<^sup>N (distr lebesgue lebesgue (\<lambda>x. t + c * x)) f"
    using f measurable_distr_eq1 nn_integral_cmult by blast
  also have "\<dots> = \<bar>c\<bar> * (\<integral>\<^sup>+x. f(t + c * x) \<partial>lebesgue)"
    using lebesgue_affine_measurable[where c= "\<lambda>x::real. c"]
    by (subst nn_integral_distr) (force+)
  finally show ?thesis .
qed

lemma lebesgue_integrable_real_affine:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  assumes f: "integrable lebesgue f" and "c \<noteq> 0"
  shows "integrable lebesgue (\<lambda>x. f(t + c * x))"
proof -
  have "(\<lambda>x. norm (f x)) \<in> borel_measurable lebesgue"
    by (simp add: borel_measurable_integrable f)
  then show ?thesis
    using assms borel_measurable_affine [of f c]
    unfolding integrable_iff_bounded
    by (subst (asm) nn_integral_real_affine_lebesgue[where c=c and t=t])  (auto simp: ennreal_mult_less_top)
qed

lemma lebesgue_integrable_real_affine_iff:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space"
  shows "c \<noteq> 0 \<Longrightarrow> integrable lebesgue (\<lambda>x. f(t + c * x)) \<longleftrightarrow> integrable lebesgue f"
  using lebesgue_integrable_real_affine[of f c t]
        lebesgue_integrable_real_affine[of "\<lambda>x. f(t + c * x)" "1/c" "-t/c"]
  by (auto simp: field_simps)

lemma\<^marker>\<open>tag important\<close> lebesgue_integral_real_affine:
  fixes f :: "real \<Rightarrow> 'a :: euclidean_space" and c :: real
  assumes c: "c \<noteq> 0" shows "(\<integral>x. f x \<partial> lebesgue) = \<bar>c\<bar> *\<^sub>R (\<integral>x. f(t + c * x) \<partial>lebesgue)"
proof cases
  have "(\<lambda>x. t + c * x) \<in> lebesgue \<rightarrow>\<^sub>M lebesgue"
    using lebesgue_affine_measurable[where c= "\<lambda>x::real. c"] \<open>c \<noteq> 0\<close> by simp
  moreover
  assume "integrable lebesgue f"
  ultimately show ?thesis
    by (subst lebesgue_real_affine[OF c, of t]) (auto simp: integral_density integral_distr)
next
  assume "\<not> integrable lebesgue f" with c show ?thesis
    by (simp add: lebesgue_integrable_real_affine_iff not_integrable_integral_eq)
qed

lemma has_bochner_integral_lebesgue_real_affine_iff:
  fixes i :: "'a :: euclidean_space"
  shows "c \<noteq> 0 \<Longrightarrow>
    has_bochner_integral lebesgue f i \<longleftrightarrow>
    has_bochner_integral lebesgue (\<lambda>x. f(t + c * x)) (i /\<^sub>R \<bar>c\<bar>)"
  unfolding has_bochner_integral_iff lebesgue_integrable_real_affine_iff
  by (simp_all add: lebesgue_integral_real_affine[symmetric] divideR_right cong: conj_cong)

lemma absolutely_integrable_measurable_real:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "S \<in> sets lebesgue"
  shows "f absolutely_integrable_on S \<longleftrightarrow>
         f \<in> borel_measurable (lebesgue_on S) \<and> integrable (lebesgue_on S) (\<lambda>x. \<bar>f x\<bar>)"
  by (simp add: absolutely_integrable_measurable assms o_def)

lemma continuous_imp_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on (cbox a b) f"
  shows "integrable (lebesgue_on (cbox a b)) f"
proof -
  have "f absolutely_integrable_on cbox a b"
    by (simp add: absolutely_integrable_continuous assms)
  then show ?thesis
    by (simp add: integrable_restrict_space set_integrable_def)
qed

lemma continuous_imp_integrable_real:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  assumes "continuous_on {a..b} f"
  shows "integrable (lebesgue_on {a..b}) f"
  by (metis assms continuous_imp_integrable interval_cbox)

lemma integral_abs_bound_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes "integrable M f" "integrable M g" "\<And>x. x \<in> space M \<Longrightarrow> \<bar>f x\<bar> \<le> g x"
  shows "\<bar>\<integral>x. f x \<partial>M\<bar> \<le> (\<integral>x. g x \<partial>M)"
proof -
  have "LINT x|M. \<bar>f x\<bar> \<le> integral\<^sup>L M g"
    by (simp add: assms integral_mono)
  then show ?thesis
    by (metis dual_order.trans integral_abs_bound)
qed

lemmas lim_explicit = tendsto_explicit

lemma ennreal_tendsto_0_iff: "(\<And>n. f n \<ge> 0) \<Longrightarrow> ((\<lambda>n. ennreal (f n)) \<longlonglongrightarrow> 0) \<longleftrightarrow> (f \<longlonglongrightarrow> 0)"
  by (metis (mono_tags) ennreal_0 eventuallyI order_refl tendsto_ennreal_iff)

lemma borel_measurable_continuous_onI: "continuous_on UNIV f \<Longrightarrow> f \<in> borel_measurable borel"
  by (drule borel_measurable_continuous_on_restrict) simp

lemma has_integral_integral_lebesgue_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "integrable (lebesgue_on S) f" "S \<in> sets lebesgue"
  shows "(f has_integral (integral\<^sup>L (lebesgue_on S) f)) S"
proof -
  let ?f = "\<lambda>x. if x \<in> S then f x else 0"
  have "integrable lebesgue (\<lambda>x. indicat_real S x *\<^sub>R f x)"
    using indicator_scaleR_eq_if [of S _ f] assms
  by (metis (full_types) integrable_restrict_space sets.Int_space_eq2)
  then have "integrable lebesgue ?f"
    using indicator_scaleR_eq_if [of S _ f] assms by auto
  then have "(?f has_integral (integral\<^sup>L lebesgue ?f)) UNIV"
    by (rule has_integral_integral_lebesgue)
  then have "(f has_integral (integral\<^sup>L lebesgue ?f)) S"
    using has_integral_restrict_UNIV by blast
  moreover
  have "S \<inter> space lebesgue \<in> sets lebesgue"
    by (simp add: assms)
  then have "(integral\<^sup>L lebesgue ?f) = (integral\<^sup>L (lebesgue_on S) f)"
    by (simp add: integral_restrict_space indicator_scaleR_eq_if)
  ultimately show ?thesis
    by auto
qed

lemma lebesgue_integral_eq_integral:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "integrable (lebesgue_on S) f" "S \<in> sets lebesgue"
  shows "integral\<^sup>L (lebesgue_on S) f = integral S f"
  by (metis has_integral_integral_lebesgue_on assms integral_unique)

declare isCont_Ln' [continuous_intros]

lemma absolutely_integrable_imp_integrable:
  assumes "f absolutely_integrable_on S" "S \<in> sets lebesgue"
  shows "integrable (lebesgue_on S) f"
  by (meson assms integrable_restrict_space set_integrable_def sets.Int sets.top)

lemma insert_null_sets_iff [simp]: "insert a N \<in> null_sets lebesgue \<longleftrightarrow> N \<in> null_sets lebesgue"
    (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (meson completion.complete2 subset_insertI)
next
  assume ?rhs then show ?lhs
  by (simp add: null_sets.insert_in_sets null_setsI)
qed

lemma
  fixes a::real
  shows lmeasurable_interval [iff]: "{a..b} \<in> lmeasurable" "{a<..<b} \<in> lmeasurable"
  apply (metis box_real(2) lmeasurable_cbox)
  by (metis box_real(1) lmeasurable_box)

lemma integrable_const_ivl [iff]:
  fixes a::"'a::ordered_euclidean_space"
  shows "integrable (lebesgue_on {a..b}) (\<lambda>x. c)"
  by (metis cbox_interval finite_measure.integrable_const finite_measure_lebesgue_on lmeasurable_cbox)

lemma absolutely_integrable_reflect[simp]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "(\<lambda>x. f(-x)) absolutely_integrable_on cbox (-b) (-a) \<longleftrightarrow> f absolutely_integrable_on cbox a b"
  apply (auto simp: absolutely_integrable_on_def dest: integrable_reflect [THEN iffD1])
  unfolding integrable_on_def by auto

lemma absolutely_integrable_reflect_real[simp]:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  shows "(\<lambda>x. f(-x)) absolutely_integrable_on {-b .. -a} \<longleftrightarrow> f absolutely_integrable_on {a..b::real}"
  unfolding box_real[symmetric] by (rule absolutely_integrable_reflect)

lemma absolutely_integrable_on_subcbox:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  shows "\<lbrakk>f absolutely_integrable_on S; cbox a b \<subseteq> S\<rbrakk> \<Longrightarrow> f absolutely_integrable_on cbox a b"
  by (meson absolutely_integrable_on_def integrable_on_subcbox)

lemma absolutely_integrable_on_subinterval:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  shows "\<lbrakk>f absolutely_integrable_on S; {a..b} \<subseteq> S\<rbrakk> \<Longrightarrow> f absolutely_integrable_on {a..b}"
  using absolutely_integrable_on_subcbox by fastforce

lemma integral_restrict:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "S \<subseteq> T" "S \<in> sets lebesgue" "T \<in> sets lebesgue"
  shows "integral\<^sup>L (lebesgue_on T) (\<lambda>x. if x \<in> S then f x else 0) = integral\<^sup>L (lebesgue_on S) f"
  using integral_restrict_Int [of S T f] assms
  by (simp add: Int_absorb2)

lemma absolutely_integrable_continuous_real:
  fixes f :: "real \<Rightarrow> 'b::euclidean_space"
  shows "continuous_on {a..b} f \<Longrightarrow> f absolutely_integrable_on {a..b}"
  by (metis absolutely_integrable_continuous box_real(2))

lemma absolutely_integrable_imp_borel_measurable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "f absolutely_integrable_on S" "S \<in> sets lebesgue"
  shows "f \<in> borel_measurable (lebesgue_on S)"
  using absolutely_integrable_measurable assms by blast

lemma measurable_bounded_by_integrable_imp_lebesgue_integrable:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes f: "f \<in> borel_measurable (lebesgue_on S)" and g: "integrable (lebesgue_on S) g"
    and normf: "\<And>x. x \<in> S \<Longrightarrow> norm(f x) \<le> g x" and S: "S \<in> sets lebesgue"
  shows "integrable (lebesgue_on S) f"
proof -
  have "f absolutely_integrable_on S"
    by (metis (no_types) S absolutely_integrable_integrable_bound f g integrable_on_lebesgue_on measurable_bounded_by_integrable_imp_integrable normf)
  then show ?thesis
    by (simp add: S integrable_restrict_space set_integrable_def)
qed

lemma lebesgue_on_mono:
  assumes major: "AE x in lebesgue_on S. P x" and minor: "\<And>x.\<lbrakk>P x; x \<in> S\<rbrakk> \<Longrightarrow> Q x"
  shows "AE x in lebesgue_on S. Q x"
proof -
  have "AE a in lebesgue_on S. P a \<longrightarrow> Q a"
    using minor space_restrict_space by fastforce
  then show ?thesis
    using major by auto
qed

lemma integral_eq_zero_null_sets:
  assumes "S \<in> null_sets lebesgue"
  shows "integral\<^sup>L (lebesgue_on S) f = 0"
proof (rule integral_eq_zero_AE)
  show "AE x in lebesgue_on S. f x = 0"
    by (metis (no_types, lifting) assms AE_not_in lebesgue_on_mono null_setsD2 null_sets_restrict_space order_refl)
qed

lemma sin_zero_pi_iff:
  fixes x::real
  assumes "\<bar>x\<bar> < pi"
  shows "sin x = 0 \<longleftrightarrow> x = 0"
proof
  show "x = 0" if "sin x = 0"
    using that assms by (auto simp: sin_zero_iff)
qed auto

lemma id_borel_measurable_lebesgue [iff]: "id \<in> borel_measurable lebesgue"
  by (simp add: measurable_completion)

lemma id_borel_measurable_lebesgue_on [iff]: "id \<in> borel_measurable (lebesgue_on S)"
  by (simp add: measurable_completion measurable_restrict_space1)

lemma root_abs_power: "n > 0 \<Longrightarrow> abs (root n (y ^n)) = abs y"
  using root_sgn_power [of n]
  by (metis abs_ge_zero power_abs real_root_abs real_root_power_cancel)

lemma power_tendsto_0_iff [simp]:
  fixes f :: "'a \<Rightarrow> real"
  assumes "n > 0"
  shows "((\<lambda>x. f x ^ n) \<longlongrightarrow> 0) F \<longleftrightarrow> (f \<longlongrightarrow> 0) F"
proof -
  have "((\<lambda>x. \<bar>root n (f x ^ n)\<bar>) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> 0) F"
    by (auto simp: assms root_abs_power tendsto_rabs_zero_iff)
  then have "((\<lambda>x. f x ^ n) \<longlongrightarrow> 0) F \<Longrightarrow> (f \<longlongrightarrow> 0) F"
    by (metis tendsto_real_root abs_0 real_root_zero tendsto_rabs)
  with assms show ?thesis
    by (auto simp: tendsto_null_power)
qed

end

