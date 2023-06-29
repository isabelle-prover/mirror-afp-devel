section \<open>Randomized Algorithms\label{sec:randomized_algorithm}\<close>

text \<open>This section introduces the @{term "random_alg"} monad, that can be used to represent
executable randomized algorithms. It is a type-definition based on the internal representation from
Section~\ref{sec:randomized_algorithm_internal} with the wellformedness restriction.

Additionally, we introduce the @{term "spmf_of_ra"} morphism, which represent the distribution of
a randomized algorithm, under the assumption that the coin flips are independent and unbiased.

We also show that it is a Scott-continuous monad-morphism and introduce transfer theorems, with
which it is possible to establish the corresponding SPMF of a randomized algorithms, even in the
case of (possibly infinite) loops.\<close>

theory Randomized_Algorithm
  imports
    Randomized_Algorithm_Internal
begin

text \<open>A stronger variant of @{thm [source] pmf_eqI}.\<close>

lemma pmf_eq_iff_le:
  fixes p q :: "'a pmf"
  assumes "\<And>x. pmf p x \<le> pmf q x"
  shows "p = q"
proof -
  have "(\<integral>x. pmf q x - pmf p x \<partial>count_space UNIV) = 0"
    by (simp_all add:integrable_pmf integral_pmf)
  moreover have "integrable (count_space UNIV) (\<lambda>x. pmf q x - pmf p x)"
    by (simp add:integrable_pmf)
  moreover  have "AE x in count_space UNIV. 0 \<le> pmf q x - pmf p x"
    using assms unfolding AE_count_space by auto
  ultimately have "AE x in count_space UNIV. pmf q x - pmf p x = 0"
    using integral_nonneg_eq_0_iff_AE by blast
  hence "\<And>x. pmf p x = pmf q x" unfolding AE_count_space by simp
  thus ?thesis by (intro pmf_eqI) auto
qed

text \<open>The following is a stronger variant of @{thm [source] "ord_spmf_eq_pmf_None_eq"}\<close>

lemma eq_iff_ord_spmf:
  assumes "weight_spmf p \<ge> weight_spmf q"
  assumes "ord_spmf (=) p q"
  shows "p = q"
proof -
  have "\<And>x. spmf p x \<le> spmf q x"
    using ord_spmf_eq_leD[OF assms(2)] by simp
  moreover have "pmf p None \<le> pmf q None"
    using assms(1) unfolding pmf_None_eq_weight_spmf by auto
  ultimately have "pmf p x \<le> pmf q x" for x by (cases x) auto
  thus ?thesis using pmf_eq_iff_le by auto
qed

lemma wf_empty: "wf_random (\<lambda>_. None)"
  unfolding wf_random_def by auto

typedef 'a random_alg = "{(r :: 'a random_alg_int). wf_random r}"
  using wf_empty by (intro exI[where x="\<lambda>_. None"]) auto

setup_lifting type_definition_random_alg

lift_definition return_ra :: "'a \<Rightarrow> 'a random_alg" is return_rai
  by (rule wf_return)

lift_definition coin_ra :: "bool random_alg" is coin_rai
  by (rule wf_coin)

lift_definition bind_ra :: "'a random_alg \<Rightarrow> ('a \<Rightarrow> 'b random_alg) \<Rightarrow> 'b random_alg" is bind_rai
  by (rule wf_bind)

adhoc_overloading Monad_Syntax.bind bind_ra

text \<open>Monad laws:\<close>

lemma return_bind_ra:
  "bind_ra (return_ra x) g = g x"
  by (rule return_bind_rai[transferred])

lemma bind_ra_assoc:
  "bind_ra (bind_ra f g) h = bind_ra f (\<lambda>x. bind_ra (g x) h)"
  by (rule bind_rai_assoc[transferred])

lemma bind_return_ra:
  "bind_ra m return_ra = m"
  by (rule bind_return_rai[transferred])

lift_definition lub_ra :: "'a random_alg set \<Rightarrow> 'a random_alg" is
  "(\<lambda>F. if Complete_Partial_Order.chain ord_rai F then lub_rai F else (\<lambda>x. None))"
  using wf_lub wf_empty by auto

lift_definition ord_ra :: "'a random_alg \<Rightarrow> 'a random_alg \<Rightarrow> bool" is "ord_rai" .

lift_definition run_ra :: "'a random_alg \<Rightarrow> coin_stream \<Rightarrow> 'a option" is
  "(\<lambda>f s. map_option fst (f s))" .

context
begin

interpretation pmf_as_measure .

lemma distr_rai_is_pmf:
  assumes "wf_random f"
  shows
    "prob_space (distr_rai f)" (is "?A")
    "sets (distr_rai f) = UNIV" (is "?B")
    "AE x in distr_rai f. measure (distr_rai f) {x} \<noteq> 0" (is "?C")
proof -
  show "prob_space (distr_rai f)"
    using prob_space_distr_rai[OF assms] by simp
  then interpret p: prob_space "distr_rai f"
    by auto
  show ?B
    unfolding distr_rai_def by simp

  have "AE bs in \<B>. map_option fst (f bs) \<in> Some ` range_rm f \<union> {None}"
    unfolding range_rm_def
    by (intro AE_I2) (auto simp:image_iff split:option.split)
  hence "AE x in distr_rai f. x \<in> Some ` range_rm f \<union> {None}"
    unfolding distr_rai_def using distr_rai_measurable[OF assms]
    by (subst AE_distr_iff) auto
  moreover have "countable (Some ` range_rm f \<union> {None})"
    using countable_range[OF assms] by simp
  moreover have "p.events = UNIV"
    unfolding distr_rai_def by simp
  ultimately show ?C
    by (intro iffD2[OF p.AE_support_countable] exI[where x= "Some ` range_rm f \<union> {None}"]) auto
qed

lift_definition spmf_of_ra :: "'a random_alg \<Rightarrow> 'a spmf" is "distr_rai"
  using distr_rai_is_pmf by metis

lemma used_bits_distr_is_pmf:
  assumes "wf_random f"
  shows
    "prob_space (used_bits_distr f)" (is "?A")
    "sets (used_bits_distr f) = UNIV" (is "?B")
    "AE x in used_bits_distr f. measure (used_bits_distr f) {x} \<noteq> 0" (is "?C")
proof -
  show "prob_space (used_bits_distr f)"
    unfolding used_bits_distr_def
    by (intro coin_space.prob_space_distr consumed_bits_measurable)
  then interpret p: prob_space "used_bits_distr f"
    by auto
  show ?B
    unfolding used_bits_distr_def by simp
  have "p.events = UNIV"
    unfolding used_bits_distr_def by simp
  thus ?C
    by (intro iffD2[OF p.AE_support_countable] exI[where x= "UNIV"]) auto
qed

lift_definition coin_usage_of_ra_aux :: "'a random_alg \<Rightarrow> nat spmf" is "used_bits_distr"
  using used_bits_distr_is_pmf by auto

definition coin_usage_of_ra
  where "coin_usage_of_ra p = map_pmf (case_option \<infinity> enat) (coin_usage_of_ra_aux p)"

end

lemma wf_rep_rand_alg:
  "wf_random (Rep_random_alg f)"
  using Rep_random_alg by auto

lemma set_pmf_spmf_of_ra:
  "set_pmf (spmf_of_ra f) \<subseteq> Some ` range_rm (Rep_random_alg f) \<union> {None}"
proof
  let ?f = "Rep_random_alg f"

  fix x assume "x \<in> set_pmf (spmf_of_ra f)"
  hence "pmf (spmf_of_ra f) x > 0"
    using pmf_positive by metis
  hence "measure (distr_rai ?f) {x} > 0"
    by (subst spmf_of_ra.rep_eq[symmetric]) (simp add: pmf.rep_eq)
  hence "0 < measure \<B> {\<omega>. map_option fst (?f \<omega>) = x}"
    using distr_rai_measurable[OF wf_rep_rand_alg] unfolding distr_rai_def
    by (subst (asm) measure_distr) (simp_all add:vimage_def space_coin_space)
  moreover have "{\<omega>. map_option fst (?f \<omega>) = x} = {}" if "x \<notin> range (map_option fst \<circ> ?f)"
    using that by (auto simp:set_eq_iff image_iff)
  hence "measure \<B> {\<omega>. map_option fst (?f \<omega>) = x} = 0" if "x \<notin> range (map_option fst \<circ> ?f)"
    using that by simp
  ultimately have "x \<in> range (map_option fst \<circ> ?f)"
    by auto
  thus "x \<in> Some ` range_rm (Rep_random_alg f) \<union> {None}"
    unfolding range_rm_def by (cases x) auto
qed

lemma spmf_of_ra_return: "spmf_of_ra (return_ra x) = return_spmf x"
proof -
  have "measure_pmf (spmf_of_ra (return_ra x)) = measure_pmf (return_spmf x)"
    unfolding  spmf_of_ra.rep_eq distr_rai_return'[symmetric]
    by (simp add: return_ra.rep_eq)
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_coin: "spmf_of_ra coin_ra = coin_spmf"
proof -
  have "measure_pmf (spmf_of_ra coin_ra) = measure_pmf coin_spmf"
    unfolding  spmf_of_ra.rep_eq distr_rai_coin[symmetric]
    by (simp add: coin_ra.rep_eq)
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_bind:
  "spmf_of_ra (bind_ra f g) = bind_spmf (spmf_of_ra f) (\<lambda>x. spmf_of_ra (g x))" (is "?L = ?R")
proof -
  let ?f = "Rep_random_alg f"
  let ?g = "\<lambda>x. Rep_random_alg (g x)"

  have 0: "x \<in> Some ` range_rm ?f \<or> x = None" if "x \<in> set_pmf (spmf_of_ra f)" for x
    using that set_pmf_spmf_of_ra by auto

  have "measure_pmf ?L = distr_rai (?f \<bind> ?g)"
    unfolding spmf_of_ra.rep_eq bind_ra.rep_eq by (simp add:comp_def)
  also have "... = distr_rai ?f \<bind>
    (\<lambda>x. if x \<in> Some ` range_rm ?f then distr_rai (?g (the x)) else return \<D> None)"
    by (intro distr_rai_bind wf_rep_rand_alg)
  also have "... = measure_pmf (spmf_of_ra f) \<bind>
    (\<lambda>x. measure_pmf (if x \<in> Some ` range_rm ?f then spmf_of_ra (g (the x)) else return_pmf None))"
    by (intro arg_cong2[where f="bind"] ext) (auto simp:spmf_of_ra.rep_eq return_discrete)
  also have "... = measure_pmf (spmf_of_ra f \<bind>
    (\<lambda>x. if x \<in> Some ` range_rm ?f then spmf_of_ra (g (the x)) else return_pmf None))"
    unfolding bind_pmf.rep_eq by (simp add:comp_def id_def)
  also have "... = measure_pmf ?R"
    using 0 unfolding bind_spmf_def
    by (intro arg_cong[where f="measure_pmf"] bind_pmf_cong refl) (auto split:option.split)
  finally have "measure_pmf ?L = measure_pmf ?R" by simp
  thus ?thesis
    using measure_pmf_inject by blast
qed

lemma spmf_of_ra_mono:
  assumes "ord_ra f g"
  shows "ord_spmf (=) (spmf_of_ra f) (spmf_of_ra g)"
proof -
  have "ord_rai (Rep_random_alg f) (Rep_random_alg g)"
    using assms unfolding ord_ra.rep_eq by simp
  hence "ennreal (spmf (spmf_of_ra f) x) \<le> ennreal (spmf (spmf_of_ra g) x)" for x
    unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq
    by (intro distr_rai_ord_rai_mono wf_rep_rand_alg) auto
  hence "spmf (spmf_of_ra f) x \<le> spmf (spmf_of_ra g) x" for x
    by simp
  thus ?thesis
    by (intro ord_pmf_increaseI) auto
qed

lemma spmf_of_ra_lub_ra_empty:
  "spmf_of_ra (lub_ra {}) = return_pmf None" (is "?L = ?R")
proof -
  have "measure_pmf ?L = distr_rai (lub_rai {})"
    unfolding spmf_of_ra.rep_eq lub_ra.rep_eq Complete_Partial_Order.chain_def by auto
  also have "... = distr_rai (\<lambda>_. None)"
    unfolding lub_rai_def fun_lub_def flat_lub_def by auto
  also have "... = measure_pmf ?R"
    unfolding distr_rai_None by simp
  finally have "measure_pmf ?L = measure_pmf ?R"
    by simp
  thus ?thesis
    using measure_pmf_inject by auto
qed

lemma spmf_of_ra_lub_ra:
  fixes A :: "'a random_alg set"
  assumes "Complete_Partial_Order.chain ord_ra A"
  shows "spmf_of_ra (lub_ra A) = lub_spmf (spmf_of_ra ` A)" (is "?L = ?R")
proof (cases "A \<noteq> {}")
  case True
  have 0:"Complete_Partial_Order.chain ord_rai (Rep_random_alg ` A)"
    using assms unfolding ord_ra.rep_eq Complete_Partial_Order.chain_def by auto
  have 1:"Complete_Partial_Order.chain (ord_spmf (=)) (spmf_of_ra ` A)"
    using spmf_of_ra_mono by (intro chain_imageI[OF assms]) auto

  show ?thesis
  proof (rule spmf_eqI)
    fix x :: "'a"
    have "ennreal (spmf ?L x) = emeasure (distr_rai (lub_rai (Rep_random_alg ` A))) {Some x}"
      using 0 unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq lub_ra.rep_eq by simp
    also have "... = (SUP f\<in>Rep_random_alg ` A. emeasure (distr_rai f) {Some x})"
      using True wf_rep_rand_alg by (intro distr_rai_lub 0) auto
    also have "... = (SUP p\<in>A. ennreal (spmf (spmf_of_ra p) x))"
      unfolding emeasure_pmf_single[symmetric] spmf_of_ra.rep_eq by (simp add:image_image)
    also have "... = (SUP p\<in>spmf_of_ra ` A. ennreal (spmf p x))"
      by (simp add:image_image)
    also have "... = ennreal (spmf ?R x)"
      using True by (intro ennreal_spmf_lub_spmf[symmetric] 1) auto
    finally have "ennreal (spmf ?L x) = ennreal (spmf ?R x)"
      by simp
    thus "spmf ?L x = spmf ?R x"
      by simp
  qed
next
  case False
  thus ?thesis using spmf_of_ra_lub_ra_empty by simp
qed

lemma rep_lub_ra:
  assumes "Complete_Partial_Order.chain ord_ra F"
  shows "Rep_random_alg (lub_ra F) = lub_rai (Rep_random_alg ` F)"
proof -
  have "Complete_Partial_Order.chain ord_rai (Rep_random_alg ` F)"
    using assms unfolding ord_ra.rep_eq Complete_Partial_Order.chain_def by auto
  thus ?thesis
    unfolding lub_ra.rep_eq by simp
qed

lemma partial_function_image_improved:
  fixes ord
  assumes "\<And>A. Complete_Partial_Order.chain ord (f ` A) \<Longrightarrow> l1 (f ` A) = f (l2 A)"
  assumes "partial_function_definitions ord l1"
  assumes "inj f"
  shows "partial_function_definitions (img_ord f ord) l2"
proof -
  interpret pd: partial_function_definitions ord l1
    using assms(2) by auto
  have "img_ord f ord x x" for x
    unfolding img_ord_def using pd.leq_refl by simp
  moreover have "img_ord f ord x z" if "img_ord f ord x y" "img_ord f ord y z"  for x y z
    using that pd.leq_trans unfolding img_ord_def by blast
  moreover have "x = y" if "img_ord f ord x y" "img_ord f ord y x"  for x y
  proof -
    have "f x = f y"
      using that pd.leq_antisym unfolding img_ord_def by blast
    thus ?thesis
      using inj_onD[OF assms(3)] by simp
  qed
  moreover have "img_ord f ord x (l2 A)"
    if "x \<in> A" "Complete_Partial_Order.chain (img_ord f ord) A" for x A
  proof -
    have 0:"Complete_Partial_Order.chain ord (f ` A)"
      using that(2) unfolding chain_def img_ord_def by auto
    have "ord (f x) (l1 (f ` A))"
      using that by (intro pd.lub_upper[OF 0]) auto
    thus ?thesis
      unfolding img_ord_def assms(1)[OF 0] by auto
  qed
  moreover have "img_ord f ord (l2 A) z"
    if "Complete_Partial_Order.chain (img_ord f ord) A" "(\<forall>x. x \<in> A \<longrightarrow> img_ord f ord x z)"
    for z A
  proof -
    have 0:"Complete_Partial_Order.chain ord (f ` A)"
      using that(1) unfolding chain_def img_ord_def by auto
    have "ord (l1 (f ` A)) (f z)"
      using that(2) by (intro pd.lub_least[OF 0]) (auto simp:img_ord_def)
    thus ?thesis
      unfolding img_ord_def assms(1)[OF 0] by auto
  qed
  ultimately show ?thesis
    unfolding partial_function_definitions_def by blast
qed

lemma random_alg_pfd: "partial_function_definitions ord_ra lub_ra"
proof -
  have 0: "inj Rep_random_alg"
    using Rep_random_alg_inject unfolding inj_on_def by auto

  have 1:"partial_function_definitions ord_rai lub_rai"
    using random_alg_int_pd_fact by simp

  have 2:"ord_ra = img_ord Rep_random_alg ord_rai"
    unfolding ord_ra.rep_eq img_ord_def by auto

  show ?thesis
    unfolding 2 by (intro partial_function_image_improved[OF _ 1 0]) (auto simp: lub_ra.rep_eq)
qed

interpretation random_alg_pf: partial_function_definitions "ord_ra" "lub_ra"
  using random_alg_pfd by auto

abbreviation "mono_ra \<equiv> monotone (fun_ord ord_ra) ord_ra"

lemma bind_mono_aux_ra:
  assumes "ord_ra f1 f2" "\<And>y. ord_ra (g1 y) (g2 y)"
  shows "ord_ra (bind_ra f1 g1) (bind_ra f2 g2)"
  using assms unfolding ord_ra.rep_eq bind_ra.rep_eq
  by (intro bind_rai_mono) auto

lemma bind_mono_ra [partial_function_mono]:
  assumes "mono_ra B" and "\<And>y. mono_ra (C y)"
  shows "mono_ra (\<lambda>f. bind_ra (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_aux_ra) (auto simp:monotone_def)

definition map_ra :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a random_alg \<Rightarrow> 'b random_alg"
  where "map_ra f p = p \<bind> (\<lambda>x. return_ra (f x))"

lemma spmf_of_ra_map: "spmf_of_ra (map_ra f p) = map_spmf f (spmf_of_ra p)"
  unfolding map_ra_def map_spmf_conv_bind_spmf spmf_of_ra_bind spmf_of_ra_return by simp

lemmas spmf_of_ra_simps =
  spmf_of_ra_return spmf_of_ra_bind spmf_of_ra_coin spmf_of_ra_map

lemma map_mono_ra [partial_function_mono]:
  assumes "mono_ra B"
  shows "mono_ra (\<lambda>f. map_ra g (B f))"
  using assms unfolding map_ra_def by (intro bind_mono_ra) auto

definition rel_spmf_of_ra :: "'a spmf \<Rightarrow> 'a random_alg \<Rightarrow> bool" where
  "rel_spmf_of_ra q p \<longleftrightarrow> q = spmf_of_ra p"

lemma admissible_rel_spmf_of_ra:
  "ccpo.admissible (prod_lub lub_spmf lub_ra) (rel_prod (ord_spmf (=)) ord_ra) (case_prod rel_spmf_of_ra)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_spmf_of_ra p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_spmf_of_ra p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain (ord_ra) (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto

  have "lub_spmf (fst ` Y) = lub_spmf (spmf_of_ra ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_spmf] image_cong) (auto simp: rel_spmf_of_ra_def)
  also have "\<dots> = spmf_of_ra (lub_ra (snd ` Y))"
    by (intro spmf_of_ra_lub_ra[symmetric] chain2)
  finally have "rel_spmf_of_ra (lub_spmf (fst ` Y)) (lub_ra (snd ` Y))"
    unfolding rel_spmf_of_ra_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_spmf_of_ra_cont [cont_intro]:
  fixes ord
  shows "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f; mcont lub ord lub_ra ord_ra g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_spmf_of_ra (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_spmf_of_ra, where f="\<lambda>x. (f x, g x)", simplified])
     (rule mcont_Pair)

lemma mcont2mcont_spmf_of_ra[THEN spmf.mcont2mcont, cont_intro]:
  shows mcont_spmf_of_sampler: "mcont lub_ra ord_ra lub_spmf (ord_spmf (=)) spmf_of_ra"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: spmf_of_ra_mono spmf_of_ra_lub_ra)

context
  includes lifting_syntax
begin

lemma fixp_ra_parametric[transfer_rule]:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_ra (\<lambda>f. G f x)"
  and param: "((A ===> rel_spmf_of_ra) ===> A ===> rel_spmf_of_ra) F G"
  shows "(A ===> rel_spmf_of_ra) (spmf.fixp_fun F) (random_alg_pf.fixp_fun G)"
  using f g
proof(rule parallel_fixp_induct_1_1[OF
      partial_function_definitions_spmf random_alg_pfd _ _ reflexive reflexive,
        where P="(A ===> rel_spmf_of_ra)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub lub_ra))
        (rel_prod (fun_ord (ord_spmf (=))) (fun_ord ord_ra))
        (\<lambda>x. (A ===> rel_spmf_of_ra) (fst x) (snd x))"
    unfolding rel_fun_def
    by(rule admissible_all admissible_imp cont_intro)+
  show "(A ===> rel_spmf_of_ra) (\<lambda>_. lub_spmf {}) (\<lambda>_. lub_ra {})"
    by (auto simp: rel_fun_def rel_spmf_of_ra_def spmf_of_ra_lub_ra_empty)
  show "(A ===> rel_spmf_of_ra) (F f) (G g)" if "(A ===> rel_spmf_of_ra) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma return_ra_tranfer[transfer_rule]: "((=) ===> rel_spmf_of_ra) return_spmf return_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_return by simp

lemma bind_ra_tranfer[transfer_rule]:
  "(rel_spmf_of_ra ===> ((=) ===> rel_spmf_of_ra) ===> rel_spmf_of_ra) bind_spmf bind_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_bind by simp presburger

lemma coin_ra_tranfer[transfer_rule]:
  "rel_spmf_of_ra coin_spmf coin_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_coin by simp

lemma map_ra_tranfer[transfer_rule]:
  "((=) ===> rel_spmf_of_ra ===> rel_spmf_of_ra) map_spmf map_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def spmf_of_ra_map by simp

end

declare [[function_internals]]

declaration \<open>Partial_Function.init "random_alg" \<^term>\<open>random_alg_pf.fixp_fun\<close>
  \<^term>\<open>random_alg_pf.mono_body\<close>
  @{thm random_alg_pf.fixp_rule_uc} @{thm random_alg_pf.fixp_induct_uc}
  NONE\<close>

subsection \<open>Almost surely terminating randomized algorithms\<close>

definition terminates_almost_surely :: "'a random_alg \<Rightarrow> bool"
  where "terminates_almost_surely f \<longleftrightarrow> lossless_spmf (spmf_of_ra f)"

definition pmf_of_ra :: "'a random_alg \<Rightarrow> 'a pmf" where
  "pmf_of_ra p = map_pmf the (spmf_of_ra p)"

lemma pmf_of_spmf: "map_pmf the (spmf_of_pmf x) = x"
  by (simp add:map_pmf_comp spmf_of_pmf_def)

definition coin_pmf :: "bool pmf" where "coin_pmf = pmf_of_set UNIV"

lemma pmf_of_ra_coin: "pmf_of_ra (coin_ra) = coin_pmf" (is "?L = ?R")
proof -
  have 0:"spmf_of_ra (coin_ra) = spmf_of_pmf (pmf_of_set UNIV)"
    unfolding spmf_of_ra_coin spmf_of_set_def by simp
  thus ?thesis
    unfolding 0 pmf_of_ra_def pmf_of_spmf coin_pmf_def by simp
qed

lemma pmf_of_ra_return: "pmf_of_ra (return_ra x) = return_pmf x"
  unfolding pmf_of_ra_def spmf_of_ra_return by simp

lemma pmf_of_ra_bind:
  assumes "terminates_almost_surely f"
  shows "pmf_of_ra (f \<bind> g) = pmf_of_ra f \<bind> (\<lambda>x. pmf_of_ra (g x))" (is "?L = ?R")
proof -
  have 0:"x \<noteq> None" if "x \<in> set_pmf (spmf_of_ra f)" for x
    using assms that unfolding terminates_almost_surely_def
    by (meson lossless_iff_set_pmf_None)

  have "?L = spmf_of_ra f \<bind> (\<lambda>x. map_pmf the (case_option (return_pmf None) (spmf_of_ra \<circ> g) x))"
    unfolding pmf_of_ra_def spmf_of_ra_bind bind_spmf_def map_bind_pmf comp_def by simp
  also have "... = spmf_of_ra f \<bind>
    (\<lambda>x. (case x of None \<Rightarrow> return_pmf (the None) | Some x \<Rightarrow> pmf_of_ra (g x)))"
    unfolding map_pmf_def comp_def  pmf_of_ra_def map_pmf_def
    by (intro arg_cong2[where f="bind_pmf"] refl ext) (simp add:bind_return_pmf split:option.split)
  also have "... = spmf_of_ra f \<bind> (\<lambda>x. pmf_of_ra (g (the x)))"
    using 0 by (intro bind_pmf_cong refl) (auto split:option.split)
  also have "... = ?R"
    unfolding pmf_of_ra_def map_pmf_def by (simp add:bind_assoc_pmf bind_return_pmf)
  finally show ?thesis
    by simp
qed

lemma pmf_of_ra_map:
  assumes "terminates_almost_surely m"
  shows "pmf_of_ra (map_ra f m) = map_pmf f (pmf_of_ra m)"
  unfolding map_ra_def pmf_of_ra_bind[OF assms] pmf_of_ra_return map_pmf_def by simp

lemma terminates_almost_surely_return:
  "terminates_almost_surely (return_ra x)"
  unfolding terminates_almost_surely_def spmf_of_ra_return by simp

lemma terminates_almost_surely_coin:
  "terminates_almost_surely coin_ra"
  unfolding terminates_almost_surely_def spmf_of_ra_coin by simp

lemma terminates_almost_surely_bind:
  assumes "terminates_almost_surely f"
  assumes "\<And>x. x \<in> set_pmf (pmf_of_ra f) \<Longrightarrow> terminates_almost_surely (g x)"
  shows "terminates_almost_surely (f \<bind> g)"
proof -
  have 0: "None \<notin> set_pmf (spmf_of_ra f)"
    using assms(1) lossless_iff_set_pmf_None unfolding terminates_almost_surely_def
    by blast
  hence "Some x \<in> set_pmf (spmf_of_ra f) \<longleftrightarrow> x \<in> the ` set_pmf (spmf_of_ra f)" for x
    by (metis image_iff option.collapse option.sel)
  hence "set_spmf (spmf_of_ra f) = set_pmf (pmf_of_ra f)"
    unfolding pmf_of_ra_def set_map_pmf  by (simp add:set_eq_iff set_spmf_def)

  thus ?thesis
    using assms(1,2) unfolding terminates_almost_surely_def spmf_of_ra_bind lossless_bind_spmf
    by auto
qed

lemma terminates_almost_surely_map:
  assumes "terminates_almost_surely p"
  shows "terminates_almost_surely (map_ra f p)"
  unfolding map_ra_def
  by (intro assms terminates_almost_surely_bind terminates_almost_surely_return)

lemmas pmf_of_ra_simps =
  pmf_of_ra_return pmf_of_ra_bind pmf_of_ra_coin pmf_of_ra_map

lemmas terminates_almost_surely_intros =
  terminates_almost_surely_return
  terminates_almost_surely_bind
  terminates_almost_surely_coin
  terminates_almost_surely_map

end