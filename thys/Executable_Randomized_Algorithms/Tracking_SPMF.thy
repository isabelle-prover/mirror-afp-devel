section \<open>Tracking SPMFs\label{sec:tracking_spmfs}\<close>

text \<open>This section introduces tracking SPMFs --- this is a resource monad on top of SPMFs, we also
introduce the Scott-continous monad morphism @{term "tspmf_of_ra"}, with which it is possible to
reason about the joint-distribution of a randomized algorithm's result and used coin-flips.

An example application of the results in this theory can be found in Section~\ref{sec:dice_roll}.\<close>

theory Tracking_SPMF
  imports Tracking_Randomized_Algorithm
begin

type_synonym 'a tspmf = "('a \<times> nat) spmf"

definition return_tspmf :: "'a \<Rightarrow> 'a tspmf" where
  "return_tspmf x = return_spmf (x,0)"

definition coin_tspmf :: "bool tspmf" where
  "coin_tspmf = pair_spmf coin_spmf (return_spmf 1)"

definition bind_tspmf :: "'a tspmf \<Rightarrow> ('a \<Rightarrow> 'b tspmf) \<Rightarrow> 'b tspmf" where
  "bind_tspmf f g = bind_spmf f (\<lambda>(r,c). map_spmf (apsnd ((+) c)) (g r))"

adhoc_overloading Monad_Syntax.bind bind_tspmf

text \<open>Monad laws:\<close>

lemma return_bind_tspmf:
  "bind_tspmf (return_tspmf x) g = g x"
  unfolding bind_tspmf_def return_tspmf_def map_spmf_conv_bind_spmf
  by (simp add:apsnd_def map_prod_def)

lemma bind_tspmf_assoc:
  "bind_tspmf (bind_tspmf f g) h = bind_tspmf f (\<lambda>x. bind_tspmf (g x) h)"
  unfolding bind_tspmf_def
  by (simp add: case_prod_beta' algebra_simps map_spmf_conv_bind_spmf apsnd_def map_prod_def)

lemma bind_return_tspmf:
  "bind_tspmf m return_tspmf = m"
  unfolding bind_tspmf_def return_tspmf_def map_spmf_conv_bind_spmf apsnd_def
  by (simp add:case_prod_beta')

lemma bind_mono_tspmf_aux:
  assumes "ord_spmf (=) f1 f2" "\<And>y. ord_spmf (=) (g1 y) (g2 y)"
  shows "ord_spmf (=) (bind_tspmf f1 g1) (bind_tspmf f2 g2)"
  using assms unfolding bind_tspmf_def map_spmf_conv_bind_spmf
  by (auto intro!: bind_spmf_mono' simp add:case_prod_beta')

lemma bind_mono_tspmf [partial_function_mono]:
  assumes "mono_spmf B" and "\<And>y. mono_spmf (C y)"
  shows "mono_spmf (\<lambda>f. bind_tspmf (B f) (\<lambda>y. C y f))"
  using assms by (intro monotoneI bind_mono_tspmf_aux) (auto simp:monotone_def)

definition ord_tspmf :: "'a tspmf \<Rightarrow> 'a tspmf \<Rightarrow> bool" where
  "ord_tspmf = ord_spmf (\<lambda>x y. fst x = fst y \<and> snd x \<ge> snd y)"

bundle ord_tspmf_notation
begin
  notation ord_tspmf  ("(_/ \<le>\<^sub>R _)"  [51, 51] 50)
end

bundle no_ord_tspmf_notation
begin
  no_notation ord_tspmf  ("(_/ \<le>\<^sub>R _)"  [51, 51] 50)
end

unbundle ord_tspmf_notation

definition coin_usage_of_tspmf :: "'a tspmf \<Rightarrow> enat pmf"
  where "coin_usage_of_tspmf = map_pmf (\<lambda>x. case x of None \<Rightarrow> \<infinity> | Some y \<Rightarrow> enat (snd y))"

definition expected_coin_usage_of_tspmf :: "'a tspmf \<Rightarrow> ennreal"
  where
    "expected_coin_usage_of_tspmf p = (\<integral>\<^sup>+x. x \<partial>(map_pmf ennreal_of_enat (coin_usage_of_tspmf p)))"

definition expected_coin_usage_of_ra where
  "expected_coin_usage_of_ra p = \<integral>\<^sup>+x. x \<partial>(map_pmf ennreal_of_enat (coin_usage_of_ra p))"

definition result :: "'a tspmf \<Rightarrow> 'a spmf"
  where "result = map_spmf fst"

lemma coin_usage_of_tspmf_alt_def:
  "coin_usage_of_tspmf p = map_pmf (\<lambda>x. case x of None \<Rightarrow> \<infinity> | Some y \<Rightarrow> enat y) (map_spmf snd p)"
  unfolding coin_usage_of_tspmf_def map_pmf_comp map_option_case
  by (metis enat_def infinity_enat_def option.case_eq_if option.sel)

lemma coin_usage_of_tspmf_bind_return:
  "coin_usage_of_tspmf (bind_tspmf f (\<lambda>x. return_tspmf (g x))) = (coin_usage_of_tspmf f)"
  unfolding bind_tspmf_def return_tspmf_def coin_usage_of_tspmf_alt_def map_spmf_bind_spmf
  by (simp add:comp_def case_prod_beta map_spmf_conv_bind_spmf)

lemma coin_usage_of_tspmf_mono:
  assumes "ord_tspmf p q"
  shows "measure (coin_usage_of_tspmf p) {..k} \<le> measure (coin_usage_of_tspmf q) {..k}"
proof -
  define p' where "p' = map_spmf snd p"
  define q' where "q' = map_spmf snd q"
  have 0:"ord_spmf (\<ge>) p' q'"
    using assms(1) ord_spmf_mono unfolding p'_def q'_def ord_tspmf_def ord_spmf_map_spmf12 by fastforce

  have cp:"coin_usage_of_tspmf p = map_pmf (case_option \<infinity> enat) p'"
    unfolding coin_usage_of_tspmf_alt_def p'_def by simp
  have cq:"coin_usage_of_tspmf q = map_pmf (case_option \<infinity> enat) q'"
    unfolding coin_usage_of_tspmf_alt_def q'_def by simp

  have 0:"rel_pmf (\<ge>) (coin_usage_of_tspmf p) (coin_usage_of_tspmf q)"
    unfolding cp cq map_pmf_def by (intro rel_pmf_bindI[OF 0]) (auto split:option.split)
  show ?thesis
    unfolding atMost_def by (intro measure_Ici[OF 0] transp_on_ge) (simp add:reflp_def)
qed

lemma coin_usage_of_tspmf_mono_rev:
  assumes "ord_tspmf p q"
  shows "measure (coin_usage_of_tspmf q) {x. x > k} \<le> measure (coin_usage_of_tspmf p) {x. x > k}"
    (is "?L \<le> ?R")
proof -
  have 0:"UNIV - {x. x > k} = {..k}"
    by (auto simp add:set_diff_eq set_eq_iff)
  have "1 - ?R \<le> 1 - ?L"
    using coin_usage_of_tspmf_mono[OF assms]
    by (subst (1 2) measure_pmf.prob_compl[symmetric]) (auto simp:0)
  thus ?thesis
    by simp
qed

lemma expected_coin_usage_of_tspmf:
  "expected_coin_usage_of_tspmf p = (\<Sum>k. ennreal (measure (coin_usage_of_tspmf p) {x. x > enat k}))" (is "?L = ?R")
proof -
  have "?L = integral\<^sup>N (measure_pmf (coin_usage_of_tspmf p)) ennreal_of_enat"
    unfolding expected_coin_usage_of_tspmf_def by simp
  also have "... = (\<Sum>k. emeasure (measure_pmf (coin_usage_of_tspmf p)) {x. enat k < x})"
    by (subst nn_integral_enat_function) auto
  also have "... = ?R"
    by (subst measure_pmf.emeasure_eq_measure) simp
  finally show ?thesis
    by simp
qed

lemma ord_tspmf_min: "ord_tspmf (return_pmf None) p"
  unfolding ord_tspmf_def by (simp add: ord_spmf_reflI)

lemma ord_tspmf_refl: "ord_tspmf p p"
  unfolding ord_tspmf_def by (simp add: ord_spmf_reflI)

lemma ord_tspmf_trans[trans]:
  assumes "ord_tspmf p q" "ord_tspmf q r"
  shows "ord_tspmf p r"
proof -
  have 0:"transp (ord_tspmf)"
    unfolding ord_tspmf_def
    by (intro transp_rel_pmf transp_ord_option) (auto simp:transp_def)
  thus ?thesis
    using assms transpD[OF 0] by auto
qed

lemma ord_tspmf_map_spmf:
  assumes "\<And>x. x \<le> f x"
  shows "ord_tspmf (map_spmf (apsnd f) p) p"
  using assms unfolding ord_tspmf_def ord_spmf_map_spmf1
  by (intro ord_spmf_reflI) auto

lemma ord_tspmf_bind_pmf:
  assumes "\<And>x. ord_tspmf (f x) (g x)"
  shows "ord_tspmf (bind_pmf p f) (bind_pmf p g)"
  using assms unfolding ord_tspmf_def
  by (intro rel_pmf_bindI[where R="(=)"]) (auto simp add: pmf.rel_refl)

lemma ord_tspmf_bind_tspmf:
  assumes "\<And>x. ord_tspmf (f x) (g x)"
  shows "ord_tspmf (bind_tspmf p f) (bind_tspmf p g)"
  using assms unfolding bind_tspmf_def ord_tspmf_def
  by (intro ord_spmf_bind_reflI) (simp add:case_prod_beta ord_spmf_map_spmf12)

definition use_coins :: "nat \<Rightarrow> 'a tspmf \<Rightarrow> 'a tspmf"
  where "use_coins k = map_spmf (apsnd ((+) k))"

lemma use_coins_add:
  "use_coins k (use_coins s f) = use_coins (k+s) f"
  unfolding use_coins_def spmf.map_comp
  by (simp add:comp_def apsnd_def map_prod_def case_prod_beta' algebra_simps)

lemma coin_tspmf_split:
  fixes f :: "bool \<Rightarrow> 'b tspmf"
  shows "(coin_tspmf \<bind> f) = use_coins 1 (coin_spmf \<bind> f)"
  unfolding coin_tspmf_def use_coins_def map_spmf_conv_bind_spmf pair_spmf_alt_def bind_tspmf_def
  by (simp)

lemma ord_tspmf_use_coins:
  "ord_tspmf (use_coins k p) p"
  unfolding use_coins_def by (intro ord_tspmf_map_spmf) auto

lemma ord_tspmf_use_coins_2:
  assumes "ord_tspmf p q"
  shows  "ord_tspmf (use_coins k p) (use_coins k q)"
  using assms unfolding use_coins_def ord_tspmf_def ord_spmf_map_spmf12 by auto

lemma result_mono:
  assumes "ord_tspmf p q"
  shows "ord_spmf (=) (result p) (result q)"
  using assms ord_spmf_mono unfolding result_def ord_tspmf_def ord_spmf_map_spmf12 by force

lemma result_bind:
  "result (bind_tspmf f g) = result f \<bind> (\<lambda>x. result (g x))"
  unfolding bind_tspmf_def result_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

lemma result_return:
  "result (return_tspmf x) = return_spmf x"
  unfolding return_tspmf_def result_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

lemma result_coin:
  "result (coin_tspmf) = coin_spmf"
  unfolding coin_tspmf_def result_def pair_spmf_alt_def map_spmf_conv_bind_spmf by (simp add:case_prod_beta')

definition tspmf_of_ra :: "'a random_alg \<Rightarrow> 'a tspmf" where
  "tspmf_of_ra = spmf_of_ra \<circ> track_coin_use"

lemma tspmf_of_ra_coin: "tspmf_of_ra coin_ra = coin_tspmf"
  unfolding tspmf_of_ra_def comp_def track_coin_use_coin coin_tra_def coin_tspmf_def
    spmf_of_ra_bind spmf_of_ra_coin spmf_of_ra_return pair_spmf_alt_def
  by simp

lemma tspmf_of_ra_return: "tspmf_of_ra (return_ra x) = return_tspmf x"
  unfolding tspmf_of_ra_def comp_def track_coin_use_return return_tra_def return_tspmf_def
     spmf_of_ra_return by simp

lemma tspmf_of_ra_bind:
  "tspmf_of_ra (bind_ra m f) = bind_tspmf (tspmf_of_ra m) (\<lambda>x. tspmf_of_ra (f x))"
  unfolding tspmf_of_ra_def comp_def track_coin_use_bind bind_tra_def bind_tspmf_def
    map_spmf_conv_bind_spmf
  by (simp add:case_prod_beta' spmf_of_ra_bind spmf_of_ra_return apsnd_def map_prod_def)

lemmas tspmf_of_ra_simps = tspmf_of_ra_bind tspmf_of_ra_return tspmf_of_ra_coin

lemma tspmf_of_ra_mono:
  assumes "ord_ra f g"
  shows "ord_spmf (=) (tspmf_of_ra f) (tspmf_of_ra g)"
  unfolding tspmf_of_ra_def comp_def
  by (intro spmf_of_ra_mono track_coin_use_mono assms)

lemma tspmf_of_ra_lub:
  assumes "Complete_Partial_Order.chain ord_ra A"
  shows "tspmf_of_ra (lub_ra A) = lub_spmf (tspmf_of_ra ` A)" (is "?L = ?R")
proof -
  have 0:"Complete_Partial_Order.chain ord_ra (track_coin_use ` A)"
    by (intro chain_imageI[OF assms] track_coin_use_mono)

  have "?L = spmf_of_ra (lub_ra (track_coin_use ` A))"
    unfolding tspmf_of_ra_def comp_def
    by (intro arg_cong[where f="spmf_of_ra"] track_coin_use_lub assms)
  also have "... = lub_spmf (spmf_of_ra ` track_coin_use ` A)"
    by (intro spmf_of_ra_lub_ra 0)
  also have "... = ?R"
    unfolding image_image tspmf_of_ra_def by simp
  finally show "?thesis" by simp
qed

definition rel_tspmf_of_ra :: "'a tspmf \<Rightarrow> 'a random_alg \<Rightarrow> bool" where
  "rel_tspmf_of_ra q p \<longleftrightarrow> q = tspmf_of_ra p"

lemma admissible_rel_tspmf_of_ra:
  "ccpo.admissible (prod_lub lub_spmf lub_ra) (rel_prod (ord_spmf (=)) ord_ra) (case_prod rel_tspmf_of_ra)"
  (is "ccpo.admissible ?lub ?ord ?P")
proof (rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ?ord Y"
    and Y: "Y \<noteq> {}"
    and R: "\<forall>(p, q) \<in> Y. rel_tspmf_of_ra p q"
  from R have R: "\<And>p q. (p, q) \<in> Y \<Longrightarrow> rel_tspmf_of_ra p q" by auto
  have chain1: "Complete_Partial_Order.chain (ord_spmf (=)) (fst ` Y)"
    and chain2: "Complete_Partial_Order.chain ord_ra (snd ` Y)"
    using chain by(rule chain_imageI; clarsimp)+
  from Y have Y1: "fst ` Y \<noteq> {}" and Y2: "snd ` Y \<noteq> {}" by auto

  have "lub_spmf (fst ` Y) = lub_spmf (tspmf_of_ra ` snd ` Y)"
    unfolding image_image using R
    by (intro arg_cong[of _ _ lub_spmf] image_cong) (auto simp: rel_tspmf_of_ra_def)
  also have "\<dots> = tspmf_of_ra (lub_ra (snd ` Y))"
    by (intro tspmf_of_ra_lub[symmetric] chain2)
  finally have "rel_tspmf_of_ra (lub_spmf (fst ` Y)) (lub_ra (snd ` Y))"
    unfolding rel_tspmf_of_ra_def .
  then show "?P (?lub Y)"
    by (simp add: prod_lub_def)
qed

lemma admissible_rel_tspmf_of_ra_cont [cont_intro]:
  fixes ord
  shows "\<lbrakk> mcont lub ord lub_spmf (ord_spmf (=)) f; mcont lub ord lub_ra ord_ra g \<rbrakk>
  \<Longrightarrow> ccpo.admissible lub ord (\<lambda>x. rel_tspmf_of_ra (f x) (g x))"
  by (rule admissible_subst[OF admissible_rel_tspmf_of_ra, where f="\<lambda>x. (f x, g x)", simplified])
     (rule mcont_Pair)

lemma mcont_tspmf_of_ra:
  "mcont lub_ra ord_ra lub_spmf (ord_spmf (=)) tspmf_of_ra"
  unfolding mcont_def monotone_def cont_def
  by (auto simp: tspmf_of_ra_mono tspmf_of_ra_lub)

lemmas mcont2mcont_tspmf_of_ra = mcont_tspmf_of_ra[THEN spmf.mcont2mcont]

context includes lifting_syntax
begin

lemma fixp_rel_tspmf_of_ra_parametric[transfer_rule]:
  assumes f: "\<And>x. mono_spmf (\<lambda>f. F f x)"
  and g: "\<And>x. mono_ra (\<lambda>f. G f x)"
  and param: "((A ===> rel_tspmf_of_ra) ===> A ===> rel_tspmf_of_ra) F G"
  shows "(A ===> rel_tspmf_of_ra) (spmf.fixp_fun F) (random_alg_pf.fixp_fun G)"
  using f g
proof(rule parallel_fixp_induct_1_1[OF
      partial_function_definitions_spmf random_alg_pfd _ _ reflexive reflexive,
        where P="(A ===> rel_tspmf_of_ra)"])
  show "ccpo.admissible (prod_lub (fun_lub lub_spmf) (fun_lub lub_ra))
        (rel_prod (fun_ord (ord_spmf (=))) (fun_ord ord_ra))
        (\<lambda>x. (A ===> rel_tspmf_of_ra) (fst x) (snd x))"
    unfolding rel_fun_def
    by(rule admissible_all admissible_imp cont_intro)+
  have 0:"tspmf_of_ra (lub_ra {}) = return_pmf None"
    using tspmf_of_ra_lub[where A="{}"]
    by (simp add:Complete_Partial_Order.chain_def)
  show "(A ===> rel_tspmf_of_ra) (\<lambda>_. lub_spmf {}) (\<lambda>_. lub_ra {})"
    by (auto simp: rel_fun_def rel_tspmf_of_ra_def 0)
  show "(A ===> rel_tspmf_of_ra) (F f) (G g)" if "(A ===> rel_tspmf_of_ra) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma return_ra_tranfer[transfer_rule]: "((=) ===> rel_tspmf_of_ra) return_tspmf return_ra"
  unfolding rel_fun_def rel_tspmf_of_ra_def tspmf_of_ra_return by simp

lemma bind_ra_tranfer[transfer_rule]:
  "(rel_tspmf_of_ra ===> ((=) ===> rel_tspmf_of_ra) ===> rel_tspmf_of_ra) bind_tspmf bind_ra"
  unfolding rel_fun_def rel_tspmf_of_ra_def tspmf_of_ra_bind by simp presburger

lemma coin_ra_tranfer[transfer_rule]:
  "rel_tspmf_of_ra coin_tspmf coin_ra"
  unfolding rel_fun_def rel_tspmf_of_ra_def tspmf_of_ra_coin by simp

end

lemma spmf_of_tspmf:
  "result (tspmf_of_ra f) = spmf_of_ra f"
  unfolding tspmf_of_ra_def result_def
  by (simp add: untrack_coin_use spmf_of_ra_map[symmetric])

lemma coin_usage_of_tspmf_correct:
  "coin_usage_of_tspmf (tspmf_of_ra p) = coin_usage_of_ra p" (is "?L = ?R")
proof -
  let ?p = "Rep_random_alg p"

  have "measure_pmf (map_spmf snd (tspmf_of_ra p)) =
    distr (distr_rai (track_random_bits ?p)) \<D> (map_option snd)"
    unfolding tspmf_of_ra_def map_pmf_rep_eq spmf_of_ra.rep_eq comp_def track_coin_use.rep_eq
    by simp
  also have "... = distr \<B> \<D> (map_option snd \<circ> (map_option fst \<circ> track_random_bits ?p))"
    unfolding distr_rai_def
    by (intro distr_distr distr_rai_measurable wf_track_random_bits wf_rep_rand_alg) simp
  also have "... = distr \<B> \<D> (\<lambda>x. ?p x \<bind> (\<lambda>xa. consumed_bits ?p x))"
    unfolding track_random_bits_def by (simp add:comp_def map_option_bind case_prod_beta)
  also have "... = distr \<B> \<D> (\<lambda>x. consumed_bits ?p x)"
    by (intro arg_cong[where f="distr \<B> \<D>"] ext)
     (auto simp:consumed_bits_inf_iff[OF wf_rep_rand_alg] split:bind_split)
  also have "... = measure_pmf (coin_usage_of_ra_aux p)"
    unfolding coin_usage_of_ra_aux.rep_eq used_bits_distr_def by simp
  finally have "measure_pmf (map_spmf snd (tspmf_of_ra p)) = measure_pmf (coin_usage_of_ra_aux p)"
    by simp
  hence 0:"map_spmf snd (tspmf_of_ra p) = coin_usage_of_ra_aux p"
    using measure_pmf_inject by auto
  show ?thesis
    unfolding coin_usage_of_tspmf_def 0[symmetric] coin_usage_of_ra_def map_pmf_comp
    by (intro map_pmf_cong) (auto split:option.split)
qed

lemma expected_coin_usage_of_tspmf_correct:
  "expected_coin_usage_of_tspmf (tspmf_of_ra p) = expected_coin_usage_of_ra p"
  unfolding expected_coin_usage_of_tspmf_def coin_usage_of_tspmf_correct
    expected_coin_usage_of_ra_def by simp

end