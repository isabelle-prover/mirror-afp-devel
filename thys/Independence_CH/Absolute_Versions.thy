section\<open>From $M$ to $\calV$\<close>

theory Absolute_Versions
  imports
    CH
    ZF.Cardinal_AC
begin

hide_const (open) Order.pred

subsection\<open>Locales of a class \<^term>\<open>M\<close> hold in \<^term>\<open>\<V>\<close>\<close>

interpretation V: M_trivial \<V>
  using Union_ax_absolute upair_ax_absolute
  by unfold_locales auto

lemmas bad_simps = V.nonempty V.Forall_in_M_iff V.Inl_in_M_iff V.Inr_in_M_iff
  V.succ_in_M_iff V.singleton_in_M_iff V.Equal_in_M_iff V.Member_in_M_iff V.Nand_in_M_iff
  V.Cons_in_M_iff V.pair_in_M_iff V.upair_in_M_iff

lemmas bad_M_trivial_simps[simp del] = V.Forall_in_M_iff V.Equal_in_M_iff
  V.nonempty

lemmas bad_M_trivial_rules[rule del] =  V.pair_in_MI V.singleton_in_MI V.pair_in_MD V.nat_into_M
  V.depth_closed V.length_closed V.nat_case_closed V.separation_closed
  V.Un_closed V.strong_replacement_closed V.nonempty

interpretation V:M_basic \<V>
  using power_ax_absolute separation_absolute replacement_absolute
  by unfold_locales auto

interpretation V:M_eclose \<V>
  by unfold_locales (auto intro:separation_absolute replacement_absolute
      simp:iterates_replacement_def wfrec_replacement_def)

lemmas bad_M_basic_rules[simp del, rule del] =
  V.cartprod_closed V.finite_funspace_closed V.converse_closed
  V.list_case'_closed V.pred_closed

interpretation V:M_cardinal_arith \<V>
  by unfold_locales (auto intro:separation_absolute replacement_absolute
      simp add:iterates_replacement_def wfrec_replacement_def lam_replacement_def)

lemmas bad_M_cardinals_rules[simp del, rule del] =
  V.iterates_closed V.M_nat V.trancl_closed V.rvimage_closed

interpretation V:M_cardinal_arith_jump \<V>
  by unfold_locales (auto intro:separation_absolute replacement_absolute
      simp:wfrec_replacement_def)

lemma choice_ax_Universe: "choice_ax(\<V>)"
proof -
  {
    fix x
    obtain f where "f \<in> surj(|x|,x)"
      using cardinal_eqpoll unfolding eqpoll_def bij_def by fast
    moreover
    have "Ord(|x|)" by simp
    ultimately
    have "\<exists>a. Ord(a) \<and> (\<exists>f. f \<in> surj(a,x))"
      by fast
  }
  then
  show ?thesis  unfolding choice_ax_def rall_def rex_def
    by simp
qed

interpretation V:M_master \<V>
  using choice_ax_Universe
  by unfold_locales (auto intro:separation_absolute replacement_absolute
      simp:lam_replacement_def transrec_replacement_def wfrec_replacement_def
      is_wfrec_def M_is_recfun_def)

named_theorems V_simps

\<comment> \<open>To work systematically, ASCII versions of "\_absolute" theorems as
    those below are preferable.\<close>
lemma eqpoll_rel_absolute[V_simps]: "x \<approx>\<^bsup>\<V>\<^esup> y \<longleftrightarrow> x \<approx> y"
  unfolding eqpoll_def using V.def_eqpoll_rel by auto

lemma cardinal_rel_absolute[V_simps]: "|x|\<^bsup>\<V>\<^esup> = |x|"
  unfolding cardinal_def cardinal_rel_def by (simp add:V_simps)

lemma Card_rel_absolute[V_simps]:"Card\<^bsup>\<V>\<^esup>(a) \<longleftrightarrow> Card(a)"
  unfolding Card_rel_def Card_def by (simp only:V_simps)

lemma csucc_rel_absolute[V_simps]:"(a\<^sup>+)\<^bsup>\<V>\<^esup> = a\<^sup>+"
  unfolding csucc_rel_def csucc_def by (simp add:V_simps)

lemma function_space_rel_absolute[V_simps]:"x \<rightarrow>\<^bsup>\<V>\<^esup> y = x \<rightarrow> y"
  using V.function_space_rel_char by (simp add:V_simps)

lemma cexp_rel_absolute[V_simps]:"x\<^bsup>\<up>y,\<V>\<^esup> = x\<^bsup>\<up>y\<^esup>"
  unfolding cexp_rel_def cexp_def by (simp only:V_simps)

lemma HAleph_rel_absolute[V_simps]:"HAleph_rel(\<V>,a,b) = HAleph(a,b)"
  unfolding HAleph_rel_def HAleph_def by (auto simp add:V_simps)

lemma Aleph_rel_absolute[V_simps]: "Ord(x) \<Longrightarrow> \<aleph>\<^bsub>x\<^esub>\<^bsup>\<V>\<^esup> = \<aleph>\<^bsub>x\<^esub>"
proof -
  assume "Ord(x)"
  have "\<aleph>\<^bsub>x\<^esub>\<^bsup>\<V>\<^esup> = transrec(x, \<lambda>a b. HAleph_rel(\<V>,a,b))"
    unfolding Aleph_rel_def by simp
  also
  have "\<dots> = transrec(x, HAleph)"
    by (simp only:V_simps)
  also from \<open>Ord(x)\<close>
  have "\<dots> = \<aleph>\<^bsub>x\<^esub>"
    using Aleph'_eq_Aleph unfolding Aleph'_def by simp
  finally
  show ?thesis .
qed

text\<open>Example of absolute lemmas obtained from the relative versions.
    Note the \<^emph>\<open>only\<close> declarations\<close>
lemma Ord_cardinal_idem': "Ord(A) \<Longrightarrow> ||A|| = |A|"
  using V.Ord_cardinal_rel_idem by (simp only:V_simps)

lemma Aleph_succ': "Ord(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>succ(\<alpha>)\<^esub> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^sup>+"
  using V.Aleph_rel_succ by (simp only:V_simps)

text\<open>These two results are new, first obtained in relative form
    (not ported).\<close>
lemma csucc_cardinal:
  assumes "Ord(\<kappa>)" shows "|\<kappa>|\<^sup>+ = \<kappa>\<^sup>+"
  using assms V.csucc_rel_cardinal_rel by (simp only:V_simps)

lemma csucc_le_mono:
  assumes "\<kappa> \<le> \<nu>"  shows "\<kappa>\<^sup>+ \<le> \<nu>\<^sup>+"
  using assms V.csucc_rel_le_mono by (simp only:V_simps)

text\<open>Example of transferring results from a transitive model to \<^term>\<open>\<V>\<close>\<close>
lemma (in M_Perm) eqpoll_rel_transfer_absolute:
  assumes "M(A)" "M(B)" "A \<approx>\<^bsup>M\<^esup> B"
  shows "A \<approx> B"
proof -
  interpret M_N_Perm M \<V>
    by (unfold_locales, simp only:V_simps)
  from assms
  show ?thesis using eqpoll_rel_transfer
    by (simp only:V_simps)
qed

text\<open>The “relationalized” $\CH$ with respect to \<^term>\<open>\<V>\<close> corresponds
    to the real $\CH$.\<close>
lemma is_ContHyp_iff_CH: "is_ContHyp(\<V>) \<longleftrightarrow> ContHyp"
  using V.is_ContHyp_iff
  by (auto simp add:ContHyp_rel_def ContHyp_def V_simps)

end