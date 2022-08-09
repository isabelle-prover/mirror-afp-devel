section\<open>Model of the negation of the Continuum Hypothesis\<close>

theory Not_CH
  imports
    Cardinal_Preservation
begin

text\<open>We are taking advantage that the poset of finite functions is absolute,
and thus we work with the unrelativized \<^term>\<open>Fn\<close>. But it would have been more
appropriate to do the following using the relative \<^term>\<open>Fn_rel\<close>. As it turns
out, the present theory was developed prior to having \<^term>\<open>Fn\<close> relativized!

We also note that \<^term>\<open>Fn(\<omega>,\<kappa>\<times>\<omega>,2)\<close> is separative, i.e. each \<^term>\<open>X \<in> Fn(\<omega>,\<kappa>\<times>\<omega>,2)\<close>
has two incompatible extensions; therefore we may recover part of our previous theorem
@{thm [source] extensions_of_ctms_ZF}. But that result also included the possibility
of not having $\AC$ in the ground model, which would not be sensible in a context
where the cardinality of the continuum is under discussion. It is also the case that
@{thm [source] extensions_of_ctms_ZF} was historically our first formalized result
(with a different proof) that showed the forcing machinery had all of its elements
in place.\<close>

abbreviation
  Add_subs :: "i \<Rightarrow> i" where
  "Add_subs(\<kappa>) \<equiv> Fn(\<omega>,\<kappa>\<times>\<omega>,2)"

abbreviation
  Add_le :: "i \<Rightarrow> i" where
  "Add_le(\<kappa>) \<equiv> Fnle(\<omega>,\<kappa> \<times> \<omega>,2)"

lemma (in M_aleph) Aleph_rel2_closed[intro,simp]: "M(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
  using nat_into_Ord by simp

locale M_master = M_cohen + M_library +
  assumes
    UN_lepoll_assumptions:
    "M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> M(A') \<Longrightarrow> separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x\<in>if_range_F_else_F((`)(A), b, f, i)\<rangle>)"

subsection\<open>Non-absolute concepts between extensions\<close>

sublocale M_master \<subseteq> M_Pi_replacement
  by unfold_locales

locale M_master_sub = M_master + N:M_aleph N for N +
  assumes
    M_imp_N: "M(x) \<Longrightarrow> N(x)" and
    Ord_iff: "Ord(x) \<Longrightarrow> M(x) \<longleftrightarrow> N(x)"

sublocale M_master_sub \<subseteq> M_N_Perm
  using M_imp_N by unfold_locales

context M_master_sub
begin

lemma cardinal_rel_le_cardinal_rel: "M(X) \<Longrightarrow> |X|\<^bsup>N\<^esup> \<le> |X|\<^bsup>M\<^esup>"
  using M_imp_N N.lepoll_rel_cardinal_rel_le[OF lepoll_rel_transfer Card_rel_is_Ord]
    cardinal_rel_eqpoll_rel[THEN eqpoll_rel_sym, THEN eqpoll_rel_imp_lepoll_rel]
  by simp

lemma Aleph_rel_sub_closed: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> N(\<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup>)"
  using Ord_iff[THEN iffD1, OF Card_rel_Aleph_rel[THEN Card_rel_is_Ord]]
  by simp

lemma Card_rel_imp_Card_rel: "Card\<^bsup>N\<^esup>(\<kappa>) \<Longrightarrow> M(\<kappa>) \<Longrightarrow> Card\<^bsup>M\<^esup>(\<kappa>)"
  using N.Card_rel_is_Ord[of \<kappa>] M_imp_N Ord_cardinal_rel_le[of \<kappa>]
    cardinal_rel_le_cardinal_rel[of \<kappa>] le_anti_sym
  unfolding Card_rel_def by auto

lemma csucc_rel_le_csucc_rel:
  assumes "Ord(\<kappa>)" "M(\<kappa>)"
  shows "(\<kappa>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<kappa>\<^sup>+)\<^bsup>N\<^esup>"
proof -
  note assms
  moreover from this
  have "N(L) \<and> Card\<^bsup>N\<^esup>(L) \<and> \<kappa> < L \<Longrightarrow> M(L) \<and> Card\<^bsup>M\<^esup>(L) \<and> \<kappa> < L"
    (is "?P(L) \<Longrightarrow> ?Q(L)") for L
    using M_imp_N Ord_iff[THEN iffD2, of L] N.Card_rel_is_Ord lt_Ord
      Card_rel_imp_Card_rel by auto
  moreover from assms
  have "N((\<kappa>\<^sup>+)\<^bsup>N\<^esup>)" "Card\<^bsup>N\<^esup>((\<kappa>\<^sup>+)\<^bsup>N\<^esup>)" "\<kappa> < (\<kappa>\<^sup>+)\<^bsup>N\<^esup>"
    using N.lt_csucc_rel[of \<kappa>] N.Card_rel_csucc_rel[of \<kappa>] M_imp_N by simp_all
  ultimately
  show ?thesis
    using M_imp_N Least_antitone[of _ ?P ?Q] unfolding csucc_rel_def by blast
qed

lemma Aleph_rel_le_Aleph_rel: "Ord(\<alpha>) \<Longrightarrow> M(\<alpha>) \<Longrightarrow> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>\<alpha>\<^esub>\<^bsup>N\<^esup>"
proof (induct rule:trans_induct3)
  case 0
  then
  show ?case
    using Aleph_rel_zero N.Aleph_rel_zero by simp
next
  case (succ x)
  then
  have "\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>x\<^esub>\<^bsup>N\<^esup>" "Ord(x)" "M(x)" by simp_all
  moreover from this
  have "(\<aleph>\<^bsub>x\<^esub>\<^bsup>M\<^esup>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<aleph>\<^bsub>x\<^esub>\<^bsup>N\<^esup>\<^sup>+)\<^bsup>M\<^esup>"
    using M_imp_N Ord_iff[THEN iffD2, OF N.Card_rel_is_Ord]
    by (intro csucc_rel_le_mono) simp_all
  moreover from calculation
  have "(\<aleph>\<^bsub>x\<^esub>\<^bsup>N\<^esup>\<^sup>+)\<^bsup>M\<^esup> \<le> (\<aleph>\<^bsub>x\<^esub>\<^bsup>N\<^esup>\<^sup>+)\<^bsup>N\<^esup>"
    using M_imp_N N.Card_rel_is_Ord Ord_iff[THEN iffD2, OF N.Card_rel_is_Ord]
    by (intro csucc_rel_le_csucc_rel) auto
  ultimately
  show ?case
    using M_imp_N Aleph_rel_succ N.Aleph_rel_succ csucc_rel_le_csucc_rel
      le_trans by auto
next
  case (limit x)
  then
  show ?case
    using M_imp_N Aleph_rel_limit N.Aleph_rel_limit
    by simp (blast dest: transM intro!:le_implies_UN_le_UN)
qed

end \<comment> \<open>\<^locale>\<open>M_master_sub\<close>\<close>

lemmas (in M_ZF3_trans) sep_instances =
  separation_ifrangeF_body separation_ifrangeF_body2 separation_ifrangeF_body3
  separation_ifrangeF_body4 separation_ifrangeF_body5 separation_ifrangeF_body6
  separation_ifrangeF_body7 separation_cardinal_rel_lesspoll_rel
  separation_is_dcwit_body separation_cdltgamma separation_cdeqgamma

lemmas (in M_ZF3_trans) repl_instances = lam_replacement_inj_rel

sublocale M_ZFC3_ground_notCH_trans \<subseteq> M_master "##M"
  using replacement_trans_apply_image
  by unfold_locales (simp_all add:repl_instances sep_instances del:setclass_iff
      add: transrec_replacement_def wfrec_replacement_def)

sublocale M_ZFC3_trans \<subseteq> M_Pi_replacement "##M"
  by unfold_locales

subsection\<open>Cohen forcing is ccc\<close>

context M_ctm3_AC
begin

lemma ccc_Add_subs_Aleph_2: "ccc\<^bsup>M\<^esup>(Add_subs(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>),Add_le(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>))"
proof -
  interpret M_add_reals "##M" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>"
    by unfold_locales blast
  show ?thesis
    using ccc_rel_Fn_nat by fast
qed

end \<comment> \<open>\<^locale>\<open>M_ctm3_AC\<close>\<close>

sublocale G_generic4_AC \<subseteq> M_master_sub "##M" "##(M[G])"
  using M_subset_MG[OF one_in_G] generic Ord_MG_iff
  by unfold_locales auto

lemma (in M_trans) mem_F_bound4:
  fixes F A
  defines "F \<equiv> (`)"
  shows "x\<in>F(A,c) \<Longrightarrow> c \<in> (range(f) \<union> domain(A))"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def)

lemma (in M_trans) mem_F_bound5:
  fixes F A
  defines "F \<equiv> \<lambda>_ x. A`x "
  shows "x\<in>F(A,c) \<Longrightarrow> c \<in> (range(f) \<union> domain(A))"
  using apply_0 unfolding F_def
  by (cases "M(c)", auto simp:F_def drSR_Y_def dC_F_def)

sublocale M_ctm3_AC \<subseteq> M_replacement_lepoll "##M" "(`)"
  using UN_lepoll_assumptions lam_replacement_apply lam_replacement_inj_rel
    mem_F_bound4 apply_0 lam_replacement_minimum
  unfolding lepoll_assumptions_defs
proof (unfold_locales,
    rule_tac [3] lam_Least_assumption_general[where U=domain, OF _ mem_F_bound4], simp_all)
  fix A i x
  assume "A \<in> M" "x \<in> M" "x \<in> A ` i"
  then
  show "i \<in> M"
    using apply_0[of i A] transM[of _ "domain(A)", simplified]
    by force
qed

context G_generic4_AC begin

context
  includes G_generic1_lemmas
begin

lemma G_in_MG: "G \<in> M[G]"
  using G_in_Gen_Ext
  by blast

lemma ccc_preserves_Aleph_succ:
  assumes "ccc\<^bsup>M\<^esup>(P,leq)" "Ord(z)" "z \<in> M"
  shows "Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
proof (rule ccontr)
  assume "\<not> Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
  moreover
  note \<open>z \<in> M\<close> \<open>Ord(z)\<close>
  moreover from this
  have "Ord(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_is_Ord by fastforce
  ultimately
  obtain \<alpha> f where "\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "f \<in> surj\<^bsup>M[G]\<^esup>(\<alpha>, \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
    using ext.lt_surj_rel_empty_imp_Card_rel M_subset_MG[OF one_in_G]
    by force
  moreover from this and \<open>z\<in>M\<close> \<open>Ord(z)\<close>
  have "\<alpha> \<in> M" "f \<in> M[G]"
    using ext.trans_surj_rel_closed
    by (auto dest:transM ext.transM dest!:ltD)
  moreover
  note \<open>ccc\<^bsup>M\<^esup>(P,leq)\<close> \<open>z\<in>M\<close>
  ultimately
  obtain F where "F:\<alpha>\<rightarrow>Pow\<^bsup>M\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)" "\<forall>\<beta>\<in>\<alpha>. f`\<beta> \<in> F`\<beta>" "\<forall>\<beta>\<in>\<alpha>. |F`\<beta>|\<^bsup>M\<^esup> \<le> \<omega>"
    "F \<in> M"
    using ccc_fun_approximation_lemma[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" f]
      ext.mem_surj_abs[of f \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"] \<open>Ord(z)\<close>
      surj_is_fun[of f \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"] by auto
  then
  have "\<beta> \<in> \<alpha> \<Longrightarrow> |F`\<beta>|\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup>" for \<beta>
    using Aleph_rel_zero by simp
  have "w \<in> F ` x \<Longrightarrow> x \<in> M" for w x
  proof -
    fix w x
    assume "w \<in> F`x"
    then
    have "x \<in> domain(F)"
      using apply_0 by auto
    with \<open>F:\<alpha>\<rightarrow>Pow\<^bsup>M\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close> \<open>\<alpha> \<in> M\<close>
    show "x \<in> M" using domain_of_fun
      by (auto dest:transM)
  qed
  with \<open>\<alpha> \<in> M\<close> \<open>F:\<alpha>\<rightarrow>Pow\<^bsup>M\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close> \<open>F\<in>M\<close>
  interpret M_cardinal_UN_lepoll "##M" "\<lambda>\<beta>. F`\<beta>" \<alpha>
    using UN_lepoll_assumptions lepoll_assumptions
      lam_replacement_apply lam_replacement_inj_rel lam_replacement_minimum
  proof (unfold_locales, auto dest:transM simp del:if_range_F_else_F_def)
    fix f b
    assume "b\<in>M" "f\<in>M"
    with \<open>F\<in>M\<close>
    show "lam_replacement(##M, \<lambda>x. \<mu> i. x \<in> if_range_F_else_F((`)(F), b, f, i))"
      using UN_lepoll_assumptions mem_F_bound5
      by (rule_tac lam_Least_assumption_general[where U="domain", OF _ mem_F_bound5])
        simp_all
  qed
  from \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<alpha> \<in> M\<close> \<open>Ord(z)\<close> \<open>z\<in>M\<close>
  have "\<alpha> \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using
      cardinal_rel_lt_csucc_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      le_Card_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      Aleph_rel_succ[of z] Card_rel_lt_iff[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      lt_Ord[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_csucc_rel[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_Aleph_rel[THEN Card_rel_is_Ord]
    by simp
  with \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<forall>\<beta>\<in>\<alpha>. |F`\<beta>|\<^bsup>M\<^esup> \<le> \<omega>\<close> \<open>\<alpha> \<in> M\<close> assms
  have "|\<Union>\<beta>\<in>\<alpha>. F`\<beta>|\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using InfCard_rel_Aleph_rel[of z] Aleph_rel_zero
      subset_imp_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le,
        of "\<Union>\<beta>\<in>\<alpha>. F`\<beta>" "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"] Aleph_rel_succ
      Aleph_rel_increasing[THEN leI, THEN [2] le_trans, of _ 0 z]
      Ord_0_lt_iff[THEN iffD1, of z]
    by (cases "0<z"; rule_tac lepoll_rel_imp_cardinal_rel_UN_le) (auto, force)
  moreover
  note \<open>z\<in>M\<close> \<open>Ord(z)\<close>
  moreover from \<open>\<forall>\<beta>\<in>\<alpha>. f`\<beta> \<in> F`\<beta>\<close> \<open>f \<in> surj\<^bsup>M[G]\<^esup>(\<alpha>, \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close>
    \<open>\<alpha> \<in> M\<close> \<open>f \<in> M[G]\<close> and this
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<subseteq> (\<Union>\<beta>\<in>\<alpha>. F`\<beta>)"
    using ext.mem_surj_abs by (force simp add:surj_def)
  moreover from \<open>F \<in> M\<close> \<open>\<alpha> \<in> M\<close>
  have "(\<Union>x\<in>\<alpha>. F ` x) \<in> M"
    using j.B_replacement
    by (intro Union_closed[simplified] RepFun_closed[simplified])
      (auto dest:transM)
  ultimately
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using subset_imp_le_cardinal_rel[of "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "\<Union>\<beta>\<in>\<alpha>. F`\<beta>"]
      le_trans by auto
  with assms
  show "False"
    using Aleph_rel_increasing not_le_iff_lt[of "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_Aleph_rel[THEN Card_rel_is_Ord]
    by auto
qed

end \<comment> \<open>bundle G\_generic1\_lemmas\<close>

end \<comment> \<open>\<^locale>\<open>G_generic4_AC\<close>\<close>

context M_ctm1
begin

abbreviation
  Add :: "i" where
  "Add \<equiv> Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>, 2)"

end \<comment> \<open>\<^locale>\<open>M_ctm1\<close>\<close>

locale add_generic4 = G_generic4_AC "Fn(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" "Fnle(\<omega>, \<aleph>\<^bsub>2\<^esub>\<^bsup>##M\<^esup> \<times> \<omega>, 2)" 0

sublocale add_generic4 \<subseteq> cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto

context add_generic4
begin

notation Leq (infixl "\<preceq>" 50)
notation Incompatible (infixl "\<bottom>" 50)

lemma Add_subs_preserves_Aleph_succ: "Ord(z) \<Longrightarrow> z\<in>M \<Longrightarrow> Card\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)"
  using ccc_preserves_Aleph_succ ccc_Add_subs_Aleph_2
  by auto

lemma Aleph_rel_nats_MG_eq_Aleph_rel_nats_M:
  includes G_generic1_lemmas
  assumes "z \<in> \<omega>"
  shows "\<aleph>\<^bsub>z\<^esub>\<^bsup>M[G]\<^esup> = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
  using assms
proof (induct)
  case 0
  show ?case
    by(rule trans[OF ext.Aleph_rel_zero Aleph_rel_zero[symmetric]])
next
  case (succ z)
  then
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M[G]\<^esup>"
    using Aleph_rel_le_Aleph_rel nat_into_M by simp
  moreover from \<open>z \<in> \<omega>\<close>
  have "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup> \<in> M[G]" "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<in> M[G]"
    using nat_into_M by simp_all
  moreover from this and \<open>\<aleph>\<^bsub>z\<^esub>\<^bsup>M[G]\<^esup> = \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>\<close> \<open>z \<in> \<omega>\<close>
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M[G]\<^esup> \<le> \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"
    using ext.Aleph_rel_succ nat_into_M
      Add_subs_preserves_Aleph_succ[THEN ext.csucc_rel_le, of z]
      Aleph_rel_increasing[of z "succ(z)"]
    by simp
  ultimately
  show ?case using le_anti_sym by blast
qed

abbreviation
  f_G :: "i" (\<open>f\<^bsub>G\<^esub>\<close>) where
  "f\<^bsub>G\<^esub> \<equiv> \<Union>G"

abbreviation
  dom_dense :: "i \<Rightarrow> i" where
  "dom_dense(x) \<equiv> {p \<in> Add . x \<in> domain(p) }"

declare (in M_ctm3_AC) Fn_nat_closed[simplified setclass_iff, simp, intro]
declare (in M_ctm3_AC) Fnle_nat_closed[simp del, rule del,
    simplified setclass_iff, simp, intro]
declare (in M_ctm3_AC) cexp_rel_closed[simplified setclass_iff, simp, intro]
declare (in G_generic4_AC) ext.cexp_rel_closed[simplified setclass_iff, simp, intro]

lemma dom_dense_closed[intro,simp]: "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<Longrightarrow> dom_dense(x) \<in> M"
  using separation_in_domain[of x] nat_into_M
  by (rule_tac separation_closed[simplified], blast dest:transM) simp

lemma domain_f_G: assumes "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "y \<in> \<omega>"
  shows "\<langle>x, y\<rangle> \<in> domain(f\<^bsub>G\<^esub>)"
proof -
  from assms
  have "Add = Fn\<^bsup>M\<^esup>(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<times>\<omega>,2)"
    using Fn_nat_abs by auto
  moreover from this
  have "Fnle(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<times>\<omega>,2) = Fnle\<^bsup>M\<^esup>(\<omega>,\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<times>\<omega>,2)"
    unfolding Fnle_rel_def Fnle_def by auto
  moreover from calculation assms
  have "dense(dom_dense(\<langle>x, y\<rangle>))"
    using dense_dom_dense[of "\<langle>x,y\<rangle>" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>\<times>\<omega>" \<omega>  2] InfCard_rel_nat
    unfolding dense_def by auto
  with assms
  obtain p where "p\<in>dom_dense(\<langle>x, y\<rangle>)" "p\<in>G"
    using M_generic_denseD[of "dom_dense(\<langle>x, y\<rangle>)"]
    by auto
  then
  show "\<langle>x, y\<rangle> \<in> domain(f\<^bsub>G\<^esub>)" by blast
qed

lemma f_G_funtype:
  includes G_generic1_lemmas
  shows "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<rightarrow> 2"
  using generic domain_f_G Pi_iff Un_filter_is_function generic
    subset_trans[OF filter_subset_notion Fn_nat_subset_Pow]
  by force

lemma inj_dense_closed[intro,simp]:
  "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> inj_dense(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,2,w,x) \<in> M"
  using transM[OF _ Aleph_rel2_closed] separation_conj separation_bex
    lam_replacement_product
    separation_in lam_replacement_fst lam_replacement_snd lam_replacement_constant
    lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_restrict']
    separation_bex separation_conj
  by simp

lemma Aleph_rel2_new_reals:
  assumes "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "w \<noteq> x"
  shows "(\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle>) \<noteq> (\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle>)"
proof -
  have "0\<in>2" by auto
  with assms
  have "dense(inj_dense(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,2,w,x))"
    unfolding dense_def using dense_inj_dense by auto
  with assms
  obtain p where "p\<in>inj_dense(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,2,w,x)" "p\<in>G"
    using M_generic_denseD[of "inj_dense(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>,2,w,x)"]
    by blast
  then
  obtain n where "n \<in> \<omega>" "\<langle>\<langle>w, n\<rangle>, 1\<rangle> \<in> p" "\<langle>\<langle>x, n\<rangle>, 0\<rangle> \<in> p"
    by blast
  moreover from this and \<open>p\<in>G\<close>
  have "\<langle>\<langle>w, n\<rangle>, 1\<rangle> \<in> f\<^bsub>G\<^esub>" "\<langle>\<langle>x, n\<rangle>, 0\<rangle> \<in> f\<^bsub>G\<^esub>" by auto
  moreover from calculation
  have "f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle> = 1" "f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle> = 0"
    using f_G_funtype apply_equality
    by auto
  ultimately
  have "(\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle>) ` n \<noteq> (\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle>) ` n"
    by simp
  then
  show ?thesis by fastforce
qed

definition
  h_G :: "i" (\<open>h\<^bsub>G\<^esub>\<close>) where
  "h\<^bsub>G\<^esub> \<equiv> \<lambda>\<alpha>\<in>\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>. \<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub>`\<langle>\<alpha>,n\<rangle>"

lemma h_G_in_MG[simp]:
  includes G_generic1_lemmas
  shows "h\<^bsub>G\<^esub> \<in> M[G]"
  using ext.curry_closed[unfolded curry_def] G_in_MG
  unfolding h_G_def
  by simp

lemma h_G_inj_Aleph_rel2_reals: "h\<^bsub>G\<^esub> \<in> inj\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
  using Aleph_rel_sub_closed f_G_funtype G_in_MG Aleph_rel_sub_closed
    ext.curry_rel_exp[unfolded curry_def] ext.curry_closed[unfolded curry_def]
    ext.mem_function_space_rel_abs
  by (intro ext.mem_inj_abs[THEN iffD2],simp_all)
      (auto simp: inj_def h_G_def dest:Aleph_rel2_new_reals)

lemma Aleph2_extension_le_continuum_rel:
  includes G_generic1_lemmas
  shows "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<lesssim>\<^bsup>M[G]\<^esup> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
    using ext.def_lepoll_rel[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"]
      h_G_inj_Aleph_rel2_reals Aleph_rel_nats_MG_eq_Aleph_rel_nats_M
    by auto
  moreover from calculation
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<lesssim>\<^bsup>M[G]\<^esup> |\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2|\<^bsup>M[G]\<^esup>"
    using ext.lepoll_rel_imp_lepoll_rel_cardinal_rel by simp
  ultimately
  have "|\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup>|\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using ext.lepoll_rel_imp_cardinal_rel_le[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2",
        OF _ _ ext.function_space_rel_closed]
      ext.Aleph_rel_zero
    unfolding cexp_rel_def by simp
  then
  show "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using ext.Card_rel_Aleph_rel[of 2, THEN ext.Card_rel_cardinal_rel_eq]
    by simp
qed

lemma Aleph_rel_lt_continuum_rel: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> < 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
  using Aleph2_extension_le_continuum_rel
    ext.Aleph_rel_increasing[of 1 2] le_trans by auto

corollary not_CH: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> \<noteq> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
  using Aleph_rel_lt_continuum_rel by auto

end \<comment> \<open>\<^locale>\<open>add_generic4\<close>\<close>

subsection\<open>Models of fragments of $\ZFC + \neg \CH$\<close>

definition
  ContHyp :: "o" where
  "ContHyp \<equiv> \<aleph>\<^bsub>1\<^esub> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^esup>"

relativize functional "ContHyp" "ContHyp_rel"
notation ContHyp_rel (\<open>CH\<^bsup>_\<^esup>\<close>)
relationalize "ContHyp_rel" "is_ContHyp"

context M_ZF_library
begin

is_iff_rel for "ContHyp"
  using is_cexp_iff is_Aleph_iff[of 0] is_Aleph_iff[of 1]
  unfolding is_ContHyp_def ContHyp_rel_def
  by (auto simp del:setclass_iff) (rule rexI[of _ _ M, OF _ nonempty], auto)

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

synthesize "is_ContHyp" from_definition assuming "nonempty"
arity_theorem for "is_ContHyp_fm"

notation is_ContHyp_fm (\<open>\<cdot>CH\<cdot>\<close>)

theorem ctm_of_not_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}"
    "\<Phi> \<subseteq> formula" "M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>} \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N))"
proof -
  from \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}\<close>
  interpret M_ZFC4 M
    using M_satT_overhead_imp_M_ZF4 unfolding overhead_notCH_def by force
  from \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH}\<close> \<open>Transset(M)\<close>
  interpret M_ZF_ground_notCH_trans M
    using M_satT_imp_M_ZF_ground_notCH_trans
    unfolding ZC_def by auto
  from \<open>M \<approx> \<omega>\<close>
  obtain enum where "enum \<in> bij(\<omega>,M)"
    using eqpoll_sym unfolding eqpoll_def by blast
  then
  interpret M_ctm4_AC M enum by unfold_locales
  interpret cohen_data \<omega> "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2 by unfold_locales auto
  have "Add \<in> M" "Add_le(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>) \<in> M"
    using nat_into_M Aleph_rel_closed M_nat cartprod_closed Fn_nat_closed Fnle_nat_closed
    by simp_all
  then
  interpret forcing_data1 "Add" "Add_le(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)" 0 M enum
    by unfold_locales simp_all
  obtain G where "M_generic(G)"
    using generic_filter_existence[OF one_in_P]
    by auto
  moreover from this
  interpret add_generic4 M enum G by unfold_locales
  have "\<not> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>)"
    using not_CH .
  then
  have "M[G], [] \<Turnstile> \<cdot>\<not>\<cdot>CH\<cdot>\<cdot>"
    using ext.is_ContHyp_iff
    by (simp add:ContHyp_rel_def)
  then
  have "M[G] \<Turnstile> ZC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}"
    using ext.M_satT_ZC by auto
  moreover
  have "Transset(M[G])" using Transset_MG .
  moreover
  have "M \<subseteq> M[G]" using M_subset_MG[OF one_in_G] generic by simp
  moreover
  note \<open>M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}\<close> \<open>\<Phi> \<subseteq> formula\<close>
  ultimately
  show ?thesis
    using Ord_MG_iff MG_eqpoll_nat satT_ground_repl_fm_imp_satT_ZF_replacement_fm[of \<Phi>]
    by (rule_tac x="M[G]" in exI, blast)
qed

lemma ZF_replacement_overhead_sub_ZFC: "{\<cdot>Replacement(p)\<cdot> . p \<in> overhead} \<subseteq> ZFC"
  using overhead_type unfolding ZFC_def ZF_def ZF_schemes_def by auto

lemma ZF_replacement_overhead_notCH_sub_ZFC: "{\<cdot>Replacement(p)\<cdot> . p \<in> overhead_notCH} \<subseteq> ZFC"
  using overhead_notCH_type unfolding ZFC_def ZF_def ZF_schemes_def by auto

lemma ZF_replacement_overhead_CH_sub_ZFC: "{\<cdot>Replacement(p)\<cdot> . p \<in> overhead_CH} \<subseteq> ZFC"
  using overhead_CH_type unfolding ZFC_def ZF_def ZF_schemes_def by auto

corollary ctm_ZFC_imp_ctm_not_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZFC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N))"
proof-
  from assms
  have "\<exists>N.
      M \<subseteq> N \<and>
        N \<approx> \<omega> \<and>
        Transset(N) \<and>
        N \<Turnstile> ZC \<and> N \<Turnstile> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<and> N \<Turnstile> {\<cdot>Replacement(x)\<cdot> . x \<in> formula} \<and> (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)"
    using ctm_of_not_CH[of M formula] satT_ZFC_imp_satT_ZC[of M]
      satT_mono[OF _ ground_repl_fm_sub_ZFC, of M]
      satT_mono[OF _ ZF_replacement_overhead_notCH_sub_ZFC, of M]
      satT_mono[OF _ ZF_replacement_fms_sub_ZFC, of M]
    by (simp add: satT_Un_iff)
  then
  obtain N where "N \<Turnstile> ZC" "N \<Turnstile> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}" "N \<Turnstile> {\<cdot>Replacement(x)\<cdot> . x \<in> formula}"
    "M \<subseteq> N" "N \<approx> \<omega>" "Transset(N)" "(\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)"
    by auto
  moreover from this
  have "N \<Turnstile> ZFC"
    using satT_ZC_ZF_replacement_imp_satT_ZFC
    by auto
  moreover from this and \<open>N \<Turnstile> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}\<close>
  have "N \<Turnstile> ZFC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>}"
    by auto
  ultimately
  show ?thesis by auto
qed

end