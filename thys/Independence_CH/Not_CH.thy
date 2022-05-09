section\<open>Model of the negation of the Continuum Hypothesis\<close>

theory Not_CH
  imports
    Cardinal_Preservation
begin

txt\<open>We are taking advantage that the poset of finite functions is absolute,
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

locale M_master = M_cohen + M_library_DC +
  assumes
  UN_lepoll_assumptions:
  "M(A) \<Longrightarrow> M(b) \<Longrightarrow> M(f) \<Longrightarrow> M(A') \<Longrightarrow> separation(M, \<lambda>y. \<exists>x\<in>A'. y = \<langle>x, \<mu> i. x\<in>if_range_F_else_F((`)(A), b, f, i)\<rangle>)"

subsection\<open>Non-absolute concepts between extensions\<close>

locale M_master_sub = M_master + N:M_master N for N +
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
 separation_insnd_ballPair
 separation_ifrangeF_body separation_ifrangeF_body2 separation_ifrangeF_body3
 separation_ifrangeF_body4 separation_ifrangeF_body5 separation_ifrangeF_body6
 separation_ifrangeF_body7 separation_cardinal_rel_lesspoll_rel
 separation_is_dcwit_body

lemmas (in M_ZF3_trans) repl_instances = lam_replacement_inj_rel
  lam_replacement_cardinal replacement_trans_apply_image

sublocale M_ZFC3_trans \<subseteq> M_master "##M"
  using replacement_dcwit_repl_body\<comment> \<open>this is another replacement instance\<close>
  by unfold_locales (simp_all add:repl_instances sep_instances del:setclass_iff
      add: transrec_replacement_def wfrec_replacement_def dcwit_repl_body_def)

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
    mem_F_bound4 apply_0
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
  using G_in_Gen_Ext[ OF _ one_in_G, OF _ generic]
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
    using ext.lt_surj_rel_empty_imp_Card_rel M_subset_MG[OF one_in_G, OF generic]
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
      with \<open>F:\<alpha>\<rightarrow>Pow\<^bsup>M\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close>
      have "x \<in> \<alpha>"
        using domain_of_fun by simp
      with \<open>\<alpha> \<in> M\<close>
      show "x \<in> M" by (auto dest:transM)
    qed
    with \<open>\<alpha> \<in> M\<close> \<open>F:\<alpha>\<rightarrow>Pow\<^bsup>M\<^esup>(\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close> \<open>F\<in>M\<close>
  interpret M_cardinal_UN_lepoll "##M" "\<lambda>\<beta>. F`\<beta>" \<alpha>
    using UN_lepoll_assumptions lepoll_assumptions
      lam_replacement_apply lam_replacement_inj_rel
  proof (unfold_locales, auto dest:transM simp del:if_range_F_else_F_def)
    fix f b
    assume "b\<in>M" "f\<in>M"
    with \<open>F\<in>M\<close>
    show "lam_replacement(##M, \<lambda>x. \<mu> i. x \<in> if_range_F_else_F((`)(F), b, f, i))"
      using UN_lepoll_assumptions mem_F_bound5
      by (rule_tac lam_Least_assumption_general[where U="domain", OF _ mem_F_bound5])
        simp_all
  qed
  from \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<alpha> \<in> M\<close> assms
  have "\<alpha> \<lesssim>\<^bsup>M\<^esup> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using
      Aleph_rel_zero
      cardinal_rel_lt_csucc_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      le_Card_rel_iff[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>" \<alpha>]
      Aleph_rel_succ[of z] Card_rel_lt_iff[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      lt_Ord[of \<alpha> "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>"]
      Card_rel_csucc_rel[of "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"]
      Aleph_rel_closed[of z]
      Card_rel_Aleph_rel[THEN Card_rel_is_Ord, OF _ _ Aleph_rel_closed]
    by simp
  with \<open>\<alpha> < \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>\<close> \<open>\<forall>\<beta>\<in>\<alpha>. |F`\<beta>|\<^bsup>M\<^esup> \<le> \<omega>\<close> \<open>\<alpha> \<in> M\<close> assms
  have "|\<Union>\<beta>\<in>\<alpha>. F`\<beta>|\<^bsup>M\<^esup> \<le> \<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"
    using InfCard_rel_Aleph_rel[of z] Aleph_rel_zero
      subset_imp_lepoll_rel[THEN lepoll_rel_imp_cardinal_rel_le,
        of "\<Union>\<beta>\<in>\<alpha>. F`\<beta>" "\<aleph>\<^bsub>z\<^esub>\<^bsup>M\<^esup>"] Aleph_rel_succ
      Aleph_rel_increasing[THEN leI, THEN [2] le_trans, of _ 0 z]
      Ord_0_lt_iff[THEN iffD1, of z]
    by (cases "0<z"; rule_tac leqpoll_rel_imp_cardinal_rel_UN_le) (auto, force)
  moreover
  note \<open>z\<in>M\<close> \<open>Ord(z)\<close>
  moreover from \<open>\<forall>\<beta>\<in>\<alpha>. f`\<beta> \<in> F`\<beta>\<close> \<open>f \<in> surj\<^bsup>M[G]\<^esup>(\<alpha>, \<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup>)\<close>
    \<open>\<alpha> \<in> M\<close> \<open>f \<in> M[G]\<close> and this
  have "\<aleph>\<^bsub>succ(z)\<^esub>\<^bsup>M\<^esup> \<subseteq> (\<Union>\<beta>\<in>\<alpha>. F`\<beta>)"
    using ext.mem_surj_abs by (force simp add:surj_def)
  moreover from \<open>F \<in> M\<close> \<open>\<alpha> \<in> M\<close>
  have "(\<Union>x\<in>\<alpha>. F ` x) \<in> M"
    using j.B_replacement\<comment> \<open>NOTE: it didn't require @{thm j.UN_closed} before!\<close>
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
notation GenExt_at_P ("_[_]" [71,1])

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
  have "\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup> = \<omega>"
    using ext.Aleph_rel_zero .
  also
  have "\<omega> = \<aleph>\<^bsub>0\<^esub>\<^bsup>M\<^esup>"
    using Aleph_rel_zero by simp
  finally
  show ?case .
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
  dom_dense :: "i\<Rightarrow>i" where
  "dom_dense(x) \<equiv> { p\<in>Add . x \<in> domain(p) }"

(* TODO: write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close> *)
lemma dense_dom_dense: "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<Longrightarrow> dense(dom_dense(x))"
proof
  fix p
  assume "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" "p \<in> Add"
  show "\<exists>d\<in>dom_dense(x). d \<preceq> p"
  proof (cases "x \<in> domain(p)")
    case True
    with \<open>x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close> \<open>p \<in> Add\<close>
    show ?thesis using refl_leq by auto
  next
    case False
    note \<open>p \<in> Add\<close>
    moreover from this and False and \<open>x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>\<close>
    have "cons(\<langle>x,0\<rangle>, p) \<in> Add"
      using FiniteFun.consI[of x "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 0 2 p]
        Fn_nat_eq_FiniteFun by auto
    moreover from \<open>p \<in> Add\<close>
    have "x\<in>domain(cons(\<langle>x,0\<rangle>, p))" by simp
    ultimately
    show ?thesis
      by (fastforce del:FnD)
  qed
qed

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
  have "dense(dom_dense(\<langle>x, y\<rangle>))" using dense_dom_dense by simp
  with assms
  obtain p where "p\<in>dom_dense(\<langle>x, y\<rangle>)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "dom_dense(\<langle>x, y\<rangle>)"]
    by auto
  then
  show "\<langle>x, y\<rangle> \<in> domain(f\<^bsub>G\<^esub>)" by blast
qed

lemma f_G_funtype:
  includes G_generic1_lemmas
  shows "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega> \<rightarrow> 2"
  using generic domain_f_G
  unfolding Pi_def
proof (auto)
  show "x \<in> B \<Longrightarrow> B \<in> G \<Longrightarrow> x \<in> (\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>) \<times> 2" for B x
    using Fn_nat_subset_Pow by blast
  show "function(f\<^bsub>G\<^esub>)"
    using Un_filter_is_function generic
    unfolding M_generic_def by fast
qed

abbreviation
  inj_dense :: "i\<Rightarrow>i\<Rightarrow>i" where
  "inj_dense(w,x) \<equiv>
    { p\<in>Add . (\<exists>n\<in>\<omega>. \<langle>\<langle>w,n\<rangle>,1\<rangle> \<in> p \<and> \<langle>\<langle>x,n\<rangle>,0\<rangle> \<in> p) }"

(* TODO write general versions of this for \<^term>\<open>Fn(\<omega>,I,J)\<close> *)
lemma dense_inj_dense:
  assumes "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "w \<noteq> x"
  shows "dense(inj_dense(w,x))"
proof
  fix p
  assume "p \<in> Add"
  then
  obtain n where "\<langle>w,n\<rangle> \<notin> domain(p)" "\<langle>x,n\<rangle> \<notin> domain(p)" "n \<in> \<omega>"
  proof -
    {
      assume "\<langle>w,n\<rangle> \<in> domain(p) \<or> \<langle>x,n\<rangle> \<in> domain(p)" if "n \<in> \<omega>" for n
      then
      have "\<omega> \<subseteq> range(domain(p))" by blast
      then
      have "\<not> Finite(p)"
        using Finite_range Finite_domain subset_Finite nat_not_Finite
        by auto
      with \<open>p \<in> Add\<close>
      have False
        using Fn_nat_eq_FiniteFun FiniteFun.dom_subset[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 2]
          Fin_into_Finite by auto
    }
    with that\<comment> \<open>the shape of the goal puts assumptions in this variable\<close>
    show ?thesis by auto
  qed
  moreover
  note \<open>p \<in> Add\<close> assms
  moreover from calculation
  have "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) \<in> Add"
    using FiniteFun.consI[of "\<langle>x,n\<rangle>" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 0 2 p]
      Fn_nat_eq_FiniteFun by auto
  ultimately
  have "cons(\<langle>\<langle>w,n\<rangle>,1\<rangle>, cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p) ) \<in> Add"
    using FiniteFun.consI[of "\<langle>w,n\<rangle>" "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<times> \<omega>" 1 2 "cons(\<langle>\<langle>x,n\<rangle>,0\<rangle>, p)"]
      Fn_nat_eq_FiniteFun by auto
  with \<open>n \<in> \<omega>\<close>
  show "\<exists>d\<in>inj_dense(w,x). d \<preceq> p"
    using \<open>p \<in> Add\<close> by (intro bexI) auto
qed

lemma inj_dense_closed[intro,simp]:
  "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> inj_dense(w,x) \<in> M"
  using transM[OF _ Aleph_rel2_closed] separation_conj separation_bex
    lam_replacement_hcomp2[OF _ _  _ _ lam_replacement_Pair]
    separation_in lam_replacement_fst lam_replacement_snd lam_replacement_constant
    lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_restrict']
    separation_bex separation_conj
  by simp

lemma Aleph_rel2_new_reals:
  assumes "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "w \<noteq> x"
  shows "(\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>w, n\<rangle>) \<noteq> (\<lambda>n\<in>\<omega>. f\<^bsub>G\<^esub> ` \<langle>x, n\<rangle>)"
proof -
  from assms
  have "dense(inj_dense(w,x))" using dense_inj_dense by simp
  with assms
  obtain p where "p\<in>inj_dense(w,x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "inj_dense(w,x)"]
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
  using ext.lam_apply_replacement ext.apply_replacement2
    ext.lam_apply_replacement[unfolded lam_replacement_def]
    ext.Union_closed[simplified, OF G_in_MG]
    \<comment> \<open>The "simplified" here is because of
        the \<^term>\<open>setclass\<close> ocurrences\<close>
    ext.nat_into_M
  unfolding h_G_def
  by (rule_tac ext.lam_closed[simplified] |
      auto dest:transM del:ext.cexp_rel_closed[simplified])+

lemma h_G_inj_Aleph_rel2_reals: "h\<^bsub>G\<^esub> \<in> inj\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
  using Aleph_rel_sub_closed
proof (intro ext.mem_inj_abs[THEN iffD2])
  show "h\<^bsub>G\<^esub> \<in> inj(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
    unfolding inj_def
  proof (intro ballI CollectI impI)
    show "h\<^bsub>G\<^esub> \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
      using f_G_funtype G_in_MG ext.nat_into_M
      unfolding h_G_def
      apply (intro lam_type ext.mem_function_space_rel_abs[THEN iffD2], simp_all)
      apply (rule_tac ext.lam_closed[simplified], simp_all)
       apply (rule ext.apply_replacement2)
        apply (auto dest:ext.transM[OF _ Aleph_rel_sub_closed])
      done
    fix w x
    assume "w \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "x \<in> \<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "h\<^bsub>G\<^esub> ` w = h\<^bsub>G\<^esub> ` x"
    then
    show "w = x"
      unfolding h_G_def using Aleph_rel2_new_reals by auto
  qed
qed simp_all

lemma Aleph2_extension_le_continuum_rel:
  includes G_generic1_lemmas
  shows "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<in> M[G]" "Ord(\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_is_Ord by auto
  moreover from this
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M[G]\<^esup> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
    using ext.def_lepoll_rel[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"]
      h_G_inj_Aleph_rel2_reals by auto
  moreover from calculation
  have "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup> \<lesssim>\<^bsup>M[G]\<^esup> |\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2|\<^bsup>M[G]\<^esup>"
    using ext.lepoll_rel_imp_lepoll_rel_cardinal_rel by simp
  ultimately
  have "|\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>|\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using ext.lepoll_rel_imp_cardinal_rel_le[of "\<aleph>\<^bsub>2\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2",
        OF _ _ ext.function_space_rel_closed]
      ext.Aleph_rel_zero Aleph_rel_nats_MG_eq_Aleph_rel_nats_M
    unfolding cexp_rel_def by simp
  then
  show "\<aleph>\<^bsub>2\<^esub>\<^bsup>M[G]\<^esup> \<le> 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using Aleph_rel_nats_MG_eq_Aleph_rel_nats_M
      ext.Card_rel_Aleph_rel[of 2, THEN ext.Card_rel_cardinal_rel_eq]
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

context M_master
begin

is_iff_rel for "ContHyp"
  using is_cexp_iff is_Aleph_iff[of 0] is_Aleph_iff[of 1]
  unfolding is_ContHyp_def ContHyp_rel_def
  by (auto simp del:setclass_iff) (rule rexI[of _ _ M, OF _ nonempty], auto)

end \<comment> \<open>\<^locale>\<open>M_master\<close>\<close>

synthesize "is_ContHyp" from_definition assuming "nonempty"
arity_theorem for "is_ContHyp_fm"

notation is_ContHyp_fm (\<open>\<cdot>CH\<cdot>\<close>)

theorem ctm_of_not_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}"
    "\<Phi> \<subseteq> formula" "M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZC \<union> {\<cdot>\<not>\<cdot>CH\<cdot>\<cdot>} \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>} \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N))"
proof -
  from \<open>M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}\<close>
  interpret M_ZFC4 M
    using M_satT_overhead_imp_M_ZF4 by simp
  from \<open>Transset(M)\<close>
  interpret M_ZFC4_trans M
    using M_satT_imp_M_ZF4
    by unfold_locales
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
      satT_mono[OF _ ZF_replacement_overhead_sub_ZFC, of M]
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