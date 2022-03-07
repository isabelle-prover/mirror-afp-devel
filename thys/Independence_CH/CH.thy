section\<open>Forcing extension satisfying the Continuum Hypothesis\<close>

theory CH
  imports
    Kappa_Closed_Notions
    Cohen_Posets_Relative
begin

context M_ctm3_AC
begin

declare Fn_rel_closed[simp del, rule del, simplified setclass_iff, simp, intro]
declare Fnle_rel_closed[simp del, rule del, simplified setclass_iff, simp, intro]

abbreviation
  Coll :: "i" where
  "Coll \<equiv> Fn\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"

abbreviation
  Colleq :: "i" where
  "Colleq \<equiv> Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"

lemma Coll_in_M[intro,simp]: "Coll \<in> M" by simp

lemma Colleq_refl : "refl(Coll,Colleq)"
  unfolding Fnle_rel_def Fnlerel_def refl_def
  using RrelI by simp

subsection\<open>Collapse forcing is sufficiently closed\<close>

\<comment> \<open>Kunen IV.7.14, only for \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>\<close>
lemma succ_omega_closed_Coll: "succ(\<omega>)-closed\<^bsup>M\<^esup>(Coll,Colleq)"
proof -
  \<comment> \<open>Case for finite sequences\<close>
  have "n\<in>\<omega> \<Longrightarrow> \<forall>f \<in> n \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq)).
          \<exists>q\<in>M. q \<in> Coll \<and> (\<forall>\<alpha>\<in>M. \<alpha> \<in> n \<longrightarrow> \<langle>q, f ` \<alpha>\<rangle> \<in> Colleq)" for n
  proof (induct rule:nat_induct)
    case 0
    then
    show ?case
      using zero_lt_Aleph_rel1 zero_in_Fn_rel
      by (auto simp del:setclass_iff) (rule bexI[OF _ zero_in_M], auto)
  next
    case (succ x)
    then
    have "\<forall>f\<in>succ(x) \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq)). \<forall>\<alpha> \<in> succ(x). \<langle>f`x, f ` \<alpha>\<rangle> \<in> Colleq"
    proof(intro ballI)
      fix f \<alpha>
      assume "f\<in>succ(x) \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq))" "\<alpha>\<in>succ(x)"
      moreover from \<open>x\<in>\<omega>\<close> this
      have "f\<in>succ(x) \<^sub><\<rightarrow> (Coll,converse(Colleq))"
        using mono_seqspace_rel_char nat_into_M
        by simp
      moreover from calculation succ
      consider "\<alpha>\<in>x" | "\<alpha>=x"
        by auto
      then
      show "\<langle>f`x, f ` \<alpha>\<rangle> \<in> Colleq"
      proof(cases)
        case 1
        then
        have "\<langle>\<alpha>, x\<rangle> \<in> Memrel(succ(x))" "x\<in>succ(x)" "\<alpha>\<in>succ(x)"
          by auto
        with \<open>f\<in>succ(x) \<^sub><\<rightarrow> (Coll,converse(Colleq))\<close>
        show ?thesis
          using mono_mapD(2)[OF _ \<open>\<alpha>\<in>succ(x)\<close> _ \<open>\<langle>\<alpha>, x\<rangle> \<in> Memrel(succ(x))\<close>]
          unfolding mono_seqspace_def
          by auto
      next
        case 2
        with \<open>f\<in>succ(x) \<^sub><\<rightarrow> (Coll,converse(Colleq))\<close>
        show ?thesis
          using Colleq_refl mono_seqspace_is_fun[THEN apply_type]
          unfolding refl_def
          by simp
      qed
    qed
    moreover
    note \<open>x\<in>\<omega>\<close>
    moreover from this
    have "f`x \<in> Coll" if "f: succ(x) \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq))" for f
      using that mono_seqspace_rel_char[simplified, of "succ(x)" Coll "converse(Colleq)"]
        nat_into_M[simplified] mono_seqspace_is_fun[of "converse(Colleq)"]
      by (intro apply_type[of _ "succ(x)"]) (auto simp del:setclass_iff)
    ultimately
    show ?case
      using transM[of _ Coll]
      by (auto dest:transM simp del:setclass_iff, rule_tac x="f`x" in bexI)
        (auto simp del:setclass_iff, simp)
  qed
  moreover
    \<comment> \<open>Interesting case: Countably infinite sequences.\<close>
  have "\<forall>f\<in>M. f \<in> \<omega> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq)) \<longrightarrow>
                  (\<exists>q\<in>M. q \<in> Coll \<and> (\<forall>\<alpha>\<in>M. \<alpha> \<in> \<omega> \<longrightarrow> \<langle>q, f ` \<alpha>\<rangle> \<in> Colleq))"
  proof(intro ballI impI)
    fix f
    let ?G="f``\<omega>"
    assume "f\<in>M" "f \<in> \<omega> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (Coll,converse(Colleq))"
    moreover from this
    have "f\<in>\<omega> \<^sub><\<rightarrow> (Coll,converse(Colleq))" "f\<in>\<omega> \<rightarrow> Coll"
      using mono_seqspace_rel_char mono_mapD(2) nat_in_M
      by auto
    moreover from this
    have "countable\<^bsup>M\<^esup>(f`x)" if "x\<in>\<omega>" for x
      using that Fn_rel_is_function countable_iff_lesspoll_rel_Aleph_rel_one
      by auto
    moreover from calculation
    have "?G \<in> M" "f\<subseteq>\<omega>\<times>Coll"
      using nat_in_M image_closed Pi_iff
      by simp_all
    moreover from calculation
    have 1:"\<exists>d\<in>?G. d \<supseteq> h \<and> d \<supseteq> g" if "h \<in> ?G" "g \<in> ?G" for h g
    proof -
      from calculation
      have "?G={f`x . x\<in>\<omega>}"
        using  image_function[of f \<omega>] Pi_iff domain_of_fun
        by auto
      from \<open>?G=_\<close> that
      obtain m n where eq:"h=f`m" "g=f`n" "n\<in>\<omega>" "m\<in>\<omega>"
        by auto
      then
      have "m\<union>n\<in>\<omega>" "m\<le>m\<union>n" "n\<le>m\<union>n"
        using Un_upper1_le Un_upper2_le nat_into_Ord by simp_all
      with calculation eq \<open>?G=_\<close>
      have "f`(m\<union>n)\<in>?G" "f`(m\<union>n) \<supseteq> h" "f`(m\<union>n) \<supseteq> g"
        using Fnle_relD mono_map_lt_le_is_mono converse_refl[OF Colleq_refl]
        by auto
      then
      show ?thesis
        by auto
    qed
    moreover from calculation
    have "?G \<subseteq> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightharpoonup>\<^bsup>##M\<^esup> (nat \<rightarrow>\<^bsup>M\<^esup> 2))"
      using subset_trans[OF image_subset[OF \<open>f\<subseteq>_\<close>,of \<omega>] Fn_rel_subset_PFun_rel]
      by simp
    moreover
    have "\<Union> ?G \<in> (\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightharpoonup>\<^bsup>##M\<^esup> (nat \<rightarrow>\<^bsup>M\<^esup> 2))"
      using pfun_Un_filter_closed'[OF \<open>?G\<subseteq>_\<close> 1]  \<open>?G\<in>M\<close>
      by simp
    moreover from calculation
    have "\<Union>?G \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
      using countable_fun_imp_countable_image[of f]
        mem_function_space_rel_abs[simplified,OF nat_in_M Coll_in_M \<open>f\<in>M\<close>]
        countableI[OF lepoll_rel_refl]
        countable_iff_lesspoll_rel_Aleph_rel_one[of "\<Union>?G"]
      by auto
    moreover from calculation
    have "\<Union>?G\<in>Coll"
      unfolding Fn_rel_def
      by simp
    moreover from calculation
    have "\<Union>?G \<supseteq> f ` \<alpha> " if "\<alpha>\<in>\<omega>" for \<alpha>
      using that image_function[OF fun_is_function] domain_of_fun
      by auto
    ultimately
    show "\<exists>q\<in>M. q \<in> Coll \<and> (\<forall>\<alpha>\<in>M. \<alpha> \<in> \<omega> \<longrightarrow> \<langle>q, f ` \<alpha>\<rangle> \<in> Colleq)"
      using Fn_rel_is_function Fnle_relI
      by auto
  qed
  ultimately
  show ?thesis
    unfolding kappa_closed_rel_def by (auto elim!:leE dest:ltD)
qed

end \<comment> \<open>\<^locale>\<open>M_ctm3_AC\<close>\<close>

locale collapse_generic4 = G_generic4_AC "Fn\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" "Fnle\<^bsup>M\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>##M\<^esup>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M\<^esup> 2)" 0

sublocale collapse_generic4 \<subseteq> forcing_notion "Coll" "Colleq" 0
  using zero_lt_Aleph_rel1 by unfold_locales

context collapse_generic4
begin

notation Leq (infixl "\<preceq>" 50)
notation Incompatible (infixl "\<bottom>" 50)
notation GenExt_at_P ("_[_]" [71,1])

abbreviation
  f_G :: "i" (\<open>f\<^bsub>G\<^esub>\<close>) where
  "f\<^bsub>G\<^esub> \<equiv> \<Union>G"

lemma f_G_in_MG[simp]:
  shows "f\<^bsub>G\<^esub> \<in> M[G]"
  using G_in_MG by simp

abbreviation
  dom_dense :: "i\<Rightarrow>i" where
  "dom_dense(x) \<equiv> { p\<in>Coll . x \<in> domain(p) }"

lemma Coll_into_countable_rel: "p \<in> Coll \<Longrightarrow> countable\<^bsup>M\<^esup>(p)"
proof -
  assume "p\<in>Coll"
  then
  have "p \<prec>\<^bsup>M\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "p\<in>M"
    using Fn_rel_is_function by simp_all
  moreover from this
  have "p \<lesssim>\<^bsup>M\<^esup> \<omega>"
    using lesspoll_rel_Aleph_rel_succ[of 0] Aleph_rel_zero
    by simp
  ultimately
  show ?thesis
    using countableI eqpoll_rel_imp_lepoll_rel eqpoll_rel_sym cardinal_rel_eqpoll_rel
    by simp
qed

(* TODO: Should be more general, cf. @{thm add_generic.dense_dom_dense} *)
lemma dense_dom_dense: "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<Longrightarrow> dense(dom_dense(x))"
proof
  fix p
  assume "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "p \<in> Coll"
  show "\<exists>d\<in>dom_dense(x). d \<preceq> p"
  proof (cases "x \<in> domain(p)")
    case True
    with \<open>x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close> \<open>p \<in> Coll\<close>
    show ?thesis using refl_leq by auto
  next
    case False
    note \<open>p \<in> Coll\<close>
    moreover from this and False and \<open>x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>\<close>
    have "cons(\<langle>x,\<lambda>n\<in>\<omega>. 0\<rangle>, p) \<in> Coll" "x\<in>M"
      using function_space_rel_char
        function_space_rel_closed lam_replacement_constant
        lam_replacement_iff_lam_closed InfCard_rel_Aleph_rel
      by (auto intro!: cons_in_Fn_rel dest:transM intro:function_space_nonempty)
    ultimately
    show ?thesis
      using Fn_relD by blast
  qed
qed

lemma dom_dense_closed[intro,simp]: "x\<in>M \<Longrightarrow> dom_dense(x) \<in> M"
  using separation_in_domain[of x]
  by simp

lemma domain_f_G: assumes "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  shows "x \<in> domain(f\<^bsub>G\<^esub>)"
proof -
  from assms
  have "dense(dom_dense(x))" "x\<in>M"
    using dense_dom_dense transitivity[OF _
        Aleph_rel_closed[of 1,THEN setclass_iff[THEN iffD1]]]
    by simp_all
  with assms
  obtain p where "p\<in>dom_dense(x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "dom_dense(x)"]
    by auto
  then
  show "x \<in> domain(f\<^bsub>G\<^esub>)" by blast
qed

lemma rex_mono : assumes "\<exists> d \<in> A . P(d)" "A\<subseteq>B"
  shows "\<exists> d \<in> B. P(d)"
  using assms by auto

lemma Un_filter_is_function:
  assumes "filter(G)"
  shows "function(\<Union>G)"
proof -
  have "Coll \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightharpoonup>\<^bsup>##M\<^esup> (\<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"
    using Fn_rel_subset_PFun_rel
    by simp
  moreover
  have "\<exists> d \<in> Coll. d \<supseteq> f \<and> d \<supseteq> g" if "f\<in>G" "g\<in>G" for f g
    using filter_imp_compat[OF assms \<open>f\<in>G\<close> \<open>g\<in>G\<close>] filterD[OF assms]
    unfolding compat_def compat_in_def
    by auto
  ultimately
  have "\<exists>d \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightharpoonup>\<^bsup>##M\<^esup> (\<omega> \<rightarrow>\<^bsup>M\<^esup> 2). d \<supseteq> f \<and> d \<supseteq> g" if "f\<in>G" "g\<in>G" for f g
    using rex_mono[of Coll] that by simp
  moreover
  have "G\<subseteq>Coll"
    using assms
    unfolding filter_def
    by simp
  moreover from this
  have "G \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightharpoonup>\<^bsup>##M\<^esup> (\<omega> \<rightarrow>\<^bsup>M\<^esup> 2)"
    using assms  unfolding Fn_rel_def
    by auto
  ultimately
  show ?thesis
    using pfun_Un_filter_closed[of G]
    by simp
qed

lemma f_G_funtype:
  shows "f\<^bsub>G\<^esub> : \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
proof -
  have "x \<in> B \<Longrightarrow> B \<in> G \<Longrightarrow> x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<times> (\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)" for B x
  proof -
    assume "x\<in>B" "B\<in>G"
    moreover from this
    have "x \<in> M[G]"
      by (auto dest!:generic_dests ext.transM)
        (intro generic_simps(2)[of Coll], simp)
    moreover from calculation
    have "x \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<times> (\<omega> \<rightarrow> 2)"
      using Fn_rel_subset_Pow[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2",
          OF _ _ function_space_rel_closed] function_space_rel_char
      by (auto dest!:generic_dests)
    moreover from this
    obtain z w where "x=\<langle>z,w\<rangle>" "z\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "w:\<omega> \<rightarrow> 2" by auto
    moreover from calculation
    have "w \<in> M[G]" by (auto dest:ext.transM)
    ultimately
    show ?thesis using ext.function_space_rel_char by auto
  qed
  moreover
  have "function(f\<^bsub>G\<^esub>)"
    using Un_filter_is_function generic
    unfolding M_generic_def by fast
  ultimately
  show ?thesis
    using generic domain_f_G unfolding Pi_def by auto
qed

abbreviation
  surj_dense :: "i\<Rightarrow>i" where
  "surj_dense(x) \<equiv> { p\<in>Coll . x \<in> range(p) }"

(* TODO: write general versions of this for \<^term>\<open>Fn\<^bsup>M\<^esup>(\<kappa>,I,J)\<close> *)
lemma dense_surj_dense:
  assumes "x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
  shows "dense(surj_dense(x))"
proof
  fix p
  assume "p \<in> Coll"
  then
  have "countable\<^bsup>M\<^esup>(p)" using Coll_into_countable_rel by simp
  show "\<exists>d\<in>surj_dense(x). d \<preceq> p"
  proof -
    from \<open>p \<in> Coll\<close>
    have "domain(p) \<subseteq> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "p\<in>M"
      using transM[of _ Coll] domain_of_fun
      by (auto del:Fn_relD dest!:Fn_relD del:domainE)
    moreover from \<open>countable\<^bsup>M\<^esup>(p)\<close>
    have "domain(p) \<subseteq> {fst(x) . x \<in> p }" by (auto intro!: rev_bexI)
    moreover from calculation
    have "{ fst(x) . x \<in> p } \<in> M"
      using lam_replacement_fst[THEN lam_replacement_imp_strong_replacement]
      by (auto simp flip:setclass_iff intro!:RepFun_closed dest:transM)
    moreover from calculation and \<open>countable\<^bsup>M\<^esup>(p)\<close>
    have "countable\<^bsup>M\<^esup>({fst(x) . x \<in> p })"
      using cardinal_rel_RepFun_le lam_replacement_fst
        countable_rel_iff_cardinal_rel_le_nat[THEN iffD1, THEN [2] le_trans, of _ p]
      by (rule_tac countable_rel_iff_cardinal_rel_le_nat[THEN iffD2]) simp_all
    moreover from calculation
    have "countable\<^bsup>M\<^esup>(domain(p))"
      using uncountable_rel_not_subset_countable_rel[of "{fst(x) . x \<in> p }" "domain(p)"]
      by auto
    ultimately
    obtain \<alpha> where "\<alpha> \<notin> domain(p)" "\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
      using lt_cardinal_rel_imp_not_subset[of "domain(p)" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"]
        Ord_Aleph_rel countable_iff_le_rel_Aleph_rel_one[THEN iffD1,
          THEN lesspoll_cardinal_lt_rel, of "domain(p)"]
        cardinal_rel_idem by auto
    moreover note assms
    moreover from calculation and \<open>p \<in> Coll\<close>
    have "cons(\<langle>\<alpha>,x\<rangle>, p) \<in> Coll" "x\<in>M" "cons(\<langle>\<alpha>,x\<rangle>, p) \<preceq> p"
      using InfCard_rel_Aleph_rel
      by (auto del:Fnle_relI intro!: cons_in_Fn_rel Fnle_relI dest:transM)
    ultimately
    show ?thesis by blast
  qed
qed

lemma surj_dense_closed[intro,simp]:
  "x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2 \<Longrightarrow> surj_dense(x) \<in> M"
  using separation_in_range transM[of x] by simp

lemma reals_sub_image_f_G:
  assumes "x\<in>\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
  shows "\<exists>\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>. f\<^bsub>G\<^esub> ` \<alpha> = x"
proof -
  from assms
  have "dense(surj_dense(x))" using dense_surj_dense by simp
  with \<open>x \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2\<close>
  obtain p where "p\<in>surj_dense(x)" "p\<in>G"
    using generic[THEN M_generic_denseD, of "surj_dense(x)"]
    by blast
  then
  show ?thesis
    using succ_omega_closed_Coll f_G_funtype function_apply_equality[of _ x f_G]
      succ_omega_closed_imp_no_new_reals[symmetric]
    by (auto, rule_tac bexI) (auto simp:Pi_def)
qed

lemma f_G_surj_Aleph_rel1_reals: "f\<^bsub>G\<^esub> \<in> surj\<^bsup>M[G]\<^esup>(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
  using Aleph_rel_sub_closed
proof (intro ext.mem_surj_abs[THEN iffD2])
  show "f\<^bsub>G\<^esub> \<in> surj(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>, \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2)"
    unfolding surj_def
  proof (intro ballI CollectI impI)
    show "f\<^bsub>G\<^esub> \<in> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<rightarrow> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
      using f_G_funtype G_in_MG ext.nat_into_M f_G_in_MG by simp
    fix x
    assume "x \<in> \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
    then
    show "\<exists>\<alpha>\<in>\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>. f\<^bsub>G\<^esub> ` \<alpha> = x"
      using reals_sub_image_f_G succ_omega_closed_Coll
        f_G_funtype succ_omega_closed_imp_no_new_reals by simp
  qed
qed simp_all

lemma continuum_rel_le_Aleph1_extension:
  includes G_generic1_lemmas
  shows "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> \<in> M[G]" "Ord(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
    using Card_rel_is_Ord by auto
  moreover from this
  have "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2 \<lesssim>\<^bsup>M[G]\<^esup> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    using ext.surj_rel_implies_inj_rel[OF f_G_surj_Aleph_rel1_reals]
      f_G_in_MG unfolding lepoll_rel_def by auto
  with \<open>Ord(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)\<close>
  have "|\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2|\<^bsup>M[G]\<^esup> \<le> |\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M[G]\<^esup>"
    using  M_subset_MG[OF one_in_G, OF generic] Aleph_rel_closed[of 1]
    by (rule_tac ext.lepoll_rel_imp_cardinal_rel_le) simp_all
  ultimately
  have "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> |\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>|\<^bsup>M[G]\<^esup>"
    using ext.lepoll_rel_imp_cardinal_rel_le[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"]
      ext.Aleph_rel_zero succ_omega_closed_Coll
      succ_omega_closed_imp_Aleph_1_preserved
    unfolding cexp_rel_def by simp
  then
  show "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>" by simp
qed

theorem CH: "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
  using continuum_rel_le_Aleph1_extension ext.Aleph_rel_succ[of 0]
    ext.Aleph_rel_zero ext.csucc_rel_le[of "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>" \<omega>]
    ext.Card_rel_cexp_rel ext.cantor_cexp_rel[of \<omega>] ext.Card_rel_nat
    le_anti_sym
  by auto

end \<comment> \<open>\<^locale>\<open>collapse_generic4\<close>\<close>

subsection\<open>Models of fragments of $\ZFC + \CH$\<close>

theorem ctm_of_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZC \<union> {\<cdot>Replacement(p)\<cdot> . p \<in> overhead}"
    "\<Phi> \<subseteq> formula" "M \<Turnstile> { \<cdot>Replacement(ground_repl_fm(\<phi>))\<cdot> . \<phi> \<in> \<Phi>}"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZC \<union> {\<cdot>CH\<cdot>} \<union> { \<cdot>Replacement(\<phi>)\<cdot> . \<phi> \<in> \<Phi>} \<and>
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
  interpret M_ctm3_AC M enum by unfold_locales
  interpret forcing_data1 "Coll" "Colleq" 0 M enum
    using zero_in_Fn_rel[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"]
      zero_top_Fn_rel[of _ "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"]
      preorder_on_Fnle_rel[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2"]
      zero_lt_Aleph_rel1
    by unfold_locales simp_all
  obtain G where "M_generic(G)"
    using generic_filter_existence[OF one_in_P]
    by auto
  moreover from this
  interpret collapse_generic4 M enum G by unfold_locales
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> = 2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^bsup>M[G]\<^esup>,M[G]\<^esup>"
    using CH .
  then
  have "M[G], [] \<Turnstile> \<cdot>CH\<cdot>"
    using ext.is_ContHyp_iff
    by (simp add:ContHyp_rel_def)
  then
  have "M[G] \<Turnstile> ZC \<union> {\<cdot>CH\<cdot>}"
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
    by (rule_tac x="M[G]" in exI,blast)
qed

corollary ctm_ZFC_imp_ctm_CH:
  assumes
    "M \<approx> \<omega>" "Transset(M)" "M \<Turnstile> ZFC"
  shows
    "\<exists>N.
      M \<subseteq> N \<and> N \<approx> \<omega> \<and> Transset(N) \<and> N \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>} \<and>
      (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> (\<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N))"
proof -
  from assms
  have "\<exists>N.
      M \<subseteq> N \<and>
        N \<approx> \<omega> \<and>
        Transset(N) \<and>
        N \<Turnstile> ZC \<and> N \<Turnstile> {\<cdot>CH\<cdot>} \<and> N \<Turnstile> {\<cdot>Replacement(x)\<cdot> . x \<in> formula} \<and> (\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)"
    using ctm_of_CH[of M formula] satT_ZFC_imp_satT_ZC[of M]
      satT_mono[OF _ ground_repl_fm_sub_ZFC, of M]
      satT_mono[OF _ ZF_replacement_overhead_sub_ZFC, of M]
      satT_mono[OF _ ZF_replacement_fms_sub_ZFC, of M]
    by (simp add: satT_Un_iff)
  then
  obtain N where "N \<Turnstile> ZC" "N \<Turnstile> {\<cdot>CH\<cdot>}" "N \<Turnstile> {\<cdot>Replacement(x)\<cdot> . x \<in> formula}"
    "M \<subseteq> N" "N \<approx> \<omega>" "Transset(N)" "(\<forall>\<alpha>. Ord(\<alpha>) \<longrightarrow> \<alpha> \<in> M \<longleftrightarrow> \<alpha> \<in> N)"
    by auto
  moreover from this
  have "N \<Turnstile> ZFC"
    using satT_ZC_ZF_replacement_imp_satT_ZFC
    by auto
  moreover from this and \<open>N \<Turnstile> {\<cdot>CH\<cdot>}\<close>
  have "N \<Turnstile> ZFC \<union> {\<cdot>CH\<cdot>}"
    using satT_ZC_ZF_replacement_imp_satT_ZFC
    by auto
  ultimately
  show ?thesis
    by auto
qed

end