theory Wellfounded_Extra
  imports
    Main
    "Ordered_Resolution_Prover.Lazy_List_Chain"
begin


subsection \<open>Basic Results\<close>

subsubsection \<open>Minimal-element characterization of well-foundedness\<close>

lemma minimal_if_wf_on:
  assumes wf: "wf_on A R" and "B \<subseteq> A" and "B \<noteq> {}"
  shows "\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  using wf_on_iff_ex_minimal[THEN iffD1, rule_format, OF assms] .

lemma wfE_min':
  "wf R \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> (\<And>z. z \<in> Q \<Longrightarrow> (\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using wfE_min[of R _ Q] by blast

lemma wf_on_if_minimal:
  assumes "\<And>B. B \<subseteq> A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> \<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  shows "wf_on A R"
  using wf_on_iff_ex_minimal[THEN iffD2, rule_format, OF assms] .

lemma bex_rtrancl_min_element_if_wf_on:
  assumes wf: "wf_on A r" and x_in: "x \<in> A"
  shows "\<exists>y \<in> A. (y, x) \<in> r\<^sup>* \<and> \<not>(\<exists>z \<in> A. (z, y) \<in> r)"
  using wf
proof (induction x rule: wf_on_induct)
  case in_set
  thus ?case
    using x_in by metis
next
  case (less x)
  thus ?case
    by (metis rtrancl.rtrancl_into_rtrancl rtrancl.rtrancl_refl)
qed

lemma bex_rtransclp_min_element_if_wfp_on: "wfp_on A R \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>y\<in>A. R\<^sup>*\<^sup>* y x \<and> \<not> (\<exists>z\<in>A. R z y)"
  by (rule bex_rtrancl_min_element_if_wf_on[to_pred])

text \<open>Well-foundedness of the empty relation\<close>

definition inv_imagep_on :: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "inv_imagep_on A R f = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> R (f x) (f y))"

lemma wfp_on_inv_imagep:
  assumes wf: "wfp_on (f ` A) R"
  shows "wfp_on A (inv_imagep R f)"
  unfolding wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix B assume "B \<subseteq> A" and "B \<noteq> {}"
  hence "\<exists>z\<in>f ` B. \<forall>y. R y z \<longrightarrow> y \<notin> f ` B"
    using wf[unfolded wfp_on_iff_ex_minimal, rule_format, of "f ` B"] by blast
  thus "\<exists>z\<in>B. \<forall>y. inv_imagep R f y z \<longrightarrow> y \<notin> B"
    unfolding inv_imagep_def
    by (metis image_iff)
qed

definition lex_prodp where
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> R\<^sub>A (fst x) (fst y) \<or> fst x = fst y \<and> R\<^sub>B (snd x) (snd y)"

lemma lex_prodp_lex_prod_iff[pred_set_conv]:
  "lex_prodp R\<^sub>A R\<^sub>B x y \<longleftrightarrow> (x, y) \<in> lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma lex_prod_lex_prodp_iff:
  "lex_prod {(x, y). R\<^sub>A x y} {(x, y). R\<^sub>B x y} = {(x, y). lex_prodp R\<^sub>A R\<^sub>B x y}"
  unfolding lex_prodp_def lex_prod_def by auto

lemma wfp_on_lex_prodp: "wfp_on A R\<^sub>A \<Longrightarrow> wfp_on B R\<^sub>B \<Longrightarrow> wfp_on (A \<times> B) (lex_prodp R\<^sub>A R\<^sub>B)"
  using wf_on_lex_prod[of A _ B _, to_pred, unfolded lex_prod_lex_prodp_iff, to_pred] .

corollary wfp_lex_prodp: "wfp R\<^sub>A \<Longrightarrow> wfp R\<^sub>B \<Longrightarrow> wfp (lex_prodp R\<^sub>A R\<^sub>B)"
  using wfp_on_lex_prodp[of UNIV _ UNIV, simplified] .

lemma wfp_on_sup_if_convertible_to_wfp:
  includes lattice_syntax
  assumes
    wf_S: "wfp_on A S" and
    wf_Q: "wfp_on (f ` A) Q" and
    convertible_R: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q (f x) (f y)" and
    convertible_S: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> S x y \<Longrightarrow> Q (f x) (f y) \<or> f x = f y"
  shows "wfp_on A (R \<squnion> S)"
proof (rule wfp_on_if_convertible_to_wfp_on)
  show "wfp_on ((\<lambda>x. (f x, x)) ` A) (lex_prodp Q S)"
  proof (rule wfp_on_subset)
    show "wfp_on (f ` A \<times> A) (lex_prodp Q S)"
      by (rule wfp_on_lex_prodp[OF wf_Q wf_S])
  next
    show "(\<lambda>x. (f x, x)) ` A \<subseteq> f ` A \<times> A"
      by auto
  qed
next
  fix x y
  show "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (R \<squnion> S) x y \<Longrightarrow> lex_prodp Q S (f x, x) (f y, y)"
    using convertible_R convertible_S
    by (auto simp add: lex_prodp_def)
qed

lemma chain_lnth_rtranclp:
  assumes
    chain: "Lazy_List_Chain.chain R xs" and
    len: "enat j < llength xs"
  shows "R\<^sup>*\<^sup>* (lhd xs) (lnth xs j)"
  using len
proof (induction j)
  case 0
  from chain obtain x xs' where "xs = LCons x xs'"
    by (auto elim: chain.cases)
  thus ?case
    by simp
next
  case (Suc j)
  then show ?case
    by (metis Suc_ile_eq chain chain_lnth_rel less_le_not_le rtranclp.simps)
qed

lemma chain_conj_rtranclpI:
  fixes xs :: "'a llist"
  assumes "Lazy_List_Chain.chain (\<lambda>x y. R x y) (LCons init xs)"
  shows "Lazy_List_Chain.chain (\<lambda>x y. R x y \<and> R\<^sup>*\<^sup>* init x) (LCons init xs)"
proof (intro lnth_rel_chain allI impI conjI)
  show "\<not> lnull (LCons init xs)"
    by simp
next
  fix j
  assume hyp: "enat (j + 1) < llength (LCons init xs)"

  from hyp show "R (lnth (LCons init xs) j) (lnth (LCons init xs) (j + 1))"
    using assms[THEN chain_lnth_rel, of j] by simp

  from hyp show "R\<^sup>*\<^sup>* init (lnth (LCons init xs) j)"
    using assms[THEN chain_lnth_rtranclp, of j]
    by (simp add: Suc_ile_eq)
qed

lemma rtranclp_implies_ex_lfinite_chain:
  assumes run: "R\<^sup>*\<^sup>* x\<^sub>0 x"
  shows "\<exists>xs. lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs) \<and> llast (LCons x\<^sub>0 xs) = x"
  using run
proof (induction x rule: rtranclp_induct)
  case base
  then show ?case
    by (meson chain.chain_singleton lfinite_code(1) llast_singleton)
next
  case (step y z)
  from step.IH obtain xs where
    "lfinite xs" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)" and "llast (LCons x\<^sub>0 xs) = y"
    by auto
  let ?xs = "lappend xs (LCons z LNil)"
  show ?case
  proof (intro exI conjI)
    show "lfinite ?xs"
      using \<open>lfinite xs\<close> by simp
  next
    show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 ?xs)"
      using \<open>chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)\<close> \<open>llast (LCons x\<^sub>0 xs) = y\<close>
        chain.chain_singleton chain_lappend step.hyps(1) step.hyps(2)
      by fastforce
  next
    show "llast (LCons x\<^sub>0 ?xs) = z"
      by (simp add: \<open>lfinite xs\<close> llast_LCons)
  qed
qed

lemma chain_conj_rtranclpD:
  fixes xs :: "'a llist"
  assumes inf: "\<not> lfinite xs" and chain: "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
  shows "\<exists>ys. lfinite ys \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs) \<and> lhd (lappend ys xs) = x\<^sub>0"
  using chain
proof (cases "\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y" xs rule: chain.cases)
  case (chain_singleton x)
  with inf have False
    by simp
  thus ?thesis ..
next
  case (chain_cons xs' x)
  hence "R\<^sup>*\<^sup>* x\<^sub>0 x"
    by auto
  thus ?thesis
  proof (cases R x\<^sub>0 x rule: rtranclp.cases)
    case rtrancl_refl
    then show ?thesis
      using chain local.chain_cons(1) by force
  next
    case (rtrancl_into_rtrancl x\<^sub>n)
    then obtain ys where
      lfin_ys: "lfinite ys" and
      chain_ys: "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 ys)" and
      llast_ys: "llast (LCons x\<^sub>0 ys) = x\<^sub>n"
      by (auto dest: rtranclp_implies_ex_lfinite_chain)
    show ?thesis
    proof (intro exI conjI)
      show "lfinite (LCons x\<^sub>0 ys)"
        using lfin_ys
        by simp
    next
      have "R (llast (LCons x\<^sub>0 ys)) (lhd xs)"
        using rtrancl_into_rtrancl(2) chain_cons(1) llast_ys
        by simp
      moreover have "R\<^sup>*\<^sup>* x\<^sub>0 (llast (LCons x\<^sub>0 ys))"
        using rtrancl_into_rtrancl(1,2)
        using lappend_code(2)[of x\<^sub>0 ys xs]
          lhd_LCons[of x\<^sub>0 "(lappend ys xs)"] local.chain_cons(1)
        using llast_ys
        by fastforce
      ultimately show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend (LCons x\<^sub>0 ys) xs)"
        using chain_lappend[OF chain_ys chain]
        by metis
    next
      show "lhd (lappend (LCons x\<^sub>0 ys) xs) = x\<^sub>0"
        by simp
    qed 
  qed
qed

lemma wfp_on_rtranclp_conversep_iff_no_infinite_down_chain_llist:
  fixes R x\<^sub>0
  shows "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse> \<longleftrightarrow> (\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs))"
proof (rule iffI)
  assume "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse>"
  hence "wfp (\<lambda>z y. R\<inverse>\<inverse> z y \<and> z \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x} \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    using wfp_on_iff_wfp by blast
  hence "wfp (\<lambda>z y. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y)"
    by (auto elim: wfp_on_antimono_strong)
  hence "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
    unfolding wfP_iff_no_infinite_down_chain_llist
    by (metis (no_types, lifting) Lazy_List_Chain.chain_mono conversepI)
  hence "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    by (meson lfinite_LCons)
  thus "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs)"
    using chain_conj_rtranclpI
    by fastforce
next
  assume "\<nexists>xs. \<not> lfinite xs \<and> Lazy_List_Chain.chain R (LCons x\<^sub>0 xs)"
  hence no_inf_chain: "\<nexists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    by (metis (mono_tags, lifting) Lazy_List_Chain.chain_mono)
  have "\<nexists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
  proof (rule notI, elim exE conjE)
    fix xs assume "\<not> lfinite xs" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) xs"
    then obtain ys where
      "lfinite ys" and "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs)" and "lhd (lappend ys xs) = x\<^sub>0"
    by (auto dest: chain_conj_rtranclpD)
    hence "\<exists>xs. \<not> lfinite xs \<and> chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 xs)"
    proof (intro exI conjI)
      show "\<not> lfinite (ltl (lappend ys xs))"
        using \<open>\<not> lfinite xs\<close> lfinite_lappend lfinite_ltl
        by blast
    next
      show "chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (LCons x\<^sub>0 (ltl (lappend ys xs)))"
        using \<open>chain (\<lambda>y z. R y z \<and> R\<^sup>*\<^sup>* x\<^sub>0 y) (lappend ys xs)\<close> \<open>lhd (lappend ys xs) = x\<^sub>0\<close>
          chain_not_lnull lhd_LCons_ltl
        by fastforce
    qed
    with no_inf_chain show False
      by argo
  qed
  hence "Wellfounded.wfP (\<lambda>z y. R y z \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    unfolding wfP_iff_no_infinite_down_chain_llist
    using Lazy_List_Chain.chain_mono by fastforce
  hence "wfp (\<lambda>z y. R\<inverse>\<inverse> z y \<and> z \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x} \<and> y \<in> {x. R\<^sup>*\<^sup>* x\<^sub>0 x})"
    by (auto elim: wfp_on_antimono_strong)
  thus "wfp_on {x. R\<^sup>*\<^sup>* x\<^sub>0 x} R\<inverse>\<inverse>"
    unfolding wfp_on_iff_wfp[of "{x. R\<^sup>*\<^sup>* x\<^sub>0 x}" "R\<inverse>\<inverse>"] by argo
qed

end
