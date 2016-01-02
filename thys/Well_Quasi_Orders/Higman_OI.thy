(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>A Proof of Higman's Lemma via Open Induction\<close>

theory Higman_OI
imports
  "../Open_Induction/Open_Induction"
  Minimal_Elements
  Almost_Full
begin

subsection \<open>Some facts about the suffix relation\<close>

lemma wfp_on_suffix:
  "wfp_on suffix A"
by (rule wfp_on_mono [OF subset_refl, of _ _ "measure_on length A"])
   (auto simp: suffix_def)

lemma transp_on_suffix:
  "transp_on suffix A"
by (force simp: suffix_def transp_on_def)

lemma irreflp_on_suffix:
  "irreflp_on suffix A"
by (auto simp: irreflp_on_def suffix_def)

lemma antisymp_on_suffix:
  "antisymp_on suffix A"
by (auto simp: antisymp_on_def suffix_def)


subsection \<open>Lexicographic Order on Infinite Sequences\<close>

definition "LEX P f g \<longleftrightarrow> (\<exists>i::nat. P (f i) (g i) \<and> (\<forall>j<i. f j = g j))"
abbreviation "LEXEQ P \<equiv> (LEX P)\<^sup>=\<^sup>="

lemma antisymp_on_LEX:
  assumes "irreflp_on P A" and "antisymp_on P A"
  shows "antisymp_on (LEX P) (SEQ A)"
proof
  fix f g assume SEQ: "f \<in> SEQ A" "g \<in> SEQ A" and "LEX P f g" and "LEX P g f"
  then obtain i j where "P (f i) (g i)" and "P (g j) (f j)"
    and "\<forall>k<i. f k = g k" and "\<forall>k<j. g k = f k" by (auto simp: LEX_def)
  then have "P (f (min i j)) (f (min i j))"
    using assms(2) and SEQ by (cases "i = j") (auto simp: antisymp_on_def min_def, force)
  with assms(1) and SEQ show  "f = g" by (auto simp: irreflp_on_def)
qed

lemma LEX_trans:
  assumes "transp_on P A" and "f \<in> SEQ A" and "g \<in> SEQ A" and "h \<in> SEQ A"
    and "LEX P f g" and "LEX P g h"
  shows "LEX P f h"
using assms by (auto simp: LEX_def transp_on_def) (metis less_trans linorder_neqE_nat)

lemma qo_on_LEXEQ:
  assumes "transp_on P A"
  shows "qo_on (LEXEQ P) (SEQ A)"
using assms
apply (auto simp: qo_on_def reflp_on_def)
apply (subst transp_on_def)
apply (auto dest: LEX_trans)
done

context minimal_element
begin

lemma LEX_chain_on_eq_upto_imp_ith_chain_on:
  assumes "chain_on (LEX P) (eq_upto C f i) (SEQ A)"
  shows "chain_on P (ith (eq_upto C f i) i) A"
using assms
proof -
  { fix x y assume "x \<in> ith (eq_upto C f i) i" and "y \<in> ith (eq_upto C f i) i"
      and "\<not> P x y" and "y \<noteq> x"
    then obtain g h where *: "g \<in> eq_upto C f i" "h \<in> eq_upto C f i"
      and [simp]: "x = g i" "y = h i" and eq: "\<forall>j<i. g j = f j \<and> h j = f j"
      by (auto simp: ith_def eq_upto_def)
    with assms and \<open>y \<noteq> x\<close> have "LEX P g h \<or> LEX P h g" by (auto simp: chain_on_def)
    moreover
    { assume "LEX P g h"
      with eq and \<open>y \<noteq> x\<close> have "P x y" using assms and *
        by (auto simp: LEX_def)
           (metis SEQ_iff chain_on_imp_subset linorder_neqE_nat minimal subsetCE)
      with \<open>\<not> P x y\<close> have "P y x" .. }
    moreover
    { assume "LEX P h g"
      with eq and \<open>y \<noteq> x\<close> have "P y x" using assms and *
        by (auto simp: LEX_def)
           (metis SEQ_iff chain_on_imp_subset linorder_neqE_nat minimal subsetCE) }
    ultimately have "P y x" by (auto simp: chain_on_def LEX_def) }
  then show ?thesis using assms by (auto simp: chain_on_def) blast
qed

lemma lb_LEX_minlex:
  assumes chain: "chain_on (LEX P) C (SEQ A)"
    and *: "C \<subseteq> SEQ A" "C \<noteq> {}"
  shows "lb (LEX P) C (minlex C)"
proof -
  { fix f assume "f \<in> C" and "f \<noteq> minlex C"
    then have neq: "\<exists>i. f i \<noteq> minlex C i" by auto
    def i \<equiv> "LEAST i. f i \<noteq> minlex C i"
    from LeastI_ex [OF neq, folded i_def]
      and not_less_Least [where P = "\<lambda>i. f i \<noteq> minlex C i", folded i_def]
      have neq: "f i \<noteq> minlex C i" and eq: "\<forall>j<i. f j = minlex C j" by auto
    then have "f \<in> eq_upto C (minlex C) i" using \<open>f \<in> C\<close> by auto
    then have fi: "f i \<in> ith (eq_upto C (minlex C) i) i" (is "f i \<in> ?A") by blast
    moreover have "f i \<in> A" using \<open>f \<in> C\<close> and \<open>C \<subseteq> SEQ A\<close> by auto
    ultimately have not_P: "\<not> P (f i) (minlex C i)"
      using minlex_minimal [OF *, of "f i" i] by blast
    have "chain_on (LEX P) (eq_upto C (minlex C) i) (SEQ A)"
      by (rule subchain_on [OF _ chain]) auto
    then have "chain_on P ?A A"
      by (simp add: LEX_chain_on_eq_upto_imp_ith_chain_on)
    moreover from minlex_mem [OF *] have "minlex C i \<in> ?A" by auto
    ultimately have "P (minlex C i) (f i)"
      using fi and not_P and neq by (force simp: chain_on_def)
    with eq have "LEX P (minlex C) f" by (auto simp: LEX_def) }
  then show ?thesis by (auto simp: lb_def)
qed

lemma glb_LEX_minlex:
  assumes "chain_on (LEX P) C (SEQ A)"
    and *: "C \<subseteq> SEQ A" "C \<noteq> {}"
  shows "glb (LEX P) C (minlex C)"
proof -
  have "C \<subseteq> SEQ A" using assms(1) by (auto simp: chain_on_def)
  then have "minlex C \<in> SEQ A" using \<open>C \<noteq> {}\<close> by (intro minlex_SEQ_mem)
  have "lb (LEX P) C (minlex C)" by (rule lb_LEX_minlex [OF assms])
  moreover
  { fix f assume lb: "lb (LEX P) C f" and "f \<noteq> minlex C"
    then have neq: "\<exists>i. f i \<noteq> minlex C i" by auto
    def i \<equiv> "LEAST i. f i \<noteq> minlex C i"
    from LeastI_ex [OF neq, folded i_def]
      and not_less_Least [where P = "\<lambda>i. f i \<noteq> minlex C i", folded i_def]
    have neq: "f i \<noteq> minlex C i" and eq: "\<forall>j<i. f j = minlex C j" by auto
    from eq_upto_minlex_non_empty [OF *] obtain h
      where "h \<in> eq_upto C (minlex C) (Suc i)" and "h \<in> C" by (auto simp: eq_upto_def)
    then have hi: "h i = minlex C i" and eq': "\<forall>j<i. h i = minlex C i" by (auto)
    with lb and \<open>h \<in> C\<close> have "LEXEQ P f h" by (auto simp: lb_def)
    with \<open>f \<noteq> minlex C\<close> and eq and eq' and hi and neq
      have "P (f i) (minlex C i)" apply (auto simp: LEX_def)
      by (metis SEQ_iff \<open>h \<in> eq_upto C (minlex C) (Suc i)\<close> \<open>minlex C \<in> SEQ A\<close> eq_uptoE less_Suc_eq linorder_neqE_nat minimal neq)
    with eq have "LEXEQ P f (minlex C)" by (auto simp: LEX_def) }
  ultimately show ?thesis by (auto simp: glb_def)
qed

(*Proposition 6*)
proposition dc_on_LEXEQ:
  "dc_on (LEXEQ P) (SEQ A)"
proof
  fix C assume "chain_on (LEXEQ P) C (SEQ A)" and "C \<noteq> {}"
  then have chain: "chain_on (LEX P) C (SEQ A)" by (auto simp: chain_on_def)
  then have "C \<subseteq> SEQ A" by (auto simp: chain_on_def)
  then have "minlex C \<in> SEQ A" using \<open>C \<noteq> {}\<close> by (intro minlex_SEQ_mem)
  have "glb (LEX P) C (minlex C)" by (rule glb_LEX_minlex [OF chain \<open>C \<subseteq> SEQ A\<close> \<open>C \<noteq> {}\<close>])
  then have "glb (LEXEQ P) C (minlex C)" by (auto simp: glb_def lb_def)
  with \<open>minlex C \<in> SEQ A\<close> show "\<exists>f \<in> SEQ A. glb (LEXEQ P) C f" by blast
qed

end

lemma open_on_good:
  "open_on (LEXEQ suffix) (good (list_emb P)) (SEQ (lists A))"
proof
  fix C assume chain: "chain_on (LEXEQ suffix) C (SEQ (lists A))" and ne: "C \<noteq> {}"
    and "\<exists>g \<in> SEQ (lists A). glb (LEXEQ suffix) C g \<and> good (list_emb P) g"
  then obtain g where g: "g \<in> SEQ (lists A)" and "glb (LEXEQ suffix) C g"
    and good: "good (list_emb P) g" by blast
  then have glb: "glb (LEX suffix) C g" by (auto simp: glb_def lb_def)
  interpret minimal_element suffix "lists A"
    by (unfold_locales) (intro transp_on_suffix wfp_on_suffix)+
  from chain have "chain_on (LEX suffix) C (SEQ (lists A))"
    and C: "C \<subseteq> SEQ (lists A)" by (auto simp: chain_on_def)
  note * = glb_LEX_minlex [OF this \<open>C \<noteq> {}\<close>]
  have "minlex C \<in> SEQ (lists A)" using \<open>C \<noteq> {}\<close>
    using \<open>C \<subseteq> SEQ (lists A)\<close> by (intro minlex_SEQ_mem)
  from glb_unique [OF _ g this glb *] and antisymp_on_LEX [OF irreflp_on_suffix antisymp_on_suffix]
    have [simp]: "minlex C = g" by auto
  from good obtain i j :: nat where "i < j" and "list_emb P (g i) (g j)" by (auto simp: good_def)
  moreover from eq_upto_minlex_non_empty [OF C ne, of "Suc j"]
    obtain f where "f \<in> eq_upto C g (Suc j)" by auto
  ultimately have "f \<in> C" and "list_emb P (f i) (f j)" by auto
  then show "\<exists>f \<in> C. good (list_emb P) f" using \<open>i < j\<close> by (auto simp: good_def)
qed

lemma higman:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_emb P) (lists A)"
proof
  interpret minimal_element suffix "lists A"
    by (unfold_locales) (intro transp_on_suffix wfp_on_suffix)+
  fix f presume "f \<in> SEQ (lists A)"
  with qo_on_LEXEQ [OF transp_on_suffix] dc_on_LEXEQ and open_on_good
    show "good (list_emb P) f"
  proof (induct rule: open_induct_on)
    case (less f)
    show ?case
    proof (cases "\<exists>i. f i = []")
      def h \<equiv> "\<lambda>i. hd (f i)"
      case False
      then have ne: "\<forall>i. f i \<noteq> []" by auto
      with \<open>f \<in> SEQ (lists A)\<close> have "\<forall>i. h i \<in> A" by (auto simp: h_def ne_lists)
      from almost_full_on_imp_homogeneous_subseq [OF assms this]
        obtain \<phi> :: "nat \<Rightarrow> nat" where mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
        and P: "\<And>i j. i < j \<Longrightarrow> P (h (\<phi> i)) (h (\<phi> j))" by blast
      def f' \<equiv> "\<lambda>i. if i < \<phi> 0 then f i else tl (f (\<phi> (i - \<phi> 0)))"
      have f': "f' \<in> SEQ (lists A)" using ne and \<open>f \<in> SEQ (lists A)\<close>
        by (auto simp: f'_def) (metis in_listsD list.set_sel(2))
      have "\<forall>i<\<phi> 0. f i = f' i" by (auto simp: f'_def)
      have [simp]: "\<And>i. i < \<phi> 0 \<Longrightarrow> f' i = f i" by (auto simp: f'_def)
      have [simp]: "\<And>i. \<phi> 0 \<le> i \<Longrightarrow> h (\<phi> (i - \<phi> 0)) # f' i = f (\<phi> (i - \<phi> 0))"
        using ne by (auto simp: f'_def h_def)
      moreover have "suffix (f' (\<phi> 0)) (f (\<phi> 0))" using ne by (auto simp: f'_def)
      ultimately have "LEX suffix f' f" by (auto simp: LEX_def)
      then have "strict (LEXEQ suffix) f' f"
        by (auto simp: LEX_def suffix_def)
           (metis append_assoc append_is_Nil_conv append_self_conv2 linorder_neqE_nat)
      from less(2) [OF f' this] have "good (list_emb P) f'" .
      then obtain i j :: nat where "i < j"
        and emb: "list_emb P (f' i) (f' j)" by (auto simp: good_def)
      moreover
      { assume "j < \<phi> 0"
        with \<open>i < j\<close> and emb have "good (list_emb P) f" by (auto simp: good_def) }
      moreover
      { assume i: "\<phi> 0 \<le> i"
        with \<open>i < j\<close> and P have "P (h (\<phi> (i - \<phi> 0))) (h (\<phi> (j - \<phi> 0)))" by auto
        with emb have "list_emb P (h (\<phi> (i - \<phi> 0)) # f' i) (h (\<phi> (j - \<phi> 0)) # f' j)" by auto
        then have "list_emb P (f (\<phi> (i - \<phi> 0))) (f (\<phi> (j - \<phi> 0)))" using i and \<open>i < j\<close> by auto
        moreover with i and \<open>i <j\<close> have "\<phi> (i - \<phi> 0) < \<phi> (j - \<phi> 0)" using mono by auto
        ultimately have "good (list_emb P) f" by (auto simp: good_def) }
      moreover
      { assume i: "i < \<phi> 0" and j: "\<phi> 0 \<le> j"
        with emb have "list_emb P (f i) (f' j)" by auto
        moreover have "f (\<phi> (j - \<phi> 0)) = h (\<phi> (j - \<phi> 0)) # f' j" using j by auto
        ultimately have "list_emb P (f i) (f (\<phi> (j - \<phi> 0)))" by auto
        moreover have "i < \<phi> (j - \<phi> 0)" using mono [of 0 "j - \<phi> 0"] and i and j by force
        ultimately have "good (list_emb P) f" by (auto simp: good_def) }
      ultimately show ?thesis by arith
    qed auto
  qed
qed blast

(*
definition "pretty P f \<longleftrightarrow>
  (\<exists>\<phi>::nat \<Rightarrow> nat. \<forall>i j::nat. i < j \<longrightarrow> \<phi> i < \<phi> j \<and> P (f (\<phi> i)) (f (\<phi> j)))"

definition "LESS P f g \<longleftrightarrow> LEX suffix f g \<and>
  (\<exists>h. (\<forall>i. list_emb P (h i) (h (Suc i))) \<and>
       (\<exists>\<phi>::nat \<Rightarrow> nat. \<forall>i. g (\<phi> i) = h i @ f i))"

lemma LESS_trans:
  assumes "f \<in> SEQ (lists A)" and "g \<in> SEQ (lists A)" and "h \<in> SEQ (lists A)"
    and "LESS P f g" and "LESS P g h"
  shows "LESS P f h"
using assms and LEX_trans [OF transp_on_suffix, of f "lists A" g h]
apply (auto simp: LESS_def)
sorry

lemma qo_on_LESS:
  "qo_on (LESS P)\<^sup>=\<^sup>= (SEQ (lists A))"
apply (auto simp: qo_on_def reflp_on_def transp_on_def)
using LESS_trans [of _ A _ _ P]
unfolding SEQ_iff by blast

lemma open_on_pretty:
  "open_on (LESS P)\<^sup>=\<^sup>= (pretty (list_emb P)) (SEQ (lists A))"
sorry

proposition dc_on_LESS:
  "dc_on (LESS P)\<^sup>=\<^sup>= (SEQ (lists A))"
proof
  fix C assume "chain_on (LESS P)\<^sup>=\<^sup>= C (SEQ (lists A))" and "C \<noteq> {}"
  then have chain: "chain_on (LESS P) C (SEQ (lists A))" by (auto simp: chain_on_def)
  then have "chain_on (LEXEQ suffix) C (SEQ (lists A))" by (auto simp: chain_on_def LESS_def)
  with dc_on_LEXEQ [OF transp_on_suffix wfp_on_suffix, unfolded dc_on_def, of "lists A"]
    and \<open>C \<noteq> {}\<close>  obtain f where "f \<in> SEQ (lists A)" and "glb (LEXEQ suffix) C f" by blast
  show "\<exists>f \<in> SEQ (lists A). glb (LESS P)\<^sup>=\<^sup>= C f" sorry
qed


lemma almost_full_alt_def:
  "almost_full_on P A \<longleftrightarrow> (\<forall>f \<in> SEQ A. pretty P f)"
proof
  assume *: "almost_full_on P A"
  show "\<forall>f \<in> SEQ A. pretty P f"
    using almost_full_on_imp_homogeneous_subseq [OF *] by (auto simp: pretty_def)
next
  assume "\<forall>f \<in> SEQ A. pretty P f"
  then show "almost_full_on P A"
    by (auto simp: almost_full_on_def pretty_def good_def SEQ_def) blast
qed


lemma higman:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_emb P) (lists A)"
proof (unfold almost_full_alt_def, intro ballI)
  fix f assume "f \<in> SEQ (lists A)"
  with qo_on_LESS dc_on_LESS open_on_pretty
  show "pretty (list_emb P) f"
  proof (induct rule: open_induct_on)
    case (1 f)
    then show ?case
    proof (cases "\<forall>i. \<exists>j>i. f j = []")
      case True
      then interpret infinitely_many "\<lambda>i. f i = []"
        using INFM_nat by (unfold_locales) blast
      obtain g :: "nat \<Rightarrow> nat"
        where "\<forall>i j. i < j \<longrightarrow> g i < g j" and "\<forall>i. f (g i) = []"
        using index_ordered_less index_p by blast 
      then show ?thesis unfolding pretty_def by (intro exI [of _ g]) auto
    next
      case False
      then obtain N where *: "\<forall>i\<ge>N. f i \<noteq> []"
        by auto (metis less_Suc_eq linorder_neqE_nat not_less)
      def h \<equiv> "\<lambda>i. hd (f (i + N))"
      with \<open>f \<in> SEQ (lists A)\<close> and * have "\<forall>i. h i \<in> A" by (auto simp: ne_lists)
      from almost_full_on_imp_homogeneous_subseq [OF assms this]
        obtain \<phi> :: "nat \<Rightarrow> nat" where **: "\<forall>i j. i < j \<longrightarrow> \<phi> i < \<phi> j \<and> P (h (\<phi> i)) (h (\<phi> j))" ..
      then obtain N' where N': "N' \<ge> N" "\<phi> N' \<ge> N" by (metis le_add2 less_le_trans mono_nat_linear_lb not_le) 
      def f' \<equiv> "\<lambda>i. if i < \<phi> N' then f i else tl (f (\<phi> (i - \<phi> N' + N')))"
      have "\<forall>i<\<phi> N'. f i = f' i" using N' by (auto simp: f'_def)
      moreover have "suffix (f' (\<phi> N')) (f (\<phi> N'))" using * and N' by (auto simp: f'_def)
      ultimately have "LEX suffix f' f" by (auto simp: LEX_def)
      moreover have "\<forall>i. list_emb P [h (\<phi> i)] [h (\<phi> (Suc i))]"
        using * and ** by (auto)
      moreover have "\<forall>i. f (\<phi> (i + N')) = [h (\<phi> i)] @ f' i"
        using * and ** and N' apply (auto simp: f'_def h_def)
      thm LESS_def
      show ?thesis sorry
    qed
  qed
qed
*)

end
