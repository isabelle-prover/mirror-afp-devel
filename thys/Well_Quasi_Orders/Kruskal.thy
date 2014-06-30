(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem *}

theory Kruskal
imports Well_Quasi_Orders
begin

locale kruskal =
  size size for size :: "'a \<Rightarrow> nat" +
  fixes F :: "('b \<times> nat) set"
    and mk :: "'b \<Rightarrow> 'a list \<Rightarrow> 'a"
    and root :: "'a \<Rightarrow> 'b \<times> nat"
    and args :: "'a \<Rightarrow> 'a list"
    and terms :: "'a set"
  assumes size_arg: "t \<in> terms \<Longrightarrow> s \<in> set (args t) \<Longrightarrow> size s < size t"
    and root_mk: "(f, length ts) \<in> F \<Longrightarrow> root (mk f ts) = (f, length ts)"
    and args_mk: "(f, length ts) \<in> F \<Longrightarrow> args (mk f ts) = ts"
    and mk_root_args: "t \<in> terms \<Longrightarrow> mk (fst (root t)) (args t) = t"
    and terms_root: "t \<in> terms \<Longrightarrow> root t \<in> F"
    and terms_arity: "t \<in> terms \<Longrightarrow> length (args t) = snd (root t)"
    and terms_args: "\<And>s. t \<in> terms \<Longrightarrow> s \<in> set (args t) \<Longrightarrow> s \<in> terms"
begin

lemma mk_inject [iff]:
  assumes "(f, length ss) \<in> F" and "(g, length ts) \<in> F"
  shows "mk f ss = mk g ts \<longleftrightarrow> f = g \<and> ss = ts"
proof -
  { assume "mk f ss = mk g ts"
    then have "root (mk f ss) = root (mk g ts)"
      and "args (mk f ss) = args (mk g ts)" by auto }
  show ?thesis
    using root_mk [OF assms(1)] and root_mk [OF assms(2)]
      and args_mk [OF assms(1)] and args_mk [OF assms(2)] by auto
qed

lemma wf_size:
  "wf {(x, y). size x < size y}"
proof -
  have "measure size = {(x, y). size x < size y}" by auto
  moreover have "wf (measure size)" by (rule wf_measure)
  ultimately show ?thesis by simp
qed

lemma wfp_on_size:
  "wfp_on (\<lambda>x y. size x < size y) A"
  using wf_size [to_pred, unfolded wfp_on_UNIV [symmetric]]
    and wfp_on_subset [of A UNIV] by blast

(*TODO: move*)
lemma reflclp_mono:
  assumes "\<And>x y. P x y \<longrightarrow> Q x y"
  shows "P\<^sup>=\<^sup>= x y \<longrightarrow> Q\<^sup>=\<^sup>= x y"
  using assms by auto

inductive emb for P
where
  arg: "\<lbrakk>(f, m) \<in> F; length ts = m; \<forall>t\<in>set ts. t \<in> terms; t \<in> set ts; (emb P)\<^sup>=\<^sup>= s t\<rbrakk>
    \<Longrightarrow> emb P s (mk f ts)" |
  list_emb: "\<lbrakk>(f, m) \<in> F; (g, n) \<in> F; P (f, m) (g, n); length ss = m; length ts = n;
    \<forall>s \<in> set ss. s \<in> terms; \<forall>t \<in> set ts. t \<in> terms; list_emb (emb P) ss ts\<rbrakk>
    \<Longrightarrow> emb P (mk f ss) (mk g ts)"
monos list_emb_mono  reflclp_mono

lemma almost_full_on_terms:
  assumes "almost_full_on P F"
  shows "almost_full_on (emb P) terms" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret mbs "\<lambda>s t. size s < size t" ?A
    by (unfold_locales) (auto simp: wfp_on_size)
  assume "\<not> ?thesis"
  from mbs' [OF this] obtain m
    where bad: "m \<in> BAD ?P"
    and min: "\<forall>g. (m, g) \<in> gseq \<longrightarrow> good ?P g" ..
  then have terms: "\<And>i. m i \<in> terms" by auto

  def r \<equiv> "\<lambda>i. root (m i)"
  def a \<equiv> "\<lambda>i. args (m i)"
  def S \<equiv> "\<Union>{set (a i) | i. True}"

  have m: "\<And>i. m i = mk (fst (r i)) (a i)" by (simp add: r_def a_def mk_root_args [OF terms])
  have lists: "\<forall>i. a i \<in> lists S" by (auto simp: a_def S_def)
  have arity: "\<And>i. length (a i) = snd (r i)"
    using terms_arity [OF terms] by (auto simp: r_def a_def)
  then have sig: "\<And>i. (fst (r i), length (a i)) \<in> F"
    using terms_root [OF terms] by (auto simp: a_def r_def)
  have a_terms: "\<And>i. \<forall>t \<in> set (a i). t \<in> terms" by (auto simp: a_def terms_args [OF terms])

  have "almost_full_on ?P S"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain s :: "nat \<Rightarrow> 'a"
      where S: "\<And>i. s i \<in> S" and bad_s: "bad ?P s" by (auto simp: almost_full_on_def)

    def n \<equiv> "LEAST n. \<exists>k. s k \<in> set (a n)"
    have "\<exists>n. \<exists>k. s k \<in> set (a n)" using S by (force simp: S_def)
    from LeastI_ex [OF this] obtain k
      where sk: "s k \<in> set (a n)" by (auto simp: n_def)
    have args: "\<And>k. \<exists>m \<ge> n. s k \<in> set (a m)"
      using S by (auto simp: S_def) (metis Least_le n_def)

    def m' \<equiv> "\<lambda>i. if i < n then m i else s (k + (i - n))"
    
    have m'_less: "\<And>i. i < n \<Longrightarrow> m' i = m i" by (simp add: m'_def)
    have m'_geq: "\<And>i. i \<ge> n \<Longrightarrow> m' i = s (k + (i - n))" by (simp add: m'_def)

    have "bad ?P m'"
    proof
      assume "good ?P m'"
      then obtain i j where "i < j" and emb: "?P (m' i) (m' j)" by auto
      { assume "j < n"
        with `i < j` and emb have "?P (m i) (m j)" by (auto simp: m'_less)
        with `i < j` and bad have False by blast }
      moreover
      { assume "n \<le> i"
        with `i < j` and emb have "?P (s (k + (i - n))) (s (k + (j - n)))"
          and "k + (i - n) < k + (j - n)" by (auto simp: m'_geq)
        with bad_s have False by auto }
      moreover
      { assume "i < n" and "n \<le> j"
        with `i < j` and emb have *: "?P\<^sup>=\<^sup>= (m i) (s (k + (j - n)))" by (auto simp: m'_less m'_geq)
        with args obtain l where "l \<ge> n" and **: "s (k + (j - n)) \<in> set (a l)" by blast
        from emb.arg [OF sig [of l] _ a_terms [of l] ** *]
          have "?P (m i) (m l)" by (simp add: m)
        moreover have "i < l" using `i < n` and `n \<le> l` by auto
        ultimately have False using bad by blast }
      ultimately show False using `i < j` by arith
    qed
    moreover have "(m, m') \<in> gseq"
    proof -
      have "m \<in> SEQ ?A" using terms by auto
      moreover have "m' \<in> SEQ ?A"
        using terms and S and terms_args [OF terms] by (auto simp: m'_def a_def S_def)
      moreover have "\<forall>i < n. m i = m' i" by (auto simp: m'_less)
      moreover have "size (m' n) < size (m n)"
        using sk and size_arg [OF terms, unfolded m]
        by (auto simp: m m'_geq root_mk [OF sig] args_mk [OF sig])
      ultimately show ?thesis by (auto simp: gseq_def)
    qed
    ultimately show False using min by blast
  qed
  from almost_full_on_lists [OF this, THEN almost_full_on_imp_homogeneous_subseq, OF lists]
    obtain \<phi> :: "nat \<Rightarrow> nat"
    where less: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
      and lemb: "\<And>i j. i < j \<Longrightarrow> list_emb ?P (a (\<phi> i)) (a (\<phi> j))" by blast
  have roots: "\<And>i. r (\<phi> i) \<in> F" using terms [THEN terms_root] by (auto simp: r_def)
  then have "r \<circ> \<phi> \<in> SEQ F" by auto
  with assms have "good P (r \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j
    where "i < j" and "P (r (\<phi> i)) (r (\<phi> j))" by auto
  with lemb [OF `i < j`] have "?P (m (\<phi> i)) (m (\<phi> j))"
    using sig and arity and a_terms by (auto simp: m intro!: emb.list_emb)
  with less [OF `i < j`] and bad show False by blast
qed

inductive_cases
  emb_mk2 [consumes 1, case_names arg list_emb]: "emb P s (mk g ts)"

lemma emb_trans:
  assumes trans: "\<And>f g h. f \<in> F \<Longrightarrow> g \<in> F \<Longrightarrow> h \<in> F \<Longrightarrow> P f g \<Longrightarrow> P g h \<Longrightarrow> P f h"
  assumes "emb P s t" and "emb P t u"
  shows "emb P s u"
using assms(3, 2)
proof (induct arbitrary: s)
  case (arg f m ts v)
  then show ?case by (auto intro: emb.arg)
next
  case (list_emb f m g n ss ts)
  note IH = this
  from `emb P s (mk f ss)`
    show ?case
  proof (cases rule: emb_mk2)
    case arg
    then show ?thesis using IH by (auto elim!: list_emb_set intro: emb.arg)
  next
    case list_emb
    then show ?thesis using IH by (auto intro: emb.intros dest: trans list_emb_trans_right)
  qed
qed

lemma transp_on_emb:
  assumes "transp_on P F"
  shows "transp_on (emb P) terms"
  using assms and emb_trans [of P] unfolding transp_on_def by blast

lemma  kruskal:
  assumes "wqo_on P F"
  shows "wqo_on (emb P) terms"
  using almost_full_on_terms [of P] and assms by (metis transp_on_emb wqo_on_def)

end

end

