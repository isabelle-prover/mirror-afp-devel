theory Kruskal_New
imports Almost_Full_Relations
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

inductive emb for P
where
  arg: "\<lbrakk>(f, m) \<in> F; length ts = m; \<forall>t\<in>set ts. t \<in> terms; t \<in> set ts\<rbrakk> \<Longrightarrow> emb P t (mk f ts)" |
  list_hembeq: "\<lbrakk>(f, m) \<in> F; (g, n) \<in> F; P (f, m) (g, n); length ss = m; length ts = n;
    \<forall>s \<in> set ss. s \<in> terms; \<forall>t \<in> set ts. t \<in> terms;
    list_hembeq (emb P) ss ts\<rbrakk> \<Longrightarrow> emb P (mk f ss) (mk g ts)" |
  trans: "\<lbrakk>emb P s t; emb P t u\<rbrakk> \<Longrightarrow> emb P s u"
monos list_hembeq_mono

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
        with `i < j` and emb have *: "?P (m i) (s (k + (j - n)))" by (auto simp: m'_less m'_geq)
        with args obtain l where "l \<ge> n" and "s (k + (j - n)) \<in> set (a l)" by blast
        from emb.arg [OF sig [of l] _ a_terms [of l] this(2), of P]
          have "?P (s (k + (j - n))) (m l)" by (simp add: m)
        with * have "?P (m i) (m l)" by (auto elim: emb.trans)
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
      and lemb: "\<And>i j. i < j \<Longrightarrow> list_hembeq ?P (a (\<phi> i)) (a (\<phi> j))" by blast
  have roots: "\<And>i. r (\<phi> i) \<in> F" using terms [THEN terms_root] by (auto simp: r_def)
  then have "r \<circ> \<phi> \<in> SEQ F" by auto
  with assms have "good P (r \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j
    where "i < j" and "P (r (\<phi> i)) (r (\<phi> j))" by auto
  with lemb [OF `i < j`] have "?P (m (\<phi> i)) (m (\<phi> j))"
    using sig and arity and a_terms by (auto simp: m intro!: emb.list_hembeq)
  with less [OF `i < j`] and bad show False by blast
qed

end

(*
inductive tree_hembeq for P
where
  arg: "t \<in> set ts \<Longrightarrow> tree_hembeq P t (mk f ts)" |
  list_hembeq: "P\<^sup>=\<^sup>= f g \<Longrightarrow> list_hembeq (tree_hembeq P) ss ts \<Longrightarrow> tree_hembeq P (mk f ss) (mk g ts)" |
  trans: "tree_hembeq P s t \<Longrightarrow> tree_hembeq P t u \<Longrightarrow> tree_hembeq P s u" |
  ctxt: "tree_hembeq P s t \<Longrightarrow> tree_hembeq P (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
  monos list_hembeq_mono

definition "trees A = terms (A \<times> UNIV)"

lemma trees_subset:
  "trees A \<subseteq> terms (A \<times> UNIV)" by (auto simp: trees_def)

lemma emb_imp_tree_hembeq:
  assumes "emb (A \<times> UNIV) (prod_le P (\<lambda>_ _. True)) s t"
  shows "tree_hembeq P s t"
  using assms
  apply (induct)
  using list_hembeq_mono [of _ "tree_hembeq P", of "\<lambda>s t. Q s t \<and> tree_hembeq P s t" for Q]
  by (auto intro: tree_hembeq.intros simp: prod_le_def)

lemma almost_full_on_trees:
  assumes "almost_full_on P A"
  shows "almost_full_on (tree_hembeq P) (trees A)"
apply (rule almost_full_on_mono [of _ _ "emb (A \<times> UNIV) (prod_le P (\<lambda>_ _. True))"])
apply (rule trees_subset)
apply (rule emb_imp_tree_hembeq, assumption)
apply (rule almost_full_on_terms [OF almost_full_on_Sigma [OF assms almost_full_on_UNIV]])
done
*)

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun root
where
  "root (Fun f ts) = (f, length ts)"

fun args
where
  "args (Fun f ts) = ts"

inductive_set gterms for F
where
  "(f, n) \<in> F \<Longrightarrow> length ts = n \<Longrightarrow> \<forall>s \<in> set ts. s \<in> gterms F \<Longrightarrow> Fun f ts \<in> gterms F"

interpretation kruskal_term: kruskal size F Fun root args "gterms F" for F
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: gterms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_term.almost_full_on_terms

inductive_set terms
where
  "\<forall>t \<in> set ts. t \<in> terms \<Longrightarrow> Fun f ts \<in> terms"

interpretation kruskal_variadic: kruskal size UNIV Fun root args terms
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: terms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_variadic.almost_full_on_terms

datatype 'a exp = V 'a | C nat | Plus "'a exp" "'a exp"

datatype 'a symb = v 'a | c nat | p

fun mk
where
  "mk (v x) [] = V x" |
  "mk (c n) [] = C n" |
  "mk p [a, b] = Plus a b"

fun rt
where
  "rt (V x) = (v x, 0)" |
  "rt (C n) = (c n, 0)" |
  "rt (Plus a b) = (p, 2)"

fun ags
where
  "ags (V x) = []" |
  "ags (C n) = []" |
  "ags (Plus a b) = [a, b]"

inductive_set exps
where
  "V x \<in> exps" |
  "C n \<in> exps" |
  "a \<in> exps \<Longrightarrow> b \<in> exps \<Longrightarrow> Plus a b \<in> exps"

lemma [simp]:
  assumes "length ts = 2"
  shows "rt (mk p ts) = (p, 2)"
  using assms by (induct ts) (auto, case_tac ts, auto)

lemma [simp]:
  assumes "length ts = 2"
  shows "ags (mk p ts) = ts"
  using assms by (induct ts) (auto, case_tac ts, auto)

interpretation kruskal_exp: kruskal size
  "{(v x, 0) | x. True} \<union> {(c n, 0) | n. True} \<union> {(p, 2)}"
  mk rt ags exps
apply (unfold_locales)
apply auto
apply (case_tac [!] t rule: exps.cases)
by auto

thm kruskal_exp.almost_full_on_terms

end

