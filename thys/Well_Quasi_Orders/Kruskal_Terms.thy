(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem for Almost-Full Relations -- Infinite Version for Terms *}

theory Kruskal_Terms
imports
  Well_Quasi_Orders
  Kruskal_Auxiliaries
  Finite_Tree
  Multiset_Extension
begin

context finite_tree
begin

inductive
  term_hemb :: "('b \<times> nat) set \<Rightarrow> ('b \<times> nat \<Rightarrow> 'b \<times> nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for F :: "('b \<times> nat) set"
    and P :: "('b \<times> nat \<Rightarrow> 'b \<times> nat \<Rightarrow> bool)"
where
  term_hemb_base [intro]:
    "\<lbrakk>(f, n) \<in> F; length ts = n; \<forall>t\<in>set ts. t \<in> terms F; t \<in> set ts\<rbrakk> \<Longrightarrow> term_hemb F P t (mk f ts)" |
  term_hemb_sublisteq [intro]:
    "\<lbrakk>(f, n) \<in> F; (g, m) \<in> F; P (f, n) (g, m); length ss = n; length ts = m;
    \<forall>t\<in>set ss. t \<in> terms F; \<forall>t\<in>set ts. t \<in> terms F; sublisteq ss ts\<rbrakk> \<Longrightarrow>
      term_hemb F P (mk f ss) (mk g ts)" |
  term_hemb_trans [intro]: "\<lbrakk>term_hemb F P s t; term_hemb F P t u\<rbrakk> \<Longrightarrow> term_hemb F P s u" |
  term_hemb_ctxt [intro]:
    "\<lbrakk>term_hemb F P s t; (f, n) \<in> F; Suc (length (ss1@ss2)) = n; \<forall>t\<in>set (ss1@ss2). t \<in> terms F\<rbrakk> \<Longrightarrow>
      term_hemb F P (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"

abbreviation term_hembeq where
  "term_hembeq F P \<equiv> (term_hemb F P)\<^sup>=\<^sup>="

lemma term_hemb_imp_terms:
  assumes "term_hemb F P s t"
  shows "s \<in> terms F \<and> t \<in> terms F"
  using assms by (induct) force+

lemma term_hemb_size:
  assumes "term_hemb F P s t"
  shows "size s \<le> size t"
  using assms
  by (induct)
     (auto simp: less_imp_le [OF size_simp2] dest!: sublisteq_size term_hemb_imp_terms)

lemma term_hemb_subtree:
  assumes "u \<in> terms F" and "term_hemb F P s t" and "subtree t u"
  shows "term_hemb F P s u"
  using assms(3, 2, 1)
  by (induct) (auto iff: mk_terms_iff)

lemma subtree_imp_term_hemb:
  assumes "subtree s t" and "t \<in> terms F" shows "term_hemb F P s t"
  using assms by (induct) (auto iff: mk_terms_iff)

lemma term_hembeq_subtree:
  assumes "u \<in> terms F" and "term_hembeq F P s t" and "subtree t u"
  shows "term_hembeq F P s u"
  using assms and term_hemb_subtree [of u F P s t]
  by (auto intro: subtree_imp_term_hemb)

lemma term_hembeq_subtreeeq:
  assumes "u \<in> terms F" and "term_hembeq F P s t" and "subtreeeq t u"
  shows "term_hembeq F P s u"
  using assms and term_hembeq_subtree [of u F P s t]
  by (auto intro: subtree_imp_term_hemb)

lemma args_steps_imp_steps_term_hemb:
  assumes len: "length ss = length ts"
    and F: "(f, length ss) \<in> F"
    and terms: "\<forall>t\<in>set (ss@ts). t \<in> terms F"
    and args: "\<forall>i<length ss. (term_hemb F P)\<^sup>=\<^sup>= (ss ! i) (ts ! i)"
  shows "(term_hemb F P)\<^sup>*\<^sup>* (mk f ss) (mk f ts)" (is "?P (mk f ss) (mk f ts)")
proof (rule args_steps_imp_steps_gen_terms [OF _ F terms len])
  fix i
  assume "i < length ts" thus "?P (ss ! i) (ts ! i)" using args and len by auto
next
  fix s t and ss1 ss2 :: "'a list"
  assume "(f, Suc (length (ss1 @ ss2))) \<in> F"
    and "\<forall>t\<in>set (ss1@ss2). t \<in> terms F"
    and "term_hemb F P s t"
    and "length ts = Suc (length ss1 + length ss2)"
  then have "term_hemb F P (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    by (auto simp: len)
  then show "(term_hemb F P)\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))" by simp
qed

lemma term_hemb_rtranclp [simp]:
  shows "(term_hemb F P)\<^sup>*\<^sup>* s t = term_hembeq F P s t" (is "?l = ?r")
proof -
  {
    assume "?l"
    then have "?r" by (induct) auto
  }
  then show "?l = ?r" by auto
qed

lemma list_hembeq_term_hembeq_imp_sublisteq:
  assumes "list_hembeq (term_hembeq F P) xs zs"
    (is "list_hembeq ?P xs zs")
  shows "\<exists>ys. sublisteq ys zs \<and> length ys = length xs \<and>
    (\<forall>i<length xs. term_hembeq F P (xs ! i) (ys ! i))"
using assms
proof (induct)
  case (list_hembeq_Nil ys)
  thus ?case by auto
next
  case (list_hembeq_Cons xs zs z)
  then obtain ys where *: "sublisteq ys zs" and "length ys = length xs"
    and "\<forall>i<length xs. ?P\<^sup>=\<^sup>= (xs ! i) (ys ! i)" by auto
  moreover have "sublisteq ys (z # zs)" using * by auto
  ultimately show ?case by blast
next
  case (list_hembeq_Cons2 x z xs zs)
  then obtain ys where *: "sublisteq ys zs"
    and len: "length ys = length xs"
    and **: "\<forall>i<length xs. ?P\<^sup>=\<^sup>= (xs ! i) (ys ! i)" by auto
  let ?ys = "z # ys" and ?xs = "x # xs"
  from * have "sublisteq ?ys (z # zs)" by auto
  moreover have "length ?ys = length ?xs" using len by auto
  moreover have "\<forall>i<length ?xs. ?P\<^sup>=\<^sup>= (?xs ! i) (?ys ! i)"
  proof (intro allI impI)
    fix i
    assume i: "i < length ?xs"
    show "?P\<^sup>=\<^sup>= (?xs ! i) (?ys ! i)"
      using i and ** and `?P\<^sup>=\<^sup>= x z`
      by (cases i) (auto)
  qed
  ultimately show ?case by blast
qed

lemma term_hembeq_list_hembeq:
  assumes "P\<^sup>=\<^sup>= (f, length ss) (g, length ts)"
    and F: "(f, length ss) \<in> F" and G: "(g, length ts) \<in> F"
    and terms: "\<forall>t\<in>set (ss@ts). t \<in> terms F"
    and list: "list_hembeq (term_hembeq F P) ss ts"
  shows "term_hembeq F P (mk f ss) (mk g ts)"
proof -
  from list_hembeq_term_hembeq_imp_sublisteq [OF list]
    obtain us where sub: "sublisteq us ts" and len: "length ss = length us"
    and *: "\<forall>i<length ss. term_hembeq F P (ss ! i) (us ! i)" by auto
  from sublisteq_set_subset [OF sub]
    have "\<forall>t\<in>set (ss@us). t \<in> terms F" using terms by auto
  from args_steps_imp_steps_term_hemb [OF len F this *]
    have **: "term_hembeq F P (mk f ss) (mk f us)" by simp
  from `P\<^sup>=\<^sup>= (f, length ss) (g, length ts)`
    show ?thesis
  proof
    from sublisteq_set_subset [OF sub]
      have terms: "\<forall>t\<in>set (us@ts). t \<in> terms F" using terms by auto
    assume "P (f, length ss) (g, length ts)"
    with sub have "term_hemb F P (mk f us) (mk g ts)"
      using F and G and terms
      unfolding len by auto
    with ** show ?thesis by auto
  next
    assume "(f, length ss) = (g, length ts)"
    then have [simp]: "f = g" "length ss = length ts" by simp+
    with sublisteq_same_length [OF sub] and len
      have [simp]: "us = ts" by simp
    from ** show ?thesis by simp
  qed
qed

lemma term_hemb_reflclp_refl [simp]:
  assumes "t \<in> terms F"
  shows "term_hemb F (P\<^sup>=\<^sup>=) t t"
  using assms by (induct) auto

lemma term_hembeq_term_hemb_conv:
  assumes "t \<in> terms F"
  shows "term_hembeq F P s t = term_hemb F (P\<^sup>=\<^sup>=) s t" (is "?l = ?r")
proof
  assume "?r" then show "?l"
    by (induct) (auto dest: sublisteq_same_length)
next
  assume "?l"
  moreover {
    assume "term_hemb F P s t"
    then have "?r" by (induct) auto
  }
  ultimately show "?r" using assms by auto
qed

lemma terms_root_succs:
  "t \<in> terms F \<Longrightarrow> (root t, length (succs t)) \<in> F \<and> (\<forall>t\<in>set (succs t). t \<in> terms F)"
  unfolding mk_terms_iff [symmetric]
  by (induct rule: terms.induct) auto

lemma almost_full_on_terms:
  assumes "almost_full_on P F"
  shows "almost_full_on (term_hemb F P)\<^sup>=\<^sup>= (terms F)"
proof (rule ccontr)
  let ?A = "terms F"
  let ?P = "(term_hemb F P)\<^sup>=\<^sup>="
  interpret term_mbs: mbs subtree ?A
    by (unfold_locales)
       (auto intro: wfp_on_subtree_terms elim: subtree_trans)
  have refl: "reflp_on ?P ?A" by (auto simp: reflp_on_def)

  assume "\<not> ?thesis"
  then obtain f where "f \<in> term_mbs.BAD ?P"
    unfolding almost_full_on_def term_mbs.BAD_def by blast
  from term_mbs.mbs [OF this] obtain m where bad: "bad ?P m"
    and min: "term_mbs.minimal ?P m"
    and in_terms: "\<And>i. m i \<in> terms F"
    by (auto simp: term_mbs.minimal_def term_mbs.BAD_def)
  obtain r s where [simp]: "\<And>i. r i = root (m i)" "\<And>i. s i = succs (m i)" by force
  have [simp]: "\<And>i. mk (root (m i)) (succs (m i)) = m i" by (metis in_terms root_mk succs_mk terms.cases)

  {
    assume "\<exists>t \<phi>::nat seq. (\<forall>i. t i \<in> set (s (\<phi> i)) \<and> \<phi> i \<ge> \<phi> 0) \<and> bad ?P t"
    then obtain t and \<phi> :: "nat seq"
      where in_succs: "\<And>i. t i \<in> set (s (\<phi> i))"
      and ge: "\<And>i. \<phi> i \<ge> \<phi> 0"
      and "bad ?P t" by auto
    let ?n = "\<phi> 0"
    def c \<equiv> "\<lambda>i. if i < ?n then m i else t (i - ?n)"
    have [simp]: "\<And>i. i < ?n \<Longrightarrow> c i = m i" by (auto simp: c_def)
    have [simp]: "\<And>i. ?n \<le> i \<Longrightarrow> c i = t (i - ?n)" by (auto simp: c_def)
    have "bad ?P c"
    proof
      assume "good ?P c"
      then obtain i j where "i < j" and *: "?P (c i) (c j)" by (auto simp: good_def)
      {
        assume "j < ?n" with `i < j` and * have "?P (m i) (m j)" by simp
        with `i < j` and `bad ?P m` have False by (auto simp: good_def)
      } moreover {
        let ?i' = "i - ?n" and ?j' = "j - ?n"
        assume "?n \<le> i" with `i < j` and * have "?P (t ?i') (t ?j')" by simp
        moreover with `i < j` and `?n \<le> i` have "?i' < ?j'" by auto
        ultimately have False using `bad ?P t` by (auto simp: good_def)
      } moreover {
        let ?j' = "j - ?n"
        from in_succs have "t ?j' \<in> set (s (\<phi> ?j'))" by simp
        with in_succs_imp_subtree and in_terms
          have subtree: "subtreeeq (t ?j') (m (\<phi> ?j'))"
          by (auto dest!: terms_imp_trees)
        assume "i < ?n" and "?n \<le> j"
        with * have "?P (m i) (t ?j')" by auto
        with subtree have "?P (m i) (m (\<phi> ?j'))"
          using term_hembeq_subtreeeq and in_terms
          by blast
        moreover from ge [of "?j'"] and `i < ?n` have "i < \<phi> ?j'" by auto
        ultimately have False using `bad ?P m` by (auto simp: good_def)
      } ultimately show False by arith
    qed
    have "\<forall>i. c i \<in> terms F"
      using in_terms
      by (simp add: c_def) (metis `\<And>i. s i = succs (m i)` in_succs terms_root_succs)
    moreover have "\<forall>i<?n. c i = m i" by simp
    moreover have "subtree (c ?n) (m ?n)"
      using in_succs_imp_subtree and in_terms and in_succs
      by (fastforce dest!: terms_imp_trees)
    ultimately have "good ?P c"
      using min [unfolded term_mbs.BAD_def term_mbs.minimal_def term_mbs.gbseq_def]
      apply auto
      by (metis `\<forall>i<\<phi> 0. c i = m i` `subtree (c (\<phi> 0)) (m (\<phi> 0))`)
    with `bad ?P c` have False by blast
  }
  hence no_special_bad_seq: "\<not> (\<exists>t \<phi>. (\<forall>i. t i \<in> set (s (\<phi> i)) \<and> \<phi> 0 \<le> \<phi> i) \<and> bad ?P t)" by blast

  let ?R = "{(r i, length (s i)) | i. True}"
  let ?S = "{s i | i. True}"
  have "almost_full_on P ?R"
  proof -
    have "?R \<subseteq> F"
    proof
      fix x assume "x \<in> ?R"
      then obtain i where [simp]: "x = (r i, length (s i))" by auto
      from in_terms [of i] show "x \<in> F" by (cases "m i") (simp)
    qed
    from almost_full_on_subset [OF this assms] show ?thesis .
  qed
  moreover have "almost_full_on (list_hembeq ?P) ?S"
  proof -
    let ?S' = "\<Union>(set ` ?S)"
    have "almost_full_on ?P ?S'"
    proof
      have "?S' \<subseteq> terms F"
      proof
        fix x assume "x \<in> ?S'"
        then obtain i where "x \<in> set (s i)" by auto
        with in_succs_imp_subtree and in_terms
          have "subtreeeq x (m i)" by (auto dest!: terms_imp_trees)
        with in_terms [of i] show "x \<in> terms F"
          using subtreeeq_terms by blast
      qed
      from reflp_on_subset [OF this refl] have refl: "reflp_on ?P ?S'" .
      fix f :: "'a seq" assume "\<forall>i. f i \<in> ?S'"
      with bad_of_special_shape' [OF refl this] and no_special_bad_seq
        show "good ?P f" by blast
    qed
    moreover have "?S \<subseteq> lists ?S'" by auto
    ultimately show ?thesis
      using almost_full_on_lists [of ?P ?S']
        and almost_full_on_subset [of ?S "lists ?S'"]
        by blast
  qed
  ultimately
  have "almost_full_on (prod_le P (list_hembeq ?P)) (?R \<times> ?S)"
    by (rule almost_full_on_Sigma)
  moreover have "\<forall>i. ((r i, length (s i)), s i) \<in> (?R \<times> ?S)" by auto
  ultimately have "good (prod_le P (list_hembeq ?P)) (\<lambda>i. ((r i, length (s i)), s i))"
    by (auto simp: almost_full_on_def)
  then obtain i j where "i < j"
    and "prod_le P (list_hembeq ?P) ((r i, length (s i)), s i) ((r j, length (s j)), s j)"
    by (auto simp: good_def almost_full_on_def)
  then have "P\<^sup>=\<^sup>= (r i, length (s i)) (r j, length (s j))" and "list_hembeq ?P (s i) (s j)"
    by (auto simp: prod_le_def)
  moreover have "(r i, length (s i)) \<in> F" and "(r j, length (s j)) \<in> F"
      and "\<forall>t\<in>set (s i @ s j). t \<in> terms F"
      using terms_root_succs [OF in_terms] by auto
  ultimately have "?P (m i) (m j)"
    using term_hembeq_list_hembeq [of P "r i" "s i" "r j" "s j" F] by auto
  with `i < j` and `bad ?P m` show False by (auto simp: good_def)
qed

text {*Multiset of function symbol / arity pairs.*}
definition "funas_ms = rec (\<lambda>f ts N. {#(f, length ts)#} + N) {#} (\<lambda>t ts M N. M + N)"
definition "funas_list_ms = list_rec (\<lambda>f ts N. {#(f, length ts)#} + N) {#} (\<lambda>t ts M N. M + N)"

lemma terms_imp_trees_list:
  "(\<forall>t\<in>set ts. t \<in> terms F) \<Longrightarrow> ts \<in> trees_list (fst ` F)"
  by (induct ts) (auto dest: terms_imp_trees intro: trees_trees_list.intros)

lemma rec_simps_terms [simp]:
  assumes "(x, length ts) \<in> F"
    and "\<forall>t\<in>set ts. t \<in> terms F"
  shows "rec f g h (mk x ts) = f x ts (list_rec f g h ts)"
proof -
  from assms have "x \<in> fst ` F"
    and "ts \<in> trees_list (fst ` F)" by (force dest: terms_imp_trees_list)+
  then show ?thesis by simp
qed

lemma list_rec_simps_terms [simp]:
  assumes "t \<in> terms F"
    and "\<forall>t\<in>set ts. t \<in> terms F"
  shows "list_rec f g h (t # ts) = h t ts (rec f g h t) (list_rec f g h ts)"
proof -
  from assms have "t \<in> trees (fst ` F)"
    and "ts \<in> trees_list (fst ` F)" by (auto dest: terms_imp_trees_list terms_imp_trees)
  then show ?thesis by simp
qed

lemma funas_list_ms_Nil [simp]:
  "funas_list_ms [] = {#}"
  by (simp add: funas_list_ms_def)

lemma funas_ms [simp]:
  "(f, length ts) \<in> F \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow>
    funas_ms (mk f ts) = {#(f, length ts)#} + funas_list_ms ts"
  "t \<in> terms F \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow> funas_list_ms (t # ts) = funas_ms t + funas_list_ms ts"
  by (simp_all add: funas_ms_def funas_list_ms_def)

lemma listsum_map_funas_ms [simp]:
  assumes "\<forall>t\<in>set ts. t \<in> terms F"
  shows "listsum (map funas_ms ts) = funas_list_ms ts"
  using assms by (induct ts) (auto)

lemma funas_ms_simps:
  "(f, length ts) \<in> F \<Longrightarrow> \<forall>t\<in>set ts. t \<in> terms F \<Longrightarrow>
    funas_ms (mk f ts) = {#(f, length ts)#} + listsum (map funas_ms ts)"
  by (simp)

lemma listsum_map_funas_msD:
  assumes "x \<in># listsum (map funas_ms ts)"
  shows "\<exists>t\<in>set ts. x \<in># funas_ms t"
  using assms by (induct ts) auto

lemma funas_ms_imp_mem:
  assumes "t \<in> terms F"
    and "(f, n) \<in># funas_ms t"
  shows "(f, n) \<in> F"
  using assms
  by (induct t, auto simp del: funas_ms simp: funas_ms_simps dest: listsum_map_funas_msD)
     (metis (full_types) less_not_refl3)

lemma funas_list_ms_imp_mem:
  assumes "\<forall>t\<in>set ts. t \<in> terms F"
    and "(f, n) \<in># funas_list_ms ts"
  shows "(f, n) \<in> F"
  using assms by (induct ts) (auto simp: funas_ms_imp_mem)

lemma funas_ms_multisets:
  assumes "t \<in> terms F"
  shows "funas_ms t \<in> multisets F"
  using assms
proof (induct)
  fix f n ts
  assume "(f, n) \<in> F" and "length ts = n"
    and "\<forall>t\<in>set ts. t \<in> terms F \<and> funas_ms t \<in> multisets F"
  moreover then have "\<forall>t\<in>set ts. t \<in> terms F" by blast
  ultimately show "funas_ms (mk f ts) \<in> multisets F"
    by (auto simp: multisets_def dest: funas_list_ms_imp_mem)
qed

lemma funas_list_ms_multisets:
  assumes "\<forall>t\<in>set ts. t \<in> terms F"
  shows "funas_list_ms ts \<in> multisets F"
  using assms
  by (induct ts)
     (auto, auto dest: funas_ms_multisets)

lemma funas_list_ms_append [simp]:
  assumes "\<forall>t\<in>set (ss @ ts). t \<in> terms F"
  shows "funas_list_ms (ss @ ts) = funas_list_ms ss + funas_list_ms ts"
  using assms by (induct ss) (auto simp: ac_simps)

lemma funas_ms_not_empty:
  assumes "t \<in> terms F"
  shows "funas_ms t \<noteq> {#}"
  using assms by (induct t) (auto)

lemma mulex_on_funas_list_ms_Cons [simp]:
  assumes "s \<in> terms F" and "\<forall>t\<in>set ss. t \<in> terms F"
  shows "mulex_on P F (funas_list_ms ss) (funas_list_ms (s # ss))"
  using assms
  by (auto dest: funas_ms_multisets funas_list_ms_multisets funas_ms_not_empty
           intro: mulex_on_self_add_right
           simp: ac_simps)

lemma set_reflclp_mulex_on:
  assumes "t \<in> set ts" and "\<forall>t\<in>set ts. t \<in> terms F"
  shows "(mulex_on P F)\<^sup>=\<^sup>= (funas_ms t) (funas_list_ms ts)"
using assms
proof (induct ts)
  case (Cons s ss)
  then have *: "s \<in> terms F" "\<forall>t\<in>set ss. t \<in> terms F" by auto
  {
    assume "funas_ms s \<noteq> funas_ms s + funas_list_ms ss"
    with * have "mulex_on P F (funas_ms s) (funas_ms s + funas_list_ms ss)"
      by (cases "funas_list_ms ss \<noteq> {#}")
         (auto dest!: funas_ms_multisets funas_list_ms_multisets)
  }
  moreover
  {
    assume "mulex_on P F (funas_ms t) (funas_list_ms ss)"
    with * have "mulex_on P F (funas_ms t) (funas_ms s + funas_list_ms ss)"
      by (auto dest: funas_ms_multisets mulex_on_union_right)
  }
  moreover
  {
    from * have "mulex_on P F (funas_list_ms ss) (funas_ms s + funas_list_ms ss)"
      by (auto simp: funas_ms_not_empty funas_ms_multisets funas_list_ms_multisets ac_simps)
  }
  ultimately show ?case using Cons by auto
qed simp

lemma sublisteq_aux:
  assumes "sublisteq xs ys" and "\<forall>x\<in>set ys. P x"
  shows "\<forall>x\<in>set xs. P x"
  using assms by (induct) auto

lemma sublisteq_reflclp_mulex_on:
  assumes "sublisteq ss ts" and "\<forall>t\<in>set ts. t \<in> terms F"
  shows "(mulex_on P F)\<^sup>=\<^sup>= (funas_list_ms ss) (funas_list_ms ts)"
using assms
proof (induct)
  case (list_hembeq_Nil ys)
  then show ?case by (force dest: funas_list_ms_multisets)
next
  case (list_hembeq_Cons xs ys y)
  moreover then have "funas_ms y \<noteq> {#}"
    and "funas_ms y \<in> multisets F"
    and "funas_list_ms ys \<in> multisets F"
    by (auto dest: funas_ms_not_empty funas_ms_multisets funas_list_ms_multisets)
  ultimately show ?case by (auto simp: ac_simps)
next
  case (list_hembeq_Cons2 x y xs ys)
  moreover
  then have "\<forall>t\<in>set xs. t \<in> terms F" by (auto dest: sublisteq_aux)
  ultimately
  show ?case
    by (auto intro!: mulex_on_union dest: funas_ms_multisets)
qed

lemma mono_on_term_hemb_mulex_on_funas_ms_terms:
  "mono_on (term_hemb F P) (mulex_on P F) funas_ms (terms F)"
proof
  let ?f = "funas_ms" and ?fs = "funas_list_ms"
  let ?P = "term_hemb F P" and ?Q = "mulex_on P F"
  let ?A = "terms F" and ?B = "multisets F"
  fix s t
  assume "?P s t"
  then show "?Q (?f s) (?f t)"
  proof (induct)
    case (term_hemb_base f n ts t)
    note IH = this
    then have 1: "?f (mk f ts) = {#(f, length ts)#} + ?fs ts" by (simp)
    have "t \<in> set ts" by fact
    moreover have "\<forall>t\<in>set ts. t \<in> terms F" by fact
    ultimately have "?Q\<^sup>=\<^sup>= (?f t) (?fs ts)" by (rule set_reflclp_mulex_on)
    moreover have "?f t \<in> ?B" using IH by (auto dest: funas_ms_multisets)
    moreover have "(f, length ts) \<in> F" using IH by simp
    ultimately show ?case by (simp add: 1)
  next
    case (term_hemb_sublisteq f n g m ss ts)
    note IH = this
    then have 1: "?f (mk f ss) = {#(f, length ss)#} + ?fs ss"
      and 2: "?f (mk g ts) = {#(g, length ts)#} + ?fs ts"
      by (simp_all)
    show ?case
      unfolding 1 2
    proof (rule union_mulex_on_mono2)
      from IH show "?fs ss \<in> ?B" by (blast dest: funas_list_ms_multisets)
    next
      from IH show "?Q {#(f, length ss)#} {#(g, length ts)#}" by (blast intro: singleton_mulex_onI)
    next
      show "?Q\<^sup>=\<^sup>= (?fs ss) (?fs ts)"
        by (rule sublisteq_reflclp_mulex_on) fact+
    qed
  next
    case (term_hemb_trans s t u)
    then show ?case using mulex_on_trans by blast
  next
    case (term_hemb_ctxt s t f n ss1 ss2)
    note IH = this
    let ?n = "Suc (length (ss1 @ ss2))"
    let ?ss = "ss1 @ s # ss2" and ?ts = "ss1 @ t # ss2"
    from IH have n: "n = ?n" by simp
    have 1: "?f (mk f ?ss) = {#(f, ?n)#} + ?f s + ?fs ss1 + ?fs ss2"
    proof -
      from IH have "(f, ?n) \<in> F" and "\<forall>t\<in>set ?ss. t \<in> ?A" by (auto dest: term_hemb_imp_terms)
      then have "?f (mk f ?ss) = {#(f, ?n)#} + ?fs ?ss" by (simp)
      moreover have "?fs ?ss = ?f s + ?fs ss1 + ?fs ss2"
      proof -
        from IH have "s \<in> terms F" and "\<forall>t\<in>set ?ss. t \<in> ?A" by (auto dest: term_hemb_imp_terms)
        then show ?thesis by (auto simp: ac_simps)
      qed
      ultimately show ?thesis by (simp (no_asm_simp) add: ac_simps)
    qed
    have 2: "?f (mk f ?ts) = {#(f, ?n)#} + ?f t + ?fs ss1 + ?fs ss2"
    proof -
      from IH have "(f, ?n) \<in> F" and "\<forall>t\<in>set ?ts. t \<in> ?A" by (auto dest: term_hemb_imp_terms)
      then have "?f (mk f ?ts) = {#(f, ?n)#} + ?fs ?ts" by (simp)
      moreover have "?fs ?ts = ?f t + ?fs ss1 + ?fs ss2"
      proof -
        from IH have "t \<in> terms F" and "\<forall>t\<in>set ?ts. t \<in> ?A" by (auto dest: term_hemb_imp_terms)
        then show ?thesis by (auto simp: ac_simps)
      qed
      ultimately show ?thesis by (simp (no_asm_simp) add: ac_simps)
    qed
    have 3: "?fs ss1 \<in> ?B"
    proof -
      from IH have "\<forall>t\<in>set ss1. t \<in> ?A" by (auto)
      then show ?thesis by (auto simp: multisets_def funas_list_ms_imp_mem)
    qed
    have 4: "?fs ss2 \<in> ?B"
    proof -
      from IH have "\<forall>t\<in>set ss2. t \<in> ?A" by auto
      then show ?thesis by (auto simp: multisets_def funas_list_ms_imp_mem)
    qed
    from IH and 3 and 4 have "{#(f, ?n)#} \<in> ?B"
      by (force simp: multisets_def dest: funas_list_ms_imp_mem)
    show ?case
      unfolding 1 2
      by (intro mulex_on_union' mulex_on_union) fact+
  qed
qed

text {*Homeomorphic embedding on terms is irreflexive when based on a well-founded
precedence.*}
lemma irreflp_on_term_hemb_terms:
  assumes "wfp_on P F"
  shows "irreflp_on (term_hemb F P) (terms F)"
proof -
  let ?P = "term_hemb F P" and ?Q = "mulex_on P F"
  let ?A = "terms F" and ?B = "multisets F"
  from assms [THEN irreflp_on_mulex_on]
    have "irreflp_on ?Q ?B" .
  moreover have "funas_ms ` ?A \<subseteq> ?B" by (blast intro: funas_ms_multisets)
  moreover have "mono_on ?P ?Q funas_ms ?A"
    by (rule mono_on_term_hemb_mulex_on_funas_ms_terms)
  ultimately show ?thesis by (rule mono_on_irreflp_on)
qed

end

end

