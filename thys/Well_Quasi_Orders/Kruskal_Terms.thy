(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem -- Infinite Version for Terms *}

theory Kruskal_Terms
imports
  Well_Quasi_Orders
  Kruskal_Auxiliaries
  Finite_Tree
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

lemma almost_full_on_terms:
  assumes "almost_full_on P F"
  shows "almost_full_on (term_hemb F (P\<^sup>=\<^sup>=)) (terms F)"
proof -
  let ?P = "(term_hemb F P)\<^sup>=\<^sup>="
  let ?A = "terms F"
  interpret term_mbs: mbs "\<lambda>F. (term_hemb F P)\<^sup>=\<^sup>=" subtree "terms"
    apply (unfold_locales)
    apply (rule term_hembeq_subtree, assumption+)
    apply (rule wfp_on_subtree_terms)
    apply (erule subtree_trans, assumption)
    apply (rule subtree_terms, assumption+)
  done
  { have "reflp_on ?P ?A" by (auto simp: reflp_on_def) }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> good ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> terms F" and "bad ?P f" by blast
      from term_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at (\<lambda>F. (term_hemb F P)\<^sup>=\<^sup>=) subtree F m n" and
        in_terms: "\<And>i. m i \<in> terms F"
        by blast
      let ?A = m
      obtain a as
        where a: "\<forall>i. root (?A i) = a i \<and> succs (?A i) = as i" by force
      let ?B = "\<lambda>i. set (succs (?A i))"
      {
        assume "\<exists>R f::nat seq. (\<forall>i. R i \<in> ?B (f i) \<and> f i \<ge> f 0) \<and> bad ?P R"
        then obtain R and f :: "nat seq"
          where in_succs: "\<forall>i. R i \<in> ?B (f i)"
          and ge: "\<forall>i. f i \<ge> f 0"
          and "bad ?P R" by auto
        let ?C = "\<lambda>i. if i < f 0 then ?A i else R (i - f 0)"
        have [simp]: "\<And>i. i < f 0 \<Longrightarrow> ?C i = ?A i" by auto
        have [simp]: "\<And>i. f 0 \<le> i \<Longrightarrow> ?C i = R (i - f 0)" by auto
        have "bad ?P ?C"
        proof
          assume "good ?P ?C"
          then obtain i j where "i < j" and *: "?P (?C i) (?C j)" by (auto simp: good_def)
          {
            assume "j < f 0" with `i < j` and * have "?P (?A i) (?A j)" by simp
            with `i < j` and `bad ?P ?A` have False by (auto simp: good_def)
          } moreover {
            assume "f 0 \<le> i" with `i < j` and * have "?P (R (i - f 0)) (R (j - f 0))" by simp
            moreover with `i < j` and `f 0 \<le> i` have "i - (f 0) < j - (f 0)" by auto
            ultimately have False using `bad ?P R` by (auto simp: good_def)
          } moreover {
            let ?i = "j - f 0"
            from in_succs have "R ?i \<in> ?B (f ?i)" by simp
            from in_succs_imp_subtree [OF _ this] and in_terms
              have subtree: "subtreeeq (R ?i) (?A (f ?i))"
              by (auto dest: terms_imp_trees)
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P (?A i) (R ?i)" by auto
            with subtree have "?P (?A i) (?A (f ?i))"
              using term_hembeq_subtreeeq and in_terms
              by blast
            moreover from ge [THEN spec [of _ "?i"]] and `i < f 0` have "i < f ?i" by auto
            ultimately have False using `bad ?P ?A` by (auto simp: good_def)
          } ultimately show False by arith
        qed
        have "\<forall>i<f 0. ?C i = ?A i" by simp
        moreover have "subtree (?C (f 0)) (?A (f 0))"
          using in_succs_imp_subtree [OF _ in_succs [THEN spec, of 0]]
          and in_terms by (auto dest: terms_imp_trees)
        moreover have "\<forall>i\<ge>f 0. \<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)"
        proof (intro allI impI)
          fix i
          let ?i = "i - f 0"
          assume "f 0 \<le> i"
          with `\<forall>i. f 0 \<le> f i` have "f 0 \<le> f ?i" by auto
          from `f 0 \<le> i` have "?C i = R ?i" by auto
          with in_succs_imp_subtree [OF _ in_succs [THEN spec [of _ ?i]]] and in_terms
            have "subtree\<^sup>=\<^sup>= (?C i) (?A (f ?i))" by (auto dest: terms_imp_trees)
          thus "\<exists>j\<ge>f 0. subtree\<^sup>=\<^sup>= (?C i) (?A j)" using `f 0 \<le> f ?i` by auto
        qed
        ultimately have "good ?P ?C"
          using mb [of "f 0", unfolded term_mbs.min_at_def, rule_format] by simp
        with `bad ?P ?C` have False by blast
      }
      hence no_special_bad_seq: "\<not> (\<exists>R f. (\<forall>i. R i \<in> ?B (f i) \<and> f 0 \<le> f i) \<and> bad ?P R)" by blast
      let ?B' = "{x. \<exists>i. x \<in> ?B i}"
      have subset: "?B' \<subseteq> terms F"
      proof
        fix x assume "x \<in> ?B'"
        then obtain i where B: "x \<in> ?B i" by auto
        from in_succs_imp_subtree [OF _ this] and in_terms
          have "subtreeeq x (?A i)" by (auto dest: terms_imp_trees)
        with in_terms [of i] show "x \<in> terms F"
          using subtreeeq_terms by blast
      qed
      have "almost_full_on ?P ?B'"
      proof
        from reflp_on_subset [OF subset refl] have refl: "reflp_on ?P ?B'" .
        fix f :: "'a seq" assume "\<forall>i. f i \<in> ?B'"
        from no_bad_of_special_shape_imp_good' [OF no_special_bad_seq refl this]
          show "good ?P f" .
      qed
      let ?a' = "{(a i, length (as i)) | i. True}"
      have "?a' \<subseteq> F"
      proof
        fix x assume "x \<in> ?a'"
        then obtain i where x: "x = (a i, length (as i))" by auto
        from in_terms [of i] and a [THEN spec [of _ i]]
          show "x \<in> F" by (cases "m i") (simp add: x)
      qed
      from almost_full_on_subset [OF this assms]
        have "almost_full_on P ?a'" .

      from almost_full_on_lists [OF `almost_full_on ?P ?B'`]
        have lists: "almost_full_on (list_hembeq ?P) (lists ?B')" .

      let ?succs = "{succs (?A i) | i. True}"
      have "?succs \<subseteq> lists ?B'" by auto
      from almost_full_on_subset [OF this lists]
        have "almost_full_on (list_hembeq ?P) ?succs" .

      let ?P' = "prod_le P (list_hembeq ?P)"

      from almost_full_on_Sigma [OF `almost_full_on P ?a'` `almost_full_on (list_hembeq ?P) ?succs`]
        have af: "almost_full_on ?P' (?a' \<times> ?succs)" .
      
      let ?aB = "\<lambda>i. ((a i, length (as i)), succs (?A i))"

      have "\<forall>i. ?aB i \<in> (?a' \<times> ?succs)" by auto
      with af have "good ?P' ?aB" unfolding almost_full_on_def by auto
      then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
        by (auto simp: good_def almost_full_on_def)

      from root_succs and in_terms
        have root_succs: "\<And>i. mk (root (?A i)) (succs (?A i)) = ?A i"
          by (force dest: terms_imp_trees)+

      have in_terms': "\<And>i. mk (a i) (as i) \<in> terms F"
      proof -
        fix i
        from a have "a i = root (m i)" and "as i = succs (m i)" by auto
        then show "?thesis i" using in_terms and root_succs by simp
      qed
      from in_terms'
        have Fi: "(a i, length (as i)) \<in> F" and Fj: "(a j, length (as j)) \<in> F"
          and terms: "\<forall>t\<in>set (as i @ as j). t \<in> terms F"
          by (auto iff: mk_terms_iff)
      from * have "P\<^sup>=\<^sup>= (a i, length (as i)) (a j, length (as j))" and "list_hembeq ?P (succs (?A i)) (succs (?A j))"
        by (auto simp: prod_le_def)
      with term_hembeq_list_hembeq [OF this(1) Fi Fj terms]
        have "?P (?A i) (?A j)" using a and root_succs by auto
      with `i < j` and `bad ?P ?A` show False by (auto simp: good_def almost_full_on_def)
    qed
  }
  then show ?thesis
    using term_hembeq_term_hemb_conv by (auto simp: almost_full_on_def good_def)
qed

end

end

