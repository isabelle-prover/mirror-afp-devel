(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Kruskal's Tree Theorem -- Finite Version for Terms *}

theory Kruskal_Finite
imports
  Well_Quasi_Orders
  Kruskal_Auxiliaries
  Finite_Tree
begin

context finite_tree
begin

text {*Embedding on trees.*}
inductive term_emb for F where
  term_emb_base [intro]:
    "\<lbrakk>(f, n) \<in> F; length ts = n; \<forall>t\<in>set ts. t \<in> terms F; t \<in> set ts\<rbrakk> \<Longrightarrow> term_emb F t (mk f ts)" |
  term_emb_trans [intro]: "term_emb F s t \<Longrightarrow> term_emb F t u \<Longrightarrow> term_emb F s u" |
  term_emb_ctxt [intro]:
    "\<lbrakk>term_emb F s t; (f, n) \<in> F; Suc (length (ss1@ss2)) = n; \<forall>t\<in>set (ss1@ss2). t \<in> terms F\<rbrakk> \<Longrightarrow>
    term_emb F (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"

abbreviation term_embeq where
  "term_embeq F \<equiv> (term_emb F)\<^sup>=\<^sup>="

lemma term_emb_imp_terms:
  assumes "term_emb F s t"
  shows "s \<in> terms F \<and> t \<in> terms F"
  using assms by (induct) force+


lemma term_emb_size:
  assumes "term_emb F s t"
  shows "size s < size t"
  using assms
  by (induct)
     (auto simp: size_simp2 dest!: term_emb_imp_terms)

lemma term_emb_subtree:
  assumes "u \<in> terms F" and "term_emb F s t" and "subtree t u" shows "term_emb F s u"
  using assms(3, 2, 1) by (induct) (auto iff: mk_terms_iff)

lemma subtree_imp_term_emb:
  assumes "subtree s t" and "t \<in> terms F" shows "term_emb F s t"
  using assms by (induct) (auto iff: mk_terms_iff)

lemma term_embeq_subtree:
  assumes "u \<in> terms F" and "term_embeq F s t" and "subtree t u"
  shows "term_embeq F s u"
  using assms and term_emb_subtree [of u F s t]
  by (auto intro: subtree_imp_term_emb)

lemma term_embeq_subtreeeq:
  assumes "u \<in> terms F" and "term_embeq F s t" and "subtreeeq t u" shows "term_embeq F s u"
  using assms and term_emb_subtree [of u F s t]
  by (auto intro: subtree_imp_term_emb)

lemma reflp_on_term_embeq:
  "reflp_on (term_embeq F) A"
  by (auto simp: reflp_on_def)

lemma args_steps_imp_steps_term_emb:
  assumes len: "length ss = length ts"
    and F: "(f, length ss) \<in> F"
    and terms: "\<forall>t\<in>set (ss@ts). t \<in> terms F"
    and args: "\<forall>i<length ss. (term_emb F)\<^sup>=\<^sup>= (ss ! i) (ts ! i)"
  shows "(term_emb F)\<^sup>*\<^sup>* (mk f ss) (mk f ts)" (is "?P (mk f ss) (mk f ts)")
proof (rule args_steps_imp_steps_gen_terms [OF _ F terms len])
  fix i
  assume "i < length ts" thus "?P (ss ! i) (ts ! i)" using args and len by auto
next
  fix s t and ss1 ss2 :: "'a list"
  assume "(f, Suc (length (ss1 @ ss2))) \<in> F"
    and "\<forall>t\<in>set (ss1@ss2). t \<in> terms F"
    and "term_emb F s t"
    and "length ts = Suc (length ss1 + length ss2)"
  then have "term_emb F (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))"
    by (auto simp: len)
  then show "(term_emb F)\<^sup>*\<^sup>* (mk f (ss1 @ s # ss2)) (mk f (ss1 @ t # ss2))" by simp
qed

lemma term_emb_rtranclp [simp]:
  shows "(term_emb F)\<^sup>*\<^sup>* s t = term_embeq F s t" (is "?l = ?r")
proof -
  {
    assume "?l"
    then have "?r" by (induct) auto
  }
  then show "?l = ?r" by auto
qed

lemma list_hembeq_term_hembeq_imp_sublisteq:
  assumes "list_hembeq (term_embeq F) xs zs"
    (is "list_hembeq ?P xs zs")
  shows "\<exists>ys. sublisteq ys zs \<and> length ys = length xs \<and>
    (\<forall>i<length xs. term_embeq F (xs ! i) (ys ! i))"
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

lemma term_embeq_list_hembeq:
  assumes F: "(f, length ss) \<in> F"
    and len: "length ss = length ts"
    and terms: "\<forall>t\<in>set (ss@ts). t \<in> terms F"
    and list: "list_hembeq (term_embeq F) ss ts"
  shows "term_embeq F (mk f ss) (mk f ts)"
proof -
  from list_hembeq_term_hembeq_imp_sublisteq [OF list]
    obtain us where sub: "sublisteq us ts" and len': "length ss = length us"
    and *: "\<forall>i<length ss. term_embeq F (ss ! i) (us ! i)" by auto
  from sublisteq_set_subset [OF sub]
    have "\<forall>t\<in>set (ss@us). t \<in> terms F" using terms by auto
  from args_steps_imp_steps_term_emb [OF len' F this *]
    have **: "term_embeq F (mk f ss) (mk f us)" by simp
  from sublisteq_same_length [OF sub] and len and len'
    have [simp]: "us = ts" by simp
  from ** show ?thesis by simp
qed


subsection {* Kruskal's Tree Theorem -- Finite Version *}

lemma almost_full_on_trees:
  assumes "finite F"
  shows "almost_full_on (term_embeq F) (terms F)"
    (is "almost_full_on ?P ?A")
proof -
  interpret term_mbs: mbs term_embeq subtree terms
  proof -
    show "mbs term_embeq subtree terms"
    apply (unfold_locales)
    apply (rule term_embeq_subtree, assumption+)
    apply (rule wfp_on_subtree_terms)
    apply (rule subtree_trans, assumption+)
    apply (rule subtree_terms, assumption+)
    done
  qed
  { from reflp_on_term_embeq have "reflp_on ?P ?A" . }
  note refl = this
  {
    have "\<forall>f. (\<forall>i. f i \<in> ?A) \<longrightarrow> good ?P f"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain f where "\<forall>i. f i \<in> terms F" and "bad ?P f" by blast
      from term_mbs.mbs [OF this] obtain m where
        bad: "bad ?P m" and
        mb: "\<And>n. mbs.min_at term_embeq subtree F m n" and
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
              have subtree: "subtreeeq (R ?i) (?A (f ?i))" by (auto dest: terms_imp_trees)
            assume "i < f 0" and "f 0 \<le> j"
            with * have "?P (?A i) (R ?i)" by auto
            with subtree have "?P (?A i) (?A (f ?i))"
              using term_embeq_subtreeeq and in_terms by blast
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
      from almost_full_on_subset [OF this eq_almost_full_on_finite_set [OF assms]]
        have "almost_full_on (op =) ?a'" .

      from almost_full_on_lists [OF `almost_full_on ?P ?B'`]
        have lists: "almost_full_on (list_hembeq ?P) (lists ?B')" .

      let ?succs = "{succs (?A i) | i. True}"
      have "?succs \<subseteq> lists ?B'" by auto
      from almost_full_on_subset [OF this lists]
        have "almost_full_on (list_hembeq ?P) ?succs" .

      let ?P' = "prod_le (op =) (list_hembeq ?P)"

      from almost_full_on_Sigma [OF `almost_full_on (op =) ?a'` `almost_full_on (list_hembeq ?P) ?succs`]
        have af: "almost_full_on ?P' (?a' \<times> ?succs)" .
      
      let ?aB = "\<lambda>i. ((a i, length (as i)), succs (?A i))"

      have "\<forall>i. ?aB i \<in> (?a' \<times> ?succs)" by auto
      with af have "good ?P' ?aB" unfolding almost_full_on_def by auto
      then obtain i j where "i < j" and *: "?P' (?aB i) (?aB j)"
        by (auto simp: good_def almost_full_on_def)

      from root_succs and in_terms
        have root_succs: "\<And>i. mk (root (?A i)) (succs (?A i)) = ?A i"
          by (force dest: terms_imp_trees)+
      
      have mk: "\<And>i::nat. mk (a i) (as i) = m i"
      proof -
        fix i
        from a have "a i = root (m i)" and "as i = succs (m i)" by auto
        then show "?thesis i" using root_succs by simp
      qed

      have in_terms': "\<And>i. mk (a i) (as i) \<in> terms F" using mk and in_terms by simp

      from in_terms'
        have Fi: "(a i, length (as i)) \<in> F" and Fj: "(a j, length (as j)) \<in> F"
          and terms: "\<forall>t\<in>set (as i @ as j). t \<in> terms F"
          by (auto iff: mk_terms_iff)
      from * have ai: "a i = a j" and "length (as i) = length (as j)"
        and "list_hembeq ?P (as i) (as j)"
        using a by (auto simp: prod_le_def)
      from term_embeq_list_hembeq [OF Fi this(2) terms this(3)]
        have "?P (?A i) (?A j)" unfolding mk unfolding ai unfolding mk .
      with `i < j` and `bad ?P ?A` show False by (auto simp: good_def almost_full_on_def)
    qed
  }
  with trans show ?thesis unfolding almost_full_on_def by blast
qed

end

end

