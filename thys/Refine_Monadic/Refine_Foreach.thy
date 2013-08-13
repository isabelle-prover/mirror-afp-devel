header {* \isaheader{Foreach Loops} *}
theory Refine_Foreach
imports Refine_While "../Collections/iterator/SetIterator"
begin

text {*
  A common pattern for loop usage is iteration over the elements of a set.
  This theory provides the @{text "FOREACH"}-combinator, that iterates over 
  each element of a set.
*}

subsection {* Auxilliary Lemmas *}
text {* The following lemma is commonly used when reasoning about iterator
  invariants.
  It helps converting the set of elements that remain to be iterated over to
  the set of elements already iterated over. *}
lemma it_step_insert_iff: 
  "it \<subseteq> S \<Longrightarrow> x\<in>it \<Longrightarrow> S-(it-{x}) = insert x (S-it)" by auto

subsection {* Definition *}

text {*
  Foreach-loops come in different versions, depending on whether they have an 
  annotated invariant (I), a termination condition (C), and an order (O).

  Note that asserting that the set is finite is not necessary to guarantee
  termination. However, we currently provide only iteration over finite sets,
  as this also matches the ICF concept of iterators.
*}
   
definition "FOREACH_body f \<equiv> \<lambda>(xs, \<sigma>). do {
  let x = hd xs; \<sigma>'\<leftarrow>f x \<sigma>; RETURN (tl xs,\<sigma>')
  }"

definition FOREACH_cond where "FOREACH_cond c \<equiv> (\<lambda>(xs,\<sigma>). xs\<noteq>[] \<and> c \<sigma>)"

text {* Foreach with continuation condition, order and annotated invariant: *}

definition FOREACHoci ("FOREACH\<^sub>O\<^sub>C\<^bsup>_\<^esup>") where "FOREACHoci \<Phi> S R c f \<sigma>0 \<equiv> do {
  ASSERT (finite S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_by_rel R xs);
  (_,\<sigma>) \<leftarrow> WHILEIT 
    (\<lambda>(it,\<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) (FOREACH_cond c) (FOREACH_body f) (xs,\<sigma>0); 
  RETURN \<sigma> }"

text {* Foreach with continuation condition and annotated invariant: *}
definition FOREACHci ("FOREACH\<^sub>C\<^bsup>_\<^esup>") where "FOREACHci \<Phi> S \<equiv> FOREACHoci \<Phi> S (\<lambda>_ _. True)"

text {* Foreach with continuation condition: *}
definition FOREACHc ("FOREACH\<^sub>C") where "FOREACHc \<equiv> FOREACHci (\<lambda>_ _. True)"

text {* Foreach with annotated invariant: *}
definition FOREACHi ("FOREACH\<^bsup>_\<^esup>") where 
  "FOREACHi \<Phi> S f \<sigma>0 \<equiv> FOREACHci \<Phi> S (\<lambda>_. True) f \<sigma>0"

text {* Foreach with annotated invariant and order: *}
definition FOREACHoi ("FOREACH\<^sub>O\<^bsup>_\<^esup>") where 
  "FOREACHoi \<Phi> S R f \<sigma>0 \<equiv> FOREACHoci \<Phi> S R (\<lambda>_. True) f \<sigma>0"

text {* Basic foreach *}
definition "FOREACH S f \<sigma>0 \<equiv> FOREACHc S (\<lambda>_. True) f \<sigma>0"

subsection {* Proof Rules *}

lemma FOREACHoci_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> c \<sigma>; x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma>;
                         \<forall>x\<in>it. \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoci I S R c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHoci_def
  apply (intro refine_vcg)

  apply (rule FIN)

  apply (subgoal_tac "wf (measure (\<lambda>(xs, _). length xs))")
    apply assumption
    apply simp

  apply (insert I0, simp add: I0) []
  unfolding FOREACH_body_def FOREACH_cond_def
  apply (rule refine_vcg)+
  apply (simp, elim conjE exE)+
  apply (rename_tac xs'' s xs' \<sigma> xs)
defer
  apply (simp, elim conjE exE)+
  apply (rename_tac x s xs' \<sigma> \<sigma>' xs)
defer
proof -
  fix xs' \<sigma> xs

  assume I_xs': "I (set xs') \<sigma>"
     and sorted_xs_xs': "sorted_by_rel R (xs @ xs')"
     and dist: "distinct xs" "distinct xs'" "set xs \<inter> set xs' = {}"
     and S_eq: "S = set xs \<union> set xs'" 

  from S_eq have "set xs' \<subseteq> S" by simp
  from dist S_eq have S_diff: "S - set xs' = set xs" by blast

  { assume "xs' \<noteq> []" "c \<sigma>"
    from `xs' \<noteq> []` obtain x xs'' where xs'_eq: "xs' = x # xs''" by (cases xs', auto)

    have x_in_xs': "x \<in> set xs'" and x_nin_xs'': "x \<notin> set xs''" 
       using `distinct xs'` unfolding xs'_eq by simp_all
  
    from IP[of \<sigma> x "set xs'", OF `c \<sigma>` x_in_xs' `set xs' \<subseteq> S` `I (set xs') \<sigma>`] x_nin_xs''
         sorted_xs_xs' S_diff
    show "f (hd xs') \<sigma> \<le> SPEC
            (\<lambda>x. (\<exists>xs'a. xs @ xs' = xs'a @ tl xs') \<and>
                 I (set (tl xs')) x)"
      apply (simp add: xs'_eq)
      apply (simp add: sorted_by_rel_append)
    done
  }

  { assume "xs' = [] \<or> \<not>(c \<sigma>)"
    show "P \<sigma>" 
    proof (cases "xs' = []")
      case True thus "P \<sigma>" using `I (set xs') \<sigma>` by (simp add: II1)
    next
      case False note xs'_neq_nil = this
      with `xs' = [] \<or> \<not> c \<sigma>` have "\<not> c \<sigma>" by simp
 
      from II2 [of "set xs'" \<sigma>] S_diff sorted_xs_xs'
      show "P \<sigma>" 
        apply (simp add: xs'_neq_nil S_eq `\<not> c \<sigma>` I_xs')
        apply (simp add: sorted_by_rel_append)
      done
    qed
  }
qed

lemma FOREACHoi_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoi I S R f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHoi_def 
  by (rule FOREACHoci_rule) (simp_all add: assms)

lemma FOREACHci_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHci I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHci_def
  by (rule FOREACHoci_rule) (simp_all add: assms)

lemma FOREACHoci_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>\<forall>y\<in>it-{x}. RR x y; 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHoci \<Phi> S RR c f \<sigma>0 \<le> \<Down>R (FOREACHoci \<Phi>' S' RR' c' f' \<sigma>0')"
  unfolding FOREACHoci_def
  apply (rule ASSERT_refine_right ASSERT_refine_left)+
  using REFS INJ apply (auto dest: finite_imageD) []

  apply (rule bind_refine)
  apply (subgoal_tac 
     "SPEC (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_by_rel RR xs) \<le> 
        \<Down> {(xs, xsa). xsa = map \<alpha> xs \<and> sorted_by_rel RR xs \<and> distinct xs \<and> distinct xsa \<and> set xs = S \<and> set xsa = S'}
      (SPEC (\<lambda>xs. distinct xs \<and> S' = set xs \<and> sorted_by_rel RR' xs))")
  apply assumption
  apply (rule SPEC_refine_sv)
  apply (simp add: single_valued_def)
  apply (rule SPEC_rule)
  apply (insert INJ, simp add: REFS distinct_map sorted_by_rel_map)[]
  apply (rule sorted_by_rel_weaken[of _ RR])
  apply (simp add: RR_OK)
  apply (simp)

  apply (rule bind_refine)
  apply (rule_tac WHILEIT_refine)
  apply (subgoal_tac "((x, \<sigma>0), x', \<sigma>0')\<in>{((xs,\<sigma>),(xs',\<sigma>')). sorted_by_rel RR xs \<and> 
    xs'=map \<alpha> xs \<and> set xs \<subseteq> S \<and> set xs' \<subseteq> S' \<and> (\<sigma>,\<sigma>')\<in>R \<and> \<Phi>'' (set xs) \<sigma> (set xs') \<sigma>'}", assumption)
  apply (simp add: REFS REF0 REFPHI0)

  apply (auto intro: single_valuedI single_valuedD[OF SV]) []

  using REFPHI 
  apply (simp) 
  apply (clarify)
  apply (rule conjI)  
  prefer 2
  apply auto[]
defer
  using REFC apply (clarify) apply (auto simp add: FOREACH_cond_def) []

  apply (simp add: FOREACH_body_def Let_def split: prod.splits) []
  apply (rule bind_refine)
    apply (case_tac a, simp add: FOREACH_cond_def) []
    apply (rule REFSTEP)
      apply (subgoal_tac "\<forall>y\<in>set a-{hd a}. RR (hd a) y", assumption)
      apply simp
      apply simp
      apply simp
      apply (subgoal_tac "hd (map \<alpha> a)\<in>set aa", assumption)
      apply simp_all[3]
      apply fast
      apply simp
      apply simp
      apply fast
      apply (simp add: FOREACH_cond_def)
      apply (simp add: FOREACH_cond_def)
      apply simp
    apply (rule RETURN_refine_sv)
    apply (rule single_valuedI)
    apply (auto simp add: single_valuedD[OF SV]) []
    apply (case_tac a, simp)
    apply (clarify, simp)

  apply (split prod.split, intro allI impI)+
  apply (rule RETURN_refine_sv[OF SV])
  apply (auto)[]
proof -
  fix xs axs' xs''
  assume map_eq: "map \<alpha> xs = axs' @ map \<alpha> xs''"
     and xs''_subset: "set xs'' \<subseteq> set xs"
     and dist_xs: "distinct (map \<alpha> xs)"
  hence "axs' = take (length axs') (map \<alpha> xs)" by (metis append_eq_conv_conj)
  hence axs'_eq: "axs' = map \<alpha> (take (length axs') xs)" by (simp add: take_map)

  from map_eq axs'_eq have map_eq: "map \<alpha> xs = map \<alpha> ((take (length axs') xs) @ xs'')"
    by (metis map_append)

  have inj_\<alpha>: "inj_on \<alpha> (set xs \<union> set ((take (length axs') xs) @ xs''))"
  proof -
    from xs''_subset
    have "(set xs \<union> set ((take (length axs') xs) @ xs'')) = set xs"
      by (auto elim: in_set_takeD)

    with dist_xs show ?thesis
      by (simp add: distinct_map)
  qed
  
  from inj_on_map_eq_map [OF inj_\<alpha>] map_eq
  have "xs = (take (length axs') xs) @ xs''" by blast
  thus "\<exists>xs'. xs = xs' @ xs''" by blast
qed 
 
lemma FOREACHoci_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes SV: "single_valued R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> \<forall>y\<in>it-{x}. RR x y;
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHoci \<Phi> S RR c f \<sigma>0 \<le> \<Down>R (FOREACHoci \<Phi>' S' RR' c' f' \<sigma>0')"
  apply (rule FOREACHoci_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHoci_weaken:
  assumes IREF: "\<And>it \<sigma>. it\<subseteq>S \<Longrightarrow> I it \<sigma> \<Longrightarrow> I' it \<sigma>"
  shows "FOREACHoci I' S RR c f \<sigma>0 \<le> FOREACHoci I S RR c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: IREF)
  done

lemma FOREACHoci_weaken_order:
  assumes RRREF: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> RR x y \<Longrightarrow> RR' x y"
  shows "FOREACHoci I S RR c f \<sigma>0 \<le> FOREACHoci I S RR' c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: RRREF)
  done


subsubsection {* Rules for Derived Constructs *}

lemma FOREACHoi_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>\<forall>y\<in>it-{x}. RR x y; 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHoi \<Phi> S RR f \<sigma>0 \<le> \<Down>R (FOREACHoi \<Phi>' S' RR' f' \<sigma>0')"
  unfolding FOREACHoi_def
  apply (rule FOREACHoci_refine [of \<alpha> _ _ _ _ _ _ _ \<Phi>''])
  apply (simp_all add: assms)
done

lemma FOREACHoi_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes SV: "single_valued R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> \<forall>y\<in>it-{x}. RR x y;
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHoi \<Phi> S RR f \<sigma>0 \<le> \<Down>R (FOREACHoi \<Phi>' S' RR' f' \<sigma>0')"
  apply (rule FOREACHoi_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHci_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHci_def
  apply (rule FOREACHoci_refine [of \<alpha> _ _ _ _ _ _ _ \<Phi>''])
  apply (simp_all add: assms)
done

lemma FOREACHci_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  apply (rule FOREACHci_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by auto

lemma FOREACHci_weaken:
  assumes IREF: "\<And>it \<sigma>. it\<subseteq>S \<Longrightarrow> I it \<sigma> \<Longrightarrow> I' it \<sigma>"
  shows "FOREACHci I' S c f \<sigma>0 \<le> FOREACHci I S c f \<sigma>0"
  apply (rule FOREACHci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: IREF)
  done

lemma FOREACHi_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHi I S f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHi_def
  apply (rule FOREACHci_rule[of S I])
  using assms by auto

lemma FOREACHc_rule:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHc S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule[where I=I])
  using assms by auto

lemma FOREACH_rule:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACH S f \<sigma>0 \<le> SPEC P"
  unfolding FOREACH_def FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule[where I=I])
  using assms by auto

lemma FOREACHc_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 SV REFPHI0])
  apply (erule (4) REFC)
  apply (rule TrueI)
  apply (erule (9) REFSTEP)
  done

lemma FOREACHc_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_rcg)
  apply (rule assms)+
  using assms by auto

lemma FOREACHi_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 SV REFPHI0])
  apply (rule refl)
  apply (erule (5) REFPHI)
  apply (erule (9) REFSTEP)
  done

lemma FOREACHi_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine_rcg)
  apply (rule assms)+
  using assms apply auto
  done

lemma FOREACH_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 SV REFPHI0])
  apply (rule refl)
  apply (erule (7) REFSTEP)
  done

lemma FOREACH_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine_rcg)
  apply (rule assms)+
  using assms by auto

lemma FOREACHci_refine_rcg'[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_rcg) 
  apply (rule assms)
  apply (rule assms)
  apply (rule assms)
  apply (rule assms)
  apply (erule (4) REFC)
  apply (rule TrueI)
  apply (rule REFSTEP, assumption+)
  done

lemma FOREACHi_refine_rcg'[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes SV: "single_valued R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>' it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACH_def FOREACHi_def
  apply (rule FOREACHci_refine_rcg') 
  apply (rule assms)+
  apply simp
  apply (rule REFSTEP, assumption+)
  done

subsection {* FOREACH with empty sets *}

lemma FOREACHoci_emp [simp] :
  "FOREACHoci \<Phi> {} R c f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
apply (simp add: FOREACHoci_def bind_RES image_def)
apply (simp add: WHILEIT_unfold FOREACH_cond_def)
done

lemma FOREACHoi_emp [simp] :
  "FOREACHoi \<Phi> {} R f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHoi_def)

lemma FOREACHci_emp [simp] :
  "FOREACHci \<Phi> {} c f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHci_def)

lemma FOREACHc_emp [simp] :
  "FOREACHc {} c f \<sigma> = RETURN \<sigma>"
by (simp add: FOREACHc_def)

lemma FOREACH_emp [simp] :
  "FOREACH {} f \<sigma> = RETURN \<sigma>"
by (simp add: FOREACH_def)

lemma FOREACHi_emp [simp] :
  "FOREACHi \<Phi> {} f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHi_def)


locale transfer_FOREACH = transfer +
  constrains \<alpha> :: "'mc \<Rightarrow> 's nres"
  fixes creturn :: "'s \<Rightarrow> 'mc"
  and cbind :: "'mc \<Rightarrow> ('s\<Rightarrow>'mc) \<Rightarrow> 'mc"
  and liftc :: "('s \<Rightarrow> bool) \<Rightarrow> 'mc \<Rightarrow> bool"

  assumes transfer_bind: "\<lbrakk>\<alpha> m \<le> M; \<And>x. \<alpha> (f x) \<le> F x \<rbrakk> 
    \<Longrightarrow> \<alpha> (cbind m f) \<le> bind M F"
  assumes transfer_return: "\<alpha> (creturn x) \<le> RETURN x"

  assumes liftc: "\<lbrakk>RETURN x \<le> \<alpha> m; \<alpha> m \<noteq> FAIL\<rbrakk> \<Longrightarrow> liftc c m \<longleftrightarrow> c x"
begin

abbreviation lift_it :: "('x,'mc) set_iterator \<Rightarrow> 
  ('s\<Rightarrow>bool) \<Rightarrow> ('x \<Rightarrow> 's \<Rightarrow> 'mc) \<Rightarrow> 's \<Rightarrow> 'mc"
  where
  "lift_it it c f s0 \<equiv> it 
    (liftc c) 
    (\<lambda>x s. cbind s (f x)) 
    (creturn s0)"

lemma transfer_FOREACHoci[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator_genord iterate X R"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate c f s0) \<le> FOREACHoci I X R c F s0"
proof -
  from IT obtain xs where xs_props: 
    "distinct xs" "X = set xs" "sorted_by_rel R xs" "iterate = foldli xs"
    unfolding set_iterator_genord_def by blast

  def RL\<equiv>"\<lambda>(it,s). WHILE (FOREACH_cond c) (FOREACH_body F) (it, s) \<guillemotright>=
      (\<lambda>(_, \<sigma>). RETURN \<sigma>)"
  hence RL_def': 
    "\<And>it s. RL (it,s) = WHILE (FOREACH_cond c) (FOREACH_body F) (it, s) \<guillemotright>=
    (\<lambda>(_, \<sigma>). RETURN \<sigma>)" by auto

  {
    fix it s
    have "RL (it, s) = (
      if (FOREACH_cond c (it,s)) then 
        (FOREACH_body F (it,s) \<guillemotright>= RL)
      else 
        RETURN s)"
      unfolding RL_def
      apply (subst WHILE_unfold)
      apply (auto simp: pw_eq_iff refine_pw_simps)
      done
  } note RL_unfold = this

  {
    fix it::"'x list" and x and s :: "'s"
    assume C: "c s"
    have "do{ s'\<leftarrow>F x s; RL (it, s')} \<le> RL (x # it,s)"
      apply (subst (2) RL_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply (rule pw_leI)
      using C apply (simp add: refine_pw_simps)
      done
  } note RL_unfold_step=this

  have RL_le: "RL (xs,s0) \<le> FOREACHoci I X R c F s0"
    unfolding FOREACHoci_def
    apply (rule le_ASSERTI)
    apply (rule bind2let_refine [of xs Id _ "\<lambda>_. RL(xs,s0)" Id, simplified])
    apply (simp add: xs_props)
    apply (rule order_trans[OF _ monoD[OF bind_mono1 WHILEI_le_WHILEIT]])
    apply (rule order_trans[OF _ monoD[OF bind_mono1 WHILEI_weaken[OF TrueI]]])
    apply (fold WHILE_def)
    apply (fold RL_def')
    by simp

  { fix S xs'
    have "do { s\<leftarrow>\<alpha> S; RL (xs',s) } \<le> RL (xs,s0) \<Longrightarrow>
          \<alpha> (foldli xs' (liftc c) (\<lambda>x s. cbind s (f x)) S) \<le> 
          RL (xs, s0)"
    proof (induct xs' arbitrary: S)
      case (Nil S) thus ?case 
        by (simp add: RL_unfold FOREACH_cond_def)
      next
        case (Cons x xs' S) 
        note ind_hyp = Cons(1)
        note pre = Cons(2)

        show ?case
        proof (cases "\<alpha> S")
          case FAIL with pre have "RL (xs, s0) = FAIL" by simp
          thus ?thesis by simp
        next
          case (RES S') note \<alpha>_S_eq[simp] = this 

          from transfer_bind [of S "RES S'" "f x" "F x", OF _ RS]
          have \<alpha>_bind: "\<alpha> (cbind S (f x)) \<le> RES S' \<guillemotright>= F x" by simp

          { fix s
            assume "s \<in> S'"
            with liftc [of s S c]
            have "c s = liftc c S" by simp
          } note liftc_intro = this

          show ?thesis
          proof (cases "liftc c S")
            case False note not_liftc = this
            with liftc_intro have "\<And>s. c s \<Longrightarrow> s \<notin> S'" by auto

            hence "RES S' \<guillemotright>= (\<lambda>s. RL (x # xs', s)) = RES S'"
              apply (simp add: bind_def Sup_nres_def image_iff RL_unfold
                               FOREACH_cond_def Ball_def Bex_def) 
              apply (auto)
            done
            with pre not_liftc show ?thesis by simp
          next
            case True note liftc = this

            with liftc_intro have S'_simps: "S' \<inter> {s. c s} = S'" "S' \<inter> {s. \<not> c s} = {}"
               by auto
            have "((\<alpha> (cbind S (f x))) \<guillemotright>= (\<lambda>s. RL (xs', s))) \<le> 
                  ((RES S' \<guillemotright>= F x) \<guillemotright>= (\<lambda>s. RL (xs', s)))"
              by (rule bind_mono) (simp_all add: \<alpha>_bind)
            also have "... =  RES S' \<guillemotright>= (\<lambda>s. F x s \<guillemotright>= (\<lambda>s. RL (xs', s)))" by simp
            also have "\<dots> \<le> \<alpha> S \<guillemotright>= (\<lambda>s. RL (x # xs', s))"
              apply (simp add: RL_unfold[of "x # xs'"] FOREACH_cond_def bind_RES S'_simps)
              apply (simp add: FOREACH_body_def)
              done
            also note pre
            finally have pre': "\<alpha> (cbind S (f x)) \<guillemotright>= (\<lambda>s. RL (xs', s)) \<le> RL (xs, s0)" by simp

            from ind_hyp[OF pre'] liftc
            show ?thesis by simp
          qed
        qed
      qed
  }
  moreover
  have "\<alpha> (creturn s0) \<guillemotright>= (\<lambda>s. RL (xs, s)) \<le> RL (xs, s0)"
  proof -
    have "\<alpha> (creturn s0) \<guillemotright>= (\<lambda>s. RL (xs, s)) \<le>
          RETURN s0 \<guillemotright>= (\<lambda>s. RL (xs, s))"
      apply (rule bind_mono)
      apply (simp_all add: transfer_return)
    done
    thus ?thesis by simp
  qed
  ultimately have lift_le: "\<alpha> (lift_it (foldli xs) c f s0) \<le> RL (xs, s0)" by simp
  
  
  from order_trans[OF lift_le RL_le, folded xs_props(4)]
  show ?thesis .
qed

lemma transfer_FOREACHoi[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator_genord iterate X R"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate (\<lambda>_. True) f s0) \<le> FOREACHoi I X R F s0"
unfolding FOREACHoi_def
by (rule transfer_FOREACHoci [OF IT RS])

lemma transfer_FOREACHci[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate c f s0) \<le> FOREACHci I X c F s0"
unfolding FOREACHci_def
by (rule transfer_FOREACHoci [OF IT[unfolded set_iterator_def] RS])

lemma transfer_FOREACHc[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate c f s0) \<le> FOREACHc X c F s0"
  unfolding FOREACHc_def using assms by (rule transfer_FOREACHci)

lemma transfer_FOREACHI[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate (\<lambda>_. True) f s0) \<le> FOREACHi I X F s0"
  unfolding FOREACHi_def 
  using assms by (rule transfer_FOREACHci)

lemma det_FOREACH[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iterator iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate (\<lambda>_. True) f s0) \<le> FOREACH X F s0"
  unfolding FOREACH_def
  using assms by (rule transfer_FOREACHc)

end

lemma FOREACHoci_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACHoci I S R c f s0 \<le> FOREACHoci I S R c f' s0"
  using assms apply -
  unfolding FOREACHoci_def FOREACH_body_def
  apply (refine_mono)
  done
lemma FOREACHoi_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACHoi I S R f s0 \<le> FOREACHoi I S R f' s0"
  using assms apply -
  unfolding FOREACHoi_def FOREACH_body_def
  apply (refine_mono)
  done
lemma FOREACHci_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACHci I S c f s0 \<le> FOREACHci I S c f' s0"
  using assms apply -
  unfolding FOREACHci_def FOREACH_body_def
  apply (refine_mono)
  done
lemma FOREACHc_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACHc S c f s0 \<le> FOREACHc S c f' s0"
  using assms apply -
  unfolding FOREACHc_def 
  apply (refine_mono)
  done
lemma FOREACHi_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACHi I S f s0 \<le> FOREACHi I S f' s0"
  using assms apply -
  unfolding FOREACHi_def 
  apply (refine_mono)
  done
lemma FOREACH_mono[refine_mono]:
  assumes "\<And>x. f x \<le> f' x"
  shows "FOREACH S f s0 \<le> FOREACH S f' s0"
  using assms apply -
  unfolding FOREACH_def 
  apply (refine_mono)
  done

end
