header {* \isaheader{Foreach Loops} *}
theory Refine_Foreach
imports 
  Refine_While 
  Refine_Pfun 
  Refine_Transfer 
  (*"../Collections/Lib/SetIterator"
  "../Collections/Lib/Proper_Iterator"*)
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

definition FOREACHoci ("FOREACH\<^sub>O\<^sub>C\<^bsup>_,_\<^esup>") where "FOREACHoci R \<Phi> S c f \<sigma>0 \<equiv> do {
  ASSERT (finite S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_by_rel R xs);
  (_,\<sigma>) \<leftarrow> WHILEIT 
    (\<lambda>(it,\<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) (FOREACH_cond c) (FOREACH_body f) (xs,\<sigma>0); 
  RETURN \<sigma> }"

text {* Foreach with continuation condition and annotated invariant: *}
definition FOREACHci ("FOREACH\<^sub>C\<^bsup>_\<^esup>") where "FOREACHci \<equiv> FOREACHoci (\<lambda>_ _. True)"

text {* Foreach with continuation condition: *}
definition FOREACHc ("FOREACH\<^sub>C") where "FOREACHc \<equiv> FOREACHci (\<lambda>_ _. True)"

text {* Foreach with annotated invariant: *}
definition FOREACHi ("FOREACH\<^bsup>_\<^esup>") where 
  "FOREACHi \<Phi> S \<equiv> FOREACHci \<Phi> S (\<lambda>_. True)"

text {* Foreach with annotated invariant and order: *}
definition FOREACHoi ("FOREACH\<^sub>O\<^bsup>_,_\<^esup>") where 
  "FOREACHoi R \<Phi> S \<equiv> FOREACHoci R \<Phi> S (\<lambda>_. True)"

text {* Basic foreach *}
definition "FOREACH S \<equiv> FOREACHc S (\<lambda>_. True)"

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
  shows "FOREACHoci R I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHoci_def
  apply (intro refine_vcg)

  apply (rule FIN)

  apply (subgoal_tac "wf (measure (\<lambda>(xs, _). length xs))")
    apply assumption
    apply simp

  apply (insert I0, simp add: I0) []
  unfolding FOREACH_body_def FOREACH_cond_def
  apply (rule refine_vcg)+
  apply ((simp, elim conjE exE)+) []
  apply (rename_tac xs'' s xs' \<sigma> xs)
defer
  apply (simp, elim conjE exE)+
  apply (rename_tac x s xs' \<sigma> xs)
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
  shows "FOREACHoi R I S f \<sigma>0 \<le> SPEC P"
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

subsubsection {* Refinement: *}

text {*
  Refinement rule using a coupling invariant over sets of remaining
  items and the state.
*}

lemma FOREACHoci_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; 
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; \<forall>y\<in>it-{x}. RR x y;
    x'\<in>it'; \<forall>y'\<in>it'-{x'}. RR' x' y';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R' (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"
  (* TODO: Clean up this mess !!! *)
  unfolding FOREACHoci_def
  apply (refine_rcg WHILEIT_refine_genR[where 
    R'="{((xs,\<sigma>),(xs',\<sigma>')) . 
      xs'=map \<alpha> xs \<and> 
      set xs \<subseteq> S \<and> set xs' \<subseteq> S' \<and>
      (\<forall>x\<in>S - set xs. \<forall>y\<in>set xs. RR x y) \<and>
      (\<forall>x\<in>S' - set xs'. \<forall>y\<in>set xs'. RR' x y) \<and>
      ((set xs,\<sigma>),(set xs',\<sigma>')) \<in> R }"
    ])

  using REFS INJ apply (auto dest: finite_imageD) []
  apply (rule intro_prgR[where R="{(xs,xs') . xs'=map \<alpha> xs }"])
  apply (rule SPEC_refine_sv)
  apply (auto simp: single_valued_def) []
  using INJ RR_OK 
  apply (auto 
    simp add: distinct_map sorted_by_rel_map 
    intro: sorted_by_rel_weaken[of _ RR]) []
  using REF0 apply auto []
  defer

  apply simp apply (rule conjI)
  using INJ apply clarsimp
  apply (erule map_eq_concE)
  apply clarsimp
  apply (rule_tac x=l in exI)
  apply simp
  apply (subst inj_on_map_eq_map[where f=\<alpha>,symmetric])
  apply (rule subset_inj_on, assumption, blast)
  apply assumption

  apply (simp split: prod.split_asm, elim conjE)
  apply (rule REFPHI, auto) []

  apply (simp add: FOREACH_cond_def split: prod.split prod.split_asm, 
    intro allI impI conj_cong) []
  apply auto []
  apply (rule REFC, auto) []

  unfolding FOREACH_body_def
  apply refine_rcg
  apply (rule REFSTEP) []
  prefer 3 apply auto []
  prefer 3 apply auto []
  apply simp_all[13]
  apply auto []
  apply (case_tac aa, auto simp: FOREACH_cond_def) []
  apply auto []
  apply (auto simp: FOREACH_cond_def) []
  apply (clarsimp simp: FOREACH_cond_def)
  apply (rule ccontr)
  apply (case_tac aaa)
  apply (auto simp: sorted_by_rel_append) [2]

  apply (auto simp: FOREACH_cond_def) []
  apply (case_tac aaa)
  apply (auto) [2]

  apply (clarsimp simp: FOREACH_cond_def)
  apply (rule ccontr)
  apply (case_tac aaa)
  apply (auto simp: sorted_by_rel_append) [2]

  apply (clarsimp simp: FOREACH_cond_def)
  apply (clarsimp simp: FOREACH_cond_def)
  
  using SV apply (auto simp: single_valued_def) []
  
  apply (clarsimp simp: map_tl)
  apply (intro conjI)

  apply (case_tac aaa, auto) []
  apply (case_tac aaa, auto) []
  apply (case_tac aaa, auto simp: sorted_by_rel_append) []
  apply (case_tac aaa, auto simp: sorted_by_rel_append) []
  apply (case_tac aaa, auto) []

  apply (rule introR[where R="{((xs,\<sigma>),(xs',\<sigma>')). 
      xs'=map \<alpha> xs \<and> \<Phi> (set xs) \<sigma> \<and> \<Phi>' (set xs') \<sigma>' \<and>
      set xs \<subseteq> S \<and> set xs' \<subseteq> S' \<and>
      (\<forall>x\<in>S - set xs. \<forall>y\<in>set xs. RR x y) \<and>
      (\<forall>x\<in>S' - set xs'. \<forall>y\<in>set xs'. RR' x y) \<and>
      ((set xs,\<sigma>),(set xs',\<sigma>')) \<in> R \<and>
      \<not> FOREACH_cond c (xs,\<sigma>) \<and> \<not> FOREACH_cond c' (xs',\<sigma>')
    }
    "])
  apply auto []
  apply (rule SV')
  apply (simp add: FOREACH_cond_def, elim conjE)
  apply (elim disjE1, simp_all) []
  using REF_R_DONE apply auto []
  using REF_R_BRK apply auto []

  using SV apply (auto simp: single_valued_def) []
  done

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
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"

  apply (rule FOREACHoci_refine_genR[
    where R = "{((it,\<sigma>),(it',\<sigma>')). (\<sigma>,\<sigma>')\<in>R \<and> \<Phi>'' it \<sigma> it' \<sigma>'}"
    ])
  apply fact
  apply fact
  apply fact
  using REF0 REFPHI0 apply blast
  using REFC apply auto []
  using REFPHI apply auto []
  using REFSTEP apply auto []
  apply auto []
  apply auto []
  using SV apply (auto simp: single_valued_def) []
  apply fact
  done
 
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
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"
  apply (rule FOREACHoci_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHoci_weaken:
  assumes IREF: "\<And>it \<sigma>. it\<subseteq>S \<Longrightarrow> I it \<sigma> \<Longrightarrow> I' it \<sigma>"
  shows "FOREACHoci RR I' S c f \<sigma>0 \<le> FOREACHoci RR I S c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: IREF)
  done

lemma FOREACHoci_weaken_order:
  assumes RRREF: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> RR x y \<Longrightarrow> RR' x y"
  shows "FOREACHoci RR I S c f \<sigma>0 \<le> FOREACHoci RR' I S c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: RRREF)
  done


subsubsection {* Rules for Derived Constructs *}

lemma FOREACHoi_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; \<forall>y\<in>it-{x}. RR x y;
    x'\<in>it'; \<forall>y'\<in>it'-{x'}. RR' x' y'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R' (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHoi_def
  apply (rule FOREACHoci_refine_genR)
  apply (fact | simp)+
  using REFSTEP apply auto []
  apply (fact | simp)+
  done

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
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
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
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
  apply (rule FOREACHoi_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHci_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R' (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHci_def
  apply (rule FOREACHoci_refine_genR)
  apply (fact|simp)+
  using REFC apply auto []
  using REFPHI apply auto []
  using REFSTEP apply auto []
  apply (fact|simp)+
  using REF_R_BRK apply auto []
  apply (fact|simp)+
  done

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
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
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


lemma FOREACHc_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; 
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R' (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_genR)
  apply simp_all
  apply (fact|simp)+
  using REFC apply auto []
  using REFSTEP apply auto []
  using REF_R_DONE apply auto []
  using REF_R_BRK apply auto []
  apply (fact|simp)+
  done

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

lemma FOREACHi_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R' (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine_genR)
  apply (fact|simp)+
  using REFSTEP apply auto []
  apply (fact|simp)+
  done

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

lemma FOREACH_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" -- "Abstraction mapping of elements"
  fixes S :: "'S set" -- "Concrete set"
  fixes S' :: "'Sa set" -- "Abstract set"
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes SV: "single_valued { ((it,\<sigma>),(it',\<sigma>')) . 
    it'=\<alpha>`it \<and> ((it,\<sigma>),(it',\<sigma>'))\<in>R }"
  assumes SV': "single_valued R'"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R' (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine_genR)
  apply (fact|simp)+
  using REFSTEP apply auto []
  apply (fact|simp)+
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

subsubsection {* Alternative set of FOREACHc-rules *}
text {* Here, we provide an alternative set of FOREACH rules with 
  interruption. In some cases, they are easier to use, as they avoid 
  redundancy between the final cases for interruption and non-interruption *}

lemma FOREACHoci_rule':
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> c \<sigma>; x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma>;
                         \<forall>x\<in>it. \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoci R I S c f \<sigma>0 \<le> SPEC P"
  apply (rule FOREACHoci_rule[OF FIN, where I=I, OF I0])
  apply (rule IP, assumption+)
  apply (case_tac "c \<sigma>")
  apply (blast intro: II1)
  apply (blast intro: II2)
  apply (blast intro: II2)
  done
  
lemma FOREACHci_rule'[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHci I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHci_def
  by (rule FOREACHoci_rule') (simp_all add: assms)

lemma FOREACHc_rule':
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHc S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule'[where I=I])
  using assms by auto



subsection {* FOREACH with empty sets *}

lemma FOREACHoci_emp [simp] :
  "FOREACHoci R \<Phi> {} c f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
apply (simp add: FOREACHoci_def bind_RES image_def)
apply (simp add: WHILEIT_unfold FOREACH_cond_def)
done

lemma FOREACHoi_emp [simp] :
  "FOREACHoi R \<Phi> {} f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
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

subsubsection "Monotonicity"

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

subsubsection {* Transfer to fold *}
text {*
  A foreach-loop can be conveniently expressed as an operation that converts
  the set to a list, followed by folding over the list.
  
  This representation is handy for automatic refinement, as the complex 
  foreach-operation is expressed by two relatively simple operations.
*}

text {* We first define a fold-function in the nres-monad *}
partial_function (nrec) nfoldli where
  "nfoldli l c f s = (case l of 
    [] \<Rightarrow> RETURN s 
    | x#ls \<Rightarrow> if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURN s
  )"

lemma nfoldli_simps[simp]:
  "nfoldli [] c f s = RETURN s"
  "nfoldli (x#ls) c f s = 
    (if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURN s)"
  apply (subst nfoldli.simps, simp)+
  done
  
lemma param_nfoldli[param]:
  assumes "single_valued Rb"
  shows "(nfoldli,nfoldli) \<in> 
    \<langle>Ra\<rangle>list_rel \<rightarrow> (Rb\<rightarrow>Id) \<rightarrow> (Ra\<rightarrow>Rb\<rightarrow>\<langle>Rb\<rangle>nres_rel) \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  apply (intro fun_relI)
proof -
  case (goal1 l l' c c' f f' s s')
  thus ?case
    apply (induct arbitrary: s s')
    using assms
    apply -
    apply (simp only: nfoldli_simps True_implies_equals)
    apply parametricity
    apply (simp only: nfoldli_simps True_implies_equals)
    apply (parametricity)
    done
qed

text {* The fold-function over the nres-monad is transfered to a plain 
  foldli function *}
lemma nfoldli_transfer_plain[refine_transfer]:
  assumes "\<And>x s. RETURN (f x s) \<le> f' x s"
  shows "RETURN (foldli l c f s) \<le> (nfoldli l c f' s)"
  using assms
  apply (induct l arbitrary: s)
  apply (auto)
  by (metis (lifting) plain_bind)

lemma nfoldli_transfer_dres[refine_transfer]:
  fixes l :: "'a list" and c:: "'b \<Rightarrow> bool"
  assumes FR: "\<And>x s. nres_of (f x s) \<le> f' x s"
  shows "nres_of 
    (foldli l (dres_case False False c) (\<lambda>x s. s\<guillemotright>=f x) (dRETURN s)) 
    \<le> (nfoldli l c f' s)"
proof (induct l arbitrary: s)
  case Nil thus ?case by auto
next
  case (Cons a l)
  thus ?case
    apply (auto)
    apply (cases "f a s")
    apply (cases l, simp_all) []
    apply simp
    apply (rule order_trans[rotated])
    apply (rule bind_mono)
    apply (rule FR)
    apply assumption
    apply simp
    apply simp
    using FR[of a s]
    apply simp
    done
qed

lemma nfoldli_mono[refine_mono]:
  "\<lbrakk> \<And>x. f x \<le> f' x \<rbrakk> \<Longrightarrow> nfoldli l c f \<sigma> \<le> nfoldli l c f' \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply auto
  apply refine_mono
  done

text {* We relate our fold-function to the while-loop that we used in
  the original definition of the foreach-loop *}
lemma nfoldli_while: "nfoldli l c f \<sigma>
          \<le>
         (WHILE\<^sub>T\<^bsup>I\<^esup>
           (FOREACH_cond c) (FOREACH_body f) (l, \<sigma>) \<guillemotright>=
          (\<lambda>(_, \<sigma>). RETURN \<sigma>))"
proof (induct l arbitrary: \<sigma>)
  case Nil thus ?case by (subst WHILEIT_unfold) (auto simp: FOREACH_cond_def)
next
  case (Cons x ls)
  show ?case
  proof (cases "c \<sigma>")
    case False thus ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def
      by simp
  next
    case True[simp]
    from Cons show ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply clarsimp
      apply (rule Refine_Basic.bind_mono)
      apply simp_all
      done
  qed
qed

lemma while_nfoldli:
  "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (FOREACH_body f) (l,\<sigma>);
    RETURN \<sigma>
  } \<le> nfoldli l c f \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply (subst WHILET_unfold)
  apply (simp add: FOREACH_cond_def)

  apply (subst WHILET_unfold)
  apply (auto
    simp: FOREACH_cond_def FOREACH_body_def
    intro: bind_mono)
  done

lemma while_eq_nfoldli: "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (FOREACH_body f) (l,\<sigma>);
    RETURN \<sigma>
  } = nfoldli l c f \<sigma>"
  apply (rule antisym)
  apply (rule while_nfoldli)
  apply (rule order_trans[OF nfoldli_while[where I="\<lambda>_. True"]])
  apply (simp add: WHILET_def)
  done



(* TODO: Remove --- Hopefully obsolete 
definition "it_FOREACH tsl s c f \<sigma> \<equiv> do { 
  l \<leftarrow> tsl s; 
  nfoldli l c f \<sigma> 
}"

lemma param_it_FOREACH[param]:
  assumes "single_valued R\<sigma>"
  shows "(it_FOREACH,it_FOREACH) \<in> 
    (\<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel) \<rightarrow> \<langle>Rk\<rangle>Rs \<rightarrow> 
      (R\<sigma>\<rightarrow>Id) \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) 
    \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
  using assms
  unfolding it_FOREACH_def[abs_def]
  by parametricity

lemma FOREACH_to_it_FOREACH:
  fixes R I tsl
  defines "lspec \<equiv> \<lambda>s. (SPEC (\<lambda>l. distinct l \<and> s = set l \<and> sorted_by_rel R l))"
  assumes SV: "single_valued R\<sigma>"
  assumes LS: "\<And>s s'. (s,s')\<in>\<langle>Rk\<rangle>Rs \<Longrightarrow> tsl s \<le> \<Down>(\<langle>Rk\<rangle>list_rel) (lspec s')"
  shows "(it_FOREACH tsl,FOREACHoci R I) 
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (R\<sigma>\<rightarrow>Id) \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof (intro fun_relI nres_relI)
  fix s s' c c' f f' \<sigma> \<sigma>'
  assume [param]:
    "(s,s')\<in>\<langle>Rk\<rangle>Rs"
    "(c,c')\<in>R\<sigma>\<rightarrow>(Id::(bool\<times>_) set)" 
    "(f,f')\<in>Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel"
    "(\<sigma>,\<sigma>')\<in>R\<sigma>"

  have "it_FOREACH tsl s c f \<sigma> \<le> \<Down>R\<sigma> (it_FOREACH lspec s' c' f' \<sigma>')"
    apply (rule nres_relD)
    using SV LS[THEN nres_relI]
    by parametricity
  also have 
    "it_FOREACH lspec s' c' f' \<sigma>' \<le> FOREACHoci R I s' c' f' \<sigma>'"
    apply (rule refine_IdD)
    unfolding it_FOREACH_def FOREACHoci_def lspec_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done 
  finally show "it_FOREACH tsl s c f \<sigma> \<le> \<Down> R\<sigma> (FOREACH\<^sub>O\<^sub>C\<^bsup>R,I\<^esup> s' c' f' \<sigma>')" .
qed

lemma it_FOREACH_transfer_plain[refine_transfer]:
  assumes "\<And>s. RETURN (tsl s) \<le> TSL s"
  assumes "\<And>x \<sigma>. RETURN (f x \<sigma>) \<le> F x \<sigma>"
  shows "RETURN (foldli (tsl s) c f \<sigma>) \<le> it_FOREACH TSL s c F \<sigma>"
proof -
  have "RETURN (let x = tsl s in foldli x c f \<sigma>) \<le> it_FOREACH TSL s c F \<sigma>"
    using assms
    unfolding it_FOREACH_def
    apply refine_transfer
    done
  thus ?thesis by simp
qed

definition "dres_it_FOREACH tsl s c f \<sigma> \<equiv> 
  tsl s \<guillemotright>= (\<lambda>l. foldli l (dres_case False False c) (\<lambda>x s. s\<guillemotright>=f x) (dRETURN \<sigma>))"

lemma it_FOREACH_transfer_dres[refine_transfer]:
  assumes "\<And>s. nres_of (tsl s) \<le> (TSL s)"
  assumes "\<And>x \<sigma>. nres_of (f x \<sigma>) \<le> F x \<sigma>"
  shows "nres_of (dres_it_FOREACH tsl s c f \<sigma>) \<le> it_FOREACH TSL s c F \<sigma>"
  using assms
  unfolding it_FOREACH_def dres_it_FOREACH_def
  by refine_transfer

lemma it_FOREACH_mono[refine_mono]:
  "\<lbrakk> \<And>x. f x \<le> f' x \<rbrakk> \<Longrightarrow> it_FOREACH it s c f \<sigma> \<le> it_FOREACH it s c f' \<sigma>"
  unfolding it_FOREACH_def
  by refine_mono
*)


lemma foldli_mono_dres_aux1:
  fixes \<sigma> :: "'a :: {order_bot, order_top}"
  assumes COND: "\<And>\<sigma> \<sigma>'. \<sigma>\<le>\<sigma>' \<Longrightarrow> c \<sigma> \<noteq> c \<sigma>' \<Longrightarrow> \<sigma>=bot \<or> \<sigma>'=top "
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes B: "\<sigma>\<le>\<sigma>'"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l c f \<sigma> \<le> foldli l c f' \<sigma>'"
proof -
  { fix l 
    have "foldli l c f bot = bot" by (induct l) (auto simp: STRICT)
  } note [simp] = this
  { fix l 
    have "foldli l c f' top = top" by (induct l) (auto simp: STRICT)
  } note [simp] = this

  show ?thesis
    using B
    apply (induct l arbitrary: \<sigma> \<sigma>')
    apply (auto simp: A STRICT dest!: COND)
    done
qed

lemma foldli_mono_dres_aux2:
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l (dres_case False False c) f \<sigma> 
    \<le> foldli l (dres_case False False c) f' \<sigma>"
  apply (rule foldli_mono_dres_aux1)
  apply (simp_all split: dres.split_asm add: STRICT A)
  done

lemma foldli_mono_dres[refine_mono]:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "foldli l (dres_case False False c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> foldli l (dres_case False False c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
  apply (rule foldli_mono_dres_aux2)
  apply (simp_all)
  apply (rule dbind_mono)
  apply (simp_all add: A)
  done

(*
lemma dres_it_FOREACH_mono[refine_mono]: 
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "dres_it_FOREACH l s c f \<sigma> \<le> dres_it_FOREACH l s c f' \<sigma>"
  using assms
  unfolding dres_it_FOREACH_def
  by refine_mono
*)

lemma dres_foldli_ne_bot[refine_transfer]:
  assumes 1: "\<sigma> \<noteq> dSUCCEED"
  assumes 2: "\<And>x \<sigma>. f x \<sigma> \<noteq> dSUCCEED"
  shows "foldli l c (\<lambda>x s. s \<guillemotright>= f x) \<sigma> \<noteq> dSUCCEED"
  using 1 apply (induct l arbitrary: \<sigma>)
  apply simp
  apply (simp split: dres.split, intro allI impI)
  apply rprems
  using 2
  apply (simp add: dres_ne_bot_basic)
  done

(*lemma dres_it_FOREACH_ne_bot[refine_transfer]:
  assumes "\<And>s. l s\<noteq>dSUCCEED"
  assumes "\<And>x \<sigma>. f x \<sigma> \<noteq> dSUCCEED"
  shows "dres_it_FOREACH l s c f \<sigma> \<noteq> dSUCCEED"
  using assms
  unfolding dres_it_FOREACH_def
  apply refine_transfer
  done
*)

subsection {* Autoref Setup *}
text {*
  Foreach-loops are mapped to the combinator @{text "LIST_FOREACH"}, that
  takes as first argument an explicit @{text "to_list"} operation. 
  This mapping is done during operation identification. 
  It is then the responsibility of the various implementations to further map
  the @{text "to_list"} operations to custom @{text "to_list"} operations, like
  @{text "set_to_list"}, @{text "map_to_list"}, @{text "nodes_to_list"}, etc.
*}

text {* This constant is a placeholder to be converted to
  custom operations by pattern rules *}
definition "it_to_sorted_list R s 
  \<equiv> SPEC (\<lambda>l. distinct l \<and> s = set l \<and> sorted_by_rel R l)"

definition "LIST_FOREACH \<Phi> tsl c f \<sigma>0 \<equiv> do {
  xs \<leftarrow> tsl;
  (_,\<sigma>) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(it, \<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>\<^esup>
    (FOREACH_cond c) (FOREACH_body f) (xs, \<sigma>0);
    RETURN \<sigma>}"

lemma FOREACHoci_by_LIST_FOREACH:
  "FOREACHoci R \<Phi> S c f \<sigma>0 = do {
    ASSERT (finite S);
    LIST_FOREACH \<Phi> (it_to_sorted_list R S) c f \<sigma>0
  }"
  unfolding OP_def FOREACHoci_def LIST_FOREACH_def it_to_sorted_list_def 
  by simp

text {* Patterns that convert FOREACH-constructs 
  to @{text "LIST_FOREACH"}
*}
context begin interpretation autoref_syn .
lemma FOREACH_patterns[autoref_op_pat]: 
  "FOREACHoci R \<Phi> s c f \<sigma> \<equiv> do {
    ASSERT (finite s);
    OP (LIST_FOREACH \<Phi>) (it_to_sorted_list R s) c f \<sigma>
  }"
  "FOREACHc s c f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s c f \<sigma>"
  "FOREACH s f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s (\<lambda>_. True) f \<sigma>"
  "FOREACHci I s c f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) I s c f \<sigma>"
  "FOREACHi I s f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) I s (\<lambda>_. True) f \<sigma>"
  "FOREACHoi R I s f \<sigma> \<equiv> FOREACHoci R I s (\<lambda>_. True) f \<sigma>"
  unfolding 
    FOREACHoci_by_LIST_FOREACH[abs_def]
    FOREACHc_def[abs_def] 
    FOREACH_def[abs_def] 
    FOREACHci_def[abs_def] 
    FOREACHi_def[abs_def] 
    FOREACHoi_def[abs_def] 
  by simp_all
end
definition "LIST_FOREACH' tsl c f \<sigma> \<equiv> do {xs \<leftarrow> tsl; nfoldli xs c f \<sigma>}"

lemma LIST_FOREACH'_param[param]: 
  assumes "single_valued R\<sigma>"
  shows "(LIST_FOREACH',LIST_FOREACH') 
  \<in> (\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel \<rightarrow> (R\<sigma>\<rightarrow>bool_rel) 
    \<rightarrow> (Rv \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel)"
  using assms
  unfolding LIST_FOREACH'_def[abs_def]
  by parametricity

lemma LIST_FOREACH_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  shows "(LIST_FOREACH', LIST_FOREACH \<Phi>) \<in> 
    (\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel \<rightarrow> (R\<sigma>\<rightarrow>bool_rel) 
      \<rightarrow> (Rv \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel)"
proof (intro fun_relI nres_relI)
  fix tsl tsl' c c' f f' \<sigma> \<sigma>'
  assume [param]:
    "(tsl,tsl')\<in>\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel"
    "(c,c')\<in>R\<sigma>\<rightarrow>bool_rel" 
    "(f,f')\<in>Rv\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel"
    "(\<sigma>,\<sigma>')\<in>R\<sigma>"

  note SV = SV[simplified]

  have "LIST_FOREACH' tsl c f \<sigma> \<le> \<Down>R\<sigma> (LIST_FOREACH' tsl' c' f' \<sigma>')"
    apply (rule nres_relD)
    using SV
    by parametricity
  also have "LIST_FOREACH' tsl' c' f' \<sigma>'
    \<le> LIST_FOREACH \<Phi> tsl' c' f' \<sigma>'"
    apply (rule refine_IdD)
    unfolding LIST_FOREACH_def LIST_FOREACH'_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done 
  finally show 
    "LIST_FOREACH' tsl c f \<sigma> \<le> \<Down> R\<sigma> (LIST_FOREACH \<Phi> tsl' c' f' \<sigma>')"
    .
qed

lemma LIST_FOREACH'_mono[refine_mono]:
  assumes "tsl \<le> tsl'"
  assumes "\<And>x \<sigma>. f x \<sigma> \<le> f' x \<sigma>"
  shows "LIST_FOREACH' tsl c f \<sigma> \<le> LIST_FOREACH' tsl' c f' \<sigma>"
  using assms unfolding LIST_FOREACH'_def
  by refine_mono

lemma LIST_FOREACH'_transfer_plain[refine_transfer]:
  assumes "RETURN tsl \<le> tsl'"
  assumes "\<And>x \<sigma>. RETURN (f x \<sigma>) \<le> f' x \<sigma>"
  shows "RETURN (foldli tsl c f \<sigma>) \<le> LIST_FOREACH' tsl' c f' \<sigma>"
  apply (rule order_trans[rotated])
  unfolding LIST_FOREACH'_def
  using assms
  apply refine_transfer
  by simp

thm refine_transfer

lemma LIST_FOREACH'_transfer_nres[refine_transfer]:
  assumes "nres_of tsl \<le> tsl'"
  assumes "\<And>x \<sigma>. nres_of (f x \<sigma>) \<le> f' x \<sigma>"
  shows "nres_of (
    do {
      xs\<leftarrow>tsl; 
      foldli xs (dres_case False False c) (\<lambda>x s. s\<guillemotright>=f x) (dRETURN \<sigma>)
    }) \<le> LIST_FOREACH' tsl' c f' \<sigma>"
  unfolding LIST_FOREACH'_def
  using assms
  by refine_transfer

(*
lemma FOREACHoci_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS: "GEN_OP tsl (it_to_sorted_list R) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(it_FOREACH tsl,FOREACHoci R I)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (R\<sigma>\<rightarrow>Id) \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
  using FOREACH_to_it_FOREACH[OF SV[simplified], OF nres_relD] LS
  apply (simp add: it_to_sorted_list_def[abs_def])
  apply parametricity
  apply (erule (1) fun_relD)
  done

lemma FOREACHoi_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS: "GEN_OP tsl (it_to_sorted_list R) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(\<lambda>s. it_FOREACH tsl s (\<lambda>_. True),FOREACHoi R I)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof -
  note [relator_props] = SV[unfolded autoref_tag_defs]
  note [autoref_rules] = LS[unfolded autoref_tag_defs]
  show ?thesis
    unfolding FOREACHoi_def[abs_def]
    by (autoref (keep_goal))

qed

lemma FOREACHci_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS: 
    "GEN_OP tsl (it_to_sorted_list (\<lambda>_ _. True)) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(it_FOREACH tsl,FOREACHci I)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (R\<sigma>\<rightarrow>Id) \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof -
  note [relator_props] = SV[unfolded autoref_tag_defs]
  note [autoref_rules] = LS[unfolded autoref_tag_defs]
  show ?thesis
    unfolding FOREACHci_def[abs_def]
    by (autoref)
qed

lemma FOREACHi_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS:
    "GEN_OP tsl (it_to_sorted_list (\<lambda>_ _. True)) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(\<lambda>s. it_FOREACH tsl s (\<lambda>_. True),FOREACHi I)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof -
  note [relator_props] = SV[unfolded autoref_tag_defs]
  note [autoref_rules] = LS[unfolded autoref_tag_defs]
  show ?thesis
    unfolding FOREACHi_def[abs_def]
    by (autoref (keep_goal))
qed

lemma FOREACHc_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS:
    "GEN_OP tsl (it_to_sorted_list (\<lambda>_ _. True)) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(it_FOREACH tsl,FOREACHc)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (R\<sigma>\<rightarrow>Id) \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof -
  note [relator_props] = SV[unfolded autoref_tag_defs]
  note [autoref_rules] = LS[unfolded autoref_tag_defs]
  show ?thesis
    unfolding FOREACHc_def[abs_def]
    by (autoref)
qed

lemma FOREACH_autoref[autoref_rules]:
  assumes SV: "PREFER single_valued R\<sigma>"
  assumes LS:
    "GEN_OP tsl (it_to_sorted_list (\<lambda>_ _. True)) (\<langle>Rk\<rangle>Rs\<rightarrow>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel)"
  shows "(\<lambda>s. it_FOREACH tsl s (\<lambda>_. True),FOREACH)
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> (Rk\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel"
proof -
  note [relator_props] = SV[unfolded autoref_tag_defs]
  note [autoref_rules] = LS[unfolded autoref_tag_defs]
  show ?thesis
    unfolding FOREACH_def[abs_def]
    by (autoref (keep_goal))
qed
*)

text {* Simplification rules to summarize iterators *}
lemma [refine_transfer_post_simp]: 
  "do {
    xs \<leftarrow> dRETURN tsl;
    foldli xs c f \<sigma>
  } = foldli tsl c f \<sigma>" 
  by simp

lemma [refine_transfer_post_simp]: 
  "(let xs = tsl in foldli xs c f \<sigma>) = foldli tsl c f \<sigma>" 
  by simp

subsection {* Miscellanneous Utility Lemmas *}

(* TODO: Can we make this somewhat more general ? *)
lemma map_foreach:
  assumes "finite S"
  shows "FOREACH S (\<lambda>x \<sigma>. RETURN (insert (f x) \<sigma>)) R0 \<le> SPEC (op = (R0 \<union> f`S))"
  apply (rule FOREACH_rule[where I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(S-it)"])
  apply (auto intro: assms)
  done

lemma map_sigma_foreach:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c"
  assumes "finite A"
  assumes "\<And>x. x\<in>A \<Longrightarrow> finite (B x)"
  shows "FOREACH A (\<lambda>a \<sigma>. 
    FOREACH (B a) (\<lambda>b \<sigma>. RETURN (insert (f (a,b)) \<sigma>)) \<sigma>
  ) R0 \<le> SPEC (op = (R0 \<union> f`Sigma A B))"
  apply (rule FOREACH_rule[where I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A-it) B)"])
  apply (auto intro: assms) [2]
  
  apply (rule_tac I="\<lambda>it' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) B) 
    \<union> f`({x} \<times> (B x - it'))"
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  apply (rule refine_vcg)
  apply auto []
  apply auto []
  apply auto []
  done

lemma map_sigma_sigma_foreach:
  fixes f :: "'a \<times> ('b \<times> 'c) \<Rightarrow> 'd"
  assumes "finite A"
  assumes "\<And>a. a\<in>A \<Longrightarrow> finite (B a)"
  assumes "\<And>a b. \<lbrakk>a\<in>A; b\<in>B a\<rbrakk> \<Longrightarrow> finite (C a b)"
  shows "FOREACH A (\<lambda>a \<sigma>. 
    FOREACH (B a) (\<lambda>b \<sigma>. 
      FOREACH (C a b) (\<lambda>c \<sigma>.
        RETURN (insert (f (a,(b,c))) \<sigma>)) \<sigma>) \<sigma>
  ) R0 \<le> SPEC (op = (R0 \<union> f`Sigma A (\<lambda>a. Sigma (B a) (C a))))"
  apply (rule FOREACH_rule[where 
    I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A-it) (\<lambda>a. Sigma (B a) (C a)))"])
  apply (auto intro: assms) [2]
  apply (rule_tac 
    I="\<lambda>it' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) (\<lambda>a. Sigma (B a) (C a))) 
      \<union> f`({x} \<times> ( Sigma (B x - it') (C x)))"
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  apply (rule_tac 
    I="\<lambda>it'' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) (\<lambda>a. Sigma (B a) (C a))) 
      \<union> f`({x} \<times> ( Sigma (B x - ita) (C x)))
      \<union> f`({x} \<times> ({xa} \<times> (C x xa - it'')))
    "
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  
  apply auto
  done

end
