header {* \isaheader{Foreach Loops} *}
theory Refine_Foreach
imports Refine_While Iterator_Locale
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
  Foreach-loops come in four versions, depending on whether they have an 
  annotated invariant (I), and a termination condition (C).

  Note that asserting that the set is finite is not necessary to guarantee
  termination. However, we currently provide only iteration over finite sets,
  as this also matches the ICF concept of iterators.
*}
   
definition "FOREACH_body f \<equiv> \<lambda>(S,\<sigma>). do {
  x\<leftarrow>RES S; \<sigma>'\<leftarrow>f x \<sigma>; RETURN (S-{x},\<sigma>')
  }"

definition FOREACH_cond where "FOREACH_cond c \<equiv> (\<lambda>(S,\<sigma>). S\<noteq>{} \<and> c \<sigma>)"

text {* Foreach with continuation condition and annotated invariant: *}
definition FOREACHci ("FOREACH\<^isub>C\<^bsup>_\<^esup>") where "FOREACHci \<Phi> S c f \<sigma>0 \<equiv> do {
  ASSERT (finite S);
  (_,\<sigma>) \<leftarrow> WHILEIT 
    (\<lambda>(it,\<sigma>). it\<subseteq>S \<and> \<Phi> it \<sigma>) (FOREACH_cond c) (FOREACH_body f) (S,\<sigma>0); 
  RETURN \<sigma> }"

text {* Foreach with continuation condition: *}
definition FOREACHc ("FOREACH\<^isub>C") where "FOREACHc \<equiv> FOREACHci (\<lambda>_ _. True)"

text {* Foreach with annotated invariant: *}
definition FOREACHi ("FOREACH\<^bsup>_\<^esup>") where 
  "FOREACHi \<Phi> S f \<sigma>0 \<equiv> FOREACHci \<Phi> S (\<lambda>_. True) f \<sigma>0"

text {* Basic foreach *}
definition "FOREACH S f \<sigma>0 \<equiv> FOREACHc S (\<lambda>_. True) f \<sigma>0"

subsection {* Proof Rules *}
lemma FOREACHci_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHci I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHci_def
  apply (intro refine_vcg)

  apply (rule FIN)

  apply (subgoal_tac "wf (finite_psubset <*lex*> {})")
    apply assumption
    apply auto []

  apply (simp add: I0)
  unfolding FOREACH_body_def
  apply (rule refine_vcg)+
  apply simp
  apply (rule order_trans[OF IP], assumption)
  apply simp
  apply simp
  apply (rule refine_vcg)+
  apply (auto simp: finite_subset) []
  apply (simp add: FOREACH_cond_def)
  apply (erule disjE)
  apply (simp add: II1)
  apply (case_tac "a={}")
  apply (simp add: II1)
  apply (simp add: II2)
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
  apply (rule ASSERT_refine_right ASSERT_refine_left)+
  using REFS INJ apply (auto dest: finite_imageD) []

  apply (rule bind_refine)
  apply (rule_tac WHILEIT_refine)
  apply (subgoal_tac "((S, \<sigma>0), S', \<sigma>0')\<in>{((s,\<sigma>),(s',\<sigma>')). 
    s'=\<alpha>`s \<and> s\<subseteq>S \<and> s'\<subseteq> S' \<and> (\<sigma>,\<sigma>')\<in>R \<and> \<Phi>'' s \<sigma> s' \<sigma>'}", assumption)
  apply (auto simp: REFS REF0 REFPHI0) []

  apply (auto intro: single_valuedI single_valuedD[OF SV]) []

  using REFPHI apply auto []
  using REFC apply (auto simp add: FOREACH_cond_def) []

  apply (simp (no_asm) only: FOREACH_body_def) []
  txt {* Important: Here, we need more information about the binding! Hence
    using @{text "bind_refine'"} !*}

  apply (split prod.split, intro allI impI)+

  apply (rule bind_refine')+
    apply (subgoal_tac "RES a \<le> \<Down>{(s,s'). s'=\<alpha> s} (RES aa)", assumption)
    apply (rule RES_refine, auto) []
  
    apply (rule bind_refine)
      apply (rule REFSTEP)
        apply simp
        apply (subgoal_tac "xa\<in>a", assumption)
        apply simp
        apply (subgoal_tac "x'a\<in>aa", assumption)
        apply simp
        apply (auto) []
        apply simp
        apply auto []
        apply simp
        apply simp
        apply auto []
        apply (simp add: FOREACH_cond_def)
        apply (simp add: FOREACH_cond_def)
        apply simp
        apply (rule RETURN_refine_sv)
        apply (auto intro: single_valuedI single_valuedD[OF SV]) []

      using INJ apply (auto dest: inj_onD) []

  apply (split prod.split, intro allI impI)+
  apply (rule RETURN_refine_sv[OF SV])
  apply (auto)
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

subsubsection {* Rules for Derived Constructs *}
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

abbreviation lift_it :: "('x,'mc) iteratori_tmpl \<Rightarrow> 
  ('s\<Rightarrow>bool) \<Rightarrow> ('x \<Rightarrow> 's \<Rightarrow> 'mc) \<Rightarrow> 's \<Rightarrow> 'mc"
  where
  "lift_it it c f s0 \<equiv> it 
    (liftc c) 
    (\<lambda>x s. cbind s (f x)) 
    (creturn s0)"


lemma transfer_FOREACHci[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iteratori iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate c f s0) \<le> FOREACHci I X c F s0"
proof -
  interpret set_iteratori iterate X by fact

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
    fix it::"'x set" and x and s :: "'s"
    assume MEM: "x\<in>it" and C: "c s"
    have "do{ s'\<leftarrow>F x s; RL (it-{x}, s')} \<le> RL (it,s)"
      apply (subst (2) RL_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply (rule pw_leI)
      using MEM C apply (simp add: refine_pw_simps)
      apply blast
      done
  } note RL_unfold_step=this

  have RL_le: "RL (X,s0) \<le> FOREACHci I X c F s0"
    unfolding RL_def' FOREACHci_def
    apply (rule le_ASSERTI)
    apply (rule order_trans[OF _ monoD[OF bind_mono1 WHILEI_le_WHILEIT]])
    apply (rule order_trans[OF _ monoD[OF bind_mono1 
      WHILEI_weaken[OF TrueI]]])
    apply (fold WHILE_def)
    apply (fold RL_def')
    by simp


  show ?thesis
    apply (rule order_trans[OF _ RL_le])
    apply (rule_tac 
      I="\<lambda>it \<sigma>. do { s\<leftarrow>\<alpha> \<sigma>; RL (it,s) } \<le> RL (X,s0)"
      in iterate_rule_P)

      apply (rule order_trans[OF bind_mono[OF transfer_return order_refl]])
      apply simp

      apply (case_tac "\<alpha> \<sigma> = FAIL")
      apply simp
      apply (erule order_trans[rotated])
      apply (rule order_trans[rotated, 
        OF bind_mono[OF order_refl RL_unfold_step]])
      apply assumption
      apply (simp add: liftc)
      apply (subst nres_monad3[symmetric])
      apply (rule bind_mono[OF _ order_refl])
      apply (rule transfer_bind)
      apply simp
      apply (rule RS)

      apply (erule order_trans[rotated])
      apply (subst RL_unfold)
      apply (simp add: FOREACH_cond_def)

      apply (erule order_trans[rotated])
      apply (subst RL_unfold)
      apply (simp add: FOREACH_cond_def)
      
      apply (rule pw_leI)
      apply rule
      apply rule
      apply (simp add: refine_pw_simps)
      using liftc[simplified pw_le_iff]
      apply (auto simp add: refine_pw_simps)
      done
  qed

lemma transfer_FOREACHc[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iteratori iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate c f s0) \<le> FOREACHc X c F s0"
  unfolding FOREACHc_def using assms by (rule transfer_FOREACHci)

lemma transfer_FOREACHI[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iteratori iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate (\<lambda>_. True) f s0) \<le> FOREACHi I X F s0"
  unfolding FOREACHi_def 
  using assms by (rule transfer_FOREACHci)

lemma det_FOREACH[refine_transfer]:
  fixes X :: "'x set" and s0 :: "'s"
  assumes IT: "set_iteratori iterate X"
  assumes RS: "\<And>x s. \<alpha> (f x s) \<le> F x s"
  shows "\<alpha> (lift_it iterate (\<lambda>_. True) f s0) \<le> FOREACH X F s0"
  unfolding FOREACH_def
  using assms by (rule transfer_FOREACHc)

end

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
