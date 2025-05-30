theory Ground_Term_Rewrite_System
  imports 
    Generic_Context 
    "Abstract-Rewriting.Abstract_Rewriting"
begin

(* TODO: Find way to not have this as locale! *)
locale ground_term_rewrite_system = 
  "context" where apply_context = apply_context 
  for apply_context :: "'c \<Rightarrow> 't \<Rightarrow> 't"
begin

definition compatible_with_context :: "'t rel \<Rightarrow> bool" where
  "compatible_with_context I \<longleftrightarrow> (\<forall>t t' c. (t, t') \<in> I \<longrightarrow> (c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I)"

lemma compatible_with_contextD:
  "compatible_with_context I \<Longrightarrow> (t, t') \<in> I \<Longrightarrow> (c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I"
  by (simp add: compatible_with_context_def)

lemma compatible_with_context_converse:
  assumes "compatible_with_context I"
  shows "compatible_with_context (I\<inverse>)"
  unfolding compatible_with_context_def
proof (intro allI impI)
  fix t t' c
  assume "(t, t') \<in> I\<inverse>"
  thus "(c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I\<inverse>"
    by (simp add: assms compatible_with_contextD)
qed

lemma compatible_with_context_symcl:
  assumes "compatible_with_context I"
  shows "compatible_with_context (I\<^sup>\<leftrightarrow>)"
  unfolding compatible_with_context_def
proof (intro allI impI)
  fix t t' c
  assume "(t, t') \<in> I\<^sup>\<leftrightarrow>"
  thus "(c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I\<^sup>\<leftrightarrow>"
    using assms compatible_with_contextD 
    by auto
qed

lemma compatible_with_context_rtrancl:
  assumes "compatible_with_context I"
  shows "compatible_with_context (I\<^sup>*)"
  unfolding compatible_with_context_def
proof (intro allI impI)
  fix t t' c
  assume "(t, t') \<in> I\<^sup>*"
  thus "(c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I\<^sup>*"
  proof (induction t' rule: rtrancl_induct)
    case base

    show ?case
      by simp
  next
    case (step y z)

    thus ?case
      using assms[unfolded compatible_with_context_def]
      by (meson rtrancl.rtrancl_into_rtrancl)
  qed
qed

lemma compatible_with_context_relcomp:
  assumes "compatible_with_context I1" and "compatible_with_context I2"
  shows "compatible_with_context (I1 O I2)"
  unfolding compatible_with_context_def
proof (intro allI impI)
  fix t t'' c
  assume "(t, t'') \<in> I1 O I2"

  then obtain t' where "(t, t') \<in> I1" and "(t', t'') \<in> I2"
    by auto

  have "(c\<langle>t\<rangle>, c\<langle>t'\<rangle>) \<in> I1"
    using \<open>(t, t') \<in> I1\<close> assms(1) compatible_with_contextD 
    by blast

  moreover have "(c\<langle>t'\<rangle>, c\<langle>t''\<rangle>) \<in> I2"
    using \<open>(t', t'') \<in> I2\<close> assms(2) compatible_with_contextD 
    by blast

  ultimately show "(c\<langle>t\<rangle>, c\<langle>t''\<rangle>) \<in> I1 O I2"
    by auto
qed

lemma compatible_with_context_join:
  assumes "compatible_with_context I"
  shows "compatible_with_context (I\<^sup>\<down>)"
  using assms
  unfolding join_def
  by (simp add: compatible_with_context_relcomp compatible_with_context_rtrancl
        compatible_with_context_converse)

lemma compatible_with_context_conversion:
  assumes "compatible_with_context I"
  shows "compatible_with_context (I\<^sup>\<leftrightarrow>\<^sup>*)"
  using  assms
  unfolding conversion_def
  by (simp add: compatible_with_context_rtrancl compatible_with_context_symcl)

definition rewrite_in_context :: "'t rel \<Rightarrow> 't rel" where
  "rewrite_in_context R = {(c\<langle>t\<^sub>1\<rangle>, c\<langle>t\<^sub>2\<rangle>) | c t\<^sub>1 t\<^sub>2. (t\<^sub>1, t\<^sub>2) \<in> R}"

lemma mem_rewrite_in_context_if_mem_rewrite_rules[intro]:
  "(l, r) \<in> R \<Longrightarrow> (l, r) \<in> rewrite_in_context R"   
  unfolding rewrite_in_context_def mem_Collect_eq
  by (metis apply_hole)

lemma context_mem_rewrite_in_context_if_mem_rewrite_rules[intro]:
  "(l, r) \<in> R \<Longrightarrow> (c\<langle>l\<rangle>, c\<langle>r\<rangle>) \<in> rewrite_in_context R"
  by (auto simp: rewrite_in_context_def)

lemma rewrite_in_context_mono: "R \<subseteq> S \<Longrightarrow> rewrite_in_context R \<subseteq> rewrite_in_context S"
  by (auto simp add: rewrite_in_context_def)

lemma rewrite_in_context_union:
  "rewrite_in_context (R \<union> S) = rewrite_in_context R \<union> rewrite_in_context S"
  by (auto simp add: rewrite_in_context_def)

lemma rewrite_in_context_insert:
  "rewrite_in_context (insert r R) = rewrite_in_context {r} \<union> rewrite_in_context R"
  using rewrite_in_context_union[of "{r}" R, simplified] .

lemma converse_rewrite_steps: "(rewrite_in_context R)\<inverse> = rewrite_in_context (R\<inverse>)"
  by (auto simp: rewrite_in_context_def)

lemma rhs_lt_lhs_if_rule_in_rewrite_in_context:
  fixes less_trm :: "'t \<Rightarrow> 't \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    rule_in: "(t1, t2) \<in> rewrite_in_context R" and
    ball_R_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    compatible_with_context: "\<And>t1 t2 c. t2 \<prec>\<^sub>t t1 \<Longrightarrow> c\<langle>t2\<rangle> \<prec>\<^sub>t c\<langle>t1\<rangle>"
  shows "t2 \<prec>\<^sub>t t1"
proof -
  from rule_in obtain t1' t2' c where
    "(t1', t2') \<in> R" and
    "t1 = c\<langle>t1'\<rangle>" and
    "t2 = c\<langle>t2'\<rangle>"
    by (auto simp: rewrite_in_context_def)

  from ball_R_rhs_lt_lhs have "t2' \<prec>\<^sub>t t1'"
    using \<open>(t1', t2') \<in> R\<close> 
    by simp

  with compatible_with_context have "c\<langle>t2'\<rangle> \<prec>\<^sub>t c\<langle>t1'\<rangle>"
    by metis

  thus ?thesis
    using \<open>t1 = c\<langle>t1'\<rangle>\<close> \<open>t2 = c\<langle>t2'\<rangle>\<close> 
    by metis
qed

lemma mem_rewrite_step_union_NF:
  assumes "(t, t') \<in> rewrite_in_context (R1 \<union> R2)"
    "t \<in> NF (rewrite_in_context R2)"
  shows "(t, t') \<in> rewrite_in_context R1"
  using assms
  unfolding rewrite_in_context_union
  by blast

lemma predicate_holds_of_mem_rewrite_in_context:
  assumes rule_in: "(t1, t2) \<in> rewrite_in_context R" and
    ball_P: "\<And>t1 t2. (t1, t2) \<in> R \<Longrightarrow> P t1 t2" and
    preservation: "\<And>t1 t2 c. (t1, t2) \<in> R \<Longrightarrow> P t1 t2 \<Longrightarrow> P c\<langle>t1\<rangle> c\<langle>t2\<rangle>"
  shows "P t1 t2"
proof -
  from rule_in obtain t1' t2' c where
    "(t1', t2') \<in> R" and
    "t1 = c\<langle>t1'\<rangle>" and
    "t2 = c\<langle>t2'\<rangle>"
    by (auto simp: rewrite_in_context_def)

  thus ?thesis
    using ball_P[OF \<open>(t1', t2') \<in> R\<close>]
    using preservation[OF \<open>(t1', t2') \<in> R\<close>]
    by simp
qed

lemma compatible_with_context_rewrite_in_context [simp]:
  "compatible_with_context (rewrite_in_context E)"
  unfolding compatible_with_context_def rewrite_in_context_def mem_Collect_eq
  by (metis Pair_inject compose_context_iff)

lemma subset_rewrite_in_context [simp]: "E \<subseteq> rewrite_in_context E"
proof (rule Set.subsetI)
  fix e 
  assume e_in: "e \<in> E"

  moreover obtain s t where e_def: "e = (s, t)"
    by fastforce

  show "e \<in> rewrite_in_context E"
    unfolding rewrite_in_context_def mem_Collect_eq
  proof (intro exI conjI)
    show "e = (\<box>\<langle>s\<rangle>, \<box>\<langle>t\<rangle>)"
      unfolding e_def
      by simp
  next
    show "(s, t) \<in> E"
      using e_in
      unfolding e_def .
  qed
qed

lemma wf_converse_rewrite_in_context:
  fixes E :: "'t rel"
  assumes
    wfP_R: "wfP R" and
    R_compatible_with_context: "\<And>c t t'. R t t' \<Longrightarrow> R c\<langle>t\<rangle> c\<langle>t'\<rangle>" and
    equations_subset_R: "\<And>x y. (x, y) \<in> E \<Longrightarrow> R y x"
  shows "wf ((rewrite_in_context E)\<inverse>)"
proof (rule wf_subset)
  from wfP_R show "wf {(x, y). R x y}"
    by (simp add: wfp_def)
next
  show "(rewrite_in_context E)\<inverse> \<subseteq> {(x, y). R x y}"
  proof (rule Set.subsetI)
    fix e 
    assume "e \<in> (rewrite_in_context E)\<inverse>"

    then obtain c s t where e_def: "e = (c\<langle>s\<rangle>, c\<langle>t\<rangle>)" and "(t, s) \<in> E"
      by (smt (verit) Pair_inject converseE mem_Collect_eq rewrite_in_context_def)

    hence "R s t"
      using equations_subset_R 
      by simp

    hence "R c\<langle>s\<rangle> c\<langle>t\<rangle>"
      using R_compatible_with_context 
      by simp

    then show "e \<in> {(x, y). R x y}"
      by (simp add: e_def)
  qed
qed

lemma rewrite_in_context_add_context [intro]:
  assumes "(s, t) \<in> (rewrite_in_context R)"
  shows "(c\<langle>s\<rangle>, c\<langle>t\<rangle>) \<in> (rewrite_in_context R)"
  using assms 
  unfolding rewrite_in_context_def mem_Collect_eq
  by (metis compose_context_iff prod.inject)

lemma rewrite_in_context_trancl_add_context [intro]:
  assumes "(s, t) \<in> (rewrite_in_context R)\<^sup>*"
  shows "(c\<langle>s\<rangle>, c\<langle>t\<rangle>) \<in> (rewrite_in_context R)\<^sup>*"
  using assms
proof (induction s t rule: rtrancl.induct)
  case rtrancl_refl

  show ?case
    by simp
next
  case (rtrancl_into_rtrancl t\<^sub>1 t\<^sub>2 t\<^sub>3)

  then have "(c\<langle>t\<^sub>2\<rangle>, c\<langle>t\<^sub>3\<rangle>) \<in> rewrite_in_context R"
    by fast
 
  then show ?case
    using rtrancl_into_rtrancl(3)
    by simp
qed

end

end