theory Smolka_AI_Independence_System
  imports Main Set_System Smolka_AI
begin

text \<open>
  Formalisation of the annotation algorithm via independence systems. We prove:
  \begin{itemize}
  \item The Best-In-Greedy algorithm returns a maximal independent set.
  \item The annotation set system is an independence system.
  \item Local minimality of the kept positions.
  \item The witness variable corollary.
  \end{itemize}
\<close>

subsection \<open>The Annotation Set System\<close>

text \<open>
  We now define the annotation set system.
  We abstract away from the concrete type-theoretic setting and work with:
  \begin{itemize}
  \item A finite set \<^term>\<open>S\<close> of candidate positions (the ground set).
  \item A finite set \<^term>\<open>V\<close> of inference variables.
  \item A key function mapping each position to a set of variables.
  \item The coverage condition: \<^term>\<open>S\<close> covers \<^term>\<open>V\<close>.
  \end{itemize}
\<close>

subsubsection \<open>Setup\<close>

locale annotation_setup =
  fixes S :: "nat set"
    and V :: "string set"
    and key :: "nat \<Rightarrow> string set"
  assumes finite_S: "finite S"
  assumes finite_V: "finite V"
  assumes key_subset: "\<And>p. p \<in> S \<Longrightarrow> key p \<subseteq> V"
  assumes S_covers_V: "\<Union>(key ` S) = V"
begin

text \<open>Coverage\<close>

definition covers :: "nat set \<Rightarrow> bool" where
  "covers Q \<longleftrightarrow> V \<subseteq> \<Union>(key ` Q)"

lemma covers_S: "covers S"
  unfolding covers_def using S_covers_V by blast

lemma covers_mono:
  assumes "covers Q" "Q \<subseteq> Q'"
  shows "covers Q'"
  unfolding covers_def using assms unfolding covers_def by blast

subsubsection \<open>The Independence System\<close>

text \<open>
  The annotation set system (S, F) is defined by:
    $F = \{F \subseteq S \| S \setminus F \textrm{ covers } V\}$
  A set $F$ represents positions that may be dropped: it is independent precisely
  when the remaining positions $S \setminus F$ still cover all inference variables.
\<close>

definition ann_indep :: "nat set \<Rightarrow> bool" where
  "ann_indep F \<longleftrightarrow> F \<subseteq> S \<and> covers (S - F)"

subsubsection \<open>The annotation set system is an independence system\<close>

lemma ann_indep_empty: "ann_indep {}"
  unfolding ann_indep_def using covers_S by simp

lemma ann_indep_subset_carrier:
  "ann_indep F \<Longrightarrow> F \<subseteq> S"
  unfolding ann_indep_def by simp

lemma ann_indep_hereditary:
  assumes "ann_indep F" "F' \<subseteq> F"
  shows "ann_indep F'"
proof -
  from assms have "F \<subseteq> S" and cov: "covers (S - F)" 
    unfolding ann_indep_def by auto
  from assms have "F' \<subseteq> S" using \<open>F \<subseteq> S\<close> by blast
  moreover have "S - F \<subseteq> S - F'" using \<open>F' \<subseteq> F\<close> by blast
  then have "covers (S - F')" using cov covers_mono by blast
  ultimately show ?thesis unfolding ann_indep_def by blast
qed

text \<open>The annotation set system forms an independence system.\<close>

sublocale indep_system S ann_indep
proof unfold_locales
  show "finite S" by (rule finite_S)
  show "ann_indep {}" by (rule ann_indep_empty)
  show "\<And>F. ann_indep F \<Longrightarrow> F \<subseteq> S" by (rule ann_indep_subset_carrier)
  show "\<And>F F'. ann_indep F \<Longrightarrow> F' \<subseteq> F \<Longrightarrow> ann_indep F'"
    by (rule ann_indep_hereditary)
qed

subsection \<open>Feasibility and Count Condition\<close>

text \<open>
  For \<^term>\<open>F\<close> in the independence family with \<^term>\<open>p \<in> S - F\<close>, we have
  \<^term>\<open>F \<union> {p}\<close> is independent iff \<^term>\<open>var_count F \<alpha> > 1\<close> for every \<^term>\<open>\<alpha> \<in> key p\<close>,
  where \<^term>\<open>var_count \<alpha>\<close> counts positions in \<^term>\<open>S - F\<close> covering \<^term>\<open>\<alpha>\<close>.
\<close>

definition var_count :: "nat set \<Rightarrow> string \<Rightarrow> nat" where
  "var_count F \<alpha> = card {q \<in> S - F. \<alpha> \<in> key q}"

lemma feasibility_iff_count:
  assumes "ann_indep F" "p \<in> S - F"
  shows "ann_indep (F \<union> {p}) \<longleftrightarrow> (\<forall>\<alpha> \<in> key p. var_count F \<alpha> > 1)"
proof
  assume indep_Fp: "ann_indep (F \<union> {p})"
  show "\<forall>\<alpha> \<in> key p. var_count F \<alpha> > 1"
  proof
    fix \<alpha> assume \<alpha>_in: "\<alpha> \<in> key p"
    from indep_Fp have "covers (S - (F \<union> {p}))" unfolding ann_indep_def by simp
    then have V_cov: "V \<subseteq> \<Union>(key ` (S - (F \<union> {p})))" unfolding covers_def .
    from \<alpha>_in assms(2) key_subset have "\<alpha> \<in> V" by blast
    then obtain q where q: "q \<in> S - (F \<union> {p})" "\<alpha> \<in> key q"
      using V_cov by blast
    then have "q \<noteq> p" "q \<in> S - F" by auto
    then have "{p, q} \<subseteq> {r \<in> S - F. \<alpha> \<in> key r}" 
      using \<alpha>_in q(2) assms(2) by blast
    moreover have "p \<noteq> q" using \<open>q \<noteq> p\<close> by simp
    moreover have "finite {r \<in> S - F. \<alpha> \<in> key r}" using finite_S by auto
    ultimately have "card {r \<in> S - F. \<alpha> \<in> key r} \<ge> 2"
      by (metis card_2_iff card_mono)
    then show "var_count F \<alpha> > 1" unfolding var_count_def by simp
  qed
next
  assume count_cond: "\<forall>\<alpha> \<in> key p. var_count F \<alpha> > 1"
  have "F \<union> {p} \<subseteq> S" using assms unfolding ann_indep_def by auto
  moreover have "covers (S - (F \<union> {p}))"
  proof -
    have V_sub: "V \<subseteq> \<Union>(key ` (S - F))"
      using assms(1) unfolding ann_indep_def covers_def by simp
    show ?thesis unfolding covers_def
    proof
      fix \<alpha> assume "\<alpha> \<in> V"
      then obtain q where q: "q \<in> S - F" "\<alpha> \<in> key q" 
        using V_sub by blast
      show "\<alpha> \<in> \<Union>(key ` (S - (F \<union> {p})))"
      proof (cases "\<alpha> \<in> key p")
        case True
        then have cnt_gt: "card {r \<in> S - F. \<alpha> \<in> key r} > 1" 
          using count_cond unfolding var_count_def by simp
        moreover have p_mem: "p \<in> {r \<in> S - F. \<alpha> \<in> key r}" using True assms(2) by simp
        moreover have fin: "finite {r \<in> S - F. \<alpha> \<in> key r}" using finite_S by auto
        ultimately have "card ({r \<in> S - F. \<alpha> \<in> key r} - {p}) > 0"
          by (simp add: card_Diff_singleton)
        then have "{r \<in> S - F. \<alpha> \<in> key r} - {p} \<noteq> {}" 
          using card_gt_0_iff fin finite_Diff by blast
        then obtain r where "r \<in> S - F" "\<alpha> \<in> key r" "r \<noteq> p" by blast
        then show ?thesis by blast
      next
        case False
        then have "q \<noteq> p" using q(2) by blast
        then have "q \<in> S - (F \<union> {p})" using q(1) by blast
        then show ?thesis using q(2) by blast
      qed
    qed
  qed
  ultimately show "ann_indep (F \<union> {p})" unfolding ann_indep_def by blast
qed

subsection \<open>Local Minimality\<close>

lemma local_minimality_coverage:
  assumes "ann_indep F_star"
  shows "covers (S - F_star)"
  using assms unfolding ann_indep_def by simp

lemma local_minimality:
  assumes greedy_maximal: "maximal F_star"
    and p_in_P: "p \<in> S - F_star"
  shows "\<not> covers (S - F_star - {p})"
proof -
  from greedy_maximal p_in_P have "\<not> ann_indep (F_star \<union> {p})"
    using maximalD(2) by blast
  moreover have "F_star \<union> {p} \<subseteq> S" 
    using maximalD(1)[OF greedy_maximal] indep_subset_carrier p_in_P by blast
  ultimately have "\<not> covers (S - (F_star \<union> {p}))"
    unfolding ann_indep_def by simp
  moreover have "S - (F_star \<union> {p}) = S - F_star - {p}" by blast
  ultimately show ?thesis by simp
qed

corollary witness_variable:
  assumes greedy_maximal: "maximal F_star"
    and p_in_P: "p \<in> S - F_star"
  obtains \<alpha> where "\<alpha> \<in> key p" "\<alpha> \<in> V" 
    "\<And>q. q \<in> S - F_star - {p} \<Longrightarrow> \<alpha> \<notin> key q"
proof -
  let ?P = "S - F_star"
  have cov: "covers ?P" 
    using maximalD(1)[OF greedy_maximal] local_minimality_coverage by simp
  have not_cov: "\<not> covers (?P - {p})" 
    using local_minimality[OF greedy_maximal p_in_P] by simp
  from not_cov obtain \<alpha> where \<alpha>: "\<alpha> \<in> V" "\<alpha> \<notin> \<Union>(key ` (?P - {p}))"
    unfolding covers_def by blast
  from cov have "V \<subseteq> \<Union>(key ` ?P)" unfolding covers_def by simp
  with \<alpha>(1) obtain q where "q \<in> ?P" "\<alpha> \<in> key q" by blast
  with \<alpha>(2) have "q = p" by blast
  then have "\<alpha> \<in> key p" using \<open>\<alpha> \<in> key q\<close> by simp
  moreover have "\<And>q. q \<in> ?P - {p} \<Longrightarrow> \<alpha> \<notin> key q"
    using \<alpha>(2) by blast
  ultimately show ?thesis using that \<alpha>(1) by blast
qed

subsection \<open>Reverse Greedy Correctness\<close>
definition \<open>reverse_greedy' es = S - best_in_greedy ann_indep es\<close>

theorem annotation_algorithm_correct:
  assumes perm: "set es = S" and distinct: "distinct es"
  shows "covers (reverse_greedy' es)"
    and "\<And>p. p \<in> reverse_greedy' es \<Longrightarrow> 
           \<exists>\<alpha> \<in> key p. \<alpha> \<in> V \<and> (\<forall>q \<in> reverse_greedy' es - {p}. \<alpha> \<notin> key q)"
proof -
  have mx: "maximal (best_in_greedy ann_indep es)"
    using best_in_greedy_maximal[OF perm distinct] .
  then have indep_star: "ann_indep (best_in_greedy ann_indep es)" 
    using maximalD by blast
  show "covers (reverse_greedy' es)"
    using local_minimality_coverage[OF indep_star] reverse_greedy'_def by simp
  show "\<And>p. p \<in> reverse_greedy' es \<Longrightarrow> 
           \<exists>\<alpha> \<in> key p. \<alpha> \<in> V \<and> (\<forall>q \<in> reverse_greedy' es - {p}. \<alpha> \<notin> key q)"
    using witness_variable[OF mx] reverse_greedy'_def by metis
qed
end

context annotation_problem
begin

text \<open>The annotation problem gives rise to an annotation set system.\<close>

lemma finite_tvars_ty: "finite (tvars_ty t)"
  by (induction t) auto

interpretation ann: annotation_setup "pos_set a_star" V key
proof unfold_locales
  show "finite (pos_set a_star)" by (simp add: pos_set_def)
  have "finite (tvars_aterm a_star)" by (induction a_star) (auto simp: finite_tvars_ty)
  then show "finite V" unfolding V_def by auto
  show "\<And>p. p \<in> pos_set a_star \<Longrightarrow> key p \<subseteq> V"
    unfolding key_def by auto
  show "\<Union>(key ` pos_set a_star) = V"
  proof
    show "\<Union>(key ` pos_set a_star) \<subseteq> V" unfolding key_def by auto
  next
    show "V \<subseteq> \<Union>(key ` pos_set a_star)"
    proof
      fix \<alpha> assume "\<alpha> \<in> V"
      then have "\<alpha> \<in> tvars_aterm a_star" unfolding V_def by auto
      then obtain p s \<tau> where "(p, s, \<tau>) \<in> set (enum_aterm a_star)" "\<alpha> \<in> tvars_ty \<tau>"
        using tvars_aterm_subset_enum by blast
      then have "p \<in> pos_set a_star" unfolding pos_set_def by force
      moreover have "\<alpha> \<in> key p" unfolding key_def using \<open>(p, s, \<tau>) \<in> _\<close> \<open>\<alpha> \<in> tvars_ty \<tau>\<close> \<open>\<alpha> \<in> V\<close> by auto
      ultimately show "\<alpha> \<in> \<Union>(key ` pos_set a_star)" by auto
    qed
  qed
qed

definition es_from_enum :: "nat list" where
  "es_from_enum = map fst (enum_aterm a_star)"

lemma es_set: "set es_from_enum = pos_set a_star"
  unfolding es_from_enum_def pos_set_def
  by (force simp: image_iff)

lemma es_distinct: "distinct es_from_enum"
  unfolding es_from_enum_def
  by (simp add: distinct_enum_fst)

lemma reverse_greedy'_subs_pos: \<open>ann.reverse_greedy' es_from_enum \<subseteq> pos_set a_star\<close>
  by (simp add: ann.reverse_greedy'_def)

lemma reverse_greedy'_coverage: \<open>\<Union> (key ` ann.reverse_greedy' es_from_enum) = V\<close>
  using ann.annotation_algorithm_correct(1)[OF es_set es_distinct] ann.S_covers_V 
  using ann.covers_def ann.reverse_greedy'_def by auto

lemma reverse_greedy'_witness: 
  assumes \<open>p \<in> ann.reverse_greedy' es_from_enum\<close> 
  shows \<open>\<exists>\<alpha>\<in>key p. \<forall>p'\<in>ann.reverse_greedy' es_from_enum. p' \<noteq> p \<longrightarrow> \<alpha> \<notin> key p'\<close>
  using assms ann.annotation_algorithm_correct(2)[OF es_set es_distinct, of p] 
  by auto

interpretation ann: annotation_selection 
  const_type
  \<Gamma> a a_star \<sigma> \<open>ann.reverse_greedy' es_from_enum\<close>
  using reverse_greedy'_subs_pos reverse_greedy'_coverage reverse_greedy'_witness
  by unfold_locales auto

thm ann.local_minimality
thm ann.completeness
end
end