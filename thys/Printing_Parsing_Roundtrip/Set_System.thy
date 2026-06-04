theory Set_System
  imports Main
begin

section \<open>AI-Authored proof formalization via independence systems\<close>

subsection \<open>Independence Systems\<close>

text \<open>
  An independence system consists of a finite ground set \<^term>\<open>E\<close> and a family \<^term>\<open>F\<close>
  of subsets satisfying: (1) the empty set is in \<^term>\<open>F\<close>, and (2) \<^term>\<open>F\<close> is hereditary
  (downward closed under subsets).
\<close>

locale indep_system =
  fixes E :: "'a set" and indep :: "'a set \<Rightarrow> bool"
  assumes finite_E: "finite E"
  assumes empty_indep: "indep {}"
  assumes indep_subset_carrier: "\<And>F. indep F \<Longrightarrow> F \<subseteq> E"
  assumes hereditary: "\<And>F F'. indep F \<Longrightarrow> F' \<subseteq> F \<Longrightarrow> indep F'"

text \<open>
  A maximal independent set is one where no element can be added while preserving independence.
\<close>

definition (in indep_system) maximal :: "'a set \<Rightarrow> bool" where
  "maximal F \<longleftrightarrow> indep F \<and> (\<forall>e \<in> E - F. \<not> indep (F \<union> {e}))"

lemma (in indep_system) maximalI:
  assumes "indep F" "\<And>e. e \<in> E - F \<Longrightarrow> \<not> indep (F \<union> {e})"
  shows "maximal F"
  unfolding maximal_def using assms by blast

lemma (in indep_system) maximalD:
  assumes "maximal F"
  shows "indep F" "\<And>e. e \<in> E - F \<Longrightarrow> \<not> indep (F \<union> {e})"
  using assms unfolding maximal_def by blast+

subsection \<open>Best-In-Greedy Algorithm\<close>

text \<open>
  The Best-In-Greedy algorithm processes elements of \<^term>\<open>E\<close> in a given order, 
  greedily adding each element if independence is preserved.
  We model it as a fold over a list.
\<close>

definition greedy_step :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "greedy_step indep e F = (if indep (F \<union> {e}) then F \<union> {e} else F)"

definition best_in_greedy :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a set" where
  "best_in_greedy indep es = foldl (\<lambda>F e. greedy_step indep e F) {} es"

text \<open>
  We define the sequence of intermediate sets produced by the greedy algorithm.
\<close>

fun greedy_partial :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a set" where
  "greedy_partial indep es 0 = {}" |
  "greedy_partial indep es (Suc i) = 
    greedy_step indep (es ! i) (greedy_partial indep es i)"


text \<open>The final result equals the partial result after processing all elements.\<close>

lemma best_in_greedy_foldl_partial:
  assumes "n \<le> length es"
  shows "foldl (\<lambda>F e. greedy_step indep e F) {} (take n es) = greedy_partial indep es n" 
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  thus ?case
    by (simp add: take_Suc_conv_app_nth)
qed

lemma best_in_greedy_eq_partial:
  "best_in_greedy indep es = greedy_partial indep es (length es)"
  unfolding best_in_greedy_def
  using best_in_greedy_foldl_partial[of "length es" es indep]
  by simp

subsubsection \<open>Properties of \<^term>\<open>greedy_partial\<close>\<close>

text \<open>The partial result is monotonically increasing.\<close>

lemma greedy_partial_mono:
  "i \<le> j \<Longrightarrow> greedy_partial indep es i \<subseteq> greedy_partial indep es j"
proof (induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case
    by (cases "i = Suc j") (auto simp: greedy_step_def)
qed

text \<open>If an element was skipped at step \<^term>\<open>j\<close>, adding it to F\_{j-1} was not independent.\<close>

lemma greedy_partial_skip:
  assumes "j < length es" "es ! j \<notin> greedy_partial indep es (Suc j)"
  shows "\<not> indep (greedy_partial indep es j \<union> {es ! j})"
  using assms by (simp add: greedy_step_def split: if_splits)

text \<open>The partial set is always contained in the first i elements.\<close>

lemma greedy_partial_subset:
  assumes "i \<le> length es"
  shows "greedy_partial indep es i \<subseteq> set (take i es)"
  using assms
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then have "greedy_partial indep es i \<subseteq> set (take i es)" by simp
  moreover have "set (take i es) \<subseteq> set (take (Suc i) es)"
    by (simp add: set_take_subset_set_take)
  moreover have "es ! i \<in> set (take (Suc i) es)"
    using Suc.prems by (simp add: take_Suc_conv_app_nth)
  ultimately show ?case 
    by (auto simp: greedy_step_def)
qed


subsubsection \<open>Theorem: Best-In-Greedy returns a maximal independent set\<close>

text \<open>
  Theorem 2.1 of larry2.tex (Theorem 13.9 of Korte-Vygen).
  If (E, indep) is an independence system and es is a permutation of E,
  then the Best-In-Greedy output is a maximal independent set.
  
  First we show the greedy output is independent, by induction.
\<close>

lemma (in indep_system) greedy_partial_indep:
  assumes "i \<le> length es" "set es \<subseteq> E"
  shows "indep (greedy_partial indep es i)"
  using assms
proof (induction i)
  case 0
  then show ?case using empty_indep by simp
next
  case (Suc i)
  then have IH: "indep (greedy_partial indep es i)" by simp
  show ?case
  proof (cases "indep (greedy_partial indep es i \<union> {es ! i})")
    case True
    then show ?thesis by (simp add: greedy_step_def)
  next
    case False
    then show ?thesis using IH by (simp add: greedy_step_def)
  qed
qed

text \<open>Now the main theorem.\<close>

theorem (in indep_system) best_in_greedy_maximal:
  assumes perm: "set es = E" and distinct: "distinct es"
  shows "maximal (best_in_greedy indep es)"
proof (rule maximalI)
  have set_es: "set es \<subseteq> E" using perm by simp

  show indep_result: "indep (best_in_greedy indep es)"
    unfolding best_in_greedy_eq_partial
    using greedy_partial_indep[of "length es" es] set_es by simp

  fix e assume e_outside: "e \<in> E - best_in_greedy indep es"
  show "\<not> indep (best_in_greedy indep es \<union> {e})"
  proof -
    from e_outside perm have "e \<in> set es" by simp
    then obtain j where j: "j < length es" "es ! j = e" 
      by (metis in_set_conv_nth)
    from e_outside have "e \<notin> greedy_partial indep es (length es)"
      unfolding best_in_greedy_eq_partial by simp
    then have "e \<notin> greedy_partial indep es (Suc j)"
      using greedy_partial_mono[of "Suc j" "length es" indep es] j by auto
    then have not_indep_j: "\<not> indep (greedy_partial indep es j \<union> {e})"
      using greedy_partial_skip[of j es indep] j by simp
    have sub: "greedy_partial indep es j \<union> {e} \<subseteq> best_in_greedy indep es \<union> {e}"
      unfolding best_in_greedy_eq_partial 
      using greedy_partial_mono[of j "length es" indep es] j by auto
    show "\<not> indep (best_in_greedy indep es \<union> {e})"
    proof 
      assume "indep (best_in_greedy indep es \<union> {e})"
      then show False using hereditary[OF _ sub] not_indep_j by blast
    qed
  qed
qed


end