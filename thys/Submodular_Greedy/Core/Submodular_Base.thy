theory Submodular_Base
  imports Complex_Main
begin

lemma finite_has_maximal_on:
  fixes g :: "'a \<Rightarrow> 'b::linorder"
  assumes fin: "finite A"
    and nonempty: "A \<noteq> {}"
  shows "\<exists>x\<in>A. \<forall>y\<in>A. g y \<le> g x" using arg_max_on_def[of g A]
proof -
  have fin_image: "finite (g ` A)"
    using fin by simp
  have nonempty_image: "g ` A \<noteq> {}"
    using nonempty by auto

  have max_in_image: "Max (g ` A) \<in> g ` A"
    using Max_in[OF fin_image nonempty_image] .

  then obtain x where xA: "x \<in> A" and x_eq: "g x = Max (g ` A)"
    by auto

  have "\<forall>y\<in>A. g y \<le> g x"
    by (simp add: fin_image x_eq)

  then show ?thesis
    using xA by blast
qed

text \<open>
  The main development is carried out in a single locale for normalized
  monotone submodular functions, which is the setting needed for the
  cardinality-constrained greedy approximation guarantees below. Some
  auxiliary facts hold under weaker assumptions; for this entry we keep them
  in the same locale to maintain a compact and uniform development.
\<close>

locale Submodular_Func =
  fixes V :: "'a set" and f :: "'a set \<Rightarrow> real"
  assumes finite_V: "finite V"
      and monotone_f: "\<And>S T. S \<subseteq> T \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f S \<le> f T"
      and submodular_f:
        "\<And>S T. S \<subseteq> V \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f (S \<union> T) + f (S \<inter> T) \<le> f S + f T"
      and f_empty: "f {} = 0"
begin

text \<open>Marginal gain of adding a single element to a set.\<close>
definition gain :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "gain S e = f (S \<union> {e}) - f S"

lemma f_nonneg:
  assumes "S \<subseteq> V"
  shows "0 \<le> f S"
proof -
  have "{} \<subseteq> S" by auto
  from monotone_f[OF this assms] have "f {} \<le> f S" .
  thus ?thesis by (simp add: f_empty)
qed

lemma monotone_on_PowV:
  shows "monotone_on (Pow V) (\<subseteq>) (\<le>) f"
  unfolding monotone_on_def
  using monotone_f by auto

lemma gain_nonneg:
  assumes "S \<subseteq> V" and "x \<in> V - S"
  shows "0 \<le> gain S x"
proof -
  have "S \<subseteq> S \<union> {x}" by auto
  moreover from assms have "S \<union> {x} \<subseteq> V" by auto
  ultimately have "f S \<le> f (S \<union> {x})" using monotone_f by auto
  thus ?thesis by (simp add: gain_def)
qed

text \<open>Diminishing returns for single-element marginal gains.\<close>
lemma gain_decreasing:
  assumes "S \<subseteq> T" "T \<subseteq> V" "x \<in> V" "x \<notin> T"
  shows "gain S x \<ge> gain T x"
proof -
  have Sx_sub_V: "insert x S \<subseteq> V"
    using assms by auto

  have subm:
    "f (insert x (S \<union> T)) + f (insert x S \<inter> T) \<le> f (insert x S) + f T"
    using submodular_f[OF Sx_sub_V assms(2)]
    by simp

  have inter_eq: "insert x S \<inter> T = S"
    using assms by auto

  have union_eq: "insert x (S \<union> T) = insert x T"
    using assms by auto

  from subm have "f S + f (insert x T) \<le> f T + f (insert x S)"
    by (simp add: inter_eq union_eq)

  hence "f (insert x S) - f S \<ge> f (insert x T) - f T"
    by linarith

  thus ?thesis
    by (simp add: gain_def)
qed

text \<open>Set-valued diminishing returns.\<close>
lemma gain_decreasing_set:
  assumes "S \<subseteq> T" "T \<subseteq> V" "A \<subseteq> V"
  shows "f (S \<union> A) - f S \<ge> f (T \<union> A) - f T"
proof -
  have SUA_subV: "S \<union> A \<subseteq> V"
    using assms by auto

  have subm:
    "f ((S \<union> A) \<union> T) + f ((S \<union> A) \<inter> T) \<le> f (S \<union> A) + f T"
    using submodular_f[OF SUA_subV assms(2)] .

  have union_eq: "(S \<union> A) \<union> T = T \<union> A"
    using assms by auto

  have S_sub_inter: "S \<subseteq> (S \<union> A) \<inter> T"
    using assms by auto

  have inter_subV: "(S \<union> A) \<inter> T \<subseteq> V"
    using assms by auto

  have mono_inter: "f S \<le> f ((S \<union> A) \<inter> T)"
    using monotone_f[OF S_sub_inter inter_subV] .

  have "f (T \<union> A) + f ((S \<union> A) \<inter> T) \<le> f (S \<union> A) + f T"
    using subm by (simp add: union_eq)
  then have "f (T \<union> A) + f S \<le> f (S \<union> A) + f T"
    using mono_inter by linarith
  then show ?thesis
    by linarith
qed

end

text \<open>
  This entry treats cardinality-constrained monotone submodular maximization.
  Other constraint systems, such as matroid or knapsack constraints, are
  outside the scope of the present development.
\<close>

locale Cardinality_Constraint = Submodular_Func +
  fixes k :: nat
  assumes k_le_cardV: "k \<le> card V"
begin

definition feasible :: "'a set \<Rightarrow> bool" where
  "feasible S \<longleftrightarrow> S \<subseteq> V \<and> card S \<le> k"

lemma feasibleI:
  assumes "S \<subseteq> V" "card S \<le> k"
  shows "feasible S"
  using assms unfolding feasible_def by auto

lemma feasibleD:
  assumes "feasible S"
  shows "S \<subseteq> V" "card S \<le> k"
  using assms unfolding feasible_def by auto

lemma feasible_empty[simp]: "feasible {}"
  unfolding feasible_def by auto

lemma feasible_family_nonempty: "Collect feasible \<noteq> {}"
proof -
  have "\<exists>S. feasible S"
  proof
    show "feasible {}" by (rule feasible_empty)
  qed
  then show ?thesis by auto
qed

lemma finite_feasible_family: "finite {S. feasible S}"
proof -
  have "{S. feasible S} \<subseteq> Pow V"
    by (auto simp: feasible_def)
  moreover have "finite (Pow V)"
    using finite_V by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsection \<open>Optimal feasible sets\<close>

text \<open>
  We select a canonical optimal feasible set \<open>OPT_set\<close> using Hilbert choice
  and define \<open>OPT_k\<close> as its value. These are problem-level objects for the
  cardinality-constrained maximization problem, independent of any particular
  greedy implementation.
\<close>

definition OPT_set :: "'a set" where
  "OPT_set =
     (SOME X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X))"

lemma exists_max_feasible:
  "\<exists>X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
proof -
  from finite_has_maximal_on[OF finite_feasible_family feasible_family_nonempty]
  obtain X where X_feas: "X \<in> Collect feasible"
    and X_max: "\<forall>Y \<in> Collect feasible. f Y \<le> f X"
    by blast
  have "feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
    using X_feas X_max by auto
  thus ?thesis ..
qed

lemma OPT_set_props:
  shows OPT_set_in: "feasible OPT_set"
    and OPT_set_max: "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
proof -
  from exists_max_feasible
  obtain X where X_in: "feasible X"
    and X_max: "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X"
    by blast
  then have ex_spec:
    "\<exists>X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
    by blast
  from someI_ex[OF ex_spec]
  have "feasible OPT_set \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set)"
    unfolding OPT_set_def by simp
  then show "feasible OPT_set"
    and "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
    by auto
qed

definition OPT_k :: real where
  "OPT_k = f OPT_set"

lemma exists_opt_set:
  "\<exists>X. feasible X \<and> f X = OPT_k"
proof -
  have "feasible OPT_set"
    by (rule OPT_set_in)
  moreover have "f OPT_set = OPT_k"
    unfolding OPT_k_def by simp
  ultimately show ?thesis
    by blast
qed

lemma OPT_k_upper_bound:
  assumes "feasible S"
  shows "f S \<le> OPT_k"
proof -
  have "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
    by (rule OPT_set_max)
  with assms have "f S \<le> f OPT_set"
    by auto
  thus ?thesis
    unfolding OPT_k_def by simp
qed

subsection \<open>Basic non-emptiness facts\<close>

lemma nonempty_candidates:
  assumes "S \<subseteq> V" "card S < k"
  shows "V - S \<noteq> {}"
proof
  assume "V - S = {}"
  hence "V \<subseteq> S" by auto
  with assms(1) have "V = S" by auto
  with assms(2) k_le_cardV show False by simp
qed

lemma nonempty_gap:
  assumes "S \<subseteq> V" "Opt \<subseteq> V" "f S < f Opt"
  shows "Opt - S \<noteq> {}"
proof
  assume "Opt - S = {}"
  hence "Opt \<subseteq> S" by auto
  with assms(1,2) have "f Opt \<le> f S"
    using monotone_f by auto
  with assms(3) show False by linarith
qed

lemma OPT_k_nonneg: "0 \<le> OPT_k"
proof -
  have "feasible {}"
    by (rule feasible_empty)
  then have "f {} \<le> OPT_k"
    by (rule OPT_k_upper_bound)
  thus ?thesis
    by (simp add: f_empty)
qed

text \<open>Submodular telescoping: sum of marginals upper-bounds the joint gain.\<close>
lemma submod_sum_upper:
  assumes "finite A" "A \<subseteq> V" "S \<subseteq> V" "A \<inter> S = {}"
  shows "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)"
  using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  from insert.hyps have a_notin: "a \<notin> A" and finA: "finite A" by auto

  from insert.prems have S_sub: "S \<subseteq> V" by auto
  from insert.prems have ins_subV: "insert a A \<subseteq> V" by auto
  from insert.prems have ins_disj: "insert a A \<inter> S = {}" by auto

  have A_sub: "A \<subseteq> V" using ins_subV by auto
  have aV   : "a \<in> V"  using ins_subV by auto
  have disjA: "A \<inter> S = {}" using ins_disj by auto
  have a_notS: "a \<notin> S" using ins_disj by auto

  have step:
    "f (S \<union> insert a A) - f S
     = (f ((S \<union> A) \<union> {a}) - f (S \<union> A)) + (f (S \<union> A) - f S)"
    by (simp add: insert_commute Un_assoc)

  have SSUA: "S \<subseteq> S \<union> A" by auto
  have SUA_subV: "S \<union> A \<subseteq> V" using S_sub A_sub by auto
  have a_notin_SUA: "a \<notin> S \<union> A" using a_notS a_notin by auto
  have dec:
    "f ((S \<union> A) \<union> {a}) - f (S \<union> A) \<le> gain S a"
    using gain_decreasing[OF SSUA SUA_subV aV a_notin_SUA]
    by (simp add: gain_def)

  from insert.IH[OF A_sub S_sub disjA]
  have IH: "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)" .

  have "(f ((S \<union> A) \<union> {a}) - f (S \<union> A)) + (f (S \<union> A) - f S)
        \<le> gain S a + (\<Sum>x\<in>A. gain S x)"
    using dec IH by linarith
  thus ?case
    by (simp add: step insert_commute finA a_notin)
qed

text \<open>
  Average marginal bound against any candidate set \<open>Opt \<subseteq> V\<close> with
  \<open>card Opt \<le> k\<close>: if \<open>S \<subseteq> V\<close> and \<open>card S < k\<close>, then there exists an
  element \<open>e \<in> V - S\<close> such that
  \<open>gain S e \<ge> (f Opt - f S) / real k\<close>.
\<close>
lemma marginal_gain_lower_bound:
  fixes Opt S :: "'a set"
  assumes S_sub: "S \<subseteq> V"
    and O_sub: "Opt \<subseteq> V"
    and cardS_lt_k: "card S < k"
    and cardO_le_k: "card Opt \<le> k"
  shows "\<exists>e\<in>V - S. gain S e \<ge> (f Opt - f S) / real k"
proof -
  have finV: "finite V" by (rule finite_V)
  have k_pos: "0 < k" using cardS_lt_k by (simp add: not_less)

  consider (le) "f Opt \<le> f S" | (gt) "f S < f Opt" by linarith
  then show ?thesis
  proof cases
    case le
    have VS_ne: "V - S \<noteq> {}"
      using nonempty_candidates[OF S_sub cardS_lt_k] .

    then obtain e where eVS: "e \<in> V - S" by blast
    hence ge0: "0 \<le> gain S e" using S_sub gain_nonneg by auto

    moreover have "(f Opt - f S) / real k \<le> 0"
    proof -
      have "f Opt - f S \<le> 0" using le by linarith
      thus ?thesis
        using k_pos by (simp add: divide_nonpos_pos)
    qed

    ultimately have "(f Opt - f S) / real k \<le> gain S e"
      by linarith

    thus ?thesis
      using eVS by (intro bexI[of _ e]) auto
  next
    case gt
    have OS_ne: "Opt - S \<noteq> {}"
      using nonempty_gap[OF S_sub O_sub gt] .

    have finOS: "finite (Opt - S)"
      using finV O_sub by (meson Diff_subset finite_subset)
    have OS_subV: "Opt - S \<subseteq> V" using O_sub by auto
    have disj: "(Opt - S) \<inter> S = {}" by auto
    have finO: "finite Opt" using finV O_sub finite_subset by blast

    have step_sum:
      "f (S \<union> (Opt - S)) - f S \<le> (\<Sum>x\<in>Opt - S. gain S x)"
      using submod_sum_upper[OF finOS OS_subV S_sub disj] .

    have SUO_subV: "S \<union> Opt \<subseteq> V" using S_sub O_sub by auto
    have sum_upper: "f Opt - f S \<le> (\<Sum>x\<in>Opt - S. gain S x)"
    proof -
      have "f Opt \<le> f (S \<union> Opt)"
        using monotone_f[rule_format, of Opt "S \<union> Opt"] SUO_subV by auto
      then have "f Opt - f S \<le> f (S \<union> Opt) - f S" by linarith
      also have "S \<union> Opt = S \<union> (Opt - S)" by auto
      also have "f (S \<union> (Opt - S)) - f S
                   \<le> (\<Sum>x\<in>Opt - S. gain S x)"
        using step_sum .
      finally show ?thesis .
    qed

    obtain e where e_in: "e \<in> Opt - S"
      and e_max: "\<forall>y\<in>Opt - S. gain S y \<le> gain S e"
      using finite_has_maximal_on[OF finOS OS_ne, of "gain S"]
      by blast

    have "(\<Sum>x\<in>Opt - S. gain S x) \<le> (\<Sum>x\<in>Opt - S. gain S e)"
      using e_max by (intro sum_mono) simp_all
    also have "... = real (card (Opt - S)) * gain S e"
      by simp
    finally have sum_le_card_max:
      "(\<Sum>x\<in>Opt - S. gain S x) \<le> real (card (Opt - S)) * gain S e" .

    have base: "f Opt - f S \<le> real (card (Opt - S)) * gain S e"
      using sum_upper sum_le_card_max by linarith

    have cardOS_le_k: "card (Opt - S) \<le> k"
    proof -
      have "card (Opt - S) \<le> card Opt"
        using finO Diff_subset by (rule card_mono)
      also have "... \<le> k" using cardO_le_k .
      finally show ?thesis .
    qed

    have eVS: "e \<in> V - S" using e_in O_sub by auto
    have ge0: "0 \<le> gain S e" using S_sub eVS gain_nonneg by auto

    have "real (card (Opt - S)) * gain S e \<le> real k * gain S e"
      using cardOS_le_k ge0 by (simp add: mult_right_mono)
    hence main_ineq: "f Opt - f S \<le> real k * gain S e"
      using base by linarith

    have "gain S e \<ge> (f Opt - f S) / real k"
      using main_ineq k_pos by (simp add: mult.commute pos_divide_le_eq)
    thus ?thesis using eVS by blast
  qed
qed

end

end