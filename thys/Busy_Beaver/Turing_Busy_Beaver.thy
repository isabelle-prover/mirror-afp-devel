theory Turing_Busy_Beaver
  imports
    Busy_Beaver_Base
    "Universal_Turing_Machine.TuringComputable"
begin

section \<open>Busy Beaver Upper Bounds for Universal Turing Machines\<close>

text \<open>
  This theory connects the abstract Busy Beaver upper-bound principle to the
  Turing machines from AFP's Universal Turing Machine entry \<^cite>\<open>Xu13\<close>.  We
  use halting with a numeric result, the halting predicate that occurs in AFP's
  formalization of the special halting problems.  The first instantiation is a
  direct Turing-program Busy Beaver function.  Inside AFP's \<open>hpk\<close> locale we
  also define code-indexed variants for the one-argument problem \<open>K1\<close> and the
  two-argument problem \<open>H1\<close>.  Finally, using AFP's Turing-computability
  interface, we make the noncomputability consequence explicit for the
  characteristic functions of the induced \<open>H1\<close> decider sets.
\<close>

text \<open>
  Three related Busy Beaver notions appear below.  The theory
  \<open>Busy_Beaver_Base\<close> supplies the model-parametric function
  \<open>BB_time\<close>, whose objects are abstract programs run on input \<open>0\<close>.  The
  first concrete interpretation instantiates this as \<open>Turing_BB_time\<close> for
  AFP Turing programs, still using a direct program-size measure.  The
  code-indexed interpretations are introduced for the halting problems in the
  Universal Turing Machine entry: the diagonal code-indexed function decides
  \<open>K1\<close>, while the pair-indexed function folds a machine code and input into a
  single Busy Beaver object so that upper bounds decide \<open>H1\<close>.
\<close>


subsection \<open>Exact halting times for numeric results\<close>

definition has_num_result_at :: "tprog0 \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "has_num_result_at tm ns t \<longleftrightarrow>
    is_final (steps0 (1, [], <ns>) tm t) \<and>
    (\<exists>k n l. steps0 (1, [], <ns>) tm t = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"

definition tm_num_halts_in :: "tprog0 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "tm_num_halts_in tm input t \<longleftrightarrow>
    has_num_result_at tm [input] t \<and> (\<forall>u<t. \<not> has_num_result_at tm [input] u)"

lemma tm_num_halts_in_unique:
  assumes "tm_num_halts_in tm input t"
    and "tm_num_halts_in tm input u"
  shows "t = u"
  by (meson assms nat_neq_iff tm_num_halts_in_def)

lemma TMC_has_num_res_iff_tm_num_halts:
  "TMC_has_num_res tm [input] \<longleftrightarrow> (\<exists>t. tm_num_halts_in tm input t)"
proof
  assume "TMC_has_num_res tm [input]"
  then obtain t k n l where
    final: "is_final (steps0 (1, [], <[input]>) tm t)" and
    result: "steps0 (1, [], <[input]>) tm t = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    unfolding TMC_has_num_res_iff by blast
  have t: "has_num_result_at tm [input] t"
    unfolding has_num_result_at_def using final result by blast
  let ?t = "LEAST u. has_num_result_at tm [input] u"
  have ex: "\<exists>u. has_num_result_at tm [input] u"
    using t by blast
  have least: "has_num_result_at tm [input] ?t"
    using ex by (rule LeastI_ex)
  have none_before: "\<forall>u<?t. \<not> has_num_result_at tm [input] u"
    by (meson not_less_Least)
  have "tm_num_halts_in tm input ?t"
    using least not_less_Least tm_num_halts_in_def by auto
  then show "\<exists>t. tm_num_halts_in tm input t"
    by blast
next
  assume "\<exists>t. tm_num_halts_in tm input t"
  then obtain t where "tm_num_halts_in tm input t"
    by blast
  then have "has_num_result_at tm [input] t"
    unfolding tm_num_halts_in_def by blast
  then show "TMC_has_num_res tm [input]"
    unfolding TMC_has_num_res_iff
    using has_num_result_at_def by auto
qed


subsection \<open>A finite size measure for Turing programs\<close>

fun action_rank :: "action \<Rightarrow> nat" where
  "action_rank WB = 0"
| "action_rank WO = 1"
| "action_rank L = 2"
| "action_rank R = 3"
| "action_rank Nop = 4"

definition instr_size :: "instr \<Rightarrow> nat" where
  "instr_size i = Suc (action_rank (fst i) + snd i)"

definition tm_size :: "tprog0 \<Rightarrow> nat" where
  "tm_size tm = length tm + sum_list (map instr_size tm)"

lemma finite_instr_size_le: "finite {i::instr. instr_size i \<le> n}"
proof -
  have subset: "{i::instr. instr_size i \<le> n} \<subseteq> (UNIV::action set) \<times> {s. s \<le> n}"
    by (auto simp: instr_size_def)
  have "finite (UNIV::action set)"
  proof -
    have eq: "(UNIV::action set) = {WB, WO, L, R, Nop}"
      by (auto intro: action.exhaust)
    have "finite ({WB, WO, L, R, Nop} :: action set)"
      by simp
    then show ?thesis
      using eq by simp
  qed
  have fin: "finite ((UNIV::action set) \<times> {s. s \<le> n})"
    by (simp add: \<open>finite (UNIV::action set)\<close>)
  show ?thesis
    by (rule finite_subset[OF subset fin])
qed

lemma length_le_tm_size:
  "length tm \<le> tm_size tm"
  by (simp add: tm_size_def)

lemma instr_size_le_tm_size:
  assumes "i \<in> set tm"
  shows "instr_size i \<le> tm_size tm"
proof -
  have "instr_size i \<in> set (map instr_size tm)"
    using assms by auto
  then have "instr_size i \<le> sum_list (map instr_size tm)"
    by (simp add: member_le_sum_list)
  also have "\<dots> \<le> tm_size tm"
    by (simp add: tm_size_def)
  finally show ?thesis .
qed

lemma finite_tm_size_le: "finite {tm::tprog0. tm_size tm \<le> n}"
proof -
  let ?I = "{i::instr. instr_size i \<le> n}"
  have subset: "{tm::tprog0. tm_size tm \<le> n}
      \<subseteq> {tm. set tm \<subseteq> ?I \<and> length tm \<le> n}"
  proof
    fix tm :: tprog0
    assume tm: "tm \<in> {tm. tm_size tm \<le> n}"
    then have len: "length tm \<le> n"
      using length_le_tm_size[of tm] by simp
    have "set tm \<subseteq> ?I"
      using instr_size_le_tm_size mem_Collect_eq order_trans subset_code(1) tm
      by fastforce
    then show "tm \<in> {tm. set tm \<subseteq> ?I \<and> length tm \<le> n}"
      using len by simp
  qed
  have fin: "finite {tm::tprog0. set tm \<subseteq> ?I \<and> length tm \<le> n}"
    using finite_instr_size_le by (rule finite_lists_length_le)
  show ?thesis
    by (rule finite_subset[OF subset fin])
qed

interpretation turing_busy_beaver: busy_beaver_base tm_size tm_num_halts_in
proof
  fix n
  show "finite {p. tm_size p \<le> n}"
    by (rule finite_tm_size_le)
next
  fix p x t u
  assume "tm_num_halts_in p x t" and "tm_num_halts_in p x u"
  then show "t = u"
    by (rule tm_num_halts_in_unique)
qed

abbreviation Turing_BB_time :: "nat \<Rightarrow> nat" where
  "Turing_BB_time \<equiv> turing_busy_beaver.BB_time"

theorem Turing_BB_time_ge:
  assumes "tm_size tm \<le> n"
    and "tm_num_halts_in tm 0 t"
  shows "t \<le> Turing_BB_time n"
  using turing_busy_beaver.BB_time_ge_time assms by blast


subsection \<open>The code-indexed Busy Beaver function and AFP's special halting problem\<close>

context hpk
begin

text \<open>
  The next predicate is deliberately diagonal: the formal locale input is not
  used because the special halting problem \<open>K1\<close> asks whether the machine coded
  by \<open>c\<close> halts on input \<open>c\<close>.
\<close>

definition coded_diagonal_num_halts_in :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "coded_diagonal_num_halts_in c input t \<longleftrightarrow> tm_num_halts_in (c2t c) c t"

interpretation coded_busy_beaver: busy_beaver_base "\<lambda>c::nat. c" coded_diagonal_num_halts_in
proof
  fix n
  show "finite {p::nat. p \<le> n}"
    by simp
next
  fix p x t u
  assume "coded_diagonal_num_halts_in p x t" and "coded_diagonal_num_halts_in p x u"
  then show "t = u"
    by (auto simp: coded_diagonal_num_halts_in_def dest: tm_num_halts_in_unique)
qed

abbreviation Coded_BB_time :: "nat \<Rightarrow> nat" where
  "Coded_BB_time \<equiv> coded_busy_beaver.BB_time"

lemma coded_halts_iff_K1:
  "coded_busy_beaver.halts c 0 \<longleftrightarrow> [c] \<in> K1"
proof
  assume "coded_busy_beaver.halts c 0"
  then have "\<exists>t. tm_num_halts_in (c2t c) c t"
    unfolding coded_busy_beaver.halts_def coded_diagonal_num_halts_in_def by blast
  then have "TMC_has_num_res (c2t c) [c]"
    using TMC_has_num_res_iff_tm_num_halts by blast
  then show "[c] \<in> K1"
    unfolding K1_def by blast
next
  assume "[c] \<in> K1"
  then have "TMC_has_num_res (c2t c) [c]"
    unfolding K1_def by auto
  then have "\<exists>t. tm_num_halts_in (c2t c) c t"
    using TMC_has_num_res_iff_tm_num_halts by blast
  then show "coded_busy_beaver.halts c 0"
    unfolding coded_busy_beaver.halts_def coded_diagonal_num_halts_in_def by blast
qed

theorem coded_BB_upper_bound_decides_K1:
  assumes "coded_busy_beaver.upper_bound_for_BB b"
  shows "coded_busy_beaver.halting_decider_from b c 0 \<longleftrightarrow> [c] \<in> K1"
  using coded_busy_beaver.halting_decider_from_correct_0[OF assms, of c]
  by (simp add: coded_halts_iff_K1)

corollary K1_not_turing_decidable_again: "\<not> turing_decidable K1"
  by (rule not_Turing_decidable_K1)


subsection \<open>A code-indexed Busy Beaver function for the two-argument halting problem\<close>

text \<open>
  The previous code-indexed function targets the diagonal/special problem
  \<open>K1\<close>.  To cover AFP's two-argument halting problem \<open>H1\<close>, we fold the input
  into the Busy Beaver object itself: an object is a pair \<open>(c, m)\<close> consisting
  of a machine code and an input.  The size measure \<open>c + m\<close> has finite bounded
  classes, and an upper bound for the resulting Busy Beaver function decides
  membership in \<open>H1\<close>.
\<close>

definition coded_pair_num_halts_in :: "(nat \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "coded_pair_num_halts_in cm input t \<longleftrightarrow>
    tm_num_halts_in (c2t (fst cm)) (snd cm) t"

definition coded_pair_size :: "nat \<times> nat \<Rightarrow> nat" where
  "coded_pair_size cm = fst cm + snd cm"

lemma finite_coded_pair_size_le:
  "finite {cm::nat \<times> nat. coded_pair_size cm \<le> n}"
proof -
  have subset:
    "{cm::nat \<times> nat. coded_pair_size cm \<le> n} \<subseteq> {c. c \<le> n} \<times> {m. m \<le> n}"
    by (auto simp: coded_pair_size_def)
  have fin: "finite ({c. c \<le> n} \<times> {m. m \<le> n})"
    by simp
  show ?thesis
    by (rule finite_subset[OF subset fin])
qed

interpretation pair_busy_beaver: busy_beaver_base coded_pair_size coded_pair_num_halts_in
proof
  fix n
  show "finite {p. coded_pair_size p \<le> n}"
    by (rule finite_coded_pair_size_le)
next
  fix p x t u
  assume "coded_pair_num_halts_in p x t" and "coded_pair_num_halts_in p x u"
  then show "t = u"
    by (auto simp: coded_pair_num_halts_in_def dest: tm_num_halts_in_unique)
qed

abbreviation Pair_BB_time :: "nat \<Rightarrow> nat" where
  "Pair_BB_time \<equiv> pair_busy_beaver.BB_time"

lemma coded_pair_halts_iff_H1:
  "pair_busy_beaver.halts (c, m) 0 \<longleftrightarrow> [c, m] \<in> H1"
proof
  assume "pair_busy_beaver.halts (c, m) 0"
  then have "\<exists>t. tm_num_halts_in (c2t c) m t"
    unfolding pair_busy_beaver.halts_def coded_pair_num_halts_in_def by simp
  then have "TMC_has_num_res (c2t c) [m]"
    using TMC_has_num_res_iff_tm_num_halts by blast
  then show "[c, m] \<in> H1"
    unfolding H1_def by blast
next
  assume "[c, m] \<in> H1"
  then have "TMC_has_num_res (c2t c) [m]"
    unfolding H1_def by auto
  then have "\<exists>t. tm_num_halts_in (c2t c) m t"
    using TMC_has_num_res_iff_tm_num_halts by blast
  then show "pair_busy_beaver.halts (c, m) 0"
    unfolding pair_busy_beaver.halts_def coded_pair_num_halts_in_def by simp
qed

theorem pair_BB_upper_bound_decides_H1_pair:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "pair_busy_beaver.halting_decider_from b (c, m) 0 \<longleftrightarrow> [c, m] \<in> H1"
  using pair_busy_beaver.halting_decider_from_correct_0[OF assms, of "(c, m)"]
  by (simp add: coded_pair_halts_iff_H1)

definition H1_decider_from :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> bool" where
  "H1_decider_from b nl \<longleftrightarrow>
    (case nl of
      [c, m] \<Rightarrow> pair_busy_beaver.halting_decider_from b (c, m) 0
    | _ \<Rightarrow> False)"

theorem H1_decider_from_correct:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "H1_decider_from b nl \<longleftrightarrow> nl \<in> H1"
proof (cases nl)
  case Nil
  then show ?thesis
    by (simp add: H1_decider_from_def H1_def)
next
  case (Cons c xs)
  note nl_Cons = Cons
  then show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis
      using nl_Cons by (simp add: H1_decider_from_def H1_def)
  next
    case (Cons m ys)
    note xs_Cons = Cons
    then show ?thesis
    proof (cases ys)
      case Nil
      have nl_eq: "nl = [c, m]"
        using nl_Cons xs_Cons Nil by simp
      then show ?thesis
        using pair_BB_upper_bound_decides_H1_pair[OF assms, of c m] nl_eq
        by (simp add: H1_decider_from_def)
    next
      case (Cons k zs)
      then show ?thesis
        using nl_Cons xs_Cons by (auto simp: H1_decider_from_def H1_def)
    qed
  qed
qed

corollary H1_not_turing_decidable_again: "\<not> turing_decidable H1"
  by (rule not_Turing_decidable_H1)

text \<open>
  For every upper bound, the Boolean decider above defines the same set as
  \<open>H1\<close>.  Hence AFP's existing undecidability theorem for \<open>H1\<close> immediately
  yields a concrete noncomputability consequence: the characteristic function of
  any such upper-bound-induced decider set is not Turing-computable, even in the
  total sense.  In particular, this applies to the decider induced by
  \<open>Pair_BB_time\<close> itself.
\<close>

definition H1_decider_set_from :: "(nat \<Rightarrow> nat) \<Rightarrow> nat list set" where
  "H1_decider_set_from b = {nl. H1_decider_from b nl}"

lemma H1_decider_set_from_eq_H1:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "H1_decider_set_from b = H1"
  using H1_decider_from_correct[OF assms]
  by (auto simp: H1_decider_set_from_def)

theorem no_turing_decidable_H1_decider_set_from:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "\<not> turing_decidable (H1_decider_set_from b)"
  using H1_decider_set_from_eq_H1[OF assms] not_Turing_decidable_H1
  by simp

theorem no_turing_computable_partial_H1_decider_from:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "\<not> turing_computable_partial (chi_fun (H1_decider_set_from b))"
  using no_turing_decidable_H1_decider_set_from[OF assms]
    turing_computable_partial_imp_turing_decidable
  by blast

theorem no_turing_computable_total_H1_decider_from:
  assumes "pair_busy_beaver.upper_bound_for_BB b"
  shows "\<not> turing_computable_total (chi_fun (H1_decider_set_from b))"
  using no_turing_computable_partial_H1_decider_from[OF assms]
    turing_computable_total_imp_turing_computable_partial
  by blast

theorem no_turing_computable_total_H1_deciding_upper_bound:
  "\<not> (\<exists>b. pair_busy_beaver.upper_bound_for_BB b \<and>
      turing_computable_total (chi_fun (H1_decider_set_from b)))"
  using no_turing_computable_total_H1_decider_from by blast

corollary no_turing_computable_total_Pair_BB_time_decider:
  "\<not> turing_computable_total (chi_fun (H1_decider_set_from Pair_BB_time))"
  using no_turing_computable_total_H1_decider_from
    pair_busy_beaver.BB_time_is_upper_bound
  by blast

end

end
