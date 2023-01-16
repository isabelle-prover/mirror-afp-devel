
theory Boolean_functions
  imports
    Main
    "Jordan_Normal_Form.Matrix"
begin

section\<open>Boolean functions\<close>

text\<open>Definition of monotonicity\<close>

text\<open>We consider (monotone) Boolean
  functions over vectors of length $n$, so that we can later
  prove that those are isomorphic to
  simplicial complexes of dimension $n$ (in $n$ vertexes).\<close>

locale boolean_functions
  = fixes n::"nat"
begin

definition bool_fun_dim_n :: "(bool vec => bool) set"
  where "bool_fun_dim_n = {f. f \<in> carrier_vec n \<rightarrow> (UNIV::bool set)}"

definition monotone_bool_fun :: "(bool vec => bool) => bool"
  where "monotone_bool_fun \<equiv> (mono_on (carrier_vec n))"

definition monotone_bool_fun_set :: "(bool vec => bool) set"
  where "monotone_bool_fun_set = (Collect monotone_bool_fun)"

text\<open>Some examples of Boolean functions\<close>

definition bool_fun_top :: "bool vec => bool"
  where "bool_fun_top f = True"

definition bool_fun_bot :: "bool vec => bool"
  where "bool_fun_bot f = False"

end

section\<open>Threshold function\<close>

definition count_true :: "bool vec => nat"
  where "count_true v = sum (\<lambda>i. if vec_index v i then 1 else 0::nat) {0..<dim_vec v}"

lemma "vec_index (vec (5::nat) (\<lambda>i. False)) 2 = False"
  by simp

lemma "vec_index (vec (5::nat) (\<lambda>i. True)) 3 = True"
  by simp

lemma "count_true (vec (1::nat) (\<lambda>i. True)) = 1"
  unfolding count_true_def by simp

lemma "count_true (vec (2::nat) (\<lambda>i. True)) = 2"
  unfolding count_true_def by simp

lemma "count_true (vec (5::nat) (\<lambda>i. True)) = 5"
  unfolding count_true_def by simp

text\<open>The threshold function is a Boolean function
  which also satisfies the condition of being \emph{evasive}.
  We follow the definition by Scoville~\<^cite>\<open>\<open>Problem 6.5\<close> in "SC19"\<close>.\<close>

definition bool_fun_threshold :: "nat => (bool vec => bool)"
  where "bool_fun_threshold i = (\<lambda>v. if i \<le> count_true v then True else False)"

context boolean_functions
begin

lemma "mono_on UNIV bool_fun_top"
  by (simp add: bool_fun_top_def mono_onI monotone_bool_fun_def)

lemma "monotone_bool_fun bool_fun_top"
  by (simp add: bool_fun_top_def mono_onI monotone_bool_fun_def)

lemma "mono_on UNIV bool_fun_bot"
  by (simp add: bool_fun_bot_def mono_onI monotone_bool_fun_def)

lemma "monotone_bool_fun bool_fun_bot"
  by (simp add: bool_fun_bot_def mono_onI monotone_bool_fun_def)

lemma
  monotone_count_true:
  assumes ulev: "(u::bool vec) \<le> v"
  shows "count_true u \<le> count_true v"
  unfolding count_true_def
  using Groups_Big.ordered_comm_monoid_add_class.sum_mono
    [of "{0..<dim_vec u}"
      "(\<lambda>i. if vec_index u i then 1 else 0)"
      "(\<lambda>i. if vec_index v i then 1 else 0)"]
  using ulev
  unfolding Matrix.less_eq_vec_def
  by fastforce

text\<open>The threshold function is monotone.\<close>

lemma
  monotone_threshold:
  assumes ulev: "(u::bool vec) \<le> v"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  unfolding bool_fun_threshold_def
  using monotone_count_true [OF ulev] by simp

lemma
  assumes "(u::bool vec) \<le> v"
  and "n < dim_vec u"
  shows "bool_fun_threshold n u \<le> bool_fun_threshold n v"
  using monotone_threshold [OF assms(1)] .

lemma "mono_on UNIV (bool_fun_threshold n)"
  by (meson mono_onI monotone_bool_fun_def monotone_threshold)

lemma "monotone_bool_fun (bool_fun_threshold n)"
  unfolding monotone_bool_fun_def
  by (meson boolean_functions.monotone_threshold mono_onI)

end

end
