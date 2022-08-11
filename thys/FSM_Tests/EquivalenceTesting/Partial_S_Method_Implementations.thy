section \<open>Implementations of the Partial-S-Method\<close>

theory Partial_S_Method_Implementations
imports Intermediate_Frameworks
begin

subsection \<open>Using the H-Framework\<close>

(* check whether q2 can be reached from q1 in up to a given number steps *)
fun distance_at_most :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "distance_at_most M q1 q2 0 = (q1 = q2)" |
  "distance_at_most M q1 q2 (Suc k) = ((q1 = q2) \<or> (\<exists> x \<in> inputs M . \<exists> (y,q1') \<in> h M (q1,x) . distance_at_most M q1' q2 k))"

(* check whether X (unverified transitions) contains some t' such that the source of t' is reachable from the target of t in at most l steps *)
definition do_establish_convergence :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> nat \<Rightarrow> bool" where
  "do_establish_convergence M V t X l = (find (\<lambda> t' . distance_at_most M (t_target t) (t_source t') l) X \<noteq> None)"      

definition partial_s_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "partial_s_method_via_h_framework = h_framework_dynamic do_establish_convergence"

definition partial_s_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "partial_s_method_via_h_framework_lists M m completeInputTraces useInputHeuristic = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (partial_s_method_via_h_framework M m completeInputTraces useInputHeuristic))"

lemma partial_s_method_via_h_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (partial_s_method_via_h_framework M1 m completeInputTraces useInputHeuristic)) = (L M2 \<inter> set (partial_s_method_via_h_framework M1 m completeInputTraces useInputHeuristic)))"
and "finite_tree (partial_s_method_via_h_framework M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_completeness_and_finiteness[OF assms]
  unfolding partial_s_method_via_h_framework_def 
  by blast+

lemma partial_s_method_via_h_framework_lists_completeness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (partial_s_method_via_h_framework_lists M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_lists_completeness[OF assms]
  unfolding partial_s_method_via_h_framework_lists_def h_framework_dynamic_lists_def partial_s_method_via_h_framework_def
  by blast


end