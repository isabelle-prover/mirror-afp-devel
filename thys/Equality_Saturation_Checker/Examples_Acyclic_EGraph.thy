section \<open>Global extraction over a finite e-class DAG\<close>

theory Examples_Acyclic_EGraph
  imports Certified_Acyclic_EGraph
begin

datatype dag_sym = Dag_X | Dag_One | Dag_Two | Dag_Add | Dag_Mul | Dag_Shl

fun dag_cost :: "dag_sym \<Rightarrow> nat" where
  "dag_cost Dag_X = 0"
| "dag_cost Dag_One = 1"
| "dag_cost Dag_Two = 1"
| "dag_cost Dag_Add = 1"
| "dag_cost Dag_Mul = 4"
| "dag_cost Dag_Shl = 5"

text \<open>
  Classes 0--2 are leaves.  Class 3 contains three representations of the
  same strength-reduced expression.  Class 4 contains one binary addition
  e-node whose two children both refer to class 3.  Consequently class 4
  represents all nine combinations of the three child representations.
\<close>

definition strength_dag :: "dag_sym acyclic_egraph" where
  "strength_dag =
    [ [(Dag_X, [])]
    , [(Dag_One, [])]
    , [(Dag_Two, [])]
    , [(Dag_Shl, [0, 1]), (Dag_Mul, [0, 2]), (Dag_Add, [0, 0])]
    , [(Dag_Add, [3, 3])] ]"

definition dag_x :: "(dag_sym, unit) term" where
  "dag_x = Fun Dag_X []"

definition dag_best_child :: "(dag_sym, unit) term" where
  "dag_best_child = Fun Dag_Add [dag_x, dag_x]"

definition dag_best_root :: "(dag_sym, unit) term" where
  "dag_best_root = Fun Dag_Add [dag_best_child, dag_best_child]"

definition dag_canonical_child :: "(dag_sym, unit) term" where
  "dag_canonical_child = Fun Dag_Shl [dag_x, Fun Dag_One []]"

definition dag_canonical_root :: "(dag_sym, unit) term" where
  "dag_canonical_root =
    Fun Dag_Add [dag_canonical_child, dag_canonical_child]"

definition strength_dag_rules :: "(dag_sym, unit) rule list" where
  "strength_dag_rules =
    [ (dag_canonical_child, dag_best_child)
    , (Fun Dag_Mul [dag_x, Fun Dag_Two []], dag_best_child) ]"

definition strength_dag_certificates :: "dag_sym dag_certificates" where
  "strength_dag_certificates =
    [ [[]]
    , [[]]
    , [[]]
    , [ []
      , [Rule_At [] 0 Forward Var, Rule_At [] 1 Backward Var]
      , [Rule_At [] 0 Forward Var] ]
    , [[]] ]"

lemma strength_dag_wf:
  "wf_acyclic_egraph strength_dag"
  by eval

lemma strength_dag_extracts:
  "extract_eclass dag_cost strength_dag 4 = Some dag_best_root"
  by eval

lemma strength_dag_certified:
  "check_certified_egraph
    strength_dag_rules strength_dag strength_dag_certificates"
  by eval

lemma strength_dag_canonical:
  "canonical_eclass strength_dag 4 = Some dag_canonical_root"
  by eval

definition cyclic_dag :: "dag_sym acyclic_egraph" where
  "cyclic_dag = [[(Dag_Add, [0, 0])]]"

lemma cyclic_dag_not_wf:
  "\<not> wf_acyclic_egraph cyclic_dag"
  by eval

lemma cyclic_dag_extraction_rejected:
  "extract_egraph dag_cost cyclic_dag = None"
  unfolding extract_egraph_def using cyclic_dag_not_wf by simp

lemma cyclic_dag_certificate_rejected:
  "\<not> check_certified_egraph [] cyclic_dag [[[]]]"
  unfolding check_certified_egraph_def using cyclic_dag_not_wf by simp

lemma strength_dag_child_alternatives:
  "represents_eclass strength_dag 3
      (Fun Dag_Shl [dag_x, Fun Dag_One []])"
  "represents_eclass strength_dag 3
      (Fun Dag_Mul [dag_x, Fun Dag_Two []])"
  "represents_eclass strength_dag 3 dag_best_child"
  unfolding dag_x_def dag_best_child_def strength_dag_def
  by (auto intro!: represents_eclass.intros)

lemma strength_dag_root_has_cross_product:
  "represents_eclass strength_dag 4
    (Fun Dag_Add
      [Fun Dag_Shl [dag_x, Fun Dag_One []],
       Fun Dag_Mul [dag_x, Fun Dag_Two []]])"
  unfolding strength_dag_def dag_x_def
  by (auto intro!: represents_eclass.intros)

theorem strength_dag_global_minimum:
  assumes "represents_eclass strength_dag 4 t"
  shows "term_cost dag_cost dag_best_root \<le> term_cost dag_cost t"
proof -
  have index: "4 < length strength_dag" by eval
  from extract_eclass_global_minimum[
      OF strength_dag_wf index, of dag_cost]
  obtain best where
    extracted: "extract_eclass dag_cost strength_dag 4 = Some best" and
    minimal: "\<And>u. represents_eclass strength_dag 4 u \<Longrightarrow>
      term_cost dag_cost best \<le> term_cost dag_cost u"
    by blast
  from extracted strength_dag_extracts have "best = dag_best_root" by simp
  with minimal[OF assms] show ?thesis by simp
qed

theorem strength_dag_all_represented_equal:
  assumes "represents_eclass strength_dag 4 t"
  shows "(dag_canonical_root, t)
    \<in> (rstep (set strength_dag_rules))\<^sup>\<leftrightarrow>\<^sup>*"
proof -
  have index: "4 < length strength_dag" by eval
  have "(canonical_prefix strength_dag (Suc 4) ! 4, t)
      \<in> (rstep (set strength_dag_rules))\<^sup>\<leftrightarrow>\<^sup>*"
    by (rule checked_egraph_representation_sound[
          OF strength_dag_certified index assms])
  moreover have
    "canonical_prefix strength_dag (Suc 4) ! 4 = dag_canonical_root"
    by eval
  ultimately show ?thesis by simp
qed

theorem certified_strength_dag_extraction:
  "(dag_canonical_root, dag_best_root)
    \<in> (rstep (set strength_dag_rules))\<^sup>\<leftrightarrow>\<^sup>*"
  "represents_eclass strength_dag 4 dag_best_root"
  "\<And>u. represents_eclass strength_dag 4 u \<Longrightarrow>
    term_cost dag_cost dag_best_root \<le> term_cost dag_cost u"
proof -
  have index: "4 < length strength_dag" by eval
  from certified_egraph_extraction_correct[
      OF strength_dag_certified index, of dag_cost]
  obtain source chosen where
    source: "canonical_eclass strength_dag 4 = Some source" and
    chosen: "extract_eclass dag_cost strength_dag 4 = Some chosen" and
    sound:
      "(source, chosen)
        \<in> (rstep (set strength_dag_rules))\<^sup>\<leftrightarrow>\<^sup>*" and
    represented: "represents_eclass strength_dag 4 chosen" and
    minimal: "\<And>u. represents_eclass strength_dag 4 u \<Longrightarrow>
      term_cost dag_cost chosen \<le> term_cost dag_cost u"
    by blast
  from source strength_dag_canonical have source_eq:
    "source = dag_canonical_root" by simp
  from chosen strength_dag_extracts have chosen_eq:
    "chosen = dag_best_root" by simp
  from sound source_eq chosen_eq show
    "(dag_canonical_root, dag_best_root)
      \<in> (rstep (set strength_dag_rules))\<^sup>\<leftrightarrow>\<^sup>*"
    by simp
  from represented chosen_eq show
    "represents_eclass strength_dag 4 dag_best_root" by simp
  from minimal chosen_eq show
    "term_cost dag_cost dag_best_root \<le> term_cost dag_cost u"
    if "represents_eclass strength_dag 4 u" for u
    using that by simp
qed

value "extract_egraph dag_cost strength_dag"
value "extract_eclass dag_cost strength_dag 4"

end
