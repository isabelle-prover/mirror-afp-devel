section \<open>Executable checker and producer\<close>

theory Code_Generation
  imports Examples_Compiler Examples_Egg Examples_Acyclic_EGraph
begin

text \<open>
  Only the equality-saturation-specific layer is exported.  Terms,
  substitutions, positions, and position enumeration come from
  \<^session>\<open>First_Order_Terms\<close>; the specification theorem targets
  \<^session>\<open>First_Order_Rewriting\<close>.  The exported acyclic-e-graph
  functions include both the global dynamic-programming extractor and the
  certificate checker for e-class equality.
\<close>

export_code
  apply_step apply_steps check_explanation
  tokenize_egg parse_egg_sexp decode_egg_line
  compile_egg_explanation check_egg_explanation
  check_merge_log_from check_merge_log recorded_merges
  check_extraction
  wf_acyclic_egraph instantiate_enode best_eclass_term
  extract_prefix extract_egraph extract_eclass
  canonical_prefix canonical_eclass check_dag_class check_certified_egraph
  run_bounded_search find_explanation
  in SML

export_code
  apply_step apply_steps check_explanation
  tokenize_egg parse_egg_sexp decode_egg_line
  compile_egg_explanation check_egg_explanation
  check_merge_log_from check_merge_log recorded_merges
  check_extraction
  wf_acyclic_egraph instantiate_enode best_eclass_term
  extract_prefix extract_egraph extract_eclass
  canonical_prefix canonical_eclass check_dag_class check_certified_egraph
  run_bounded_search find_explanation
  in Haskell module_name Equality_Saturation_Checker

definition produced_steps :: "(string, string) certificate_step list" where
  "produced_steps =
    the (find_explanation demo_rules [] (forward_generator demo_rules) 2
      demo_start demo_result)"

lemma produced_steps_accepted:
  "check_explanation demo_rules [] produced_steps demo_start demo_result"
proof -
  have "find_explanation demo_rules [] (forward_generator demo_rules) 2
      demo_start demo_result = Some produced_steps"
    unfolding produced_steps_def
    using demo_search_succeeds
    by (cases "find_explanation demo_rules []
          (forward_generator demo_rules) 2 demo_start demo_result") auto
  then show ?thesis by (rule find_explanation_accepted)
qed

value "check_explanation demo_rules [] produced_steps demo_start demo_result"
value "check_egg_explanation egg_compiler_rules egg_compiler_flat_output
  egg_compiler_start egg_compiler_final"
value "map (\<lambda>st. case st of
    Rule_At p i d \<sigma> \<Rightarrow> (p, i, d)
  | Merge_At p i d \<Rightarrow> (p, i, d)) produced_steps"

end
