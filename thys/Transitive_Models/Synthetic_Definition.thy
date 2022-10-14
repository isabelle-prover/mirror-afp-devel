section\<open>Automatic synthesis of formulas\<close>
theory Synthetic_Definition
  imports
    Utils
  keywords
    "synthesize" :: thy_decl % "ML"
    and
    "synthesize_notc" :: thy_decl % "ML"
    and
    "generate_schematic" :: thy_decl % "ML"
    and
    "arity_theorem" :: thy_decl % "ML"
    and
    "manual_schematic" :: thy_goal_stmt % "ML"
    and
    "manual_arity" :: thy_goal_stmt % "ML"
    and
    "from_schematic"
    and
    "for"
    and
    "from_definition"
    and
    "assuming"
    and
    "intermediate"

begin

named_theorems fm_definitions "Definitions of synthetized formulas."

named_theorems iff_sats "Theorems for synthetising formulas."

named_theorems arity "Theorems for arity of formulas."

named_theorems arity_aux "Auxiliary theorems for calculating arities."

ML_file\<open>Synthetic_Definition.ml\<close>

text\<open>The \<^ML>\<open>synthetic_def\<close> function extracts definitions from
schematic goals. A new definition is added to the context. \<close>

(* example of use *)
(*
schematic_goal mem_formula_ex :
  assumes "m\<in>nat" "n\<in> nat" "env \<in> list(M)"
  shows "nth(m,env) \<in> nth(n,env) \<longleftrightarrow> sats(M,?frm,env)"
  by (insert assms ; (rule sep_rules empty_iff_sats cartprod_iff_sats | simp del:sats_cartprod_fm)+)

synthesize "\<phi>" from_schematic mem_formula_ex
*)

end
