\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Assumption Tactic\<close>
theory Unify_Assumption_Tactic
  imports
    ML_Functor_Instances
    ML_Unifiers
    ML_Unification_Parsers
begin

paragraph \<open>Summary\<close>
text \<open>Assumption tactic and method with adjustable unifier.\<close>

ML_file\<open>unify_assumption_base.ML\<close>
ML_file\<open>unify_assumption.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_Assumption
    and functor_name = Unify_Assumption
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
      unifier = SOME Standard_Mixed_Unification.first_higherp_first_comb_higher_unify
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_Assumption.setup_attribute NONE\<close>
local_setup \<open>Standard_Unify_Assumption.setup_method NONE\<close>


paragraph \<open>Examples\<close>

experiment
begin

lemma "PROP P \<Longrightarrow> PROP P"
  by uassm

lemma
  assumes h: "\<And>P. PROP P"
  shows "PROP P x"
  using h by uassm

schematic_goal "\<And>x. PROP P (c :: 'a) \<Longrightarrow> PROP ?Y (x :: 'a)"
  by uassm

schematic_goal a: "PROP ?P (y :: 'a) \<Longrightarrow> PROP ?P (?x :: 'a)"
  by uassm \<comment>\<open>compare the result with following call\<close>
  (* by assumption *)

schematic_goal
  "PROP ?P (x :: 'a) \<Longrightarrow> PROP P (?x :: 'a)"
  by uassm \<comment>\<open>compare the result with following call\<close>
  (* by assumption *)

schematic_goal
  "\<And>x. PROP D \<Longrightarrow> (\<And>P y. PROP P y x) \<Longrightarrow> PROP C \<Longrightarrow> PROP P x"
  by (uassm unifier = Higher_Order_Unification.unify) \<comment>\<open>the line below is equivalent\<close>
  (* using [[uassm unifier = Higher_Order_Unification.unify]] by uassm *)

text \<open>Unlike @{method assumption}, @{method uassm} will not close the goal if the order of premises
of the assumption and the goal are different. Compare the following two examples:\<close>

lemma "\<And>x. PROP D \<Longrightarrow> (\<And>y. PROP A y \<Longrightarrow> PROP B x) \<Longrightarrow> PROP C \<Longrightarrow> PROP A x \<Longrightarrow> PROP B x"
  by uassm

lemma "\<And>x. PROP D \<Longrightarrow> (\<And>y. PROP A y \<Longrightarrow> PROP B x) \<Longrightarrow> PROP A x \<Longrightarrow> PROP C \<Longrightarrow> PROP B x"
  by assumption
  (* by uassm *)
end

end
