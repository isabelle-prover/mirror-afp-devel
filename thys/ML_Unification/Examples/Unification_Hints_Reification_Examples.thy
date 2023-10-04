\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
section \<open>Examples: Reification Via Unification Hints\<close>
theory Unification_Hints_Reification_Examples
  imports
    HOL.Rat
    ML_Unification_HOL_Setup
    Unify_Fact_Tactic
begin

paragraph \<open>Summary\<close>
text \<open>Reification via unification hints. For an introduction to unification hints refer
to \<^cite>\<open>"unif-hints"\<close>. We support a generalisation of unification hints as described
in @{theory ML_Unification.ML_Unification_Hints}.\<close>

subsection \<open>Setup\<close>

text \<open>One-time setup to obtain a unifier with unification hints for the purpose of reification.
We could also simply use the standard unification hints @{attribute uhint},
but having separate instances is a cleaner approach.\<close>

ML\<open>
  @{functor_instance struct_name = Reification_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>"reify"\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        normalisers = SOME Higher_Order_Pattern_Unification.norms_unify,
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.unifiables),
        prems_unifier = NONE,
        concl_unifier = NONE,
        hint_preprocessor = SOME (Standard_Unification_Hints.get_hint_preprocessor
          (Context.the_generic_context ()))
      }\<close>}
  val reify_unify = Unification_Combinator.add_fallback_unifier
    (fn unif_theory =>
      Higher_Order_Pattern_Unification.e_unify Unification_Util.unify_types unif_theory unif_theory)
    (Reification_Unification_Hints.try_hints
      |> Unification_Combinator.norm_unifier (#norm_term Higher_Order_Pattern_Unification.norms_unify))
\<close>
local_setup \<open>Reification_Unification_Hints.setup_attribute NONE\<close>

text \<open>Premises of hints should again be unified by the reification unifier.\<close>
declare [[reify_uhint where prems_unifier = reify_unify]]

subsection \<open>Formulas with Quantifiers and Environment\<close>

text \<open>The following example is taken from HOL-Library.Reflection\_Examples. It is recommended
to compare the approach presented here with the reflection tactic presented in said theory.\<close>

datatype form =
  TrueF
| FalseF
| Less nat nat
| And form form
| Or form form
| Neg form
| ExQ form

primrec interp :: "form \<Rightarrow> ('a::ord) list \<Rightarrow> bool"
where
  "interp TrueF vs \<longleftrightarrow> True"
| "interp FalseF vs \<longleftrightarrow> False"
| "interp (Less i j) vs \<longleftrightarrow> vs ! i < vs ! j"
| "interp (And f1 f2) vs \<longleftrightarrow> interp f1 vs \<and> interp f2 vs"
| "interp (Or f1 f2) vs \<longleftrightarrow> interp f1 vs \<or> interp f2 vs"
| "interp (Neg f) vs \<longleftrightarrow> \<not> interp f vs"
| "interp (ExQ f) vs \<longleftrightarrow> (\<exists>v. interp f (v # vs))"

paragraph \<open>Reification with unification and recursive hint unification for conclusion\<close>

text \<open>The following illustrates how to use the equations @{thm interp.simps} directly
as unification hints for reification.\<close>

experiment
begin

text \<open>Hints for list lookup.\<close>
declare List.nth_Cons_Suc[reify_uhint where prio = Prio.LOW]
  and List.nth_Cons_0[reify_uhint]

text \<open>Hints to reify formulas of type @{type bool} into formulas of type @{type form}.\<close>
declare interp.simps[reify_uhint]

text \<open>We have to allow the hint unifier to recursively look for hints during unification of
the hint's conclusion.\<close>
declare [[reify_uhint where concl_unifier = reify_unify]]

(*uncomment the following to see the hint unification process*)
(* declare [[ML_map_context \<open>Logger.set_log_levels Unification_Base.logger Logger.DEBUG\<close>]] *)

schematic_goal
  "interp ?f (?vs :: ('a :: ord) list) = (\<exists>(x :: 'a). x < y \<and> \<not>(\<exists>(z :: 'a). v < z \<or> \<not>False))"
  by (ufact refl where unifier = reify_unify)

text \<open>While this all works nicely if set up correctly, it can be rather difficult to
understand and debug the recursive unification process for a hint's conclusion.
In the next paragraph, we present an alternative that is closer to the examples presented
in the original unification hints paper \<^cite>\<open>"unif-hints"\<close>.\<close>

end

paragraph \<open>Reification with matching without recursion for conclusion\<close>

text \<open>We disallow the hint unifier to recursively look for hints while unifying the conclusion;
instead, we only allow the hint unifier to match the hint's conclusion against the disagreement terms.\<close>
declare [[reify_uhint where concl_unifier = Higher_Order_Pattern_Unification.match]]

text \<open>However, this also means that we now have to write our hints such that the hint's
conclusion can successfully be matched against the disagreement terms. In particular,
the disagreement terms may still contain meta variables that we want to instantiate with the help
of the unification hints. Essentially, a hint then describes a canonical instantiation for
these meta variables.\<close>

experiment
begin

lemma [reify_uhint where prio = Prio.LOW]:
  "n \<equiv> Suc n' \<Longrightarrow> vs \<equiv> v # vs' \<Longrightarrow> vs' ! n' \<equiv> x \<Longrightarrow> vs ! n \<equiv> x"
  by simp

lemma [reify_uhint]: "n \<equiv> 0 \<Longrightarrow> vs \<equiv> x # vs' \<Longrightarrow> vs ! n \<equiv> x"
  by simp

lemma [reify_uhint]:
  "\<lbrakk>e \<equiv> ExQ f; \<And>v. interp f (v # vs) \<equiv> P v\<rbrakk> \<Longrightarrow> interp e vs \<equiv> \<exists>v. P v"
  "\<lbrakk>e \<equiv> Less i j; x \<equiv> vs ! i; y \<equiv> vs ! j\<rbrakk> \<Longrightarrow> interp e vs \<equiv> x < y"
  "\<lbrakk>e \<equiv> And f1 f2; interp f1 vs \<equiv> r1; interp f2 vs \<equiv> r2\<rbrakk> \<Longrightarrow> interp e vs \<equiv> r1 \<and> r2"
  "\<lbrakk>e \<equiv> Or f1 f2; interp f1 vs \<equiv> r1; interp f2 vs \<equiv> r2\<rbrakk> \<Longrightarrow> interp e vs \<equiv> r1 \<or> r2"
  "e \<equiv> Neg f \<Longrightarrow> interp f vs \<equiv> r \<Longrightarrow> interp e vs \<equiv> \<not>r"
  "e \<equiv> TrueF \<Longrightarrow> interp e vs \<equiv> True"
  "e \<equiv> FalseF \<Longrightarrow> interp e vs \<equiv> False"
  by simp_all

schematic_goal
  "interp ?f (?vs :: ('a :: ord) list) = (\<exists>(x :: 'a). x < y \<and> \<not>(\<exists>(z :: 'a). v < z \<or> \<not>False))"
  by (urule refl where unifier = reify_unify)
end

text \<open>The next examples are modification from \<^cite>\<open>"unif-hints"\<close>.\<close>

subsection \<open>Simple Arithmetic\<close>

datatype add_expr = Var int | Add add_expr add_expr

fun eval_add_expr :: "add_expr \<Rightarrow> int" where
  "eval_add_expr (Var i) = i"
| "eval_add_expr (Add ex1 ex2) = eval_add_expr ex1 + eval_add_expr ex2"

lemma eval_add_expr_Var [reify_uhint where prio = Prio.LOW]:
  "e \<equiv> Var i \<Longrightarrow> eval_add_expr e \<equiv> i" by simp

lemma eval_add_expr_add [reify_uhint]:
  "e \<equiv> Add e1 e2 \<Longrightarrow> eval_add_expr e1 \<equiv> m \<Longrightarrow> eval_add_expr e2 \<equiv> n \<Longrightarrow> eval_add_expr e \<equiv> m + n"
  by simp

ML_command\<open>
  val t1 = Proof_Context.read_term_pattern @{context} "eval_add_expr ?e"
  val t2 = Proof_Context.read_term_pattern @{context} "1 + (2 + 7) :: int"
  val _ = Unification_Util.log_unif_results @{context} (t1, t2) (reify_unify [])
\<close>

schematic_goal "eval_add_expr ?e = (1 + (2 + 7) :: int)"
  by (urule refl where unifier = reify_unify)


subsection \<open>Arithmetic with Environment\<close>

datatype mul_expr =
  Unit
| Var nat
| Mul mul_expr mul_expr
| Inv mul_expr

fun eval_mul_expr :: "mul_expr \<times> rat list \<Rightarrow> rat" where
  "eval_mul_expr (Unit, \<Gamma>) = 1"
| "eval_mul_expr (Var i, \<Gamma>) = \<Gamma> ! i"
| "eval_mul_expr (Mul e1 e2, \<Gamma>) = eval_mul_expr (e1, \<Gamma>) * eval_mul_expr (e2, \<Gamma>)"
| "eval_mul_expr (Inv e, \<Gamma>) = inverse (eval_mul_expr (e, \<Gamma>))"

text \<open>Split @{term e} into an expression and an environment.\<close>
lemma [reify_uhint where prio = Prio.VERY_LOW]:
  "e \<equiv> (e1, \<Gamma>) \<Longrightarrow> eval_mul_expr (e1, \<Gamma>) \<equiv> n \<Longrightarrow> eval_mul_expr e \<equiv> n"
  by simp

text \<open>Hints for environment lookup.\<close>
lemma [reify_uhint where prio = Prio.LOW]:
  "e \<equiv> Var (Suc p) \<Longrightarrow> \<Gamma> \<equiv> s # \<Delta> \<Longrightarrow> n \<equiv> eval_mul_expr (Var p, \<Delta>) \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> n"
  by simp

lemma [reify_uhint]: "e \<equiv> Var 0 \<Longrightarrow> \<Gamma> \<equiv> n # \<Theta> \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> n"
  by simp

lemma [reify_uhint]:
  "e1 \<equiv> Inv e2 \<Longrightarrow> n \<equiv> eval_mul_expr (e2, \<Gamma>) \<Longrightarrow> eval_mul_expr (e1, \<Gamma>) \<equiv> inverse n"
  "e \<equiv> Mul e1 e2 \<Longrightarrow> m \<equiv> eval_mul_expr (e1, \<Gamma>) \<Longrightarrow>
  n \<equiv> eval_mul_expr (e2, \<Gamma>) \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> m * n"
  "e \<equiv> Unit \<Longrightarrow> eval_mul_expr (e, \<Gamma>) \<equiv> 1"
  by simp_all

ML_command\<open>
  val t1 = Proof_Context.read_term_pattern @{context} "eval_mul_expr ?e"
  val t2 = Proof_Context.read_term_pattern @{context} "1 * inverse 3 * 5 :: rat"
  val _ = Unification_Util.log_unif_results' 1 @{context} (t2, t1) (reify_unify [])
\<close>

schematic_goal "eval_mul_expr ?e = (1 * inverse 3 * 5 :: rat)"
  by (ufact refl where unifier = reify_unify)

end
