\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Resolution Tactics\<close>
theory Unify_Resolve_Tactics
  imports
    Unify_Assumption_Tactic
    ML_Method_Utils
begin

paragraph \<open>Summary\<close>
text \<open>Resolution tactics and methods with adjustable unifier.\<close>

ML_file\<open>unify_resolve_base.ML\<close>
ML_file\<open>unify_resolve.ML\<close>
ML\<open>
  @{functor_instance struct_name = Standard_Unify_Resolve
    and functor_name = Unify_Resolve
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
      unifier = SOME Standard_Mixed_Unification.first_higherp_first_comb_higher_unify,
      mode = SOME (Unify_Resolve_Args.PM.key Unify_Resolve_Args.PM.any),
      chained = SOME (Unify_Resolve_Args.PCM.key Unify_Resolve_Args.PCM.resolve)
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_Resolve.setup_attribute NONE\<close>
local_setup \<open>Standard_Unify_Resolve.setup_method NONE\<close>


paragraph \<open>Examples\<close>

experiment
begin

lemma
  assumes h: "\<And>x. PROP D x \<Longrightarrow> PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  apply (urule h) \<comment>\<open>the line below is equivalent\<close>
  (* apply (rule h) *)
  oops

lemma
  assumes h: "PROP C x"
  shows "PROP C x"
  by (urule h where unifier = First_Order_Unification.unify) \<comment>\<open>the line below is equivalent\<close>
  (* using [[urule unifier = First_Order_Unification.unify]] by (urule h) *)

lemma
  assumes h: "\<And>x. PROP A x \<Longrightarrow> PROP D x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  \<comment>\<open>use (r,e,d,f) to specify the resolution mode (resolution, elim, dest, forward)\<close>
  apply (urule (d) h) \<comment>\<open>the line below is equivalent\<close>
  (* apply (drule h) *)
  oops

text\<open>You can specify how chained facts should be used. By default, @{method urule} works like
@{method rule}: it uses chained facts to resolve against the premises of the passed rules.\<close>

lemma
  assumes h1: "\<And>x. (PROP F x \<Longrightarrow> PROP E x) \<Longrightarrow> PROP C x"
  and h2: "\<And>x. PROP F x \<Longrightarrow> PROP E x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  \<comment>\<open>Compare all of the following calls:\<close>
  (* apply (rule h1) *)
  (* apply (urule h1) *)
  (* using h2 apply (rule h1) *)
  (* using h2 apply (urule h1) *)
  using h2 apply (urule h1 where chained = fact)
  (* using h2 apply (urule h1 where chained = insert) *)
  done

text\<open>You can specify whether any or every rule must resolve against the goal:\<close>

lemma
  assumes h1: "\<And>x y. PROP C y \<Longrightarrow> PROP D x \<Longrightarrow> PROP C x"
  and h2: "\<And>x y. PROP C x \<Longrightarrow> PROP D x"
  and h3: "\<And>x y. PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  using h3 apply (urule h1 h2 where mode = every)
  (* using h3 apply (urule h1 h2) *)
  done

lemma
  assumes h1: "\<And>x y. PROP C y \<Longrightarrow> PROP A x \<Longrightarrow> PROP C x"
  and h2: "\<And>x y. PROP C x \<Longrightarrow> PROP B x \<Longrightarrow> PROP D x"
  and h3: "\<And>x y. PROP C x"
  shows "\<And>x. PROP A x \<Longrightarrow> PROP B x \<Longrightarrow> PROP C x"
  using h3 apply (urule (d) h1 h2 where mode = every)
  oops

end

end
