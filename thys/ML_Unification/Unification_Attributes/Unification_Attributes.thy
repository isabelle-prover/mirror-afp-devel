\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Attributes\<close>
theory Unification_Attributes
  imports Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>OF attribute with adjustable unifier.\<close>

ML_file\<open>unify_of_base.ML\<close>
ML_file\<open>unify_of.ML\<close>

ML\<open>
  @{functor_instance struct_name = Standard_Unify_OF
    and functor_name = Unify_OF
    and id = \<open>""\<close>
    and more_args = \<open>val init_args = {
      normalisers = SOME Standard_Mixed_Unification.norms_first_higherp_first_comb_higher_unify,
      unifier = SOME Standard_Mixed_Unification.first_higherp_first_comb_higher_unify,
      mode = SOME (Unify_OF_Args.PM.key Unify_OF_Args.PM.fact)
    }\<close>}
\<close>
local_setup \<open>Standard_Unify_OF.setup_attribute NONE\<close>

paragraph \<open>Examples\<close>

experiment
begin
lemma
  assumes h1: "(PROP A \<Longrightarrow> PROP D) \<Longrightarrow> PROP E \<Longrightarrow> PROP C"
  assumes h2: "PROP B \<Longrightarrow> PROP D"
  and h3: "PROP F \<Longrightarrow> PROP E"
  shows "(PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP F \<Longrightarrow> PROP C"
  by (fact h1[uOF h2 h3 where mode = resolve]) \<comment>\<open>the line below is equivalent\<close>
  (* by (fact h1[OF h2 h3]) *)

lemma
  assumes h1: "(PROP A \<Longrightarrow> PROP A)"
  assumes h2: "(PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP B"
  shows "PROP B"
  by (fact h2[uOF h1]) \<comment>\<open>the line below is equivalent\<close>
  (* by (fact h2[uOF h1 where mode = fact]) *)
  \<comment>\<open>Note: @{attribute OF} would not work in this case:\<close>
  (* thm h2[OF h1] *)

lemma
  assumes h1: "\<And>x y z. PROP P x y \<Longrightarrow> PROP P y y \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow>
    (PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP C"
  and h2: "\<And>x y. PROP P x y"
  and h3 : "PROP A \<Longrightarrow> PROP A"
  and h4 : "PROP D \<Longrightarrow> PROP B"
  shows "(PROP A \<Longrightarrow> PROP D) \<Longrightarrow> PROP C"
  by (fact h1[uOF h2 h2 h3, uOF h4 where mode = resolve])

lemma
  assumes h1: "\<And>P x. PROP P x \<Longrightarrow> PROP E P x"
  and h2: "PROP P x"
  shows "PROP E P x"
  by (fact h1[uOF h2]) \<comment>\<open>the following line does not work (multiple unifiers error)\<close>
  (* by (fact h1[OF h2]) *)

text\<open>We can also specify the unifier to be used:\<close>

lemma
  assumes h1: "\<And>P. PROP P \<Longrightarrow> PROP E"
  and h2: "\<And>P. PROP P"
  shows "PROP E"
  by (fact h1[uOF h2 where unifier = First_Order_Unification.unify]) \<comment>\<open>the line below is equivalent\<close>
  (* using [[uOF unifier = First_Order_Unification.unify]] by (fact h1[uOF h2]) *)
end

end
