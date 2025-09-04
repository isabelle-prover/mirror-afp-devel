\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Unification_Attributes
  imports
    Unification_Attributes_Base
    ML_Unifiers
begin

paragraph \<open>Summary\<close>
text \<open>Setup of OF attribute with adjustable unifier.\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Standard_Unify_OF
  functor_name: Unify_OF
  id: \<open>""\<close>
  more_args: \<open>val init_args = {
    normalisers = SOME Standard_Mixed_Comb_Unification.norms_first_higherp_comb_unify,
    unifier = SOME Standard_Mixed_Comb_Unification.first_higherp_comb_unify,
    mode = SOME (Unify_OF_Args.PM.key Unify_OF_Args.PM.fact)
  }\<close>\<close>
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
  by (fact h1[uOF h2 h3 mode: resolve]) \<comment>\<open>the line below is equivalent\<close>
  (* by (fact h1[OF h2 h3]) *)

lemma
  assumes h1: "(PROP A \<Longrightarrow> PROP A)"
  assumes h2: "(PROP A \<Longrightarrow> PROP A) \<Longrightarrow> PROP B"
  shows "PROP B"
  by (fact h2[uOF h1]) \<comment>\<open>the line below is equivalent\<close>
  (* by (fact h2[uOF h1 mode: fact]) *)
  (* \<comment>\<open>Note: @{attribute OF} would not work in this case:\<close> *)
  (* thm h2[OF h1] *)

lemma
  assumes h1: "\<And>x y z. PROP P x y \<Longrightarrow> PROP P y y \<Longrightarrow> (PROP A \<Longrightarrow> PROP A) \<Longrightarrow>
    (PROP A \<Longrightarrow> PROP B) \<Longrightarrow> PROP C"
  and h2: "\<And>x y. PROP P x y"
  and h3 : "PROP A \<Longrightarrow> PROP A"
  and h4 : "PROP D \<Longrightarrow> PROP B"
  shows "(PROP A \<Longrightarrow> PROP D) \<Longrightarrow> PROP C"
  by (fact h1[uOF h2 h2 h3, uOF h4 mode: resolve])

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
  by (fact h1[uOF h2 unifier: First_Order_Unification.unify]) \<comment>\<open>the line below is equivalent\<close>
  (* supply [[uOF unifier: First_Order_Unification.unify]] by (fact h1[uOF h2]) *)
end

end
