\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Unification Hints\<close>
theory ML_Unification_Hints
  imports
    ML_Unification_Hints_Base
    ML_Unifiers
begin

paragraph \<open>Summary\<close>
text \<open>Setup of unification hints.\<close>

text \<open>We now set up two unifiers using unification hints. The first one allows for recursive
applications of unification hints when unifying a hint's conclusion \<open>lhs \<equiv> rhs\<close> with a goal
\<open>lhs' \<equiv> rhs'\<close>.
The second disallows recursive applications of unification hints. Recursive applications have to be
made explicit in the hint itself (cf. @{dir "../Examples"}).

While the former can be convenient for local hint registrations and quick developments,
it is advisable to use the second for global hints to avoid unexpected looping behaviour.\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Standard_Unification_Hints_Rec
  functor_name: Term_Index_Unification_Hints
  id: \<open>"rec"\<close>
  more_args: \<open>
    structure TI = Discrimination_Tree
    val init_args = {
      concl_unifier = SOME Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify,
      prems_unifier = SOME (Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify
        |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
      normalisers = SOME Standard_Mixed_Comb_Unification.norms_first_higherp_decomp_comb_higher_unify,
      retrieval = SOME (Term_Index_Unification_Hints_Args.mk_retrieval_sym_pair
        TI.unifiables TI.norm_term),
      hint_preprocessor = SOME (K I)}\<close>\<close>
\<close>
local_setup \<open>Standard_Unification_Hints_Rec.setup_attribute NONE\<close>

text\<open>Standard unification hints using
@{ML Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify}
when looking for hints are accessible via @{attribute rec_uhint}.

\<^emph>\<open>Note:\<close> when we retrieve a potential unification hint with conclusion \<open>lhs \<equiv> rhs\<close> for a goal
\<open>lhs' \<equiv> rhs'\<close>, we consider those hints whose lhs or rhs potentially higher-order unifies with
lhs' or rhs' \<^emph>\<open>without using hints\<close>. For otherwise, any hint \<open>lhs \<equiv> rhs\<close> applied to a goal
\<open>rhs \<equiv> lhs\<close> leads to an immediate loop. The retrieval can be further restricted and modified by
via the retrieval setting of @{attribute rec_uhint}.\<close>

declare [[ucombine \<open>Standard_Unification_Combine.eunif_data
  (Standard_Unification_Hints_Rec.try_hints
  |> Unification_Combinator.norm_unifier
    (Unification_Util.inst_norm_term'
      Standard_Mixed_Comb_Unification.norms_first_higherp_decomp_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.metadata Standard_Unification_Hints_Rec.binding Prio.LOW)\<close>]]

ML\<open>
\<^functor_instance>\<open>struct_name: Standard_Unification_Hints
  functor_name: Term_Index_Unification_Hints
  id: \<open>""\<close>
  more_args: \<open>
    structure TI = Discrimination_Tree
    val init_args = {
      concl_unifier = NONE,
      prems_unifier = SOME (Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify
        |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
      normalisers = SOME Standard_Mixed_Comb_Unification.norms_first_higherp_decomp_comb_higher_unify,
      retrieval = SOME (Term_Index_Unification_Hints_Args.mk_retrieval_sym_pair
        TI.unifiables TI.norm_term),
      hint_preprocessor = SOME (K I)}\<close>\<close>
\<close>
local_setup \<open>Standard_Unification_Hints.setup_attribute NONE\<close>
declare [[uhint config: concl_unifier = \<open>fn binders =>
  Standard_Unification_Combine.delete_eunif_data
    (Standard_Unification_Combine.metadata Standard_Unification_Hints.binding Prio.LOW1)
  (*TODO: should we also remove the recursive hint unifier here? time will tell...*)
  (*#> Standard_Unification_Combine.delete_eunif_data
    (Standard_Unification_Combine.metadata Standard_Unification_Hints_Rec.binding Prio.LOW)*)
  |> Context.proof_map
  #> Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify binders\<close>]]

text\<open>Standard unification hints using
@{ML Standard_Mixed_Comb_Unification.first_higherp_decomp_comb_higher_unify} when looking for hints,
without using fallback list of unifiers, are accessible via @{attribute uhint}.

\<^emph>\<open>Note:\<close> there will be no recursive usage of unification hints when searching for potential
unification hints in this case. See also @{dir "../Examples"}.\<close>

declare [[ucombine \<open>Standard_Unification_Combine.eunif_data
  (Standard_Unification_Hints.try_hints
  |> Unification_Combinator.norm_unifier
    (Unification_Util.inst_norm_term'
      Standard_Mixed_Comb_Unification.norms_first_higherp_decomp_comb_higher_unify)
  |> K)
  (Standard_Unification_Combine.metadata Standard_Unification_Hints.binding Prio.LOW1)\<close>]]


text\<open>Examples see @{dir "../Examples"}.\<close>

end
