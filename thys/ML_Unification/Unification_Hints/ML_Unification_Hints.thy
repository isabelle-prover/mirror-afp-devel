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
\<^functor_instance>\<open>struct_name: Unification_Hints_Rec
  functor_name: Term_Index_Unification_Hints
  id: \<open>"rec_uhint"\<close>
  more_args: \<open>
    structure TI = Discrimination_Tree
    structure Args = Term_Index_Unification_Hints_Args
    val init_args = {
      concl_unifier = SOME Mixed_Comb_Unification.fo_hop_comb_unify,
      prems_unifier = SOME (Mixed_Comb_Unification.fo_hop_comb_unify
        |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
      normalisers = SOME Mixed_Comb_Unification.norms_fo_hop_comb_unify,
      retrieval = SOME (Args.mk_retrieval_sym_pair (K TI.unifiables |> Args.retrieve_transfer)
        TI.norm_term),
      hint_preprocessor = SOME (K I)}\<close>\<close>
\<close>
local_setup \<open>Unification_Hints_Rec.setup_attribute NONE\<close>

text\<open>Standard recursive unification hints using @{ML Mixed_Comb_Unification.fo_hop_comb_unify} when
looking for hints are accessible via @{attribute rec_uhint}.

\<^emph>\<open>Note:\<close> when we retrieve a potential unification hint with conclusion \<open>lhs \<equiv> rhs\<close> for a goal
\<open>lhs' \<equiv> rhs'\<close>, we consider those hints whose lhs or rhs potentially higher-order unifies with
lhs' or rhs' \<^emph>\<open>without using hints\<close>. For otherwise, any hint \<open>lhs \<equiv> rhs\<close> applied to a goal
\<open>rhs \<equiv> lhs\<close> leads to an immediate loop. The retrieval can be further restricted and modified with
the retrieval setting of @{attribute rec_uhint}.\<close>

declare [[ucombine \<open>Unification_Combine.eunif_data
  (Unification_Combine.metadata (Unification_Hints_Rec.binding, Prio.LOW),
  Unification_Hints_Rec.try_hints
  |> Unification_Combinator.norm_unifier (Unification_Util.inst_norm_term'
    Mixed_Comb_Unification.norms_fo_hop_comb_unify)
  |> K)\<close>]]

ML\<open>
\<^functor_instance>\<open>struct_name: Unification_Hints
  functor_name: Term_Index_Unification_Hints
  id: \<open>"uhint"\<close>
  more_args: \<open>
    structure TI = Discrimination_Tree
    structure Args = Term_Index_Unification_Hints_Args
    val init_args = {
      concl_unifier = NONE,
      prems_unifier = SOME (Mixed_Comb_Unification.fo_hop_comb_unify
        |> Unification_Combinator.norm_unifier Envir_Normalisation.beta_norm_term_unif),
      normalisers = SOME Mixed_Comb_Unification.norms_fo_hop_comb_unify,
      retrieval = SOME (Args.mk_retrieval_sym_pair (K TI.unifiables |> Args.retrieve_transfer)
        TI.norm_term),
      hint_preprocessor = SOME (K I)}\<close>\<close>
\<close>
local_setup \<open>Unification_Hints.setup_attribute NONE\<close>
declare [[uhint config concl_unifier: \<open>fn binders =>
  Unification_Combine.delete_id Unification_Hints.binding
  (*TODO: should we also remove the recursive hint unifier here? time will tell...*)
  (* #> Unification_Combine.delete_id Unification_Hints_Rec.binding *)
  |> Context.proof_map
  #> Mixed_Comb_Unification.fo_hop_comb_unify binders\<close>]]

text\<open>Standard non-recursive unification hints using @{ML Mixed_Comb_Unification.fo_hop_comb_unify}
when looking for hints are accessible via @{attribute uhint}.

\<^emph>\<open>Note:\<close> there will be no recursive usage of unification hints when searching for potential
unification hints in this case. See also @{dir "../Examples"}.\<close>

declare [[ucombine \<open>Unification_Combine.eunif_data
  (Unification_Combine.metadata (Unification_Hints.binding, Prio.LOW1),
  Unification_Hints.try_hints
  |> Unification_Combinator.norm_unifier (Unification_Util.inst_norm_term'
      Mixed_Comb_Unification.norms_fo_hop_comb_unify)
  |> K)\<close>]]


text\<open>Examples see @{dir "../Examples"}.\<close>

end
