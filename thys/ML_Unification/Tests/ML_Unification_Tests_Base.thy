\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Test Setup\<close>
theory ML_Unification_Tests_Base
  imports
    ML_Unification_Hints
    SpecCheck.SpecCheck
    Main
begin

paragraph \<open>Summary\<close>
text \<open>Shared setup for unification tests. We use \<^cite>\<open>speccheck\<close> to generate
tests and create unit tests.\<close>

ML\<open>
\<^functor_instance>\<open>struct_name: Test_Unification_Hints
  functor_name: Term_Index_Unification_Hints
  id: \<open>"test"\<close>
  more_args: \<open>
    structure TI = Discrimination_Tree
    structure Args = Term_Index_Unification_Hints_Args
    val init_args = {
      concl_unifier = SOME (Higher_Order_Pattern_Unification.match
        |> Type_Unification.e_match Unification_Util.match_types),
      normalisers = SOME Unification_Util.beta_eta_short_norms_unif,
      prems_unifier = SOME (Higher_Order_Pattern_Unification.unify
        |> Type_Unification.e_unify Unification_Util.unify_types),
      retrieval = SOME (Args.mk_retrieval_sym_pair (K TI.generalisations |> Args.retrieve_transfer)
        TI.norm_term),
      hint_preprocessor = SOME (K I)}\<close>\<close>
\<close>

ML_file \<open>tests_base.ML\<close>
ML_file \<open>first_order_unification_tests.ML\<close>

end