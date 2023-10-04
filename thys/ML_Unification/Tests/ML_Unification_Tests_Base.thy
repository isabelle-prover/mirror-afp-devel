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
  @{functor_instance struct_name = Test_Unification_Hints
    and functor_name = Term_Index_Unification_Hints
    and id = \<open>"test"\<close>
    and more_args = \<open>
      structure TI = Discrimination_Tree
      val init_args = {
        concl_unifier = SOME Higher_Order_Pattern_Unification.match,
        normalisers = SOME Unification_Util.beta_eta_short_norms_unif,
        prems_unifier = SOME Higher_Order_Pattern_Unification.unify,
        retrieval = SOME (Term_Index_Unification_Hints_Args.mk_sym_retrieval
          TI.norm_term TI.generalisations),
        hint_preprocessor = SOME (K I)
      }\<close>}
\<close>

ML_file \<open>tests_base.ML\<close>
ML_file \<open>first_order_unification_tests.ML\<close>

end