\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Alternating Zippers\<close>
theory ML_Alternating_Zippers
  imports
    ML_Linked_Zippers
begin

ML\<open>
  val pfx_sfx_nargs = ML_Gen.pfx_sfx_nargs
  val succ_mod_nzippers = ML_Gen.succ_mod_nzippers'
  val pred_mod_nzippers = ML_Gen.pred_mod_nzippers'
\<close>

ML_gen_file\<open>alternating_zipper_morphs.ML\<close>
ML_gen_file\<open>alternating_zipper.ML\<close>
ML_gen_file\<open>sub_alternating_zipper.ML\<close>
ML_gen_file\<open>pair_alternating_zipper.ML\<close>
ML_gen_file\<open>rotate_alternating_zipper.ML\<close>

end