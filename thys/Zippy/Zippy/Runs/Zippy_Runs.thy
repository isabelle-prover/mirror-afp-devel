\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Runs\<close>
theory Zippy_Runs
  imports
    Zippy_Action_Applications
    Zippy_Actions
    Zippy_Lists_Goals
    Zippy_Lists_Positions
    Zippy_Runs_Base
    Zippy_Seqs
begin

ML_file\<open>zippy_step_mixin_base.ML\<close>
ML_file\<open>zippy_step_mixin.ML\<close>

ML_file\<open>zippy_run_mixin_base.ML\<close>
ML_file\<open>zippy_run_mixin.ML\<close>

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_run_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
