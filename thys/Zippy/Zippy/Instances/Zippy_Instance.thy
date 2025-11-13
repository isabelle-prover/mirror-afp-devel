\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Instance of Zippy for Proof Search\<close>
theory Zippy_Instance
  imports
    ML_Unification.ML_Costs_Priorities
    Zippy_Actions_Positions
    Zippy_Lists_Goal_Pos_Updates
    Zippy_Lists_Positions_Collect
    Zippy_Tactics
begin

ML_file\<open>zippy_instance_base.ML\<close>
ML_file\<open>zippy_instance.ML\<close>
ML_file\<open>zippy_instance_paction.ML\<close>
ML_file\<open>zippy_instance_presults.ML\<close>
ML_file\<open>zippy_instance_tactic.ML\<close>

end
