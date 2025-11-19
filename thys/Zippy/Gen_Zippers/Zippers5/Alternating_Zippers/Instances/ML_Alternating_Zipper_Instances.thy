\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Alternating_Zipper_Instances
  imports
    ML_Alternating_Zipper_Nodes
    ML_Zipper_Instances
begin

ML_gen_file\<open>alternating_local_position_zipper.ML\<close>
ML_gen_file\<open>alternating_global_position_zipper.ML\<close>
ML_gen_file\<open>alternating_depth_zipper.ML\<close>

end
