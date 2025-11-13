\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Alternating_Zipper_Paths
  imports
    ML_Alternating_Zipper_Instances
    ML_Zipper_Position_Utils
begin

ML_gen_file\<open>alternating_zipper_path.ML\<close>
ML_gen_file\<open>alternating_zipper_path_util.ML\<close>
ML_gen_file\<open>alternating_zipper_path_local_position_zipper.ML\<close>

end