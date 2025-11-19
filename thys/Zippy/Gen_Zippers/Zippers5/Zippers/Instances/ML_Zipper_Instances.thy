\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_Zipper_Instances
  imports
    ML_Zippers
    ML_Zipper_Directions
    ML_Zipper_Positions
    ML_Lists
begin

ML_gen_file\<open>content_zipper.ML\<close>
ML_gen_file\<open>direction_zipper.ML\<close>
ML_gen_file\<open>position_zipper.ML\<close>

ML_gen_file\<open>list_zipper.ML\<close>
ML_gen_file\<open>rose_zipper.ML\<close>

end
