\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippers\<close>
theory ML_Zippers
  imports
    ML_Morphs
    ML_Structured_Lenses
begin

ML_gen_file\<open>zipper_morphs.ML\<close>
ML_gen_file\<open>modify_zipper_morphs_zipper.ML\<close>
ML_gen_file\<open>modify_zipper_morphs_container.ML\<close>
ML_gen_file\<open>pair_zipper_morphs.ML\<close>

ML_gen_file\<open>zipper_data.ML\<close>
ML_gen_file\<open>modify_zipper_data_zipper.ML\<close>
ML_gen_file\<open>modify_zipper_data_content.ML\<close>
ML_gen_file\<open>pair_zipper_data.ML\<close>

ML_gen_file\<open>zipper.ML\<close>
ML_gen_file\<open>modify_zipper_zipper.ML\<close>
ML_gen_file\<open>modify_zipper_content.ML\<close>
ML_gen_file\<open>extend_zipper_context.ML\<close>
ML_gen_file\<open>sub_zipper.ML\<close>
ML_gen_file\<open>pair_zipper.ML\<close>

end