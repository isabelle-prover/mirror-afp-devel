\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Induction\<close>
theory Zippy_Instance_Induction
  imports
    Zippy_Instance_Hom_Changed_Goals_Data
    Induction_Tactics
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_induction_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
