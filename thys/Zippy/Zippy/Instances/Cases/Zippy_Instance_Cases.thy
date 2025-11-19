\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Cases\<close>
theory Zippy_Instance_Cases
  imports
    Zippy_Instance_Hom_Changed_Goals_Data
    Cases_Tactics
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_cases_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
