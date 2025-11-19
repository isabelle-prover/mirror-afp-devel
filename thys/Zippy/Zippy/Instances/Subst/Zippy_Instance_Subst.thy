\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Substitution\<close>
theory Zippy_Instance_Subst
  imports
    Zippy_Instance_Hom_Changed_Goals_Data
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_subst_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
