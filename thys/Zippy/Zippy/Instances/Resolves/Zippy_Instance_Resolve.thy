\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Resolution\<close>
theory Zippy_Instance_Resolve
  imports
    Zippy_Instance_Hom_Changed_Goals_Data
begin

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_uresolve_data.ML\<close>
ML_file\<open>zippy_instance_resolves_data.ML\<close>
ML_file\<open>zippy_instance_uresolves_data.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
