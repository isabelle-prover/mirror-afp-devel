\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Prover with Resolution and Simplification\<close>
theory Zippy_Instance_Resolves_Simp
  imports
    Extended_Simp_Data
    Zippy_Instance_Resolve
begin

paragraph \<open>Summary\<close>
text \<open>Basic ingredients for a prover supporting resolution and simplification based on Zippy.\<close>

setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_resolves_simp.ML\<close>
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end