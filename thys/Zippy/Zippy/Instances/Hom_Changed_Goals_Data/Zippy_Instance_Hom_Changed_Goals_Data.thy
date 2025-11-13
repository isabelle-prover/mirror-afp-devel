\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Homogenously Changed Goals Data\<close>
theory Zippy_Instance_Hom_Changed_Goals_Data
  imports
    Generic_Term_Index_Data
    Zippy_Instance
begin

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_instance_hom_changed_goals_data.ML\<close>
(*reset grounding*)
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

end
