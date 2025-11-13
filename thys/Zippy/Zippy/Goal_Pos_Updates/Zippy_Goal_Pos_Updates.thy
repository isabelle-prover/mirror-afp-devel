\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Goal_Pos_Updates
  imports
    Generic_Table_Data
    Zippy_Actions
    Zippy_Action_Clusters
    Zippy_Goal_Pos_Updates_Base
    Zippy_Goals
begin

ML_file\<open>zippy_goals_pos_mixin_base.ML\<close>
ML_file\<open>zippy_goals_pos_mixin.ML\<close>

(*ground polymorphic types since only ground types can be stored in the generic context.*)
setup\<open>Context.theory_map ML_Gen.ground_zipper_types\<close>
ML_file\<open>zippy_update_goal_cluster_mixin_base.ML\<close>
ML_file\<open>zippy_update_goal_cluster_mixin.ML\<close>
(*reset grounding*)
setup\<open>Context.theory_map ML_Gen.reset_zipper_types\<close>

ML_file\<open>zippy_goals_pos_copy_mixin_base.ML\<close>
ML_file\<open>zippy_goals_pos_copy_mixin.ML\<close>

end
