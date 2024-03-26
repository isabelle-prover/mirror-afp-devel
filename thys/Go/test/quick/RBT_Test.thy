theory RBT_Test imports
 "HOL-Data_Structures.RBT_Set"
 "Go.Go_Setup"
begin



definition t1 :: "integer rbt" where
  "t1 = fold insert [1,2,3,4,5] empty"

fun tree_from_list :: "'a::linorder list \<Rightarrow> 'a rbt" where
 "tree_from_list xs = fold insert xs empty"

fun delete_list :: "'a::linorder list \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt" where
  "delete_list xs a = fold del xs a"

fun trees_equal :: "'a::equal rbt \<Rightarrow> 'a rbt \<Rightarrow> bool" where
  "trees_equal a b = (a = b)"

export_code delete_list tree_from_list join invc trees_equal t1 in Go
  module_name RbtTest


export_code delete_list tree_from_list join invc trees_equal t1 checking Go?

end
