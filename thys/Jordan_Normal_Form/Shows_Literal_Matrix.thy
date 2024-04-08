(*  
    Author:      René Thiemann 
    License:     BSD
*)
theory Shows_Literal_Matrix
  imports 
    Jordan_Normal_Form.Matrix
    Show.Shows_Literal
begin

subsection \<open>For the @{class showl}-class\<close>

instantiation Matrix.vec :: (showl)showl begin
definition showsl_vec :: "'a Matrix.vec \<Rightarrow> showsl" where
  "showsl_vec v \<equiv> showsl_list (list_of_vec v)"
definition "showsl_list (xs :: 'a Matrix.vec list) = default_showsl_list showsl xs"
instance ..
end

instantiation mat :: (showl)showl begin
definition showsl_mat :: "'a Matrix.mat \<Rightarrow> showsl" where
  "showsl_mat a \<equiv> default_showsl_list id (map showsl_list (mat_to_list a))"
definition "showsl_list (xs :: 'a Matrix.mat list) = default_showsl_list showsl xs"
instance ..
end

value "showsl (one_mat 3 :: nat mat) (STR '' is the identity matrix of dimension 3'')" 

end
