(*
    Author:      René Thiemann
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Generation for Carrier Matrix Operations\<close>

text \<open>In this theory we implement the infinite carrier set using
  A.\ Lochbihler's container framework \<^cite>\<open>"Containers-AFP"\<close>.\<close>

theory Matrix_Carrier_Impl
imports
  Matrix_IArray_Impl
  Containers.Set_Impl
begin

derive (eq) ceq vec mat
derive (no) ccompare vec mat
derive (dlist) set_impl vec mat
derive (no) cenum vec mat

lemma carrier_mat_code [code]:
  "carrier_mat nr nc = Collect_set (\<lambda> A. dim_row A = nr \<and> dim_col A = nc)"
  by auto

lemma carrier_vec_code [code]:
  "carrier_vec n = Collect_set (\<lambda> v. dim_vec v = n)"
  by auto

end
