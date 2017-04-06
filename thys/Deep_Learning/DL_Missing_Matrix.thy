(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Matrix\<close>

theory DL_Missing_Matrix
imports "../Jordan_Normal_Form/Matrix"
begin

lemma dim_vec_of_list[simp] :"dim\<^sub>v (vec_of_list as) = length as" by transfer auto

lemma list_vec: "list_of_vec (vec_of_list xs) = xs"
by (transfer, metis (mono_tags, lifting) atLeastLessThan_iff map_eq_conv map_nth mk_vec_def old.prod.case set_upt)

lemma vec_list: "vec_of_list (list_of_vec v) = v"
apply transfer unfolding mk_vec_def by auto

lemma index_vec_of_list: "i<length xs \<Longrightarrow> (vec_of_list xs) $ i = xs ! i"
by (metis vec.abs_eq vec_index_vec vec_of_list.abs_eq)

lemma nth_list_of_vec: "i<dim\<^sub>v v \<Longrightarrow> (list_of_vec v) ! i = v $ i"
by (metis dim_vec_of_list index_vec_of_list vec_list)

lemma vec_of_list_index: "vec_of_list xs $ j = xs ! j"
  apply transfer unfolding mk_vec_def unfolding undef_vec_def
  by (simp, metis append_Nil2 nth_append)

lemma list_of_vec_index: "list_of_vec v ! j = v $ j"
  by (metis vec_list vec_of_list_index)
    
lemma list_of_vec_map: "list_of_vec xs = map (op $ xs) [0..<dim\<^sub>v xs]" by transfer auto

definition "component_mult v w = vec (min (dim\<^sub>v v) (dim\<^sub>v w)) (\<lambda>i. v $ i * w $ i)"
definition vec_set::"'a vec \<Rightarrow> 'a set" ("set\<^sub>v")
  where "vec_set v = vec_index v ` {..<dim\<^sub>v v}"

lemma index_component_mult:
assumes "i < dim\<^sub>v v" "i < dim\<^sub>v w"
shows "component_mult v w $ i = v $ i * w $ i"
  unfolding component_mult_def using assms vec_index_vec by auto

lemma dim_component_mult:
"dim\<^sub>v (component_mult v w) = min (dim\<^sub>v v) (dim\<^sub>v w)"
  unfolding component_mult_def using vec_index_vec by auto

lemma vec_setE:
assumes "a \<in> set\<^sub>v v"
obtains i where "v$i = a" "i<dim\<^sub>v v" using assms unfolding vec_set_def by blast

lemma vec_setI:
assumes "v$i = a" "i<dim\<^sub>v v"
shows "a \<in> set\<^sub>v v" using assms unfolding vec_set_def using image_eqI lessThan_iff by blast

lemma set_list_of_vec:
"set (list_of_vec v) = set\<^sub>v v" unfolding vec_set_def by transfer auto

lemma length_list_of_vec[simp] :"length (list_of_vec v) = dim\<^sub>v v" by transfer auto

end
