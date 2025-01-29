theory Natural_Magma \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports Main
begin

locale natural_magma =
  fixes
    to_set :: "'b \<Rightarrow> 'a set" and
    plus :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and
    wrap :: "'a \<Rightarrow> 'b" and
    add
  defines "\<And>a b. add a b \<equiv> plus (wrap a) b"
  assumes
    to_set_plus [simp]: "\<And>b b'. to_set (plus b b') = (to_set b) \<union> (to_set b')" and
    to_set_wrap [simp]: "\<And>a. to_set (wrap a) = {a}"
begin

lemma to_set_add [simp]: "to_set (add a b) = insert a (to_set b)"
  using to_set_plus to_set_wrap add_def
  by simp

end

locale natural_magma_with_empty = natural_magma +
  fixes empty
  assumes to_set_empty [simp]: "to_set empty = {}"

end
