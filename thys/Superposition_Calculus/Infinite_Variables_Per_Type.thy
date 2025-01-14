theory Infinite_Variables_Per_Type
  imports Fun_Extra Fresh_Identifiers.Fresh
begin

definition infinite_variables_per_type where 
  "infinite_variables_per_type \<V> \<equiv> \<forall>ty. infinite {x. \<V> x = ty}"

lemma exists_infinite_variables_per_type:
  assumes "|UNIV :: 'ty set| \<le>o |UNIV :: ('v :: infinite) set|"
  shows "\<exists>\<V> :: ('v :: infinite \<Rightarrow> 'ty). infinite_variables_per_type \<V>"
  using infinite_domain[OF assms infinite_UNIV]
  unfolding infinite_variables_per_type_def.

end
