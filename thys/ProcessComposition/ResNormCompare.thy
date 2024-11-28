theory ResNormCompare
  imports
    ResNormDirect
    ResNormRewrite
begin

section\<open>Comparison of Resource Term Normalisation\<close>

text\<open>The two normalisation procedures have the same outcome, because they both normalise the term\<close>
lemma normal_rewr_is_normal_dir:
  "normal_rewr = normal_dir"
proof
  fix x :: "('a, 'b) res_term"
  show "normal_rewr x = normal_dir x"
    using normal_dir_normalised res_term_equiv_normal_dir
          normal_rewr_normalised res_term_equiv_normal_rewr
    by metis
qed

text\<open>
  With resource term normalisation to decide the equvialence, we can prove that the resource term
  mapping may render terms equivalent.
\<close>
lemma
  fixes a b :: 'a and c :: 'b
  assumes "a \<noteq> b"
  obtains f :: "'a \<Rightarrow> 'b" and x y where "map_res_term f g x \<sim> map_res_term f g y" and "\<not> x \<sim> y"
proof
  show "map_res_term (\<lambda>x. c) g (Res a) \<sim> map_res_term (\<lambda>x. c) g (Res b)"
    by simp
  show "\<not> Res a \<sim> Res b"
    using assms by (simp add: res_term_equiv_is_normal_rewr)
qed

end