theory Generator_Aux
imports 
  Main
begin

ML_file "bnf_access.ML"
ML_file "generator_aux.ML"

lemma in_set_simps: 
  "x \<in> set (y # z # ys) = (x = y \<or> x \<in> set (z # ys))"
  "x \<in> set ([y]) = (x = y)"
  "x \<in> set [] = False" 
  "Ball (set []) P = True" 
  "Ball (set [x]) P = P x" 
  "Ball (set (x # y # zs)) P = (P x \<and> Ball (set (y # zs)) P)" 
  by auto
  
lemma conj_weak_cong: "a = b \<Longrightarrow> c = d \<Longrightarrow> (a \<and> c) = (b \<and> d)" by auto

lemma refl_True: "(x = x) = True" by simp

end