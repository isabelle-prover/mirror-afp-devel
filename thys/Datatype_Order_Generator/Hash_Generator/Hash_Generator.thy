section \<open>Generating Hash-Functions\<close>

theory Hash_Generator
imports
  "../Generator_Aux"
  "../Derive_Manager"
  "../../Collections/Lib/HashCode"
begin

fun hash_combine :: "hashcode list \<Rightarrow> hashcode list \<Rightarrow> hashcode" where
  "hash_combine [] [x] = x"
| "hash_combine (y # ys) (z # zs) = y * z + hash_combine ys zs"
| "hash_combine _ _ = 0"

subsection \<open>improved code for non-lazy languages\<close>

lemma hash_combine_code [code_unfold]: 
  "hash_combine [] [x] = x"
  "hash_combine (y # ys) (z # zs) = y * z + hash_combine ys zs" 
  by auto

subsection \<open>The Generator\<close>

ML_file "hash_generator.ML"

end