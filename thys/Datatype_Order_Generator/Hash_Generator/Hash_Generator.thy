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
derive (hashcode) hash_code int bool char unit nat

derive hash_code prod sum option list 

datatype ('a,'b)tree = Node 'a 'a 'a "(('a,'b) tree list list) \<times> (('a,'b) tree)" bool | Foo
derive hash_code tree
thm hash_code_list_def
thm partial_hash_code_list_def
thm hash_code_list_simps
thm hash_code_tree_simps[unfolded hash_combine_code]
export_code hash_code_tree in Haskell
end