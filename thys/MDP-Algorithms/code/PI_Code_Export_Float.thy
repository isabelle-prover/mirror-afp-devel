theory PI_Code_Export_Float      
  imports 
    PI_Code 
    Code_Real_Approx_By_Float_Fix 
begin               

text \<open>The code generation for Gaussian elimination and pmfs conflicts.\<close>
code_datatype set RBT_set Complement Collect_set Set_Monad DList_set

lemmas List.subset_code(1)[code] List.in_set_member[code]

lemma [code]: "finite (set xs) = True" by auto

lemma set_fold_cfc_code[code]:"
    set_fold_cfc f b (set (xs :: 'c::ccompare list)) =
    (case ID ccompare of None \<Rightarrow> Code.abort STR ''set_fold_cfc RBT_set: ccompare = None'' (\<lambda>_. set_fold_cfc f b (set xs))
     | Some (x :: 'c \<Rightarrow> 'c \<Rightarrow> order) \<Rightarrow> fold (comp_fun_commute_apply f) (remdups xs) b)"
  unfolding set_fold_cfc.rep_eq
  by (auto split: option.splits simp: comp_fun_commute.comp_fun_commute comp_fun_commute_def'
      intro!: comp_fun_commute_on.fold_set_fold_remdups[of "set xs"] Finite_Set.comp_fun_commute_on.intro)

export_code
  d0 to_valid_MDP MDP RBT_Map.update nat_map_from_list assoc_list_to_MDP RBT_Set.empty PI_code 
  nat_pmf_of_list pmf_of_list nat_of_integer Ratreal int_of_integer inverse_divide Tree2.inorder 
  integer_of_nat
  in SML module_name PI_Code_Float file_prefix PI_Code_Float

end
