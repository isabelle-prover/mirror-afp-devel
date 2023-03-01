theory PI_Code_Export_Rat
  imports 
    PI_Code
begin

code_datatype set RBT_set Complement Collect_set Set_Monad DList_set

lemmas List.subset_code(1)[code] List.in_set_member[code]

lemma finite_set_code[code]: "finite (set xs) = True" by auto

lemma set_fold_cfc_code[code]:"
    set_fold_cfc f b (set (xs :: 'c::ccompare list)) =
    (case ID ccompare of None \<Rightarrow> Code.abort STR ''set_fold_cfc RBT_set: ccompare = None'' (\<lambda>_. set_fold_cfc f b (set xs))
     | Some (x :: 'c \<Rightarrow> 'c \<Rightarrow> order) \<Rightarrow> fold (comp_fun_commute_apply f) (remdups xs) b)"
  unfolding set_fold_cfc.rep_eq
  by (auto split: option.splits simp: comp_fun_commute.comp_fun_commute comp_fun_commute_def'
      intro!: comp_fun_commute_on.fold_set_fold_remdups[of "set xs"] Finite_Set.comp_fun_commute_on.intro)

export_code
  ord_real_inst.less_eq_real quotient_of
  plus_real_inst.plus_real minus_real_inst.minus_real d0 to_valid_MDP MDP RBT_Map.update 
  Rat.of_int divide divide_rat_inst.divide_rat divide_real_inst.divide_real nat_map_from_list 
  assoc_list_to_MDP nat_pmf_of_list RBT_Set.empty PI_code pmf_of_list nat_of_integer 
  Ratreal int_of_integer inverse_divide Tree2.inorder integer_of_nat 
  in SML module_name PI_Code_Rat file_prefix PI_Code_Rat

end