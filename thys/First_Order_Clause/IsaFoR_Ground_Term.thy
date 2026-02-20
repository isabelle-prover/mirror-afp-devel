theory IsaFoR_Ground_Term
  imports 
    "Regular_Tree_Relations.Ground_Terms"
    Generic_Term
begin

abbreviation (input) is_var where
  "is_var _ \<equiv> False"

interpretation gterm: smaller_subterms where
  subterms = gargs and size = size and is_var = is_var
  by 
    unfold_locales
    (metis add.commute elem_size_size_list_size gterm.exhaust_sel gterm.size(2) trans_less_add2)

interpretation gterm: term_interpretation where
  Fun = "\<lambda>f _. GFun f" and fun_sym = groot_sym and subterms = gargs and extra = "\<lambda>_.()" and
  is_var = is_var and size = size
  by unfold_locales (auto intro: gterm.exhaust)

end
