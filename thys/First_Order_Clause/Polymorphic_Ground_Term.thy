theory Polymorphic_Ground_Term
  imports 
    IsaFoR_Ground_Term
    Generic_Term
begin

datatype ('f, 'tyf) poly_gterm =
  PGFun (fun_sym: 'f) (type_args: "'tyf gterm list") (args: "('f, 'tyf) poly_gterm list")

interpretation poly_gterm: smaller_subterms where
  subterms = args and size = size and is_var = "\<lambda>_. False"
proof unfold_locales
  fix t t' :: "('f, 'tyf) poly_gterm"
  assume "t' \<in> set (poly_gterm.args t)" 
  then show "size t' < size t"
    by (induction t arbitrary: t') (auto simp: elem_size_size_list_size less_SucI trans_less_add2)
qed

interpretation poly_gterm: term_interpretation where
  Fun = PGFun and fun_sym = fun_sym and subterms = args and extra = type_args and is_var = is_var
  by unfold_locales (auto intro: poly_gterm.exhaust)

end
