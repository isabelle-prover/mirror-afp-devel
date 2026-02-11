theory Polymorphic_Ground_Context
  imports
    Abstract_Context
    Polymorphic_Ground_Term
begin

interpretation poly_gcontext: abstract_context where 
  Fun = PGFun and fun_sym = fun_sym and subterms = args and extra = type_args and 
  is_var = is_var and size = size
  by unfold_locales

end
