theory Fofu_Impl_Base
imports 
  "../Refine_Imperative_HOL/IICF/IICF"
  "../Refine_Imperative_HOL/Sepref_ICF_Bindings"
  "~~/src/HOL/Library/Rewrite"
  Refine_Monadic_Syntax_Sugar
begin
  hide_type (open) List_Seg.node

  interpretation Refine_Monadic_Syntax .


end
