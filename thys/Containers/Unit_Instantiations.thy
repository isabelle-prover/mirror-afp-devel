theory Unit_Instantiations
imports Main
begin
  text {* Contains instantiations for the unit type. To be moved to HOL!*}
  
text {* instantiations for unit *}

declare
  less_eq_unit_def [abs_def, code_unfold]
  less_unit_def [abs_def, code_unfold]

instantiation unit :: "wellorder" begin
instance by intro_classes auto
end

instantiation unit :: "complete_boolean_algebra" begin

definition "top = ()"
definition "bot = ()"
definition [code_unfold]: "sup _ _ = ()"
definition [code_unfold]: "inf _ _ = ()"
definition "Sup _ = ()"
definition "Inf _ = ()"
definition [simp, code_unfold]: "uminus = (\<lambda>_ :: unit. ())"

instance by intro_classes simp_all
end

instantiation unit :: "complete_linorder" begin
  instance by intro_classes simp_all
end

end
