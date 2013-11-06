theory Unit_Instantiations
imports Main
begin
  text {* Contains instantiations for the unit type. To be moved to HOL!*}
  
text {* instantiations for unit *}

instantiation unit :: linorder begin
definition [code_unfold]: "less_eq = (\<lambda>_ _ :: unit. True)"
definition [code_unfold]: "less = (\<lambda>_ _ :: unit. False)"

lemma not_less_unit [simp]: "\<not> () < ()" by(simp add: less_unit_def)
lemma le_unit [simp]: "() \<le> ()" by(simp add: less_eq_unit_def)

instance
  apply intro_classes
  apply auto
  done
end

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
