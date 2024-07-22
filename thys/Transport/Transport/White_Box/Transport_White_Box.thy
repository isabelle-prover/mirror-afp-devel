\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_White_Box
  imports
    Transport_Equality
    Transport_Existential_Quantifier
    Transport_Galois_Relator_Properties
    Transport_Universal_Quantifier
begin

paragraph \<open>Summary\<close>
text \<open>Theorems for white-box transports.\<close>

context galois
begin
(*TODO: for the Galois relator, many assumptions needed for the white-box transport theorems of the
logical connectives become vacuous. Example:*)

notepad
begin
  print_statement Fun_Rel_imp_eq_restrict_if_right_unique_onI
    [of "in_field (\<le>\<^bsub>L\<^esub>)" "(\<^bsub>L\<^esub>\<lessapprox>)" "in_field (\<le>\<^bsub>R\<^esub>)"]

  have "((\<^bsub>L\<^esub>\<lessapprox>) \<Rrightarrow> (\<longrightarrow>)) (in_field (\<le>\<^bsub>L\<^esub>)) (in_field (\<le>\<^bsub>R\<^esub>))" by (intro Fun_Rel_relI) auto
end

end

end