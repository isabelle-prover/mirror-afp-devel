\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Implies
  imports
    Function_Relators
    Reverse_Implies
begin

lemma Fun_Rel_iff_imp_imp: "((\<longleftrightarrow>) \<Rrightarrow> (\<longleftrightarrow>) \<Rrightarrow> (\<longleftrightarrow>)) (\<longrightarrow>) (\<longrightarrow>)"
  by auto

lemma Fun_Rel_imp_imp_imp: "((\<longleftarrow>) \<Rrightarrow> (\<longrightarrow>) \<Rrightarrow> (\<longrightarrow>)) (\<longrightarrow>) (\<longrightarrow>)"
  by auto

lemma Fun_Rel_rev_imp_imp_imp: "((\<longrightarrow>) \<Rrightarrow> (\<longleftarrow>) \<Rrightarrow> (\<longleftarrow>)) (\<longrightarrow>) (\<longrightarrow>)"
  by auto

lemma Fun_Rel_iff_rev_imp_rev_imp: "((\<longleftrightarrow>) \<Rrightarrow> (\<longleftrightarrow>) \<Rrightarrow> (\<longleftrightarrow>)) (\<longleftarrow>) (\<longleftarrow>)"
  by auto

lemma Fun_Rel_imp_rev_imp_rev_imp: "((\<longrightarrow>) \<Rrightarrow> (\<longleftarrow>) \<Rrightarrow> (\<longrightarrow>)) (\<longleftarrow>) (\<longleftarrow>)"
  by force

lemma Fun_Rel_rev_imp_rev_imp_rev_imp: "((\<longleftarrow>) \<Rrightarrow> (\<longrightarrow>) \<Rrightarrow> (\<longleftarrow>)) (\<longleftarrow>) (\<longleftarrow>)"
  by force

end