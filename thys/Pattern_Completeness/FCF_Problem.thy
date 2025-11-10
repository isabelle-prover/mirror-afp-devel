theory FCF_Problem
  imports Pattern_Completeness_Set
begin

type_synonym('f,'s)simple_match_problem = "('f,nat \<times> 's)term set set" 

definition UNIQ_subst where "UNIQ_subst \<sigma> A = UNIQ (A \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>)" 

lemma UNIQ_subst_pairI: assumes "\<And> s t. s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow> s \<cdot> \<sigma> = t \<cdot> \<sigma>" 
  shows "UNIQ_subst \<sigma> A" unfolding UNIQ_subst_def Uniq_def using assms by blast

lemma UNIQ_subst_trivial[simp]: "UNIQ_subst \<sigma> {t}" "UNIQ_subst \<sigma> {}" 
  by (auto simp: UNIQ_subst_def Uniq_def)

lemma UNIQ_subst_pairD: assumes "UNIQ_subst \<sigma> A" 
  shows "s \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow> s \<cdot> \<sigma> = t \<cdot> \<sigma>" 
  using assms unfolding UNIQ_subst_def Uniq_def by blast

lemma UNIQ_mono: assumes "A \<subseteq> B" 
  shows "UNIQ B \<Longrightarrow> UNIQ A" using assms
  by (simp add: Uniq_def subset_iff)

lemma UNIQ_subst_mono: assumes "A \<subseteq> B"
  shows "UNIQ_subst \<sigma> B \<Longrightarrow> UNIQ_subst \<sigma> A" 
  unfolding UNIQ_subst_def using assms
  by (metis UNIQ_mono image_mono)

lemma UNIQ_subst_alt_def: "UNIQ_subst \<sigma> A = (\<forall> s t. s \<in> A \<longrightarrow> t \<in> A \<longrightarrow> s \<cdot> \<sigma> = t \<cdot> \<sigma>)" 
  unfolding UNIQ_subst_def Uniq_def by auto

definition simple_match_complete_wrt :: "('f,nat \<times> 's,'w)gsubst \<Rightarrow> ('f,'s)simple_match_problem \<Rightarrow> bool" where
  "simple_match_complete_wrt \<sigma> mp = (\<forall> eqc \<in> mp. UNIQ_subst \<sigma> eqc)" 

type_synonym('f,'s)simple_pat_problem = "('f,'s)simple_match_problem set" 

abbreviation tvars_spat :: "('f,'s)simple_pat_problem \<Rightarrow> (nat \<times> 's) set" where
  "tvars_spat spp \<equiv> \<Union> (\<Union> (\<Union> (image (image vars) ` spp)))" 

abbreviation tvars_smp :: "('f,'s)simple_match_problem \<Rightarrow> (nat \<times> 's) set" where
  "tvars_smp smp \<equiv> \<Union> (\<Union> (image vars ` smp))" 

definition simple_pat_complete :: "('f,'s) ssig \<Rightarrow> (nat \<times> 's) set \<Rightarrow> ('f,'s)simple_pat_problem \<Rightarrow> bool" where
  "simple_pat_complete C S pp \<longleftrightarrow> (\<forall>\<sigma> :\<^sub>s \<V> |` S \<rightarrow> \<T>(C). \<exists> mp \<in> pp. simple_match_complete_wrt \<sigma> mp)"

lemma tvars_spat_cong: assumes "\<And> x. x \<in> tvars_spat spp \<Longrightarrow> \<sigma> x = \<delta> x" 
  and "mp \<in> spp" 
shows "simple_match_complete_wrt \<sigma> mp = simple_match_complete_wrt \<delta> mp" 
  unfolding simple_match_complete_wrt_def UNIQ_subst_alt_def
  apply (intro ball_cong refl all_cong1 imp_cong)
  apply (subst (1 2) term_subst_eq[of _ \<sigma> \<delta>])
  using assms by force+


abbreviation set2 :: "'a list list \<Rightarrow> 'a set set" where "set2 \<equiv> image set o set" 
abbreviation set3 :: "'a list list list \<Rightarrow> 'a set set set" where "set3 \<equiv> image set2 o set"

context pattern_completeness_context
begin

definition finite_constructor_form_mp :: "('f,'s)simple_match_problem \<Rightarrow> bool" where
  "finite_constructor_form_mp mp = (\<forall> eqc \<in> mp. eqc \<noteq> {} \<and> (\<exists> \<iota>. finite_sort C \<iota> \<and> (\<forall> t \<in> eqc. t : \<iota> in \<T>(C,\<V> |` SS))))" 

definition "finite_constructor_form_pat p = Ball p finite_constructor_form_mp" 

lemmas finite_constructor_form_defs = finite_constructor_form_pat_def finite_constructor_form_mp_def

definition fcf_solver where 
  "fcf_solver k solver = (\<forall> fcf n. 
    finite_constructor_form_pat (set3 fcf) \<longrightarrow> 
    tvars_spat (set3 fcf) \<subseteq> {..<n} \<times> UNIV \<longrightarrow>
    length fcf < k \<longrightarrow>
      solver n fcf = simple_pat_complete C SS (set3 fcf))" 
end

end