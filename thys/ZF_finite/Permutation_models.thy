(*  Author:     Štěpán Holub, Department of Algebra, Charles University
    Author:     Zuzana Haniková, Institute of Computer Science of the Czech Academy of Sciences
*)

section \<open>Permutation models\<close>
theory Permutation_models
imports ZFfin
begin

text \<open>A useful tool of constructing models with specific properties is the Bernays-Rieger permutation method, 
which redefines the membership relation. We show that a permutation model obtained in this way preserves extensionality, 
empty set, powerset, union, and replacement. The method has been used, inter alia, in several works directly relevant to our formalization 
(\<^cite>\<open>Rieger1957\<close>, \<^cite>\<open>VopenkaHajek1963\<close>, \<^cite>\<open>BaratellaFerro1993\<close>, \<^cite>\<open>ManciniZambella2001\<close>)\<close>

locale permutation_model = L_setext_empty_power_union_repl +
  fixes perm
  assumes 
     bij_perm: "bij (perm :: 'a \<Rightarrow> 'a)" and
     SR_fmem: "SetRelation (\<lambda> x y. x \<epsilon> perm y)"

begin

abbreviation perm_mem  (infixr "\<epsilon>\<^sup>f" 51) where
     "perm_mem x y \<equiv> x \<epsilon> perm y"

sublocale L_setext_empty
  by unfold_locales

interpretation pm: L_setext perm_mem
proof (unfold_locales, rule iffI, blast)
  show "x = y" if "\<forall>z. z \<epsilon>\<^sup>f x = z \<epsilon>\<^sup>f y" for x y
    using that[folded setext[of "perm x" "perm y"]] bij_perm
    by (simp add: bij_betw_def inj_eq) 
qed

lemma SFP_fmem[SFP_rules]: "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> m \<epsilon>\<^sup>f \<Xi> n)"
  by (rule transform_variables[OF SR_fmem[unfolded SetRelation_def], of "id(0:=m,1:=n)", simplified]) 

lemma SR_perm_eq: "SetRelation (\<lambda> x y. perm x = y)"
  unfolding SetRelation_def setext logsimps by (rule SFP_rules)+

lemma permSFP_SFP: assumes "pm.SetFormulaPredicate P" shows "SetFormulaPredicate P" 
proof (rule pm.SetFormulaPredicate.induct[OF assms])
  show "SetFormulaPredicate (\<lambda>\<Xi>. \<Xi> m \<epsilon>\<^sup>f \<Xi> n)" for m n
    using transform_variables[OF SR_fmem[unfolded SetRelation_def], of "id(0:=_,1:=_)"] by simp
qed (simp_all add: SFP_rules) 

lemma perm_model:
  shows "L_setext_empty_power_union_repl perm_mem"
proof
  write pm.subsetM (infix  "\<subseteq>\<^sup>f" 51 ) 
  have finv: "perm ((inv perm) u) = u"  for u
    using bij_perm bij_inv_eq_iff by fast
  have finv': "(inv perm) (perm u) = u"  for u
    using bij_perm bij_inv_eq_iff by metis 
  have inv_iff: "(inv perm) x = y \<longleftrightarrow> perm y = x" for x y
    using bij_perm finv finv' by auto    
  have SR_f': "SetRelation (\<lambda> x y. (inv perm) x = y)"
    using  SR_sym[OF SR_perm_eq, unfolded SR_perm_eq] unfolding inv_iff.  
  have finv_unique: "\<forall>u. \<exists>!v. v = inv perm u"
    using bij_perm by blast
  obtain femp where femp_def: "perm femp  = \<emptyset>"
    using bij_perm bij_pointE by metis 
  show "\<exists>x. \<forall>y. \<not> y \<epsilon>\<^sup>f x"
    using femp_def by (metis empty_is_empty) 
  have fsubset: "x \<subseteq>\<^sup>f y \<longleftrightarrow> (perm x) \<subseteq>\<^sub>M (perm y)" for x y
    unfolding pm.subsetM_def subsetM_def..
  show "\<forall>x. \<exists>y. \<forall>u. u \<epsilon>\<^sup>f y = u \<subseteq>\<^sup>f x"
    unfolding fsubset
  proof
    fix x
    obtain y' where y': "\<And> u. u \<epsilon> y' \<longleftrightarrow> u \<subseteq>\<^sub>M (perm x)"
      using power[rule_format, of "perm x"] by blast
    obtain y where y: "\<And> u. (u \<epsilon> y) = (\<exists>v. v \<epsilon> y' \<and> inv perm v = u)"
      using replf[OF SR_f'[unfolded SetRelation_def], rule_format, of _ y', simplified] by blast 
    have "\<forall>v. (v \<epsilon> perm (inv perm y)) \<longleftrightarrow> perm v \<subseteq>\<^sub>M perm x"
      using y y' bij_perm bij_inv_eq_iff by metis   
    then show "\<exists>y. \<forall>v. (v \<epsilon> perm y) = perm v \<subseteq>\<^sub>M perm x"
      by blast
  qed
  show "\<forall>x. \<exists>y. \<forall>v. v \<epsilon>\<^sup>f y = (\<exists>u. u \<epsilon>\<^sup>f x \<and> v \<epsilon>\<^sup>f u)"
  proof
    fix x
    obtain x' where x': "\<And> u. (u \<epsilon> x') = (\<exists>v. v \<epsilon> perm x \<and>  perm v = u)"
      using replf[OF SR_perm_eq[unfolded SetRelation_def], simplified]  
      using replf[OF SR_f'[unfolded SetRelation_def], rule_format,  simplified] by blast 
    obtain y where y: "\<And> v. v \<epsilon> y \<longleftrightarrow> (\<exists> u. u \<epsilon> x' \<and> v \<epsilon> u)"
      using union[rule_format, of x'] by blast
    have "\<forall>v. (v \<epsilon> perm (inv perm y)) \<longleftrightarrow> (\<exists>u. u \<epsilon> perm x \<and> v \<epsilon> perm u)"
      using  y x' bij_perm finv by auto   
    then show "\<exists>y. \<forall>v. (v \<epsilon> perm y) = (\<exists>u. u \<epsilon> perm x \<and> v \<epsilon> perm u)"
      by blast
  qed
  fix P \<Xi>
  assume "pm.SetFormulaPredicate P" 
  show "(\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))) \<longrightarrow> (\<forall>x. \<exists>z. \<forall>v. v \<epsilon>\<^sup>f z = (\<exists>u. u \<epsilon>\<^sup>f x \<and> P (\<Xi>(0 := u, 1 := v))))"
  proof (rule impI, rule allI)
    assume "\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))"
    fix x
    have "SetFormulaPredicate P"
      by (simp add: \<open>pm.SetFormulaPredicate P\<close> permSFP_SFP) 
    from replf[rule_format, OF this \<open>\<forall>u. \<exists>!v. P (\<Xi>(0 := u, 1 := v))\<close>[rule_format], of "perm x"]
    obtain z where "\<forall>v. (v \<epsilon> z) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v)))"
      by blast
    hence "\<forall>v. (v \<epsilon> perm ((inv perm) z)) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v)))"
      unfolding finv.
    thus "\<exists>z. \<forall>v. (v \<epsilon> perm z) = (\<exists>u. u \<epsilon> perm x \<and> P (\<Xi>(0 := u, 1 := v))) "
      by blast
  qed
qed

end

end
