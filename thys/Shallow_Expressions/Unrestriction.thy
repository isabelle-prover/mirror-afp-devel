section \<open> Unrestriction \<close>

theory Unrestriction
  imports Expressions
begin

text \<open> Unrestriction means that an expression does not depend on the value of the state space
  described by the given scene (i.e. set of variables) for its valuation. It is a semantic
  characterisation of fresh variables. \<close>

consts unrest :: "'s scene \<Rightarrow> 'p \<Rightarrow> bool"

definition unrest_expr :: "'s scene \<Rightarrow> ('b, 's) expr \<Rightarrow> bool" where
[expr_defs]: "unrest_expr a e = (\<forall> s s'. e (s \<oplus>\<^sub>S s' on a) = e s)"

adhoc_overloading unrest \<rightleftharpoons> unrest_expr

syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)

translations
  "_unrest x p" == "CONST unrest x p"                                           

named_theorems unrest

lemma unrest_empty [unrest]: "\<emptyset> \<sharp> P"
  by (simp add: expr_defs lens_defs)

lemma unrest_var_union [unrest]:
  "\<lbrakk> A \<sharp> P; B \<sharp> P \<rbrakk> \<Longrightarrow> A \<union> B \<sharp> P"
  by (simp add: expr_defs lens_defs)
     (metis scene_override_union scene_override_unit scene_union_incompat)

lemma unrest_neg_union:
  assumes "A ##\<^sub>S B" "- A \<sharp> P" "- B \<sharp> P"
  shows "(- (A \<union> B)) \<sharp> P"
  using assms by (simp add: unrest_expr_def scene_override_commute scene_override_union)

text \<open> The following two laws greatly simplify proof when reasoning about unrestricted lens,
  and so we add them to the expression simplification set. \<close>

lemma unrest_lens [expr_simps]:
  "mwb_lens x \<Longrightarrow> ($x \<sharp> e) = (\<forall> s v. e (put\<^bsub>x\<^esub> s v) = e s)"
  by (simp add: unrest_expr_def var_alpha_def comp_mwb_lens lens_override_def)
     (metis mwb_lens.put_put)

lemma unrest_compl_lens [expr_simps]:
  "mwb_lens x \<Longrightarrow> (- $x \<sharp> e) = (\<forall>s s'. e (put\<^bsub>x\<^esub> s' (get\<^bsub>x\<^esub> s)) = e s)"
  by (simp add: unrest_expr_def var_alpha_def comp_mwb_lens lens_override_def scene_override_commute)

lemma unrest_subscene: "\<lbrakk> idem_scene a; a \<sharp> e; b \<subseteq>\<^sub>S a \<rbrakk> \<Longrightarrow> b \<sharp> e"
  by (metis subscene_eliminate unrest_expr_def)

lemma unrest_lens_comp [unrest]: "\<lbrakk> mwb_lens x; mwb_lens y; $x \<sharp> e \<rbrakk> \<Longrightarrow> $x:y \<sharp> e"
  by (simp add: unrest_lens, simp add: lens_comp_def ns_alpha_def)

lemma unrest_expr [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> (e)\<^sub>e"
  by (simp add: expr_defs)

lemma unrest_lit [unrest]: "x \<sharp> (\<guillemotleft>v\<guillemotright>)\<^sub>e"
  by (simp add: expr_defs)

lemma unrest_var [unrest]: 
  "\<lbrakk> vwb_lens x; idem_scene a; var_alpha x \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> a \<sharp> ($x)\<^sub>e"
  by (auto simp add: unrest_expr_def scene_indep_override var_alpha_def)
     (metis lens_override_def lens_override_idem mwb_lens_weak vwb_lens_mwb weak_lens_def)

lemma unrest_var_single [unrest]:
  "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> ($y)\<^sub>e"
  by (simp add: expr_defs lens_indep.lens_put_irr2 lens_indep_sym lens_override_def var_alpha_def)

lemma unrest_sublens:
  assumes "mwb_lens x" "$x \<sharp> P" "y \<subseteq>\<^sub>L x"
  shows "$y \<sharp> P"
  by (metis assms sublens_pres_mwb sublens_put_put unrest_lens)

text \<open> If two lenses are equivalent, and thus they characterise the same state-space regions,
  then clearly unrestrictions over them are equivalent. \<close>
    
lemma unrest_equiv:
  assumes "mwb_lens y" "x \<approx>\<^sub>L y" "$x \<sharp> P"
  shows "$y \<sharp> P"
  using assms lens_equiv_def sublens_pres_mwb unrest_sublens by blast

text \<open> If we can show that an expression is unrestricted on a bijective lens, then is unrestricted
  on the entire state-space. \<close>

lemma bij_lens_unrest_all:
  assumes "bij_lens x" "$x \<sharp> P"
  shows "\<Sigma> \<sharp> P"
  by (metis assms bij_lens_vwb lens_scene_top_iff_bij_lens univ_alpha_def var_alpha_def vwb_lens_iff_mwb_UNIV_src)

lemma bij_lens_unrest_all_eq:
  assumes "bij_lens x"
  shows "(\<Sigma> \<sharp> P) \<longleftrightarrow> ($x \<sharp> P)"
  by (metis assms bij_lens_vwb lens_scene_top_iff_bij_lens univ_alpha_def var_alpha_def vwb_lens_mwb)

text \<open> If an expression is unrestricted by all variables, then it is unrestricted by any variable \<close>

lemma unrest_all_var:
  assumes "\<Sigma> \<sharp> e"
  shows "$x \<sharp> e"
  by (metis assms scene_top_greatest top_idem_scene univ_alpha_def unrest_subscene)

lemma unrest_pair [unrest]:
  assumes "mwb_lens x" "mwb_lens y" "$x \<sharp> P" "$y \<sharp> P"
  shows "$(x, y) \<sharp> P"
  using assms
  by expr_simp (simp add: lens_override_def lens_scene.rep_eq scene_override.rep_eq)

lemma unrest_pair_split:
  assumes "x \<bowtie> y" "vwb_lens x" "vwb_lens y"
  shows "($(x, y) \<sharp> P) = (($x \<sharp> P) \<and> ($y \<sharp> P))"
  using assms
  by (metis lens_equiv_scene lens_indep_sym lens_plus_comm lens_plus_right_sublens plus_vwb_lens sublens_refl unrest_pair unrest_sublens var_alpha_def var_pair_def vwb_lens_def)

lemma unrest_get [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> get\<^bsub>y\<^esub>"
  by (expr_simp, simp add: lens_indep.lens_put_irr2)

lemma unrest_conj [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<and> Q)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_not [unrest]:
  "\<lbrakk> x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> (\<not> P)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_disj [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<or> Q)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_implies [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<longrightarrow> Q)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_expr_if [unrest]:
  assumes "a \<sharp> P" "a \<sharp> Q" "a \<sharp> (e)\<^sub>e"
  shows "a \<sharp> (P \<triangleleft> e \<triangleright> Q)"
  using assms by expr_simp

lemma unrest_uop:
  "\<lbrakk> x \<sharp> e \<rbrakk> \<Longrightarrow> x \<sharp> (\<guillemotleft>f\<guillemotright> e)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_bop:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2 \<rbrakk> \<Longrightarrow> x \<sharp> (\<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2)\<^sub>e"
  by (auto simp add: expr_defs)

lemma unrest_trop:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2; x \<sharp> e\<^sub>3 \<rbrakk> \<Longrightarrow> x \<sharp> (\<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2 e\<^sub>3)\<^sub>e"
  by (auto simp add: expr_defs)

end