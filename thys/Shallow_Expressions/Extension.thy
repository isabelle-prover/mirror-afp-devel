section \<open> Extension and Restriction \<close>

theory Extension
  imports Substitutions
begin

text \<open> It is often necessary to coerce an expression into a different state space using a lens,
  for example when the state space grows to add additional variables. Extension and restriction
  is provided by @{term aext} and @{term ares} respectively. Here, we provide syntax translations
  and reasoning support for these.
\<close>

subsection \<open> Syntax \<close>

syntax 
  "_aext"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>" 80)
  "_ares"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>" 80)
  "_pre"       :: "logic \<Rightarrow> logic" ("_\<^sup><" [999] 1000)
  "_post"      :: "logic \<Rightarrow> logic" ("_\<^sup>>" [999] 1000)
  "_drop_pre"  :: "logic \<Rightarrow> logic" ("_\<^sub><" [999] 1000)
  "_drop_post" :: "logic \<Rightarrow> logic" ("_\<^sub>>" [999] 1000)

translations
  "_aext P a" == "CONST aext P a"
  "_ares P a" == "CONST ares P a"
  "_pre P" == "_aext (P)\<^sub>e fst\<^sub>L"
  "_post P" == "_aext (P)\<^sub>e snd\<^sub>L"
  "_drop_pre P" == "_ares (P)\<^sub>e fst\<^sub>L"
  "_drop_post P" == "_ares (P)\<^sub>e snd\<^sub>L"

expr_constructor aext
expr_constructor ares

named_theorems alpha

subsection \<open> Laws \<close>

lemma aext_var [alpha]: "($x)\<^sub>e \<up> a = ($a:x)\<^sub>e"
  by (simp add: expr_defs lens_defs)

lemma ares_aext [alpha]: "weak_lens a \<Longrightarrow> P \<up> a \<down> a = P"
  by (simp add: expr_defs)

lemma aext_ares [alpha]: "\<lbrakk> mwb_lens a; (- $a) \<sharp> P \<rbrakk> \<Longrightarrow> P \<down> a \<up> a = P"
  unfolding unrest_compl_lens
  by (auto simp add: expr_defs fun_eq_iff lens_create_def)

lemma expr_pre [simp]: "e\<^sup>< (s\<^sub>1, s\<^sub>2) = (e)\<^sub>e s\<^sub>1"
  by (simp add: subst_ext_def subst_app_def)

lemma expr_post [simp]: "e\<^sup>> (s\<^sub>1, s\<^sub>2) = (@e)\<^sub>e s\<^sub>2"
  by (simp add: subst_ext_def subst_app_def)

lemma unrest_aext_expr_lens [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> a \<rbrakk> \<Longrightarrow> $x \<sharp> (P \<up> a)"
  by (expr_simp add: lens_indep.lens_put_irr2)

lemma unrest_init_pre [unrest]: "\<lbrakk> mwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> $x\<^sup>< \<sharp> e\<^sup><"
  by expr_auto

lemma unrest_init_post [unrest]: "mwb_lens x \<Longrightarrow> $x\<^sup>< \<sharp> e\<^sup>>"
  by expr_auto

lemma unrest_fin_pre [unrest]: "mwb_lens x \<Longrightarrow> $x\<^sup>> \<sharp> e\<^sup><"
  by expr_auto

lemma unrest_fin_post [unrest]: "\<lbrakk> mwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> $x\<^sup>> \<sharp> e\<^sup>>"
  by expr_auto

lemma aext_get_fst [usubst]: "aext (get\<^bsub>x\<^esub>) fst\<^sub>L = get\<^bsub>ns_alpha fst\<^sub>L x\<^esub>"
  by expr_simp

lemma aext_get_snd [usubst]: "aext (get\<^bsub>x\<^esub>) snd\<^sub>L = get\<^bsub>ns_alpha snd\<^sub>L x\<^esub>"
  by expr_simp

subsection \<open> Substitutions \<close>

definition subst_aext :: "'a subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'b subst"
  where [expr_defs]: "subst_aext \<sigma> x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

definition subst_ares :: "'b subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'a subst"
  where [expr_defs]: "subst_ares \<sigma> x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

syntax 
  "_subst_aext" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>\<^sub>s" 80)
  "_subst_ares" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>\<^sub>s" 80)

translations
  "_subst_aext P a" == "CONST subst_aext P a"
  "_subst_ares P a" == "CONST subst_ares P a"

lemma unrest_subst_aext [unrest]: "x \<bowtie> a \<Longrightarrow> $x \<sharp>\<^sub>s (\<sigma> \<up>\<^sub>s a)"
  by (expr_simp)
     (metis lens_indep_def lens_override_def lens_scene.rep_eq scene_override.rep_eq)

lemma subst_id_ext [usubst]:
  "vwb_lens x \<Longrightarrow> [\<leadsto>] \<up>\<^sub>s x = [\<leadsto>]"
  by expr_auto

lemma upd_subst_ext [alpha]:
  "vwb_lens x \<Longrightarrow> \<sigma>(y \<leadsto> e) \<up>\<^sub>s x = (\<sigma> \<up>\<^sub>s x)(x:y \<leadsto> e \<up> x)"
  by expr_auto

lemma apply_subst_ext [alpha]:
  "vwb_lens x \<Longrightarrow> (\<sigma> \<dagger> e) \<up> x = (\<sigma> \<up>\<^sub>s x) \<dagger> (e \<up> x)"
  by (expr_auto)

lemma subst_aext_compose [alpha]: "(\<sigma> \<up>\<^sub>s x) \<up>\<^sub>s y = \<sigma> \<up>\<^sub>s y:x"
  by (expr_simp)

lemma subst_aext_comp [usubst]:
  "vwb_lens a \<Longrightarrow> (\<sigma> \<up>\<^sub>s a) \<circ>\<^sub>s (\<rho> \<up>\<^sub>s a) = (\<sigma> \<circ>\<^sub>s \<rho>) \<up>\<^sub>s a"
  by expr_auto

lemma subst_id_res: "mwb_lens a \<Longrightarrow> [\<leadsto>] \<down>\<^sub>s a = [\<leadsto>]"
  by expr_auto

lemma upd_subst_res_in: 
  "\<lbrakk> mwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<down>\<^sub>s a = (\<sigma> \<down>\<^sub>s a)(x \<restriction> a \<leadsto> e \<down> a)"
  by (expr_simp, fastforce)

lemma upd_subst_res_out: 
  "\<lbrakk> mwb_lens a; x \<bowtie> a \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<down>\<^sub>s a = \<sigma> \<down>\<^sub>s a"
  by (simp add: expr_defs lens_indep_sym)

lemma subst_ext_lens_apply: "\<lbrakk> mwb_lens a; -$a \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> (a\<^sup>\<up> \<circ>\<^sub>s \<sigma>) \<dagger> P = ((\<sigma> \<down>\<^sub>s a) \<dagger> P) \<up> a"
  by (expr_simp, simp add: lens_override_def scene_override_commute)

end
