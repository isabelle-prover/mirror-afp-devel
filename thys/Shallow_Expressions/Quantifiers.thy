subsection \<open> Quantifying Lenses \<close>

theory Quantifiers
  imports Liberation
begin

text \<open> We define operators to existentially and universally quantify an expression over a lens. \<close>

subsection \<open> Operators and Syntax \<close>

definition ex_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex_expr x e = (\<lambda> s. (\<exists> v. e (put\<^bsub>x\<^esub> s v)))"

definition ex1_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex1_expr x e = (\<lambda> s. (\<exists>! v. e (put\<^bsub>x\<^esub> s v)))"

definition all_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "all_expr x e = (\<lambda> s. (\<forall> v. e (put\<^bsub>x\<^esub> s v)))"

expr_constructor ex_expr (1)
expr_constructor ex1_expr (1)
expr_constructor all_expr (1)

syntax 
  "_ex_expr"  :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<Zspot> _" [0, 20] 20)
  "_ex1_expr" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists>\<^sub>1 _ \<Zspot> _" [0, 20] 20)
  "_all_expr" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<Zspot> _" [0, 20] 20)

translations
  "_ex_expr x P" == "CONST ex_expr x P"
  "_ex1_expr x P" == "CONST ex1_expr x P"
  "_all_expr x P" == "CONST all_expr x P"

subsection \<open> Laws \<close>

lemma ex_is_liberation: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> P) = (P \\ $x)"
  by (expr_auto, metis mwb_lens_weak weak_lens.put_get)

lemma ex_unrest_iff: "\<lbrakk> mwb_lens x \<rbrakk> \<Longrightarrow> ($x \<sharp> P) \<longleftrightarrow> (\<exists> x \<Zspot> P) = P"
  by (simp add: ex_is_liberation unrest_liberate_iff)

lemma ex_unrest: "\<lbrakk> mwb_lens x; $x \<sharp> P \<rbrakk> \<Longrightarrow> (\<exists> x \<Zspot> P) = P"
  using ex_unrest_iff by blast

lemma unrest_ex_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> $x \<sharp> (\<exists> y \<Zspot> P)"
  by (simp add: ex_expr_def sublens_pres_mwb sublens_put_put unrest_lens)

lemma unrest_ex_out [unrest]:
  "\<lbrakk> mwb_lens x; $x \<sharp> P; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> (\<exists> y \<Zspot> P)"
  by (simp add: ex_expr_def unrest_lens, metis lens_indep.lens_put_comm)

lemma subst_ex_out [usubst]: "\<lbrakk> mwb_lens x; $x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (\<exists> x \<Zspot> P) = (\<exists> x \<Zspot> \<sigma> \<dagger> P)"
  by (expr_simp)

lemma subst_lit_ex_indep [usubst]:
  "y \<bowtie> x \<Longrightarrow> \<sigma>(y \<leadsto> \<guillemotleft>v\<guillemotright>) \<dagger> (\<exists> x \<Zspot> P) = \<sigma> \<dagger> (\<exists> x \<Zspot> [y \<leadsto> \<guillemotleft>v\<guillemotright>] \<dagger> P)"
  by (expr_simp, simp add: lens_indep.lens_put_comm)

lemma subst_ex_in [usubst]:
  "\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<dagger> (\<exists> a \<Zspot> P) = \<sigma> \<dagger> (\<exists> a \<Zspot> P)"
  by (expr_simp, force)

declare lens_plus_right_sublens [simp]

lemma ex_as_subst: "vwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> e) = (\<exists> v. e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sub>e"
  by expr_auto

lemma ex_twice [simp]: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> \<exists> x \<Zspot> P) = (\<exists> x \<Zspot> P)"
  by (expr_simp)

lemma ex_commute: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<Zspot> \<exists> y \<Zspot> P) = (\<exists> y \<Zspot> \<exists> x \<Zspot> P)"
  by (expr_auto, metis lens_indep_comm)+
  
lemma ex_true [simp]: "(\<exists> x \<Zspot> (True)\<^sub>e) = (True)\<^sub>e"
  by expr_simp

lemma ex_false [simp]: "(\<exists> x \<Zspot> (False)\<^sub>e) = (False)\<^sub>e"
  by (expr_simp)

lemma ex_disj [simp]: "(\<exists> x \<Zspot> (P \<or> Q)\<^sub>e) = ((\<exists> x \<Zspot> P) \<or> (\<exists> x \<Zspot> Q))\<^sub>e"
  by (expr_auto)

lemma ex_plus:
  "(\<exists> (y,x) \<Zspot> P) = (\<exists> x \<Zspot> \<exists> y \<Zspot> P)"
  by (expr_auto)

lemma all_as_ex: "(\<forall> x \<Zspot> P) = (\<not> (\<exists> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

lemma ex_as_all: "(\<exists> x \<Zspot> P) = (\<not> (\<forall> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

subsection \<open> Cylindric Algebra \<close>

lemma ex_C1: "(\<exists> x \<Zspot> (False)\<^sub>e) = (False)\<^sub>e"
  by (expr_auto)

lemma ex_C2: "wb_lens x \<Longrightarrow> `P \<longrightarrow> (\<exists> x \<Zspot> P)`"
  by (expr_simp, metis wb_lens.get_put)

lemma ex_C3: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> (P \<and> (\<exists> x \<Zspot> Q)))\<^sub>e = ((\<exists> x \<Zspot> P) \<and> (\<exists> x \<Zspot> Q))\<^sub>e"
  by (expr_auto)

lemma ex_C4a: "x \<approx>\<^sub>L y \<Longrightarrow> (\<exists> x \<Zspot> \<exists> y \<Zspot> P) = (\<exists> y \<Zspot> \<exists> x \<Zspot> P)"
  by (expr_simp, metis (mono_tags, lifting) lens.select_convs(2))

lemma ex_C4b: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<Zspot> \<exists> y \<Zspot> P) = (\<exists> y \<Zspot> \<exists> x \<Zspot> P)"
  using ex_commute by blast

lemma ex_C5:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "($x = $x)\<^sub>e = (True)\<^sub>e"
  by simp

lemma ex_C6:
  assumes "wb_lens x" "x \<bowtie> y" "x \<bowtie> z"
  shows "($y = $z)\<^sub>e = (\<exists> x \<Zspot> $y = $x \<and> $x = $z)\<^sub>e"
  using assms
  by (expr_simp, metis lens_indep_def)

lemma ex_C7:
  assumes "weak_lens x" "x \<bowtie> y"
  shows "((\<exists> x \<Zspot> $x = $y \<and> P) \<and> (\<exists> x \<Zspot> $x = $y \<and> \<not> P))\<^sub>e = (False)\<^sub>e"
  using assms by (expr_simp, simp add: lens_indep_sym)

end
