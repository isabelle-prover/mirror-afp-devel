subsection \<open> Liberation \<close>

theory Liberation
  imports Extension
begin

text \<open> Liberation~\cite{Dongol19} is an operator that removes dependence on a number of variables.
  It is similar to existential quantification, but is defined over a scene (a variable set). \<close>

subsection \<open> Definition and Syntax \<close>

definition liberate :: "('s \<Rightarrow> bool) \<Rightarrow> 's scene \<Rightarrow> ('s \<Rightarrow> bool)" where
[expr_defs]: "liberate P x = (\<lambda> s. \<exists> s'. P (s \<oplus>\<^sub>S s' on x))"

syntax
  "_liberate" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\\" 80)

translations
  "_liberate P x" == "CONST liberate P x"
  "_liberate P x" <= "_liberate (P)\<^sub>e x"

expr_constructor liberate (0)

subsection \<open> Laws \<close>

lemma liberate_lens [expr_simps]: 
  "mwb_lens x \<Longrightarrow> P \\ $x = (\<lambda>s. \<exists>s'. P (s \<triangleleft>\<^bsub>x\<^esub> s'))"
  by (simp add: liberate_def)

lemma liberate_lens': "mwb_lens x \<Longrightarrow> P \\ $x = (\<lambda>s. \<exists>v. P (put\<^bsub>x\<^esub> s v))"
  by (auto simp add: liberate_def lens_defs fun_eq_iff)
     (metis mwb_lens_weak weak_lens.put_get)

lemma liberate_as_subst: "vwb_lens x \<Longrightarrow> e \\ $x = (\<exists> v. e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sub>e"
  by (expr_simp, metis vwb_lens.put_eq)

lemma unrest_liberate: "a \<sharp> P \\ a"
  by (expr_simp)

lemma unrest_liberate_iff: "(a \<sharp> P) \<longleftrightarrow> (P \\ a = P)"
  by (expr_simp, metis (full_types) scene_override_overshadow_left)

lemma liberate_none [simp]: "P \\ \<emptyset> = P"
  by (expr_simp)

lemma liberate_idem [simp]: "P \\ a \\ a = P \\ a"
  by (expr_simp)

lemma liberate_commute [simp]: "a \<bowtie>\<^sub>S b \<Longrightarrow> P \\ a \\ b = P \\ b \\ a"
  using scene_override_commute_indep by (expr_auto, fastforce+)

lemma liberate_true [simp]: "(True)\<^sub>e \\ a = (True)\<^sub>e"
  by (expr_simp)

lemma liberate_false [simp]: "(False)\<^sub>e \\ a = (False)\<^sub>e"
  by (expr_simp)

lemma liberate_disj [simp]: "(P \<or> Q)\<^sub>e \\ a = (P \\ a \<or> Q \\ a)\<^sub>e"
  by (expr_auto)

end