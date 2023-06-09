section \<open>Properties of Power Allegories\<close>

theory Power_Allegories_Properties

imports Relational_Properties

begin

subsection \<open>Power transpose, epsilon, epsiloff\<close>

definition Lambda :: "('a,'b) rel \<Rightarrow> ('a,'b set) rel" ("\<Lambda>") where
  "\<Lambda> R = {(a,B) |a B. B = {b. (a,b) \<in> R}}"

definition epsilon :: "('a,'a set) rel" where
  "epsilon = {(a,A). a \<in> A}"

definition "epsiloff = {(A,a). a \<in> A}"

definition alpha :: "('a,'b set) rel \<Rightarrow> ('a,'b) rel" ("\<alpha>") where
  "\<alpha> R = R ; epsiloff"

text \<open>alpha can be seen as a relational approximation of a multirelation.
The next lemma provides a relational definition of Lambda.\<close>

lemma Lambda_syq: "\<Lambda> R = R\<^sup>\<smile> \<div> epsilon"
  unfolding Lambda_def syq_set epsilon_def by blast

lemma epsiloff_epsilon: "epsiloff = epsilon\<^sup>\<smile>"
  unfolding epsiloff_def epsilon_def converse_unfold by simp

lemma alpha_set: "\<alpha> R = {(a,b) |a b. b \<in> \<Union>{B. (a,B) \<in> R}}"
  unfolding alpha_def epsiloff_def by force

lemma alpha_relcomp [simp]: "\<alpha> (R ; S) = R ; \<alpha> S"
  by (simp add: O_assoc alpha_def)

lemma Lambda_epsiloff_up1: "f = \<Lambda> R \<Longrightarrow> R = \<alpha> f"
  unfolding Lambda_def alpha_set by simp

lemma Lambda_epsiloff_up2: "deterministic f \<Longrightarrow> R = \<alpha> f \<Longrightarrow> f = \<Lambda> R"
  unfolding Lambda_def alpha_set deterministic_set
  apply safe
  apply force
  by (clarsimp, smt (verit, best) mem_Collect_eq set_eq_iff)

lemma Lambda_epsiloff_up:
  assumes "deterministic f"
  shows "(R = \<alpha> f) = (f = \<Lambda> R)"
  by (meson Lambda_epsiloff_up1 Lambda_epsiloff_up2 assms)

lemma det_lambda: "deterministic (\<Lambda> R)"
  unfolding Lambda_def deterministic_set by simp

lemma Lambda_alpha_canc: "deterministic f \<Longrightarrow> \<Lambda> (\<alpha> f) = f"
  using Lambda_epsiloff_up2 by blast

lemma alpha_Lambda_canc [simp]: "\<alpha> (\<Lambda> R) = R"
  using Lambda_epsiloff_up1 by blast

lemma alpha_cancel:
  assumes "deterministic f"
  and "deterministic g"
  shows "\<alpha> f = \<alpha> g \<Longrightarrow> f = g"
  by (metis Lambda_epsiloff_up2 assms)

lemma Lambda_fusion:
  assumes "deterministic f"
  shows "\<Lambda> (f ; R) = f ; \<Lambda> R"
proof -
  have h: "deterministic (f ; \<Lambda> R)"
    by (simp add: assms det_lambda det_relcomp)
  have "f ; R = \<alpha> (f ; \<Lambda> R)"
    by simp
  also have "\<dots> = f ; \<alpha> (\<Lambda> R)"
    by simp
  thus ?thesis
    by (simp add: alpha_cancel det_lambda h)
qed

lemma Lambda_fusion_var: "\<Lambda> (\<Lambda> R ; S) = \<Lambda> R ; \<Lambda> S"
  by (simp add: Lambda_fusion det_lambda)

lemma Lambda_epsiloff [simp]: "\<Lambda> epsiloff = Id"
proof -
  have "\<Lambda> epsiloff = \<Lambda> (Id ; epsiloff)"
    by simp
  also have "\<dots> = Id"
    by (metis Lambda_epsiloff_up alpha_def det_Id)
  finally show ?thesis.
qed

lemma alpha_epsiloff [simp]: "\<alpha> Id = epsiloff"
  by (simp add: alpha_def)

lemma alpha_Sup_pres: "\<alpha> (\<Union>\<R>) = (\<Union>R \<in> \<R>. \<alpha> R)"
  unfolding alpha_def by force

lemma alpha_ord_pres: "R \<subseteq> S \<Longrightarrow> alpha R \<subseteq> alpha S"
  unfolding alpha_def by force

lemma alpha_inf_pres: "\<alpha> {(a,A). \<exists>B C. A = B \<inter> C \<and> (a,B) \<in> R \<and> (a,C) \<in> S} = \<alpha> R \<inter> \<alpha> S"
  unfolding alpha_set by blast


subsection \<open>Relational image functor\<close>

definition pow :: "('a, 'b) rel \<Rightarrow> ('a set, 'b set) rel" ("\<P>") where
  "\<P> R = \<Lambda> (epsiloff ; R)"

lemma pow_set: "\<P> R = {(A,B). B = Image R A}"
  unfolding pow_def epsiloff_def Lambda_def relcomp_def Image_def by force

lemma pow_set_var: "\<P> R = {(A,B). B = {b. \<exists>a \<in> A. (a,b) \<in> R}}"
  unfolding pow_set Image_def by simp

lemma pow_converse_set: "\<P> (R\<^sup>\<smile>) = {(Q,P). P = {a. \<exists>b. (a,b) \<in> R \<and> b \<in> Q}}"
  unfolding pow_set Image_def by force

lemma det_pow: "deterministic (\<P> R)"
  unfolding pow_set deterministic_set Image_def by simp

lemma Lambda_pow: "\<Lambda> (R ; S) = \<Lambda> R ; \<P> S"
proof -
  have "\<Lambda> R ; \<P> S = \<Lambda> R ; \<Lambda> (epsiloff ; S)"
    by (simp add: pow_def)
  also have "\<dots> = \<Lambda> (\<Lambda> R ; epsiloff ; S)"
    by (simp add: Lambda_fusion_var O_assoc)
  also have "\<dots> = \<Lambda> (R ; S)"
    by (metis alpha_Lambda_canc alpha_def)
  finally show ?thesis..
qed

lemma pow_func1 [simp]: "\<P> Id = Id"
  by (simp add: pow_def)

lemma pow_func2: "\<P> (R ; S) = \<P> R ; \<P> S"
  by (metis Lambda_pow pow_def O_assoc)

lemma Grph_Image [simp]: "Grph \<circ> Image = \<P>"
  apply (simp add: fun_eq_iff)
  unfolding pow_def Grph_def Image_def Lambda_def epsiloff_def by blast

lemma lambda_alpha_idem [simp]: "\<Lambda> (\<alpha> (\<Lambda> (\<alpha> R))) = \<Lambda> (\<alpha> R)"
  by simp


subsection \<open>Unit and multiplication of powerset monad\<close>

definition eta :: "('a,'a set) rel" ("\<eta>") where
  "\<eta> = \<Lambda> Id"

definition mu :: "('a set set, 'a set) rel" ("\<mu>") where
  "\<mu> = pow epsiloff"

lemma eta_set: "\<eta> = {(a,{a}) |a. True}"
  unfolding eta_def Lambda_def Id_def by simp

lemma alpha_eta [simp]: "\<alpha> \<eta> = Id"
  by (simp add: eta_def)

lemma det_eta: "deterministic \<eta>"
  unfolding deterministic_set eta_set by simp

lemma mu_set: "\<mu> = {(A,B). B = {b. \<exists>C. C \<in> A \<and> b \<in> C}}"
  unfolding mu_def pow_def Lambda_def epsiloff_def by force

lemma det_mu: "deterministic \<mu>"
  unfolding deterministic_set mu_set by simp

lemma Lambda_eta:
  assumes "deterministic R"
  shows "\<Lambda> R = R ; \<eta>"
proof -
  have "\<Lambda> R = \<Lambda> (R ; Id)"
    by simp
  also have "\<dots> = R ; \<Lambda> Id"
    using Lambda_fusion assms by blast
  also have "\<dots> = R ; \<eta>"
    by (simp add: eta_def)
  finally show ?thesis.
qed

lemma eta_nat_trans:
  assumes "deterministic R"
  shows "\<eta> ; \<P> R = R ; \<eta>"
proof -
  have "\<eta> ; \<P> R = \<Lambda> Id ; \<P> R"
    by (simp add: eta_def)
  also have "\<dots> = \<Lambda> (Id ; R)"
    using Lambda_pow by blast
  also have "\<dots> = \<Lambda> R"
    by simp
  also have "\<dots> = R ; \<eta>"
    by (simp add: Lambda_eta assms)
  finally show ?thesis.
qed

lemma mu_nat_trans:
  assumes "deterministic R"
  shows "\<P> (\<P> R) ; \<mu> = \<mu> ; \<P> R"
  by (metis pow_def alpha_Lambda_canc alpha_def mu_def pow_func2)

text \<open>The standard axioms for the powerset monad are derivable.\<close>

lemma pow_monad1 [simp]: "\<P> \<mu> ; \<mu> = \<mu> ; \<mu>"
  by (metis pow_def alpha_Lambda_canc alpha_def mu_def pow_func2)

lemma pow_monad2 [simp]: "\<P> \<eta> ; \<mu> = Id"
  by (metis alpha_Lambda_canc alpha_def eta_def mu_def pow_func1 pow_func2)

lemma pow_monad3 [simp]: "\<eta> ; \<mu> = Id"
  by (metis Lambda_epsiloff Lambda_pow alpha_def alpha_epsiloff eta_def mu_def)

lemma Lambda_mu:
  assumes "deterministic R"
  shows "\<Lambda>(R) ; \<mu> = R"
proof -
  have "\<Lambda> R ; \<mu> = R ; \<eta> ; \<mu>"
    by (simp add: Lambda_eta assms)
  also have "\<dots> = R"
    by (simp add: O_assoc)
  finally show ?thesis.
qed

lemma pow_Lambda_mu [simp]: "\<P> (\<Lambda> R) ; \<mu> = \<P> R"
  by (metis alpha_Lambda_canc alpha_def mu_def pow_func2)

lemma lambda_alpha_mu: "\<Lambda> (\<alpha> R) = \<Lambda> R ; \<mu>"
  by (simp add: Lambda_pow alpha_def mu_def)

lemma alpha_eta_pow [simp]: "\<alpha> (\<eta> ; \<P> R) = R"
proof -
  have "\<alpha> (\<eta> ; \<P> R) = \<alpha> (\<Lambda> Id ; \<P> R)"
    by (simp add: eta_def)
  also have "\<dots> = \<alpha> (\<Lambda> (Id ; R))"
    by (metis Lambda_pow)
  also have "\<dots> = R"
    by simp
  finally show ?thesis.
qed

lemma eta_pow_Lambda [simp]: "\<eta> ; \<P> R = \<Lambda> R"
  by (metis Id_O_R Lambda_pow eta_def)

lemma pow_prop1: "\<P> R \<subseteq> S \<Longrightarrow> R \<subseteq> \<alpha> (\<eta> ; S)"
  by (metis alpha_eta_pow alpha_ord_pres relcomp_distrib subset_Un_eq)

lemma pow_prop_2: "R \<subseteq> \<P> S \<Longrightarrow> \<alpha> (\<eta> ; R) \<subseteq> S"
  by (metis alpha_eta_pow alpha_ord_pres relcomp_distrib subset_Un_eq)

lemma pow_prop: "R = \<P> S \<Longrightarrow> \<alpha> (\<eta> ; R) = S"
  using alpha_eta_pow by blast

lemma alpha_eta_id [simp]: "\<alpha> (R ; \<eta>) = R"
  by simp

lemma eta_alpha_idem [simp]: "\<alpha> (\<alpha> R; \<eta>) ; \<eta> = \<alpha> R ; \<eta>"
  by simp

lemma lambda_eta_alpha [simp]: "\<Lambda> (\<alpha> (\<alpha> R ; \<eta>)) = \<Lambda> (\<alpha> R)"
  by simp

lemma eta_lambda_idem [simp]: "\<alpha> (\<Lambda> (\<alpha> R)) ; \<eta> = \<alpha> R ; \<eta>"
  by simp

lemma Grph_eta [simp]: "Grph (\<lambda>x. {x}) = \<eta>"
  unfolding Grph_def eta_def Lambda_def Id_def by force

lemma Grph_epsiloff [simp]: "Grph (\<lambda>x. {x}) ; epsiloff = Id"
  by (metis Grph_eta alpha_def alpha_eta)

lemma Image_epsiloff [simp]: "Image epsiloff \<circ> (\<lambda>x. {x}) = id"
  unfolding Image_def epsiloff_def id_def by force


subsection \<open>Subset relation\<close>

definition Omega :: "('a set, 'a set) rel" ("\<Omega>") where
  "\<Omega> = epsilon \<setminus> epsilon"

lemma Omega_set: "\<Omega> = {(A,B). A \<subseteq> B}"
  unfolding Omega_def rres_def epsilon_def by force

lemma conv_Omega: "Omega\<^sup>\<smile> = epsiloff \<sslash> epsiloff"
  by (simp add: Omega_def epsiloff_epsilon rres_lres_conv)

lemma epsilon_eta_Omega [simp]: "\<eta> ; \<Omega> = epsilon"
  unfolding eta_set Omega_set epsilon_def by force

lemma epsiloff_eta_Omega [simp]: "\<Omega>\<^sup>\<smile> ; \<eta>\<^sup>\<smile> = epsiloff"
  by (metis converse_relcomp epsiloff_epsilon epsilon_eta_Omega)

lemma epsilon_Omega [simp]: "epsilon ; \<Omega> = epsilon"
  by (simp add: Omega_def)

lemma conv_Omega_epsiloff [simp]: "\<Omega>\<^sup>\<smile> ; epsiloff = epsiloff"
  by (simp add: conv_Omega)

lemma Lambda_conv [simp]: "(\<Lambda> R)\<^sup>\<smile> = epsilon \<div> R\<^sup>\<smile>"
  by (simp add: Lambda_syq)

lemma Lambda_Omega: "\<Lambda> R ; \<Omega> = R\<^sup>\<smile> \<setminus> epsilon"
proof -
  have "\<Lambda> R ; \<Omega> = \<Lambda> R ; (epsilon \<setminus> epsilon)"
    by (simp add: Omega_def)
  also have "\<dots> = \<Lambda> R ; -(epsiloff ; -epsilon)"
    by (simp add: epsiloff_epsilon rres_compl)
  also have "\<dots> = -(\<Lambda> R ; epsiloff ; -epsilon)"
    by (metis O_assoc det_lambda deterministic_var2)
  also have "\<dots> = - (R ; -epsilon)"
    by (metis alpha_Lambda_canc alpha_def)
  also have "\<dots> = R\<^sup>\<smile> \<setminus> epsilon"
    by (simp add: rres_compl)
  finally show ?thesis.
qed

lemma syq_epsiloff_prop [simp]: "\<Omega>\<^sup>\<smile> ; (epsilon \<div> R) = epsiloff \<sslash> R\<^sup>\<smile>"
  by (metis Lambda_Omega Lambda_syq converse_converse converse_relcomp converse_syq epsiloff_epsilon rres_lres_conv)

lemma pow_semicomm: "((P,Q) \<in> \<P> R ; \<Omega>) = (\<Delta> P ; R \<subseteq> R ; \<Delta> Q)"
  unfolding pow_set Image_def Omega_def rres_def epsilon_def Delta_def by blast


subsection \<open>Complementation relation\<close>

definition Compl :: "('a set,'a set) rel" ("\<C>") where
  "\<C> = epsilon \<div> -epsilon"

lemma Compl_set: "\<C> = {(A,-A) |A. True}"
  unfolding Compl_def syq_set epsilon_def by force

lemma Compl_Compl [simp]: "\<C> ; \<C> = Id"
  by (metis Compl_def Lambda_syq boolean_algebra_class.boolean_algebra.double_compl converse_converse converse_syq det_lambda deterministic_def set_eq_subset syq_compl2 total_def univalent_def)

lemma Compl_def_var: "\<C> = \<Lambda> (-epsiloff)"
  by (metis Compl_def Lambda_syq boolean_algebra_class.boolean_algebra.double_compl compl_conv converse_converse epsiloff_epsilon syq_compl2)

lemma converse_Compl [simp]: "\<C>\<^sup>\<smile> = \<C>"
  by (metis Compl_def converse_syq double_complement syq_compl2)

lemma det_Compl: "deterministic \<C>"
  by (simp add: Compl_def_var det_lambda)

lemma bij_Compl: "bijective \<C>"
  by (simp add: bij_det det_Compl)

lemma Compl_compl_epsiloff [simp]: "\<C> ; -epsiloff = epsiloff"
  by (metis Compl_Compl Compl_def_var alpha_Lambda_canc alpha_epsiloff alpha_relcomp)

lemma Compl_epsiloff [simp]: "\<C> ; epsiloff = -epsiloff"
  by (smt (z3) Compl_def_var alpha_Lambda_canc alpha_def)

lemma compl_epsilon_Compl [simp]: "-epsilon ; \<C> = epsilon"
  by (metis Compl_compl_epsiloff compl_conv converse_Compl converse_converse converse_relcomp epsiloff_epsilon)

lemma epsilon_Compl [simp]: "epsilon ; \<C> = -epsilon"
  by (metis Compl_epsiloff compl_conv converse_Compl converse_converse converse_relcomp epsiloff_epsilon)

lemma Lambda_Compl_var: "\<Lambda> R ; \<C> = R\<^sup>\<smile> \<div> -epsilon"
  by (simp add: Lambda_syq bij_det det_Compl syq_bij)

lemma Lambda_Compl: "\<Lambda> R ; \<C> = \<Lambda> (-R)"
proof -
  have "\<Lambda> R ; \<C> = \<Lambda> R ; \<Lambda> (-epsiloff)"
    by (simp add: Compl_def_var)
  also have "\<dots> = \<Lambda> (\<Lambda> R ; -epsiloff)"
    by (simp add: Lambda_fusion_var)
  also have "\<dots> = \<Lambda> (-(\<Lambda> R ; epsiloff))"
    by (metis det_lambda deterministic_var2)
  also have "\<dots> = \<Lambda> (-R)"
    by (metis alpha_Lambda_canc alpha_def)
  finally show ?thesis.
qed


subsection \<open>Kleisli lifting and Kleisli composition\<close>

definition klift :: "('a,'b set) rel \<Rightarrow> ('a set,'b set) rel" ("_\<^sub>\<P>" [1000] 999) where
  "(R)\<^sub>\<P> = \<P> (\<alpha> R)"

definition kcomp :: "('a,'b set) rel \<Rightarrow> ('b,'c set) rel \<Rightarrow> ('a,'c set) rel" (infixl "\<cdot>\<^sub>\<P>" 70) where
  "R \<cdot>\<^sub>\<P> S = R ; (S)\<^sub>\<P>"

lemma klift_var: "(R)\<^sub>\<P> = \<Lambda> (epsiloff ; R ; epsiloff)"
  by (simp add: pow_def O_assoc alpha_def klift_def)

lemma klift_set: "(R)\<^sub>\<P> = {(A,B). B = \<Union>(Image R A)}"
  unfolding klift_def Image_def pow_set alpha_set by force

lemma klift_set_var: "(R)\<^sub>\<P> = {(A,B). B = \<Union>{C. \<exists>a \<in> A.(a,C) \<in> R}}"
  unfolding klift_set Image_def by auto

lemma klift_mu: "(R)\<^sub>\<P> = \<P> R ; \<mu>"
proof -
  have "(R)\<^sub>\<P> = \<P> (R ; epsiloff)"
    by (simp add: alpha_def klift_def)
  also have "\<dots> = \<P> R ; \<P> epsiloff"
    by (simp add: pow_func2)
  also have "\<dots> = \<P> R ; \<mu>"
    by (simp add: mu_def)
  finally show ?thesis.
qed

lemma klift_empty: "({},A) \<in> (R)\<^sub>\<P> \<longleftrightarrow> A = {}"
  using klift_set by auto

lemma klift_ext1: "(R ; (S)\<^sub>\<P>)\<^sub>\<P> = (R)\<^sub>\<P> ; (S)\<^sub>\<P>"
  by (metis (no_types, opaque_lifting) Lambda_epsiloff_up1 Lambda_fusion_var O_assoc alpha_def klift_var)

lemma klift_ext2: "deterministic R \<Longrightarrow> \<eta> ; (R)\<^sub>\<P> = R"
  by (metis Id_O_R Lambda_alpha_canc Lambda_pow eta_def klift_def)

lemma klift_ext3 [simp]: "(\<eta>)\<^sub>\<P> = Id"
  by (simp add: klift_def)

lemma pow_klift [simp]: "(R ; \<eta>)\<^sub>\<P> = \<P> R"
  by (simp add: klift_def)

lemma mu_klift [simp]: "(Id)\<^sub>\<P> = \<mu>"
  by (simp add: klift_def mu_def)

lemma kcomp_var: "R \<cdot>\<^sub>\<P> S = R ; \<P> S ; \<mu>"
  by (simp add: O_assoc kcomp_def klift_mu)

lemma kcomp_assoc: "R \<cdot>\<^sub>\<P> (S \<cdot>\<^sub>\<P> T) = (R \<cdot>\<^sub>\<P> S) \<cdot>\<^sub>\<P>T"
proof -
  have "R \<cdot>\<^sub>\<P> (S \<cdot>\<^sub>\<P> T) = R ; (S ; (T)\<^sub>\<P>)\<^sub>\<P>"
    by (simp add: kcomp_def)
  also have "\<dots> = R ; ((S)\<^sub>\<P> ; (T)\<^sub>\<P>)"
    by (simp add: klift_ext1)
  also have "\<dots> = (R \<cdot>\<^sub>\<P> S) \<cdot>\<^sub>\<P> T"
    by (simp add: O_assoc kcomp_def)
  finally show ?thesis.
qed

lemma kcomp_oner: "R \<cdot>\<^sub>\<P> \<eta> = R"
  by (simp add: kcomp_def)

lemma kcomp_onel: "deterministic R \<Longrightarrow> \<eta> \<cdot>\<^sub>\<P> R = R"
  by (simp add: kcomp_def klift_ext2)


subsection \<open>Relational box\<close>

definition rbox :: "('a,'b) rel \<Rightarrow> ('b set, 'a set) rel" where
  "rbox R = \<Lambda> (epsiloff \<sslash> R)"

lemma rbox_set: "rbox R = {(Q,P). P = {a. \<forall>b. (a,b) \<in> R \<longrightarrow> b \<in> Q}}"
  unfolding rbox_def Lambda_def lres_def epsiloff_def
  by force

lemma rbox_exp: "((Q,P) \<in> (rbox (R::('a,'b) rel))) = (P = -{a. \<exists>b. (a,b) \<in> R \<and> b \<in> -Q})"
  by (smt (z3) Collect_cong Collect_neg_eq ComplD ComplI case_prodD case_prodI mem_Collect_eq rbox_set)

lemma rbox_subset: "rbox R ; \<Omega>\<^sup>\<smile> = {(Q,P). P \<subseteq> {a. \<forall>b. (a,b) \<in> R \<longrightarrow> b \<in> Q}}"
  unfolding rbox_set Omega_set by blast

lemma rbox_semicomm: "(Q,P) \<in> rbox R ; \<Omega>\<^sup>\<smile> = (\<Delta> P ; R \<subseteq> R ; \<Delta> Q)"
  unfolding rbox_subset Delta_def by blast

lemma rbox_semicomm_var: "(Q,P) \<in> rbox R ; \<Omega>\<^sup>\<smile> = (\<Delta> P \<subseteq> (R ; \<Delta> Q) \<sslash> R)"
  by (simp add: lres_galois rbox_semicomm)

lemma rbox_omega: "rbox epsiloff = \<Lambda> (\<Omega>\<^sup>\<smile>)"
  by (simp add: conv_Omega rbox_def)

lemma Omega_rbox: "\<Omega> = (\<alpha> (rbox epsiloff))\<^sup>\<smile>"
  by (simp add: rbox_omega)

lemma pow_rbox: "((Q,P) \<in> rbox R ; \<Omega>\<^sup>\<smile>) = ((P,Q) \<in> \<P> R ; \<Omega>)"
proof -
  have "(Q,P) \<in> rbox R ; \<Omega>\<^sup>\<smile> = (\<Delta> P ; R \<subseteq> R ; \<Delta> Q)"
    by (simp add: rbox_semicomm)
  also have "\<dots> = ((P,Q) \<in> \<P> R ; \<Omega>)"
    by (simp add: pow_semicomm)
  finally show ?thesis.
qed

lemma rbox_pow_Compl: "rbox R = \<C> ; \<P> (R\<^sup>\<smile>) ; \<C>"
proof -
  have "\<C> ; \<P> (R\<^sup>\<smile>) ; \<C> = \<Lambda> (-epsiloff) ; \<P> (R\<^sup>\<smile>) ; \<C>"
    by (simp add: Compl_def_var)
  also have "\<dots> = \<Lambda> (-epsiloff ; R\<^sup>\<smile>) ; \<C>"
    by (simp add: Lambda_pow)
  also have "\<dots> = \<Lambda> (-(-epsiloff ; R\<^sup>\<smile>))"
    by (simp add: Lambda_Compl)
  also have "\<dots> = \<Lambda> (epsiloff \<sslash> R)"
    by (simp add: lres_compl)
  also have "\<dots> = rbox R"
    by (simp add: rbox_def)
  finally show ?thesis..
qed

lemma pow_rbox_Compl: "\<P> R = \<C> ; rbox (R\<^sup>\<smile>) ; \<C>"
  by (metis Compl_Compl Id_O_R O_assoc R_O_Id converse_converse rbox_pow_Compl)

lemma pow_conjugation: "\<C> ; (\<P> (R\<^sup>\<smile>) ; \<Omega>)\<^sup>\<smile> = \<P> R ; \<C> ; \<Omega>\<^sup>\<smile>"
proof -
  have "\<P> R ; \<C> ; \<Omega>\<^sup>\<smile> = \<Lambda> (-(epsiloff ; R)) ; -(- epsiloff ; epsilon)"
    by (simp add: Lambda_Compl pow_def conv_Omega epsiloff_epsilon lres_compl)
  also have "\<dots> = -(\<Lambda> (-(epsiloff ; R)) ; - epsiloff ; epsilon)"
    by (metis (no_types, opaque_lifting) alpha_Lambda_canc alpha_def converse_converse det_lambda det_lres deterministic_var2 epsiloff_epsilon lres_compl)
  also have "\<dots> = -(\<Lambda> (-(epsiloff ; R)) ; \<C> ; epsiloff ; epsilon)"
    by (metis Compl_epsiloff alpha_def alpha_relcomp)
  also have "\<dots> = -(\<Lambda> (epsiloff ; R) ; epsiloff ; epsilon)"
    by (simp add: Lambda_Compl)
  also have "\<dots> = -(epsiloff ; R ; epsilon)"
    by (metis Lambda_epsiloff_up1 alpha_def)
  also have "\<dots> = -(\<C> ; -epsiloff ; (epsiloff ; R\<^sup>\<smile>)\<^sup>\<smile>)"
    by (metis Compl_compl_epsiloff O_assoc converse_converse converse_relcomp epsiloff_epsilon)
  also have "\<dots> = \<C> ; (epsiloff \<sslash> (epsiloff ; R\<^sup>\<smile>))"
    by (metis (no_types, opaque_lifting) Compl_def_var Lambda_Compl Lambda_fusion_var pow_def alpha_Lambda_canc boolean_algebra_class.boolean_algebra.double_compl converse_converse pow_rbox_Compl rbox_def)
  also have "\<dots> = \<C>; (\<P> (R\<^sup>\<smile>) ; \<Omega>)\<^sup>\<smile>"
    by (simp add: Lambda_Omega pow_def epsiloff_epsilon rres_lres_conv)
  finally show ?thesis..
qed

lemma pow_rbox_eq: "rbox R ; \<Omega>\<^sup>\<smile> = (\<P> R ; \<Omega>)\<^sup>\<smile>"
  by (metis (no_types, lifting) Compl_Compl O_assoc R_O_Id converse_converse converse_relcomp pow_conjugation rbox_pow_Compl)

end
