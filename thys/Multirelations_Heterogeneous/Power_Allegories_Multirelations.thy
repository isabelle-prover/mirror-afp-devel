section \<open>Multirelational Properties of Power Allegories\<close>

theory Power_Allegories_Multirelations

imports Multirelations_Basics

begin

text \<open>We start with random little properties.\<close>

lemma eta_s_id: "\<eta> = s_id"
  unfolding s_id_def eta_set by force

lemma Lambda_empty [simp]: "\<Lambda> {} = p_id"
  unfolding Lambda_def p_id_def by blast

lemma alpha_pid [simp]: "\<alpha> p_id = {}"
  unfolding alpha_def epsiloff_def p_id_def by force


subsection \<open>Peleg lifting\<close>

definition plift :: "('a,'b) mrel \<Rightarrow> ('a set,'b set) rel" ("_\<^sub>*" [1000] 999) where
  "R\<^sub>* = {(A,B). \<exists>f. (\<forall>a \<in> A. (a,f(a)) \<in> R) \<and> B = \<Union>(f ` A)}"

lemma pcomp_plift: "R \<cdot> S = R ; S\<^sub>*"
  unfolding s_prod_def plift_def relcomp_unfold by simp

lemma det_plift_klift: "deterministic R \<Longrightarrow> R\<^sub>* = (R)\<^sub>\<P>"
  unfolding deterministic_set plift_def klift_set_var
  apply (simp add: set_eq_iff)
  apply safe
  by metis+

lemma plift_ext2 [simp]: "\<eta> ; R\<^sub>* = R"
  by (metis eta_s_id pcomp_plift s_prod_idl)

lemma pliftext_3 [simp]: "\<eta>\<^sub>* = Id"
  by (simp add: det_eta det_plift_klift)

lemma d_dom_plift: "(Dom R)\<^sub>* = dom (R\<^sub>*)"
  unfolding Dom_def dom_set plift_def
  apply clarsimp
  apply safe
  apply (metis (full_types) UN_singleton image_cong)
  by (metis UN_singleton)

lemma d_pid_plift: "(Dom R)\<^sub>* \<subseteq> Id"
  by (metis d_dom_plift d_idem dom_subid inf.absorb_iff2)

lemma d_plift_sub: "A \<subseteq> B \<Longrightarrow> (B,B) \<in> (Dom R)\<^sub>* \<Longrightarrow> (A,A) \<in> (Dom R)\<^sub>*"
  by (smt (z3) Pair_inject UN_singleton Dom_def mem_Collect_eq plift_def split_conv subsetD)

lemma plift_empty: "({},A) \<in> R\<^sub>* \<longleftrightarrow> A = {}"
  using plift_def by auto

lemma univ_plift_klift:
  assumes "univalent R"
  shows "R\<^sub>* = (Dom R)\<^sub>* ; (R)\<^sub>\<P>"
proof -
  have "\<forall>A B . (A,B) \<in> R\<^sub>* \<longleftrightarrow> (A,B) \<in> (Dom R)\<^sub>* ; (R)\<^sub>\<P>"
  proof (intro allI, rule iffI)
    fix A B
    assume 1: "(A,B) \<in> R\<^sub>*"
    hence "(A,B) \<in> (R)\<^sub>\<P>"
      unfolding klift_set_var
      apply clarsimp
      by (smt (z3) Collect_cong Pair_inject Union_eq assms case_prodE image_iff mem_Collect_eq plift_def univalent_set)
    thus "(A,B) \<in> (Dom R)\<^sub>* ; (R)\<^sub>\<P>"
      using 1 d_dom_plift dom_set by fastforce
  next
    fix A B
    assume "(A,B) \<in> (Dom R)\<^sub>* ; (R)\<^sub>\<P>"
    from this obtain C where 2: "(A,C) \<in> (Dom R)\<^sub>* \<and> (C,B) \<in> (R)\<^sub>\<P>"
      by auto
    from this obtain f where 3: "(\<forall>a \<in> A. (a,f(a)) \<in> Dom R) \<and> C = \<Union>(f ` A)"
      by (smt (verit) Pair_inject case_prodE mem_Collect_eq plift_def)
    hence "\<forall>a \<in> A . \<exists>D . (a,D) \<in> R"
      by (simp add: Dom_def)
    from this obtain g where 4: "\<forall>a \<in> A . (a,g(a)) \<in> R"
      by metis
    hence "\<forall>a \<in> A. f(a) = {a}"
      using 3 by (simp add: Dom_def)
    hence "A = C"
      using 2 3 by (smt (verit) Pair_inject UN_singleton case_prodE image_cong mem_Collect_eq plift_def)
    hence "(A,B) \<in> (R)\<^sub>\<P>"
      using 2 by simp
    thus "(A,B) \<in> R\<^sub>*"
      unfolding plift_def klift_set_var
      apply clarsimp
      apply (rule exI[where ?x="g"])
      using 4 by (smt (verit, ccfv_SIG) Collect_cong assms image_def univalent_set)
  qed
  thus "R\<^sub>* = (Dom R)\<^sub>* ; (R)\<^sub>\<P>"
    by force
qed

lemma plift_ext1:
  assumes "univalent f"
  shows "(R ; f\<^sub>*)\<^sub>* = R\<^sub>* ; f\<^sub>*"
proof -
  have "\<forall>A B . (A,B) \<in> (R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>)\<^sub>* \<longleftrightarrow> (A,B) \<in> R\<^sub>* ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>"
  proof (intro allI, rule iffI)
    fix A B
    assume 1: "(A,B) \<in> (R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>)\<^sub>*"
    from this obtain g where 2: "(\<forall>a \<in> A. (a,g(a)) \<in> R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>) \<and> B = \<Union>(g ` A)"
      by (smt (verit) Pair_inject case_prodE mem_Collect_eq plift_def)
    hence "\<forall>a \<in> A . \<exists>C D . (a,C) \<in> R \<and> (C,D) \<in> (Dom f)\<^sub>* \<and> (D,g(a)) \<in> (f)\<^sub>\<P>"
      by (meson relcompEpair)
    hence "\<forall>a \<in> A . \<exists>C . (a,C) \<in> R \<and> (C,C) \<in> (Dom f)\<^sub>* \<and> (C,g(a)) \<in> (f)\<^sub>\<P>"
      using d_pid_plift by fastforce
    from this obtain h where 3: "\<forall>a \<in> A . (a,h a) \<in> R \<and> (h a,h a) \<in> (Dom f)\<^sub>* \<and> (h a,g(a)) \<in> (f)\<^sub>\<P>"
      by metis
    let ?h = "\<Union>(h ` A)"
    have 4: "(A,?h) \<in> R\<^sub>*"
      using 3 plift_def by fastforce
    have 5: "(?h,?h) \<in> (Dom f)\<^sub>*"
      using 3
      unfolding plift_def Dom_def
      apply clarsimp
      by (metis UN_extend_simps(9) UN_singleton)
    have "(?h,B) \<in> (f)\<^sub>\<P>"
      using 2 3
      unfolding klift_set
      by auto
    thus "(A,B) \<in> R\<^sub>* ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>"
      using 4 5 by blast
  next
    fix A B
    assume "(A,B) \<in> R\<^sub>* ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>"
    from this obtain C D where 6: "(A,C) \<in> R\<^sub>* \<and> (C,D) \<in> (Dom f)\<^sub>* \<and> (D,B) \<in> (f)\<^sub>\<P>"
      by blast
    hence 7: "C = D"
      using d_pid_plift by auto
    from 6 obtain g where 8: "(\<forall>a \<in> A. (a,g(a)) \<in> R) \<and> C = \<Union>(g ` A)"
      by (smt (verit) Pair_inject case_prodE mem_Collect_eq plift_def)
    hence 9: "\<forall>a \<in> A. (g(a),g(a)) \<in> (Dom f)\<^sub>*"
      using 6 7 by (metis d_plift_sub UN_iff subsetI)
    let ?h = "\<lambda>a . \<Union>(f `` g a)"
    have "\<forall>a \<in> A. (g(a),?h a) \<in> (f)\<^sub>\<P>"
      using 6 by (simp add: klift_set)
    hence 10: "\<forall>a \<in> A. (a,?h a) \<in> R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>"
      using 8 9 by blast
    have "B = \<Union>(f `` D)"
      using 6 klift_set by fastforce
    hence 11: "B = (\<Union>a\<in>A . ?h a)"
      using 7 8 image_empty by blast
    show "(A,B) \<in> (R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>)\<^sub>*"
      apply (subst plift_def)
      apply clarsimp
      apply (rule exI[where ?x="?h"])
      using 10 11 by simp
  qed
  hence "(R ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>)\<^sub>* = R\<^sub>* ; (Dom f)\<^sub>* ; (f)\<^sub>\<P>"
    by force
  thus ?thesis
    by (metis (no_types, opaque_lifting) assms univ_plift_klift O_assoc)
qed

lemma plift_assoc_univ: "univalent f \<Longrightarrow> (R \<cdot> S) \<cdot> f = R \<cdot> (S \<cdot> f)"
  by (simp add: pcomp_plift O_assoc plift_ext1)

lemma Lambda_funct: "\<Lambda> (R ; S) = \<Lambda> R \<cdot> \<Lambda> S"
  by (simp add: Lambda_pow det_lambda det_plift_klift klift_def pcomp_plift)

lemma eta_funct: "R ; S ; \<eta> = (R ; \<eta>) \<cdot> (S ; \<eta>)"
proof -
  have "(R ; \<eta>) \<cdot> (S ; \<eta>) = R ; \<eta> ; (S ; \<eta>)\<^sub>*"
    by (simp add: pcomp_plift)
  also have "\<dots> = R ; (\<eta> \<cdot> (S ; \<eta>))"
    by (simp add: O_assoc pcomp_plift)
  also have "\<dots> = R ; S ; \<eta>"
    by (simp add: O_assoc pcomp_plift)
  finally show ?thesis..
qed

lemma alpha_funct_det: "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> \<alpha> (R \<cdot> S) = \<alpha> R ; \<alpha> S"
  by (metis Lambda_epsiloff_up2 Lambda_funct alpha_Lambda_canc)

lemma pcomp_det: "deterministic S \<Longrightarrow> R \<cdot> S = R ; (S)\<^sub>\<P>"
  by (simp add: det_plift_klift pcomp_plift)

lemma pcomp_det2: "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> (R \<cdot> S)\<^sub>\<P> = (R)\<^sub>\<P> ; (S)\<^sub>\<P>"
  by (simp add: klift_ext1 pcomp_det)

lemma pcomp_alpha: "\<alpha> (R \<cdot> S) = R ; \<alpha> ((S)\<^sub>*)"
  by (simp add: pcomp_plift)


subsection \<open>Fusion and fission\<close>

definition fus :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" where
  "fus R = \<Lambda> (\<alpha> R)"

definition fis :: "('a,'b) mrel \<Rightarrow> ('a,'b) mrel" where
  "fis R = \<alpha> R ; \<eta>"

lemma fus_set: "fus R = {(a,B) |a B. B = \<Union>(Image R {a})}"
  unfolding fus_def Lambda_def alpha_set by force

lemma fis_set: "fis R = {(a,{b}) |a b. b \<in> \<Union>(Image R {a})}"
  unfolding fis_def alpha_set eta_set relcomp_unfold by force

lemma fis_det_comp: "deterministic R \<Longrightarrow> deterministic S \<Longrightarrow> fis (R \<cdot> S) = fis R \<cdot> fis S"
  by (simp add: alpha_funct_det eta_funct fis_def)

lemma fis_fix_det: "deterministic R = (fus R = R)"
  by (metis Lambda_alpha_canc det_lambda fus_def)


subsection \<open>Galois connections for multirelations\<close>

lemma sub_subh: "R \<subseteq> S \<Longrightarrow> R \<subseteq> S ; (epsiloff \<sslash> epsiloff)"
  by (metis R_O_Id alpha_def alpha_epsiloff lres_galois order_refl relcomp_mono)

lemma alpha_Lambda_galois: "(\<alpha> R \<subseteq> S) = (R \<subseteq> \<Lambda> S ; (epsiloff \<sslash> epsiloff))"
proof -
  have a: "(\<alpha> R \<subseteq> S) = (R \<subseteq> S \<sslash> epsiloff)"
    by (simp add: alpha_def lres_galois)
  have "S \<sslash> epsiloff = (\<Lambda> S ; epsiloff) \<sslash> epsiloff"
    by (metis alpha_Lambda_canc alpha_def)
  also have "\<dots> = \<Lambda> S ; (epsiloff \<sslash> epsiloff)"
    by (simp add: det_lambda det_lres)
  finally have "S \<sslash> epsiloff = \<Lambda> S ; (epsiloff \<sslash> epsiloff)"
    .
  thus ?thesis
    using a by presburger
qed

lemma alpha_Lambda_galois_set: "(\<alpha> R \<subseteq> S) = (R \<subseteq> {(a,A). \<exists>B. (a,B) \<in> \<Lambda> S \<and> A \<subseteq> B})"
  unfolding alpha_set Lambda_def by blast

lemma epsiloff_eta_lres: "epsiloff ; \<eta> \<subseteq> epsiloff \<sslash> epsiloff"
proof -
  have "epsiloff ; \<eta> ; epsiloff = epsiloff ; \<alpha> (\<Lambda> Id)"
    by (simp add: O_assoc alpha_def eta_def)
  also have "\<dots> = epsiloff"
    by simp
  finally have "epsiloff ; \<eta> ; epsiloff = epsiloff".
  thus ?thesis
    by (smt (verit) lres_galois order_refl)
qed

lemma eta_alpha_galois: "(R ; \<eta> \<subseteq> S ; (epsiloff \<sslash> epsiloff)) = (R \<subseteq> \<alpha> S)"
proof
  assume "R ; \<eta> \<subseteq> S ; (epsiloff \<sslash> epsiloff)"
  hence "R \<subseteq> S ; (epsiloff \<sslash> epsiloff) ; epsiloff"
    by (metis R_O_Id alpha_def alpha_eta alpha_ord_pres alpha_relcomp)
  thus "R \<subseteq> \<alpha> S"
    by (simp add: O_assoc alpha_def)
next
  assume "R \<subseteq> \<alpha> S"
  hence "R ; \<eta> \<subseteq> \<alpha> S ; \<eta>"
    by (simp add: relcomp_mono)
  hence "R ; \<eta> \<subseteq> S ; epsiloff ; \<eta>"
    by (simp add: alpha_def)
  thus "R ; \<eta> \<subseteq> S ; (epsiloff \<sslash> epsiloff)"
    using epsiloff_eta_lres in_mono by fastforce
qed

lemma eta_alpha_galois_set: "(R ; \<eta> \<subseteq> {(a,A). \<exists>B. (a,B) \<in> S \<and> A \<subseteq> B}) = (R \<subseteq> \<alpha> S)"
  unfolding eta_set alpha_set by auto

lemma Lambda_iso: "R \<subseteq> S \<Longrightarrow> \<Lambda> R \<subseteq> \<Lambda> S ; (epsiloff \<sslash> epsiloff)"
  by (metis alpha_Lambda_canc alpha_Lambda_galois)

lemma eta_iso: "R \<subseteq> S \<Longrightarrow> R ; \<eta> \<subseteq> S ; \<eta> ; (epsiloff \<sslash> epsiloff)"
  by (simp add: eta_alpha_galois)

lemma alpha_iso: "R \<subseteq> S ; (epsiloff \<sslash> epsiloff) \<Longrightarrow> \<alpha> R \<subseteq> \<alpha> S"
  by (metis (no_types, lifting) alpha_def alpha_ord_pres alpha_relcomp conv_Omega conv_Omega_epsiloff)

lemma Lambda_canc_dcl: "R \<subseteq> \<Lambda> (\<alpha> R) ; (epsiloff \<sslash> epsiloff)"
  using alpha_Lambda_galois by blast

lemma eta_canc_dcl: "\<alpha> R ; \<eta> \<subseteq> R ; (epsiloff \<sslash> epsiloff)"
  by (simp add: eta_alpha_galois)

lemma alpha_surj: "surj \<alpha>"
  using alpha_Lambda_canc by blast

lemma Lambda_inj: "inj \<Lambda>"
  by (metis alpha_Lambda_canc injI)

lemma eta_inj: "inj (\<lambda>x. x ; \<eta>)"
  by (metis alpha_eta_id injI)

lemma fus_least_odet:
  assumes "\<Lambda> (\<alpha> S) = S"
  and "R \<subseteq> S ; (epsiloff \<sslash> epsiloff)"
  shows "\<Lambda> (\<alpha> R) \<subseteq> S ; (epsiloff \<sslash> epsiloff)"
proof -
  have "\<alpha> R \<subseteq> \<alpha> S"
    by (simp add: alpha_iso assms(2))
  hence "\<Lambda> (\<alpha> R) \<subseteq> \<Lambda> (\<alpha> S) ; (epsiloff \<sslash> epsiloff)"
    by (simp add: Lambda_iso)
  thus ?thesis
    using assms(1) by auto
qed

lemma fis_greatest_idet:
  assumes "\<alpha> S ; \<eta> = S"
  and "S \<subseteq> R ; (epsiloff \<sslash> epsiloff)"
  shows "S \<subseteq> \<alpha> R ; \<eta> ; (epsiloff \<sslash> epsiloff)"
proof -
  have "\<alpha> S \<subseteq> \<alpha> R"
    by (simp add: alpha_iso assms(2))
  hence "\<alpha> S ; \<eta> \<subseteq> \<alpha> R ; \<eta> ; (epsiloff \<sslash> epsiloff)"
    by (simp add: eta_iso)
  thus ?thesis
    using assms(1) by auto
qed

lemma fis_fus_galois: "(\<alpha> R ; \<eta> \<subseteq> S ; (epsiloff \<sslash> epsiloff)) = (R \<subseteq> \<Lambda> (\<alpha> S) ; (epsiloff \<sslash> epsiloff))"
  by (simp add: alpha_Lambda_galois eta_alpha_galois)


subsection \<open>Properties of alpha, fission and fusion\<close>

lemma alpha_lax: "\<alpha> (R \<cdot> S) \<subseteq> \<alpha> R ; \<alpha> S"
  unfolding alpha_def s_prod_def epsiloff_def relcomp_unfold by blast

lemma alpha_down [simp]: "\<alpha> (R ; \<Omega>\<^sup>\<smile>) = \<alpha> R"
  by (metis alpha_def alpha_relcomp conv_Omega_epsiloff)

lemma fis_fis [simp]: "fis \<circ> fis = fis"
  unfolding fun_eq_iff fis_def by simp

lemma fus_fus [simp]: "fus \<circ> fus = fus"
  unfolding fun_eq_iff fus_def by simp

lemma fis_fus [simp]: "fis \<circ> fus = fis"
  unfolding fun_eq_iff fus_def fis_def by simp

lemma fus_fis [simp]: "fus \<circ> fis = fus"
  unfolding fun_eq_iff fus_def fis_def by simp

lemma fis_alpha: "fis R \<cdot> S = \<alpha> R ; S"
  by (simp add: O_assoc fis_def pcomp_plift)

lemma fis_lax: "fis (R \<cdot> S) \<subseteq> fis R \<cdot> fis S"
  by (metis fis_def alpha_lax eta_funct relcomp_mono subsetI)

lemma klift_fus: "(R)\<^sub>\<P> = fus (epsiloff ; R)"
  by (simp add: alpha_def fus_def klift_var)

lemma fus_eta_klift: "fus R = \<eta> ; (R)\<^sub>\<P>"
  by (metis Id_O_R Lambda_pow eta_def fus_def klift_def)

lemma fus_Lambda_mu: "fus R = \<Lambda> R ; \<mu>"
  by (simp add: fus_def lambda_alpha_mu)


subsection \<open>Properties of fusion, fission, nu and tau\<close>

lemma alpha_tau [simp]: "\<alpha> (\<tau> R) = {}"
  by (metis alpha_ord_pres alpha_pid subset_empty tau_le_c)

lemma alpha_nu [simp]: "\<alpha> (\<nu> R) = \<alpha> R"
  unfolding alpha_def nu_def epsiloff_def U_def p_id_def relcomp_unfold by force

lemma nu_fis [simp]: "\<nu> (fis R) = fis R"
  by (metis alpha_fp empty_iff equals0I fis_alpha relcompE)

lemma nu_fis_var: "\<nu> (fis R) = fis (\<nu> R)"
  by (metis alpha_nu fis_def nu_fis)

lemma tau_fis [simp]: "\<tau> (fis R) = {}"
  by (metis nu_fis tau_alpha_zero)


text \<open>Properties of tests and domain\<close>

lemma subid_plift: "(P \<inter> \<eta>)\<^sub>* = {(A,A)|A. \<forall>a \<in> A. (a,{a}) \<in> (P \<inter> \<eta>)}"
  unfolding plift_def eta_set by safe auto

lemma U_subid: "R ; (P \<inter> \<eta>)\<^sub>* = R \<inter> U ; (P \<inter> \<eta>)\<^sub>*"
  unfolding plift_def U_def eta_set relcomp_unfold
  apply safe
  apply force
  apply blast
  by force

lemma subid_plift_down: "U ; (P \<inter> \<eta>)\<^sub>* ; \<Omega>\<^sup>\<smile> = U ; (P \<inter> \<eta>)\<^sub>*"
  unfolding U_def relcomp_unfold plift_def Omega_set eta_set converse_def
  apply safe
  apply clarsimp
  apply (metis IntE UN_singleton inf.orderE)
  by blast

lemma nu_subid_plift: "\<nu> (R ; (P \<inter> \<eta>)\<^sub>*) = \<nu> R ; ( P \<inter> \<eta>)\<^sub>*"
  unfolding nu_def relcomp_unfold plift_def U_def p_id_def eta_set by safe fastforce+

lemma dom_fis1: "dom (fis R) = dom (\<alpha> R)"
  unfolding dom_set fis_set alpha_set by blast

lemma dom_fis2: "dom (fis R) = dom (\<alpha> (\<nu> R))"
  by (simp add: dom_fis1)

lemma dom_fis3: "dom (fis R) = dom (\<nu> R)"
  unfolding dom_set fis_set nu_def U_def p_id_def by safe fastforce+

lemma dom_fis4: "dom (fis R) = dom (\<nu> (fus R))"
  by (metis comp_eq_dest_lhs dom_fis3 fis_fus)

lemma dom_alpha: "dom (\<alpha> R ; (P \<inter> \<eta>)) = dom (\<nu> (R ; \<Omega>\<^sup>\<smile>) ; (P \<inter> \<eta>)\<^sub>*)"
  unfolding dom_set alpha_set eta_set Omega_set plift_def nu_def relcomp_unfold U_def p_id_def
  apply safe
  apply (clarsimp, metis empty_iff empty_subsetI insert_subset singletonD singletonI UN_singleton)
  by clarsimp fastforce


subsection \<open>Box and diamond\<close>

definition box :: "('a, 'b) mrel \<Rightarrow> ('b set, 'a set) rel" where
  "box R = rbox (\<alpha> R)"

definition dia :: "('a, 'b) mrel \<Rightarrow> ('b set, 'a set) rel" where
  "dia R = \<P> ((\<alpha> R)\<^sup>\<smile>)"

lemma box_set: "box R = {(B, A). A = {a. \<forall>C. (a, C) \<in> R \<longrightarrow> C \<subseteq> B}}"
  unfolding box_def rbox_set alpha_set by force

lemma dia_set: "dia R = {(B, A). A = {a. \<exists>C. (a, C) \<in> R \<and> C \<inter> B \<noteq> {}}}"
  unfolding dia_def pow_set Image_def alpha_set converse_def by force

lemma box_Omega: "box R = \<Lambda> (\<Omega>\<^sup>\<smile> \<sslash> R)"
  unfolding box_set Lambda_def lres_def Omega_set by auto

end
