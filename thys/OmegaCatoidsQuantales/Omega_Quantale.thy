(* 
Title: Omega-Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>$\omega$-Quantales\<close>

theory Omega_Quantale
  imports Quantales_Converse.Modal_Quantale Omega_Kleene_Algebra

begin

class iquantale = complete_lattice + imonoid_mult +
  assumes Sup_distl: "x \<cdot>\<^bsub>i\<^esub> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot>\<^bsub>i\<^esub> y)" 
  assumes Sup_distr: "\<Squnion>X \<cdot>\<^bsub>i\<^esub> y = (\<Squnion>x \<in> X. x \<cdot>\<^bsub>i\<^esub> y)"

sublocale iquantale \<subseteq> qiq: unital_quantale "un i" "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" _ _ _ _ _ _ _ _ 
  apply unfold_locales using local.Sup_distr local.Sup_distl by auto

definition (in iquantale) "istar = qiq.qstar"

lemma (in iquantale) istar_unfold: "istar i x = (\<Squnion>k. mm.power i x k)"
  unfolding local.qiq.qstar_def local.istar_def by simp

sublocale iquantale \<subseteq> dqisi: idioid "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un
  by unfold_locales (simp_all add: local.qiq.sup_distl)

sublocale iquantale \<subseteq> dqikai: ikleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un istar
  by unfold_locales (simp_all add: local.istar_def local.qiq.uwqlka.star_inductl local.qiq.uqka.star_inductr')

class idomain_quantale = iquantale + idom_op +
  assumes do_absorb: "x \<le> do i x \<cdot>\<^bsub>i\<^esub> x"
  and do_local [simp]: "do i (x \<cdot>\<^bsub>i\<^esub> do i y) = do i (x \<cdot>\<^bsub>i\<^esub> y)"
  and do_add: "do i (x \<squnion> y) = do i x \<squnion> do i y"
  and do_subid: "do i x \<le> un i"
  and do_zero [simp]: "do i \<bottom> = \<bottom>"

sublocale idomain_quantale \<subseteq> dqidq: domain_quantale "do i" "un i" "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" _ _ _ _ _ _ _ _
  by (unfold_locales, simp_all add: local.do_absorb local.do_add local.do_subid)

sublocale idomain_quantale \<subseteq> dqidsi: idomain_semiring "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  icomp un do
  by (unfold_locales, simp_all add: local.do_add local.do_subid)

class icodomain_quantale = iquantale + icod_op +
  assumes cd_absorb: "x \<le> x \<cdot>\<^bsub>i\<^esub> cd i x" 
  and cd_local [simp]: "cd i (cd i x \<cdot>\<^bsub>i\<^esub> y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  and cd_add: "cd i (x \<squnion> y) = cd i x \<squnion> cd i y"
  and cd_subid: "cd i x \<le> un i"
  and cd_zero [simp]: "cd i \<bottom> = \<bottom>"

sublocale icodomain_quantale \<subseteq> cdqicdq: codomain_quantale "un i" "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" _ _ _ _ _ _ _ _ "cd i"
  by (unfold_locales, simp_all add: local.cd_absorb local.cd_add local.cd_subid)

sublocale icodomain_quantale \<subseteq> cdqidcsi: icodomain_semiring cd "(\<squnion>)"  "(\<le>)" "(<)" "\<bottom>" icomp un
  by (unfold_locales, simp_all add: local.cd_absorb local.cd_add local.cd_subid)

class imodal_quantale = idomain_quantale + icodomain_quantale +
  assumes dc_compat [simp]: "do i (cd i x) = cd i x" 
  and cd_compat [simp]: "cd i (do i x) = do i x" 

sublocale imodal_quantale \<subseteq> mqimq: dc_modal_quantale "un i" "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" _ _ _ _ _ _ _ _  "cd i" "do i"
  by unfold_locales simp_all

sublocale imodal_quantale \<subseteq> mqimka: imodal_kleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un istar cd do
  by unfold_locales simp_all

sublocale imodal_quantale \<subseteq> mqidual: imodal_quantale do _ _ _ _ _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ cd
  by unfold_locales (simp_all add: local.cdqicdq.coddual.Sup_distl local.Sup_distl)

class omega_quantale = imodal_quantale +
  assumes interchange: "i < j \<Longrightarrow> (w \<cdot>\<^bsub>j\<^esub> x) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> z) \<le> (w \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (x \<cdot>\<^bsub>i\<^esub> z)"
  and dj_hom: "i \<noteq> j \<Longrightarrow> do j (x \<cdot>\<^bsub>i\<^esub> y) \<le> do j x \<cdot>\<^bsub>i\<^esub> do j y"
  and cj_hom: "i \<noteq> j \<Longrightarrow> cd j (x \<cdot>\<^bsub>i\<^esub> y) \<le> cd j x \<cdot>\<^bsub>i\<^esub> cd j y"
  and djdi: "i < j \<Longrightarrow> do j (do i x) = do i x"

class strong_omega_quantale = omega_quantale +
  assumes dj_strong_hom: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>i\<^esub> y) = do j x \<cdot>\<^bsub>i\<^esub> do j y"
  and cj_strong_hom: "i < j \<Longrightarrow> cd j (x \<cdot>\<^bsub>i\<^esub> y) = cd j x \<cdot>\<^bsub>i\<^esub> cd j y"

sublocale omega_quantale \<subseteq> tgqs: omega_semiring cd "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un do
  by unfold_locales (simp_all add: local.interchange local.dj_hom local.cj_hom local.djdi)

sublocale strong_omega_quantale \<subseteq> stgqs: strong_omega_semiring cd "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un do
  by unfold_locales (simp_all add: local.dj_strong_hom local.cj_strong_hom) 

sublocale omega_quantale \<subseteq> tgqs: omega_kleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  icomp un istar cd do ..

sublocale strong_omega_quantale \<subseteq> tgqs: strong_omega_kleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" icomp un  istar cd do  ..

context omega_quantale
begin

lemma istar_aux: "i < j \<Longrightarrow> mm.power i (x \<cdot>\<^bsub>j\<^esub> y) k \<le> mm.power i x k \<cdot>\<^bsub>j\<^esub> mm.power i y k"
proof (induct k)
  case 0
  then show ?case
    by (simp add: tgqs.uni_compj_eq)
next
  case (Suc k)
  fix k 
  assume "i < j"
  assume h: "i < j \<Longrightarrow> mm.power i (x \<cdot>\<^bsub>j\<^esub> y) k \<le> mm.power i x k \<cdot>\<^bsub>j\<^esub> mm.power i y k"
  have "mm.power i (x \<cdot>\<^bsub>j\<^esub> y) (Suc k) = (x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> mm.power i (x \<cdot>\<^bsub>j\<^esub> y) k"
    by simp
  also have "\<dots> \<le> (x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (mm.power i x k \<cdot>\<^bsub>j\<^esub> mm.power i y k)"
    by (simp add: Suc.prems h local.qiq.psrpq.mult_isol)
  also have "\<dots> \<le> (x \<cdot>\<^bsub>i\<^esub> mm.power i x k) \<cdot>\<^bsub>j\<^esub> (y \<cdot>\<^bsub>i\<^esub> mm.power i y k)"
    by (simp add: Suc.prems local.tgqs.tgsdual.interchange)
  also have "\<dots> = mm.power i x (Suc k) \<cdot>\<^bsub>j\<^esub> mm.power i y (Suc k)"
    by simp
  finally show "mm.power i (x \<cdot>\<^bsub>j\<^esub> y) (Suc k) \<le> mm.power i x (Suc k) \<cdot>\<^bsub>j\<^esub> mm.power i y (Suc k)".
qed

lemma istar_oplax: "i < j \<Longrightarrow> istar i (x \<cdot>\<^bsub>j\<^esub> y) \<le> istar i x \<cdot>\<^bsub>j\<^esub> istar i y"
  by (simp add: local.tgqs.star_compj)

lemma istar_distli: "i < j \<Longrightarrow> x \<cdot>\<^bsub>i\<^esub> (istar j y) = (\<Squnion>k. x \<cdot>\<^bsub>i\<^esub> (mm.power j y k))"
  by (simp add: image_image local.qiq.Sup_distl local.istar_unfold)

lemma istar_distri: "i < j \<Longrightarrow> (istar j x) \<cdot>\<^bsub>i\<^esub> y = (\<Squnion>k. mm.power j x k \<cdot>\<^bsub>i\<^esub> y)"
  by (simp add: image_image local.qiq.Sup_distr local.istar_unfold)

lemma istar_distlj: "i < j \<Longrightarrow> x \<cdot>\<^bsub>j\<^esub> (istar i y) = (\<Squnion>k. x \<cdot>\<^bsub>j\<^esub> (mm.power i y k))"
  by (simp add: image_image local.Sup_distl local.istar_unfold)

lemma istar_distrj: "i < j \<Longrightarrow> (istar i x) \<cdot>\<^bsub>j\<^esub> y = (\<Squnion>k. mm.power i x k \<cdot>\<^bsub>j\<^esub> y)"
  by (simp add: image_image local.qiq.Sup_distr local.istar_unfold)

lemma istar_laxl_aux_var: "i < j \<Longrightarrow> do i x \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) k"
proof (induct k)
  case 0
  assume "i < j"
  have "do i x \<cdot>\<^bsub>i\<^esub> un j = do j (do i x) \<cdot>\<^bsub>i\<^esub> un j"
    by (simp add: "0" local.djdi)
  also have "\<dots> \<le> un j \<cdot>\<^bsub>i\<^esub> un j"
    by (simp add: local.qiq.nsrnq.mult_isor)
  finally have "do i x \<cdot>\<^bsub>i\<^esub> un j \<le> un j"
    by (simp add: local.dqidq.dqmsr.dom_subid_aux2)
  thus "do i x \<cdot>\<^bsub>i\<^esub> mm.power j y 0 \<le> mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) 0"
    by simp
next
  case (Suc k)
  fix k
  assume "i < j"
  assume h: "i < j \<Longrightarrow> do i x \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) k"
  have "do i x \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) = do i x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub>  mm.power j y k)"
    by simp
  also have "\<dots> = (do i x \<cdot>\<^bsub>j\<^esub> do i x) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> mm.power j y k)"
    using Suc.prems less_imp_add_positive by fastforce
  also have "\<dots>  \<le> (do i x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (do i x \<cdot>\<^bsub>i\<^esub> mm.power j y k)"
    by (simp add: Suc.prems local.interchange)
  also have "\<dots>  \<le> (do i x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) k"
    by (simp add: Suc.prems h local.qiq.psrpq.mult_isol)
  finally show "do i x \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) \<le> mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) (Suc k)"
    by simp
qed

lemma istar_laxl_var: 
  assumes "i < j"
  shows "do i x \<cdot>\<^bsub>i\<^esub> istar j y \<le> istar j (do i x \<cdot>\<^bsub>i\<^esub> y)"  
proof-
  have "do i x \<cdot>\<^bsub>i\<^esub> istar j y = (\<Squnion>k. do i x \<cdot>\<^bsub>i\<^esub> mm.power j y k)"
    by (simp add: image_image local.Sup_distl local.istar_unfold)
  also have "\<dots> \<le> (\<Squnion>k. mm.power j (do i x \<cdot>\<^bsub>i\<^esub> y) k)"
    by (simp add: assms local.SUP_mono' local.istar_laxl_aux_var)
  finally show ?thesis
    using local.istar_unfold by auto
qed

lemma istar_laxl_var2: "do i x \<cdot>\<^bsub>i\<^esub> istar (i + k + 1) y \<le> istar (i + k + 1) (do i x \<cdot>\<^bsub>i\<^esub> y)"
  using istar_laxl_var by force  

lemma istar_laxr_aux_var: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> cd i y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd i y) k"
proof (induct k)
  case 0 show ?case
    by (simp add: local.cdqicdq.coddual.dqmsr.dom_subid_aux2)
next
  case (Suc k)
  assume h0: "i < j"
  fix k
  assume h: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> cd i y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd i y) k"
  have "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> cd i y = (x \<cdot>\<^bsub>j\<^esub> mm.power j x k) \<cdot>\<^bsub>i\<^esub> (cd i y \<cdot>\<^bsub>j\<^esub> cd i y)"
    using h0 less_imp_add_positive by fastforce
  also have "\<dots>  \<le> (x \<cdot>\<^bsub>i\<^esub> cd i y) \<cdot>\<^bsub>j\<^esub> (mm.power j x k \<cdot>\<^bsub>i\<^esub> cd i y)"
    by (simp add: h0 local.tgqs.tgsdual.interchange)
  finally show "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> cd i y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd i y) (Suc k)"
    by (simp add: h h0 local.qiq.h_w2 local.qiq.psrpq.mult_isol)
qed
 
lemma istar_laxr_var: 
  assumes "i < j"
  shows "istar j x \<cdot>\<^bsub>i\<^esub> cd i y \<le> istar j (x \<cdot>\<^bsub>i\<^esub> cd i y)"
proof-
  have "istar j x \<cdot>\<^bsub>i\<^esub> cd i y = (\<Squnion>k. mm.power j x k \<cdot>\<^bsub>i\<^esub> cd i y)"
    using assms istar_distri by presburger
  also have "\<dots> \<le> (\<Squnion>k. mm.power j (x \<cdot>\<^bsub>i\<^esub> cd i y) k)"
    by (simp add: assms local.SUP_mono' local.istar_laxr_aux_var)
  finally show ?thesis
    by (simp add: local.istar_unfold)
qed

lemma istar_laxr_var2: "istar (i + k + 1) x \<cdot>\<^bsub>i\<^esub> cd i y \<le> istar (i + k + 1) (x \<cdot>\<^bsub>i\<^esub> cd i y)"
  using istar_laxr_var by force

lemma istar_prop:
  assumes "i < j"
  shows "istar j x \<cdot>\<^bsub>i\<^esub> istar j y = (\<Squnion>k l. mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y l)"
proof-
  have "istar j x \<cdot>\<^bsub>i\<^esub> istar j y = istar j x \<cdot>\<^bsub>i\<^esub> ( \<Squnion>k. mm.power j y k)"
    using local.istar_unfold by auto
  also have "\<dots> = (\<Squnion>l. istar j x \<cdot>\<^bsub>i\<^esub> mm.power j y l)"
    by (simp add: image_image local.Sup_distl)
  also have "\<dots> = (\<Squnion>l. (\<Squnion>k. mm.power j x k) \<cdot>\<^bsub>i\<^esub> mm.power j y l)"
    unfolding istar_def qiq.qstar_def by (simp add: full_SetCompr_eq)
  also have "\<dots> = (\<Squnion>l. (\<Squnion>k. mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y l))"
    using assms istar_distri local.istar_unfold by auto
  also have "\<dots> = (\<Squnion>k l. mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y l)"
    using local.SUP_commute by force
  finally show ?thesis.
qed

end

context strong_omega_quantale
begin

lemma istar_laxl_aux: "i < j \<Longrightarrow> do j x \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) k"
proof (induct k)
  case 0
  assume "i < j"
  have "do i x \<cdot>\<^bsub>i\<^esub> un j \<le> un j \<cdot>\<^bsub>i\<^esub> un j"
    using "0" local.dqidq.dqmsr.dom_subid_aux2 local.stgqs.stgsdual.idj_compi_eq by force
  thus "do j x \<cdot>\<^bsub>i\<^esub> mm.power j y 0 \<le> mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) 0"
    by (metis "0" local.do_subid local.mm.power.power_0 local.qiq.nsrnq.mult_isor local.stgqs.stgsdual.idj_compi_eq)
next
  case (Suc k)
  assume "i < j"
  fix k
  assume h: "i < j \<Longrightarrow> do j x \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) k"
  have "do j x \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) = do j x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub>  mm.power j y k)"
    by simp
  also have "\<dots> = (do j x \<cdot>\<^bsub>j\<^esub> do j x) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> mm.power j y k)"
    by simp
  also have "\<dots>  \<le> (do j x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (do j x \<cdot>\<^bsub>i\<^esub> mm.power j y k)"
    using Suc.prems local.interchange by blast
  also have "\<dots>  \<le> (do j x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) k"
    by (simp add: Suc.prems h local.qiq.psrpq.mult_isol)
  finally show "do j x \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) \<le> mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) (Suc k)"
    by simp
qed

lemma istar_laxl: 
  assumes "i < j"
  shows "do j x \<cdot>\<^bsub>i\<^esub> istar j y \<le> istar j (do j x \<cdot>\<^bsub>i\<^esub> y)" 
proof-
  have "do j x \<cdot>\<^bsub>i\<^esub> istar j y = (\<Squnion>k. do j x \<cdot>\<^bsub>i\<^esub> mm.power j y k)"
    using assms local.istar_distli by force
  also have "\<dots> \<le> (\<Squnion>k. mm.power j (do j x \<cdot>\<^bsub>i\<^esub> y) k)"
    by (simp add: assms istar_laxl_aux local.SUP_mono')
  finally show ?thesis
    by (simp add: local.istar_unfold)
qed

lemma istar_laxr_aux: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> cd j y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd j y) k"
proof (induct k)
  case 0 thus ?case
    by (metis local.cd_subid local.mm.power.power_0 local.qiq.psrpq.mult_isol local.stgqs.stgsdual.idj_compi_eq)
next
  case (Suc k)
  assume "i < j"
  fix k
  assume h: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> cd j y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd j y) k"
  have "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> cd j y = (x \<cdot>\<^bsub>j\<^esub>  mm.power j x k) \<cdot>\<^bsub>i\<^esub> cd j y"
    by simp
  also have "\<dots> = (x \<cdot>\<^bsub>j\<^esub> mm.power j x k) \<cdot>\<^bsub>i\<^esub> (cd j y \<cdot>\<^bsub>j\<^esub> cd j y)"
    by simp
  also have "\<dots>  \<le> (x \<cdot>\<^bsub>i\<^esub> cd j y) \<cdot>\<^bsub>j\<^esub> (mm.power j x k \<cdot>\<^bsub>i\<^esub> cd j y)"
    using Suc.prems local.interchange by blast
  also have "\<dots>  \<le>  (x \<cdot>\<^bsub>i\<^esub> cd j y) \<cdot>\<^bsub>j\<^esub> mm.power j (x  \<cdot>\<^bsub>i\<^esub> cd j y) k"
    by (simp add: Suc.prems h local.qiq.psrpq.mult_isol)
  finally show "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> cd j y \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> cd j y) (Suc k)"
    by simp
qed

lemma iqstar_laxr: 
  assumes "i < j"
  shows "istar j x \<cdot>\<^bsub>i\<^esub> cd j y \<le> istar j (x \<cdot>\<^bsub>i\<^esub> cd j y)"  
proof-
  have "istar j x \<cdot>\<^bsub>i\<^esub> cd j y = (\<Squnion>k. mm.power j x k \<cdot>\<^bsub>i\<^esub> cd j y)"
    using assms local.istar_distri by force
  also have "\<dots> \<le> (\<Squnion>k. mm.power j (x \<cdot>\<^bsub>i\<^esub> cd j y) k)"
    by (simp add: assms istar_laxr_aux local.SUP_mono')
  finally show ?thesis
    by (simp add: local.istar_unfold)
qed

lemma qstar1_aux: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> y) k"
proof (induct k)
  case 0
  then show ?case
    using local.stgqs.stgsdual.idj_compi_eq by force
next
  case (Suc k)
  assume "i < j"
 fix k
  assume h: "i < j \<Longrightarrow> mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y k \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> y) k" 
  have "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) = (x \<cdot>\<^bsub>j\<^esub> mm.power j x k) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> mm.power j y k)"
    by simp
  also have "\<dots> \<le> (x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (mm.power j x k \<cdot>\<^bsub>i\<^esub> mm.power j y k)"
    using Suc.prems local.interchange by force
  also have "\<dots> \<le> (x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> mm.power j (x \<cdot>\<^bsub>i\<^esub> y) k"
    by (simp add: Suc.prems h local.qiq.psrpq.mult_isol)
  also have "\<dots> = mm.power j (x \<cdot>\<^bsub>i\<^esub> y) (Suc k)"
    by simp
  finally show "mm.power j x (Suc k) \<cdot>\<^bsub>i\<^esub> mm.power j y (Suc k) \<le> mm.power j (x \<cdot>\<^bsub>i\<^esub> y) (Suc k)".
qed

end

end




