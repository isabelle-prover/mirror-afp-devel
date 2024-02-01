(* 
Title: 2-Quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>2-Quantales\<close>

theory Two_Quantale
  imports Quantales_Converse.Modal_Quantale Two_Kleene_Algebra

begin

class quantale0 = complete_lattice + monoid_mult0 +
  assumes Sup_distl0: "x \<cdot>\<^sub>0 \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot>\<^sub>0 y)" 
  assumes Sup_distr0: "\<Squnion>X \<cdot>\<^sub>0 y = (\<Squnion>x \<in> X. x \<cdot>\<^sub>0 y)"

sublocale quantale0 \<subseteq> q0q: unital_quantale "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ _ _ _ _ 
  apply unfold_locales using local.Sup_distr0 local.Sup_distl0 by auto

definition (in quantale0) "qstar0 = q0q.qstar"

lemma (in quantale0) qstar0_unfold: "qstar0 x = (\<Squnion>i. mm0.power x i)"
  by (simp add: local.q0q.qstar_def local.qstar0_def)

sublocale quantale0 \<subseteq> dq0s0: dioid0 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0"
  by unfold_locales (simp_all add: local.q0q.sup_distl)

sublocale quantale0 \<subseteq> dq0ka0: kleene_algebra0 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  "(\<cdot>\<^sub>0)" "1\<^sub>0" qstar0
  by unfold_locales (simp_all add: local.qstar0_def local.q0q.uwqlka.star_inductl local.q0q.uqka.star_inductr')

class domain_quantale0 = quantale0 + dom0_op +
  assumes dom0_absorb: "x \<le> dom\<^sub>0 x \<cdot>\<^sub>0 x"
  and dom0_local: "dom\<^sub>0 (x \<cdot>\<^sub>0 dom\<^sub>0 y) = dom\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and dom0_add: "dom\<^sub>0 (x \<squnion> y) = dom\<^sub>0 x \<squnion> dom\<^sub>0 y"
  and dom0_subid: "dom\<^sub>0 x \<le> 1\<^sub>0"
  and dom0_zero: "dom\<^sub>0 \<bottom> = \<bottom>"

sublocale domain_quantale0 \<subseteq> dq0dq: domain_quantale "dom\<^sub>0" "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ _ _ _ _
  by unfold_locales (simp_all add: local.dom0_absorb local.dom0_local local.dom0_add local.dom0_subid dom0_zero)

sublocale domain_quantale0 \<subseteq> dq0ds0: domain_semiring0 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  "(\<cdot>\<^sub>0)" "1\<^sub>0" "dom\<^sub>0"
  by unfold_locales (simp_all add: local.dom0_local local.dom0_add local.dom0_subid dom0_zero)

class codomain_quantale0 = quantale0 + cod0_op +
  assumes cod0_absorb: "x \<le> x \<cdot>\<^sub>0 cod\<^sub>0 x" 
  and cod0_local: "cod\<^sub>0 (cod\<^sub>0 x \<cdot>\<^sub>0 y) = cod\<^sub>0 (x \<cdot>\<^sub>0 y)"
  and cod0_add: "cod\<^sub>0 (x \<squnion> y) = cod\<^sub>0 x \<squnion> cod\<^sub>0 y"
  and cod0_subid: "cod\<^sub>0 x \<le> 1\<^sub>0"
  and cod0_zero: "cod\<^sub>0 \<bottom> = \<bottom>"

sublocale codomain_quantale0 \<subseteq> cdq0cdq: codomain_quantale "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ _ _ _ _ "cod\<^sub>0"
  by (unfold_locales, simp_all add: local.cod0_absorb local.cod0_local local.cod0_add local.cod0_subid cod0_zero)

sublocale codomain_quantale0 \<subseteq> cdq0dcs0: codomain_semiring0 "cod\<^sub>0" "(\<squnion>)"  "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0"
  by (unfold_locales, simp_all add: local.cod0_absorb local.cod0_local local.cod0_add local.cod0_subid cod0_zero)

class modal_quantale0 = domain_quantale0 + codomain_quantale0 +
  assumes dc_compat: "dom\<^sub>0 (cod\<^sub>0 x) = cod\<^sub>0 x" 
  and cd_compat: "cod\<^sub>0 (dom\<^sub>0 x) = dom\<^sub>0 x" 

sublocale modal_quantale0 \<subseteq> mq0mq: dc_modal_quantale "1\<^sub>0" "(\<cdot>\<^sub>0)" _ _ _ _ _ _ _ _  "cod\<^sub>0" "dom\<^sub>0"
  by (unfold_locales, simp_all add: dc_compat cd_compat)

sublocale modal_quantale0 \<subseteq> mq0mka: modal_kleene_algebra0 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0" qstar0 "cod\<^sub>0" "dom\<^sub>0"
  by unfold_locales simp_all

sublocale modal_quantale0 \<subseteq> mq0dual: modal_quantale0 "dom\<^sub>0" _ _ _ _ _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>0 x" _ "cod\<^sub>0"
  by unfold_locales (simp_all add: local.cdq0cdq.coddual.Sup_distl local.Sup_distl0)


class quantale1 = complete_lattice + monoid_mult1 +
  assumes Sup_distl1: "x \<cdot>\<^sub>1 \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot>\<^sub>1 y)" 
  assumes Sup_distr1: "\<Squnion>X \<cdot>\<^sub>1 y = (\<Squnion>x \<in> X. x \<cdot>\<^sub>1 y)"

sublocale quantale1 \<subseteq> q1q: unital_quantale "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ _ _ _ _ 
  by (unfold_locales, auto simp: local.Sup_distl1 local.Sup_distr1)

definition (in quantale1) "qstar1 = q1q.qstar"

lemma (in quantale1) qstar1_unfold: "qstar1 x = (\<Squnion>i. mm1.power x i)"
  by (simp add: local.q1q.qstar_def local.qstar1_def)

sublocale quantale1 \<subseteq> dq1s1: dioid1 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>1)" "1\<^sub>1"
  by unfold_locales (simp_all add: local.q1q.wswq.distrib_left)

sublocale quantale1 \<subseteq> dq0ka1: kleene_algebra1 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>1)" "1\<^sub>1" qstar1
  by unfold_locales (simp_all add: local.qstar1_def local.q1q.uwqlka.star_inductl local.q1q.uqka.star_inductr')

class domain_quantale1 = quantale1 + dom1_op +
  assumes dom1_absorb: "x \<le> dom\<^sub>1 x \<cdot>\<^sub>1 x"
  and dom1_local: "dom\<^sub>1 (x \<cdot>\<^sub>1 dom\<^sub>1 y) = dom\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and dom1_add: "dom\<^sub>1 (x \<squnion> y) = dom\<^sub>1 x \<squnion> dom\<^sub>1 y"
  and dom1_subid: "dom\<^sub>1 x \<le> 1\<^sub>1"
  and dom1_zero: "dom\<^sub>1 \<bottom> = \<bottom>"

sublocale domain_quantale1 \<subseteq> dq1dq: domain_quantale "dom\<^sub>1" "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ _ _ _ _
  by (unfold_locales, simp_all add: local.dom1_absorb local.dom1_local local.dom1_add local.dom1_subid dom1_zero)

sublocale domain_quantale1 \<subseteq> dq1ds1: domain_semiring1 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  "(\<cdot>\<^sub>1)" "1\<^sub>1" "dom\<^sub>1"
  by (unfold_locales, simp_all add: local.dom1_local local.dom1_add local.dom1_subid dom1_zero)
 
class codomain_quantale1 = quantale1 + cod1_op +
  assumes cod1_absorb: "x \<le> x \<cdot>\<^sub>1 cod\<^sub>1 x" 
  and cod1_local: "cod\<^sub>1 (cod\<^sub>1 x \<cdot>\<^sub>1 y) = cod\<^sub>1 (x \<cdot>\<^sub>1 y)"
  and cod1_add: "cod\<^sub>1 (x \<squnion> y) = cod\<^sub>1 x \<squnion> cod\<^sub>1 y"
  and cod1_subid: "cod\<^sub>1 x \<le> 1\<^sub>1"
  and cod1_zero: "cod\<^sub>1 \<bottom> = \<bottom>"

sublocale codomain_quantale1 \<subseteq> cdq1cdq: codomain_quantale "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ _ _ _ _ "cod\<^sub>1"
  by (unfold_locales, simp_all add: local.cod1_absorb local.cod1_local local.cod1_add local.cod1_subid cod1_zero)

sublocale codomain_quantale1 \<subseteq> cdq1dcs1: codomain_semiring1 "cod\<^sub>1" "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>1)" "1\<^sub>1"
  by (unfold_locales, simp_all add: local.cod1_absorb local.cod1_local local.cod1_add local.cod1_subid cod1_zero)

class modal_quantale1 = domain_quantale1 + codomain_quantale1 +
  assumes dc_compat: "dom\<^sub>1 (cod\<^sub>1 x) = cod\<^sub>1 x" 
  and cd_compat: "cod\<^sub>1 (dom\<^sub>1 x) = dom\<^sub>1 x" 

sublocale modal_quantale1 \<subseteq> mq1mq: dc_modal_quantale "1\<^sub>1" "(\<cdot>\<^sub>1)" _ _ _ _ _ _ _ _ "cod\<^sub>1" "dom\<^sub>1"
  by (unfold_locales, simp_all add: local.dc_compat local.cd_compat)

sublocale modal_quantale1 \<subseteq> mq1mka: modal_kleene_algebra1 "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  "(\<cdot>\<^sub>1)" "1\<^sub>1" qstar1 "cod\<^sub>1" "dom\<^sub>1"
  by unfold_locales simp_all

sublocale modal_quantale1 \<subseteq> mq1dual: modal_quantale1 "dom\<^sub>1" _ _ _ _ _ _ _ _ "\<lambda>x y. y \<cdot>\<^sub>1 x" _ "cod\<^sub>1"
  by unfold_locales (simp_all add: local.Sup_distr1 local.Sup_distl1)

class two_quantale = modal_quantale0 + modal_quantale1 +
  assumes interchange: "(w \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (w \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 z)"
  and d1_hom: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) \<le> dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_hom: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) \<le> cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"
  and d0_weak_hom: "dom\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
  and c0_weak_hom: "cod\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  and d1d0 [simp]: "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"

class strong_two_quantale = two_quantale +
  assumes d1_strong_hom [simp]: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) = dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_strong_hom [simp]: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"

sublocale two_quantale \<subseteq> tgqs: two_semiring "cod\<^sub>0" "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0" "dom\<^sub>0"  "cod\<^sub>1" "(\<cdot>\<^sub>1)" "1\<^sub>1" "dom\<^sub>1"
  by (unfold_locales, simp_all add: local.mq0mq.mqs.msrdual.cd_compat local.mq0mq.mqs.msrdual.dc_compat local.dc_compat local.cd_compat local.interchange local.c0_weak_hom local.c1_hom local.d0_weak_hom local.d1_hom)

sublocale strong_two_quantale \<subseteq> stgqs: strong_two_semiring "cod\<^sub>0" "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0" "dom\<^sub>0"  "cod\<^sub>1" "(\<cdot>\<^sub>1)" "1\<^sub>1" "dom\<^sub>1"
  by unfold_locales simp_all

sublocale two_quantale \<subseteq> tgqs: two_kleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>"  "(\<cdot>\<^sub>0)" "1\<^sub>0" qstar0 "(\<cdot>\<^sub>1)"  "1\<^sub>1" qstar1 "cod\<^sub>0" "dom\<^sub>0" "cod\<^sub>1" "dom\<^sub>1" ..

sublocale strong_two_quantale \<subseteq> tgqs: strong_two_kleene_algebra "(\<squnion>)" "(\<le>)" "(<)" "\<bottom>" "(\<cdot>\<^sub>0)" "1\<^sub>0" qstar0 "(\<cdot>\<^sub>1)"  "1\<^sub>1" qstar1 "cod\<^sub>0" "dom\<^sub>0" "cod\<^sub>1" "dom\<^sub>1" ..

lemma (in strong_two_quantale) id0_le_id1: "1\<^sub>0 = 1\<^sub>1"
  (* nitpick [expect = genuine] *)
  oops

context two_quantale
begin

lemma qstar0_aux: "mm0.power (x \<cdot>\<^sub>1 y) i \<le> mm0.power x i \<cdot>\<^sub>1 mm0.power y i"
proof (induct i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  fix i 
  assume h: "mm0.power (x \<cdot>\<^sub>1 y) i \<le> mm0.power x i \<cdot>\<^sub>1 mm0.power y i"
  have "mm0.power (x \<cdot>\<^sub>1 y) (Suc i) = (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 mm0.power (x \<cdot>\<^sub>1 y) i"
    by simp
  also have "\<dots> \<le> (x \<cdot>\<^sub>1 y) \<cdot>\<^sub>0 (mm0.power x i \<cdot>\<^sub>1 mm0.power y i)"
    by (simp add: h local.q0q.psrpq.mult_isol)
  also have "\<dots> \<le> (x \<cdot>\<^sub>0 mm0.power x i) \<cdot>\<^sub>1 (y \<cdot>\<^sub>0 mm0.power y i)"
    by (simp add: local.interchange)
  also have "\<dots> = mm0.power x (Suc i) \<cdot>\<^sub>1 mm0.power y (Suc i)"
    by simp
  finally show "mm0.power (x \<cdot>\<^sub>1 y) (Suc i) \<le> mm0.power x (Suc i) \<cdot>\<^sub>1 mm0.power y (Suc i)".
qed

lemma qstar0_oplax: "qstar0 (x \<cdot>\<^sub>1 y) \<le> qstar0 x \<cdot>\<^sub>1 qstar0 y"
  by (simp add: local.tgqs.star0_comp1)

lemma qstar1_distl0: "x \<cdot>\<^sub>0 (qstar1 y) = (\<Squnion>i. x \<cdot>\<^sub>0 mm1.power y i)"
  by (simp add: image_image local.Sup_distl0 local.qstar1_unfold)

lemma qstar1_distr0: "(qstar1 x) \<cdot>\<^sub>0 y = (\<Squnion>i. mm1.power x i \<cdot>\<^sub>0 y)"
  by (simp add: image_image local.Sup_distr0 local.qstar1_unfold)

lemma qstar0_distl1: "x \<cdot>\<^sub>1 (qstar0 y) = (\<Squnion>i. x \<cdot>\<^sub>1 mm0.power y i)"
  by (simp add: image_image local.Sup_distl1 local.qstar0_unfold)

lemma qstar0_distr1: "(qstar0 x) \<cdot>\<^sub>1 y = (\<Squnion>i. mm0.power x i \<cdot>\<^sub>1 y)"
  by (smt (verit, best) image_image local.SUP_cong local.Sup_distr1 local.qstar0_unfold)

lemma star1_laxl_aux_var: "dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) i"
proof (induct i)
  case 0
  have "dom\<^sub>0 x \<cdot>\<^sub>0 1\<^sub>1 = dom\<^sub>1 (dom\<^sub>0 x) \<cdot>\<^sub>0 1\<^sub>1"
    by simp
  also have "\<dots> \<le> 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
    using local.dom1_subid local.q0q.nsrnq.mult_isor by blast
  finally have "dom\<^sub>0 x \<cdot>\<^sub>0 1\<^sub>1 \<le> 1\<^sub>1"
    by (simp add: local.dq0dq.dqmsr.dom_subid_aux2)
  thus "dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y 0 \<le> mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) 0"
    by simp
next
  case (Suc i)
  fix i
  assume h: "dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) i"
  have "dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y (Suc i) = dom\<^sub>0 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1  mm1.power y i)"
    by simp
  also have "\<dots> = (dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 mm1.power y i)"
    by simp
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y i)"
    using local.interchange by blast
  also have "\<dots> \<le> (dom\<^sub>0 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) i"
    by (simp add: h local.q1q.psrpq.mult_isol)
  finally show "dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y (Suc i) \<le> mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) (Suc i)"
    by simp
qed
 
lemma star1_laxl_var: "dom\<^sub>0 x \<cdot>\<^sub>0 qstar1 y \<le> qstar1 (dom\<^sub>0 x \<cdot>\<^sub>0 y)"  
proof-
  have "dom\<^sub>0 x \<cdot>\<^sub>0 qstar1 y = (\<Squnion>i. dom\<^sub>0 x \<cdot>\<^sub>0 mm1.power y i)"
    using local.qstar1_distl0 by auto
  also have "\<dots> \<le> (\<Squnion>i. mm1.power (dom\<^sub>0 x \<cdot>\<^sub>0 y) i)"
    by (simp add: local.SUP_mono' local.star1_laxl_aux_var)
  finally show ?thesis
    by (simp add: local.qstar1_unfold)
qed

lemma star1_laxr_aux_var: "mm1.power x i \<cdot>\<^sub>0 cod\<^sub>0 y \<le> mm1.power (x \<cdot>\<^sub>0 cod\<^sub>0 y) i"
proof (induct i)
  case 0 show ?case
    by (simp add: local.cdq0cdq.coddual.dqmsr.dom_subid_aux2)
next
  case (Suc i)
  fix i
  assume h: "mm1.power x i \<cdot>\<^sub>0 cod\<^sub>0 y \<le> mm1.power (x \<cdot>\<^sub>0 cod\<^sub>0 y) i"
  have "mm1.power x (Suc i) \<cdot>\<^sub>0 cod\<^sub>0 y = (x \<cdot>\<^sub>1 mm1.power x i ) \<cdot>\<^sub>0 (cod\<^sub>0 y \<cdot>\<^sub>1 cod\<^sub>0 y)"
    by simp
  also have "\<dots>  \<le> (x \<cdot>\<^sub>0 cod\<^sub>0 y) \<cdot>\<^sub>1 (mm1.power x i \<cdot>\<^sub>0 cod\<^sub>0 y)"
    by (simp add: local.tgqs.tgsdual.d0_comp1)
  finally show "mm1.power x (Suc i) \<cdot>\<^sub>0 cod\<^sub>0 y \<le> mm1.power (x \<cdot>\<^sub>0 cod\<^sub>0 y) (Suc i)"
    by (simp add: h local.q0q.h_w2 local.q1q.psrpq.mult_isol)
qed
 
lemma qstar1_laxr_var: "qstar1 x \<cdot>\<^sub>0 cod\<^sub>0 y \<le> qstar1 (x \<cdot>\<^sub>0 cod\<^sub>0 y)"  
proof-
  have "qstar1 x \<cdot>\<^sub>0 cod\<^sub>0 y = (\<Squnion>i. mm1.power x i \<cdot>\<^sub>0 cod\<^sub>0 y)"
    using local.qstar1_distr0 by auto
  also have "\<dots> \<le> (\<Squnion>i. mm1.power (x \<cdot>\<^sub>0 cod\<^sub>0 y) i)"
    by (simp add: local.SUP_mono' local.star1_laxr_aux_var)
  finally show ?thesis
    by (simp add: local.qstar1_unfold)
qed

lemma qstar_1_power: "qstar1 x \<cdot>\<^sub>0 qstar1 y = (\<Squnion>i j. mm1.power x i \<cdot>\<^sub>0 mm1.power y j)"
proof-
  have "qstar1 x \<cdot>\<^sub>0 qstar1 y = qstar1 x \<cdot>\<^sub>0( \<Squnion>j. mm1.power y j)"
    using bot_nat_0.extremum local.qstar1_unfold by presburger
  also have "\<dots> = (\<Squnion>j. qstar1 x \<cdot>\<^sub>0 mm1.power y j)"
    using calculation local.qstar1_distl0 by auto
  also have "\<dots> = (\<Squnion>j. (\<Squnion>i. mm1.power x i) \<cdot>\<^sub>0 mm1.power y j)"
    unfolding qstar1_def q1q.qstar_def by (simp add: full_SetCompr_eq)
  also have "\<dots> = (\<Squnion>i j. mm1.power x i \<cdot>\<^sub>0 mm1.power y j)"
    by (smt (verit, ccfv_SIG) Sup.SUP_cong calculation local.qstar1_distl0 local.qstar1_distr0)
  finally show ?thesis.
qed

end

context strong_two_quantale
begin

lemma star1_laxl_aux: "dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) i"
proof (induct i)
  case 0
  have "dom\<^sub>1 x \<cdot>\<^sub>0 1\<^sub>1 \<le> 1\<^sub>1 \<cdot>\<^sub>0 1\<^sub>1"
    using local.dom1_subid local.q0q.nsrnq.mult_isor by blast
  thus "dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y 0 \<le> mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) 0"
    by simp
next
  case (Suc i)
  fix i
  assume h: "dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) i"
  have "dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y (Suc i) = dom\<^sub>1 x \<cdot>\<^sub>0 (y \<cdot>\<^sub>1  mm1.power y i)"
    by simp
  also have "\<dots> = (dom\<^sub>1 x \<cdot>\<^sub>1 dom\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 mm1.power y i)"
    by simp
  also have "\<dots>  \<le> (dom\<^sub>1 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y i)"
    using local.interchange by blast
  also have "\<dots>  \<le> (dom\<^sub>1 x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) i"
    by (simp add: h local.q1q.psrpq.mult_isol)
  finally show "dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y (Suc i) \<le> mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) (Suc i)"
    by simp
qed

lemma star1_laxl: "dom\<^sub>1 x \<cdot>\<^sub>0 qstar1 y \<le> qstar1 (dom\<^sub>1 x \<cdot>\<^sub>0 y)" 
proof-
  have "dom\<^sub>1 x \<cdot>\<^sub>0 qstar1 y = (\<Squnion>i. dom\<^sub>1 x \<cdot>\<^sub>0 mm1.power y i)"
    using local.qstar1_distl0 by auto
  also have "\<dots> \<le> (\<Squnion>i. mm1.power (dom\<^sub>1 x \<cdot>\<^sub>0 y) i)"
    by (simp add: local.SUP_mono' local.star1_laxl_aux)
  finally show ?thesis
    by (simp add: local.qstar1_unfold)
qed

lemma star1_laxr_aux: "mm1.power x i \<cdot>\<^sub>0 cod\<^sub>1 y \<le> mm1.power (x \<cdot>\<^sub>0 cod\<^sub>1 y) i"
  apply (induct i)
   apply (metis local.cod1_subid local.mm1.power.power_0 local.q0q.psrpq.mult_isol local.stgqs.stgsdual.id1_comp0_eq)
  by (smt (verit, ccfv_SIG) local.dual_order.trans local.q1q.psrpq.mult_isol local.tgqs.tgsdual.d1_comp1 power.power.power_Suc)

lemma qstar1_laxr: "qstar1 x \<cdot>\<^sub>0 cod\<^sub>1 y \<le> qstar1 (x \<cdot>\<^sub>0 cod\<^sub>1 y)"  
proof-
  have "qstar1 x \<cdot>\<^sub>0 cod\<^sub>1 y = (\<Squnion>i. mm1.power x i \<cdot>\<^sub>0 cod\<^sub>1 y)"
    using local.qstar1_distr0 by auto
  also have "\<dots> \<le> (\<Squnion>i. mm1.power (x \<cdot>\<^sub>0 cod\<^sub>1 y) i)"
    by (simp add: local.SUP_mono' local.star1_laxr_aux)
  finally show ?thesis
    by (simp add: local.qstar1_unfold)
qed

lemma qstar1_aux: "mm1.power x i \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (x \<cdot>\<^sub>0 y) i"
proof (induct i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
 fix i 
  assume h: "mm1.power x i \<cdot>\<^sub>0 mm1.power y i \<le> mm1.power (x \<cdot>\<^sub>0 y) i" 
  have "mm1.power x (Suc i) \<cdot>\<^sub>0 mm1.power y (Suc i) = (x \<cdot>\<^sub>1 mm1.power x i) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 mm1.power y i)"
    by simp
  also have "\<dots> \<le> (x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (mm1.power x i \<cdot>\<^sub>0 mm1.power y i)"
    using local.interchange by force
  also have "\<dots> \<le> (x \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 mm1.power (x \<cdot>\<^sub>0 y) i"
    by (simp add: h local.q1q.psrpq.mult_isol)
  also have "\<dots> = mm1.power (x \<cdot>\<^sub>0 y) (Suc i)"
    by simp
  finally show "mm1.power x (Suc i) \<cdot>\<^sub>0 mm1.power y (Suc i) \<le> mm1.power (x \<cdot>\<^sub>0 y) (Suc i)".
qed

lemma "qstar1 x \<cdot>\<^sub>0 qstar1 y \<le> qstar0 (x \<cdot>\<^sub>1 y)"
  (* no proof, no counterexample *)
  oops

lemma "qstar1 x \<cdot>\<^sub>0 qstar1 y \<le> qstar1 (x \<cdot>\<^sub>1 y)"
  (* no proof, no counterexample *)
  oops

lemma "qstar1 (x \<cdot>\<^sub>1 y) \<le> qstar1 x \<cdot>\<^sub>0 qstar1 y"
  (* no proof, no counterexample *)
  oops

lemma "qstar1 x \<cdot>\<^sub>0 qstar1 y \<le> qstar1 (x \<cdot>\<^sub>0 y)"
  (* no proof, no counterexample *)
  oops

lemma "qstar1 (x \<cdot>\<^sub>0 y) \<le> qstar1 x \<cdot>\<^sub>0 qstar1 y"
  (* no proof, no counterexample *)
  oops

lemma "qstar0 x \<cdot>\<^sub>1 qstar0 y \<le> qstar0 (x \<cdot>\<^sub>0 y)"
  (* no proof, no counterexample *)
  oops

end

lemma (in strong_two_kleene_algebra) "qstar0 x \<cdot>\<^sub>1 qstar0 y \<le> qstar0 (x \<cdot>\<^sub>1 y)"
  (* no proof, no counterexample *)
  oops

lemma (in strong_two_kleene_algebra) "qstar0 (x \<cdot>\<^sub>1 y) \<le> qstar0 x \<cdot>\<^sub>1 qstar0 y"
  (* no proof, no counterexample *)
  oops

class two_quantale_lmcs = modal_quantale0 + modal_quantale1 +
  assumes interchange: "(w \<cdot>\<^sub>1 x) \<cdot>\<^sub>0 (y \<cdot>\<^sub>1 z) \<le> (w \<cdot>\<^sub>0 y) \<cdot>\<^sub>1 (x \<cdot>\<^sub>0 z)"
  and d1_hom: "dom\<^sub>1 (x \<cdot>\<^sub>0 y) = dom\<^sub>1 x \<cdot>\<^sub>0 dom\<^sub>1 y"
  and c1_hom: "cod\<^sub>1 (x \<cdot>\<^sub>0 y) = cod\<^sub>1 x \<cdot>\<^sub>0 cod\<^sub>1 y"
  and d1d0 [simp]: "dom\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
 and c1d0 [simp]: "cod\<^sub>1 (dom\<^sub>0 x) = dom\<^sub>0 x"
 and d1c0 [simp]: "dom\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
 and c1c0 [simp]: "cod\<^sub>1 (cod\<^sub>0 x) = cod\<^sub>0 x"
  and d0d1 [simp]: "dom\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 x"
 and c0d1 [simp]: "cod\<^sub>0 (dom\<^sub>1 x) = dom\<^sub>0 x"
 and d0c1 [simp]: "dom\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>0 x"
 and c0c1 [simp]: "cod\<^sub>0 (cod\<^sub>1 x) = cod\<^sub>0 x"

begin

lemma "dom\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> dom\<^sub>0 x \<cdot>\<^sub>1 dom\<^sub>0 y"
  (* no proof no counterexample *)
  oops

lemma  "cod\<^sub>0 (x \<cdot>\<^sub>1 y) \<le> cod\<^sub>0 x \<cdot>\<^sub>1 cod\<^sub>0 y"
  (* no proof no counterexample *)
  oops

end

end



