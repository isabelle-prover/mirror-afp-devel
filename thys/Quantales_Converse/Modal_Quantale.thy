(*
Title: Modal quantales
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Modal quantales\<close>

theory Modal_Quantale
  imports Quantales.Quantale_Star Modal_Kleene_Algebra_Var KAD.Modal_Kleene_Algebra

begin

subsection \<open>Simplified modal semirings and Kleene algebras\<close>

text \<open>The previous formalisation of modal Kleene algebra in the AFP adds two compatibility axioms between domain and codomain
when combining an antidomain semiring with an antirange semiring. But these are unnecessary. They are derivable from the other
axioms. Thus I provide a simpler axiomatisation that should eventually replace the one in the AFP.\<close>

class modal_semiring_simp = antidomain_semiring + antirange_semiring

lemma (in modal_semiring_simp) dr_compat [simp]: "d (r x) = r x"
proof-
  have a: "ar x \<cdot> d (r x) = 0"
    using local.ads_d_def local.ars_r_def local.dpdz.dom_weakly_local by auto
  have "r x \<cdot> d (r x) \<cdot> ar x \<le> r x \<cdot> ar x"
    by (simp add: local.a_subid_aux2 local.ads_d_def local.mult_isor)
  hence b: "r x \<cdot> d (r x) \<cdot> ar x = 0"
    by (simp add: local.ardual.am2 local.ars_r_def local.join.bot_unique)
  have "d (r x) = (ar x + r x) \<cdot> d (r x)"
    using local.add_comm local.ardual.ans3 local.ars_r_def local.mult_1_left by presburger
  also have "\<dots> = ar x \<cdot> d (r x) + r x \<cdot> d (r x)"
    by simp
  also have "\<dots> = r x \<cdot> d (r x)"
    by (simp add: a)
  also have "\<dots> = r x \<cdot> d (r x) \<cdot> (ar x + r x)"
    using local.add_comm local.ardual.ans3 local.ars_r_def by auto
  also have "\<dots> = r x \<cdot> d (r x) \<cdot> ar x + r x \<cdot> d (r x) \<cdot> r x"
    by simp
  also have "\<dots> = r x \<cdot> d (r x) \<cdot> r x"
    using b by auto
  also have "\<dots> = r x"
    by (metis local.ads_d_def local.am3 local.ardual.a_mult_idem local.ars_r_def local.ds.ddual.mult_assoc)
  finally show ?thesis
    by simp
qed

lemma (in modal_semiring_simp) rd_compat [simp]: "r (d x) = d x"
  by (smt (verit) local.a_mult_idem local.ads_d_def local.am2 local.ardual.dpdz.dom_weakly_local local.ars_r_def local.dr_compat local.kat_3_equiv')

subclass (in modal_semiring_simp) modal_semiring
  apply unfold_locales by simp_all

class modal_kleene_algebra_simp = modal_semiring_simp + kleene_algebra

subclass (in modal_kleene_algebra_simp) modal_kleene_algebra..


subsection \<open>Domain quantales\<close>

class domain_quantale = unital_quantale + domain_op +
  assumes dom_absorb: "x \<le> dom x \<cdot> x"
  and dom_local: "dom (x \<cdot> dom y) = dom (x \<cdot> y)"
  and dom_add: "dom (x \<squnion> y) = dom x \<squnion> dom y"
  and dom_subid: "dom x \<le> 1"
  and dom_zero [simp]: "dom \<bottom> = \<bottom>"

text \<open>The definition is that of a domain semiring. I cannot extend the quantale class with respect to domain semirings
because of different operations are used for addition/sup. The following sublocale statement brings all those properties into scope.\<close>

sublocale domain_quantale \<subseteq> dqmsr: domain_semiring "(\<squnion>)" "(\<cdot>)" 1 \<bottom> dom "(\<le>)" "(<)"
  by unfold_locales (simp_all add: dom_add dom_local dom_absorb sup.absorb2 dom_subid)

sublocale domain_quantale \<subseteq> dqmka: domain_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom>  dom "(\<le>)" "(<)" qstar..

typedef (overloaded)  'a d_element = "{x :: 'a :: domain_quantale. dom x = x}"
  using dqmsr.dom_one by blast

setup_lifting type_definition_d_element

instantiation d_element :: (domain_quantale) bounded_lattice

begin

lift_definition less_eq_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> bool" is "(<)" .

lift_definition bot_d_element :: "'a d_element" is \<bottom>
  by simp

lift_definition top_d_element :: "'a d_element" is 1
  by simp

lift_definition inf_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> 'a d_element" is "(\<cdot>)"
  by (metis dqmsr.dom_mult_closed)

lift_definition sup_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> 'a d_element" is "(\<squnion>)"
  by simp

instance
  apply (standard; transfer)
             apply (simp_all add: less_le_not_le)
     apply (metis dqmsr.dom_subid_aux2'')
    apply (metis dqmsr.dom_subid_aux1'')
   apply (metis dqmsr.dom_glb_eq)
  by (metis dqmsr.dom_subid)

end

instance d_element :: (domain_quantale) distrib_lattice
  by (standard, transfer, metis dqmsr.dom_distrib)

context domain_quantale
begin

lemma dom_top [simp]: "dom \<top> = 1"
proof-
  have "1 \<le> \<top>"
    by simp
  hence "dom 1 \<le> dom \<top>"
    using local.dqmsr.d_iso by blast
  thus ?thesis
    by (simp add: local.dual_order.antisym)
qed

lemma dom_top2: "x \<cdot> \<top> \<le> dom x \<cdot> \<top>"
proof-
  have "x \<cdot> \<top> = dom x \<cdot> x \<cdot> \<top>"
    by simp
  also have "\<dots> \<le> dom x \<cdot> \<top> \<cdot> \<top>"
    using local.dqmsr.d_restrict_iff_1 local.top_greatest local.top_times_top mult_assoc by presburger
  finally show ?thesis
    by (simp add: local.mult.semigroup_axioms semigroup.assoc)
qed

lemma weak_twisted: "x \<cdot> dom y \<le> dom (x \<cdot> y) \<cdot> x"
  using local.dqmsr.fd_def local.dqmsr.fdemodalisation2 local.eq_refl by blast

lemma dom_meet: "dom x \<cdot> dom y = dom x \<sqinter> dom y"
  apply (rule order.antisym)
   apply (simp add: local.dqmsr.dom_subid_aux2 local.dqmsr.dom_subid_aux2'')
  by (smt (z3) local.dom_absorb local.dqmsr.dom_iso local.dqmsr.dom_subid_aux2 local.dqmsr.dsg3 local.dqmsr.dsg4 local.dual_order.antisym local.inf.cobounded1 local.inf.cobounded2 local.psrpq.mult_isol_var)

lemma dom_meet_pres: "dom (dom x \<sqinter> dom y) = dom x \<sqinter> dom y"
  using dom_meet local.dqmsr.dom_mult_closed by presburger

lemma dom_meet_distl: "dom x \<cdot> (y \<sqinter> z) = (dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)"
proof-
  have a: "dom x \<cdot> (y \<sqinter> z) \<le> (dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)"
    using local.mult_isol by force
  have "(dom x \<cdot> y) \<sqinter> (dom x \<cdot> z) = dom ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)) \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    by simp
  also have "\<dots> \<le> dom ((dom x \<cdot> y)) \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    using calculation local.dqmsr.dom_iso local.dqmsr.dom_llp2 local.inf.cobounded1 by presburger
  also have "\<dots> \<le> dom x \<cdot> ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z))"
    by (metis local.dqmsr.domain_1'' local.dqmsr.domain_invol local.mult_isor)
  also have "\<dots> \<le> dom x \<cdot> (y \<sqinter> z)"
    by (meson local.dqmsr.dom_subid_aux2 local.inf_mono local.order_refl local.psrpq.mult_isol_var)
  finally show ?thesis
    using a local.dual_order.antisym by blast
qed

lemma dom_meet_approx: "dom ((dom x \<cdot> y) \<sqinter> (dom x \<cdot> z)) \<le> dom x"
  by (metis dom_meet_distl local.dqmsr.domain_1'' local.dqmsr.domain_invol)

lemma dom_inf_pres_aux: "Y \<noteq> {} \<Longrightarrow> dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> dom x"
proof-
  assume "Y \<noteq> {}"
  have "\<forall>z\<in>Y. dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> dom (dom x \<cdot> z)"
    by (meson local.INF_lower local.dqmsr.dom_iso)
  hence "\<forall>z\<in>Y. dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> dom x \<cdot> dom z"
    by fastforce
  hence "\<forall>z\<in>Y. dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> dom x"
    using dom_meet by fastforce
  thus "dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> dom x"
    using \<open>Y \<noteq> {}\<close> by blast
qed

lemma dom_inf_pres_aux2: "(\<Sqinter>y \<in> Y. dom x \<cdot> y) \<le> \<Sqinter>Y"
  by (simp add: local.INF_lower2 local.dqmsr.dom_subid_aux2 local.le_Inf_iff)

lemma dom_inf_pres: "Y \<noteq> {} \<Longrightarrow> dom x \<cdot> (\<Sqinter>Y) = (\<Sqinter>y \<in> Y. dom x \<cdot> y)"
proof-
  assume hyp: "Y \<noteq> {}"
  have a: "dom x \<cdot> (\<Sqinter>Y) \<le> (\<Sqinter>y \<in> Y. dom x \<cdot> y)"
    by (simp add: Setcompr_eq_image local.Inf_subdistl)
  have "(\<Sqinter>y \<in> Y. dom x \<cdot> y) = dom (\<Sqinter>y \<in> Y. dom x \<cdot> y) \<cdot> (\<Sqinter>y \<in> Y. dom x \<cdot> y)"
    by simp
  also have "\<dots> \<le> dom x \<cdot> (\<Sqinter>y \<in> Y. dom x \<cdot> y)"
    using dom_inf_pres_aux hyp local.mult_isor by blast
  also have "\<dots> \<le> dom x \<cdot> \<Sqinter>Y"
    by (simp add: dom_inf_pres_aux2 local.psrpq.mult_isol_var)
  finally show ?thesis
    using a order.antisym by blast
qed

lemma "dom (\<Sqinter>X) \<le> \<Sqinter> (dom ` X)"
  by (simp add: local.INF_greatest local.Inf_lower local.dqmsr.dom_iso)

text \<open>The domain operation need not preserve arbitrary sups, though this property holds, for instance,
in quantales of binary relations. I do not aim at a stronger axiomatisation in this theory.\<close>

lemma dom_top_pres: "(x \<le> dom y \<cdot> x) = (x \<le> dom y \<cdot> \<top>)"
  apply standard
   apply (meson local.dqmsr.ddual.mult_isol_var local.dual_order.eq_iff local.dual_order.trans local.top_greatest)
  using local.dqmsr.dom_iso local.dqmsr.dom_llp by fastforce

lemma dom_lla_var: "(dom x \<le> dom y) = (x \<le> dom y \<cdot> \<top>)"
  using dom_top_pres local.dqmsr.dom_llp by force

lemma "dom (1 \<sqinter> x) = 1 \<sqinter> x \<Longrightarrow> x \<le> 1 \<Longrightarrow> dom x = x"
  using local.inf_absorb2 by force

lemma dom_meet_sub: "dom (x \<sqinter> y) \<le> dom x \<sqinter> dom y"
  by (simp add: local.dqmsr.d_iso)

lemma dom_dist1: "dom x \<squnion> (dom y \<sqinter> dom z) = (dom x \<squnion> dom y) \<sqinter> (dom x \<squnion> dom z)"
  by (metis dom_meet local.dom_add local.dqmsr.dom_distrib)

lemma dom_dist2: "dom x \<sqinter> (dom y \<squnion> dom z) = (dom x \<sqinter> dom y) \<squnion> (dom x \<sqinter> dom z)"
  by (metis dom_meet local.dom_add local.sup_distl)

abbreviation "fd' \<equiv> dqmsr.fd"

definition "bb x y = \<Squnion>{dom z |z. fd' x z \<le> dom y}"

lemma fd'_bb_galois_aux: "fd' x (dom p) \<le> dom q \<Longrightarrow> dom p \<le> bb x (dom q)"
  by (simp add: bb_def local.SUP_upper setcompr_eq_image)

lemma dom_iso_var: "(\<Squnion>x \<in> X. dom x) \<le> dom (\<Squnion>x \<in> X. dom x)"
  by (meson local.SUP_le_iff local.dom_subid local.dqmsr.domain_subid)

lemma dom_iso_var2: "(\<Squnion>x \<in> X. dom x) \<le> dom (\<Squnion>x \<in> X. x)"
  by (simp add: local.SUP_le_iff local.Sup_upper local.dqmsr.dom_iso)

end


subsection \<open>Codomain quantales\<close>

class codomain_quantale = unital_quantale + range_op +
  assumes cod_absorb: "x \<le> x \<cdot> cod x"
  and cod_local: "cod (cod x \<cdot> y) = cod (x \<cdot> y)"
  and cod_add: "cod (x \<squnion> y) = cod x \<squnion> cod y"
  and cod_subid: "cod x \<le> 1"
  and cod_zero: "cod \<bottom> = \<bottom>"

sublocale codomain_quantale \<subseteq> coddual: domain_quantale range_op _ "\<lambda>x y. y \<cdot> x" _ _ _ _ _ _ _ _
  by unfold_locales (auto simp: mult_assoc cod_subid cod_zero cod_add cod_local cod_absorb Sup_distr Sup_distl)

abbreviation (in codomain_quantale) "bd' \<equiv> coddual.fd'"

definition (in codomain_quantale) "fb x y = \<Squnion>{cod z |z. bd' x z \<le> cod y}"

lemma (in codomain_quantale) bd'_fb_galois_aux: "bd' x (cod p) \<le> cod q \<Longrightarrow> cod p \<le> fb x (cod q)"
  using local.coddual.bb_def local.coddual.fd'_bb_galois_aux local.fb_def by auto


subsection \<open>Modal quantales\<close>

class dc_modal_quantale = domain_quantale + codomain_quantale +
  assumes dc_compat [simp]: "dom (cod x) = cod x"
  and cd_compat [simp]: "cod (dom x) = dom x"

sublocale dc_modal_quantale \<subseteq> mqs: dr_modal_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar dom cod
  by unfold_locales simp_all

sublocale dc_modal_quantale \<subseteq> mqdual: dc_modal_quantale _ "\<lambda>x y. y \<cdot> x" _ _ _ _ _ _ _ _  dom cod
  by unfold_locales simp_all

lemma (in dc_modal_quantale) "x \<cdot> \<top> = dom x \<cdot> \<top>"
(*  nitpick[expect=genuine] *)
  oops

lemma (in dc_modal_quantale) "\<top> \<cdot> x = \<top> \<cdot> cod x"
(*  nitpick[expect=genuine] *)
  oops


subsection \<open>Antidomain and anticodomain quantales\<close>

notation antidomain_op ("adom")

class antidomain_quantale = unital_quantale + antidomain_op +
  assumes as1 [simp]: "adom x \<cdot> x = \<bottom>"
  and as2 [simp]: "adom (x \<cdot> y) \<le> adom (x \<cdot> adom (adom y))"
  and as3 [simp]: "adom (adom x) \<squnion> adom x = 1"

definition (in antidomain_quantale) "ddom = adom \<circ> adom"

sublocale antidomain_quantale \<subseteq> adqmsr: antidomain_semiring adom "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)"
  by unfold_locales (simp_all add: local.sup.absorb2)

sublocale antidomain_quantale \<subseteq> adqmka: antidomain_kleene_algebra adom "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar..

sublocale antidomain_quantale \<subseteq> addq: domain_quantale ddom
  by unfold_locales (simp_all add: ddom_def local.adqmsr.ans_d_def)

notation antirange_op ("acod")

class anticodomain_quantale = unital_quantale + antirange_op +
  assumes ars1 [simp]: "x \<cdot> acod x = \<bottom>"
  and ars2 [simp]: "acod (x \<cdot> y) \<le> acod (acod (acod x) \<cdot> y)"
  and ars3 [simp]: "acod (acod x) \<squnion> acod x = 1"

sublocale anticodomain_quantale \<subseteq> acoddual: antidomain_quantale acod _ "\<lambda>x y. y \<cdot> x" _ _ _ _ _ _ _ _
  by unfold_locales (auto simp: mult_assoc Sup_distl Sup_distr)

definition (in anticodomain_quantale) "ccod = acod \<circ> acod"

sublocale anticodomain_quantale \<subseteq> acdqmsr: antirange_semiring "(\<squnion>)" "(\<cdot>)" 1 \<bottom> acod "(\<le>)" "(<)"..

sublocale anticodomain_quantale \<subseteq> acdqmka: antirange_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar acod..

sublocale anticodomain_quantale \<subseteq> acddq: codomain_quantale _ _ _ _ _ _ _ _ _ _ "\<lambda> x. acod (acod x)"
  by unfold_locales (simp_all add: local.acoddual.adqmsr.ans_d_def)

class modal_quantale = antidomain_quantale + anticodomain_quantale

sublocale modal_quantale \<subseteq> mmqs: modal_kleene_algebra_simp "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar adom acod..

sublocale modal_quantale \<subseteq> mmqdual: modal_quantale _ "\<lambda>x y. y \<cdot> x" _ _ _ _ _ _ _ _ adom acod
  by unfold_locales simp_all

end



