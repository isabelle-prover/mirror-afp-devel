(* 
Title: Omega-Kleene Algebras
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>$\omega$-Kleene algebras\<close>

theory "Omega_Kleene_Algebra"
  imports Quantales_Converse.Modal_Kleene_Algebra_Var

begin

text \<open>Here we develop $\omega$-semigroups and $\omega$-Kleene algebras.\<close>

subsection \<open>Copies for i-structures\<close>

class icomp_op =
  fixes icomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<cdot>\<^bsub>_\<^esub> _" [70,70,70]70)

class iid_op =
  fixes un :: "nat \<Rightarrow> 'a"

class istar_op =
  fixes star :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"

class idom_op =
  fixes do :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"

class icod_op =
  fixes cd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"

class imonoid_mult = icomp_op + iid_op +
  assumes assoc: "x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>i\<^esub> z) = (x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>i\<^esub> z"
  and comp_unl: "un i \<cdot>\<^bsub>i\<^esub> x = x" 
  and comp_unr: "x \<cdot>\<^bsub>i\<^esub> un i = x" 

class idioid = imonoid_mult + join_semilattice_zero +
  assumes distl: "x \<cdot>\<^bsub>i\<^esub> (y + z) = x \<cdot>\<^bsub>i\<^esub> y + x \<cdot>\<^bsub>i\<^esub> z"
  and distr: "(x + y) \<cdot>\<^bsub>i\<^esub> z = x \<cdot>\<^bsub>i\<^esub> z + y \<cdot>\<^bsub>i\<^esub> z"
  and annil: "0 \<cdot>\<^bsub>i\<^esub> x = 0"
  and annir: "x \<cdot>\<^bsub>i\<^esub> 0 = 0"

class ikleene_algebra = idioid + istar_op +
  assumes star_unfoldl: "un i + x \<cdot>\<^bsub>i\<^esub> star i x \<le> star i x"  
  and star_unfoldr: "un i + star i x \<cdot>\<^bsub>i\<^esub> x \<le> star i x"
  and star_inductl: "z + x \<cdot>\<^bsub>i\<^esub> y \<le> y \<Longrightarrow> star i x \<cdot>\<^bsub>i\<^esub> z \<le> y"
  and star_inductr: "z + y \<cdot>\<^bsub>i\<^esub> x \<le> y \<Longrightarrow> z \<cdot>\<^bsub>i\<^esub> star i x \<le> y"

class idomain_semiring = idioid + idom_op +
  assumes do_absorb: "x \<le> do i x \<cdot>\<^bsub>i\<^esub> x"
  and do_local: "do i (x \<cdot>\<^bsub>i\<^esub> do i y) = do i (x \<cdot>\<^bsub>i\<^esub> y)"
  and do_add: "do i (x + y) = do i x + do i y"
  and do_subid: "do i x \<le> un i"
  and do_zero: "do i 0 = 0"

class icodomain_semiring = idioid + icod_op +
  assumes cd_absorb: "x \<le> x \<cdot>\<^bsub>i\<^esub> cd i x" 
  and cd_local: "cd i (cd i x \<cdot>\<^bsub>i\<^esub> y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  and cd_add: "cd i (x + y) = cd i x + cd i y"
  and cd_subid: "cd i x \<le> un i"
  and cd_zero: "cd i 0 = 0"

class imodal_semiring = idomain_semiring + icodomain_semiring +
  assumes dc_compat: "do i (cd i x) = cd i x" 
  and cd_compat: "cd i (do i x) = do i x" 

class imodal_kleene_algebra = imodal_semiring + ikleene_algebra

sublocale imonoid_mult \<subseteq> mm: monoid_mult "un i" "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y"
  by (unfold_locales, simp_all add: local.assoc local.comp_unl local.comp_unr)

sublocale idioid \<subseteq> di: dioid_one_zero _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _ _ _
  by (unfold_locales, simp_all add: local.distl local.distr annil annir)

sublocale idioid \<subseteq> ddi: idioid _ _ _ _"\<lambda>x i y. icomp y i x" _
  by unfold_locales (simp_all add: local.mm.mult_assoc local.distl)

sublocale ikleene_algebra \<subseteq> ki: kleene_algebra _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _ _ _ "star i"
  apply unfold_locales
  using local.star_unfoldl apply blast
  by (simp_all add: local.star_inductl local.star_inductr local.star_unfoldl)

sublocale ikleene_algebra \<subseteq> dki: ikleene_algebra _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ _
  by (unfold_locales, simp_all add: local.star_inductr local.star_inductl)

sublocale idomain_semiring \<subseteq> dsri: domain_semiring _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _ "do i" _ _
  by unfold_locales (simp_all add: local.do_absorb local.join.sup_absorb2 local.do_local local.do_zero local.do_add local.do_subid)

sublocale icodomain_semiring \<subseteq> csri: range_semiring _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _ "cd i" _ _
  by unfold_locales (simp_all add: local.cd_absorb local.join.sup_absorb2 local.cd_local local.cd_subid local.cd_zero local.cd_add)

sublocale icodomain_semiring \<subseteq> ds0dual: idomain_semiring _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ cd
  by unfold_locales simp_all

sublocale imodal_semiring \<subseteq> msri: dr_modal_semiring _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _  "do i" _ _ "cd i"
  by (unfold_locales, simp_all add: local.dc_compat local.cd_compat)

sublocale imodal_semiring \<subseteq> msridual: imodal_semiring do _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ cd
  by unfold_locales simp_all

sublocale imodal_kleene_algebra \<subseteq> mkai: dr_modal_kleene_algebra _ "\<lambda>x y. x \<cdot>\<^bsub>i\<^esub> y" "un i" _ _ _ "star i"  "do i" "cd i"..

sublocale imodal_kleene_algebra \<subseteq> mkaidual: imodal_kleene_algebra _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ _ do cd ..

subsection \<open>Globular $\omega$-semirings\<close>

class omega_semiring = imodal_semiring +
  assumes interchange: "i < j \<Longrightarrow> (w \<cdot>\<^bsub>j\<^esub> x) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> z) \<le> (w \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (x \<cdot>\<^bsub>i\<^esub> z)"
  and di_hom: "i \<noteq> j \<Longrightarrow> do i (x \<cdot>\<^bsub>j\<^esub> y) \<le> do i x \<cdot>\<^bsub>j\<^esub> do i y"
  and ci_hom: "i \<noteq> j \<Longrightarrow> cd i (x \<cdot>\<^bsub>j\<^esub> y) \<le> cd i x \<cdot>\<^bsub>j\<^esub> cd i y"
  and djdi: "i < j \<Longrightarrow> do j (do i x) = do i x"

class strong_omega_semiring = omega_semiring + 
  assumes dj_strong_hom: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>i\<^esub> y) = do j x \<cdot>\<^bsub>i\<^esub> do j y"
  and cj_strong_hom: "i < j \<Longrightarrow> cd j (x \<cdot>\<^bsub>i\<^esub> y) = cd j x \<cdot>\<^bsub>i\<^esub> cd j y"

sublocale omega_semiring \<subseteq> tgsdual: omega_semiring do _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ cd
  apply unfold_locales
     apply (simp_all add: local.interchange local.ci_hom local.di_hom)
  by (metis local.dc_compat local.djdi msri.d_cod_fix)

sublocale strong_omega_semiring \<subseteq> stgsdual: strong_omega_semiring do _ _ _ _ "\<lambda>x i y. y \<cdot>\<^bsub>i\<^esub> x" _ cd 
  by unfold_locales (simp_all add: local.cj_strong_hom local.dj_strong_hom)

context omega_semiring
begin

lemma interchange_var: "(w \<cdot>\<^bsub>(i + k + 1)\<^esub> x) \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>(i + k + 1)\<^esub> z) \<le> (w \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>(i + k +1)\<^esub> (x \<cdot>\<^bsub>i\<^esub> z)"
  by (simp add: local.interchange)

lemma djdi_var [simp]: "do (i + k + 1) (do i x) = do i x"
  by (simp add: local.djdi)

lemma cjdi: "i \<le> j \<Longrightarrow> cd j (do i x) = do i x"
  by (metis local.cd_compat local.djdi order_class.nless_le)

lemma cjdi_var [simp]: "cd (i + k) (do i x) = do i x"
  by (simp add: cjdi)

lemma djci: "i \<le> j \<Longrightarrow> do j (cd i x) = cd i x"
  by (metis cjdi local.dc_compat)

lemma djci_var [simp]: "do (i + k) (cd i x) = cd i x"
  by (simp add: djci)

lemma cjci: "i \<le> j \<Longrightarrow> cd j (cd i x) = cd i x"
  using djci msri.d_cod_fix by force

lemma cjci_var [simp]: "cd (i + k) (cd i x) = cd i x"
  by (simp add: cjci)

lemma unj_compi_var: "i \<le> j \<Longrightarrow> un j \<le> un j \<cdot>\<^bsub>i\<^esub> un j"
  by (metis cjdi local.cd_subid local.di.mult_isol local.dsri.dom_one local.mm.mult_1_right)

lemma un_iso: "i \<le> j \<Longrightarrow> un i \<le> un j"
  by (metis cjdi_var le_Suc_ex local.cd_subid local.dsri.dom_one)

lemma uni_compj_eq : "i < j \<Longrightarrow> un i \<cdot>\<^bsub>j\<^esub> un i = un i"
  by (metis local.djdi local.dsri.dom_one local.dsri.dsg1)

lemma uni_compj_eq_var [simp]: "un i \<cdot>\<^bsub>(i + k)\<^esub> un i = un i"
  by (metis cjdi le_add1 local.csri.rdual.dns1'' local.dsri.dom_one)

lemma dj_uni: "i < j \<Longrightarrow> do j (un i) = un i"
  by (metis local.djdi local.dsri.dom_one)

lemma dj_uni_var [simp]: "do (i + k) (un i) = un i"
  by (metis djci_var local.csri.rdual.dom_one)

lemma di_unj: "i < j \<Longrightarrow> do i (un j) = un i"
  by (metis dj_uni local.do_subid local.dsri.dom_iso local.dsri.dom_one local.dual_order.antisym)

lemma di_unj_var [simp]: "do i (un (i + k)) = un i"
  by (metis di_unj le_add1 local.dsri.dom_one order_neq_le_trans)

lemma ci_unj: "i < j \<Longrightarrow> cd i (un j) = un i"
  by (metis less_or_eq_imp_le local.cd_subid local.csri.rdual.dom_iso local.csri.rdual.dom_one local.dual_order.antisym un_iso)

lemma ci_unj_var [simp]: "cd i (un (i + k)) = un i"
  by (metis ci_unj le_add1 local.csri.rdual.dom_one order_neq_le_trans)

lemma cj_uni: "i < j \<Longrightarrow> cd j (un i) = un i"
  using dj_uni local.msri.msrdual.d_cod_fix by force

lemma cj_uni_var [simp]: "cd (i + k) (un i) = un i"
  by (simp add: local.msri.msrdual.d_cod_fix)

lemma comm_didj: "i \<le> j \<Longrightarrow> do i (do j x) = do j (do i x)"
proof-
  have h: "i < j \<Longrightarrow> do i (do j x) = do j (do i x)"
    by (smt (verit) local.di_hom local.djdi local.dsri.dom_llp local.dsri.dom_subid_aux2 local.dual_order.eq_iff)
  have "i = j \<Longrightarrow> do i (do j x) = do j (do i x)"
    by simp
  thus ?thesis
    by (smt (verit) local.di_hom local.djdi local.dsri.dom_llp local.dsri.dsg1 local.dual_order.antisym nat_neq_iff)
qed

lemma comm_didj_var: "do i (do (i + k) x) = do (i + k) (do i x)"
  by (meson comm_didj le_add1)

lemma comm_dicj: "i < j \<Longrightarrow> do i (cd j x) = cd j (do i x)"
  by (smt (verit, ccfv_threshold) cjdi less_or_eq_imp_le local.csri.rdual.d_preserves_equation local.csri.rdual.dns1'' local.dc_compat local.di_hom local.dsri.d_preserves_equation local.dsri.dom_llp local.dsri.dsg1 local.tgsdual.di_hom nat_neq_iff)

lemma comm_dicj_var: "do i (cd (i + k + 1) x) = cd (i + k + 1) (do i x)"
  using comm_dicj by auto

lemma comm_cicj: "i \<le> j \<Longrightarrow> cd i (cd j x) = cd j (cd i x)"
  by (smt (verit) cjci local.csri.rdual.dns1'' local.csri.rdual.dom_llp local.dual_order.antisym local.tgsdual.di_hom)

lemma comm_cicj_var [simp]: "cd i (cd (i + k) x) = cd (i + k) (cd i x)"
  by (meson comm_cicj le_add1)

lemma comm_cidj: "i < j \<Longrightarrow> cd i (do j x) = do j (cd i x)"
  by (smt (verit) comm_cicj djci less_or_eq_imp_le local.cd_compat local.csri.rdual.dns1'' local.csri.rdual.dom_llp local.di_hom local.dsri.dom_subid_aux2'' local.dsri.dsg1 local.dual_order.antisym local.tgsdual.di_hom nat_neq_iff)

text \<open>We prove further lemmas that are not related to the globular structure.\<close>

lemma di_compi_idem: "i \<le> j \<Longrightarrow> do i x \<cdot>\<^bsub>j\<^esub> do i x = do i x"
  by (metis cjdi local.csri.rdual.dns1'')

lemma di_compi_idem_var [simp]: "do i x \<cdot>\<^bsub>(i + k)\<^esub> do i x = do i x"
  by (simp add: di_compi_idem)

lemma codi_compj_idem: "i \<le> j \<Longrightarrow> cd i x \<cdot>\<^bsub>j\<^esub> cd i x = cd i x"
  by (metis djci local.dsri.dsg1)

lemma codi_compj_idem_var [simp]: "cd i x \<cdot>\<^bsub>(i + k)\<^esub> cd i x = cd i x"
  by (simp add: codi_compj_idem)

lemma domij_loc: "i \<le> j \<Longrightarrow> do i (x \<cdot>\<^bsub>j\<^esub> do j y) = do i (x \<cdot>\<^bsub>j\<^esub> y)"
  by (smt (verit, ccfv_SIG) comm_didj local.djdi local.do_local order_class.dual_order.order_iff_strict)

lemma domij_loc_var [simp]: "do i (x \<cdot>\<^bsub>(i + k)\<^esub> do (i + k) y) = do i (x \<cdot>\<^bsub>(i + k)\<^esub> y)"
  by (simp add: domij_loc)

lemma codij_locl: "i \<le> j \<Longrightarrow> cd i (cd j x \<cdot>\<^bsub>j\<^esub> y) = cd i (x \<cdot>\<^bsub>j\<^esub> y)"
  by (smt (verit, ccfv_SIG) cjci comm_cicj local.ds0dual.do_local)

lemma codij_locl_var [simp]: "cd i (cd (i + k) x \<cdot>\<^bsub>(i + k)\<^esub> y) = cd i (x \<cdot>\<^bsub>(i + k)\<^esub> y)"
  by (simp add: codij_locl)

lemma domij_exp: "i < j \<Longrightarrow> do i (cd j x \<cdot>\<^bsub>j\<^esub> y) = do i (x \<cdot>\<^bsub>j\<^esub> y)"
  by (metis cjdi comm_dicj local.cd_local preorder_class.dual_order.strict_implies_order)

lemma domij_exp_var [simp]: "do i (cd (i + k + 1) x \<cdot>\<^bsub>(i + k + 1)\<^esub> y) = do i (x \<cdot>\<^bsub>(i + k + 1)\<^esub> y)"
  using domij_exp by force

lemma codij_exp: "i < j \<Longrightarrow> cd i (x \<cdot>\<^bsub>j\<^esub> do j y) = cd i (x \<cdot>\<^bsub>j\<^esub> y)"
  by (metis comm_cidj djci less_or_eq_imp_le local.do_local)

lemma codij_exp_var [simp]: "cd i (x \<cdot>\<^bsub>(i + k + 1)\<^esub> do (i + k + 1) y) = cd i (x \<cdot>\<^bsub>(i + k + 1)\<^esub> y)"
  using codij_exp by force

lemma domij_loc_var2: "i \<le> j \<Longrightarrow> do i (x \<cdot>\<^bsub>i\<^esub> do j y) = do i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (metis domij_loc local.do_local local.dsri.dom_el_idem local.dsri.dsg1)

lemma domij_loc_var3: "do i (x \<cdot>\<^bsub>i\<^esub> do (i + k) y) = do i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (simp add: domij_loc_var2)

lemma codij_loc_var: "i \<le> j \<Longrightarrow> cd i (cd j x \<cdot>\<^bsub>i\<^esub> y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (metis codij_locl local.csri.rdual.dom_el_idem local.csri.rdual.dsg1 local.ds0dual.do_local)

lemma codij_loc_var2: "cd i (cd (i + k) x \<cdot>\<^bsub>i\<^esub> y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (simp add: codij_loc_var)

lemma di_compj: "i < j \<Longrightarrow> do i x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> z) \<le> (do i x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (do i x \<cdot>\<^bsub>i\<^esub> z)"
  by (metis di_compi_idem local.tgsdual.interchange preorder_class.less_le_not_le)

lemma dj_compj: "i < j \<Longrightarrow> do j x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>j\<^esub> z) \<le> (do j x \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub>(do j x \<cdot>\<^bsub>i\<^esub> z)"
  by (metis local.dsri.dom_el_idem local.tgsdual.interchange)

lemma dij_export: "i \<le> j \<Longrightarrow> do i (do j x \<cdot>\<^bsub>j\<^esub> y) \<le> do i x \<cdot>\<^bsub>j\<^esub> do i y"
  by (smt (verit, ccfv_SIG) comm_didj domij_loc local.ddi.di.mult_isol_var local.dsri.dom_iso local.dsri.dom_subid_aux2 local.dsri.dsg1 local.dsri.dsg4)

lemma dij_export_var [simp]: "do i (do (i + k) x \<cdot>\<^bsub>(i + k)\<^esub> y) \<le> do i x \<cdot>\<^bsub>(i + k)\<^esub> do i y"
  by (simp add: dij_export)

lemma codij_export: "i \<le> j \<Longrightarrow> cd i (x \<cdot>\<^bsub>j\<^esub> cd j y) \<le> cd i x \<cdot>\<^bsub>j\<^esub> cd i y"
  by (smt (verit, ccfv_SIG) cjci comm_cicj local.ci_hom local.csri.rdual.dsg3 local.dual_order.eq_iff)

lemma codij_export_var [simp]: "cd i (x \<cdot>\<^bsub>(i + k)\<^esub> cd (i + k) y) \<le> cd i x \<cdot>\<^bsub>(i + k)\<^esub> cd i y"
  by (simp add: codij_export)

lemma dji_export: "i \<le> j \<Longrightarrow> do j (do i x \<cdot>\<^bsub>j\<^esub> y) = do i x \<cdot>\<^bsub>j\<^esub> do j y"
  by (smt (verit, del_insts) comm_didj domij_loc local.dsri.dsg1 local.dsri.dsg3)

lemma dji_export_var: "do (i + k) (do i x \<cdot>\<^bsub>(i + k)\<^esub> y) = do i x \<cdot>\<^bsub>(i + k)\<^esub> do (i + k) y"
  by (simp add: dji_export)

lemma codji_export: "i \<le> j \<Longrightarrow> cd j (x \<cdot>\<^bsub>j\<^esub> cd i y) = cd j x \<cdot>\<^bsub>j\<^esub> cd i y"
  by (metis cjci local.csri.rdual.dsg3)

lemma codji_export_var: "cd (i + k) (x \<cdot>\<^bsub>(i + k)\<^esub> cd i y) = cd (i + k) x \<cdot>\<^bsub>(i + k)\<^esub> cd i y"
  by (simp add: codji_export)

lemma di_compji: "i \<le> j \<Longrightarrow> do i x \<cdot>\<^bsub>j\<^esub> do i y = do i x \<cdot>\<^bsub>i\<^esub> do i y"
  apply (rule order.antisym)
  apply (metis cjdi local.csri.rdual.dom_subid_aux2 local.csri.rdual.dom_subid_aux2'' local.ddi.di.mult_isol_var local.dsri.dom_iso local.dsri.domain_invol local.dsri.dsg1)
  by (metis local.ddi.di.mult_isol_var local.djdi local.dsri.dom_iso local.dsri.dom_subid_aux2 local.dsri.dom_subid_aux2'' local.dsri.dsg1 order_le_imp_less_or_eq)

lemma di_compji_var: "do i x \<cdot>\<^bsub>(i + k)\<^esub> do i y = do i x \<cdot>\<^bsub>i\<^esub> do i y"
  by (meson di_compji le_add1)

lemma dom_exchange_strong: "i \<le> j \<Longrightarrow> (do i w \<cdot>\<^bsub>j\<^esub> do i x) \<cdot>\<^bsub>i\<^esub> (do i y \<cdot>\<^bsub>j\<^esub> do i z) = (do i w \<cdot>\<^bsub>i\<^esub> do i y) \<cdot>\<^bsub>j\<^esub> (do i x \<cdot>\<^bsub>i\<^esub> do i z)"
  by (metis di_compji local.ddi.assoc local.dsri.dsg3 local.dsri.dsg4)

lemma codidomj_exp: "i < j \<Longrightarrow> cd i (x \<cdot>\<^bsub>i\<^esub> y) \<le> cd i (x \<cdot>\<^bsub>i\<^esub> cd j y)"
  by (smt (verit) local.cjci local.codij_loc_var local.comm_cicj local.csri.rdual.dom_iso  order_less_le local.tgsdual.di_hom)

lemma codidomj_exp_var: "cd i (x \<cdot>\<^bsub>i\<^esub> y) \<le> cd i (x \<cdot>\<^bsub>i\<^esub> cd (i + k + 1) y)"
  using codidomj_exp by force


text \<open>The following laws are diamond laws. It remains to define diamonds for them.\<close>

lemma fdiaifdiaj_prop: "i \<le> j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> do j (x \<cdot>\<^bsub>j\<^esub> z)) = do i (y \<cdot>\<^bsub>i\<^esub> (x \<cdot>\<^bsub>j\<^esub> z))"
  by (simp add: domij_loc_var2)

lemma bdiaifdiaj_prop: "i < j \<Longrightarrow> cd i (do j (x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y) = cd i ((x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y)"
  by (metis codij_exp local.cd_local local.dsri.dom_el_idem local.dsri.dsg1)

lemma fdiaibdiaj_prop: "i < j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> cd j (x \<cdot>\<^bsub>j\<^esub> z)) = do i (y \<cdot>\<^bsub>i\<^esub> (x \<cdot>\<^bsub>j\<^esub> z))"
  by (metis domij_exp local.csri.rdual.dom_el_idem local.csri.rdual.dsg1 local.msridual.cd_local)

lemma bdiaibdiaj_prop: "i \<le> j \<Longrightarrow> cd i (cd j (x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y) = cd i ((x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y)"
  by (simp add: codij_loc_var)

lemma fdiaifdiaj_prop2: "i < j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> do j (x \<cdot>\<^bsub>j\<^esub> z)) \<le> do i (y \<cdot>\<^bsub>i\<^esub> (do i x \<cdot>\<^bsub>j\<^esub> do i z))"
  by (metis di_compji domij_loc local.di_hom local.dsri.ddual.bd_def local.dsri.dom_mult_closed local.dsri.dsg1 local.dsri.fd_iso1 nat_neq_iff preorder_class.order.strict_implies_order)

lemma fdiaii_prop2: "i < j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> do i (x \<cdot>\<^bsub>j\<^esub> z)) \<le> do i (y \<cdot>\<^bsub>i\<^esub> (do i x \<cdot>\<^bsub>j\<^esub> do i z))"
  using local.di.mult_isol local.di_hom local.dsri.dom_iso nat_neq_iff by presburger

lemma bdiaidomj_prop2: "i < j \<Longrightarrow> cd i (do j (x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y) \<le> cd i ((cd i x \<cdot>\<^bsub>j\<^esub> cd i z) \<cdot>\<^bsub>i\<^esub> y)"
  by (metis bdiaifdiaj_prop csri.bd_def less_not_refl local.csri.rdual.dom_iso local.csri.rdual.domain_invol local.csri.rdual.fd_iso1 local.tgsdual.di_hom)

lemma bdiaidomi_prop2: "i < j \<Longrightarrow> cd i (do i (x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y) \<le> cd i ((do i x \<cdot>\<^bsub>j\<^esub> do i z) \<cdot>\<^bsub>i\<^esub> y)"
  by (simp add: local.csri.rdual.dom_iso local.ddi.di.mult_isol_var local.di_hom)

lemma fdiaibdiaj_prop_2: "i < j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> cd j (z \<cdot>\<^bsub>j\<^esub> x)) \<le> do i (y \<cdot>\<^bsub>i\<^esub> (do i x \<cdot>\<^bsub>j\<^esub> do i z))"
  by (smt (verit) fdiaibdiaj_prop fdiaii_prop2 local.djdi local.dsri.dsg4 local.msridual.cd_local msri.d_cod_fix)

lemma fdiaibdiai_prop2: "i < j \<Longrightarrow> do i (y \<cdot>\<^bsub>i\<^esub> cd i (z \<cdot>\<^bsub>j\<^esub> x)) \<le> do i (y \<cdot>\<^bsub>i\<^esub> (cd i z \<cdot>\<^bsub>j\<^esub> cd i x))"
  by (simp add: local.di.mult_isol local.dsri.dom_iso local.tgsdual.di_hom)

lemma bdiaibdiaj_prop2: "i < j \<Longrightarrow> cd i (cd j (z \<cdot>\<^bsub>j\<^esub> x) \<cdot>\<^bsub>i\<^esub> y) \<le> cd i ((cd i x \<cdot>\<^bsub>j\<^esub> cd i z) \<cdot>\<^bsub>i\<^esub> y)"
  by (smt (z3) bdiaibdiaj_prop bdiaidomj_prop2 bdiaifdiaj_prop codji_export djci less_or_eq_imp_le local.dsri.dsg4 msri.d_cod_fix)

lemma bdiaibdiai_prop2: "i < j \<Longrightarrow> cd i (cd i (x \<cdot>\<^bsub>j\<^esub> z) \<cdot>\<^bsub>i\<^esub> y) \<le> cd i ((cd i x \<cdot>\<^bsub>j\<^esub> cd i z) \<cdot>\<^bsub>i\<^esub> y)"
  using bdiaidomj_prop2 bdiaifdiaj_prop by force

lemma fdiajfdiai_prop3: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>j\<^esub> do i (y \<cdot>\<^bsub>i\<^esub> z)) \<le> do j (x \<cdot>\<^bsub>j\<^esub> do i (do j y \<cdot>\<^bsub>i\<^esub> z))"
  by (smt (verit) comm_didj domij_loc_var2 local.di.mult_isol local.di_hom local.djdi local.dsri.dom_iso nat_neq_iff preorder_class.order.strict_implies_order)

lemma bdiajbdiai_prop3: "i < j \<Longrightarrow> cd j (cd i (z \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> x) \<le> cd j (cd i (z \<cdot>\<^bsub>i\<^esub> cd j y) \<cdot>\<^bsub>j\<^esub> x)"
  by (simp add: codidomj_exp local.csri.rdual.dom_iso local.di.mult_isor)

end

text \<open>The following proofs need the domain codomain duality, which has been formalised using a sublocale
statement above. It is only available outside of a context.\<close>

lemma (in omega_semiring) domicodj_exp: "i < j \<Longrightarrow> do i (x \<cdot>\<^bsub>i\<^esub> y) \<le> do i (cd j x \<cdot>\<^bsub>i\<^esub> y)"
  by (smt (verit, ccfv_SIG) local.cjdi local.comm_dicj local.dsri.dom_iso local.order_eq_iff local.tgsdual.domij_loc_var local.djdi local.msridual.cd_local local.tgsdual.di_hom msri.d_cod_fix nat_neq_iff)

lemma (in omega_semiring) domicodj_exp_var: "do i (x \<cdot>\<^bsub>i\<^esub> y) \<le> do i (cd (i + k + 1) x \<cdot>\<^bsub>i\<^esub> y)"
  using local.domicodj_exp by force

lemma (in omega_semiring) fdiajbdiai_prop3: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>j\<^esub> cd i (z \<cdot>\<^bsub>i\<^esub> y)) \<le> do j (x \<cdot>\<^bsub>j\<^esub> cd i (z \<cdot>\<^bsub>i\<^esub> do j y))"
  by (simp add: local.di.mult_isol local.dsri.dom_iso local.tgsdual.domicodj_exp)

lemma (in omega_semiring) bdiajfdiai_prop3: "i < j \<Longrightarrow> cd j (do i (y \<cdot>\<^bsub>i\<^esub> z) \<cdot>\<^bsub>j\<^esub> x) \<le> cd j (do i (cd j y \<cdot>\<^bsub>i\<^esub> z) \<cdot>\<^bsub>j\<^esub> x)"
  by (simp add: local.tgsdual.fdiajbdiai_prop3)

context strong_omega_semiring
begin

lemma idj_compj: "i \<le> j \<Longrightarrow> un j \<cdot>\<^bsub>i\<^esub> un j \<le> un j"
  by (metis local.cd_subid local.cj_strong_hom local.csri.rdual.dns1'' local.csri.rdual.dom_one order_le_imp_less_or_eq)

lemma idj_compi_eq: "i < j \<Longrightarrow> un j = un j \<cdot>\<^bsub>i\<^esub> un j"
  by (simp add: idj_compj local.order_eq_iff local.unj_compi_var)

lemma domicodj_exp: "i < j \<Longrightarrow> do i (x \<cdot>\<^bsub>i\<^esub> y) = do i (cd j x \<cdot>\<^bsub>i\<^esub> y)"
  by (smt (verit, del_insts) local.csri.rdual.domain_invol local.csri.rdual.dsg1 local.domij_exp local.stgsdual.dj_strong_hom)

lemma domicodj_exp_var [simp] : "do i (cd (i + k + 1) x \<cdot>\<^bsub>i\<^esub> y) = do i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (metis Suc_eq_plus1 less_add_Suc1 local.domicodj_exp)

lemma codidomj_exp: "i < j \<Longrightarrow> cd i (x \<cdot>\<^bsub>i\<^esub> do j y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  by (smt (verit, ccfv_SIG) local.comm_cidj local.dc_compat local.dj_strong_hom local.ds0dual.do_local local.tgsdual.djdi)

lemma codidomj_exp_var [simp]: "cd i (x \<cdot>\<^bsub>i\<^esub> do (i + k + 1) y) = cd i (x \<cdot>\<^bsub>i\<^esub> y)"
  using local.codidomj_exp by force

lemma fdiajfdiai_prop3: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>j\<^esub> do i (do j y \<cdot>\<^bsub>i\<^esub> z)) = do j (x \<cdot>\<^bsub>j\<^esub> do i (y \<cdot>\<^bsub>i\<^esub> z))"
  by (smt (verit, best) local.comm_didj local.dj_strong_hom local.tgsdual.cjci local.tgsdual.codij_loc_var preorder_class.less_le_not_le)

lemma fdiajbdiai_prop3: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>j\<^esub> cd i (z \<cdot>\<^bsub>i\<^esub> do j y)) = do j (x \<cdot>\<^bsub>j\<^esub> cd i (z \<cdot>\<^bsub>i\<^esub> y))"
  by (simp add: local.codidomj_exp)

lemma bdiajfdiai_prop3: "i < j \<Longrightarrow> cd j (do i (cd j y \<cdot>\<^bsub>i\<^esub> z) \<cdot>\<^bsub>j\<^esub> x) = cd j (do i (y \<cdot>\<^bsub>i\<^esub> z) \<cdot>\<^bsub>j\<^esub> x)"
  by (metis local.domicodj_exp)

lemma bdiajbdiai_prop3: "i < j \<Longrightarrow> cd j (cd i (z \<cdot>\<^bsub>i\<^esub> cd j y) \<cdot>\<^bsub>j\<^esub> x) = cd j (cd i (z \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> x)"
  by (smt (verit, ccfv_threshold) less_or_eq_imp_le local.cj_strong_hom local.cjci local.comm_cicj)

lemma fdiaifdiaj_prop4: "i < j \<Longrightarrow> do i z \<cdot>\<^bsub>i\<^esub> do j (x \<cdot>\<^bsub>j\<^esub> y) \<le> do j ((do i z \<cdot>\<^bsub>i\<^esub> x) \<cdot>\<^bsub>j\<^esub> (do i z \<cdot>\<^bsub>i\<^esub> y))"
  by (smt (verit, ccfv_threshold) local.di_compj local.djdi local.dsri.dom_iso local.stgsdual.cj_strong_hom)

lemma fdia0bdia1_prop4: "i < j \<Longrightarrow> do i z \<cdot>\<^bsub>i\<^esub> cd j (y \<cdot>\<^bsub>j\<^esub> x) \<le> cd j ((do i z \<cdot>\<^bsub>i\<^esub> y) \<cdot>\<^bsub>j\<^esub> (do i z \<cdot>\<^bsub>i\<^esub> x))"
  by (smt (verit, ccfv_threshold) local.csri.rdual.dom_iso local.di_compj local.djdi local.stgsdual.dj_strong_hom msri.d_cod_fix)

lemma fdiajfdiaj_prop4: "i < j \<Longrightarrow> do j (x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> do i z \<le> do j ((x \<cdot>\<^bsub>i\<^esub> do i z) \<cdot>\<^bsub>j\<^esub> (y \<cdot>\<^bsub>i\<^esub> do i z))"
  by (smt (verit, ccfv_threshold) local.djdi local.dsri.dom_iso local.dsri.dsg1 local.stgsdual.cj_strong_hom local.tgsdual.interchange)

lemma bdiajbdiaj_prop4: "i < j \<Longrightarrow> cd j (y \<cdot>\<^bsub>j\<^esub> x) \<cdot>\<^bsub>i\<^esub> do i z \<le> cd j ((y \<cdot>\<^bsub>i\<^esub> do i z) \<cdot>\<^bsub>j\<^esub> (x \<cdot>\<^bsub>i\<^esub> do i z))"
  by (smt (verit) local.cd_compat local.csri.rdual.dom_iso local.stgsdual.dj_strong_hom local.tgsdual.di_compj local.tgsdual.djdi)

end


subsection \<open>Globular $\omega$-Kleene algebras\<close>

class omega_kleene_algebra = omega_semiring + ikleene_algebra

class strong_omega_kleene_algebra = strong_omega_semiring + ikleene_algebra

context omega_kleene_algebra
begin

lemma interchange_var1: "i < j \<Longrightarrow> (x \<cdot>\<^bsub>j\<^esub> x) \<cdot>\<^bsub>i\<^esub> ((y \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (z \<cdot>\<^bsub>j\<^esub> z)) \<le> (x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>i\<^esub> z)) \<cdot>\<^bsub>j\<^esub> (x \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>i\<^esub> z))"
  by (meson local.di.mult_isol local.interchange local.order_trans)

lemma interchange_var2: "i < j \<Longrightarrow> (x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> ((x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (x \<cdot>\<^bsub>j\<^esub> y)) \<le> (x \<cdot>\<^bsub>i\<^esub> (x \<cdot>\<^bsub>i\<^esub> x)) \<cdot>\<^bsub>j\<^esub> (y \<cdot>\<^bsub>i\<^esub> (y \<cdot>\<^bsub>i\<^esub> y))"
  by (meson local.di.mult_isol local.interchange local.order_trans)

lemma star_compj: 
  assumes "i < j"
  shows "star i (x \<cdot>\<^bsub>j\<^esub> y) \<le> star i x \<cdot>\<^bsub>j\<^esub> star i y"
proof-
  have a: "un i \<le> star i x \<cdot>\<^bsub>j\<^esub> star i y"
    by (metis assms local.di.mult_isol_var local.ki.star_ref local.uni_compj_eq)
  have "(x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (star i x \<cdot>\<^bsub>j\<^esub> star i y) \<le> (x \<cdot>\<^bsub>i\<^esub> star i x ) \<cdot>\<^bsub>j\<^esub> (y \<cdot>\<^bsub>i\<^esub> star i y)"
    by (simp add: assms local.interchange)
  also have "\<dots> \<le> star i x \<cdot>\<^bsub>j\<^esub> star i y"
    by (simp add: local.di.mult_isol_var)
  finally have "(x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (star i x \<cdot>\<^bsub>j\<^esub> star i y) \<le> star i x \<cdot>\<^bsub>j\<^esub> star i y".
  hence "un i + (x \<cdot>\<^bsub>j\<^esub> y) \<cdot>\<^bsub>i\<^esub> (star i x \<cdot>\<^bsub>j\<^esub> star i y) \<le> star i x \<cdot>\<^bsub>j\<^esub> star i y"
    by (simp add: a)
  thus ?thesis
    using local.star_inductl by force
qed

lemma star_compj_var: "star i (x \<cdot>\<^bsub>(i + k + 1)\<^esub> y) \<le> star i x \<cdot>\<^bsub>(i + k + 1)\<^esub> star i y"
  using star_compj by force

end

end
