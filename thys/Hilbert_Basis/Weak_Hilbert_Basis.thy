section \<open>The weak Hilbert Basis theorem\<close>
theory Weak_Hilbert_Basis

imports 
  "HOL-Algebra.Polynomials" 
  "HOL-Algebra.Indexed_Polynomials" 
  "Polynomials_Ring_Misc" 
  "Padic_Field.Cring_Multivariable_Poly" 
  "HOL-Algebra.Module" 
  "Ring_Misc"
begin

text \<open>In this section, we show what we called "weak" Hilbert basis theorem, meaning Hilbert basis
theorem for univariate polynomials
The theorem is done for all three (Polynomials, UP, IP with card = 1)
  models of polynomials that exists in HOL-Algebra\<close>

subsection \<open>Weak Hilbert Basis\<close>
lemma (in noetherian_domain) weak_Hilbert_basis:\<open>noetherian_ring ((carrier R)[X])\<close>
proof(rule ring.trivial_ideal_chain_imp_noetherian)
  show \<open>ring ((carrier R) [X])\<close>
    using carrier_is_subring univ_poly_is_ring by blast
next
  interpret kxr: cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by blast
  fix C
  assume F:\<open>C \<noteq> {}\<close> \<open>subset.chain {I. ideal I ((carrier R) [X])} C\<close>
  have f1:\<open>I\<in>C \<Longrightarrow> ideal I (carrier R[X])\<close> for I
    using F unfolding subset.chain_def by(auto)
  have f2:\<open>a\<in>carrier((carrier R)[X])\<and> aa\<in>carrier((carrier R)[X]) 
          \<Longrightarrow> coeff (a\<oplus>\<^bsub>(carrier R)[X]\<^esub> aa) k = coeff a k\<oplus> coeff aa k \<close>
    for a aa k
    unfolding univ_poly_add 
    apply(subst poly_add_coeff) 
    using polynomial_in_carrier[of \<open>carrier R\<close> a] polynomial_in_carrier[of \<open>carrier R\<close> aa] 
      polynomial_def carrier_is_subring 
    by (simp add: univ_poly_carrier)+
  have f4a:\<open>subring (carrier R) R\<close> 
    using carrier_is_subring by auto
  have degree_of_inv:
    \<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> degree (inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> p) = degree p\<close> for p
    by (metis a_inv_def local.ring_axioms ring.carrier_is_subring univ_poly_a_inv_degree)
  from f1 have \<open>I\<in>C \<Longrightarrow> a \<in> I \<Longrightarrow> coeff a (degree a)\<in> (carrier R)\<close> for a I
    using lead_coeff_in_carrier by blast
  have emp_in_i:\<open>ideal I ((carrier R)[X]) \<Longrightarrow> []  \<in> I\<close> for I
    by (simp add: additive_subgroup_def ideal_def subgroup_def univ_poly_zero)
  have g0:\<open>I\<subseteq>I' \<Longrightarrow> lead_coeff_set I k \<subseteq> lead_coeff_set I' k\<close>
    for I I' k
    unfolding lead_coeff_set_def deg_poly_set by(auto)
  have g1:\<open> ideal I ((carrier R)[X]) \<Longrightarrow> {(X\<otimes>\<^bsub>(carrier R)[X]\<^esub>l) | l. l\<in>I} \<subseteq> I\<close> for I
    using f4a ideal.I_l_closed var_closed(1) by fastforce
  then have g2:
    \<open>ideal I ((carrier R)[X]) \<Longrightarrow> lead_coeff_set {(X\<otimes>\<^bsub>(carrier R)[X]\<^esub>l) | l. l\<in>I} k \<subseteq> lead_coeff_set I k\<close> 
    for I k
    using g0 g1 by auto
  have f7b:\<open>ideal I ((carrier R)[X]) \<Longrightarrow>  lead_coeff_set I k \<subseteq> lead_coeff_set I (k+1)\<close> for I k 
    unfolding lead_coeff_set_def deg_poly_set 
  proof(safe) 
    fix x a
    assume y1:\<open>ideal I (poly_ring R)\<close> \<open>a \<in> I\<close> \<open>k = degree a\<close>
    then show 
      \<open>\<exists>aa. local.coeff a (degree a) = local.coeff aa (degree aa) \<and> aa \<in> {aa \<in> I. degree aa = degree a + 1} \<union> {[]}\<close>
      apply(cases \<open>a=[]\<close>)
       apply(rule exI[where x=\<open>[]\<close>]) 
       apply blast
      apply(rule exI[where x=\<open>a\<otimes>\<^bsub>(carrier R)[X]\<^esub>X\<close>]) 
      apply(safe)
      unfolding ideal_def univ_poly_mult 
      using poly_mult_var[of "(carrier R)" a for a] 
        apply (metis One_nat_def additive_subgroup.a_Hcarr 
          append_is_Nil_conv f4a hd_append2 lead_coeff_simp univ_poly_mult)
       apply (simp add: f4a ideal_axioms_def univ_poly_mult var_closed(1))
      using poly_mult_var[of \<open>(carrier R)\<close> a for a] 
      by (metis Suc_eq_plus1 Suc_pred' diff_Suc_Suc f4a ideal.Icarr length_append_singleton 
          length_greater_0_conv minus_nat.diff_0 univ_poly_mult y1(1))
  next
    assume y1:\<open>ideal I (poly_ring R)\<close>
    then show 
      \<open>\<exists>a. local.coeff [] (degree []) = local.coeff a (degree a) \<and> a \<in> {a \<in> I. degree a = k + 1} \<union> {[]}\<close>
      by force
  qed
  then have f7:\<open>y\<in>C \<Longrightarrow>  lead_coeff_set y k \<subseteq> lead_coeff_set y (k+1)\<close> for k y
    using f1 by blast
  then have f8:\<open>k\<le>k' \<Longrightarrow> y\<in>C \<Longrightarrow>  lead_coeff_set y k \<subseteq> lead_coeff_set y k'\<close> for k k' y
    apply(induct k') 
    using le_Suc_eq by(auto) 
  have n:\<open>noetherian_ring R\<close> 
    by (simp add: noetherian_ring_axioms)
  have c:\<open>x\<in>C \<Longrightarrow> subset.chain {I. ideal I R} {lead_coeff_set x k | k. k\<in>UNIV}\<close> for x
    apply(subst subset_chain_def) 
    apply(safe) 
     apply (simp add: f1 ideal_lead_coeff_set) 
    by (meson f8 nle_le subsetD)
  have c':\<open> subset.chain {I. ideal I R} {lead_coeff_set x k | x. x\<in>C}\<close> for k
  proof(rule Zorn.subset.chainI)
    show \<open>{lead_coeff_set x k |x. x \<in> C} \<subseteq> {I. ideal I R}\<close>
      using f1 ideal_lead_coeff_set by blast
  next
    fix xa y
    assume 1:\<open>xa \<in> {lead_coeff_set x k |x. x \<in> C}\<close> \<open> y \<in> {lead_coeff_set x k |x. x \<in> C}\<close>
    obtain z z' where g10:\<open>xa = lead_coeff_set z k  \<and> y =lead_coeff_set z' k \<and> z\<in>C \<and> z' \<in>C \<close>
      using "1"(1) "1"(2) by blast
    then have \<open>z\<subseteq>z' \<or> z' \<subseteq> z\<close>
      using F unfolding subset.chain_def by(auto) 
    then show \<open>(\<subset>)\<^sup>=\<^sup>= xa y \<or> (\<subset>)\<^sup>=\<^sup>= y xa\<close>
      using g0 g10 by blast+
  qed
  then have U0:\<open>\<forall>x\<in>C. (\<Union>{lead_coeff_set x k | k. k\<in>UNIV}) \<in> {lead_coeff_set x k | k. k\<in>UNIV}\<close> 
  proof(safe)
    fix x
    assume a1: "x \<in> C"
    have "\<forall>A. \<not> subset.chain {A. ideal A R} A \<or> \<Union> A \<in> A \<or> A = {}"
      using ideal_chain_is_trivial by blast
    then show \<open>\<exists>k. \<Union> {lead_coeff_set x k |k. k \<in> UNIV} = lead_coeff_set x k \<and> k \<in> UNIV\<close>
      using a1 c by auto
  qed
  have t9:\<open>x\<in>C \<Longrightarrow> ideal (lead_coeff_set x k) R\<close> for k x
    using f1 ideal_lead_coeff_set by blast
  then have degree_of_inv:\<open>{lead_coeff_set x k | x. x\<in>C} \<noteq> {}\<close> for x::\<open>'a set\<close> and k 
    using F(1) by blast
  then have U1:\<open>\<forall>k. (\<Union>{lead_coeff_set x k |x. x \<in> C}) \<in> {lead_coeff_set x k | x. x\<in>C}\<close> 
    using ideal_lead_coeff_set f7b n c' 
    using ideal_chain_is_trivial[OF degree_of_inv c'] by(auto)
  have kl0:\<open>x\<in>C \<and> y\<in>C\<Longrightarrow>x=y \<longleftrightarrow> (\<forall>k. deg_poly_set x k = deg_poly_set y k)\<close> for x y
  proof(safe)
    fix xa :: "'a list"
    assume a1: "y \<in> C"
    assume a2: "\<forall>k. deg_poly_set x k = deg_poly_set y k"
    assume "xa \<in> x"
    then have "\<exists>n. xa \<in> deg_poly_set x n"
      using deg_poly_set noetherian_domain_axioms by fastforce
    then show "xa \<in> y"
      using a2 a1 
      by (metis (no_types, lifting) UnE emp_in_i f1 local.ring_axioms
          mem_Collect_eq ring.deg_poly_set singleton_iff)
  next
    fix xa :: "'a list"
    assume a1: "x \<in> C"
    assume a2: "\<forall>k. deg_poly_set x k = deg_poly_set y k"
    assume "xa \<in> y"
    then have "\<exists>n. xa \<in> deg_poly_set y n"
      using deg_poly_set noetherian_domain_axioms by fastforce
    then show "xa \<in> x"
      using a2 a1 
      by (metis (no_types, lifting) UnE emp_in_i f1 local.ring_axioms 
          mem_Collect_eq ring.deg_poly_set singleton_iff)
  qed
  have kl:\<open>x'\<in>C \<and> y\<in>C \<and> x'\<subseteq> y\<Longrightarrow>(\<forall>k\<le>n. lead_coeff_set x' k = lead_coeff_set y k) 
      \<longleftrightarrow> (\<forall>k\<le>n. deg_poly_set x' k = deg_poly_set y k)\<close>
    for x' y n
    apply(rule iffI)
    subgoal
    proof(induct n)
      case z:0 
      from lead_coeff_set_0 have d2:\<open>{a. [a] \<in> x'} = {a. [a] \<in> y}\<close>
        using z(2)[rule_format, of 0] unfolding lead_coeff_set_def
        using z.prems(1) f1 unfolding ideal_def 
        by (simp add:f1 ideal_def polynomial_def univ_poly_carrier additive_subgroup.a_Hcarr)
          (metis (mono_tags, lifting) additive_subgroup.a_Hcarr insert_iff 
            list.sel(1) list.simps(3) mem_Collect_eq polynomial_def univ_poly_carrier)
      show ?case 
        apply(insert z)
        apply(simp) 
        apply(subst (asm) (1 2) lead_coeff_set_0)
        apply(subst (1 2) deg_poly_set_0) 
        using d2 by(auto) 
    next
      case (Suc n)
      have t0:\<open>\<forall>k\<le>n. deg_poly_set x' k = deg_poly_set y k\<close> 
        using Suc.hyps Suc.prems(1) Suc.prems(2) le_Suc_eq by blast
      have t':\<open>ideal x' ((carrier R)[X])\<close>
        using Suc.prems(1) f1 by blast
      have t:\<open>deg_poly_set x' (Suc n) = deg_poly_set y (Suc n) \<Longrightarrow> ?case\<close>
        using Suc.hyps Suc.prems(1) Suc.prems(2) le_Suc_eq by presburger
      have \<open> \<forall>k. \<exists>S. lead_coeff_set x' k = genideal R (S k) \<and> finite (S k)\<close>
        by (meson ideal_lead_coeff_set finetely_gen t')
      then have \<open>\<exists>S. \<forall>k. lead_coeff_set x' k = genideal R (S k) \<and> finite (S k)\<close>
        by moura
      then obtain S where t1:\<open>\<forall>k. lead_coeff_set x' k = genideal R (S k) \<and> finite (S k)\<close>
        by (blast)
      then have \<open>\<forall>k\<le>Suc n. lead_coeff_set y (k) = genideal R (S k)\<close>
        using Suc.prems(2) le_Suc_eq by presburger   
      show ?case 
      proof(rule t)
        show \<open>deg_poly_set x' (Suc n) = deg_poly_set y (Suc n)\<close>
          unfolding deg_poly_set 
        proof(safe)
          fix x
          assume 2:\<open>x \<notin> {}\<close> \<open>x \<noteq> []\<close> \<open>x \<in> x'\<close> \<open>degree x = Suc n\<close>
          then show \<open>x \<in> y\<close>
            using Suc.prems(1) by blast
        next
          fix x
          assume 2:\<open>x \<notin> {}\<close> \<open>x \<noteq> []\<close> \<open>x \<in> y\<close> \<open>degree x = Suc n\<close>
          {assume 1:\<open>x \<noteq> []\<close> \<open>x \<in> y\<close> \<open>length x - Suc 0 = Suc n\<close> \<open>x \<notin> x'\<close>
            have \<open>lead_coeff_set x' (Suc n) = lead_coeff_set y (Suc n)\<close>
              using Suc.prems(2) by auto
            then have tp:\<open>coeff x (degree x) \<in> lead_coeff_set x' (Suc n)\<close> 
              by (metis (mono_tags, lifting) "1"(2) "1"(3) One_nat_def 
                  Un_iff deg_poly_set lead_coeff_set_def mem_Collect_eq)
            then have \<open>\<exists>x2. x2\<noteq>x \<and> x2 \<in> x' \<and> coeff x2 (degree x2) = coeff x (degree x)\<and> degree x2 = Suc n\<close>
              unfolding lead_coeff_set_def by(simp) (metis (mono_tags, lifting) "1"(1) "1"(2) "1"(4) 
                  One_nat_def Suc.prems(1) Un_iff coeff.simps(1) deg_poly_set f1 ideal.Icarr lead_coeff_simp
                  mem_Collect_eq partial_object.select_convs(1) polynomial_def singletonD univ_poly_def)
            then obtain x2 where g1:\<open>coeff x2 (degree x2) \<in> lead_coeff_set x' (Suc n) \<and> x2 \<noteq> x \<and>degree x2 
                                  = Suc n\<and> x2\<in> x'\<and> coeff x2 (degree x2) = coeff x (degree x)\<close>
              using tp by force
            then have g2:\<open>x2 \<in> y\<close> 
              using Suc.prems(1) by blast
            then have g3:\<open>x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2 \<in> y\<close>
              using t' 
              by (meson "1"(2) Suc.prems(1) additive_subgroup.a_closed additive_subgroup_def 
                  f1 group.subgroupE(3) ideal_def kxr.add.group_l_invI kxr.add.l_inv_ex)
            then have g4:\<open>x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2 \<notin> x'\<close>
              using t' g1 "1"(2) "1"(4) f1 Suc.prems(1)
                kxr.add.m_assoc kxr.add.r_inv_ex kxr.add.subgroupE(4) kxr.minus_unique kxr.r_zero
              unfolding additive_subgroup_def ideal_def 
              by (smt (verit, best) f1 ideal.Icarr kxr.add.comm_inv_char)
            have \<open>degree x = Suc n \<and> degree x2 = Suc n\<close> 
              using 1 g1 by auto 
            also have \<open>coeff  (inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2) (degree x2) = inv\<^bsub>add_monoid R\<^esub> (coeff x (degree x))\<close>
              by (smt (verit, best) a_inv_def diff_0_eq_0 f4a g1 ideal.Icarr kxr.add.inv_closed 
                  kxr.l_neg length_add list.size(3) max.idem nat.discI t' univ_poly_a_inv_degree univ_poly_zero)
            then have \<open>coeff ((x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2)) (Suc n) = \<zero> \<close>
              by (smt (verit, best) "1"(2) Suc.prems(1) \<open>degree x = Suc n \<and> degree x2 = Suc n\<close> 
                  a_inv_def add.Units_eq add.Units_r_inv lead_coeff_in_carrier f1 f2 g1 ideal.Icarr kxr.add.inv_closed)
            then have *:\<open>\<forall>k\<ge>Suc n. coeff ((x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2)) (k) = \<zero> \<close>
              by (smt (verit, best) "1"(2) Suc.prems(1) a_inv_def calculation coeff_degree f1 f2 f4a g2
                  ideal.Icarr kxr.add.inv_closed l_zero le_eq_less_or_eq univ_poly_a_inv_degree zero_closed)
            then have **:\<open>degree (x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2) \<le> Suc n\<close> 
              unfolding univ_poly_add 
              by (metis (no_types, lifting) a_inv_def calculation f4a g1 ideal.Icarr 
                  max.idem poly_add_degree t' univ_poly_a_inv_degree univ_poly_add)
            then have b0:\<open>coeff ((x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2)) (Suc n) = \<zero> \<close>
              using * by auto
            have b1:\<open>x\<in>(carrier ((carrier R)[X])) \<Longrightarrow> degree x \<le> Suc n \<and> coeff x (Suc n) = \<zero> \<Longrightarrow> degree x \<le> n \<close> for x
              by (metis diff_0_eq_0 diff_Suc_1 le_SucE lead_coeff_simp list.size(3) polynomial_def univ_poly_carrier)
            then have \<open>degree (x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2) \<le> n\<close>
              using b0 b1 ** 
              by (meson Suc.prems(1) f1 g3 ideal.Icarr)
            then obtain k where n:\<open>k\<le>n \<and> k = degree (x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2)\<close> 
              by blast
            then have\<open>x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2 \<in> deg_poly_set y k \<and> x \<oplus>\<^bsub>(carrier R)[X]\<^esub> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> x2 \<notin> deg_poly_set x' k\<close>
              unfolding deg_poly_set using g1 g2 g3 monoid.cases monoid.simps(1) monoid.simps(2) 
                partial_object.select_convs(1) emp_in_i g4 t' by fastforce
            then have False using n t0 by blast
          }note this_is_proof=this 
          then show \<open>x\<in>x'\<close> 
            using this_is_proof "2"(2) "2"(3) "2"(4) One_nat_def by argo  
        qed
      qed
    qed
    using lead_coeff_set_def by presburger
  have chain_is:\<open>x'\<in>C \<and> y\<in>C \<Longrightarrow>x' \<subseteq> y \<or> y \<subseteq> x' \<close> for x' y
    using F unfolding subset.chain_def by(auto)
  from kl have imppp:\<open>x'\<in>C \<and> y\<in>C \<and> x'\<subseteq> y
\<Longrightarrow>(\<forall>k. lead_coeff_set x' k = lead_coeff_set y k) \<longleftrightarrow> (\<forall>k. deg_poly_set x' k = deg_poly_set y k)\<close>
    for x' y 
    by (meson dual_order.refl)
  then have impp:\<open>x'\<in>C \<and> y\<in>C\<Longrightarrow>(\<forall>k. lead_coeff_set x' k = lead_coeff_set y k) 
                  \<longleftrightarrow> (\<forall>k. deg_poly_set x' k = deg_poly_set y k)\<close>
    for x' y
    by (metis chain_is)
  then have sup1:\<open>x'\<in>C \<and> y\<in>C \<Longrightarrow> (x' = y) \<longleftrightarrow>(\<forall>k. lead_coeff_set x' k = lead_coeff_set y k)\<close> for x' y
    using kl0 by presburger
  then have \<open>\<exists>Ux. \<forall>k. Ux k = \<Union>{lead_coeff_set x k |x. x \<in> C} \<close>
    by auto
  then obtain Ux where U_x:\<open>\<forall>k. Ux k = \<Union>{lead_coeff_set x k |x. x \<in> C}\<close> by blast
  then have \<open>\<exists>Uk. \<forall>x\<in>C. ( Uk x = \<Union>{lead_coeff_set x k |k. k\<in>UNIV})\<close> using U0 by auto
  then obtain Uk where U_k:\<open>\<forall>x\<in>C. (Uk x = \<Union>{lead_coeff_set x k |k. k\<in>UNIV})\<close> using U0 by(auto)
  have \<open>(\<Union>{lead_coeff_set x k |x k. x \<in> C \<and> k\<in>UNIV}) = (\<Union>x\<in>C. (\<Union>k. lead_coeff_set x k))\<close>
    by auto
  have \<open>(\<Union>x\<in>C. (\<Union>k. lead_coeff_set x k)) \<in> {lead_coeff_set x k|x k. x\<in>C} \<close>
  proof -
    have n0:\<open>x\<in>C \<and> y\<in>C \<and> x\<subseteq>y \<Longrightarrow> (\<Union>k. lead_coeff_set x k) \<subseteq> (\<Union>k. lead_coeff_set y k)\<close> for x y
      by (simp add: SUP_mono' g0)
    obtain s1 where n1:\<open>(\<forall>x\<in>C. (\<Union>k. lead_coeff_set x k) = lead_coeff_set x (s1 x))\<close>
      using U0 
      by(simp)(metis full_SetCompr_eq)
    then have n4:\<open>(\<Union>x\<in>C. (\<Union>k. lead_coeff_set x k)) = (\<Union>x\<in>C. lead_coeff_set x (s1 x))\<close>
      by auto
    have \<open>x\<in>C \<and> y\<in>C \<Longrightarrow> x\<subseteq>y \<or> y\<subseteq>x\<close> for x y
      using F unfolding subset.chain_def by(auto)
    then have n1:\<open>x\<in>C \<and> y\<in>C \<Longrightarrow> lead_coeff_set x (s1 x) \<subseteq> lead_coeff_set y (s1 y) \<or> 
                  lead_coeff_set y (s1 y) \<subseteq> lead_coeff_set x (s1 x)\<close>
      for x y 
      apply(cases \<open>x\<subseteq>y\<close>)
       apply(rule disjI1)
      subgoal using n0 n1 by auto[1]
      by (metis n0 n1)
    have n2:\<open>subset.chain {I. ideal I R} {lead_coeff_set x (s1 x) |x. x\<in>C}\<close>
      apply(rule subset.chainI)
      using \<open>\<And>x k. x \<in> C \<Longrightarrow> ideal (lead_coeff_set x k) R\<close> apply force
      using n1 by auto
    have n3:\<open>{lead_coeff_set x (s1 x) |x. x\<in>C} \<noteq> {}\<close> 
      using F(1) by blast
    have \<open>(\<Union>x\<in>C. lead_coeff_set x (s1 x)) = (\<Union> {lead_coeff_set x (s1 x) |x. x\<in>C})\<close>
      by auto
    then have \<open>(\<Union>x\<in>C. lead_coeff_set x (s1 x)) \<in> {lead_coeff_set x (s1 x) |x. x\<in>C}\<close>
      using ideal_chain_is_trivial[OF n3 n2] 
      by(auto) 
    then show \<open>(\<Union>x\<in>C. \<Union> (range (lead_coeff_set x))) \<in> {lead_coeff_set x k |x k. x \<in> C} \<close> 
      using n4 by auto
  qed
  then obtain x l where n5:\<open>(\<Union> {lead_coeff_set x k |x k. x\<in>C}) = lead_coeff_set x l \<and> x\<in>C\<close>
    using \<open>\<Union> {lead_coeff_set x k |x k. x \<in> C \<and> k \<in> UNIV} = (\<Union>x\<in>C. \<Union> (range (lead_coeff_set x)))\<close> 
    by auto
  then have \<open>\<forall>y\<in>C. x\<subseteq>y \<longrightarrow> (\<forall> n\<ge>l. (lead_coeff_set y n = lead_coeff_set x l))\<close>
    apply(safe) 
    subgoal using UnionI by blast
    by (meson f8 g0 in_mono)
  have \<open>\<forall>k. \<exists>y'. \<Union>{lead_coeff_set x k |x. x \<in> C} = lead_coeff_set (y' k) k \<and> y' k \<in> C\<close> 
    using U1 by fastforce
  then have \<open>\<exists>y'.  \<forall>k. \<Union>{lead_coeff_set x k |x. x \<in> C} = lead_coeff_set (y' k) k \<and> y' k \<in> C\<close>
    by moura
  then obtain y' where n10:\<open>\<Union>{lead_coeff_set x k |x. x \<in> C} = lead_coeff_set (y' k) k \<and> y' k \<in> C\<close> 
    for k
    by blast
  have n8:\<open>({y' k|k. k\<le>l}\<union>{x}) \<subseteq> C\<close>
    using \<open>\<And>k. \<Union> {lead_coeff_set x k |x. x \<in> C} = lead_coeff_set (y' k) k \<and> y' k \<in> C\<close> n5 by auto
  then have fin:\<open>finite ({y' k|k. k\<le>l}\<union>{x})\<close>
    by(auto)
  have n9:\<open>subset.chain C ({y' k|k. k\<le>l}\<union>{x})\<close>
    apply(rule subset.chainI) 
    using n8 apply force
    using F(2) n8 unfolding subset.chain_def 
    by (meson subset_eq)
  then obtain M where n11:\<open>M\<in>C \<and> (\<Union>({y' k|k. k\<le>l}\<union>{x}) = M)\<close>
    unfolding subset_chain_def 
    by (metis (no_types, lifting) Un_empty Union_in_chain n9 fin insert_not_empty subsetD)
  then have \<open>\<forall>y\<in>C. M\<subseteq>y \<longrightarrow> (\<forall> n\<le>l. (lead_coeff_set y n = lead_coeff_set (y' n) n))\<close>
    using n10 g0 apply(safe)
    using Sup_le_iff mem_Collect_eq by blast+
  then have nn:\<open>\<forall>y\<in>C. \<forall>n\<le>l. M\<subseteq>y \<longrightarrow> (lead_coeff_set (y) n = lead_coeff_set M n)\<close>
    using \<open>M \<in> C \<and> \<Union> ({y' k |k. k \<le> l} \<union> {x}) = M\<close> by auto
  then have \<open>\<forall>y\<in>C. \<forall>n\<ge>l. M\<subseteq>y \<longrightarrow> (lead_coeff_set (y) n = lead_coeff_set M n)\<close>
    using \<open>M \<in> C \<and> \<Union> ({y' k |k. k \<le> l} \<union> {x}) = M\<close>  
    using \<open>\<forall>y\<in>C. x \<subseteq> y \<longrightarrow> (\<forall>n\<ge>l. lead_coeff_set y n = lead_coeff_set x l)\<close> by auto
  then have n_1:\<open>\<forall>y\<in>C. M \<subseteq> y \<longrightarrow> M = y\<close>
    by (metis n11 sup1 nn linorder_le_cases)
  have \<open>\<Union>C = M\<close>
  proof(rule ccontr)
    assume h_1:\<open>\<Union>C \<noteq> M\<close>
    then have f_0:\<open>\<exists>x\<in>\<Union>C. x\<notin>M\<close>
      by (meson UnionI \<open>M \<in> C \<and> \<Union> ({y' k |k. k \<le> l} \<union> {x}) = M\<close> subset_antisym subset_iff)
    then obtain x where f_1:\<open>x\<in>\<Union>C \<and> x\<notin>M\<close> by blast
    then have f_3:\<open>\<exists>M'\<in>C. x\<in>M'\<close> 
      by blast 
    then obtain M' where f_2:\<open>x\<in>M'\<close> by blast
    then have \<open>M\<subseteq>M' \<and> M\<noteq>M'\<close>
      using F unfolding subset_chain_def 
      by (metis f_1 f_3 n11 n_1 subsetD)
    then show False 
      using n_1 n11 f_1 f_3 F(2) unfolding subset_chain_def
      by (metis subsetD)
  qed
  then show \<open>\<Union> C \<in> C\<close> 
    by (simp add: n11)
qed

subsection \<open>Some properties of noetherian rings\<close>
text \<open>Assuming I is an ideal of A and A is noetherian, then \<open>A/I\<close> is noetherian.\<close>
lemma noetherian_ring_imp_quot_noetherian_ring:
  assumes h1:\<open>noetherian_ring A\<close> and h2:\<open>ideal I A\<close> 
  shows\<open>noetherian_ring (A Quot I)\<close>
proof -
  interpret cr:ring A
    using h1 unfolding noetherian_ring_def by(auto)
  interpret crI: ring "(A Quot I)"
    by (simp add: h2 ideal.quotient_is_ring)
  interpret rhr:ring_hom_ring A "(A Quot I)" "((+>\<^bsub>A\<^esub>) I)"
    using h2 ideal.rcos_ring_hom_ring by blast
  have rhr_p:\<open>ring_hom_ring A (A Quot I) ((+>\<^bsub>A\<^esub>) I)\<close>
    using h2 ideal.rcos_ring_hom_ring by blast
  from h1 show ?thesis 
  proof(intro ring.trivial_ideal_chain_imp_noetherian)
    assume 1:\<open>noetherian_ring A\<close>
    show \<open>ring (A Quot I)\<close> 
      by (simp add: crI.ring_axioms)
  next
    fix C
    assume 1:\<open>noetherian_ring A\<close> \<open>C \<noteq> {}\<close> \<open>subset.chain {Ia. ideal Ia (A Quot I)} C\<close>
    let ?f=\<open>the_inv_into ({J. ideal J A \<and> I \<subseteq> J}) (\<lambda>x. (+>\<^bsub>A\<^esub>) I ` x)\<close>
    have inv_imp:\<open>\<forall>J\<in>{J. ideal J A \<and> I \<subseteq> J}. ?f ((+>\<^bsub>A\<^esub>) I ` J) = J\<close>
      using the_inv_into_onto[of \<open>\<lambda>x. (+>\<^bsub>A\<^esub>) I`x\<close> \<open>{J. ideal J A \<and> I \<subseteq> J}\<close>] 
      apply(subst set_eq_iff)
      by (metis (no_types, lifting) Collect_cong bij_betw_def cr.ring_axioms h2 
          ring.quot_ideal_correspondence the_inv_into_f_f)+
    have rule_inv:\<open>x \<in> the_inv_into {J. ideal J A \<and> I \<subseteq> J} ((`) ((+>\<^bsub>A\<^esub>) I)) J 
                  \<Longrightarrow>ideal J (A Quot I) \<Longrightarrow> ideal J' (A Quot I) \<Longrightarrow> J \<subseteq> J' 
                  \<Longrightarrow> x \<in> the_inv_into {J. ideal J A \<and> I \<subseteq> J} ((`) ((+>\<^bsub>A\<^esub>) I)) J'\<close>
      for x J J'
      by (smt (verit, best) Collect_cong additive_subgroup.a_subset bij_betw_imp_surj_on 
          cr.canonical_proj_vimage_mem_iff f_the_inv_into_f_bij_betw h2 ideal_def image_eqI 
          image_eqI inj_onI mem_Collect_eq mem_Collect_eq ring.ideal_incl_iff 
          ring.quot_ideal_correspondence subsetD the_inv_into_onto)
    have inv:\<open>bij_betw ?f {J. ideal J (A Quot I)} {J. ideal J A \<and> I \<subseteq> J} 
\<and> (\<forall>J J'. {J,J'} \<subseteq> {J. ideal J (A Quot I)} \<and> J \<subseteq> J' \<longrightarrow> ?f J \<subseteq> ?f J')\<close>
      using ring.quot_ideal_correspondence[of A I]  the_inv_into_onto[of \<open>\<lambda>x. (+>\<^bsub>A\<^esub>) I`x\<close> 
          \<open>{J. ideal J A \<and> I \<subseteq> J}\<close>]
      unfolding bij_betw_def 
      using cr.ring_axioms h2 the_inv_into_onto inj_on_the_inv_into f_the_inv_into_f
        inj_on_the_inv_into[of \<open>\<lambda>x. (+>\<^bsub>A\<^esub>) I`x\<close> \<open>{J. ideal J A \<and> I \<subseteq> J}\<close>] 
        additive_subgroup.a_subset cr.canonical_proj_vimage_mem_iff 
        f_the_inv_into_f[of \<open>(\<lambda>x. (+>\<^bsub>A\<^esub>) I ` x)\<close> \<open>{J. ideal J A \<and> I \<subseteq> J}\<close>] 
        ideal_def image_eqI mem_Collect_eq ring.ideal_incl_iff subsetD  
      by(auto simp: rule_inv) 
    then have \<open>\<forall>c\<in>C. ideal (?f c) A\<close> 
      using 1(3) inv unfolding subset.chain_def 
      using bij_betwE by fast
    have inv_imp2:\<open>\<forall>J\<in>{J. ideal J (A Quot I)}. ((+>\<^bsub>A\<^esub>) I ` ?f J) = J\<close>
      by (smt (verit, del_insts) Collect_cong bij_betw_def cr.ring_axioms 
          h2 imageE inv_imp ring.quot_ideal_correspondence)
    have \<open>\<forall>c c'. c \<in>C \<and> c' \<in>C \<and> c\<subseteq>c' \<longrightarrow> ?f c \<subseteq> ?f c'\<close>
      using inv using 1(3) unfolding subset_chain_def 
      by (meson empty_subsetI insert_subset subsetD)    
    then have sub1:\<open>subset.chain {Ia. ideal Ia (A)} (?f`C)\<close>
      using 1(3) unfolding subset_chain_def image_def 
      using \<open>\<forall>c\<in>C. ideal (?f c) A\<close> apply(safe)
       apply (simp add: image_def)
      by (meson in_mono)
    have sub2 :\<open>(?f`C) \<noteq> {}\<close> 
      using "1"(2) by blast
    then have k0:\<open>(\<Union>(?f`C)) \<in> (?f`C)\<close>
      by (metis (no_types) h1 noetherian_ring.ideal_chain_is_trivial sub1 sub2)
    then have \<open>(+>\<^bsub>A\<^esub>) I ` (\<Union>(?f`C)) = (\<Union>C)\<close> 
      apply(safe)
       apply (smt (verit, del_insts) "1"(3) UnionI image_eqI inv_imp2 subset.chain_def subsetD)
      by (smt (verit, best) "1"(3) SUP_upper in_mono inv_imp2 subset_chain_def subset_image_iff)
    then show \<open>\<Union> C \<in> C\<close> 
      by (smt (verit) "1"(3) k0 image_iff inv_imp2 subset.chain_def subsetD)
  qed
qed

text \<open>If A is noetherian and \<open>A \<simeq> B\<close> then B is noetherian.\<close>
lemma noetherian_isom_imp_noetherian:
  assumes h1:\<open>noetherian_ring A \<and> ring B \<and>  A \<simeq> B\<close>
  shows \<open>noetherian_ring B\<close>
proof(rule ring.trivial_ideal_chain_imp_noetherian)
  show \<open>ring B\<close> using h1 by(simp)
next
  fix C
  assume h2:\<open>C\<noteq>{}\<close> and h3:\<open>subset.chain {I. ideal I B} C\<close>
  obtain g where bij_g:\<open>bij_betw g (carrier A) (carrier B) \<and> g\<in>ring_hom A B\<close>
    using h1 is_ring_iso_def ring_iso_def by fastforce
  obtain h where bij_h:\<open>bij_betw h (carrier B) (carrier A) \<and> h\<in>ring_hom B A \<and> h = the_inv_into (carrier A) g\<close>
    using h1 is_ring_iso_def ring_iso_def 
    by (smt (verit, ccfv_SIG) bij_betwE bij_betw_def bij_betw_the_inv_into bij_g f_the_inv_into_f 
        noetherian_ring.axioms(1) ring.ring_simprules(1) ring.ring_simprules(5) ring.ring_simprules(6) 
        ring_hom_add ring_hom_memI ring_hom_mult ring_hom_one the_inv_into_f_f)
  from bij_g have f0:\<open>ideal I A \<Longrightarrow> ideal (g ` I) B\<close> for I
    using h1 img_ideal_is_ideal noetherian_ring_def ring_iso_def by fastforce
  from bij_h have f2:\<open>ideal I B \<Longrightarrow> ideal (h ` I) A\<close> for I
    using h1 img_ideal_is_ideal noetherian_ring_def ring_iso_def by fastforce
  then obtain g' where jj1:\<open>g' = the_inv_into (carrier A) (g)\<close>
    by blast
  then have f1:\<open>\<forall>a\<in>carrier A. \<forall>b\<in>carrier B. g (g' b) = b \<and> g' (g a) = a\<close>
    by (meson bij_betw_def bij_g f_the_inv_into_f_bij_betw the_inv_into_f_f) 
  then have \<open>\<exists>f'. bij_betw f' {I. ideal I A} {I. ideal I B}\<close>
    apply(intro exI[where x=\<open>(`) g\<close>])
    apply(rule bij_betw_byWitness[where f'=\<open>(`) h\<close>])
    unfolding image_def apply(safe) 
    using jj1 bij_h h1 ideal.Icarr ring.ring_simprules(6) apply fastforce
    using jj1 additive_subgroup.a_subset bij_h h1 ideal.axioms(1) ring.ring_simprules(6) apply fastforce
       apply (metis bij_betwE bij_h ideal.Icarr jj1)
    using bij_g bij_h f_the_inv_into_f_bij_betw ideal.Icarr apply fastforce
     apply(fold image_def) 
    using f0 apply presburger
    using f2 by presburger
  then have f5:\<open>\<forall>J\<in>{I. ideal I A}. h ` g ` J = J \<and> (\<forall>J\<in>{I. ideal I B}. g ` h ` J = J)\<close>
    unfolding image_def apply(safe) 
       apply (metis bij_betw_def bij_g bij_h ideal.Icarr the_inv_into_f_f)
      apply (smt (verit, best) bij_betwE bij_g bij_h f1 ideal.Icarr jj1 mem_Collect_eq)
     apply (metis bij_g bij_h f_the_inv_into_f_bij_betw ideal.Icarr)
    by (metis (mono_tags, lifting) bij_g bij_h f_the_inv_into_f_bij_betw ideal.Icarr mem_Collect_eq)
  then have \<open>\<forall>c\<in>C. ideal (h ` c) A\<close> 
    unfolding subset.chain_def 
    by (metis f2 h3 mem_Collect_eq subset_chain_def subset_eq)
  then have inv_imp2:\<open>\<forall>J\<in>{J. ideal J (B)}. (g ` h ` J) = J\<close>
    by (metis f5 f2 mem_Collect_eq)
  then have sub1:\<open>subset.chain {Ia. ideal Ia (A)} ((\<lambda>x. h ` x) `C)\<close>
    unfolding subset_chain_def image_def apply(safe)
     apply (metis \<open>\<forall>c\<in>C. ideal (h ` c) A\<close> image_def)
    by (metis (no_types, lifting) h3 subsetD subset_chain_def)
  have sub2 :\<open>((\<lambda>x. h ` x)`C) \<noteq> {}\<close> 
    using h2 by blast
  then have f10:\<open>(\<Union>((\<lambda>x. h ` x)`C)) \<in> ((\<lambda>x. h ` x)`C)\<close>
    by (meson h1 noetherian_ring.ideal_chain_is_trivial sub1)
  then have f9:\<open>g ` (\<Union>((\<lambda>x. h ` x)`C)) = (\<Union>C)\<close> 
    apply(safe) 
     apply (metis UnionI additive_subgroup.a_Hcarr bij_h f1 h1 h3 ideal.axioms(1) jj1 
        mem_Collect_eq noetherian_ring_def ring.ring_simprules(6) subset.chain_def subsetD) 
    by (smt (verit, del_insts) UN_iff h3 image_def inv_imp2 mem_Collect_eq subsetD subset_chain_def)
  show \<open>\<Union>C \<in> C\<close> 
    by (smt (verit, best) f10 f9 h3 image_iff in_mono inv_imp2 subset.chain_def)
qed

lemma (in domain) subring:\<open>subring (carrier R) R\<close>
  using carrier_is_subring by auto

subsection \<open>Some properties of the polynomial rings regarding ideals and quotients\<close>

lemma (in domain) gen_is_cgen:\<open>(genideal ((carrier R)[X]) {X}) = cgenideal ((carrier R)[X]) X\<close>
  by (simp add: cring.cgenideal_eq_genideal domain.univ_poly_is_cring domain_axioms subring var_closed(1))

lemma (in domain) principal_X:\<open>principalideal (genideal ((carrier R)[X]) {X}) ((carrier R)[X])\<close>
  apply(subst gen_is_cgen)
  by (simp add: cring.cgenideal_is_principalideal domain.univ_poly_is_cring domain_axioms subring var_closed(1)) 

named_theorems poly

lemma (in ring) PIdl_X[poly]:
  \<open>(cgenideal ((carrier R)[X]) X) = {a\<otimes>\<^bsub>(carrier R) [X]\<^esub>X |a. a\<in>carrier((carrier R)[X])}\<close>
  unfolding cgenideal_def by(auto)

lemma (in domain) Idl_X[poly]:
  \<open>(genideal ((carrier R)[X]) {X})= {a\<otimes>\<^bsub>(carrier R) [X]\<^esub>X |a. a\<in>carrier((carrier R)[X])}\<close>
  using PIdl_X gen_is_cgen by argo
lemma (in domain) Idl_X_is_X[poly]:
  \<open>p\<in>(genideal ((carrier R)[X]) {X}) \<Longrightarrow> \<exists>a\<in>carrier((carrier R)[X]). p = a\<otimes>\<^bsub>(carrier R) [X]\<^esub>X \<close> 
  using gen_is_cgen Idl_X by auto

lemma (in ring) degree_of_nonempty_p[poly]:\<open>a\<in>carrier((carrier R)[X]) \<and> a\<noteq>[] \<Longrightarrow> coeff a (degree a) \<noteq> \<zero>\<close>
  by (metis lead_coeff_simp polynomial_def univ_poly_carrier)

lemma (in domain)coeff_0_of_mult_X[poly]:\<open>a\<in>carrier((carrier R)[X]) \<Longrightarrow> coeff (a\<otimes>\<^bsub>(carrier R) [X]\<^esub>X) 0 = \<zero>\<close>
  apply(cases \<open>a=[]\<close>) 
   apply (simp add: domain.poly_mult_var domain_axioms subring univ_poly_zero_closed)
  apply(induct a)
  using coeff.simps(1) poly_mult.simps(1) 
   apply (simp add: univ_poly_mult)
  by (simp add: append_coeff poly_mult_var subring)

lemma (in domain)zero_coeff_of_Idl_X[poly]:\<open>p\<in>genideal ((carrier R)[X]) {X} \<Longrightarrow> coeff p 0 = \<zero>\<close>
  using Idl_X coeff_0_of_mult_X by auto

lemma (in domain) mult_X_append_0[poly]:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow>  p\<noteq>[] \<Longrightarrow> poly_mult p X = p@[\<zero>]\<close>
  using poly_mult_var[of \<open>(carrier R)\<close> p] 
  by(auto simp add: poly_mult_var'(2) polynomial_incl subring univ_poly_carrier univ_poly_mult) 


lemma (in ring) polynomial_incl':\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> set p \<subseteq>(carrier R)\<close> for p
  unfolding univ_poly_def
  using polynomial_incl by auto

lemma (in ring) hd_in_carrier:\<open>p\<noteq> [] \<Longrightarrow> p\<in>carrier((carrier R)[X]) \<Longrightarrow> hd p \<in>(carrier R)\<close> for p
  using polynomial_incl' unfolding univ_poly_def 
  using list.set_sel(1) by blast

lemma (in ring) inv_in_carrier:
  \<open>p\<noteq>[] \<Longrightarrow> p\<in>carrier((carrier R)[X]) \<Longrightarrow> (inv\<^bsub>add_monoid R\<^esub> (hd p)) \<in>(carrier R)\<close> for p
  using hd_in_carrier  by simp

lemma (in ring) inv_ld_coeff:
  \<open>p\<noteq>[] \<Longrightarrow> p\<in>carrier((carrier R)[X]) \<Longrightarrow> (inv\<^bsub>add_monoid R\<^esub> (hd p)#replicate (degree p) \<zero>)\<in>carrier((carrier R)[X])\<close>
  for p
  using inv_in_carrier  by (metis a_inv_def  add.inv_eq_1_iff hd_in_carrier list.sel(1) local.monom_def 
      monom_in_carrier polynomial_def univ_poly_carrier)

lemma (in ring) take_in_RX:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> n\<le>length p \<Longrightarrow> (set (take n p)) \<subseteq>(carrier R)\<close> for p n
  using set_take_subset[of n p] polynomial_incl' by blast

lemma (in ring) normalize_take_is_poly:
  \<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> n\<le>length p \<Longrightarrow> normalize (take n p) \<in> carrier((carrier R)[X])\<close> for n p
  using take_in_RX by (meson normalize_gives_polynomial univ_poly_carrier)


lemma (in ring) normalize_take_is_take:\<open>p\<in>carrier((carrier R)[X]) \<and>n\<le>length p \<Longrightarrow> normalize (take n p) = take n p\<close>
  by (metis bot_nat_0.not_eq_extremum degree_of_nonempty_p hd_take lead_coeff_simp 
      normalize.elims normalize.simps(1) take_eq_Nil)

lemma (in ring) take_in_carrier:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> n\<le>length p \<Longrightarrow> (take n p) \<in> carrier((carrier R)[X])\<close>
  using normalize_take_is_poly normalize_take_is_take by force

lemma (in domain) take_misc_poly:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> p\<noteq>[] \<Longrightarrow> coeff p 0 = \<zero> \<Longrightarrow> ((take (degree p) p))\<otimes>\<^bsub>(carrier R) [X]\<^esub>X = p\<close> for p
  apply(unfold univ_poly_mult) 
  apply(cases \<open>p=[]\<close>) 
  subgoal by(simp)
  apply(subst mult_X_append_0)
    apply (simp add: normalize_take_is_poly univ_poly_carrier)
  using normalize_take_is_poly normalize_take_is_take apply force
  using degree_of_nonempty_p normalize_take_is_take apply force
  by (metis One_nat_def Suc_pred coeff_nth diff_Suc_eq_diff_pred diff_less le_refl 
      length_greater_0_conv less_one take_Suc_conv_app_nth take_all)

lemma (in ring) length_geq_2:\<open>normalize p\<noteq>[] \<and> \<not>(\<exists>a. normalize p=[a]) \<Longrightarrow> length p \<ge> 2\<close> for p::\<open>'a list\<close>
  apply(induct p) 
  using not_less_eq_eq 
  by (auto split:if_splits)

lemma (in ring) norm_take_not_mt:\<open>length (normalize p) \<ge> 2 \<Longrightarrow> normalize (take (degree p) p) \<noteq> []\<close> for p::\<open>'a list\<close>
  using length_geq_2 
  apply(induct p rule:normalize.induct) 
   apply simp
  using One_nat_def Suc_eq_plus1 Suc_le_lessD list.sel(3) list.size(3)
    list.size(4) nat_less_le normalize.elims numeral_2_eq_2 take_Cons' take_eq_Nil 
  by (smt (z3) length_tl list.sel(1) normalize.simps(2))

lemma (in ring) normalize_take_invariant:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> p\<noteq>[] \<Longrightarrow> (normalize (take (degree p) p))@[coeff p 0] = p\<close>
  for p
  apply(subst normalize_take_is_take)
   apply simp
  by (metis One_nat_def Suc_pred coeff_nth diff_Suc_eq_diff_pred diff_less le_refl 
      length_greater_0_conv less_one take_Suc_conv_app_nth take_all)

lemma (in domain) lower_coeff_add:\<open>p\<noteq>[] \<Longrightarrow> p\<in>carrier((carrier R)[X])\<and> b \<in> (carrier R) 
\<Longrightarrow> coeff (((normalize p) @[\<zero>])\<oplus>\<^bsub>(carrier R) [X]\<^esub> [b]) = coeff ((normalize p) @[b])\<close> for p b
  unfolding univ_poly_add 
  apply(subst poly_add_coeff) 
    apply (metis local.ring_axioms mult_X_append_0 normalize_polynomial ring.poly_mult_in_carrier 
      ring.polynomial_in_carrier subring univ_poly_carrier var_closed(2))
  by(auto simp add:fun_eq_iff append_coeff  polynomial_incl' normalize_polynomial univ_poly_carrier)

lemma (in ring) cons_in_RX:\<open>a@p\<in>carrier((carrier R)[X]) \<Longrightarrow> normalize p\<in>carrier((carrier R)[X])\<close>
proof -
  assume h1:\<open>a@p\<in>carrier((carrier R)[X])\<close>
  then have \<open>set (a@p) \<subseteq> (carrier R)\<close> 
    using polynomial_incl' by presburger
  then have \<open>set p \<subseteq> (carrier R)\<close>
    by simp
  then show ?thesis 
    using normalize_gives_polynomial univ_poly_carrier by blast
qed 

lemma (in ring) p_in_norm:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> normalize p = p\<close>
  by (simp add: normalize_polynomial univ_poly_carrier)

lemma (in domain) lower_coeff_add':\<open>p\<noteq>[] \<Longrightarrow> p\<in>carrier((carrier R)[X])\<and> b \<in> (carrier R) \<Longrightarrow>  (((normalize p) @[\<zero>])\<oplus>\<^bsub>(carrier R) [X]\<^esub> [b]) = ((normalize p) @[b])\<close> for p b
proof -
  interpret kcr:cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by auto
  assume h1:\<open>p\<noteq>[]\<close> \<open>p\<in>carrier((carrier R)[X])\<and> b \<in> (carrier R)\<close>
  have f0:\<open>b\<noteq>\<zero> \<Longrightarrow> polynomial (carrier R) p \<and> polynomial (carrier R) [b]\<close>
    by (metis h1(2) insert_subset polynomial_incl' list.sel(1) list.simps(15) polynomial_def univ_poly_carrier)
  with h1 show ?thesis
    apply(cases \<open>b=\<zero>\<close>)
     apply (metis append_self_conv2 domain.mult_X_append_0 domain_axioms kcr.r_zero kcr.zero_closed 
        polynomial_incl' p_in_norm poly_add_append_zero poly_mult_var'(2) univ_poly_add univ_poly_zero)
    unfolding univ_poly_add apply(subst coeff_iff_polynomial_cond[of \<open>(carrier R)\<close>])
      apply (metis polynomial_incl' mult_X_append_0 normalize_polynomial poly_add_closed poly_mult_is_polynomial subring var_closed(1))
     apply (metis (mono_tags, lifting) Un_insert_right append_Nil2 hd_append2 insert_subset 
        list.simps(15) normalize_polynomial polynomial_def set_append)
    by (metis lower_coeff_add univ_poly_add)
qed

lemma (in domain) poly_invariant:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> p\<noteq>[] \<Longrightarrow> ((normalize (take (degree p) p))\<otimes>\<^bsub>(carrier R) [X]\<^esub>X ) \<oplus>\<^bsub>(carrier R) [X]\<^esub> [coeff p 0] = p\<close>
  for p
proof -
  interpret kcr:cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by auto
  assume h1:\<open>p \<in> carrier (poly_ring R)\<close> \<open> p \<noteq> [] \<close>
  with h1 show ?thesis
    using take_misc_poly apply(cases \<open>p=[]\<close>) apply(simp)
    apply(cases \<open>\<exists>a. p=[a]\<close>) 
     apply (metis One_nat_def diff_is_0_eq' kcr.l_zero le_refl lead_coeff_simp length_Cons 
        list.sel(1) list.size(3) normalize.simps(1) poly_mult.simps(1) take0 univ_poly_mult univ_poly_zero)
    unfolding univ_poly_mult
    apply(subst mult_X_append_0)
    using diff_le_self normalize_take_is_poly apply presburger
    using length_geq_2[of p] norm_take_not_mt[of p] 
     apply (metis coeff_iff_length_cond degree_of_nonempty_p lead_coeff_simp normalize_coeff normalize_length_eq)
    by (metis (no_types, lifting) append.right_neutral append_self_conv2 coeff_in_carrier 
        diff_le_self polynomial_incl' normalize_take_invariant lower_coeff_add' normalize_take_is_poly local.normalize_idem) 
qed

lemma (in domain) gen_ideal_X_iff:\<open>p\<in>(genideal ((carrier R)[X]) {X}) \<longleftrightarrow> (p\<in>carrier ((carrier R)[X]) \<and> coeff p 0 = \<zero>)\<close> for p::\<open>'a list\<close>
  using poly take_misc_poly apply(safe) 
  using domain.univ_poly_is_ring domain_axioms monoid.m_closed ring_def subring var_closed(1) 
    apply (metis (no_types, lifting))
   apply (meson domain.univ_poly_is_ring domain_axioms monoid.m_closed ring_def subring var_closed(1))
  by (smt (verit, ccfv_threshold) mem_Collect_eq nat_le_linear poly_mult.simps(1) take_all 
      take_in_carrier univ_poly_mult)

lemma (in domain) gen_ideal_X_iff':\<open>(genideal ((carrier R)[X]) {X}) = {p\<in>carrier ((carrier R)[X]). coeff p 0 = \<zero>}\<close> for p::\<open>'a list\<close>
  using gen_ideal_X_iff by auto


lemma (in domain) quot_X_is_R:\<open>carrier (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X})) 
= {{x\<in>carrier((carrier R)[X]). coeff x 0 = a} |a. a\<in>(carrier R)}\<close>
proof(subst set_eq_subset, safe)
  interpret kcr:cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by auto
  fix x
  assume h1:\<open>x \<in> carrier ((carrier R) [X] Quot (genideal ((carrier R)[X]) {X}))\<close>
  have l0:\<open>as\<noteq>[] \<Longrightarrow> take (length as) (a#as) = a#take (degree as) as\<close> for a::'a and as
    by (simp add: take_Cons')
  have rule_U:\<open>xaa \<in> (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa}) 
                = (\<exists>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. xaa = x \<oplus>\<^bsub>poly_ring R\<^esub> xa)\<close>
    for xaa xa
    by auto
  from h1 have \<open>\<exists>xa\<in>carrier (poly_ring R). x = (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa})\<close>
    unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def  by simp
  with h1 show \<open>\<exists>a. x = {x \<in> carrier (poly_ring R). local.coeff x 0 = a} \<and> a \<in> carrier R\<close>
    unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def 
  proof(safe, fold FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def )
    fix xa
    assume h1:\<open>(\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa})
          \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X})\<close>
      \<open>xa \<in> carrier (poly_ring R)\<close>
      \<open>x = (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa})\<close>
      \<open>x \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X})\<close>
      \<open>\<exists>xa\<in>carrier (poly_ring R). x = (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa})\<close>
    show \<open>\<exists>a. (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa}) =
              {x \<in> carrier (poly_ring R). local.coeff x 0 = a} \<and>
              a \<in> carrier R\<close>
    proof(rule exI[where x=\<open>coeff xa 0\<close>], safe) 
      fix x' xaa
      assume h2:\<open>xaa \<in> Idl\<^bsub>poly_ring R\<^esub> {X}\<close>
      with h1 show \<open>xaa \<oplus>\<^bsub>poly_ring R\<^esub> xa \<in> carrier (poly_ring R)\<close>
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def  
        using Idl_X subring var_closed(1) by auto[1]
      show \<open>local.coeff (xaa \<oplus>\<^bsub>poly_ring R\<^esub> xa) 0 = local.coeff xa 0\<close>
        apply(insert h1 h2)
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def
        using Idl_X subring var_closed(1) apply(safe)
        apply(frule coeff_0_of_mult_X) 
        apply(frule zero_coeff_of_Idl_X)
        apply(subst coeffs_of_add_poly)
        using gen_ideal_X_iff apply blast
         apply blast
        by (simp add: polynomial_incl univ_poly_carrier)
    next
      fix y
      assume h2:\<open>y \<in> carrier (poly_ring R)\<close>
        \<open>local.coeff y 0 = local.coeff xa 0\<close>
      with h1 show \<open>y \<in> (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa})\<close>
        apply(subst rule_U)
        apply(rule bexI[where x=\<open>y\<oplus>\<^bsub>(carrier R) [X]\<^esub>(inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> xa)\<close>])
         apply (metis a_inv_def kcr.add.inv_solve_right' kcr.minus_closed kcr.minus_eq)
        by (metis a_inv_def coeff.simps(1) coeffs_of_add_poly gen_ideal_X_iff kcr.add.inv_closed 
            kcr.add.inv_solve_right kcr.add.m_closed kcr.add.m_lcomm 
            kcr.r_zero kcr.zero_closed univ_poly_zero)
    next
      from h1 show \<open>local.coeff xa 0 \<in> carrier R\<close>
        by (simp add: polynomial_incl univ_poly_carrier)
    qed
  qed
next
  interpret kcr:cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by auto
  fix a
  assume h1:\<open>a \<in> (carrier R)\<close> 
  have p_h1:\<open>a\<noteq>\<zero> \<Longrightarrow> [a] \<in> carrier ((carrier R)[X])\<close>
    by (metis Diff_iff const_is_polynomial empty_iff h1 insert_iff univ_poly_carrier)
  have rule_s:\<open>{x \<in> carrier (poly_ring R). local.coeff x 0 = a} \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}) =
(\<exists>x\<in>carrier (poly_ring R).
       {x \<in> carrier (poly_ring R). local.coeff x 0 = a} =
       (\<Union>xa\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {xa \<oplus>\<^bsub>poly_ring R\<^esub> x}) )\<close>
    unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def by(auto)
  show \<open>{x \<in> carrier (poly_ring R). local.coeff x 0 = a}
           \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X})\<close>
    apply(subst rule_s)
    apply(cases \<open>a=\<zero>\<close>)
     apply(rule bexI[where x=\<open>[]\<close>])
      apply(subst Idl_X) apply(safe)[1] 
        apply (metis (no_types, lifting) PIdl_X UN_iff gen_ideal_X_iff gen_is_cgen 
        insert_iff kcr.r_zero univ_poly_zero)
    using subring var_closed(1) apply force
      apply (metis coeff_0_of_mult_X kcr.m_closed kcr.r_zero subring univ_poly_zero var_closed(1))
     apply blast
    apply(rule bexI[where x=\<open>[a]\<close>]) 
     apply(subst Idl_X)
     apply(safe)
       apply(simp) 
       apply (metis poly_invariant coeff.simps(1) diff_le_self normalize_take_is_poly)
    using h1 subring var_closed(1) p_h1 apply(auto)[1]
     apply (metis coeffs_of_add_poly diff_Suc_1 domain.coeff_0_of_mult_X domain.poly_mult_var 
        domain_axioms kcr.l_zero kcr.m_closed kcr.zero_closed lead_coeff_simp length_Cons
        list.distinct(1) list.sel(1) list.size(3) p_h1 subring univ_poly_zero var_closed(1))
    using p_h1 by auto
qed

lemma (in domain) uniq_a_quot:
  \<open>c\<in> carrier (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X})) \<Longrightarrow> \<exists>!a\<in>(carrier R). \<forall>y\<in>c. coeff y 0 = a\<close>
proof(subst (asm) quot_X_is_R, safe)
  fix a
  assume h1:\<open>a \<in> carrier R\<close> \<open>c = {x \<in> carrier (poly_ring R). local.coeff x 0 = a}\<close>
  then show \<open>\<exists>aa. aa \<in> carrier R \<and>
              (\<forall>y\<in>{x \<in> carrier (poly_ring R). local.coeff x 0 = a}. local.coeff y 0 = aa)\<close>
    apply(intro exI[where x=a]) 
    by fastforce
next
  fix a aa y
  assume h1:\<open>a \<in> carrier R\<close> \<open>c = {x \<in> carrier (poly_ring R). local.coeff x 0 = a}\<close> \<open>aa \<in> carrier R\<close>
    \<open>\<forall>y\<in>{x \<in> carrier (poly_ring R). local.coeff x 0 = a}. local.coeff y 0 = aa\<close> \<open>y \<in> carrier R\<close>
    \<open>\<forall>ya\<in>{x \<in> carrier (poly_ring R). local.coeff x 0 = a}. local.coeff ya 0 = y\<close>
  have \<open>{x |x. x \<in> carrier ((carrier R) [X]) \<and> local.coeff x 0 = a} \<noteq> {}\<close>
    apply(subst ex_in_conv[symmetric]) apply(cases \<open>a=\<zero>\<close>)
     apply(rule exI[where x=\<open>[]\<close>]) 
     apply(fastforce)
    apply(rule exI[where x=\<open>[a]\<close>])
    using h1(1) apply(safe) 
    apply(rule exI[where x=\<open>[a]\<close>])apply(simp)
    by (metis empty_subsetI insert_subset list.sel(1)
        list.simps(15) polynomialI set_empty univ_poly_carrier)
  then show \<open>aa = y\<close>
    using  h1(4) h1(6) all_not_in_conv[of \<open>{x |x. x \<in> carrier (poly_ring R) \<and> local.coeff x 0 = a}\<close>]
    by (metis (no_types, lifting))
qed

lemma (in ring) append_in_carrier:\<open>a\<in>carrier((carrier R)[X]) \<and> b\<in>carrier((carrier R)[X]) \<Longrightarrow> a@b \<in> carrier((carrier R)[X])\<close>
  apply(induct b arbitrary:a)
  by (metis append_self_conv2 hd_append2 le_sup_iff mem_Collect_eq 
      partial_object.select_convs(1) polynomial_def set_append univ_poly_def)+

lemma (in domain) The_a_is_a:\<open>a\<in>(carrier R) \<Longrightarrow> 
(THE aa. \<forall>y\<in>{x |x. x \<in> carrier ((carrier R) [X]) \<and> local.coeff x 0 = a}. local.coeff y 0 = aa) = a\<close>
proof -
  assume h1:\<open>a\<in>(carrier R)\<close>
  have \<open>\<exists>c \<in> carrier (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X})). 
          c = {x |x. x \<in> carrier ((carrier R) [X]) \<and> local.coeff x 0 = a}\<close>
    apply(subst quot_X_is_R)  
    using h1 by auto
  then obtain c where f0:\<open>c = {x |x. x \<in> carrier ((carrier R) [X]) \<and> local.coeff x 0 = a} 
                          \<and> c \<in> carrier (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X}))\<close>
    by blast
  then have \<open>(THE aa. \<forall>y\<in>c. local.coeff y 0 = aa) = a\<close>
    by (smt (verit, best) coeff.simps(1) h1 mem_Collect_eq theI uniq_a_quot univ_poly_zero_closed zero_closed)
  then show ?thesis 
    by (simp add:f0)
qed 

lemma (in ring) poly_mult_in_carrier2:
  "\<lbrakk> set p1 \<subseteq> carrier R; set p2 \<subseteq> carrier R \<rbrakk> \<Longrightarrow> poly_mult p1 p2 \<in> carrier ((carrier R)[X])"
  using poly_mult_is_polynomial polynomial_in_carrier carrier_is_subring 
  by (simp add: univ_poly_carrier)

lemma (in ring) normalize_equiv:\<open>polynomial (carrier R) (normalize p) \<longleftrightarrow> (coeff (normalize p)) \<in> carrier (UP R)\<close>
proof(safe)
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  assume \<open>polynomial (carrier R) (normalize p)\<close>
  then show \<open>coeff (normalize p) \<in> carrier (UP R)\<close>
    by (meson carrier_is_subring coeff_degree poly_coeff_in_carrier UP_r.UP_car_memI)
next
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  assume \<open>coeff (normalize p) \<in> carrier (UP R)\<close>
  then show \<open>polynomial (carrier R) (normalize p)\<close>
    unfolding polynomial_def UP_r.P_def UP_def apply(safe)
    using coeff_img_restrict[of \<open>(normalize p)\<close>] imageE[of _ \<open>coeff (normalize p)\<close> ] 
      mem_upD[of \<open>coeff (normalize p)\<close>] partial_object.select_convs(1)
     apply (metis (no_types, lifting))
    by (meson ring_axioms polynomial_def ring.normalize_gives_polynomial subsetI)
qed  

lemma (in ring) p_in_RX_imp_in_P:\<open>p\<in>carrier ((carrier R)[X]) \<Longrightarrow> coeff p \<in> up R\<close>
  by (meson bound.intro coeff_in_carrier coeff_length 
      linorder_not_less mem_upI nat_le_linear polynomial_incl')


lemma (in ring) X_has_correp:\<open>coeff X = (\<lambda>i. if i = 1 then \<one> else \<zero>)\<close>
  unfolding var_def by(auto)


lemma (in ring) mult_is_mult:
  \<open>{x,y}\<subseteq>carrier ((carrier R)[X]) \<Longrightarrow> coeff (x\<otimes>\<^bsub>(carrier R)[X]\<^esub>y) = coeff x \<otimes>\<^bsub>UP R\<^esub> coeff y\<close>
proof -
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  assume a1: "{x,y}\<subseteq>carrier ((carrier R)[X])"
  then have a2: "y \<in> carrier (poly_ring R)" "x \<in> carrier (poly_ring R)" 
    by auto
  then have f3: "coeff y \<in> carrier (UP R)"
    by (metis p_in_norm normalize_equiv univ_poly_carrier)
  have "coeff x \<in> carrier (UP R)"
    using a2 by (metis p_in_norm normalize_equiv univ_poly_carrier)
  then show ?thesis 
    unfolding univ_poly_mult
    apply(subst poly_mult_coeff)
      apply (simp add: polynomial_incl' a2)+
    unfolding UP_r.P_def UP_def 
    using UP_r.p_in_RX_imp_in_P UP_r.UP_ring_axioms a2(1) 
    by (simp add: local.ring_axioms ring.p_in_RX_imp_in_P)
qed    


lemma (in ring) add_is_add:\<open>x \<in> carrier (poly_ring R) \<Longrightarrow>
           y \<in> carrier (poly_ring R)
\<Longrightarrow> coeff (x \<oplus>\<^bsub>poly_ring R\<^esub> y) = coeff x \<oplus>\<^bsub>UP R\<^esub> coeff y\<close>
proof -
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  assume a1: "x \<in> carrier (poly_ring R)"
  assume a2: "y \<in> carrier (poly_ring R)"
  then have f3: "coeff y \<in> carrier (UP R)"
    by (metis p_in_norm normalize_equiv univ_poly_carrier)
  have "coeff x \<in> carrier (UP R)"
    using a1 by (metis p_in_norm normalize_equiv univ_poly_carrier)
  then show ?thesis
    using f3 a2 a1  UP_r.cfs_add[of \<open>coeff x\<close> \<open>coeff y\<close>] coeffs_of_add_poly[of x y] by presburger
qed 

subsection \<open>The isomorphisms between the different models of polynomials\<close>
lemma (in ring) coeff_iso_RX_P:\<open>coeff \<in> ring_iso (poly_ring R) (UP R)\<close>
proof -
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  {
    fix x
    assume h1:\<open>x \<in> carrier (UP R)\<close>
    then obtain n::nat where \<open>bound \<zero> n x\<close> using UP_r.P_def unfolding UP_def by auto
    then have \<open>x\<noteq>(\<lambda>_. \<zero>) \<Longrightarrow> \<exists>n'. \<forall>m>n'. x m = \<zero> \<and>  x n' \<noteq> \<zero>\<close>
      by (metis UP_ring.coeff_simp UP_r.UP_ring_axioms UP_r.deg_gtE UP_r.deg_nzero_nzero h1 UP_r.lcoeff_nonzero not_gr_zero)
    then obtain n'::nat where f5:\<open>x\<noteq>(\<lambda>_. \<zero>) \<Longrightarrow>  \<forall>m>n'. x m = \<zero> \<and>  x n' \<noteq> \<zero>\<close> by blast
    define l::"'a list" where l_is:\<open>l \<equiv> rev (map x [0..<Suc n'])\<close>
    then have \<open>x\<noteq>(\<lambda>_. \<zero>) \<Longrightarrow> normalize l = l\<close>
      using f5 by(auto) 
    from l_is have \<open>l\<noteq>[]\<close> 
      by simp
    then have f6:\<open>k\<le>length l - 1  \<Longrightarrow> coeff l k = l!(length l - 1 - k)\<close> for k
      apply(induct l rule:coeff.induct)
      using coeff_nth diff_diff_left le_neq_implies_less plus_1_eq_Suc by auto
    have gen_ideal_X_iff:\<open>k\<le>length g - 1 \<Longrightarrow> g!k = (rev g) ! (length g -1 - k)\<close> for g::"'a list" and k::nat
      apply(induct g) 
       apply force
      by (metis One_nat_def diff_Suc_Suc length_Cons length_rev less_Suc_eq_le minus_nat.diff_0 rev_nth rev_rev_ident)
    then have \<open>length l - 1 = n'\<close> using l_is by(auto)
    then have f9:\<open>\<forall>n\<le>n'. x n = coeff l n\<close>
      using l_is f6
      by (metis add_0 diff_Suc_Suc diff_diff_cancel diff_less_Suc diff_zero l_is length_map length_upt nth_map_upt rev_nth)
    then have \<open>\<forall>n>n'. coeff l n = \<zero>\<close> 
      using coeff_degree \<open>Polynomials.degree l = n'\<close> by blast
    then have f8:\<open>\<forall>n>n'. x n = coeff l n\<close>
      using f5 by(auto)
    have f10:\<open>\<forall>n. x n = coeff l n\<close>
      using f8 f9 
      by (meson linorder_not_less)
    then have \<open>\<exists>xa\<in>carrier (poly_ring R). x = coeff xa\<close> 
      apply(cases \<open>x=(\<lambda>_. \<zero>)\<close>)
       apply(rule bexI[where x=\<open>[]\<close>])
        apply simp 
       apply (simp add: univ_poly_zero_closed)
      apply(rule bexI[where x=l])
       apply blast
      by (metis \<open>x \<noteq> (\<lambda>_. \<zero>) \<Longrightarrow> normalize l = l\<close> ext h1 mem_Collect_eq 
          normalize_equiv partial_object.select_convs(1) univ_poly_def)}note subg=this
  show ?thesis
    unfolding is_ring_iso_def ring_iso_def 
    apply(safe)
    subgoal unfolding ring_hom_def apply(safe)
         apply(simp add: local.ring_axioms UP_def ring.p_in_RX_imp_in_P univ_poly_def) 
        apply (simp add: mult_is_mult)
       apply (simp add: add_is_add)
      using UP_r.P_def unfolding univ_poly_def UP_def by(simp add:fun_eq_iff) 
    unfolding bij_betw_def inj_on_def apply(safe)
      apply (simp add: coeff_iff_polynomial_cond univ_poly_carrier)
     apply (metis normalize_polynomial mem_Collect_eq normalize_equiv partial_object.select_convs(1) 
        univ_poly_def)
    apply(simp add:image_def) 
    by(simp add:subg)
qed  

lemma (in ring) RX_iso_P:\<open>(carrier R)[X] \<simeq> (UP R)\<close>
  unfolding is_ring_iso_def 
  using coeff_iso_RX_P by force


lemma (in domain) R_isom_RX_X:\<open>R \<simeq> (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X}))\<close>
proof(unfold is_ring_iso_def, subst ex_in_conv[symmetric])
  show \<open>\<exists>x. x \<in> ring_iso R ((carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X})\<close>
  proof(rule exI[where  x=\<open>\<lambda>x. {y. y\<in>carrier((carrier R)[X]) \<and> coeff y 0 = x}\<close>], rule ring_iso_memI)
    fix x
    assume h1:\<open>x\<in>(carrier R)\<close>
    then show \<open>{y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} \<in> carrier ((carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X})\<close>
      using quot_X_is_R by auto
  next
    interpret kcr:cring "(carrier R)[X]"
      using carrier_is_subring univ_poly_is_cring by auto
    fix x y
    assume h1:\<open>x\<in>(carrier R)\<close> and h2:\<open>y\<in>(carrier R)\<close>
    interpret RcR: cring R
      by (simp add: is_cring)
    interpret QcR: cring \<open>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<close>
      by (simp add: ideal.quotient_is_cring kcr.genideal_ideal kcr.is_cring subring var_closed(1))
    have left:\<open>x\<in>(carrier R) \<and> y\<in>(carrier R) \<Longrightarrow> x = \<zero> \<Longrightarrow>
   {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = x \<otimes> y} =
    {y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} 
\<otimes>\<^bsub>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<^esub> {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = y}\<close> 
      if h3:\<open>x\<in>(carrier R) \<and> y\<in>(carrier R)\<close> for x y
      unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
      apply(simp, safe, simp)
        apply (metis Diff_iff One_nat_def coeff.simps(1) const_is_polynomial diff_self_eq_0 empty_iff 
          gen_ideal_X_iff  insert_iff kcr.l_null kcr.r_zero lead_coeff_simp length_Cons list.distinct(1) list.sel(1) 
          list.size(3)   univ_poly_carrier univ_poly_zero univ_poly_zero_closed )
      using gen_ideal_X_iff apply blast
      unfolding univ_poly_mult univ_poly_add 
      apply(frule zero_coeff_of_Idl_X)
      apply(subst (asm) Idl_X)
      using h3  
      by (metis (no_types, lifting) PIdl_X coeffs_of_add_poly gen_ideal_X_iff gen_is_cgen  ideal.I_l_closed 
          kcr.cgenideal_ideal kcr.m_comm l_zero subring univ_poly_add univ_poly_mult var_closed(1))
    have right :\<open>y = \<zero> \<Longrightarrow> {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = x \<otimes> y} =
    {y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} \<otimes>\<^bsub>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<^esub> 
    {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = y}\<close>
      apply(subst m_comm[OF h1 h2]) 
      apply(subst QcR.m_comm)
      using h1 quot_X_is_R left h1 by auto
    have poly_mult_a_b:\<open>a\<in>(carrier R) \<and> b\<in>(carrier R) \<and> a\<noteq>\<zero> \<and> b\<noteq>\<zero> \<Longrightarrow> poly_mult ([a]) ([b]) = [a\<otimes>b]\<close> for a b
      using integral_iff by force
    have poly_mult_0:\<open>a\<in>carrier((carrier R)[X]) \<and> b\<in>carrier((carrier R)[X]) \<Longrightarrow> coeff (poly_mult a b) 0 = coeff a 0 \<otimes> coeff b 0\<close>
      for a b
      apply(subst poly_mult_coeff)
      by (simp add: polynomial_incl')+
    have j0:\<open>xa \<in> carrier (poly_ring R) \<Longrightarrow> local.coeff xa 0 = x \<otimes> y \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> y \<noteq> \<zero>
 \<Longrightarrow> \<exists>xb. xb \<in> carrier (poly_ring R) \<and> local.coeff xb 0 = x \<and> (\<exists>x. x \<in> carrier (poly_ring R) \<and>
   local.coeff x 0 = y \<and> (\<exists>xc\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. xa = xc \<oplus>\<^bsub>poly_ring R\<^esub> xb \<otimes>\<^bsub>poly_ring R\<^esub> x))\<close>
      for xa
      apply(rule exI[where x=\<open>[x]\<close>])
      apply(safe) 
      subgoal by (metis Diff_iff const_is_polynomial empty_iff h1 insert_iff univ_poly_carrier)
      subgoal by simp
      apply(rule exI[where x=\<open>[y]\<close>])
      apply(safe)
      subgoal  by (metis Diff_iff const_is_polynomial empty_iff h2 insert_iff univ_poly_carrier)
      subgoal  by simp
      apply(rule bexI[where x=\<open>normalize (take (degree xa) xa @[\<zero>])\<close>])
      unfolding univ_poly_add univ_poly_mult
       apply(subst poly_mult_a_b) 
      subgoal using h1 h2 by(simp)
      subgoal by (metis (no_types, lifting) diff_le_self 
            domain.coeff_0_of_mult_X domain.m_lcancel domain.poly_mult_var domain_axioms h1 h2 
            poly_invariant take_in_RX normalize_take_is_take poly_mult_var'(2) r_null subring  univ_poly_add 
            univ_poly_mult zero_closed)
      apply(subst Idl_X) 
      by (metis (no_types, lifting) PIdl_X coeff_0_of_mult_X diff_le_self gen_ideal_X_iff gen_is_cgen 
          kcr.m_closed take_in_RX poly_mult_var'(2) subring take_in_carrier univ_poly_mult var_closed(1))
    show fst:\<open>{ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = x \<otimes> y} =
           {y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} \<otimes>\<^bsub>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<^esub>
           {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = y}\<close> 
    proof(safe)
      fix xa
      assume h1:\<open>xa \<in> carrier (poly_ring R)\<close> \<open>local.coeff xa 0 = x \<otimes> y\<close>
      then show \<open>xa \<in> {y \<in> carrier (poly_ring R). local.coeff y 0 = x} \<otimes>\<^bsub>poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}\<^esub>
                {ya \<in> carrier (poly_ring R). local.coeff ya 0 = y}\<close>
        apply(cases \<open>x=\<zero> \<or> y=\<zero>\<close>)
        using h2 left right apply blast
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
        using j0  by(auto) [1]
    next
      fix xa
      assume h1':\<open>xa \<in> {y \<in> carrier (poly_ring R). local.coeff y 0 = x} \<otimes>\<^bsub>poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}\<^esub>
                 {ya \<in> carrier (poly_ring R). local.coeff ya 0 = y}\<close>
      then show \<open>xa \<in> carrier (poly_ring R)\<close>
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def 
        by simp (metis gen_ideal_X_iff kcr.add.m_closed kcr.m_closed univ_poly_add univ_poly_mult)
      from h1' show \<open>local.coeff xa 0 = x \<otimes> y\<close>
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def 
        apply(simp, safe)
        apply(frule zero_coeff_of_Idl_X) 
        apply (simp add: polynomial_incl' domain_axioms gen_ideal_X_iff)
        using polynomial_incl' poly_mult_in_carrier 
        by (metis coeffs_of_add_poly h1 h2 kcr.m_closed l_distr l_null l_zero poly_mult_0 univ_poly_mult zero_closed)
    qed
    have poly_add_a_b:\<open>a\<in>(carrier R) \<and> b\<in>(carrier R) \<and> a\<noteq>\<zero> \<and> b\<noteq>\<zero> \<Longrightarrow> poly_add ([a]) ([b]) = normalize [a\<oplus>b]\<close> for a b
      by(auto)
    have is_inv_0:\<open>local.normalize [inv\<^bsub>add_monoid R\<^esub> y \<oplus> y] = []\<close>
      by (simp add: h2)
    have poly_add_comm: \<open>{x,y,z}\<subseteq>carrier ((carrier R)[X]) \<Longrightarrow>poly_add (poly_add y z) x = poly_add y (poly_add z x) \<close> for x y z
      by (metis insert_subset kcr.add.m_assoc univ_poly_add)
    show \<open>{ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = x \<oplus> y} =
           {y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} \<oplus>\<^bsub>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<^esub>
           {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = y}\<close>
    proof(safe)
      fix xa 
      assume h1':\<open>xa \<in> carrier (poly_ring R)\<close>\<open>local.coeff xa 0 = x \<oplus> y \<close>
      then show \<open>xa \<in> {y \<in> carrier (poly_ring R). local.coeff y 0 = x} \<oplus>\<^bsub>poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}\<^esub>
                {ya \<in> carrier (poly_ring R). local.coeff ya 0 = y}\<close>
        apply(cases \<open>x=\<zero> \<or> y=\<zero>\<close>)
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
          set_add_def set_mult_def apply(simp, safe)[1] 
          apply (metis coeff.simps(1) h2 kcr.l_zero l_zero univ_poly_zero univ_poly_zero_closed)
         apply (metis coeff.simps(1) h1 kcr.r_zero r_zero univ_poly_zero univ_poly_zero_closed)
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
          set_add_def set_mult_def apply(simp)
        apply(rule exI[where x=\<open>xa \<oplus>\<^bsub>(carrier R) [X]\<^esub> [inv\<^bsub>add_monoid R\<^esub> y]\<close>])
        apply(safe) 
          apply (metis a_inv_def add.Units_eq add.Units_inv_closed add.inv_eq_1_iff h2 insert_subset 
            kcr.add.m_closed list.sel(1) list.simps(15) polynomial_def polynomial_incl univ_poly_carrier)
         apply (metis (no_types, lifting) a_assoc add.Units_eq add.Units_inv_closed add.Units_r_inv 
            coeffs_of_add_poly diff_Suc_1 h1 h2 insert_subset polynomial_incl' lead_coeff_simp length_Cons list.distinct(1) list.sel(1) list.simps(15) list.size(3) mem_Collect_eq partial_object.select_convs(1) polynomial_def r_zero univ_poly_def)
        apply(rule exI[where x=\<open>[y]\<close>])
        apply(safe) apply(simp add:h2 univ_poly_def polynomial_def) 
         apply(simp) 
        apply(cases xa)
        unfolding univ_poly_add 
        using add.Units_eq add.inv_eq_one_eq add.Units_inv_closed add.Units_l_inv h2 r_zero apply(auto)[1]
        apply(subst poly_add_comm) 
         apply (metis Diff_iff One_nat_def append.right_neutral const_is_polynomial diff_self_eq_0 
            empty_iff empty_subsetI h2 insert_iff insert_subset inv_ld_coeff length_Cons list.distinct(1) list.sel(1) 
            list.size(3) normalize.simps(1) normalize_trick univ_poly_carrier)
        apply(subst poly_add_a_b)
         apply(simp add:h2 add.inv_eq_one_eq) 
        apply(subst is_inv_0)
        by (metis polynomial_incl' p_in_norm poly_add_zero'(1))
    next
      fix xa
      assume h1':\<open>xa \<in> {y \<in> carrier (poly_ring R). local.coeff y 0 = x} \<oplus>\<^bsub>poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}\<^esub>
               {ya \<in> carrier (poly_ring R). local.coeff ya 0 = y} \<close>
      then show \<open>xa \<in> carrier (poly_ring R)\<close> 
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
          set_add_def set_mult_def by(auto) 
      from h1' show \<open>local.coeff xa 0 = x \<oplus> y\<close>
        unfolding FactRing_def A_RCOSETS_def RCOSETS_def rcoset_mult_def r_coset_def a_r_coset_def
          set_add_def set_mult_def using polynomial_incl' poly_add_coeff coeffs_of_add_poly by auto
    qed
  next
    interpret kcr:cring "(carrier R)[X]"
      using carrier_is_subring univ_poly_is_cring by auto
    show \<open>{y \<in> carrier ((carrier R) [X]). local.coeff y 0 = \<one>} = \<one>\<^bsub>(carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}\<^esub>\<close>
      unfolding FactRing_def  a_r_coset_def r_coset_def
      using gen_ideal_X_iff apply(simp, safe, simp)
        apply (metis (no_types, lifting)  diff_le_self domain.coeff_0_of_mult_X 
          domain.poly_mult_var domain_axioms gen_ideal_X_iff kcr.m_closed  poly_invariant normalize_take_is_poly monoid.simps(2)  subring univ_poly_def 
          var_closed(1) zero_not_one)
       apply force
      by (metis One_nat_def coeff.simps(1) coeffs_of_add_poly diff_self_eq_0 kcr.l_zero kcr.one_closed 
          lead_coeff_simp length_Cons list.distinct(1) list.sel(1) list.size(3) univ_poly_one univ_poly_zero 
          univ_poly_zero_closed)
  next
    interpret kcr:cring "(carrier R)[X]"
      using carrier_is_subring univ_poly_is_cring by auto
    have rule_1:\<open>{y \<in> carrier (poly_ring R). local.coeff y 0 = xa} \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}) =
(\<exists>x\<in>carrier (poly_ring R). {y \<in> carrier (poly_ring R). local.coeff y 0 = xa} = (\<Union>xa\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {xa \<oplus>\<^bsub>poly_ring R\<^esub> x}))\<close> for xa
      unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def by(auto) 
    have rule_2:\<open>(\<And>x. x \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}) \<Longrightarrow>
         x \<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R)
 \<Longrightarrow>  (\<And>xa. xa \<in> carrier (poly_ring R) \<Longrightarrow>
          (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa}) \<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R)\<close> 
      unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def 
      using UN_singleton by auto 
    have rule_2':\<open> (\<And>xa. xa \<in> carrier (poly_ring R) \<Longrightarrow>
          (\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa}) \<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R)
\<Longrightarrow> (\<And>x. x \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}) \<Longrightarrow>
         x \<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R)\<close> 
      unfolding FactRing_def A_RCOSETS_def RCOSETS_def r_coset_def 
      using UN_singleton by auto 
    show \<open>bij_betw (\<lambda>x. {y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x}) (carrier R) (carrier ((carrier R) [X] Quot Idl\<^bsub>(carrier R) [X]\<^esub> {X}))\<close>
      unfolding bij_betw_def
      apply(safe)
        apply(rule inj_onI)
      subgoal proof -
        fix x :: 'a and y :: 'a
        assume a1: "x \<in> (carrier R)"
        assume a2: "y \<in> (carrier R)"
        assume "{y \<in> carrier ((carrier R) [X]). local.coeff y 0 = x} = {ya \<in> carrier ((carrier R) [X]). local.coeff ya 0 = y}"
        then have "y = (THE a. \<forall>as. as \<in> {as \<in> carrier ((carrier R) [X]). local.coeff as 0 = x} \<longrightarrow> local.coeff as 0 = a)"
          using a2 The_a_is_a by force
        then show "x = y"
          using a1 The_a_is_a by auto
      qed
    proof(subst rule_1)
      fix x xa
      have rule_1:\<open>x' \<in> (\<Union>xa\<in>{p \<in> carrier (poly_ring R). local.coeff p 0 = \<zero>}. {xa \<oplus>\<^bsub>poly_ring R\<^esub> [local.coeff x' 0]}) =
 (\<exists>xa. xa \<in> carrier (poly_ring R) \<and> local.coeff xa 0 = \<zero> \<and> x' = xa \<oplus>\<^bsub>poly_ring R\<^esub> [local.coeff x' 0])\<close> for x'
        by simp
      assume h1':\<open>xa \<in> carrier R\<close>
      then show \<open>\<exists>x\<in>carrier (poly_ring R).
          {y \<in> carrier (poly_ring R). local.coeff y 0 = xa} = (\<Union>xa\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {xa \<oplus>\<^bsub>poly_ring R\<^esub> x})\<close>
        apply(cases \<open>xa=\<zero>\<close>)
         apply(rule bexI[where x=\<open>[]\<close>]) 
        using gen_ideal_X_iff kcr.r_zero univ_poly_zero apply(safe)[1]
            apply (simp add: univ_poly_zero)+
         apply (simp add: univ_poly_zero_closed)
        apply(rule bexI[where x=\<open>[xa]\<close>])
         apply(subst gen_ideal_X_iff') 
         apply(safe)
           apply(subst rule_1)
           apply (metis coeff.simps(1) coeff_0_of_mult_X diff_le_self kcr.m_closed 
            normalize_take_is_poly poly_invariant subring var_closed(1))
          apply (metis bot_least insert_subset list.simps(15) poly_add_is_polynomial polynomial_incl' 
            set_empty2 subring univ_poly_add univ_poly_carrier)
         apply (metis diff_Suc_1 insert_subset kcr.zero_closed l_zero lead_coeff_simp length_Cons 
            list.distinct(1) list.sel(1) list.simps(15) list.size(3) poly_add_coeff polynomial_incl' univ_poly_add univ_poly_zero)
        by (metis Diff_iff const_is_polynomial emptyE insertE univ_poly_carrier)
    next
      show \<open>\<And>x. x \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X}) 
\<Longrightarrow> x \<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R\<close>
      proof(rule rule_2')
        fix x xa
        assume h1:\<open>x \<in> carrier (poly_ring R Quot Idl\<^bsub>poly_ring R\<^esub> {X})\<close> \<open>xa \<in> carrier (poly_ring R)\<close>
        then show \<open>(\<Union>x\<in>Idl\<^bsub>poly_ring R\<^esub> {X}. {x \<oplus>\<^bsub>poly_ring R\<^esub> xa}) 
\<in> (\<lambda>x. {y \<in> carrier (poly_ring R). local.coeff y 0 = x}) ` carrier R\<close>
          apply(simp only:image_def, safe)
          apply(rule bexI[where x=\<open>coeff xa 0\<close>])
           apply(safe)
          by(auto simp:gen_ideal_X_iff coeffs_of_add_poly domain_axioms polynomial_incl')
            (metis coeff.simps(1) coeffs_of_add_poly gen_ideal_X_iff insertI1 kcr.add.inv_closed 
              kcr.add.inv_solve_right kcr.add.m_comm kcr.l_neg kcr.minus_closed kcr.minus_eq univ_poly_zero)+
      qed
    qed
  qed
qed

lemma (in domain) RX_imp_RX_over_X:
  \<open>noetherian_ring (carrier R[X]) \<Longrightarrow> noetherian_ring (carrier R[X] Quot  genideal (carrier R[X]) {X})\<close>
  by (meson domain.var_closed(1) domain_axioms empty_subsetI insert_subset noetherian_ring_def 
      noetherian_ring_imp_quot_noetherian_ring ring.genideal_ideal subring)


lemma (in domain) noetherian_RX_imp_noetherian_R:
  \<open>noetherian_ring ((carrier R)[X]) \<Longrightarrow> noetherian_ring R\<close>
proof -
  assume h1:\<open>noetherian_ring ((carrier R)[X])\<close>
  have \<open>noetherian_ring (((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X}))\<close>
    using RX_imp_RX_over_X h1 by auto
  moreover have \<open>(((carrier R)[X]) Quot  (genideal ((carrier R)[X]) {X})) \<simeq> R\<close>
    using R_isom_RX_X local.ring_axioms ring_iso_sym by blast
  ultimately show ?thesis 
    using local.ring_axioms noetherian_isom_imp_noetherian by blast
qed


lemma  principal_imp_noetherian:\<open>principal_domain R \<Longrightarrow> noetherian_ring R\<close>
proof -
  assume h1:\<open>principal_domain R\<close>
  then show ?thesis
    apply(intro ring.noetherian_ringI)
    using cring.axioms(1) domain_def principal_domain.axioms(1) apply blast
    by (metis cring.cgenideal_eq_genideal domain_def empty_subsetI finite.emptyI finite.insertI
        insert_subset principal_domain.axioms(1) principal_domain.exists_gen)
qed

lemma (in ring) coeff_iff_poly_carrier:\<open>x \<in> carrier (poly_ring R) \<Longrightarrow>
       y \<in> carrier (poly_ring R) \<Longrightarrow> (x=y) \<longleftrightarrow> coeff x = coeff y\<close>
  by (auto simp add: coeff_iff_polynomial_cond univ_poly_carrier)





lemma zero_is_zero:\<open>B = B\<lparr>zero :=  \<zero>\<^bsub>B\<^esub>\<rparr>\<close>
  unfolding ring_def monoid_def ring_axioms_def abelian_group_def abelian_group_axioms_def
    abelian_monoid_def comm_monoid_def by(auto)

lemma ring_iso_imp_iso:\<open>A\<simeq>B \<Longrightarrow> A\<cong>B\<close>
  unfolding is_ring_iso_def is_iso_def ring_iso_def iso_def 
    ring_hom_def hom_def by(auto)


lemma (in ring) iso_imp_exist_0:\<open>R\<simeq>B  \<Longrightarrow> \<exists>x. ring (B\<lparr>zero:=x\<rparr>)\<close>
proof -
  assume h1:\<open>R\<simeq>B\<close>
  have \<open>ring R\<close> 
    by (simp add: local.ring_axioms)
  with h1 obtain h where f0:\<open>h \<in> ring_hom R B \<and> bij_betw h (carrier R) (carrier B)\<close>
    unfolding is_ring_iso_def ring_iso_def by auto
  then have f1:"ring (B \<lparr> carrier := h ` (carrier R), zero := h \<zero>\<^bsub>R\<^esub> \<rparr>)"
    using ring_hom_imp_img_ring[of ] h1 unfolding ring_iso_def  
    using ring.ring_hom_imp_img_ring by blast
  moreover have f2:"h ` (carrier R) = carrier B"
    using h1 unfolding ring_iso_def bij_betw_def 
    by (simp add: f0 bij_betw_imp_surj_on)
  then show ?thesis using f1 f2 by(auto) 
qed

lemma (in domain) noetherian_R_imp_noetherian_UP_R:
  assumes h1:\<open>noetherian_ring R\<close> 
  shows \<open>noetherian_ring (UP R)\<close>
proof -
  interpret UPring: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  have \<open>noetherian_ring ((carrier R)[X])\<close>
    using noetherian_domain.weak_Hilbert_basis h1
    using domain_axioms noetherian_domain.intro by auto
  with h1 show ?thesis
    unfolding noetherian_domain_def 
    using  \<open>noetherian_ring (poly_ring R)\<close> noetherian_isom_imp_noetherian h1  UPring.UP_ring RX_iso_P 
    by blast
qed

lemma (in domain) noetheriandom_R_imp_noetheriandom_UP_R:
  assumes h1:\<open>noetherian_domain R\<close> 
  shows \<open>noetherian_domain (UP R)\<close>
proof -
  interpret UP_dom: UP_domain R "UP R"
    by (simp add: UP_domain.intro domain_axioms)+
  have \<open>noetherian_ring ((carrier R)[X])\<close>
    using noetherian_domain.weak_Hilbert_basis h1
    by(auto)
  with h1 show ?thesis 
    unfolding noetherian_domain_def 
    using UP_dom.domain_axioms noetherian_R_imp_noetherian_UP_R by blast
qed


lemma (in cring) Pring_one_index_isom_P:\<open>(Pring R {N}) \<simeq> UP R\<close>
proof -
  interpret UPcring: UP_cring R "UP R"
    by (simp add: UP_cring_def is_cring)+
  have \<open>IP_to_UP N \<in> ring_hom (Pring R {N}) (UP R)\<close>
    by (simp add: UPcring.IP_to_UP_ring_hom ring_hom_ring.homh)  
  then show ?thesis unfolding is_ring_iso_def ring_iso_def 
    apply(subst ex_in_conv[symmetric])
    apply(rule exI[where x=\<open>IP_to_UP N\<close>])
    unfolding bij_betw_def apply(safe)
      apply (simp add: UPcring.IP_to_UP_ring_hom_inj)
     apply (simp add: IP_to_UP_closed is_cring)
    by (metis UPcring.IP_to_UP_inv UPcring.UP_to_IP_closed image_eqI)
qed

lemma (in cring) P_isom_Pring_one_index: \<open>UP R \<simeq> (Pring R {N})\<close>
proof -
  interpret UPcring: UP_cring R "UP R"
    by (simp add: UP_cring_def is_cring)+
  interpret crR:cring "Pring R {N}"
    by (simp add: Pring_is_cring is_cring)
  show ?thesis 
    using cring.Pring_one_index_isom_P crR.ring_axioms ring_iso_sym is_cring by fastforce
qed

lemma (in domain) P_iso_RX:\<open> UP R \<simeq> ((carrier R)[X])\<close>
proof -
  interpret d: domain "(carrier R)[X]"
    by (simp add: subring univ_poly_is_domain)
  have \<open>(carrier R)[X] \<simeq> UP R\<close> 
    using RX_iso_P UP_ring_def local.ring_axioms by blast
  then show ?thesis 
    using d.ring_axioms ring_iso_sym by blast
qed


lemma (in domain) IP_noeth_imp_R_noeth:\<open>noetherian_ring (Pring R {a}) \<Longrightarrow> noetherian_ring R\<close>
proof -
  assume h1:\<open>noetherian_ring (Pring R {a})\<close>
  have \<open>(Pring R {a}) \<simeq> ((carrier R)[X])\<close> 
    by (meson Pring_one_index_isom_P domain.P_iso_RX domain_axioms ring_iso_trans) 
  then have \<open>noetherian_ring  ((carrier R)[X])\<close> 
    using domain.univ_poly_is_ring domain_axioms h1 noetherian_isom_imp_noetherian subring by blast
  then show ?thesis 
    using noetherian_RX_imp_noetherian_R by fastforce
qed

lemma (in domain) R_iso_UPR_quot_X:\<open>R \<simeq> (UP R) Quot (cgenideal (UP R) (\<lambda>i. if i=1 then \<one> else \<zero>))\<close>
proof -
  interpret UP_r: UP_ring R "UP R"
    by (simp add: UP_ring_def local.ring_axioms)+
  have f0:\<open>coeff \<in> ring_iso (poly_ring R) (UP R)\<close>
    using coeff_iso_RX_P by blast
  have \<open>X \<in> carrier (poly_ring R)\<close> \<open>(\<lambda>i. if i = 1 then \<one> else \<zero>) \<in> carrier (UP R)\<close>
    \<open>cring (poly_ring R)\<close> \<open>cring (UP R)\<close>
       apply (simp add: subring var_closed(1))
      apply(force simp:UP_def up_def)
     apply (simp add: subring univ_poly_is_cring)
    by (simp add: UP_cring.UP_cring UP_cring.intro is_cring)
  then have \<open>(carrier R[X]) Quot (cgenideal (poly_ring R) X) \<simeq>(UP R) Quot (cgenideal (UP R) (\<lambda>i. if i=1 then \<one> else \<zero>))\<close>
    using Quot_iso_cgen[of X \<open>poly_ring R\<close> \<open>(\<lambda>i. if i=1 then \<one> else \<zero>)\<close> \<open>(UP R)\<close> coeff] X_has_correp
      f0 by fastforce
  then show ?thesis
    using domain.R_isom_RX_X domain_axioms gen_is_cgen ring_iso_trans by force
qed

end

