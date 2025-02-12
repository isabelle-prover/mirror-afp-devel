section \<open>Polynomials Ring Miscellaneous\<close>

theory Polynomials_Ring_Misc

imports "HOL-Algebra.Polynomials"

begin

text \<open>Some lemmas that may be considered as useful, and that helps for the Hilbert's basis proof\<close>

definition(in ring) deg_poly_set:\<open>deg_poly_set S k =  {a. a\<in>S \<and> degree a = k}\<union>{[]}\<close>

definition (in ring)  lead_coeff_set::\<open>'a list set\<Rightarrow> nat \<Rightarrow> 'a set\<close>
  where \<open>lead_coeff_set S k \<equiv> {coeff a (degree a) | a. a\<in>deg_poly_set S k}\<close>



lemma rule_union:\<open>x\<in>(\<Union>n\<le>k. A l n) \<longleftrightarrow> (\<exists>n\<le>k. x\<in>A l n)\<close>
  by(auto)

lemma (in ring) add_0_eq_0_is_0:\<open>a\<in>carrier ((carrier R)[X]) \<Longrightarrow> [] \<oplus>\<^bsub>(carrier R) [X]\<^esub> a = [] \<Longrightarrow> a = []\<close>
proof -
  assume h1:\<open>a\<in>carrier ((carrier R)[X])\<close> and h2:\<open>[] \<oplus>\<^bsub>(carrier R) [X]\<^esub> a = []\<close>
  have \<open>poly_add [] a = a\<close>
    apply(rule local.poly_add_zero(2)[of \<open>(carrier R)\<close>])
     apply (simp add: carrier_is_subring)
    by (simp add: h1 univ_poly_carrier)
  then show ?thesis 
    using h2 unfolding univ_poly_add by presburger
qed


lemma (in domain) inv_coeff_sum:\<open>a\<in>carrier((carrier R)[X]) \<Longrightarrow> aa\<in>carrier((carrier R)[X]) 
\<Longrightarrow> a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa = [] \<longleftrightarrow> (\<forall>n. coeff a n = inv\<^bsub>add_monoid R\<^esub> (coeff aa n))\<close>
proof(safe, induct a)
  case Nil
  then have \<open>aa = []\<close> 
    by (simp add: Nil.prems(2) Nil.prems(3) add_0_eq_0_is_0)
  then show ?case by(auto)
next
  case (Cons a1 a2)
  then show ?case 
    by (metis add.comm_inv_char coeff.simps(1) coeff_in_carrier local.add.m_comm local.ring_axioms 
        poly_add_coeff polynomial_in_carrier ring.carrier_is_subring univ_poly_add univ_poly_carrier)
next 
  interpret kxr: cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by blast
  assume h1:\<open>a \<in> carrier ((carrier R) [X])\<close> and h2:\<open>aa \<in> carrier ((carrier R) [X])\<close>
    and h3:\<open>\<forall>n. local.coeff a n = inv\<^bsub>add_monoid R\<^esub> local.coeff aa n\<close>
  then show \<open>a \<oplus>\<^bsub>(carrier R) [X]\<^esub> aa = []\<close> 
    by (metis (no_types, lifting) abelian_group_def abelian_monoid.a_monoid add.Units_eq
        carrier_is_subring coeff_in_carrier kxr.add.m_closed kxr.add.m_comm lead_coeff_simp local.ring_axioms 
        mem_Collect_eq monoid.Units_r_inv monoid.select_convs(1) monoid.select_convs(2) partial_object.select_convs(1) 
        poly_add_coeff polynomial_def polynomial_in_carrier ring_def univ_poly_add univ_poly_def)
qed


lemma (in ring) coeffs_of_add_poly:\<open>a\<in>carrier((carrier R)[X]) \<Longrightarrow> aa\<in>carrier((carrier R)[X]) 
    \<Longrightarrow> coeff (a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa) n = coeff a n \<oplus> coeff aa n\<close>
  by (metis local.ring_axioms poly_add_coeff ring.polynomial_incl univ_poly_add univ_poly_carrier)

lemma (in ring) length_add:\<open>a\<in>carrier((carrier R)[X]) \<Longrightarrow> aa\<in>carrier((carrier R)[X]) 
\<Longrightarrow> coeff a (degree a) \<noteq> inv\<^bsub>add_monoid R\<^esub> coeff aa (degree aa)
 \<Longrightarrow> degree (a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa) = max (degree a) (degree aa)\<close>
proof -
  assume h1:\<open>a\<in>carrier((carrier R)[X])\<close> 
    and h2:\<open>aa\<in>carrier((carrier R)[X])\<close> 
    and h3:\<open>coeff a (degree a) \<noteq> inv\<^bsub>add_monoid R\<^esub> coeff aa (degree aa)\<close>
  have f0:\<open>\<forall>n>(max (degree a) (degree aa)). coeff (a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa) n = \<zero>\<close>
    by (simp add: coeff_degree coeffs_of_add_poly h1 h2)
  then have f1:\<open>degree a = degree aa \<Longrightarrow> coeff (a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa) (degree a)
                 = coeff a (degree a) \<oplus> coeff aa (degree aa)\<close>
    using coeffs_of_add_poly h1 h2 by presburger
  also have f2: \<open>coeff a (degree a) \<oplus> coeff aa (degree aa) \<noteq> \<zero>\<close> using h3 
    by (meson add.inv_comm add.inv_unique' coeff_in_carrier h1 h2 local.ring_axioms 
        ring.polynomial_incl univ_poly_carrier)
  then show ?thesis 
    apply(cases "degree a = degree aa")
    using f0 f1 
     apply (metis coeff_degree le_neq_implies_less max.idem poly_add_degree univ_poly_add)
    apply(cases \<open>degree a > degree aa\<close>)
    by (metis carrier_is_subring h1 h2 local.ring_axioms 
        ring.poly_add_degree_eq univ_poly_add univ_poly_carrier)+
qed


lemma (in domain) inv_imp_zero:\<open>a\<in>carrier((carrier R)[X]) \<Longrightarrow> a \<oplus>\<^bsub>(carrier R) [X]\<^esub> inv\<^bsub>add_monoid ((carrier R) [X])\<^esub> a = []\<close>
  using local.add.Units_eq local.add.Units_r_inv univ_poly_zero 
  by (metis a_inv_def abelian_group.r_neg carrier_is_subring domain.univ_poly_is_abelian_group domain_axioms)

lemma (in domain) R_subdom:\<open>subdomain (carrier R) R\<close>
  by (simp add: carrier_is_subring subdomainI')

lemma (in domain) lead_coeff_in_carrier:
  \<open>ideal I ((carrier R)[X]) \<Longrightarrow> a\<in> I \<Longrightarrow> coeff a (degree a) \<in> (carrier R)\<close> for I a
  using poly_coeff_in_carrier[of \<open>carrier R\<close> a] 
  by (simp add: carrier_is_subring ideal.Icarr univ_poly_carrier)

lemma (in domain) degree_of_inv:\<open>p\<in>carrier((carrier R)[X]) \<Longrightarrow> degree (inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> p) = degree p\<close> for p
  using univ_poly_a_inv_degree[of \<open>carrier R\<close> p] 
  by (simp add: a_inv_def carrier_is_subring)

lemma (in domain) inv_in_deg_poly_set:\<open>ideal I ((carrier R)[X]) \<Longrightarrow> a\<in> deg_poly_set I k 
\<Longrightarrow> inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> a \<in> deg_poly_set I k\<close> for I k a
proof -
  interpret kxr: cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by blast
  assume h1:\<open>ideal I ((carrier R)[X])\<close> \<open>a\<in> deg_poly_set I k\<close>
  then show ?thesis
    unfolding deg_poly_set
    apply(safe) 
       apply (meson additive_subgroup_def group.subgroupE(3) ideal_def kxr.add.is_group)
      apply (meson degree_of_inv ideal.Icarr)
    by (metis kxr.add.inv_one univ_poly_zero)+
qed

lemma (in domain) ideal_lead_coeff_set:\<open>ideal (lead_coeff_set I k) R\<close> 
  if  h':\<open>ideal I ((carrier R)[X])\<close> for I k 
proof(rule idealI)
  show \<open>ring R\<close> 
    by (simp add: local.ring_axioms)
next
  interpret kxr: cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by blast
  show \<open>subgroup (lead_coeff_set I k) (add_monoid R)\<close>
    unfolding subgroup_def lead_coeff_set_def 
  proof(safe)
    fix a x
    assume h1:\<open>a \<in> deg_poly_set I k\<close>
    show \<open>local.coeff a (degree a) \<in> carrier (add_monoid R)\<close>
      using lead_coeff_in_carrier h' h1  
      by (metis (no_types, lifting) Un_iff deg_poly_set empty_iff insert_iff 
          kxr.oneideal mem_Collect_eq partial_object.select_convs(1) univ_poly_zero_closed)
  next 
    fix x y a aa
    assume h1:\<open>a \<in> deg_poly_set I k\<close> and h2:\<open>aa \<in> deg_poly_set I k\<close> 
    then have imp:\<open>a\<in>carrier ((carrier R)[X]) \<and> aa \<in> carrier ((carrier R)[X])\<close>
      unfolding deg_poly_set using h' unfolding ideal_def 
      by(auto simp:additive_subgroup.a_Hcarr)
    then show \<open>\<exists>ab. local.coeff a (degree a) \<otimes>\<^bsub>add_monoid R\<^esub> local.coeff aa (degree aa) 
  = local.coeff ab (degree ab) \<and> ab \<in> deg_poly_set I k\<close>
      apply(cases \<open>a=[]\<close>)
      using lead_coeff_in_carrier h2 kxr.oneideal apply auto[1]
      apply(cases \<open>aa=[]\<close>)
      using lead_coeff_in_carrier h1 kxr.oneideal apply auto[1]
      apply(cases \<open>local.coeff aa (length aa - Suc 0) 
  \<noteq> inv\<^bsub>add_monoid R\<^esub> local.coeff a (length a - Suc 0)\<close>)
       apply(rule exI[where x=\<open>a \<oplus>\<^bsub>(carrier R)[X]\<^esub> aa\<close>])
      using imp length_add h1 h2 unfolding deg_poly_set apply(safe) 
         apply (metis One_nat_def coeffs_of_add_poly kxr.add.m_comm max.idem monoid.select_convs(1))
        apply (meson additive_subgroup.a_closed ideal_def that)
       apply (metis One_nat_def kxr.add.m_comm max.idem)
      by (metis (no_types, lifting) One_nat_def Un_iff add.comm_inv_char add.r_inv_ex coeff.simps(1) 
          lead_coeff_in_carrier insert_iff monoid.select_convs(1) that)
  next
    show \<open>\<exists>a. \<one>\<^bsub>add_monoid R\<^esub> = local.coeff a (degree a) \<and> a \<in> deg_poly_set I k\<close>
      by (smt (verit, ccfv_threshold) Un_insert_right coeff.simps(1) deg_poly_set insertI1 monoid.select_convs(2))
  next
    fix a
    assume \<open>a \<in> deg_poly_set I k\<close>
    obtain a' where \<open>a'= inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> a \<and> a \<in> I\<close>
      using h' 
      by (metis (no_types, lifting) Un_iff \<open>a \<in> deg_poly_set I k\<close> deg_poly_set empty_iff insert_iff kxr.add.normal_invE(1)
          kxr.ideal_is_normal mem_Collect_eq monoid.select_convs(2) subgroup_def univ_poly_zero)
    then show \<open>\<exists>aa. inv\<^bsub>add_monoid R\<^esub> local.coeff a (degree a) = local.coeff aa (degree aa) \<and> aa \<in> deg_poly_set I k\<close>
      apply(intro exI[where x=\<open>inv\<^bsub>add_monoid ((carrier R)[X])\<^esub> a\<close>]) 
      apply(safe) 
       apply (metis (no_types, opaque_lifting) degree_of_inv ideal.Icarr kxr.add.Units_eq kxr.add.Units_inv_closed 
          kxr.add.Units_l_inv inv_coeff_sum that univ_poly_zero)
      using \<open>a \<in> deg_poly_set I k\<close> inv_in_deg_poly_set that by blast
  qed
next
  interpret kxr: cring "(carrier R)[X]"
    using carrier_is_subring univ_poly_is_cring by blast
  fix a y
  assume h1:\<open> a \<in> lead_coeff_set I k\<close> and h2:\<open>y \<in> (carrier R)\<close>
  then obtain l where h3:\<open>l\<in>deg_poly_set I k \<and> a = coeff l (degree l)\<close>
    using lead_coeff_set_def by auto
  then have t0:\<open>set l \<subseteq> (carrier R)\<close> 
    by (metis (no_types, lifting) Un_iff additive_subgroup.a_Hcarr deg_poly_set h' ideal.axioms(1) 
        kxr.zeroideal mem_Collect_eq partial_object.select_convs(1) polynomial_incl univ_poly_def 
        univ_poly_zero)
  have t1:\<open>l\<in>carrier ((carrier R)[X])\<close> using h3 h' unfolding deg_poly_set ideal_def 
    by(auto simp:additive_subgroup.a_Hcarr)
  have h4:\<open>y\<noteq>\<zero> \<Longrightarrow> [y] \<in> carrier((carrier R)[X])\<close>  
    using h2 by (simp add: polynomial_def univ_poly_def)
  have f4a:\<open>subring (carrier R) R\<close> 
    using carrier_is_subring by auto
  have h5:\<open>y\<noteq>\<zero> \<Longrightarrow> [y] \<in> carrier ((carrier R) [X]) \<Longrightarrow> l \<in> carrier ((carrier R)[X]) 
  \<Longrightarrow> l\<noteq>[] \<Longrightarrow> [y] \<otimes>\<^bsub>(carrier R) [X]\<^esub> l \<in> deg_poly_set I k\<close>
    using h3 h4 unfolding deg_poly_set apply(safe)
     apply (meson h' ideal_axioms_def ideal_def) 
    unfolding univ_poly_mult
    using poly_mult_degree_eq[of "(carrier R)" \<open>[y]\<close> l] 
    using f4a univ_poly_carrier by auto 
  have t4:\<open>y\<noteq>\<zero> \<Longrightarrow> [y] \<in> carrier ((carrier R) [X]) \<Longrightarrow> l \<in> carrier ((carrier R)[X]) \<Longrightarrow> l\<noteq>[] \<Longrightarrow>y \<otimes> a = local.coeff ([y] \<otimes>\<^bsub>(carrier R) [X]\<^esub> l) (degree ([y] \<otimes>\<^bsub>(carrier R) [X]\<^esub> l))\<close>
    unfolding univ_poly_mult 
    by (metis f4a h3 lead_coeff_simp list.sel(1) not_Cons_self poly_mult_integral 
        poly_mult_lead_coeff univ_poly_carrier)
  have t6:\<open>a\<noteq>\<zero> \<Longrightarrow> l\<noteq>[]\<close> 
    using h3 by fastforce
  show symet:\<open>y \<otimes> a \<in> lead_coeff_set I k\<close> 
    unfolding lead_coeff_set_def deg_poly_set apply(safe)
    apply(cases \<open>a = \<zero>\<close>)
     apply(rule exI[where x=\<open>[]\<close>])
     apply (simp add: h2)
    apply(cases \<open>y=\<zero>\<close>)     
     apply(rule exI[where x=\<open>[]\<close>])
    using coeff.simps(1) coeff_in_carrier h2 h3 integral_iff t0 apply simp
    apply(rule exI[where x=\<open> [y] \<otimes>\<^bsub>(carrier R) [X]\<^esub> l\<close>])
    apply(safe)
      apply (metis One_nat_def coeff.simps(1) h3 h4 t1 t4)
    using h5 h4 t6 by(auto simp add: deg_poly_set t1)  
  show \<open>a \<otimes> y \<in> lead_coeff_set I k\<close> 
    using h2 h3 m_comm symet t0 by auto
qed

lemma (in ring) deg_poly_set_0:\<open>deg_poly_set x' 0 = {[a] | a. [a]\<in>x'}\<union>{[]}\<close> for x'::\<open>'c list set\<close>
  unfolding deg_poly_set 
  apply(safe)
   apply (metis One_nat_def Suc_pred length_0_conv length_Suc_conv length_greater_0_conv)
  by(auto)

lemma (in ring) lead_coeff_set_0:\<open>lead_coeff_set x' 0 = {a. [a]\<in>x'}\<union>{\<zero>}\<close> for x'
  unfolding lead_coeff_set_def 
proof(subst deg_poly_set_0, safe)
  fix x a aa
  assume h1:\<open>local.coeff [aa] (degree [aa]) \<notin> {}\<close> \<open>local.coeff [aa] (degree [aa]) \<noteq> \<zero>\<close>
    \<open>[aa] \<in> x'\<close>
  then show \<open>[local.coeff [aa] (degree [aa])] \<in> x'\<close>
    by(simp) 
next
  fix x a
  assume h1:\<open>local.coeff [] (degree []) \<notin> {}\<close> \<open>local.coeff [] (degree []) \<noteq> \<zero>\<close>
  then show \<open>[local.coeff [] (degree [])] \<in> x'\<close> by simp
next
  fix x
  assume h1:\<open>[x] \<in> x'\<close>
  then show \<open>\<exists>a. x = local.coeff a (degree a) \<and> a \<in> {[a] |a. [a] \<in> x'} \<union> {[]}\<close>
    apply(intro exI[where x=\<open>[x]\<close>]) 
    by(simp)
next
  fix x
  show \<open>\<exists>a. \<zero> = local.coeff a (degree a) \<and> a \<in> {[a] |a. [a] \<in> x'} \<union> {[]} \<close>
    apply(rule exI[where x=\<open>[]\<close>]) 
    by(simp)
qed

end