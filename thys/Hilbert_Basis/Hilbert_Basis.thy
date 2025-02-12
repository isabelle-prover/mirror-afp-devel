section \<open>The Hilbert Basis theorem for Indexed Polynomials Rings\<close>
theory Hilbert_Basis

imports "Weak_Hilbert_Basis" 

begin 

subsection \<open>The isomorphism between \<open>A[X\<^sub>0..X\<^sub>n] and A[X\<^sub>0..X\<^sub>n\<^sub>-\<^sub>1][X\<^sub>n]\<close>\<close>

text \<open>This part until $var_factor_iso$ is due to Aaron Crighton\<close>
lemma ring_iso_memI': 
  assumes "f \<in> ring_hom R S"
  assumes "g \<in> ring_hom S R"
  assumes "\<And> x. x \<in> carrier R \<Longrightarrow> g (f x) = x"
  assumes "\<And> x. x \<in> carrier S \<Longrightarrow> f (g x) = x"
  shows "f \<in> ring_iso R S"
    "g \<in> ring_iso S R"
proof- 
  show 0: "f \<in> ring_iso R S"
    unfolding ring_iso_def mem_Collect_eq
    apply(rule conjI, rule assms(1), rule bij_betwI[of _ _ _ g])
    using assms ring_hom_memE by auto 
  show "g \<in> ring_iso S R"
    unfolding ring_iso_def mem_Collect_eq
    apply(rule conjI, rule assms(2), rule bij_betwI[of _ _ _ f])
    using assms ring_hom_memE by auto 
qed


lemma(in cring) var_factor_inverse:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi>1 = (var_factor_inv I J0 J1)"
  assumes "\<psi>0 = (var_factor I J0 J1)"
  assumes "P \<in> carrier (Pring (Pring R J0) J1)"
  shows "\<psi>0 (\<psi>1 P) = P"
proof(induct rule: ring.Pring_car_induct''[of "Pring R J0" _ J1])
  case 1
  then show ?case 
    using Pring_is_ring by blast 
next
  case 2
  then show ?case 
    using assms(6) by force
next
  case (3 c)
  interpret pring_cring: cring "Pring R J0"
    using Pring_is_cring is_cring by auto 
  interpret Rcring: cring R
    using is_cring by auto 
  have 0: "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I) \<psi>1"
    by (simp add: assms(1) assms(3) assms(4) var_factor_inv_morphism(1)) 
  have 1: "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi>0"
    by (simp add: assms(1) assms(3) assms(5) var_factor_morphism'(1))
  have 2: "\<psi>0 \<circ> \<psi>1 \<in> ring_hom (Pring (Pring R J0) J1) (Pring (Pring R J0) J1) "
    using 0 1 ring_hom_trans[of \<psi>1 "Pring (Pring R J0) J1" "Pring R I" \<psi>0 "Pring (Pring R J0) J1"]
      ring_hom_ring.homh[of "Pring R I" "Pring (Pring R J0) J1" \<psi>0]
      ring_hom_ring.homh[of "Pring (Pring R J0) J1" "Pring R I" \<psi>1]
    by blast
  then show ?case using assms 
    by (simp add: 3 var_factor_inv_morphism(3) var_factor_morphism'(3))
next
  case (4 p q)
  interpret pring_cring: cring "Pring R J0"
    using Pring_is_cring is_cring by auto 
  interpret Rcring: cring R
    using is_cring by auto 
  have 0: "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I) \<psi>1"
    by (simp add: assms(1) assms(3) assms(4) var_factor_inv_morphism(1)) 
  have 1: "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi>0"
    by (simp add: assms(1) assms(3) assms(5) var_factor_morphism'(1))
  have 2: "\<psi>0 \<circ> \<psi>1 \<in> ring_hom (Pring (Pring R J0) J1) (Pring (Pring R J0) J1) "
    using 0 1 ring_hom_trans[of \<psi>1 "Pring (Pring R J0) J1" "Pring R I" \<psi>0 "Pring (Pring R J0) J1"]
      ring_hom_ring.homh[of "Pring R I" "Pring (Pring R J0) J1" \<psi>0]
      ring_hom_ring.homh[of "Pring (Pring R J0) J1" "Pring R I" \<psi>1]
    by blast
  from 4 show ?case  
  proof- 
    fix p q
    assume A: "p \<in> carrier (Pring (Pring R J0) J1)"
      "q \<in> carrier (Pring (Pring R J0) J1)"
      "\<psi>0 (\<psi>1 p) = p"
      "\<psi>0 (\<psi>1 q) = q"
    show "\<psi>0 (\<psi>1 (p \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub> q)) = p \<oplus>\<^bsub>Pring (Pring R J0) J1\<^esub> q"
      using A 2 ring_hom_add[of "\<psi>0 \<circ> \<psi>1" "Pring (Pring R J0) J1" "Pring (Pring R J0) J1" p q]
        comp_apply[of \<psi>0 \<psi>1]
      by (simp add: pring_cring.Pring_add pring_cring.Pring_car)
  qed
next
  case (5 p i)
  interpret pring_cring: cring "Pring R J0"
    using Pring_is_cring is_cring by auto 
  interpret Rcring: cring R
    using is_cring by auto 
  have 0: "ring_hom_ring (Pring (Pring R J0) J1) (Pring R I) \<psi>1"
    by (simp add: assms(1) assms(3) assms(4) var_factor_inv_morphism(1)) 
  have 1: "ring_hom_ring (Pring R I) (Pring (Pring R J0) J1) \<psi>0"
    by (simp add: assms(1) assms(3) assms(5) var_factor_morphism'(1))
  have 2: "\<psi>0 \<circ> \<psi>1 \<in> ring_hom (Pring (Pring R J0) J1) (Pring (Pring R J0) J1) "
    using 0 1 ring_hom_trans[of \<psi>1 "Pring (Pring R J0) J1" "Pring R I" \<psi>0 "Pring (Pring R J0) J1"]
      ring_hom_ring.homh[of "Pring R I" "Pring (Pring R J0) J1" \<psi>0]
      ring_hom_ring.homh[of "Pring (Pring R J0) J1" "Pring R I" \<psi>1]
    by blast
  from 5 show ?case 
  proof-
    fix p i assume A: "p \<in> carrier (Pring (Pring R J0) J1)"
      "\<psi>0 (\<psi>1 p) = p"
      "i \<in> J1"
    show " \<psi>0 (\<psi>1 (p \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub> pvar (Pring R J0) i)) =
         p \<otimes>\<^bsub>Pring (Pring R J0) J1\<^esub> pvar (Pring R J0) i"              
    proof- 
      have A1: "\<psi>0 (\<psi>1 (pvar (Pring R J0) i)) = pvar (Pring R J0) i"
        by (metis A(3) assms(1) assms(2) assms(3) assms(4) assms(5) 
            var_factor_inv_morphism(2) var_factor_morphism'(2)) 
      then show ?thesis
        using 2  A ring_hom_mult[of "\<psi>0 \<circ> \<psi>1" "(Pring (Pring R J0) J1)"] 2
          Pring_car  comp_apply[of \<psi>0 \<psi>1] 
        by (metis pring_cring.Pring_car pring_cring.Pring_var_closed)
    qed
  qed
qed


lemma(in cring) var_factor_iso:
  assumes "I = J0 \<union> J1"
  assumes "J1 \<subseteq> I"
  assumes "J1 \<inter> J0 = {}"
  assumes "\<psi>1 = (var_factor_inv I J0 J1)"
  assumes "\<psi>0 = (var_factor I J0 J1)"
  shows "\<psi>0 \<in> ring_iso (Pring R I) (Pring (Pring R J0) J1)"
    "\<psi>1 \<in> ring_iso (Pring (Pring R J0) J1)(Pring R I)"
proof- 
  have 1: "\<psi>0 \<in> ring_hom (Pring R I) (Pring (Pring R J0) J1)"
    "\<psi>1 \<in> ring_hom (Pring (Pring R J0) J1) (Pring R I)"
    "\<And>x. x \<in> carrier (Pring R I) \<Longrightarrow> \<psi>1 (\<psi>0 x) = x"
    "\<And>x. x \<in> carrier (Pring (Pring R J0) J1) \<Longrightarrow> \<psi>0 (\<psi>1 x) = x"
    using assms var_factor_inv_inverse[of I  J0 J1 \<psi>1] var_factor_inverse[of I  J0 J1 \<psi>1]
    by (auto simp add: var_factor_inv_morphism(1) cring.var_factor_morphism'(1) is_cring 
        ring_hom_ring.homh)
  show "\<psi>0 \<in> ring_iso (Pring R I) (Pring (Pring R J0) J1)"
    "\<psi>1 \<in> ring_iso (Pring (Pring R J0) J1) (Pring R I) "
    using 1 ring_iso_memI'[of \<psi>0 "Pring R I" "Pring (Pring R J0) J1"  \<psi>1  ] 
    by auto 
qed


lemma (in cring) is_iso_Prings:
  assumes h1:"I = J0 \<union> J1"
  assumes h2:"J1 \<subseteq> I"
  assumes h3:"J1 \<inter> J0 = {}"
  shows "(Pring (Pring R J0) J1) \<simeq> (Pring R I)" and "(Pring R I) \<simeq> (Pring (Pring R J0) J1)"
proof -
  show \<open>(Pring (Pring R J0) J1) \<simeq> (Pring R I)\<close> 
    unfolding is_ring_iso_def 
    using h2 var_factor_iso[of I J0 J1 \<open>var_factor_inv I J0 J1\<close> \<open>var_factor I J0 J1\<close>]
    using h1 h3 by auto
  show \<open>(Pring R I) \<simeq> (Pring (Pring R J0) J1)\<close> 
    unfolding is_ring_iso_def 
    using h2 var_factor_iso[of I J0 J1 \<open>var_factor_inv I J0 J1\<close> \<open>var_factor I J0 J1\<close>]
    using h1 h3 by auto
qed

subsection \<open>Preliminaries lemmas\<close>
lemma (in cring) poly_no_var:
  assumes \<open>x \<in> ((carrier R) [\<X>\<^bsub>{}\<^esub>]) \<and> xa \<noteq> {#}\<close>
  shows \<open>x xa = \<zero>\<close>
  apply(rule ring.Pring_car_induct''[of "R" x \<open>{}\<close>])
      apply (simp add: local.ring_axioms)
     apply (simp add: Pring_car assms)
  unfolding indexed_const_def using assms 
  by(auto simp add: Pring_add indexed_padd_def) 


lemma (in cring) R_isom_P_mt:\<open>R \<simeq> Pring R {}\<close> 
proof -
  interpret cringP: cring "Pring R {}"
    by (simp add: Pring_is_cring is_cring)
  have f0:\<open>bij_betw indexed_const (carrier R) (carrier (Pring R {}))\<close>
  proof(unfold bij_betw_def inj_on_def, safe)
    fix x y
    assume h1:\<open>x \<in> carrier R\<close>\<open>y \<in> carrier R\<close>\<open>indexed_const x = indexed_const y\<close>
    show \<open>indexed_const x = indexed_const y \<Longrightarrow> x = y\<close>
      by (metis indexed_const_def)
  next
    fix x xa
    assume h1:\<open>xa \<in> carrier R\<close>
    show \<open>indexed_const xa \<in> carrier (Pring R {})\<close>
      by (simp add: h1 indexed_const_closed)
  next
    fix x::\<open>'f multiset \<Rightarrow> 'a\<close>
    assume h1:\<open>x \<in> carrier (Pring R {})\<close>
    then show \<open>x \<in> indexed_const ` carrier R\<close>
      unfolding image_def apply(safe)
      apply(rule bexI[where x=\<open>x {#}\<close>])
      unfolding indexed_const_def
      by (auto simp:fun_eq_iff Pring_def poly_no_var)
  qed
  show ?thesis
    unfolding is_ring_iso_def ring_iso_def 
    apply(subst ex_in_conv[symmetric])
    unfolding ring_hom_def
    apply(rule exI[where  x="indexed_const"])
    apply(safe)
        apply (simp add: indexed_const_closed)
       apply (simp add: indexed_const_mult)
    using  cringP.indexed_padd_const 
      apply (simp add: Pring_add indexed_padd_const)
     apply (simp add: Pring_one)
    by(simp add:f0)
qed

subsection \<open>Hilbert Basis theorem\<close>
text \<open>We show after this Hilbert basis theorem, based on Indexed Polynomials in HOL-Algebra
and its extension in $Padic_Fields$\<close>

theorem (in domain) Hilbert_basis:
  assumes h1:\<open>noetherian_ring R\<close> and h2:\<open>finite I\<close>
  shows \<open>noetherian_ring (Pring R I)\<close>
proof(induct rule :finite.induct[OF h2])
  case 1
  interpret cringP: cring "Pring R {}"
    by (simp add: Pring_is_cring is_cring)
  show ?case 
    using R_isom_P_mt cringP.ring_axioms h1 noetherian_isom_imp_noetherian by auto
next
  case (2 A a)
  have f0:\<open>noetherian_ring (Pring R A)\<close> 
    using 2 by blast
  have f1:\<open>cring (Pring R A)\<close>
    using Pring_is_cring is_cring by auto
  interpret UPcring: UP_cring "Pring R A" "UP (Pring R A)"
    by (simp add: UP_cring.intro f1)+
  have f2:\<open>Pring (Pring R A) {a} \<simeq> UP (Pring R A)\<close>
    using cring.Pring_one_index_isom_P UP_cring_def f1 
    by (simp add: UPcring.R.Pring_one_index_isom_P)
  then have f3:\<open>noetherian_ring (UP (Pring R A))\<close> 
    using Pring_is_domain domain.noetherian_R_imp_noetherian_UP_R f0 by blast
  have f7:\<open>cring (Pring (Pring R A) {a})\<close>
    by (simp add: UPcring.R.Pring_is_cring f1)
  then have \<open>UP (Pring R A) \<simeq> Pring (Pring R A) {a}\<close>
    by (simp add: cring_def f2 ring_iso_sym)
  have f6:\<open>noetherian_ring (Pring (Pring R A) {a})\<close>
    using \<open>UP (Pring R A) \<simeq> Pring (Pring R A) {a}\<close> cring.axioms(1) f3 
      f7 noetherian_isom_imp_noetherian by auto
  have f10:\<open>a\<notin>A \<Longrightarrow> Pring (Pring R A) {a} \<simeq> (Pring R (insert a A))\<close>
    apply(rule cring.is_iso_Prings(1))
    by (simp add: is_cring)+
  have f11:\<open>ring (Pring R (insert a A))\<close>
    by (simp add: Pring_is_ring)
  then show ?case 
    apply(cases \<open>a\<in>A\<close>)
    using f0 
     apply (simp add: insert_absorb)
    using noetherian_isom_imp_noetherian[of \<open>Pring (Pring R A) {a}\<close> 
        \<open>(Pring R (insert a A))\<close>] f10 f11 f6 by(simp)
qed

lemma (in domain) R_noetherian_implies_IP_noetherian:
  assumes h1:\<open>noetherian_ring R\<close> 
  shows \<open>noetherian_ring (Pring R {0..N::nat})\<close>
  using Hilbert_basis h1 by blast

lemma (in domain) IP_noetherian_implies_R_noetherian:
  assumes h1:\<open>noetherian_ring (Pring R I)\<close> and h2:\<open>finite I\<close>
  shows \<open>noetherian_ring R\<close>
proof(insert h1, induct rule:finite.induct[OF h2])
  case 1
  interpret cringP: cring "Pring R {}"
    by (simp add: Pring_is_cring is_cring)
  have \<open>Pring R {} \<simeq> R\<close>
    using local.ring_axioms R_isom_P_mt ring_iso_sym by blast
  then show ?case 
    using "1" local.ring_axioms noetherian_isom_imp_noetherian by blast
next
  case (2 A a)
  have f1:\<open>cring (Pring R A)\<close>
    using Pring_is_cring is_cring by auto
  interpret UPcring: UP_cring "Pring R A" "UP (Pring R A)"
    by (simp add: UP_cring.intro f1)+
  interpret dom: domain "(Pring R (A))"
    using Pring_is_domain by blast
  have f2:\<open>Pring (Pring R A) {a} \<simeq> UP (Pring R A)\<close>
    using cring.Pring_one_index_isom_P UP_cring_def f1 
    by (simp add: UPcring.R.Pring_one_index_isom_P)
  {assume h2:\<open>a\<notin>A\<close>
    then have \<open> (Pring (Pring R (A)) {a}) \<simeq> (Pring R (insert a A))\<close>
      by (simp add: cring.is_iso_Prings(1) is_cring)
    then have \<open>noetherian_ring (Pring (Pring R (A)) {a})\<close> 
      using "2.prems" UPcring.R.Pring_is_ring 
        noetherian_isom_imp_noetherian ring_iso_sym by blast
    then have \<open>noetherian_ring (Pring R (A))\<close>
      by (simp add: dom.IP_noeth_imp_R_noeth)
    then have \<open>noetherian_ring R\<close> 
      using "2.hyps"(2) by blast}note a_not_in=this
  then show ?case apply(cases \<open>a\<in>A\<close>)
    using 2 
     apply (simp add: insert_absorb)
    using a_not_in by blast
qed



end