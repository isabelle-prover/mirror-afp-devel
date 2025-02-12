section \<open>Examples\<close>
theory Examples_Noetherian_Rings

imports 
  "Hilbert_Basis" 
  Real_Ring_Definition
begin

subsection \<open>Examples of noetherian rings with \<open>\<int>\<close> and \<open>\<int>[X]\<close>\<close>
lemma INTEG_euclidean_domain:\<open>euclidean_domain INTEG (\<lambda>x. nat (abs x))\<close>
  apply(rule domain.euclidean_domainI)
  unfolding domain_def domain_axioms_def using INTEG_cring apply(simp add:INTEG_def)
  unfolding INTEG_def 
  using abs_mod_less div_mod_decomp_int mult.commute 
  by (metis Diff_iff INTEG.R.r_null INTEG_def INTEG_mult UNIV_I abs_ge_zero insert_iff 
      mult_zero_left nat_less_eq_zless partial_object.select_convs(1) ring_record_simps(12))


lemma principal_ideal_INTEG:\<open>ideal I INTEG \<Longrightarrow> principalideal I INTEG\<close>
proof(rule principalidealI)
  assume h:\<open>ideal I INTEG\<close>
  then show \<open>ideal I INTEG\<close> by(simp)
  {assume h1:\<open>I \<noteq> {0}\<close>
    define E where imp:\<open>E\<equiv>{nat (abs x)|x. x\<in>I \<and> x\<noteq>0}\<close>
    then have \<open>E\<noteq>{}\<close> 
      using h h1 additive_subgroup.zero_closed unfolding ideal_def 
      by fastforce
    then have \<open>\<exists>n\<in>E. \<forall>x\<in>E. n\<le>x \<and> n>0\<close>
      using abs_ge_zero imp zero_less_abs_iff 
      by (smt (verit) all_not_in_conv exists_least_iff gr_zeroI leI mem_Collect_eq nat_0_iff)
    define E' where imp2:\<open>E'\<equiv>{(abs x)|x. x\<in>I \<and> x\<noteq>0}\<close>
    then have \<open>bij_betw nat E' E\<close>
      unfolding bij_betw_def
      apply(safe) 
      using inj_on_def apply force
      using imp apply blast
      using imp by blast
    then have \<open>\<exists>n\<in>E'. \<forall>x\<in>E'. n\<le>x \<and> n>0\<close> 
      by (smt (verit, best) \<open>\<exists>n\<in>E. \<forall>x\<in>E. n \<le> x \<and> 0 < n\<close> 
          bij_betw_iff_bijections le_nat_iff nat_eq_iff2 nat_le_iff zero_less_nat_eq) 
    then obtain n where f1:\<open>\<forall>x\<in>E'. n\<le>x \<and> n>0 \<and> n\<in>E'\<close> by blast
    then have \<open>\<exists>a\<in>I. abs a =  n\<close> 
      using \<open>\<exists>n\<in>E'. \<forall>x\<in>E'. n \<le> x \<and> 0 < n\<close> imp2 by blast 
    then obtain a where f0:\<open>a\<in>I \<and> abs a =  n\<close> by blast
    then have \<open>\<forall>x. \<exists>q r. x = a*q+r \<and> abs r < abs a\<close>
      using INTEG_euclidean_domain unfolding euclidean_domain_def 
      by (metis \<open>\<exists>n\<in>E'. \<forall>x\<in>E'. n \<le> x \<and> 0 < n\<close> \<open>\<forall>x\<in>E'. n \<le> x \<and> 0 < n \<and> n \<in> E'\<close> 
          abs_mod_less div_mod_decomp_int mult.commute zero_less_abs_iff)
    then have f2:\<open>x\<in>I\<and> r =x - a*q \<Longrightarrow> r\<in>I\<close> for q r x
      using h unfolding ideal_def INTEG_def additive_subgroup_def subgroup_def ideal_axioms_def
        ring_def apply(safe, simp)
      by (metis \<open>a \<in> I \<and> \<bar>a\<bar> = n\<close> integer_group_def inv_integer_group uminus_add_conv_diff)
    have f3:\<open>x\<in>I\<and> r =x - a*q \<Longrightarrow> abs r < abs a \<Longrightarrow> r = 0\<close> for r q x 
      apply(frule f2)
      using imp2 f1 f0
      by fastforce
    have \<open>x\<in>I\<and> r =x - a*q \<Longrightarrow> abs r < abs a \<Longrightarrow> x \<in> Idl\<^bsub>INTEG\<^esub> {a}\<close>
      for x r q 
      apply(frule f3)
       apply blast
      unfolding genideal_def ideal_def INTEG_def additive_subgroup_def 
        subgroup_def ideal_axioms_def by(auto)
    then have \<open>x\<in>I \<Longrightarrow> x \<in> Idl\<^bsub>INTEG\<^esub> {a}\<close>   for x
      by (metis \<open>\<forall>x. \<exists>q r. x = a * q + r \<and> \<bar>r\<bar> < \<bar>a\<bar>\<close> add_diff_cancel_left')
    then have \<open>ideal I INTEG \<Longrightarrow> \<exists>i\<in>carrier INTEG. I = Idl\<^bsub>INTEG\<^esub> {i}\<close>
      using INTEG.R.cgenideal_eq_genideal INTEG.R.cgenideal_minimal f0 by blast
  }note non_trivial_ideal=this
  show \<open>\<exists>i\<in>carrier INTEG. I = Idl\<^bsub>INTEG\<^esub> {i}\<close>
    apply(cases \<open>I={0}\<close>) 
     apply (metis INTEG.R.genideal_self 
        INTEG.R.ring_axioms INTEG_closed h ring.Idl_subset_ideal subsetI subset_antisym)
    using non_trivial_ideal h by auto
qed


lemma INTEG_noetherian_ring:\<open>noetherian_ring INTEG\<close>
  apply(rule ring.noetherian_ringI)
   apply (simp add: INTEG.R.ring_axioms)
  using principal_ideal_INTEG unfolding principalideal_def
  by (meson INTEG_closed finite.emptyI finite_insert principalideal_axioms_def subsetI)

lemma INTEG_noetherian_domain:\<open>noetherian_domain INTEG\<close>
  unfolding noetherian_domain_def 
  using INTEG_noetherian_ring INTEG_euclidean_domain euclidean_domain.axioms(1) by blast

lemma Polynomials_INTEG_noetherian_ring:\<open>noetherian_ring (univ_poly INTEG (carrier INTEG))\<close>
  by (simp add: INTEG_noetherian_domain noetherian_domain.weak_Hilbert_basis)

lemma Polynomials_INTEG_noetherian_domain: \<open>noetherian_domain (univ_poly INTEG (carrier INTEG))\<close>
  using INTEG.R.ring_axioms INTEG_noetherian_domain Polynomials_INTEG_noetherian_ring 
    domain.univ_poly_is_domain noetherian_domain.axioms(2) noetherian_domain.intro 
    ring.carrier_is_subring by blast



subsection \<open>Another example with \<open>\<real>\<close> and \<open>\<real>[X]\<close>\<close>

lemma REAL_noetherian_domain:\<open>noetherian_domain REAL\<close>
  unfolding noetherian_domain_def 
  by (simp add: REAL_field domain.noetherian_RX_imp_noetherian_R domain.univ_poly_is_principal 
      field.axioms(1) field.carrier_is_subfield principal_imp_noetherian)

lemma PolyREAL_noetherian_domain:\<open>noetherian_domain (univ_poly REAL (carrier REAL))\<close>
  unfolding noetherian_domain_def 
  by (simp add: REAL_field REAL_noetherian_domain REAL_ring domain.univ_poly_is_domain 
      field.axioms(1) noetherian_domain.weak_Hilbert_basis ring.carrier_is_subring)


end