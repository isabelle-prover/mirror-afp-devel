section \<open>Ring Miscellaneous\<close>
theory Ring_Misc

imports 
  "HOL-Algebra.RingHom" 
  "HOL-Algebra.QuotRing" 
  "HOL-Algebra.Embedded_Algebras"
begin

text \<open>Some lemmas that may be considered as useful, and that helps for the Hilbert's basis proof\<close>

lemma (in ring)carrier_quot: \<open>ideal I R \<Longrightarrow> carrier (R Quot I) = {{y\<oplus>x | y. y\<in>I} |x. x\<in>carrier R}\<close>
proof(safe)
  fix x
  assume h:\<open>ideal I R\<close> \<open>x \<in> carrier (R Quot I)\<close>
  then have \<open>\<exists>xa\<in>carrier R. x = (\<Union>x\<in>I. {x \<oplus> xa})\<close> 
    unfolding FactRing_def A_RCOSETS_def RCOSETS_def cgenideal_def r_coset_def 
    by(simp) 
  then obtain y where \<open>x = (\<Union>x\<in>I. {x \<oplus> y}) \<and> y \<in>carrier R\<close> by blast
  with h show \<open>\<exists>xa. x = {y \<oplus> xa |y. y \<in> I} \<and> xa \<in> carrier R\<close>
    by(blast) 
next
  fix x xa
  assume \<open>ideal I R\<close> \<open>xa \<in> carrier R\<close>
  then show \<open>{y \<oplus> xa |y. y \<in> I} \<in> carrier (R Quot I)\<close>
    unfolding FactRing_def A_RCOSETS_def RCOSETS_def cgenideal_def r_coset_def 
    apply simp
    apply(rule bexI[where x=xa])
    by auto
qed


context
  fixes A B h
  assumes ring_A: \<open>ring A\<close>
  assumes ring_B: \<open>ring B\<close>
  assumes h1:\<open>h\<in>ring_iso A B\<close>
begin
interpretation ringA: ring A
  using ring_A by auto
interpretation ringB: ring B
  using ring_B by auto

interpretation rhr:ring_hom_ring A B h
  apply(unfold_locales)
  using h1 unfolding ring_iso_def by auto

lemma inv_img_exist:\<open>\<forall>xa\<in>carrier B. \<exists>y.  y \<in> carrier A \<and> h y = xa\<close>
  using h1 bij_betw_iff_bijections[of h \<open>carrier A\<close> \<open>carrier B\<close>] unfolding ring_iso_def
  by(auto)

lemma img_ideal_is_ideal:assumes j1:\<open>ideal I A\<close> 
  shows \<open>ideal (h ` I) B\<close>
proof(intro idealI)
  show \<open>ring B\<close>
    by(simp add: ringB.ring_axioms) 
  from j1 show \<open>subgroup (h ` I) (add_monoid B)\<close>
    by (metis (no_types, lifting) additive_subgroup_def ideal_def rhr.img_is_add_subgroup)
  fix a x
  assume hyp:\<open>a \<in> h ` I\<close> \<open>x \<in> carrier B\<close> 
  with j1 show fst:\<open>x \<otimes>\<^bsub>B\<^esub> a \<in> h ` I\<close>
    by (smt (verit, ccfv_threshold) inv_img_exist h1  ideal.I_l_closed ideal.Icarr image_iff ring_iso_memE(2))
  from j1 show \<open>a \<otimes>\<^bsub>B\<^esub> x \<in> h ` I\<close> 
    using inv_img_exist fst hyp(2) 
    by (smt (verit, best) hyp(1) ideal.I_r_closed ideal.Icarr image_iff rhr.hom_mult)
qed


lemma img_in_carrier_quot:\<open>\<forall>x\<in> carrier (A Quot I). h ` x \<in> carrier (B Quot (h`I))\<close> if j:\<open>ideal I A\<close> for I
proof(subst ringA.carrier_quot(1)[OF j],subst ringB.carrier_quot[of \<open>h`I\<close>], safe)
  show \<open>ideal (h ` I) B\<close> 
    using img_ideal_is_ideal that by blast
next
  fix x xa
  assume h:\<open>xa \<in> carrier A\<close>
  then show \<open>\<exists>x. h ` {y \<oplus>\<^bsub>A\<^esub> xa |y. y \<in> I} = {y \<oplus>\<^bsub>B\<^esub> x |y. y \<in> h ` I} \<and> x \<in> carrier B\<close>
    apply(intro exI[where x=\<open>h xa\<close>])
    apply(safe)       
    using h1 j ideal.Icarr ring_iso_memE(3) that apply fastforce
    using h1 ideal.Icarr image_iff mem_Collect_eq ring_iso_memE(3) that apply fastforce
    by (meson h1 ring_iso_memE(1))
qed

lemma f8:\<open>xa\<in>carrier B \<and> xb\<in>I \<Longrightarrow>h(xb \<oplus>\<^bsub>A\<^esub> inv_into (carrier A) h xa) = h xb  \<oplus>\<^bsub>B\<^esub> xa\<close> if j:\<open>ideal I A\<close> for I xb xa
proof -
  assume "xa \<in> carrier B \<and> xb \<in> I"
  then show ?thesis
    using inv_img_exist f_inv_into_f[of xa h \<open>carrier A\<close>] ideal.Icarr[OF that, of xb] 
      inv_into_into[of xa h] 
    by(auto)
qed

lemma f9:\<open>\<forall>xa\<in>carrier B. \<forall>xb\<in>carrier A. \<exists>y. h y = h xb \<oplus>\<^bsub>B\<^esub> xa\<close>
  using f8 ringA.oneideal by blast

lemma img_over_set_is_iso: \<open>ideal I A \<Longrightarrow> ((`) h) \<in> ring_iso (A Quot I) (B Quot (h`I))\<close> for I
proof(rule ring_iso_memI)
  fix x
  assume k:\<open>ideal I A\<close> \<open>x \<in> carrier (A Quot I)\<close>
  then show \<open>h ` x \<in> carrier (B Quot h ` I)\<close>
    using h1 ringA.ring_axioms ringB.ring_axioms
    by(simp add:img_in_carrier_quot)
  fix y
  {
    fix xa xb xc
    assume g:\<open>xa \<in> x\<close> \<open>xb \<in> y\<close> \<open>xc \<in> I\<close> \<open>ideal I A\<close>\<open>x \<in> a_rcosets\<^bsub>A\<^esub> I\<close> \<open>y \<in> a_rcosets\<^bsub>A\<^esub> I\<close>
    have xa:\<open>xa \<in> carrier A\<close> 
      using abelian_subgroup.a_rcosets_carrier abelian_subgroupI3 g(1) g(5) 
        ideal_def k(1) ring_def by blast
    have xb:\<open>xb \<in>carrier A\<close> 
      using abelian_subgroup.a_rcosets_carrier abelian_subgroupI3 g(2) g(6) 
        ideal_def k(1) ring_def by blast
    have xc:\<open>xc\<in>carrier A\<close>
      using g(3) k(1) ringA.ideal_is_subalgebra ringA.subalgebra_in_carrier by fastforce
    have \<open>\<exists>x\<in>x. \<exists>xd\<in>y. \<exists>xe\<in>I. h (xc \<oplus>\<^bsub>A\<^esub> xa \<otimes>\<^bsub>A\<^esub> xb) = h xe \<oplus>\<^bsub>B\<^esub> h x \<otimes>\<^bsub>B\<^esub> h xd \<close>
      apply(rule bexI[where x=xa]) 
       apply(rule bexI[where x=xb]) 
        apply(rule bexI[where x=xc]) 
      using g rhr.hom_add[OF xc ] rhr.hom_mult[OF xa xb] 
      using ringA.m_closed xa xb by presburger+ 
  }note fst_prf=this 
  {fix xa xb xc
    assume g:\<open>xa \<in> x\<close> \<open>xb \<in> y\<close> \<open>xc \<in> I\<close> \<open>ideal I A\<close>\<open>x \<in> a_rcosets\<^bsub>A\<^esub> I\<close> \<open>y \<in> a_rcosets\<^bsub>A\<^esub> I\<close>
    have xa:\<open>xa \<in> carrier A\<close> 
      using abelian_subgroup.a_rcosets_carrier abelian_subgroupI3 g(1) g(5) 
        ideal_def k(1) ring_def by blast
    have xb:\<open>xb \<in>carrier A\<close> 
      using abelian_subgroup.a_rcosets_carrier abelian_subgroupI3 g(2) g(6) 
        ideal_def k(1) ring_def by blast
    have xc:\<open>xc\<in>carrier A\<close>
      using g(3) k(1) ringA.ideal_is_subalgebra ringA.subalgebra_in_carrier by fastforce
    have \<open>\<exists>ya\<in>x. \<exists>y\<in>y. \<exists>yb\<in>I. h xc \<oplus>\<^bsub>B\<^esub> h xa \<otimes>\<^bsub>B\<^esub> h xb = h (yb \<oplus>\<^bsub>A\<^esub> ya \<otimes>\<^bsub>A\<^esub> y)\<close>
      apply(rule bexI[where x=xa]) 
       apply(rule bexI[where x=xb])
        apply(rule bexI[where x=xc]) 
      using g rhr.hom_add[OF xc ] rhr.hom_mult[OF xa xb] 
      using ringA.m_closed xa xb by presburger+ }note snd_prf=this
  assume k1:\<open>y \<in> carrier (A Quot I)\<close>
  with k show \<open>h ` (x \<otimes>\<^bsub>A Quot I\<^esub> y) = h ` x \<otimes>\<^bsub>B Quot h ` I\<^esub> h ` y\<close>
    by(auto simp:FactRing_def image_iff rcoset_mult_def r_coset_def a_r_coset_def snd_prf fst_prf)
  from k k1 show \<open>h ` (x \<oplus>\<^bsub>A Quot I\<^esub> y) = h ` x \<oplus>\<^bsub>B Quot h ` I\<^esub> h ` y\<close>
    apply(simp add:FactRing_def rcoset_mult_def r_coset_def a_r_coset_def)
    using h1 ring_A ring_B unfolding ring_iso_def FactRing_def rcoset_mult_def r_coset_def a_r_coset_def
    by (metis (no_types, lifting) abelian_subgroup.a_rcosets_carrier abelian_subgroupI3
        ideal.axioms(1) mem_Collect_eq ring_def set_add_hom)
next 
  assume k:\<open>ideal I A\<close>
  have important:\<open>xa \<in> carrier (B Quot h ` I) \<Longrightarrow> \<exists>y\<in>carrier (A Quot I). h ` y = xa\<close> for xa
  proof(rule bexI[where x=\<open>inv_into (carrier A) h ` xa\<close>])
    assume g:\<open>xa \<in> carrier (B Quot h ` I)\<close>
    then show \<open>h ` inv_into (carrier A) h ` xa = xa\<close>
      by (metis Sup_le_iff bij_betw_def img_ideal_is_ideal h1 image_inv_into_cancel k 
          ringB.canonical_proj_vimage_in_carrier ring_iso_memE(5) subset_refl)
    {fix x
      assume g1:\<open>x\<in>carrier B\<close> \<open> xa = (\<Union>xa\<in>I. {h xa \<oplus>\<^bsub>B\<^esub> x})\<close>
      {fix xaa
        assume g2:\<open>xaa \<in> I\<close>
        with g1 have \<open>\<exists>xa\<in>I. (SOME y. y \<in> carrier A \<and> h y = h xaa \<oplus>\<^bsub>B\<^esub> x) = xa \<oplus>\<^bsub>A\<^esub> inv_into (carrier A) h x\<close>
          by (smt (verit, del_insts) bij_betw_def bij_betw_iff_bijections h1 ideal.Icarr 
              inv_into_f_f k rhr.hom_add ringA.add.m_closed ring_iso_memE(5) some_equality)
      }note 2=this
      {fix xaa
        assume \<open>xaa\<in>I\<close>
        with g1 have \<open>xaa \<oplus>\<^bsub>A\<^esub> inv_into (carrier A) h x = (SOME y. y \<in> carrier A \<and> h y = h xaa \<oplus>\<^bsub>B\<^esub> x)\<close>
          using h1 ring_A ring_B unfolding ring_iso_def
          by (smt (verit, del_insts) bij_betw_def k inv_img_exist f8 h1 ideal.Icarr
              inv_into_f_f mem_Collect_eq ringA.add.m_closed someI_ex)
      }note 3=this
      from g1 have \<open>\<exists>xa\<in>carrier A. (\<lambda>x. SOME y. y \<in> carrier A \<and> h y = x) ` (\<Union>xa\<in>I. {h xa \<oplus>\<^bsub>B\<^esub> x}) = (\<Union>x\<in>I. {x \<oplus>\<^bsub>A\<^esub> xa})\<close>
        apply(intro bexI[where x=\<open>inv_into (carrier A) h x\<close>]) 
        using inv_img_exist image_eqI inv_into_into[of x h \<open>carrier A\<close>] 
        by(auto simp: 2 3) 
    }note 1 =this
    from g show \<open>inv_into (carrier A) h ` xa \<in> carrier (A Quot I)\<close>
      unfolding FactRing_def inv_into_def A_RCOSETS_def RCOSETS_def r_coset_def by(auto simp:1)  
  qed
  have imp2:\<open>\<forall>J\<subseteq>carrier A. \<forall>K\<subseteq>carrier A. h ` J = h ` K \<longrightarrow> J = K\<close>
    unfolding image_def using h1  apply(safe) 
    using h1 ring_A ring_B unfolding ring_iso_def 
    by (smt (verit, ccfv_SIG) bij_betw_iff_bijections in_mono mem_Collect_eq) +
  with important have important3:\<open>xa \<in> carrier (B Quot h ` I) 
  \<Longrightarrow> \<exists>!y\<in>carrier (A Quot I). h ` y = xa\<close> for xa
    apply(safe) 
      apply blast
     apply (metis Sup_le_iff equalityE k ringA.canonical_proj_vimage_in_carrier)
    by (metis Sup_le_iff dual_order.refl k ringA.canonical_proj_vimage_in_carrier)
  have bij_inv:\<open>bij_betw (inv_into (carrier A) h) (carrier B) (carrier A)\<close>
    by (simp add: bij_betw_inv_into h1 ring_iso_memE(5))
  with k show \<open>h ` \<one>\<^bsub>A Quot I\<^esub> = \<one>\<^bsub>B Quot h ` I\<^esub>\<close> 
    apply(auto simp:image_def FactRing_def rcoset_mult_def r_coset_def a_r_coset_def) [1]
     apply (smt (verit, ccfv_threshold) h1 ideal.Icarr insert_iff ringA.one_closed ring_iso_memE(3) ring_iso_memE(4))
    by (metis (full_types) h1 ideal.Icarr ringA.one_closed ring_iso_memE(3) ring_iso_memE(4) singletonI)
  show \<open>bij_betw ((`) h) (carrier (A Quot I)) (carrier (B Quot h ` I))\<close>
  proof(intro  bij_betw_byWitness[where ?f' = "(`) (inv_into (carrier A) h)"])
    from k show \<open>\<forall>a\<in>carrier (A Quot I). inv_into (carrier A) h ` h ` a = a\<close>
      apply(intro ballI)
      apply(subst inv_into_image_cancel) 
      using bij_betw_def h1 ring_A ring_B unfolding ring_iso_def apply blast
       apply (metis FactRing_def abelian_subgroup.a_rcosets_carrier 
          abelian_subgroupI3 ideal_def partial_object.select_convs(1) ring_def)
      by(simp)
    from k show \<open>\<forall>a'\<in>carrier (B Quot h ` I). h ` inv_into (carrier A) h ` a' = a'\<close>
      using ring_A ring_B h1 unfolding ring_iso_def
      by (metis (no_types, lifting) Sup_le_iff bij_betw_def img_ideal_is_ideal image_inv_into_cancel
          mem_Collect_eq ringB.canonical_proj_vimage_in_carrier subset_refl)
    from k show \<open>(`) h ` carrier (A Quot I) \<subseteq> carrier (B Quot h ` I)\<close>
      using img_in_carrier_quot by blast
    from k show \<open>(`) (inv_into (carrier A) h) ` carrier (B Quot h ` I) \<subseteq> carrier (A Quot I)\<close>
      apply(subst (1) image_def)
      apply(safe)  
      by (metis \<open>\<forall>a\<in>carrier (A Quot I). inv_into (carrier A) h ` h ` a = a\<close> important3)
  qed
qed   
end

lemma Quot_iso_cgen:\<open>a\<in>carrier A \<and> b:carrier B \<and> cring A \<and> cring B \<and> h \<in> ring_iso A B \<and>  h(a) = b 
\<Longrightarrow> A Quot (cgenideal A a) \<simeq> B Quot (cgenideal B b)\<close>
  unfolding is_ring_iso_def ring_iso_def 
proof(subst ex_in_conv[symmetric]) 
  assume h1:\<open>a\<in>carrier A \<and> b:carrier B \<and>cring A \<and> cring B \<and> h \<in> {h \<in> ring_hom A B. bij_betw h (carrier A) (carrier B)} \<and> h a = b\<close>
  have h1':\<open>h \<in> ring_iso A B\<close>
    using h1 apply(fold ring_iso_def) by simp
  interpret ringA: cring A
    using h1 by auto
  interpret ringB: cring B
    using h1 by simp
  have f1:\<open>\<forall>xa\<in>carrier B. \<exists>y.  y \<in> carrier A \<and> h y = xa\<close>
    by (metis (no_types, lifting) bij_betw_iff_bijections h1 mem_Collect_eq)
  have f0:\<open>ideal (PIdl\<^bsub>A\<^esub> a) A \<and> ideal (PIdl\<^bsub>B\<^esub> b) B\<close>
    using ringA.cgenideal_ideal[of a] ringB.cgenideal_ideal[of b] h1 by(simp)
  then have f2:\<open>(carrier (A Quot PIdl\<^bsub>A\<^esub> a)) = {{y\<oplus>\<^bsub>A\<^esub>x | y. y\<in>PIdl\<^bsub>A\<^esub> a} |x. x\<in>carrier A}
\<close> \<open>(carrier (B Quot PIdl\<^bsub>B\<^esub> b)) = {{y\<oplus>\<^bsub>B\<^esub>x | y. y\<in>PIdl\<^bsub>B\<^esub> b} |x. x\<in>carrier B}\<close>
    using ringA.carrier_quot ringB.carrier_quot by simp+
  then have \<open>h`(PIdl\<^bsub>A\<^esub> a) = (PIdl\<^bsub>B\<^esub> b)\<close>
    unfolding image_def cgenideal_def 
  proof(safe) 
    fix x xa xb
    assume h2:\<open> carrier (A Quot {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}) = {{y \<oplus>\<^bsub>A\<^esub> x |y. y \<in> {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}} |x. x \<in> carrier A}\<close>
      \<open>carrier (B Quot {x \<otimes>\<^bsub>B\<^esub> b |x. x \<in> carrier B}) = {{y \<oplus>\<^bsub>B\<^esub> x |y. y \<in> {x \<otimes>\<^bsub>B\<^esub> b |x. x \<in> carrier B}} |x. x \<in> carrier B}\<close>
      \<open>xb \<in> carrier A\<close>
    then show \<open>\<exists>x. h (xb \<otimes>\<^bsub>A\<^esub> a) = x \<otimes>\<^bsub>B\<^esub> b \<and> x \<in> carrier B\<close>
      using h1 ring_iso_def ring_iso_memE(1) ring_iso_memE(2) by fastforce
  next
    fix x xa
    assume h2:\<open> carrier (A Quot {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}) = {{y \<oplus>\<^bsub>A\<^esub> x |y. y \<in> {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}} |x. x \<in> carrier A}\<close>
      \<open>carrier (B Quot {x \<otimes>\<^bsub>B\<^esub> b |x. x \<in> carrier B}) = {{y \<oplus>\<^bsub>B\<^esub> x |y. y \<in> {x \<otimes>\<^bsub>B\<^esub> b |x. x \<in> carrier B}} |x. x \<in> carrier B}\<close>
      \<open>xa \<in> carrier B\<close>
    show \<open>\<exists>x\<in>{x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}. xa \<otimes>\<^bsub>B\<^esub> b = h x \<close>
      using f1 h1 h1' h2(3) ring_iso_memE(2) by fastforce
  qed
  then have \<open>\<forall>x\<in>(PIdl\<^bsub>B\<^esub> b). \<exists>!y\<in>(PIdl\<^bsub>A\<^esub> a). h y = x\<close>
    by (smt (verit) bij_betw_iff_bijections f0 h1 ideal.Icarr image_def mem_Collect_eq)
  then have \<open>x\<in>carrier (A Quot {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A}) \<Longrightarrow> \<exists>y'\<in>carrier A. x = {y\<oplus>\<^bsub>A\<^esub>y' | y. y\<in>PIdl\<^bsub>A\<^esub> a}\<close> for x
  proof -
    assume a1: "x \<in> carrier (A Quot {x \<otimes>\<^bsub>A\<^esub> a |x. x \<in> carrier A})"
    have f2: "\<forall>Aa Ab. Ab \<notin> carrier (A Quot Aa) \<or> \<not> ideal Aa A 
              \<or> (\<exists>a. Ab = {aa \<oplus>\<^bsub>A\<^esub> a |aa. aa \<in> Aa} \<and> a \<in> carrier A)"
      using ringA.carrier_quot by auto
    have "x \<in> carrier (A Quot PIdl\<^bsub>A\<^esub> a)"
      using a1 by (simp add: cgenideal_def)
    then show ?thesis
      using f2 f0 by blast
  qed
  show \<open>\<exists>x. x \<in> {h \<in> ring_hom (A Quot PIdl\<^bsub>A\<^esub> a) (B Quot PIdl\<^bsub>B\<^esub> b).
              bij_betw h (carrier (A Quot PIdl\<^bsub>A\<^esub> a)) (carrier (B Quot PIdl\<^bsub>B\<^esub> b))}\<close>
    apply(fold ring_iso_def)
    apply(intro exI[where x=\<open>\<lambda>x. h`x\<close>])
    using \<open>h ` (PIdl\<^bsub>A\<^esub> a) = PIdl\<^bsub>B\<^esub> b\<close> f0 h1' img_over_set_is_iso ringA.ring_axioms ringB.ring_axioms 
    by force
qed


end