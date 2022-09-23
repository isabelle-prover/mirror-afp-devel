theory Fraction_Field
  imports "HOL-Algebra.UnivPoly"
          Localization_Ring.Localization
          "HOL-Algebra.Subrings"
          Padic_Ints.Supplementary_Ring_Facts
begin

section\<open>The Field of Fractions of a Ring\<close>

text\<open>
  This theory defines the fraction field of a domain and establishes its basic properties.
  The fraction field is defined in the standard way as the localization of a domain at its nonzero
  elements. This is done by importing the AFP session \texttt{Localization\_Ring}. Choice functions
  for numerator and denominators of fractions are introduced, and the inclusion of a domain into
  its ring of fractions is defined.
\<close>

subsection\<open>The Monoid of Nonzero Elements in a Domain\<close>
locale domain_frac = domain

lemma zero_not_in_nonzero: "\<zero>\<^bsub>R\<^esub> \<notin> nonzero R"
  unfolding nonzero_def by blast 

lemma(in domain) nonzero_is_submonoid: "submonoid R (nonzero R)"
proof
  show " nonzero R \<subseteq> carrier R"
    using nonzero_def by fastforce
  show "\<And>x y. x \<in> nonzero R \<Longrightarrow> y \<in> nonzero R \<Longrightarrow> x \<otimes> y \<in> nonzero R" 
    by (metis (mono_tags, lifting) local.integral m_closed mem_Collect_eq nonzero_def)
  show "\<one> \<in> nonzero R"
    by (simp add: nonzero_def)
qed

lemma(in domain) nonzero_closed:
  assumes "a \<in> nonzero R"
  shows "a \<in> carrier R"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) nonzero_mult_closed:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "a \<otimes> b \<in> carrier R"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) nonzero_one_closed:
"\<one> \<in> nonzero R"
  by (simp add: nonzero_def)

lemma(in domain) nonzero_memI:
  assumes "a \<in> carrier R"
  assumes "a \<noteq> \<zero>"
  shows "a \<in> nonzero R"
  using assms by(simp add: nonzero_def)

lemma(in domain) nonzero_memE:
  assumes "a \<in> nonzero R"
  shows "a \<in> carrier R" "a \<noteq>\<zero>"
  using assms by(auto simp: nonzero_def)

lemma(in domain) not_nonzero_memE:
  assumes "a \<notin> nonzero R"
  assumes "a \<in> carrier R"
  shows "a = \<zero>"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) not_nonzero_memI:
  assumes "a = \<zero>"
  shows "a \<notin> nonzero R"
  using assms nonzero_memE(2) by auto

lemma(in domain) one_nonzero:
"\<one> \<in> nonzero R"
  by (simp add: nonzero_one_closed)

lemma(in domain_frac) eq_obj_rng_of_frac_nonzero:
  "eq_obj_rng_of_frac R (nonzero R)"
  using nonzero_is_submonoid 
  by (simp add: eq_obj_rng_of_frac.intro 
      is_cring local.ring_axioms mult_submonoid_of_crng_def mult_submonoid_of_rng_def)

subsection\<open>Numerator and Denominator Choice Functions\<close>

definition(in eq_obj_rng_of_frac) denom where
"denom a = (if (a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>) then \<one> else ( snd (SOME x. x \<in> a)))"
      
text\<open>The choice function for numerators must be compatible with denom:\<close>

definition(in eq_obj_rng_of_frac) numer where
"numer a = (if (a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>) then \<zero> else (fst (SOME x. x \<in> a \<and> (snd x = denom a))))"

text\<open>Basic properties of numer and denom:\<close>
lemma(in eq_obj_rng_of_frac) numer_denom_facts0:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  assumes "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  shows "a = ((numer a) |\<^bsub>rel\<^esub> (denom a))"
        "(numer a) \<in> carrier R"
        "(denom a) \<in> S"
        "numer a = \<zero> \<Longrightarrow> a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
        "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac(denom a)) = rng_to_rng_of_frac (numer a)"
        "(rng_to_rng_of_frac(denom a)) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> a = rng_to_rng_of_frac (numer a)"
proof-  
  have 0: "carrier rel \<noteq> {}" 
     by (metis (no_types, lifting) SigmaI empty_iff one_closed partial_object.select_convs(1) rel_def zero_closed) 
  have 1: "(numer a, denom a) \<in> a" 
  proof-    
   have "\<exists> r s. (r \<in> carrier R \<and> s \<in> S \<and> (a = (r |\<^bsub>rel\<^esub> s)))" 
     using rel_def assms(3) assms(1) set_eq_class_of_rng_of_frac_def rec_rng_of_frac_def  
     by (smt mem_Collect_eq mem_Sigma_iff partial_object.select_convs(1))     
   then obtain r s where "r \<in> carrier R \<and> s \<in> S \<and> (a = (r |\<^bsub>rel\<^esub> s))" 
     by blast
   hence "a = class_of\<^bsub>rel\<^esub> (r, s)" 
     by (simp add: class_of_to_rel)
   hence "(r,s) \<in> a" using  eq_class_of_def rel_def  
     using \<open>r \<in> carrier R \<and> s \<in> S \<and> a = (r |\<^bsub>rel\<^esub> s)\<close> equiv_obj_rng_of_frac equivalence.refl by fastforce
   hence "(\<exists> x. x \<in> a)"
     by blast 
   hence "(SOME x. x \<in> a) \<in> a" 
      by (meson some_eq_ex) 
   hence "(\<exists> x. x \<in> a \<and> (snd x = denom a))" 
      using denom_def assms  by metis 
   hence "\<exists>x. x \<in> a \<and> (snd x = denom a) \<and> (fst x = numer a)" 
     using numer_def assms  by (metis (mono_tags, lifting) exE_some) 
   thus ?thesis
    by simp 
  qed
  have "a \<in> {r |\<^bsub>rel\<^esub> s |r s. (r, s) \<in> carrier rel}" 
    using assms(3) rec_rng_of_frac_def set_eq_class_of_rng_of_frac_def by auto 
  hence "\<exists> x y. a = (x |\<^bsub>rel\<^esub> y) \<and> (x,y) \<in> carrier rel"    
    using  rec_rng_of_frac_def  eq_class_of_rng_of_frac_def set_eq_class_of_rng_of_frac_def
    by blast 
  then obtain x y where "a = (x |\<^bsub>rel\<^esub> y)" and P0:"(x,y) \<in> carrier rel" 
    by blast 
  hence P1: "(numer a, denom a) \<in>(x |\<^bsub>rel\<^esub> y)" 
    using "1" by blast 
  thus 2:"a = ((numer a) |\<^bsub>rel\<^esub> (denom a))"
  proof-
     have P2:"(numer a, denom a) \<in> carrier rel \<and> (x, y).=\<^bsub>rel\<^esub> (numer a, denom a)  "
      using eq_class_of_rng_of_frac_def P1 by fastforce 
    hence "(x, y).=\<^bsub>rel\<^esub> (numer a, denom a)" 
      by blast 
    hence "(numer a, denom a).=\<^bsub>rel\<^esub>(x, y)"
      using equiv_obj_rng_of_frac by (simp add: equivalence.sym P0 P2) 
    thus ?thesis 
      by (metis P0 P2 \<open>a = (x |\<^bsub>rel\<^esub> y)\<close> class_of_to_rel elem_eq_class equiv_obj_rng_of_frac) 
    qed
  have 3:"(numer a, denom a) \<in> carrier rel" 
    using P1 by (simp add: eq_class_of_rng_of_frac_def) 
  thus 4: "numer a \<in> carrier R" 
    by (simp add: rel_def) 
  show 5: "denom a \<in> S" 
    using "3" rel_def by auto 
  show "numer a = \<zero> \<Longrightarrow> a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
  proof-
    assume "numer a = \<zero>"
    hence "a = (\<zero> |\<^bsub>rel\<^esub> (denom a))" 
      using "2" by auto 
    thus ?thesis 
      using "5" class_of_zero_rng_of_frac by auto 
  qed
  show "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = rng_to_rng_of_frac (numer a)"
  proof-
    have S: "(denom a, \<one>) \<in>carrier rel" 
      using "5" rel_def subset by auto 
    hence "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = (((numer a) \<otimes> (denom a)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> \<one>)) "
      using 2 3 mult_rng_of_frac_fundamental_lemma rng_to_rng_of_frac_def 
      rec_monoid_rng_of_frac_def rec_rng_of_frac_def by fastforce       
    hence "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = (((denom a)\<otimes> (numer a)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> \<one>))"
      using "4" "5" m_comm subset by auto 
    hence "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (denom a) = ((denom a) |\<^bsub>rel\<^esub> (denom a)) \<otimes>\<^bsub>rec_rng_of_frac\<^esub>( (numer a) |\<^bsub>rel\<^esub> \<one>)"
      using mult_rng_of_frac_fundamental_lemma  "4" "5" S 
        rec_monoid_rng_of_frac_def rec_rng_of_frac_def rel_def by auto
    thus ?thesis 
      using "4" "5" \<open>a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac 
      (denom a) = (denom a \<otimes> numer a |\<^bsub>rel\<^esub> denom a \<otimes> \<one>)\<close> rel_def 
        rng_to_rng_of_frac_def simp_in_frac by auto
  qed
  thus "(rng_to_rng_of_frac(denom a)) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> a = rng_to_rng_of_frac (numer a)"
    by (smt "5" assms(3) cring.cring_simprules(14) crng_rng_of_frac ring_hom_closed rng_to_rng_of_frac_is_ring_hom subset subsetD)    
qed

lemma(in eq_obj_rng_of_frac) frac_zero:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "(a |\<^bsub>rel\<^esub> b) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  shows "a = \<zero>"
proof-
  have 0: "(a |\<^bsub>rel\<^esub> b) = (\<zero> |\<^bsub>rel\<^esub> \<one>)" 
    by (simp add: assms(5) class_of_zero_rng_of_frac) 
  have 1: "(a,b) \<in> carrier rel" 
    by (simp add: assms(3) assms(4) rel_def) 
  have 2: "(\<zero>, \<one>) \<in> carrier rel" 
    by (simp add: rel_def) 
  have 3: "(b, \<one>) \<in> carrier rel" 
    using assms(4) rel_def subset by auto 
  have "(a,b) .=\<^bsub>rel\<^esub> (\<zero>, \<one>)" 
    by (metis (no_types, lifting) "0" "1" "2" eq_class_to_rel partial_object.select_convs(1) rel_def) 
  have "(a |\<^bsub>rel\<^esub> b) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (b |\<^bsub>rel\<^esub>\<one>) = (\<zero> |\<^bsub>rel\<^esub> b)" 
    by (metis (no_types, opaque_lifting) assms(4) assms(5) 
       basic_trans_rules(31) class_of_zero_rng_of_frac cring.axioms(1) 
       crng_rng_of_frac ring.ring_simprules(24) ring_hom_closed 
       rng_to_rng_of_frac_def rng_to_rng_of_frac_is_ring_hom subset) 
  hence 4: "((a \<otimes> b) |\<^bsub>rel\<^esub> b)  = (\<zero> |\<^bsub>rel\<^esub> b)" 
    using "1" "3" assms(4) mult_rng_of_frac_fundamental_lemma
      rec_monoid_rng_of_frac_def rec_rng_of_frac_def subset by auto 
  have S: "((a \<otimes> b) , b) \<in> carrier rel" 
      using assms(3) assms(4) rel_def subset by auto 
  have T: "(\<zero>, b) \<in>carrier rel" 
      by (simp add: assms(4) rel_def) 
  hence " ((a \<otimes> b) , b).=\<^bsub>rel\<^esub> (\<zero> , b)"
    using 4 S eq_class_to_rel rel_def by auto   
  hence "eq rel ((a \<otimes> b) , b) (\<zero> , b)" 
    by blast 
  hence "\<exists>t\<in>S. t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>"
    using  rel_def by auto 
  then obtain t where "t \<in> S" and "t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>" 
    by blast 
  have "t \<noteq>\<zero>" 
    using \<open>t \<in> S\<close> assms(2) by blast 
  hence "(b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>" 
    by (meson \<open>t \<in> S\<close> \<open>t \<otimes> (b \<otimes> (a \<otimes> b) \<ominus> b \<otimes> \<zero>) = \<zero>\<close> assms(1) assms(3) 
        assms(4) domain.integral_iff minus_closed semiring_simprules(3)
        set_mp subset zero_closed)
  hence "b \<otimes> (a \<otimes> b) = \<zero>" 
    using "3" S rel_def abelian_group.minus_to_eq is_abelian_group by fastforce 
  thus "a = \<zero>" 
    by (metis (no_types, lifting) assms(1) assms(2) 
        assms(3) assms(4) domain.integral_iff 
        semiring_simprules(3) subset subsetCE) 
qed

text\<open>When S does not contain 0, and R is a domain, the localization is a domain.\<close>

lemma(in eq_obj_rng_of_frac) rec_rng_of_frac_is_domain:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  shows "domain rec_rng_of_frac"
proof(rule domainI)
  show "cring rec_rng_of_frac" 
   by (simp add: crng_rng_of_frac) 
  show "\<one>\<^bsub>rec_rng_of_frac\<^esub> \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
 proof-
    have  " \<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>" 
      by (simp add: assms domain.one_not_zero) 
    hence 0: " \<one>\<^bsub>R\<^esub> \<notin> (a_kernel  R  rec_rng_of_frac rng_to_rng_of_frac)"  
      using assms(1) rng_to_rng_of_frac_without_zero_div_is_inj 
      by (simp add: assms(2) domain_axioms_def domain_def) 
    hence "rng_to_rng_of_frac \<one> \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
      by (simp add: a_kernel_def') 
    thus ?thesis 
      using ring_hom_one rng_to_rng_of_frac_is_ring_hom by blast 
  qed 
  show "\<And>a b. a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<Longrightarrow>
           a \<in> carrier rec_rng_of_frac \<Longrightarrow>
           b \<in> carrier rec_rng_of_frac \<Longrightarrow> 
           a = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<or> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  proof-
    fix a b
    assume A1: "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    assume A2: " a \<in> carrier rec_rng_of_frac"
    assume A3: "b \<in> carrier rec_rng_of_frac"
    show "a = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<or> b = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    proof(rule disjCI)
      assume "b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
      have "\<not> a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub> "
      proof
        assume "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
        have B1: "numer a \<noteq> \<zero>" 
          using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(4) by blast 
        have B2: "numer b \<noteq> \<zero>" 
          using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(4) by blast 
        have B3: "denom a \<noteq>\<zero>" 
          using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2)
            eq_obj_rng_of_frac.numer_denom_facts0(1) eq_obj_rng_of_frac_axioms 
            using numer_denom_facts0(3) by force 
        have B4: "denom b \<noteq>\<zero>" 
          using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
            eq_obj_rng_of_frac_axioms by (metis (no_types, lifting) numer_denom_facts0(3)) 
        have "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> b = (((numer a) \<otimes> (numer b)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> (denom b)))"
        proof-
          have S0: "a = (numer a |\<^bsub>rel\<^esub> denom a)"
            by (simp add: A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(1)) 
          have S1: "b= (numer b |\<^bsub>rel\<^esub> denom b)" 
            by (simp add: A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) numer_denom_facts0(1))    
          have S2: "(numer a, denom a) \<in> carrier rel" 
            using A2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
              eq_obj_rng_of_frac.numer_denom_facts0(2) eq_obj_rng_of_frac.numer_denom_facts0(3)
              eq_obj_rng_of_frac_axioms rel_def by fastforce 
          have S3: "(numer b, denom b) \<in> carrier rel" 
            using A3 \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2)
              eq_obj_rng_of_frac.numer_denom_facts0(2) eq_obj_rng_of_frac_axioms
              numer_denom_facts0(3) rel_def by auto 
          show ?thesis using S0 S1 S2 S3 mult_rng_of_frac_fundamental_lemma 
            using rec_monoid_rng_of_frac_def rec_rng_of_frac_def by force 
        qed 
        hence "(((numer a) \<otimes> (numer b)) |\<^bsub>rel\<^esub> ((denom a) \<otimes> (denom b))) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
          using A1 by blast 
        hence "(numer a) \<otimes> (numer b) = \<zero>" 
          by (meson A2 A3 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close>
              assms(1) assms(2) eq_obj_rng_of_frac.numer_denom_facts0(2) 
              eq_obj_rng_of_frac.numer_denom_facts0(3) eq_obj_rng_of_frac_axioms
              frac_zero m_closed semiring_simprules(3))
        thus False 
          by (meson A2 A3 B1 B2 \<open>a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> 
              \<open>b \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub>\<close> assms(1) assms(2) 
              domain.integral_iff eq_obj_rng_of_frac.numer_denom_facts0(2) 
              eq_obj_rng_of_frac_axioms)
      qed
      thus "a = \<zero>\<^bsub>rec_rng_of_frac\<^esub>" 
        by auto 
    qed
  qed
qed

lemma(in eq_obj_rng_of_frac) numer_denom_facts:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  shows "a = (numer a |\<^bsub>rel\<^esub> denom a)"
        "(numer a) \<in> carrier R"
        "(denom a) \<in> S"
        "a \<noteq> \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<Longrightarrow> (numer a) \<noteq>\<zero>"
        "a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (rng_to_rng_of_frac(denom a)) = rng_to_rng_of_frac (numer a)"
        "(rng_to_rng_of_frac(denom a)) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> a = rng_to_rng_of_frac (numer a)"
  using assms(1) assms(2) assms(3) class_of_zero_rng_of_frac denom_def numer_def numer_denom_facts0(1) apply force
    using assms(1) assms(2) assms(3) numer_def numer_denom_facts0(2) apply force
      using assms(1) assms(2) assms(3) denom_def numer_denom_facts0(3) apply force
        using assms(1) assms(2) assms(3) numer_denom_facts0(4) apply blast
          apply (metis (no_types, lifting) assms(1) assms(2) assms(3) class_of_zero_rng_of_frac 
                denom_def monoid.r_one monoid.simps(2) numer_def numer_denom_facts0(5) one_closed 
                rec_rng_of_frac_def ringE(2) rng_rng_of_frac rng_to_rng_of_frac_def)
            by (metis (no_types, lifting) assms(1) assms(2) assms(3) class_of_zero_rng_of_frac 
                cring.cring_simprules(12) crng_rng_of_frac denom_def monoid.simps(2) numer_def
                numer_denom_facts0(6) one_closed rec_rng_of_frac_def rng_to_rng_of_frac_def)
  
lemma(in eq_obj_rng_of_frac) numer_denom_closed:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac"
  shows "(numer a, denom a) \<in> carrier rel"
  by (simp add: assms(1) assms(2) assms(3) numer_denom_facts(2) numer_denom_facts(3) rel_def) 

text\<open>Fraction function which suppresses the "rel" argument.\<close>

definition(in eq_obj_rng_of_frac) fraction where
"fraction x y = (x |\<^bsub>rel\<^esub> y)"

lemma(in eq_obj_rng_of_frac) a_is_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier rec_rng_of_frac" 
  shows "a = fraction (numer a) (denom a)"
  by (simp add: assms(1) assms(2) assms(3) fraction_def numer_denom_facts(1))  

lemma(in eq_obj_rng_of_frac) add_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "c \<in> carrier R"
  assumes "d \<in> S"
  shows "(fraction a b) \<oplus>\<^bsub>rec_rng_of_frac\<^esub> (fraction c d) = (fraction ((a \<otimes> d) \<oplus> (b \<otimes> c)) (b \<otimes> d))"  
proof-
  have 0:"(a,b) \<in> carrier rel"
    by (simp add: assms(3) assms(4) rel_def) 
  have 1:"(c,d) \<in> carrier rel" 
    by (simp add: assms(5) assms(6) rel_def) 
  show ?thesis
    using 0 1 add_rng_of_frac_fundamental_lemma assms numer_denom_facts fraction_def 
          domain_def m_comm subset 
    by auto      
qed

lemma(in eq_obj_rng_of_frac) mult_fraction:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  assumes "c \<in> carrier R"
  assumes "d \<in> S"
  shows "(fraction a b) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (fraction c d) = (fraction (a \<otimes> c) (b \<otimes> d))"
proof-
  have 0:"(a,b) \<in> carrier rel"
    by (simp add: assms(3) assms(4) rel_def) 
  have 1:"(c,d) \<in> carrier rel" 
    by (simp add: assms(5) assms(6) rel_def) 
  show ?thesis using 0 1 mult_rng_of_frac_fundamental_lemma 
    by (simp add: fraction_def rec_monoid_rng_of_frac_def rec_rng_of_frac_def)
qed

lemma(in eq_obj_rng_of_frac) fraction_zero:
"\<zero>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<zero> \<one> " 
  by (simp add: class_of_zero_rng_of_frac fraction_def) 

lemma(in eq_obj_rng_of_frac) fraction_zero':
  assumes "a \<in> S"
  assumes "\<zero> \<notin> S"
  shows "\<zero>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<zero> a" 
  by (simp add: assms(1) class_of_zero_rng_of_frac fraction_def) 

lemma(in eq_obj_rng_of_frac) fraction_one:
"\<one>\<^bsub>rec_rng_of_frac\<^esub> = fraction \<one> \<one>"
  by (simp add: fraction_def rec_rng_of_frac_def) 

lemma(in eq_obj_rng_of_frac) fraction_one':
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> S"
  shows "fraction a a = \<one>\<^bsub>rec_rng_of_frac\<^esub>"  
  using assms fraction_def fraction_one one_closed simp_in_frac subset 
  by (smt mem_Sigma_iff partial_object.select_convs(1) r_one rel_def subsetD)
  
lemma(in eq_obj_rng_of_frac) fraction_closed:
  assumes "domain R"
  assumes "\<zero> \<notin> S"
  assumes "a \<in> carrier R"
  assumes "b \<in> S"
  shows "fraction a b \<in> carrier rec_rng_of_frac" 
proof-
  have "(a,b) \<in> carrier rel" 
    by (simp add: assms(3) assms(4) rel_def) 
  hence "(a |\<^bsub>rel\<^esub> b) \<in> set_class_of\<^bsub>rel\<^esub>"  
    using  set_eq_class_of_rng_of_frac_def  
    by blast
  thus ?thesis using fraction_def 
    by (simp add: rec_rng_of_frac_def) 
qed

subsection\<open>Defining the Field of Fractions\<close>

definition Frac where
"Frac R  = eq_obj_rng_of_frac.rec_rng_of_frac R (nonzero R)"

lemma(in domain_frac) fraction_field_is_domain:
"domain (Frac R)"
  using domain_axioms eq_obj_rng_of_frac.rec_rng_of_frac_is_domain 
    eq_obj_rng_of_frac_nonzero Frac_def 
  by (metis nonzero_memE(2))

subsubsection\<open>Numerator and Denominator Choice Functions for \texttt{domain\_frac}\<close>
definition numerator where
"numerator R = eq_obj_rng_of_frac.numer R (nonzero R)"

abbreviation(in domain_frac)(input) numer where
"numer \<equiv> numerator R"

definition denominator where
"denominator R = eq_obj_rng_of_frac.denom  R (nonzero R)"

abbreviation(in domain_frac)(input) denom where
"denom \<equiv> denominator R"

definition fraction where
"fraction R = eq_obj_rng_of_frac.fraction  R (nonzero R)"

abbreviation(in domain_frac)(input) frac where
"frac \<equiv> fraction R"

subsubsection\<open>The inclusion of R into its fraction field\<close>

definition Frac_inc where
"Frac_inc R =  eq_obj_rng_of_frac.rng_to_rng_of_frac R (nonzero R)"

abbreviation(in domain_frac)(input) inc ("\<iota>") where
"inc \<equiv>  Frac_inc R"

lemma(in domain_frac) inc_equation:
  assumes "a \<in> carrier R"
  shows "\<iota> a = frac a \<one>"
  unfolding  Frac_inc_def fraction_def   
  using assms 
  by (simp add: eq_obj_rng_of_frac.fraction_def eq_obj_rng_of_frac.rng_to_rng_of_frac_def eq_obj_rng_of_frac_nonzero)

lemma(in domain_frac) inc_is_hom:
"inc \<in> ring_hom R (Frac R)"
  by (simp add: eq_obj_rng_of_frac.rng_to_rng_of_frac_is_ring_hom Frac_def 
      eq_obj_rng_of_frac_nonzero Frac_inc_def) 

lemma(in domain_frac) inc_is_hom1:
"ring_hom_ring R (Frac R) inc"
  apply(rule ring_hom_ringI2)
  using cring_def domain.axioms(1) fraction_field_is_domain
  by(auto simp:inc_is_hom local.ring_axioms) 

text\<open>Inclusion map is injective:\<close>

lemma(in domain_frac) inc_inj0:
"a_kernel R (Frac R) inc = {\<zero>}"
proof-
  have 0: "\<zero> \<notin> nonzero R" 
    by (simp add: nonzero_def) 
  have 1: "eq_obj_rng_of_frac R (nonzero R)" 
    by (simp add: eq_obj_rng_of_frac_nonzero) 
  have 2: "\<forall> a\<in> carrier R. \<forall> b\<in>carrier R. a \<otimes> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>" 
    using local.integral by blast 
  show ?thesis using 0 1 2  
    by (simp add: eq_obj_rng_of_frac.rng_to_rng_of_frac_without_zero_div_is_inj
        Frac_def Frac_inc_def) 
qed

lemma(in domain_frac) inc_inj1:
  assumes "a \<in> carrier R"
  assumes "inc a = \<zero>\<^bsub>Frac R\<^esub>"
  shows "a = \<zero>"
proof-
  have "a \<in> a_kernel R (Frac R) inc" using  a_kernel_def' assms(2)  
    by (simp add: a_kernel_def' assms(1)) 
  thus ?thesis
    using inc_inj0  by blast 
qed

lemma(in domain_frac) inc_inj2:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "inc a = inc b"
  shows "a = b"
proof-
  have "inc (a \<ominus> b) = (inc a) \<oplus>\<^bsub>Frac R\<^esub> (inc (\<ominus> b))" 
    using inc_is_hom by (simp add: ring_hom_add assms(1) assms(2) minus_eq) 
  hence "inc (a \<ominus> b) = \<zero>\<^bsub>Frac R\<^esub>" using assms inc_is_hom 
    by (smt Frac_def add.inv_closed eq_obj_rng_of_frac.rng_rng_of_frac
        eq_obj_rng_of_frac_nonzero local.ring_axioms r_neg ring_hom_add ring_hom_zero) 
  thus ?thesis 
    by (meson abelian_group.minus_to_eq assms(1) assms(2) domain_frac.inc_inj1 domain_frac_axioms is_abelian_group minus_closed)   
qed

text\<open>Image of inclusion map is a subring:\<close>

lemma(in domain_frac) inc_im_is_subring:
"subring (\<iota> ` (carrier R)) (Frac R)" 
  using carrier_is_subring inc_is_hom1 ring_hom_ring.img_is_subring by blast 

subsubsection\<open>Basic Properties of numer, denom, and frac\<close>

lemma(in domain_frac) numer_denom_facts:
  assumes "a \<in> carrier (Frac R)"
  shows "a = frac (numer a) (denom a)"
        "(numer a) \<in> carrier R"
        "(denom a) \<in> nonzero R"
        "a \<noteq>  \<zero>\<^bsub>Frac R\<^esub> \<Longrightarrow> numer a \<noteq> \<zero> "
        "a \<otimes>\<^bsub>Frac R\<^esub> (inc (denom a)) = inc (numer a)"
  unfolding fraction_def numerator_def denominator_def Frac_inc_def
  apply (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.a_is_fraction eq_obj_rng_of_frac_nonzero not_nonzero_memI)
     apply (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts(2) eq_obj_rng_of_frac_nonzero nonzero_memE(2))
      apply (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts(3) eq_obj_rng_of_frac_nonzero not_nonzero_memI)
        apply (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts0(4) eq_obj_rng_of_frac_nonzero not_nonzero_memI)
          by (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.numer_denom_facts(5) eq_obj_rng_of_frac_nonzero nonzero_memE(2))
 
lemma(in domain_frac) frac_add:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(frac a b) \<oplus>\<^bsub>Frac R\<^esub> (frac c d) = (frac ((a \<otimes> d) \<oplus> (b \<otimes> c)) (b \<otimes> d))"
  using eq_obj_rng_of_frac.add_fraction[of R "nonzero R" a b c d] 
        eq_obj_rng_of_frac_nonzero assms zero_not_in_nonzero[of R]
  by (simp add: Frac_def domain_axioms fraction_def)
  
lemma(in domain_frac) frac_mult:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(frac a b) \<otimes>\<^bsub>Frac R\<^esub> (frac c d) = (frac (a \<otimes> c) (b \<otimes> d))"
  by (simp add: Frac_def assms(1) assms(2) assms(3) assms(4) domain_axioms 
      eq_obj_rng_of_frac.mult_fraction eq_obj_rng_of_frac_nonzero fraction_def not_nonzero_memI)

lemma(in domain_frac) frac_one:
  assumes "a \<in> nonzero R"
  shows "frac a a = \<one>\<^bsub>Frac R\<^esub>"
  by (metis Frac_def assms domain_axioms eq_obj_rng_of_frac.fraction_one' eq_obj_rng_of_frac_nonzero fraction_def nonzero_memE(2))

lemma(in domain_frac) frac_closed:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  shows "frac a b \<in> carrier (Frac R)"
  by (metis Frac_def assms(1) assms(2) domain_axioms eq_obj_rng_of_frac.fraction_closed eq_obj_rng_of_frac_nonzero fraction_def nonzero_memE(2))

lemma(in domain_frac) nonzero_fraction:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "frac a b \<noteq> \<zero>\<^bsub>Frac R\<^esub>"
proof
  assume "frac a b = \<zero>\<^bsub>Frac R\<^esub>"
  hence "(frac a b) \<otimes>\<^bsub>Frac R\<^esub> (frac b a) = \<zero>\<^bsub>Frac R\<^esub> \<otimes>\<^bsub>Frac R\<^esub> (frac b a)"
    by simp 
  hence "(frac a b) \<otimes>\<^bsub>Frac R\<^esub> (frac b a) = \<zero>\<^bsub>Frac R\<^esub>"
    by (metis Localization.submonoid.subset assms(1) assms(2) cring.cring_simprules(26) 
      domain.axioms(1) frac_closed fraction_field_is_domain nonzero_is_submonoid subsetCE) 
  hence "frac (a \<otimes>b)  (b \<otimes> a)  = \<zero>\<^bsub>Frac R\<^esub>"
    by (metis (no_types, lifting) Localization.submonoid.subset 
        assms(1) assms(2) frac_mult nonzero_is_submonoid subsetCE) 
  hence "frac (a \<otimes>b)  (a \<otimes> b)  = \<zero>\<^bsub>Frac R\<^esub>"
    by (metis (no_types, lifting) Localization.submonoid.subset assms(1) assms(2) m_comm nonzero_is_submonoid subsetCE) 
  hence "\<one>\<^bsub>Frac R\<^esub> = \<zero>\<^bsub>Frac R\<^esub>" 
    using Localization.submonoid.m_closed assms(1) assms(2) frac_one nonzero_is_submonoid by force 
  thus False 
    using domain.one_not_zero fraction_field_is_domain by blast 
qed

lemma(in comm_monoid) UnitsI:
  assumes "a \<in> carrier G"
  assumes "b \<in> carrier G"
  assumes "a \<otimes> b = \<one>"
  shows "a \<in> Units G" "b \<in> Units G" 
  unfolding Units_def using comm_monoid_axioms_def assms m_comm[of a b] 
  by auto 

lemma(in comm_monoid) is_invI:
  assumes "a \<in> carrier G"
  assumes "b \<in> carrier G"
  assumes "a \<otimes> b = \<one>"
  shows "inv\<^bsub>G\<^esub> b = a" "inv\<^bsub>G\<^esub> a = b"
  using assms inv_char m_comm 
  by auto

lemma(in ring) ring_in_Units_imp_not_zero:
  assumes "\<one> \<noteq> \<zero>"
  assumes "a \<in> Units R"
  shows "a \<noteq> \<zero>"
  using assms monoid.Units_l_cancel
  by (metis l_null  monoid_axioms one_closed zero_closed)

lemma(in domain_frac) in_Units_imp_not_zero:
  assumes "a \<in> Units R"
  shows "a \<noteq> \<zero>"
  using assms ring_in_Units_imp_not_zero domain_axioms 
  by simp
  
lemma(in domain_frac) units_of_fraction_field0:
  assumes "a \<in> carrier (Frac R)"
  assumes "a \<noteq> \<zero>\<^bsub>Frac R\<^esub>"
  shows "inv\<^bsub>Frac R\<^esub> a = frac (denom a) (numer a)"
        "a\<otimes>\<^bsub>Frac R\<^esub> (inv\<^bsub>Frac R\<^esub> a)  = \<one>\<^bsub>Frac R\<^esub>"
        "(inv\<^bsub>Frac R\<^esub> a)\<otimes>\<^bsub>Frac R\<^esub>a   = \<one>\<^bsub>Frac R\<^esub>"
proof-
  have 0: "a \<otimes>\<^bsub>Frac R\<^esub> (frac (denom a) (numer a)) =
    frac ((numer a) \<otimes> (denom a)) ((numer a) \<otimes> (denom a))"     
  proof -
    have "denom a \<in> nonzero R"
      by (simp add: assms(1) numer_denom_facts(3))   
    hence "frac (numer a) (denom a) \<otimes>\<^bsub>Frac R\<^esub> frac (denom a) (numer a)
      = frac (numer a \<otimes> denom a) (denom a \<otimes> numer a)"
      by (simp add: assms(1) assms(2) domain_frac.numer_denom_facts(2) domain_frac_axioms frac_mult nonzero_closed nonzero_memI numer_denom_facts(4))       
    thus ?thesis
      using assms(1) numer_denom_facts(5)  domain_frac.numer_denom_facts(2) 
        domain_axioms m_comm nonzero_closed numer_denom_facts(1) 
      by (simp add: domain_frac.numer_denom_facts(2) \<open>denominator R a \<in> nonzero R\<close> domain_frac_axioms)                             
  qed 
  have 1:"((numer a) \<otimes> (denom a)) \<in> nonzero R"
    by (metis assms(1) assms(2) domain_frac.numer_denom_facts(2) domain_frac_axioms 
        local.integral m_closed nonzero_closed nonzero_memI numer_denom_facts(3) numer_denom_facts(4))           
  have  2: "a \<otimes>\<^bsub>Frac R\<^esub> (frac (denom a) (numer a)) = \<one>\<^bsub>Frac R\<^esub>" 
    using 0 1 frac_one by blast
  have 3: "(frac (denom a) (numer a)) \<in> carrier (Frac R)" 
    by (simp add: assms(1) assms(2) frac_closed nonzero_closed nonzero_memI numer_denom_facts(2) numer_denom_facts(3) numer_denom_facts(4))            
  hence 4: "(frac (denom a) (numer a)) \<in> carrier (Frac R) \<and>
             a \<otimes>\<^bsub>Frac R\<^esub> (frac (denom a) (numer a))  = \<one>\<^bsub>Frac R\<^esub> \<and> 
           (frac (denom a) (numer a))  \<otimes>\<^bsub>Frac R\<^esub> a  = \<one>\<^bsub>Frac R\<^esub>"
    by (simp add: "2" assms(1) cring.cring_simprules(14) domain.axioms(1) fraction_field_is_domain)
  thus 5: "inv\<^bsub>Frac R\<^esub> a = frac (denom a) (numer a)"
    using m_inv_def 2 assms(1) comm_monoid.comm_inv_char cring_def
      domain_def fraction_field_is_domain by fastforce
  thus 6: "a\<otimes>\<^bsub>Frac R\<^esub> (inv\<^bsub>Frac R\<^esub> a)   = \<one>\<^bsub>Frac R\<^esub>" 
    by (simp add: "2") 
  thus "(inv\<^bsub>Frac R\<^esub> a)\<otimes>\<^bsub>Frac R\<^esub>a   = \<one>\<^bsub>Frac R\<^esub>"
    using assms 
    by (simp add: "4" "5")  
qed

lemma(in domain_frac) units_of_fraction_field:
"Units (Frac R) = carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>}"
proof
  show "Units (Frac R) \<subseteq> carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>}"
  proof fix x assume A: "x \<in> Units (Frac R)"
    have "x \<in> carrier (Frac R)" 
      using Units_def \<open>x \<in> Units (Frac R)\<close> by force 
    hence "x \<noteq> \<zero>\<^bsub>Frac R\<^esub>" 
      using fraction_field_is_domain 
      by (simp add: A domain_frac.in_Units_imp_not_zero domain_frac.intro)      
    thus "x \<in> carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>}" 
      by (simp add: \<open>x \<in> carrier (Frac R)\<close>) 
  qed
  show "carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>} \<subseteq> Units (Frac R)"
  proof fix x assume A: "x \<in> carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>}"
     show "x \<in> Units (Frac R)"
      using comm_monoid.UnitsI(1)[of "Frac R" x "inv\<^bsub>Frac R\<^esub> x"] 
      by (metis A Diff_iff cring.axioms(2) domain.axioms(1) domain_frac.numer_denom_facts(2)
          domain_frac.numer_denom_facts(3) domain_frac.units_of_fraction_field0(1)
          domain_frac.units_of_fraction_field0(2) domain_frac_axioms frac_closed 
          fraction_field_is_domain insert_iff nonzero_closed nonzero_memI numer_denom_facts(4))     
  qed
qed

subsection\<open>The Fraction Field as a Field\<close>

lemma(in domain_frac) fraction_field_is_field:
"field (Frac R)"
proof(rule Ring.field.intro)
  show "domain (Frac R)" by(auto simp: fraction_field_is_domain)
  show "field_axioms (Frac R)"
  proof
    show "Units (Frac R) = carrier (Frac R) - {\<zero>\<^bsub>Frac R\<^esub>}" 
      using units_of_fraction_field by blast 
  qed
qed

lemma(in domain_frac) frac_inv:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R" 
  shows "inv\<^bsub>Frac R\<^esub> (frac a b) = (frac b a)"   
  using cring_def[of "Frac R"] domain_def[of "Frac R"] fraction_field_is_domain 
        frac_closed[of a b] frac_closed[of b a] nonzero_closed[of a] 
        nonzero_closed[of b] assms comm_monoid.is_invI(2)[of "Frac R" "frac a b" "frac b a"] 
  by (metis frac_mult frac_one integral_iff m_comm nonzero_memE(2) nonzero_memI nonzero_mult_closed)

lemma(in domain_frac) frac_inv_id:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R" 
  assumes "c \<in> nonzero R"
  assumes "d \<in> nonzero R" 
  assumes "frac a b = frac c d"
  shows "frac b a = frac d c"
  using frac_inv assms  by metis  

lemma(in domain_frac) frac_uminus:
  assumes "a \<in> carrier  R"
  assumes "b \<in> nonzero R"
  shows "\<ominus>\<^bsub>Frac R\<^esub> (frac a b) = frac (\<ominus> a) b" 
proof-
  have "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = frac (((\<ominus> a)\<otimes>b) \<oplus> (a \<otimes>b)) (b\<otimes>b)"
    using frac_add  by (smt Localization.submonoid.subset add.inv_closed
        assms(1) assms(2) m_comm nonzero_is_submonoid subsetCE) 
  hence "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = frac (b \<otimes>((\<ominus> a) \<oplus> a)) (b\<otimes>b)" 
    by (metis (no_types, lifting) add.inv_closed  assms(1) assms(2)
        local.ring_axioms m_comm mem_Collect_eq nonzero_def ringE(4) )
  hence "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = (frac \<zero> (b \<otimes>b))"  
    using Localization.submonoid.subset assms(1) assms(2) l_neg nonzero_is_submonoid by fastforce 
  hence "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = (frac \<zero> \<one>) \<otimes>\<^bsub>Frac R\<^esub>  (frac \<zero> (b \<otimes>b))"
    using frac_mult    by (smt Localization.submonoid.m_closed Localization.submonoid.one_closed
        Localization.submonoid.subset assms(2) l_one nonzero_is_submonoid r_null subsetCE zero_closed) 
  hence "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = \<zero>\<^bsub>Frac R\<^esub> \<otimes>\<^bsub>Frac R\<^esub>  (frac \<zero> (b \<otimes>b))" 
    using Frac_def eq_obj_rng_of_frac.fraction_zero' eq_obj_rng_of_frac_nonzero 
    by (simp add: Frac_def eq_obj_rng_of_frac.fraction_zero fraction_def)   
  hence "frac (\<ominus> a) b \<oplus>\<^bsub>Frac R\<^esub> (frac a b) = \<zero>\<^bsub>Frac R\<^esub>"
    using fraction_field_is_field 
    by (simp add: Localization.submonoid.m_closed assms(2) cring.cring_simprules(26)
        domain.axioms(1) frac_closed fraction_field_is_domain nonzero_is_submonoid)
  thus 0: "\<ominus>\<^bsub>Frac R\<^esub> (frac a b) = frac (\<ominus> a) b" 
    by (metis add.inv_closed assms(1) assms(2) cring.sum_zero_eq_neg
        domain.axioms(1) frac_closed fraction_field_is_domain) 
qed    

lemma(in domain_frac) frac_eqI:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R" 
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R" 
  assumes "a \<otimes> d \<ominus> b \<otimes> c = \<zero>"
  shows "frac a b = frac c d"
proof-
 have "frac a b \<ominus>\<^bsub>Frac R\<^esub> frac c d = frac (a \<otimes> d \<ominus> b \<otimes> c) (b\<otimes>d)"
   by (simp add: a_minus_def assms(1) assms(2) assms(3) assms(4) frac_uminus local.frac_add nonzero_closed r_minus)
 hence "frac a b \<ominus>\<^bsub>Frac R\<^esub> frac c d = \<zero>\<^bsub>Frac R\<^esub>"
   by (metis Frac_def assms(2) assms(4) assms(5) eq_obj_rng_of_frac.fraction_zero' 
       eq_obj_rng_of_frac_nonzero fraction_def local.integral nonzero_memE(1) nonzero_memE(2) 
       nonzero_memI nonzero_mult_closed)  
  thus ?thesis 
    by (meson assms(1) assms(2) assms(3) assms(4) field.is_ring frac_closed fraction_field_is_field ring.r_right_minus_eq) 
qed

lemma(in domain_frac) frac_eqI':
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R" 
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R" 
  assumes "a \<otimes> d = b \<otimes> c"
  shows "frac a b = frac c d"
  using assms frac_eqI[of a b c d]
  by (simp add: nonzero_closed)
  
lemma(in domain_frac) frac_cancel_l:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (a \<otimes> c) (a \<otimes> b) = frac c b" 
proof-
  have 0: "frac (a \<otimes>c) (a \<otimes>b) =(frac b b) \<otimes>\<^bsub>Frac R\<^esub> (frac c b)" 
    by (metis (no_types, lifting) assms(1) assms(2) assms(3)
        frac_mult frac_one mem_Collect_eq nonzero_def)  
  have 1: "frac b b = \<one>\<^bsub>Frac R\<^esub>" 
    by (simp add: assms(2) frac_one) 
  show ?thesis using 0 1 
    using Frac_def assms(2) assms(3) eq_obj_rng_of_frac.rng_rng_of_frac 
      eq_obj_rng_of_frac_nonzero frac_closed ring.ring_simprules(12) 
    by (simp add: Frac_def eq_obj_rng_of_frac.rng_rng_of_frac ring.ring_simprules(12))
qed

lemma(in domain_frac) frac_cancel_r:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (c \<otimes> a) (b \<otimes> a) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE) 

lemma(in domain_frac) frac_cancel_lr:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (a \<otimes> c) (b \<otimes> a) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE) 

lemma(in domain_frac) frac_cancel_rl:
  assumes "a \<in>nonzero R"
  assumes "b \<in>nonzero R"
  assumes "c \<in>carrier R"
  shows "frac (c \<otimes> a) (a \<otimes> b) = frac c b"
  by (metis (no_types, lifting) Localization.submonoid.subset assms(1)
      assms(2) assms(3) frac_cancel_l m_comm nonzero_is_submonoid subsetCE)

lemma(in domain_frac) i_mult:
  assumes "a \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  shows "(\<iota> a) \<otimes>\<^bsub>Frac R\<^esub> (frac c d) = frac (a \<otimes> c) d"
proof-
  have "(\<iota> a) \<otimes>\<^bsub>Frac R\<^esub> (frac c d) = (frac a \<one>) \<otimes>\<^bsub>Frac R\<^esub> (frac c d)" 
    by (simp add: assms(1) inc_equation)
  thus ?thesis 
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) cring_simprules(12) 
        cring_simprules(6) frac_mult local.one_not_zero mem_Collect_eq nonzero_def)
qed

lemma(in domain_frac) frac_eqE:
  assumes "a \<in> carrier R"
  assumes "b \<in> nonzero R"
  assumes "c \<in> carrier R"
  assumes "d \<in> nonzero R"
  assumes "frac a b = frac c d"
  shows "a \<otimes> d = b \<otimes> c"
proof-
  have "(\<iota> b) \<otimes>\<^bsub>Frac R\<^esub> (frac a b) = (\<iota> b) \<otimes>\<^bsub>Frac R\<^esub> (frac c d)" 
    by (simp add: assms(5))
  hence "(frac (a \<otimes> b)  b) = (frac (c \<otimes> b) d)" 
    using i_mult 
    by (metis (no_types, lifting) Localization.submonoid.subset assms(1) 
        assms(2) assms(3) assms(4) m_comm nonzero_is_submonoid subsetCE)
  hence "(frac a  \<one>) = (frac (c \<otimes> b) d)"
    by (smt assms(1) assms(2) frac_cancel_r l_one mem_Collect_eq nonzero_def one_closed zero_not_one)
  hence "(\<iota> d) \<otimes>\<^bsub>Frac R\<^esub>(frac a  \<one>) =(\<iota> d) \<otimes>\<^bsub>Frac R\<^esub> (frac (c \<otimes> b) d)"
    by auto
  hence "(frac (a \<otimes> d) \<one>) =(frac ((c \<otimes> b)\<otimes> d) d)"
    using i_mult    
    by (smt Localization.submonoid.m_closed Localization.submonoid.subset assms(1) assms(2) assms(3)
        assms(4) cring_simprules(27) cring_simprules(6) local.one_not_zero m_comm
        mem_Collect_eq nonzero_def nonzero_is_submonoid)
  hence "(frac (a \<otimes> d) \<one>) =(frac (c \<otimes> b) \<one>)" 
    by (smt Localization.submonoid.subset assms(2) assms(3) assms(4) cring_simprules(5)
        cring_simprules(6) frac_one i_mult inc_equation inc_is_hom nonzero_is_submonoid
        r_one ring_hom_mult ring_hom_one subsetCE)
  thus ?thesis using assms
    unfolding fraction_def 
    by (simp add: fraction_def inc_equation inc_inj2 m_comm nonzero_closed)      
qed

lemma(in domain_frac) frac_add_common_denom:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c \<in> nonzero R"
  shows "(frac a c) \<oplus>\<^bsub>Frac R\<^esub> (frac b c) = frac (a \<oplus> b) c"
proof-
  have "(frac a c) \<oplus>\<^bsub>Frac R\<^esub> (frac b c) = frac ((a \<otimes> c) \<oplus> (b \<otimes> c)) (c \<otimes> c)"
    using assms(1) assms(2) assms(3) domain_frac.frac_add domain_axioms frac_eqE local.frac_add 
    by auto    
  hence "(frac a c) \<oplus>\<^bsub>Frac R\<^esub> (frac b c) = frac ((a \<oplus> b) \<otimes> c) (c \<otimes> c)"
    by (metis Localization.submonoid.subset assms(1) assms(2) assms(3) l_distr nonzero_is_submonoid subsetCE)
  thus ?thesis 
    by (simp add: assms(1) assms(2) assms(3) frac_cancel_r)
qed

lemma(in domain_frac) common_denominator:
  assumes "x \<in> carrier (Frac R)"
  assumes "y \<in> carrier (Frac R)"
  obtains a b c where
    "a \<in> carrier R"
    "b \<in> carrier R" 
    "c \<in> nonzero R"
    "x = frac a c"
    "y = frac b c"
proof-
  obtain x1 x2 where X1: "x1 \<in> carrier R" and X2: "x2 \<in> nonzero R" and Fx: "x = frac x1 x2"
    by (meson assms(1) numer_denom_facts(1) numer_denom_facts(2) numer_denom_facts(3))   
  obtain y1 y2 where Y1: "y1 \<in> carrier R" and Y2: "y2 \<in> nonzero R" and Fy: "y = frac y1 y2"
    by (meson assms(2) numer_denom_facts(1) numer_denom_facts(2) numer_denom_facts(3))  
  let ?a = "x1 \<otimes> y2"
  let ?b = "y1 \<otimes> x2"
  let ?c = "x2 \<otimes> y2"
  have 0: "?a \<in> carrier R" 
    using X1 Y2  by (simp add: nonzero_def)
  have 1: "?b \<in> carrier R" using Y1 X2 
    by (simp add: nonzero_def)
  have 2: "?c \<in> nonzero R" using X2 Y2 
    by (simp add: Localization.submonoid.m_closed nonzero_is_submonoid)
  have 3: "x = frac ?a ?c" 
    using Fx X1 X2 Y2 frac_cancel_r by auto
  have 4: "y = frac ?b ?c" 
    using Fy X2 Y1 Y2 frac_cancel_rl by auto
  thus ?thesis using 0 1 2 3 4 
    using that by blast
qed

sublocale  domain_frac < F: field "Frac R"
  by (simp add: fraction_field_is_field)

text\<open>Inclusions of natural numbers into \texttt{(Frac R)}:\<close>

lemma(in domain_frac) nat_0:
"[(0::nat)]\<cdot>\<one> = \<zero>"
  by simp

lemma(in domain_frac) nat_suc:
"[Suc n]\<cdot>\<one> = \<one> \<oplus> [n]\<cdot>\<one>"
  using add.nat_pow_Suc2 by auto

lemma(in domain_frac) nat_inc_rep:
  fixes n::nat
  shows "[n]\<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = frac ([n]\<cdot>\<one>) \<one>"
proof(induction n)
  case 0
  have "[(0::nat)] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = \<zero>\<^bsub>Frac R\<^esub>"
    using fraction_field_is_domain 
    by (simp add: domain_frac.intro domain_frac.nat_0)
  thus ?case 
    by (simp add: Frac_def eq_obj_rng_of_frac.fraction_zero eq_obj_rng_of_frac_nonzero fraction_def)    
next
  case (Suc n)
  assume A:  "[n] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = frac ([n] \<cdot> \<one>) \<one>"
  have "[Suc n] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = \<one>\<^bsub>Frac R\<^esub> \<oplus>\<^bsub>Frac R\<^esub> [n] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub>" 
    using F.add.nat_pow_Suc2 by auto    
  hence "[Suc n] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = (frac \<one> \<one>) \<oplus>\<^bsub>Frac R\<^esub> (frac ([n] \<cdot> \<one>) \<one>)"
    by (simp add: Suc.IH frac_one nonzero_def)
  hence "[Suc n] \<cdot>\<^bsub>Frac R\<^esub> \<one>\<^bsub>Frac R\<^esub> = (frac (\<one>\<oplus>[n] \<cdot> \<one>) \<one>)"
    by (simp add: frac_add_common_denom nonzero_def)
  thus ?case 
    using nat_suc by auto
qed

lemma(in domain_frac) pow_0:
  assumes "a \<in> nonzero R"
  shows "a[^](0::nat) = \<one>"
  by simp

lemma(in domain_frac) pow_suc:
  assumes "a \<in> carrier R"
  shows "a[^](Suc n) = a \<otimes>(a[^]n)"
  using assms nat_pow_Suc2 by auto

lemma(in domain_frac) nat_inc_add:
"[((n::nat) + (m::nat))]\<cdot>\<one> = [n]\<cdot>\<one> \<oplus> [m]\<cdot>\<one>"
  using domain_def add_pow_def 
  by (simp add: add.nat_pow_mult)
  
lemma(in domain_frac) int_inc_add:
"[((n::int) + (m::int))]\<cdot>\<one> = [n]\<cdot>\<one> \<oplus> [m]\<cdot>\<one>"
  using domain_def add_pow_def 
  by (simp add: add.int_pow_mult)

lemma(in domain_frac) nat_inc_mult:
"[((n::nat) * (m::nat))]\<cdot>\<one> = [n]\<cdot>\<one> \<otimes> [m]\<cdot>\<one>"
  using domain_def add_pow_def 
  by (simp add: Groups.mult_ac(2) add.nat_pow_pow add_pow_ldistr)

lemma(in domain_frac) int_inc_mult:
"[((n::int) * (m::int))]\<cdot>\<one> = [n]\<cdot>\<one> \<otimes> [m]\<cdot>\<one>"
  using domain_def add_pow_def 
  by (simp add: Groups.mult_ac(2) add.int_pow_pow add_pow_ldistr_int)

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Facts About Ring Units\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in ring) Units_nonzero:
  assumes "u \<in> Units R"
  assumes "\<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
  shows "u \<in> nonzero R"
proof-
  have "u \<in>carrier R" 
    using Units_closed assms by auto
  have "u \<noteq>\<zero>" 
    using Units_r_inv_ex assms(1) assms(2) 
    by force 
  thus ?thesis 
    by (simp add: \<open>u \<in> carrier R\<close> nonzero_def)
qed

lemma(in ring) Units_inverse:
  assumes "u \<in> Units R"
  shows "inv u \<in> Units R"
  by (simp add: assms)

lemma(in cring) invI:  
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
  shows "y = inv \<^bsub>R\<^esub> x"
        "x = inv \<^bsub>R\<^esub> y"
  using assms(1) assms(2) assms(3) is_invI 
  by auto 

lemma(in cring) inv_cancelR:
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = x \<otimes>\<^bsub>R\<^esub> z"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
  apply (metis Units_closed assms(1) assms(3) assms(4) cring.cring_simprules(12) 
    is_cring m_assoc monoid.Units_inv_closed monoid.Units_l_inv monoid_axioms)
  by (metis Units_closed assms(1) assms(3) assms(4) m_assoc m_comm monoid.Units_inv_closed 
      monoid.Units_r_inv monoid.r_one monoid_axioms)
   
lemma(in cring) inv_cancelL:
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = z \<otimes>\<^bsub>R\<^esub> x"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
  apply (simp add: Units_closed assms(1) assms(3) assms(4) m_lcomm)
  by (simp add: Units_closed assms(1) assms(3) assms(4) m_assoc)

lemma(in domain_frac) nat_pow_nonzero:
  assumes "x \<in>nonzero R"
  shows "x[^](n::nat) \<in> nonzero R"
  unfolding nonzero_def 
  apply(induction n)
  using assms integral_iff nonzero_closed zero_not_in_nonzero by auto

lemma(in monoid) Units_int_pow_closed:
  assumes "x \<in> Units G"
  shows "x[^](n::int) \<in> Units G"
  by (metis Units_pow_closed assms int_pow_def2 monoid.Units_inv_Units monoid_axioms)

subsection\<open>Facts About Fraction Field Units\<close>

lemma(in domain_frac) frac_nonzero_Units:
"nonzero (Frac R) = Units (Frac R)"
  unfolding nonzero_def using F.field_Units 
  by blast 

lemma(in domain_frac) frac_nonzero_inv_Unit:
  assumes "b \<in> nonzero (Frac R)"
  shows "inv\<^bsub>Frac R\<^esub> b \<in> Units (Frac R)"
  using assms frac_nonzero_Units
  by simp

lemma(in domain_frac) frac_nonzero_inv_closed:
  assumes "b \<in> nonzero (Frac R)"
  shows "inv\<^bsub>Frac R\<^esub> b \<in> carrier (Frac R)"
  using  frac_nonzero_inv_Unit 
  by (simp add: Units_def assms)

lemma(in domain_frac) frac_nonzero_inv:
  assumes "b \<in> nonzero (Frac R)"
  shows "b \<otimes>\<^bsub>Frac R\<^esub> inv \<^bsub>Frac R\<^esub> b = \<one>\<^bsub>Frac R\<^esub>"
        "inv \<^bsub>Frac R\<^esub> b \<otimes>\<^bsub>Frac R\<^esub> b = \<one>\<^bsub>Frac R\<^esub>"
  using frac_nonzero_Units assms by auto  

lemma(in domain_frac) fract_cancel_right[simp]:
  assumes "a \<in> carrier (Frac R)"
  assumes "b \<in> nonzero (Frac R)"
  shows "b \<otimes>\<^bsub>Frac R\<^esub> (a \<otimes>\<^bsub>Frac R\<^esub> inv\<^bsub>Frac R\<^esub> b) = a"
  by (metis F.Units_inv_inv F.inv_cancelL(1) F.m_closed assms(1) assms(2) frac_nonzero_Units frac_nonzero_inv_Unit frac_nonzero_inv_closed)

lemma(in domain_frac) fract_cancel_left[simp]:
  assumes "a \<in> carrier (Frac R)"
  assumes "b \<in> nonzero (Frac R)"
  shows "(a \<otimes>\<^bsub>Frac R\<^esub> inv\<^bsub>Frac R\<^esub> b) \<otimes>\<^bsub>Frac R\<^esub> b = a"
  by (metis Diff_iff assms(1) assms(2) cring.cring_simprules(14) cring.cring_simprules(5) 
      domain.axioms(1) frac_nonzero_Units frac_nonzero_inv_closed fract_cancel_right 
      fraction_field_is_domain units_of_fraction_field)
  
lemma(in domain_frac) fract_mult_inv:
  assumes "b \<in> nonzero (Frac R)"
  assumes "d \<in> nonzero (Frac R)"
  shows "(inv\<^bsub>Frac R\<^esub> b) \<otimes>\<^bsub>Frac R\<^esub> (inv\<^bsub>Frac R\<^esub> d) = (inv\<^bsub>Frac R\<^esub> (b \<otimes>\<^bsub>Frac R\<^esub>d))"
  by (metis F.Units_inv_closed F.Units_m_closed F.inv_cancelR(2) F.nonzero_closed assms(1) assms(2) frac_nonzero_Units)

lemma(in domain_frac) fract_mult:
  assumes "a \<in> carrier (Frac R)"
  assumes "b \<in> nonzero (Frac R)"
  assumes "c \<in> carrier (Frac R)"
  assumes "d \<in> nonzero (Frac R)"
  shows  "(a \<otimes>\<^bsub>Frac R\<^esub> inv\<^bsub>Frac R\<^esub> b) \<otimes>\<^bsub>Frac R\<^esub> (c \<otimes>\<^bsub>Frac R\<^esub> inv\<^bsub>Frac R\<^esub> d) = ((a \<otimes>\<^bsub>Frac R\<^esub> c)\<otimes>\<^bsub>Frac R\<^esub> inv\<^bsub>Frac R\<^esub> (b \<otimes>\<^bsub>Frac R\<^esub>d))"
  using F.m_assoc F.m_lcomm assms(1) assms(2) assms(3) assms(4) frac_nonzero_Units fract_mult_inv by auto

lemma(in domain_frac) Frac_nat_pow_nonzero:
  assumes "x \<in> nonzero (Frac R)"
  shows "x[^]\<^bsub>Frac R\<^esub>(n::nat) \<in> nonzero (Frac R)"
  by (simp add: assms domain_frac.intro domain_frac.nat_pow_nonzero fraction_field_is_domain)
  
lemma(in domain_frac) Frac_nonzero_nat_pow:
  assumes "x \<in> carrier (Frac R)"
  assumes "n > 0"
  assumes "x[^]\<^bsub>Frac R\<^esub>(n::nat) \<in> nonzero (Frac R)"
  shows "x \<in> nonzero (Frac R)"
proof(rule ccontr)
  assume "x \<notin> nonzero (Frac R)"
  hence 0: "x = \<zero>\<^bsub>Frac R\<^esub>"
    by (simp add: assms(1) nonzero_def) 
  have "x[^]\<^bsub>Frac R\<^esub>(n::nat) = \<zero>\<^bsub>Frac R\<^esub>"
  proof-
    obtain k where "n = Suc k"
      using assms(2) lessE by blast
    hence 00: "x[^]\<^bsub>Frac R\<^esub>(n::nat) = x[^]\<^bsub>Frac R\<^esub>k \<otimes>\<^bsub>Frac R\<^esub> x"
      by simp
    have "x[^]\<^bsub>Frac R\<^esub>k \<in> carrier (Frac R)"
      using assms monoid.nat_pow_closed[of "Frac R" x k] 
      by (meson field.is_ring fraction_field_is_field ring_def)   
    thus ?thesis using 0 assms 
      using "00" cring.cring_simprules(27) domain.axioms(1) fraction_field_is_domain by fastforce      
  qed
  thus False 
    using "0" \<open>x \<notin> nonzero (Frac R)\<close> assms(3) by auto 
qed
  
lemma(in domain_frac) Frac_int_pow_nonzero:
  assumes "x \<in> nonzero (Frac R)"
  shows "x[^]\<^bsub>Frac R\<^esub>(n::int) \<in> nonzero (Frac R)"
  using assms field.is_ring frac_nonzero_Units fraction_field_is_field monoid.Units_pow_closed[of "Frac R" x]
  by (simp add: field.is_ring monoid.Units_int_pow_closed ring.is_monoid)

lemma(in domain_frac) Frac_nonzero_int_pow:
  assumes "x \<in> carrier (Frac R)"
  assumes "n > 0"
  assumes "x[^]\<^bsub>Frac R\<^esub>(n::int) \<in> nonzero (Frac R)"
  shows "x \<in> nonzero (Frac R)"
  by (metis (mono_tags, opaque_lifting) Frac_nonzero_nat_pow assms  int_pow_int pos_int_cases)

lemma(in domain_frac) numer_denom_frac[simp]:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "frac (numer (frac a b)) (denom (frac a b)) = frac a b"
  using assms(1) assms(2) domain_frac.numer_denom_facts(1) 
domain_axioms frac_closed nonzero_closed numer_denom_facts(1) by auto
  
lemma(in domain_frac) numer_denom_swap:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "a \<otimes> (denom (frac a b)) = b \<otimes> (numer (frac a b))"
  using numer_denom_frac[of a b] assms 
  by (simp add: frac_closed frac_eqE nonzero_closed numer_denom_facts(2) numer_denom_facts(3))
    
lemma(in domain_frac) numer_nonzero:
  assumes "a \<in> nonzero (Frac R)"
  shows "numer a \<in> nonzero R"
  using assms  numer_denom_facts(4)[of a] zero_not_in_nonzero[of R]
  by (simp add: frac_nonzero_Units nonzero_memI numer_denom_facts(2) units_of_fraction_field)

lemma(in domain_frac) fraction_zero[simp]:
  assumes "b \<in> nonzero R"
  shows "frac \<zero> b = \<zero>\<^bsub>Frac R\<^esub>"
  by (metis Frac_def assms eq_obj_rng_of_frac.fraction_zero' eq_obj_rng_of_frac_nonzero fraction_def nonzero_memE(2))

end
