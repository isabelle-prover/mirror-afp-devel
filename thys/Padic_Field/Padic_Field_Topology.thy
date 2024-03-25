theory Padic_Field_Topology
  imports Padic_Fields
begin

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Topology of $p$-adic Fields\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  In this section we develop some basic properties of the topology on the $p$-adics. Open and 
  closed sets are defined, convex subsets of the value group are characterized.
\<close>
type_synonym padic_univ_poly = "nat \<Rightarrow> padic_number"  

(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>$p$-adic Balls\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_fields
begin

definition c_ball :: "int \<Rightarrow> padic_number \<Rightarrow> padic_number set" ("B\<^bsub>_\<^esub>[_]") where
"c_ball n c = {x \<in> carrier Q\<^sub>p. val (x \<ominus> c) \<ge> n}"

lemma c_ballI: 
  assumes "x \<in> carrier Q\<^sub>p"
  assumes " val (x \<ominus> c) \<ge> n"
  shows "x \<in> c_ball n c"
  using assms c_ball_def 
  by blast

lemma c_ballE: 
  assumes "x \<in> c_ball n c"
  shows "x \<in> carrier Q\<^sub>p"
        " val (x \<ominus> c) \<ge> n"
  using assms c_ball_def apply blast
    using assms c_ball_def by blast

lemma c_ball_in_Qp: 
  "B\<^bsub>n\<^esub>[c] \<subseteq> carrier Q\<^sub>p"
  unfolding c_ball_def 
  by blast

definition  
q_ball :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> padic_number \<Rightarrow> padic_number set" where
"q_ball n k m c = {x \<in> carrier Q\<^sub>p. (ac n (x \<ominus> c) = k \<and> (ord (x \<ominus> c)) = m) }"

lemma q_ballI: 
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "ac n (x \<ominus> c) = k" 
  assumes "(ord (x \<ominus> c)) = m"
  shows "x \<in> q_ball n k m c"
  using assms q_ball_def 
  by blast

lemma q_ballE: 
  assumes "x \<in> q_ball n k m c "
  shows "x \<in> carrier Q\<^sub>p"

  using assms q_ball_def by blast 

lemma q_ballE': 
  assumes "x \<in> q_ball n k m c "
  shows  "ac n (x \<ominus> c) = k" 
        "(ord (x \<ominus> c)) = m"
  using assms q_ball_def apply blast 
  using assms q_ball_def by blast 

lemma q_ball_in_Qp: 
  "q_ball n k m c  \<subseteq> carrier Q\<^sub>p"
  unfolding q_ball_def by blast 

lemma ac_ord_prop:
  assumes "a \<in> nonzero Q\<^sub>p"
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "ord a = ord b"
  assumes "ord a = n"
  assumes "ac m a = ac m b"
  assumes "m > 0"
  shows "val (a \<ominus> b) \<ge> m + n "
proof-
  have 0: "a = (\<pp>[^]n) \<otimes> \<iota> (angular_component a)"
    using angular_component_factors_x assms(1) assms(4) by blast
  have 1: "b = (\<pp>[^]n) \<otimes> \<iota> (angular_component b)"
    using angular_component_factors_x assms(4) assms(2) assms(3) 
    by presburger
  have 2: "a \<ominus>b = (\<pp>[^]n) \<otimes> \<iota> (angular_component a) \<ominus>
                     (\<pp>[^]n) \<otimes> \<iota> (angular_component b) "
    using 0 1 by auto 
  have 3: "a \<ominus>b = (\<pp>[^]n) \<otimes>( \<iota> (angular_component a) \<ominus>  \<iota> (angular_component b))"
  proof-
    have 30: "(\<pp>[^]n) \<in> carrier Q\<^sub>p"
      by (simp add: p_intpow_closed(1))        
    have 31: " \<iota> (angular_component a)  \<in> carrier Q\<^sub>p"
      using Zp.nonzero_one_closed angular_component_closed assms(1) frac_closed local.inc_def 
      by presburger
    have 32: " \<iota> (angular_component b)  \<in> carrier Q\<^sub>p"
      using Zp.nonzero_one_closed angular_component_closed assms(2) frac_closed local.inc_def 
      by presburger
    show ?thesis 
      using 2 30 31 32 ring.ring_simprules(23)[of Q\<^sub>p "(\<pp>[^]n)"]
      unfolding a_minus_def 
      by (metis Qp.domain_axioms cring.cring_simprules(25) cring.cring_simprules(29) 
          cring.cring_simprules(3) domain.axioms(1))
  qed
  have 4: "a \<ominus>b = (\<pp>[^]n) \<otimes>( \<iota> ((angular_component a) \<ominus>\<^bsub>Z\<^sub>p\<^esub>  (angular_component b)))"
    using 3 
    by (simp add: angular_component_closed assms(1) assms(2) inc_of_diff)    
  have 5: "val_Zp ((angular_component a) \<ominus>\<^bsub>Z\<^sub>p\<^esub>  (angular_component b)) \<ge>  m "    
  proof-
    have "((angular_component a) \<ominus>\<^bsub>Z\<^sub>p\<^esub> (angular_component b)) m = 0"      
      using assms(5)
      unfolding ac_def 
      using Q\<^sub>p_def Qp.nonzero_memE(2) angular_component_closed assms(1) assms(2) residue_of_diff' 
      by auto     
    then show ?thesis 
      using  Zp.minus_closed angular_component_closed assms(1) assms(2) ord_Zp_geq val_Zp_def val_ord_Zp
      by auto      
  qed
  have 6: "val (a \<ominus> b) \<ge> n + val ( \<iota> (angular_component a) \<ominus>  \<iota> (angular_component b))"
    using 3 Qp.minus_closed angular_component_closed assms(1) assms(2) inc_closed 
        ord_p_pow_int p_intpow_closed(1) p_intpow_closed(2) val_mult val_ord
    by simp
  have 7: "n + val ( \<iota> (angular_component a) \<ominus>  \<iota> (angular_component b)) 
          = n + val_Zp ((angular_component a) \<ominus>\<^bsub>Z\<^sub>p\<^esub>  (angular_component b))"
    using Zp.minus_closed angular_component_closed assms(1) assms(2) inc_of_diff val_of_inc 
    by simp
  have 8: "n + val_Zp ( (angular_component a) \<ominus>\<^bsub>Z\<^sub>p\<^esub>(angular_component b))
                \<ge> n + m"
    using 5 
    by (metis add_mono_thms_linordered_semiring(2) plus_eint_simps(1))
  then have 9: "n + val ( \<iota> (angular_component a) \<ominus>  \<iota> (angular_component b)) 
                \<ge> n + m"
    using "7" by presburger
  then show ?thesis 
    by (metis (no_types, opaque_lifting) "6" add.commute order_trans plus_eint_simps(1))   
qed

lemma c_ball_q_ball: 
  assumes "b \<in> nonzero Q\<^sub>p"
  assumes "n > 0"
  assumes "k = ac n b"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> q_ball n k m c"
  shows "q_ball n k m c = c_ball (m + n) d"
proof
  show "q_ball n k m c \<subseteq> B\<^bsub>m + int n\<^esub>[d]"
  proof
    fix x
    assume A0: "x \<in> q_ball n k m c"
    show "x \<in> B\<^bsub>m + int n\<^esub>[d]"
    proof-
      have A1: "(ac n (x \<ominus> c) = k \<and> (ord (x \<ominus> c)) = m)"
        using A0 q_ball_def 
        by blast
      have "val (x \<ominus> d) \<ge> m + n"
      proof-
        have A2: "(ac n (d \<ominus> c) = k \<and> (ord (d \<ominus> c)) = m)"
          using assms(5) q_ball_def 
          by blast
        have A3: "(x \<ominus> c) \<in> nonzero Q\<^sub>p"
        proof-
          have "k \<noteq>0"
            using A2 assms(1) assms(3) assms(5) ac_units[of b n]
            by (metis One_nat_def Suc_le_eq assms(2) zero_not_in_residue_units)                            
          then show ?thesis 
            by (smt A0 Qp.domain_axioms ac_def assms(4) cring.cring_simprules(4) domain.axioms(1)
              mem_Collect_eq not_nonzero_Qp q_ball_def)
        qed
        have A4: "(d \<ominus> c) \<in> nonzero Q\<^sub>p"
        proof-
          have "k \<noteq>0"
            using A2 assms(1) assms(3) assms(5) ac_units[of b n] 
            by (metis One_nat_def Suc_le_eq assms(2) zero_not_in_residue_units)         
          then show ?thesis 
            by (metis (no_types, lifting) A2 Qp.domain_axioms ac_def assms(4) assms(5) 
                cring.cring_simprules(4) domain.axioms(1) mem_Collect_eq not_nonzero_Qp q_ball_def)
        qed
        then have " val ((x \<ominus> c) \<ominus>(d \<ominus> c)) \<ge>  n + m"
          using ac_ord_prop[of "(x \<ominus> c)" "(d \<ominus> c)" m n ] A1 A2 assms A3 
          by simp          
        then show ?thesis 
          by (smt A0 Qp_diff_diff assms(4) assms(5) q_ballE)
      qed
      then show ?thesis 
        by (metis (no_types, lifting) A0 c_ball_def mem_Collect_eq q_ball_def)
    qed
  qed
  show "B\<^bsub>m + int n\<^esub>[d] \<subseteq> q_ball n k m c"
  proof
    fix x
    assume A: "x \<in> B\<^bsub>m + int n\<^esub>[d]"
    show "x \<in> q_ball n k m c"
    proof-
      have A0: "val (x \<ominus> d) \<ge> m + n"
        using A c_ball_def 
        by blast
      have A1: "ord (d \<ominus> c) = m"
        using assms(5) q_ball_def 
        by blast
      have A2: "ac n (d \<ominus> c) = k"
        using assms(5) q_ball_def 
        by blast 
      have A3: "(d \<ominus> c) \<noteq> \<zero>" 
        using A2 assms 
        by (metis ac_def ac_units le_eq_less_or_eq le_neq_implies_less less_one nat_le_linear 
            padic_integers.zero_not_in_residue_units padic_integers_def prime zero_less_iff_neq_zero)                    
      have A4: "val (d \<ominus> c) =m"
        by (simp add: A1 A3 val_def)
      have A5: "val (x \<ominus> d) > val (d \<ominus> c)"
        by (smt A0 A4 assms(2) eint_ord_code(4) eint_ord_simps(1) eint_ord_simps(2) of_nat_0_less_iff val_def)        
      have A6: "val ((x \<ominus> d) \<oplus> (d \<ominus> c)) = m"
        using A4 A0 A5  
        by (metis (mono_tags, opaque_lifting) A Qp.minus_closed assms(4) assms(5) 
            c_ballE(1) q_ballE val_ultrametric_noteq)       
      have A7: "val (x \<ominus> c) = m"
      proof-
        have "(x \<ominus> d) \<oplus> (d \<ominus> c) = ((x \<ominus> d) \<oplus> d) \<ominus> c"
          by (metis (no_types, lifting) A Qp.domain_axioms a_minus_def assms(4) assms(5)
              c_ball_def cring.cring_simprules(3) cring.cring_simprules(4) 
              cring.cring_simprules(7) domain.axioms(1) mem_Collect_eq q_ball_def)
        have "(x \<ominus> d) \<oplus> (d \<ominus> c) = (x \<oplus> (\<ominus> d \<oplus> d)) \<ominus> c"
          by (metis (no_types, opaque_lifting) A Qp.add.l_cancel_one Qp.add.m_comm Qp.l_neg 
              Qp.minus_closed Qp.plus_diff_simp Qp.zero_closed assms(4) assms(5)
              c_ballE(1) q_ballE)          
        then show ?thesis 
          by (metis (no_types, lifting) A A6 Qp.domain_axioms assms(5) c_ball_def 
              cring.cring_simprules(16) cring.cring_simprules(9) domain.axioms(1) 
              mem_Collect_eq q_ball_def)
      qed
      have A8: "ac n (x \<ominus> c) = ac n (d \<ominus> c)"
      proof-
        have A80: "(x \<ominus> c) \<in> nonzero Q\<^sub>p"
          by (metis (no_types, lifting) A A4 A5 A7 Qp.domain_axioms 
              assms(4) cring.cring_simprules(4) domain.axioms(1) 
              mem_Collect_eq c_ball_def val_nonzero)
        have A81: "(d \<ominus> c) \<in> nonzero Q\<^sub>p"
          by (metis (no_types, lifting) A3 Qp.domain_axioms assms(4) assms(5) 
              cring.cring_simprules(4) domain.axioms(1) mem_Collect_eq not_nonzero_Qp q_ball_def)
        have A82: "n + m= val (x \<ominus> c) + n"
          by (simp add: A7)
        show ?thesis 
          using A0 A4 A7 ac_val[of "(x \<ominus> c)" "(d \<ominus> c)" n] A A80 A81 Qp_diff_diff assms(4) assms(5) c_ballE(1) q_ballE 
          by auto         
      qed
      show ?thesis using A8 A3 A7 A2 q_ball_def[of n k m c] q_ballI[of x n c k m]   
        by (metis (no_types, lifting) A A4 A5 Qp.minus_closed assms(4) c_ballE(1) eint.inject val_nonzero val_ord)        
    qed
  qed
qed

definition is_ball :: "padic_number set \<Rightarrow> bool" where
"is_ball B = (\<exists>(m::int). \<exists> c \<in> carrier Q\<^sub>p. (B = B\<^bsub>m\<^esub>[c]))" 

lemma is_ball_imp_in_Qp:
  assumes "is_ball B"
  shows "B \<subseteq> carrier Q\<^sub>p"
  unfolding is_ball_def 
  using assms c_ball_in_Qp is_ball_def 
  by auto

lemma c_ball_centers:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "d \<in> B"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "B = B\<^bsub>n\<^esub>[d]"
proof
  show "B \<subseteq> B\<^bsub>n\<^esub>[d]"
  proof
    fix x
    assume A0: "x \<in> B"
    have "val (x \<ominus> d) \<ge> n"
    proof-
      have A00: "val (x \<ominus> c) \<ge> n"
        using A0 assms(2) c_ballE(2) by blast
      have A01: "val (d \<ominus> c) \<ge> n"
        using assms(2) assms(3) c_ballE(2) by blast
      then show ?thesis 
        using Qp_isosceles[of x c d "n"] assms A0 A00 c_ballE(1) 
        by blast
    qed
    then show "x \<in> B\<^bsub>n\<^esub>[d]" 
      using A0 assms(1) c_ballI is_ball_imp_in_Qp 
      by blast
  qed
  show "B\<^bsub>n\<^esub>[d] \<subseteq> B"
  proof
    fix x
    assume "x \<in> B\<^bsub>n\<^esub>[d]"
    show "x \<in> B"
      using Qp_isosceles[of x d c "n"]
            assms 
      unfolding c_ball_def
      by (metis (no_types, lifting) Qp.domain_axioms Qp_isosceles \<open>x \<in> B\<^bsub>n\<^esub>[d]\<close> 
          a_minus_def assms(2) c_ballE(2) c_ballI cring.cring_simprules(17) domain.axioms(1) 
          c_ballE(1))
  qed
qed

lemma c_ball_center_in:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "c \<in> B"
  using assms  unfolding c_ball_def
  by (metis (no_types, lifting) Qp.r_right_minus_eq assms(2) c_ballI eint_ord_code(3) local.val_zero)
  
text \<open>Every point a has a point b of distance exactly n away from it.\<close>
lemma dist_nonempty:
  assumes "a \<in> carrier Q\<^sub>p"
  shows "\<exists>b \<in> carrier Q\<^sub>p. val (b \<ominus> a) = eint n"
proof-
  obtain b where b_def: "b = (\<pp> [^] n) \<oplus> a"
    by simp 
  have "val (b \<ominus>a) = n"
    using b_def assms 
    by (metis (no_types, lifting) Qp.domain_axioms a_minus_def cring.cring_simprules(16)
        cring.cring_simprules(17) cring.cring_simprules(3) cring.cring_simprules(7)
        domain.axioms(1) ord_p_pow_int p_intpow_closed(1) p_intpow_closed(2) val_ord)
  then show ?thesis 
    by (metis Qp.domain_axioms assms b_def cring.cring_simprules(1) domain.axioms(1) p_intpow_closed(1))
qed

lemma dist_nonempty':
  assumes "a \<in> carrier Q\<^sub>p"
  shows "\<exists>b \<in> carrier Q\<^sub>p. val (b \<ominus> a) = \<alpha>"
proof(cases "\<alpha> = \<infinity>")
  case True
  then have "val (a \<ominus> a) = \<alpha>"
    using assms 
    by (metis Qp.r_right_minus_eq local.val_zero)    
  then show ?thesis 
    using assms 
    by blast
next
  case False
  then obtain n where n_def: "eint n = \<alpha>"
    by blast
  then show ?thesis 
    using assms dist_nonempty[of a n] 
    by blast    
qed

lemma ball_rad_0:
  assumes "is_ball B"
  assumes "B\<^bsub>m\<^esub>[c] \<subseteq> B\<^bsub>n\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "n \<le> m"
proof-
  obtain b where b_def: "b \<in> carrier Q\<^sub>p \<and> val (b \<ominus>c) = m"
    by (meson assms(3) dist_nonempty)
  then have "b \<in> B\<^bsub>n\<^esub>[c]"
    using assms c_ballI 
    by auto
   
  then have "m \<ge> n"
    using Q\<^sub>p_def Zp_def b_def c_ballE(2) padic_integers_axioms 
    by force
  then show ?thesis 
    by (simp )
qed

lemma ball_rad:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B = B\<^bsub>m\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  shows "n = m"
proof-
  have 0: "n \<ge>m"
    using assms ball_rad_0 
    by (metis order_refl)
  have 1: "m \<ge>n"
    using assms ball_rad_0 
    by (metis order_refl)
  show ?thesis 
    using 0 1 
    by auto
qed

definition radius :: "padic_number set \<Rightarrow> int" ("rad") where
"radius B = (SOME n. (\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>n\<^esub>[c]))"

lemma radius_of_ball:
  assumes "is_ball B"
  assumes "c \<in> B"
  shows "B = B\<^bsub>rad B\<^esub>[c]"
proof-
  obtain d m where d_m_def: "d \<in> carrier Q\<^sub>p \<and>  B = B\<^bsub>m\<^esub>[d]"
    using assms(1) is_ball_def 
    by blast
  then have "B = B\<^bsub>m\<^esub>[c]"
    using assms(1) assms(2) c_ball_centers by blast
  then have "rad B = m" 
  proof-
    have "\<exists>n. (\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>n\<^esub>[c])"
      using d_m_def by blast 
    then have "(\<exists>c \<in> carrier Q\<^sub>p . B = B\<^bsub>rad B\<^esub>[c])"
      using radius_def[of B] 
      by (smt someI_ex)
    then show ?thesis 
      using radius_def ball_rad[of B m ]
      by (metis (mono_tags, lifting) \<open>B = B\<^bsub>m\<^esub>[c]\<close> assms(1) assms(2) c_ballE(1) c_ball_centers)
  qed
  then show ?thesis 
    using \<open>B = B\<^bsub>m\<^esub>[c]\<close> by blast
qed

lemma ball_rad':
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B = B\<^bsub>m\<^esub>[d]"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "n = m"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) ball_rad c_ball_center_in c_ball_centers)

lemma nested_balls:
  assumes "is_ball B"
  assumes "B = B\<^bsub>n\<^esub>[c]"
  assumes "B' = B\<^bsub>m\<^esub>[c]"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "d \<in> carrier Q\<^sub>p"
  shows "n \<ge>m \<longleftrightarrow> B \<subseteq> B'"
proof
  show "m \<le> n \<Longrightarrow> B \<subseteq> B'" 
  proof
    assume A0: "m \<le>n" 
    then have A0': "m \<le> n"
      by (simp add: )
    fix x
    assume A1: "x \<in> B"
    show "x \<in> B'"
      using assms c_ballI[of x m c] A0' A1 c_ballE(2)[of x n c]  c_ball_in_Qp 
      by (meson c_ballE(1) dual_order.trans eint_ord_simps(1))      
  qed
  show "B \<subseteq> B' \<Longrightarrow> m \<le> n"
    using assms(1) assms(2) assms(3) assms(4) ball_rad_0 
    by blast
qed

lemma nested_balls':
  assumes "is_ball B"
  assumes "is_ball B'"
  assumes "B \<inter> B' \<noteq> {}"
  shows "B \<subseteq> B' \<or> B' \<subseteq> B"
proof-
  obtain b where b_def: "b \<in> B \<inter> B'"
    using assms(3) by blast
  show "B \<subseteq> B' \<or> B' \<subseteq> B"
  proof-
    have "\<not> B \<subseteq> B' \<Longrightarrow> B' \<subseteq> B"
    proof-
      assume A: "\<not> B \<subseteq> B' "
      have 0: "B = B\<^bsub>rad B\<^esub>[b]"
        using assms(1) b_def radius_of_ball by auto
      have 1: "B' = B\<^bsub>rad B'\<^esub>[b]"
        using assms(2) b_def radius_of_ball by auto
      show "B' \<subseteq> B" using 0 1 A nested_balls 
        by (smt IntD2 Q\<^sub>p_def Zp_def assms(1) assms(2) b_def
            c_ballE(1) padic_integers_axioms)
    qed
    then show ?thesis by blast 
  qed
qed

definition is_bounded:: "padic_number set \<Rightarrow> bool" where
"is_bounded S = (\<exists>n. \<exists>c \<in> carrier Q\<^sub>p. S \<subseteq> B\<^bsub>n\<^esub>[c] )"

lemma empty_is_bounded:
"is_bounded {}"
  unfolding is_bounded_def 
  by blast  


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>$p$-adic Open Sets\<close>
(**************************************************************************************************)
(**************************************************************************************************)


definition is_open:: "padic_number set \<Rightarrow> bool" where
"is_open U \<equiv> (U \<subseteq> carrier Q\<^sub>p) \<and> (\<forall>c \<in> U. \<exists>n. B\<^bsub>n\<^esub>[c]\<subseteq> U )"

lemma is_openI:
  assumes "U \<subseteq>carrier Q\<^sub>p"
  assumes "\<And>c. c \<in> U \<Longrightarrow> \<exists>n. B\<^bsub>n\<^esub>[c]\<subseteq> U"
  shows "is_open U"
  by (simp add: assms(1) assms(2) is_open_def)

lemma ball_is_open:
  assumes "is_ball B"
  shows "is_open B"
  by (metis (mono_tags, lifting) assms is_ball_imp_in_Qp is_open_def radius_of_ball subset_iff)

lemma is_open_imp_in_Qp:
  assumes "is_open U"
  shows "U \<subseteq> carrier Q\<^sub>p"
  using assms unfolding is_open_def 
  by linarith

lemma is_open_imp_in_Qp':
  assumes "is_open U"
  assumes " x \<in> U"
  shows "x \<in> carrier Q\<^sub>p"
  using assms(1) assms(2) is_open_imp_in_Qp 
  by blast

text\<open>
  Owing to the total disconnectedness of the $p$-adic field, every open set can be decomposed
  into a disjoint union of balls which are maximal with respect to containment in that set.
  This unique decomposition is occasionally useful.
\<close>

definition is_max_ball_of ::"padic_number set \<Rightarrow> padic_number set  \<Rightarrow> bool" where
"is_max_ball_of U B \<equiv> (is_ball B) \<and> (B \<subseteq> U) \<and> (\<forall>B'. ((is_ball B') \<and> (B' \<subseteq> U) \<and> B \<subseteq> B') \<longrightarrow> B' \<subseteq> B)"

lemma is_max_ball_ofI:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "(B\<^bsub>m\<^esub>[c]) \<subseteq> U"
  assumes "c \<in> carrier Q\<^sub>p"
  assumes "\<forall>m'. m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
  shows "is_max_ball_of U (B\<^bsub>m\<^esub>[c])"
proof(rule ccontr)
  assume " \<not> is_max_ball_of U B\<^bsub>m\<^esub>[c]"
  then have "\<not> (\<forall>B'. is_ball B' \<and> B' \<subseteq> U \<and> B\<^bsub>m\<^esub>[c] \<subseteq> B'\<longrightarrow> B' \<subseteq> B\<^bsub>m\<^esub>[c])"
    using assms is_max_ball_of_def[of U "B\<^bsub>m\<^esub>[c]" ] 
    unfolding is_ball_def
    by blast
  then obtain B' where B'_def: "is_ball B' \<and> B' \<subseteq> U \<and> B\<^bsub>m\<^esub>[c] \<subseteq> B' \<and> \<not> B' \<subseteq> B\<^bsub>m\<^esub>[c]"
  by auto
  obtain n where n_def: "B' = B\<^bsub>n\<^esub>[c]" 
    by (meson B'_def assms(3) c_ball_center_in is_ball_def radius_of_ball subset_iff)
  then show False 
    using assms 
    by (smt B'_def Q\<^sub>p_def Zp_def ball_rad_0 padic_integers_axioms)
qed

lemma int_prop:
  fixes P:: "int \<Rightarrow> bool"
  assumes "P n"
  assumes "\<forall>m. m \<le>N \<longrightarrow> \<not> P m"
  shows  "\<exists>n. P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
proof-
  have "n > N"
    by (meson assms(1) assms(2) not_less)
  obtain k::nat  where k_def: "k = nat (n - N)"
    by blast
  obtain l::nat where l_def: "l = (LEAST M.  P (N + int M))"
    by simp 
  have 0: " P (N + int l)"
    by (metis (full_types) LeastI \<open>N < n\<close> assms(1) l_def zless_iff_Suc_zadd)
  have 1: "l > 0"
    using "0" assms(2) of_nat_0_less_iff by fastforce
  have 2: "\<And>M. M < l \<longrightarrow> \<not> P (N + M)"
    by (metis Least_le l_def less_le_trans nat_less_le)
  obtain n where n_def: "n = (N + int l)"
    by simp 
  have "P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge> n)"
  proof-
    have "P n"
      by (simp add: "0" n_def)
    have "(\<forall>n'. P n'\<longrightarrow> n' \<ge> n)"
    proof
      fix n'
      show "P n' \<longrightarrow> n \<le> n'"
      proof
        assume "P n'"
        show  "n \<le>n'"
        proof(rule ccontr)
          assume " \<not> n \<le> n'"
          then have C: "n' < n"
            by auto
          show "False"
          proof(cases "n' \<ge> N")
            case True
            obtain M where M_def: "nat (n' - N) = M"
              by simp 
            then have M0: "n' = N + int M "
              using True by linarith
            have M1: "M < l"
              using n_def C M0 
              by linarith
            then show ?thesis using 2 M_def M0 M1 
              using \<open>P n'\<close> by auto
          next
            case False
            then show ?thesis using assms  
              using \<open>P n'\<close> by auto
          qed
        qed
      qed
    qed
    then show ?thesis 
      using \<open>P n\<close> by blast
  qed
  then show ?thesis by blast 
qed

lemma open_max_ball:
  assumes  "is_open U"
  assumes  "U \<noteq> carrier Q\<^sub>p"
  assumes "c \<in> U"
  shows "\<exists>B. is_max_ball_of U B \<and> c \<in> B"
proof-
  obtain B where B_def: "is_ball B \<and> B \<subseteq> U \<and> c \<in> B"
    by (meson assms(1) assms(3) c_ball_center_in is_ball_def is_open_imp_in_Qp' is_open_def padic_integers_axioms)
  show P: "\<exists>B. is_max_ball_of U B \<and> c \<in> B"
  proof(rule ccontr)
    assume C: "\<nexists>B. is_max_ball_of U B \<and> c \<in> B"
    show False
    proof-
      have C': "\<forall>B. c \<in> B \<longrightarrow> \<not>  is_max_ball_of U B "
        using C 
        by auto
      have C'': "\<forall>N. \<exists>m <N. B\<^bsub>m\<^esub>[c] \<subseteq> U "
      proof
        fix N
        show "\<exists>m<N. B\<^bsub>m\<^esub>[c] \<subseteq> U"
        proof(rule  ccontr)
          assume A: "\<not> (\<exists>m<N. B\<^bsub>m\<^esub>[c] \<subseteq> U)"
          obtain P where P_def: "P = (\<lambda> n. \<exists>m<n. B\<^bsub>m\<^esub>[c] \<subseteq> U)"
            by simp
          have A0: "\<exists>n. P n"
            by (metis B_def P_def gt_ex radius_of_ball)
          have A1: "\<forall>m. m \<le>N \<longrightarrow> \<not> P m"
            using A P_def by auto 
          have A2: "\<exists>n. P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
            using A0 A1 int_prop 
            by auto
          obtain n where n_def: " P n \<and> (\<forall>n'. P n'\<longrightarrow> n' \<ge>n)"
            using A2 by blast 
          have " B\<^bsub>n\<^esub>[c] \<subseteq> U"
            by (smt B_def P_def c_ball_def is_ball_def mem_Collect_eq n_def nested_balls order_trans)
          obtain m where m_def: "m < n \<and>B\<^bsub>m\<^esub>[c] \<subseteq> U"
            using P_def n_def by blast
          have "m = n-1"
          proof-
            have "P (m +1)"
              using P_def m_def  
              by auto
            then have "m + 1 \<ge> n"
              using n_def by blast  
            then show ?thesis using m_def by auto  
          qed
          have "\<forall>m'. m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
          proof
            fix m'
            show " m' < m \<longrightarrow> \<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
            proof
              assume "m' < m"
              show "\<not> B\<^bsub>m'\<^esub>[c] \<subseteq> U"
              proof
                assume "B\<^bsub>m'\<^esub>[c] \<subseteq> U"
                then have "P (m' + 1)"
                  using P_def by auto
                have "m'+ 1 < n"
                  using \<open>m = n - 1\<close> \<open>m' < m\<close> by linarith
                then show False 
                  using n_def \<open>P (m' + 1)\<close> by auto
              qed
            qed
          qed
          then have "is_max_ball_of U B\<^bsub>m\<^esub>[c]"
            using is_max_ball_ofI  assms(1) assms(3) is_open_imp_in_Qp is_open_imp_in_Qp' m_def 
            by presburger
          then show False 
            using C assms(1) assms(3) c_ball_center_in is_open_imp_in_Qp'
              is_max_ball_of_def padic_integers_axioms 
            by blast
        qed
      qed
      have "U = carrier Q\<^sub>p"
      proof
        show "carrier Q\<^sub>p \<subseteq> U"
        proof
          fix x
          assume "x \<in> carrier Q\<^sub>p"
          show "x \<in> U"
          proof(cases "x = c")
            case True
            then show ?thesis using assms by auto 
          next
            case False
            obtain m where m_def: "eint m = val(x \<ominus> c)"
              using False 
              by (metis (no_types, opaque_lifting) Qp_diff_diff Qp.domain_axioms \<open>x \<in> carrier Q\<^sub>p\<close> a_minus_def
                  assms(1) assms(3) cring.cring_simprules(16) cring.cring_simprules(17)
                  cring.cring_simprules(4) domain.axioms(1) is_open_imp_in_Qp' val_def val_minus)
            obtain m' where m'_def: "m' < m \<and>  B\<^bsub>m'\<^esub>[c] \<subseteq> U "
              using C'' 
              by blast
            have "val (x \<ominus> c) \<ge> m'"
              by (metis eint_ord_simps(1) less_imp_le m'_def m_def)              
            then have "x \<in> B\<^bsub>m'\<^esub>[c]"
              using \<open>x \<in> carrier Q\<^sub>p\<close> c_ballI by blast
            then show "x \<in> U"
              using m'_def by blast
          qed
        qed
        show "U \<subseteq> carrier Q\<^sub>p " 
          using assms 
          by (simp add: is_open_imp_in_Qp)          
      qed
      then show False using assms by auto 
    qed
  qed
qed

definition interior where
  "interior U = {a. \<exists>B. is_open B \<and> B \<subseteq> U \<and> a \<in> B}"

lemma interior_subset:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior U \<subseteq> U"
proof
  fix x
  assume "x \<in> interior U"
  show "x \<in> U"
  proof-
    obtain B where B_def: "is_open B \<and> B \<subseteq> U \<and> x \<in> B"
      using \<open>x \<in> interior U\<close> interior_def 
      by auto
    then show "x \<in> U"
      by blast
  qed
qed

lemma interior_open:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "is_open (interior U)"
proof(rule is_openI)
  show "interior U \<subseteq> carrier Q\<^sub>p"
    using assms interior_subset by blast
  show "\<And>c. c \<in> interior U \<Longrightarrow> \<exists>n. B\<^bsub>n\<^esub>[c] \<subseteq> interior U"
  proof-
    fix c
    assume "c \<in> interior U"
    show "\<exists>n. B\<^bsub>n\<^esub>[c] \<subseteq> interior U"
    proof-
    obtain B where B_def: "is_open B \<and> B \<subseteq> U \<and> c \<in> B"
      using \<open>c \<in> interior U\<close> interior_def padic_integers_axioms
      by auto
    then show ?thesis 
    proof -
      obtain ii :: "((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set \<Rightarrow> ((nat \<Rightarrow> int) \<times> (nat \<Rightarrow> int)) set set \<Rightarrow> int" 
        where
        "B\<^bsub>ii c B\<^esub>[c] \<subseteq> B"
        by (meson B_def is_open_def)
      then show ?thesis
        using B_def interior_def padic_integers_axioms by auto
qed
  qed
  qed
qed

lemma interiorI:
  assumes "W \<subseteq> U"
  assumes "is_open W"
  shows "W \<subseteq> interior U"
  using assms(1) assms(2) interior_def by blast

lemma max_ball_interior:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "is_max_ball_of (interior U) B"
  shows "is_max_ball_of U B"
proof(rule ccontr)
  assume C: " \<not> is_max_ball_of U B"
  then obtain B' where B'_def: "is_ball B' \<and> B' \<subseteq> U \<and> B \<subseteq> B' \<and> B \<noteq> B'"
    by (metis (no_types, lifting) assms(1) assms(2) dual_order.trans 
        interior_subset is_max_ball_of_def )
  then have "B' \<subseteq> interior U"
    using interior_def padic_integers_axioms ball_is_open 
    by auto   
  then show False using assms B'_def is_max_ball_of_def[of "interior U" "B"]  
    by blast
qed

lemma ball_in_max_ball:
  assumes  "U \<subseteq> carrier Q\<^sub>p"
  assumes  "U \<noteq> carrier Q\<^sub>p"
  assumes "c \<in> U"
  assumes "\<exists>B. B \<subseteq> U \<and> is_ball B \<and> c \<in> B"
  shows "\<exists>B'. is_max_ball_of U B' \<and> c \<in> B'"
proof-
  obtain B where " B \<subseteq> U \<and> is_ball B \<and> c \<in> B"
    using assms(4)
    by blast
  then have 0: "B \<subseteq> interior U"
    using ball_is_open interior_def by blast
  have 1: "c \<in> interior U"
    using "0" \<open>B \<subseteq> U \<and> is_ball B \<and> c \<in> B\<close> by blast
  then have "\<exists>B'. is_max_ball_of (interior U) B' \<and> c \<in> B'"
    using open_max_ball[of "interior U" c] assms(1) assms(2) interior_open interior_subset
    by blast
  then show ?thesis 
    using assms(1) max_ball_interior 
    by blast
qed

lemma ball_in_max_ball':
  assumes  "U \<subseteq> carrier Q\<^sub>p"
  assumes  "U \<noteq> carrier Q\<^sub>p"
  assumes "B \<subseteq> U \<and> is_ball B"
  shows "\<exists>B'. is_max_ball_of U B' \<and> B \<subseteq> B'"
proof-
  obtain c where c_def: "c \<in> B"
    by (metis assms(3) c_ball_center_in is_ball_def)
  obtain B' where B'_def: " is_max_ball_of U B' \<and> c \<in> B'"
    using assms ball_in_max_ball[of U c] c_def 
    by blast
  then show ?thesis 
    by (meson assms(3) c_def disjoint_iff_not_equal nested_balls' 
        is_max_ball_of_def padic_integers_axioms)
qed

lemma max_balls_disjoint:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "is_max_ball_of U B"
  assumes "is_max_ball_of U B'"
  assumes "B \<noteq>B'"
  shows "B \<inter> B' = {}"
  by (meson assms(2) assms(3) assms(4) nested_balls' is_max_ball_of_def 
      padic_integers_axioms subset_antisym)

definition max_balls :: "padic_number set \<Rightarrow> padic_number set set" where
"max_balls U = {B. is_max_ball_of U B }"

lemma max_balls_interior:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  shows "interior U = {x \<in> carrier Q\<^sub>p. (\<exists>B \<in> (max_balls U). x \<in> B)}"
proof
  show "interior U \<subseteq> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
  proof
    fix x
    assume A: " x \<in> interior U"
    show "x \<in> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B}"
      by (metis (mono_tags, lifting) A assms(1) assms(2) interior_open 
          interior_subset is_open_imp_in_Qp' max_ball_interior max_balls_def
          mem_Collect_eq open_max_ball subset_antisym)
  qed
  show "{x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B} \<subseteq> interior U"
  proof
    fix x
    assume A: " x \<in> {x \<in> carrier Q\<^sub>p. \<exists>B\<in>max_balls U. x \<in> B} "
    show "x \<in> interior U"
    proof-
      obtain B where B_def: "B\<in>max_balls U \<and> x \<in> B"
        using A by blast
      then have "B \<subseteq> interior U"
        by (metis (no_types, lifting) interior_def is_max_ball_of_def mem_Collect_eq
            ball_is_open max_balls_def subsetI)
      then show ?thesis 
        using B_def by blast
    qed
  qed
qed

lemma max_balls_interior':
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  assumes "B \<in> max_balls U"
  shows "B \<subseteq> interior U"
  using assms(1) assms(2) assms(3) is_max_ball_of_def max_balls_interior
        max_balls_def padic_integers_axioms 
  by auto

lemma max_balls_interior'':
  assumes "U \<subseteq> carrier Q\<^sub>p"
  assumes "U \<noteq> carrier Q\<^sub>p"
  assumes "a \<in> interior U"
  shows "\<exists>B \<in> max_balls U. a \<in> B"
  using assms(1) assms(2) assms(3) max_balls_interior
  by blast

lemma open_interior:
  assumes "is_open U"
  shows "interior U = U"
  unfolding interior_def using assms  
  by blast

lemma interior_idempotent:
  assumes "U \<subseteq> carrier Q\<^sub>p"
  shows "interior (interior U) = interior U"
  using assms interior_open[of U] open_interior[of "interior U"]
  by auto 


(**************************************************************************************************)
(**************************************************************************************************)
subsection\<open>Convex Subsets of the Value Group\<close>
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  The content of this section will be useful for defining and reasoning about $p$-adic cells in the
  proof of Macintyre's theorem. It is proved that every convex set in the extended integers is 
  either an open ray, a closed ray, a closed interval, or a left-closed interval.\<close>

definition is_convex :: "eint set \<Rightarrow> bool" where
"is_convex A = (\<forall> x \<in> A. \<forall>y \<in> A. \<forall>c. x \<le> c \<and> c \<le> y \<longrightarrow> c \<in> A)"

lemma is_convexI: 
  assumes "\<And>x y c. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<le> c \<and> c \<le>y \<Longrightarrow> c \<in> A"
  shows "is_convex  A"
  unfolding is_convex_def 
  using assms 
  by blast

lemma is_convexE: 
  assumes "is_convex A"
  assumes "x \<in> A" 
  assumes "y \<in> A"
  assumes "x \<le> a"
  assumes "a \<le> y"
  shows "a \<in> A"
  using assms is_convex_def 
  by blast

lemma empty_convex:
"is_convex {}"
  apply(rule is_convexI)
  by blast

lemma UNIV_convex:
"is_convex UNIV"
  apply(rule is_convexI)
  by blast

definition closed_interval ("I[_ _]") where
  "closed_interval \<alpha> \<beta> = {a . \<alpha> \<le> a \<and>  a \<le> \<beta>}"

lemma closed_interval_is_convex:
  assumes "A = closed_interval \<alpha> \<beta>"
  shows "is_convex A"
  apply(rule is_convexI)
  using assms unfolding closed_interval_def 
  by auto  

lemma empty_closed_interval:
"{} = closed_interval \<infinity> (eint 1)"
  unfolding closed_interval_def 
  by auto

definition left_closed_interval  where
"left_closed_interval \<alpha> \<beta> = {a . \<alpha> \<le>  a \<and>  a < \<beta>}"

lemma left_closed_interval_is_convex:
  assumes "A = left_closed_interval \<alpha> \<beta>"
  shows "is_convex A"
  apply(rule is_convexI)
  using assms unfolding left_closed_interval_def 
  using leD order.trans by auto
  
definition closed_ray where
"closed_ray \<alpha> \<beta>  = {a .   a \<le> \<beta> }"

lemma closed_ray_is_convex:
  assumes "A = closed_ray \<alpha> \<beta>"
  shows "is_convex A"
  apply(rule is_convexI)
  using assms unfolding closed_ray_def 
  by auto  

lemma UNIV_closed_ray:
"(UNIV::eint set)= closed_ray \<alpha> \<infinity>"
  unfolding closed_ray_def 
  by simp

definition open_ray :: "eint \<Rightarrow> eint \<Rightarrow> eint set" where
"open_ray \<alpha> \<beta>  = {a .   a < \<beta> }"

lemma open_ray_is_convex:
  assumes "A = open_ray \<alpha> \<beta>"
  shows "is_convex A"
  apply(rule is_convexI)
  using assms unfolding open_ray_def 
  using leD by auto
 
lemma open_rayE:
  assumes "a < \<beta>"
  shows "a \<in> open_ray \<alpha> \<beta>"
  unfolding open_ray_def using assms 
  by blast
  
lemma value_group_is_open_ray:
"UNIV - {\<infinity>} = open_ray \<alpha> \<infinity>"
proof
  show "UNIV - {\<infinity>} \<subseteq> open_ray \<alpha> \<infinity>"  
    using open_rayE[of _ \<alpha> "\<infinity>"]
    by (simp add: open_rayE subset_eq)
  show "open_ray \<alpha> \<infinity> \<subseteq> UNIV - {\<infinity>}"
    unfolding open_ray_def 
    by blast
qed

text\<open>
  This is a predicate which identifies a certain kind of set-valued function on the extended
  integers. Convex conditions will be important in the definition of $p$-adic cells later, and 
  it will be proved that every convex set is induced by a convex condition.\<close>
definition is_convex_condition :: "(eint \<Rightarrow> eint \<Rightarrow> eint set) \<Rightarrow> bool"
  where "is_convex_condition I \<equiv> 
              I = closed_interval \<or> I = left_closed_interval \<or> I = closed_ray \<or> I = open_ray"

lemma convex_condition_imp_convex: 
  assumes "is_convex_condition I"
  shows "is_convex (I \<alpha> \<beta>)"
  using assms 
  unfolding is_convex_condition_def 
  by (meson closed_interval_is_convex closed_ray_is_convex left_closed_interval_is_convex open_ray_is_convex)

lemma bounded_order:
  assumes "(a::eint) < \<infinity>"
  assumes  "b \<le>  a"
  obtains k::nat where  "a = b + k"
proof-
  obtain m::int where m_def: "a = m"
    using assms(1) less_infinityE by blast
  obtain n::int where n_def: "b = n"
    using assms(2) eint_ile m_def by blast
  have 0: "a - b =  eint (m - n)"
    by (simp add: m_def n_def)
  then have "a = b + nat (m - n)"
    using assms m_def n_def 
    by simp
  thus ?thesis 
    using that by blast
qed
  
text\<open>Every convex set is given by a convex condition\<close>
lemma convex_imp_convex_condition:
  assumes "is_convex A"
  shows "\<exists> I \<alpha> \<beta>. is_convex_condition I \<and> A = (I \<alpha> \<beta>)"
proof(cases "\<exists> a \<in> A. \<forall> b \<in> A. a \<le> b")
  case True
  then obtain \<alpha> where alpha_def: "\<alpha> \<in> A \<and> (\<forall> b \<in> A. \<alpha> \<le> b)"
    by blast 
  then show ?thesis
  proof(cases "\<exists> a \<in> A. \<forall> b \<in> A. b \<le> a")
    case True
    then obtain \<beta> where beta_def: "\<beta> \<in> A \<and> (\<forall> b \<in> A. b \<le> \<beta>)"
      by blast 
    have "A = closed_interval \<alpha> \<beta>"
      unfolding closed_interval_def 
      using alpha_def beta_def assms is_convexE[of A \<alpha> \<beta>]
      by blast
    then show ?thesis 
      using is_convex_condition_def 
      by blast
  next
    case False
    have F0: "\<forall>a. \<alpha> \<le> a \<and> a < \<infinity> \<longrightarrow> a \<in> A"
    proof(rule ccontr)
      assume A: "\<not> (\<forall>a. a \<ge> \<alpha> \<and> a < \<infinity> \<longrightarrow> a \<in> A)"
      then obtain a where a_def: " \<alpha> \<le> a \<and> a < \<infinity> \<and> a \<notin> A"
        by blast 
      obtain n where n_def: "\<alpha> = eint n"
        using False alpha_def by force        
      obtain m where m_def: "a = eint m"
        using a_def less_infinityE by blast        
      have "\<forall>k::nat. \<exists>c. (\<alpha> + eint (int k)) < c \<and> c \<in> A"
      proof fix k
        show "\<exists>c>\<alpha> + eint (int k). c \<in> A"
          apply(induction k)
           using False alpha_def le_less_linear zero_eint_def apply fastforce           
        proof- fix k
          assume IH: "\<exists>c>\<alpha> + eint (int k). c \<in> A"
          then obtain c where c_def: "c>\<alpha> + eint (int k) \<and> c \<in> A"
            by blast 
          then obtain c' where c'_def: "c' \<in> A \<and> c < c'" 
            using False 
            by (meson le_less_linear)            
          then have "(\<alpha> + eint (int (Suc k))) \<le> c'"
          proof-
            have 0: "eint (int (Suc k)) = eint (int k) + eint 1"
              by simp
            have "\<alpha> + eint (int k) \<le>c'"
              by (meson c'_def c_def le_less le_less_trans)              
            then have 1: "(\<alpha> + eint (int k)) < c'"
              using c'_def c_def le_less_trans 
              by auto                      
            have 2: "\<alpha> + eint (int k) + eint 1 = \<alpha> + eint (int (Suc k))"
              using 0 
              by (simp add: n_def)
            then show "(\<alpha> + eint (int (Suc k))) \<le> c'"
              by (metis "1" ileI1 one_eint_def)              
          qed
          then show "\<exists>c>\<alpha> + eint (int (Suc k)). c \<in> A"
            using False c'_def not_less by fastforce            
        qed
      qed
      obtain k where k_def: "k = a - \<alpha>"
        using a_def n_def 
        by blast 
      hence "k \<ge> 0"
        using a_def n_def 
        by (metis alpha_def eint_minus_le le_less)        
      hence 0: "\<exists>n::nat. k = n"
        using a_def n_def  k_def   
        by (metis eint.distinct(2) eint_0_iff(2) eint_add_cancel_fact eint_ord_simps(1) fromeint.cases m_def nonneg_int_cases plus_eint_simps(3))        
      have 1: "a = \<alpha> + k"
        using k_def a_def n_def 
        by simp
      then obtain c where "c \<in> A \<and> a < c"
        by (metis "0" \<open>\<forall>k. \<exists>c>\<alpha> + eint (int k). c \<in> A\<close> the_eint.simps)        
      then have "a \<in> A"
        using is_convexE[of A \<alpha> a c] a_def alpha_def assms is_convexE 
        by (meson linear not_less)        
      then show False 
        using a_def by blast
    qed
    have "A = closed_interval \<alpha>  \<infinity> \<or> A = left_closed_interval \<alpha> \<infinity>"
      apply(cases "\<infinity> \<in> A")
      using False eint_ord_code(3) apply blast      
    proof-
      assume A0: "\<infinity> \<notin> A "
      have "A = left_closed_interval \<alpha> \<infinity>"
      proof
        show "A \<subseteq> left_closed_interval \<alpha> \<infinity>"
          unfolding left_closed_interval_def 
          using alpha_def A0 
          by (metis (mono_tags, lifting) False eint_ord_code(3) le_less_linear less_le_trans mem_Collect_eq subsetI)
        show "left_closed_interval \<alpha> \<infinity> \<subseteq> A"
          unfolding left_closed_interval_def 
          using alpha_def A0 F0 
          by blast
      qed
      then show ?thesis 
        by blast 
    qed
    then show ?thesis 
      unfolding is_convex_condition_def  
      by blast
  qed
next
  case False
  show ?thesis apply(cases "A = {}")
    using empty_closed_interval is_convex_condition_def apply blast
  proof-
    assume A0: "A \<noteq> {}"
    have "A \<noteq> {\<infinity>}"
      using False  
      by blast
    then obtain \<alpha> where alpha_def: "\<alpha> \<in> A \<and> \<alpha> \<noteq>\<infinity>"
      using A0 
      by fastforce
    have A1: "\<And>k::nat. \<exists> b \<in> A. b + eint (int k) \<le> \<alpha>"
    proof- fix k
      show " \<exists> b \<in> A. b + eint (int k) \<le> \<alpha>"
      proof(induction k)
        case 0
        then have "\<alpha> + eint (int 0) = \<alpha>"
          by (simp add: zero_eint_def)          
        then show ?case 
          using alpha_def by auto                      
      next
        case (Suc k) fix k
        assume IH: "\<exists>b\<in>A. \<alpha> \<ge> b + eint (int k)"
        show "\<exists>b\<in>A. \<alpha> \<ge> b + eint (int (Suc k))"
        proof-
          obtain b where b_def: "b \<in> A \<and> \<alpha> \<ge> b + eint (int k)"
            using IH by blast 
          then obtain c where c_def: "c \<in> A \<and> c < b"
            using False le_less_linear by blast           
          have 0: "(c + eint (int (Suc k))) < (b + eint (int (Suc k)))"
            using c_def 
            by simp            
          have 1: "b + eint (int (Suc k)) =  (b + eint (int k)) + eint 1"
            by simp            
          then show ?thesis 
            by (metis "0" b_def c_def eSuc_ile_mono ileI1 le_less one_eint_def)            
        qed
      qed
    qed
    show ?thesis 
    proof(cases "\<exists> a \<in> A. \<forall> b \<in> A. b \<le> a")
      case True
      then obtain \<beta> where beta_def: "\<beta> \<in> A \<and> (\<forall> b \<in> A. b \<le> \<beta>)"
        by blast 
      have "A = closed_ray \<alpha> \<beta>"
        unfolding closed_ray_def 
      proof
        show "A \<subseteq> {a. \<beta> \<ge> a}"
          using assms beta_def 
          by blast
        show "{a. \<beta> \<ge> a} \<subseteq> A"
        proof fix x assume "x \<in> {a. \<beta> \<ge> a}"
          then have 0: "\<beta> \<ge> x" by blast 
          show "x \<in> A"
          proof(cases "x \<le> \<alpha>")
            case True
            obtain n where n_def: "\<alpha>= eint n"
              using alpha_def 
              by blast              
            obtain m where m_def: "x = eint m"
              using True eint_ile n_def by blast             
            have 1: "m \<le> n"
              using  True m_def n_def 
              by simp             
            have 2: "eint (int (nat (n - m))) = eint (n - m)"
              by (simp add: "1")
            then obtain b where b_def: "b \<in> A \<and> b + eint (n - m) \<le> \<alpha>"
              using  A1[of "nat (n - m)"] 
              by (metis)
            then have "b + eint (n - m) \<le> x + eint (n - m)"
              using b_def  
              by (simp add: m_def n_def)              
            then have "b \<le> x"
              by auto              
            then show ?thesis 
              using "0" assms b_def beta_def is_convex_def 
              by blast           
          next
            case False
            then show ?thesis 
              using "0" alpha_def assms beta_def is_convexE 
              by (meson linear)              
          qed
        qed
      qed
      then show ?thesis 
        using is_convex_condition_def 
        by blast
    next
      case f: False
      have F0: "\<forall>a. \<alpha> \<le> a \<and> a < \<infinity> \<longrightarrow> a \<in> A"
      proof(rule ccontr)
      assume A: "\<not> (\<forall>a. a \<ge> \<alpha> \<and> a < \<infinity> \<longrightarrow> a \<in> A)"
      then obtain a where a_def: " \<alpha> \<le> a \<and> a < \<infinity> \<and> a \<notin> A"
        by blast 
      obtain n where n_def: "\<alpha> = eint n"
        using alpha_def by blast        
      obtain m where m_def: "a = eint m"
        using a_def less_infinityE by blast       
      have 0: "\<forall>k::nat. \<exists>c. (\<alpha> + eint (int k)) < c \<and> c \<in> A"
      proof fix k
        show "\<exists>c>\<alpha> + eint (int k). c \<in> A"
          apply(induction k)
           using alpha_def f le_less_linear apply fastforce                               
        proof- fix k
          assume IH: "\<exists>c>\<alpha> + eint (int k). c \<in> A"
          then obtain c where c_def: "c>\<alpha> + eint (int k) \<and> c \<in> A"
            by blast 
          then obtain c' where c'_def: "c' \<in> A \<and> c < c'" 
            using False f le_less_linear by blast                        
          then have "(\<alpha> + eint (int (Suc k))) \<le> c'"
          proof-
            have 0: "eint (int (Suc k)) = eint (int k) + eint 1"
              by simp
            have "\<alpha> + eint (int k) \<le>c'"
              using c_def c'_def dual_order.strict_trans le_less by blast                 
            then have 1: "(\<alpha> + eint (int k)) < c'"
              using c'_def c_def le_less_trans by auto                          
            have 2: "\<alpha> + eint (int k) + eint 1 = \<alpha> + eint (int (Suc k))"
              using 0 by (simp add: n_def)
            then show "(\<alpha> + eint (int (Suc k))) \<le> c'"
              by (metis "1" ileI1 one_eint_def)              
          qed
          then show "\<exists>c>\<alpha> + eint (int (Suc k)). c \<in> A"
            using False c'_def 
            by (smt c_def eSuc_eint iadd_Suc_right ileI1 le_less of_nat_Suc)            
        qed
      qed
      obtain k::nat where "a = \<alpha> + eint (int k)"
        using bounded_order a_def
        by blast
      then obtain c where "c \<in> A \<and> a <c"
        using 0 by blast        
      then have "a \<in> A"
        using is_convexE[of A \<alpha> a c] a_def alpha_def assms is_convexE 
        by (meson linear not_less)       
      then show False 
        using a_def by blast
      qed
      have "A = UNIV - {\<infinity>}"
      proof
        show "A \<subseteq> UNIV - {\<infinity>}"
          using f by auto        
        show "UNIV - {\<infinity>} \<subseteq> A"       
        proof fix x ::eint 
          assume A: "x \<in> UNIV - {\<infinity>}"
          show "x \<in> A"
          proof(cases "x \<le> \<alpha>")
            case True
            obtain k::nat where k_def: "x + k = \<alpha>"
              by (metis True alpha_def bounded_order eint_ord_simps(4))
            obtain c where c_def: "c \<in> A \<and> c + k = \<alpha>"
              by (metis A1 True add.commute alpha_def assms eint_add_left_cancel_le is_convexE k_def not_eint_eq)
            have "x = c"
              using k_def c_def 
              by auto
            thus ?thesis 
              by (simp add: c_def)
          next
            case False
            thus ?thesis 
              using A F0 by auto            
          qed
        qed
      qed
    then show ?thesis 
      by (meson is_convex_condition_def value_group_is_open_ray)
   qed
 qed
qed

lemma ex_val_less:
  shows "\<exists> (\<alpha>::eint). \<alpha> < \<beta>"
  apply(induction \<beta>)
  using eint_ord_simps(2) lt_ex apply blast
  using eint_ord_simps(4) by blast

lemma ex_dist_less:
  assumes "c \<in> carrier Q\<^sub>p"
  shows "\<exists> a \<in> carrier Q\<^sub>p. val (a \<ominus> c) < \<beta>"
  using ex_val_less[of \<beta>] assms 
  by (metis dist_nonempty' ex_val_less)
end
end