subsection \<open> Cauchy's Polygonal Number Theorem \<close>

text \<open>We will use the definition of the polygonal numbers from the Gauss Theorem theory file
which also imports the Three Squares Theorem AFP entry \cite{Three_Squares-AFP}.\<close>

theory Polygonal_Number_Theorem_Cauchy
  imports Polygonal_Number_Theorem_Gauss
begin

text\<open>The following lemma shows there are two consecutive odd integers in any four consecutive
integers.\<close>

lemma two_consec_odd:
  fixes a1 a2 a3 a4 :: int
  assumes "a1-a2 = 1"
  assumes "a2-a3 = 1"
  assumes "a3-a4 = 1"
  shows "\<exists>k1 k2 :: int. {k1, k2} \<subseteq> {a1, a2, a3, a4} \<and> (k2 = k1+2) \<and> odd k1"

proof -
  have c1:"\<exists>k1 k2 :: int. {k1, k2} \<subseteq> {a1, a2, a3, a4} \<and> (k2 = k1+2) \<and> odd k1"
    if odd_case:"odd a4"
  proof-
    define k1 where k1_def:"k1 = a4"
    define k2 where k2_def:"k2 = k1 + 2"
    have 0:"k2 = a2" using k2_def k1_def assms by simp
    have 1:"odd k1" using k1_def odd_case by simp
    show "\<exists>k1 k2 :: int. {k1, k2} \<subseteq> {a1, a2, a3, a4} \<and> (k2 = k1+2) \<and> odd k1"
      using 0 1 k1_def k2_def by auto
  qed

  have c2:"\<exists>k1 k2 :: int. {k1, k2} \<subseteq> {a1, a2, a3, a4} \<and> (k2 = k1+2) \<and> odd k1"
    if even_case:"even a4"
  proof -
    define k1 where k1_def:"k1 = a3"
    define k2 where k2_def:"k2 = k1 + 2"
    have 2:"odd k1" using even_case assms k1_def by presburger
    have 3:"k2 = a1" using k1_def k2_def assms by simp
    show "\<exists>k1 k2 :: int. {k1, k2} \<subseteq> {a1, a2, a3, a4} \<and> (k2 = k1+2) \<and> odd k1"
      using 2 3 k1_def k2_def by auto
  qed
  show ?thesis using c1 c2 by auto
qed

text \<open>This lemma proves that for two consecutive integers $b_1$ and $b_2$, and $r \in \{0,1,\dots,m-3\}$,
numbers of the form $b_1+r$ and $b_2+r$ can cover all the congruence classes modulo $m$.\<close>

lemma cong_classes:
  fixes b1 b2 :: int
  fixes m :: nat
  assumes "m \<ge> 4"
  assumes "odd b1"
  assumes "b2 = b1 + 2"
  shows "\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"

proof -
  have first:"\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
    if first_assum:"b1 mod m \<ge> 3"
  proof -
    define k1 where k1_def:"k1 = b1 mod m"
    define l where l_def:"l = m - k1"
    have k1_size:"k1\<ge>3" using first_assum k1_def by simp
    have l_size:"l \<le> m-3" using first_assum k1_def l_def by auto
    have "(l+k1) mod m = 0" using l_def by auto
    hence "(l+b1) mod m = 0" using k1_def l_def by (metis mod_add_right_eq)
    define w where w_def:"w = m-3-l"
    have w_size:"w\<ge>0 \<and> w\<le>m-3" using w_def l_size l_def k1_def first_assum
      by (smt (verit, best) Euclidean_Rings.pos_mod_bound assms(1) le_antisym numeral_neq_zero
 of_nat_0_less_iff order_trans_rules(22) verit_comp_simplify(3) zero_le_numeral)
    have "k1 = w+3" using w_def k1_def l_def w_size first_assum by linarith
    hence "w+2 = k1-1" by auto
    hence "w+2 = (b1-1) mod m" using first_assum k1_def
      by (smt (verit, del_insts) Euclidean_Rings.pos_mod_bound assms(1)
 mod_diff_eq mod_pos_pos_trivial of_nat_le_0_iff verit_comp_simplify(8))
    hence w_cover:"w+2 = k1-1" using k1_def using \<open>w + 2 = k1 - 1\<close> by fastforce

    have "\<exists>r::nat. (r\<le>m-3) \<and> [N=b1+r] (mod m)" if asm1:"N mod m \<ge> k1 \<and> N mod m \<le> m-1" for N
    proof -
      have "m - (N mod m) \<le> l" using asm1 l_def k1_def by linarith
      hence "\<exists>d::nat. d\<le>l \<and> [N = k1+d] (mod m)" using asm1 k1_def l_def
        by (metis add.commute add_le_cancel_left cong_mod_left cong_refl diff_add_cancel
 diff_le_self le_trans of_nat_mod of_nat_mono zle_iff_zadd)
      hence "\<exists>d::nat. d\<le>l \<and> [N=b1+d] (mod m)" using  k1_def
        by (metis mod_add_left_eq unique_euclidean_semiring_class.cong_def)
      thus "\<exists>r::nat. (r\<le>m-3) \<and> [N=b1+r] (mod m)" using l_size
        by (smt (verit, best) nat_leq_as_int)
    qed
    hence c1:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)" if asm1:"N mod m \<ge> k1 \<and> N mod m \<le> m-1" for N using asm1 by blast

    have c2:"\<exists>r::nat. (r\<le>m-3) \<and> [N=b1+r] (mod m)" if asm2:"N mod m =0" for N using l_def k1_def
      by (smt (verit, ccfv_threshold) \<open>(l + b1) mod int m = 0\<close> add_diff_cancel_left' cong_0_iff
 cong_sym cong_trans diff_add_cancel diff_ge_0_iff_ge dvd_eq_mod_eq_0 int_dvd_int_iff nat_0_le
of_nat_le_iff that w_def w_size)
    hence c2:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm2:"N mod m = 0" for N using asm2 by metis

    have "\<exists>r::nat. (r\<le>m-3) \<and> [N=b1+r] (mod m)" if asm3:"N mod m > 0 \<and> N mod m \<le>w" for N
    proof -
      have "l+ (N mod m) \<le> m-3" using asm3 w_def by auto
      hence "\<exists>d::nat. (d\<le>w) \<and> [N = k1+l+d] (mod m)" using asm3 w_def k1_def l_def
        by (smt (verit, ccfv_threshold) minus_mod_self2 mod_mod_trivial of_nat_mod
            unique_euclidean_semiring_class.cong_def)
      hence "\<exists>d::nat. (d\<le>w) \<and> [N = b1+l+d] (mod m)" using k1_def by (metis (mono_tags,
              opaque_lifting) mod_add_left_eq unique_euclidean_semiring_class.cong_def)
      hence "\<exists>r::nat. (r\<le>w+l) \<and> [N = b1+r] (mod m)" by (smt (verit) add.commute
            add.left_commute le_add_same_cancel2 of_nat_0_le_iff w_def w_size zero_le_imp_eq_int)
      thus "\<exists>r::nat. (r\<le>m-3) \<and> [N = b1+r] (mod m)" using w_def by auto
    qed
    hence "\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm3:"N mod m > 0 \<and> N mod m \<le>w" for N using asm3 by blast
    hence c3:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm8:"N mod m > 0 \<and> N mod m \<le>k1-3" using asm8 w_cover by auto

    have "\<exists>r::nat. (r\<le>m-3) \<and> [N=b2+r] (mod m)" if asm4:"N mod m = w+1 \<or> N mod m = w+2" for N
    proof -
      have c4_1:"[N = b2+(m-3)] (mod m)" if asm5:"N mod m=w+2" for N using asm5 w_def assms(3) l_def
        by (smt (verit) \<open>w + 2 = (b1 - 1) mod int m\<close> \<open>w + 2 = k1 - 1\<close> mod_add_self1 of_nat_mod
            unique_euclidean_semiring_class.cong_def)
      hence "[N-1 = b2+(m-4)] (mod m)" if asm5:"N mod m = w+2" for N
        by (smt (verit, ccfv_threshold) Num.of_nat_simps(2) \<open>w + 2 = k1 - 1\<close> asm5 assms(1)
 cong_iff_lin first_assum k1_def l_def mod_less_eq_dividend numeral_Bit0 of_nat_diff of_nat_le_iff
of_nat_numeral semiring_norm(172) w_def)
      hence "[N = b2+(m-4)] (mod m)" if asm6:"N mod m = w+1" for N using asm6
        by (metis \<open>w + 2 = (b1 - 1) mod int m\<close> add_diff_cancel_right' arith_special(3) int_ops(4)
            is_num_normalize(1) mod_add_left_eq mod_diff_left_eq of_nat_mod)
      thus ?thesis using c4_1 by (metis asm4 diff_le_mono2 nat_le_linear numeral_le_iff
            verit_comp_simplify(10) verit_comp_simplify(13))
    qed
    hence "\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm4:"N mod m = w+1 \<or> N mod m = w+2" for N using asm4 by blast
    hence c4:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm7:"N mod m = k1-2 \<or> N mod m = k1-1" for N using w_cover asm7 by auto

    have "\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm10:"N mod m \<ge> 0 \<and> N mod m \<le>w" for N using c2 c3 asm10
      using \<open>\<And>N. 0 < N mod m \<and> int (N mod m) \<le> w \<Longrightarrow> \<exists>b r. r \<le> m - 3 \<and> [int N = b + int r]
      (mod int m) \<and> (b = b1 \<or> b = b2)\<close> by blast
    hence c5:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm11:"N mod m \<ge> 0 \<and> N mod m \<le>k1-3" for N using w_cover using asm11 by force

    have c6:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm9:"(N mod m \<ge>0 \<and> N mod m \<le> k1-3) \<or> N mod m = k1-2 \<or> N mod m = k1-1" for N
      using c5 c4 asm9 by blast

    hence c7:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if asm12:"(N mod m \<ge>0 \<and> N mod m \<le> k1-3) \<or> N mod m = k1-2 \<or> N mod m = k1-1 \<or>
 (N mod m \<ge> k1 \<and> N mod m \<le> m-1)" for N using asm12 c1 by blast

    have "\<forall>N::nat. (N mod m \<ge>0 \<and> N mod m\<le> k1-3) \<or> N mod m = k1-2 \<or> N mod m = k1-1 \<or>
 (N mod m \<ge> k1 \<and> N mod m \<le> m-1)" using k1_def
      by (smt (verit, best) Suc_pred' assms(1) bot_nat_0.extremum le_simps(2) mod_less_divisor
not_numeral_le_zero of_nat_0_less_iff of_nat_le_0_iff)

    thus ?thesis using c7 by auto
  qed

  have second:"\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
    if second_assum:"b1 mod m \<ge>0 \<and> b1 mod m \<le>2"
  proof -
    have case1:"\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if case1_assum:"b1 mod m = 0"
    proof -
      have "\<exists>r::nat. (r \<le> m-3) \<and> [N = b1+r] (mod m)" if case1_1_assum:"N mod m \<le>m-3" for N
        using case1_assum case1_1_assum
        by (metis cong_add_rcancel_0 cong_mod_left cong_refl cong_sym_eq zmod_int)
      hence case1_1:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case1_1_assum:"N mod m \<le>m-3" for N using case1_1_assum by blast

      have "[N = b1+(m-2)] (mod m)" if case1_2_assum:"N mod m = m-2" for N using case1_2_assum
        case1_assum by (metis (no_types, opaque_lifting) add.commute cong_add_lcancel_0
            cong_mod_right of_nat_mod unique_euclidean_semiring_class.cong_def)
      hence "[N = b2+(m-4)] (mod m)" if case1_2_assum:"N mod m = m-2" for N using case1_2_assum assms(3)
        by (smt (verit, best) add_leD2 assms(1) int_ops(2) numeral_Bit0 of_nat_diff of_nat_numeral
            semiring_norm(172))
      hence "\<exists>r::nat. (r \<le> m-3) \<and> [N = b2+r] (mod m)" if case1_2_assum:"N mod m = m-2" for N
        using case1_2_assum
        by (meson diff_le_mono2 less_num_simps(2) numeral_le_iff verit_comp_simplify(15))
      hence case1_2:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case1_2_assum:"N mod m = m-2" for N using case1_2_assum by blast

      have "[N = b1+(m-1)] (mod m)" if case1_3_assum:"N mod m = m-1" for N using case1_3_assum
        case1_assum by (metis (no_types, opaque_lifting) add.commute cong_add_lcancel_0
            cong_mod_right of_nat_mod unique_euclidean_semiring_class.cong_def)
      hence "[N = b2+(m-3)] (mod m)" if case1_3_assum:"N mod m = m-1" for N using case1_3_assum assms(3)
        by (smt (verit, best) assms(1) int_ops(2) int_ops(6) numeral_Bit0 numeral_Bit1 of_nat_mono
            of_nat_numeral semiring_norm(172))
      hence "\<exists>r::nat. (r \<le> m-3) \<and> [N = b2+r] (mod m)" if case1_3_assum:"N mod m = m-1" for N
        using case1_3_assum by blast
      hence case1_3:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case1_3_assum:"N mod m = m-1" for N using case1_3_assum by blast

      have "\<forall>N::nat. (N mod m = m-1) \<or> (N mod m = m-2) \<or> (N mod m \<le> m-3)"
        by (smt (verit, ccfv_threshold) Suc_pred' assms(1) bot_nat_0.not_eq_extremum diff_diff_add
diff_is_0_eq' le_simps(2) mod_less_divisor nat_1_add_1 nat_less_le not_numeral_le_zero
numeral.simps(3) semiring_norm(172))
      thus ?thesis using case1_1 case1_2 case1_3 by blast
    qed

    have case2:"\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if case2_assum:"b1 mod m = 1"
    proof -
      have case2b2:"b2 mod m = 3" using case2_assum assms(3) by (smt (verit) assms(1) int_ops(2)
 mod_add_eq mod_pos_pos_trivial numeral_Bit0 of_nat_mono of_nat_numeral semiring_norm(172))

      have "\<exists>r::nat. (r\<le>m-3) \<and> [N = b2+r] (mod m)" if case2_1_assum:"N mod m = m-1" for N
      proof -
        have "[N = 3+(m-4)] (mod m)" using case2_1_assum
          by (metis (mono_tags, lifting) Suc_eq_plus1 Suc_numeral add_diff_cancel_left
             arithmetic_simps(1) arithmetic_simps(7) assms(1)mod_mod_trivial
             ordered_cancel_comm_monoid_diff_class.diff_add_assoc unique_euclidean_semiring_class.cong_def)
        hence "[N = b2+(m-4)] (mod m)" using case2b2
          by (metis (mono_tags, lifting) Num.of_nat_simps(4) mod_add_left_eq
              of_nat_mod of_nat_numeral unique_euclidean_semiring_class.cong_def)
        thus ?thesis using le_diff_conv by fastforce
      qed
      hence case2_1:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case2_1_assum:"N mod m = m-1" for N using case2_1_assum by blast

      have "\<exists>r::nat. (r\<le>m-3) \<and> [N = b2+r] (mod m)" if case2_2_assum:"N mod m =0" for N
      proof -
        have "(3+(m-3)) mod m = 0" using assms(1) by fastforce
        hence "(b2+(m-3)) mod m = 0" using case2b2 by (metis Num.of_nat_simps(1)
              Num.of_nat_simps(4) mod_add_left_eq of_nat_mod of_nat_numeral)
        thus ?thesis using case2_2_assum
          by (metis int_ops(1) nat_le_linear of_nat_mod unique_euclidean_semiring_class.cong_def)
      qed
      hence case2_2:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case2_2_assum:"N mod m =0" for N using case2_2_assum by metis

      have "\<exists>r::nat. (r \<le> m-3) \<and> [N = b1+r] (mod m)" if
        case2_3_assum:"N mod m \<le>m-2 \<and> N mod m \<ge>1" for N
      proof -
        have "\<exists>r::nat. (r\<le>m-3)\<and>((b1+r) mod m = l)" if asml:"l\<ge>1 \<and> l\<le>m-2" for l
        proof -
          define r where r_def:"r = l-1"
          from asml have r_range:"r\<ge>0 \<and> r\<le>m-3" using r_def by linarith
          have "(1+r) mod m = l" using asml r_def r_range by fastforce
          hence "(b1+r) mod m = l" using case2_assum
            by (metis Num.of_nat_simps(3) int_ops(9) mod_add_left_eq plus_1_eq_Suc)
          thus ?thesis using asml r_range by blast
        qed
        thus ?thesis using case2_3_assum
          by (metis case2_3_assum of_nat_mod unique_euclidean_semiring_class.cong_def)
      qed
      hence case2_3:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if  case2_3_assum:"N mod m \<le>m-2 \<and> N mod m \<ge>1" for N using case2_3_assum by blast

      have "\<forall>N::nat. N mod m = 0 \<or> (N mod m \<ge>1 \<and> N mod m \<le>m-1)" by (metis One_nat_def Suc_pred
assms(1) bot_nat_0.extremum_uniqueI leI less_Suc_eq_le mod_less_divisor not_numeral_le_zero)
      hence "\<forall>N::nat. N mod m = 0 \<or> (N mod m \<ge>1 \<and> N mod m \<le>m-2) \<or> N mod m = m-1"
        by (smt (verit) arithmetic_simps(68) diff_diff_eq le_add_diff_inverse le_neq_implies_less le_simps(2)
           le_trans plus_1_eq_Suc)
      thus ?thesis using case2_1 case2_2 case2_3 by (metis \<open>\<And>N. N mod m \<le> m - 2 \<and> 1 \<le> N mod m
   \<Longrightarrow> \<exists>r\<le>m - 3. [int N = b1 + int r] (mod int m)\<close>)
    qed

    have case3:"\<forall>N::nat. \<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
      if case3_assum:"b1 mod m = 2"
    proof -
      have case3b2:"b2 mod m = 4"
        using assms case3_assum
        by (smt (verit, ccfv_SIG) Euclidean_Rings.pos_mod_sign dvd_mod_imp_dvd even_numeral int_ops(2)
                int_ops(4) mod_diff_eq mod_pos_pos_trivial nat_1_add_1 numeral_Bit0 of_nat_le_iff
                of_nat_numeral plus_1_eq_Suc)

      have "\<exists>r::nat. (r\<le>m-3)\<and> [N = b2+r] (mod m)" if case3_1_assum:"N mod m = 0 \<or> N mod m =1" for N
      proof -
        have "(4+(m-3)) mod m = (4+m-3) mod m" using assms(1) by auto
        have "(4+m-3) mod m = (1+m) mod m" by simp
        hence "(4+(m-3)) mod m = 1" using \<open>(4+(m-3)) mod m = (4+m-3) mod m\<close>
          by (smt (verit, best) Euclidean_Rings.pos_mod_bound add_lessD1 arith_special(2) assms(1) case3b2
              landau_product_preprocess(4) mod_add_self2 mod_less numeral_Bit0 of_nat_numeral order_le_less)
        hence caseone:"(b2+(m-3)) mod m = 1" using case3b2
          by (metis Num.of_nat_simps(2) Num.of_nat_simps(4) mod_add_left_eq of_nat_mod of_nat_numeral)

        have "(4+(m-4)) mod m = 0" using assms(1) by auto
        hence casezero:"(b2+(m-4)) mod m = 0" using case3b2
          by (metis (full_types) Num.of_nat_simps(1) Num.of_nat_simps(4) mod_add_left_eq of_nat_mod of_nat_numeral)

        show ?thesis using caseone casezero case3_1_assum
          by (metis cong_int cong_mod_right cong_refl diff_le_mono2 nat_le_linear numeral_le_iff
              of_nat_0 of_nat_1 semiring_norm(69) semiring_norm(72))
      qed
      hence case3_1:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case3_1_assum:"N mod m = 0 \<or> N mod m =1" for N using case3_1_assum by metis

      have "\<exists>r::nat.(r\<le>m-3)\<and> [N = b1+r] (mod m)" if case3_2_assum:"N mod m \<ge>2\<and>N mod m \<le> m-1" for N
      proof -
        have "\<exists>r::nat. (r\<le>m-3)\<and>((b1+r) mod m = l)" if asml1:"l\<ge>2 \<and> l\<le>m-1" for l
        proof -
          define r1 where r1_def:"r1 = l-2"
          from asml1 have r1_range:"r1\<ge>0 \<and> r1\<le>m-2" using r1_def by linarith
          have "(2+r1) mod m = l" using asml1 r1_def r1_range by fastforce
          hence "(b1+r1) mod m = l" using case3_assum
            by (metis Num.of_nat_simps(4) mod_add_left_eq of_nat_mod of_nat_numeral)
          thus ?thesis using asml1 r1_range by (metis One_nat_def diff_diff_add diff_le_mono
                nat_1_add_1 numeral_3_eq_3 plus_1_eq_Suc r1_def)
        qed
        thus ?thesis using case3_2_assum
          by (metis case3_2_assum of_nat_mod unique_euclidean_semiring_class.cong_def)
      qed
      hence case3_2:"\<exists>b::int. \<exists>r::nat. (r \<le> m-3) \<and> [N=b+r] (mod m) \<and> (b = b1 \<or> b = b2)"
        if case3_2_assum:"N mod m \<ge>2\<and>N mod m \<le> m-1" for N using case3_2_assum by blast

      have "\<forall>N::nat. N mod m = 0 \<or> (N mod m \<ge>1 \<and> N mod m \<le>m-1)" by (metis Suc_pred' assms(1)
bot_nat_0.not_eq_extremum less_one mod_Suc_le_divisor rel_simps(76) verit_comp_simplify1(3))
      hence "\<forall>N::nat. N mod m = 0 \<or> N mod m = 1 \<or> (N mod m \<ge>2 \<and> N mod m \<le>m-1)"
        by (metis Suc_eq_plus1 le_neq_implies_less le_simps(3) nat_1_add_1)

      thus ?thesis using case3_1 case3_2 by blast
    qed

    show ?thesis using case1 case2 case3 using that by fastforce
  qed

  show ?thesis using first second using assms(1) by force
qed

text\<open>The strong form of Cauchy's polygonal number theorem shows for a natural number $N$ satisfying
certain conditions, it may be written as the sum of $m+1$ polygonal numbers of order $m+2$, at most four
of which are different from 0 or 1. This corresponds to Theorem 1.9 in \cite{nathanson1996}.\<close>

theorem Strong_Form_of_Cauchy_Polygonal_Number_Theorem_1:
  fixes m N :: nat
  assumes "m\<ge>4"
  assumes "N\<ge>108*m"
  shows "\<exists> xs :: nat list. (length xs = m+1) \<and> (sum_list xs = N) \<and> (\<forall>k\<le>3. \<exists>a. xs! k = polygonal_number m a)
  \<and> (\<forall> k \<in> {4..m} . xs! k = 0 \<or> xs! k = 1)"

proof -
  define L where L_def:"L = (2/3 + sqrt (8*N/m - 8)) - (1/2 + sqrt (6*N/m - 3))"
  from assms L_def have "L>4" using interval_length_greater_than_four
    apply(rule_tac N = "of_nat N" and m = "of_nat m" in interval_length_greater_than_four)
    by auto
  define c1 where c1_def:"c1 = \<lceil>1/2 + sqrt (6*N/m - 3)\<rceil>"
  define c2 where c2_def:"c2 = c1+1"
  define c3 where c3_def:"c3 = c1+2"
  define c4 where c4_def:"c4 = c1+3"
  from \<open>L>4\<close> c1_def c2_def c3_def c4_def L_def have "c4<(2/3 + sqrt (8*N/m - 8))" by linarith

  have "N/m \<ge> 108" using assms using le_divide_eq by fastforce
  hence "sqrt(6*N/m - 3)\<ge>1" by simp
  hence "1/2 + sqrt(6*N/m - 3) \<ge>1" by linarith
  hence "c1 \<ge>1" using c1_def by simp

  obtain b1 b2 where bproperties:"{b1, b2} \<subseteq> {c1, c2, c3, c4} \<and> (b2 = b1+2) \<and> odd b1"
    using two_consec_odd c1_def c2_def c3_def c4_def by (metis (no_types, opaque_lifting) Groups.add_ac(2)
empty_subsetI even_plus_one_iff insert_commute insert_mono nat_arith.add1 numeral.simps(2) numeral.simps(3))
  have b1andb2:"odd b1 \<and> b2 = b1+2" using bproperties by auto
  have b1pos:"b1 \<ge>1" using \<open>c1\<ge>1\<close> c2_def c3_def c4_def bproperties by auto
  hence b2pos:"b2 \<ge>3" using bproperties by simp
  have b2odd:"odd b2" using bproperties by simp

  obtain b r where b_r:"r\<le>m-3 \<and> (b = b1 \<or> b = b2) \<and> [int N = b+r] (mod m)" using b1andb2 assms(1)
      cong_classes by meson
  have bpos:"b\<ge>1" using b1pos b2pos b_r by auto
  have bodd:"odd b" using b_r bproperties by auto

  define a where a_def:"a = b+2*(N-b-r) div m"
  have m_div_num:"m dvd (N-b-r)" using b_r
    by (simp add: diff_diff_add mod_eq_dvd_iff unique_euclidean_semiring_class.cong_def)
  hence "(N-b-r)/m = (N-b-r) div m" by (simp add: real_of_int_div)
  hence a_def1:"a = b+2*(N-b-r)/m" using a_def by (metis \<open>int m dvd int N - b - int r\<close>
        dvd_add_right_iff mult_2 of_int_add of_int_of_nat_eq real_of_int_div)
  have "N-m>0" using assms by linarith
  hence "N-r>0" using b_r by force
  hence "(N-b-r) = (N-r)-b" by linarith
  hence "(N-b-r)/m = (N-r)/m - b/m" by (metis diff_divide_distrib int_of_reals(3) of_int_of_nat_eq)
  hence "a = b+2*((N-r)/m - b/m)" using a_def1 by (metis int_of_reals(6) of_int_mult times_divide_eq_right)
  hence a_def2:"a = b- b*2/m+2*(N-r)/m " by simp
  have "b*(1-2/m) = b*1-b*(2/m)" by (simp add: Rings.ring_distribs(4))
  hence a_def3:"a = b*(1-2/m) + 2*(N-r)/m" using a_def2 by simp
  have "1-2/m>0" using assms(1) by simp
  hence size1:"b*(1-2/m)>0" using bpos by simp
  have "N-r>0" using b_r assms by auto
  hence size2:"2*(N-r)/m>0" using assms(1) by simp
  have apos:"a\<ge>1" using size1 size2 a_def3 by simp

  have "odd (b+2*(N-b-r) div m)" using m_div_num b_r b2odd bproperties
    by (metis div_mult_swap zdvd_reduce)
  hence aodd:"odd a" using a_def by simp

  from a_def1 have "a-b = 2*(N-b-r)/m" by simp
  hence "m*(a-b)/2 = N-b-r" using assms(1) by simp
  hence N_expr:"N = r+b+m*(a-b)/2" by simp

  have "b1 \<ge> c1" using bproperties c2_def c3_def c4_def by force
  hence "b1 \<ge> 1/2 + sqrt (6*N/m - 3)" using c1_def using ceiling_le_iff by blast
  have b_ineq1:"b \<ge> 1/2 + sqrt (6*N/m - 3)" using b_r bproperties
    using \<open>1 / 2 + sqrt (real (6 * N) / real m - 3) \<le> real_of_int b1\<close> by fastforce

  have "b2 \<le> c4" using bproperties c1_def c2_def c3_def c4_def by fastforce
  hence "b2 \<le> (2/3 + sqrt (8*N/m - 8))"
    using \<open>real_of_int c4 < 2 / 3 + sqrt (real (8 * N) / real m - 8)\<close> by linarith
  hence b_ineq2:"b\<le>(2/3 + sqrt (8*N/m - 8))" using b_r bproperties by linarith

  define Nr where "Nr = real_of_nat N"
  define mr where "mr = real m"
  define ar where "ar = real_of_int a"
  define br where "br = real_of_int b"
  define rr where "rr = real_of_nat r"
  from assms(1) have "mr \<ge>3" using mr_def by auto
  from assms(2) have "N\<ge>2*m" by simp
  hence "Nr \<ge> 2*mr" using Nr_def mr_def \<open>N \<ge> 2 * m\<close> by auto
  moreover have "br\<ge>0" using br_def bpos by auto
  moreover have "mr\<ge>3" using mr_def assms by auto
  moreover have "ar\<ge>0" using ar_def apos by auto
  moreover have "rr\<ge>0" using rr_def b_r by auto
  moreover have "mr > rr" using mr_def rr_def b_r assms(1) by linarith
  moreover have "Nr = mr*(ar-br)/2+br+rr" using Nr_def mr_def ar_def br_def N_expr rr_def by auto
  moreover have "1/2+sqrt(6*Nr/mr-3)\<le>br \<and> br\<le>2/3+sqrt(8*Nr/mr-8)" using Nr_def mr_def br_def b_ineq1 b_ineq2 by auto
  ultimately have "br^2<4*ar \<and> 3*ar<br^2+2*br+4" using Cauchy_lemma by auto
  hence real_ineq:"(real_of_int b)^2 < 4*(real_of_int a) \<and> 3*(real_of_int a) < (real_of_int b)^2 + 2*(real_of_int b) + 4"
    using br_def ar_def by auto
  hence int_ineq1: "b^2<4*a" using of_int_less_iff by fastforce
  from real_ineq have int_ineq2: "3*a<b^2+2*b+4" using of_int_less_iff by fastforce

  have con1:"nat a \<ge>1" using apos by auto
  have con2:"nat b \<ge>1" using bpos by auto
  have con3:"odd (nat a)" using aodd apos even_nat_iff by auto
  have con4:"odd (nat b)" using bodd bpos even_nat_iff by auto
  have "(nat b)^2 = b^2" using \<open>nat b \<ge>1\<close> by auto
  hence con5:"(nat b)^2<4*(nat a)" using int_ineq1 by linarith
  have con6:"3*(nat a)<(nat b)^2+2*(nat b)+4" using \<open>(nat b)^2 = b^2\<close> int_ineq2 by linarith
  obtain s t u v where stuv:"s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> int(nat a) = s^2 + t^2 + u^2 + v^2 \<and>
  int(nat b) = s+t+u+v" using four_nonneg_int_sum con1 con2 con3 con4 con5 con6 by presburger
  have a_expr:"a = s^2 + t^2 + u^2 + v^2" using apos stuv by linarith
  have b_expr:"b = s+t+u+v" using bpos stuv by linarith

  from N_expr have "N = m/2*(s^2-s+t^2-t+u^2-u+v^2-v)+r+(s+t+u+v)" using a_expr b_expr by simp
  hence N_expr2:"N = m/2*(s^2-s)+ m/2*(t^2-t)+ m/2*(u^2-u)+ m/2*(v^2-v)+ r+(s+t+u+v)"
    by (metis (no_types, opaque_lifting) add_diff_eq nat_distrib(2) of_int_add)
  have s_div2:"m/2*(s^2-s) = m*(s^2-s) div 2" using real_of_int_div by auto
  have t_div2:"m/2*(t^2-t) = m*(t^2-t) div 2" using real_of_int_div by auto
  have u_div2:"m/2*(u^2-u) = m*(u^2-u) div 2" using real_of_int_div by auto
  have v_div2:"m/2*(v^2-v) = m*(v^2-v) div 2" using real_of_int_div by auto
  have N_expr3:"N = (m*(s^2-s) div 2+s)+(m*(t^2-t) div 2+t)+(m*(u^2-u) div 2+u)+(m*(v^2-v) div 2+v)+r"
    using s_div2 t_div2 u_div2 v_div2 N_expr2 by simp

  define sn where "sn = nat s"
  define tn where "tn = nat t"
  define un where "un = nat u"
  define vn where "vn = nat v"
  have seqsn:"s^2-s = sn^2 - sn" using stuv sn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have teqtn:"t^2-t = tn^2 - tn" using stuv tn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have uequn:"u^2-u = un^2 - un" using stuv un_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have veqvn:"v^2-v = vn^2 - vn" using stuv vn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)

  from N_expr3 have
    "N = (m*(sn^2-sn) div 2+s)+(m*(tn^2-tn) div 2+t)+(m*(un^2-un) div 2+u)+(m*(vn^2-vn) div 2+ v)+r"
    using seqsn teqtn uequn veqvn by (metis (mono_tags, lifting) int_ops(2) int_ops(4) int_ops(7)
        numeral_Bit0 numeral_code(1) plus_1_eq_Suc zdiv_int)
  hence "N = (m*(sn^2-sn) div 2+sn)+(m*(tn^2-tn) div 2+tn)+(m*(un^2-un) div 2+un)+(m*(vn^2-vn) div 2+ v)+r"
    using sn_def tn_def un_def  stuv int_nat_eq int_ops(5) by presburger
  hence "N = (m*(sn^2-sn) div 2+sn)+(m*(tn^2-tn) div 2+tn)+(m*(un^2-un) div 2+un)+(m*(vn^2-vn) div 2+ vn)+r"
    using vn_def stuv by (smt (verit, del_insts) Num.of_nat_simps(4) int_nat_eq of_nat_eq_iff)
  hence "N = (m* sn*(sn-1) div 2+sn)+(m*tn*(tn-1) div 2+tn)+(m*un*(un-1) div 2+un)+(m* vn*(vn-1) div 2+ vn)+r"
    by (smt (verit, ccfv_threshold) more_arith_simps(11) mult.right_neutral power2_eq_square right_diff_distrib')
  hence N_expr4:"N = polygonal_number m sn + polygonal_number m tn + polygonal_number m un + polygonal_number m vn +r"
    using Polygonal_Number_Theorem_Gauss.polygonal_number_def by presburger

  define T where T_def:"T = [polygonal_number m sn,polygonal_number m tn,polygonal_number m un,polygonal_number m vn]"
  define ones where ones_def:"ones = replicate r (1::nat)"
  define zeros where zeros_def:"zeros = replicate (m+1-4-r) (0::nat)"
  define final where final_def:"final = T@ones@zeros"

  have "m+1-4-r\<ge>0" using assms(1) b_r by force
  hence "4+r+(m+1-4-r) = m+1" using assms(1) b_r by force
  have "length final = 4+r+(m+1-4-r)" using final_def T_def ones_def zeros_def by auto
  hence final_length:"length final = m+1" using \<open>4+r+(m+1-4-r) = m+1\<close> by simp
  have T_sum:"sum_list T = polygonal_number m sn + polygonal_number m tn + polygonal_number m un + polygonal_number m vn" by (simp add: T_def)
  have ones_sum:"sum_list ones = r" using ones_def by (simp add: sum_list_replicate)
  have zeros_sum:"sum_list zeros = 0" using zeros_def by simp
  have "sum_list final = sum_list T + sum_list ones + sum_list zeros" using final_def by simp
  hence final_sum:"sum_list final = N" using N_expr4 by (simp add: T_sum ones_sum zeros_sum)

  have final_0th:"final! 0 = polygonal_number m sn" using final_def T_def by simp
  have final_1st:"final! 1 = polygonal_number m tn" using final_def T_def by simp
  have final_2nd:"final! 2 = polygonal_number m un" using final_def T_def by simp
  have final_3rd:"final! 3 = polygonal_number m vn" using final_def T_def by simp

  have first_four:"\<forall>k\<le>3. \<exists>a. final! k = polygonal_number m a" using final_0th final_1st final_2nd final_3rd
    by (metis Suc_eq_plus1 add_leD2 arith_simps(50) le_simps(2) numeral_Bit0 numeral_Bit1
        numeral_One verit_comp_simplify1(3) verit_la_disequality)

  have "length T = 4" using T_def by simp
  have "\<forall>k<length (ones@zeros). (ones@zeros)! k =1 \<or>  (ones@zeros)! k =0" using ones_def zeros_def
    by (simp add: nth_append)
  hence "final! k = 1 \<or> final! k = 0" if "k\<ge>4 \<and> k<(length final)" for k
    using \<open>length T = 4\<close> final_def that by (metis add_less_cancel_left le_add_diff_inverse
        length_append nth_append verit_comp_simplify1(3))
  hence other_terms:"\<forall> k \<in> {4..m} . final! k = 0 \<or> final! k = 1" using final_length
    by (metis Suc_eq_plus1 atLeastAtMost_iff le_simps(2))

  show ?thesis using final_length final_sum first_four other_terms by auto
qed


theorem Strong_Form_of_Cauchy_Polygonal_Number_Theorem_2:
  fixes N :: nat
  assumes "N\<ge>324"
  shows "\<exists> p1 p2 p3 p4 r ::nat. N = p1+p2+p3+p4+r \<and> (\<exists>k1. p1 = polygonal_number 3 k1) \<and> (\<exists>k2. p2 = polygonal_number 3 k2)
\<and> (\<exists>k3. p3 = polygonal_number 3 k3) \<and> (\<exists>k4. p4 = polygonal_number 3 k4) \<and> (r = 0 \<or> r = 1)"

proof -
  define L where L_def:"L = (2/3 + sqrt (8*N/3 - 8)) - (1/2 + sqrt (6*N/3 - 3))" (*Now m = 3*)
  from assms L_def have "L>4" using interval_length_greater_than_four
    apply -
    apply(rule interval_length_greater_than_four[where N = "of_nat N" and m = "of_nat 3"])
    by auto
  define c1 where c1_def:"c1 = \<lceil>1/2 + sqrt (6*N/3 - 3)\<rceil>"
  define c2 where c2_def:"c2 = c1+1"
  define c3 where c3_def:"c3 = c1+2"
  define c4 where c4_def:"c4 = c1+3"
  from \<open>L>4\<close> c1_def c2_def c3_def c4_def L_def have "c4<(2/3 + sqrt (8*N/3 - 8))" by linarith

  define Nn where "Nn = int N"
  have "c4<(2/3 + sqrt (8*Nn/3 - 8))" using Nn_def \<open>c4<(2/3 + sqrt (8*N/3 - 8))\<close> by simp
  have Nn3:"(Nn-3)^2 - (sqrt (8*Nn/3 - 8))^2 = Nn^2-3*Nn-3*Nn+9 - (sqrt (8*Nn/3 - 8))^2"
    using assms Nn_def power2_diff by (simp add: power2_eq_square algebra_simps)
  have "(Nn-3)^2 - (sqrt (8*Nn/3 - 8))^2 = Nn^2-3*Nn-3*Nn+9 - (8*Nn/3 - 8)" using assms Nn_def Nn3 by fastforce
  hence "(Nn-3)^2 - (sqrt (8*Nn/3 - 8))^2 = Nn^2-6*Nn+9-8*Nn/3 +8" by linarith
  hence Nn4:"(Nn-3)^2 - (sqrt (8*Nn/3 - 8))^2 = Nn*(Nn-26/3)+17" by (simp add: Rings.ring_distribs(4) power2_eq_square)
  have "Nn*(Nn-26/3)+17>17" using assms Nn_def by auto
  hence "(Nn-3)^2 - (sqrt (8*Nn/3 - 8))^2 > 0" using Nn4 by auto
  hence "Nn-3 > sqrt (8*Nn/3 - 8)" using assms Nn_def by (simp add: real_less_lsqrt)
  hence "Nn-2 > sqrt (8*Nn/3 - 8)+2/3" by linarith
  hence "N > c4" using Nn_def \<open>c4<(2/3 + sqrt (8*Nn/3 - 8))\<close> by simp

  have "N/3 \<ge> 108" using assms using le_divide_eq by fastforce
  hence "sqrt(6*N/3 - 3)\<ge>1" by simp
  hence "1/2 + sqrt(6*N/3 - 3) \<ge>1" by linarith
  hence "c1 \<ge>1" using c1_def by simp

  obtain b1 b2 where bproperties:"{b1, b2} \<subseteq> {c1, c2, c3, c4} \<and> (b2 = b1+2) \<and> odd b1"
    using two_consec_odd c1_def c2_def c3_def c4_def by (metis (no_types, opaque_lifting) Groups.add_ac(2)
empty_subsetI even_plus_one_iff insert_commute insert_mono nat_arith.add1 numeral.simps(2) numeral.simps(3))
  have b1andb2:"odd b1 \<and> b2 = b1+2" using bproperties by auto
  have b1pos:"b1 \<ge>1" using \<open>c1\<ge>1\<close> c2_def c3_def c4_def bproperties by auto
  hence b2pos:"b2 \<ge>3" using bproperties by simp
  have b2odd:"odd b2" using bproperties by simp
  define b1n where "b1n = nat b1"
  define b2n where "b2n = nat b2"

  from b1n_def b1pos have "b1n mod 3 = b1 mod 3" using int_ops(9) by force
  from b2n_def b2pos have "b2n mod 3 = b2 mod 3" using int_ops(9) by force

  have b_and_r:"\<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
  proof -
    have case1:"\<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
      if asm1:"b1 mod 3 = 0"
    proof -
      have "b1n mod 3 = 0" using asm1 \<open>b1n mod 3 = b1 mod 3\<close> by simp
      hence "b2n mod 3 = 2" using \<open>b2n mod 3 = b2 mod 3\<close> bproperties asm1 by fastforce
      have case1_1:"[0 = b1n+0] (mod 3)" using \<open>b1n mod 3 = 0\<close>
        by (metis mod_0 nat_arith.rule0 unique_euclidean_semiring_class.cong_def)
      have case1_2:"[1 = b1n+1] (mod 3)" using \<open>b1n mod 3 = 0\<close>
        by (metis \<open>[0 = b1n + 0] (mod 3)\<close> add.commute cong_add_lcancel_0_nat cong_sym)
      have case1_3:"[2 = b2n+0] (mod 3)" using \<open>b2n mod 3 = 2\<close>
        by (simp add: unique_euclidean_semiring_class.cong_def)
      have "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 \<ge> 1" by linarith
      hence "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 = 1 \<or> N mod 3 = 2" by linarith
      hence "\<forall>N. \<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
        if asm1:"b1 mod 3 = 0" using case1_1 case1_2 case1_3 by (metis cong_mod_left)
      thus ?thesis using asm1 by auto
    qed

    have case2:"\<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
      if asm2:"b1 mod 3 = 1"
    proof -
      have "b1n mod 3 = 1" using asm2 \<open>b1n mod 3 = b1 mod 3\<close> by simp
      hence "b2n mod 3 = 0" using \<open>b2n mod 3 = b2 mod 3\<close> bproperties asm2
        by (smt (verit, best) Euclidean_Rings.pos_mod_bound Euclidean_Rings.pos_mod_sign
            int_ops(1) mod_diff_eq mod_pos_pos_trivial of_nat_eq_iff)
      have case2_1:"[0 = b2n+0] (mod 3)" using \<open>b2n mod 3 = 0\<close>
        by (metis mod_0 nat_arith.rule0 unique_euclidean_semiring_class.cong_def)
      have case2_2:"[1 = b1n+0] (mod 3)" using \<open>b1n mod 3 = 1\<close>
        by (simp add: unique_euclidean_semiring_class.cong_def)
      have case2_3:"[2 = b1n+1] (mod 3)" using \<open>b1n mod 3 = 1\<close>
        by (metis case2_2 cong_add_rcancel_nat nat_1_add_1 nat_arith.rule0)
      have "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 \<ge> 1" by linarith
      hence "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 = 1 \<or> N mod 3 = 2" by linarith
      hence "\<forall>N. \<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
        if asm2:"b1 mod 3 = 1" using case2_1 case2_2 case2_3 by (metis cong_mod_left)
      thus ?thesis using asm2 by auto
    qed

    have case3:"\<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
      if asm3:"b1 mod 3 = 2"
    proof -
      have "b1n mod 3 = 2" using asm3 \<open>b1n mod 3 = b1 mod 3\<close> by simp
      have "(b1+2) mod 3 = (2+2) mod 3" using asm3 by (metis Groups.add_ac(2) mod_add_right_eq)
      hence "b2n mod 3 = 1" using \<open>b2n mod 3 = b2 mod 3\<close> bproperties by simp
      have case3_1:"[0 = b1n+1] (mod 3)" using \<open>b1n mod 3 = 2\<close>
        by (metis One_nat_def add.commute mod_0 mod_add_right_eq mod_self nat_1_add_1 numeral_3_eq_3
            plus_1_eq_Suc unique_euclidean_semiring_class.cong_def)
      have case3_2:"[1 = b2n+0] (mod 3)" using \<open>b2n mod 3 = 1\<close>
        by (simp add: unique_euclidean_semiring_class.cong_def)
      have case3_3:"[2 = b1n+0] (mod 3)" using \<open>b1n mod 3 = 2\<close>
        by (simp add: unique_euclidean_semiring_class.cong_def)
      have "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 \<ge> 1" by linarith
      hence "\<forall>N::nat. N mod 3 = 0 \<or> N mod 3 = 1 \<or> N mod 3 = 2" by linarith
      hence "\<forall>N. \<exists>b r::nat. [N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
        if asm3:"b1 mod 3 = 2" using case3_1 case3_2 case3_3 by (metis cong_mod_left)
      thus ?thesis using asm3 by auto
    qed

    have "b1 mod 3 = 0 \<or> b1 mod 3 = 1 \<or> b1 mod 3 = 2" by auto
    thus ?thesis using case1 case2 case3 by auto
  qed

  obtain b r where b_r:"[N = b+r] (mod 3) \<and> (b = b1n \<or> b = b2n) \<and> (r = 0 \<or> r = 1)"
    using b_and_r by auto

  have bpos:"b\<ge>1" using b1pos b2pos b_r b1n_def b2n_def by auto
  have bodd:"odd b"
    using b_r bproperties by (metis b1n_def b2n_def b2odd bpos even_nat_iff nat_eq_iff2 rel_simps(45))

  define a where a_def:"a = b+2*(N-b-r) div 3"
  have "int b1n = b1" using b1n_def b1pos by linarith
  have "int b2n = b2" using b2n_def b2pos by linarith
  have m_div_num:"3 dvd (N-b-r)" using b_r
    by (metis cong_altdef_nat diff_diff_left diff_is_0_eq' dvd_0_right nat_le_linear)
  hence a_def1:"a = b+2*(N-b-r)/3" using a_def m_div_num real_of_nat_div by auto
  from \<open>N>c4\<close> have "N>b" using b_r bproperties b1n_def b2n_def
    by (smt (verit, del_insts) \<open>int b1n = b1\<close> \<open>int b2n = b2\<close> c2_def c3_def c4_def empty_iff insert_iff insert_subset of_nat_less_imp_less)
  hence "(N-b-r)/3 = (N-r)/3 - b/3" using \<open>b < N\<close> b_r by force
  hence "a = b- b*2/3+2*(N-r)/3" using a_def1 by linarith
  hence a_def3:"a = b*(1-2/3) + 2*(N-r)/3" by simp

  have size1:"b*(1-2/3)>0" using bpos by simp
  have "N-r>0" using b_r assms by auto
  hence size2:"2*(N-r)/3>0" using assms(1) by simp
  have apos:"a\<ge>1" using size1 size2 a_def3 by simp

  have "odd (b+2*(N-b-r) div 3)" using m_div_num b_r b2odd bproperties by (simp add: bodd mult_2)
  hence aodd:"odd a" using a_def by simp
  from a_def1 have "a-b = 2*(N-b-r)/3" by simp
  hence "(a-b)/2 = (N-b-r)/3" by simp
  hence "3*(a-b)/2 = N-b-r"  by simp
  have "N-b-r\<ge>0" using b_r by simp
  hence N_expr:"N = r+b+3*(a-b)/2" using \<open>N-b-r\<ge>0\<close>  \<open>b < N\<close> b_r \<open>real (3 * (a - b)) / 2 = real (N - b - r)\<close> by linarith
  from a_def \<open>N-b-r\<ge>0\<close> have "a\<ge>b" using a_def le_add1 by blast

  have "b1 \<ge> c1" using bproperties c2_def c3_def c4_def by force
  hence "b1 \<ge> 1/2 + sqrt (6*N/3 - 3)" using c1_def using ceiling_le_iff by blast
  hence b1ngreater:"b1n \<ge> 1/2 + sqrt (6*N/3 - 3)" using b1n_def by simp
  hence b2ngreater:"b2n \<ge> 1/2 + sqrt (6*N/3 - 3)" using bproperties b1n_def b2n_def by linarith
  hence b_ineq1:"b \<ge> 1/2 + sqrt (6*N/3 - 3)" using b_r b1ngreater by auto

  have "b2 \<le> c4" using bproperties c1_def c2_def c3_def c4_def by fastforce
  hence "b2 \<le> (2/3 + sqrt (8*N/3 - 8))"
    using \<open>real_of_int c4 < 2 / 3 + sqrt (real (8 * N) / 3 - 8)\<close> by linarith
  hence b2nsmaller:"b2n \<le> (2/3 + sqrt (8*N/3 - 8))" using b2n_def by (metis \<open>int b2n = b2\<close> of_int_of_nat_eq)
  hence "b1n \<le> (2/3 + sqrt (8*N/3 - 8))" using b1n_def bproperties using \<open>int b2n = b2\<close> by linarith
  hence b_ineq2:"b\<le>(2/3 + sqrt (8*N/3 - 8))" using b_r b2nsmaller by auto

  define Nr where "Nr = real_of_nat N"
  define ar where "ar = real_of_int a"
  define br where "br = real_of_int b"
  define rr where "rr = real_of_nat r"
  define m where "m = real_of_nat 3"
  from assms have "N\<ge>2*m" using m_def by simp
  then have "Nr \<ge> 2*m" using Nr_def  \<open>N \<ge> 2 * m\<close> by auto
  moreover have "br\<ge>0" using br_def bpos by auto
  moreover have "ar\<ge>0" using ar_def apos by auto
  moreover have "rr\<ge>0" using rr_def b_r by auto
  moreover have "m\<ge>3" using m_def by auto
  moreover have "m>rr" using m_def rr_def b_r by auto
  moreover have "Nr = m*(ar-br)/2+br+rr" using Nr_def ar_def br_def N_expr rr_def m_def \<open>a\<ge>b\<close> by auto
  moreover have "1/2+sqrt(6*Nr/m-3)\<le>br \<and> br\<le>2/3+sqrt(8*Nr/m-8)" using Nr_def  br_def b_ineq1 b_ineq2 m_def by auto
  ultimately have "br^2<4*ar \<and> 3*ar<br^2+2*br+4" using Cauchy_lemma by auto
  hence real_ineq:"(real_of_int b)^2 < 4*(real_of_int a) \<and> 3*(real_of_int a) < (real_of_int b)^2 + 2*(real_of_int b) + 4"
    using br_def ar_def by auto
  hence nat_ineq1: "b^2<4*a" using br_def  by (smt (verit, del_insts) Num.of_nat_simps(4)
mult.commute mult_2_right nat_distrib(1) numeral_Bit0 of_int_of_nat_eq of_nat_less_of_nat_power_cancel_iff)
  from real_ineq have nat_ineq2: "3*a<b^2+2*b+4" using ar_def br_def of_nat_less_iff by fastforce

  obtain s t u v where stuv:"s \<ge> 0 \<and> t \<ge> 0 \<and> u \<ge> 0 \<and> v \<ge> 0 \<and> int a = s^2 + t^2 + u^2 + v^2 \<and>
 int b = s+t+u+v" using apos bpos aodd bodd nat_ineq1 nat_ineq2 four_nonneg_int_sum by presburger
  have a_expr:"a = s^2 + t^2 + u^2 + v^2" using apos stuv by linarith
  have b_expr:"b = s+t+u+v" using bpos stuv by linarith

  have "N = r + (s+t+u+v)+ 3*(a-(s+t+u+v))/2" using b_expr N_expr
    by (metis Num.of_nat_simps(4) Num.of_nat_simps(5) \<open>b \<le> a\<close> of_int_of_nat_eq of_nat_diff of_nat_numeral)
  hence "N = 3/2*(s^2-s+t^2-t+u^2-u+v^2-v)+r+(s+t+u+v)" using a_expr by simp
  hence N_expr2:"N = 3/2*(s^2-s)+ 3/2*(t^2-t)+ 3/2*(u^2-u)+ 3/2*(v^2-v)+ r+(s+t+u+v)"
    by (metis (no_types, opaque_lifting) add_diff_eq nat_distrib(2) of_int_add)

  have s_div2:"3/2*(s^2-s) = 3*(s^2-s) div 2" using real_of_int_div by auto
  have t_div2:"3/2*(t^2-t) = 3*(t^2-t) div 2" using real_of_int_div by auto
  have u_div2:"3/2*(u^2-u) = 3*(u^2-u) div 2" using real_of_int_div by auto
  have v_div2:"3/2*(v^2-v) = 3*(v^2-v) div 2" using real_of_int_div by auto
  have N_expr3:"N = (3*(s^2-s) div 2+s)+(3*(t^2-t) div 2+t)+(3*(u^2-u) div 2+u)+(3*(v^2-v) div 2+v)+r"
    using N_expr2 s_div2 t_div2 u_div2 v_div2 by simp

  define sn where "sn = nat s"
  define tn where "tn = nat t"
  define un where "un = nat u"
  define vn where "vn = nat v"
  have seqsn:"s^2-s = sn^2 - sn" using stuv sn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have teqtn:"t^2-t = tn^2 - tn" using stuv tn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have uequn:"u^2-u = un^2 - un" using stuv un_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)
  have veqvn:"v^2-v = vn^2 - vn" using stuv vn_def
    by (metis int_nat_eq le_refl of_nat_diff of_nat_power power2_nat_le_imp_le)

  from N_expr3 have
    "N = (3*(sn^2-sn) div 2+s)+(3*(tn^2-tn) div 2+t)+(3*(un^2-un) div 2+u)+(3*(vn^2-vn) div 2+ v)+r"
    using seqsn teqtn uequn veqvn
    by (metis (mono_tags, lifting) Num.of_nat_simps(5) of_nat_numeral zdiv_int)
  hence "N = (3*(sn^2-sn) div 2+sn)+(3*(tn^2-tn) div 2+tn)+(3*(un^2-un) div 2+un)+(3*(vn^2-vn) div 2+ v)+r"
    using sn_def tn_def un_def  stuv int_nat_eq int_ops(5) by presburger
  hence "N = (3*(sn^2-sn) div 2+sn)+(3*(tn^2-tn) div 2+tn)+(3*(un^2-un) div 2+un)+(3*(vn^2-vn) div 2+ vn)+r"
    using vn_def stuv by (smt (verit, del_insts) Num.of_nat_simps(4) int_nat_eq of_nat_eq_iff)
  hence "N = (3* sn*(sn-1) div 2+sn)+(3*tn*(tn-1) div 2+tn)+(3*un*(un-1) div 2+un)+(3* vn*(vn-1) div 2+ vn)+r"
    by (smt (verit, ccfv_threshold) more_arith_simps(11) mult.right_neutral power2_eq_square right_diff_distrib')
  hence N_expr4:"N = polygonal_number 3 sn + polygonal_number 3 tn + polygonal_number 3 un + polygonal_number 3 vn +r"
    using Polygonal_Number_Theorem_Gauss.polygonal_number_def by presburger

  define p1 where "p1 = polygonal_number 3 sn"
  define p2 where "p2 = polygonal_number 3 tn"
  define p3 where "p3 = polygonal_number 3 un"
  define p4 where "p4 = polygonal_number 3 vn"
  have N_expr5:"N = p1 + p2 + p3 + p4 + r" using N_expr4 p1_def p2_def p3_def p4_def by auto
  thus ?thesis using p1_def p2_def p3_def p4_def b_r by blast
qed
end