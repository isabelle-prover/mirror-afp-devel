theory Alternative_Proofs
  imports Smith_Normal_Form.Admits_SNF_From_Diagonal_Iff_Bezout_Ring
          Smith_Normal_Form.Elementary_Divisor_Rings
begin


text \<open>Theorem 2: (C) ==> (A)\<close>

lemma diagonal_2x2_admits_SNF_imp_bezout_ring_JNF:
  assumes admits_SNF: "\<forall>A. (A::'a mat) \<in> carrier_mat 2 2 \<and> isDiagonal_mat A
  \<longrightarrow> (\<exists>P Q. P \<in> carrier_mat 2 2 \<and> Q \<in> carrier_mat 2 2 \<and> invertible_mat P \<and> invertible_mat Q 
      \<and> Smith_normal_form_mat (P*A*Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (intro_classes)
  fix a b::'a
  show "\<exists>p q d. p * a + q * b = d \<and> d dvd a \<and> d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)"
  proof (cases "a=b")
    case True
    show ?thesis
      by (metis True add.right_neutral comm_semiring_class.distrib dvd_refl mult_1)
  next
    case False note a_not_b = False
    let ?A = "Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a else if i = 1 \<and> j = 1 then b else 0)"
    have A_carrier: "?A \<in> carrier_mat 2 2" by auto
    moreover have diag_A: "isDiagonal_mat ?A" by (simp add: isDiagonal_mat_def)
    ultimately obtain P Q where P: "P \<in> carrier_mat 2 2" 
        and Q: "Q \<in> carrier_mat 2 2" and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q"
        and SNF_PAQ: "Smith_normal_form_mat (P*?A*Q)" 
      using admits_SNF by blast 
    let ?p = "P$$(0,0)*Q$$(0,0)"
    let ?q = "P$$(0,1)*Q$$(1,0)"
    let ?d = "(P*?A*Q) $$ (0,0)"
    let ?d' = "(P*?A*Q) $$ (1,1)"
    have d_dvd_d': "?d dvd ?d'" 
      by (metis (no_types, lifting) A_carrier One_nat_def P Q SNF_PAQ SNF_first_divides_all bot_nat_0.not_eq_extremum
          less_Suc_numeral mult_carrier_mat pred_numeral_simps(2) zero_neq_numeral)
    have pa_qb_d: "?p*a + ?q * b = ?d"
    proof -
      let ?U = "P*?A"
      have "?U $$ (0, 0) = P $$ (0,0)* ?A $$ (0,0) + P $$ (0,1)* ?A $$ (1,0)" 
        by (rule mat_mult2_00, insert P, auto)
      also have "... = P $$ (0,0) * a" by auto
      finally have 1: "(P*?A) $$ (0, 0) = P $$ (0,0) * a" .
      have "?U $$ (0, 1) = P $$ (0,0)* ?A $$ (0,1) + P $$ (0,1)* ?A $$ (1,1)"
        by (rule mat_mult2_01, insert P, auto)
      hence 2: "(P*?A) $$ (0, 1)= P $$ (0,1)* b" by auto
      have "?d = ?U $$ (0, 0) * Q $$ (0, 0) + ?U $$ (0, 1) * Q $$ (1, 0)"
        by (rule mat_mult2_00, insert Q P, auto)
      also have "... = ?p*a + ?q * b" unfolding 1 unfolding 2 by auto
      finally show ?thesis ..
    qed    
    have i: "ideal_generated {a, b} = ideal_generated {?d}" 
    proof
      show "ideal_generated {?d} \<subseteq> ideal_generated {a, b}"
      proof (rule ideal_generated_subset2, rule ballI, simp)
        fix x 
        let ?f = "\<lambda>x. if x = a then ?p else ?q"
        show "?d \<in> ideal_generated {a, b}"        
          unfolding ideal_explicit 
          by simp (rule exI[of _ ?f], rule exI[of _ "{a,b}"], 
                  insert a_not_b One_nat_def pa_qb_d, auto)  
      qed
      show "ideal_generated {a, b}  \<subseteq> ideal_generated {?d}" 
      proof -
        obtain P' where inverts_mat_P': "inverts_mat P P' \<and> inverts_mat P' P" 
            using inv_P unfolding invertible_mat_def by auto
          have P': "P' \<in> carrier_mat 2 2" 
            using inverts_mat_P' 
            unfolding carrier_mat_def inverts_mat_def
            by (auto,metis P carrier_matD index_mult_mat(3) one_carrier_mat)+
          obtain Q' where inverts_mat_Q': "inverts_mat Q Q' \<and> inverts_mat Q' Q"
            using inv_Q unfolding invertible_mat_def by auto
          have Q': "Q' \<in> carrier_mat 2 2" 
            using inverts_mat_Q'
            unfolding carrier_mat_def inverts_mat_def
            by (auto,metis Q carrier_matD index_mult_mat(3) one_carrier_mat)+
          have rw_PAQ: "(P'*(P*?A*Q)*Q') $$ (i, i) = ?A $$ (i,i)" for i 
            using inv_P'PAQQ'[OF A_carrier P _ _ Q P' Q'] inverts_mat_P' inverts_mat_Q' by auto
          have diag_PAQ: "isDiagonal_mat (P*?A*Q)" 
            using SNF_PAQ unfolding Smith_normal_form_mat_def by auto
          have PAQ_carrier: "(P*?A*Q) \<in> carrier_mat 2 2" using P Q by auto
          have z1: "0<(2::nat)" and z2: "1<(2::nat)" by auto        
          obtain f where f: "(P'*(P*?A*Q)*Q') $$ (0, 0) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). f i * i)"          
            using exists_f_PAQ_Aii[OF diag_PAQ P' PAQ_carrier Q' z1] by blast
          obtain g where g: "(P'*(P*?A*Q)*Q') $$ (1, 1) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). g i * i)"          
            using exists_f_PAQ_Aii[OF diag_PAQ P' PAQ_carrier Q' z2] by blast
          have A00: "?A $$ (0, 0) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). f i * i)"
            using rw_PAQ[of 0] using f by presburger
          have A11: "?A $$ (1, 1) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). g i * i)"
            using rw_PAQ[of 1] using g by presburger
          have d_dvd_a: "?d dvd a" using A00 d_dvd_d'
            by (auto, smt (verit, best) A00 A_carrier P Q S00_dvd_all_A SNF_PAQ inv_P inv_Q 
                numeral_2_eq_2 zero_less_Suc)
          have d_dvd_b: "?d dvd b" using A11 d_dvd_d'
            by (smt (verit, ccfv_threshold) A_carrier One_nat_def P Q S00_dvd_all_A SNF_PAQ 
                index_mat(1) inv_P inv_Q lessI nat.simps(3) numeral_2_eq_2 split_conv)
        have 1: "a \<in> ideal_generated {?d}" and 2: "b \<in> ideal_generated {?d}"
          using d_dvd_a d_dvd_b dvd_ideal_generated_singleton' ideal_generated_subset_generator
          by blast+
        show ?thesis by (rule ideal_generated_subset2, insert 1 2, auto)
      qed
    qed
    have "\<exists> p q. p * a + q * b = ?d" by (rule ideal_generated_pair_exists[OF i])
    moreover have d_dvd_a: "?d dvd a" and d_dvd_b: "?d dvd b"
      using i ideal_generated_singleton_dvd by blast+
    moreover have "(\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd ?d)" using ideal_generated_dvd[OF i] by auto
    ultimately show ?thesis
      by blast
  qed
qed


text \<open>Theorem 2: (A) ==> (C)\<close>

lemma bezout_ring_imp_diagonal_2x2_admits_SNF_JNF:
  assumes c: "OFCLASS('a::comm_ring_1, bezout_ring_class)"
  shows "\<forall>A. (A::'a mat) \<in> carrier_mat 2 2 \<and> isDiagonal_mat A
  \<longrightarrow> (\<exists>P Q. P \<in> carrier_mat 2 2 \<and> Q \<in> carrier_mat 2 2 
      \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat (P*A*Q))"  
  using bezout_ring_imp_diagonal_admits_SNF_JNF
      [OF OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a, OF c]]
  unfolding admits_SNF_JNF_def
  using \<open>\<forall>A. admits_SNF_JNF A\<close> admits_SNF_JNF_alt_def by blast


text \<open>Theorem 2: (A) <==> (C)\<close>

lemma diagonal_2x2_admits_SNF_iff_bezout_ring: 
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class) 
    \<equiv> (\<And>A::'a mat. A \<in> carrier_mat 2 2 \<longrightarrow> admits_SNF_JNF A)" (is "?lhs \<equiv> ?rhs")
proof 
  fix A::"'a mat"
  assume c: "OFCLASS('a, bezout_ring_class)"
  show "A \<in> carrier_mat 2 2 \<longrightarrow> admits_SNF_JNF A"
    using bezout_ring_imp_diagonal_admits_SNF_JNF
          [OF OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a, OF c]]
    unfolding admits_SNF_JNF_def by blast
next
  assume rhs: "(\<And>A::'a mat. A \<in> carrier_mat 2 2 \<longrightarrow> admits_SNF_JNF A)"
  show "OFCLASS('a::comm_ring_1, bezout_ring_class)"
    by (rule diagonal_2x2_admits_SNF_imp_bezout_ring_JNF, insert rhs, simp add: admits_SNF_JNF_def) 
qed

text \<open>Theorem 2: (B) <==> (C)\<close>
lemma diagonal_2x2_admits_SNF_iff_diagonal_admits_SNF:
  shows "(\<forall>(A::'a::comm_ring_1 mat). admits_SNF_JNF A) =
      (\<forall>(A::'a mat) \<in> carrier_mat 2 2. admits_SNF_JNF A)"
proof 
 assume "\<forall>A::'a mat. admits_SNF_JNF A"
  thus "\<forall>(A::'a mat)\<in>carrier_mat 2 2. admits_SNF_JNF A" 
    by (insert admits_SNF_JNF_alt_def, blast)
next
  assume "\<forall>A::'a mat \<in>carrier_mat 2 2. admits_SNF_JNF A "
  hence H: "OFCLASS('a, bezout_ring_class)"
    using diagonal_2x2_admits_SNF_iff_bezout_ring[where ?'a = 'a] by auto  
  show "\<forall>A::'a mat. admits_SNF_JNF A" 
    using bezout_ring_imp_diagonal_admits_SNF_JNF
      [OF OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a, OF H]]
    by simp
qed

text \<open>Theorem 2: final statements\<close>

theorem Theorem2_final:
  shows A_imp_B: "OFCLASS('a::comm_ring_1, bezout_ring_class) 
    \<Longrightarrow> (\<forall>A::'a mat. admits_SNF_JNF A)"
  and B_imp_C: "(\<forall>A::'a mat. admits_SNF_JNF A) \<Longrightarrow> 
      (\<forall>(A::'a mat) \<in> carrier_mat 2 2. admits_SNF_JNF A)"
  and C_imp_A: "(\<forall>(A::'a mat) \<in> carrier_mat 2 2. admits_SNF_JNF A) 
    \<Longrightarrow> OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof
  fix A::"'a mat"
  assume H: "OFCLASS('a, bezout_ring_class)"
  show "admits_SNF_JNF A"
    using bezout_ring_imp_diagonal_admits_SNF_JNF[OF OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a, OF H]]
    by simp
next
  assume "\<forall>A::'a mat. admits_SNF_JNF A"
  thus "\<forall>(A::'a mat)\<in>carrier_mat 2 2. admits_SNF_JNF A" 
    by (insert admits_SNF_JNF_alt_def, blast)
next
  assume "\<forall>(A::'a mat)\<in>carrier_mat 2 2. admits_SNF_JNF A" 
  thus "OFCLASS('a, bezout_ring_class)"
    using diagonal_2x2_admits_SNF_iff_bezout_ring[where ?'a = 'a] by auto
qed


theorem Theorem2_final':
  shows A_eq_B: "OFCLASS('a::comm_ring_1, bezout_ring_class) \<equiv> (\<And>A::'a mat. admits_SNF_JNF A)"
  and A_eq_C: "OFCLASS('a::comm_ring_1, bezout_ring_class) \<equiv>
      (\<And>(A::'a mat). A \<in> carrier_mat 2 2 \<longrightarrow> admits_SNF_JNF A)"
  and B_eq_C: "(\<forall>(A::'a::comm_ring_1 mat). admits_SNF_JNF A) =
      (\<forall>(A::'a mat) \<in> carrier_mat 2 2. admits_SNF_JNF A)"
  using diagonal_admits_SNF_iff_bezout_ring' 
  using diagonal_2x2_admits_SNF_iff_bezout_ring
  using diagonal_2x2_admits_SNF_iff_diagonal_admits_SNF by auto

text \<open>Theorem 2: final statement in HA. (A) <==> (C).\<close>

theorem Theorem2_A_eq_C_HA:
   "OFCLASS('a::comm_ring_1, bezout_ring_class) \<equiv> (\<And>(A::'a^2^2). admits_SNF_HA A)"
proof 
  fix A::"'a^2^2"
  assume H: "OFCLASS('a, bezout_ring_class)"
  let ?A = "Mod_Type_Connect.from_hma\<^sub>m A" 
  have A: "?A \<in> carrier_mat 2 2" by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?A A" 
    unfolding Mod_Type_Connect.HMA_M_def A by auto
  have "admits_SNF_JNF ?A" using A_imp_B[OF H] by auto
  thus "admits_SNF_HA A" by transfer'
next
  assume a: "(\<And>A::'a^2^2. admits_SNF_HA A)"
  have [transfer_rule]: "Mod_Type_Connect.HMA_M (Mod_Type_Connect.from_hma\<^sub>m A) A" for A::"'a^2^2" 
    unfolding Mod_Type_Connect.HMA_M_def by auto
  have a': "(\<And>A::'a^2^2. admits_SNF_JNF (Mod_Type_Connect.from_hma\<^sub>m A))" 
  proof -
    fix A::"'a^2^2"
    have ad: "admits_SNF_HA A" using a by simp
    let ?A = "Mod_Type_Connect.from_hma\<^sub>m A" 
    have A: "?A \<in> carrier_mat 2 2" by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_M ?A A" 
      unfolding Mod_Type_Connect.HMA_M_def A by auto
    show "admits_SNF_JNF (Mod_Type_Connect.from_hma\<^sub>m A)" using ad by transfer'
  qed
  have "(\<forall>A::'a^2^2. admits_SNF_JNF (Mod_Type_Connect.from_hma\<^sub>m A)) 
    = (\<forall>(A::'a mat)\<in>carrier_mat 2 2. admits_SNF_JNF A)" 
  proof (auto)
    fix A::"'a mat" assume a1: "\<forall>A::'a^2^2. admits_SNF_JNF (Mod_Type_Connect.from_hma\<^sub>m A)" 
      and "A \<in> carrier_mat 2 2" 
    thus "admits_SNF_JNF A" by (metis Mod_Type_Connect.from_hma_to_hma\<^sub>m One_nat_def  UNIV_1 a1 
          card.empty card.insert card_bit0 empty_iff finite mult.right_neutral)
  next
    fix A::"'a^2^2" assume "\<forall>A\<in>carrier_mat 2 2. admits_SNF_JNF A"
    have ad: "admits_SNF_HA A" using a by simp
    let ?A = "Mod_Type_Connect.from_hma\<^sub>m A" 
    have A: "?A \<in> carrier_mat 2 2" by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_M ?A A" 
      unfolding Mod_Type_Connect.HMA_M_def A by auto
    show "admits_SNF_JNF (Mod_Type_Connect.from_hma\<^sub>m A)" using ad by transfer'
  qed
  hence "(\<And>A::'a mat. A \<in> carrier_mat 2 2 \<longrightarrow> admits_SNF_JNF A)" using a' by auto
  thus "OFCLASS('a, bezout_ring_class)" using Theorem2_final'[where ?'a='a] by auto
qed


text \<open>Hermite implies Bezout\<close>

text \<open>Theorem 3, proof for 1x2 matrices\<close>
lemma theorem3_restricted_12_part1:
  assumes T: "(\<forall>a b::'a::comm_ring_1. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d 
    \<and> ideal_generated {a1,b1} = ideal_generated {1})"
  shows "\<forall>(A::'a mat) \<in> carrier_mat 1 2. admits_triangular_reduction A"
proof (rule)
  fix A::"'a mat"
  assume A: "A \<in> carrier_mat 1 2"
  let ?a = "A $$ (0,0)"
  let ?b = "A $$ (0,1)"
  obtain a1 b1 d where a: "?a = a1*d" and b: "?b = b1*d" 
    and i: "ideal_generated {a1,b1} = ideal_generated {1}" 
    using T by blast
  obtain s t where sa1tb1:"s*a1+t*b1=1" using ideal_generated_pair_exists_pq1[OF i[simplified]] by blast
  let ?Q = "Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then s else
                                    if  i = 0 \<and> j = 1 then -b1 else
                                    if  i = 1 \<and> j = 0 then t else a1)"
  have Q: "?Q \<in> carrier_mat 2 2" by auto
  have det_Q: "Determinant.det ?Q = 1" unfolding det_2[OF Q] 
    using sa1tb1 by (simp add: mult.commute)
  hence inv_Q: "invertible_mat ?Q" using invertible_iff_is_unit_JNF[OF Q] by auto
  have lower_AQ: "lower_triangular (A*?Q)" 
  proof -
    have "Matrix.row A 0 $v Suc 0 * a1 = Matrix.row A 0 $v 0 * b1" if j2: "j<2" and j0: "0<j" for j
      by (metis A One_nat_def a b carrier_matD(1) carrier_matD(2) index_row(1) lessI 
          more_arith_simps(11) mult.commute numeral_2_eq_2 pos2)
    thus ?thesis unfolding lower_triangular_def using A 
      by (auto simp add: scalar_prod_def sum_two_rw)
  qed
  show "admits_triangular_reduction A" 
    unfolding admits_triangular_reduction_def using lower_AQ inv_Q Q A by force    
qed


lemma theorem3_restricted_12_part2:
  assumes 1: "\<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat 1 2. admits_triangular_reduction A"
  shows "\<forall>a b::'a. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1}"
proof (rule allI)+
  fix a b::'a
  let ?A = "Matrix.mat 1 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a else b)"
  obtain Q where AQ: "lower_triangular (?A*Q)" and inv_Q: "invertible_mat Q"
    and Q: "Q \<in> carrier_mat 2 2"
    using 1 unfolding admits_triangular_reduction_def by fastforce
  hence [simp]: "dim_col Q = 2" and [simp]: "dim_row Q = 2" by auto
  let ?s = "Q $$ (0,0)"
  let ?t = "Q $$ (1,0)"
  let ?a1 = "Q $$ (1,1)"
  let ?b1 = "-(Q $$ (0,1))"
  let ?d = "(?A*Q) $$ (0,0)"
  have ab1_ba1: "a*?b1 = b*?a1"
  proof -     
    have  "(?A*Q) $$ (0,1) =  (\<Sum>i = 0..<2. (if i = 0 then a else b) * Q $$ (i, Suc 0))"
      unfolding times_mat_def col_def scalar_prod_def by auto
    also have "... = (\<Sum>i \<in> {0,1}. (if i = 0 then a else b) * Q $$ (i, Suc 0))" 
      by (rule sum.cong, auto)
    also have "... = - a*?b1 + b*?a1" by auto
    finally have "(?A*Q) $$ (0,1) = - a*?b1 + b*?a1" by simp
    moreover have "(?A*Q) $$ (0,1) = 0" using AQ unfolding lower_triangular_def by auto  
    ultimately show ?thesis
      by (metis add_left_cancel more_arith_simps(3) more_arith_simps(7))    
  qed
  have sa_tb_d: "?s*a+?t*b = ?d"
  proof -
    have "?d = (\<Sum>i = 0..<2. (if i = 0 then a else b) * Q $$ (i, 0))"
      unfolding times_mat_def col_def scalar_prod_def by auto
    also have "... = (\<Sum>i \<in> {0,1}. (if i = 0 then a else b) * Q $$ (i, 0))" by (rule sum.cong, auto)
    also have "... = ?s*a+?t*b" by auto
    finally show ?thesis by simp
  qed
  have det_Q_dvd_1: "(Determinant.det Q dvd 1)"
    using invertible_iff_is_unit_JNF[OF Q] inv_Q by auto
  moreover have det_Q_eq: "Determinant.det Q = ?s*?a1 + ?t*?b1" unfolding det_2[OF Q] by simp
  ultimately have "?s*?a1 + ?t*?b1 dvd 1" by auto
  from this obtain u where u_eq: "?s*?a1 + ?t*?b1 = u" and u: "u dvd 1" by auto
  hence eq1: "?s*?a1*a + ?t*?b1*a = u*a"
    by (metis ring_class.ring_distribs(2))
  hence "?s*?a1*a + ?t*?a1*b = u*a"
    by (metis (no_types, lifting) ab1_ba1 mult.assoc mult.commute)
  hence a1d_ua:"?a1*?d=u*a"
    by (smt Groups.mult_ac(2) distrib_left more_arith_simps(11) sa_tb_d)
  hence b1d_ub: "?b1*?d=u*b"
    by (smt Groups.mult_ac(2) Groups.mult_ac(3) ab1_ba1 distrib_right sa_tb_d u_eq)
  obtain inv_u where inv_u: "inv_u * u = 1" using u unfolding dvd_def
    by (metis mult.commute)
  hence inv_u_dvd_1: "inv_u dvd 1" unfolding dvd_def by auto
  have cond1: "(inv_u*?b1)*?d = b" using b1d_ub inv_u
    by (metis (no_types, lifting) Groups.mult_ac(3) more_arith_simps(11) more_arith_simps(6))
  have cond2: "(inv_u*?a1)*?d = a" using a1d_ua inv_u
    by (metis (no_types, lifting) Groups.mult_ac(3) more_arith_simps(11) more_arith_simps(6))
  have "ideal_generated {inv_u*?a1, inv_u*?b1} = ideal_generated {?a1,?b1}"
    by (rule ideal_generated_mult_unit2[OF inv_u_dvd_1])    
  also have "... = UNIV" using ideal_generated_pair_UNIV[OF u_eq u] by simp
  finally have cond3: "ideal_generated {inv_u*?a1, inv_u*?b1} = ideal_generated {1}" by auto
  show "\<exists>a1 b1 d. a = a1 * d \<and> b = b1 * d \<and> ideal_generated {a1, b1} = ideal_generated {1}"
    by (rule exI[of _ "inv_u*?a1"], rule exI[of _ "inv_u*?b1"], rule exI[of _ ?d],
        insert cond1 cond2 cond3, auto)
qed


lemma Hermite_ring_imp_Bezout_ring:
  assumes H: "OFCLASS('a::comm_ring_1, Hermite_ring_class)"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (intro_classes)
  fix a b::'a
  let ?A = "Matrix.mat 1 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a else b)"
  have *: "(\<And>(A::'a::comm_ring_1 mat). admits_triangular_reduction A)"
    using OFCLASS_Hermite_ring_def[where ?'a='a] H by auto
  have "admits_triangular_reduction ?A"
    using H unfolding OFCLASS_Hermite_ring_def by auto
  have "\<exists> a1 b1 d. a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1}"
    using theorem3_restricted_12_part2 * by auto
  from this obtain a1 b1 d where a_a'd: "a = a1*d" and b_b'd: "b = b1*d"
    and a'b'_1: "ideal_generated {a1,b1} = ideal_generated {1}"
    by blast
  obtain p q where "p * a1 + q * b1 = 1" using a'b'_1
    using ideal_generated_pair_exists_UNIV by blast
  hence pa_qb_d: "p * a + q * b = d" unfolding a_a'd b_b'd
    by (metis mult.assoc mult_1 ring_class.ring_distribs(2))
  moreover have d_dvd_a: "d dvd a" using a_a'd by auto
  moreover have d_dvd_b: "d dvd b" using b_b'd by auto    
  moreover have "(\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)" using pa_qb_d by force
  ultimately show "\<exists>p q d. p * a + q * b = d \<and> d dvd a \<and> d dvd b
        \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)" by blast
qed

end
