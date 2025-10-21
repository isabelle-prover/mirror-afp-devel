theory DFI_square_1
  imports DFI_square_0 Lucas_Diophantine

begin

fun rec_forte_init012::"nat \<Rightarrow> nat" where
"rec_forte_init012 0 = 0" |
"rec_forte_init012 (Suc 0) = 0" |
"rec_forte_init012 (Suc (Suc 0)) = 0" |
"rec_forte_init012 (Suc (Suc (Suc n))) = (\<Sum>i\<le>Suc (Suc n). rec_forte_init012 i)"

theorem strong_induct_init012 [consumes 0, case_names 0 1 2 sucsucsuc]:
"P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> P (Suc (Suc 0)) \<Longrightarrow> (\<And>n. ( (\<forall>i\<le>Suc (Suc n). P i) \<Longrightarrow> P (Suc (Suc (Suc n))) ))
\<Longrightarrow> P (n::nat)"
  using rec_forte_init012.induct by auto

lemma sun_lemma2:"\<And>n k r. \<psi> A (k*n+r) = 
(\<Sum>i\<le>n. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A (r+i))"
proof -
  have case_n1: "\<And>r. \<psi> A (k+r)
      = (\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (k+1) - A*\<psi> A k)^(1-i)*(\<psi> A k)^i*\<psi> A (r+i))" for k
  proof (induction k rule: strong_induct_init012)
    case 0
    then show ?case by auto
  next
    case 1
    then show ?case by auto
  next
    case 2
    then show ?case by auto
  next
    case (sucsucsuc k)
    note t = this
    hence IH_k: "\<psi> A (k+s)
      = (\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (k+1) - A*\<psi> A k)^(1-i)*(\<psi> A k)^i*\<psi> A (s+i))" for s by auto
    have IH_Suck: "\<psi> A (Suc k+s)
      = (\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (Suc k+1) - A*\<psi> A (Suc k))^(1-i)*(\<psi> A (Suc k))^i*\<psi> A (s+i))"
      for s 
      using t Suc_n_not_le_n nat_le_linear by blast
    have IH_SucSuck: "\<psi> A (Suc (Suc k)+s) = (\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (Suc (Suc k)+1)
      - A*\<psi> A (Suc (Suc k)))^(1-i)*(\<psi> A (Suc (Suc k)))^i*\<psi> A (s+i))" for s
      using t Suc_n_not_le_n nat_le_linear by blast
    have "\<psi> A (Suc (Suc k)+r) = (\<psi> A (Suc (Suc k)+1)
      - A*\<psi> A (Suc (Suc k)))*\<psi> A r + \<psi> A (Suc (Suc k)) * \<psi> A (r+1)"
      using IH_SucSuck[of r] by (auto simp add: algebra_simps)
    hence simp_psi_sucsuc: "\<psi> A (Suc (Suc k)+r)
      = \<psi> A (Suc (Suc k)) * \<psi> A (r+1) - \<psi> A (Suc k) * \<psi> A r" by auto
    have "\<psi> A (Suc k + r) = (\<psi> A (Suc k + 1) - A*\<psi> A (Suc k))*\<psi> A r + \<psi> A (Suc k) * \<psi> A (r+1)"
      using IH_Suck[of r] by (auto simp add: algebra_simps)
    hence "\<psi> A (Suc k + r) = \<psi> A (Suc k) * \<psi> A (r+1) - \<psi> A k * \<psi> A r" by auto
    hence "\<psi> A (Suc (Suc (Suc k)) + r) = A*(\<psi> A (Suc (Suc k)) * \<psi> A (r+1) - \<psi> A (Suc k) * \<psi> A r)
      - \<psi> A (Suc k) * \<psi> A (r+1) + \<psi> A k * \<psi> A r "
      using simp_psi_sucsuc by auto
    hence "\<psi> A (Suc (Suc (Suc k)) + r) = (A*\<psi> A (Suc (Suc k)) - \<psi> A (Suc k)) * \<psi> A (r+1)
      - (A * \<psi> A (Suc k) - \<psi> A k)*\<psi> A r" by (auto simp add: algebra_simps)
    hence simp_psi: "\<psi> A (Suc (Suc (Suc k)) + r)
      = \<psi> A (Suc (Suc (Suc k))) * \<psi> A (r+1) - \<psi> A (Suc (Suc k))*\<psi> A r" by auto
    have "(\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (Suc (Suc (Suc k))+1)
      - A*\<psi> A (Suc (Suc (Suc k))))^(1-i)*(\<psi> A (Suc (Suc (Suc k))))^i*\<psi> A (r+i))
      = (\<psi> A (Suc (Suc (Suc (Suc k)))) - A*\<psi> A (Suc (Suc (Suc k))))*\<psi> A r
      + \<psi> A (Suc (Suc (Suc k))) *\<psi> A (r+1)"
      by (auto simp add: algebra_simps)
    hence "(\<Sum>i\<le>1. int (1 choose i) * (\<psi> A (Suc (Suc (Suc k))+1)
      - A*\<psi> A (Suc (Suc (Suc k))))^(1-i)*(\<psi> A (Suc (Suc (Suc k))))^i*\<psi> A (r+i))
      = - \<psi> A (Suc (Suc k)) * \<psi> A r + \<psi> A (Suc (Suc (Suc k))) * \<psi> A (r+1)" by simp
    then show ?case using simp_psi by (auto simp add: algebra_simps)
  qed
  show "\<And>k r. \<psi> A (k*n+r)
      = (\<Sum>i\<le>n. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A (r+i))" for n
  proof (induction n rule: \<psi>_induct)
  case 0
    then show ?case by auto
  next
  case 1
    then show ?case using case_n1 by auto
  next
  case (sucsuc n)
    note t = this
    have eq1: "\<psi> A (k*(n+2)+r)
        = (\<Sum>i\<le>n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i))"
      using t[of k "k+r"] by (auto simp add: algebra_simps)
    have case_n1_to_ri: "\<psi> A (k+r+i) = (\<psi> A (k+1) - A*\<psi> A k)*\<psi> A (r+i) + \<psi> A k * \<psi> A (r+i+1)" for i
      using case_n1[of k "r+i"] by (auto simp add: algebra_simps)
    hence "(\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i)
        = (\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*(\<psi> A (k+1) - A*\<psi> A k)*\<psi> A (r+i)
        + (\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A k*\<psi> A (r+i+1)" for i
      using case_n1_to_ri[of i] distrib_left[of "(\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i"
          "(\<psi> A (k+1) - A*\<psi> A k)*\<psi> A (r+i)" "\<psi> A k * \<psi> A (r+i+1)"] by auto
    hence "(\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i)
        = (\<psi> A (k+1) - A*\<psi> A k)*(\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (r+i)
        + (\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*\<psi> A k*(\<psi> A k)^i*\<psi> A (r+i+1)" for i by auto
    hence "(\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i)
        = (\<psi> A (k+1) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + (\<psi> A (k+1) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^(i+1)*\<psi> A (r+i+1)" for i
      using power_Suc[of "\<psi> A (k+1) - A*\<psi> A k" "n+1-i"] power_Suc[of "\<psi> A k" i] by auto
    hence "(\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i)
        = (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k) ^(i+1) * \<psi> A (r+i+1)" for i by auto
    hence "int ((n+1) choose i) * ((\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i))
        = int ((n+1) choose i) * ((\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k) ^(i+1) * \<psi> A (r+i+1))" for i by auto
    hence "int ((n+1) choose i) * ((\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i))
        = int ((n+1) choose i) * ((\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
        + int ((n+1) choose i) * ((\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k) ^(i+1) * \<psi> A (r+i+1))" for i
      by (auto simp add: algebra_simps)
    hence "int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^i*\<psi> A (k+r+i)
        = int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k) ^(i+1) * \<psi> A (r+i+1)" for i
      by (auto simp add: algebra_simps)
    hence "\<psi> A (k*(n+2)+r) =
        (\<Sum>i\<le>n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*\<psi> A k ^(i+1) * \<psi> A (r+i+1))"
      using eq1 by auto
    hence eq2: "\<psi> A (k*(n+2)+r) =
        (\<Sum>i\<le>n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
        + (\<Sum>i\<le>n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^(i+1)*\<psi> A (r+i+1))"
      using sum.distrib[of "\<lambda>i. int ((n+1) choose i)*(\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)"
          "\<lambda>i. int ((n+1) choose i) *(\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^(i+1)*\<psi> A (r+i+1)" "{..n+1}"]
      by auto
    have "i \<le> n+1 \<Longrightarrow> int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+1-i)*(\<psi> A k)^(i+1)*\<psi> A (r+i+1)
    = int (n+1 choose (i+1-1))*(\<psi> A (Suc k)- A*\<psi> A k) ^(n+2-(i+1))*\<psi> A k ^ (i+1)*\<psi> A (r+(i+1))" for i
      by auto
    hence "\<psi> A (k*(n+2)+r) =
        (\<Sum>i\<le>n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
        + (\<Sum>i\<le>n + 1. int (n+1 choose (i+1-1))*(\<psi> A (Suc k)- A*\<psi> A k) ^(n+2-(i+1))
        * \<psi> A k ^ (i+1)*\<psi> A (r+(i+1)))"
      using eq2 by (auto simp add: algebra_simps)
    hence "\<psi> A (k*(n+2)+r) =
        (\<Sum>i=0..n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
        + (\<Sum>i=0..n + 1. int (n+1 choose (i+1-1))*(\<psi> A (Suc k)- A*\<psi> A k) ^(n+2-(i+1))
        * \<psi> A k ^ (i+1)*\<psi> A (r+(i+1)))"
      using atMost_atLeast0 by presburger
    hence eq3: "\<psi> A (k*(n+2)+r) =
        (\<Sum>i=0..n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
        + (\<Sum>i=1..n+2. int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))"
      using translation_var_0_to_1[of "\<lambda>i. int ((n+1) choose (i-1))*(\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)" "n+1"]
      by auto
    have obvious: "{0}\<union>{1..n+1} = {0..n+1} \<and> {0}\<inter>{1..n+1} = {} \<and> finite {0} \<and> finite {1..n+1}
        \<and> finite {n+2} \<and> {1..n+1}\<union>{n+2} = {1..n+2} \<and> {1..n+1}\<inter>{n+2} = {}" by auto
    hence "\<psi> A (k*(n+2)+r) =
      int ((n+1) choose 0) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-0))*(\<psi> A k)^0*\<psi> A (r+0)
      + (\<Sum>i=1..n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i))
      + (\<Sum>i=1..n+1. int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))
      + int ((n+1) choose ((n+2)-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-(n+2))*(\<psi> A k)^(n+2)*\<psi> A (r+(n+2))"
      using sum.union_disjoint[of "{0}" "{1..n+1}" "\<lambda>i. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)"]
        sum.union_disjoint[of "{1..n+1}" "{n+2}"
          "\<lambda>i. int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)"]
        Suc_1 add_Suc_right diff_le_self diff_self_eq_0 eq3 numeral_1_eq_Suc_0 numerals(1)
        sum.atLeast_Suc_atMost sum.nat_ivl_Suc' by auto
    hence "\<psi> A (k*(n+2)+r) =
      int ((n+1) choose 0) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-0))*(\<psi> A k)^0*\<psi> A (r+0)
      + (\<Sum>i=1..n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
      + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))
      + int ((n+1) choose ((n+2)-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-(n+2))*(\<psi> A k)^(n+2)*\<psi> A (r+(n+2))"
      using sum.distrib[of "\<lambda>i. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)"
          "\<lambda>i. int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)" "{1..n+1}"]
      by auto
    hence eq4: "\<psi> A (k*(n+2)+r) =
      int ((n+2) choose 0) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-0)*(\<psi> A k)^0*\<psi> A (r+0)
      + (\<Sum>i=1..n+1. int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
      + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))
      + int ((n+2) choose (n+2)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-(n+2))*(\<psi> A k)^(n+2)*\<psi> A (r+(n+2))"
      by (auto simp add: algebra_simps)
    have "i\<in>{1..n+1} \<Longrightarrow> int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)
        = int ((n+1) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)" for i
      by (simp add: Suc_diff_le)
    hence "i\<in>{1..n+1} \<Longrightarrow> int ((n+1) choose i)*(\<psi> A (Suc k)-A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)
        = (int ((n+1) choose i)
        + int ((n+1) choose (i-1))) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)" for i
      by (auto simp add: algebra_simps)
    hence "i\<in>{1..n+1} \<Longrightarrow> int ((n+1) choose i)*(\<psi> A (Suc k)-A*\<psi> A k)^(Suc (n+1-i))*(\<psi> A k)^i*\<psi> A (r+i)
        + int ((n+1) choose (i-1)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)
        = int ((n+2) choose i)* (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i)" for i
      using choose_reduce_nat[of "n+2" i] by auto
    hence "\<psi> A (k*(n+2)+r) = int ((n+2) choose 0) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-0)*(\<psi> A k)^0*\<psi> A (r+0)
        + (\<Sum>i=1..n+1. int ((n+2) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))
        + int ((n+2) choose (n+2)) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-(n+2))*(\<psi> A k)^(n+2)*\<psi> A (r+(n+2))"
    using eq4 by auto
    hence "\<psi> A (k*(n+2)+r) = int ((n+2) choose 0) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-0)*(\<psi> A k)^0*\<psi> A (r+0)
        + (\<Sum>i=1..n+2. int ((n+2) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))"
      by auto
    hence "\<psi> A (k*(n+2)+r) =
        (\<Sum>i=0..n+2. int ((n+2) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))"
      using obvious by (simp add: sum.atLeast_Suc_atMost)
    hence "\<psi> A (k*(n+2)+r) =
        (\<Sum>i\<le>n+2. int ((n+2) choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n+2-i)*(\<psi> A k)^i*\<psi> A (r+i))"
      using atMost_atLeast0 by presburger
    then show ?case by simp
  qed
qed


lemma lucas_consec_coprime: "coprime (\<psi> A k) (\<psi> A (Suc k))"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note IH=this
  have "\<forall>c. c dvd \<psi> A (Suc k) \<and> c dvd \<psi> A (Suc (Suc k)) \<longrightarrow> is_unit c"
  proof
    fix c
    show "c dvd \<psi> A (Suc k) \<and> c dvd \<psi> A (Suc (Suc k)) \<longrightarrow> is_unit c"
    proof
      assume divhyp: "c dvd \<psi> A (Suc k) \<and> c dvd \<psi> A (Suc (Suc k))"
      then have "c dvd A * \<psi> A (Suc k) - \<psi> A k" by simp
      then have "c dvd \<psi> A k" using divhyp by algebra
      then show "is_unit c" using divhyp IH by fastforce
    qed
  qed
  then show ?case unfolding coprime_def by simp
qed

(* The following basic number theory lemmas probably already exist in some
   form but this was the shortest possible *)
lemma eq_mod_power: fixes a::int and b::int assumes "a mod n = b mod n" shows "a^k mod n = b^k mod n"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note IH=this
  then show "a ^ Suc k mod n = b ^ Suc k mod n" using assms mod_mult_cong[of a n b "a^k" "b^k"]
    by fastforce
qed

lemma euclids_lemma: "(coprime (a::int) b) \<and> a dvd (b*c) \<longrightarrow> a dvd c"
  using coprime_dvd_mult_right_iff by blast

lemma coprime_power: fixes a::int and b::int assumes "coprime a b" shows "coprime (a^k) b"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note IH=this
  then have "c dvd a ^ Suc k \<and> c dvd b \<Longrightarrow> is_unit c" for c
  proof -
    assume assm: "c dvd a ^ Suc k \<and> c dvd b"
    then have "coprime c a"
      by (meson assms coprime_def dvd_trans)
    then show "is_unit c"
      using euclids_lemma[of c a "a^k"] IH assm by fastforce
  qed
  then show "coprime (a^(Suc k)) b"
    by fastforce
qed
(* End of the auxiliary number theory lemmas *)

(* In the next lemma k is assumed non-zero because that case is trivial and
   this assumption simplifies things (eg. euclidean division) *)
lemma dvd_remove_psi:
  fixes A::int and k::nat and m::nat
  assumes "(\<psi> A k) dvd (\<psi> A m)" and "A^2-4\<ge>0" and "k>0"
  shows "(int k) dvd (int m)"
proof -
  define r where "r = m mod k"
  then have "\<exists>n. m = n * k + r"
    using div_mod_decomp by blast
  then obtain n where n_def: "m = n * k + r" by auto
  have termszero:"\<forall>i\<in>{1..n}. int(n choose i) * (\<psi> A (Suc k)
      - A*\<psi> A k)^(n-i) * (\<psi> A k)^i * \<psi> A (r+i) mod (\<psi> A k) = 0"
    by simp
  have yes: "finite {0} \<and> finite {1..n} \<and> {0} \<inter> {1..n} = {} \<and> {0}\<union>{1..n} = {0..n}" by auto
  have termszero2: "(\<Sum>i\<in>{1..n}. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i
      * \<psi> A (r+i)) mod (\<psi> A k)) = 0"
    using termszero sum.neutral by fast

  have eq1: "\<psi> A m mod (\<psi> A k) = (\<Sum>i\<le>n. int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)
      * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k)"
    using n_def sun_lemma2[of "A" "k" "n" "r"] by (simp add: mult.commute)
  also have eq2: "... = (\<Sum>i\<le>n. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i
      * \<psi> A (r+i)) mod (\<psi> A k)) mod (\<psi> A k)"
    by (simp add: mod_sum_eq)
  have eq3: "(\<Sum>i\<le>n. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k))
      = (\<Sum>i\<le>0. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k))
      + (\<Sum>i\<in>{1..n}. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k))"
    using sum.union_disjoint[of "{0}" "{1..n}"
        "(\<lambda>i. int (n choose i) * (\<psi> A (Suc k) - A * \<psi> A k) ^ (n - i) * \<psi> A k ^ i * \<psi> A (r + i) mod \<psi> A k)"]
      yes
    by (metis atMost_0 atMost_atLeast0)
  moreover have eq4: "... = (\<Sum>i\<le>0. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)
      * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k)) mod (\<psi> A k)"
    using termszero2 by simp
  moreover have eq5: "... = ((\<psi> A (Suc k) - A*\<psi> A k)^n * \<psi> A (r)) mod (\<psi> A k)"
    by fastforce
  have eq5': "(\<Sum>i\<le>n. (int(n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i) * (\<psi> A k)^i * \<psi> A (r+i)) mod (\<psi> A k))
      = ((\<psi> A (Suc k) - A*\<psi> A k)^n * \<psi> A (r)) mod (\<psi> A k)"
    using eq3 eq4 eq5 by metis
  have "(\<psi> A (Suc k) - A*\<psi> A k) mod (\<psi> A k) = (\<psi> A (Suc k)) mod (\<psi> A k)" by algebra
  then have "(\<psi> A (Suc k) - A*\<psi> A k)^n mod (\<psi> A k) = (\<psi> A (Suc k))^n mod (\<psi> A k)"
    using eq_mod_power by fast
  then have eq6: "((\<psi> A (Suc k) - A*\<psi> A k)^n * \<psi> A (r)) mod (\<psi> A k) = ((\<psi> A (Suc k))^n * \<psi> A (r)) mod (\<psi> A k)"
    using mod_mult_cong by fast
  then have eq7: "0 = ((\<psi> A (Suc k))^n * \<psi> A (r)) mod (\<psi> A k)"
    using assms eq1 eq2 eq5' eq6 by simp
  then have eq8: "(\<psi> A k) dvd (\<psi> A (Suc k))^n * \<psi> A r" by fastforce
  have "coprime ((\<psi> A (Suc k))^n) (\<psi> A k)"
    using lucas_consec_coprime[of A k] coprime_power coprime_commute by blast
  then have eq9: "\<psi> A k dvd \<psi> A r"
    using eq8 euclids_lemma coprime_commute by blast

  have "(abs A)^2 \<ge> 4" using assms by simp
  then have ABe2: "abs A \<ge> 2"
    by (smt (verit, ccfv_SIG) abs_1 abs_square_le_1 zero_power2)
  have "r<k" using r_def \<open>k>0\<close> by simp
  then have "r + (k - r - 1) = k-1 \<and> Suc (k-1) = k" by simp
  then have "\<psi> (abs A) r < \<psi> (abs A) k"
    using ABe2 lucas_monotone2[of "abs A" r "k-r-1"] lucas_strict_monotonicity[of "abs A" "k-1"] by simp
  then have "abs (\<psi> A r) < abs (\<psi> A k)" using lucas_symmetry_A_abs ABe2 by fastforce
  then have psir0:"\<psi> A r = 0" using eq9
    by (meson abs_dvd_iff dvd_abs_iff zdvd_not_zless zero_less_abs_iff)
  have contr: "r>0 \<Longrightarrow> abs(\<psi> A r) > 0"
    using ABe2 lucas_strict_monotonicity[of "abs A" "r-1"] lucas_symmetry_A_abs[of A r] by simp
  then have "r=0" using psir0 by auto
  then have "int m = int k * int n" using n_def by simp
  then show ?thesis by simp
qed

lemma sun_lemma7:
  fixes A::int and k::nat and m::nat
  assumes "A^2-4\<ge>0" and "(\<psi> A k)^2 dvd \<psi> A m" and "k>0"
  shows "\<psi> A k dvd (int m)"
proof -
  have "k dvd m" using assms dvd_remove_psi[of A k m] by auto
  then obtain "n" where n_def: "m = k * n" by auto
  then show ?thesis
  proof (cases "n=0")
    case True
    then show ?thesis using n_def by simp
  next
    case False
    have "i\<ge>2 \<longrightarrow> (\<psi> A k)^i = (\<psi> A k)^2 * (\<psi> A k)^(i-2)" for i
      by (metis le_add_diff_inverse2 mult.commute power_add)
    then have "\<forall>i\<in>{2..n}. ((\<psi> A k)^i) mod (\<psi> A k)^2 = 0"
      by (meson atLeastAtMost_iff dvd_imp_mod_0 le_imp_power_dvd)
    then have termszero: "\<forall>i\<in>{2..n}. (int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)
      *(\<psi> A k)^i*\<psi> A i) mod (\<psi> A k)^2 = 0"
      by auto
    have disj_sum: "finite {..(1::nat)}  \<and> finite {2..n} \<and> {..1} \<inter> {2..n} = {}
      \<and> {0..1}\<union>{2..n} = {0..n}"
      using \<open>n\<noteq>0\<close> by auto

    have "0 = (\<psi> A m) mod (\<psi> A k)^2" using assms by simp
    also have "... = (\<Sum>i\<le>n. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i)mod (\<psi> A k)^2"
      using n_def sun_lemma2[of A k n 0] by simp
    also have "... = (\<Sum>i\<le>n. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i mod (\<psi> A k)^2) mod (\<psi> A k)^2"
      using mod_sum_eq[of "(\<lambda>i. (int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i ) )" "(\<psi> A k)^2" "{..n}"] by simp
    also have "... = ( (\<Sum>i\<le>1. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i mod (\<psi> A k)^2 )
              + (\<Sum>i\<in>{2..n}. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i mod (\<psi> A k)^2 ) )mod (\<psi> A k)^2"
      using disj_sum sum.union_disjoint[of "{..(1::nat)}" "{2..n}"
          "(\<lambda>i. (int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i mod (\<psi> A k)^2) )"]
      by (metis (mono_tags, lifting) atMost_atLeast0)
    also have "... = (\<Sum>i\<le>1. int (n choose i) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-i)*(\<psi> A k)^i*\<psi> A i mod (\<psi> A k)^2 ) mod (\<psi> A k)^2"
      using termszero sum.neutral by simp
    finally have mod_eq1: "0 = int(n) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-1)*(\<psi> A k) mod (\<psi> A k)^2"
      by force
    have "(abs A)^2 \<ge> 4" using assms by simp
    then have ABe2: "abs A \<ge> 2"
      by (smt (verit, ccfv_SIG) abs_1 abs_square_le_1 zero_power2)
    have psiAknn: "abs(\<psi> A k) > 0"
      using ABe2 assms lucas_strict_monotonicity[of "abs A" "k-1"] lucas_symmetry_A_abs[of A k] by simp
    then have "\<psi> A k dvd int(n) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-1)"
      using mod_eq1 by (smt (z3) dvd_times_right_cancel_iff mod_0_imp_dvd power2_eq_square)
    then have mod_eq2:"0 = int(n) * (\<psi> A (Suc k) - A*\<psi> A k)^(n-1) mod (\<psi> A k)" by simp
    have "(\<psi> A (Suc k) - A*\<psi> A k) mod (\<psi> A k) = (\<psi> A (Suc k)) mod (\<psi> A k)" by algebra
    then have "(\<psi> A (Suc k) - A*\<psi> A k)^(n-1) mod (\<psi> A k) = (\<psi> A (Suc k))^(n-1) mod (\<psi> A k)"
      using eq_mod_power by fast
    then have mod_eq3:"0 = int(n) * (\<psi> A (Suc k))^(n-1) mod (\<psi> A k)"
      using mod_eq2 mod_mult_cong by metis
    then have eq4:"(\<psi> A k) dvd int(n) * (\<psi> A (Suc k))^(n-1)" by fastforce
    have "coprime ((\<psi> A (Suc k))^(n-1)) (\<psi> A k)"
      using lucas_consec_coprime[of A k] coprime_power coprime_commute by blast
    then have "\<psi> A k dvd int n"
      using eq4 euclids_lemma coprime_commute mult.commute by metis
    then show "\<psi> A k dvd int m" using n_def by simp
  qed
qed

text \<open>Introducing \<open>\<psi>\<close> and \<open>\<chi>\<close> with both interger parameters. It is a broader definition but induction
      is harder, that's why a lot of properties for these vesion are proved in the following lemmas\<close>

definition \<psi>_int::"int \<Rightarrow> int \<Rightarrow> int" where
"\<psi>_int A n = (-1)^(if n \<ge> 0 then 0 else 1) * \<psi> A (nat (abs n))"
definition \<chi>_int::"int \<Rightarrow> int \<Rightarrow> int" where
"\<chi>_int A n = \<chi> A (nat (abs n))"

lemma \<psi>_int_eq: "\<psi>_int A n = (if n \<ge> 0 then 1 else -1) * \<psi> A (nat (abs n))"
  unfolding \<psi>_int_def by auto

lemma \<psi>_int_ind:
  fixes A::int and n::int
  shows "\<psi>_int A (n+2) = A*\<psi>_int A (n+1) - \<psi>_int A n"
proof -
  consider (2)  "n=-2" | (1) "n=-1" | (pos) "n \<ge> 0" |(neg) "n \<le> -3" by linarith
  then show ?thesis
  proof cases
    case 2
    note t=this
    have "\<psi> A 2 = A \<and> \<psi> A 1 = 1 \<and> \<psi> A 0 = 0"
      by (smt (verit, ccfv_SIG) \<psi>.elims \<psi>.simps(1) \<psi>.simps(2) add_diff_cancel_left' diff_Suc_1
          mult_cancel_left2 nat_1_add_1 numeral_1_eq_Suc_0 numeral_One zero_neq_numeral)
    hence "\<psi>_int A (-2) = -A \<and> \<psi>_int A (-1) = -1 \<and> \<psi>_int A 0 = 0" unfolding \<psi>_int_def by auto
    then show ?thesis using t by simp
  next
    case 1
    note t=this
    have "\<psi>_int A (-1) = -1 \<and> \<psi>_int A 0 = 0 \<and> \<psi>_int A 1 = 1" unfolding \<psi>_int_def by auto
    then show ?thesis using t by simp
next
  case pos
  have triv_abs: "n \<ge> 0 \<and> n+1 \<ge> 0 \<and> n+2 \<ge> 0 \<and> nat (abs (n+1)) = nat (abs n) +1
      \<and> nat (abs (n+2)) = nat (abs n) +2"
    by (simp add: nat_add_distrib pos)
  hence "\<psi>_int A n = \<psi> A (nat (abs n)) \<and> \<psi>_int A (n+1) = \<psi> A (nat (abs n) +1)
      \<and> \<psi>_int A (n+2) = \<psi> A (nat (abs n) +2)"
    unfolding \<psi>_int_def by (simp add: triv_abs mult_numeral_1)
  then show ?thesis by auto
next
  case neg
  hence triv_abs2: "n < 0 \<and> n+1 < 0 \<and> n+2 < 0 \<and> nat (abs (n+1)) = nat (abs (n+2)) +1
      \<and> nat (abs n) = nat (abs (n+2)) +2"
    by auto
  hence "\<psi>_int A n = -\<psi> A (nat (abs (n+2))+2) \<and> \<psi>_int A (n+1) = -\<psi> A (nat (abs (n+2)) +1)
      \<and> \<psi>_int A (n+2) = -\<psi> A (nat (abs (n+2)))"
    unfolding \<psi>_int_def by auto
  then show ?thesis by auto
qed
qed

lemma \<chi>_int_ind:
  fixes A::int and n::int
  shows "\<chi>_int A (n+2) = A*\<chi>_int A (n+1) - \<chi>_int A n"
proof -
  consider (2)  "n=-2" | (1) "n=-1" | (pos) "n \<ge> 0" |(neg) "n \<le> -3" by linarith
  then show ?thesis
  proof cases
    case 2
    note t=this
    have "\<chi> A 2 = A*A-2 \<and> \<chi> A 1 = A \<and> \<chi> A 0 = 2"
      by (metis One_nat_def Suc_1 \<chi>.simps(1) \<chi>.simps(2) \<chi>.simps(3))
    hence "\<chi>_int A (-2) = A*A-2 \<and> \<chi>_int A (-1) = A \<and> \<chi>_int A 0 = 2" unfolding \<chi>_int_def by auto
    then show ?thesis using t by simp
  next
    case 1
    note t=this
    have "\<chi>_int A (-1) = A \<and> \<chi>_int A 0 = 2 \<and> \<chi>_int A 1 = A" unfolding \<chi>_int_def by auto
    then show ?thesis using t by simp
next
  case pos
  have triv_abs: "n \<ge> 0 \<and> n+1 \<ge> 0 \<and> n+2 \<ge> 0 \<and> nat (abs (n+1)) = nat (abs n) +1
      \<and> nat (abs (n+2)) = nat (abs n) +2"
    by (simp add: nat_add_distrib pos)
  hence "\<chi>_int A n = \<chi> A (nat (abs n)) \<and> \<chi>_int A (n+1) = \<chi> A (nat (abs n) +1)
      \<and> \<chi>_int A (n+2) = \<chi> A (nat (abs n) +2)"
    unfolding \<chi>_int_def by (simp add: triv_abs mult_numeral_1)
  then show ?thesis by auto
next
  case neg
  hence triv_abs2: "n < 0 \<and> n+1 < 0 \<and> n+2 < 0 \<and> nat (abs (n+1)) = nat (abs (n+2)) +1
      \<and> nat (abs n) = nat (abs (n+2)) +2"
    by auto
  hence "\<chi>_int A n = \<chi> A (nat (abs (n+2))+2) \<and> \<chi>_int A (n+1) = \<chi> A (nat (abs (n+2)) +1)
      \<and> \<chi>_int A (n+2) = \<chi> A (nat (abs (n+2)))"
    unfolding \<chi>_int_def by auto
  then show ?thesis by auto
qed
qed

lemma \<psi>_int_odd:
  fixes A::int and n::int
  shows "\<psi>_int A (-n) = -\<psi>_int A n"
  unfolding \<psi>_int_def by auto

lemma \<chi>_int_even:
  fixes A::int and n::int
  shows "\<chi>_int A (-n) = \<chi>_int A n"
  unfolding \<chi>_int_def by auto

lemma technical_lemma1:
  fixes k::int and r::int and A::int
  shows "\<psi>_int A (k+r) = \<psi>_int A r * \<chi>_int A k + \<psi>_int A (k-r)"
proof -
  have case_pos:  "\<psi>_int A (int l +s) = \<psi>_int A s * \<chi>_int A (int l) + \<psi>_int A (int l-s)"
    for l::nat and s::int
  proof (induction l rule: \<psi>_induct)
    case 0
    have "\<chi>_int A (int 0) = 2 \<and> \<psi>_int A (int 0 - s) = - \<psi>_int A s"
      unfolding \<chi>_int_def \<psi>_int_def by auto
    then show ?case by auto
  next
    case 1
    have "\<chi>_int A (int 1) = A \<and> \<psi>_int A (int 1 - s) = -\<psi>_int A (s - 1)"
      unfolding \<chi>_int_def using \<psi>_int_odd[of A "s - 1"] by auto
    then show ?case using \<psi>_int_ind[of A " s - 1"] by auto
  next
    case (sucsuc l)
    note t = this
    have "\<psi>_int A (int (Suc (Suc l)) + s) = \<psi>_int A (int l + s +2)"
      by (auto simp add: algebra_simps)
    hence "\<psi>_int A (int (Suc (Suc l))+s) = A*\<psi>_int A (int (Suc l)+s) - \<psi>_int A (int l+s)"
      using \<psi>_int_ind[of A "int l+s"] by (auto simp add: algebra_simps)
    hence "\<psi>_int A (int (Suc (Suc l))+s) = \<psi>_int A s*(A*\<chi>_int A (int l + 1) - \<chi>_int A (int l))
+ A*\<psi>_int A (int l - s + 1) - \<psi>_int A (int l - s)"
      using t by (auto simp add: algebra_simps)
    hence "\<psi>_int A (int (Suc (Suc l))+s) = \<psi>_int A s*\<chi>_int A (int l + 2) + \<psi>_int A (int l - s +2)"
      using \<psi>_int_ind[of A "int l - s"] \<chi>_int_ind[of A "int l"] by auto
      then show ?case by (auto simp add: algebra_simps)
  qed
  then show ?thesis
  proof (cases k)
  case (nonneg k)
    then show ?thesis using case_pos[of k r] by auto
  next
    case (neg n)
    hence intnatk: "int (nat (abs k)) = - k" by auto
    hence "\<psi>_int A (-k+r) = \<psi>_int A r * \<chi>_int A (-k) + \<psi>_int A (-k-r)"
      using case_pos[of "nat (abs k)" r] by argo
    hence "-\<psi>_int A (k-r) = \<psi>_int A r * \<chi>_int A k - \<psi>_int A (k+r)"
      using \<psi>_int_odd[of A "k-r"] \<psi>_int_odd[of A "k+r"] \<chi>_int_even[of A k] by auto
    then show ?thesis by auto
  qed
qed

text \<open>It is now much easier to state the following lemma\<close>

lemma technical_lemma2:
  fixes r::int and A::int and n::int and q::int and k::int
  assumes "n \<noteq> 0" and "\<chi>_int A n = 2*k"
  shows "\<psi>_int A (2*n+r) mod (\<chi>_int A n) = (-\<psi>_int A r) mod (\<chi>_int A n)"
and "\<psi>_int A (4*n*q+r) mod k = \<psi>_int A r mod k"
proof -
  have "\<psi>_int A (2*n+s) = \<psi>_int A (n+s) * \<chi>_int A n + \<psi>_int A (-s)" for s
    using technical_lemma1[of A n "n+s"] by auto
  hence "\<psi>_int A (2*n+s) mod (\<chi>_int A n) = \<psi>_int A (-s) mod (\<chi>_int A n)" for s
    by (auto simp add: algebra_simps)
  hence first_fact: "\<psi>_int A (2*n+s) mod (\<chi>_int A n) = (-\<psi>_int A s) mod (\<chi>_int A n)" for s
    using \<psi>_int_odd[of A s] by auto
  thus "\<psi>_int A (2*n+r) mod (\<chi>_int A n) = (-\<psi>_int A r) mod (\<chi>_int A n)" by auto
  have dvd_mod: "a dvd b \<Longrightarrow> l mod b = m mod b \<Longrightarrow> l mod a = m mod a" for a::int and b and l and m
    by (metis mod_mod_cancel)
  have cor_modk: "\<psi>_int A (2*n+s) mod k = (-\<psi>_int A s) mod k" for s
    using assms first_fact dvd_mod[of k "\<chi>_int A n" "\<psi>_int A (2*n+s)" "-\<psi>_int A s"] by auto
  have cor_modk2: "\<psi>_int A (-2*n+s) mod k = (-\<psi>_int A s) mod k" for s
    using cor_modk[of "-2*n*s"] using mod_minus_cong by (smt (z3) cor_modk)

  have q_identity: "\<And>r. \<psi>_int A (4*n*int s+r) mod k = \<psi>_int A r mod k
      \<and> \<psi>_int A (-4*n*int s+r) mod k = \<psi>_int A r mod k" for s::nat
  proof (induction s)
    case 0
    then show ?case by auto
  next
    case (Suc s)
    note t = this
    have "\<psi>_int A (4*n*int (Suc s)+r) = \<psi>_int A (4*n*int s + (4*n+r))
      \<and> \<psi>_int A (-4*n*int (Suc s)+r) = \<psi>_int A (-4*n*int s + (-4*n+r))"
      by (auto simp add: algebra_simps)
    hence "\<psi>_int A (4*n*int (Suc s)+r) mod k = \<psi>_int A (4*n+r) mod k
      \<and> \<psi>_int A (-4*n*int (Suc s)+r) mod k = \<psi>_int A (-4*n+r) mod k"
      using t[of "4*n+r"] t[of "-4*n+r"] by auto
    hence "\<psi>_int A (4*n*int (Suc s)+r) mod k = (-\<psi>_int A (2*n+r)) mod k
      \<and> \<psi>_int A (-4*n*int (Suc s)+r) mod k = (-\<psi>_int A (-2*n+r)) mod k"
      using cor_modk[of "2*n+r"] cor_modk2[of "-2*n+r"] by auto
    thus "\<psi>_int A (4*n*int (Suc s)+r) mod k = \<psi>_int A r mod k
      \<and> \<psi>_int A (-4*n*int (Suc s)+r) mod k = \<psi>_int A r mod k"
      using cor_modk[of r] cor_modk2[of r] mod_minus_cong by (metis add.inverse_inverse)
  qed
  thus "\<psi>_int A (4*n*q+r) mod k = \<psi>_int A r mod k"
  proof (cases q)
    case (nonneg l)
    then show ?thesis using q_identity[of "nat q" r] by auto
  next
    case (neg l)
    then show ?thesis using q_identity[of "nat (-q)" r] by (auto simp add: algebra_simps)
  qed
qed


lemma lucas_solves_pell:
  fixes A :: int
  shows "(A^2-4)*(\<psi>_int A m)^2 + 4 = (\<chi>_int A m)^2"
  unfolding \<psi>_int_def \<chi>_int_def using lucas_pell_part3 by auto 

lemma pell_yields_lucas:
  fixes A Y :: int
  shows "(\<exists>k. (A^2-4)*Y^2 + 4 = k^2) = (\<exists>m. Y = \<psi>_int A m)"
  (* using lucas_pell_nat unfolding \<psi>_int_def
  apply (auto)
  subgoal for m by (rule exI[of _ "int m"], auto)
  subgoal for m by (rule exI[of _ "- int m"], auto)
  done
 *)

proof (rule iffI)
  assume "\<exists>k. (A\<^sup>2 - 4) * Y\<^sup>2 + 4 = k\<^sup>2"
  then obtain m :: nat where m: "Y = \<psi> A m \<or> Y = - \<psi> A m"
     using lucas_pell_nat(1) by auto 
  show "\<exists>m :: int. Y = \<psi>_int A m" 
    apply (rule disjE[OF m])
    subgoal 
      apply (rule exI[of _ "int m"]) unfolding \<psi>_int_def by auto
    subgoal 
      apply (rule exI[of _ "- int m"]) unfolding \<psi>_int_def by auto
    done
next
  assume "\<exists>m. Y = \<psi>_int A m"
  then obtain m where m: "Y = \<psi>_int A m" by auto
  show "\<exists>k. (A\<^sup>2 - 4) * Y\<^sup>2 + 4 = k\<^sup>2"
    unfolding lucas_pell_nat
    apply (cases "0 \<le> m")
    subgoal 
      apply (rule exI[of _ "nat m"])
      using m unfolding \<psi>_int_def
      by auto
    subgoal 
      apply (rule exI[of _ "nat (- m)"])
      using m unfolding \<psi>_int_def
      by auto
    done
qed

corollary technical_lemma2_part2:
fixes r::int and A::int and n::int and q::int and k::int
  assumes "n \<noteq> 0" and "\<chi>_int A n = 2*k"
  shows "\<psi>_int A (4*n*q+r) mod k = \<psi>_int A r mod k"
  using technical_lemma2 assms by auto

corollary technical_cor3:
  fixes r::int and A::int and n::int and k::int
  assumes "n \<noteq> 0" and "\<chi>_int A n = 2*k"
  shows "\<psi>_int A (2*n+r) mod k = (-\<psi>_int A r) mod k"
proof -
  have "(\<psi>_int A (2*n+r) + \<psi>_int A r) mod \<chi>_int A n = 0 mod \<chi>_int A n"
    using technical_lemma2[of n A k r] assms mod_add_cong[of "\<psi>_int A (2*n+r)" "\<chi>_int A n"
        "-\<psi>_int A r" "\<psi>_int A r" "\<psi>_int A r"] by (auto simp add: algebra_simps)
  hence "\<chi>_int A n dvd (\<psi>_int A (2*n+r) + \<psi>_int A r)" by auto
  hence "k dvd (\<psi>_int A (2*n+r) + \<psi>_int A r)" using assms by auto
  hence "(\<psi>_int A (2*n+r) + \<psi>_int A r) mod k = 0 mod k" by auto
  thus ?thesis using mod_diff_cong[of "\<psi>_int A (2*n+r) + \<psi>_int A r" k 0 "\<psi>_int A r" "\<psi>_int A r"]
    by auto
qed

end
