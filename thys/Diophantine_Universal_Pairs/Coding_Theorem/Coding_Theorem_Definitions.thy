theory Coding_Theorem_Definitions
  imports "../Coding/Multinomial" "../Coding/Bit_Counting" "Digit_Expansions.Bits_Digits"
          "../MPoly_Utils/More_More_MPoly_Type" "../MPoly_Utils/Poly_Extract"
          "../MPoly_Utils/Total_Degree_Env" "../MPoly_Utils/Poly_Degree"
begin

section \<open>The Coding Theorem\<close>

lemma series_bound:
  fixes b :: int
  assumes "b \<ge> 2"
  shows "(\<forall>k\<le>q. f k < b) \<Longrightarrow> (\<Sum>k = 0..q. f k * b ^ k) < b^(Suc q)"
proof (induct q)
  case 0
  then show ?case
    by simp
next
  case (Suc q)
  hence f_le_bound: "\<forall>k\<le>Suc q. f k \<le> b-1" using assms
    by auto
  
  from Suc show ?case
  proof -
    assume "\<forall>k\<le>q. f k < b \<Longrightarrow> (\<Sum>k = 0..q. f k * b ^ k) < b ^ Suc q"
    with Suc have asm: "(\<Sum>k = 0..q. f k * b ^ k) < b ^ Suc q"
      by auto

    have "(\<Sum>k = 0..q. f k * b ^ k) + f (Suc q) * (b * b ^ q)
          \<le> (\<Sum>k = 0..q. f k * b ^ k) + (b-1) * (b * b ^ q)"
      using f_le_bound assms by auto
    also have "... < b^(Suc q) + (b-1) * (b * b ^ q)"
      using asm by auto
    also have "... \<le> b * b * b^q"
      by (simp add: left_diff_distrib)
    finally show ?thesis
      using asm by auto
  qed 
qed

subsection \<open>Definition of polynomials required in the Coding Theorem\<close>

locale coding_variables =
  fixes P :: "int mpoly"
    and a :: int
    and f :: int
begin

text \<open>Notation for working with P\<close>

definition \<delta> :: nat where "\<delta> \<equiv> total_degree P"
definition \<nu> :: nat where "\<nu> \<equiv> max_vars P"

(* Beware : we can't use Abs_poly_mapping ((!) i) *)
definition P_coeff :: "nat list \<Rightarrow> int" where
  "P_coeff i \<equiv> coeff P (Abs_poly_mapping ((!\<^sub>0) i))"

text \<open>Notation used in the proofs\<close>
definition n :: "nat \<Rightarrow> nat" where "n i \<equiv> (\<delta>+1)^i"
definition \<delta>_tuples :: "(nat list) set" where
  "\<delta>_tuples \<equiv> {i. length i = \<nu> + 1 \<and> sum_list i \<le> \<delta>}"

lemma \<delta>_tuples_finite[simp]: "finite \<delta>_tuples"
proof -
  have stronger: "finite {i::nat list. length i = n \<and> sum_list i \<le> K }" 
    (is "finite (?S n)") for n K
  proof (induction n)
    case 0 thus ?case by auto
  next
    case (Suc n)
    { fix i assume assm_i: "i \<in> ?S (Suc n)"
      then obtain j0 j where i_def: "i = j0#j"
        by (smt (verit, best) Suc_length_conv mem_Collect_eq)
      hence "(j0, j) \<in> ({..K} \<times> ?S n)" using assm_i by auto
      hence "i \<in> (\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n)" using i_def by auto }
    hence "?S (Suc n) \<subseteq> (\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n)" 
     by blast
    moreover have "finite ((\<lambda>(j0, j). j0#j) ` ({..K} \<times> ?S n))" 
      using Suc.IH by blast
    ultimately have "finite (?S (Suc n))" 
      by (meson finite_subset)
    thus ?case .
  qed
  thus ?thesis unfolding \<delta>_tuples_def .
qed
  
abbreviation \<sigma> where "\<sigma> \<equiv> count_bits"
abbreviation \<tau> where "\<tau> \<equiv> count_carries"

text \<open>The variables of Definition 2.2\<close>

text \<open>This is not the same \<open>\<L>\<close> as in Lemma 1.8\<close>
definition \<L> :: nat where "\<L> \<equiv> nat (\<Sum>i\<in>\<delta>_tuples. abs (P_coeff i))"
text \<open>We have to use Inf instead of Min to define r because the set is infinite\<close>
definition r :: nat where "r \<equiv> Inf {y. 4^y > 2 * fact \<delta> * \<L> * (\<nu> + 3)^\<delta>}"
definition \<beta> :: nat where "\<beta> \<equiv> 4^r"
definition \<gamma> :: nat where "\<gamma> \<equiv> \<beta>^(n \<nu>)"
definition \<alpha> :: nat where "\<alpha> \<equiv> \<delta> * n \<nu> + 1"

lemma \<alpha>_gt_0: "\<alpha> > 0" unfolding \<alpha>_def by auto
lemma \<gamma>_gt_0: "\<gamma> > 0" unfolding \<gamma>_def \<beta>_def n_def by auto

definition b :: "int" where 
  "b \<equiv> 1 + 3*(2*a + 1) * f"
definition \<B> :: "int" where
  "\<B> \<equiv> (of_nat \<beta>) * b^\<delta>"
definition N0 :: "int" where 
  "N0 \<equiv> \<B>^((\<delta>+1)^\<nu> + 1)"
definition N1 :: "int" where 
  "N1 \<equiv> 4 * \<B>^((2*\<delta>+1) * (\<delta>+1)^\<nu> + 1)"
definition N :: "int" where 
  "N \<equiv> N0 * N1"
definition c :: "int \<Rightarrow> int" where 
  "c g \<equiv> 1 + a*\<B> + g"

poly_extract b
poly_degree b_poly

poly_extract \<B>
poly_degree \<B>_poly

poly_extract N0
poly_extract N1
poly_extract N
poly_extract c
poly_degree c_poly


text \<open>The M polynomial.\<close>
definition m :: "nat \<Rightarrow> int" where 
  "m j \<equiv> (if j \<in> n ` {1..\<nu>} then \<B> - b else \<B> - 1)"
definition M :: "int" where 
  "M \<equiv> (\<Sum>j=0..n \<nu>. m j * \<B>^j)"

definition m_poly :: "nat \<Rightarrow> int mpoly" where
  "m_poly j = (if j \<in> n ` {1..\<nu>} then \<B>_poly - b_poly else \<B>_poly - 1)"

definition M_poly :: "int mpoly" where 
  "M_poly \<equiv> (\<Sum> j=0..n \<nu>. m_poly j * \<B>_poly ^ j)"

lemma m_correct: "insertion fn (m_poly j) = coding_variables.m P (fn 0) (fn (Suc 0)) j"
  unfolding coding_variables.m_def coding_variables.m_poly_def
  by (cases "j \<in> n ` {1..\<nu>}", simp_all add: \<B>_correct b_correct) 

lemma m_poly_degree_env_correct: "total_degree_env ctxt (m_poly j)
   \<le> max (total_degree_env ctxt \<B>_poly) (total_degree_env ctxt b_poly)"
  unfolding m_poly_def by (auto simp: le_trans[OF total_degree_env_diff])

lemma M_correct:
  "insertion fn (coding_variables.M_poly P) = coding_variables.M P (fn 0) (fn 1)"
  unfolding M_poly_def coding_variables.M_def apply simp
  unfolding \<B>_correct m_correct by auto

(* This lemma relies on poly_degree having been called on \<B>_poly and b_poly
    within the locale where they are defined *)
lemma m_poly_degree_correct: 
  shows "\<delta> > 0 \<Longrightarrow> total_degree (m_poly j) \<le> 2*\<delta>"
  unfolding total_degree_env_id[symmetric]
  apply (rule le_trans[OF coding_variables.m_poly_degree_env_correct])
  apply (unfold total_degree_env_id, simp, intro conjI)
  using coding_variables.\<B>_poly_degree_correct[unfolded coding_variables.\<B>_poly_degree_def]
  using coding_variables.b_poly_degree_correct[unfolded coding_variables.b_poly_degree_def]
  by (auto simp add: mult_2)

lemma M_poly_degree_correct:
  assumes asm: "\<delta> > 0"
  shows "total_degree M_poly \<le> (1+(\<delta>+1)^\<nu>) * 2*\<delta>"
proof -
  have fin0: "finite {0..(\<delta> + 1)^\<nu>}" by simp
  {
    fix a
    assume "a \<in> {0..Suc \<delta>^\<nu>}"
    hence a: "a \<le> (\<delta>+1)^\<nu>" by auto
    have "total_degree (coding_variables.m_poly P a * \<B>_poly ^ a)
            \<le> total_degree (coding_variables.m_poly P a) + a * total_degree \<B>_poly"
      apply (rule le_trans[OF total_degree_mult add_mono])
      by (auto simp: le_trans total_degree_mult total_degree_pow)
    also have "... \<le> 2*\<delta> + (\<delta>+1)^\<nu> * (2*\<delta>)"
      apply (rule add_mono, simp add: m_poly_degree_correct[OF asm])
      apply (rule mult_mono, simp_all add: a[unfolded Suc_eq_plus1[symmetric]])
      using coding_variables.\<B>_poly_degree_correct[unfolded coding_variables.\<B>_poly_degree_def]
      by (auto simp add: mult_2)
    finally have "total_degree (coding_variables.m_poly P a * \<B>_poly ^ a)
                  \<le> 2*\<delta> + (\<delta>+1)^\<nu> * (2*\<delta>)".
  } note h0 = this

  show ?thesis
    unfolding coding_variables.M_poly_def coding_variables.n_def
    apply (rule le_trans[OF total_degree_sum[OF fin0]], simp)
    using h0 by (auto simp: mult.assoc)
qed 


definition D_exponent :: "nat list \<Rightarrow> nat" where
  "D_exponent i \<equiv> n (\<nu>+1) - (\<Sum>s\<le>\<nu>. i!s * n s)"
definition D_precoeff :: "nat list \<Rightarrow> int" where
  "D_precoeff i \<equiv> int (mfact i * fact (\<delta> - sum_list i))"
definition D :: "int" where
  "D \<equiv> \<Sum>i\<in>\<delta>_tuples. of_int (D_precoeff i * P_coeff i) * \<B>^(D_exponent i)"

definition D_poly :: "int mpoly" where 
  "D_poly \<equiv> \<Sum>i\<in>\<delta>_tuples. Const (D_precoeff i * P_coeff i) * \<B>_poly ^ (D_exponent i)"

lemma D_correct: 
  "insertion fn (coding_variables.D_poly P) = coding_variables.D P (fn 0) (fn 1)"
  unfolding D_poly_def coding_variables.D_def apply simp
  using insertion_sum[OF \<delta>_tuples_finite, of fn] apply simp
  unfolding \<B>_correct by auto

lemma D_poly_degree_env_correct:
  shows "total_degree_env fv D_poly \<le> n (\<nu>+1) * total_degree_env fv \<B>_poly"
proof -
  {
    fix a
    assume "a \<in> \<delta>_tuples"
    hence d: "D_exponent a \<le> n (\<nu>+1)"
      unfolding D_exponent_def by simp
    have "total_degree_env fv (Const (D_precoeff a * P_coeff a) * \<B>_poly ^ D_exponent a)
            \<le> D_exponent a * total_degree_env fv (\<B>_poly)"
      by (metis add_0 le_trans total_degree_env_Const total_degree_env_mult total_degree_env_pow)
    with d have "total_degree_env fv (Const (D_precoeff a * P_coeff a) * \<B>_poly ^ D_exponent a)
            \<le> n (\<nu>+1) * total_degree_env fv (\<B>_poly)"
      by (simp add: le_trans)
  } note h0 = this

  show ?thesis
    unfolding D_poly_def
    apply (rule le_trans[OF total_degree_env_sum[OF \<delta>_tuples_finite]])
    using h0 by simp
qed

lemma D_poly_degree_correct: "total_degree (coding_variables.D_poly P) \<le> (\<delta>+1)^(\<nu>+1) * (2*\<delta>)"
  unfolding total_degree_env_id[symmetric]
  apply (rule le_trans[OF D_poly_degree_env_correct], unfold total_degree_env_id n_def)
  apply (rule mult_le_mono)
  using \<B>_poly_degree_correct[unfolded \<B>_poly_degree_def] by auto


(* The K polynomial. I would have preferred to write something like "\<B> / 2"
  instead of "of_nat (\<beta> div 2) * b^\<delta>", but there is nothing quite like this: 
  "sdiv 2 \<B>" is not what we want since it divides each coefficient. *)
definition K :: "int \<Rightarrow> int" where 
  "K g \<equiv> (c g)^\<delta> * D + (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. of_nat (\<beta> div 2) * b^\<delta> * \<B>^i)"

definition K_poly :: "int mpoly" where
  "K_poly \<equiv> c_poly^\<delta> * D_poly + (\<Sum>i=0..(2*\<delta>+1)*n \<nu>. of_nat (\<beta> div 2) * b_poly^\<delta> * \<B>_poly^i)"

lemma K_correct: 
  "insertion fn (coding_variables.K_poly P) = coding_variables.K P (fn 0) (fn 1) (fn 2)"
  unfolding K_poly_def coding_variables.K_def apply simp
  unfolding c_correct D_correct b_correct \<B>_correct by auto

lemma K_poly_degree_correct:
  shows "total_degree (coding_variables.K_poly P)
  \<le> max (\<delta>*(1+2*\<delta>) + (\<delta>+1)^(\<nu>+1) * 2*\<delta>) ((1 + (2*\<delta>+1)*(\<delta>+1)^\<nu>) * 2*\<delta>)"
proof -
  have fin0: "finite {0..(2 * \<delta> + 1) * n \<nu>}" by simp

  {
    fix a
    assume "a\<in>{0..Suc \<delta> ^ \<nu> + 2 * \<delta> * Suc \<delta> ^ \<nu>}"
    hence a: "a \<le> Suc \<delta> ^ \<nu> + 2 * \<delta> * Suc \<delta> ^ \<nu>" by simp
    have "total_degree (of_nat (\<beta> div 2) * b_poly ^ \<delta> * \<B>_poly ^ a)
       \<le> 2*\<delta> + (Suc \<delta> ^ \<nu> + 2 * (\<delta> * Suc \<delta> ^ \<nu>)) * (2*\<delta>)"
      apply (rule le_trans[OF total_degree_mult add_mono])
      subgoal
        apply (rule le_trans[OF total_degree_mult], simp add: of_nat_Const)
        apply (rule le_trans[OF total_degree_pow])
        using b_poly_degree_correct[unfolded b_poly_degree_def] 
        by simp
      subgoal
        apply (rule le_trans[OF total_degree_pow], rule mult_le_mono)
        using \<B>_poly_degree_correct[unfolded \<B>_poly_degree_def]
        using a by simp_all
      done
  } note h0 = this

  show ?thesis
    unfolding K_poly_def
    apply (rule le_trans[OF total_degree_add max.mono]
        | rule le_trans[OF total_degree_diff max.mono]
        | rule le_trans[OF total_degree_mult add_mono]
        | rule le_trans[OF total_degree_pow mult_le_mono2])+
    subgoal using c_poly_degree_correct[unfolded c_poly_degree_def] by simp
    subgoal unfolding mult.assoc by (rule D_poly_degree_correct)
    apply (rule le_trans[OF total_degree_sum[OF fin0]])
    using h0 by (simp add: n_def algebra_simps) 
qed


definition T where "T \<equiv> M + (\<B>-2) * \<B>^((\<delta>+1)^(\<nu>+1)) * N0"
definition S :: "int \<Rightarrow> int" where "S g \<equiv> g + 2 * K g * N0"
definition R :: "int \<Rightarrow> int" where "R g \<equiv> (S g + T + 1)*N + T + 1"
definition X :: "int \<Rightarrow> int" where "X g \<equiv> (N-1) * R g"
definition Y :: "int" where "Y \<equiv> N^2"

poly_extract T
poly_extract S
poly_extract R
poly_extract X
poly_extract Y


text \<open>These are the statements that make up theorem I.\<close>
definition statement1_weak where 
  "statement1_weak y \<equiv> (y 0 = a) \<and> (\<forall>i. 0 \<le> y i \<and> y i < b) \<and> insertion y P = 0"
definition statement1_strong where 
  "statement1_strong y \<equiv> statement1_weak y \<and> (\<exists>i\<in>{1..\<nu>}. y i \<noteq> 0)"
text \<open>We evaluate Y in 0 because it doesn't depend on g.\<close>
definition statement2_strong where 
  "statement2_strong g \<equiv> b \<le> g \<and> g < (int \<gamma>) * b^\<alpha> \<and> Y dvd (2 * nat (X g) choose nat (X g))"
definition statement2_weak where 
  "statement2_weak g \<equiv> 0 \<le> g \<and> g < 2 * (int \<gamma>) * b^\<alpha> \<and> Y dvd (2 * nat (X g) choose nat (X g))"

lemma \<delta>_tuples_nonempty: "\<delta>_tuples \<noteq> {}"
proof -
  define i where "i \<equiv> replicate (\<nu>+1) (0::nat)"
  have "i \<in> \<delta>_tuples"
    unfolding \<delta>_tuples_def i_def
    by (smt (verit, best) in_set_replicate length_replicate less_eq_nat.simps(1) 
        mem_Collect_eq sum_list_eq_0_iff) 
  thus ?thesis by auto
qed

corollary x_series_bound:
  assumes "0 < \<delta>"
  assumes "x \<in> \<delta>_tuples"
  shows "(\<Sum>s\<le>\<nu>. x ! s * Suc \<delta> ^ s) \<le> (\<delta>+1)^(\<nu>+1)"
proof -
  from assms have "2 \<le> int (Suc \<delta>)"
    by auto
  from assms have "length x = Suc \<nu>"
    unfolding \<delta>_tuples_def by simp
  have x_bound: "\<forall>s\<le>\<nu>. (x ! s) < Suc \<delta>"
    using assms unfolding \<delta>_tuples_def
    by simp (smt (verit) elem_le_sum_list le_imp_less_Suc order_trans)
  hence x_bound2: "\<forall>k\<le>\<nu>. int (x ! k) < int (Suc \<delta>)"
    by auto
  show ?thesis
    using series_bound[of "Suc \<delta>" \<nu> "(!) x", OF \<open>2 \<le> int (Suc \<delta>)\<close> x_bound2]
    apply (subst atMost_atLeast0, subst less_imp_le, simp_all)
    apply (subst nat_int_comparison(2))
    by auto (smt (verit, del_insts) of_nat_Suc of_nat_add of_nat_mult
                 of_nat_power times_nat.simps(2))
qed

lemma D_exponent_injective:
  assumes "0 < \<delta>"
  shows "inj_on D_exponent \<delta>_tuples"
proof -
  from assms have "1 < \<delta> + 1"
    by auto

  {
    fix x y
    assume a1: "x \<in> \<delta>_tuples" and a2: "y \<in> \<delta>_tuples"
    hence l1: "length x = Suc \<nu>" and l2: "length y = Suc \<nu>"
      unfolding \<delta>_tuples_def by auto
    from a1 a2 have l3: "\<forall>s\<le>\<nu>. x ! s < \<delta> + 1" and l4: "\<forall>s\<le>\<nu>. y ! s < \<delta> + 1" 
      unfolding \<delta>_tuples_def using l1 l2 elem_le_sum_list
      by (metis (no_types, lifting) Suc_eq_plus1 le_imp_less_Suc mem_Collect_eq order_trans)+
    
    assume "(\<Sum>s\<le>\<nu>. x ! s * (\<delta> + 1) ^ s) = (\<Sum>s\<le>\<nu>. y ! s * (\<delta> + 1) ^ s)"
    hence "x = y"
      apply (subst (asm) digit_wise_gen_equiv[OF \<open>1 < \<delta> + 1\<close>])
      apply (subst (asm) atMost_atLeast0)+
      apply (subst (asm) nth_digit_gen_power_series_general[OF \<open>1 < \<delta> + 1\<close> l3])
      apply (subst (asm) nth_digit_gen_power_series_general[OF \<open>1 < \<delta> + 1\<close> l4])
      using l1 l2 l3 l4 by (metis less_Suc_eq_le nth_equalityI)
  }

  then show ?thesis
    unfolding inj_on_def D_exponent_def n_def
    using x_series_bound[OF \<open>0 < \<delta>\<close>]
  proof -
    { fix nns :: "nat list" and nnsa :: "nat list"
      have ff1: "\<And>ns. ns \<notin> \<delta>_tuples \<or> (\<Sum>n\<le>\<nu>. ns ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu>"
        using \<open>\<And>x. x \<in> \<delta>_tuples \<Longrightarrow> (\<Sum>s\<le>\<nu>. x ! s * Suc \<delta> ^ s) \<le> (\<delta> + 1) ^ (\<nu> + 1)\<close> by force
      have "\<forall>n na. \<exists>nb. \<not> (na::nat) \<le> n \<or> na + nb = n"
        using le_Suc_ex by blast
      then obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
        ff2: "\<And>n na. \<not> n \<le> na \<or> n + nn na n = na"
        by metis
      then have ff3: "\<And>n na. \<not> n \<le> na \<or> na - nn na n = n"
        by (metis (no_types) add_diff_cancel_right')
      { assume "(\<Sum>n\<le>\<nu>. nnsa ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<and> (\<Sum>n\<le>\<nu>. nns ! n * Suc \<delta> ^ n) \<noteq> (\<Sum>n\<le>\<nu>. nnsa ! n * Suc \<delta> ^ n)"
        then have "(\<Sum>n\<le>\<nu>. nns ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<longrightarrow> (\<Sum>n\<le>\<nu>. nns ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<and> Suc \<delta> ^ Suc \<nu> - nn (Suc \<delta> ^ Suc \<nu>) (\<Sum>n\<le>\<nu>. nnsa ! n * Suc \<delta> ^ n) \<noteq> (\<Sum>n\<le>\<nu>. nns ! n * Suc \<delta> ^ n)"
          using ff3 by (smt (z3))
        then have "(\<Sum>n\<le>\<nu>. nnsa ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<and> (\<Sum>n\<le>\<nu>. nns ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<longrightarrow> nns \<notin> \<delta>_tuples \<or> nnsa \<notin> \<delta>_tuples \<or> nns = nnsa \<or> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nns ! n * (\<delta> + 1) ^ n) \<noteq> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nnsa ! n * (\<delta> + 1) ^ n)"
          using ff2 by fastforce
        then have "(\<Sum>n\<le>\<nu>. nnsa ! n * Suc \<delta> ^ n) \<le> Suc \<delta> ^ Suc \<nu> \<longrightarrow> nns \<notin> \<delta>_tuples \<or> nnsa \<notin> \<delta>_tuples \<or> nns = nnsa \<or> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nns ! n * (\<delta> + 1) ^ n) \<noteq> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nnsa ! n * (\<delta> + 1) ^ n)"
          using ff1 by blast }
      then have "nns \<notin> \<delta>_tuples \<or> nnsa \<notin> \<delta>_tuples \<or> nns = nnsa \<or> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nns ! n * (\<delta> + 1) ^ n) \<noteq> (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nnsa ! n * (\<delta> + 1) ^ n)"
        using ff1 by (metis (no_types) Suc_eq_plus1 \<open>\<And>y x. \<lbrakk>x \<in> \<delta>_tuples; y \<in> \<delta>_tuples; (\<Sum>s\<le>\<nu>. x ! s * (\<delta> + 1) ^ s) = (\<Sum>s\<le>\<nu>. y ! s * (\<delta> + 1) ^ s)\<rbrakk> \<Longrightarrow> x = y\<close>) }
    then show "\<forall>ns\<in>\<delta>_tuples. \<forall>nsa\<in>\<delta>_tuples. (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. ns ! n * (\<delta> + 1) ^ n) = (\<delta> + 1) ^ (\<nu> + 1) - (\<Sum>n\<le>\<nu>. nsa ! n * (\<delta> + 1) ^ n) \<longrightarrow> ns = nsa"
      by blast
  qed
qed

corollary D_exponent_injective': "0 < \<delta> \<Longrightarrow> inj_on D_exponent (\<delta>_tuples - {x})"
  using D_exponent_injective by (rule inj_on_diff)

lemma D_precoeff_bound:
  assumes "0 < sum_list i" and "sum_list i \<le> \<delta>"
  shows "\<bar>D_precoeff i\<bar> \<le> fact \<delta>"
proof -
  have "\<delta> mchoose i \<ge> 1"
    using assms unfolding multinomial_def multinomial'_def
    by simp (metis dvd_mult_div_cancel fact_ge_Suc_0_nat mchoose_dvd mult.commute one_le_mult_iff)
  thus ?thesis
    using assms unfolding D_precoeff_def multinomial_def multinomial'_def
    by (metis abs_of_nat mchoose_le of_nat_fact of_nat_le_iff)
qed

text \<open>We later assume that \<open>\<delta> > 0\<close> i.e. P is not the zero polynomial\<close>
lemma P_coeffs_not_all_zero:
  assumes "\<delta> > 0"
  shows "\<exists>i\<in>\<delta>_tuples. P_coeff i \<noteq> 0"
proof -
  have "\<not> (\<forall>i\<in>\<delta>_tuples. P_coeff i = 0)"
  proof
    assume coeffs_zero: "\<forall>i\<in>\<delta>_tuples. P_coeff i = 0"
    { fix m assume assm: "m \<in> keys (mapping_of P)"
      then obtain i where "m = Abs_poly_mapping ((!\<^sub>0) i)" and "i\<in>\<delta>_tuples"
        using mpoly_keys_subset unfolding \<delta>_tuples_def \<delta>_def \<nu>_def by auto
      hence "P_coeff i \<noteq> 0" 
        using assm P_coeff_def by (simp add: coeff_keys)
      hence "False" 
        using coeffs_zero \<open>i\<in>\<delta>_tuples\<close> by auto }
    hence "keys (mapping_of P) = {}"
      by blast
    hence "P = 0"
      by (metis keys_eq_empty mapping_of_inverse zero_mpoly.abs_eq)
    thus "False"
       using \<open>\<delta> > 0\<close> \<delta>_def by simp
  qed
  thus ?thesis by auto
qed

lemma \<L>_pos:
  assumes "\<delta> > 0"
  shows "\<L> > 0"
proof -
  have "\<not> \<L> = 0"
  proof 
    assume "\<L> = 0"
    hence "(\<Sum>i\<in>\<delta>_tuples. abs (P_coeff i)) = 0"
      unfolding \<L>_def by (metis int_ops(1) nat_0_le sum_abs_ge_zero)
    hence "i\<in>\<delta>_tuples \<Longrightarrow> abs (P_coeff i) = 0" for i
      using sum_nonneg_eq_0_iff[OF \<delta>_tuples_finite] by (metis (full_types) abs_ge_zero)
    hence "i\<in>\<delta>_tuples \<Longrightarrow> P_coeff i = 0" for i
      by auto
    thus "False" 
      using P_coeffs_not_all_zero[OF \<open>\<delta> > 0\<close>] by auto 
  qed
  thus ?thesis by auto
qed

lemma \<L>_ge_P_coeff: "i\<in>\<delta>_tuples \<Longrightarrow> abs (P_coeff i) \<le> int \<L>" for i
proof -
  assume "i\<in>\<delta>_tuples"
  hence "abs (P_coeff i) \<le> (\<Sum>i\<in>\<delta>_tuples. abs (P_coeff i))"
    by (meson \<delta>_tuples_finite abs_ge_zero sum_nonneg_leq_bound)
  also have "... = int \<L>"
    unfolding \<L>_def by auto
  finally show ?thesis .
qed

lemma \<L>_ge_max_coeff:
  assumes "\<delta> > 0"
  shows "max_coeff P \<le> int \<L>"
proof -
  have "lookup (mapping_of P) i \<in> (P_coeff ` \<delta>_tuples) \<union> {0}" for i
  proof (cases "lookup (mapping_of P) i = 0")
    case True thus ?thesis by simp
  next
    case False
    hence "i\<in>keys (mapping_of P)" 
      by (simp add: in_keys_iff)
    thus ?thesis 
      using mpoly_keys_subset unfolding P_coeff_def MPoly_Type.coeff_def \<delta>_tuples_def \<delta>_def \<nu>_def 
      by auto
  qed
  hence 1: "coeffs P \<subseteq> P_coeff ` \<delta>_tuples" 
    unfolding coeffs_def range_def by auto

  have 2: "coeffs P \<noteq> {}"
  proof 
    assume "coeffs P = {}"
    hence "\<delta> = 0"
      unfolding \<delta>_def using coeffs_empty_iff[of "P"] by simp
    thus "False"
      using \<open>\<delta> > 0\<close> by auto
  qed

  from \<L>_ge_P_coeff 1 2 show ?thesis
    unfolding max_coeff_def by auto
qed

lemma \<beta>_lower_bound: "\<beta> > 2 * fact \<delta> * \<L> * (\<nu>+3)^\<delta>"
proof -
  define S where "S \<equiv> {y. 4^y > 2 * fact \<delta> * \<L> * (\<nu> + 3)^\<delta>}"
 
  have "2 * fact \<delta> * \<L> * (\<nu> + 3)^\<delta> \<in> S"
    unfolding S_def using power_gt_expt by auto
  hence "S \<noteq> {}"
    by auto
  hence "Inf S \<in> S"
    by (simp add: Inf_nat_def1)
  hence "r \<in> S"
    using r_def S_def by simp
  thus ?thesis 
    unfolding S_def \<beta>_def by simp
qed

corollary r_pos:
  assumes "\<delta> > 0"
  shows "r > 0"
  using \<beta>_lower_bound \<beta>_def \<L>_pos[OF \<open>\<delta> > 0\<close>] zero_less_iff_neq_zero by fastforce


lemma marcos_state: 
  fixes i 
  shows "total_degree_env 
  (\<lambda>m. total_degree_env (\<lambda>_. Suc 0) ([Var 0, Var 1, Var 2] !\<^sub>0 m)) 
  ([Var 0, Var 1, Var 2] !\<^sub>0 i) \<le> 1"
proof -
  have 1: "[Var 0, Var 1, Var 2] !\<^sub>0 m = map Var [0, 1, 2] !\<^sub>0 m" for m 
    apply auto done

  have aux: "(\<lambda>m. total_degree_env (\<lambda>_. Suc 0) (map Var [0, 1, 2] !\<^sub>0 m)) = 
        (\<lambda>m. if m < length [0, 1, 2] then 1 else 0)" 
    by (metis One_nat_def length_Cons list.size(3) total_degree_env_Var_list)

  show ?thesis
    apply (rule le_trans[of _ "total_degree_env (\<lambda>m. if m < length [0, 1, 2] then 1 else 0) ([Var 0, Var 1, Var 2] !\<^sub>0 i)"])
    subgoal 
      apply simp
      using aux
      by (smt (z3) "1" Suc_1 Suc_eq_plus1 dual_order.refl le_less_Suc_eq less_2_cases 
          linorder_not_less list.size(3,4) nth0_0
          nth0_Cons_0 nth0_Cons_Suc total_degree_env_Var total_degree_env_zero)
    subgoal 
      by (smt (verit, del_insts) One_nat_def Suc_leI Suc_le_mono add.right_neutral add_Suc_right antisym_conv1
          bot_nat_0.not_eq_extremum list.size(3,4) nth0_0 nth0_Cons_0 nth0_Cons_Suc total_degree_env_Var
          total_degree_env_zero)
    done
qed

end

end