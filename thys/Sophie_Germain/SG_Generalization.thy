
(* Author: Benoît Ballenghien, Université Paris-Saclay, CNRS, ENS Paris-Saclay, LMF *)

(*<*)
theory SG_Generalization
  imports SG_Theorem
begin 
  (*>*)


section \<open>Sophie Germain's Theorem: generalized Version\<close>

text \<open>The proof we give here is from \<^cite>\<open>kiefer2012theoreme\<close>.\<close>

subsection \<open>Auxiliary Primes\<close>

abbreviation non_consecutivity_condition :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>NC\<close>)
  where \<open>NC p q \<equiv> \<nexists>x y :: int. [x \<noteq> 0] (mod q) \<and> [y \<noteq> 0] (mod q) \<and> [x ^ p = 1 + y ^ p] (mod q)\<close>

lemma non_consecutivity_condition_bis :
  \<open>NC p q \<longleftrightarrow> (\<nexists>x y a b. [a :: int \<noteq> 0] (mod q) \<and> [a ^ p = x] (mod q) \<and>
                         [b :: int \<noteq> 0] (mod q) \<and> [b ^ p = y] (mod q) \<and> [x = 1 + y] (mod q))\<close>
  by (simp add: cong_def) (metis mod_add_right_eq)


abbreviation not_pth_power :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>PPP\<close>)
  where \<open>PPP p q \<equiv> \<nexists>x :: int. [p = x ^ p] (mod q)\<close>



definition auxiliary_prime :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>aux'_prime\<close>)
  where \<open>aux_prime p q \<equiv> prime p \<and> prime q \<and> NC p q \<and> PPP p q\<close>

lemma auxiliary_primeI :
  \<open>\<lbrakk>prime p; prime q; NC p q; PPP p q\<rbrakk> \<Longrightarrow> aux_prime p q\<close>
  unfolding auxiliary_prime_def by auto

lemma auxiliary_primeD :
  \<open>prime p\<close> \<open>prime q\<close> \<open>NC p q\<close> \<open>PPP p q\<close> if \<open>aux_prime p q\<close>
  using that by (auto simp add: auxiliary_prime_def)


text \<open>We do not give code equation yet, let us first work around these notions.\<close>



lemma gen_mult_group_mod_prime_as_ord : \<open>ord p g = p - 1\<close>
  if \<open>prime p\<close> \<open>{1 .. p - 1} = {g ^ k mod p |k. k \<in> UNIV}\<close>
proof -
  from that(2) have \<open>g mod p \<in> {1 .. p - 1}\<close>
    by (simp add: set_eq_iff) (metis power_one_right)
  hence \<open>[g \<noteq> 0] (mod p)\<close> by (simp add: cong_def)

  with cong_0_iff prime_imp_coprime \<open>prime p\<close>
  have \<open>ord p g = (LEAST d. 0 < d \<and> [g ^ d = 1] (mod p))\<close>
    unfolding ord_def by auto
  also have \<open>\<dots> = p - 1\<close>
  proof (rule ccontr)
    assume \<open>(LEAST d. 0 < d \<and> [g ^ d = 1] (mod p)) \<noteq> p - 1\<close>
    with fermat_theorem \<open>prime p\<close> \<open>[g \<noteq> 0] (mod p)\<close>
    obtain k where \<open>0 < k\<close> \<open>k < p - 1\<close> \<open>[g ^ k = 1] (mod p)\<close>
      by (metis calculation cong_0_iff coprime_ord linorder_neqE_nat
          lucas_coprime_lemma ord_minimal prime_gt_1_nat zero_less_diff)
    { fix l m
      have \<open>g ^ (m + (l * k)) mod p = (g ^ m mod p * ((g ^ k) ^ l mod p)) mod p\<close>
        by (simp add: mod_mult_eq mult.commute power_add power_mult)
      also from \<open>[g ^ k = 1] (mod p)\<close> have \<open>((g ^ k) ^ l mod p) = 1\<close>
        by (metis cong_def cong_pow mod_if power_one prime_nat_iff \<open>prime p\<close>)
      finally have \<open>g ^ (m + (l * k)) mod p = g ^ m mod p\<close> by simp
    } note $ = this

    have \<open>UNIV = (\<Union>l. {m + (l * k) |m. m \<in> {0..k - 1}})\<close>
      by auto (metis Suc_pred \<open>0 < k\<close> add.commute div_mod_decomp mod_Suc_le_divisor)
    hence \<open>{g ^ k mod p |k. k \<in> UNIV} =
             (\<Union>l. {g ^ (m + (l * k)) mod p |m. m \<in> {0..k - 1}})\<close>
      by (simp add: set_eq_iff) metis
    also have \<open>\<dots> = {g ^ m mod p |m. m \<in> {0..k - 1}}\<close> by (simp add: "$") 
    finally have \<open>card {g ^ k mod p |k. k \<in> UNIV} = card \<dots>\<close> by simp
    also have \<open>{g ^ m mod p |m. m \<in> {0..k - 1}} =
                 (\<lambda>m. g ^ m mod p) ` {0..k - 1}\<close> by auto
    also from card_image_le have \<open>card \<dots> \<le> card {0..k - 1}\<close> by blast
    also have \<open>\<dots> = k\<close> by (simp add: \<open>0 < k\<close>)
    finally show False
      by (metis that(2) \<open>k < p - 1\<close> card_atLeastAtMost diff_Suc_1 linorder_not_less)
  qed
  finally show \<open>ord p g = p - 1\<close> .
qed


lemma exists_nth_power_mod_prime_iff :
  fixes p n assumes \<open>prime p\<close>
  defines d_def : \<open>d \<equiv> gcd n (p - 1)\<close>
  shows \<open>(\<exists>x :: int. [a = x ^ n] (mod p)) \<longleftrightarrow>
         (n \<noteq> 0 \<and> [a = 0] (mod p)) \<or> [a ^ ((p - 1) div d) = 1] (mod p)\<close>
proof (cases \<open>n = 0\<close>)
  show \<open>n = 0 \<Longrightarrow> ?thesis\<close>
    by (simp add: d_def)
      (metis \<open>prime p\<close> Suc_0_not_prime_nat Suc_pred div_self power_one_right prime_gt_0_nat)
next
  show ?thesis if \<open>n \<noteq> 0\<close>
  proof (cases \<open>[a = 0] (mod p)\<close>)
    show \<open>[a = 0] (mod p) \<Longrightarrow> ?thesis\<close>
      by (auto simp add: cong_def power_0_left \<open>n \<noteq> 0\<close> intro!: exI[of _ 0])
  next
    have \<open>0 < int p\<close> by (simp add: prime_gt_0_nat \<open>prime p\<close>)
    from \<open>prime p\<close> residue_prime_mult_group_has_gen gen_mult_group_mod_prime_as_ord
    obtain g where * : \<open>{1 .. p - 1} = {g ^ k mod p |k. k \<in> UNIV}\<close> and \<open>ord p g = p - 1\<close> by blast
    have \<open>[g \<noteq> 0] (mod p)\<close>
      by (metis \<open>ord p g = p - 1\<close> \<open>prime p\<close> nat_less_le ord_0_right_nat
          ord_cong prime_nat_iff zero_less_diff)

    show \<open>?thesis\<close> if \<open>[a \<noteq> 0] (mod p)\<close>
    proof (rule iffI)
      assume \<open>\<exists>x. [a = x ^ n] (mod p)\<close>
      then obtain x where \<open>[a = x ^ n] (mod p)\<close> ..
      from cong_less_unique_int[OF \<open>0 < int p\<close>, of x]
      obtain y :: nat where \<open>0 \<le> y\<close> \<open>y < p\<close> \<open>[x = y] (mod p)\<close>
        by (metis int_nat_eq less_eq_nat.simps(1) nat_less_iff)
      from \<open>[a \<noteq> 0] (mod p)\<close> \<open>[a = x ^ n] (mod p)\<close> have \<open>[x \<noteq> 0] (mod p)\<close>
        by (metis cong_pow cong_sym cong_trans power_0_left \<open>n \<noteq> 0\<close>)
      with \<open>[x = y] (mod p)\<close> have \<open>y \<noteq> 0\<close> by (metis of_nat_0)
      with \<open>0 \<le> y\<close> \<open>y < p\<close> have \<open>y \<in> {1 .. p - 1}\<close> by simp
      with "*" \<open>[x = y] (mod p)\<close> zmod_int obtain k where \<open>[x = g ^ k] (mod p)\<close> by auto

      with \<open>[a = x ^ n] (mod p)\<close> have \<open>[a = g ^ (k * n)] (mod p)\<close>
        by (metis (no_types, lifting) cong_pow cong_trans of_nat_power power_mult)
      hence \<open>[a ^ ((p - 1) div d) = (g ^ (k * n)) ^ ((p - 1) div d)] (mod p)\<close>
        by (simp add: cong_pow)
      moreover have \<open>[(g ^ (k * n)) ^ ((p - 1) div d) = g ^ (k * n * (p - 1) div d)] (mod p)\<close>
        by (metis (no_types) d_def cong_refl div_mult_swap gcd_dvd2 power_mult)
      moreover have \<open>[g ^ (k * n * (p - 1) div d) = (g ^ (k * n div d)) ^ (p - 1)] (mod p)\<close>
        by (metis (no_types) d_def cong_def dvd_div_mult dvd_mult gcd_dvd1 power_mult)
      moreover have \<open>[(g ^ (k * n div d)) ^ (p - 1) = 1] (mod p)\<close>
        by (rule fermat_theorem[OF \<open>prime p\<close>])
          (metis \<open>[g \<noteq> 0] (mod p)\<close> cong_0_iff prime_dvd_power_nat \<open>prime p\<close>)
      ultimately have \<open>[a ^ ((p - 1) div d) = 1] (mod p)\<close>
        by (metis (no_types, opaque_lifting) cong_def cong_int_iff of_nat_1)
      thus \<open> n \<noteq> 0 \<and> [a = 0] (mod p) \<or> [a ^ ((p - 1) div d) = 1] (mod p)\<close> ..
    next
      assume \<open> n \<noteq> 0 \<and> [a = 0] (mod p) \<or> [a ^ ((p - 1) div d) = 1] (mod p)\<close>
      with \<open>[a \<noteq> 0] (mod p)\<close> have \<open>[a ^ ((p - 1) div d) = 1] (mod p)\<close> by blast

      from cong_less_unique_int[OF \<open>0 < int p\<close>, of a]
      obtain b :: nat where \<open>0 \<le> b\<close> \<open>b < p\<close> \<open>[a = b] (mod p)\<close>
        by (metis int_nat_eq less_eq_nat.simps(1) nat_less_iff)
      from \<open>[a \<noteq> 0] (mod p)\<close> \<open>[a = b] (mod p)\<close> have \<open>b \<noteq> 0\<close> by (metis of_nat_0)
      with \<open>0 \<le> b\<close> \<open>b < p\<close> have \<open>b \<in> {1 .. p - 1}\<close> by simp
      with "*" have \<open>b \<in> {g ^ k mod p |k. k \<in> UNIV}\<close> by blast
      with \<open>[a = b] (mod p)\<close> zmod_int obtain k where \<open>[a = g ^ k] (mod p)\<close> by auto
      from this[THEN cong_pow, of \<open>(p - 1) div d\<close>] \<open>[a ^ ((p - 1) div d) = 1] (mod p)\<close>
      have \<open>[(g ^ k) ^ ((p - 1) div d) = 1] (mod p)\<close>
        by (simp flip: cong_int_iff) (metis (no_types) cong_def)
      hence \<open>[g ^ (k * (p - 1) div d) = 1] (mod p)\<close>
        by (metis (no_types) d_def div_mult_swap gcd_dvd2 power_mult)
      hence \<open>p - 1 dvd k * (p - 1) div d\<close>
        by (simp add: ord_divides' \<open>ord p g = p - 1\<close>)
      hence \<open>d dvd k\<close>
        by (metis \<open>prime p\<close> d_def div_mult_swap dvd_div_eq_0_iff dvd_mult_div_cancel
            dvd_times_right_cancel_iff gcd_dvd2 less_numeral_extra(3) prime_gt_1_nat zero_less_diff)
      then obtain l where \<open>k = l * d\<close> by (metis dvd_div_mult_self)
      moreover from bezout_nat[OF \<open>n \<noteq> 0\<close>]
      obtain u v where \<open>u * n = v * (p - 1) + d\<close> by (metis d_def mult.commute)
      ultimately have \<open>l * u * n = l * v * (p - 1) + k\<close>
        by (metis distrib_left mult.assoc)
      hence \<open>(g ^ (l * u)) ^ n = (g ^ (l * v)) ^ (p - 1) * g ^ k\<close>
        by (metis power_add power_mult)
      hence \<open>[(g ^ (l * u)) ^ n = (g ^ (l * v)) ^ (p - 1) * g ^ k] (mod p)\<close> by simp
      moreover have \<open>[(g ^ (l * v)) ^ (p - 1) = 1] (mod p)\<close>
        by (metis \<open>ord p g = p - 1\<close> dvd_triv_right ord_divides power_mult)
      ultimately have \<open>[(g ^ (l * u)) ^ n = g ^ k] (mod p)\<close>
        by (metis cong_scalar_right cong_trans mult_1)
      with \<open>[a = g ^ k] (mod p)\<close> have \<open>[a = (g ^ (l * u)) ^ n] (mod p)\<close>
        by (meson cong_int_iff cong_sym cong_trans)
      thus \<open>\<exists>x. [a = x ^ n] (mod p)\<close> by auto
    qed
  qed
qed


corollary not_pth_power_iff :
  \<open>PPP p q \<longleftrightarrow> [p \<noteq> 0] (mod q) \<and> [p ^ ((q - 1) div gcd p (q - 1)) \<noteq> 1] (mod q)\<close>
  if \<open>prime p\<close> \<open>prime q\<close>
  by (subst exists_nth_power_mod_prime_iff[OF \<open>prime q\<close>, of p p])
    (metis cong_int_iff not_prime_0 of_nat_0 of_nat_1 of_nat_power \<open>prime p\<close>)

corollary not_pth_power_iff_mod :
  \<open>PPP p q \<longleftrightarrow> \<not> q dvd p \<and> p ^ ((q - 1) div gcd p (q - 1)) mod q \<noteq> 1\<close>
  if \<open>prime p\<close> and \<open>prime q\<close>
  by (subst not_pth_power_iff[OF \<open>prime p\<close> \<open>prime q\<close>])
    (simp add: cong_def mod_eq_0_iff_dvd prime_gt_Suc_0_nat)


lemma non_consecutivity_condition_iff_enum_mod :
  \<comment> \<open>This version is oriented towards code generation.\<close>
  \<open>NC p q \<longleftrightarrow>
   (\<forall>x \<in> {1..q - 1}. let x_p_mod = x ^ p mod q
                      in \<forall>y \<in> {1..q - 1}. x_p_mod \<noteq> (1 + y ^ p mod q) mod q)\<close>
  if \<open>q \<noteq> 0\<close>
proof (unfold Let_def, intro iffI conjI ballI)
  fix x y assume \<open>NC p q\<close> \<open>x \<in> {1..q - 1}\<close> \<open> y \<in> {1..q - 1}\<close>
  show \<open>x ^ p mod q \<noteq> (1 + y ^ p mod q) mod q\<close>
  proof (rule ccontr)
    assume \<open>\<not> x ^ p mod q \<noteq> (1 + y ^ p mod q) mod q\<close>
    hence \<open>[x ^ p = 1 + y ^ p] (mod q)\<close>
      by (simp add: cong_def) presburger
    with \<open>NC p q\<close> have \<open>[x = 0] (mod q) \<or> [y = 0] (mod q)\<close>
      by (metis (mono_tags, opaque_lifting) cong_int_iff int_ops(1)
          of_nat_Suc of_nat_power_eq_of_nat_cancel_iff plus_1_eq_Suc)
    with cong_less_modulus_unique_nat
    have \<open>x \<notin> {1..q - 1} \<or> y \<notin> {1..q - 1}\<close> by force
    with \<open>x \<in> {1..q - 1}\<close> \<open> y \<in> {1..q - 1}\<close> show False by blast
  qed
next
  show \<open>NC p q\<close> if * : \<open>\<forall>x\<in>{1..q - 1}. \<forall>y\<in>{1..q - 1}. x ^ p mod q \<noteq> (1 + y ^ p mod q) mod q\<close>
  proof (rule ccontr)
    assume \<open>\<not> NC p q\<close>
    then obtain x y :: int where \<open>[x \<noteq> 0] (mod q)\<close> \<open>[y \<noteq> 0] (mod q)\<close>
      \<open>[x ^ p = 1 + y ^ p] (mod q)\<close> by blast

    from \<open>[x \<noteq> 0] (mod q)\<close> \<open>q \<noteq> 0\<close> have \<open>x mod q \<in> {1..q - 1}\<close>
      by (simp add: cong_0_iff)
        (metis linorder_not_le mod_by_1 mod_eq_0_iff_dvd
          mod_pos_pos_trivial of_nat_0_less_iff pos_mod_sign)
    then obtain x' :: nat where \<open>x' \<in> {1..q - 1}\<close> \<open>x' = x mod q\<close>
      by (cases \<open>x mod q\<close>) simp_all

    from \<open>[y \<noteq> 0] (mod q)\<close> \<open>q \<noteq> 0\<close> have \<open>y mod q \<in> {1..q - 1}\<close>
      by (simp add: cong_0_iff)
        (metis linorder_not_le mod_by_1 mod_eq_0_iff_dvd
          mod_pos_pos_trivial of_nat_0_less_iff pos_mod_sign)
    then obtain y' :: nat where \<open>y' \<in> {1..q - 1}\<close> \<open>y' = y mod q\<close>
      by (cases \<open>y mod q\<close>) simp_all

    from \<open>[x ^ p = 1 + y ^ p] (mod q)\<close>
    have \<open>(x mod q) ^ p mod q = (1 + (y mod q) ^ p mod q) mod q\<close>
      by (simp add: cong_def mod_add_right_eq power_mod)
    hence \<open>x' ^ p mod q = (1 + y' ^ p mod q) mod q\<close>
      by (metis \<open>x' = x mod int q\<close> \<open>y' = y mod int q\<close> nat_mod_as_int
          of_nat_Suc of_nat_power plus_1_eq_Suc zmod_int)
    with "*" \<open>x' \<in> {1..q - 1}\<close> \<open>y' \<in> {1..q - 1}\<close> show False by blast
  qed
qed


lemma auxiliary_prime_iff_enum_mod [code] :
  \<comment> \<open>We will have a more optimized version later.\<close>
  \<open>aux_prime p q \<longleftrightarrow>
   prime p \<and> prime q \<and>
   \<not> q dvd p \<and> p ^ ((q - 1) div gcd p (q - 1)) mod q \<noteq> 1 \<and>
   (\<forall>x \<in> {1..q - 1}. let x_p_mod = x ^ p mod q
                      in \<forall>y \<in> {1..q - 1}. x_p_mod \<noteq> (1 + y ^ p mod q) mod q)\<close>
proof (cases \<open>prime p\<close>; cases \<open>prime q\<close>)
  assume \<open>prime p\<close> and \<open>prime q\<close>
  from \<open>prime q\<close> have \<open>q \<noteq> 0\<close> by auto
  show ?thesis
    unfolding auxiliary_prime_def not_pth_power_iff_mod[OF \<open>prime p\<close> \<open>prime q\<close>]
      non_consecutivity_condition_iff_enum_mod[OF \<open>q \<noteq> 0\<close>] by blast
next
  show \<open>\<not> prime q \<Longrightarrow> ?thesis\<close>
    and \<open>\<not> prime q \<Longrightarrow> ?thesis\<close>
    and \<open>\<not> prime p \<Longrightarrow> ?thesis\<close>
    by (simp_all add: auxiliary_prime_def)
qed


text \<open>We can for example compute pairs of auxiliary primes less than \<^term>\<open>110 :: nat\<close>.\<close>

value \<open>[(p, q). p \<leftarrow> [1..110], q \<leftarrow> [1..110], aux_prime (nat p) (nat q)]\<close>


lemma auxiliary_primeI' :
  \<open>\<lbrakk>prime p; prime q; \<not> q dvd p; p ^ ((q - 1) div gcd p (q - 1)) mod q \<noteq> 1;
    \<And>x y. x \<in> {1..q - 1} \<Longrightarrow> y \<in> {1..q - 1} \<Longrightarrow> [x ^ p \<noteq> 1 + y ^ p] (mod q)\<rbrakk>
   \<Longrightarrow> aux_prime p q\<close>
  by (simp add: auxiliary_prime_iff_enum_mod cong_def mod_Suc_eq)



lemma two_is_not_auxiliary_prime : \<open>\<not> aux_prime p 2\<close>
  by (simp add: auxiliary_prime_iff_enum_mod) presburger


lemma auxiliary_prime_of_2 : \<open>aux_prime 2 q \<longleftrightarrow> q = 3 \<or> q = 5\<close>
proof (rule iffI)
  show \<open>q = 3 \<or> q = 5 \<Longrightarrow> aux_prime 2 q\<close>
  proof (elim disjE)
    show \<open>q = 3 \<Longrightarrow> aux_prime 2 q\<close>
    proof (intro auxiliary_primeI')
      show \<open>prime (2 :: nat)\<close> and \<open>q = 3 \<Longrightarrow> prime q\<close> by simp_all
    next
      fix x y assume \<open>q = 3\<close> \<open>x \<in> {1..q - 1}\<close> \<open>y \<in> {1..q - 1}\<close>
      hence \<open>x = 1 \<and> y = 1 \<or> x = 1 \<and> y = 2 \<or> x = 2 \<and> y = 1 \<or> x = 2 \<and> y = 2\<close>
        by simp (metis le_Suc_eq le_antisym numeral_2_eq_2)
      with \<open>q = 3\<close> show \<open>[x\<^sup>2 \<noteq> 1 + y\<^sup>2] (mod q)\<close>
        by (fastforce simp add: cong_def)
    next
      show \<open>q = 3 \<Longrightarrow> \<not> q dvd 2\<close> by simp
    next
      show \<open>q = 3 \<Longrightarrow> 2 ^ ((q - 1) div gcd 2 (q - 1)) mod q \<noteq> 1\<close> by simp
    qed
  next
    show \<open>q = 5 \<Longrightarrow> aux_prime 2 q\<close>
    proof (intro auxiliary_primeI')
      show \<open>prime (2 :: nat)\<close> and \<open>q = 5 \<Longrightarrow> prime q\<close> by simp_all
    next
      fix x y assume \<open>q = 5\<close> \<open>x \<in> {1..q - 1}\<close> \<open>y \<in> {1..q - 1}\<close>
      hence \<open>(x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4) \<and> (y = 1 \<or> y = 2 \<or> y = 3 \<or> y = 4)\<close>
        by (simp add: numeral_eq_Suc) linarith
      with \<open>q = 5\<close> show \<open>[x\<^sup>2 \<noteq> 1 + y\<^sup>2] (mod q)\<close>
        by (fastforce simp add: cong_def)
    next
      show \<open>q = 5 \<Longrightarrow> \<not> q dvd 2\<close> by simp
    next
      show \<open>q = 5 \<Longrightarrow> 2 ^ ((q - 1) div gcd 2 (q - 1)) mod q \<noteq> 1\<close> by simp
    qed
  qed
next
  assume aux_q : \<open>aux_prime 2 q\<close>
  with two_is_not_auxiliary_prime have \<open>q \<noteq> 2\<close> by blast
  show \<open>q = 3 \<or> q = 5\<close>
  proof (rule ccontr)
    assume \<open>\<not> (q = 3 \<or> q = 5)\<close>
    with \<open>q \<noteq> 2\<close> auxiliary_primeD(1-2)[OF aux_q] prime_prime_factor
      le_neq_implies_less prime_ge_2_nat
    have \<open>prime q\<close> \<open>odd q\<close> \<open>2 < q\<close> by metis+

    hence \<open>5 \<le> q\<close>
      by (metis Suc_1 \<open>\<not> (q = 3 \<or> q = 5)\<close> add.commute add_Suc_right eval_nat_numeral(3)
          even_numeral not_less_eq_eq numeral_Bit0 order_antisym_conv plus_1_eq_Suc prime_ge_2_nat)
    with \<open>prime q\<close> have \<open>gcd 4 q = (1 :: int)\<close>
      by (metis coprime_imp_gcd_eq_1 eval_nat_numeral(3) gcd.commute less_Suc_eq
          of_nat_1 order_less_le_trans prime_nat_iff'' zero_less_numeral)
    with cong_solve_dvd_int obtain inv_4 :: int
      where inv_4: \<open>[4 * inv_4 = 1] (mod q)\<close>
      by (metis dvd_refl gcd_int_int_eq of_nat_numeral)
    define x where \<open>x \<equiv> 1 + inv_4\<close>
    define y where \<open>y \<equiv> 1 - inv_4\<close>

    from inv_4 have \<open>[x\<^sup>2 = 1 + y\<^sup>2] (mod q)\<close>
      by (simp add: x_def y_def power2_eq_square cong_iff_dvd_diff ring_class.ring_distribs)
    moreover obtain x' y' :: nat where \<open>[x' = x] (mod q)\<close> \<open>[y' = y] (mod q)\<close>
      by (metis \<open>prime q\<close> cong_less_unique_int cong_sym int_eq_iff of_nat_0_less_iff prime_gt_0_nat)
    ultimately have \<open>[x'\<^sup>2 = 1 + y'\<^sup>2] (mod q)\<close>
      by (simp flip: cong_int_iff)
        (meson cong_add cong_pow cong_refl cong_sym_eq cong_trans)
    moreover have \<open>[x' \<noteq> 0] (mod q)\<close>
    proof (rule ccontr)
      assume \<open>\<not> [x' \<noteq> 0] (mod q)\<close>
      with \<open>[x' = x] (mod q)\<close> have \<open>[x = 0] (mod q)\<close>
        by (metis cong_0_iff cong_dvd_iff int_dvd_int_iff)
      hence \<open>[4 * x = 0] (mod q)\<close>
        by (metis cong_scalar_left mult_zero_right)
      with cong_add[OF cong_refl[of 4] inv_4] have \<open>q dvd 5\<close>
        by (simp add: x_def) (metis cong_0_iff cong_dvd_iff int_ops(3) of_nat_dvd_iff)
      with \<open>prime q\<close> have \<open>q = 5\<close> by (auto intro: primes_dvd_imp_eq)
      with \<open>\<not> (q = 3 \<or> q = 5)\<close> show False by blast
    qed
    moreover have \<open>[y' \<noteq> 0] (mod q)\<close>
    proof (rule ccontr)
      assume \<open>\<not> [y' \<noteq> 0] (mod q)\<close>
      with \<open>[y' = y] (mod q)\<close> have \<open>[y = 0] (mod q)\<close>
        by (metis cong_0_iff cong_dvd_iff int_dvd_int_iff)
      hence \<open>[4 * y = 0] (mod q)\<close>
        by (metis cong_scalar_left mult_zero_right)
      with cong_diff[OF cong_refl[of 4] inv_4] have \<open>q dvd 3\<close>
        by (simp add: y_def) (metis cong_0_iff cong_dvd_iff int_ops(3) of_nat_dvd_iff)
      with \<open>prime q\<close> have \<open>q = 3\<close> by (auto intro: primes_dvd_imp_eq)
      with \<open>\<not> (q = 3 \<or> q = 5)\<close> show False by blast
    qed
    ultimately have \<open>[(int x')\<^sup>2 = 1 + (int y')\<^sup>2] (mod q) \<and>
      [int x' \<noteq> 0] (mod q) \<and> [int y' \<noteq> 0] (mod q)\<close>
      by (metis cong_int_iff of_nat_0 of_nat_Suc of_nat_power plus_1_eq_Suc)
    with auxiliary_primeD(3) aux_q show False by blast
  qed
qed




text \<open>An auxiliary prime \<open>q\<close> of \<open>p\<close> is generally of the form \<^term>\<open>q = 2 * n * p + 1\<close>.\<close>

lemma auxiliary_prime_pattern_aux :
  \<open>\<exists>x y. [x \<noteq> 0] (mod q) \<and> [y \<noteq> 0] (mod q) \<and> [x ^ p = 1 + y ^ p] (mod q)\<close>
  if \<open>p \<noteq> 0\<close> \<open>prime q\<close> \<open>coprime p (q - 1)\<close> \<open>odd q\<close>
proof -
  from bezout_nat \<open>coprime p (q - 1)\<close> \<open>p \<noteq> 0\<close>
  obtain u v where bez : \<open>u * p = 1 + v * (q - 1)\<close>
    by (metis add.commute coprime_imp_gcd_eq_1 mult.commute)
  have \<open>[x \<noteq> 0] (mod q) \<Longrightarrow> [(x ^ v) ^ (q - 1) = 1] (mod q)\<close> for x
    by (meson cong_0_iff fermat_theorem prime_dvd_power \<open>prime q\<close>)
  hence * : \<open>[(x ^ u) ^ p = x] (mod q)\<close> for x
    by (fold power_mult, unfold bez, unfold power_add power_mult)
      (metis cong_0_iff cong_def cong_scalar_left \<open>prime q\<close>
        mult.right_neutral power_one_right prime_dvd_mult_iff)
  obtain x0 y0 where \<open>[x0 \<noteq> 0] (mod q)\<close> \<open>[y0 \<noteq> 0] (mod q)\<close> \<open>[x0 = 1 + y0] (mod q)\<close>
    by (metis \<open>odd q\<close> \<open>prime q\<close> cong_0_iff cong_refl not_prime_unit
        one_add_one prime_prime_factor two_is_prime_nat)
  from "*" this(3) have \<open>[(x0 ^ u) ^ p = 1 + (y0 ^ u) ^ p] (mod q)\<close>
    by (metis cong_add_lcancel_nat cong_def)
  moreover from \<open>[x0 \<noteq> 0] (mod q)\<close> \<open>[y0 \<noteq> 0] (mod q)\<close>
  have \<open>[x0 ^ u \<noteq> 0] (mod q)\<close> \<open>[y0 ^ u \<noteq> 0] (mod q)\<close>
    by (meson cong_0_iff prime_dvd_power \<open>prime q\<close>)+
  ultimately show ?thesis by blast
qed


theorem auxiliary_prime_pattern :
  \<open>p = 2 \<and> (q = 3 \<or> q = 5) \<or> odd p \<and> (\<exists>n\<ge>1. q = 2 * n * p + 1)\<close> if aux_p : \<open>aux_prime p q\<close>
proof -
  from auxiliary_prime_of_2 consider \<open>p = 2\<close> \<open>q = 3 \<or> q = 5\<close> | \<open>odd p\<close> \<open>q \<noteq> 2\<close>
    by (metis aux_p auxiliary_prime_def prime_prime_factor two_is_not_auxiliary_prime)
  thus ?thesis
  proof cases
    show \<open>p = 2 \<Longrightarrow> q = 3 \<or> q = 5 \<Longrightarrow> ?thesis\<close> by blast
  next
    assume \<open>odd p\<close> \<open>q \<noteq> 2\<close>
    have \<open>2 < q\<close> \<open>odd q\<close>
      by (use \<open>q \<noteq> 2\<close> auxiliary_prime_def le_neq_implies_less prime_ge_2_nat that in presburger)
        (metis \<open>q \<noteq> 2\<close> auxiliary_prime_def prime_prime_factor that two_is_prime_nat)
    from aux_p have \<open>prime p\<close> and \<open>prime q\<close> by (simp_all add: auxiliary_primeD(1-2))
    from euler_criterion[OF \<open>prime q\<close> \<open>2 < q\<close>]
    have * : \<open>[Legendre p q = p ^ ((q - 1) div 2)] (mod q)\<close> by simp
    have \<open>\<not> coprime p (q - 1)\<close>
      by (metis auxiliary_prime_def cong_0_iff coprime_iff_gcd_eq_1
          div_by_1 fermat_theorem not_pth_power_iff aux_p)
    with \<open>prime p\<close> prime_imp_coprime have \<open>p dvd q - 1\<close> by blast
    then obtain k where \<open>q = k * p + 1\<close>
      by (metis add.commute \<open>prime q\<close> dvd_div_mult_self
          le_add_diff_inverse less_or_eq_imp_le prime_gt_1_nat)
    with \<open>odd q\<close> \<open>odd p\<close> have \<open>even k\<close> by simp
    then obtain n where \<open>k = 2 * n\<close> by fast
    with \<open>q = k * p + 1\<close> have \<open>q = 2 * n * p + 1\<close> by blast
    with \<open>2 < q\<close> have \<open>1 \<le> n\<close> 
      by (metis One_nat_def add.commute less_one linorder_not_less
          mult_is_0 one_le_numeral plus_1_eq_Suc)
    with \<open>odd p\<close> \<open>q = 2 * n * p + 1\<close> show ?thesis by blast
  qed
qed



lemma auxiliary_prime_imp_less : \<open>aux_prime p q \<Longrightarrow> p < q\<close>
  by (auto dest: auxiliary_prime_pattern simp add: less_Suc_eq)

lemma auxiliary_primeE :
  assumes \<open>aux_prime p q\<close>
  obtains \<open>p = 2\<close> \<open>q = 3\<close> | \<open>p = 2\<close> \<open>q = 5\<close>
  | n where \<open>odd p\<close> \<open>1 \<le> n\<close> \<open>q = 2 * n * p + 1\<close>
    \<open>NC p (2 * n * p + 1)\<close> \<open>PPP p (2 * n * p + 1)\<close>
  by (metis assms auxiliary_prime_def auxiliary_prime_pattern)



text \<open>With this, we can quickly eliminate numbers that cannot be auxiliary.\<close>

declare auxiliary_prime_iff_enum_mod [code del]

lemma auxiliary_prime_iff_enum_mod_optimized [code] :
  \<open>aux_prime p q \<longleftrightarrow>
   p = 2 \<and> (q = 3 \<or> q = 5) \<or>
   p < q \<and>
   2 * p dvd q - 1 \<and>
   prime p \<and> prime q \<and>
   \<not> q dvd p \<and> p ^ ((q - 1) div gcd p (q - 1)) mod q \<noteq> 1 \<and>
   (\<forall>x \<in> {1..q - 1}. let x_p_mod = x ^ p mod q
                      in \<forall>y \<in> {1..q - 1}. x_p_mod \<noteq> (1 + y ^ p mod q) mod q)\<close>
  by (fold auxiliary_prime_iff_enum_mod)
    (metis add_diff_cancel_right' auxiliary_prime_imp_less auxiliary_prime_of_2
      auxiliary_prime_pattern dvd_refl even_mult_iff mult_dvd_mono)

value \<open>[(p, q). p \<leftarrow> [1..1000], q \<leftarrow> [1..110], aux_prime (nat p) (nat q)]\<close>



subsection \<open>Sophie Germain Primes are auxiliary\<close>

text \<open>When \<open>p\<close> is an \<^const>\<open>odd\<close> \<^const>\<open>prime\<close> and \<^term>\<open>2 * p + 1 :: nat\<close> is also
      a \<^const>\<open>prime\<close> (what we call a Sophie Germain \<^const>\<open>prime\<close>),
      \<^term>\<open>2 * p + 1 :: nat\<close> is automatically an \<^const>\<open>auxiliary_prime\<close>.\<close>

lemma SophGer_prime_imp_auxiliary_prime :
  fixes p assumes \<open>SG p\<close> defines q_def: \<open>q \<equiv> 2 * p + 1\<close>
  shows \<open>aux_prime p q\<close>
proof (rule auxiliary_primeI)
  from SophGer_primeD(2-3)[OF \<open>SG p\<close>]
  show \<open>prime p\<close> and \<open>prime q\<close> by (unfold q_def)
next
  from SophGer_primeD[OF \<open>SG p\<close>, folded q_def]
  have \<open>odd p\<close> \<open>prime p\<close> \<open>prime q\<close> \<open>prime (int q)\<close> \<open>p \<noteq> 0\<close> by simp_all
  show \<open>NC p q\<close>
  proof (rule ccontr)
    assume \<open>\<not> NC p q\<close>
    then obtain x y :: int where \<open>[x \<noteq> 0] (mod q)\<close> \<open>[y \<noteq> 0] (mod q)\<close>
      \<open>[x ^ p = 1 + y ^ p] (mod q)\<close> by blast
    from SG_simps.p_th_power_mod_q \<open>[x \<noteq> 0] (mod q)\<close> \<open>SG p\<close> cong_0_iff q_def
    consider \<open>[x ^ p = 1] (mod q)\<close> | \<open>[x ^ p = - 1] (mod q)\<close> by blast
    thus False
    proof cases
      assume \<open>[x ^ p = 1] (mod q)\<close>
      with \<open>[x ^ p = 1 + y ^ p] (mod q)\<close> have \<open>[y ^ p = 0] (mod q)\<close>
        by (metis add.right_neutral cong_add_lcancel cong_sym cong_trans)
      with \<open>[y \<noteq> 0] (mod q)\<close> show False
        by (meson \<open>prime (int q)\<close> cong_0_iff prime_dvd_power_int)
    next
      assume \<open>[x ^ p = - 1] (mod q)\<close>
      with \<open>[x ^ p = 1 + y ^ p] (mod q)\<close>
      have \<open>[- 1 = 1 + y ^ p] (mod q)\<close> by (metis cong_def)
      moreover have \<open>- (1::int) = 1 + - 2\<close> by force
      ultimately have \<open>[y ^ p = - 2] (mod q)\<close>
        by (metis cong_add_lcancel cong_sym)
      with \<open>odd p\<close> cong_minus_minus_iff have \<open>[(- y) ^ p = 2] (mod q)\<close> by force
      with cong_sym have \<open>\<exists>x :: int. [2 = x ^ p] (mod q)\<close> by blast
      with \<open>p \<noteq> 0\<close> exists_nth_power_mod_prime_iff[OF \<open>prime q\<close>]
      have \<open>([2 = 0] (mod q) \<or> [4 = 1] (mod q))\<close>
        by (simp add: q_def flip: cong_int_iff)
      hence \<open>p \<le> 1\<close>
      proof (elim disjE)
        from \<open>p \<noteq> 0\<close> show \<open>[2 = 0] (mod q) \<Longrightarrow> p \<le> 1\<close>
          by (auto simp add: q_def cong_def)
      next
        from linorder_not_less show \<open>[4 = 1] (mod q) \<Longrightarrow> p \<le> 1\<close>
          by (fastforce simp add: q_def cong_def)
      qed
      with \<open>SG p\<close> show False
        by (metis \<open>prime p\<close> linorder_not_less prime_nat_iff)
    qed
  qed
next
  from \<open>SG p\<close>[THEN SophGer_primeD(3), folded q_def]
  have \<open>prime q\<close> \<open>prime (int q)\<close> by simp_all
  from SG_simps.p_th_power_mod_q[OF \<open>SG p\<close>]
  have \<open>\<not> q dvd x \<Longrightarrow> [x ^ p = 1] (mod q) \<or> [x ^ p = - 1] (mod q)\<close> for x :: int
    unfolding q_def .
  moreover have \<open>[p \<noteq> (1 :: int)] (mod q)\<close> \<open>[p \<noteq> - 1] (mod q)\<close>
    using SG_simps.notcong_p(1, 3)[OF \<open>SG p\<close>] cong_sym unfolding q_def by blast+
  ultimately have \<open>\<not> q dvd x \<Longrightarrow> [p \<noteq> x ^ p] (mod q)\<close> for x :: int
    using cong_trans by blast
  moreover have \<open>q dvd x \<Longrightarrow> [p \<noteq> x ^ p] (mod q)\<close> for x :: int
    by (metis SG_simps.pos Suc_eq_plus1 \<open>SG p\<close> cong_dvd_iff dvd_power dvd_trans
        int_dvd_int_iff less_add_Suc1 mult.commute mult_2_right nat_dvd_not_less q_def)
  ultimately show \<open>PPP p q\<close> by blast
qed



subsection \<open>Main Theorems\<close>

theorem Sophie_Germain_auxiliary_prime :
  \<open>q dvd x \<or> q dvd y \<or> q dvd z\<close>
  if \<open>x ^ p + y ^ p = z ^ p\<close> and \<open>aux_prime p q\<close> for x y z :: int
proof (rule ccontr)
  assume not_dvd : \<open>\<not> (q dvd x \<or> q dvd y \<or> q dvd z)\<close>
  from auxiliary_primeD[OF \<open>aux_prime p q\<close>]
  have \<open>prime p\<close> \<open>prime q\<close> \<open>NC p q\<close> by simp_all

  have \<open>coprime x q\<close>
    by (meson coprime_commute not_dvd prime_imp_coprime prime_nat_int_transfer \<open>prime q\<close>)
  with bezout_int[of x q] obtain inv_x v :: int where \<open>inv_x * x + v * q = 1\<close> by auto
  hence inv_x : \<open>[x * inv_x = 1] (mod q)\<close> by (metis cong_iff_lin mult.commute)

  from \<open>x ^ p + y ^ p = z ^ p\<close> have \<open>z ^ p = x ^ p + y ^ p\<close> ..
  hence \<open>(inv_x * z) ^ p = (inv_x * x) ^ p + (inv_x * y) ^ p\<close>
    by (metis distrib_left power_mult_distrib)
  with inv_x have \<open>[(inv_x * z) ^ p = 1 + (inv_x * y) ^ p] (mod q)\<close>
    by (metis cong_add_rcancel cong_pow mult.commute power_one)
  moreover from inv_x \<open>prime q\<close> have \<open>[(inv_x * z) ^ p \<noteq> 0] (mod q)\<close>
    by (metis cong_dvd_iff dvd_0_right not_dvd not_prime_unit
        prime_dvd_mult_eq_int prime_dvd_power prime_nat_int_transfer)
  moreover from inv_x \<open>prime q\<close> have \<open>[(inv_x * y) ^ p \<noteq> 0] (mod q)\<close>
    by (metis cong_dvd_iff dvd_0_right not_dvd not_prime_unit
        prime_dvd_mult_eq_int prime_dvd_power prime_nat_int_transfer)
  moreover obtain y' z' :: int where \<open>[y' = inv_x * y] (mod q)\<close> \<open>[z' = inv_x * z] (mod q)\<close>
    by (metis \<open>prime q\<close> cong_less_unique_int cong_sym int_eq_iff of_nat_0_less_iff prime_gt_0_nat)
  ultimately show False
    by (metis \<open>NC p q\<close> \<open>prime p\<close> \<open>prime q\<close> cong_0_iff
        prime_dvd_power_iff prime_gt_0_nat prime_nat_int_transfer)
qed



theorem Sophie_Germain_generalization :
  \<open>\<nexists>x y z :: int. x ^ p + y ^ p = z ^ p \<and>
                  [x \<noteq> 0] (mod p\<^sup>2) \<and> [y \<noteq> 0] (mod p\<^sup>2) \<and> [z \<noteq> 0] (mod p\<^sup>2)\<close>
  if odd_p : \<open>odd p\<close> and aux_prime : \<open>aux_prime p q\<close>
proof (rule ccontr) \<comment> \<open>The proof is done by contradiction.\<close>
  from \<open>aux_prime p q\<close> have prime_p : \<open>prime p\<close>
    by (metis auxiliary_primeD(1))
  hence not_p_0 : \<open>p \<noteq> 0\<close> and prime_int_p : \<open>prime (int p)\<close> by simp_all
  from \<open>aux_prime p q\<close> have prime_q : \<open>prime q\<close>
    by (metis auxiliary_primeD(2))
  hence prime_int_q : \<open>prime (int q)\<close> by simp
  from \<open>odd p\<close> \<open>prime p\<close> have p_ge_3 : \<open>3 \<le> p\<close>
    by (simp add: numeral_eq_Suc)
      (metis Suc_le_eq dvd_refl le_antisym not_less_eq_eq prime_gt_Suc_0_nat)

  assume \<open>\<not> (\<nexists>x y z. x ^ p + y ^ p = z ^ p \<and> [x \<noteq> 0] (mod int (p\<^sup>2)) \<and>
                     [y \<noteq> 0] (mod int (p\<^sup>2)) \<and> [z \<noteq> 0] (mod (int p)\<^sup>2))\<close>
  then obtain x y z :: int
    where fermat : \<open>x ^ p + y ^ p = z ^ p\<close>
      and not_cong_0 : \<open>[x \<noteq> 0] (mod p\<^sup>2)\<close> \<open>[y \<noteq> 0] (mod p\<^sup>2)\<close> \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> by auto

\<comment> \<open>We first assume without loss of generality that
    \<^term>\<open>x\<close>, \<^term>\<open>y\<close> and \<^term>\<open>z\<close> are setwise \<^const>\<open>coprime\<close>.\<close>
  let ?gcd = \<open>Gcd {x, y, z}\<close>
  wlog coprime : \<open>?gcd = 1\<close> goal False generalizing x y z keeping fermat not_cong_0
    using FLT_setwise_coprime_reduction_mod_version[OF fermat not_cong_0]
      hypothesis by blast

\<comment> \<open>Then we can deduce that \<^term>\<open>x\<close>, \<^term>\<open>y\<close> and \<^term>\<open>z\<close> are pairwise \<^const>\<open>coprime\<close>.\<close>
  have coprime_x_y : \<open>coprime x y\<close>
    by (fact FLT_setwise_coprime_imp_pairwise_coprime[OF \<open>p \<noteq> 0\<close> fermat coprime])
  have coprime_y_z : \<open>coprime y z\<close>
  proof (subst coprime_minus_right_iff[symmetric],
      rule FLT_setwise_coprime_imp_pairwise_coprime[OF \<open>p \<noteq> 0\<close>])
    from fermat \<open>odd p\<close> show \<open>y ^ p + (- z) ^ p = (- x) ^ p\<close> by simp
  next
    show \<open>Gcd {y, - z, - x} = 1\<close>
      by (metis Gcd_insert coprime gcd_neg1_int insert_commute)
  qed
  have coprime_x_z : \<open>coprime x z\<close>
  proof (subst coprime_minus_right_iff[symmetric],
      rule FLT_setwise_coprime_imp_pairwise_coprime[OF \<open>p \<noteq> 0\<close>])
    from fermat \<open>odd p\<close> show \<open>x ^ p + (- z) ^ p = (- y) ^ p\<close> by simp
  next
    show \<open>Gcd {x, - z, - y} = 1\<close> 
      by (metis Gcd_insert coprime gcd_neg1_int insert_commute)
  qed

\<comment> \<open>From @{thm [show_question_marks = false] Sophie_Germain_auxiliary_prime}
    we have that among \<^term>\<open>x\<close>, \<^term>\<open>y\<close> and \<^term>\<open>z\<close>,
    one (and only one, see below) is a multiple of \<^term>\<open>q\<close>.\<close>
  from Sophie_Germain_auxiliary_prime[OF fermat aux_prime]
  have q_dvd_xyz : \<open>q dvd x \<or> q dvd y \<or> q dvd z\<close> .

\<comment> \<open>Without loss of generality, we can assume that \<^term>\<open>x\<close> is a multiple of \<^term>\<open>q\<close>.\<close>
  wlog q_dvd_z : \<open>q dvd z\<close> goal False generalizing x y z
    keeping fermat not_cong_0 coprime_x_y coprime_y_z coprime_x_z
  proof -
    from negation q_dvd_xyz have \<open>q dvd x \<or> q dvd y\<close> by simp
    thus False
    proof (elim disjE)
      show \<open>q dvd x \<Longrightarrow> False\<close>
        by (erule hypothesis[of x \<open>- y\<close> z])
          (use fermat not_cong_0 \<open>odd p\<close> in
            \<open>simp_all add: cong_0_iff coprime_commute coprime_x_y coprime_x_z coprime_y_z\<close>)
    next
      show \<open>q dvd y \<Longrightarrow> False\<close>
        by (erule hypothesis[of y \<open>- x\<close> z])
          (use fermat not_cong_0 \<open>odd p\<close> in
            \<open>simp_all add: cong_0_iff coprime_commute coprime_x_y coprime_x_z coprime_y_z\<close>)
    qed
  qed

  define S where \<open>S \<equiv> \<lambda>y z :: int. \<Sum>k = 0..p - 1. (- z) ^ (p - 1 - k) * y ^ k\<close>

\<comment> \<open>Now we prove that \<^term>\<open>x\<close>, \<^term>\<open>y\<close> or \<^term>\<open>x\<close> is dividable by \<^term>\<open>p\<close>.\<close>
  have p_dvd_xyz : \<open>p dvd x \<or> p dvd y \<or> p dvd z\<close>
  proof (rule ccontr)
    assume \<open>\<not> (p dvd x \<or> p dvd y \<or> p dvd z)\<close>
    hence \<open>[x \<noteq> 0] (mod p)\<close> \<open>[y \<noteq> 0] (mod p)\<close> \<open>[z \<noteq> 0] (mod p)\<close> 
      by (simp_all add: cong_0_iff)
    from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- z\<close> x y]
      coprime_x_y fermat \<open>[z \<noteq> 0] (mod p)\<close>
    obtain a \<alpha> where \<open>x + y = a ^ p\<close> \<open>S x y = \<alpha> ^ p\<close>
      by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)
    from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- x\<close> z \<open>- y\<close>]
      coprime_y_z fermat \<open>[x \<noteq> 0] (mod int p)\<close>
    obtain b \<beta> where \<open>z - y = b ^ p\<close> \<open>S z (- y) = \<beta> ^ p\<close>
      by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)
    from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- y\<close> z \<open>- x\<close>]
      coprime_x_z fermat \<open>[y \<noteq> 0] (mod p)\<close>
    obtain c \<gamma> where \<open>z - x = c ^ p\<close> \<open>S z (- x) = \<gamma> ^ p\<close>
      by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)

    have \<open>a ^ p + b ^ p + c ^ p = x + y + (z - y) + (z - x)\<close>
      by (simp add: \<open>x + y = a ^ p\<close> \<open>z - y = b ^ p\<close> \<open>z - x = c ^ p\<close>)
    also have \<open>\<dots> = 2 * z\<close> by simp
    also from \<open>q dvd z\<close> have \<open>[\<dots> = 0] (mod q)\<close> by (simp add: cong_0_iff)
    finally have \<open>[a ^ p + b ^ p + c ^ p = 0] (mod q)\<close> .

    have \<open>[a = 0] (mod q) \<or> [b = 0] (mod q) \<or> [c = 0] (mod q)\<close>
    proof (rule ccontr)
      assume \<open>\<not> ([a = 0] (mod q) \<or> [b = 0] (mod q) \<or> [c = 0] (mod q))\<close>
      hence \<open>[a \<noteq> 0] (mod q)\<close> \<open>[b \<noteq> 0] (mod q)\<close> \<open>[c \<noteq> 0] (mod q)\<close> by simp_all
      from \<open>[c \<noteq> 0] (mod q)\<close> have \<open>gcd c q = 1\<close>
        by (meson aux_prime auxiliary_prime_def cong_0_iff coprime_iff_gcd_eq_1
            residues_prime.p_coprime_right_int residues_prime_def)
      from bezout_int[of c q, unfolded this]
      obtain u v where \<open>u * c + v * int q = 1\<close> by blast
      with \<open>[a \<noteq> 0] (mod q)\<close> have \<open>[u \<noteq> 0] (mod q)\<close>
        by (metis cong_0_iff cong_dvd_iff cong_iff_lin dvd_mult mult.commute unit_imp_dvd)

      from \<open>[a ^ p + b ^ p + c ^ p = 0] (mod q)\<close>
      have \<open>[(u * a) ^ p + (u * b) ^ p + (u * c) ^ p = 0] (mod q)\<close>
        by (simp add: power_mult_distrib)
          (metis cong_scalar_left distrib_left mult.commute mult_zero_left)
      also from \<open>u * c + v * int q = 1\<close> have \<open>u * c = 1 - v * int q\<close> by simp
      finally have \<open>[(u * a) ^ p + (u * b) ^ p + (1 - v * int q) ^ p = 0] (mod q)\<close> .
      moreover have \<open>[(1 - v * int q) ^ p = 1] (mod q)\<close>
        by (metis add_uminus_conv_diff cong_0_iff cong_add_lcancel_0
            cong_pow dvd_minus_iff dvd_triv_right power_one)
      ultimately have \<open>[(u * a) ^ p + (u * b) ^ p + 1 = 0] (mod q)\<close>
        by (meson cong_add_lcancel cong_sym cong_trans)
      hence \<open>[1 + (u * b) ^ p = (- (u * a)) ^ p] (mod q)\<close>
        by (simp add: \<open>odd p\<close> cong_iff_dvd_diff) presburger
      hence \<open>[(- (u * a)) ^ p = 1 + (u * b) ^ p] (mod q)\<close> by (fact cong_sym)
      moreover from \<open>[a \<noteq> 0] (mod q)\<close> \<open>[u \<noteq> 0] (mod q)\<close>
        cong_prime_prod_zero_int[OF _ \<open>prime (int q)\<close>, of u a] cong_minus_minus_iff
      have \<open>[- u * a \<noteq> 0] (mod q)\<close> by force
      moreover from \<open>[b \<noteq> 0] (mod q)\<close> \<open>[u \<noteq> 0] (mod q)\<close>
        cong_prime_prod_zero_int[OF _ \<open>prime (int q)\<close>, of u b]
      have \<open>[u * b \<noteq> 0] (mod q)\<close> by blast
      ultimately show False
        using aux_prime auxiliary_primeD(3) by auto
    qed
    hence \<open>q dvd a\<close>
    proof (elim disjE)
      show \<open>[a = 0] (mod q) \<Longrightarrow> q dvd a\<close> by (simp add: cong_0_iff)
    next
      assume \<open>[b = 0] (mod q)\<close>
      with \<open>z - y = b ^ p\<close> \<open>q dvd z\<close> \<open>prime p\<close> have \<open>q dvd y\<close>
        by (metis cong_0_iff cong_dvd_iff cong_iff_dvd_diff
            dvd_power dvd_trans prime_gt_0_nat)
      with \<open>prime (int q)\<close> \<open>q dvd z\<close> \<open>coprime y z\<close> have False
        by (metis coprime_def not_prime_unit)
      thus \<open>q dvd a\<close> ..
    next
      assume \<open>[c = 0] (mod q)\<close>
      with \<open>z - x = c ^ p\<close> \<open>q dvd z\<close> \<open>prime p\<close> have \<open>q dvd x\<close>
        by (metis cong_0_iff cong_dvd_iff cong_iff_dvd_diff
            dvd_power dvd_trans prime_gt_0_nat)
      with \<open>prime (int q)\<close> \<open>q dvd z\<close> \<open>coprime x z\<close> have False
        by (metis coprime_def not_prime_unit)
      thus \<open>q dvd a\<close> ..
    qed
    with \<open>x + y = a ^ p\<close> \<open>p \<noteq> 0\<close> \<open>prime (int q)\<close> have \<open>[y = - x] (mod q)\<close>
      by (metis add.commute add.inverse_inverse add_uminus_conv_diff
          bot_nat_0.not_eq_extremum cong_iff_dvd_diff prime_dvd_power_int_iff)
    hence \<open>[S x y = p * x ^ (p - 1)] (mod q)\<close>
      unfolding S_def by (fact Sophie_Germain_lemma_computation_cong_simp[OF \<open>p \<noteq> 0\<close>])
    moreover from \<open>z - x = c ^ p\<close> \<open>q dvd z\<close> have \<open>[x = (- c) ^ p] (mod q)\<close>
      by (simp add: \<open>odd p\<close> cong_iff_dvd_diff)
        (metis add_diff_cancel_left' diff_diff_eq2)
    ultimately have \<open>[S x y = p * ((- c) ^ p) ^ (p - 1)] (mod q)\<close>
      by (meson cong_pow cong_scalar_left cong_trans)
    also have \<open>S x y = \<alpha> ^ p\<close> by (fact \<open>S x y = \<alpha> ^ p\<close>)
    also have \<open>((- c) ^ p) ^ (p - 1) = ((- c) ^ (p - 1)) ^ p\<close>
      by (metis mult.commute power_mult)
    finally have \<open>[\<alpha> ^ p = p * ((- c) ^ (p - 1)) ^ p] (mod q)\<close> .

    have \<open>gcd q ((- c) ^ (p - 1)) = 1\<close>
      by (metis \<open>[x = (- c) ^ p] (mod int q)\<close> \<open>int q dvd z\<close> cong_dvd_iff
          coprime_def coprime_imp_gcd_eq_1 coprime_x_z dvd_mult not_prime_unit
          power_eq_if prime_imp_coprime_int \<open>p \<noteq> 0\<close> \<open>prime (int q)\<close>)
    with bezout_int obtain u v
      where \<open>u * int q + v * (- c) ^ (p - 1) = 1\<close> by metis
    hence \<open>v * (- c) ^ (p - 1) = 1 - u * int q\<close> by simp
    have \<open>[1 - u * int q = 1] (mod q)\<close> by (simp add: cong_iff_lin)
    from \<open>[\<alpha> ^ p = p * ((- c) ^ (p - 1)) ^ p] (mod q)\<close>
    have \<open>[(v * \<alpha>) ^ p = p * (v * (- c) ^ (p - 1)) ^ p] (mod q)\<close>
      by (simp add: power_mult_distrib) (metis cong_scalar_left mult.left_commute)
    with \<open>[1 - u * int q = 1] (mod int q)\<close> have \<open>[(v * \<alpha>) ^ p = p] (mod q)\<close>
      by (unfold \<open>v * (- c) ^ (p - 1) = 1 - u * int q\<close>)
        (metis cong_pow cong_scalar_left cong_trans mult.comm_neutral power_one)
    with \<open>aux_prime p q\<close>[THEN auxiliary_primeD(4)] cong_sym show False by blast
  qed

\<comment> \<open>Without loss of generality, we can assume that it is \<^term>\<open>z\<close>.\<close>
  wlog p_dvd_z : \<open>p dvd z\<close> goal False generalizing x y z S
    keeping fermat not_cong_0 coprime_x_y coprime_y_z coprime_x_z S_def
  proof -
    from negation p_dvd_xyz have \<open>p dvd x \<or> p dvd y\<close> by simp
    thus False
    proof (elim disjE)
      show \<open>p dvd x \<Longrightarrow> False\<close>
        by (erule hypothesis[of x \<open>- y\<close> z])
          (use fermat not_cong_0 \<open>odd p\<close> in
            \<open>simp_all add: cong_0_iff coprime_commute coprime_x_y coprime_x_z coprime_y_z\<close>)
    next
      show \<open>p dvd y \<Longrightarrow> False\<close>
        by (erule hypothesis[of y \<open>- x\<close> z])
          (use fermat not_cong_0 \<open>odd p\<close> in
            \<open>simp_all add: cong_0_iff coprime_commute coprime_x_y coprime_x_z coprime_y_z\<close>)
    qed
  qed

\<comment> \<open>The rest of the proof consists in deducing that actually \<^term>\<open>p\<^sup>2\<close>
    divides \<^term>\<open>z\<close>, which contradicts @{thm \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close>}.\<close>
  from \<open>p dvd z\<close> coprime_x_z coprime_y_z
  have \<open>[x \<noteq> 0] (mod p)\<close> \<open>[y \<noteq> 0] (mod p)\<close>
    by (simp_all add: cong_0_iff)
      (meson not_coprimeI not_prime_unit \<open>prime (int p)\<close>)+

  from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- x\<close> z \<open>- y\<close>]
    coprime_y_z fermat \<open>[x \<noteq> 0] (mod int p)\<close>
  obtain b \<beta> where \<open>z - y = b ^ p\<close> \<open>S z (- y) = \<beta> ^ p\<close>
    by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)
  from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- y\<close> z \<open>- x\<close>]
    coprime_x_z fermat \<open>[y \<noteq> 0] (mod p)\<close>
  obtain c \<gamma> where \<open>z - x = c ^ p\<close> \<open>S z (- x) = \<gamma> ^ p\<close>
    by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)

  from fermat have \<open>(- z) ^ p + x ^ p + y ^ p = 0\<close> by (simp add: \<open>odd p\<close>)
  from Sophie_Germain_lemma_computation[OF \<open>odd p\<close>] fermat
  have \<open>(x + y) * S x y = z ^ p\<close> by (simp add: S_def)
  with \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> have \<open>x + y \<noteq> 0\<close> \<open>S x y \<noteq> 0\<close> by auto

  define z' where \<open>z' \<equiv> z div p\<close>
  from \<open>p dvd z\<close> \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> \<open>p \<noteq> 0\<close>
  have \<open>z = z' * p\<close> \<open>[z' \<noteq> 0] (mod p)\<close>
    by (simp_all add: cong_0_iff z'_def dvd_div_iff_mult power2_eq_square)

  from Sophie_Germain_lemma_only_possible_prime_common_divisor[OF \<open>prime p\<close> _ \<open>coprime x y\<close>]
  have \<open>\<exists>q\<in>#prime_factorization r. q \<noteq> p \<Longrightarrow> \<not> r dvd x + y \<or> \<not> r dvd S x y\<close> for r :: nat
    unfolding S_def
    by (meson dvd_trans in_prime_factors_iff int_dvd_int_iff
        of_nat_eq_iff prime_nat_int_transfer)
  from this[OF Ex_other_prime_factor[OF _ _ \<open>prime p\<close>]]
  have \<open>r dvd x + y \<Longrightarrow> r dvd S x y \<Longrightarrow> r = 0 \<or> (\<exists>k. r = p ^ k)\<close> for r :: nat by auto
  moreover have \<open>\<not> (p ^ k dvd x + y \<and> p ^ k dvd S x y)\<close> if \<open>1 < k\<close> for k
  proof (rule ccontr)
    assume \<open>\<not> (\<not> (p ^ k dvd x + y \<and> p ^ k dvd S x y))\<close>
    moreover from \<open>1 < k\<close> have \<open>p\<^sup>2 dvd p ^ k\<close>
      by (simp add: le_imp_power_dvd)
    ultimately have \<open>p\<^sup>2 dvd x + y\<close> \<open>p\<^sup>2 dvd S x y\<close>
      by (meson dvd_trans of_nat_dvd_iff)+
    from \<open>p\<^sup>2 dvd x + y\<close> have \<open>[y = - x] (mod p\<^sup>2)\<close>
      by (simp add: add.commute cong_iff_dvd_diff)
    hence \<open>[S x y = p * x ^ (p - 1)] (mod p\<^sup>2)\<close>
      unfolding S_def by (fact Sophie_Germain_lemma_computation_cong_simp[OF \<open>p \<noteq> 0\<close>])
    moreover from \<open>[x \<noteq> 0] (mod p)\<close> \<open>z = z' * p\<close> \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> \<open>prime (int p)\<close>
    have \<open>\<not> p\<^sup>2 dvd p * x ^ (p - 1)\<close>
      by (metis cong_0_iff dvd_mult_cancel_left mult_zero_right
          of_nat_power power2_eq_square prime_dvd_power_int)
    ultimately show False using \<open>p\<^sup>2 dvd S x y\<close> cong_dvd_iff by blast
  qed
  ultimately have p_only_nontrivial_div :
    \<open>r dvd x + y \<Longrightarrow> r dvd S x y \<Longrightarrow> r = 1 \<or> r = p\<close> for r :: nat
    by (metis \<open>S x y \<noteq> 0\<close> dvd_0_left_iff less_one
        linorder_neqE_nat of_nat_eq_0_iff power_0 power_one_right)
      \<comment> \<open>\<^term>\<open>p\<close> is therefore the only possible nontrivial common divisor.\<close>

  define mul_x_plus_y where \<open>mul_x_plus_y = multiplicity p (x + y)\<close>
  define mul_S_x_y where \<open>mul_S_x_y = multiplicity p (S x y)\<close>
  from \<open>(x + y) * S x y = z ^ p\<close>
  have \<open>(x + y) * S x y = z' ^ p * p ^ p\<close>
    by (simp add: \<open>z = z' * p\<close> power_mult_distrib)


  have \<open>mul_x_plus_y + mul_S_x_y = multiplicity p (z ^ p)\<close>
    unfolding mul_x_plus_y_def mul_S_x_y_def
    by (metis \<open>(x + y) * S x y = z ^ p\<close> \<open>S x y \<noteq> 0\<close> \<open>x + y \<noteq> 0\<close> prime_def
        prime_elem_multiplicity_mult_distrib \<open>prime (int p)\<close>)
  also have \<open>z ^ p = z' ^ p * p ^ p\<close>
    by (simp add: \<open>z = z' * p\<close> power_mult_distrib)
  also have \<open>multiplicity p \<dots> = p\<close>
    by (metis \<open>[z' \<noteq> 0] (mod int p)\<close> aux_prime auxiliary_prime_def cong_0_iff
        mult_of_nat_commute multiplicity_decomposeI of_nat_eq_0_iff of_nat_power
        prime_dvd_power_iff prime_gt_0_nat \<open>p \<noteq> 0\<close> \<open>prime (int p)\<close>)
  finally have \<open>mul_x_plus_y + mul_S_x_y = p\<close> .

  moreover have \<open>(2 \<le> mul_x_plus_y \<longrightarrow> mul_S_x_y    \<le> 1) \<and>
                 (2 \<le> mul_S_x_y    \<longrightarrow> mul_x_plus_y \<le> 1)\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    hence \<open>2 \<le> mul_x_plus_y \<and> 2 \<le> mul_S_x_y\<close> by linarith
    hence \<open>p\<^sup>2 dvd (x + y) \<and> p\<^sup>2 dvd (S x y)\<close>
      by (simp add: mul_x_plus_y_def mul_S_x_y_def multiplicity_dvd')
    thus False
      by (metis cong_0_iff less_numeral_extra(3) one_eq_prime_power_iff
          p_dvd_z p_only_nontrivial_div pos2 \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> \<open>prime p\<close>)
  qed
  ultimately consider \<open>mul_x_plus_y = p\<close> \<open>mul_S_x_y = 0\<close>
    | \<open>mul_x_plus_y = 0\<close> \<open>mul_S_x_y = p\<close>
    | \<open>mul_x_plus_y = 1\<close> \<open>mul_S_x_y = p - 1\<close>
    | \<open>mul_x_plus_y = p - 1\<close> \<open>mul_S_x_y = 1\<close>
    by (metis Nat.add_diff_assoc add_cancel_right_right add_diff_cancel_left'
        diff_is_0_eq not_less_eq_eq one_add_one plus_1_eq_Suc)
  thus False
  proof cases

    assume \<open>mul_x_plus_y = p\<close> \<open>mul_S_x_y = 0\<close>
    from \<open>mul_x_plus_y = p\<close> have \<open>p dvd (x + y)\<close>
      by (metis mul_x_plus_y_def not_dvd_imp_multiplicity_0 \<open>p \<noteq> 0\<close>)
    hence \<open>[y = - x] (mod p)\<close>
      by (simp add: add.commute cong_iff_dvd_diff)
    hence \<open>[S x y = S x (- x)] (mod p)\<close>
      unfolding S_def
      by (meson cong_minus_minus_iff cong_pow cong_scalar_right cong_sum)
    also have \<open>S x (- x) = (\<Sum>k = 0..p - 1. x ^ (p - 1))\<close>
      unfolding S_def
      by (rule sum.cong[OF refl], simp)
        (metis One_nat_def diff_Suc_eq_diff_pred le_add_diff_inverse2 power_add)
    also from \<open>p \<noteq> 0\<close> have \<open>\<dots> = p * x ^ (p - 1)\<close> by simp
    finally have \<open>[S x y = p * x ^ (p - 1)] (mod p)\<close> .
    with \<open>[x \<noteq> 0] (mod p)\<close> have \<open>p dvd S x y\<close> by (simp add: cong_dvd_iff)
    with \<open>mul_S_x_y = 0\<close> show False
      by (metis \<open>S x y \<noteq> 0\<close> mul_S_x_y_def not_one_le_zero not_prime_unit
          power_dvd_iff_le_multiplicity power_one_right \<open>prime (int p)\<close>)
  next

    assume \<open>mul_x_plus_y = 0\<close> \<open>mul_S_x_y = p\<close>
    from \<open>mul_S_x_y = p\<close> have \<open>p dvd S x y\<close>
      by (metis mul_S_x_y_def not_dvd_imp_multiplicity_0 \<open>p \<noteq> 0\<close>)
    from Sophie_Germain_lemma_computation[OF \<open>odd p\<close>]
    have \<open>(x + y) * S x y = x ^ p + y ^ p\<close> unfolding S_def .
    moreover from \<open>p dvd S x y\<close> have \<open>[(x + y) * S x y = 0] (mod p)\<close>
      by (simp add: cong_0_iff)
    moreover have \<open>[x ^ p + y ^ p = x + y] (mod p)\<close>
    proof (rule cong_add)
      have \<open>x ^ p = x * x ^ (p - 1)\<close>
        by (simp add: power_eq_if \<open>p \<noteq> 0\<close>)
      moreover from \<open>[x \<noteq> 0] (mod p)\<close> have \<open>[x ^ (p - 1)  = 1] (mod p)\<close>
        using cong_0_iff fermat_theorem_int \<open>prime p\<close> by blast
      ultimately show \<open>[x ^ p = x] (mod p)\<close>
        by (metis cong_scalar_left mult.right_neutral)
    next
      have \<open>y ^ p = y * y ^ (p - 1)\<close>
        by (simp add: power_eq_if \<open>p \<noteq> 0\<close>)
      moreover from \<open>[y \<noteq> 0] (mod p)\<close> have \<open>[y ^ (p - 1)  = 1] (mod p)\<close>
        using cong_0_iff fermat_theorem_int \<open>prime p\<close> by blast
      ultimately show \<open>[y ^ p = y] (mod p)\<close>
        by (metis cong_scalar_left mult.right_neutral)
    qed
    ultimately have \<open>p dvd x + y\<close>
      by (simp add: cong_0_iff cong_dvd_iff)
    with \<open>mul_x_plus_y = 0\<close> show False
      by (metis \<open>x + y \<noteq> 0\<close> mul_x_plus_y_def multiplicity_eq_zero_iff
          not_prime_unit \<open>prime (int p)\<close>)
  next

    define x_plus_y' where \<open>x_plus_y' \<equiv> (x + y) div p\<close>
    define S_x_y' where \<open>S_x_y' \<equiv> (S x y) div p ^ (p - 1)\<close>
    define s where \<open>s \<equiv> x + y\<close>
    let ?f  = \<open>\<lambda>k. (p choose k) * (- x) ^ k * s ^ (p - k)\<close>
    let ?f' = \<open>\<lambda>k. (p choose k) * (- x) ^ k * s ^ (p - 1 - k)\<close>

    assume \<open>mul_x_plus_y = 1\<close> \<open>mul_S_x_y = p - 1\<close>
    hence \<open>s = p * x_plus_y'\<close> \<open>S x y = p ^ (p - 1) * S_x_y'\<close>
      by (simp_all add: s_def x_plus_y'_def S_x_y'_def)
        (metis dvd_mult_div_cancel mul_x_plus_y_def multiplicity_dvd power_Suc0_right,
          metis dvd_mult_div_cancel mul_S_x_y_def multiplicity_dvd)

    from fermat have \<open>s * S x y = (s - x) ^ p + x ^ p\<close>
      by (simp add: s_def \<open>(x + y) * S x y = z ^ p\<close>)
    also have \<open>s - x = (- x + s)\<close> by simp
    also have \<open>(- x + s) ^ p = (\<Sum>k\<le>p. (p choose k) * (- x) ^ k * s ^ (p - k))\<close>
      by (fact binomial_ring)
    also have \<open>\<dots> = (\<Sum>k\<in>{0..p - 1}. ?f k) + (\<Sum>k\<in>{p}. ?f k)\<close>
      by (rule sum_Un_eq[symmetric])
        (auto simp add: linorder_not_le prime_gt_0_nat \<open>prime p\<close>)
    also have \<open>(\<Sum>k\<in>{0..p - 1}. ?f k) = (\<Sum>k\<in>{0}. ?f k) + (\<Sum>k\<in>{1..p - 1}. ?f k)\<close>
      by (rule sum_Un_eq[symmetric]) auto
    also have \<open>(\<Sum>k\<in>{1..p - 1}. ?f k) = (\<Sum>k\<in>{1..p - 2}. ?f k) + (\<Sum>k\<in>{p - 1}. ?f k)\<close>
      by (rule sum_Un_eq[symmetric]) (use \<open>3 \<le> p\<close> in auto)
    also have \<open>(\<Sum>k\<in>{0}. ?f k) = s * s ^ (p - 1)\<close> by (simp add: power_eq_if \<open>p \<noteq> 0\<close>)
    also have \<open>(\<Sum>k\<in>{1..p - 2}. ?f k) = (\<Sum>k\<in>{1..p - 2}. s * ?f' k)\<close>
      by (rule sum.cong, simp_all)
        (metis Suc_diff_Suc diff_less less_2_cases_iff less_zeroE
          linorder_neqE order.strict_iff_not power_Suc \<open>p \<noteq> 0\<close>)
    also have \<open>\<dots> = s * (\<Sum>k\<in>{1..p - 2}. ?f' k)\<close>
      by (simp add: mult.assoc sum_distrib_left)
    also have \<open>(\<Sum>k\<in>{p - 1}. ?f k) = s * p * x ^ (p - 1)\<close>
      by (simp del: One_nat_def, subst binomial_symmetric[symmetric])
        (use \<open>3 \<le> p\<close> in \<open>auto simp add: \<open>odd p\<close>\<close>)
    finally have \<open>s * S x y =
                  s * (s ^ (p - 1) + (\<Sum>k\<in>{1..p - 2}. ?f' k) + p * x ^ (p - 1))\<close>
      by (simp add: \<open>odd p\<close> distrib_left int_distrib(4))
    hence S_x_y_developed : \<open>S x y = s ^ (p - 1) + (\<Sum>k\<in>{1..p - 2}. ?f' k) + p * x ^ (p - 1)\<close>
      using \<open>x + y \<noteq> 0\<close> mult_cancel_left unfolding s_def by blast
    have \<open>[p * x ^ (p - 1) = 0] (mod p\<^sup>2)\<close>
    proof (rule cong_trans[OF _ cong_sym])
      show \<open>[p * x ^ (p - 1) = 0 + 0 + p * x ^ (p - 1)] (mod p\<^sup>2)\<close> by simp
    next
      show \<open>[0 = 0 + 0 + p * x ^ (p - 1)] (mod p\<^sup>2)\<close>
      proof (rule cong_trans)
        have \<open>p ^ (p - 1) dvd S x y\<close>
          by (simp add: \<open>S x y = p ^ (p - 1) * S_x_y'\<close>)
        moreover from \<open>3 \<le> p\<close> have \<open>p ^ 2 dvd p ^ (p - 1)\<close>
          by (auto intro: le_imp_power_dvd)
        ultimately show \<open>[0 = S x y] (mod p\<^sup>2)\<close>
          by (metis cong_0_iff cong_sym dvd_trans of_nat_dvd_iff)
      next
        show \<open>[S x y = 0 + 0 + p * x ^ (p - 1)] (mod p\<^sup>2)\<close>
        proof (unfold S_x_y_developed, rule cong_add[OF _ cong_refl])
          show \<open>[s ^ (p - 1) + (\<Sum>k = 1..p - 2. ?f' k) = 0 + 0] (mod p\<^sup>2)\<close>
          proof (rule cong_add)
            have \<open>p dvd s\<close> by (simp add: \<open>s = p * x_plus_y'\<close>)
            hence \<open>p ^ (p - 1) dvd s ^ (p - 1)\<close> by (simp add: dvd_power_same)
            moreover from \<open>3 \<le> p\<close> have \<open>p ^ 2 dvd p ^ (p - 1)\<close>
              by (auto intro: le_imp_power_dvd)
            ultimately show \<open>[s ^ (p - 1) = 0] (mod p\<^sup>2)\<close>
              by (metis cong_0_iff dvd_trans of_nat_dvd_iff)
          next
            show \<open>[\<Sum>k = 1..p - 2. ?f' k = 0] (mod p\<^sup>2)\<close>
            proof (rule cong_trans)
              show \<open>[\<Sum>k = 1..p - 2. ?f' k = \<Sum>k\<in>{1..p - 2}. 0] (mod p\<^sup>2)\<close>
              proof (rule cong_sum)
                fix k assume \<open>k \<in> {1..p - 2}\<close>
                from \<open>k \<in> {1..p - 2}\<close> have \<open>p dvd (p choose k)\<close>
                  by (auto intro: dvd_choose_prime simp add: \<open>prime p\<close>)
                moreover from \<open>k \<in> {1..p - 2}\<close> have \<open>p dvd s ^ (p - 1 - k)\<close>
                  by (auto simp add: \<open>prime p\<close> \<open>s = p * x_plus_y'\<close> prime_dvd_power_int_iff)
                ultimately show \<open>[?f' k = 0] (mod p\<^sup>2)\<close>
                  by (simp add: cong_0_iff mult_dvd_mono power2_eq_square)
              qed
            next
              show \<open>[\<Sum>k = 1..p - 2. 0 = 0] (mod int (p\<^sup>2))\<close> by simp
            qed
          qed
        qed
      qed
    qed
    hence \<open>p dvd x ^ (p - 1)\<close> by (simp add: cong_iff_dvd_diff power2_eq_square \<open>p \<noteq> 0\<close>)
    with prime_dvd_power \<open>prime (int p)\<close> have \<open>p dvd x\<close> by blast
    with \<open>[x \<noteq> 0] (mod p)\<close> show False by (simp add: cong_0_iff)
  next

    define x_plus_y' where \<open>x_plus_y' \<equiv> (x + y) div p ^ (p - 1)\<close>
    define S_x_y' where \<open>S_x_y' \<equiv> (S x y) div p\<close>
    assume \<open>mul_x_plus_y = p - 1\<close> \<open>mul_S_x_y = 1\<close>
    with \<open>(x + y) * S x y = z ^ p\<close> \<open>mul_x_plus_y + mul_S_x_y = p\<close>
    have \<open>x_plus_y' * S_x_y' = z' ^ p\<close>
      unfolding x_plus_y'_def S_x_y'_def z'_def
      by (metis (no_types, opaque_lifting)
          div_mult_div_if_dvd div_power mul_S_x_y_def mul_x_plus_y_def
          multiplicity_dvd of_nat_power p_dvd_z power_add power_one_right)
    have \<open>coprime x_plus_y' S_x_y'\<close>
    proof (rule ccontr)
      assume \<open>\<not> coprime x_plus_y' S_x_y'\<close>
      then obtain r where \<open>prime r\<close> \<open>r dvd x_plus_y'\<close> \<open>r dvd S_x_y'\<close>
        by (metis coprime_absorb_left not_coprime_nonzeroE
            prime_factor_int unit_imp_dvd zdvd1_eq)
      from \<open>r dvd x_plus_y'\<close> have \<open>r dvd x + y\<close>
        by (metis \<open>mul_x_plus_y = p - 1\<close> dvd_div_iff_mult dvd_mult_left
            mul_x_plus_y_def multiplicity_dvd of_nat_eq_0_iff of_nat_power
            power_not_zero \<open>p \<noteq> 0\<close> x_plus_y'_def)
      moreover from \<open>r dvd S_x_y'\<close> have \<open>r dvd S x y\<close>
        by (metis S_x_y'_def \<open>mul_S_x_y = 1\<close> dvd_mult_div_cancel dvd_trans
            dvd_triv_right mul_S_x_y_def multiplicity_dvd power_one_right)
      ultimately have \<open>r = p\<close>
        by (metis \<open>prime r\<close> not_prime_1 p_only_nontrivial_div
            pos_int_cases prime_gt_0_int prime_nat_int_transfer)
      with \<open>[z' \<noteq> 0] (mod int p)\<close> \<open>r dvd S_x_y'\<close> \<open>prime p\<close> \<open>prime (int p)\<close>
        \<open>x_plus_y' * S_x_y' = z' ^ p\<close> show False
        by (metis  cong_0_iff dvd_trans dvd_triv_right prime_dvd_power_int_iff prime_gt_0_nat)
    qed
    from prod_is_some_powerE[OF \<open>coprime x_plus_y' S_x_y'\<close> \<open>x_plus_y' * S_x_y' = z' ^ p\<close>]
    obtain a where \<open>normalize x_plus_y' = a ^ p\<close> by blast
    moreover from prod_is_some_powerE
      [OF coprime_commute[THEN iffD1, OF \<open>coprime x_plus_y' S_x_y'\<close>]]
    obtain \<alpha> where \<open>normalize S_x_y' = \<alpha> ^ p\<close>
      by (metis \<open>x_plus_y' * S_x_y' = z' ^ p\<close> mult.commute)
    ultimately have \<open>x_plus_y' = (if 0 \<le> x_plus_y' then a ^ p else (- a) ^ p)\<close>
      \<open>S_x_y' = (if 0 \<le> S_x_y' then \<alpha> ^ p else (- \<alpha>) ^ p)\<close>
      by (metis \<open>odd p\<close> abs_of_nonneg abs_of_nonpos add.inverse_inverse
          linorder_linear normalize_int_def power_minus_odd)+
    then obtain \<alpha> a where \<open>x_plus_y' = a ^ p\<close> \<open>S_x_y' = \<alpha> ^ p\<close> by meson

    from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- x\<close> z \<open>- y\<close>]
      coprime_y_z fermat \<open>[x \<noteq> 0] (mod int p)\<close>
    obtain b \<beta> where \<open>z - y = b ^ p\<close> \<open>S z (- y) = \<beta> ^ p\<close>
      by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)
    from Sophie_Germain_lemma[OF \<open>odd p\<close> \<open>prime p\<close>, of \<open>- y\<close> z \<open>- x\<close>]
      coprime_x_z fermat \<open>[y \<noteq> 0] (mod p)\<close>
    obtain c \<gamma> where \<open>z - x = c ^ p\<close> \<open>S z (- x) = \<gamma> ^ p\<close>
      by (simp add: S_def \<open>odd p\<close> coprime_commute) (meson cong_0_iff dvd_minus_iff)

    have \<open>\<not> p dvd c\<close>
      by (metis \<open>[x \<noteq> 0] (mod int p)\<close> \<open>z - x = c ^ p\<close> cong_0_iff cong_dvd_iff
          cong_iff_dvd_diff dvd_def dvd_trans p_dvd_z power_eq_if \<open>p \<noteq> 0\<close>)
    have \<open>\<not> p dvd b\<close>
      by (metis \<open>[y \<noteq> 0] (mod int p)\<close> \<open>z - y = b ^ p\<close> cong_0_iff cong_dvd_iff
          cong_iff_dvd_diff dvd_def dvd_trans p_dvd_z power_eq_if \<open>p \<noteq> 0\<close>)

    have \<open>p dvd 2 * z - x - y\<close>
      by (metis \<open>mul_S_x_y = 1\<close> \<open>mul_x_plus_y + mul_S_x_y = p\<close> comm_monoid_add_class.add_0 diff_diff_eq dvd_diff int_ops(2)
          mul_x_plus_y_def not_dvd_imp_multiplicity_0 one_dvd p_dvd_z prime_dvd_mult_iff wlog_keep.prime_int_p)
    hence \<open>[2 * z - x - y = 0] (mod p)\<close> by (simp add: cong_0_iff)
    also from \<open>z - x = c ^ p\<close> \<open>z - y = b ^ p\<close>
    have \<open>2 * z - x - y = c ^ p + b ^ p\<close> by presburger
    also have \<open>\<dots> = c ^ (p - 1) * c + b ^ (p - 1) * b\<close>
      by (simp add: power_eq_if \<open>p \<noteq> 0\<close>)
    finally have \<open>[c ^ (p - 1) * c + b ^ (p - 1) * b = 0] (mod p)\<close> .
    moreover have \<open>[c ^ (p - 1) = 1] (mod p)\<close>
      by (fact fermat_theorem_int[OF \<open>prime p\<close> \<open>\<not> p dvd c\<close>])
    moreover have \<open>[b ^ (p - 1) = 1] (mod p)\<close>
      by (fact fermat_theorem_int[OF \<open>prime p\<close> \<open>\<not> p dvd b\<close>])
    ultimately have \<open>[1 * c + 1 * b = 0] (mod p)\<close>
      by (meson cong_add cong_scalar_right cong_sym_eq cong_trans)
    hence \<open>[c + b = 0] (mod p)\<close> by simp
    hence \<open>[b = - c] (mod p)\<close> by (simp add: add.commute cong_iff_dvd_diff)
    hence \<open>[S c b = p * c ^ (p - 1)] (mod p)\<close>
      unfolding S_def
      by (fact Sophie_Germain_lemma_computation_cong_simp[OF \<open>p \<noteq> 0\<close>])
    hence \<open>p dvd S c b\<close> by (simp add: cong_dvd_iff)
    moreover from \<open>[c + b = 0] (mod p)\<close> have \<open>p dvd c + b\<close> by (simp add: cong_dvd_iff)
    moreover from Sophie_Germain_lemma_computation[OF \<open>odd p\<close>]
    have \<open>c ^ p + b ^ p = (c + b) * S c b\<close> unfolding S_def ..
    ultimately have \<open>p\<^sup>2 dvd c ^ p + b ^ p\<close>
      by (simp add: mult_dvd_mono power2_eq_square)
    moreover have \<open>p\<^sup>2 dvd x + y\<close>
      by (metis \<open>mul_S_x_y = 1\<close> \<open>mul_x_plus_y + mul_S_x_y = p\<close> add_0
          bot_nat_0.not_eq_extremum dvd_trans linorder_not_less
          mul_x_plus_y_def multiplicity_dvd' nat_dvd_not_less odd_even_add
          odd_p of_nat_power one_dvd prime_prime_factor \<open>prime p\<close>)
    ultimately have \<open>p\<^sup>2 dvd 2 * z\<close>
      by (metis \<open>2 * z - x - y = c ^ p + b ^ p\<close> diff_diff_eq zdvd_zdiffD)
    moreover have \<open>coprime (p\<^sup>2) 2\<close> by (simp add: \<open>odd p\<close>)
    ultimately have \<open>p\<^sup>2 dvd z\<close>
      by (simp add: coprime_dvd_mult_left_iff mult.commute)
    with \<open>[z \<noteq> 0] (mod p\<^sup>2)\<close> show False by (simp add: cong_0_iff)
  qed
qed



text \<open>Since @{thm [show_question_marks = false] SophGer_prime_imp_auxiliary_prime},
      this result is a generalization of
      @{thm [show_question_marks = false] Sophie_Germain_theorem}.\<close>



(*<*)
end
  (*>*)
