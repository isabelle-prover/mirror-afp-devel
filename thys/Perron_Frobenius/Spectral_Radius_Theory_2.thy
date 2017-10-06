section \<open>Combining Spectral Radius Theory with Perron Frobenius theorem\<close>

theory Spectral_Radius_Theory_2
imports 
  Perron_Frobenius_General
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
begin

hide_const (open) Coset.order

text \<open>This criterion is tight!\<close>

lemma jnf_complexity_generic: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x \<le> 1" 
  and 1: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x = 1 \<Longrightarrow> 
    order x (char_poly A) > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A x). bsize \<le> d + 1)" 
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)" 
proof - 
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and lenn: "length as = n" by auto 
  from jordan_nf_exists[OF A cA] obtain n_xs where jnf: "jordan_nf A n_xs" ..
  have dd: "x ^ d = x ^((d + 1) - 1)" for x by simp
  show ?thesis unfolding dd
  proof (rule jordan_nf_matrix_poly_bound[OF A _ _ jnf])
    fix n x
    assume nx: "(n,x) \<in> set n_xs" 
    from jordan_nf_block_size_order_bound[OF jnf nx] 
    have no: "n \<le> order x (char_poly A)" by auto
    {
      assume "0 < n" 
      with no have "order x (char_poly A) \<noteq> 0" by auto
      hence rt: "poly (char_poly A) x = 0" unfolding order_root by auto
      from sr[OF this] show "cmod x \<le> 1" .
      note rt
    } note sr = this
    assume c1: "cmod x = 1" 
    show "n \<le> d + 1" 
    proof (rule ccontr)
      assume "\<not> n \<le> d + 1" 
      hence lt: "n > d + 1" by auto
      with sr have rt: "poly (char_poly A) x = 0" by auto
      from lt no have ord: "d + 1 < order x (char_poly A)" by auto
      from 1[OF rt c1 ord, unfolded compute_set_of_jordan_blocks[OF jnf]] nx lt
      show False by force
    qed
  qed
qed

lemma norm_bound_complex_to_real: fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat n n" 
    and bnd: "\<exists>c1 c2. \<forall>k. norm_bound ((map_mat complex_of_real A) ^\<^sub>m k) (c1 + c2 * of_nat k ^ d)"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)"
proof -
  let ?B = "map_mat complex_of_real A" 
  from bnd obtain c1 c2 where nb: "\<And> k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ d)" by auto
  show ?thesis
  proof (rule exI[of _ c1], rule exI[of _ c2], intro allI impI)
    fix k a
    assume "a \<in> elements_mat (A ^\<^sub>m k)"
    with pow_carrier_mat[OF A] obtain i j where a: "a = (A ^\<^sub>m k) $$ (i,j)" and ij: "i < n" "j < n"
      unfolding elements_mat by force
    from ij nb[of k] A have "norm ((?B ^\<^sub>m k) $$ (i,j)) \<le> c1 + c2 * real k ^ d"
      unfolding norm_bound_def by auto
    also have "(?B ^\<^sub>m k) $$ (i,j) = of_real a"
      unfolding of_real_hom.mat_hom_pow[OF A, symmetric] a using ij A by auto
    also have "norm (complex_of_real a) = abs a" by auto
    finally show "abs a \<le> (c1 + c2 * real k ^ d)" .
  qed
qed

text \<open>Now we will develop a tight criterion for non-negative real matrices.\<close>

definition max_list :: "nat list \<Rightarrow> nat" where
  "max_list xs = foldr max xs 0"

lemma max_list: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs" 
  unfolding max_list_def by (induct xs, auto)

lemma sum_list_approx: assumes kn: "k \<ge> (n :: nat)" and n: "n \<noteq> 0" 
  shows "0 \<notin> set ks \<Longrightarrow> n * length (filter (op dvd k) ks) \<le> sum_list ks" 
proof (induct ks)
  case (Cons x ks)
  {
    assume "k dvd x" 
    with Cons(2-) n have "x \<ge> k" by (simp add: dvd_imp_le)
    with kn have "x \<ge> n" by auto
  }
  with Cons show ?case using kn n by auto
qed auto

context 
  fixes A :: "real mat" and n :: nat and ks :: "nat list"
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and ks: "ks = fst (decompose_prod_root_unity (char_poly A))"
begin

  
lemma jnf_perron_frobenius_generic:  
  assumes main: "\<And> x k. 
     sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>     (* length ks = multiplicity of root 1, cheap test *)
     0 \<notin> set ks \<Longrightarrow> k \<in> {1 .. max_list ks} \<Longrightarrow>  
     length [k'\<leftarrow>ks . k dvd k'] > d + 1 \<Longrightarrow> 
        (* length [k'\<leftarrow>ks . k dvd k'] is the multiplicity of x when x^k = 1 and k is minimal *)
     primitive_root_unity k x \<Longrightarrow> (* consider primitive root of unity *)
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
       (* eventually compute Jordan-blocks *)
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (cases "n = 0")
  case n: False
  let ?cA = "map_mat complex_of_real A" 
  from A have cA: "?cA \<in> carrier_mat n n" by auto
  from ks obtain f where dec: "decompose_prod_root_unity (char_poly A) = (ks, f)" (is "?t = _")
    by (cases ?t, auto)
  note pf = perron_frobenius_for_complexity_jnf[OF A n nonneg sr dec, simplified]
  show ?thesis
  proof (rule norm_bound_complex_to_real[OF A], rule jnf_complexity_generic[OF cA])
    fix x
    from pf(1) have ks0: "0 \<notin> set ks" by auto
    let ?p = "prod_root_unity ks :: real poly" 
    have "n = degree (char_poly A)" and A0: "char_poly A \<noteq> 0" 
      using degree_monic_char_poly[OF A] by auto
    have "n = degree (char_poly A)" by fact 
    also have "\<dots> = degree ?p + degree f"
      using A0 unfolding pf(2) by (subst degree_mult_eq, auto)
    also have "\<dots> \<ge> degree ?p" by auto
    also have "degree ?p = sum_list ks" using degree_prod_root_unity[OF ks0] by auto
    finally have sum_ks: "sum_list ks \<le> n" .
    assume rt: "poly (char_poly ?cA) x = 0" 
    from pf(4)[OF this] show "cmod x \<le> 1" .
    assume 1: "cmod x = 1" and d: "d + 1 < order x (char_poly ?cA)" 
    from pf(7)[OF 1 rt] ks0 obtain K where K: "K \<in> set ks" "K \<noteq> 0" "x ^ K = 1" by auto
    from primitive_root_unity_exists[OF K(2-)] obtain k where kK: "k \<le> K" and 
      k: "primitive_root_unity k x" by auto
    from primitive_root_unity_dvd[OF k]
    have min: "x ^ n = 1 \<longleftrightarrow> k dvd n" for n .
    from primitive_root_unityD[OF k] have k0: "k \<noteq> 0" and rt: "x ^ k = 1" by auto
    from order.trans[OF kK max_list[OF K(1)]] k0 have k_mem: "k \<in> {1 .. max_list ks}" by auto
    have "order x (char_poly ?cA) = length [k\<leftarrow>ks . x ^ k = 1]" using pf(6)[OF 1] by simp
    also have "[k\<leftarrow>ks. x ^ k = 1] = filter (\<lambda> k'. k dvd k') [k'\<leftarrow>ks. x ^ k' = 1]"
      by (rule sym, unfold filter_id_conv, insert min, auto)
    also have "\<dots> = filter (\<lambda> k'. x ^ k' = 1) [k'\<leftarrow>ks. k dvd k']" unfolding filter_filter 
      by (rule filter_cong, auto)
    also have "\<dots> = [k'\<leftarrow>ks. k dvd k']" 
      by (unfold filter_id_conv, insert min, auto)
    finally have order_length: "order x (char_poly ?cA) = length [k'\<leftarrow>ks. k dvd k']" .
    from d[unfolded this] have len: "d + 1 < length (filter (op dvd k) ks)" .
    also have "\<dots> \<le> length ks" by simp
    finally have len3: "d + 1 < length ks" by auto
    from main[OF sum_ks len3 ks0 k_mem len k]
    show "\<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks ?cA x). bsize \<le> d + 1" by auto
  qed
next
  case 0: True
  from A[unfolded this] 
  have A: "A ^\<^sub>m k = 1\<^sub>m 0" for k using A by (intro eq_matI, auto)
  show ?thesis unfolding A by (auto simp: elements_mat_def) 
qed

lemma jnf_perron_frobenius_only_block_1:  
  assumes size: "n \<le> 2 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) 1). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  show ?case
  proof (cases "k = 1")
    case True
    from 1 root_1 show ?thesis unfolding True primitive_root_unity_explicit by auto
  next
    case False
    with 1 have k: "k \<ge> 2" by auto
    from 1(5) have "2 * (d + 2) \<le> 2 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "2 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed
    
lemma jnf_perron_frobenius_only_blocks_1_and_minus_1:  
  assumes size: "n \<le> 3 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) 1). 
       bsize \<le> d + 1)" 
  and root_2: "  
     length [k'\<leftarrow>ks . 2 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) (-1)). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  from 1(4)
  consider (k1) "k = 1" | (k2) "k = 2" | (k) "k \<ge> 3" by fastforce
  thus ?case
  proof cases
    case k1
    from 1 root_1 show ?thesis unfolding k1 primitive_root_unity_explicit by auto
  next
    case k2
    from 1 root_2 show ?thesis unfolding k2 primitive_root_unity_explicit by auto
  next
    case k
    from 1(5) have "3 * (d + 2) \<le> 3 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "3 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed

lemma jnf_perron_frobenius_only_square_roots:  
  assumes size: "n \<le> 5 * (d + 2) - 1" 
  and root_1: "sum_list ks \<le> n \<Longrightarrow> 
     length ks > d + 1 \<Longrightarrow>
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) 1). 
       bsize \<le> d + 1)" 
  and root_2: "  
     length [k'\<leftarrow>ks . 2 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) (-1)). 
       bsize \<le> d + 1)" 
  and root_3: "\<And> x. x \<in> {Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)} \<Longrightarrow>
     length [k'\<leftarrow>ks . 3 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
  and root_4: "\<And> x. x \<in> {\<i>, - \<i>} \<Longrightarrow>
     length [k'\<leftarrow>ks . 4 dvd k'] > d + 1 \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d + 1)" 
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ d)" 
proof (rule jnf_perron_frobenius_generic, goal_cases)
  case (1 x k)
  from 1(4)
  consider (k1) "k = 1" | (k2) "k = 2" | (k3) "k = 3" | (k4) "k = 4" | (k) "k \<ge> 5" by fastforce
  thus ?case
  proof cases
    case k1
    from 1 root_1 show ?thesis unfolding k1 primitive_root_unity_explicit by auto
  next
    case k2
    from 1 root_2 show ?thesis unfolding k2 primitive_root_unity_explicit by auto
  next
    case k3
    from 1 root_3 show ?thesis unfolding k3 primitive_root_unity_explicit by auto
  next
    case k4
    from 1 root_4 show ?thesis unfolding k4 primitive_root_unity_explicit by auto
  next
    case k
    from 1(5) have "5 * (d + 2) \<le> 5 * length (filter (op dvd k) ks)" by auto
    also have "\<dots> \<le> n" using sum_list_approx[OF k _ 1(3)] 1(1) by auto
    finally have "5 * (d + 2) \<le> n" by auto
    with size have False by auto
    thus ?thesis by simp
  qed
qed
end

end
