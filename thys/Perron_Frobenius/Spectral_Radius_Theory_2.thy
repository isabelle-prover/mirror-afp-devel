section \<open>Combining Spectral Radius Theory with Perron Frobenius theorem\<close>

theory Spectral_Radius_Theory_2
imports 
  Perron_Frobenius_2
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
begin

hide_const (open) Coset.order

text \<open>get Perron Frobenius in JNF-world\<close>
lemmas perron_frobenius_for_complexity_jnf = 
  perron_frobenius_for_complexity[unfolded atomize_imp atomize_all, 
    untransferred, cancel_card_constraint, rule_format]


text \<open>This criterion is tight!\<close>

lemma jnf_complexity_generic: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x \<le> 1" 
  and 1: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> cmod x = 1 \<Longrightarrow> 
    order x (char_poly A) > d \<Longrightarrow> 
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks A x). bsize \<le> d)" 
shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))" 
proof - 
  from char_poly_factorized[OF A] obtain as where cA: "char_poly A = (\<Prod>a\<leftarrow>as. [:- a, 1:])" 
    and lenn: "length as = n" by auto 
  from jordan_nf_exists[OF A cA] obtain n_xs where jnf: "jordan_nf A n_xs" ..
  show ?thesis 
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
    show "n \<le> d" 
    proof (rule ccontr)
      assume "\<not> n \<le> d" 
      hence lt: "n > d" by auto
      with sr have rt: "poly (char_poly A) x = 0" by auto
      from lt no have ord: "d < order x (char_poly A)" by auto
      from 1[OF rt c1 ord, unfolded compute_set_of_jordan_blocks[OF jnf]] nx lt
      show False by force
    qed
  qed
qed

lemma norm_bound_complex_to_real: fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat n n" 
    and bnd: "\<exists>c1 c2. \<forall>k. norm_bound ((map_mat complex_of_real A) ^\<^sub>m k) (c1 + c2 * of_nat k ^ (d - 1))"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ (d - 1))"
proof -
  let ?B = "map_mat complex_of_real A" 
  from bnd obtain c1 c2 where nb: "\<And> k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ (d - 1))" by auto
  show ?thesis
  proof (rule exI[of _ c1], rule exI[of _ c2], intro allI impI)
    fix k a
    assume "a \<in> elements_mat (A ^\<^sub>m k)"
    with pow_carrier_mat[OF A] obtain i j where a: "a = (A ^\<^sub>m k) $$ (i,j)" and ij: "i < n" "j < n"
      unfolding elements_mat by force
    from ij nb[of k] A have "norm ((?B ^\<^sub>m k) $$ (i,j)) \<le> c1 + c2 * real k ^ (d - 1)"
      unfolding norm_bound_def by auto
    also have "(?B ^\<^sub>m k) $$ (i,j) = of_real a"
      unfolding of_real_hom.mat_hom_pow[OF A, symmetric] a using ij A by auto
    also have "norm (complex_of_real a) = abs a" by auto
    finally show "abs a \<le> (c1 + c2 * real k ^ (d - 1))" .
  qed
qed

text \<open>A tight criterion for non-negative real matrices\<close>

definition max_list :: "nat list \<Rightarrow> nat" where
  "max_list xs = foldr max xs 0"

lemma max_list: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs" 
  unfolding max_list_def by (induct xs, auto)

lemma jnf_perron_frobenius_generic: fixes A :: "real mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and sr: "\<And> x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and ks: "ks = fst (decompose_prod_root_unity (char_poly A))" 
  and main: "\<And> x k K. 
     length ks > d \<Longrightarrow>     (* length ks = multiplicity of root 1, cheap test *)
     0 \<notin> set ks \<Longrightarrow> k \<in> {1 .. max_list ks} \<Longrightarrow>  
     length [k'\<leftarrow>ks . k dvd k'] > d \<Longrightarrow> 
        (* length [k'\<leftarrow>ks . k dvd k'] is the multiplicity of x when x^k = 1 and k is minimal *)
      x^k = 1 \<Longrightarrow> (* consider arbitrary root of unity *)
    (\<forall> bsize \<in> fst ` set (compute_set_of_jordan_blocks (map_mat complex_of_real A) x). 
       bsize \<le> d)" 
       (* eventually compute Jordan-blocks *)
shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * of_nat k ^ (d - 1))" 
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
    assume 1: "cmod x = 1" and d: "d < order x (char_poly ?cA)" 
    let ?P = "\<lambda> k. x ^ k = 1 \<and> k \<noteq> 0" 
    define k where "k = (LEAST k. ?P k)" 
    from pf(7)[OF 1 rt] ks0 obtain K where K: "K \<in> set ks" "K \<noteq> 0" "x ^ K = 1"
      and Pk: "\<exists> k. ?P k" by metis
    from LeastI_ex[OF Pk, folded k_def] have k: "x ^ k = 1" and k0: "k \<noteq> 0" by auto
    have k_least: "k' \<noteq> 0 \<Longrightarrow> k' < k \<Longrightarrow> x ^ k' \<noteq> 1" for k' 
      using not_less_Least[of k' ?P, folded k_def] by force
    from root_unity_different_powers[OF k k0 k_least] 
    have min: "x ^ n = 1 \<longleftrightarrow> k dvd n" for n by force
    from this[of K] K have "k dvd K" by auto
    with K(2) have "k \<le> K" using dvd_imp_le by blast
    from order.trans[OF this max_list[OF K(1)]] k0 have k_mem: "k \<in> {1 .. max_list ks}" by auto
    have "order x (char_poly ?cA) = length [k\<leftarrow>ks . x ^ k = 1]" using pf(6)[OF 1] by simp
    also have "[k\<leftarrow>ks. x ^ k = 1] = filter (\<lambda> k'. k dvd k') [k'\<leftarrow>ks. x ^ k' = 1]"
      by (rule sym, unfold filter_id_conv, insert min, auto)
    also have "\<dots> = filter (\<lambda> k'. x ^ k' = 1) [k'\<leftarrow>ks. k dvd k']" unfolding filter_filter 
      by (rule filter_cong, auto)
    also have "\<dots> = [k'\<leftarrow>ks. k dvd k']" 
      by (unfold filter_id_conv, insert min, auto)
    finally have order_length: "order x (char_poly ?cA) = length [k'\<leftarrow>ks. k dvd k']" .
    from d[unfolded this] have len: "d < length (filter (op dvd k) ks)" .
    also have "\<dots> \<le> length ks" by simp
    finally have len3: "d < length ks" by auto
    from main[OF len3 ks0 k_mem len k]
    show "\<forall>bsize\<in>fst ` set (compute_set_of_jordan_blocks ?cA x). bsize \<le> d" by auto
  qed
next
  case 0: True
  from A[unfolded this] 
  have A: "A ^\<^sub>m k = 1\<^sub>m 0" for k using A by (intro eq_matI, auto)
  show ?thesis unfolding A by (auto simp: elements_mat_def) 
qed    

end
