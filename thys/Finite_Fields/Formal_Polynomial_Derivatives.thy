section \<open>Formal Derivatives\label{sec:pderiv}\<close>

theory Formal_Polynomial_Derivatives
  imports "HOL-Algebra.Polynomial_Divisibility" "Ring_Characteristic"
begin

definition pderiv ("pderiv\<index>") where 
  "pderiv\<^bsub>R\<^esub> x = ring.normalize R (
    map (\<lambda>i. int_embed R i \<otimes>\<^bsub>R\<^esub> ring.coeff R x i) (rev [1..<length x]))"

context domain
begin

lemma coeff_range:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "coeff f i \<in> K"
proof -
  have "coeff f i \<in> set f \<union> {\<zero>}"
    using coeff_img(3) by auto
  also have "... \<subseteq> K \<union> {\<zero>}"
    using assms(2) univ_poly_carrier polynomial_incl by blast
  also have "... \<subseteq> K" 
    using subringE[OF assms(1)] by simp
  finally show ?thesis by simp
qed

lemma pderiv_carr:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "pderiv f \<in> carrier (K[X])"
proof -
  have "int_embed R i \<otimes> coeff f i \<in> K" for i
    using coeff_range[OF assms] int_embed_range[OF assms(1)] 
    using subringE[OF assms(1)] by simp
  hence "polynomial K (pderiv f)"
    unfolding pderiv_def by (intro normalize_gives_polynomial, auto)
  thus ?thesis
    using univ_poly_carrier by auto
qed

lemma pderiv_coeff:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])"
  shows "coeff (pderiv f) k = int_embed R (Suc k) \<otimes> coeff f (Suc k)"
    (is "?lhs = ?rhs")
proof (cases "k + 1  < length f")
  case True
  define j where "j = length f - k - 2"
  define d where 
    "d = map (\<lambda>i. int_embed R i \<otimes> coeff f i) (rev [1..<length f])"

  have a: "j+1 < length f"
    using True unfolding j_def by simp
  hence b: "j < length [1..<length f]"
    by simp
  have c: "k < length d"
    unfolding d_def using True by simp
  have d: "degree d - k = j"
    unfolding d_def j_def by simp
  have e: "rev [Suc 0..<length f] ! j = length f - 1 - j"
    using b  by (subst rev_nth, auto)
  have f: "length f - j - 1 = k+1"
    unfolding j_def using True by simp

  have "coeff (pderiv f ) k = coeff (normalize d) k"
    unfolding pderiv_def d_def by simp
  also have "... = coeff d k"
    using normalize_coeff by simp
  also have "... = d ! j"
    using c d by (subst coeff_nth, auto)
  also have 
    "... = int_embed R (length f - j - 1) \<otimes> coeff f (length f - j - 1)"
    using b e unfolding d_def by simp
  also have "... = ?rhs"
    using f by simp
  finally show ?thesis by simp
next
  case False
  hence "Suc k \<ge> length f"
    by simp
  hence a:"coeff f (Suc k) = \<zero>"
    using coeff_img by blast
  have b:"coeff (pderiv f) k = \<zero>"
    unfolding pderiv_def normalize_coeff[symmetric] using False
    by (intro coeff_length, simp)
  show ?thesis 
    using int_embed_range[OF carrier_is_subring] by (simp add:a b) 
qed

lemma pderiv_const:
  assumes "degree x = 0"
  shows "pderiv x = \<zero>\<^bsub>K[X]\<^esub>"
proof (cases "length x = 0")
  case True
  then show ?thesis by (simp add:univ_poly_zero pderiv_def)
next
  case False
  hence "length x = 1" using assms by linarith
  then obtain y where "x = [y]" by (cases x, auto) 
  then show ?thesis by (simp add:univ_poly_zero pderiv_def)
qed

lemma pderiv_var:
  shows "pderiv X = \<one>\<^bsub>K[X]\<^esub>"
  unfolding var_def pderiv_def
  by (simp add:univ_poly_one int_embed_def)

lemma pderiv_zero:
  shows "pderiv \<zero>\<^bsub>K[X]\<^esub> = \<zero>\<^bsub>K[X]\<^esub>"
  unfolding pderiv_def univ_poly_zero by simp

lemma pderiv_add:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "pderiv (f \<oplus>\<^bsub>K[X]\<^esub> g) = pderiv f \<oplus>\<^bsub>K[X]\<^esub> pderiv g"
    (is "?lhs = ?rhs")
proof -
  interpret p: ring "(K[X])"
    using univ_poly_is_ring[OF assms(1)] by simp

  let ?n = "(\<lambda>i. int_embed R i)"

  have a[simp]:"?n k \<in> carrier R" for k
    using int_embed_range[OF carrier_is_subring] by auto
  have b[simp]:"coeff f k \<in> carrier R" if "f \<in> carrier (K[X])" for k f
    using coeff_range[OF assms(1)] that
    using subringE(1)[OF assms(1)] by auto

  have "coeff ?lhs i = coeff ?rhs i" for i
  proof -
    have "coeff ?lhs i = ?n (i+1) \<otimes> coeff (f \<oplus>\<^bsub>K [X]\<^esub> g) (i+1)"
      by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = ?n (i+1) \<otimes> (coeff f (i+1) \<oplus> coeff g (i+1))"
      by (subst coeff_add[OF assms], simp)
    also have "... = ?n (i+1) \<otimes> coeff f (i+1) 
      \<oplus> int_embed R (i+1) \<otimes> coeff g (i+1)"
      by (subst r_distr, simp_all)
    also have "... = coeff (pderiv f) i \<oplus> coeff (pderiv g) i"
      by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = coeff (pderiv f \<oplus>\<^bsub>K [X]\<^esub> pderiv g) i"
      using pderiv_carr[OF assms(1)] 
      by (subst coeff_add[OF assms(1)], auto) 
    finally show ?thesis by simp
  qed
  hence "coeff ?lhs = coeff ?rhs" by auto
  thus "?lhs = ?rhs"
    using pderiv_carr[OF assms(1)]
    by (subst coeff_iff_polynomial_cond[where K="K"])
      (simp_all add:univ_poly_carrier)+
qed

lemma pderiv_inv:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])"
  shows "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = \<ominus>\<^bsub>K[X]\<^esub> pderiv f" (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(1)] by simp

  have "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> \<zero>\<^bsub>K[X]\<^esub>"
    using pderiv_carr[OF assms(1)]
    by (subst p.r_zero, simp_all)
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> (pderiv f \<ominus>\<^bsub>K[X]\<^esub> pderiv f)" 
    using pderiv_carr[OF assms(1)] by simp
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) \<oplus>\<^bsub>K[X]\<^esub> pderiv f \<ominus>\<^bsub>K[X]\<^esub> pderiv f" 
    using pderiv_carr[OF assms(1)]
    unfolding a_minus_def by (simp add:p.a_assoc)
  also have "... = pderiv (\<ominus>\<^bsub>K[X]\<^esub> f \<oplus>\<^bsub>K[X]\<^esub> f) \<ominus>\<^bsub>K[X]\<^esub> pderiv f" 
    by (subst pderiv_add[OF assms(1)], simp_all)
  also have "... = pderiv \<zero>\<^bsub>K[X]\<^esub> \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by (subst p.l_neg, simp_all)
  also have "... = \<zero>\<^bsub>K[X]\<^esub> \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by (subst pderiv_zero, simp)
  also have "... = \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    unfolding a_minus_def using pderiv_carr[OF assms(1)]
    by (subst p.l_zero, simp_all)
  finally show "pderiv (\<ominus>\<^bsub>K[X]\<^esub> f) = \<ominus>\<^bsub>K[X]\<^esub> pderiv f"
    by simp
qed


lemma coeff_mult:
  assumes "subring K R"
  assumes "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "coeff (f \<otimes>\<^bsub>K[X]\<^esub> g) i = 
    (\<Oplus> k \<in> {..i}. (coeff f) k \<otimes> (coeff g) (i - k))"
proof -
  have a:"set f \<subseteq> carrier R"
    using assms(1,2) univ_poly_carrier 
    using subringE(1)[OF assms(1)] polynomial_incl by blast
  have b:"set g \<subseteq> carrier R" 
    using assms(1,3) univ_poly_carrier
    using subringE(1)[OF assms(1)] polynomial_incl by blast
  show ?thesis
    unfolding univ_poly_mult poly_mult_coeff[OF a b] by simp
qed

lemma pderiv_mult:
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])" "g \<in> carrier (K[X])"
  shows "pderiv (f \<otimes>\<^bsub>K[X]\<^esub> g) = 
    pderiv f \<otimes>\<^bsub>K[X]\<^esub> g \<oplus>\<^bsub>K[X]\<^esub> f \<otimes>\<^bsub>K[X]\<^esub> pderiv g" 
    (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(1)] by simp

  let ?n = "(\<lambda>i. int_embed R i)"

  have a[simp]:"?n k \<in> carrier R" for k 
    using int_embed_range[OF carrier_is_subring] by auto
  have b[simp]:"coeff f k \<in> carrier R" if "f \<in> carrier (K[X])" for k f
    using coeff_range[OF assms(1)] 
    using subringE(1)[OF assms(1)] that by auto

  have "coeff ?lhs i = coeff ?rhs i" for i
  proof -
    have "coeff ?lhs i = ?n (i+1) \<otimes> coeff (f \<otimes>\<^bsub>K [X]\<^esub> g) (i+1)"
      using assms(2,3) by (simp add: pderiv_coeff[OF assms(1)])
    also have "... = ?n (i+1) \<otimes> 
      (\<Oplus>k \<in> {..i+1}. coeff f k \<otimes> (coeff g (i + 1 - k)))"
      by (subst coeff_mult[OF assms], simp)
    also have "... = 
      (\<Oplus>k \<in> {..i+1}. ?n (i+1) \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)))"
      by (intro finsum_rdistr, simp_all add:Pi_def) 
    also have "... = 
      (\<Oplus>k \<in> {..i+1}. ?n k \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)) \<oplus>
      ?n (i+1-k) \<otimes> (coeff f k \<otimes> coeff g (i + 1 - k)))" 
      using int_embed_add[symmetric] of_nat_diff
      by (intro finsum_cong') 
        (simp_all add:l_distr[symmetric] of_nat_diff) 
    also have "... = 
      (\<Oplus>k \<in> {..i+1}. ?n k \<otimes> coeff f k \<otimes> coeff g (i + 1 - k) \<oplus>
      coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i + 1 - k)))" 
      using Pi_def a b m_assoc m_comm
      by (intro finsum_cong' arg_cong2[where f="(\<oplus>)"], simp_all)
    also have "... = 
      (\<Oplus>k \<in> {..i+1}. ?n k \<otimes> coeff f k \<otimes> coeff g (i+1-k)) \<oplus>
      (\<Oplus>k \<in> {..i+1}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1-k)))" 
      by (subst finsum_addf[symmetric], simp_all add:Pi_def) 
    also have "... = 
      (\<Oplus>k\<in>insert 0 {1..i+1}. ?n k \<otimes> coeff f k \<otimes> coeff g (i+1-k)) \<oplus>
      (\<Oplus>k\<in>insert (i+1) {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1-k)))" 
      using subringE(1)[OF assms(1)]
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong')
        (auto simp:set_eq_iff)
    also have "... = 
      (\<Oplus>k \<in> {1..i+1}. ?n k \<otimes> coeff f k \<otimes> coeff g (i+1-k)) \<oplus>
      (\<Oplus>k \<in> {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1-k)))" 
      by (subst (1 2) finsum_insert, auto simp add:int_embed_zero)
    also have "... = 
      (\<Oplus>k \<in> Suc ` {..i}. ?n k \<otimes> coeff f (k) \<otimes> coeff g (i+1-k)) \<oplus>
      (\<Oplus>k \<in> {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1-k)))" 
      by (intro arg_cong2[where f="(\<oplus>)"] finsum_cong')
        (simp_all add:Pi_def atMost_atLeast0)
    also have "... = 
      (\<Oplus>k \<in> {..i}. ?n (k+1) \<otimes> coeff f (k+1) \<otimes> coeff g (i-k)) \<oplus>
      (\<Oplus>k \<in> {..i}. coeff f k \<otimes> (?n (i+1-k) \<otimes> coeff g (i+1-k)))" 
      by (subst finsum_reindex, auto)
    also have "... = 
      (\<Oplus>k \<in> {..i}. coeff (pderiv f) k \<otimes> coeff g (i-k)) \<oplus>
      (\<Oplus>k \<in> {..i}. coeff f k \<otimes> coeff (pderiv g) (i-k))" 
      using Suc_diff_le
      by (subst (1 2) pderiv_coeff[OF assms(1)]) 
        (auto intro!: finsum_cong')
    also have "... = 
      coeff (pderiv f \<otimes>\<^bsub>K[X]\<^esub> g) i \<oplus> coeff (f \<otimes>\<^bsub>K[X]\<^esub> pderiv g) i"
      using pderiv_carr[OF assms(1)]
      by (subst (1 2) coeff_mult[OF assms(1)], auto)
    also have "... = coeff ?rhs i" 
      using pderiv_carr[OF assms(1)]
      by (subst coeff_add[OF assms(1)], auto)
    finally show ?thesis by simp
  qed

  hence "coeff ?lhs = coeff ?rhs" by auto
  thus "?lhs = ?rhs"
    using pderiv_carr[OF assms(1)]
    by (subst coeff_iff_polynomial_cond[where K="K"])
     (simp_all add:univ_poly_carrier)
qed

lemma pderiv_pow:
  assumes "n > (0 :: nat)"
  assumes "subring K R"
  assumes [simp]: "f \<in> carrier (K[X])"
  shows "pderiv (f [^]\<^bsub>K[X]\<^esub> n) = 
    int_embed (K[X]) n \<otimes>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K[X]\<^esub> (n-1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f" 
    (is "?lhs = ?rhs")
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(2)] by simp

  let ?n = "\<lambda>n. int_embed (K[X]) n"

  have [simp]: "?n i \<in> carrier (K[X])" for i 
    using p.int_embed_range[OF p.carrier_is_subring] by simp

  obtain m where n_def: "n = Suc m" using assms(1) lessE by blast
  have "pderiv (f [^]\<^bsub>K[X]\<^esub> (m+1)) = 
    ?n (m+1) \<otimes>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K[X]\<^esub> m \<otimes>\<^bsub>K[X]\<^esub> pderiv f" 
  proof (induction m)
    case 0
    then show ?case 
      using pderiv_carr[OF assms(2)] assms(3) 
      using p.int_embed_one by simp
  next
    case (Suc m)
    have "pderiv (f [^]\<^bsub>K [X]\<^esub> (Suc m + 1)) = 
      pderiv (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> f) "
      by simp
    also have "... = 
      pderiv (f [^]\<^bsub>K [X]\<^esub> (m+1)) \<otimes>\<^bsub>K[X]\<^esub> f \<oplus>\<^bsub>K[X]\<^esub> 
      f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f"
      using assms(3) by (subst pderiv_mult[OF assms(2)], auto)
    also have "... = 
      (?n (m+1) \<otimes>\<^bsub>K [X]\<^esub> f [^]\<^bsub>K [X]\<^esub> m \<otimes>\<^bsub>K [X]\<^esub> pderiv f) \<otimes>\<^bsub>K[X]\<^esub> f 
      \<oplus>\<^bsub>K[X]\<^esub> f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f"
      by (subst Suc(1), simp)  
    also have 
      "... = ?n (m+1) \<otimes>\<^bsub>K[X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f) 
      \<oplus>\<^bsub>K[X]\<^esub> \<one>\<^bsub>K [X]\<^esub> \<otimes>\<^bsub>K[X]\<^esub> (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K[X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)]
      apply (intro arg_cong2[where f="(\<oplus>\<^bsub>K[X]\<^esub>)"])
      apply (simp add:p.m_assoc)
       apply (simp add:p.m_comm)
      by simp
    also have 
      "... = (?n (m+1) \<oplus>\<^bsub>K[X]\<^esub> \<one>\<^bsub>K [X]\<^esub>) \<otimes>\<^bsub>K [X]\<^esub> 
      (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K [X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)] 
      by (subst p.l_distr[symmetric], simp_all)
    also have "... = 
      (\<one>\<^bsub>K [X]\<^esub> \<oplus>\<^bsub>K[X]\<^esub> ?n (m+1)) \<otimes>\<^bsub>K [X]\<^esub> 
      (f [^]\<^bsub>K [X]\<^esub> (m+1) \<otimes>\<^bsub>K [X]\<^esub> pderiv f)"
      using assms(3) pderiv_carr[OF assms(2)]
      by (subst p.a_comm, simp_all)
    also have "... = ?n (1+ Suc m) 
      \<otimes>\<^bsub>K [X]\<^esub> f [^]\<^bsub>K [X]\<^esub> (Suc m) \<otimes>\<^bsub>K [X]\<^esub> pderiv f"
      using assms(3) pderiv_carr[OF assms(2)] of_nat_add
      apply (subst (2) of_nat_add, subst p.int_embed_add)
      by (simp add:p.m_assoc p.int_embed_one) 
    finally show ?case by simp
  qed
  thus "?thesis" using n_def by auto
qed

lemma pderiv_var_pow:
  assumes "n > (0::nat)"
  assumes "subring K R"
  shows "pderiv (X [^]\<^bsub>K[X]\<^esub> n) = 
    int_embed (K[X]) n \<otimes>\<^bsub>K[X]\<^esub> X [^]\<^bsub>K[X]\<^esub> (n-1)"
proof -
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms(2)] by simp

  have [simp]: "int_embed (K[X]) i \<in> carrier (K[X])" for i
    using p.int_embed_range[OF p.carrier_is_subring] by simp

  show ?thesis
    using var_closed[OF assms(2)] 
    using pderiv_var[where K="K"] pderiv_carr[OF assms(2)]
    by (subst pderiv_pow[OF assms(1,2)], simp_all)
qed

lemma int_embed_consistent_with_poly_of_const:
  assumes "subring K R"
  shows "int_embed (K[X]) m = poly_of_const (int_embed R m)"
proof -
  define K' where "K' = R \<lparr> carrier := K \<rparr>"
  interpret p: cring "(K[X])"
    using univ_poly_is_cring[OF assms] by simp
  interpret d: domain "K'"
    unfolding K'_def
    using assms(1) subdomainI' subdomain_is_domain by simp
  interpret h: ring_hom_ring  "K'" "K[X]" "poly_of_const"
    unfolding K'_def
    using canonical_embedding_ring_hom[OF assms(1)] by simp

  define n where "n=nat (abs m)"

  have a1: "int_embed (K[X]) (int n) = poly_of_const (int_embed K' n)"
  proof (induction n)
    case 0
    then show ?case by (simp add:d.int_embed_zero p.int_embed_zero)
  next
    case (Suc n)
    then show ?case
      using d.int_embed_closed d.int_embed_add d.int_embed_one
      by (simp add:p.int_embed_add p.int_embed_one)
  qed
  also have "... = poly_of_const (int_embed R n)"
    unfolding K'_def using int_embed_consistent[OF assms] by simp
  finally have a: 
    "int_embed (K[X]) (int n) = poly_of_const (int_embed R (int n))"
    by simp

  have "int_embed (K[X]) (-(int n)) = 
    poly_of_const (int_embed K' (- (int n)))"
    using d.int_embed_closed a1 by (simp add: p.int_embed_inv d.int_embed_inv)
  also have "... = poly_of_const (int_embed R (- (int n)))"
    unfolding K'_def using int_embed_consistent[OF assms] by simp
  finally have b:
    "int_embed (K[X]) (-int n) = poly_of_const (int_embed R (-int n))"
    by simp

  show ?thesis
    using a b n_def by (cases "m \<ge> 0", simp, simp)
qed

end

end
