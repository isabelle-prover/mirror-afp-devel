(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Polynomial\<close>

text \<open>The theory contains some basic results on polynomials which have not been detected in
  the distribution, especially on linear factors and degrees.\<close>

theory Missing_Polynomial
imports 
  "~~/src/HOL/Library/Polynomial"
begin

lemma poly_setprod: "poly (\<Prod>k\<in>A. p k) x = (\<Prod>k\<in>A. poly (p k) x)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma linear_poly_root: "(a :: 'a :: comm_ring_1) \<in> set as \<Longrightarrow> poly (\<Prod> a \<leftarrow> as. [: - a, 1:]) a = 0"
proof (induct as)
  case (Cons b as)
  show ?case
  proof (cases "a = b")
    case False
    with Cons have "a \<in> set as" by auto
    from Cons(1)[OF this] show ?thesis by simp
  qed simp
qed simp

context
  fixes sort :: "'a :: idom"
begin
lemma poly_linear_linear_factor: assumes 
  dvd: "[:b,1:] dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "b \<in> set as"
proof -
  let ?p = "\<lambda> as. (\<Prod> a \<leftarrow> as. [: a, 1:])"
  let ?b = "[:b,1:]"
  from assms[unfolded dvd_def] obtain p where id: "?p as = ?b * p" ..
  from arg_cong[OF id, of "\<lambda> p. poly p (-b)"]
  have "poly (?p as) (-b) = 0" by simp
  thus ?thesis
  proof (induct as)
    case (Cons a as)
    have "?p (a # as) = [:a,1:] * ?p as" by simp
    from Cons(2)[unfolded this] have "poly (?p as) (-b) = 0 \<or> (a - b) = 0" by simp
    with Cons(1) show ?case by auto
  qed simp
qed

lemma poly_linear_exp_linear_factors: 
  assumes dvd: "([:b,1:])^n dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "length (filter (op = b) as) \<ge> n"
proof -
  let ?p = "\<lambda> as. (\<Prod> a \<leftarrow> as. [: a, 1:])"
  let ?b = "[:b,1:]"
  from dvd show ?thesis
  proof (induct n arbitrary: as)
    case (Suc n as)
    have bs: "?b ^ Suc n = ?b * ?b ^ n" by simp
    from poly_linear_linear_factor[OF dvd_mult_left[OF Suc(2)[unfolded bs]], 
      unfolded in_set_conv_decomp]
    obtain as1 as2 where as: "as = as1 @ b # as2" by auto
    have "?p as = [:b,1:] * ?p (as1 @ as2)" unfolding as
    proof (induct as1)
      case (Cons a as1)
      have "?p (a # as1 @ b # as2) = [:a,1:] * ?p (as1 @ b # as2)" by simp
      also have "?p (as1 @ b # as2) = [:b,1:] * ?p (as1 @ as2)" unfolding Cons by simp
      also have "[:a,1:] * \<dots> = [:b,1:] * ([:a,1:] * ?p (as1 @ as2))" 
        by (metis (no_types, lifting) mult.left_commute)
      finally show ?case by simp
    qed simp
    from Suc(2)[unfolded bs this dvd_mult_cancel_left]
    have "?b ^ n dvd ?p (as1 @ as2)" by simp
    from Suc(1)[OF this] show ?case unfolding as by simp
  qed simp    
qed
end

lemma degree_setsum_le: "finite S \<Longrightarrow> (\<And> p . p \<in> S \<Longrightarrow> degree (f p) \<le> n)
  \<Longrightarrow> degree (setsum f S) \<le> n"
proof (induct S rule: finite_induct)
  case (insert p S)
  hence "degree (setsum f S) \<le> n" "degree (f p) \<le> n" by auto
  thus ?case unfolding setsum.insert[OF insert(1-2)] by (metis degree_add_le)
qed simp

lemma degree_lcoeff_setsum: assumes deg: "degree (f q) = n"
  and fin: "finite S" and q: "q \<in> S" and degle: "\<And> p . p \<in> S - {q} \<Longrightarrow> degree (f p) < n"
  and cong: "coeff (f q) n = c"
  shows "degree (setsum f S) = n \<and> coeff (setsum f S) n = c"
proof (cases "S = {q}")
  case True
  thus ?thesis using deg cong by simp
next
  case False
  with q obtain p where "p \<in> S - {q}" by auto
  from degle[OF this] have n: "n > 0" by auto
  have "degree (setsum f S) = degree (f q + setsum f (S - {q}))"
    unfolding setsum.remove[OF fin q] ..
  also have "\<dots> = degree (f q)"
  proof (rule degree_add_eq_left)
    have "degree (setsum f (S - {q})) \<le> n - 1"
    proof (rule degree_setsum_le)
      fix p
      show "p \<in> S - {q} \<Longrightarrow> degree (f p) \<le> n - 1"
        using degle[of p] by auto
    qed (insert fin, auto)
    also have "\<dots> < n" using n by simp
    finally show "degree (setsum f (S - {q})) < degree (f q)" unfolding deg .
  qed
  finally show ?thesis unfolding deg[symmetric] cong[symmetric]
  proof (rule conjI)
    have id: "(\<Sum>x\<in>S - {q}. coeff (f x) (degree (f q))) = 0"
      by (rule setsum.neutral, rule ballI, rule coeff_eq_0[OF degle[folded deg]])
    show "coeff (setsum f S) (degree (f q)) = coeff (f q) (degree (f q))"
      unfolding coeff_setsum
      by (subst setsum.remove[OF _ q], unfold id, insert fin, auto)
  qed
qed

lemma degree_setprod_setsum_le: "finite S \<Longrightarrow> degree (setprod f S) \<le> setsum (degree o f) S"
proof (induct S rule: finite_induct)
  case (insert a S)
  show ?case unfolding setprod.insert[OF insert(1-2)] setsum.insert[OF insert(1-2)]
    by (rule le_trans[OF degree_mult_le], insert insert, auto)
qed simp

lemma lcoeff_monic_mult: assumes monic: "coeff p (degree (p :: 'a :: comm_semiring_1 poly)) = 1"
  shows "coeff (p * q) (degree p + degree q) = coeff q (degree q)"
proof -
  let ?pqi = "\<lambda> i. coeff p i * coeff q (degree p + degree q - i)" 
  have "coeff (p * q) (degree p + degree q) = 
    (\<Sum>i\<le>degree p + degree q. ?pqi i)"
    unfolding coeff_mult by simp
  also have "\<dots> = ?pqi (degree p) + (setsum ?pqi ({.. degree p + degree q} - {degree p}))"
    by (subst setsum.remove[of _ "degree p"], auto)
  also have "?pqi (degree p) = coeff q (degree q)" unfolding monic by simp
  also have "(setsum ?pqi ({.. degree p + degree q} - {degree p})) = 0"
  proof (rule setsum.neutral, intro ballI)
    fix d
    assume d: "d \<in> {.. degree p + degree q} - {degree p}"
    show "?pqi d = 0"
    proof (cases "d < degree p")
      case True
      hence "degree p + degree q - d > degree q" by auto
      hence "coeff q (degree p + degree q - d) = 0" by (rule coeff_eq_0)
      thus ?thesis by simp
    next
      case False
      with d have "d > degree p" by auto
      hence "coeff p d = 0" by (rule coeff_eq_0)
      thus ?thesis by simp
    qed
  qed
  finally show ?thesis by simp
qed

lemma degree_monic_mult: assumes monic: "coeff p (degree (p :: 'a :: comm_semiring_1 poly)) = 1"
  and q: "q \<noteq> 0"
  shows "degree (p * q) = degree p + degree q"
proof -
  have "degree p + degree q \<ge> degree (p * q)" by (rule degree_mult_le)
  also have "degree p + degree q \<le> degree (p * q)"
  proof -
    from q have cq: "coeff q (degree q) \<noteq> 0" by auto
    hence "coeff (p * q) (degree p + degree q) \<noteq> 0" unfolding lcoeff_monic_mult[OF monic] .
    thus "degree (p * q) \<ge> degree p + degree q" by (rule le_degree)
  qed
  finally show ?thesis .
qed
  

lemma degree_setprod_setsum_monic: assumes
  S: "finite S"
  and nzd: "0 \<notin> (degree o f) ` S"
  and monic: "(\<And> a . a \<in> S \<Longrightarrow> coeff (f a) (degree (f a)) = 1)"
  shows "degree (setprod f S) = (setsum (degree o f) S) \<and> coeff (setprod f S) (setsum (degree o f) S) = 1"
proof -
  from S nzd monic 
  have "degree (setprod f S) = setsum (degree \<circ> f) S 
  \<and> (S \<noteq> {} \<longrightarrow> degree (setprod f S) \<noteq> 0 \<and> setprod f S \<noteq> 0) \<and> coeff (setprod f S) (setsum (degree o f) S) = 1"
  proof (induct S rule: finite_induct)
    case (insert a S)
    have IH1: "degree (setprod f S) = setsum (degree o f) S"
      using insert by auto
    have IH2: "coeff (setprod f S) (degree (setprod f S)) = 1"
      using insert by auto
    have id: "degree (setprod f (insert a S)) = setsum (degree \<circ> f) (insert a S)
      \<and> coeff (setprod f (insert a S)) (setsum (degree o f) (insert a S)) = 1"
    proof (cases "S = {}")
      case False
      with insert have nz: "setprod f S \<noteq> 0" by auto
      from insert have monic: "coeff (f a) (degree (f a)) = 1" by auto
      have id: "(degree \<circ> f) a = degree (f a)" by simp
      show ?thesis unfolding setprod.insert[OF insert(1-2)] setsum.insert[OF insert(1-2)] id
        unfolding degree_monic_mult[OF monic nz] 
        unfolding IH1[symmetric]
        unfolding lcoeff_monic_mult[OF monic] IH2 by simp
    qed (insert insert, auto)
    show ?case using id unfolding setsum.insert[OF insert(1-2)] using insert by auto
  qed simp
  thus ?thesis by auto
qed 

lemma degree_setprod_monic: 
  assumes "\<And> i. i < n \<Longrightarrow> degree (f i :: 'a :: comm_semiring_1 poly) = 1"
    and "\<And> i. i < n \<Longrightarrow> coeff (f i) 1 = 1"
  shows "degree (setprod f {0 ..< n}) = n \<and> coeff (setprod f {0 ..< n}) n = 1"
proof -
  from degree_setprod_setsum_monic[of "{0 ..< n}" f] show ?thesis using assms by force
qed

lemma degree_setprod_setsum_lt_n: assumes "\<And> i. i < n \<Longrightarrow> degree (f i :: 'a :: comm_semiring_1 poly) \<le> 1"
  and i: "i < n" and fi: "degree (f i) = 0"
  shows "degree (setprod f {0 ..< n}) < n"
proof -
  have "degree (setprod f {0 ..< n}) \<le> setsum (degree o f) {0 ..< n}"
    by (rule degree_setprod_setsum_le, auto)
  also have "setsum (degree o f) {0 ..< n} = (degree o f) i + setsum (degree o f) ({0 ..< n} - {i})"
    by (rule setsum.remove, insert i, auto)
  also have "(degree o f) i = 0" using fi by simp
  also have "setsum (degree o f) ({0 ..< n} - {i}) \<le> setsum (\<lambda> _. 1) ({0 ..< n} - {i})"
    by (rule setsum_mono, insert assms, auto)
  also have "\<dots> = n - 1" using i by simp
  also have "\<dots> < n" using i by simp
  finally show ?thesis by simp
qed

text \<open>The following proof structure is completely similar to the one
  of @{thm poly_roots_finite}.\<close>

lemma poly_roots_degree:
  fixes p :: "'a::idom poly"
  shows "p \<noteq> 0 \<Longrightarrow> card {x. poly p x = 0} \<le> degree p"
proof (induct n \<equiv> "degree p" arbitrary: p)
  case (0 p)
  then obtain a where "a \<noteq> 0" and "p = [:a:]"
    by (cases p, simp split: if_splits)
  then show ?case by simp
next
  case (Suc n p)
  show ?case
  proof (cases "\<exists>x. poly p x = 0")
    case True
    then obtain a where a: "poly p a = 0" ..
    then have "[:-a, 1:] dvd p" by (simp only: poly_eq_0_iff_dvd)
    then obtain k where k: "p = [:-a, 1:] * k" ..
    with `p \<noteq> 0` have "k \<noteq> 0" by auto
    with k have "degree p = Suc (degree k)"
      by (simp add: degree_mult_eq del: mult_pCons_left)
    with `Suc n = degree p` have "n = degree k" by simp
    from Suc.hyps(1)[OF this `k \<noteq> 0`]
    have le: "card {x. poly k x = 0} \<le> degree k" .
    have "card {x. poly p x = 0} = card {x. poly ([:-a, 1:] * k) x = 0}" unfolding k ..
    also have "{x. poly ([:-a, 1:] * k) x = 0} = insert a {x. poly k x = 0}"
      by auto
    also have "card \<dots> \<le> Suc (card {x. poly k x = 0})" 
      unfolding card_insert_if[OF poly_roots_finite[OF `k \<noteq> 0`]] by simp
    also have "\<dots> \<le> Suc (degree k)" using le by auto
    finally show ?thesis using `degree p = Suc (degree k)` by simp
  qed simp
qed

lemma poly_root_factor: "(poly ([: r, 1:] * q) (k :: 'a :: idom) = 0) = (k = -r \<or> poly q k = 0)" (is ?one)
  "(poly (q * [: r, 1:]) k = 0) = (k = -r \<or> poly q k = 0)" (is ?two)
  "(poly [: r, 1 :] k = 0) = (k = -r)" (is ?three)
proof -
  have [simp]: "r + k = 0 \<Longrightarrow> k = - r" by algebra
  show ?one unfolding poly_mult by auto
  show ?two unfolding poly_mult by auto
  show ?three by auto
qed

lemma poly_root_constant: "c \<noteq> 0 \<Longrightarrow> (poly (p * [:c:]) (k :: 'a :: idom) = 0) = (poly p k = 0)"
  unfolding poly_mult by auto

lemma degree_linear_factors: "degree (\<Prod> a \<leftarrow> as. [: f a, 1:]) = length as"
proof (induct as)
  case (Cons b as) note IH = this
  have id: "(\<Prod>a\<leftarrow>b # as. [:f a, 1:]) = [:f b,1 :] * (\<Prod>a\<leftarrow>as. [:f a, 1:])" by simp
  show ?case unfolding id
    by (subst degree_monic_mult, insert IH, auto)
qed simp

lemma smult_setsum: "smult (\<Sum>i \<in> S. f i) p = (\<Sum>i \<in> S. smult (f i) p)"
  by (induct S rule: infinite_finite_induct, auto simp: smult_add_left)

end
