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
  Missing_Unsorted
begin

subsection \<open>Basic Properties\<close>

lemma degree_0_id: assumes "degree p = 0"
  shows "[: coeff p 0 :] = p" 
proof -
  have "\<And> x. 0 \<noteq> Suc x" by auto 
  thus ?thesis using assms
  by (metis coeff_pCons_0 degree_pCons_eq_if pCons_cases)
qed

lemma degree0_coeffs: "degree p = 0 \<Longrightarrow>
  \<exists> a. p = [: a :]"
  by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)

lemma degree1_coeffs: "degree p = 1 \<Longrightarrow>
  \<exists> a b. p = [: b, a :] \<and> a \<noteq> 0" 
  by (metis One_nat_def degree_pCons_eq_if nat.inject old.nat.distinct(2) pCons_0_0 pCons_cases)

lemma degree2_coeffs: "degree p = 2 \<Longrightarrow>
  \<exists> a b c. p = [: c, b, a :] \<and> a \<noteq> 0"
  by (metis Suc_1 Suc_neq_Zero degree1_coeffs degree_pCons_eq_if nat.inject pCons_cases)

lemma coeff_monom_Suc: "coeff (monom a (Suc d) * p) (Suc i) = coeff (monom a d * p) i"
  by (simp add: monom_Suc)

lemma coeff_setsum_monom:
  assumes n: "n \<le> d"
  shows "coeff (\<Sum>i\<le>d. monom (f i) i) n = f n" (is "?l = _")
proof -
  have "?l = (\<Sum>i\<le>d. coeff (monom (f i) i) n)" (is "_ = setsum ?cmf _")
    using coeff_setsum.
  also have "{..d} = insert n ({..d}-{n})" using n by auto
    hence "setsum ?cmf {..d} = setsum ?cmf ..." by auto
  also have "... = setsum ?cmf ({..d}-{n}) + ?cmf n" by (subst setsum.insert,auto)
  also have "setsum ?cmf ({..d}-{n}) = 0" by (subst setsum.neutral, auto)
  finally show ?thesis by simp
qed

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

lemma degree_listsum_le: "(\<And> p . p \<in> set ps \<Longrightarrow> degree p \<le> n)
  \<Longrightarrow> degree (listsum ps) \<le> n"
proof (induct ps)
  case (Cons p ps)
  hence "degree (listsum ps) \<le> n" "degree p \<le> n" by auto
  thus ?case unfolding listsum.Cons by (metis degree_add_le)
qed simp

lemma degree_listprod_le: "degree (listprod ps) \<le> listsum (map degree ps)"
proof (induct ps)
  case (Cons p ps)
  show ?case unfolding listprod.Cons
    by (rule order.trans[OF degree_mult_le], insert Cons, auto)
qed simp

lemma smult_setsum: "smult (\<Sum>i \<in> S. f i) p = (\<Sum>i \<in> S. smult (f i) p)"
  by (induct S rule: infinite_finite_induct, auto simp: smult_add_left)


lemma range_coeff: "range (coeff p) = insert 0 (set (coeffs p))" 
  by (metis nth_default_coeffs_eq range_nth_default)

lemma smult_power: "(smult a p) ^ n = smult (a ^ n) (p ^ n)"
  by (induct n, auto simp: field_simps)

lemma poly_listsum: "poly (listsum ps) x = listsum (map (\<lambda> p. poly p x) ps)"
  by (induct ps, auto)

lemma poly_listprod: "poly (listprod ps) x = listprod (map (\<lambda> p. poly p x) ps)"
  by (induct ps, auto)

lemma listsum_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> listsum xs = 0"
  by (induct xs, auto)

lemma listprod_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 1) \<Longrightarrow> listprod xs = 1"
  by (induct xs, auto)

lemma (in comm_monoid_mult) listprod_map_remove1:
  "x \<in> set xs \<Longrightarrow> listprod (map f xs) = f x * listprod (map f (remove1 x xs))"
  by (induct xs) (auto simp add: ac_simps)

lemma poly_as_setsum:
  fixes p :: "'a::comm_semiring_1 poly"
  shows "poly p x = (\<Sum>i\<le>degree p. x ^ i * coeff p i)"
  unfolding poly_altdef by (simp add: ac_simps)

lemma poly_setprod_0: "finite ps \<Longrightarrow> poly (setprod f ps) x = (0 :: 'a :: field) \<longleftrightarrow> (\<exists> p \<in> ps. poly (f p) x = 0)"
  by (induct ps rule: finite_induct, auto)

lemma coeff_monom_mult:
  shows "coeff (monom a d * p) i =
    (if d \<le> i then a * coeff p (i-d) else 0)" (is "?l = ?r")
proof (cases "d \<le> i")
  case False thus ?thesis unfolding coeff_mult by simp
  next case True
    let ?f = "\<lambda>j. coeff (monom a d) j * coeff p (i - j)"
    have "\<And>j. j \<in> {0..i} - {d} \<Longrightarrow> ?f j = 0" by auto
    hence "0 = (\<Sum>j \<in> {0..i} - {d}. ?f j)" by auto
    also have "... + ?f d = (\<Sum>j \<in> insert d ({0..i} - {d}). ?f j)"
      by(subst setsum.insert, auto)
    also have "... = (\<Sum>j \<in> {0..i}. ?f j)" by (subst insert_Diff, insert True, auto)
    also have "... = (\<Sum>j\<le>i. ?f j)" by (rule setsum.cong, auto)
    also have "... = ?l" unfolding coeff_mult ..
    finally show ?thesis using True by auto
qed

lemma poly_eqI2:
  assumes "degree p = degree q" and "\<And>i. i \<le> degree p \<Longrightarrow> coeff p i = coeff q i"
  shows "p = q"
  apply(rule poly_eqI) by (metis assms le_degree)

text {*
  A nicer condition for 'a @{type poly} to be @{class ring_char_0} over @{class linordered_field}
*}

instance poly :: ("{ring_char_0,idom}") ring_char_0
proof
  show "inj (of_nat :: nat \<Rightarrow> 'a poly)" unfolding inj_on_def
  proof (intro impI ballI)
    fix x y :: nat
    assume "of_nat x = (of_nat y :: 'a poly)"
    thus "x = y" unfolding of_nat_poly by auto
  qed
qed

text {* A nice extension rule for polynomials. *}
lemma poly_ext[intro]:
  fixes p q :: "'a :: {ring_char_0, idom} poly"
  assumes "\<And>x. poly p x = poly q x" shows "p = q"
  unfolding poly_eq_poly_eq_iff[symmetric]
  using assms by (rule ext)

text {* Copied from non-negative variants. *}
lemma coeff_linear_power_neg[simp]:
  fixes a :: "'a::comm_ring_1"
  shows "coeff ([:a, -1:] ^ n) n = (-1)^n"
apply (induct n, simp_all)
apply (subst coeff_eq_0)
apply (auto intro: le_less_trans degree_power_le)
done

lemma degree_linear_power_neg[simp]:
  fixes a :: "'a::{idom,comm_ring_1}"
  shows "degree ([:a, -1:] ^ n) = n"
apply (rule order_antisym)
apply (rule ord_le_eq_trans [OF degree_power_le], simp)
apply (rule le_degree)
unfolding coeff_linear_power_neg
apply (auto)
done


subsection \<open>Polynomial Composition\<close>

lemmas [simp] = pcompose_pCons

lemma pcompose_eq_0: fixes q :: "'a :: idom poly"
  assumes q: "degree q \<noteq> 0"
  shows "p \<circ>\<^sub>p q = 0 \<longleftrightarrow> p = 0"
proof (induct p)
  case 0
  show ?case by auto
next
  case (pCons a p)
  have id: "(pCons a p) \<circ>\<^sub>p q = [:a:] + q * (p \<circ>\<^sub>p q)" by simp
  show ?case 
  proof (cases "p = 0")
    case True
    show ?thesis unfolding id unfolding True by simp
  next
    case False
    with pCons(2) have "p \<circ>\<^sub>p q \<noteq> 0" by auto
    from degree_mult_eq[OF _ this, of q] q have "degree (q * (p \<circ>\<^sub>p q)) \<noteq> 0" by force
    hence deg: "degree ([:a:] + q * (p \<circ>\<^sub>p q)) \<noteq> 0"
      by (subst degree_add_eq_right, auto)
    show ?thesis unfolding id using False deg by auto
  qed
qed

declare degree_pcompose[simp]

subsection \<open>Monic Polynomials\<close>

abbreviation monic where "monic p \<equiv> coeff p (degree p) = 1"

lemma lcoeff_monic_mult: assumes monic: "monic (p :: 'a :: comm_semiring_1 poly)"
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

lemma degree_monic_mult: assumes monic: "monic (p :: 'a :: comm_semiring_1 poly)"
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
  and monic: "(\<And> a . a \<in> S \<Longrightarrow> monic (f a))"
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

lemma degree_linear_factors: "degree (\<Prod> a \<leftarrow> as. [: f a, 1:]) = length as"
proof (induct as)
  case (Cons b as) note IH = this
  have id: "(\<Prod>a\<leftarrow>b # as. [:f a, 1:]) = [:f b,1 :] * (\<Prod>a\<leftarrow>as. [:f a, 1:])" by simp
  show ?case unfolding id
    by (subst degree_monic_mult, insert IH, auto)
qed simp

lemma monic_mult:
  fixes p q :: "'a :: idom poly"
  assumes "monic p" "monic q"
  shows "monic (p * q)"
proof -
  from assms have nz: "p \<noteq> 0" "q \<noteq> 0" by auto
  show ?thesis unfolding degree_mult_eq[OF nz] coeff_mult_degree_sum
    using assms by simp
qed

lemma monic_factor:
  fixes p q :: "'a :: idom poly"
  assumes "monic (p * q)" "monic p"
  shows "monic q"
proof -
  from assms have nz: "p \<noteq> 0" "q \<noteq> 0" by auto
  from assms[unfolded degree_mult_eq[OF nz] coeff_mult_degree_sum `monic p`]
  show ?thesis by simp
qed

lemma monic_setprod:
  fixes f :: "'a \<Rightarrow> 'b :: idom poly"
  assumes "\<And> a. a \<in> as \<Longrightarrow> monic (f a)"
  shows "monic (setprod f as)" using assms
proof (induct as rule: infinite_finite_induct)
  case (insert a as)
  hence id: "setprod f (insert a as) = f a * setprod f as" 
    and *: "monic (f a)" "monic (setprod f as)" by auto
  show ?case unfolding id by (rule monic_mult[OF *])
qed auto

lemma monic_listprod:
  fixes as :: "'a :: idom poly list"
  assumes "\<And> a. a \<in> set as \<Longrightarrow> monic a"
  shows "monic (listprod as)" using assms
  by (induct as, auto intro: monic_mult)

lemma monic_power:
  assumes "monic (p :: 'a :: idom poly)"
  shows "monic (p ^ n)"
  by (induct n, insert assms, auto intro: monic_mult)

lemma monic_listprod_pow: "monic (\<Prod>(x::'a::idom, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
proof (rule monic_listprod, goal_cases)
  case (1 a)
  then obtain x i where a: "a = [:-x, 1:]^Suc i" by force
  show "monic a" unfolding a
    by (rule monic_power, auto)
qed

lemma monic_degree_0: "monic p \<Longrightarrow> (degree p = 0) = (p = 1)"
  using le_degree poly_eq_iff by force

subsection \<open>Roots\<close>

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
  have [simp]: "r + k = 0 \<Longrightarrow> k = - r" by (simp add: minus_unique)
  show ?one unfolding poly_mult by auto
  show ?two unfolding poly_mult by auto
  show ?three by auto
qed

lemma poly_root_constant: "c \<noteq> 0 \<Longrightarrow> (poly (p * [:c:]) (k :: 'a :: idom) = 0) = (poly p k = 0)"
  unfolding poly_mult by auto


lemma poly_linear_exp_linear_factors_rev: 
  "([:b,1:])^(length (filter (op = b) as)) dvd (\<Prod> (a :: 'a :: comm_ring_1) \<leftarrow> as. [: a, 1:])"
proof (induct as)
  case (Cons a as)
  let ?ls = "length (filter (op = b) (a # as))"
  let ?l = "length (filter (op = b) as)"
  have prod: "(\<Prod> a \<leftarrow> Cons a as. [: a, 1:]) = [: a, 1 :] * (\<Prod> a \<leftarrow> as. [: a, 1:])" by simp
  show ?case
  proof (cases "a = b")
    case False
    hence len: "?ls = ?l" by simp
    show ?thesis unfolding prod len using Cons by (rule dvd_mult)
  next
    case True
    hence len: "[: b, 1 :] ^ ?ls = [: a, 1 :] * [: b, 1 :] ^ ?l" by simp
    show ?thesis unfolding prod len using Cons using dvd_refl mult_dvd_mono by blast
  qed
qed simp

lemma order_max: assumes dvd: "[: -a, 1 :] ^ k dvd p" and p: "p \<noteq> 0"
  shows "k \<le> order a p"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "\<exists> j. k = Suc (order a p + j)" by arith
  then obtain j where k: "k = Suc (order a p + j)" by auto
  have "[: -a, 1 :] ^ Suc (order a p) dvd p"
    by (rule power_le_dvd[OF dvd[unfolded k]], simp)
  with order_2[OF p, of a] show False by blast
qed

lemma coprime_poly_factor: 
  assumes cop: "coprime (p :: 'a :: field poly) (q * r)" and r: "r \<noteq> 0"
  shows "coprime p q"
proof (cases "q = 0")
  case True
  with assms show ?thesis by auto
next
  case False note q = this
  with r have qr0: "q * r \<noteq> 0" by auto
  let ?g = "gcd p (q * r)"
  let ?g' = "gcd p q"
  have d0: "degree ?g = 0" unfolding cop by simp
  have "?g' dvd ?g" by simp
  from dvd_imp_degree_le[OF this] poly_gcd_monic[of p "q * r"] qr0
  have "degree ?g' \<le> degree ?g" by auto
  with d0 have "degree ?g' = 0" by auto
  with poly_gcd_monic[of p q] q 
  show ?thesis using monic_degree_0[of ?g'] by auto
qed



subsection \<open>Divisibility\<close>

instance poly :: (field) ring_gcd
proof 
  fix a b :: "'a poly"
  show "normalize (gcd a b) = gcd a b" by (simp add: normalize_poly_def poly_gcd_monic)
  show "lcm a b = normalize (a * b) div gcd a b" 
  proof (cases "a * b = 0") 
    case False
    show ?thesis unfolding lcm_poly_def normalize_poly_def
    by (subst div_smult_right, insert False, auto simp: div_smult_left)
       (metis coeff_degree_mult divide_divide_eq_left divide_inverse_commute inverse_eq_divide)
  next
    case True
    thus ?thesis by (metis div_0 lcm_poly_def normalize_0)
  qed
qed auto

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

lemma const_poly_dvd: "([:a:] dvd [:b:]) = (a dvd b)"
proof
  assume "a dvd b"
  then obtain c where "b = a * c" unfolding dvd_def by auto
  hence "[:b:] = [:a:] * [: c:]" by (auto simp: ac_simps)
  thus "[:a:] dvd [:b:]" unfolding dvd_def by blast
next
  assume "[:a:] dvd [:b:]"
  then obtain pc where "[:b:] =  [:a:] * pc" unfolding dvd_def by blast
  from arg_cong[OF this, of "\<lambda> p. coeff p 0", unfolded coeff_mult]
  have "b = a * coeff pc 0" by auto
  thus "a dvd b" unfolding dvd_def by blast
qed

lemma const_poly_dvd_1: "([:a:] dvd 1) = (a dvd 1)"
  unfolding one_poly_def const_poly_dvd ..

lemma poly_dvd_1: "(p dvd (1 :: 'a :: idom poly)) = (degree p = 0 \<and> coeff p 0 dvd 1)"
proof (cases "degree p = 0")
  case False
  with divides_degree[of p 1] show ?thesis by auto
next
  case True
  from degree0_coeffs[OF this] obtain a where p: "p = [:a:]" by auto
  show ?thesis unfolding p const_poly_dvd_1 by auto
qed

definition irreducible :: "'a :: idom poly \<Rightarrow> bool" where
  "irreducible p = (degree p \<noteq> 0 \<and> (\<forall> q. degree q \<noteq> 0 \<longrightarrow> degree q < degree p \<longrightarrow> \<not> q dvd p))"

lemma irreducibleI: assumes 
  "degree p \<noteq> 0" "\<And> q. degree q \<noteq> 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> \<not> q dvd p"
  shows "irreducible p" using assms unfolding irreducible_def by auto

lemma irreducibleI2: assumes 
  deg: "degree p \<noteq> 0" and ndvd: "\<And> q. degree q \<ge> 1 \<Longrightarrow> degree q \<le> degree p div 2 \<Longrightarrow> \<not> q dvd p"
  shows "irreducible p"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this[unfolded irreducible_def] deg obtain q where dq: "degree q \<noteq> 0" "degree q < degree p"
    and dvd: "q dvd p" by auto
  from dvd obtain r where p: "p = q * r" unfolding dvd_def by auto
  from deg have p0: "p \<noteq> 0" by auto
  with p have "q \<noteq> 0" "r \<noteq> 0" by auto
  from degree_mult_eq[OF this] p have dp: "degree p = degree q + degree r" by simp
  show False
  proof (cases "degree q \<le> degree p div 2")
    case True
    from ndvd[OF _ True] dq dvd show False by auto
  next
    case False
    with dp have dr: "degree r \<le> degree p div 2" by auto
    from p have dvd: "r dvd p" by auto
    from ndvd[OF _ dr] dvd dp dq show False by auto
  qed
qed
    

lemma irreducibleD: assumes "irreducible p"
  shows "degree p \<noteq> 0" "\<And> q. degree q \<noteq> 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> \<not> q dvd p"
  using assms unfolding irreducible_def by auto

lemma irreducible_factor: assumes
  "degree p \<noteq> 0" 
  shows "\<exists> q r. irreducible q \<and> p = q * r \<and> degree r < degree p" using assms
proof (induct "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "irreducible p")
    case False
    with less(2) obtain q where q: "degree q < degree p" "degree q \<noteq> 0"  and dvd: "q dvd p"
      unfolding irreducible_def by auto
    from dvd obtain r where p: "p = q * r" unfolding dvd_def by auto
    from less(1)[OF q] obtain s t where IH: "irreducible s" "q = s * t" by auto
    from p have p: "p = s * (t * r)" unfolding IH by (simp add: ac_simps)
    from less(2) have "p \<noteq> 0" by auto
    hence "degree p = degree s + (degree (t * r))" unfolding p 
      by (subst degree_mult_eq, insert p, auto)
    with irreducibleD[OF IH(1)] have "degree p > degree (t * r)" by auto
    with p IH show ?thesis by auto
  next
    case True
    show ?thesis
      by (rule exI[of _ p], rule exI[of _ 1], insert True less(2), auto)
  qed 
qed

lemma irreducible_smultI: 
  "irreducible (smult c p) \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> irreducible p" 
  using dvd_smult[of _ p c] unfolding irreducible_def by auto

lemma irreducible_smult[simp]: fixes c :: "'a :: field" assumes "c \<noteq> 0"
  shows "irreducible (smult c p) = irreducible p" using `c \<noteq> 0`
  unfolding irreducible_def by (auto simp: dvd_smult_iff[OF `c \<noteq> 0`])

lemma irreducible_monic_factor: fixes p :: "'a :: field poly" 
  assumes "degree p \<noteq> 0" 
  shows "\<exists> q r. irreducible q \<and> p = q * r \<and> monic q"
proof -
  from irreducible_factor[OF assms]
  obtain q r where q: "irreducible q" and p: "p = q * r" by auto
  def c \<equiv> "coeff q (degree q)"
  from q have c: "c \<noteq> 0" unfolding c_def irreducible_def by auto
  show ?thesis
    by (rule exI[of _ "smult (1/c) q"], rule exI[of _ "smult c r"], unfold p,
    insert q c, auto simp: c_def)
qed

lemma monic_irreducible_factorization: fixes p :: "'a :: field poly" 
  shows "monic p \<Longrightarrow> 
  \<exists> as f. finite as \<and> p = setprod (\<lambda> a. a ^ Suc (f a)) as \<and> as \<subseteq> {q. irreducible q \<and> monic q}"
proof (induct "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "degree p = 0")
    case True
    with less(2) have "p = 1" by (simp add: coeff_eq_0 poly_eq_iff)
    thus ?thesis by (intro exI[of _ "{}"], auto)
  next
    case False
    from irreducible_factor[OF this] obtain q r where p: "p = q * r"
      and q: "irreducible q" and deg: "degree r < degree p" by auto
    hence q0: "q \<noteq> 0" unfolding irreducible_def by auto
    def c \<equiv> "coeff q (degree q)"
    let ?q = "smult (1/c) q"
    let ?r = "smult c r"
    from q0 have c: "c \<noteq> 0" "1 / c \<noteq> 0" unfolding c_def by auto
    hence p: "p = ?q * ?r" unfolding p by auto
    have deg: "degree ?r < degree p" using c deg by auto
    let ?Q = "{q. irreducible q \<and> monic (q :: 'a poly)}"
    have mon: "monic ?q" unfolding c_def using q0 by auto
    from monic_factor[OF `monic p`[unfolded p] this] have "monic ?r" .
    from less(1)[OF deg this] obtain f as
      where as: "finite as" "?r = (\<Prod> a \<in>as. a ^ Suc (f a))"
        "as \<subseteq> ?Q" by blast
    from q c have irred: "irreducible ?q" by simp
    show ?thesis
    proof (cases "?q \<in> as")
      case False
      let ?as = "insert ?q as"
      let ?f = "\<lambda> a. if a = ?q then 0 else f a"
      have "p = ?q * (\<Prod> a \<in>as. a ^ Suc (f a))" unfolding p as by simp
      also have "(\<Prod> a \<in>as. a ^ Suc (f a)) = (\<Prod> a \<in>as. a ^ Suc (?f a))"
        by (rule setprod.cong, insert False, auto)
      also have "?q * \<dots> = (\<Prod> a \<in> ?as. a ^ Suc (?f a))"
        by (subst setprod.insert, insert as False, auto)
      finally have p: "p = (\<Prod> a \<in> ?as. a ^ Suc (?f a))" .
      from as(1) have fin: "finite ?as" by auto
      from as mon irred have Q: "?as \<subseteq> ?Q" by auto
      from fin p Q show ?thesis 
        by(intro exI[of _ ?as] exI[of _ ?f], auto)
    next
      case True
      let ?f = "\<lambda> a. if a = ?q then Suc (f a) else f a"
      have "p = ?q * (\<Prod> a \<in>as. a ^ Suc (f a))" unfolding p as by simp
      also have "(\<Prod> a \<in>as. a ^ Suc (f a)) = ?q ^ Suc (f ?q) * (\<Prod> a \<in>(as - {?q}). a ^ Suc (f a))"
        by (subst setprod.remove[OF _ True], insert as, auto)
      also have "(\<Prod> a \<in>(as - {?q}). a ^ Suc (f a)) = (\<Prod> a \<in>(as - {?q}). a ^ Suc (?f a))"
        by (rule setprod.cong, auto)
      also have "?q * (?q ^ Suc (f ?q) * \<dots> ) = ?q ^ Suc (?f ?q) * \<dots>"
        by (simp add: ac_simps)
      also have "\<dots> = (\<Prod> a \<in> as. a ^ Suc (?f a))"
        by (subst setprod.remove[OF _ True], insert as, auto)
      finally have "p = (\<Prod> a \<in> as. a ^ Suc (?f a))" .
      with as show ?thesis 
        by (intro exI[of _ as] exI[of _ ?f], auto)
    qed
  qed
qed 

lemma linear_irreducible: assumes "degree p = 1"
  shows "irreducible p"
  by (rule irreducibleI, insert assms, auto)

lemma irreducible_dvd_smult:
  assumes "degree p \<noteq> 0" "irreducible q" "p dvd q"
  shows "\<exists> c. c \<noteq> 0 \<and> q = smult c p"
proof -
  from assms have "\<not> degree p < degree q" 
  and nz: "p \<noteq> 0" "q \<noteq> 0" unfolding irreducible_def by auto
  hence deg: "degree p \<ge> degree q" by auto
  from `p dvd q` obtain k where q: "q = k * p" unfolding dvd_def by (auto simp: ac_simps)
  with nz have "k \<noteq> 0" by auto
  from deg[unfolded q degree_mult_eq[OF `k \<noteq> 0` `p \<noteq> 0` ]] have "degree k = 0" 
    unfolding q by auto 
  then obtain c where k: "k = [: c :]" by (metis degree_0_id)
  with `k \<noteq> 0` have "c \<noteq> 0" by auto
  have "q = smult c p" unfolding q k by simp
  with `c \<noteq> 0` show ?thesis by auto
qed

subsection \<open>Map over Polynomial Coefficients\<close>

definition map_poly :: "('a::zero \<Rightarrow> 'b::zero) \<Rightarrow> 'a poly \<Rightarrow> 'b poly"
  where "map_poly f p = fold_coeffs (\<lambda>c. pCons (f c)) p 0"

lemma map_poly_simps:
  shows "map_poly f (pCons c p) =
    (if c = 0 \<and> p = 0 then 0 else pCons (f c) (map_poly f p))"
proof (cases "c = 0")
  case True note c0 = this show ?thesis
    proof (cases "p = 0")
      case True thus ?thesis using c0 unfolding map_poly_def by simp
      next case False thus ?thesis
        unfolding map_poly_def
        apply(subst fold_coeffs_pCons_not_0_0_eq) using assms by auto
    qed
  next case False thus ?thesis
    unfolding map_poly_def
    apply (subst fold_coeffs_pCons_coeff_not_0_eq) by auto
qed

lemma map_poly_pCons[simp]:
  assumes "c \<noteq> 0 \<or> p \<noteq> 0"
  shows "map_poly f (pCons c p) = pCons (f c) (map_poly f p)"
  unfolding map_poly_simps using assms by auto

lemma map_poly_simp_0[simp]:
  shows "map_poly f 0 = 0" unfolding map_poly_def by simp

lemma map_poly_id[simp]: "map_poly (id::'a::zero \<Rightarrow> 'a) = id"
proof(rule ext)
  fix p::"'a poly" show "map_poly id p = id p" by (induct p; simp)
qed

lemma map_poly_map_poly:
  assumes f0: "f 0 = 0"
  shows "map_poly f (map_poly g p) = map_poly (f \<circ> g) p"
proof (induct p)
  case (pCons a p) show ?case
    proof(cases "g a \<noteq> 0 \<or> map_poly g p \<noteq> 0")
      case True show ?thesis
        unfolding map_poly_pCons[OF pCons(1)]
        unfolding map_poly_pCons[OF True]
        unfolding pCons(2)
        by simp
      next case False
        hence [simp]: "g a = 0" "map_poly g p = 0" by simp+
        show ?thesis
          unfolding map_poly_pCons[OF pCons(1)]
          unfolding pCons(2)[symmetric]
          by (simp add: f0)
    qed
qed simp

lemma map_poly_zero:
  assumes f: "\<forall>c. f c = 0 \<longrightarrow> c = 0"
  shows [simp]: "map_poly f p = 0 \<longleftrightarrow> p = 0"
  by (induct p; auto simp: map_poly_simps f)

lemma coeff_map_poly:
  assumes "f 0 = 0"
  shows "coeff (map_poly f p) i = f (coeff p i)"
proof(induct p arbitrary:i)
  case 0 show ?case using assms by simp
  next case (pCons c p)
    hence cp0: "\<not> (c = 0 \<and> p = 0)" by auto
    show ?case
    proof(cases "i = 0")
      case True thus ?thesis
        unfolding map_poly_simps using assms by simp
      next case False
        then obtain j where j: "i = Suc j" using not0_implies_Suc by blast
        show ?thesis
        unfolding map_poly_simps j
        using pCons by(simp add: cp0)
    qed
qed

lemma map_poly_monom:
  assumes "f 0 = 0" shows "map_poly f (monom a i) = monom (f a) i"
proof(induct i)
  case 0 show ?case
    unfolding monom_0 unfolding map_poly_simps using assms by simp
  next case (Suc i) show ?case
    unfolding monom_Suc unfolding map_poly_simps unfolding Suc
    using assms by simp
qed

lemma map_poly_ext:
  assumes "\<And>a. a \<in> set (coeffs p) \<Longrightarrow> f a = g a"
  shows "map_poly f p = map_poly g p"
  using assms by(induct p, auto)

lemma map_poly_add:
  assumes h0: "h 0 = 0"
      and h_add: "\<forall>p q. h (p + q) = h p + h q"
  shows "map_poly h (p + q) = map_poly h p + map_poly h q"
proof (induct p arbitrary: q)
  case (pCons a p) note pIH = this
    show ?case
    proof(induct "q")
      case (pCons b q) note qIH = this
        show ?case
          unfolding map_poly_pCons[OF qIH(1)]
          unfolding map_poly_pCons[OF pIH(1)]
          unfolding add_pCons
          unfolding pIH(2)[symmetric]
          unfolding h_add[rule_format,symmetric]
          unfolding map_poly_simps using h0 by auto
    qed auto
qed auto

subsection \<open>Morphismic properties of @{term "pCons 0"}\<close>

lemma monom_pCons_0_monom:
  "monom (pCons 0 (monom a n)) d = map_poly (pCons 0) (monom (monom a n) d)"
  apply (induct d)
  unfolding monom_0 unfolding map_poly_simps apply simp
  unfolding monom_Suc map_poly_simps by auto

lemma pCons_0_add: "pCons 0 (p + q) = pCons 0 p + pCons 0 q" by auto

lemma setsum_pCons_0_commute:
  "setsum (\<lambda>i. pCons 0 (f i)) S = pCons 0 (setsum f S)"
  by(induct S rule: infinite_finite_induct;simp)

lemma pCons_0_as_mult:
  fixes p:: "'a :: comm_semiring_1 poly"
  shows "pCons 0 p = [:0,1:] * p" by auto



subsection \<open>Misc\<close>

fun expand_powers :: "(nat \<times> 'a)list \<Rightarrow> 'a list" where
  "expand_powers [] = []"
| "expand_powers ((Suc n, a) # ps) = a # expand_powers ((n,a) # ps)"
| "expand_powers ((0,a) # ps) = expand_powers ps"

lemma expand_powers: fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  shows "(\<Prod> (n,a) \<leftarrow> n_as. f a ^ n) = (\<Prod> a \<leftarrow> expand_powers n_as. f a)"
  by (rule sym, induct n_as rule: expand_powers.induct, auto)

lemma poly_smult_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (smult a p) x = 0) = (a = 0 \<or> poly p x = 0)"
  by simp

lemma poly_listprod_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (listprod ps) x = 0) = (\<exists> p \<in> set ps. poly p x = 0)"
  by (induct ps, auto)

lemma poly_mult_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (p * q) x = 0) = (poly p x = 0 \<or> poly q x = 0)"
  by simp

lemma poly_power_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (p^n) x = 0) = (n \<noteq> 0 \<and> poly p x = 0)"
  by (cases n, auto)


lemma setsum_monom_0_iff: assumes fin: "finite S"
  and g: "\<And> i j. g i = g j \<Longrightarrow> i = j"
  shows "setsum (\<lambda> i. monom (f i) (g i)) S = 0 \<longleftrightarrow> (\<forall> i \<in> S. f i = 0)" (is "?l = ?r")
proof -
  {
    assume "\<not> ?r"
    then obtain i where i: "i \<in> S" and fi: "f i \<noteq> 0" by auto
    let ?g = "\<lambda> i. monom (f i) (g i)"
    have "coeff (setsum ?g S) (g i) = f i + setsum (\<lambda> j. coeff (?g j) (g i)) (S - {i})"
      by (unfold setsum.remove[OF fin i], simp add: coeff_setsum)
    also have "setsum (\<lambda> j. coeff (?g j) (g i)) (S - {i}) = 0"
      by (rule setsum.neutral, insert g, auto)
    finally have "coeff (setsum ?g S) (g i) \<noteq> 0" using fi by auto
    hence "\<not> ?l" by auto
  }
  thus ?thesis by auto
qed

lemma degree_listprod_eq: assumes "\<And> p. p \<in> set ps \<Longrightarrow> (p :: 'a :: idom poly) \<noteq> 0"
  shows "degree (listprod ps) = listsum (map degree ps)" using assms
proof (induct ps)
  case (Cons p ps)
  show ?case unfolding listprod.Cons
    by (subst degree_mult_eq, insert Cons, auto simp: listprod_zero_iff)
qed simp

lemma degree_power_eq: assumes p: "p \<noteq> 0"
  shows "degree (p ^ n) = degree (p :: 'a :: idom poly) * n"
proof (induct n)
  case (Suc n)
  from p have pn: "p ^ n \<noteq> 0" by auto
  show ?case using degree_mult_eq[OF p pn] Suc by auto
qed simp


end
