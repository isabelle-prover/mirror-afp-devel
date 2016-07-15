(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Polynomial Divisibility\<close>

text \<open>We make a connection to HOL/Algebra/Divisibility to get the following two lemmas.

If $p$ is an irreducible polynomial and $p$ divides $q \cdot r$, then $p$ divides one of $q$ and $r$.

If the polynomial $k$ divides both $p \cdot q$ and $p \cdot r$ then $k$ divides $p \cdot gcd(q,r)$.

The connection was made to show that polynomials over fields are a unique factorization domain,
and in HOL/Algebra/Divisibility there is an alternative characterization unique factorization domain,
which eased the proof.\<close>


theory Polynomial_Divisibility
imports
  "../Polynomial_Interpolation/Missing_Polynomial"
  Unique_Factorization_Domain
begin

context
  fixes ty :: "'a :: {field,euclidean_ring_gcd} itself"
begin

abbreviation "poly_monoid \<equiv> mk_monoid::'a poly monoid" 

private lemma factor_id: "((x = 0 \<longleftrightarrow> y = 0) \<and> x dvd y)
   = ((x = 0 \<longleftrightarrow> y = 0) \<and> (\<exists> z. z \<noteq> 0 \<and> x * z = (y :: 'a poly)))" unfolding dvd_def
  by (auto, intro exI[of _ 1], auto)


interpretation poly_cancel: comm_monoid_cancel poly_monoid
  rewrites factorid: "(factor :: 'a poly \<Rightarrow> 'a poly \<Rightarrow> bool) = (\<lambda> x y. ((x = 0 \<longleftrightarrow> y = 0) \<and> x dvd y))" 
  unfolding factor_id[symmetric]
  by (rule comm_monoid_cancel_idom, intro ext, subst factor_idom, auto)

declare poly_cancel.divides_refl [simp del]

qualified lemma factorid_carrier: assumes "(a::'a poly) \<noteq> 0" "b \<noteq> 0"
  shows "factor a b = (a dvd b)"
  unfolding factorid using assms by auto

qualified lemma poly_Units: "Units poly_monoid = {p. p \<noteq> 0 \<and> degree p = 0}"
proof -
  {
    fix p q :: "'a poly"
    assume nz: "p \<noteq> 0" "q \<noteq> 0" and pq: "p * q = 1"
    from degree_mult_eq[OF nz, unfolded pq] have "degree p = 0" by auto
  }
  moreover
  {
    fix p :: "'a poly"
    assume "p \<noteq> 0" "degree p = 0"
    then obtain c where p: "p = [: c :]" by (metis degree_0_id)
    with `p \<noteq> 0` have "c \<noteq> 0" by auto
    hence "\<exists>q. q \<noteq> 0 \<and> q * p = 1 \<and> p * q = 1"
      by (intro exI[of _ "[: 1/c :]"], auto simp: p one_poly_def)
  }
  ultimately show ?thesis
  unfolding Units_def Bex_def by auto
qed

private lemma poly_gcd: "gcd_condition_monoid poly_monoid"
proof (unfold_locales, unfold mk_monoid_simps)
  fix a b :: "'a poly"
  let ?g = "gcd a b"
  assume a: "a \<noteq> 0" and b: "b \<noteq> 0"
  hence g: "?g \<noteq> 0" by auto
  note f = factorid_carrier
  show "\<exists>c. c \<noteq> 0 \<and> c gcdof\<^bsub>local.poly_monoid\<^esub> a b"
  proof (rule exI[of _ ?g], unfold isgcd_def f[OF g a] f[OF g b] Ball_def mk_monoid_simps, 
    intro conjI allI impI; (elim conjE)?)
    fix x :: "'a poly"
    assume x: "x \<noteq> 0" and div: "x divides\<^bsub>poly_monoid\<^esub> a"
      "x divides\<^bsub>poly_monoid\<^esub> b" 
    hence "x dvd a" "x dvd b" unfolding f[OF x b] f[OF x a] by auto
    hence "x dvd (gcd a b)" by (rule gcd_greatest)
    thus "x divides\<^bsub>poly_monoid\<^esub> gcd a b" unfolding f[OF x g] .
  qed (insert a b, auto)
qed

private lemma poly_div_chain: "divisor_chain_condition_monoid poly_monoid" 
proof (unfold_locales, unfold mk_monoid_simps, rule wf_subset[OF wf_inv_image[OF wf_less]])
  let ?f = "\<lambda> x :: 'a poly. degree x"
  {
    fix x y :: "'a poly"
    assume x: "x \<noteq> 0" and y: "y \<noteq> 0" and fac: "properfactor x y"
    from fac[unfolded properfactor_def factorid_carrier[OF x y] factorid_carrier[OF y x]]
    have xy: "x dvd y" and yx: "\<not> y dvd x" by auto
    from xy obtain z where xy: "y = x * z" unfolding dvd_def by auto
    with y have z: "z \<noteq> 0" by auto
    from degree_mult_eq[OF x z] have deg: "degree y = degree x + degree z" unfolding xy .
    {
      assume "degree z = 0"
      then obtain c where zc: "z = [: c :]" by (metis degree_0_id)
      with z have "c \<noteq> 0" by auto
      have "y = smult c x" unfolding xy zc by simp
      with `c \<noteq> 0` have "x = y * [: 1/c :]" by auto
      with yx have False unfolding dvd_def by blast
    }
    with deg have "?f x < ?f y" by auto
  }
  thus "{(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> properfactor x y} \<subseteq> inv_image {(x, y). x < y} ?f"
    by auto
qed

lemma factorial_monoid_field_poly: "factorial_monoid poly_monoid"
  unfolding factorial_condition_two[symmetric]
  using poly_div_chain poly_gcd by blast  

qualified lemma irreducible_connect:
  assumes irr: "Missing_Polynomial.irreducible (p::'a poly)" shows "irreducible p"
proof -
  from irr have deg: "degree p \<noteq> 0" and p: "p \<noteq> 0"
    unfolding Missing_Polynomial.irreducible_def by auto
  hence noU: "p \<notin> Units poly_monoid" unfolding poly_Units by auto
  show ?thesis unfolding Divisibility.irreducible_def mk_monoid_simps 
  proof (rule conjI[OF noU], intro ballI impI, unfold poly_Units mk_monoid_simps)
    fix q
    assume q: "q \<noteq> 0" and fac: "properfactor q p"
    from this[unfolded properfactor_def factorid_carrier[OF p q] factorid_carrier[OF q p]]
    have dvd: "q dvd p" and ndvd: "\<not> p dvd q" by auto
    {
      assume "degree q \<noteq> 0"
      from irreducible_dvd_smult[OF this irr dvd] ndvd obtain c where "c \<noteq> 0" and "p = smult c q" by auto
      hence q: "q = p * [: 1/c :]" by auto
      with ndvd have False unfolding dvd_def by blast
    }
    thus "q \<in> {p. p \<noteq> 0 \<and> degree p = 0}" using q by auto
  qed
qed

lemma irreducible_dvd_mult: assumes irr: "Missing_Polynomial.irreducible (p :: 'a poly)"
  and dvd: "p dvd q * r"
  shows "p dvd q \<or> p dvd r"
proof (cases "q * r = 0")
  case False
  hence q: "q \<noteq> 0" and r: "r \<noteq> 0" by auto
  from irr have p: "p \<noteq> 0" unfolding Missing_Polynomial.irreducible_def by auto
  from factorial_monoid.irreducible_is_prime[OF factorial_monoid_field_poly irreducible_connect[OF irr],
    unfolded Divisibility.prime_def Ball_def mk_monoid_simps poly_Units, OF p,
    THEN conjunct2, rule_format, OF q r] dvd show ?thesis
    using p q r by (simp add: factorid_carrier)
qed auto
end

lemma dvd_gcd_mult: fixes p :: "'a :: semiring_gcd"
  assumes dvd: "k dvd p * q" "k dvd p * r"
  shows "k dvd p * gcd q r"
  by (rule dvd_trans, rule gcd_greatest[OF dvd])
     (auto intro!: mult_dvd_mono simp: gcd_mult_left)

lemma poly_gcd_monic_factor:
  "monic p \<Longrightarrow>  gcd (p * q) (p * r) = p * gcd q r"
  by (rule gcdI [symmetric]) (simp_all add: normalize_mult normalize_monic dvd_gcd_mult)


hide_const (open) Divisibility.irreducible
hide_fact (open) Divisibility.irreducibleI
hide_fact (open) Divisibility.irreducibleD
hide_fact (open) Divisibility.irreducible_def

hide_const (open) irreducible

context
  assumes "SORT_CONSTRAINT('a :: {field,euclidean_ring_gcd})"
begin

lemma irreducible_dvd_pow: fixes p :: "'a poly" 
  assumes irr: "irreducible p"
  shows "p dvd q ^ Suc n \<Longrightarrow> p dvd q"
proof (induct n)
  case (Suc n)
  have "q ^ Suc (Suc n) = q * q ^ Suc n" by simp
  from irreducible_dvd_mult[OF irr Suc(2)[unfolded this]] Suc(1)
  show ?case by auto
qed simp

lemma irreducible_dvd_setprod: fixes p :: "'a poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd setprod f as"
  shows "\<exists> a \<in> as. p dvd f a"
proof -
  from irr[unfolded irreducible_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 div_mult_self1_is_id div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as rule: infinite_finite_induct)
    case (insert a as)
    hence "setprod f (insert a as) = f a * setprod f as" by auto
    from irreducible_dvd_mult[OF irr insert(4)[unfolded this]]
    show ?case using insert(3) by auto
  qed (insert p1, auto)
qed

lemma irreducible_dvd_listprod: fixes p :: "'a poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd listprod as"
  shows "\<exists> a \<in> set as. p dvd a"
proof -
  from irr[unfolded irreducible_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 div_mult_self1_is_id div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as)
    case (Cons a as)
    hence "listprod (Cons a as) = a * listprod as" by auto
    from irreducible_dvd_mult[OF irr Cons(2)[unfolded this]] Cons(1)
    show ?case by auto
  qed (insert p1, auto)
qed


lemma dvd_mult: fixes p :: "'a poly" 
  assumes "p dvd q * r"
  and "degree p \<noteq> 0" 
shows "\<exists> s t. irreducible s \<and> p = s * t \<and> (s dvd q \<or> s dvd r)"
proof -
  from irreducible_factor[OF assms(2)] obtain s t
  where irred: "irreducible s" and p: "p = s * t" by auto
  from `p dvd q * r` p have s: "s dvd q * r" unfolding dvd_def by auto
  from irreducible_dvd_mult[OF irred s] p irred show ?thesis by auto
qed  
end

end
