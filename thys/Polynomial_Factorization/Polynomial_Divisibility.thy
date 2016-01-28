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
  fixes ty :: "'a :: field itself"
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
    hence "x dvd (gcd a b)" by blast
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

lemma dvd_gcd_mult: fixes p :: "'a :: field poly"
  assumes dvd: "k dvd p * q" "k dvd p * r"
  shows "k dvd p * gcd q r"
proof (cases "p = 0")
  case False note p = this
  show ?thesis
  proof (cases "r = 0")
    case True
    thus ?thesis using p assms 
      by (cases "q = 0", auto simp: dvd_smult gcd_poly.simps normalize_poly_def)
  next
    case False note r = this
    show ?thesis
    proof (cases "q = 0")
      case True
      thus ?thesis using p r assms by (auto simp: dvd_smult gcd_poly.simps normalize_poly_def)
    next
      case False note q = this
      from q r have gcd: "gcd q r \<noteq> 0" by auto
      def g \<equiv> "gcd q r"
      have g: "g \<noteq> 0" unfolding g_def using gcd .
      obtain t where qq: "q = g * t" using poly_gcd_dvd1[of q r] unfolding g_def dvd_def by auto
      obtain s where rr: "r = g * s" using poly_gcd_dvd2[of q r] unfolding g_def dvd_def by auto
      from qq q have t: "t \<noteq> 0" by auto
      from rr r have s: "s \<noteq> 0" by auto
      let ?C = "carrier poly_monoid"
      let ?fac = "wfactors poly_monoid"
      let ?f = "fmset poly_monoid"
      have pq: "p * q \<noteq> 0" using p q by auto
      have pr: "p * r \<noteq> 0" using p r by auto
      have pg: "p * g \<noteq> 0" using p g by auto
      from dvd p r have k: "k \<noteq> 0" by auto
      interpret factorial_monoid poly_monoid by (rule factorial_monoid_field_poly)
      note ex = wfactors_exist[unfolded mk_monoid_simps]
      from ex[OF p] obtain P where PC: "set P \<subseteq> ?C" and Pp: "?fac P p" by auto
      from ex[OF q] obtain Q where QC: "set Q \<subseteq> ?C" and Qq: "?fac Q q" by auto
      from ex[OF r] obtain R where RC: "set R \<subseteq> ?C" and Rr: "?fac R r" by auto
      from ex[OF g] obtain G where GC: "set G \<subseteq> ?C" and Gg: "?fac G g" by auto
      from ex[OF k] obtain K where KC: "set K \<subseteq> ?C" and Kk: "?fac K k" by auto
      from ex[OF s] obtain S where SC: "set S \<subseteq> ?C" and Ss: "?fac S s" by auto
      from ex[OF t] obtain T where TC: "set T \<subseteq> ?C" and Tt: "?fac T t" by auto
      from ex[OF pq] obtain PQ where PQ: "set PQ \<subseteq> ?C" and Pq: "?fac PQ (p * q)" by auto
      from ex[OF pr] obtain PR where PR: "set PR \<subseteq> ?C" and Pr: "?fac PR (p * r)" by auto
      from ex[OF pg] obtain PG where PG: "set PG \<subseteq> ?C" and Pg: "?fac PG (p * g)" by auto
      note mult = mult_wfactors_fmset[unfolded mk_monoid_simps]
      from mult[OF Gg Ss, folded rr, OF Rr g s GC SC RC]
      have fR: "?f R = ?f G + ?f S" .
      from mult[OF Gg Tt, folded qq, OF Qq g t GC TC QC]
      have fQ: "?f Q = ?f G + ?f T" .
      from mult[OF Pp Gg Pg p g PC GC PG]
      have fPG: "?f PG = ?f P + ?f G" .
      from mult[OF Pp Qq Pq p q PC QC PQ]
      have fPQ: "?f PQ = ?f P + ?f Q" .
      from mult[OF Pp Rr Pr p r PC RC PR]
      have fPR: "?f PR = ?f P + ?f R" .
      note div = divides_as_fmsubset[unfolded mk_monoid_simps]
      note fac = Polynomial_Divisibility.factorid_carrier
      from div[OF Kk Pq k pq KC PQ] dvd(1)
      have le1: "?f K \<le># ?f PQ" using fac[OF k pq] using [[simp_trace]] by simp
      from div[OF Kk Pr k pr KC PR] dvd(2)
      have le2: "?f K \<le># ?f PR" using fac[OF k pr] by simp
      from le1 le2 have "?f K \<le># ?f PQ #\<inter> ?f PR" by simp
      also have "\<dots> =  ?f P + ?f G + (?f S #\<inter> ?f T)"
        unfolding fPQ fPG fQ fPR fR unfolding multiset_eq_iff
        by (auto simp: ac_simps)
      also have "?f S #\<inter> ?f T = {#}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain a where "a \<in># ?f S #\<inter> ?f T" 
          by (metis count_empty multiset_eqI not_gr0)
        hence a: "a \<in># ?f S" "a \<in># ?f T" by auto
        from a(1)[unfolded fmset_def in_multiset_in_set] 
          obtain a1 where a1: "a1 \<in> set S" and aa: "assocs poly_monoid a1 = a" by auto
        from a(2)[unfolded fmset_def in_multiset_in_set] 
          obtain a2 where a2: "a2 \<in> set T" and a: "a = assocs poly_monoid a2" by auto
        from SC a1 have a10: "a1 \<noteq> 0" using mk_monoid_simps by auto
        from TC a2 have a20: "a2 \<noteq> 0" using mk_monoid_simps by auto
        from Ss a1 have "Divisibility.irreducible poly_monoid a1"
          unfolding wfactors_def by auto
        hence deg_a1: "degree a1 \<noteq> 0" using a10 
          unfolding Divisibility.irreducible_def Polynomial_Divisibility.poly_Units by auto
        from assocs_eqD[OF aa[unfolded a], unfolded mk_monoid_simps, OF a20 a10]            
        have "a2 \<sim>\<^bsub>poly_monoid\<^esub> a1" .
        from this[unfolded associated_def] a10 a20 have "a2 dvd a1" "a1 dvd a2"
          by (auto simp: fac)
        then obtain a3 where a12: "a2 = a1 * a3" unfolding dvd_def by auto
        with a20 a10 have a30: "a3 \<noteq> 0" by auto
        from wfactors_dividesI[OF Ss SC _ a1] a10 s have a1s: "a1 dvd s" 
          by (simp add: fac)
        from wfactors_dividesI[OF Tt TC _ a2] a20 t have a2t: "a2 dvd t" 
          by (simp add: fac)
        hence a1t: "a1 dvd t" unfolding a12 dvd_def by auto
        from a1t a1s have "g * a1 dvd q" "g * a1 dvd r" unfolding qq rr by auto
        hence "g * a1 dvd g" unfolding g_def by auto
        then obtain h where id: "g * a1 * h = g" unfolding dvd_def by auto
        with g have "h \<noteq> 0" by auto
        with arg_cong[OF id, of degree] g a10
        have "degree a1 = 0" by (simp add: degree_mult_eq)
        with deg_a1 show False by simp
      qed
      finally have "?f K \<le># ?f PG" unfolding fPG by simp 
      with div[OF Kk Pg k pg KC PG] fac[OF k pg]
      have "k dvd p * g" by simp
      thus "k dvd p * gcd q r" unfolding g_def by auto
    qed
  qed
qed auto

hide_const (open) Divisibility.irreducible
hide_fact (open) Divisibility.irreducibleI
hide_fact (open) Divisibility.irreducibleD
hide_fact (open) Divisibility.irreducible_def

hide_const irreducible
hide_fact irreducible_def

end