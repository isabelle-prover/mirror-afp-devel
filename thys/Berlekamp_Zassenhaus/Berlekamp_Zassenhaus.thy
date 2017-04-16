(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>The Polynomial Factorization Algorithm\<close>

subsection \<open>Factoring Square-Free Integer Polynomials\<close>

text \<open>We combine all previous results, i.e., Berlekamp's algorithm, Hensel-lifting, the reconstruction
  of Zassenhaus, Mignotte-bounds, etc., to eventually assemble the factorization algorithm for 
  integer polynomials.\<close>

theory Berlekamp_Zassenhaus
imports 
  Berlekamp_Hensel
  "../Polynomial_Factorization/Gauss_Lemma"
  "../Polynomial_Factorization/Dvd_Int_Poly"
  Reconstruction
  Suitable_Prime
  Degree_Bound
  Code_Abort_Gcd
begin

context
begin
private partial_function (tailrec) find_exponent_main :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  [code]: "find_exponent_main p pm m bnd = (if pm > bnd then m
    else find_exponent_main p (pm * p) (Suc m) bnd)"

definition find_exponent :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "find_exponent p bnd = find_exponent_main p p 1 bnd"
  
lemma find_exponent: assumes p: "p > 1" 
  shows "p ^ find_exponent p bnd > bnd" "find_exponent p bnd \<noteq> 0" 
proof -
  {
    fix m and n
    assume "n = nat (1 + bnd - p^m)" and "m \<ge> 1" 
    hence "bnd < p ^ find_exponent_main p (p^m) m bnd \<and> find_exponent_main p (p^m) m bnd \<ge> 1" 
    proof (induct n arbitrary: m rule: less_induct)
      case (less n m)
      note simp = find_exponent_main.simps[of p "p^m"]
      show ?case
      proof (cases "bnd < p ^ m")
        case True
        thus ?thesis using less unfolding simp by simp
      next
        case False
        hence id: "find_exponent_main p (p ^ m) m bnd = find_exponent_main p (p ^ Suc m) (Suc m) bnd" 
          unfolding simp by (simp add: ac_simps)
        show ?thesis unfolding id 
          by (rule less(1)[OF _ refl], unfold less(2), insert False p, auto)
      qed
    qed
  }
  from this[OF refl, of 1]
  show "p ^ find_exponent p bnd > bnd" "find_exponent p bnd \<noteq> 0"
    unfolding find_exponent_def by auto
qed

end

definition berlekamp_zassenhaus_factorization :: "int poly \<Rightarrow> int poly list" where
  "berlekamp_zassenhaus_factorization f = (let 
     (* find suitable prime *)
     p = suitable_prime_bz f;
     (* compute finite field factorization *)
     (_, fs) = finite_field_factorization_int p f; 
     (* determine maximal degree that we can build by multiplying at most half of the factors *)
     max_deg = degree_bound fs;
     (* determine a number large enough to represent all coefficients of every 
        factor of lc * f that has at most degree most max-deg *)
     bnd = 2 * \<bar>lead_coeff f\<bar> * factor_bound f max_deg;
     (* determine k such that p^k > bnd *)
     k = find_exponent p bnd;
     (* perform hensel lifting to lift factorization to mod (p^k) *)
     vs = hensel_lifting p k f fs
     (* reconstruct integer factors *) 
   in zassenhaus_reconstruction vs p k f)" 
  
theorem berlekamp_zassenhaus_factorization: 
  assumes res: "berlekamp_zassenhaus_factorization f = fs" 
  and sf: "square_free f"
  and deg: "degree f \<noteq> 0" 
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. Missing_Polynomial.irreducible fi)" 
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where berl: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded berlekamp_zassenhaus_factorization_def Let_def, folded p_def,
    unfolded berl split, folded]
  from suitable_prime_bz[OF sf refl]
  have prime: "prime p" and cop: "coprime ?lc p" 
    and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  have p1: "p > 1" using prime unfolding prime_int_iff by simp
  define n where "n = find_exponent p (2 * abs ?lc * factor_bound f (degree_bound gs))" 
  note n = find_exponent[OF p1, of "2 * abs ?lc * factor_bound f (degree_bound gs)",
    folded n_def]
  note cop = cop[unfolded coprime_iff_gcd_one]
  note bh = berlekamp_and_hensel_separated[OF prime cop sf refl berl n(2)]
  have db: "degree_bound (berlekamp_hensel p n f) = degree_bound gs" unfolding bh
    degree_bound_def max_factor_degree_def by simp
  note res = res[folded n_def bh(1)]
  show ?thesis 
    by (rule zassenhaus_reconstruction[OF prime cop sf deg refl _ res], insert n db, auto)
qed

lemma content_free_prod_list:
  fixes fs :: "'a :: {factorial_semiring,semiring_Gcd} poly list" (* where content_mult is proven. *)
  assumes "content_free (prod_list fs)" and "f \<in> set fs" shows "content_free f"
proof (insert assms, induct fs arbitrary: f)
  case Nil then show ?case by auto
next
  case (Cons f' fs)
  from Cons.prems
  have "content f' * content (prod_list fs) dvd 1" by (auto simp: content_mult)
  from this[unfolded zmult_eq_1_iff]
  have "content f' = 1" and "content (prod_list fs) = 1" by auto
  moreover from Cons.prems have "f = f' \<or> f \<in> set fs" by auto
  ultimately show ?case using Cons.hyps[of f] by auto
qed

(*TODO:move*)
lemma irreducible_imp_content_free:
  fixes f :: "'a :: {idom,semiring_gcd} poly"
  assumes irr: "irreducible f" and deg: "degree f \<noteq> 0" shows "content_free f"
proof (rule ccontr)
  assume not: "\<not> ?thesis"
  then have "\<not> [:content f:] dvd 1" by simp
  moreover have "f = [:content f:] * primitive_part f" by simp
    note irreducibleD[OF irr this]
  ultimately
  have "primitive_part f dvd 1" by auto
  from this[unfolded poly_dvd_1] have "degree f = 0" by auto
  with deg show False by auto
qed

(*TODO:move*)
lemma irreducible_content_free_connect:
  fixes f :: "'a :: {idom,semiring_gcd} poly"
  assumes cf: "content_free f" shows "Missing_Polynomial.irreducible f \<longleftrightarrow> irreducible f" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l show ?r
  proof(rule ccontr, elim not_irreducibleE)
    from l have deg: "degree f > 0" by (auto dest: Missing_Polynomial.irreducibleD)
    from cf have f0: "f \<noteq> 0" by auto
    then show "f = 0 \<Longrightarrow> False" by auto
    show "f dvd 1 \<Longrightarrow> False" using deg by (auto simp:poly_dvd_1)
    fix a b assume fab: "f = a * b" and a1: "\<not> a dvd 1" and b1: "\<not> b dvd 1"
    then have af: "a dvd f" and bf: "b dvd f" by auto
    with f0 have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by auto
    from Missing_Polynomial.irreducibleD(2)[OF l, of a] af dvd_imp_degree_le[OF af f0]
    have "degree a = 0 \<or> degree a = degree f" by force
    then show False
    proof(elim disjE)
      assume "degree a = 0"
      then obtain c where ac: "a = [:c:]" by (auto dest: degree0_coeffs)
      from fab[unfolded ac] have "c dvd content f" by (simp add: content_iff coeffs_smult)
      with cf have "c dvd 1" by simp
      then have "a dvd 1" by (auto simp: ac)
      with a1 show False by auto
    next
      assume dega: "degree a = degree f"
      with f0 degree_mult_eq[OF a0 b0] fab have "degree b = 0" by (auto simp: ac_simps)
      then obtain c where bc: "b = [:c:]" by (auto dest: degree0_coeffs)
      from fab[unfolded bc] have "c dvd content f" by (simp add: content_iff coeffs_smult)
      with cf have "c dvd 1" by simp
      then have "b dvd 1" by (auto simp: bc)
      with b1 show False by auto
    qed
  qed
next
  assume r: ?r
  show ?l
  proof(intro Missing_Polynomial.irreducibleI notI)
    assume "degree f = 0"
    then obtain f0 where f: "f = [:f0:]" by (auto dest: degree0_coeffs)
    from cf[unfolded this] have "normalize f0 = 1" by auto
    then have "f0 dvd 1" by (unfold normalize_1_iff)
    with r[unfolded f irreducible_const_poly_iff] show False by auto
  next
    fix g assume deg_g: "degree g \<noteq> 0" and deg_gf: "degree g < degree f" and gf: "g dvd f"
    from gf obtain h where fgh: "f = g * h" by (elim dvdE)
    with r have "g dvd 1 \<or> h dvd 1" by auto
    with deg_g have "degree h = 0" by (auto simp: poly_dvd_1)
    with deg_gf[unfolded fgh] degree_mult_eq[of g h] show False by (cases "g = 0 \<or> h = 0", auto)
  qed
qed

corollary berlekamp_zassenhaus_factorization_content_free:
  assumes res: "berlekamp_zassenhaus_factorization f = fs" 
  and sf: "square_free f"
  and deg: "degree f \<noteq> 0"
  and cf: "content_free f"
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible fi \<and> degree fi > 0 \<and> content_free fi)" 
proof (intro conjI ballI)
  note * = berlekamp_zassenhaus_factorization[OF res sf deg]
  from * show f: "f = prod_list fs" by auto
  fix fi assume fi: "fi \<in> set fs"
  with content_free_prod_list[OF cf[unfolded f]] show "content_free fi" by auto
  with * cf[unfolded f] fi
  show "irreducible fi" by (auto simp: irreducible_content_free_connect)
  from * fi show "degree fi > 0" by (auto simp: Missing_Polynomial.irreducible_def)
qed
end
