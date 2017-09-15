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
  Polynomial_Factorization.Gauss_Lemma
  Polynomial_Factorization.Dvd_Int_Poly
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
  
theorem berlekamp_zassenhaus_factorization_irreducible\<^sub>d:  
  assumes res: "berlekamp_zassenhaus_factorization f = fs" 
  and sf: "square_free f"
  and deg: "degree f > 0" 
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)" 
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where berl: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded berlekamp_zassenhaus_factorization_def Let_def, folded p_def,
    unfolded berl split, folded]
  from suitable_prime_bz[OF sf refl]
  have prime: "prime p" and cop: "coprime ?lc p" and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  from prime interpret poly_mod_prime p by unfold_locales
  define n where "n = find_exponent p (2 * abs ?lc * factor_bound f (degree_bound gs))" 
  note n = find_exponent[OF m1, of "2 * abs ?lc * factor_bound f (degree_bound gs)",
    folded n_def]
  note bh = berlekamp_and_hensel_separated[OF cop sf refl berl n(2)]
  have db: "degree_bound (berlekamp_hensel p n f) = degree_bound gs" unfolding bh
    degree_bound_def max_factor_degree_def by simp
  note res = res[folded n_def bh(1)]
  show ?thesis 
    by (rule zassenhaus_reconstruction[OF prime cop sf deg refl _ res], insert n db, auto)
qed

corollary berlekamp_zassenhaus_factorization_irreducible:
  assumes res: "berlekamp_zassenhaus_factorization f = fs" 
  and sf: "square_free f"
  and deg: "degree f > 0"
  and cf: "content_free f"
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible fi \<and> degree fi > 0 \<and> content_free fi)" 
proof (intro conjI ballI)
  note * = berlekamp_zassenhaus_factorization_irreducible\<^sub>d[OF res sf deg]
  from * show f: "f = prod_list fs" by auto
  fix fi assume fi: "fi \<in> set fs"
  with content_free_prod_list[OF cf[unfolded f]] show "content_free fi" by auto
  from irreducible_content_free_connect[OF this] * cf[unfolded f] fi
  show "irreducible fi" by auto
  from * fi show "degree fi > 0" by (auto)
qed
end
