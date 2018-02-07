(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Implementation and soundness of a modified version of Algorithm 16.22\<close>

text \<open>Algorithm 16.22 is quite similar to the LLL factorization algorithm that was verified
in the previous section. Its main difference is that it has an inner loop where each inner loop
iteration has one invocation of the LLL basis reduction algorithm. Algorithm 16.22 of the textbook
is therefore closer to the factorization algorithm as it is described by Lenstra, Lenstra, and
Lov{\'a}sz \cite{LLL}, which also uses an inner loop.

The advantage of the inner loop is that it can find factors earlier, 
and then small lattices suffice where without the inner loop one
invokes the basis reduction algorithm on a large lattice. The disadvantage of the inner loop
is that if the input is irreducible, then one cannot find any factor early, so that all but the
last iteration have been useless: only the last iteration will prove irreducibility.\<close>

text \<open>We will describe the modifications w.r.t.\ the original Algorithm 16.22 of the textbook
later in this theory.\<close>
theory Factorization_Algorithm_16_22
  imports LLL_Factorization
begin

subsection \<open>Previous lemmas obtained using local type definitions\<close>

(*Obtaining some useful lemmas using local type definitions*)
context poly_mod_prime_type
begin                           

lemma irreducible_m_field_connect_aux [simp]:
  fixes f :: "int poly"
  shows "irreducible\<^sub>d_m f = irreducible_m f"
proof -
  let ?F="(of_int_poly f)::'a mod_ring poly"  
  have [transfer_rule]: "poly_mod_type.MP_Rel m f ?F"
    by (simp add: MP_Rel_def Mp_f_representative)
  have 1: "irreducible\<^sub>d ?F = irreducible ?F" by (transfer, rule irreducible_field_connect)
  from this[untransferred] show ?thesis .
qed

lemma irreducible\<^sub>d_m_dvdm_prod_list_connect:
  assumes irr: "irreducible\<^sub>d_m a"
  and dvd: "a dvdm (prod_list xs)"
shows "\<exists> b \<in> set xs. a dvdm b"
proof -
  let ?A="(of_int_poly a)::'a mod_ring poly"
  let ?XS="(map of_int_poly xs)::'a mod_ring poly list"
  let ?XS1 = "(of_int_poly (prod_list xs))::'a mod_ring poly"
  have [transfer_rule]: "MP_Rel a ?A"
    by (simp add: MP_Rel_def Mp_f_representative)
  have [transfer_rule]: "MP_Rel (prod_list xs) ?XS1"
    by (simp add: MP_Rel_def Mp_f_representative)
  have [transfer_rule]: "list_all2 MP_Rel xs ?XS"
    by (simp add: MP_Rel_def Mp_f_representative list_all2_conv_all_nth)
  have A: "?A dvd ?XS1" using dvd by transfer
  have "\<exists> b \<in> set ?XS. ?A dvd b" 
    by (rule irreducible\<^sub>d_dvd_prod_list, insert irr, transfer, auto simp add: A)
  from this[untransferred] show ?thesis .
qed

end

lemma (in poly_mod_prime) irreducible_m_field_connect [simp]:
  fixes f :: "int poly"  
  shows "irreducible\<^sub>d_m f = irreducible_m f"
  by (rule poly_mod_prime_type.irreducible_m_field_connect_aux[unfolded poly_mod_type_simps, 
        internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF non_empty])

lemma (in poly_mod_prime) irreducible\<^sub>d_m_dvdm_prod_list:
  assumes irr: "irreducible\<^sub>d_m a"
  and dvd: "a dvdm (prod_list xs)"
  shows "\<exists> b \<in> set xs. a dvdm b"
  by (rule poly_mod_prime_type.irreducible\<^sub>d_m_dvdm_prod_list_connect[unfolded poly_mod_type_simps, 
        internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF non_empty irr dvd])


subsection \<open>The modified version of Algorithm 16.22\<close>

    (*Now I implement the for loop of step 8. The loop will finishes in two cases:
      - If j>n'
      - If a divisor is found *)

definition B2_LLL :: "int poly \<Rightarrow> int" where
  "B2_LLL f = int (degree f +1) * 2 ^ (2 * degree f) * \<parallel>f\<parallel>\<^sub>\<infinity>\<^sup>2" 

context
  fixes p pl :: int
begin

private definition pl2 where "pl2 \<equiv> pl div 2"

context
  fixes gs :: "int poly list" 
    and f :: "int poly"
    and u :: "int poly"
begin

text \<open>This is the critical inner loop.

  In the textbook there is a bug, namely that the filter
  is applied to $g'$ and not to the primitive part of $g'$. (Problems occur if the content
  of $g'$ is divisible by $p$.) We have fixed this problem in the obvious way.

  However, there also is a second problem,
  namely it is only guaranteed that $g'$ is divisible by $u$ modulo $p^l$. However, for soundness
  we need to know that then also the primitive part of $g'$ is divisible by $u$ modulo $p^l$. 
  This is not necessary true, e.g., if $g' = p^l$, then the primitive part is $1$ which is not
  divisible by $u$ modulo $p^l$. 
  It is open, whether such a large $g'$ can actually occur. Therefore, the current fix
  is to manually test whether the leading coefficient of $g'$ is strictly smaller than $p^l$.

  With these two modifications, Algorithm 16.22 will become sound as proven below.\<close>

private definition n where "n \<equiv> degree f"
declare n_def[simp]
definition "LLL_reconstruction_inner j \<equiv>
  (*short vector computation*)
  let g' = LLL_implementation.LLL_short_polynomial pl j u 
  (* fix: forbid multiples of p^l as short vector, unclear whether this is really required *)
  in if abs (lead_coeff g') \<ge> pl then None else 
  let ppg = primitive_part g'
  in
  (* slight deviation from textbook: we check divisibility instead of norm-inequality *)
  case div_int_poly f ppg of Some f' \<Rightarrow>
    (* fix: consider modular factors of ppg and not of g' *)
    Some (filter (\<lambda>gi. \<not> poly_mod.dvdm p gi ppg) gs, lead_coeff f', f', ppg)  
  | None \<Rightarrow> None"



function LLL_reconstruction_inner_loop where
 "LLL_reconstruction_inner_loop j =
  (if j > degree f then ([],1,1,f)
   else case LLL_reconstruction_inner j
     of Some tuple \<Rightarrow> tuple
     |  None \<Rightarrow> LLL_reconstruction_inner_loop (j+1))"
  by auto
termination by (relation "measure (\<lambda> j. Suc n - j)", auto)

end
(*The main loop (line 6)*)

partial_function (tailrec) LLL_reconstruction'' where [code]:
 "LLL_reconstruction'' gs b f factors =
  (if gs = [] then factors
   else
     let u = choose_u gs;
         d = degree u;
         (gs', b', f', factor) = LLL_reconstruction_inner_loop gs f u (d+1)
     in LLL_reconstruction'' gs' b' f' (factor#factors)
   )"

definition "reconstruction_of_algorithm_16_22 gs f \<equiv>
  let G = [];
      b = lead_coeff f
  in LLL_reconstruction'' gs b f G"

end

definition factorization_algorithm_16_22 :: "int poly \<Rightarrow> int poly list" where
  "factorization_algorithm_16_22 f = (let 
     (* find suitable prime *)
     p = suitable_prime_bz f;
     (* compute finite field factorization *)
     (_, fs) = finite_field_factorization_int p f;
     (* determine l and B*)
     n = degree f;
     (* bound according to textbook, can be improved by not using max-norm, 
        cf. LLL_factorization-bound  *)
     no = int (n + 1) * (\<parallel>f\<parallel>\<^sub>\<infinity>)\<^sup>2;
     B = sqrt_int_ceiling (2 ^ (5 * n * n) * no ^ (2 * n));
     l = find_exponent p B;
     (* perform hensel lifting to lift factorization to mod (p^l) *)     
     vs = hensel_lifting p l f fs
     (* reconstruct integer factors *) 
   in reconstruction_of_algorithm_16_22 p (p^l) vs f)"


subsection \<open>Soundness proof\<close>

subsubsection \<open>Previous facts\<close>

lemma primitive_part_eq_irreducible:
  fixes a::"int poly"
  assumes a0: "a \<noteq> 0" 
  and deg_gcd: "degree (gcd a b) > 0" 
  and b: "irreducible b" 
  and deg_ab: "degree a \<le> degree b"
  shows "primitive_part a = b \<or> -(primitive_part a) = b"
proof -
  have "b \<noteq> 0 \<and> \<not> b dvd 1 \<and> (\<forall>c d. b = c * d \<longrightarrow> is_unit c \<or> is_unit d)" 
    using b by blast
  let ?g = "(gcd a b)"
  have deg_b_not0: "degree b \<noteq> 0" using b
    by (metis a0 deg_ab deg_gcd degree_gcd1 le_0_eq neq0_conv)
  hence b0: "b \<noteq> 0" by auto
  have not_unit_gcd: "\<not> is_unit ?g" using deg_gcd by auto
  have gcd_dvd_b: "?g dvd b" by simp
  from this obtain c where b_gc: "b = ?g * c" unfolding dvd_def by auto
  hence unit_c: "is_unit c" using b not_unit_gcd by blast
  hence c1: "c = 1 \<or> c = -1" unfolding is_unit_poly_iff unfolding is_unit_int by auto
  have g_dvd_a: "?g dvd a" by simp
  have deg_gb: "degree ?g = degree b" using b_gc unit_c 
    by (metis (no_types, hide_lams) c1 degree_minus mult.commute mult.left_neutral mult_minus_left)
  have deg_ga: "degree ?g \<le> degree a" by (rule degree_gcd1[OF a0])
  hence deg_ab: "degree a = degree b" using deg_ga deg_gb deg_ab by auto
  have content_1: "content b = 1" using nonconst_poly_irreducible_iff[OF deg_b_not0] b by auto 
  have "?g dvd a" by simp
  from this obtain d' where a_gd': "a = ?g * d'" unfolding dvd_def by blast
  have g0: "?g \<noteq> 0" using gcd_eq_0_iff b0 a0 by auto
  hence d'0: "d' \<noteq> 0" using a_gd' a0 by force
  have "degree d' = 0"
  proof -
    have "degree a = degree (?g * d')" using a_gd' by auto
    also have "... = degree ?g + degree d'" 
      by (rule degree_mult_eq[OF g0 d'0])      
    also have "... = degree a + degree d'" using deg_gb deg_ab by auto
    finally show ?thesis by auto
  qed
  from this obtain d where d: "d' = [:d:]" using degree0_coeffs by auto
  have d0: "d \<noteq> 0" using d'0 d by auto
  have db_dvd_a: "smult d b dvd a" 
    using a_gd' d
    by (metis Polynomial.smult_one b_gc mult_unit_dvd_iff 
        dvd_dvd_smult dvd_refl mult_smult_right unit_c)
  have a_dvd_db: "a dvd smult d b"
    using a_gd' d
    by (metis (no_types, hide_lams) Polynomial.smult_one dvd_mult_cancel_left mult.commute 
        mult.right_neutral mult_smult_right semiring_gcd_class.gcd_dvd2)
  show ?thesis
  proof (cases "unit_factor (primitive_part a) = 1")
    case True
    have "primitive_part a = 1 \<or> primitive_part a = normalize b" 
    proof (rule irreducible_normalized_divisors[OF b])
      show "normalize (primitive_part a) = primitive_part a" 
        by (rule unit_factor_1_imp_normalized[OF True])
      show "primitive_part a dvd b" 
        by (rule dvd_smult_int[OF d0 a_dvd_db])
    qed
    moreover have "primitive_part a \<noteq> 1" 
      using deg_b_not0 deg_ab degree_1 degree_primitive_part by metis
    ultimately have "primitive_part a = normalize b" by simp
    thus ?thesis
      by (metis (no_types, lifting) b b_gc c1 gcd.normalize_idem gcd_dvd_b irreducible_normalized_divisors 
          is_unit_gcd mult.commute mult_cancel_right2 mult_minus_left not_unit_gcd) 
  next
    case False
    have ppa_0: "primitive_part a \<noteq> 0" using a0 by simp
    have "coeff (primitive_part a) (degree a) \<noteq> 0" using leading_coeff_neq_0[OF ppa_0] by auto
    hence uf_pa: "unit_factor (primitive_part (-a)) = 1" 
      using False unfolding unit_factor_poly_def
      by (auto, insert zsgn_def, auto)
    have "primitive_part (-a) = 1 \<or> primitive_part (-a) = normalize b" 
    proof (rule irreducible_normalized_divisors[OF b])
      show "normalize (primitive_part (-a)) = primitive_part (-a)"
        by (rule unit_factor_1_imp_normalized[OF uf_pa])
      show "primitive_part (-a) dvd b"
        unfolding primitive_part_neg minus_dvd_iff 
        by (rule dvd_smult_int[OF d0 a_dvd_db])
    qed
    moreover have "primitive_part (-a) \<noteq> 1" using deg_b_not0 deg_ab
      by (metis degree_1 degree_minus degree_primitive_part)
    ultimately have "- primitive_part a = normalize b" by auto
    thus ?thesis
      by (metis (no_types, lifting) add.inverse_inverse b b_gc c1 gcd.normalize_idem gcd_dvd_b 
          irreducible_normalized_divisors 
          is_unit_gcd mult.commute mult.right_neutral mult_minus_left not_unit_gcd)
  qed
qed

lemma not_irreducibleI:
  fixes f:: "'a::{idom_divide,semidom_divide_unit_factor} poly"
  assumes factor_dvd: "factor dvd f" 
    and deg_factor: "degree factor < degree f" 
    and deg_factor0: "degree factor > 0"
  shows "\<not> irreducible f"
proof (rule ccontr, unfold not_not)
  assume irreducible_f: "irreducible f"
  have not_unit_factor: "\<not> is_unit factor" by (rule deg_not_zero_imp_not_unit[OF deg_factor0])
  let ?f' = "f div factor"
  have f_f'_factor: "f = ?f' * factor" using factor_dvd by auto  
  have not_unit_f': "\<not> is_unit ?f'" 
    by (rule deg_not_zero_imp_not_unit)  (metis deg_factor degree_0 degree_mult_eq f_f'_factor 
        less_add_same_cancel2 mult_eq_0_iff not_less_zero)
  have not_unit_f: "\<not> is_unit f" 
    by (rule deg_not_zero_imp_not_unit, insert deg_factor, auto) 
  show False using irreducible_f f_f'_factor not_unit_f not_unit_f' not_unit_factor 
      unfolding irreducible_def by fast
qed

subsubsection \<open>Starting the proof\<close>

text \<open>Key lemma to show that forbidding values of $p^l$ or larger suffices to find correct factors.\<close>

lemma (in poly_mod_prime) Mp_smult_p_removal: "poly_mod.Mp (p * p ^ k) (smult p f) = 0 \<Longrightarrow> poly_mod.Mp (p^k) f = 0"
  by (smt add.left_neutral m1 poly_mod.Dp_Mp_eq poly_mod.Mp_smult_m_0 sdiv_poly_smult smult_smult)

lemma (in poly_mod_prime) eq_m_smult_p_removal: "poly_mod.eq_m (p * p ^ k) (smult p f) (smult p g) 
  \<Longrightarrow> poly_mod.eq_m (p^k) f g" using Mp_smult_p_removal[of k "f - g"]
  by (metis add_diff_cancel_left' diff_add_cancel diff_self poly_mod.Mp_0 poly_mod.minus_Mp(2) smult_diff_right)

lemma content_le_lead_coeff: "abs (content (f :: int poly)) \<le> abs (lead_coeff f)"
proof (cases "f = 0")
  case False
  from content_dvd_coeff[of f "degree f"] have "abs (content f) dvd abs (lead_coeff f)" by auto
  moreover have "abs (lead_coeff f) \<noteq> 0" using False by auto
  ultimately show ?thesis by (smt dvd_imp_le_int)
qed auto

lemma poly_mod_dvd_drop_smult: assumes u: "monic u" and p: "prime p" and c: "c \<noteq> 0" "\<bar>c\<bar> < p^l"
  and dvd: "poly_mod.dvdm (p^l) u (smult c f)" 
shows "poly_mod.dvdm p u f" 
  using c dvd
proof (induct l arbitrary: c rule: less_induct)
  case (less l c)
  interpret poly_mod_prime p by (unfold_locales, insert p, auto)
  note c = less(2-3)
  note dvd = less(4)
  note IH = less(1)
  show ?case
  proof (cases "l = 0")
    case True
    thus ?thesis using c dvd by auto
  next
    case l0: False
    interpret pl: poly_mod_2 "p^l" by (unfold_locales, insert m1 l0, auto)
    show ?thesis
    proof (cases "p dvd c")
      case False
      let ?i = "inverse_mod c (p ^ l)" 
      have "gcd c p = 1" using prime_imp_coprime_int[OF p False] gcd.commute[of p] by simp
      from pl.inverse_mod_coprime_exp[OF refl p l0 this] 
      have id: "pl.M (?i * c) = 1" .
      have "pl.Mp (smult ?i (smult c f)) = pl.Mp (smult (pl.M (?i * c)) f)" by simp
      also have "\<dots> = pl.Mp f" unfolding id by simp
      finally have "pl.dvdm u f" using pl.dvdm_smult[OF dvd, of ?i] unfolding pl.dvdm_def by simp
      thus "u dvdm f" using l0 pl_dvdm_imp_p_dvdm by blast 
    next
      case True
      then obtain d where cpd: "c = p * d" unfolding dvd_def by auto
      from cpd c have d0: "d \<noteq> 0" by auto
      note to_p = Mp_Mp_pow_is_Mp[OF l0 m1]
      from dvd obtain v where eq: "pl.eq_m (u * v) (smult p (smult d f))" 
        unfolding pl.dvdm_def cpd by auto
      from arg_cong[OF this, of Mp, unfolded to_p] 
      have "Mp (u * v) = 0" unfolding Mp_smult_m_0 .
      with u have "Mp v = 0"
        by (metis Mp_0 add_eq_0_iff_both_eq_0 degree_0 
            degree_m_mult_eq monic_degree_0 monic_degree_m mult_cancel_right2)
      from Mp_0_smult_sdiv_poly[OF this]
      obtain w where v: "v = smult p w" by metis
      with eq have eq: "pl.eq_m (smult p (u * w)) (smult p (smult d f))" by simp
      from l0 obtain ll where "l = Suc ll" by (cases l, auto)
      hence pl: "p^l = p * p^ll" and ll: "ll < l" by auto
      from c(2) have d_small: "\<bar>d\<bar> < p^ll" unfolding pl cpd abs_mult
        using mult_less_cancel_left_pos[of p d "p^ll"] m1 by auto
      from eq_m_smult_p_removal[OF eq[unfolded pl]] 
      have "poly_mod.eq_m (p^ll) (u * w) (smult d f)" .
      hence dvd: "poly_mod.dvdm (p^ll) u (smult d f)" unfolding poly_mod.dvdm_def by metis
      show ?thesis by (rule IH[OF ll d0 d_small dvd])
    qed
  qed
qed


context
  fixes p :: int
    and F :: "int poly"
    and N :: nat
    and l :: nat
  defines [simp]: "N \<equiv> degree F"
  assumes p: "prime p"
      and content_F[simp]: "content F = 1"
      and N0: "N > 0"
      and bound_l: "2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N) \<le> (p^l)\<^sup>2"
begin

private lemma F0: "F\<noteq>0" using content_F 
  by fastforce

private lemma p1: "p > 1" using p prime_gt_1_int by auto

interpretation p: poly_mod_prime p using p by unfold_locales

interpretation pl: poly_mod "p^l".

lemma B2_2: "2 \<le> B2_LLL F" 
proof -
  from F0 have "\<parallel>F\<parallel>\<^sub>\<infinity> \<noteq> 0" by simp
  hence F1: "\<parallel>F\<parallel>\<^sub>\<infinity> \<ge> 1" using linf_norm_poly_ge_0[of F] by linarith  
  have "(2 :: int) = 2 * 1 * (1^2)" by simp
  also have "\<dots> \<le> B2_LLL F" unfolding B2_LLL_def
    by (intro mult_mono power_mono, insert N0 F1, auto)
  finally show "2 \<le> B2_LLL F" .
qed

lemma l_gt_0: "l > 0"
proof (cases l)
  case 0  
  have "1 * 2 \<le> 2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N)" 
  proof (rule mult_mono)
    have "2 * 1 \<le> (2 :: int) * (2 ^ (2*N - 1))" by (rule mult_left_mono, auto) 
    also have "\<dots> = 2 ^ (2 * N)" using N0 by (cases N, auto)
    also have "\<dots> \<le> B2_LLL F ^ (2 * N)" 
      by (rule power_mono[OF B2_2], force)
    finally show "2 \<le> B2_LLL F ^ (2 * N)" by simp
  qed auto
  also have "\<dots> \<le> 1" using bound_l[unfolded 0] by auto 
  finally show ?thesis by auto
qed auto

lemma l0: "l \<noteq> 0" using l_gt_0 by auto

lemma pl_not0: "p ^ l \<noteq> 0" using p1 l0 by auto

interpretation pl: poly_mod_2 "p^l" 
  by (standard, insert p1 l0, auto)

lemma coprime_pl: "coprime a p \<Longrightarrow> coprime (pl.M a) p" 
  unfolding coprime_iff_gcd_one pl.M_def
  by (metis coprime_power gcd_mod_left l_gt_0 pl_not0)

private lemmas pl_dvdm_imp_p_dvdm = p.pl_dvdm_imp_p_dvdm[OF l0]

lemma p_Mp_pl_Mp[simp]: "p.Mp (pl.Mp k) = p.Mp k" 
  using Mp_Mp_pow_is_Mp[OF l0 p.m1] .

context
  fixes u :: "int poly"
    and d and f and n
    and gs :: "int poly list" 
  defines [simp]: "d \<equiv> degree u"
  assumes d0: "d > 0"
      and u: "monic u"
      and irred_u: "p.irreducible_m u"
      and uf: "pl.dvdm u f"
      and f_dvd_F: "f dvd F"
      and [simp]: "n == degree f"
      and f_gs: "pl.unique_factorization_m f (lead_coeff f, mset gs)" 
      and cop: "coprime (lead_coeff f) p" 
      and sf: "p.square_free_m f"
      and sf_F: "square_free f" 
      and u_gs: "u \<in> set gs" 
      and norm_gs: "map pl.Mp gs = gs" 
begin

private lemma content_f[simp]: "content f = 1" 
  by (rule content_dvd_1[OF content_F f_dvd_F]) 

interpretation pl: poly_mod_2 "p^l" using l0 p1 by (unfold_locales, auto)

private lemma f0: "f \<noteq> 0" using content_f by fastforce

private lemma Mpf0: "pl.Mp f \<noteq> 0"
  by (metis p.square_free_m_def p_Mp_pl_Mp sf)

private lemma dn: "d \<le> n" using pl.dvdm_imp_degree_le[OF uf u] Mpf0 p1 l0 by auto

private lemma n0: "n > 0" using d0 dn by auto

private lemma B2_0[intro!]: "B2_LLL F > 0" using B2_2 by auto
private lemma deg_u: "degree u > 0" using d0 d_def by auto

private lemma n_le_N: "n\<le>N" by (simp add: dvd_imp_degree_le[OF f_dvd_F F0])

lemma exists_reconstruction: "\<exists>h0. irreducible\<^sub>d h0 \<and> p.dvdm u h0 \<and> h0 dvd f"
proof -   
  have deg_f: "degree f > 0" using \<open>n \<equiv> degree f\<close> n0 by blast
  from berlekamp_zassenhaus_factorization_irreducible\<^sub>d[OF refl sf_F deg_f]
  obtain fs where f_fs: "f = prod_list fs"
    and c: "(\<forall>fi\<in>set fs. irreducible\<^sub>d fi \<and> 0 < degree fi )" by blast 
  have irrd_u: "p.irreducible\<^sub>d_m u" by (simp add: irred_u)
  have "pl.dvdm u (prod_list fs)" using uf f_fs by simp
  hence "p.dvdm u (prod_list fs)" by (rule pl_dvdm_imp_p_dvdm)
  from this obtain h0 where h0: "h0 \<in> set fs" and dvdm_u_h0: "p.dvdm u h0" 
    using p.irreducible\<^sub>d_m_dvdm_prod_list[OF irrd_u] by auto
  moreover have "h0 dvd f" by (unfold f_fs, rule prod_list_dvd[OF h0])  
  moreover have "irreducible\<^sub>d h0" using c h0 by auto
  ultimately show ?thesis by blast
qed

lemma irred_pl_u: "pl.irreducible\<^sub>d_m u" 
  using u_gs f_gs unfolding pl.unique_factorization_m_alt_def pl.factorization_m_def by auto

private lemma prime_u: assumes "pl.dvdm u (g * h)" and "g * h dvd f"
  shows "pl.dvdm u g \<or> pl.dvdm u h"
proof -
  let ?uf = "pl.unique_factorization_m" 
  from assms(2) obtain k where f: "f = (g * h) * k" unfolding dvd_def by auto
  from pl.unique_factorization_m_factor[OF p.prime f_gs[unfolded f] _ _ l0 refl, folded f, OF cop sf]
  obtain fs where fs: "?uf (g * h) (lead_coeff (g * h), fs)" 
    and Mp_fs: "image_mset pl.Mp fs = fs" by auto
  from p.coprime_lead_coeff_factor[OF p.prime cop[unfolded f]] 
  have cop_gh: "coprime (lead_coeff (g * h)) p" by auto
  from sf[unfolded f] have sf_gh: "p.square_free_m (g * h)" by (rule p.square_free_m_factor)
  from pl.unique_factorization_m_factor[OF p.prime fs cop_gh sf_gh l0 refl]
  obtain gs hs where uf: "?uf g (lead_coeff g, gs)" "?uf h (lead_coeff h, hs)" 
    and id: "pl.Mf (lead_coeff (g * h), fs) = pl.Mf (lead_coeff g * lead_coeff h, gs + hs)" by auto  
  show ?thesis 
  proof (cases "pl.Mp u \<in># image_mset pl.Mp (gs + hs)")
    case True
    hence "pl.Mp u \<in># image_mset pl.Mp gs \<or> pl.Mp u \<in># image_mset pl.Mp hs" by auto
    with uf obtain k ks where k: "k \<in> {g,h}" and uf: "?uf k (lead_coeff k, ks)" 
      and mem: "pl.Mp u \<in># image_mset pl.Mp ks" by auto
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf] mem] k
    show ?thesis by auto
  next
    case False
    hence u_fs: "pl.Mp u \<notin># fs" using id[unfolded pl.Mf_def] Mp_fs by auto
    from assms(1)[unfolded pl.dvdm_def] obtain v where id_pl: "pl.eq_m (g * h) (u * v)" by auto
    define w where "w = pl.Mp v" 
    with id_pl have id_pl: "pl.eq_m (g * h) (u * w)" and w: "pl.Mp w = w" by auto
    from arg_cong[OF id_pl, of p.Mp]  have id_p: "p.eq_m (g * h) (u * w)" by simp
    from sf_gh id_p have sf_uv: "p.square_free_m (u * w)" by (rule p.square_free_m_cong)
    hence sf_w: "p.square_free_m w" by (rule p.square_free_m_factor)
    have "lead_coeff w = lead_coeff (pl.Mp (u * w))" using w \<open>monic u\<close>
      by (smt leading_coeff_neq_0 pl.M_def pl.degree_m_eq_lead_coeff pl.m1 poly_mod.degree_m_eq 
          poly_mod.lead_coeff_monic_mult)
    also have "\<dots> = lead_coeff (pl.Mp (g * h))" unfolding id_pl ..
    also have "\<dots> = pl.M (lead_coeff (g * h))"
      by (rule pl.degree_m_eq_lead_coeff[OF pl.degree_m_eq[OF p.coprime_exp_mod[OF cop_gh l0] pl.m1]])
    also have "coprime \<dots> p" using cop_gh by (rule coprime_pl)
    finally have cop_w: "coprime (lead_coeff w) p" .  
    from p.berlekamp_hensel[OF cop_w sf_w refl l0] 
    obtain wc ws where 1: "pl.factorization_m w (wc, ws)" by auto
    have 2: "pl.factorization_m u (1,{#u#})" unfolding pl.factorization_m_def
      using irred_pl_u pl.monic_Mp[OF \<open>monic u\<close>] by auto
    from pl.factorization_m_prod[OF 2 1]
    have "pl.factorization_m (pl.Mp (u * w)) (wc, {#u#} + ws)" by auto
    hence "pl.factorization_m (g * h) (wc, {#u#} + ws)" unfolding id_pl[symmetric] by simp
    with fs[unfolded pl.unique_factorization_m_alt_def] 
    have "pl.Mf (wc, {# u #} + ws) = pl.Mf (lead_coeff (g * h), fs)" by blast
    with u_fs Mp_fs have False unfolding pl.Mf_def by auto
    thus ?thesis ..
  qed
qed

lemma dvdm_power: assumes "g dvd f" 
  shows "p.dvdm u g \<longleftrightarrow> pl.dvdm u g"
proof 
  assume "pl.dvdm u g" 
  thus "p.dvdm u g" by (rule pl_dvdm_imp_p_dvdm)
next
  assume dvd: "p.dvdm u g"
  from norm_gs have norm_gsp: "\<And> f. f \<in> set gs \<Longrightarrow> pl.Mp f = f" by (induct gs, auto)
  with f_gs[unfolded pl.unique_factorization_m_alt_def pl.factorization_m_def split] 
  have gs_irred_mon: "\<And> f. f \<in># mset gs \<Longrightarrow> pl.irreducible\<^sub>d_m f \<and> monic f" by auto   
  from norm_gs have norm_gs: "image_mset pl.Mp (mset gs) = mset gs" by (induct gs, auto) 
  from assms obtain h where f: "f = g * h" unfolding dvd_def by auto
  from pl.unique_factorization_m_factor[OF p.prime f_gs[unfolded f] _ _ l0 refl, folded f, 
      OF cop sf, unfolded pl.Mf_def split] norm_gs
  obtain hs fs where uf: "pl.unique_factorization_m h (lead_coeff h, hs)" 
      "pl.unique_factorization_m g (lead_coeff g, fs)" 
     and id: "mset gs = fs + hs" 
     and norm: "image_mset pl.Mp fs = fs" "image_mset pl.Mp hs = hs" by auto
  from p.square_free_m_prod_imp_coprime_m[OF sf[unfolded f]] 
  have cop_h_f: "p.coprime_m g h" by auto  
  show "pl.dvdm u g"
  proof (cases "u \<in># fs")
    case True
    hence "pl.Mp u \<in># image_mset pl.Mp fs" by auto
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf(2)] this]
    show ?thesis .
  next
    case False
    from u_gs have "u \<in># mset gs" by auto
    from this[unfolded id] False have "u \<in># hs" by auto
    hence "pl.Mp u \<in># image_mset pl.Mp hs" by auto
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf(1)] this]
    have "pl.dvdm u h" by auto
    from pl_dvdm_imp_p_dvdm[OF this] 
    have "p.dvdm u h" by auto
    from cop_h_f[unfolded p.coprime_m_def, rule_format, OF dvd this]
    have "p.dvdm u 1" .
    from p.dvdm_imp_degree_le[OF this u _ p.m1] have "degree u = 0" by auto
    with deg_u show ?thesis by auto
  qed
qed

lemma factor_dvd_f_0: assumes "factor dvd f" 
  shows "pl.Mp factor \<noteq> 0"
proof -
  from assms obtain h where f: "f = factor * h" unfolding dvd_def ..
  from arg_cong[OF this, of pl.Mp] have "0 \<noteq> pl.Mp (pl.Mp factor * h)" 
    using Mpf0 by auto
  thus ?thesis by fastforce
qed

lemma degree_factor_ge_degree_u:
  assumes u_dvdm_factor: "pl.dvdm u factor" 
    and factor_dvd: "factor dvd f" shows "degree u \<le> degree factor"
proof - 
  from factor_dvd_f_0[OF factor_dvd] have factor0: "pl.Mp factor \<noteq> 0" .  
  from u_dvdm_factor[unfolded pl.dvdm_def] obtain v where
    *: "pl.Mp factor = pl.Mp (u * pl.Mp v)" by auto
  with factor0 have v0: "pl.Mp v \<noteq> 0" by fastforce
  hence "0 \<noteq> lead_coeff (pl.Mp v)" by auto
  also have "lead_coeff (pl.Mp v) = pl.M (lead_coeff (pl.Mp v))" 
    by (auto simp: pl.Mp_def coeff_map_poly)
  finally have **: "lead_coeff (pl.Mp v) \<noteq> p ^ l * r" for r by (auto simp: pl.M_def) 
  from * have "degree factor \<ge> pl.degree_m (u * pl.Mp v)" using pl.degree_m_le[of factor] by auto
  also have "pl.degree_m (u * pl.Mp v) = degree (u * pl.Mp v)" 
    by (rule pl.degree_m_eq, unfold lead_coeff_mult, insert u pl.m1 **, auto)
  also have "\<dots> = degree u + degree (pl.Mp v)" 
    by (rule degree_mult_eq, insert v0 u, auto)
  finally show ?thesis by auto
qed

subsubsection \<open>Inner loop\<close>

context
  fixes j' :: nat
  assumes dj': "d \<le> j'"
      and j'n: "j' < n"
      and deg: "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j'"
begin

private abbreviation (input) "j \<equiv> Suc j'"

private lemma jn: "j \<le> n" using j'n by auto

private definition "g \<equiv> LLL_implementation.LLL_short_polynomial (p^l) j u"

lemma deg_g_j: "degree g < j" 
    and g0: "g \<noteq> 0" 
    and ug :"pl.dvdm u g" 
    and short_g: "h \<noteq> 0 \<Longrightarrow> pl.dvdm u h \<Longrightarrow> degree h < j \<Longrightarrow> \<parallel>g\<parallel>\<^sup>2 \<le> 2 ^ (j - 1) * \<parallel>h\<parallel>\<^sup>2" 
proof (atomize(full), goal_cases)
  case 1
  from deg_u have degu0: "degree u \<noteq> 0" by auto
  have ju: "j \<ge> degree u" using d_def dj' le_Suc_eq by blast 
  have ju': "j > degree u" using d_def dj' by auto 
  note short = LLL_implementation.LLL_short_polynomial[OF degu0 ju pl_not0, folded g_def]
  from short(1-3) short(4)[OF u ju'] show ?case by blast
qed
  

private lemma [simp]:
  assumes "rat_of_int (sq_norm_vec b) \<le> 2 ^ m * rat_of_int (sq_norm_vec a)"
  shows "(sq_norm_vec b) \<le> 2 ^ m * (sq_norm_vec a)" 
  using of_int_le_iff assms by fastforce
  
lemma
  assumes u_factor: "pl.dvdm u factor"
     and factor_f: "factor dvd f"
     and deg_factor: "degree factor > 0"
     and "degree factor \<le> j'"
   shows deg_g_0: "degree g > 0"
     and sq_norm_factor_g_bound: "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ j' < (p^l)\<^sup>2 "
proof -
  have deg_factor_j [simp]: "degree factor = j'" 
    using assms deg[OF u_factor factor_f] by auto
  hence deg_factor_lt_j: "degree factor < j" by simp
  from deg_factor have j'0: "j' > 0" by simp
  from factor_f f0 have factor0: "factor \<noteq> 0" by auto
  have factor_dvd_F: "factor dvd F" using dvd_trans factor_f f_dvd_F by auto 
  from short_g[OF factor0 u_factor deg_factor_lt_j] 
  have short: "\<parallel>g\<parallel>\<^sup>2 \<le> 2 ^ j' * \<parallel>factor\<parallel>\<^sup>2" by simp
  have "\<dots> \<le> 2 ^ j' * ((1 + int N) * 2 ^ (2 * j') * \<parallel>F\<parallel>\<^sub>\<infinity>\<^sup>2)" 
    using sq_norm_factor_bound[OF factor_dvd_F F0] by auto
  also have "\<dots> < 2 ^ j' * B2_LLL F"
    using jn n_le_N by (auto intro!: mult_strict_right_mono simp: B2_LLL_def)
  finally have 2: "2 ^ j' * \<parallel>factor\<parallel>\<^sup>2 < \<dots>" by simp 
  from le_less_trans[OF short 2] have "\<parallel>g\<parallel>\<^sup>2 < \<dots>" by auto
  with j'0 have "\<parallel>g\<parallel>\<^sup>2^j' < \<dots>^j'" by (intro power_strict_mono, auto)
  with j'0 factor0 have "\<parallel>g\<parallel>\<^sup>2^j' * \<parallel>factor\<parallel>\<^sup>2 ^ degree g < \<dots> * \<parallel>factor\<parallel>\<^sup>2 ^ degree g"
    by (intro mult_strict_right_mono, auto)
  also have "\<dots> \<le> (2 ^ j' * B2_LLL F)^j' * \<parallel>factor\<parallel>\<^sup>2 ^ j'" using deg_g_j
    using B2_0 factor0 
    by (auto intro!: mult_left_mono power_increasing simp:int_one_le_iff_zero_less)
  also have "\<dots> = (2 ^ j' * \<parallel>factor\<parallel>\<^sup>2) ^ j' * B2_LLL F ^ j'" using j'0 factor0 B2_0
    by (auto simp add: field_simps)
  also from 2 have "\<dots> < (2 ^ j' * B2_LLL F) ^ j' * B2_LLL F ^ j'"
    using j'0 factor0 B2_0
    by (intro mult_strict_right_mono power_strict_mono mult_nonneg_nonneg, auto)
  also have "\<dots> \<le> 2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N)"
    using j'n B2_0 n_le_N
    by (auto simp: semiring_normalization_rules intro!:mult_mono power_increasing power_mono)
  also from bound_l have "\<dots> \<le> (p ^ l)\<^sup>2".
  finally show a: "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ j' < (p^l)\<^sup>2" by (auto simp: field_simps)
  show "degree g > 0"
  proof (rule ccontr)
    assume a1: "\<not> 0 < degree g"
    have deg_g0: "degree g = 0" using a1 by auto 
    obtain k' where g_k': "g = [:k':]" using deg_g0 degree0_coeffs  by auto
    have "k' mod p^l = 0" 
    proof (rule pl.monic_dvdm_constant[OF _ u])
      show "pl.dvdm u [:k':]" using ug g_k' by auto        
      show "0 < degree u" using d0 unfolding d_def by simp
    qed
    from this obtain k where g_def: "g = [:k* p^l:]" 
        using g_k' zmod_eq_0_iff by fastforce        
    have k: "k \<noteq> 0" using g_def g0 by auto     
    have "\<parallel>g\<parallel>\<^sup>2 ^ j' = \<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ j'" unfolding deg_g0 by auto
    also have "... < (p^l)\<^sup>2" using a by auto
    finally have b: "\<parallel>g\<parallel>\<^sup>2 ^ j' < (p^l)\<^sup>2" by auto      
    have "\<parallel>g\<parallel>\<^sup>2 = k\<^sup>2* (p^l)^2" unfolding g_def
      by (simp add: numeral_2_eq_2)
    hence 3: "(k\<^sup>2* (p^l)^2)^ j' < (p^l)\<^sup>2" using b by auto      
    have pl_g0: "(p ^ l)\<^sup>2 > 0" using p1 l0 by auto
    have pl_ge1: "(p ^ l)\<^sup>2 \<ge> 1" using p1 one_le_power by auto
    have kj_ge_1: "1 \<le> k\<^sup>2 ^ j'" by (rule one_le_power, simp add: int_one_le_iff_zero_less k)
    have "(p^l)\<^sup>2 = (p^l)\<^sup>2^1" by auto
    also have "... \<le> ((p^l)\<^sup>2)^j'"
      by (rule power_increasing[OF _ pl_ge1], insert j'0, linarith)
    also have "... \<le> (k\<^sup>2)^j' * (p ^ l)\<^sup>2 ^ j'" 
      by (auto simp add: mult_le_cancel_right1 kj_ge_1)      
    also have "... = (k\<^sup>2 * (p ^ l)\<^sup>2)^ j'" 
      unfolding power_mult_distrib[of "k\<^sup>2" "(p ^ l)\<^sup>2" j'] by simp      
    finally show False using 3 by auto
  qed
qed

lemma LLL_reconstruction_inner_complete:
  assumes ret: "LLL_reconstruction_inner p (p^l) gs f u j = None"
  shows "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
proof (rule ccontr)
  fix factor
  assume u_factor: "pl.dvdm u factor"
     and factor_f: "factor dvd f"
     and deg_factor2: "\<not> j \<le> degree factor"
  with deg[OF this(1,2)] have deg_factor_j [simp]: "degree factor = j'" by auto
  from content_dvd_1[OF content_f factor_f] have cf: "content factor = 1" by auto
  have deg_factor: "degree factor > 0"
    using d0 deg_factor_j dj' by linarith 
  from deg_factor have j'0: "j' > 0" by simp
  from factor_f f0 have factor0: "factor \<noteq> 0" by auto
  have irred: "irreducible factor"
  proof (rule irreducibleI)
    show factor0: "factor \<noteq> 0" using deg_factor by fastforce
    show "\<not> is_unit factor" using deg_factor by (rule deg_not_zero_imp_not_unit)
    fix a b
    assume fact: "factor = a * b" 
    from arg_cong[OF this, of degree, unfolded deg_factor_j] 
    have deg_ab: "degree a + degree b = j'" 
      using factor0[unfolded fact] by (auto simp: degree_mult_eq)
    from prime_u[OF u_factor[unfolded fact] factor_f[unfolded fact]]
    have dvd: "pl.dvdm u a \<or> pl.dvdm u b" by auto
    show "is_unit a \<or> is_unit b"
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      hence ab: "\<not> is_unit a" "\<not> is_unit b" by auto
      {
        fix c
        assume "c \<in> {a,b}" 
        with fact ab have c: "c dvd factor" "\<not> is_unit c" by auto
        from content_dvd_1[OF cf c(1)] have cc: "content c = 1" .
        with c(2) have dc: "degree c > 0" using content_free_unit by blast
        note dc cc c
      } note * = this
      from *(1)[of a] *(1)[of b] deg_ab have deg_ab: "degree a < j'" "degree b < j'" by auto
      from dvd obtain c where c: "c \<in> {a,b}" and dvd: "pl.dvdm u c" by auto
      from deg_ab *[OF c] c
      have c: "0 < degree c" "content c = 1" "c dvd factor" "degree c < j'" by auto        
      from dvd_trans[OF c(3) factor_f] have c_f: "c dvd f" .
      from deg[OF dvd c_f] c(4) show False by auto
    qed
  qed
  let ?g = "gcd factor g" 
  have gcd: "degree ?g > 0"
    apply (rule common_factor_via_short[OF _ _ u _ u_factor ug], unfold deg_factor_j)
    using d0 dj' p1
    apply (auto intro!: sq_norm_factor_g_bound deg_g_0 u_factor factor_f deg_factor)
    done
  have "?g dvd factor" by auto
  then obtain h where factor: "factor = ?g * h" unfolding dvd_def by auto
  from irreducibleD[OF irred this] gcd have "is_unit h" by auto
  then obtain k where hk1: "h * k = 1" unfolding dvd_def by auto
  from arg_cong[OF this, of degree]
  have "degree h = 0"
    by (subst (asm) degree_mult_eq, insert hk1, auto)
  from degree0_coeffs[OF this] hk1
  obtain c where h: "h = [:c:]" and c: "c \<noteq> 0" by fastforce
  from arg_cong[OF factor, of degree] have id: "degree ?g = degree factor" 
    unfolding h using c by auto
  moreover have "degree ?g \<le> degree g" 
    by (subst gcd.commute, rule degree_gcd1[OF g0])
  ultimately have "degree g \<ge> degree factor" by auto
  with id deg_factor2 deg_g_j have deg: "degree ?g = degree g" 
    and "degree g = degree factor" by auto
  have "?g dvd g" by auto
  then obtain q where g: "g = ?g * q" unfolding dvd_def by auto
  from arg_cong[OF this, of degree] deg
  have "degree q = 0" 
    by (subst (asm) degree_mult_eq, insert g g0, force, force) simp
  from degree0_coeffs[OF this] g g0
  obtain d where p: "q = [:d:]" and d: "d \<noteq> 0" by fastforce
  from arg_cong[OF factor, of "op * q"] 
  have "q * factor = h * g"
    by (subst g, auto simp: ac_simps)
  hence "smult d factor = h * g" unfolding p h by auto
  hence "g dvd smult d factor" by simp
  from dvd_smult_int[OF d this]
  have "primitive_part g dvd factor" .
  with factor_f have dvd: "primitive_part g dvd f" by (auto dest: dvd_trans)
  from ret[unfolded LLL_reconstruction_inner_def Let_def, folded g_def]
  have ret': "div_int_poly f (primitive_part g) = None \<or> p^l \<le> abs (lead_coeff g)" 
    using not_None_eq by (fastforce split: if_splits)
  with dvd g0 div_int_poly[of f "primitive_part g"]
  have "p^l \<le> abs (lead_coeff g)" unfolding dvd_def mult.commute[of _ "primitive_part g"] by force
  hence "(p^l)^2 \<le> (abs (lead_coeff g))^2" using pl.m1
    by (smt power2_less_imp_less) 
  also have "\<dots> \<le> \<parallel>g\<parallel>\<^sup>2" by (rule coeff_le_sq_norm)
  also have "\<dots> \<le> 2 ^ j' * \<parallel>factor\<parallel>\<^sup>2" 
    using short_g[OF factor0 u_factor] deg_factor_j by auto
  also have "\<dots> < 2 ^ N * \<parallel>factor\<parallel>\<^sup>2" 
    by (rule mult_strict_right_mono[OF power_strict_increasing], insert j'n n_le_N factor0, auto)
  also have "\<dots> \<le> 2 ^ N * (int (degree F + 1) * 2 ^ (2 * degree factor) * \<parallel>F\<parallel>\<^sub>\<infinity>\<^sup>2)" 
    by (rule mult_left_mono[OF sq_norm_factor_bound(1)[OF dvd_trans[OF factor_f f_dvd_F] F0]], auto)
  also have "\<dots> \<le> 2 ^ N * (int (N + 1) * 2 ^ (2 * N) * \<parallel>F\<parallel>\<^sub>\<infinity>\<^sup>2)" unfolding N_def[symmetric]
    by (rule mult_left_mono[OF mult_right_mono[OF mult_left_mono[OF power_increasing]]],
    insert j'n n_le_N, auto)
  also have "\<dots> \<le> (p ^ l)\<^sup>2" 
  proof (rule order.trans[OF _ bound_l[unfolded B2_LLL_def, folded N_def]], rule mult_mono[OF power_increasing])
    from F0 have "\<parallel>F\<parallel>\<^sub>\<infinity> \<noteq> 0" by auto
    moreover have "\<parallel>F\<parallel>\<^sub>\<infinity> \<ge> 0" by auto
    ultimately have F1: "\<parallel>F\<parallel>\<^sub>\<infinity> \<ge> 1" by linarith
    show "N \<le> N^2" using power_increasing[of 1 2 N] \<open>N > 0\<close> by auto
    show "int (N + 1) * 2 ^ (2 * N) * \<parallel>F\<parallel>\<^sub>\<infinity>\<^sup>2 \<le> (int (N + 1) * 2 ^ (2 * N) * \<parallel>F\<parallel>\<^sub>\<infinity>\<^sup>2) ^ (2 * N)" 
      unfolding power_mult[symmetric] power_mult_distrib 
      by (intro mult_mono power_increasing self_le_power, insert \<open>N > 0\<close> F0 F1, auto)
  qed auto
  finally show False by simp
qed

lemma LLL_reconstruction_inner_sound:
  assumes ret: "LLL_reconstruction_inner p (p^l) gs f u j = Some (gs',b',f',h)" 
  and uf: "pl.unique_factorization_m f (lead_coeff f, mset gs)"
  and cop: "coprime (lead_coeff f) p" 
  and sf: "p.square_free_m f" 
  notes ret' = ret[unfolded LLL_reconstruction_inner_def Let_def, folded g_def]
  shows "f = f' * h" (is "?g1")
    and "irreducible h" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (lead_coeff f', mset gs')" (is "?g4")
    and "pl.dvdm u h" (is ?g5)
    and "degree h = j'" (is ?g6)
    and "length gs' < length gs" (is ?g7)
    and "set gs' \<subseteq> set gs" (is ?g8)
    and "gs' \<noteq> []" (is ?g9) 
proof -
  let ?ppg = "primitive_part g" 
  from ret' have lc: "abs (lead_coeff g) < p^l" by (auto split: if_splits)
  from ret' obtain rest where rest: "div_int_poly f (primitive_part g) = Some rest" 
    by (auto split: if_splits option.splits)
  from ret'[unfolded this] div_int_then_rqp[OF this] lc
  have out [simp]: "h = ?ppg" "gs' = filter (\<lambda> gi. \<not> p.dvdm gi ?ppg) gs" 
    "f' = rest" "b' = lead_coeff rest"
   and f: "f = ?ppg * rest" by auto
  with div_int_then_rqp[OF rest] show ?g1 ?g3 by auto
  with f0 have h0: "h \<noteq> 0" by auto
  let ?c = "content g" 
  from g0 have ct0: "?c \<noteq> 0" by auto
  have "\<bar>?c\<bar> \<le> \<bar>lead_coeff g\<bar>" by (rule content_le_lead_coeff)
  also have "\<dots> < p^l" by fact
  finally have ct_pl: "\<bar>?c\<bar> < p^l" .
  from ug have "pl.dvdm u (smult ?c ?ppg)" by simp
  from poly_mod_dvd_drop_smult[OF u p ct0 ct_pl this]
  have "p.dvdm u h" by simp
  with dvdm_power[of h] f
  show uh: "pl.dvdm u h" by (auto simp: dvd_def)
  have "content_free h" using h0 unfolding out by simp
  note irr_con = irreducible_content_free_connect[OF this]
  from f have hf: "h dvd f" by (auto intro:dvdI)
  have degh: "degree h > 0"
    by (metis d_def deg deg_u dj' hf le_neq_implies_less not_less0 uh neq0_conv)
  show irr_h: ?g2
  proof (fold irr_con, intro irreducible\<^sub>dI degh)
    fix q r
    assume deg_q: "degree q > 0" "degree q < degree h"
      and deg_r: "degree r > 0" "degree r < degree h"
      and h: "h = q * r"
    then have g_qr: "primitive_part g = q * r" by auto
    then have "r dvd h" by auto
    with g_qr dvd_trans[OF _ hf] have 1: "q dvd f" "r dvd f" by auto
    from deg_g_j deg_q deg_r have qj': "degree q < j'" and rj': "degree r < j'" by auto
    from prime_u[OF uh[unfolded out g_qr] hf[unfolded h]] have "pl.dvdm u q \<or> pl.dvdm u r" .
    with 1 qj' rj' show False
      by (elim disjE, auto dest!: deg)
  qed
  show deg_h: ?g6 using deg deg_g_j g_def hf le_less_Suc_eq uh degree_primitive_part by force
  show ?g7 unfolding out 
    by (rule length_filter_less[of u], insert pl_dvdm_imp_p_dvdm[OF uh] u_gs, auto)
  show ?g8 by auto
  from f out have fh: "f = h * f'" and gs': "gs' = [gi \<leftarrow> gs. \<not> p.dvdm gi h]" by auto
  note [simp del] = out
  let ?fs = "filter (\<lambda>gi. p.dvdm gi h) gs" 
  have part: "partition (\<lambda>gi. p.dvdm gi h) gs = (?fs, gs')" 
    unfolding gs' by (auto simp: o_def)
  from p.unique_factorization_m_factor_partition[OF l0 f_gs fh cop sf part]
  show uf: "pl.unique_factorization_m f' (lead_coeff f', mset gs')" by auto
  show ?g9
  proof
    assume "gs' = []" 
    with pl.unique_factorization_m_imp_factorization[OF uf, unfolded pl.factorization_m_def]
    have "pl.Mp f' = pl.Mp (smult (lead_coeff f') 1)" by auto
    from arg_cong[OF this, of degree] pl.degree_m_le[of "smult (lead_coeff f') 1"] 
    have "pl.degree_m f' = 0" by simp 
    also have "pl.degree_m f' = degree f'" 
    proof (rule poly_mod.degree_m_eq[OF _ pl.m1])
      have "coprime (lead_coeff f') p" 
        by (rule  p.coprime_lead_coeff_factor[OF p.prime cop[unfolded fh]])
      hence "gcd_class.coprime (lead_coeff f') p" by auto
      thus "lead_coeff f' mod p ^ l \<noteq> 0" using l0 p.prime by fastforce
    qed
    finally have degf': "degree f' = 0" by auto
    from content_f[unfolded fh content_mult] have "content f' * content h = 1" by (simp add: ac_simps)
    from pos_zmult_eq_1_iff_lemma[OF this] have "content f' = 1" using content_ge_0_int[of f'] by auto
    with degree0_coeffs[OF degf'] have f': "f' = 1 \<or> f' = -1" by auto
    with \<open>irreducible h\<close> fh have irr_f: "irreducible f" by auto
    have "degree f = j'" using hf irr_h deg_h
      using irr_f \<open>n \<equiv> degree f\<close> degh j'n not_irreducibleI by blast
    thus "False" using j'n by auto    
  qed
qed
end
  
subsubsection \<open>Outer loop\<close>

interpretation LLL d .

lemma LLL_reconstruction_inner_None_upt_j':
  assumes ij: "\<forall>i\<in>{d+1..j}. LLL_reconstruction_inner p (p^l) gs f u i = None" 
    and dj: "d<j" and "j\<le>n"
  shows "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
  using assms
proof (induct j)
  case (Suc j)
  show ?case 
  proof (rule LLL_reconstruction_inner_complete)
    show "\<And>factor2. pl.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
    proof (cases "d = j")
       case False
       show "\<And>factor2. pl.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
         by (rule Suc.hyps, insert Suc.prems False, auto)
     next
       case True
       then show "\<And>factor2. pl.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
         using degree_factor_ge_degree_u by auto
    qed
  qed (insert Suc.prems, auto)
qed auto

corollary LLL_reconstruction_inner_None_upt_j:
  assumes ij: "\<forall>i\<in>{d+1..j}. LLL_reconstruction_inner p (p^l) gs f u i = None" 
    and dj: "d\<le>j" and jn: "j\<le>n"
  shows "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
proof (cases "d=j")
  case True
  then show "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> d = j \<Longrightarrow> j \<le> degree factor" 
    using degree_factor_ge_degree_u by auto 
next
  case False
  hence dj2: "d<j" using dj by auto
  then show "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> d \<noteq> j \<Longrightarrow> j \<le> degree factor" 
    using LLL_reconstruction_inner_None_upt_j'[OF ij dj2 jn] by auto
qed

lemma LLL_reconstruction_inner_all_None_imp_irreducible:
  assumes i: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p (p^l) gs f u i = None"
  shows "irreducible f" 
proof - 
  obtain factor 
    where irreducible_factor: "irreducible\<^sub>d factor" 
      and dvdp_u_factor: "p.dvdm u factor" and factor_dvd_f: "factor dvd f"
    using exists_reconstruction by blast
  have dvdpl_u_factor: "pl.dvdm u factor" using dvdm_power[OF factor_dvd_f] dvdp_u_factor by auto
  have f0: "f \<noteq> 0" using n0 by auto
  have deg_factor1: "degree u \<le> degree factor" 
    by (rule degree_factor_ge_degree_u[OF dvdpl_u_factor factor_dvd_f])
  hence factor_not0: "factor \<noteq> 0" using d0 by auto
  hence deg_factor2: "degree factor \<le> degree f" using divides_degree[OF factor_dvd_f] f0 by auto
  have content_factor: "content factor = 1"
    using content_dvd_1 content_f factor_dvd_f by blast
  let ?j = "degree factor"  
  show ?thesis
  proof (cases "degree factor = degree f")
    case True    
    have "primitive_part f = factor \<or> - primitive_part f = factor"
    proof (rule primitive_part_eq_irreducible[OF f0])      
      have "(gcd f factor) = normalize factor" by (unfold gcd_proj2_iff, rule factor_dvd_f)      
      thus "0 < degree (gcd f factor)" using deg_factor1 d0 by auto
      show "irreducible factor" 
        using irreducible_factor content_factor irreducible_content_free_connect by auto
      show "degree f \<le> degree factor" using True by auto
    qed
    hence f_factor: "f = factor \<or> -f = factor" using primitive_part_prim[OF content_f] by simp            
    show ?thesis
    proof (cases "f = factor")
      case True
      then show ?thesis using irreducible_factor irreducible_content_free_connect content_f by auto
    next
      case False
      hence "-f = factor" using f_factor by simp
      then show ?thesis 
        using irreducible_factor irreducible_content_free_connect content_f irreducible_uminus
        by (metis content_free_iff_content_eq_1 content_uminus)
    qed        
  next
    case False
    hence Suc_j: "Suc ?j \<le> degree f" using deg_factor2 by auto
    have "Suc ?j \<le> degree factor"
    proof (rule LLL_reconstruction_inner_None_upt_j[OF _ _ _ dvdpl_u_factor factor_dvd_f])
      show "d \<le> Suc ?j" using deg_factor1 by auto
      show "\<forall>i\<in>{d + 1..(Suc ?j)}. LLL_reconstruction_inner p (p ^ l) gs f u i = None"
        using Suc_j i by auto
      show "Suc ?j \<le> n" using Suc_j by simp
    qed
    then show ?thesis by auto
  qed
qed

lemma irreducible_imp_LLL_reconstruction_inner_all_None:
  assumes irr_f: "irreducible f"
  shows "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p (p^l) gs f u i = None"   
proof (rule ccontr)
  let ?LLL_inner = "\<lambda>i. LLL_reconstruction_inner p (p ^ l) gs f u i"
  let ?G ="{j. j \<in> {d + 1..n} \<and> ?LLL_inner j \<noteq> None}"
  assume "\<not> (\<forall>i\<in>{d + 1..n}. ?LLL_inner i = None)"
  hence G_not_empty: "?G \<noteq> {}" by auto
  define j where "j = Min ?G"
  have j_in_G: "j \<in> ?G" by (unfold j_def, rule Min_in[OF _ G_not_empty], simp)
  hence j: "j \<in> {d + 1..n}" and LLL_not_None: "?LLL_inner j \<noteq> None" using j_in_G by auto
  have "\<forall>i\<in>{d+1..<j}. ?LLL_inner i = None"
  proof (rule ccontr)
    assume "\<not> (\<forall>i\<in>{d + 1..<j}. ?LLL_inner i = None)"
    from this obtain i where i: "i \<in> {d + 1..<j}" and LLL_i: "?LLL_inner i \<noteq> None" by auto
    hence iG: "i \<in> ?G" using j_def G_not_empty by auto
    have "i<j" using i by auto
    moreover have "j\<le>i" using iG j_def by auto
    ultimately show False by linarith    
  qed
  hence all_None: "\<forall>i\<in>{d+1..j-1}. ?LLL_inner i = None" by auto
  obtain gs' b' f' factor where LLL_inner_eq: "?LLL_inner j = Some (gs', b', f', factor)" 
    using LLL_not_None by force
  have Suc_j1_eq: "Suc (j - 1) = j" using j d0 by auto
  have jn: "j - 1 < n"  using j by auto
  have dj: "d \<le> j-1" using j d0 by auto
  have degree: "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j - 1 \<le> degree factor" 
    by (rule LLL_reconstruction_inner_None_upt_j[OF all_None dj], insert jn, auto)  
  have LLL_inner_Some: "?LLL_inner (Suc (j - 1)) = Some (gs', b', f', factor)" 
    using LLL_inner_eq Suc_j1_eq by auto  
  have deg_factor: "degree factor = j-1" 
    and ff': "f = f' * factor"
    and irreducible_factor: "irreducible factor"
    using LLL_reconstruction_inner_sound[OF dj jn degree LLL_inner_Some f_gs cop sf] by (metis+)
  from ff' have factor_dvd_f: "factor dvd f" by auto
  have "\<not> irreducible f" 
  proof (rule not_irreducibleI[OF factor_dvd_f])
    show "degree factor < degree f" using deg_factor j by auto
    show "0 < degree factor" using d0 deg_factor dj by linarith
  qed
  thus False using irr_f by contradiction  
qed

lemma LLL_reconstruction_inner_all_None:
  assumes i: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p  (p^l) gs f u i = None"
  and dj: "d<j"
shows "LLL_reconstruction_inner_loop p (p^l) gs f u j = ([],1,1,f)"
  using dj                             
proof (induct j rule: LLL_reconstruction_inner_loop.induct[of f p "(p^l)" gs u])
  case (1 j)
  note hyp = "1.hyps"
  note dj = "1.prems"(1)
  show ?case 
  proof (cases "j\<le>n")
    case True note jn = True
    have step: "LLL_reconstruction_inner p (p ^ l) gs f u j = None"
      by (cases "d=j", insert  i jn dj, auto)     
    have "LLL_reconstruction_inner_loop p (p ^ l) gs f u j
      = LLL_reconstruction_inner_loop p (p ^ l) gs f u (j+1)"
      using jn step by auto
    also have "... = ([], 1, 1, f)"
      by (rule hyp[OF _ step], insert jn dj, auto simp add: jn dj)      
    finally show ?thesis .
  qed auto
qed

corollary irreducible_imp_LLL_reconstruction_inner_loop_f:
  assumes irr_f: "irreducible f" and dj: "d<j" 
shows "LLL_reconstruction_inner_loop p (p^l) gs f u j = ([],1,1,f)"
  using irreducible_imp_LLL_reconstruction_inner_all_None[OF irr_f]
  using LLL_reconstruction_inner_all_None[OF _ dj] by auto
  
lemma exists_index_LLL_reconstruction_inner_Some:
  assumes inner_loop: "LLL_reconstruction_inner_loop p (p^l) gs f u j = (gs',b',f',factor)"
    and i: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p  (p^l) gs f u i = None"
    and dj: "d<j" and jn: "j\<le>n" and f: "\<not> irreducible f"
  shows "\<exists>j'. j \<le> j' \<and> j'\<le>n \<and> d<j'
    \<and> (LLL_reconstruction_inner p (p ^ l) gs f u j' = Some (gs', b', f', factor))
    \<and> (\<forall>i\<in>{d+1..<j'}. LLL_reconstruction_inner p (p^l) gs f u i = None)"
  using inner_loop i dj jn
proof (induct j rule: LLL_reconstruction_inner_loop.induct[of f p "(p^l)" gs u])
  case (1 j)
  note hyp = "1.hyps"  
  note 1 = "1.prems"(1)
  note 2 = "1.prems"(2)
  note dj = "1.prems"(3)
  note jn = "1.prems"(4)
  show ?case
  proof (cases "LLL_reconstruction_inner p (p ^ l) gs f u j = None")
    case True
    show ?thesis
    proof (cases "j=n")
      case True note j_eq_n = True
      show ?thesis
      proof (cases "LLL_reconstruction_inner p (p ^ l) gs f u n = None")
        case True
        have i2: "\<forall>i\<in>{d + 1..n}. LLL_reconstruction_inner p (p ^ l) gs f u i = None" 
          using 2 j_eq_n True by auto
        have "irreducible f"
          by(rule LLL_reconstruction_inner_all_None_imp_irreducible[OF i2])
        thus ?thesis using f by simp
      next
        case False
        have "LLL_reconstruction_inner p (p ^ l) gs f u n = Some (gs', b', f', factor)" 
          using False 1 j_eq_n by auto
        moreover have "\<forall>i\<in>{d + 1..<n}. LLL_reconstruction_inner p (p ^ l) gs f u i = None" 
          using 2 j_eq_n by simp
        moreover have "d < n" using 1 2 jn j_eq_n
          using False  dn nat_less_le
          using d_def dj by auto
        ultimately show ?thesis using j_eq_n by fastforce
      qed    
    next
      case False
      have "\<exists>j'\<ge>j + 1. j' \<le> n \<and> d < j' \<and>
                 LLL_reconstruction_inner p (p ^ l) gs f u j' = Some (gs', b', f', factor) \<and>
                 (\<forall>i\<in>{d + 1..<j'}. LLL_reconstruction_inner p (p ^ l) gs f u i = None)"
      proof (rule hyp)
        show "\<not> degree f < j" using jn by auto
        show "LLL_reconstruction_inner p (p ^ l) gs f u j = None" using True by auto
        show "LLL_reconstruction_inner_loop p (p ^ l) gs f u (j + 1) = (gs', b', f', factor)" 
          using 1 True jn by auto
        show "\<forall>i\<in>{d + 1..<j + 1}. LLL_reconstruction_inner p (p ^ l) gs f u i = None"        
          by (metis "2" One_nat_def True add.comm_neutral add_Suc_right atLeastLessThan_iff 
              le_neq_implies_less less_Suc_eq_le)      
        show "d < j + 1" using dj by auto
        show " j + 1 \<le> n" using jn False by auto
      qed
      from this obtain j' where a1: "j'\<ge>j + 1" and a2: "j' \<le> n" and a3: "d < j'"
        and a4: "LLL_reconstruction_inner p (p ^ l) gs f u j' = Some (gs', b', f', factor)"
        and a5: "(\<forall>i\<in>{d + 1..<j'}. LLL_reconstruction_inner p (p ^ l) gs f u i = None)" by auto
      moreover have "j'\<ge>j" using a1 by auto
      ultimately show ?thesis by fastforce
    qed
  next
    case False    
    have 1: "LLL_reconstruction_inner p (p ^ l) gs f u j = Some (gs', b', f', factor)" 
      using False 1 jn by auto
    moreover have 2: "(\<forall>i\<in>{d + 1..<j}. LLL_reconstruction_inner p (p ^ l) gs f u i = None)" 
      by (rule 2)
    moreover have 3: "j \<le> n" using jn by auto
    moreover have 4: "d < j" using 2 False dj jn
      using le_neq_implies_less by fastforce
    ultimately show ?thesis by auto
  qed
qed  

(* TODO: move *)
lemma unique_factorization_m_1: "pl.unique_factorization_m 1 (1, {#})"
proof (intro pl.unique_factorization_mI)
  fix d gs
  assume pl: "pl.factorization_m 1 (d,gs)" 
  from pl.factorization_m_degree[OF this] have deg0: "\<And> g. g \<in># gs \<Longrightarrow> pl.degree_m g = 0" by auto
  {
    assume "gs \<noteq> {#}" 
    then obtain g hs where gs: "gs = {# g #} + hs" by (cases gs, auto)
    with pl have *: "pl.irreducible\<^sub>d_m (pl.Mp g)" 
      "monic (pl.Mp g)" by (auto simp: pl.factorization_m_def)
    with deg0[of g, unfolded gs] have False by (auto simp: pl.irreducible\<^sub>d_m_def)
  }
  hence "gs = {#}" by auto
  with pl show "pl.Mf (d, gs) = pl.Mf (1, {#})" by (cases "d = 0", 
    auto simp: pl.factorization_m_def pl.Mf_def pl.Mp_def)
qed (auto simp: pl.factorization_m_def)

lemma LLL_reconstruction_inner_loop_j_le_n:
  assumes ret: "LLL_reconstruction_inner_loop p (p^l) gs f u j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p  (p^l) gs f u i = None"
    and n: "n = degree f"
    and jn: "j \<le> n"
    and dj: "d < j"
  shows "f = f' * factor" (is "?g1")
    and "irreducible factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4")
    and "pl.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "gs' = [] \<longrightarrow> f' = 1" (is ?g10)
  using ret ij jn dj
proof (atomize(full), induct j)
  case 0
  then show ?case using deg_u by auto
next
  case (Suc j)
  have ij: "\<forall>i\<in>{d+1..j}. LLL_reconstruction_inner p (p^l) gs f u i = None" 
    using Suc.prems by auto  
  have dj: "d \<le> j" using Suc.prems by auto
  have jn: "j<n" using Suc.prems by auto
  have deg: "Suc j \<le> degree f" using Suc.prems by auto
  have c: "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j \<le> degree factor" 
    by (rule LLL_reconstruction_inner_None_upt_j[OF ij dj], insert n jn, auto)
  have 1: "LLL_reconstruction_inner_loop p (p ^ l) gs f u (Suc j) = (gs', b', f', factor)"
    using Suc.prems by auto
  show ?case
  proof (cases "LLL_reconstruction_inner p (p ^ l) gs f u (Suc j) = None")
    case False
    have LLL_rw: "LLL_reconstruction_inner p (p ^ l) gs f u (Suc j) = Some (gs', b', f', factor)"
      using False deg Suc.prems by auto
    show ?thesis using LLL_reconstruction_inner_sound[OF dj jn c LLL_rw f_gs cop sf] by fastforce
  next    
    case True note Suc_j_None = True
    show ?thesis
    proof (cases "d = j")
      case False
      have nj: "j \<le> degree f" using Suc.prems False by auto
      moreover have dj2: "d < j" using Suc.prems False by auto
      ultimately show ?thesis using Suc.prems Suc.hyps by fastforce
    next
      case True note d_eq_j = True
      show ?thesis
      proof (cases "irreducible f")
        case True
        have pl_Mp_1: "pl.Mp 1 = 1" by auto
        have d_Suc_j: "d < Suc j" using Suc.prems by auto
        have "LLL_reconstruction_inner_loop p (p ^ l) gs f u (Suc j) = ([],1,1,f)" 
          by (rule irreducible_imp_LLL_reconstruction_inner_loop_f[OF True d_Suc_j])
        hence result_eq: "([],1,1,f) = (gs', b', f', factor)" using Suc.prems by auto
        moreover have thesis1: "pl.dvdm u factor" using uf result_eq by auto
        moreover have thesis2: "f' = pl.Mp (Polynomial.smult b' (prod_list gs'))" 
          using result_eq pl_Mp_1 by auto
        ultimately show ?thesis using True by (auto simp: unique_factorization_m_1)
      next
        case False note irreducible_f = False
        have "\<exists>j'. Suc j \<le> j' \<and> j'\<le>n \<and> d<j'
        \<and> (LLL_reconstruction_inner p (p ^ l) gs f u j' = Some (gs', b', f', factor))
        \<and> (\<forall>i\<in>{d+1..<j'}. LLL_reconstruction_inner p (p^l) gs f u i = None)"
        proof (rule exists_index_LLL_reconstruction_inner_Some[OF _ _ _ _ False])        
          show "LLL_reconstruction_inner_loop p (p ^ l) gs f u (Suc j) = (gs', b', f', factor)" 
            using Suc.prems by auto       
          show "\<forall>i \<in> {d + 1..<Suc j}. LLL_reconstruction_inner p (p ^ l) gs f u i = None" 
            using Suc.prems by auto
          show "Suc j \<le> n" using jn by auto
          show "d < Suc j " using Suc.prems by auto
        qed
        from this obtain a where da: "d < a" and an: "a \<le> n" and ja: "j \<le> a"
          and a1: "LLL_reconstruction_inner p (p ^ l) gs f u a = Some (gs', b', f', factor)"
          and a2: "\<forall>i\<in>{d+1..<a}. LLL_reconstruction_inner p (p^l) gs f u i = None" by auto
        define j' where j'[simp]: "j'\<equiv>a-1"
        have dj': "d \<le> j'" using da by auto
        have j': "j' \<noteq> 0" using dj' d0 by auto
        hence j'n: "j' < n" using an by auto
        have LLL: "LLL_reconstruction_inner p (p ^ l) gs f u (Suc j') = Some (gs', b', f', factor)" 
          using a1 j' by auto
        have prev_None: "\<forall>i\<in>{d+1..j'}. LLL_reconstruction_inner p (p^l) gs f u i = None" 
          using a2 j' by auto
        have Suc_rw: "Suc (j'- 1) = j'" using j' by auto
        have c: "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> Suc (j' - 1) \<le> degree factor"        
          by (rule LLL_reconstruction_inner_None_upt_j, insert dj' Suc_rw j'n prev_None, auto)
        hence c2: "\<And>factor. pl.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j' \<le> degree factor"
          using j' by force
        show ?thesis using LLL_reconstruction_inner_sound[OF dj' j'n c2 LLL f_gs cop sf] by fastforce
      qed
    qed
  qed
qed

lemma LLL_reconstruction_inner_loop_j_ge_n:
  assumes ret: "LLL_reconstruction_inner_loop p (p^l) gs f u j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p  (p^l) gs f u i = None"
    and dj: "d < j"
    and jn: "j>n"
  shows "f = f' * factor" (is "?g1")
    and "irreducible factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4") 
    and "pl.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "f' = 1" (is ?g10)
proof -
  have "LLL_reconstruction_inner_loop p (p^l) gs f u j = ([],1,1,f)" using jn by auto
  hence gs': "gs'=[]" and b': "b'=1" and f': "f' = 1" and factor: "factor = f" using ret by auto
  have "irreducible f"
    by (rule LLL_reconstruction_inner_all_None_imp_irreducible[OF ij])
  thus ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10 using f' factor b' gs' uf 
    by (auto simp: unique_factorization_m_1)
qed

lemma LLL_reconstruction_inner_loop:
  assumes ret: "LLL_reconstruction_inner_loop p (p^l) gs f u j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p  (p^l) gs f u i = None"
    and n: "n = degree f"
    and dj: "d < j"
  shows "f = f' * factor" (is "?g1")
    and "irreducible factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4") 
    and "pl.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "gs' = [] \<longrightarrow> f' = 1" (is ?g10)
proof (atomize(full),(cases "j>n"; intro conjI))
  case True
  have ij2: "\<forall>i\<in>{d + 1..n}. LLL_reconstruction_inner p (p ^ l) gs f u i = None" 
    using ij True by auto
  show ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10
    using LLL_reconstruction_inner_loop_j_ge_n[OF ret ij2 dj True] by blast+
next
  case False
  hence jn: "j\<le>n" by simp
  show ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10
    using LLL_reconstruction_inner_loop_j_le_n[OF ret ij n jn dj] by blast+
qed
end

lemma LLL_reconstruction'':
  assumes 1: "LLL_reconstruction'' p (p^l) gs b f G = G'"
    and irreducible_G: "\<And>factor. factor \<in> set G \<Longrightarrow> irreducible factor" 
    and 3: "F = f * prod_list G"
    and 4: "pl.unique_factorization_m f (lead_coeff f, mset gs)"
    and 5: "gs \<noteq> []"
    and 6: "\<And> gi. gi \<in> set gs \<Longrightarrow> pl.Mp gi = gi"
    and 7: "\<And> gi. gi \<in> set gs \<Longrightarrow> p.irreducible\<^sub>d_m gi" 
    and 8: "p.square_free_m f" 
    and 9: "coprime (lead_coeff f) p" 
    and sf_F: "square_free F" 
  shows "(\<forall>g \<in> set G'. irreducible g) \<and> F = prod_list G'"
  using 1 irreducible_G 3 4 5 6 7 8 9
proof (induction gs arbitrary: b f G G' rule: length_induct)
  case (1 gs)  
  note LLL_f' = "1.prems"(1)  
  note irreducible_G = "1.prems"(2)
  note F_f_G = "1.prems" (3)
  note f_gs_factor = "1.prems" (4)
  note gs_not_empty = "1.prems" (5)
  note norm = "1.prems"(6)
  note irred_p = "1.prems"(7)
  note sf = "1.prems"(8)
  note cop = "1.prems"(9)
  obtain u where choose_u_result: "choose_u gs = u" by auto
  from choose_u_member[OF  gs_not_empty, unfolded choose_u_result]
  have u_gs: "u \<in> set gs" by auto
  define u' d n where "u' = pl.inv_Mp2 ((p^l) div 2) (pl.Mp (smult b u))"
    and [simp]: "d = degree u"
    and [simp]: "n = degree f"
  obtain gs' b' h factor where inner_loop_result: 
    "LLL_reconstruction_inner_loop p (p^l) gs f u (d+1) = (gs',b',h,factor)"
    by (metis prod_cases4)
  have a1: 
    "LLL_reconstruction_inner_loop p (p ^ l) gs f u (d+1) = (gs', b', h, factor)" 
    using inner_loop_result by auto
  have a2: 
    "\<forall>i\<in>{degree u + 1..<(d+1)}. LLL_reconstruction_inner p (p ^ l) gs f u i = None"
    by auto
  have "LLL_reconstruction'' p (p^l) gs b f G = LLL_reconstruction'' p (p^l) gs' b' h (factor # G)" 
    unfolding LLL_reconstruction''.simps[of p "(p^l)" gs] using gs_not_empty
    unfolding Let_def using choose_u_result u'_def d_def inner_loop_result by auto
  hence LLL_eq: "LLL_reconstruction'' p (p^l) gs' b' h (factor # G) = G'" using LLL_f' by auto
  from pl.unique_factorization_m_imp_factorization[OF f_gs_factor, 
    unfolded pl.factorization_m_def] norm
  have f_gs: "pl.eq_m f (smult (lead_coeff f) (prod_mset (mset gs)))" and 
    mon: "g \<in> set gs \<Longrightarrow> monic g" and irred: "g \<in> set gs \<Longrightarrow> pl.irreducible\<^sub>d_m g" for g by auto
  {
    from split_list[OF u_gs] obtain gs1 gs2 where gs: "gs = gs1 @ u # gs2" by auto
    from f_gs[unfolded gs] have "pl.dvdm u f" unfolding pl.dvdm_def
      by (intro exI[of  _ "smult (lead_coeff f) (prod_mset (mset (gs1 @ gs2)))"], auto)
  } note pl_uf = this
  have monic_u: "monic u" using mon[OF u_gs] .
  have irred_d_u: "p.irreducible\<^sub>d_m u" using irred_p[OF u_gs] by auto
  have degree_m_u: "p.degree_m u = degree u" using monic_u by simp
  have degree_u[simp]: "0 < degree u" 
    using p.irreducible\<^sub>d_mD(1)[OF irred_d_u] unfolding degree_m_u .
  have irred_u: "p.irreducible_m u" using irred_d_u by auto
  have deg_u_d: "degree u < d + 1" by auto 
  from F_f_G have f_dvd_F: "f dvd F" by auto
  from square_free_factor[OF f_dvd_F sf_F] have sf_f: "square_free f" . 
  have n_def': "n \<equiv> degree f" by auto
  from norm have norm_map: "map pl.Mp gs = gs" by (induct gs, auto)
  have length_less: "length gs' < length gs" 
    and irreducible_factor: "irreducible factor"
    and h_dvd_f: "h dvd f"
    and f_h_factor: "f = h * factor" 
    and h_eq: "pl.unique_factorization_m h (b', mset gs')"
    and gs'_gs: "set gs' \<subseteq> set gs"
    and b': "b' = lead_coeff h" 
    and h1: "gs' = [] \<longrightarrow> h = 1"
    using LLL_reconstruction_inner_loop[OF degree_u monic_u irred_u pl_uf f_dvd_F n_def' 
      f_gs_factor cop sf sf_f u_gs norm_map
      a1 a2 n_def deg_u_d] 
      gs_not_empty
    by metis+
  have F_h_factor_G: "F = h * prod_list (factor # G)"
    using F_f_G f_h_factor by auto
  hence h_dvd_F: "h dvd F" using f_dvd_F dvd_trans by auto
  have irreducible_factor_G: "\<And> x. x \<in> set (factor # G) \<Longrightarrow> irreducible x"
    using irreducible_factor irreducible_G by auto
  from p.coprime_lead_coeff_factor[OF \<open>prime p\<close> cop[unfolded f_h_factor]] 
  have cop': "coprime (lead_coeff h) p" by auto
  have lc': "lead_coeff (smult (lead_coeff h) (prod_list gs')) = lead_coeff h" 
    by (insert gs'_gs, auto intro!: monic_prod_list intro: mon)
  have lc: "lead_coeff (pl.Mp (smult (lead_coeff h) (prod_list gs'))) = pl.M (lead_coeff h)"
  proof (subst pl.degree_m_eq_lead_coeff[OF pl.degree_m_eq[OF _ pl.m1]]; unfold lc')
    show "lead_coeff h mod p^l \<noteq> 0" using p.coprime_exp_mod[OF cop' l0] by auto
  qed auto
  have uh: "pl.unique_factorization_m h (lead_coeff h, mset gs')" using h_eq unfolding b' .
  from p.square_free_m_factor[OF sf[unfolded f_h_factor]] have sf': "p.square_free_m h" by auto
  show ?case
  proof (cases "gs' \<noteq> []")
    case gs'_not_empty: True 
    show ?thesis 
      by (rule "1.IH"[rule_format, OF length_less LLL_eq irreducible_factor_G F_h_factor_G 
        uh gs'_not_empty norm irred_p sf' cop'], insert gs'_gs, auto)
  next
    case False
    have pl_ge0: "p^l > 0" using p1 by auto
    have G'_eq: "G' = factor # G" using LLL_eq False using LLL_reconstruction''.simps by auto
    have condition1: "(\<forall>a\<in>set G'. irreducible a)" using irreducible_factor_G G'_eq by auto
    have h_eq2: "pl.Mp h = pl.Mp [:b':]" using h_eq False 
      unfolding pl.unique_factorization_m_alt_def pl.factorization_m_def by auto
    have Mp_const_rw[simp]: "pl.Mp [:b':] = [:b' mod p^l:]" using pl.Mp_const_poly by blast
    have condition2: "F = prod_list G'" using h1 False f_h_factor G'_eq F_h_factor_G by auto
    show ?thesis using condition1 condition2 by auto
  qed
qed

context
  fixes gs :: "int poly list" 
  assumes gs_hen: "berlekamp_hensel p l F = gs" 
   and cop: "coprime (lead_coeff F) p" 
   and sf: "poly_mod.square_free_m p F" 
   and sf_F: "square_free F" 
begin

lemma gs_not_empty: "gs \<noteq> []"
proof (rule ccontr, simp)
  assume gs: "gs = []"
  obtain c fs where c_fs: "finite_field_factorization_int p F = (c, fs)" by force
  have "sort (map degree fs) = sort (map degree gs)" 
    by (rule p.berlekamp_hensel_main(2)[OF _ gs_hen cop sf c_fs], simp add: l0)    
  hence fs_empty: "fs = []" using gs by (cases fs, auto)
  hence fs: "mset fs = {#}" by auto
  have "p.unique_factorization_m F (c, mset fs)" and c: "c \<in> {0..<p}"
    using p.finite_field_factorization_int[OF sf c_fs] by auto
  hence "p.factorization_m F (c, mset fs)"
    using p.unique_factorization_m_imp_factorization by auto    
  hence eq_m_F: "p.eq_m F [:c:]" unfolding fs p.factorization_m_def by auto
  hence "0 = p.degree_m F" by (simp add: p.Mp_const_poly)
  also have "... = degree F" by (rule p.degree_m_eq[OF _ p1], insert cop p1, auto)
  finally have "degree F = 0" ..
  thus False using N0 by simp
qed

lemma reconstruction_of_algorithm_16_22:   
  assumes 1: "reconstruction_of_algorithm_16_22 p (p^l) gs F = G"
  shows "(\<forall>g\<in>set G. irreducible g) \<and> F = prod_list G"
proof -
  note * = p.berlekamp_hensel_unique[OF cop sf gs_hen l0]
  obtain c fs where "finite_field_factorization_int p F = (c, fs)" by force
  from p.berlekamp_hensel_main[OF l0 gs_hen cop sf this]
  show ?thesis
    using 1 unfolding reconstruction_of_algorithm_16_22_def Let_def
    by (intro LLL_reconstruction''[OF _ _ _ _ gs_not_empty], insert * sf sf_F cop, auto)
qed
end
end

text \<open>fix code equation for @{const linf_norm_poly}\<close>
definition "new_zero = 0" 
lemma linf_norm_poly_code[code]: "linf_norm_poly f = max_list (map abs (coeffs f) @ [new_zero])"
  unfolding new_zero_def linf_norm_poly_def ..

subsubsection \<open>Final statement\<close>
lemma factorization_algorithm_16_22:
  assumes res: "factorization_algorithm_16_22 f = G"
  and sff: "square_free f"
  and cf: "content f = 1" 
  and deg: "degree f > 0" 
  shows "(\<forall>g\<in>set G. irreducible g) \<and> f = prod_list G"
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where fff: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded factorization_algorithm_16_22_def Let_def, folded p_def,
    unfolded fff split, folded]
  from suitable_prime_bz[OF sff refl]
  have prime: "prime p" and cop: "coprime ?lc p" and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  note res
  from prime interpret poly_mod_prime p by unfold_locales
  define K where "K = 2 ^ (5 * degree f * degree f) *
            (int (degree f + 1) * (\<parallel>f\<parallel>\<^sub>\<infinity>)\<^sup>2) ^ (2 * degree f)"
  define N where "N = sqrt_int_ceiling K" 
  have K0: "K \<ge> 0" unfolding K_def by auto
  have N0: "N \<ge> 0" unfolding N_def sqrt_int_ceiling using K0 
    by (smt of_int_nonneg real_sqrt_ge_0_iff zero_le_ceiling)
  define n where "n = find_exponent p N" 
  note res = res[folded n_def[unfolded N_def K_def]]
  note n = find_exponent[OF m1, of N, folded n_def]
  note bh = berlekamp_and_hensel_separated[OF cop sf refl fff n(2)]
  note res = res[folded bh(1)]
  show ?thesis
  proof (rule reconstruction_of_algorithm_16_22[OF prime cf deg _ refl cop sf sff res])
    from n(1) have "N \<le> p ^ n" by simp
    hence *: "N^2 \<le> (p^n)^2" 
      by (intro power_mono N0, auto)        
    show "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) \<le> (p ^ n)\<^sup>2" 
    proof (rule order.trans[OF _ *])
      have "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) = K"
        unfolding K_def B2_LLL_def by (simp add: ac_simps 
          power_mult_distrib power2_eq_square power_mult[symmetric] power_add[symmetric])
      also have "\<dots> \<le> N\<^sup>2" unfolding N_def by (rule sqrt_int_ceiling_bound[OF K0])
      finally show "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) \<le> N\<^sup>2" .
    qed
  qed
qed

end
