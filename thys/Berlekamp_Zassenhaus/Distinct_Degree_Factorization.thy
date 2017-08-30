(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Distinct Degree Factorization\<close>
theory Distinct_Degree_Factorization
imports 
  Finite_Field
  Polynomial_Factorization.Square_Free_Factorization 
begin

definition factors_of_same_degree :: "nat \<Rightarrow> 'a :: field poly \<Rightarrow> bool" where
  "factors_of_same_degree i f = (i \<noteq> 0 \<and> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible\<^sub>d g \<longrightarrow> g dvd f \<longrightarrow> degree g = i))" 

lemma factors_of_same_degreeD: assumes "factors_of_same_degree i f"
  shows "i \<noteq> 0" "degree f \<noteq> 0" "monic f" "g dvd f \<Longrightarrow> irreducible\<^sub>d g = (degree g = i)" 
proof -
  note * = assms[unfolded factors_of_same_degree_def]
  show i: "i \<noteq> 0" and f: "degree f \<noteq> 0" "monic f" using * by auto
  assume gf: "g dvd f" 
  with * have "irreducible\<^sub>d g \<Longrightarrow> degree g = i" by auto
  moreover
  {
    assume **: "degree g = i" "\<not> irreducible\<^sub>d g" 
    with irreducible\<^sub>d_factor[of g] i obtain h1 h2 where irr: "irreducible\<^sub>d h1" and gh: "g = h1 * h2" 
      and deg_h2: "degree h2 < degree g" by auto
    from ** i have g0: "g \<noteq> 0" by auto
    from gf gh g0 have "h1 dvd f" using dvd_mult_left by blast
    from * f this irr have deg_h: "degree h1 = i" by auto
    from arg_cong[OF gh, of degree] g0 have "degree g = degree h1 + degree h2"
      by (simp add: degree_mult_eq gh)
    with **(1) deg_h have "degree h2 = 0" by auto
    from degree0_coeffs[OF this] obtain c where h2: "h2 = [:c:]" by auto
    with gh g0 have g: "g = smult c h1" "c \<noteq> 0" by auto
    with irr **(2) irreducible\<^sub>d_smult[of c h1] have False by auto
  }
  ultimately show "irreducible\<^sub>d g = (degree g = i)" by auto
qed
  
definition "exercise_16_finished = False" 
(* Exercise 16 in Knuth, pages 457 and 682 *)
lemma degree_divisor: assumes exercise_16_finished 
  and "irreducible\<^sub>d (f :: 'a :: prime_card mod_ring poly)" "degree f = d" 
  shows "f dvd (monom 1 1)^(CARD('a)^d) - monom 1 1" 
  and "1 \<le> c \<Longrightarrow> c < d \<Longrightarrow> \<not> f dvd (monom 1 1)^(CARD('a)^c) - monom 1 1"
    using assms unfolding exercise_16_finished_def by auto

context 
  assumes "SORT_CONSTRAINT('a :: prime_card)" 
begin

function dist_degree_factorize_main :: 
  "'a mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a mod_ring poly) list 
  \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "dist_degree_factorize_main v w d res = (if v = 1 then res else if d + d > degree v 
    then (degree v, v) # res else let
      w = w^(CARD('a)) mod v;
      d = Suc d;
      gd = gcd (w - monom 1 1) v
      in if gd = 1 then dist_degree_factorize_main v w d res else 
      let v' = v div gd in 
      dist_degree_factorize_main v' (w mod v') d ((d,gd) # res))" 
  by pat_completeness auto


termination 
proof (relation "measure (\<lambda> (v,w,d,res). Suc (degree v) - d)", goal_cases) 
  case (3 v w d res x xa xb xc) 
  have "xb dvd v" unfolding 3 by auto
  hence "xc dvd v" unfolding 3 by (metis dvd_def dvd_div_mult_self)
  from divides_degree[OF this] 3
  show ?case by auto
qed auto

declare dist_degree_factorize_main.simps[simp del]
  
lemma dist_degree_factorize_main: assumes 
  ex16: exercise_16_finished and 
  dist: "dist_degree_factorize_main v w d res = facts" and
  w: "w = (monom 1 1)^(CARD('a)^d) mod v" and
  sf: "square_free u" and  
  mon: "monic u" and
  prod: "u = v * prod_list (map snd res)" and
  deg: "\<And> f. irreducible\<^sub>d f \<Longrightarrow> f dvd v \<Longrightarrow> degree f > d" and
  res: "\<And> i f. (i,f) \<in> set res \<Longrightarrow> i \<noteq> 0 \<and> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible\<^sub>d g \<longrightarrow> g dvd f \<longrightarrow> degree g = i)" 
shows "u = prod_list (map snd facts) \<and> (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> factors_of_same_degree i f)" 
  using dist w prod res deg unfolding factors_of_same_degree_def
proof (induct v w d res rule: dist_degree_factorize_main.induct)
  case (1 v w d res)
  note IH = 1(1-2)
  note result = 1(3)
  note w = 1(4)
  note u = 1(5)
  note res = 1(6)
  note fact = 1(7)
  note [simp] = dist_degree_factorize_main.simps[of _ _ d] 
  let ?x = "monom 1 1 :: 'a mod_ring poly" 
  show ?case
  proof (cases "v = 1") 
    case True
    thus ?thesis using result u mon res by auto
  next
    case False note v = this
    note IH = IH[OF this]
    have mon_prod: "monic (prod_list (map snd res))" by (rule monic_prod_list, insert res, auto)
    with mon[unfolded u] have mon_v: "monic v" by (simp add: coeff_degree_mult)
    with False have deg_v: "degree v \<noteq> 0" by (simp add: monic_degree_0)
    show ?thesis
    proof (cases "degree v < d + d")
      case True
      with result False have facts: "facts = (degree v, v) # res" by simp
      show ?thesis 
      proof (intro allI conjI impI)
        fix i f g
        assume *: "(i,f) \<in> set facts" "irreducible\<^sub>d g" "g dvd f"          
        show "degree g = i"
        proof (cases "(i,f) \<in> set res")
          case True
          from res[OF this] * show ?thesis by auto
        next
          case False
          with * facts have id: "i = degree v" "f = v" by auto
          note * = *(2-3)[unfolded id]
          from fact[OF *] have dg: "d < degree g" by auto
          from divides_degree[OF *(2)] mon_v have deg_gv: "degree g \<le> degree v" by auto
          from *(2) obtain h where vgh: "v = g * h" unfolding dvd_def by auto
          from arg_cong[OF this, of degree] mon_v have dvgh: "degree v = degree g + degree h" 
            by (metis deg_v degree_mult_eq degree_mult_eq_0) 
          with dg deg_gv dg True have deg_h: "degree h < d" by auto
          {
            assume "degree h = 0" 
            with dvgh have "degree g = degree v" by simp
          }
          moreover
          {
            assume deg_h0: "degree h \<noteq> 0" 
            hence "\<exists> k. irreducible\<^sub>d k \<and> k dvd h" 
              using dvd_triv_left irreducible\<^sub>d_factor by blast
            then obtain k where irr: "irreducible\<^sub>d k" and "k dvd h" by auto
            from dvd_trans[OF this(2), of v] vgh have "k dvd v" by auto
            from fact[OF irr this] have dk: "d < degree k" .
            from divides_degree[OF \<open>k dvd h\<close>] deg_h0 have "degree k \<le> degree h" by auto
            with deg_h have "degree k < d" by auto
            with dk have False by auto
          }
          ultimately have "degree g = degree v" by auto
          thus ?thesis unfolding id by auto
        qed
      qed (insert v mon_v deg_v u facts res, force+)        
    next
      case False
      note IH = IH[OF this refl refl refl]
      let ?p = "CARD('a)" 
      let ?w = "w ^ ?p mod v"
      let ?g = "gcd (?w - ?x) v" 
      let ?v = "v div ?g" 
      let ?d = "Suc d" 
      from result[simplified] v False
      have result: "(if ?g = 1 then dist_degree_factorize_main v ?w ?d res
                  else dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res)) = facts" 
        by (auto simp: Let_def)
      from mon_v have mon_g: "monic ?g" by (metis deg_v degree_0 poly_gcd_monic)
      have ww: "?w = ?x ^ ?p ^ ?d mod v" unfolding w
        by (metis Groups.mult_ac(2) power.simps(2) power_mod power_mult)
      have gv: "?g dvd v" by auto
      hence gv': "v div ?g dvd v"
        by (metis dvd_def dvd_div_mult_self)
      {
        fix f
        assume irr: "irreducible\<^sub>d f" and fv: "f dvd v" and "degree f = ?d" 
        from degree_divisor(1)[OF ex16 this(1,3)]
        have "f dvd ?x ^ ?p ^ ?d - ?x" by auto
        hence "f dvd (?x ^ ?p ^ ?d - ?x) mod v" using fv by (rule dvd_mod)
        also have "(?x ^ ?p ^ ?d - ?x) mod v = ?x ^ ?p ^ ?d mod v - ?x mod v" by (rule poly_mod_diff_left)
        also have "?x ^ ?p ^ ?d mod v = ?w mod v" unfolding ww by auto
        also have "\<dots> - ?x mod v = (w ^ ?p mod v - ?x) mod v" by (metis poly_mod_diff_left)
        finally have "f dvd (w^?p mod v - ?x)" using fv by (rule dvd_mod_imp_dvd)
        with fv have "f dvd ?g" by auto
      } note deg_d_dvd_g = this
      show ?thesis
      proof (cases "?g = 1")
        case True
        with result have dist: "dist_degree_factorize_main v ?w ?d res = facts" by auto
        show ?thesis 
        proof (rule IH(1)[OF True dist ww u res])
          fix f
          assume irr: "irreducible\<^sub>d f" and fv: "f dvd v" 
          from fact[OF this] have "d < degree f" .
          moreover have "degree f \<noteq> ?d"
          proof
            assume "degree f = ?d" 
            from divides_degree[OF deg_d_dvd_g[OF irr fv this]] mon_v
            have "degree f \<le> degree ?g" by auto
            with irr have "degree ?g \<noteq> 0" unfolding irreducible\<^sub>d_def by auto
            with True show False by auto
          qed
          ultimately show "?d < degree f" by auto
        qed
      next
        case False
        with result 
        have result: "dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res) = facts" 
          by auto 
        from False mon_g have deg_g: "degree ?g \<noteq> 0" by (simp add: monic_degree_0)
        have www: "?w mod ?v = monom 1 1 ^ ?p ^ ?d mod ?v" using gv'
          by (simp add: mod_mod_cancel ww)
        from square_free_factor[OF _ sf, of v] u have sfv: "square_free v" by auto
        have u: "u = ?v * prod_list (map snd ((?d, ?g) # res))" 
          unfolding u by simp
        show ?thesis
        proof (rule IH(2)[OF False refl result www u], goal_cases)
          case (1 i f)
          show ?case
          proof (cases "(i,f) \<in> set res")
            case True
            from res[OF this] show ?thesis by auto
          next
            case False
            with 1 have id: "i = ?d" "f = ?g" by auto
            show ?thesis unfolding id 
            proof (intro conjI impI allI)
              fix g
              assume *: "irreducible\<^sub>d g" "g dvd ?g"
              hence gv: "g dvd v" using dvd_trans[of g ?g v] by simp
              from fact[OF *(1) this] have dg: "d < degree g" .
              {
                assume "degree g > ?d"
                from degree_divisor(2)[OF ex16 *(1) refl _ this]
                have ndvd: "\<not> g dvd ?x ^ ?p ^ ?d - ?x" by auto 
                from *(2) have "g dvd ?w - ?x" by simp
                from this[unfolded ww]
                have "g dvd ?x ^ ?p ^ ?d mod v - ?x" .
                with gv have "g dvd (?x ^ ?p ^ ?d mod v - ?x) mod v" by (metis dvd_mod)
                also have "(?x ^ ?p ^ ?d mod v - ?x) mod v = (?x ^ ?p ^ ?d - ?x) mod v"
                  by (metis mod_diff_left_eq)
                finally have "g dvd ?x ^ ?p ^ ?d - ?x" using gv by (rule dvd_mod_imp_dvd)
                with ndvd have False by auto
              }
              with dg show "degree g = ?d" by presburger
            qed (insert mon_g deg_g, auto)
          qed
        next
          case (2 f)
          note irr = 2(1)
          from dvd_trans[OF 2(2) gv'] have fv: "f dvd v" .
          from fact[OF irr fv] have df: "d < degree f" "degree f \<noteq> 0" by auto
          {
            assume "degree f = ?d" 
            from deg_d_dvd_g[OF irr fv this] have fg: "f dvd ?g" .
            from gv have id: "v = (v div ?g) * ?g" by simp
            from sfv id have "square_free (v div ?g * ?g)" by simp
            from square_free_multD(1)[OF this 2(2) fg] have "degree f = 0" .
            with df have False by auto
          }
          with df show "?d < degree f" by presburger
        qed
      qed
    qed
  qed
qed

definition distinct_degree_factorization 
  :: "'a mod_ring poly \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "distinct_degree_factorization f = 
     (if degree f = 1 then [(1,f)] else dist_degree_factorize_main f (monom 1 1) 0 [])"
  
lemma distinct_degree_factorization: assumes 
  ex16: exercise_16_finished and
  dist: "distinct_degree_factorization f = facts" and
  u: "square_free f" and  
  mon: "monic f" 
shows "f = prod_list (map snd facts) \<and> (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> factors_of_same_degree i f)" 
proof -
  note dist = dist[unfolded distinct_degree_factorization_def]
  show ?thesis 
  proof (cases "degree f \<le> 1")
    case False
    hence "degree f > 1" and dist: "dist_degree_factorize_main f (monom 1 1) 0 [] = facts" 
      using dist by auto
    hence *: "monom 1 (Suc 0) = monom 1 (Suc 0) mod f"
      by (simp add: degree_monom_eq mod_poly_less)
    show ?thesis
      by (rule dist_degree_factorize_main[OF ex16 dist _ u mon], insert *, auto simp: irreducible\<^sub>d_def)
  next
    case True
    hence "degree f = 0 \<or> degree f = 1" by auto
    thus ?thesis
    proof 
      assume "degree f = 0" 
      with mon have f: "f = 1" using monic_degree_0 by blast
      hence "facts = []" using dist unfolding dist_degree_factorize_main.simps[of _ _ 0]
        by auto
      thus ?thesis using f by auto
    next
      assume deg: "degree f = 1" 
      hence facts: "facts = [(1,f)]" using dist by auto
      show ?thesis unfolding facts factors_of_same_degree_def
      proof (intro conjI allI impI; clarsimp)
        fix g
        assume "irreducible\<^sub>d g" "g dvd f" 
        thus "degree g = Suc 0" using deg divides_degree[of g f] by (auto simp: irreducible\<^sub>d_def)
      qed (insert mon deg, auto)
    qed
  qed
qed
end


end
