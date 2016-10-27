theory Distinct_Degree_Factorization
imports 
  Finite_Field
  Poly_Mod_Finite_Field
  Square_Free_Factorization
  Poly_Mod_Finite_Field_Record_Based
  Berlekamp_Record_Based (* for power_poly_f_mod_i *)
  "~~/src/HOL/Library/Code_Target_Numeral"
  "~~/src/HOL/Library/Code_Char"
begin

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

(* Exercise 16 in Knuth, page 457 *)
lemma degree_divisor: assumes irr: "irreducible (f :: 'a mod_ring poly)" and deg: "degree f = d" 
  shows "f dvd (monom 1 1)^(CARD('a)^d) - monom 1 1" 
    "\<And> c. 1 \<le> c \<Longrightarrow> c < d \<Longrightarrow> \<not> f dvd (monom 1 1)^(CARD('a)^c) - monom 1 1"
proof -
  show "f dvd (monom 1 1)^(CARD('a)^d) - monom 1 1" using irr deg sorry
  fix c
  assume "1 \<le> c" "c < d" 
  show "\<not> f dvd (monom 1 1)^(CARD('a)^c) - monom 1 1" sorry
qed
  
lemma dist_degree_factorize_main: assumes 
  dist: "dist_degree_factorize_main v w d res = facts" and
  w: "w = (monom 1 1)^(CARD('a)^d) mod v" and
  sf: "square_free u" and  
  mon: "monic u" and
  prod: "u = v * prod_list (map snd res)" and
  deg: "\<And> f. irreducible f \<Longrightarrow> f dvd v \<Longrightarrow> degree f > d" and
  res: "\<And> i f. (i,f) \<in> set res \<Longrightarrow> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible g \<longrightarrow> g dvd f \<longrightarrow> degree g = i)" 
shows "u = prod_list (map snd facts) \<and> (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible g \<longrightarrow> g dvd f \<longrightarrow> degree g = i))" 
  using dist w prod res deg
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
        assume *: "(i,f) \<in> set facts" "irreducible g" "g dvd f"          
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
            hence "\<exists> k. irreducible k \<and> k dvd h" 
              using dvd_triv_left irreducible_factor by blast
            then obtain k where irr: "irreducible k" and "k dvd h" by auto
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
        assume irr: "irreducible f" and fv: "f dvd v" and "degree f = ?d" 
        from degree_divisor[OF this(1,3)]
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
          assume irr: "irreducible f" and fv: "f dvd v" 
          from fact[OF this] have "d < degree f" .
          moreover have "degree f \<noteq> ?d"
          proof
            assume "degree f = ?d" 
            from divides_degree[OF deg_d_dvd_g[OF irr fv this]] mon_v
            have "degree f \<le> degree ?g" by auto
            with irr have "degree ?g \<noteq> 0" unfolding irreducible_def by auto
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
              assume *: "irreducible g" "g dvd ?g"
              hence gv: "g dvd v" using dvd_trans[of g ?g v] by simp
              from fact[OF *(1) this] have dg: "d < degree g" .
              {
                assume "degree g > ?d"
                from degree_divisor(2)[OF *(1) refl _ this]
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
  dist: "distinct_degree_factorization f = facts" and
  u: "square_free f" and  
  mon: "monic f" 
shows "f = prod_list (map snd facts) \<and> 
  (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> 
    degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible g \<longrightarrow> g dvd f \<longrightarrow> degree g = i))" 
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
      by (rule dist_degree_factorize_main[OF dist _ u mon], insert *, auto simp: irreducible_def)
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
      show ?thesis unfolding facts
      proof (intro conjI allI impI; clarsimp)
        fix g
        assume "irreducible g" "g dvd f" 
        thus "degree g = Suc 0" using deg divides_degree[of g f] by (auto simp: irreducible_def)
      qed (insert mon deg, auto)
    qed
  qed
qed
end

context
  fixes p :: int
  and ff_ops :: "int arith_ops_record"  (* finite-fields *)
begin

partial_function (tailrec) dist_degree_factorize_main_i :: 
  "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> (nat \<times> int list) list 
  \<Rightarrow> (nat \<times> int list) list" where
  [code]: "dist_degree_factorize_main_i dv v w d res = (if v = [1] then res else if d + d > dv 
    then (dv, v) # res else let
      modulo = mod_field_poly_i ff_ops;
      w = power_poly_f_mod_i ff_ops (\<lambda> f. modulo f v) w (nat p);
      d = Suc d;
      gd = gcd_poly_i ff_ops (minus_poly_i ff_ops w [0,1]) v
      in if gd = [1] then dist_degree_factorize_main_i dv v w d res else 
      let v' = div_field_poly_i ff_ops v gd
      in dist_degree_factorize_main_i (degree_i v') v' (modulo w v') d ((d,gd) # res))" 

definition distinct_degree_factorization_i
  :: "int list \<Rightarrow> (nat \<times> int list) list" where
  "distinct_degree_factorization_i f = (if degree_i f = 1 then [(1,f)] else 
     dist_degree_factorize_main_i (degree_i f) f [0,1] 0 [])"
end

context prime_field
begin

lemma dist_degree_factorize_main_i: 
  "ff.poly_rel F f \<Longrightarrow> ff.poly_rel G g \<Longrightarrow> list_all2 (rel_prod op = ff.poly_rel) Res res 
   \<Longrightarrow> list_all2 (rel_prod op = ff.poly_rel) 
      (dist_degree_factorize_main_i p ff_ops (degree_i F) F G d Res)
      (dist_degree_factorize_main f g d res)" 
proof (induct f g d res arbitrary: F G Res rule: dist_degree_factorize_main.induct)
  case (1 v w d res V W Res)
  note simp = dist_degree_factorize_main.simps[of v w d] 
    dist_degree_factorize_main_i.simps[of p ff_ops "degree_i V" V W d]
  have v[transfer_rule]: "ff.poly_rel V v" by (rule 1)
  have w[transfer_rule]: "ff.poly_rel W w" by (rule 1)
  have res[transfer_rule]: "list_all2 (rel_prod op = ff.poly_rel) Res res" by (rule 1)
  have [transfer_rule]: "ff.poly_rel [1] 1" unfolding one_poly_def ff.poly_rel_def mod_ring_rel_def 
    by auto
  have id1: "(V = [1]) = (v = 1)" by transfer_prover
  have id2: "degree_i V = degree v" by transfer_prover
  note simp = simp[unfolded id1 id2]
  note IH = 1(1,2)
  show ?case 
  proof (cases "v = 1")
    case True
    with res show ?thesis unfolding id2 simp by simp
  next
    case False
    with id1 have "(v = 1) = False" by auto
    note simp = simp[unfolded this if_False]
    note IH = IH[OF False]
    show ?thesis
    proof (cases "degree v < d + d")
      case True
      thus ?thesis unfolding id2 simp using res v by auto
    next
      case False
      hence "(degree v < d + d) = False" by auto
      note simp = simp[unfolded this if_False]
      let ?P = "power_poly_f_mod_i ff_ops (\<lambda>f. mod_field_poly_i ff_ops f V) W (nat p)" 
      let ?G = "gcd_poly_i ff_ops (minus_poly_i ff_ops ?P [0, 1]) V" 
      let ?g = "gcd (w ^ CARD('a) mod v - monom 1 1) v" 
      define G where "G = ?G" 
      define g where "g = ?g"
      note simp = simp[unfolded Let_def, folded G_def g_def]
      note IH = IH[OF False refl refl refl]
      have [transfer_rule]: "ff.poly_rel [0,1] (monom 1 1)" unfolding ff.poly_rel_def mod_ring_rel_def 
        by (auto simp: coeffs_monom)
      have id: "w ^ CARD('a) mod v = power_poly_f_mod v w (nat p)"
        unfolding power_poly_f_mod_def by (simp add: p)
      have P[transfer_rule]: "ff.poly_rel ?P (w ^ CARD('a) mod v)" unfolding id
        by (rule power_poly_f_mod_i[OF _ w], transfer_prover)
      have g[transfer_rule]: "ff.poly_rel G g" unfolding G_def g_def by transfer_prover
      have id3: "(G = [1]) = (g = 1)" by transfer_prover
      note simp = simp[unfolded id3]
      show ?thesis
      proof (cases "g = 1")
        case True
        from IH(1)[OF this[unfolded g_def] v P res] True
        show ?thesis unfolding id2 simp by simp
      next
        case False
        have vg: "ff.poly_rel (div_field_poly_i ff_ops V G) (v div g)" by transfer_prover
        have "ff.poly_rel (mod_field_poly_i ff_ops ?P
          (div_field_poly_i ff_ops V G)) (w ^ CARD('a) mod v mod (v div g))" by transfer_prover        
        note IH = IH(2)[OF False[unfolded g_def] refl vg[unfolded G_def g_def] this[unfolded G_def g_def],
            folded g_def G_def]
        have "list_all2 (rel_prod op = ff.poly_rel) ((Suc d, G) # Res) ((Suc d, g) # res)" 
          using g res by auto
        note IH = IH[OF this]
        from False have "(g = 1) = False" by simp
        note simp = simp[unfolded this if_False]
        show ?thesis unfolding id2 simp using IH by simp
      qed
    qed
  qed
qed
      
lemma distinct_degree_factorization_i[transfer_rule]: "(ff.poly_rel ===> list_all2 (rel_prod op = ff.poly_rel)) 
  (distinct_degree_factorization_i p ff_ops) distinct_degree_factorization"
proof 
  fix F f
  assume f[transfer_rule]: "ff.poly_rel F f" 
  have id: "(degree_i F = 1) = (degree f = 1)" by transfer_prover
  note d = distinct_degree_factorization_i_def distinct_degree_factorization_def
  show "list_all2 (rel_prod op = ff.poly_rel) (distinct_degree_factorization_i p ff_ops F)
            (distinct_degree_factorization f)" 
  proof (cases "degree f = 1")
    case True
    with id f show ?thesis unfolding d by auto
  next
    case False
    from False id have "?thesis = (list_all2 (rel_prod op = ff.poly_rel) 
      (dist_degree_factorize_main_i p ff_ops (degree_i F) F [0, 1] 0 [])
      (dist_degree_factorize_main f (monom 1 1) 0 []))" unfolding d by simp    
    also have \<dots>
      by (rule dist_degree_factorize_main_i[OF f], auto simp: ff.poly_rel_def mod_ring_rel_def 
        coeffs_monom)
    finally show ?thesis .
  qed
qed


value (code) "let p = 13;
  f = [-1188 :: int,-4716,10134,-1620,24,17394,-22689,-7527,27556,-22663,4527,11194,-18971,2063,6915,6061,21722,-13447,608,3703,-30362,-3129,-8201,11893,9528,-38073,5158,48156,6651,-4277,6369,8520,-1256,7939,-8656,1173,-5817,7657,-21107,-14769,-2166,-4054,15880,-54900,-35573,35347,-21918,-23902,19588,73906,-15292,-17127,7899,8653,-11360,-2993,36393,-21583,18287,-24736,17126,43985,6320,27964,43478,10647,-34612,-26284,-17486,-13717,-4886,-49832,-25666,-4636,-2950,-9351,40399,-2342,-32853,-53908,14371,1815,5623,35760,5934,-19865,41962,-26611,-24306,9474,63940,20662,-32253,13048,-4340,37251,-25673,-7411,-8006,37545,-8110,-74458,-1525,-20829,25734,-16061,-58023,-8544,-17473,41169,-48918,11615,10848,18971,-8812,18288,-6423,2658,17626,54192,-25805,-25171,48841,42699,-39484,8542,36003,-13854,20115,25588,63389,-1519,-27534,-15454,-47019,-27330,8994,-23074,-3418,-7024,-8902,-9321,-9627,-211,-19522,-21173,8176,-25759,13747,-14144,39574,-18304,5778,14017,-10197,-10041,15594,12412,3489,-22812,-21645,-7953,21258,-25375,-7018,18822,-7272,-13078,-21415,-10575,-7588,-4941,21569,-27211,-33027,-1902,-7592,3021,-12120,24149,2425,6516,-18145,22817,9310,20253,424,15437,-18437,-5153,10241,-9756,10999,-3530,11317,3508,1288,704,5120];
  f = [12, 1];
  ops = finite_field_ops p;
  modulo = mod_field_poly_i ops;
  res = distinct_degree_factorization_i p ops (map (\<lambda> x. x mod p) f)
  in res"
end
