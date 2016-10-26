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
  fixes p :: nat
begin

function dist_degree_factorize_main :: 
  "'a mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a mod_ring poly) list 
  \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "dist_degree_factorize_main v w d res = (if v = 1 then res else if d + d > degree v 
    then (d, v) # res else let
      w' = w^p mod v;
      d' = Suc d;
      gd = gcd (w - monom 1 1) v
      in if gd = 1 then dist_degree_factorize_main v w' d' res else 
      let v' = v div gd in 
      dist_degree_factorize_main v' (w' mod v') d' ((d',gd) # res))" 
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
(*lemma degree_divisor: assumes "irreducible (f :: 'a mod_ring poly)" "degree f = d" 
  shows "f dvd ((monom 1 1)^(CARD('a)^d) - monom 1 1)" 
    "\<And> c. 1 \<le> c \<Longrightarrow> c < d \<Longrightarrow> \<not> f dvd ((monom 1 1)^(CARD('a)^c) - monom 1 1)" sorry *)
  
lemma dist_degree_factorize_main: assumes 
  p: "p = CARD('a)" and
  dist: "dist_degree_factorize_main v w d res = facts" and
  w: "w = (monom 1 1)^(p^d) mod v" and
  u: "square_free u" and  
  mon: "monic u" and
  prod: "u = v * prod_list (map snd res)" and
  deg: "\<And> f. irreducible f \<Longrightarrow> f dvd v \<Longrightarrow> degree f > d" and
  res: "\<And> f. f \<in> snd ` set res \<Longrightarrow> degree f \<noteq> 0 \<and> monic f" 
shows "u = prod_list (map snd facts) \<and> (\<forall> f \<in> snd ` set facts. degree f \<noteq> 0 \<and> monic f)" 
  using dist w prod res
proof (induct v w d res rule: dist_degree_factorize_main.induct)
  case (1 v w d res)
  note IH = 1(1-2)
  note result = 1(3)
  note w = 1(4)
  note u = 1(5)
  note res = 1(6)
  note [simp] = dist_degree_factorize_main.simps[of _ _ d] 
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
      with v result u res show ?thesis using mon_v deg_v by force
    next
      case False
      note IH = IH[OF this refl refl refl]
      let ?w = "w ^ p mod v"
      let ?g = "gcd (w - monom 1 1) v" 
      let ?v = "v div ?g" 
      let ?d = "Suc d" 
      from result[simplified] v False
      have result: "(if ?g = 1 then dist_degree_factorize_main v ?w ?d res
                  else dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res)) = facts" 
        by (auto simp: Let_def)
      from mon_v have mon_g: "monic ?g" by (metis deg_v degree_0 poly_gcd_monic)
      have ww: "?w = monom 1 1 ^ p ^ ?d mod v" unfolding w
        by (metis Groups.mult_ac(2) power.simps(2) power_mod power_mult)
      have gv: "?g dvd v" by auto
      hence gv': "v div ?g dvd v"
        by (metis dvd_def dvd_div_mult_self)
      show ?thesis
      proof (cases "?g = 1")
        case True
        with result have "dist_degree_factorize_main v ?w ?d res = facts" by auto
        from IH(1)[OF True this ww u res] show ?thesis .
      next
        case False
        with result have result: "dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res) = facts" 
          by auto 
        from False mon_g have deg_g: "degree ?g \<noteq> 0" by (simp add: monic_degree_0)
        have ww: "?w mod ?v = monom 1 1 ^ p ^ ?d mod ?v" unfolding ww
          by (rule mod_mod_cancel[OF gv']) 
        have u: "u = ?v * prod_list (map snd ((?d, ?g) # res))" 
          unfolding u by simp
        from IH(2)[OF False refl result ww u] res mon_g deg_g show ?thesis by force
      qed
    qed
  qed
qed

definition distinct_degree_factorization 
  :: "'a mod_ring poly \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "distinct_degree_factorization f = dist_degree_factorize_main f (monom 1 1) 0 []"
  
lemma distinct_degree_factorization: assumes 
  p: "p = CARD('a)" and
  dist: "distinct_degree_factorization f = facts" and
  u: "square_free f" and  
  mon: "monic f" 
shows "f = prod_list (map snd facts) \<and> (\<forall> f \<in> snd ` set facts. degree f \<noteq> 0 \<and> monic f)" 
proof -
  note dist = dist[unfolded distinct_degree_factorization_def]
  show ?thesis
  proof (cases "degree f \<le> 1")
    case False
    hence "degree f > 1" by auto
    hence *: "monom 1 (Suc 0) = monom 1 (Suc 0) mod f"
      by (simp add: degree_monom_eq mod_poly_less)
    show ?thesis
      by (rule dist_degree_factorize_main[OF p dist _ u mon], insert *, auto simp: irreducible_def)
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
      from degree1_coeffs[OF this] obtain a b where f: "f = [:b,a:]" by auto
      with mon deg have f: "f = [:b,1:]" by simp
      have [simp]: "normalize [:b,1:] = [:b,1:]" using f mon normalize_monic by blast
      from f dist have facts: "facts = [(1,f)]" 
        by (auto simp: one_poly_def Let_def dist_degree_factorize_main.simps)
      show ?thesis unfolding facts using deg mon by auto
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
  "distinct_degree_factorization_i f = dist_degree_factorize_main_i (degree_i f) f [0,1] 0 []"

end

value (code) "let p = 13;
  f = [-1188 :: int,-4716,10134,-1620,24,17394,-22689,-7527,27556,-22663,4527,11194,-18971,2063,6915,6061,21722,-13447,608,3703,-30362,-3129,-8201,11893,9528,-38073,5158,48156,6651,-4277,6369,8520,-1256,7939,-8656,1173,-5817,7657,-21107,-14769,-2166,-4054,15880,-54900,-35573,35347,-21918,-23902,19588,73906,-15292,-17127,7899,8653,-11360,-2993,36393,-21583,18287,-24736,17126,43985,6320,27964,43478,10647,-34612,-26284,-17486,-13717,-4886,-49832,-25666,-4636,-2950,-9351,40399,-2342,-32853,-53908,14371,1815,5623,35760,5934,-19865,41962,-26611,-24306,9474,63940,20662,-32253,13048,-4340,37251,-25673,-7411,-8006,37545,-8110,-74458,-1525,-20829,25734,-16061,-58023,-8544,-17473,41169,-48918,11615,10848,18971,-8812,18288,-6423,2658,17626,54192,-25805,-25171,48841,42699,-39484,8542,36003,-13854,20115,25588,63389,-1519,-27534,-15454,-47019,-27330,8994,-23074,-3418,-7024,-8902,-9321,-9627,-211,-19522,-21173,8176,-25759,13747,-14144,39574,-18304,5778,14017,-10197,-10041,15594,12412,3489,-22812,-21645,-7953,21258,-25375,-7018,18822,-7272,-13078,-21415,-10575,-7588,-4941,21569,-27211,-33027,-1902,-7592,3021,-12120,24149,2425,6516,-18145,22817,9310,20253,424,15437,-18437,-5153,10241,-9756,10999,-3530,11317,3508,1288,704,5120];
  ops = finite_field_ops p;
  modulo = mod_field_poly_i ops;
  res = distinct_degree_factorization_i p ops (map (\<lambda> x. x mod p) f)
  in res"
end
