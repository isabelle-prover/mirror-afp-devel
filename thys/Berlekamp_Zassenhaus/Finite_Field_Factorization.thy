(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>A Combined Factorization Algorithm for Polynomials over GF(p)\<close>

subsection\<open>Type Based Version\<close>
text \<open>We combine Berlekamp's algorithm with the distinct degree factorization
  to obtain an efficient factorization algorithm for square-free polynomials in GF(p).\<close>

theory Finite_Field_Factorization
imports Berlekamp_Type_Based
  Distinct_Degree_Factorization
begin

context
assumes "SORT_CONSTRAINT('a::prime_card)"
begin

definition finite_field_factorization :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<times> 'a mod_ring poly list" where
  "finite_field_factorization f = (if f = 0 then (0,[]) else let
     a = lead_coeff f;
     u = smult (inverse a) f;
     gs = distinct_degree_factorization u;
     (irr,hs) = partition (\<lambda> (i,f). degree f = i) gs
    in (a,map snd irr @ concat (map (\<lambda> (i,g). berlekamp_monic_factorization i g) hs)))"

lemma finite_field_factorization_explicit:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and us: "finite_field_factorization f = (c,us)"
  shows "f = smult c (prod_list us) \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)"
proof (cases "f = 0")
  case False note f = this
  define g where "g = smult (inverse c) f"
  obtain gs where dist: "distinct_degree_factorization g = gs" by auto
  note us = us[unfolded finite_field_factorization_def Let_def]
  from us f have c: "c = lead_coeff f" by auto
  obtain irr hs where part: "partition (\<lambda> (i, f). degree f = i) gs = (irr,hs)" by force
  from arg_cong[OF this, of fst] have irr: "irr = filter (\<lambda> (i, f). degree f = i) gs" by auto
  from us[folded c, folded g_def, unfolded dist part split] f
  have us: "us = map snd irr @ concat (map (\<lambda>(x, y). berlekamp_monic_factorization x y) hs)" by auto
  from f c have c0: "c \<noteq> 0" by auto
  have mon_g: "monic g" unfolding g_def
    by (metis c c0 field_class.field_inverse lead_coeff_def lead_coeff_smult)
  from sf_f have sf_g: "square_free g" unfolding g_def by (simp add: c0)
  from c0 have f: "f = smult c g" unfolding g_def by auto
  from distinct_degree_factorization[OF dist sf_g mon_g]
  have g_gs: "g = prod_list (map snd gs)" 
    and same: "\<And> i f. (i, f) \<in> set gs \<Longrightarrow> factors_of_same_degree i f" by auto
  have g: "g = prod_list (map snd irr) * prod_list (map snd hs)" unfolding g_gs
    using prod_list_map_partition[OF part] .
  {
    fix f
    assume "f \<in> snd ` set irr" 
    from this[unfolded irr] obtain i where *:  "(i,f) \<in> set gs" "degree f = i" by auto
    have "f dvd f" by auto
    from factors_of_same_degreeD[OF same[OF *(1)]] this *(2) have "monic f" "irreducible f" by auto
  } note irr = this
  let ?berl = "\<lambda> hs. concat (map (\<lambda>(x, y). berlekamp_monic_factorization x y) hs)"
  have "set hs \<subseteq> set gs" using part by auto
  hence "prod_list (map snd hs) = prod_list (?berl hs)
    \<and> (\<forall> f \<in> set (?berl hs). monic f \<and> irreducible f)" 
  proof (induct hs)
    case (Cons ih hs)
    obtain i h where ih: "ih = (i,h)" by force
    have "?berl (Cons ih hs) = berlekamp_monic_factorization i h @ ?berl hs" unfolding ih by auto
    from Cons(2)[unfolded ih] have mem: "(i,h) \<in> set gs" and sub: "set hs \<subseteq> set gs" by auto
    note IH = Cons(1)[OF sub]
    from mem have "h \<in> set (map snd gs)" by force
    from square_free_factor[OF prod_list_dvd[OF this], folded g_gs, OF sf_g] have sf: "square_free h" .
    from factors_of_same_degreeD[OF same[OF mem]] have *: "degree h \<noteq> 0" "monic h" 
      "\<And> g. g dvd h \<Longrightarrow> degree g = i \<Longrightarrow> irreducible g" by auto
    from berlekamp_monic_factorization[OF sf refl *(3) *(1-2), of i]
    have berl: "prod_list (berlekamp_monic_factorization i h) = h" 
      and irr: "\<And> f. f \<in> set (berlekamp_monic_factorization i h) \<Longrightarrow> monic f \<and> irreducible f" by auto
    have "prod_list (map snd (Cons ih hs)) = h * prod_list (map snd hs)" unfolding ih by simp
    also have "prod_list (map snd hs) = prod_list (?berl hs)" using IH by auto
    finally have "prod_list (map snd (Cons ih hs)) = prod_list (?berl (Cons ih hs))" 
      unfolding ih using berl by auto
    thus ?case using IH irr unfolding ih by auto
  qed auto
  with g irr have main: "g = prod_list us \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)" unfolding us
    by auto
  thus ?thesis unfolding f using sf_g by auto
next
  case True
  with us[unfolded finite_field_factorization_def] have c: "c = 0" and us: "us = []" by auto
  show ?thesis unfolding us True c by auto
qed

lemma finite_field_factorization:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and us: "finite_field_factorization f = (c,us)"
  shows "unique_factorization Irr_Mon f (c, mset us)"
proof -
  from finite_field_factorization_explicit[OF sf_f us]
  have fact: "factorization Irr_Mon f (c, mset us)"
    unfolding factorization_def split Irr_Mon_def by (auto simp: prod_mset_prod_list)
  from sf_f[unfolded square_free_def] have "f \<noteq> 0" by auto
  from exactly_one_factorization[OF this] fact
  show ?thesis unfolding unique_factorization_def by auto
qed
end
end
