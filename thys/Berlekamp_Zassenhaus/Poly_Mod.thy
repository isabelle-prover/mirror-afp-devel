(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Polynomials in Rings and Fields\<close>

subsection \<open>Polynomials in Rings\<close>

text \<open>We use a locale to work with polynomials in some integer-modulo ring.\<close>

theory Poly_Mod
imports 
  "../Polynomial_Factorization/Square_Free_Factorization"
begin

locale poly_mod = fixes m :: "int" 
begin

definition M :: "int \<Rightarrow> int" where "M x = x mod m" 

lemma M_0[simp]: "M 0 = 0" unfolding M_def by auto

lemma M_M[simp]: "M (M x) = M x" unfolding M_def by auto

lemma M_plus[simp]: "M (M x + y) = M (x + y)" "M (x + M y) = M (x + y)" unfolding M_def by presburger+

lemma M_minus[simp]: "M (M x - y) = M (x - y)" "M (x - M y) = M (x - y)" unfolding M_def 
  by (auto simp: zdiff_zmod_left zdiff_zmod_right)

lemma M_times[simp]: "M (M x * y) = M (x * y)" "M (x * M y) = M (x * y)" unfolding M_def
  by (auto simp: zmod_simps)

lemma M_sum: "M (sum (\<lambda> x. M (f x)) A) = M (sum f A)"
proof (induct A rule: infinite_finite_induct) 
  case (insert x A)
  from insert(1-2) have "M (\<Sum>x\<in>insert x A. M (f x)) = M (f x + M ((\<Sum>x\<in>A. M (f x))))" by simp
  also have "M ((\<Sum>x\<in>A. M (f x))) = M ((\<Sum>x\<in>A. f x))" using insert by simp
  finally show ?case using insert by simp
qed auto


definition Mp :: "int poly \<Rightarrow> int poly" where "Mp = map_poly M"

lemma Mp_0[simp]: "Mp 0 = 0" unfolding Mp_def by auto

lemma Mp_coeff: "coeff (Mp f) i = M (coeff f i)" unfolding Mp_def 
  by (simp add: M_def coeff_map_poly) 

definition equivalent :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infixl "=m" 50) where
  "f =m g = (Mp f = Mp g)" 

definition dvdm :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infix "dvdm" 50) where 
  "f dvdm g = (\<exists> h. g =m f * h)" 

definition degree_m :: "int poly \<Rightarrow> nat" where 
  "degree_m f = degree (Mp f)" 

definition irreducible_m :: "int poly \<Rightarrow> bool" where 
  "irreducible_m f = (degree_m f \<noteq> 0 \<and> (\<forall> g h. degree_m g < degree_m f \<longrightarrow> degree_m h < degree_m f \<longrightarrow> \<not> f =m g * h))"

definition square_free_m :: "int poly \<Rightarrow> bool" where 
  "square_free_m f = (\<not> f =m 0 \<and> (\<forall> g. degree_m g \<noteq> 0 \<longrightarrow> \<not> (g * g dvdm f)))"

definition coprime_m :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" where 
  "coprime_m f g = (\<forall> h. (h dvdm f \<and> h dvdm g) = (h dvdm 1))"

lemma mult_Mp[simp]: "Mp (Mp f * g) = Mp (f * g)" "Mp (f * Mp g) = Mp (f * g)" 
proof -
  {
    fix f g
    have "Mp (Mp f * g) = Mp (f * g)" 
    unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff
    proof 
      fix n
      show "M (\<Sum>i\<le>n. M (coeff f i) * coeff g (n - i)) = M (\<Sum>i\<le>n. coeff f i * coeff g (n - i))"
        by (subst M_sum[symmetric], rule sym, subst M_sum[symmetric], unfold M_times, simp)
    qed
  }
  from this[of f g] this[of g f] show "Mp (Mp f * g) = Mp (f * g)" "Mp (f * Mp g) = Mp (f * g)"
    by (auto simp: ac_simps)
qed

lemma plus_Mp[simp]: "Mp (Mp f + g) = Mp (f + g)" "Mp (f + Mp g) = Mp (f + g)" 
  unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff by (auto simp add: Mp_coeff)

lemma minus_Mp[simp]: "Mp (Mp f - g) = Mp (f - g)" "Mp (f - Mp g) = Mp (f - g)" 
  unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff by (auto simp add: Mp_coeff)    

lemma Mp_smult[simp]: "Mp (smult (M a) f) = Mp (smult a f)" "Mp (smult a (Mp f)) = Mp (smult a f)" 
  unfolding Mp_def smult_map_poly
  by (rule poly_eqI, auto simp: coeff_map_poly)+

lemma Mp_Mp[simp]: "Mp (Mp f) = Mp f" unfolding Mp_def
  by (intro poly_eqI, auto simp: coeff_map_poly)

lemma Mp_smult_m_0[simp]: "Mp (smult m f) = 0" 
  by (intro poly_eqI, auto simp: Mp_coeff, auto simp: M_def)

lemma Mp_degree_m[simp]: "degree_m (Mp f) = degree_m f" 
  unfolding degree_m_def by simp

lemma Mp_equivalent[simp]: "Mp f =m g \<longleftrightarrow> f =m g" "f =m Mp g \<longleftrightarrow> f =m g" 
  unfolding equivalent_def by auto

lemma Mp_square_free_m[simp]: "square_free_m (Mp f) = square_free_m f" 
  unfolding square_free_m_def equivalent_def dvdm_def by simp

lemma square_free_m_cong: "square_free_m f \<Longrightarrow> Mp f = Mp g \<Longrightarrow> square_free_m g" 
  unfolding square_free_m_def equivalent_def dvdm_def by simp

lemma Mp_prod_mset[simp]: "Mp (prod_mset (image_mset Mp b)) = Mp (prod_mset b)" 
proof (induct b)
  case (add x b)
  have "Mp (prod_mset (image_mset Mp ({#x#}+b))) = Mp (Mp x * prod_mset (image_mset Mp b))" by simp
  also have "\<dots> = Mp (Mp x * Mp (prod_mset (image_mset Mp b)))" by simp
  also have "\<dots> = Mp ( Mp x * Mp (prod_mset b))" unfolding add by simp
  finally show ?case by simp
qed simp

lemma Mp_prod_list: "Mp (prod_list (map Mp b)) = Mp (prod_list b)" 
proof (induct b)
  case (Cons b xs)
  have "Mp (prod_list (map Mp (b # xs))) = Mp (Mp b * prod_list (map Mp xs))" by simp
  also have "\<dots> = Mp (Mp b * Mp (prod_list (map Mp xs)))" by simp
  also have "\<dots> = Mp (Mp b * Mp (prod_list xs))" unfolding Cons by simp
  finally show ?case by simp
qed simp

text {* Polynomial evaluation modulo *}
definition "M_poly p x \<equiv> M (poly p x)"

lemma M_poly_Mp[simp]: "M_poly (Mp p) = M_poly p"
proof(intro ext, induct p)
  case 0 show ?case by auto
next
  case IH: (pCons a p)
  from IH(1) have "M_poly (Mp (pCons a p)) x = M (a + M(x * M_poly (Mp p) x))"
    by (simp add: M_poly_def Mp_def)
  also note IH(2)[of x]
  finally show ?case by (simp add: M_poly_def)
qed

lemma Mp_lift_modulus: assumes "f =m g" 
  shows "poly_mod.equivalent (m * k) (smult k f) (smult k g)" 
  using assms unfolding poly_mod.equivalent_def
    poly_eq_iff poly_mod.Mp_coeff coeff_smult
  unfolding poly_mod.M_def by simp

lemma Mp_ident_product: "n > 0 \<Longrightarrow> Mp f = f \<Longrightarrow> poly_mod.Mp (m * n) f = f"
  unfolding poly_eq_iff poly_mod.Mp_coeff poly_mod.M_def 
  by (auto simp add: zmod_zmult2_eq) (metis mod_div_trivial mod_0)

lemma Mp_shrink_modulus: assumes "poly_mod.equivalent (m * k) f g" "k \<noteq> 0" 
  shows "f =m g" 
proof -
  from assms have a: "\<And> n. coeff f n mod (m * k) = coeff g n mod (m * k)" unfolding poly_mod.equivalent_def
    poly_eq_iff poly_mod.Mp_coeff unfolding poly_mod.M_def by auto
  show ?thesis unfolding poly_eq_iff poly_mod.Mp_coeff poly_mod.equivalent_def unfolding poly_mod.M_def
  proof
    fix n
    show "coeff f n mod m = coeff g n mod m" using a[of n] \<open>k \<noteq> 0\<close> 
      by (metis mod_mult_right_eq mult.commute mult_cancel_left mult_mod_right)
  qed
qed  
  

lemma degree_m_le: "degree_m f \<le> degree f" unfolding degree_m_def Mp_def by (rule degree_map_poly_le)

lemma degree_m_eq: "coeff f (degree f) mod m \<noteq> 0 \<Longrightarrow> m > 1 \<Longrightarrow> degree_m f = degree f" 
  using degree_m_le[of f] unfolding degree_m_def
  by (metis mod_0 Mp_def degree_map_poly poly_mod.M_def)
  

lemma degree_m_mult_le:  
  assumes eq: "f =m g * h" 
  shows "degree_m f \<le> degree_m g + degree_m h" 
proof -
  have "degree_m f = degree_m (Mp g * Mp h)" using eq unfolding degree_m_def equivalent_def by simp
  also have "\<dots> \<le> degree (Mp g * Mp h)" by (rule degree_m_le)
  also have "\<dots> \<le> degree (Mp g) + degree (Mp h)" by (rule degree_mult_le)
  also have "\<dots> = degree_m g + degree_m h" unfolding degree_m_def by simp
  finally show ?thesis by simp
qed

lemma degree_m_smult_le: "degree_m (smult c f) \<le> degree_m f" unfolding degree_m_def
  by (metis Mp_0 coeff_0 degree_le degree_m_def degree_m_le degree_smult_eq poly_mod.Mp_smult(2) smult_eq_0_iff)

end

declare poly_mod.M_def[code]
declare poly_mod.Mp_def[code]
declare poly_mod.equivalent_def[code]

definition Irr_Mon :: "'a :: idom poly set" where
  "Irr_Mon = {x. irreducible x \<and> monic x}" 

definition factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "factorization Factors f cfs \<equiv> (case cfs of (c,fs) \<Rightarrow> f = (smult c (prod_mset fs)) \<and> (set_mset fs \<subseteq> Factors))" 

definition unique_factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "unique_factorization Factors f cfs = (Collect (factorization Factors f) = {cfs})" 

lemma irreducible_dvd_prod_mset: fixes p :: "'a :: {field,factorial_ring_gcd} poly"
  assumes irr: "irreducible p"
  and dvd: "p dvd prod_mset as"
  shows "\<exists> a \<in># as. p dvd a"
proof -
  from irr[unfolded irreducible_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 nonzero_mult_div_cancel_left div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as)
    case (add a as)
    hence "prod_mset (add_mset a as) = a * prod_mset as" by auto
    from irreducible_dvd_mult[OF irr add(2)[unfolded this]] add(1)
    show ?case by auto
  qed (insert p1, auto)
qed

lemma monic_factorization_unique_mset:
fixes P::"'a::{field,euclidean_ring_gcd} poly multiset"
assumes eq: "prod_mset P = prod_mset Q" 
  and P: "set_mset P \<subseteq> {q. irreducible q \<and> monic q}"
  and Q: "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}"
shows "P = Q" 
proof -
  {
    fix P Q :: "'a poly multiset"
    assume id: "prod_mset P = prod_mset Q" 
    and P: "set_mset P \<subseteq> {q. irreducible q \<and> monic q}"
    and Q: "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}"
    hence "P \<subseteq># Q"
    proof (induct P arbitrary: Q)
      case (add x P Q')
      from add(3) have irr: "irreducible x" and mon: "monic x" by auto
      have "\<exists> a \<in># Q'. x dvd a"
      proof (rule irreducible_dvd_prod_mset[OF irr])
        show "x dvd prod_mset Q'" unfolding add(2)[symmetric] by simp
      qed
      then obtain y Q where Q': "Q' = add_mset y Q" and xy: "x dvd y" by (meson mset_add)
      from add(4) Q' have irr': "irreducible y" and mon': "monic y" by auto
      have "x = y" using irreducible_dvd_eq[OF irr irr' xy mon mon'] .
      hence Q': "Q' = Q + {#x#}" using Q' by auto
      from mon have x0: "x \<noteq> 0" by auto
      from arg_cong[OF add(2)[unfolded Q'], of "\<lambda> z. z div x"] 
      have eq: "prod_mset P = prod_mset Q" using x0 by auto
      from add(3-4)[unfolded Q'] 
      have "set_mset P \<subseteq> {q. irreducible q \<and> monic q}" "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}" 
        by auto
      from add(1)[OF eq this] show ?case unfolding Q' by auto
    qed auto
  }
  from this[OF eq P Q] this[OF eq[symmetric] Q P]
  show ?thesis by auto
qed


lemma exactly_one_monic_factorization: assumes mon: "monic (f :: 'a :: {field,euclidean_ring_gcd} poly)"
  shows "\<exists>! fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible q \<and> monic q}"
proof -
  from monic_irreducible_factorization[OF mon]
  obtain gs g where fin: "finite gs" and f: "f = (\<Prod>a\<in>gs. a ^ Suc (g a))" 
    and gs: "gs \<subseteq> {q. irreducible q \<and> monic q}" 
    by blast
  from fin 
  have "\<exists> fs. set_mset fs \<subseteq> gs \<and> prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" 
  proof (induct gs)
    case (insert a gs)
    from insert(3) obtain fs where *: "set_mset fs \<subseteq> gs" "prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" by auto    
    let ?fs = "fs + replicate_mset (Suc (g a)) a" 
    show ?case 
    proof (rule exI[of _ "fs + replicate_mset (Suc (g a)) a"], intro conjI)
      show "set_mset ?fs \<subseteq> insert a gs" using *(1) by auto
      show "prod_mset ?fs = (\<Prod>a\<in>insert a gs. a ^ Suc (g a))" 
        by (subst prod.insert[OF insert(1-2)], auto simp: *(2))
    qed
  qed simp
  then obtain fs where "set_mset fs \<subseteq> gs" "prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" by auto
  with gs f have ex: "\<exists>fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible q \<and> monic q}"
    by (intro exI[of _ fs], auto)
  thus ?thesis using monic_factorization_unique_mset by blast
qed

lemma monic_prod_mset:
  fixes as :: "'a :: idom poly multiset"
  assumes "\<And> a. a \<in> set_mset as \<Longrightarrow> monic a"
  shows "monic (prod_mset as)" using assms
  by (induct as, auto intro: monic_mult)

lemma exactly_one_factorization: assumes f: "f \<noteq> (0 :: 'a :: {field,euclidean_ring_gcd} poly)"
  shows "\<exists>! cfs. factorization Irr_Mon f cfs"
proof -
  let ?a = "coeff f (degree f)" 
  let ?b = "inverse ?a" 
  let ?g = "smult ?b f" 
  define g where "g = ?g"
  from f have a: "?a \<noteq> 0" "?b \<noteq> 0" by (auto simp: field_simps)
  hence "monic g" unfolding g_def by simp
  note ex1 = exactly_one_monic_factorization[OF this, folded Irr_Mon_def]
  then obtain fs where g: "g = prod_mset fs" "set_mset fs \<subseteq> Irr_Mon" by auto
  let ?cfs = "(?a,fs)" 
  have cfs: "factorization Irr_Mon f ?cfs" unfolding factorization_def split g(1)[symmetric]
    using g(2) unfolding g_def by (simp add: a field_simps)
  show ?thesis
  proof (rule, rule cfs)
    fix dgs
    assume fact: "factorization Irr_Mon f dgs" 
    obtain d gs where dgs: "dgs = (d,gs)" by force
    from fact[unfolded factorization_def dgs split]
    have fd: "f = smult d (prod_mset gs)" and gs: "set_mset gs \<subseteq> Irr_Mon" by auto
    have "monic (prod_mset gs)" by (rule monic_prod_mset, insert gs[unfolded Irr_Mon_def], auto)
    hence d: "d = ?a" unfolding fd by auto
    from arg_cong[OF fd, of "\<lambda> x. smult ?b x", unfolded d g_def[symmetric]]
    have "g = prod_mset gs" using a by (simp add: field_simps)
    with ex1 g gs have "gs = fs" by auto
    thus "dgs = ?cfs" unfolding dgs d by auto
  qed
qed
  
lemma mod_ident_iff: "m > 0 \<Longrightarrow> (x :: int) mod m = x \<longleftrightarrow> x \<in> {0 ..< m}"
  by (metis Divides.pos_mod_bound Divides.pos_mod_sign atLeastLessThan_iff mod_pos_pos_trivial)

end
