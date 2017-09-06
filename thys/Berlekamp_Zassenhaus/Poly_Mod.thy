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
  Polynomial_Factorization.Square_Free_Factorization
begin

(**** coprime shouldn't need "gcd" ****)
hide_const(open) coprime

context comm_monoid_mult begin

  definition coprime where "coprime p q \<equiv> \<forall>r. r dvd p \<longrightarrow> r dvd q \<longrightarrow> r dvd 1"

  lemma coprimeI:
    assumes "\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1"
    shows "coprime p q" using assms by (auto simp: coprime_def)

  lemma coprimeE:
    assumes "coprime p q"
        and "(\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1) \<Longrightarrow> thesis"
    shows thesis using assms by (auto simp: coprime_def)

  lemma coprime_commute[ac_simps]: "coprime p q \<longleftrightarrow> coprime q p" unfolding coprime_def by auto

  lemma not_coprime_iff_common_factor:
    "\<not> coprime p q \<longleftrightarrow> (\<exists>r. r dvd p \<and> r dvd q \<and> \<not> r dvd 1)"
    unfolding coprime_def by auto

end

lemma(in semiring_gcd) coprime_iff_gcd_one[simp,code]:
  "coprime = (\<lambda>x y. gcd x y = 1)" using coprime by (intro ext, auto simp: coprime_def)

lemma(in comm_semiring_1) coprime_0[simp]: "coprime p 0 \<longleftrightarrow> p dvd 1" "coprime 0 p \<longleftrightarrow> p dvd 1"
  by (auto intro: coprimeI elim: coprimeE dest: dvd_trans)

(**** until here ****)

locale poly_mod = fixes m :: "int" 
begin

definition M :: "int \<Rightarrow> int" where "M x = x mod m" 

lemma M_0[simp]: "M 0 = 0"
  by (auto simp add: M_def)

lemma M_M[simp]: "M (M x) = M x"
  by (auto simp add: M_def)

lemma M_plus[simp]: "M (M x + y) = M (x + y)" "M (x + M y) = M (x + y)"
  by (auto simp add: M_def mod_simps)
  
lemma M_minus[simp]: "M (M x - y) = M (x - y)" "M (x - M y) = M (x - y)" 
  by (auto simp add: M_def mod_simps)

lemma M_times[simp]: "M (M x * y) = M (x * y)" "M (x * M y) = M (x * y)"
  by (auto simp add: M_def mod_simps)

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

abbreviation eq_m :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infixl "=m" 50) where
  "f =m g \<equiv> (Mp f = Mp g)"

notation eq_m (infixl "=m" 50)

abbreviation degree_m :: "int poly \<Rightarrow> nat" where 
  "degree_m f \<equiv> degree (Mp f)" 

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
  unfolding Mp_def smult_as_map_poly
  by (rule poly_eqI, auto simp: coeff_map_poly)+

lemma Mp_Mp[simp]: "Mp (Mp f) = Mp f" unfolding Mp_def
  by (intro poly_eqI, auto simp: coeff_map_poly)

lemma Mp_smult_m_0[simp]: "Mp (smult m f) = 0" 
  by (intro poly_eqI, auto simp: Mp_coeff, auto simp: M_def)

definition dvdm :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infix "dvdm" 50) where
  "f dvdm g = (\<exists> h. g =m f * h)"
notation dvdm (infix "dvdm" 50)


lemma dvdmE:
  assumes fg: "f dvdm g"
    and main: "\<And>h. g =m f * h \<Longrightarrow> Mp h = h \<Longrightarrow> thesis"
  shows "thesis"
proof-
  from fg obtain h where "g =m f * h" by (auto simp: dvdm_def)
  then have "g =m f * Mp h" by auto
  from main[OF this] show thesis by auto
qed

lemma Mp_dvdm[simp]: "Mp f dvdm g \<longleftrightarrow> f dvdm g"
  and dvdm_Mp[simp]: "f dvdm Mp g \<longleftrightarrow> f dvdm g" by (auto simp: dvdm_def)

definition irreducible_m
  where "irreducible_m f = (\<not>f =m 0 \<and> \<not> f dvdm 1 \<and> (\<forall>a b. f =m a * b \<longrightarrow> a dvdm 1 \<or> b dvdm 1))"

definition irreducible\<^sub>d_m :: "int poly \<Rightarrow> bool" where "irreducible\<^sub>d_m f \<equiv>
   degree_m f \<noteq> 0 \<and>
   (\<forall> g h. degree_m g < degree_m f \<longrightarrow> degree_m h < degree_m f \<longrightarrow> \<not> f =m g * h)"

lemma degree_m_le_degree [intro!]: "degree_m f \<le> degree f"
  by (simp add: Mp_def degree_map_poly_le)

lemma irreducible\<^sub>d_mI:
  assumes f0: "degree_m f \<noteq> 0"
      and main: "\<And>g h. Mp g = g \<Longrightarrow> Mp h = h \<Longrightarrow> degree g \<noteq> 0 \<Longrightarrow> degree g < degree_m f \<Longrightarrow> degree h \<noteq> 0 \<Longrightarrow> degree h < degree_m f \<Longrightarrow> f =m g * h \<Longrightarrow> False"
    shows "irreducible\<^sub>d_m f"
proof (unfold irreducible\<^sub>d_m_def, intro conjI allI impI f0 notI)
  fix g h
  assume deg: "degree_m g < degree_m f" "degree_m h < degree_m f" and "f =m g * h"
  then have f: "f =m Mp g * Mp h" by simp
  have "degree_m f \<le> degree_m g + degree_m h"
    unfolding f using degree_mult_le order.trans by blast
  with main[of "Mp g" "Mp h"] deg f show False by auto
qed

lemma irreducible\<^sub>d_mE:
  assumes "irreducible\<^sub>d_m f"
    and "degree_m f \<noteq> 0 \<Longrightarrow> (\<And>g h. degree_m g < degree_m f \<Longrightarrow> degree_m h < degree_m f \<Longrightarrow> \<not> f =m g * h) \<Longrightarrow> thesis"
  shows thesis
  using assms by (unfold irreducible\<^sub>d_m_def, auto)

lemma irreducible\<^sub>d_mD:
  assumes "irreducible\<^sub>d_m f"
  shows "degree_m f \<noteq> 0" and "\<And>g h. degree_m g < degree_m f \<Longrightarrow> degree_m h < degree_m f \<Longrightarrow> \<not> f =m g * h"
  using assms by (auto elim: irreducible\<^sub>d_mE)

definition square_free_m :: "int poly \<Rightarrow> bool" where 
  "square_free_m f = (\<not> f =m 0 \<and> (\<forall> g. degree_m g \<noteq> 0 \<longrightarrow> \<not> (g * g dvdm f)))"

definition coprime_m :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" where 
  "coprime_m f g = (\<forall> h. h dvdm f \<longrightarrow> h dvdm g \<longrightarrow> h dvdm 1)"

lemma Mp_square_free_m[simp]: "square_free_m (Mp f) = square_free_m f" 
  unfolding square_free_m_def dvdm_def by simp

lemma square_free_m_cong: "square_free_m f \<Longrightarrow> Mp f = Mp g \<Longrightarrow> square_free_m g" 
  unfolding square_free_m_def dvdm_def by simp

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
  shows "poly_mod.eq_m (m * k) (smult k f) (smult k g)" 
  using assms unfolding poly_eq_iff poly_mod.Mp_coeff coeff_smult
  unfolding poly_mod.M_def by simp

lemma Mp_ident_product: "n > 0 \<Longrightarrow> Mp f = f \<Longrightarrow> poly_mod.Mp (m * n) f = f"
  unfolding poly_eq_iff poly_mod.Mp_coeff poly_mod.M_def 
  by (auto simp add: zmod_zmult2_eq) (metis mod_div_trivial mod_0)

lemma Mp_shrink_modulus: assumes "poly_mod.eq_m (m * k) f g" "k \<noteq> 0" 
  shows "f =m g" 
proof -
  from assms have a: "\<And> n. coeff f n mod (m * k) = coeff g n mod (m * k)"
    unfolding poly_eq_iff poly_mod.Mp_coeff unfolding poly_mod.M_def by auto
  show ?thesis unfolding poly_eq_iff poly_mod.Mp_coeff unfolding poly_mod.M_def
  proof
    fix n
    show "coeff f n mod m = coeff g n mod m" using a[of n] \<open>k \<noteq> 0\<close> 
      by (metis mod_mult_right_eq mult.commute mult_cancel_left mult_mod_right)
  qed
qed  
  

lemma degree_m_le: "degree_m f \<le> degree f" unfolding Mp_def by (rule degree_map_poly_le)

lemma degree_m_eq: "coeff f (degree f) mod m \<noteq> 0 \<Longrightarrow> m > 1 \<Longrightarrow> degree_m f = degree f" 
  using degree_m_le[of f] unfolding Mp_def
  by (auto intro: degree_map_poly simp: Mp_def poly_mod.M_def)

lemma degree_m_mult_le:  
  assumes eq: "f =m g * h" 
  shows "degree_m f \<le> degree_m g + degree_m h" 
proof -
  have "degree_m f = degree_m (Mp g * Mp h)" using eq by simp
  also have "\<dots> \<le> degree (Mp g * Mp h)" by (rule degree_m_le)
  also have "\<dots> \<le> degree_m g + degree_m h" by (rule degree_mult_le)
  finally show ?thesis by auto
qed

lemma degree_m_smult_le: "degree_m (smult c f) \<le> degree_m f"
  by (metis Mp_0 coeff_0 degree_le degree_m_le degree_smult_eq poly_mod.Mp_smult(2) smult_eq_0_iff)

end

declare poly_mod.M_def[code]
declare poly_mod.Mp_def[code]

definition Irr_Mon :: "'a :: comm_semiring_1 poly set"
  where "Irr_Mon = {x. irreducible\<^sub>d x \<and> monic x}" 

definition factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "factorization Factors f cfs \<equiv> (case cfs of (c,fs) \<Rightarrow> f = (smult c (prod_mset fs)) \<and> (set_mset fs \<subseteq> Factors))" 

definition unique_factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "unique_factorization Factors f cfs = (Collect (factorization Factors f) = {cfs})" 

lemma irreducible\<^sub>d_dvd_prod_mset:
  fixes p :: "'a :: {field,factorial_ring_gcd} poly"
  assumes irr: "irreducible\<^sub>d p" and dvd: "p dvd prod_mset as"
  shows "\<exists> a \<in># as. p dvd a"
proof -
  from irr[unfolded irreducible\<^sub>d_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 nonzero_mult_div_cancel_left div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as)
    case (add a as)
    hence "prod_mset (add_mset a as) = a * prod_mset as" by auto
    from irreducible\<^sub>d_dvd_mult[OF irr add(2)[unfolded this]] add(1)
    show ?case by auto
  qed (insert p1, auto)
qed

lemma monic_factorization_unique_mset:
  fixes P::"'a::{field,euclidean_ring_gcd} poly multiset"
  assumes eq: "prod_mset P = prod_mset Q" 
    and P: "set_mset P \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    and Q: "set_mset Q \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
  shows "P = Q" 
proof -
  {
    fix P Q :: "'a poly multiset"
    assume id: "prod_mset P = prod_mset Q" 
    and P: "set_mset P \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    and Q: "set_mset Q \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    hence "P \<subseteq># Q"
    proof (induct P arbitrary: Q)
      case (add x P Q')
      from add(3) have irr: "irreducible\<^sub>d x" and mon: "monic x" by auto
      have "\<exists> a \<in># Q'. x dvd a"
      proof (rule irreducible\<^sub>d_dvd_prod_mset[OF irr])
        show "x dvd prod_mset Q'" unfolding add(2)[symmetric] by simp
      qed
      then obtain y Q where Q': "Q' = add_mset y Q" and xy: "x dvd y" by (meson mset_add)
      from add(4) Q' have irr': "irreducible\<^sub>d y" and mon': "monic y" by auto
      have "x = y" using irreducible\<^sub>d_dvd_eq[OF irr irr' xy mon mon'] .
      hence Q': "Q' = Q + {#x#}" using Q' by auto
      from mon have x0: "x \<noteq> 0" by auto
      from arg_cong[OF add(2)[unfolded Q'], of "\<lambda> z. z div x"] 
      have eq: "prod_mset P = prod_mset Q" using x0 by auto
      from add(3-4)[unfolded Q'] 
      have "set_mset P \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}" "set_mset Q \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}" 
        by auto
      from add(1)[OF eq this] show ?case unfolding Q' by auto
    qed auto
  }
  from this[OF eq P Q] this[OF eq[symmetric] Q P]
  show ?thesis by auto
qed


lemma exactly_one_monic_factorization:
  assumes mon: "monic (f :: 'a :: {field,euclidean_ring_gcd} poly)"
  shows "\<exists>! fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
proof -
  from monic_irreducible\<^sub>d_factorization[OF mon]
  obtain gs g where fin: "finite gs" and f: "f = (\<Prod>a\<in>gs. a ^ Suc (g a))" 
    and gs: "gs \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}" 
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
  with gs f have ex: "\<exists>fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible\<^sub>d q \<and> monic q}"
    by (intro exI[of _ fs], auto)
  thus ?thesis using monic_factorization_unique_mset by blast
qed

lemma monic_prod_mset:
  fixes as :: "'a :: idom poly multiset"
  assumes "\<And> a. a \<in> set_mset as \<Longrightarrow> monic a"
  shows "monic (prod_mset as)" using assms
  by (induct as, auto intro: monic_mult)

lemma exactly_one_factorization:
  assumes f: "f \<noteq> (0 :: 'a :: {field,euclidean_ring_gcd} poly)"
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
