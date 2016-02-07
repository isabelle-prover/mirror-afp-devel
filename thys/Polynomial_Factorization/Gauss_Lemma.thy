(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Gauss Lemma\<close>

text \<open>We formalized Gauss Lemma, that the content of a product of two polynomials $p$ and $q$
  is the product of the contents of $p$ and $q$. As a corollary we provide an algorithm
  to convert a rational factor of an integer polynomial into an integer factor.
  
  In contrast to the theory on unique factorization domains -- where Gauss Lemma is also proven 
   in a more generic setting --
  we are here in an executable setting and do not use the unspecified $some-gcd$ function.
  Moreover, there is a slight difference in the definition of content: in this theory it is only
  defined for integer-polynomials, whereas in the UFD theory, the content is defined for 
  polynomials in the fraction field.\<close>

theory Gauss_Lemma
imports 
  "~~/src/HOL/Number_Theory/Primes"
  "../Polynomial_Interpolation/Ring_Hom_Poly"
begin

definition content :: "'a :: semiring_gcd poly \<Rightarrow> 'a" where 
  "content p \<equiv> list_gcd (coeffs p)"

definition normalize_content :: "'a :: {semiring_gcd,semiring_div} poly \<Rightarrow> 'a poly" where 
  "normalize_content p = (div_poly (content p) p)"


definition common_denom :: "rat list \<Rightarrow> int \<times> int list" where
  "common_denom xs \<equiv> let 
     nds = map quotient_of xs;
     denom = list_lcm (map snd nds);
     ints = map (\<lambda> (n,d). n * denom div d) nds
   in (denom, ints)"

definition rat_to_int_poly :: "rat poly \<Rightarrow> int \<times> int poly" where
  "rat_to_int_poly p \<equiv> let
     ais = coeffs p;
     d = fst (common_denom ais)
   in (d, map_poly (\<lambda> x. case quotient_of x of (p,q) \<Rightarrow> p * d div q) p)"

definition rat_to_normalized_int_poly :: "rat poly \<Rightarrow> rat \<times> int poly" where
  "rat_to_normalized_int_poly p \<equiv> if p = 0 then (1,0) else case rat_to_int_poly p of (s,q)
    \<Rightarrow> (of_int (content q) / of_int s, normalize_content q)"

lemma rat_to_normalized_int_poly_code[code]:
  "rat_to_normalized_int_poly p = (if p = 0 then (1,0) else case rat_to_int_poly p of (s,q)
    \<Rightarrow> let c = content q in (of_int c / of_int s, div_poly c q))"
    unfolding Let_def rat_to_normalized_int_poly_def normalize_content_def ..

lemma common_denom: assumes cd: "common_denom xs = (dd,ys)"
  shows "xs = map (\<lambda> i. of_int i / of_int dd) ys" "dd > 0"
  "\<And>x. x \<in> set xs \<Longrightarrow> rat_of_int (case quotient_of x of (n, x) \<Rightarrow> n * dd div x) / rat_of_int dd = x"
proof -
  let ?nds = "map quotient_of xs"
  def nds \<equiv> ?nds
  let ?denom = "list_lcm (map snd nds)"
  let ?ints = "map (\<lambda> (n,d). n * dd div d) nds"
  from cd[unfolded common_denom_def Let_def]
  have dd: "dd = ?denom" and ys: "ys = ?ints" unfolding nds_def by auto
  show dd0: "dd > 0" unfolding dd 
    by (intro list_lcm_pos(3), auto simp: nds_def quotient_of_nonzero)
  {
    fix x
    assume x: "x \<in> set xs"
    obtain p q where quot: "quotient_of x = (p,q)" by force
    from x have "(p,q) \<in> set nds" unfolding nds_def using quot by force
    hence "q \<in> set (map snd nds)" by force
    from list_lcm[OF this] have q: "q dvd dd" unfolding dd .
    show "rat_of_int (case quotient_of x of (n, x) \<Rightarrow> n * dd div x) / rat_of_int dd = x"
      unfolding quot split unfolding quotient_of_div[OF quot]  
    proof -
      have f1: "q * (dd div q) = dd"
        using dvd_mult_div_cancel q by blast
      have "rat_of_int (dd div q) \<noteq> 0"
        using dd0 dvd_mult_div_cancel q by fastforce
      thus "rat_of_int (p * dd div q) / rat_of_int dd = rat_of_int p / rat_of_int q"
        using f1 by (metis (no_types) div_mult_swap mult_divide_mult_cancel_right of_int_mult q)
    qed
  } note main = this
  show "xs = map (\<lambda> i. of_int i / of_int dd) ys" unfolding ys map_map o_def nds_def
    by (rule sym, rule map_idI, rule main)
qed

lemma rat_to_int_poly: assumes "rat_to_int_poly p = (d,q)"
  shows "p = smult (inverse (of_int d)) (map_poly of_int q)" "d > 0"
proof -
  let ?f = "\<lambda> x. case quotient_of x of (pa, x) \<Rightarrow> pa * d div x"
  def f \<equiv> ?f
  from assms[unfolded rat_to_int_poly_def Let_def] 
    obtain xs where cd: "common_denom (coeffs p) = (d,xs)"
    and q: "q = map_poly f p" unfolding f_def by (cases "common_denom (coeffs p)", auto)
  from common_denom[OF cd] have d: "d > 0"  and 
    id: "\<And> x. x \<in> set (coeffs p) \<Longrightarrow> rat_of_int (f x) / rat_of_int d = x" 
    unfolding f_def by auto
  have f0: "f 0 = 0" unfolding f_def by auto
  show "d > 0" by fact
  show "p = smult (inverse (of_int d)) (map_poly of_int q)"
    unfolding q smult_map_poly
    by (rule sym, subst map_poly_compose, force+, subst map_poly_compose, force, rule f0,
     rule map_poly_eqI, insert f0 id d, auto simp: field_simps) 
qed

lemma content_iff: "x dvd content p \<longleftrightarrow> (\<forall> c \<in> set (coeffs p). x dvd c)" (is "?l = ?r")
proof
  assume "x dvd content p"
  from dvd_trans[OF this, unfolded content_def, OF list_gcd] show ?r by auto
next
  assume ?r
  thus ?l unfolding content_def by (intro list_gcd_greatest, auto)
qed

lemma content_dvd: "x \<in> set (coeffs p) \<Longrightarrow> content p dvd x"
  unfolding content_def by (rule list_gcd)

lemma content_0[simp]: "content 0 = 0" unfolding content_def list_gcd_def by simp

lemma content_0_iff[simp]: "content p = (0 :: 'a :: {semiring_gcd,idom}) \<longleftrightarrow> p = 0"
proof (cases "p = 0")
  case False
  def a \<equiv> "last (coeffs p)"
  def xs \<equiv> "coeffs p"
  from last_coeffs_not_0[OF False] not_0_coeffs_not_Nil[OF False]
  have mem: "a \<in> set (coeffs p)" and a: "a \<noteq> 0" unfolding a_def by auto
  from mem have "content p \<noteq> 0" unfolding content_def xs_def[symmetric]
  proof (induct xs)
    case (Cons x xs)
    thus ?case using a unfolding list_gcd_def
      by (cases "x = a", auto)
  qed simp
  with False show ?thesis by auto
qed simp

lemma content_ge_0_int: "content p \<ge> (0 :: int)"
  unfolding content_def list_gcd_def
  by (cases "coeffs p", auto)
  
lemma abs_content_int[simp]: fixes p :: "int poly"
  shows "abs (content p) = content p" using content_ge_0_int[of p] by auto

lemma smult_normalize_content: "smult (content p) (normalize_content p) = p"  
  unfolding  normalize_content_def
  by (rule smult_div_poly, unfold content_def, rule list_gcd)

lemma content_smult_int: fixes p :: "int poly" 
  shows "content (smult a p) = abs a * content p" (is "?l = ?r")
proof (cases "a = 0")
  case False 
  thus ?thesis unfolding content_def coeffs_smult by simp
qed simp

lemma content_normalize_content_1: assumes p0: "p \<noteq> 0" 
  shows "content (normalize_content (p :: int poly)) = 1"
proof -
  note id = smult_normalize_content[of p]
  from id p0 have "content p \<noteq> 0" by auto
  with arg_cong[OF id, of content, unfolded content_smult_int]
  show ?thesis by (simp add: content_ge_0_int)
qed

lemma normalize_content_0[simp]: "normalize_content 0 = 0"
  by (simp add: normalize_content_def div_poly_def eval_poly_def)

lemma normalize_non_0_smult: "\<exists> a. (a :: int) \<noteq> 0 \<and> smult a (normalize_content p) = p"
  by (cases "p = 0", rule exI[of _ 1], simp, rule exI[of _ "content p"], auto
    simp: smult_normalize_content)

lemma degree_normalize_content[simp]: "degree (normalize_content (p :: int poly)) = degree p" 
proof (cases "p = 0")
  case False 
  thus ?thesis 
    by (metis degree_smult_eq smult_0_left smult_normalize_content)
qed simp


lemma rat_to_normalized_int_poly: assumes "rat_to_normalized_int_poly p = (d,q)"
  shows "p = smult d (map_poly of_int q)" "d > 0" "p \<noteq> 0 \<Longrightarrow> content q = 1" "degree q = degree p"
proof -
  have "p = smult d (map_poly of_int q) \<and> d > 0 \<and> (p \<noteq> 0 \<longrightarrow> content q = 1)"
  proof (cases "p = 0")
    case True
    thus ?thesis using assms unfolding rat_to_normalized_int_poly_def
      by (auto simp: eval_poly_def)
  next
    case False
    hence p0: "p \<noteq> 0" by auto
    obtain s r where id: "rat_to_int_poly p = (s,r)" by force
    let ?cr = "rat_of_int (content r)"
    let ?s = "rat_of_int s"
    let ?q = "map_poly rat_of_int q"
    from rat_to_int_poly[OF id] have p: "p = smult (inverse ?s) (map_poly of_int r)"
    and s: "s > 0" by auto
    let ?q = "map_poly rat_of_int q"
    from p0 assms[unfolded rat_to_normalized_int_poly_def id split]
    have d: "d = ?cr / ?s" and q: "q = normalize_content r" by auto
    from smult_normalize_content[of r, folded q] have qr: "smult (content r) q = r" .
    note [simp] = ri.map_poly_0_iff
    have "smult d ?q = smult (?cr / ?s) ?q"
      unfolding d by simp
    also have "?cr / ?s = ?cr * inverse ?s" by (rule divide_inverse)
    also have "\<dots> = inverse ?s * ?cr" by simp
    also have "smult (inverse ?s * ?cr) ?q = smult (inverse ?s) (smult ?cr ?q)" by simp
    also have "smult ?cr ?q = map_poly of_int (smult (content r) q)"
      unfolding ri.map_poly_smult by simp
    also have "\<dots> = map_poly of_int r" unfolding qr ..
    finally have pq: "p = smult d ?q" unfolding p by simp
    from p p0 have r0: "r \<noteq> 0" by auto
    from content_0_iff[of r] content_ge_0_int[of r] r0 have cr: "?cr > 0" by linarith
    with s have d0: "d > 0" unfolding d by auto
    from content_normalize_content_1[OF r0] have cq: "content q = 1" unfolding q .
    from pq d0 cq show ?thesis by auto
  qed
  thus p: "p = smult d (map_poly of_int q)" and d: "d > 0" and "p \<noteq> 0 \<Longrightarrow> content q = 1" by auto
  show "degree q = degree p" unfolding p smult_map_poly
    by (rule sym, subst map_poly_compose, force+, rule degree_map_poly, insert d, auto)
qed

 
lemma gauss_lemma: fixes p :: "int poly"
  shows "content (p * q) = content p * content q"
proof (cases "p = 0 \<or> q = 0")
  case False
  hence p: "p \<noteq> 0" and q: "q \<noteq> 0" by auto
  let ?c = "content"
  {
    fix p q :: "int poly"
    assume cp: "?c p = 1" and cq: "?c q = 1"
    hence p: "p \<noteq> 0" and q: "q \<noteq> 0" and pq: "p * q \<noteq> 0" by auto
    from content_ge_0_int[of "p * q"] content_0_iff[of "p * q"] pq 
    have cpq: "?c (p * q) \<ge> 1" by linarith
    {
      assume "?c (p * q) \<noteq> 1"
      with cpq have cpq: "?c (p * q) > 1" by auto
      def cpq \<equiv> "nat (?c (p * q))"
      let ?cpq = "int cpq"
      from cpq have id: "?c (p * q) = ?cpq" and cpq: "cpq > 1" unfolding cpq_def by auto
      from prime_factor_nat[of cpq] cpq obtain n where pn: "prime n" and n: "n dvd cpq" by auto
      let ?n = "int n"
      from pn have n1: "?n > 1" unfolding prime_def by auto
      from n have "?n dvd ?cpq" by presburger
      from dvd_trans[OF this content_dvd[of _ "p * q", unfolded id]] 
      have n: "\<And> c. c \<in> set (coeffs (p * q)) \<Longrightarrow> ?n dvd c" by auto
      {
        fix p :: "int poly"
        assume cp: "?c p = 1" 
        let ?P = "\<lambda> i. \<not> ?n dvd (coeff p i)"
        {
          assume "\<forall> c \<in> set (coeffs p). ?n dvd c" 
          hence n: "?n dvd ?c p" unfolding content_iff by auto
          from n obtain k where id: "?c p = ?n * k" unfolding dvd_def by blast
          from id n1 have False unfolding cp by (simp add: pos_zmult_eq_1_iff)
        }
        then obtain cp where cp: "cp \<in> set (coeffs p)" and ncp: "\<not> ?n dvd cp" by auto
        hence "cp \<in> range (coeff p)" unfolding range_coeff by auto
        with ncp have "\<exists> i. ?P i" by auto
        from LeastI_ex[OF this] not_less_Least[of _ ?P]
        have "\<exists> i. ?P i \<and> (\<forall> j. j < i \<longrightarrow> ?n dvd (coeff p j))" by blast
      } note cont = this
      from cont[OF cp] obtain r where 
        r: "\<not> ?n dvd (coeff p r)" and r': "\<And> i. i < r \<Longrightarrow> ?n dvd (coeff p i)" by auto
      let ?r = "coeff p r"
      from cont[OF cq] obtain s where 
        s: "\<not> ?n dvd (coeff q s)" and s': "\<And> i. i < s \<Longrightarrow> ?n dvd (coeff q i)" by auto
      let ?s = "coeff q s"
      let ?f = "\<lambda> i. coeff p i * coeff q (r + s - i)"
      def a \<equiv> "(\<Sum>i\<in>{..<r}. (?f i div ?n))"
      def b \<equiv> "\<Sum> i \<in> {Suc r..r + s}. (?f i div ?n)"
      have "coeff (p * q) (r + s) = (\<Sum>i\<le>r + s. ?f i)" unfolding coeff_mult ..
      also have "{..r+s} = {..< r} \<union> {r .. r+s}" by auto
      also have "(\<Sum>i\<in>{..<r} \<union> {r..r + s}. ?f i)
        = (\<Sum>i\<in>{..<r}. ?f i) + (\<Sum> i \<in> {r..r + s}. ?f i)" 
        by (rule setsum.union_disjoint, auto)
      also have "(\<Sum>i\<in>{..<r}. ?f i) = (\<Sum>i\<in>{..<r}. ?n * (?f i div ?n))"
        by (rule setsum.cong[OF refl], insert r', auto)
      also have "\<dots> = ?n * a" unfolding setsum_right_distrib[symmetric] a_def ..
      also have "(\<Sum> i \<in> {r..r + s}. ?f i) = ?f r + (\<Sum> i \<in> {Suc r..r + s}. ?f i)"
        by (subst setsum.remove[of _ r], auto intro: setsum.cong)
      also have "(\<Sum> i \<in> {Suc r..r + s}. ?f i) = (\<Sum> i \<in> {Suc r..r + s}. ?n * (?f i div ?n))"
        by (rule setsum.cong[OF refl], insert s', auto)
      also have "(\<Sum> i \<in> {Suc r..r + s}. ?n * (?f i div ?n)) = ?n * b"
        unfolding setsum_right_distrib[symmetric] b_def ..
      finally have cpq: "coeff (p * q) (r + s) = ?n * (a + b) + ?r * ?s"
        by (simp add: field_simps)
      {
        fix i        
        from n[of "coeff (p * q) i"] have "?n dvd coeff (p * q) i" using range_coeff[of "p * q"] 
          by (cases "coeff (p * q) i = 0", auto)
      }
      from this[of "r + s", unfolded cpq] have n: "?n dvd ?r * ?s"
        by (metis dvd_add_times_triv_left_iff mult.commute)
      hence "n dvd (nat (abs ?r) * nat (abs ?s))"
        using `int n dvd coeff p r * coeff q s` pn prime_dvd_mult_eq_int r s by blast      
      with pn have "n dvd nat (abs ?r) \<or> n dvd nat (abs ?s)" by simp
      also have "(n dvd nat (abs ?r)) = (?n dvd ?r)" using int_dvd_iff by blast
      also have "(n dvd nat (abs ?s)) = (?n dvd ?s)" using int_dvd_iff by blast
      finally have False using r s by auto
    }
    hence "?c (p * q) = 1" by blast
  } note main = this
  def n \<equiv> "\<lambda> p. normalize_content (p :: int poly)"
  let ?s = "\<lambda> p. smult (content p) (n p)"
  have "?c (p * q) = ?c (?s p * ?s q)" unfolding smult_normalize_content n_def by simp
  also have "?s p * ?s q = smult (?c p * ?c q) (n p * n q)" by (simp add: mult.commute)
  also have "?c (\<dots>) = abs (?c p * ?c q) * ?c (n p * n q)" unfolding content_smult_int by simp
  also have "?c (n p * n q) = 1" unfolding n_def
    by (rule main, insert p q, auto simp: content_normalize_content_1)
  also have "abs (?c p * ?c q) = ?c p * ?c q" using content_ge_0_int by auto
  finally show ?thesis by simp
qed auto

lemma dvd_smult_int: fixes c :: int assumes c: "c \<noteq> 0"
  and dvd: "q dvd (smult c p)"
  shows "normalize_content q dvd p"
proof (cases "p = 0")
  case True thus ?thesis by auto
next
  case False note p0 = this
  let ?cp = "smult c p"
  from p0 c have cp0: "?cp \<noteq> 0" by auto
  from dvd obtain r where prod: "?cp = q * r" unfolding dvd_def by auto
  from prod cp0 have q0: "q \<noteq> 0" and r0: "r \<noteq> 0" by auto
  let ?c = "content :: int poly \<Rightarrow> int"
  let ?n = "normalize_content :: int poly \<Rightarrow> int poly"
  let ?pn = "\<lambda> p. smult (?c p) (?n p)"
  have cq: "(?c q = 0) = False" using content_0_iff q0 by auto
  from prod have id1: "?cp = ?pn q * ?pn r" unfolding smult_normalize_content by simp
  from arg_cong[OF this, of content, unfolded content_smult_int gauss_lemma
    content_normalize_content_1[OF r0] content_normalize_content_1[OF q0], symmetric]
    p0[folded content_0_iff] c
  have "abs c dvd ?c q * ?c r" unfolding dvd_def by auto
  hence "c dvd ?c q * ?c r" by auto
  then obtain d where id: "?c q * ?c r = c * d" unfolding dvd_def by auto
  have "?cp = ?pn q * ?pn r" by fact
  also have "\<dots> = smult (c * d) (?n q * ?n r)" unfolding id[symmetric] by (simp add: mult.commute)
  finally have id: "?cp = smult c (?n q * smult d (?n r))" by (simp add: mult.commute)      
  have "p = ?n q * smult d (?n r)"
    using map_poly_inj[OF id[unfolded smult_map_poly[of c]]] c by auto
  thus dvd: "?n q dvd p" unfolding dvd_def by blast
qed
  
lemma irreducible_smult_int[simp]: fixes c :: int assumes c: "c \<noteq> 0"
  shows "irreducible (smult c p) = irreducible p" (is "?l = ?r")
proof
  assume ?l
  thus ?r by (rule irreducible_smultI[OF _ c])
next
  let ?cp = "smult c p"
  assume ?r
  from irreducibleD[OF this]
  have dp: "degree p \<noteq> 0" and p0: "p \<noteq> 0" 
    and irr: "\<And> q. degree q \<noteq> 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> \<not> q dvd p" by auto
  show ?l
  proof (rule irreducibleI)
    from dp c show "degree ?cp \<noteq> 0" by auto 
    fix q :: "int poly"
    let ?nq = "normalize_content q"
    assume deg: "degree q \<noteq> 0" "degree q < degree ?cp"
    hence deg: "degree q \<noteq> 0" "degree q < degree p" using c by auto
    show "\<not> q dvd ?cp"
    proof
      assume "q dvd ?cp" 
      from dvd_smult_int[OF c this] have dvd: "?nq dvd p" by auto
      with deg have "degree ?nq \<noteq> 0" "degree ?nq < degree p" by auto
      from irr[OF this] dvd show False by auto
    qed
  qed
qed

lemma irreducible_normalize_content[simp]: "irreducible (normalize_content (p :: int poly)) =
  irreducible p"
proof (cases "p = 0")
  case False
  thus ?thesis using irreducible_smult_int[of "content p" "normalize_content p",
    unfolded smult_normalize_content[of p]] by auto
qed simp


lemma rat_to_int_factor_content_1: fixes p :: "int poly" 
  assumes cp: "content p = 1"
  and pgh: "map_poly rat_of_int p = g * h"
  and g: "rat_to_normalized_int_poly g = (r,rg)"
  and h: "rat_to_normalized_int_poly h = (s,sh)"
  and p: "p \<noteq> 0"
  shows "p = rg * sh"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  from p have rp0: "?rp p \<noteq> 0" unfolding ri.map_poly_0_iff .
  with pgh have g0: "g \<noteq> 0" and h0: "h \<noteq> 0" by auto
  from rat_to_normalized_int_poly[OF g] g0 
  have r: "r > 0" "r \<noteq> 0" and g: "g = smult r (?rp rg)" and crg: "content rg = 1" by auto
  from rat_to_normalized_int_poly[OF h] h0 
  have s: "s > 0" "s \<noteq> 0" and h: "h = smult s (?rp sh)" and csh: "content sh = 1" by auto
  let ?irs = "inverse (r * s)"
  from r s have irs0: "?irs \<noteq> 0" by (auto simp: field_simps)
  have "?rp (rg * sh) = ?rp rg * ?rp sh" unfolding ri.map_poly_mult ..
  also have "\<dots> = smult ?irs (?rp p)" unfolding pgh g h using r s
    by (simp add: field_simps)
  finally have id: "?rp (rg * sh) = smult ?irs (?rp p)" by auto
  have rsZ: "?irs \<in> \<int>"
  proof (rule ccontr)
    assume not: "\<not> ?irs \<in> \<int>"
    obtain n d where irs': "quotient_of ?irs = (n,d)" by force
    from quotient_of_denom_pos[OF irs'] have "d > 0" .
    from not quotient_of_div[OF irs'] have "d \<noteq> 1" "d \<noteq> 0" and irs: "?irs = ?r n / ?r d" by auto
    with irs0 have n0: "n \<noteq> 0" by auto
    from `d > 0` `d \<noteq> 1` have "d \<ge> 2" and "\<not> d dvd 1" by auto
    with content_iff[of d p, unfolded cp] obtain c where 
      c: "c \<in> set (coeffs p)" and dc: "\<not> d dvd c" 
      by auto
    from c range_coeff[of p] obtain i where "c = coeff p i" by auto 
    from arg_cong[OF id, of "\<lambda> p. coeff p i", 
      unfolded coeff_smult ri.coeff_map_poly_hom this[symmetric] irs]
    have "?r n / ?r d * ?r c \<in> \<int>" by (metis Ints_of_int)
    also have "?r n / ?r d * ?r c = ?r (n * c) / ?r d" by simp
    finally have inZ: "?r (n * c) / ?r d \<in> \<int>" .
    have cop: "coprime n d" by (rule quotient_of_coprime[OF irs'])
    (* now there comes tedious reasoning that `coprime n d` `\<not> d dvd c` ` nc / d \<in> \<int>` yields a 
       contradiction *)
    def prod \<equiv> "?r (n * c) / ?r d"
    obtain n' d' where quot: "quotient_of prod = (n',d')" by force
    have qr: "\<And> x. quotient_of (?r x) = (x, 1)"
      using Rat.of_int_def quotient_of_int by auto
    from quotient_of_denom_pos[OF quot] have "d' > 0" .
    with quotient_of_div[OF quot] inZ[folded prod_def] have "d' = 1"
      by (metis Ints_cases Rat.of_int_def old.prod.inject quot quotient_of_int)
    with quotient_of_div[OF quot] have "prod = ?r n'" by auto
    from arg_cong[OF this, of quotient_of, unfolded prod_def rat_divide_code qr Let_def split]
    have "Rat.normalize (n * c, d) = (n',1)" by simp
    from normalize_crossproduct[OF `d \<noteq> 0`, of 1 "n * c" n', unfolded this]
    have id: "n * c = n' * d" by auto 
    from quotient_of_coprime[OF irs'] have "coprime n d" .
    with dc id show False
      by (metis coprime_dvd_mult_iff_int dc dvd_triv_right gcd.commute mult.commute)
  qed
  then obtain irs where irs: "?irs = ?r irs" unfolding Ints_def by blast        
  from ri.map_poly_inj[OF id[unfolded irs ri.map_poly_smult[symmetric]]]
  have p: "rg * sh = smult irs p" by auto
  have "content (rg * sh) = 1" unfolding gauss_lemma crg csh by auto
  from this[unfolded p content_smult_int cp] have "abs irs = 1" by simp
  hence "abs ?irs = 1" using irs by auto
  with r s have "?irs = 1" by auto
  with irs have "irs = 1" by auto
  with p show p: "p = rg * sh" by auto
qed

lemma rat_to_int_factor_explicit: fixes p :: "int poly" 
  assumes pgh: "map_poly rat_of_int p = g * h"
  and g: "rat_to_normalized_int_poly g = (r,rg)"
  shows "\<exists> r. p = rg * smult (content p) r"
proof -
  show ?thesis
  proof (cases "p = 0")
    case True
    show ?thesis unfolding True
      by (rule exI[of _ 0], auto simp: degree_monom_eq)
  next
    case False
    hence p: "p \<noteq> 0" by auto
    let ?r = "rat_of_int"
    let ?rp = "map_poly ?r"
    def q \<equiv> "normalize_content p"
    from smult_normalize_content[of p, folded q_def] content_0_iff[of p] p
      obtain a where a: "a \<noteq> 0" and pq: "p = smult a q" and acp: "content p = a" by metis
    from a pq p have ra: "?r a \<noteq> 0" and q0: "q \<noteq> 0" by auto
    from content_normalize_content_1[OF p, folded q_def] have cq: "content q = 1" by auto
    obtain s sh where h: "rat_to_normalized_int_poly (smult (inverse (?r a)) h) = (s,sh)" by force
    from arg_cong[OF pgh[unfolded pq ri.map_poly_smult], of "smult (inverse (?r a))"] ra
    have "?rp q = g * smult (inverse (?r a)) h" by auto
    from rat_to_int_factor_content_1[OF cq this g h q0]
    have qrs: "q = rg * sh" .
    show ?thesis unfolding acp unfolding pq qrs 
      by (rule exI[of _ sh], auto)
  qed
qed

lemma rat_to_int_factor: fixes p :: "int poly" 
  assumes pgh: "map_poly rat_of_int p = g * h"
  shows "\<exists> g' h'. p = g' * h' \<and> degree g' = degree g"
proof -
  obtain r rg where ri: "rat_to_normalized_int_poly g = (r,rg)" by force
  from rat_to_int_factor_explicit[OF pgh ri] rat_to_normalized_int_poly(4)[OF ri]
  show ?thesis by blast
qed

lemma rat_to_int_factor_normalized_int_poly: fixes p :: "rat poly" 
  assumes pgh: "p = g * h"
  and p: "rat_to_normalized_int_poly p = (i,ip)"
  shows "\<exists> g' h'. ip = g' * h' \<and> degree g' = degree g"
proof -
  from rat_to_normalized_int_poly[OF p]
  have p: "p = smult i (map_poly rat_of_int ip)" and i: "i \<noteq> 0" by auto
  from arg_cong[OF p, of "smult (inverse i)", unfolded pgh] i
  have "map_poly rat_of_int ip = g * smult (inverse i) h" by auto
  from rat_to_int_factor[OF this] show ?thesis .
qed


text \<open>A polynomial with integer coefficients is
   irreducible over the rationals, if it is irreducible over the integers.\<close>
theorem irreducible_int_rat: fixes p :: "int poly" 
  assumes p: "irreducible p"
  shows "irreducible (map_poly rat_of_int p)"
proof (rule irreducibleI)
  from irreducibleD[OF p] have p: "degree p \<noteq> 0" and 
    irr: "\<And> q. degree q \<noteq> 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> \<not> q dvd p" by auto
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  note ri.degree_map_poly[simp]
  from p show rp: "degree (?rp p) \<noteq> 0" by auto
  from p have p0: "p \<noteq> 0" by auto
  fix g :: "rat poly"
  assume deg: "degree g \<noteq> 0" "degree g < degree (?rp p)"
  show "\<not> g dvd (?rp p)"
  proof
    assume "g dvd (?rp p)"
    then obtain h where pgh: "(?rp p) = g * h" unfolding dvd_def by auto
    from rat_to_int_factor[OF pgh] obtain g' where g': "g' dvd p" and dg: "degree g' = degree g" by force
    with irr[of g'] deg[unfolded dg] show False by auto
  qed
qed

corollary irreducible_rat_to_normalized_int_poly: 
  assumes rp: "rat_to_normalized_int_poly rp = (a, ip)"
  and ip: "irreducible ip"
  shows "irreducible rp"
proof -
  from rat_to_normalized_int_poly[OF rp] 
  have rp: "rp = smult a (map_poly rat_of_int ip)" and a: "a \<noteq> 0" by auto
  from irreducible_int_rat[OF ip] show ?thesis
    unfolding rp irreducible_smult[OF a] .
qed

end
