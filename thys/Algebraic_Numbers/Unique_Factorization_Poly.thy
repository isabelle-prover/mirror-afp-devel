(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Unique Factorization Domain for Polynomials\<close>

text \<open>In this theory we prove that the polynomials over a unique factorization domain (UFD) form a UFD.\<close>

theory Unique_Factorization_Poly
imports 
  "~~/src/HOL/Library/Polynomial"
  "../Jordan_Normal_Form/Missing_Fraction_Field"
  "../Polynomial_Interpolation/Missing_Unsorted"
  "../Polynomial_Factorization/Polynomial_Divisibility"
  "../Polynomial_Factorization/Unique_Factorization_Domain"
begin

lemmas irreducible_def = Divisibility.irreducible_def
abbreviation irreducible where "irreducible \<equiv> Divisibility.irreducible mk_monoid"


context ufd_loc begin

declare embed_ff.hom_mult[simp del]
lemmas embed_ff_mult[simp add] = embed_ff.hom_mult[symmetric]

abbreviation (input) "PM \<equiv> mk_monoid::'a poly monoid"
abbreviation (input) "PFM \<equiv> mk_monoid::'a fract poly monoid"

definition content :: "'a fract poly \<Rightarrow> 'a fract" where 
  "content p = some_gcd_ff_list (coeffs p)"

lemma content_iff: "divides_ff x (content p) \<longleftrightarrow> (\<forall> c \<in> set (coeffs p). divides_ff x c)" (is "?l = ?r")
proof
  assume ?l
  from divides_ff_trans[OF this, unfolded content_def, OF some_gcd_ff_list_divides] show ?r ..
next
  assume ?r
  thus ?l unfolding content_def by (intro some_gcd_ff_list_greatest, auto)
qed

lemma content_divides_ff: "x \<in> set (coeffs p) \<Longrightarrow> divides_ff (content p) x"
  unfolding content_def by (rule some_gcd_ff_list_divides)

lemma content_0[simp]: "content 0 = 0"
  using content_iff[of 0 0] by (auto simp: divides_ff_def)

lemma content_0_iff[simp]: "(content p = 0) = (p = 0)"
proof (cases "p = 0")
  case False
  def a \<equiv> "last (coeffs p)"
  def xs \<equiv> "coeffs p"
  from last_coeffs_not_0[OF False] not_0_coeffs_not_Nil[OF False]
  have mem: "a \<in> set (coeffs p)" and a: "a \<noteq> 0" unfolding a_def by auto
  from content_divides_ff[OF mem] have "divides_ff (content p) a" .
  with a have "content p \<noteq> 0" unfolding divides_ff_def by auto
  with False show ?thesis by auto
qed auto

lemma content_eq_dff_nonzero: "content p =dff x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> p \<noteq> 0"
  using divides_ff_def eq_dff_def by force

lemma content_smult: "content (smult a p) =dff a * content p"
proof (cases "a = 0")
  case False note a = this
  have id: "coeffs (smult a p) = map (op * a) (coeffs p)"
    unfolding coeffs_smult using a by auto
  show ?thesis unfolding content_def id using some_gcd_ff_list_smult[OF a] .
qed simp

definition "normalize_content p = smult (inverse (content p)) p"

lemma smult_normalize_content: "smult (content p) (normalize_content p) = p"  
  unfolding normalize_content_def
  by (cases "p = 0", auto)

lemma content_normalize_content_1: assumes p0: "p \<noteq> 0" 
  shows "content (normalize_content p) =dff 1"
proof -
  have "content p = content (smult (content p) (normalize_content p))" unfolding smult_normalize_content ..
  also have "\<dots> =dff content p * content (normalize_content p)" by (rule content_smult)
  finally show ?thesis unfolding eq_dff_def divides_ff_def using p0 by auto
qed

lemma content_embed_ff_coeffs_embed_ff: assumes "content p \<in> range embed_ff"
  shows "set (coeffs p) \<subseteq> range embed_ff"
proof 
  fix x
  assume "x \<in> set (coeffs p)"
  from content_divides_ff[OF this] assms[unfolded eq_dff_def] show "x \<in> range embed_ff"
    unfolding divides_ff_def by auto
qed

lemma content_1_coeffs_embed_ff: assumes "content p =dff 1"
  shows "set (coeffs p) \<subseteq> range embed_ff"
proof 
  fix x
  assume "x \<in> set (coeffs p)"
  from content_divides_ff[OF this] assms[unfolded eq_dff_def] show "x \<in> range embed_ff"
    unfolding divides_ff_def by auto
qed

lemma content_embed_ff: assumes "set (coeffs p) \<subseteq> range embed_ff"
  shows "content p \<in> range embed_ff"
proof -
  have "divides_ff 1 (content p)" using assms
    unfolding content_iff unfolding divides_ff_def[abs_def] by auto
  thus ?thesis unfolding divides_ff_def by auto
qed

lemma content_map_poly_embed_ff: "content (map_poly embed_ff (p :: 'a :: ufd poly)) \<in> range embed_ff"
  by (rule content_embed_ff, subst coeffs_map_poly, auto)

lemma range_coeffs_embed_ff: assumes "set (coeffs p) \<subseteq> range embed_ff" 
  shows "\<exists> m. coeff p i = embed_ff m"
proof -
  from assms(1) embed_ff_0 have "coeff p i \<in> range embed_ff" using range_coeff[of p] by force
  thus ?thesis by auto
qed

lemma divides_ff_coeff: assumes "set (coeffs p) \<subseteq> range embed_ff" and "divides_ff (embed_ff n) (coeff p i)"
  shows "\<exists> m. coeff p i = embed_ff n * embed_ff m"
proof -
  from range_coeffs_embed_ff[OF assms(1)]  obtain k where pi: "coeff p i = embed_ff k" by auto
  from assms(2)[unfolded this divides_dvd_embed_ff] have "n dvd k" .
  then obtain j where k: "k = n * j" unfolding Rings.dvd_def by auto
  show ?thesis unfolding pi k by auto
qed

definition inv_embed :: "'a :: ufd fract \<Rightarrow> 'a" where
  "inv_embed = the_inv embed_ff"

lemma inv_embed[simp]: "inv_embed (embed_ff x) = x" 
  unfolding inv_embed_def
  by (rule the_inv_f_f, insert inj_embed_ff, auto simp: inj_on_def)

lemma inv_embed_0[simp]: "inv_embed 0 = 0" unfolding embed_ff_0[symmetric] inv_embed by simp

lemma range_embed_ff_embed_poly: assumes "set (coeffs p) \<subseteq> range embed_ff"
  shows "p = map_poly embed_ff (map_poly inv_embed p)"
proof -
  have "p = map_poly (embed_ff o inv_embed) p"
    by (rule sym, rule map_poly_eqI, insert assms, auto)
  also have "\<dots> = map_poly embed_ff (map_poly inv_embed p)" 
    by (subst map_poly_compose, auto)
  finally show ?thesis .
qed

lemma gauss_lemma:
  fixes p q :: "'a :: ufd fract poly"
  shows "content (p * q) =dff content p * content q"
proof (cases "p = 0 \<or> q = 0")
  case False
  hence p: "p \<noteq> 0" and q: "q \<noteq> 0" by auto
  let ?c = "content :: 'a fract poly \<Rightarrow> 'a fract"
  {
    fix p q :: "'a fract poly"
    assume cp1: "?c p =dff 1" and cq1: "?c q =dff 1"
    def ip \<equiv> "map_poly inv_embed p"
    def iq \<equiv> "map_poly inv_embed q"
    from content_1_coeffs_embed_ff[OF cp1] have cp: "set (coeffs p) \<subseteq> range embed_ff" .
    from content_1_coeffs_embed_ff[OF cq1] have cq: "set (coeffs q) \<subseteq> range embed_ff" .
    have ip: "p = map_poly embed_ff ip" unfolding ip_def
      by (rule range_embed_ff_embed_poly[OF cp])
    have iq: "q = map_poly embed_ff iq" unfolding iq_def
      by (rule range_embed_ff_embed_poly[OF cq])
    have cpq0: "?c (p * q) \<noteq> 0"
      unfolding content_0_iff using cp1 cq1 content_eq_dff_nonzero[of _ 1] by auto
    have cpq: "set (coeffs (p * q)) \<subseteq> range embed_ff" unfolding ip iq
(*    unfolding embed_ff.map_poly_mult[symmetric] embed_ff.coeffs_map_poly by auto *)
      apply(subst semiring_hom.map_poly_mult[symmetric],unfold_locales)
      apply(subst inj_semiring_hom.coeffs_map_poly, unfold_locales)
      by auto
    have ctnt: "?c (p * q) \<in> range embed_ff" using content_embed_ff[OF cpq] .
    then obtain cpq where id: "?c (p * q) = embed_ff cpq" by auto
    have dvd: "divides_ff 1 (?c (p * q))" using ctnt unfolding divides_ff_def by auto
    from cpq0[unfolded id] have cpq0: "cpq \<noteq> 0" unfolding embed_ff_def Zero_fract_def by auto
    hence cpqM: "cpq \<in> carrier M" by auto
    have "?c (p * q) =dff 1"
    proof (rule ccontr)
      assume "\<not> ?c (p * q) =dff 1"
      with dvd have "\<not> divides_ff (?c (p * q)) 1"
        unfolding eq_dff_def by auto
      from this[unfolded id divides_ff_def] have cpq: "\<And> r. r * cpq \<noteq> 1" 
        by (auto simp: embed_ff_def One_fract_def eq_fract)
      hence "cpq \<notin> Units M" unfolding Units_def by auto
      from factors_exist[OF cpqM this] obtain fs where fs: "set fs \<subseteq> carrier M" "factors fs cpq" by auto
      have "fs \<noteq> []" using fs cpq by (cases fs, auto simp: factors_def)
      then obtain f where f: "f \<in> set fs" by (cases fs, auto)
      with fs have irrf: "irreducible f" and fM: "f \<in> carrier M" unfolding factors_def by auto
      from fM have f0: "f \<noteq> 0" by auto
      from irreducible_is_prime[OF irrf fM] have pf: "Divisibility.prime M f" .
      note * = this[unfolded Divisibility.prime_def factor_def Units_def, simplified]
      from * f0 have no_unit: "\<And> x. x * f \<noteq> 1" by (auto simp: ac_simps)
      from * f0 have prime: "\<And> a b. f dvd a * b \<Longrightarrow> f dvd a \<or> f dvd b" unfolding dvd_def by force
      let ?f = "embed_ff f"
      from factors_dividesI[OF fs(2) f fs(1)]
      have fdvd: "f dvd cpq" by auto
      hence "divides_ff ?f (embed_ff cpq)" by simp
      from divides_ff_trans[OF this, folded id, OF content_divides_ff] 
      have dvd: "\<And> z. z \<in> set (coeffs (p * q)) \<Longrightarrow> divides_ff ?f z" .
      {
        fix p :: "'a fract poly"
        assume cp: "?c p =dff 1" 
        let ?P = "\<lambda> i. \<not> divides_ff ?f (coeff p i)"
        {
          assume "\<forall> c \<in> set (coeffs p). divides_ff ?f c"           
          hence n: "divides_ff ?f (?c p)" unfolding content_iff by auto
          from divides_ff_trans[OF this] cp[unfolded eq_dff_def] have "divides_ff ?f 1" by auto
          also have "1 = embed_ff 1" by simp
          finally have "f dvd 1" unfolding divides_dvd_embed_ff .
          hence False using no_unit unfolding dvd_def by (auto simp: ac_simps)
        }
        then obtain cp where cp: "cp \<in> set (coeffs p)" and ncp: "\<not> divides_ff ?f cp" by auto
        hence "cp \<in> range (coeff p)" unfolding range_coeff by auto
        with ncp have "\<exists> i. ?P i" by auto
        from LeastI_ex[OF this] not_less_Least[of _ ?P]
        have "\<exists> i. ?P i \<and> (\<forall> j. j < i \<longrightarrow> divides_ff ?f (coeff p j))" by blast
      } note cont = this
      from cont[OF cp1] obtain r where 
        r: "\<not> divides_ff ?f (coeff p r)" and r': "\<And> i. i < r \<Longrightarrow> divides_ff ?f (coeff p i)" by auto
      have "\<forall> i. \<exists> k. i < r \<longrightarrow> coeff p i = ?f * embed_ff k" using divides_ff_coeff[OF cp r'] by blast
      from choice[OF this] obtain rr where r': "\<And> i. i < r \<Longrightarrow> coeff p i = ?f * embed_ff (rr i)" by blast
      let ?r = "coeff p r"
      from cont[OF cq1] obtain s where 
        s: "\<not> divides_ff ?f (coeff q s)" and s': "\<And> i. i < s \<Longrightarrow> divides_ff ?f (coeff q i)" by auto
      have "\<forall> i. \<exists> k. i < s \<longrightarrow> coeff q i = ?f * embed_ff k" using divides_ff_coeff[OF cq s'] by blast
      from choice[OF this] obtain ss where s': "\<And> i. i < s \<Longrightarrow> coeff q i = ?f * embed_ff (ss i)" by blast
      from range_coeffs_embed_ff[OF cp] have "\<forall> i. \<exists> m. coeff p i = embed_ff m" ..
      from choice[OF this] obtain pi where pi: "\<And> i. coeff p i = embed_ff (pi i)" by blast
      from range_coeffs_embed_ff[OF cq] have "\<forall> i. \<exists> m. coeff q i = embed_ff m" ..
      from choice[OF this] obtain qi where qi: "\<And> i. coeff q i = embed_ff (qi i)" by blast
      let ?s = "coeff q s"
      let ?g = "\<lambda> i. coeff p i * coeff q (r + s - i)"
      def a \<equiv> "(\<Sum>i\<in>{..<r}. (rr i * qi (r + s - i)))"
      def b \<equiv> "\<Sum> i \<in> {Suc r..r + s}. pi i * (ss (r + s - i))" 
      have "coeff (p * q) (r + s) = (\<Sum>i\<le>r + s. ?g i)" unfolding coeff_mult ..
      also have "{..r+s} = {..< r} \<union> {r .. r+s}" by auto
      also have "(\<Sum>i\<in>{..<r} \<union> {r..r + s}. ?g i)
        = (\<Sum>i\<in>{..<r}. ?g i) + (\<Sum> i \<in> {r..r + s}. ?g i)" 
        by (rule setsum.union_disjoint, auto)
      also have "(\<Sum>i\<in>{..<r}. ?g i) = (\<Sum>i\<in>{..<r}. ?f * (embed_ff (rr i) * embed_ff (qi (r + s - i))))"
        by (rule setsum.cong[OF refl], insert r' qi, auto)
      also have "\<dots> = embed_ff (f * a)"
        unfolding embed_ff.hom_mult embed_ff.hom_setsum setsum_right_distrib a_def ..
      also have "(\<Sum> i \<in> {r..r + s}. ?g i) = ?g r + (\<Sum> i \<in> {Suc r..r + s}. ?g i)"
        by (subst setsum.remove[of _ r], auto intro: setsum.cong)
      also have "(\<Sum> i \<in> {Suc r..r + s}. ?g i) = (\<Sum> i \<in> {Suc r..r + s}. ?f * (embed_ff (pi i) * embed_ff (ss (r + s - i))))"
        by (rule setsum.cong[OF refl], insert s' pi, auto)
      also have "\<dots> = embed_ff (f * b)"
        unfolding embed_ff.hom_mult embed_ff.hom_setsum setsum_right_distrib b_def ..
      finally have cpq: "coeff (p * q) (r + s) = embed_ff (f * (a + b)) + ?r * ?s"
        by (simp add: field_simps)
      {
        fix i        
        from dvd[of "coeff (p * q) i"] have "divides_ff ?f (coeff (p * q) i)" using range_coeff[of "p * q"] 
          by (cases "coeff (p * q) i = 0", auto simp: divides_ff_def)
      }
      from this[of "r + s", unfolded cpq] have "divides_ff ?f (embed_ff (f * (a + b) + pi r * qi s))" 
        unfolding pi qi by simp
      from this[unfolded divides_dvd_embed_ff] have "f dvd pi r * qi s"
        by (metis dvd_add_times_triv_left_iff mult.commute)
      from prime[OF this] have "f dvd pi r \<or> f dvd qi s" by auto
      with r s show False unfolding pi qi divides_dvd_embed_ff by auto
    qed
  } note main = this
  def n \<equiv> "normalize_content :: 'a fract poly \<Rightarrow> 'a fract poly"
  let ?s = "\<lambda> p. smult (content p) (n p)"
  have "?c (p * q) = ?c (?s p * ?s q)" unfolding smult_normalize_content n_def by simp
  also have "?s p * ?s q = smult (?c p * ?c q) (n p * n q)" by (simp add: mult.commute)
  also have "?c (\<dots>) =dff (?c p * ?c q) * ?c (n p * n q)" by (rule content_smult)
  also have "?c (n p * n q) =dff 1" unfolding n_def
    by (rule main, insert p q, auto simp: content_normalize_content_1)
  finally show ?thesis by simp
qed auto

abbreviation (input) "content_ff p \<equiv> content (map_poly embed_ff p)"

lemma factorization_embed_ff: assumes q: "q \<noteq> 0"
  and factor: "map_poly embed_ff (p :: 'a :: ufd poly) = q * r"
  shows "\<exists> q' r' c. c \<noteq> 0 \<and> q = smult c (map_poly embed_ff q') \<and>
    r = smult (inverse c) (map_poly embed_ff r') \<and>
    content_ff q' =dff 1 \<and> p = q' * r'"
proof -
  let ?c = content
  let ?p = "map_poly embed_ff p"
  def cq \<equiv> "normalize_content q"
  def cr \<equiv> "smult (content q) r"
  def q' \<equiv> "map_poly inv_embed cq"
  def r' \<equiv> "map_poly inv_embed cr"
  from content_map_poly_embed_ff have cp_ff: "?c ?p \<in> range embed_ff" by auto
  from smult_normalize_content[of q] have cqs: "q = smult (content q) cq" unfolding cq_def ..
  from content_normalize_content_1[OF q] have c_cq: "content cq =dff 1" unfolding cq_def .
  from content_1_coeffs_embed_ff[OF this] have cq_ff: "set (coeffs cq) \<subseteq> range embed_ff" .
  have factor: "?p = cq * cr" unfolding factor cr_def using cqs
    by (metis mult_smult_left mult_smult_right)
  from gauss_lemma[of cq cr] have cp: "?c ?p =dff ?c cq * ?c cr" unfolding factor .
  with c_cq have "?c ?p =dff ?c cr"
    by (metis eq_dff_mult_right_trans mult.commute mult.right_neutral)
  with cp_ff have "?c cr \<in> range embed_ff"
    by (metis divides_ff_def embed_ff.hom_mult eq_dff_def image_iff range_eqI)
  from content_embed_ff_coeffs_embed_ff[OF this] have cr_ff: "set (coeffs cr) \<subseteq> range embed_ff" by auto
  have cq: "cq = map_poly embed_ff q'" unfolding q'_def
    by (rule range_embed_ff_embed_poly[OF cq_ff])
  have cr: "cr = map_poly embed_ff r'" unfolding r'_def
    by (rule range_embed_ff_embed_poly[OF cr_ff])
  have p: "p = q' * r'"
    apply(subst inj_semiring_hom.map_poly_inj[of embed_ff],unfold_locales)
    unfolding factor[unfolded cq cr]
    apply(subst semiring_hom.map_poly_mult[of embed_ff,symmetric],unfold_locales)
    by auto
  (* from embed_ff.map_poly_inj[OF factor[unfolded cq cr, folded embed_ff.map_poly_mult]]
  have p: "p = q' * r'" by auto *)
  from c_cq have ctnt: "content_ff q' =dff 1" using cq q'_def by force
  from cqs have idq: "q = smult (?c q) (map_poly embed_ff q')" unfolding cq .
  with q have cq: "?c q \<noteq> 0" by auto
  have "r = smult (inverse (?c q)) cr" unfolding cr_def using cq by auto
  also have "cr = map_poly embed_ff r'" by (rule cr)
  finally have idr: "r = smult (inverse (?c q)) (map_poly embed_ff r')" by auto
  from cq p ctnt idq idr show ?thesis by blast
qed
  
lemma irreducible_PM_M_PFM: assumes irr: "irreducible p"
  shows "degree p = 0 \<and> irreducible (coeff p 0) \<or> 
  degree p \<noteq> 0 \<and> irreducible (map_poly embed_ff p) \<and> content_ff p =dff 1"
proof (cases "p = 0")
  case True
  thus ?thesis using assms by (auto simp: irreducible_def Units_def properfactor_def)
next
  case False note p = this
  from irr[unfolded irreducible_idom_nz[OF False]]
  have irr: "\<not> p dvd 1" "\<And> b. b dvd p \<Longrightarrow> \<not> p dvd b \<Longrightarrow> b dvd 1" by auto
  show ?thesis
  proof (cases "degree p = 0")
    case True
    from degree0_coeffs[OF True] obtain a where p: "p = [:a:]" by auto
    note irr = irr[unfolded p]
    from p False have a: "a \<noteq> 0" by auto
    have "irreducible a" unfolding irreducible_idom_nz[OF a]
    proof (intro conjI impI allI)
      show "\<not> a dvd 1" using irr(1)[unfolded const_poly_dvd_1] .
      fix b
      assume "b dvd a" "\<not> a dvd b"
      hence "[:b:] dvd [:a:]" "\<not> [:a:] dvd [:b:]" unfolding const_poly_dvd .
      from irr(2)[OF this] show "b dvd 1" unfolding const_poly_dvd_1 .
    qed
    with True show ?thesis unfolding p by auto
  next
    case False
    let ?E = "map_poly embed_ff"
    let ?p = "?E p"
    from p have p': "?p \<noteq> 0" by simp
    have dp: "degree ?p \<noteq> 0" using False embed_ff.degree_map_poly by simp
    have irr_p': "irreducible ?p" unfolding irreducible_idom_nz[OF p']
    proof (intro conjI impI allI)
      show "\<not> ?p dvd 1" 
      proof
        assume "?p dvd 1" then obtain q where id: "?p * q = 1" unfolding dvd_def by auto
        have deg: "degree (?p * q) = degree ?p + degree q"
          by (rule degree_mult_eq, insert id, auto)
        from arg_cong[OF id, of degree, unfolded deg] dp show False by auto
      qed
      fix q
      assume "q dvd ?p" and ndvd: "\<not> ?p dvd q"
      then obtain r where fact: "?p = q * r" unfolding dvd_def by auto
      with p' have q0: "q \<noteq> 0" by auto
      from factorization_embed_ff[OF this fact] obtain q' r' c where *: "c \<noteq> 0" "q = smult c (?E q')"
        "r = smult (inverse c) (?E r')" "content_ff q' =dff 1"
        "p = q' * r'" by auto
      hence "q' dvd p" unfolding dvd_def by auto
      note irr = irr(2)[OF this]
      have "\<not> p dvd q'"
      proof
        assume "p dvd q'"
        then obtain u where q': "q' = p * u" unfolding dvd_def by auto
        from arg_cong[OF this, of "\<lambda> x. smult c (?E x)", unfolded embed_ff.map_poly_mult *(2)[symmetric]]
        have "q = ?p * smult c (?E u)" by simp
        hence "?p dvd q" unfolding dvd_def by blast
        with ndvd show False ..
      qed
      from irr[OF this] have "q' dvd 1" .
      from divides_degree[OF this] have "degree q' = 0" by auto
      from degree0_coeffs[OF this] obtain a where "q' = [:a:]" by auto
      with *(2) obtain a where q: "q = [: a :]" by auto
      with q0 have a: "a \<noteq> 0" by auto
      show "q dvd 1" unfolding q const_poly_dvd_1 using a unfolding dvd_def
        by (intro exI[of _ "inverse a"], auto)
    qed
    let ?c = "content"
    have "?c ?p \<in> range embed_ff"
      by (rule content_embed_ff, unfold embed_ff.coeffs_map_poly, auto)
    then obtain c where cp: "?c ?p = embed_ff c" by auto
    from p' cp have c: "c \<noteq> 0" by auto
    have "?c ?p =dff 1" unfolding cp
    proof (rule ccontr)
      def cp \<equiv> "normalize_content ?p"
      from smult_normalize_content[of ?p] have cps: "?p = smult (embed_ff c) cp" unfolding cp_def cp ..
      from content_normalize_content_1[OF p'] have c_cp: "content cp =dff 1" unfolding cp_def .
      from range_embed_ff_embed_poly[OF content_1_coeffs_embed_ff[OF c_cp]] obtain cp' where "cp = ?E cp'" by auto
      from embed_ff.map_poly_inj[OF cps[unfolded this embed_ff.map_poly_smult[symmetric]]] have "p = smult c cp'" by auto
      hence dvd: "[: c :] dvd p" unfolding dvd_def by auto
      have "\<not> p dvd [: c :]" using divides_degree[of p "[: c :]"] c False by auto
      from irr(2)[OF dvd this] have "c dvd 1" unfolding const_poly_dvd_1 .      
      assume "\<not> embed_ff c =dff 1"
      from this[unfolded eq_dff_def One_fract_def embed_ff_def[symmetric] divides_ff_def embed_ff_mult embed_ff.hom_eq_iff]
      have c1: "\<And> r. 1 \<noteq> c * r" by (auto simp: ac_simps)
      with `c dvd 1` show False unfolding dvd_def by blast
    qed
    with False irr_p' show ?thesis by auto
  qed
qed

lemma irreducible_M_PM:
  fixes p :: "'a :: ufd poly" assumes 0: "degree p = 0" and irr: "irreducible (coeff p 0)"
  shows "irreducible p"
proof (cases "p = 0")
  case True
  thus ?thesis using assms by (auto simp: irreducible_def Units_def properfactor_def)
next
  case False
  from degree0_coeffs[OF 0] obtain a where p: "p = [:a:]" by auto
  with False have a: "a \<noteq> 0" by auto
  from p irr have "irreducible a" by auto
  from this[unfolded irreducible_idom_nz[OF a]]
  have irr: "\<not> a dvd 1" "\<And> b. b dvd a \<Longrightarrow> \<not> a dvd b \<Longrightarrow> b dvd 1" by auto
  show ?thesis unfolding irreducible_idom_nz[OF False] unfolding p const_poly_dvd_1
  proof (intro conjI allI impI)
    show "\<not> a dvd 1" by fact
    fix b
    assume *: "b dvd [:a:]" "\<not> [:a:] dvd b"
    from divides_degree[OF this(1)] a have "degree b = 0" by auto
    from degree0_coeffs[OF this] obtain bb where b: "b = [: bb :]" by auto
    from * irr(2)[of bb] show "b dvd 1" unfolding b const_poly_dvd const_poly_dvd_1 by auto
  qed
qed
 
lemma irreducible_PFM_degree:
  fixes p :: "'a :: ufd fract poly" assumes "p \<noteq> 0" "irreducible p"
  shows "degree p \<noteq> 0" 
proof 
  assume "degree p = 0"
  from degree0_coeffs[OF this] assms obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
  hence "1 = p * [:inverse a:]" by (auto simp: one_poly_def)
  hence "p dvd 1" ..
  hence "p \<in> Units PFM" unfolding units_idom_nz[OF `p \<noteq> 0`] .
  with assms show False unfolding irreducible_def by auto
qed
  
lemma irreducible_PFM_PM: assumes 
  irr: "irreducible (map_poly embed_ff p)" and ct: "content_ff p =dff 1"
  shows "irreducible p"
proof -
  let ?E = "map_poly embed_ff"
  let ?p = "?E p"
  from ct have p: "p \<noteq> 0" by (auto simp: eq_dff_def divides_ff_def)
  hence p': "?p \<noteq> 0" by auto
  from irreducible_PFM_degree[OF p' irr] have deg: "degree p \<noteq> 0" unfolding embed_ff.degree_map_poly .
  from irr[unfolded irreducible_idom_nz[OF p']]
  have irr: "\<And> b. b dvd ?p \<Longrightarrow> \<not> ?p dvd b \<Longrightarrow> b dvd 1" by auto
  show ?thesis unfolding irreducible_idom_nz[OF p]
  proof (intro conjI allI impI)
    show "\<not> p dvd 1" using deg divides_degree[of p 1] by auto
    fix q :: "'a poly"
    assume dvd: "q dvd p" and ndvd: "\<not> p dvd q"
    from dvd obtain r where pqr: "p = q * r" ..
    from arg_cong[OF this, of ?E] have pqr': "?p = ?E q * ?E r" by simp
    from p pqr have q: "q \<noteq> 0" and r: "r \<noteq> 0" by auto
    have dp: "degree p = degree q + degree r" unfolding pqr
      by (subst degree_mult_eq, insert q r, auto)
    from eq_dff_trans[OF eq_dff_sym[OF gauss_lemma[of "?E q" "?E r", folded pqr']] ct]
    have ct: "content (?E q) * content (?E r) =dff 1" .
    from content_map_poly_embed_ff obtain cq where cq: "content (?E q) = embed_ff cq" by auto
    from content_map_poly_embed_ff obtain cr where cr: "content (?E r) = embed_ff cr" by auto
    from ct[unfolded cq cr embed_ff_mult eq_dff_def 
      divides_ff_def One_fract_def embed_ff_def[symmetric] embed_ff.hom_eq_iff]
    obtain c where c: "c * (cq * cr) = 1" by auto
    hence one: "1 = cq * (c * cr)" "1 = cr * (c * cq)" by (auto simp: ac_simps)
    {
      assume *: "degree q \<noteq> 0 \<and> degree r \<noteq> 0"      
      with dp have "degree q < degree p" by auto
      hence "degree (?E q) < degree (?E p)" unfolding embed_ff.degree_map_poly .
      hence ndvd: "\<not> ?p dvd ?E q" using divides_degree[of ?p "?E q"] q by auto
      have "?E q dvd ?p" unfolding pqr' by auto
      from irr[OF this ndvd] have "?E q dvd 1" .
      from divides_degree[OF this] * have False by auto
    }
    hence "degree q = 0 \<or> degree r = 0" by blast
    thus "q dvd 1" 
    proof
      assume "degree q = 0"
      from degree0_coeffs[OF this] q obtain a where q: "q = [:a:]" and a: "a \<noteq> 0" by auto
      hence id: "set (coeffs (?E q)) = {embed_ff a}" by auto
      have "divides_ff (embed_ff a) (content (?E q))" unfolding content_iff id by auto
      from this[unfolded cq divides_ff_def embed_ff_mult embed_ff.hom_eq_iff]
      obtain rr where cq: "cq = rr * a" by blast
      with one(1) have "1 = a * (rr * c * cr)" by (auto simp: ac_simps)
      hence "a dvd 1" ..
      thus ?thesis unfolding q const_poly_dvd_1 .
    next
      assume "degree r = 0"
      from degree0_coeffs[OF this] r obtain a where r: "r = [:a:]" and a: "a \<noteq> 0" by auto
      hence id: "set (coeffs (?E r)) = {embed_ff a}" by auto
      have "divides_ff (embed_ff a) (content (?E r))" unfolding content_iff id by auto
      from this[unfolded cr divides_ff_def embed_ff_mult embed_ff.hom_eq_iff] obtain rr 
        where cr: "cr = rr * a" by blast
      with one(2) have one: "1 = a * (rr * c * cq)" by (auto simp: ac_simps)
      from arg_cong[OF pqr[unfolded r], of "\<lambda> p. p * [:rr * c * cq:]"]
      have "p * [:rr * c * cq:] = q * [:a * (rr * c * cq):]" by (simp add: ac_simps)
      also have "\<dots> = q" unfolding one[symmetric] by auto
      finally obtain r where "q = p * r" by blast
      hence "p dvd q" ..
      with ndvd show ?thesis by auto
    qed
  qed
qed
  
lemma irreducible_cases: "irreducible p \<longleftrightarrow>
  degree p = 0 \<and> irreducible (coeff p 0) \<or> 
  degree p \<noteq> 0 \<and> irreducible (map_poly embed_ff p) \<and> content_ff p =dff 1"
  using irreducible_PM_M_PFM irreducible_M_PM irreducible_PFM_PM
  by blast

lemma factor_constant_as_poly:
  assumes a: "a \<noteq> 0" and a1: "\<not> a dvd 1"
  shows "\<exists> fs. set fs \<subseteq> carrier PM \<and> factors fs [:a:]"
proof -
  from a a1 have "a \<in> carrier M" "a \<notin> Units M" unfolding units_idom_nz[OF a] by auto
  from factors_exist[OF this] obtain as where as: "set as \<subseteq> carrier M" and fs: "factors as a" by auto
  let ?as = "map (\<lambda> a. [:a:]) as"
  from fs[unfolded factors] have prod: "a = listprod as" 
    and irr: "\<And> a. a \<in> set as \<Longrightarrow> irreducible a"
    by auto
  hence "\<And> a. a \<in> set ?as \<Longrightarrow> irreducible a" by (subst irreducible_cases, auto)
  hence irr: "Ball (set ?as) irreducible" by auto
  let ?a = "[:a:]"
  have prod: "?a = listprod ?as" unfolding prod by (rule sym, induct as, auto simp: one_poly_def)
  have fact: "factors ?as ?a" unfolding factors using irr prod by auto
  from as have "set ?as \<subseteq> carrier PM" by auto
  thus ?thesis using fact by blast
qed  

lemma const_poly_Units_PFM[simp]: "c \<noteq> 0 \<Longrightarrow> [:c:] \<in> Units PFM"
  unfolding Units_def mk_monoid_simps 
  by (auto intro: bexI[of _ "[:inverse c:]"] simp: one_poly_def)

lemma irreducible_PFM_smult:
  assumes c: "(c::'a fract) \<noteq> 0" and p: "p \<noteq> 0" and irr: "irreducible p"
  shows "irreducible (smult c p)"
proof -
  interpret PFM: factorial_monoid PFM by (rule factorial_monoid_field_poly)
  show ?thesis using PFM.irreducible_prod_lI[OF irr const_poly_Units_PFM[OF c]] c p
    by auto
qed

lemma dvd_PM_iff: "p dvd q \<longleftrightarrow> divides_ff (content_ff p) (content_ff q) \<and> 
  map_poly embed_ff p dvd map_poly embed_ff q"
proof -
  let ?E = "map_poly embed_ff"
  show ?thesis (is "?l = ?r")
  proof
    assume "p dvd q"
    then obtain r where qpr: "q = p * r" ..
    from arg_cong[OF this, of ?E, unfolded embed_ff.map_poly_mult]
    have dvd: "?E p dvd ?E q" ..
    from content_map_poly_embed_ff obtain cq where cq: "content_ff q = embed_ff cq" by auto
    from content_map_poly_embed_ff obtain cp where cp: "content_ff p = embed_ff cp" by auto
    from content_map_poly_embed_ff obtain cr where cr: "content_ff r = embed_ff cr" by auto
    from gauss_lemma[of "?E p" "?E r", folded embed_ff.map_poly_mult qpr, unfolded cq cp cr]
    have "divides_ff (content_ff p) (content_ff q)" unfolding cq cp eq_dff_def
      by (metis divides_ff_def divides_ff_trans mult.commute)
    with dvd show ?r by blast
  next
    assume ?r
    show ?l 
    proof (cases "q = 0")
      case True
      with `?r` show ?l by auto
    next
      case False note q = this
      hence q': "?E q \<noteq> 0" by auto
      from `?r` obtain rr where qpr: "?E q = ?E p * rr" unfolding dvd_def by auto
      with q have p: "p \<noteq> 0" and Ep: "?E p \<noteq> 0" and rr: "rr \<noteq> 0" by auto
      from gauss_lemma[of "?E p" rr, folded qpr] 
      have ct: "content_ff q =dff content_ff p * content rr"
        by auto
      from content_map_poly_embed_ff[of p] obtain cp where cp: "content_ff p = embed_ff cp" by auto
      from content_map_poly_embed_ff[of q] obtain cq where cq: "content_ff q = embed_ff cq" by auto
      from `?r`[unfolded cp cq] have "divides_ff (embed_ff cp) (embed_ff cq)" ..
      with ct[unfolded cp cq eq_dff_def] have "content rr \<in> range embed_ff"
        by (metis (no_types, lifting) Ep content_0_iff cp divides_ff_def 
          divides_ff_trans mult.commute mult_right_cancel range_eqI)
      from range_embed_ff_embed_poly[OF content_embed_ff_coeffs_embed_ff[OF this]] obtain r
        where rr: "rr = ?E r" by auto
      from embed_ff.map_poly_inj[OF qpr[unfolded rr embed_ff.map_poly_mult[symmetric]]]
      have "q = p * r" .
      thus "p dvd q" ..
    qed
  qed
qed

lemma factorial_monoid_poly: "factorial_monoid PM"
proof -
  interpret PM: comm_monoid_cancel PM by (rule comm_monoid_cancel_idom)
  interpret PFM: factorial_monoid PFM by (rule factorial_monoid_field_poly)
  let ?E = "map_poly embed_ff"  
  show ?thesis unfolding factorial_condition_one[symmetric]
  proof (intro conjI)
    show "divisor_chain_condition_monoid (PM::'a poly monoid)"
    proof (unfold_locales, unfold mk_monoid_simps)
      let ?rel' = "{(x::'a poly, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> properfactor x y}"
      let ?rel'' = "{(x::'a, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> properfactor x y}"
      let ?relPM = "{(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> x dvd y \<and> \<not> y dvd (x :: 'a poly)}"
      let ?relM = "{(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> x dvd y \<and> \<not> y dvd (x :: 'a)}"
      have id: "?rel' = ?relPM" using properfactor_nz by auto
      have id': "?rel'' = ?relM" using properfactor_nz by auto
      have "wf ?rel''" using division_wellfounded by auto
      hence wfM: "wf ?relM" using id' by auto
      let ?c = "\<lambda> p. inv_embed (content_ff p)"
      let ?f = "\<lambda> p. (degree p, ?c p)"
      note wf = wf_inv_image[OF wf_lex_prod[OF wf_less wfM], of ?f]
      show "wf ?rel'" unfolding id
      proof (rule wf_subset[OF wf], clarify)
        fix p q :: "'a poly"
        assume p: "p \<noteq> 0" and q: "q \<noteq> 0" and dvd: "p dvd q" and ndvd: "\<not> q dvd p"
        from dvd obtain r where qpr: "q = p * r" ..
        from degree_mult_eq[of p r, folded qpr] q qpr have r: "r \<noteq> 0" 
          and deg: "degree q = degree p + degree r" by auto
        show "(p,q) \<in> inv_image ({(x, y). x < y} <*lex*> ?relM) ?f"
        proof (cases "degree p = degree q")
          case False
          with deg have "degree p < degree q" by auto
          thus ?thesis by auto
        next
          case True
          with deg have "degree r = 0" by simp
          from degree0_coeffs[OF this] r obtain a where ra: "r = [:a:]" and a: "a \<noteq> 0" by auto
          from arg_cong[OF qpr, of "\<lambda> p. ?E p * [:inverse (embed_ff a):]"] a
          have "?E p = ?E q * [:inverse (embed_ff a):]"
            by (auto simp: ac_simps ra)
          hence "?E q dvd ?E p" ..
          with ndvd dvd_PM_iff have ndvd: "\<not> divides_ff (content_ff q) (content_ff p)" by auto
          from content_map_poly_embed_ff obtain cq where cq: "content_ff q = embed_ff cq" by auto
          from content_map_poly_embed_ff obtain cp where cp: "content_ff p = embed_ff cp" by auto
          from ndvd[unfolded cp cq] have ndvd: "\<not> cq dvd cp" by simp
          from iffD1[OF dvd_PM_iff,OF dvd,unfolded cq cp]
          have dvd: "cp dvd cq" by simp
          have c_p: "?c p = cp" unfolding cp by simp
          have c_q: "?c q = cq" unfolding cq by simp
          from q cq have cq0: "cq \<noteq> 0" by auto
          from p cp have cp0: "cp \<noteq> 0" by auto
          from ndvd cq0 cp0 dvd have "(?c p, ?c q) \<in> ?relM" unfolding c_p c_q by auto
          with True show ?thesis by auto
        qed
      qed
    qed
    show "primeness_condition_monoid (PM::'a poly monoid)"
    proof (unfold_locales, unfold mk_monoid_simps)
      fix p :: "'a poly"
      assume p: "p \<noteq> 0" and irr: "irreducible p"
      hence p': "?E p \<noteq> 0" by auto
      from irreducible_PM_M_PFM[OF irr] have choice: "degree p = 0 \<and> irreducible (coeff p 0)
        \<or> degree p \<noteq> 0 \<and> irreducible (?E p) \<and> content_ff p =dff 1" by auto
      show "Divisibility.prime PM p"
      proof (rule primeI, unfold mk_monoid_simps units_idom_nz[OF p])
        show "\<not> p dvd 1"
        proof
          assume "p dvd 1"
          from divides_degree[OF this] have dp: "degree p = 0" by auto
          from degree0_coeffs[OF this] p obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
          with choice have irr: "irreducible a" by auto
          from `p dvd 1`[unfolded p const_poly_dvd_1] have "a dvd 1" by auto
          hence "a \<in> Units M" unfolding units_idom_nz[OF a] .
          with irr show False unfolding irreducible_def by auto
        qed
        fix q r :: "'a poly"
        assume q: "q \<noteq> 0" and r: "r \<noteq> 0" and "factor p (q * r)"
        from this[unfolded factor_idom] have "p dvd q * r" by auto
        from iffD1[OF dvd_PM_iff this] have dvd_ct: "divides_ff (content_ff p) (content (?E (q * r)))"
          and dvd_E: "?E p dvd ?E q * ?E r" by auto
        from gauss_lemma[of "?E q" "?E r"] divides_ff_trans[OF dvd_ct, of "content_ff q * content_ff r"]
        have dvd_ct: "divides_ff (content_ff p) (content_ff q * content_ff r)"
          unfolding eq_dff_def by auto
        from choice
        have "p dvd q \<or> p dvd r"
        proof
          assume "degree p \<noteq> 0 \<and> irreducible (?E p) \<and> content_ff p =dff 1"
          hence deg: "degree p \<noteq> 0" and irr: "irreducible (?E p)" and ct: "content_ff p =dff 1" by auto
          from PFM.irreducible_prime[OF _ irr] p have prime: "Divisibility.prime PFM (?E p)" by auto
          note fnz = factor_idom_nz
          from q r have Eq: "?E q \<in> carrier PFM" and Er: "?E r \<in> carrier PFM" 
            and q': "?E q \<noteq> 0" and r': "?E r \<noteq> 0" and qr': "?E q * ?E r \<noteq> 0" by auto
          from PFM.prime_divides[OF Eq Er prime, unfolded fnz[OF q'] fnz[OF r'] fnz[OF qr'] 
            monoid.simps, OF dvd_E]
          have dvd_E: "?E p dvd ?E q \<or> ?E p dvd ?E r" .
          from ct have ct: "divides_ff (content_ff p) 1" unfolding eq_dff_def by auto
          moreover have "\<And> q. divides_ff 1 (content_ff q)" using content_map_poly_embed_ff
            unfolding divides_ff_def by auto
          from divides_ff_trans[OF ct this] have ct: "\<And> q. divides_ff (content_ff p) (content_ff q)" .
          with dvd_E show ?thesis unfolding dvd_PM_iff by blast
        next
          assume "degree p = 0 \<and> irreducible (coeff p 0)"
          hence deg: "degree p = 0" and irr: "irreducible (coeff p 0)" by auto
          from degree0_coeffs[OF deg] p obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
          with irr have irr: "irreducible a" and aM: "a \<in> carrier M" by auto
          from irreducible_prime[OF aM irr] have prime: "Divisibility.prime M a" .
          from content_map_poly_embed_ff obtain cq where cq: "content_ff q = embed_ff cq" by auto
          from content_map_poly_embed_ff obtain cp where cp: "content_ff p = embed_ff cp" by auto
          from content_map_poly_embed_ff obtain cr where cr: "content_ff r = embed_ff cr" by auto
          have "divides_ff (embed_ff a) (content_ff p)" unfolding p content_iff using a by auto
          from divides_ff_trans[OF this[unfolded cp] dvd_ct[unfolded cp cq cr]]
          have "divides_ff (embed_ff a) (embed_ff (cq * cr))" by simp
          hence dvd: "a dvd cq * cr" by simp
          from content_divides_ff[of "embed_ff a" "?E p"] have "divides_ff (embed_ff cp) (embed_ff a)"
            using cp a p by auto
          hence cpa: "cp dvd a" by simp
          from a q r cq cr have aM: "a \<in> carrier M" and qM: "cq \<in> carrier M" and rM: "cr \<in> carrier M"
            and q': "cq \<noteq> 0" and r': "cr \<noteq> 0" and qr': "cq * cr \<noteq> 0" 
            by auto
          note fnz = factor_idom_nz
          from prime_divides[OF qM rM prime, unfolded fnz[OF q'] fnz[OF r'] fnz[OF qr'] monoid.simps, OF dvd]
          have "a dvd cq \<or> a dvd cr" .
          with dvd_trans[OF cpa] have dvd: "cp dvd cq \<or> cp dvd cr" by auto
          have "\<And> q. ?E p * (smult (inverse (embed_ff a)) q) = q" unfolding p using a by (auto simp: one_poly_def)
          hence Edvd: "\<And> q. ?E p dvd q" unfolding dvd_def by metis
          from dvd Edvd show ?thesis unfolding dvd_PM_iff cp cq cr by simp
        qed
        thus "factor p q \<or> factor p r" unfolding factor_idom using p q r by auto
      qed
    qed
  qed
qed

end

instance poly :: (ufd) ufd
  by (intro_classes, rule ufd_loc.factorial_monoid_poly)

lemma dvd_factor_mult_gcd: fixes p :: "'a :: ufd"
  assumes dvd: "k dvd p * q" "k dvd p * r" 
    and q: "q \<noteq> 0" and r: "r \<noteq> 0"
  shows "k dvd p * somegcd mk_monoid q r" 
proof (cases "p = 0")
  case True
  thus ?thesis by auto
next
  interpret ufd_loc.
  case False note p = this
  from p q dvd have k: "k \<noteq> 0" by auto
  have p': "p \<in> carrier M" and q': "q \<in> carrier M" and r': "r \<in> carrier M" and k': "k \<in> carrier M"
    and pq: "p * q \<noteq> 0" and pr: "p * r \<noteq> 0"
    using p q r k by auto
  let ?qr = "somegcd M q r"
  let ?pqpr = "somegcd M (p * q) (p * r)"
  note fnz = factor_idom_nz
  from q' r' have qr': "?qr \<in> carrier M" by (rule gcd_closed)
  hence qr: "?qr \<noteq> 0" by simp
  have pqpr': "?pqpr \<in> carrier M" by (rule gcd_closed, insert pq pr, auto)
  hence pqpr: "?pqpr \<noteq> 0" by simp
  from gcd_divides[of k "p * q" "p * r", unfolded fnz[OF pq] fnz[OF pr] fnz[OF pqpr] mk_monoid_simps, 
    OF dvd pq pr k]
  have kpqpr: "k dvd ?pqpr" .
  from gcd_mult[of q r p, unfolded mk_monoid_simps, OF q r p]
  have "associated M (p * ?qr) ?pqpr" .
  hence "factor ?pqpr (p * ?qr)" unfolding associated_def by blast
  from this[unfolded factor_idom] p qr have "?pqpr dvd (p * ?qr)" by auto
  from dvd_trans[OF kpqpr this] show dvd: "k dvd p * ?qr" .
qed



definition coprime_idom :: "'a :: idom \<Rightarrow> 'a \<Rightarrow> bool" ("coprime\<^sub>I") where
  "coprime\<^sub>I p q \<equiv> \<forall>r. r dvd p \<longrightarrow> r dvd q \<longrightarrow> r dvd 1"

lemma coprime_idom_commute: "coprime\<^sub>I p q \<longleftrightarrow> coprime\<^sub>I q p" unfolding coprime_idom_def by auto

lemma coprime_mult_cross_dvd:
  fixes p q :: "'a :: ufd"
  assumes coprime: "coprime\<^sub>I p q" and eq: "p' * p = q' * q" and p: "p \<noteq> 0" and q: "q \<noteq> 0"
  shows "p dvd q' \<and> q dvd p'"
proof -
  {
    interpret ufd_loc.
    fix p q r p' q' :: 'a
    assume cop: "coprime\<^sub>I p q" and eq: "p' * p = q' * q" and p: "p \<noteq> 0" and q: "q \<noteq> 0"
       and r: "r dvd p" "r dvd q"
    let ?gcd = "somegcd mk_monoid q p"
    from eq have "p' * p dvd q' * q" by auto
    hence d1: "p dvd q' * q" by (rule comm_monoid_mult_class.dvd_mult_right)
    have d2: "p dvd q' * p" by auto
    from dvd_factor_mult_gcd[OF d1 d2 q p] have 1: "p dvd q' * ?gcd" .
    note fnz = factor_idom_nz
    from gcd_divides_l[of q p, unfolded mk_monoid_simps fnz[OF q], OF q p] have 2: "?gcd dvd q" .
    from gcd_divides_r[of q p, unfolded mk_monoid_simps fnz[OF p], OF q p] have 3: "?gcd dvd p" .
    from cop[unfolded coprime_idom_def, rule_format, OF 3 2] have "?gcd dvd 1" .
    with 1 have "p dvd q'" by algebra
  } note main = this
  from main[OF coprime eq p q,of 1] coprime coprime_idom_commute main[OF _ eq[symmetric] q p, of 1]
  show ?thesis by auto
qed

lemma coprime_idom_prime_divisorI:
  assumes no_prime_divisor: "\<And> r :: 'a :: ufd. r dvd p \<Longrightarrow> r dvd q 
    \<Longrightarrow> (\<And> s t. r dvd s * t \<Longrightarrow> r dvd s \<or> r dvd t) \<Longrightarrow> r dvd 1"
  shows "coprime\<^sub>I p q" unfolding coprime_idom_def
proof (intro allI impI)
  interpret ufd_loc.
  fix r
  assume rp: "r dvd p" and rq: "r dvd q"
  show "r dvd 1"
  proof (cases "r = 0")
    case True
    with rp rq have "p = 0" "q = 0" by auto
    from no_prime_divisor[unfolded this, of 0] have "0 dvd (1 :: 'a)" by auto
    thus ?thesis by auto
  next
    case False note r = this
    show "r dvd 1"
    proof (rule ccontr)
      assume r1: "\<not> r dvd 1"
      from r1 have rU: "r \<notin> Units M" unfolding units_idom_nz[OF r] .
      from factors_exist[OF _ rU] r obtain fs where fsC: "set fs \<subseteq> carrier M" 
        and fact: "factors fs r" by auto
      from fact[unfolded factors] have prod: "monoid_mult_class.listprod fs = r"
        and irr: "Ball (set fs) irreducible" by auto
      from prod r1 obtain f ffs where fs: "fs = f # ffs" by (cases fs, auto)
      with irr have irr: "irreducible f" by auto
      from fs fsC have fC: "f \<in> carrier M" and f: "f \<noteq> 0" by auto
      from prod[unfolded fs] have fr: "f dvd r" by auto
      from fr rp have fp: "f dvd p" by (rule comm_monoid_mult_class.dvd_trans)
      from fr rq have fq: "f dvd q" by (rule comm_monoid_mult_class.dvd_trans)
      from irreducible_prime[OF fC irr] have pf: "Divisibility.prime M f" .
      from primeE[OF pf] have f1: "\<not> f dvd 1" unfolding units_idom_nz[OF f] by metis
      have "f dvd 1"
      proof (rule no_prime_divisor[OF fp fq])
        fix s t
        assume fst: "f dvd s * t"
        show "f dvd s \<or> f dvd t"
        proof (cases "s = 0 \<or> t = 0")
          case False
          hence s: "s \<noteq> 0" and t: "t \<noteq> 0" and st: "s * t \<noteq> 0" by auto
          note fnz = factor_idom_nz
          from pf[unfolded Divisibility.prime_def, THEN conjunct2, rule_format, 
            unfolded mk_monoid_simps, OF s t, unfolded fnz[OF s] fnz[OF t] fnz[OF st], OF fst]          
          show ?thesis .
        qed auto
      qed
      with f1 show False ..
    qed
  qed
qed

lemma not_coprime_iff_common_factor:
  fixes p q :: "'a :: ufd"
  shows "\<not> coprime\<^sub>I p q \<longleftrightarrow> (\<exists>r. r dvd p \<and> r dvd q \<and> \<not> r dvd 1)"
  unfolding coprime_idom_def by auto

hide_const irreducible
hide_fact irreducible_def

end

