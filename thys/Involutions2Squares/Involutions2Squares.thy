

theory Involutions2Squares
imports Main
begin


section \<open>A few basic properties\<close>

lemma nat_sqr : 
  shows "nat(n\<^sup>2) = (nat(abs n))\<^sup>2"
  by(rule int_int_eq[THEN iffD1], simp)


lemma nat_mod_int : 
  assumes "n mod m = k" 
  shows "int n mod int m = int k"
  by (metis assms of_nat_mod)


lemma sqr_geq_nat : 
  shows "(n::nat) \<le> n\<^sup>2"
  using power2_nat_le_imp_le by simp


lemma sqr_geq_abs : 
  shows "abs(n::int) \<le> n\<^sup>2"
proof(rule nat_le_eq_zle[THEN iffD1], simp)
  show "nat \<bar>n\<bar> \<le> nat (n\<^sup>2)"
    using nat_sqr sqr_geq_nat by presburger
qed


lemma sqr_fix_nat :
  assumes "(n::nat) = n\<^sup>2"
  shows "n = 0 \<or> n = 1"
  using assms numeral_2_eq_2 by fastforce


lemma card1 :
  shows "(card{a, b} = Suc 0) = (a = b)"
  using singleton_insert_inj_eq' by fastforce

lemma card2 :
  shows "card{a, b} \<ge> Suc 0 \<and> card{a, b} \<le> 2"
  by (simp add: card_insert_if) 




section \<open>The relevant properties of involutions\<close>

definition "involution_on A \<phi> = (\<phi> ` A \<subseteq> A \<and> (\<forall>x\<in>A. \<phi>(\<phi> x) = x))"


lemma involution_bij :
  assumes "involution_on A \<phi>"
  shows "bij_betw \<phi> A A"
  using assms bij_betw_byWitness involution_on_def by fast


lemma involution_sub_bij :
  assumes "involution_on A \<phi>" 
      and "S \<subseteq> A" 
      and "\<forall>x\<in>A. (x \<in> S) = (\<phi> x \<notin> S)"
 shows "bij_betw \<phi> S (A - S)"
proof(simp add: bij_betw_def, rule conjI)
  show "inj_on \<phi> S"
    by (meson assms bij_betw_def inj_on_subset involution_bij) 
next
  show "\<phi> ` S = A - S"
  proof(rule set_eqI, clarsimp)
    fix x show "(x \<in> \<phi> ` S) = (x \<in> A \<and> x \<notin> S)" (is "?L = ?R")
    proof
      assume ?L thus ?R
        by(metis assms bij_betw_imp_surj_on f_inv_into_f image_eqI inv_into_into involution_bij subset_iff)
    next
      assume ?R thus ?L
        by (metis assms(1) assms(3) image_iff involution_on_def)  
    qed
  qed
qed



lemma involution_sub_card :
  assumes "involution_on A \<phi>"
      and "finite A"
      and "S \<subseteq> A" 
      and "\<forall>x\<in>A. (x \<in> S) = (\<phi> x \<notin> S)"
    shows "2 * card S = card A"
proof -
  have "card S = card (A - S)"
    using assms bij_betw_same_card involution_sub_bij by blast

  also have "... = card A - card S"
    by (meson assms card_Diff_subset rev_finite_subset)

  finally show ?thesis by simp
qed




subsection \<open>Unions of preimage/image sets, fixed points\<close>

definition "preimg_img_on A \<phi> = (\<Union>x\<in>A. {{x, \<phi> x}})"
definition "fixpoints_on A \<phi> = {x\<in>A. \<phi> x = x}"


lemma preimg_img_on_Union :
  assumes "\<phi> ` A \<subseteq> A"
  shows "A = \<Union>(preimg_img_on A \<phi>)"
  using assms by(fastforce simp: preimg_img_on_def) 

lemma preimg_img_on_finite :
  assumes "finite A"
  shows "finite (preimg_img_on A \<phi>)"
  by(simp add: assms preimg_img_on_def)

lemma fixpoints_on_finite :
  assumes "finite A"
  shows "finite (fixpoints_on A \<phi>)"
  by(simp add: assms fixpoints_on_def)

lemma preimg_img_on_card :
  assumes "x \<in> preimg_img_on A \<phi>"
  shows "1 \<le> card x \<and> card x \<le> 2"
  using assms by(fastforce simp: preimg_img_on_def card2)



corollary preimg_img_on_eq :
  shows "preimg_img_on A \<phi> = {x \<in> preimg_img_on A \<phi>. card x = 1} \<union> 
                              {x \<in> preimg_img_on A \<phi>. card x = 2}"
proof(rule equalityI[rotated 1], clarsimp+)
  fix x assume "card x \<noteq> 2" and "x \<in> preimg_img_on A \<phi>"
  thus "card x = Suc 0"
    using preimg_img_on_card by fastforce
qed


lemma fixpoints_on_card_eq :
  shows "card(fixpoints_on A \<phi>) = card {x \<in> preimg_img_on A \<phi>. card x = 1}"
proof -
  have "bij_betw (\<lambda>x. {x}) (fixpoints_on A \<phi>) 
                           {x. x \<in> preimg_img_on A \<phi> \<and> card x = 1}"
    by(fastforce simp: bij_betw_def fixpoints_on_def preimg_img_on_def card1)
  thus ?thesis by(rule bij_betw_same_card)
qed


lemma preimg_img_on_disjoint :
  assumes "involution_on A \<phi>"
  shows "pairwise disjnt (preimg_img_on A \<phi>)"
proof(clarsimp simp: pairwise_def disjnt_def preimg_img_on_def)
  fix u v assume b: "u \<in> A" and c: "v \<in> A" and d: "{u, \<phi> u} \<noteq> {v, \<phi> v}"
  hence e: "u \<noteq> v" by clarsimp
  with b and c have f: "\<phi> u \<noteq> \<phi> v" by (metis assms involution_on_def) 
  have "(\<phi> v = u) = (v = \<phi> u)" by (metis assms b c involution_on_def) 
  with d have "\<phi> v \<noteq> u \<and> v \<noteq> \<phi> u" by fastforce 
  with e and f show "v \<noteq> u \<and> v \<noteq> \<phi> u \<and> \<phi> v \<noteq> u \<and> \<phi> v \<noteq> \<phi> u" by simp
qed



theorem involution_dom_card_sum :
  assumes "involution_on A \<phi>"
      and "finite A"
    shows "card A = card (fixpoints_on A \<phi>) + 
                    2 * card {x \<in> preimg_img_on A \<phi>. card x = 2}" 
proof -
  have eq: "{x \<in> preimg_img_on A \<phi>. card x = Suc 0} \<inter> 
           {x \<in> preimg_img_on A \<phi>. card x = 2} = {}"
    by fastforce

  have f1 : "finite {x \<in> preimg_img_on A \<phi>. card x = 1}"
    by (simp add: assms preimg_img_on_finite)
  have f2 : "finite {x \<in> preimg_img_on A \<phi>. card x = 2}"
    by (simp add: assms preimg_img_on_finite)

  have "card A = card (\<Union>(preimg_img_on A \<phi>))"
    by (metis assms(1) involution_on_def preimg_img_on_Union) 

  also have "... = sum card (preimg_img_on A \<phi>)"
    by (metis assms(1) card_Union_disjoint card_eq_0_iff not_one_le_zero preimg_img_on_card 
        preimg_img_on_disjoint)

  also have "... = sum card ({x \<in> preimg_img_on A \<phi>. card x = 1} \<union> 
                             {x \<in> preimg_img_on A \<phi>. card x = 2})"
    by (metis preimg_img_on_eq)

  also have "... = sum card {x \<in> preimg_img_on A \<phi>. card x = 1} + 
                   sum card {x \<in> preimg_img_on A \<phi>. card x = 2}"
    by (metis (no_types, lifting) Collect_cong One_nat_def eq f1 f2 sum.union_disjoint)

  also have "... = card (fixpoints_on A \<phi>) + 
                   2 * card {x \<in> preimg_img_on A \<phi>. card x = 2}"
    by(simp add: fixpoints_on_card_eq)

  finally show ?thesis .
qed


corollary involution_dom_fixpoints_parity :
  assumes "involution_on A \<phi>" 
      and "finite A"
 shows "odd(card A) = odd(card(fixpoints_on A \<phi>))"
  using assms involution_dom_card_sum by fastforce




section \<open>Primes and the two squares theorem\<close>

definition "is_prime (n :: nat) = (n > 1 \<and> (\<forall>d. d dvd n \<longrightarrow> d = 1 \<or> d = n))"

lemma prime_factors :
  assumes "is_prime p"
      and "p = n * m" 
    shows "(n = 1 \<and> m = p) \<or> (n = p \<and> m = 1)"
using assms proof(clarsimp simp: is_prime_def)
  assume "\<forall>d. d dvd n * m \<longrightarrow> d = Suc 0 \<or> d = n * m"
  hence a: "n = Suc 0 \<or> n = n * m \<and> m = Suc 0 \<or> m = n * m"
    by (meson dvd_triv_left dvd_triv_right)
  assume "0 < n \<and> Suc 0 \<noteq> m \<or> m \<noteq> Suc 0" and "Suc 0 < n*m"
  with a show "n = Suc 0 \<and> (m = 0 \<or> Suc 0 = n)" by fastforce
qed

lemma prime_not_sqr : 
  assumes "is_prime p"
  shows "p \<noteq> n\<^sup>2"
  by (metis assms is_prime_def order_less_irrefl power2_eq_square prime_factors)

lemma int_prime_not_sqr : 
  assumes "is_prime p"
  shows "int p \<noteq> n\<^sup>2"
  by (metis assms nat_int nat_sqr prime_not_sqr)

lemma prime_gr4 :
  assumes "is_prime p"
      and "p mod 4 = 1"
    shows "p > 4"
proof(rule ccontr, drule leI)
  assume "p \<le> 4"
  thus False
    by (metis assms dvd_imp_mod_0 dvd_triv_left is_prime_def mod_less mult.right_neutral 
        order_less_le zero_neq_one) 
qed




theorem two_squares :
  assumes a: "is_prime p" 
      and b: "p mod 4 = 1"
    shows "\<exists>n m. p = n\<^sup>2 + m\<^sup>2"
proof -
  let ?S  =  "{(u, v, w). int p = 4 * u * v + w\<^sup>2 \<and> u > 0 \<and> v > 0}"
  let ?T  =  "?S \<inter> {(u, v, w). w > 0}"
  let ?U  =  "?S \<inter> {(u, v, w). u - v + w > 0}"
  let ?f  =  "\<lambda>(u, v, w). (v, u, -w)"
  let ?g  =  "\<lambda>(u, v, w). (u - v + w, v, 2 * v - w)"
  let ?h  =  "\<lambda>(u, v, w). (v, u, w)"

  have w_neq0 : "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> w \<noteq> 0" 
  proof clarsimp
    fix u v assume "int p = 4 * u * v" 
    hence "4 dvd int p" by simp
    hence "4 dvd p" by presburger
    with b show False by simp
  qed

  have fin_S : "finite ?S"
  proof -
    have uv_comm : "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> (v, u, w) \<in> ?S" by simp

    have bound1 : "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> u \<le> (int p - 1) div 4"
    proof clarsimp
      fix u v w assume 1: "int p = 4 * u * v + w\<^sup>2" and 2: "(0::int) < v" and 3: "(0::int) < u"
      with 2 and 3 have 4: "4 * u \<le> 4 * u * v" by simp
      have "w \<noteq> (0::int)" using 1 2 3 w_neq0 by simp
      hence "1 \<le> w\<^sup>2"
        by (metis add_0 linorder_not_le power2_less_eq_zero_iff zless_imp_add1_zle)
      with 4 have 5: "4 * u \<le> 4 * u * v + w\<^sup>2 - 1" by simp
      note zdiv_mono1[OF 5, where b="4::int", simplified]
      thus "u \<le> (4 * u * v + w\<^sup>2 - 1) div 4" .
    qed

    have bound2 : "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> v \<le> (int p - 1) div 4"
      using bound1 uv_comm by blast

    have bound3 : "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> \<bar>w\<bar> \<le> int p"
    proof clarsimp
      fix u v w::int 
      have 1: "\<bar>w\<bar> \<le> w\<^sup>2" by(rule sqr_geq_abs)
      assume "(0::int) < u" and "(0::int) < v"
      hence "0 < u * v" by(rule mult_pos_pos)
      hence "0 \<le> u * v" by simp
      hence "w\<^sup>2 \<le> 4 * u * v + w\<^sup>2" by simp 
      with 1 show "\<bar>w\<bar> \<le> 4 * u * v + w\<^sup>2" by simp 
    qed

    let ?prod = "{1..(int p - 1) div 4} \<times> {1..(int p - 1) div 4} \<times> {- int p..int p}"

    have prod: "\<forall>u v w. (u, v, w) \<in> ?S \<longrightarrow> (u, v, w) \<in> ?prod"
    proof(intro allI)
      fix u v w show "(u, v, w) \<in> ?S \<longrightarrow> (u, v, w) \<in> ?prod"
      proof(rule impI)
        assume 1: "(u, v, w) \<in> ?S"
        note bound1[rule_format, OF 1] and
             bound2[rule_format, OF 1] 
        with 1 show "(u, v, w) \<in> ?prod" 
        proof simp
          have "\<bar>w\<bar> \<le> int p" by(rule bound3[rule_format, OF 1])
          hence "w \<le> int p \<and> -w \<le> int p" by(rule abs_le_iff[THEN iffD1])
          with 1 show "- (4 * u * v) - w\<^sup>2 \<le> w \<and> w \<le> 4 * u * v + w\<^sup>2" by simp
        qed
      qed
    qed

    show ?thesis
    proof(rule_tac B="?prod" in finite_subset)
      show "?S \<subseteq> ?prod" using prod by fast
    next
      show "finite ?prod" by simp
    qed
  qed

  have inv1 : "involution_on ?S ?f"
    by(clarsimp simp: involution_on_def)

  have inv2 : "involution_on ?U ?g"
    by(fastforce simp: involution_on_def int_distrib power2_diff power2_eq_square)

  have inv3 : "involution_on ?T ?h"
    by(fastforce simp: involution_on_def)

  have part1 : "\<forall>x\<in>?S. (x \<in> ?T) = (?f x \<notin> ?T)"
  proof clarsimp
    fix u v w assume 1: "int p = 4 * u * v + w\<^sup>2" and 2: "(0::int) < v" and 3: "(0::int) < u"
    have "w \<noteq> 0" 
    proof(rule w_neq0[rule_format])
      from 1 2 3 show "(u, v, w) \<in> ?S" by simp
    qed
    thus "(0 < w) = (\<not> w < 0)" by fastforce
  qed
  
  have part2 : "\<forall>x\<in>?S. (x \<in> ?U) = (?f x \<notin> ?U)"
  proof clarsimp
    fix u v w assume 1: "int p = 4 * u * v + w\<^sup>2" and 2: "u > 0" and 3: "v > 0" 
    show "(0 < u - v + w) = (\<not> w < v - u)" (is "?L = ?R")
    proof
      assume ?L with 2 and 3 show ?R by fastforce 
    next
      assume ?R hence 4: "v - u \<le> w" by simp
      show ?L
      proof(rule ccontr)
        assume "\<not> ?L" with 4 have "w = v - u" by fastforce
        with 1 have "int p = 4 * u * v + (v - u)\<^sup>2" by fast
        then have sqr : "int p = (v + u)\<^sup>2" by(simp add: power2_diff power2_sum)
        with int_prime_not_sqr[OF a] show False ..
      qed
    qed
  qed

  have card_eq : "card ?T = card ?U"
  proof -
    have 1: "2*card ?T = card ?S"
      by (smt (verit, ccfv_SIG) Int_iff fin_S inv1 involution_sub_card part1 subsetI)
    have "2*card ?U = card ?S"
      by (smt (verit, ccfv_SIG) Int_iff fin_S inv1 involution_sub_card part2 subsetI)
    with 1 show ?thesis by simp
  qed

  have fixp: "fixpoints_on ?U ?g = {((int p - 1) div 4, 1, 1)}" (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof(clarsimp simp: fixpoints_on_def)
      fix u v assume 1: "int p = 4 * u * v + v\<^sup>2" and 2: "0 < u" and 3: "0 < v"
      then have 4: "int p = v * (4 * u + v)" 
        by(simp add: power2_eq_square int_distrib)
      have 5: "p = nat v * (4 * nat u + nat v)" 
      proof(rule int_int_eq[THEN iffD1])
        show "int p = int (nat v * (4 * nat u + nat v))"
          using 2 3 proof(simp add: 4)
        qed
      qed
      note prime_factors[OF a 5]
      then show "u = (4 * u * v + v\<^sup>2 - 1) div 4 \<and> v = 1"
      proof
        assume "nat v = 1 \<and> 4 * nat u + nat v = p"
        with 2 and 3 have "v = 1 \<and> 4 * u + v = int p" by fastforce
        thus ?thesis by simp
      next
        assume "nat v = p \<and> 4 * nat u + nat v = 1"
        with 2 have False by fastforce
        thus ?thesis ..
      qed
    qed
  next
    show "?R \<subseteq> ?L"
    proof(clarsimp simp: fixpoints_on_def, rule conjI)
      show "int p = 4 * ((int p - 1) div 4) + 1"
      proof(subst dvd_mult_div_cancel)
        show "4 dvd int p - 1"
        proof(subst mod_eq_dvd_iff[THEN sym])
          show "int p mod 4 = 1 mod 4" by(simp add: nat_mod_int[OF b, simplified])
        qed
      next
        show "int p = int p - 1 + 1" by simp
      qed
    next
      show "0 < (int p - 1) div 4"
        using a b prime_gr4 by fastforce
    qed
  qed

  have cardS1 : "odd(card ?T)"
  proof(subst card_eq)
    show "odd(card ?U)"
      using add_diff_cancel_right' fin_S fixp inv2 involution_dom_fixpoints_parity by fastforce
  qed

  have fixp_ex : "\<exists>x. x \<in> fixpoints_on ?T ?h"
  proof(rule ccontr)
    assume "\<not> ?thesis" hence 1: "fixpoints_on ?T ?h = {}" by fast
    note involution_dom_card_sum[OF inv3, simplified 1]
    hence "even(card ?T)" by (simp add: fin_S) 
    with cardS1 show False ..
  qed

  note fixp_ex then have "\<exists>u w. u > 0 \<and> w > 0 \<and> int p = 4 * u * u + w\<^sup>2" 
    by(clarsimp simp: fixpoints_on_def, fast)
  then obtain u w where c: "u > 0 \<and> w > 0 \<and> int p = (2 * u)\<^sup>2 + w\<^sup>2"
    by(fastforce simp: power2_eq_square)
  hence "p = (nat(2 * u))\<^sup>2 + (nat w)\<^sup>2"
    by (smt (verit) int_nat_eq nat_int nat_int_add of_nat_power)
  thus ?thesis by fast

qed



end