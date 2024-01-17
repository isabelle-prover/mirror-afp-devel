section \<open>Rabin's test for irreducible polynomials\<close>

theory Rabin_Irreducibility_Test
  imports Card_Irreducible_Polynomials_Aux
begin

text \<open>This section introduces an effective test for irreducibility of polynomials
(in finite fields) based on Rabin~\cite[rabin1980].\<close>

definition pcoprime :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("pcoprime\<index>")
  where "pcoprime\<^bsub>R\<^esub> p q =
    (\<forall>r \<in> carrier (poly_ring R). r pdivides\<^bsub>R\<^esub> p \<and> r pdivides\<^bsub>R\<^esub> q \<longrightarrow> degree r = 0)"

lemma pcoprimeI:
  assumes "\<And>r. r \<in> carrier (poly_ring R) \<Longrightarrow> r pdivides \<^bsub>R\<^esub> p \<Longrightarrow> r pdivides\<^bsub>R\<^esub> q \<Longrightarrow> degree r = 0"
  shows "pcoprime\<^bsub>R\<^esub> p q"
  using assms unfolding pcoprime_def by auto

context field
begin

interpretation r:polynomial_ring R "(carrier R)"
  unfolding polynomial_ring_def polynomial_ring_axioms_def
  using carrier_is_subfield field_axioms by force

lemma pcoprime_one: "pcoprime\<^bsub>R\<^esub> p \<one>\<^bsub>poly_ring R\<^esub>"
proof (rule pcoprimeI)
  fix r
  assume r_carr: "r \<in> carrier (poly_ring R)"
  moreover assume "r pdivides \<^bsub>R\<^esub> \<one>\<^bsub>poly_ring R\<^esub>"
  moreover have "\<one>\<^bsub>poly_ring R\<^esub> \<noteq> []" by (simp add:univ_poly_one)
  ultimately have "degree r \<le> degree \<one>\<^bsub>poly_ring R\<^esub>"
    by (intro pdivides_imp_degree_le[OF carrier_is_subring] r_carr) auto
  also have "... = 0" by (simp add:univ_poly_one)
  finally show "degree r = 0" by auto
qed

lemma pcoprime_left_factor:
  assumes "x \<in> carrier (poly_ring R)"
  assumes "y \<in> carrier (poly_ring R)"
  assumes "z \<in> carrier (poly_ring R)"
  assumes "pcoprime\<^bsub>R\<^esub> (x \<otimes>\<^bsub>poly_ring R\<^esub> y) z"
  shows "pcoprime\<^bsub>R\<^esub> x z"
proof (rule pcoprimeI)
  fix r
  assume r_carr: "r \<in> carrier (poly_ring R)"
  assume "r pdivides \<^bsub>R\<^esub> x"
  hence "r pdivides  \<^bsub>R\<^esub> (x \<otimes>\<^bsub>poly_ring R\<^esub> y)"
    using assms(1,2) r_carr r.p.divides_prod_r unfolding pdivides_def by simp
  moreover assume "r pdivides \<^bsub>R\<^esub> z"
  ultimately show "degree r = 0" using assms(4) r_carr unfolding pcoprime_def by simp
qed

lemma pcoprime_sym:
  shows "pcoprime x y = pcoprime y x"
  unfolding pcoprime_def by auto

lemma pcoprime_left_assoc_cong_aux:
  assumes "x1 \<in> carrier (poly_ring R)" "x2 \<in> carrier (poly_ring R)"
  assumes "x2 \<sim>\<^bsub>poly_ring R\<^esub> x1"
  assumes "y \<in> carrier (poly_ring R)"
  assumes "pcoprime x1 y"
  shows "pcoprime x2 y"
  using assms r.p.divides_cong_r[OF _ assms(3)] unfolding pcoprime_def pdivides_def by simp

lemma pcoprime_left_assoc_cong:
  assumes "x1 \<in> carrier (poly_ring R)" "x2 \<in> carrier (poly_ring R)"
  assumes "x1 \<sim>\<^bsub>poly_ring R\<^esub> x2"
  assumes "y \<in> carrier (poly_ring R)"
  shows "pcoprime x1 y = pcoprime x2 y"
  using assms pcoprime_left_assoc_cong_aux r.p.associated_sym by metis

lemma pcoprime_right_assoc_cong:
  assumes "x1 \<in> carrier (poly_ring R)" "x2 \<in> carrier (poly_ring R)"
  assumes "x1 \<sim>\<^bsub>poly_ring R\<^esub> x2"
  assumes "y \<in> carrier (poly_ring R)"
  shows "pcoprime y x1 = pcoprime y x2"
  using assms pcoprime_sym pcoprime_left_assoc_cong by metis

lemma pcoprime_step:
  assumes "f \<in> carrier (poly_ring R)"
  assumes "g \<in> carrier (poly_ring R)"
  shows "pcoprime f g \<longleftrightarrow> pcoprime g (f pmod g)"
proof -
  have "d pdivides f \<longleftrightarrow> d pdivides (f pmod g)" if "d \<in> carrier (poly_ring R)" "d pdivides g" for d
  proof -
    have "d pdivides f \<longleftrightarrow> d pdivides (g \<otimes>\<^bsub>r.P\<^esub> (f pdiv g) \<oplus>\<^bsub>r.P\<^esub> (f pmod g))"
      using pdiv_pmod[OF carrier_is_subfield assms] by simp
    also have "... \<longleftrightarrow> d pdivides ((f pmod g))"
      using that assms long_division_closed[OF carrier_is_subfield] r.p.divides_prod_r
      unfolding pdivides_def by (intro r.p.div_sum_iff) simp_all
    finally show ?thesis by simp
  qed
  hence "d pdivides f \<and> d pdivides g \<longleftrightarrow> d pdivides g \<and> d pdivides (f pmod g)"
    if "d \<in> carrier (poly_ring R)" for d
    using that by auto
  thus ?thesis
    unfolding pcoprime_def by auto
qed

lemma pcoprime_zero_iff:
  assumes "f \<in> carrier (poly_ring R)"
  shows "pcoprime f [] \<longleftrightarrow> length f = 1"
proof -
  consider (i) "length f = 0" | (ii) "length f = 1" | (iii) "length f > 1"
    by linarith
  thus ?thesis
  proof (cases)
    case i
    hence "f = []" by simp
    moreover have "X pdivides []" using r.pdivides_zero r.var_closed(1) by blast
    moreover have "degree X = 1" using degree_var by simp
    ultimately have "\<not>pcoprime f []" using r.var_closed(1) unfolding pcoprime_def by auto
    then show ?thesis using i by auto
  next
    case ii
    hence "f \<noteq> []" "degree f = 0" by auto
    hence "degree d = 0" if "d pdivides f" "d \<in> carrier (poly_ring R)" for d
      using that(1) pdivides_imp_degree_le[OF carrier_is_subring that(2) assms] by simp
    hence "pcoprime f []" unfolding pcoprime_def by auto
    then show ?thesis using ii by simp
  next
    case iii
    have "f pdivides f" using assms unfolding pdivides_def by simp
    moreover have "f pdivides []" using assms r.pdivides_zero by blast
    moreover have "degree f > 0" using iii by simp
    ultimately have "\<not>pcoprime f []" using assms unfolding pcoprime_def by auto
    then show ?thesis using iii by auto
  qed
qed

end

context finite_field
begin

interpretation r:polynomial_ring R "(carrier R)"
  unfolding polynomial_ring_def polynomial_ring_axioms_def
  using carrier_is_subfield field_axioms by force

lemma exists_irreducible_proper_factor:
  assumes "monic_poly R f" "degree f > 0" "\<not>monic_irreducible_poly R f"
  shows "\<exists>g. monic_irreducible_poly R g \<and> g pdivides\<^bsub>R\<^esub> f \<and> degree g < degree f"
proof -
  define S where "S = {d. monic_irreducible_poly R d \<and> 0 < pmult d f}"

  have f_carr: "f \<in> carrier (poly_ring R)" "f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>"
    using assms(1) unfolding monic_poly_def univ_poly_zero by auto

  have "S \<noteq> {}"
  proof (rule ccontr)
    assume S_empty: "\<not>(S \<noteq> {})"
    have "f = (\<Otimes>\<^bsub>poly_ring R\<^esub>d\<in>S. d [^]\<^bsub>poly_ring R\<^esub> pmult d f)"
      unfolding S_def by (intro factor_monic_poly assms(1))
    also have "... = \<one>\<^bsub>poly_ring R\<^esub>" using S_empty by simp
    finally have "f = \<one>\<^bsub>poly_ring R\<^esub>" by simp
    hence "degree f = 0" using degree_one by simp
    thus "False" using assms(2) by simp
  qed
  then obtain g where g_irred: "monic_irreducible_poly R g" and "0 < pmult g f"
    unfolding S_def by auto

  hence "1 \<le> pmult g f" by simp

  hence g_div: "g pdivides f" using multiplicity_ge_1_iff_pdivides f_carr g_irred by blast

  then obtain h where f_def: "f = g \<otimes>\<^bsub>poly_ring R\<^esub> h" and h_carr:"h \<in> carrier (poly_ring R)"
    unfolding pdivides_def by auto

  have g_nz: "g \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>" and h_nz: "h \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>"
    and g_carr: "g \<in> carrier (poly_ring R)"
    using f_carr(2) h_carr g_irred unfolding f_def monic_irreducible_poly_def monic_poly_def
    by auto

  have "degree f = degree g + degree h"
    using g_nz h_nz g_carr h_carr unfolding f_def by (intro degree_mult[OF r.K_subring]) auto
  moreover have "degree h > 0"
  proof (rule ccontr)
    assume "\<not>(degree h > 0)"
    hence "degree h = 0" by simp
    hence "h \<in> Units (poly_ring R)"
      using h_carr h_nz by (simp add: carrier_is_subfield univ_poly_units' univ_poly_zero)
    hence "f \<sim>\<^bsub>poly_ring R\<^esub> g"
      unfolding f_def using g_carr r.p.associatedI2' by force
    hence "f \<sim>\<^bsub>mult_of (poly_ring R)\<^esub> g"
      using f_carr g_nz g_carr by (simp add: r.p.assoc_iff_assoc_mult)
    hence "f = g"
      using monic_poly_not_assoc assms(1) g_irred unfolding monic_irreducible_poly_def by simp
    hence "monic_irreducible_poly R f"
      using g_irred by simp
    thus "False"
      using assms(3) by auto
  qed
  ultimately have "degree g < degree f" by simp
  thus ?thesis using g_irred g_div by auto
qed

theorem rabin_irreducibility_condition:
  assumes "monic_poly R f" "degree f > 0"
  defines "N \<equiv> {degree f div p | p . Factorial_Ring.prime p \<and> p dvd degree f}"
  shows "monic_irreducible_poly R f \<longleftrightarrow>
    (f pdivides gauss_poly R (order R^degree f) \<and> (\<forall>n \<in> N. pcoprime (gauss_poly R (order R^n)) f))"
    (is "?L \<longleftrightarrow> ?R1 \<and> ?R2")
proof -
  have f_carr: "f \<in> carrier (poly_ring R)"
    using assms(1) unfolding monic_poly_def by blast

  have "?R1" if "?L"
    using div_gauss_poly_iff[where n="degree f"] that assms(2) by simp
  moreover have "False" if cthat:"\<not>pcoprime (gauss_poly R (order R^n)) f" "?L" "n \<in> N" for n
  proof -
    obtain d where d_def:
      "d pdivides f"
      "d pdivides (gauss_poly R (order R^n))" "degree d > 0" "d \<in> carrier (poly_ring R)"
      using cthat(1) unfolding pcoprime_def by auto

    obtain p where p_def:
      "n = degree f div p" "Factorial_Ring.prime p" "p dvd degree f"
      using cthat(3) unfolding N_def by auto

    have n_gt_0: "n > 0"
      using p_def assms(2) by (metis dvd_div_eq_0_iff gr0I)

    have "d \<notin> Units (poly_ring R)"
      using d_def(3,4)  univ_poly_units'[OF carrier_is_subfield] by simp
    hence "f pdivides d"
      using cthat(2) d_def(1,4) unfolding monic_irreducible_poly_def ring_irreducible_def
        Divisibility.irreducible_def properfactor_def pdivides_def f_carr by auto
    hence "f pdivides (gauss_poly R (order R^n))"
      using d_def(2,4) f_carr r.p.divides_trans unfolding pdivides_def by metis
    hence "degree f dvd n"
      using n_gt_0 div_gauss_poly_iff[OF _ cthat(2)] by auto
    thus "False"
      using p_def by (metis assms(2) div_less_dividend n_gt_0 nat_dvd_not_less prime_gt_1_nat)
  qed
  moreover have "False" if not_l:"\<not>?L" and r1:"?R1" and r2: "?R2"
  proof -
    obtain g where g_def: "g pdivides f" "degree g < degree f" "monic_irreducible_poly R g"
      using r1 not_l exists_irreducible_proper_factor assms(1,2) by auto

    have g_carr: "g \<in> carrier (poly_ring R)" and g_nz: "g \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>"
      using g_def(3) unfolding monic_irreducible_poly_def monic_poly_def by (auto simp:univ_poly_zero)

    have "g pdivides gauss_poly R (order R^degree f)"
      using g_carr r1 g_def(1) unfolding pdivides_def using r.p.divides_trans by blast

    hence "degree g dvd degree f"
      using div_gauss_poly_iff[OF assms(2) g_def(3)] by auto

    then obtain t where deg_f_def:"degree f = t * degree g"
      by fastforce
    hence "t > 1" using g_def(2) by simp
    then obtain p where p_prime: "Factorial_Ring.prime p" "p dvd t"
      by (metis order_less_irrefl prime_factor_nat)
    hence p_div_deg_f: "p dvd degree f"
      unfolding deg_f_def by simp
    define n where "n = degree f div p"
    have n_in_N: "n \<in> N"
      unfolding N_def n_def using p_prime(1) p_div_deg_f by auto

    have deg_g_dvd_n: "degree g dvd n"
      using p_prime(2) unfolding n_def deg_f_def by auto

    have n_gt_0: "n > 0"
      using p_div_deg_f assms(2) p_prime(1) unfolding n_def
      by (metis dvd_div_eq_0_iff gr0I)

    have deg_g_gt_0: "degree g > 0"
      using monic_poly_min_degree[OF g_def(3)] by simp

    have 0:"g pdivides gauss_poly R (order R^n)"
      using deg_g_dvd_n div_gauss_poly_iff[OF n_gt_0 g_def(3)] by simp

    have "pcoprime (gauss_poly R (order R^n)) f"
      using n_in_N r2 by simp
    thus "False"
      using 0 g_def(1) g_carr deg_g_gt_0 unfolding pcoprime_def by simp
  qed
  ultimately show ?thesis
    by auto
qed

text \<open>A more general variance of the previous theorem for non-monic polynomials. The result is
from Lemma~1 \cite[rabin1980].\<close>

theorem rabin_irreducibility_condition_2:
  assumes "f \<in> carrier (poly_ring R)" "degree f > 0"
  defines "N \<equiv> {degree f div p | p . Factorial_Ring.prime p \<and> p dvd degree f}"
  shows "pirreducible (carrier R) f \<longleftrightarrow>
    (f pdivides gauss_poly R (order R^degree f) \<and> (\<forall>n \<in> N. pcoprime (gauss_poly R (order R^n)) f))"
    (is "?L \<longleftrightarrow> ?R1 \<and> ?R2")
proof -
  define \<alpha> where "\<alpha> = [inv (hd f)]"
  let ?g = "(\<lambda>x. gauss_poly R (order R^x))"
  let ?h = "\<alpha> \<otimes>\<^bsub>poly_ring R\<^esub> f"

  have f_nz: "f \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>" unfolding univ_poly_zero using assms(2) by auto

  hence "hd f \<in> carrier R - {\<zero>}" using assms(1) lead_coeff_carr by simp
  hence "inv (hd f) \<in> carrier R - {\<zero>}" using field_Units by auto
  hence \<alpha>_unit: "\<alpha> \<in> Units (poly_ring R)"
    unfolding \<alpha>_def using univ_poly_carrier_units by simp

  have \<alpha>_nz: "\<alpha> \<noteq> \<zero>\<^bsub>poly_ring R\<^esub>" unfolding univ_poly_zero \<alpha>_def by simp
  have "hd ?h = hd \<alpha> \<otimes> hd f"
    using \<alpha>_nz f_nz assms(1) \<alpha>_unit by (intro lead_coeff_mult) auto
  also have "... = inv (hd f) \<otimes> hd f" unfolding \<alpha>_def by simp
  also have "... = \<one>" using lead_coeff_carr f_nz assms(1) by (simp add: field_Units)
  finally have "hd ?h = \<one>" by simp
  moreover have "?h \<noteq> []"
    using \<alpha>_nz f_nz univ_poly_zero by (metis \<alpha>_unit assms(1) r.p.Units_closed r.p.integral)
  ultimately have h_monic: "monic_poly R ?h"
    using r.p.Units_closed[OF \<alpha>_unit] assms(1) unfolding monic_poly_def by auto

  have "degree ?h = degree \<alpha> + degree f"
    using assms(1) f_nz \<alpha>_unit \<alpha>_nz by (intro degree_mult[OF carrier_is_subring]) auto
  also have "... = degree f" unfolding \<alpha>_def by simp
  finally have deg_f: "degree f = degree ?h" by simp

  have hf_cong:"?h \<sim>\<^bsub>r.P\<^esub> f"
    using assms(1) \<alpha>_unit by (simp add: r.p.Units_closed r.p.associatedI2 r.p.m_comm)
  hence 0: "f pdivides ?g (degree f) \<longleftrightarrow> ?h pdivides ?g (degree f)"
    unfolding pdivides_def using r.p.divides_cong_l r.p.associated_sym
    using r.p.Units_closed[OF \<alpha>_unit] assms(1) gauss_poly_carr by blast

  have 1: "pcoprime (?g n) f \<longleftrightarrow> pcoprime (?g n) ?h" for n
    using hf_cong r.p.associated_sym r.p.Units_closed[OF \<alpha>_unit] assms(1)
    by (intro pcoprime_right_assoc_cong gauss_poly_carr) auto

  have "?L \<longleftrightarrow> pirreducible (carrier R) (\<alpha> \<otimes>\<^bsub>poly_ring R\<^esub> f)"
    using \<alpha>_unit \<alpha>_nz assms(1) f_nz r.p.integral unfolding ring_irreducible_def
    by (intro arg_cong2[where f="(\<and>)"] r.p.irreducible_prod_unit assms) auto
  also have "... \<longleftrightarrow> monic_irreducible_poly R (\<alpha> \<otimes>\<^bsub>poly_ring R\<^esub> f)"
    using h_monic unfolding monic_irreducible_poly_def by auto
  also have "... \<longleftrightarrow> ?h pdivides ?g (degree f) \<and> (\<forall>n \<in> N. pcoprime (?g n) ?h)"
    using assms(2) unfolding N_def deg_f by (intro rabin_irreducibility_condition h_monic) auto
  also have "... \<longleftrightarrow> f pdivides ?g (degree f) \<and> (\<forall>n \<in> N. pcoprime (?g n) f)"
    using 0 1 by simp
  finally show ?thesis by simp
qed

end

end