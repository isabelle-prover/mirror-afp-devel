theory Localization_Interface
  imports
    "HOL-Algebra.Ring_Divisibility"
    "HOL-Algebra.QuotRing"
    Localization_Ring.Localization
begin

section \<open>Localization helper lemmas\<close>

text \<open>
  The AFP entry \<^theory>\<open>Localization_Ring.Localization\<close> develops localizations as
  quotient rings in the HOL-Algebra hierarchy.  For the present development we
  package a small wrapper layer at the level of equality of representatives,
  denominator rescaling, units coming from the multiplicative set, and
  injectivity of the canonical map.
\<close>

context eq_obj_rng_of_frac
begin

lemma fraction_eq_iff_rel:
  assumes "(r, s) \<in> carrier rel"
    and "(r', s') \<in> carrier rel"
  shows "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s') \<longleftrightarrow> (r, s) .=\<^bsub>rel\<^esub> (r', s')"
proof
  from assms have rs: "(r, s) \<in> carrier R \<times> S" and rs': "(r', s') \<in> carrier R \<times> S"
    by (simp_all add: rel_def)
  assume "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s')"
  then show "(r, s) .=\<^bsub>rel\<^esub> (r', s')"
    using eq_class_to_rel[of r s r' s'] rs rs' by blast
next
  assume hrel: "(r, s) .=\<^bsub>rel\<^esub> (r', s')"
  have "class_of\<^bsub>rel\<^esub> (r, s) = class_of\<^bsub>rel\<^esub> (r', s')"
    using equiv_obj_rng_of_frac assms hrel by (rule elem_eq_class)
  then show "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s')"
    by (simp add: class_of_to_rel)
qed

lemma fraction_zero_rep [simp]:
  assumes "s \<in> S"
  shows "(\<zero> |\<^bsub>rel\<^esub> s) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  using assms by (rule class_of_zero_rng_of_frac)

lemma fraction_surj:
  assumes "x \<in> carrier rec_rng_of_frac"
  shows "\<exists>r \<in> carrier R. \<exists>s \<in> S. x = (r |\<^bsub>rel\<^esub> s)"
  using assms
  unfolding rec_rng_of_frac_def set_eq_class_of_rng_of_frac_def rel_def
  by auto

lemma fraction_rescale:
  assumes "(r, s) \<in> carrier rel"
    and "s' \<in> S"
  shows "(r |\<^bsub>rel\<^esub> s) = (s' \<otimes> r |\<^bsub>rel\<^esub> s' \<otimes> s)"
  using assms by (rule simp_in_frac)

lemma fraction_mult_rep:
  assumes rs: "(r, s) \<in> carrier rel"
    and r's': "(r', s') \<in> carrier rel"
  shows "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (r' |\<^bsub>rel\<^esub> s') =
      (r \<otimes>\<^bsub>R\<^esub> r' |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> s')"
proof -
  have hfund:
      "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_monoid_rng_of_frac\<^esub> (r' |\<^bsub>rel\<^esub> s') =
        (r \<otimes>\<^bsub>R\<^esub> r' |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> s')"
    using mult_rng_of_frac_fundamental_lemma[OF rs r's']
    by simp
  have hmonoid_mult:
      "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_monoid_rng_of_frac\<^esub> (r' |\<^bsub>rel\<^esub> s') =
        mult_rng_of_frac (r |\<^bsub>rel\<^esub> s) (r' |\<^bsub>rel\<^esub> s')"
    by (simp add: rec_monoid_rng_of_frac_def)
  have "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (r' |\<^bsub>rel\<^esub> s') =
      mult_rng_of_frac (r |\<^bsub>rel\<^esub> s) (r' |\<^bsub>rel\<^esub> s')"
    by (simp only: rec_rng_of_frac_def ring_record_simps)
  also have "\<dots> = (r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_monoid_rng_of_frac\<^esub> (r' |\<^bsub>rel\<^esub> s')"
    using hmonoid_mult by simp
  also have "\<dots> = (r \<otimes>\<^bsub>R\<^esub> r' |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> s')"
    by (rule hfund)
  finally show ?thesis .
qed

lemma map_mul_fraction:
  assumes a_in: "a \<in> carrier R"
    and rs: "(r, s) \<in> carrier rel"
  shows "rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (r |\<^bsub>rel\<^esub> s) = (a \<otimes>\<^bsub>R\<^esub> r |\<^bsub>rel\<^esub> s)"
proof -
  have one_in: "\<one> \<in> S"
    by (rule one_closed)
  have a_rel: "(a, \<one>) \<in> carrier rel"
    using a_in one_in by (simp add: rel_def)
  have s_in: "s \<in> S"
    using rs by (simp add: rel_def)
  have s_carrier: "s \<in> carrier R"
    using subset s_in by blast
  have one_s: "\<one> \<otimes>\<^bsub>R\<^esub> s = s"
    using s_carrier by simp
  have "rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (r |\<^bsub>rel\<^esub> s) = (a |\<^bsub>rel\<^esub> \<one>) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (r |\<^bsub>rel\<^esub> s)"
    by (simp add: rng_to_rng_of_frac_def)
  also have "\<dots> = (a \<otimes>\<^bsub>R\<^esub> r |\<^bsub>rel\<^esub> \<one> \<otimes>\<^bsub>R\<^esub> s)"
    by (rule fraction_mult_rep[OF a_rel rs])
  also have "\<dots> = (a \<otimes>\<^bsub>R\<^esub> r |\<^bsub>rel\<^esub> s)"
    using one_s by simp
  finally show ?thesis .
qed

lemma fraction_mul_map:
  assumes rs: "(r, s) \<in> carrier rel"
    and a_in: "a \<in> carrier R"
  shows "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a = (r \<otimes>\<^bsub>R\<^esub> a |\<^bsub>rel\<^esub> s)"
proof -
  have one_in: "\<one> \<in> S"
    by (rule one_closed)
  have a_rel: "(a, \<one>) \<in> carrier rel"
    using a_in one_in by (simp add: rel_def)
  have s_in: "s \<in> S"
    using rs by (simp add: rel_def)
  have s_carrier: "s \<in> carrier R"
    using subset s_in by blast
  have s_one: "s \<otimes>\<^bsub>R\<^esub> \<one> = s"
    using s_carrier by simp
  have "(r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac a = (r |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (a |\<^bsub>rel\<^esub> \<one>)"
    by (simp add: rng_to_rng_of_frac_def)
  also have "\<dots> = (r \<otimes>\<^bsub>R\<^esub> a |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> \<one>)"
    by (rule fraction_mult_rep[OF rs a_rel])
  also have "\<dots> = (r \<otimes>\<^bsub>R\<^esub> a |\<^bsub>rel\<^esub> s)"
    using s_one by simp
  finally show ?thesis .
qed

lemma fraction_eq_iff_cross_multiply:
  assumes rs: "(r, s) \<in> carrier rel"
    and rs': "(r', s') \<in> carrier rel"
    and zero_notin: "\<zero> \<notin> S"
    and no_zero_div: "\<forall>a \<in> carrier R. \<forall>b \<in> carrier R. a \<otimes> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>"
  shows "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s') \<longleftrightarrow> s' \<otimes>\<^bsub>R\<^esub> r = s \<otimes>\<^bsub>R\<^esub> r'"
proof (intro iffI)
  from rs rs' have r_in: "r \<in> carrier R" and s_in: "s \<in> S"
    and r'_in: "r' \<in> carrier R" and s'_in: "s' \<in> S"
    by (simp_all add: rel_def)
  have s_carrier: "s \<in> carrier R" and s'_carrier: "s' \<in> carrier R"
    using s_in s'_in subset rev_subsetD by auto
  have lhs_in: "s' \<otimes>\<^bsub>R\<^esub> r \<in> carrier R"
    using s'_carrier r_in by auto
  have rhs_in: "s \<otimes>\<^bsub>R\<^esub> r' \<in> carrier R"
    using s_carrier r'_in by auto
  assume eq_frac: "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s')"
    have hrel: "(r, s) .=\<^bsub>rel\<^esub> (r', s')"
      using fraction_eq_iff_rel[OF rs rs'] eq_frac by blast
    then obtain t where t_in: "t \<in> S" and t_zero: "t \<otimes> ((s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) = \<zero>"
      unfolding rel_def by auto
    have t_carrier: "t \<in> carrier R"
      using t_in subset rev_subsetD by auto
    have diff_in: "(s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') \<in> carrier R"
      using lhs_in rhs_in by auto
    have "t = \<zero> \<or> (s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') = \<zero>"
      using no_zero_div t_carrier diff_in t_zero by blast
    moreover have "t \<noteq> \<zero>"
      using t_in zero_notin by auto
    ultimately have "(s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') = \<zero>"
      by auto
    then have "((s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') =
        \<zero> \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')"
      by simp
    then have "(s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> ((\<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) =
        s \<otimes>\<^bsub>R\<^esub> r'"
      using lhs_in rhs_in by (simp add: a_minus_def a_assoc)
    have inv_cancel: "(\<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') = \<zero>"
      using rhs_in by (rule l_neg)
    then have "(s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> ((\<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) =
        (s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> \<zero>"
      by simp
    then have "(s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> \<zero> = s \<otimes>\<^bsub>R\<^esub> r'"
      using \<open>(s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> ((\<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) \<oplus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) =
        s \<otimes>\<^bsub>R\<^esub> r'\<close>
      by simp
  then show "s' \<otimes>\<^bsub>R\<^esub> r = s \<otimes>\<^bsub>R\<^esub> r'"
    using lhs_in by (simp add: r_zero)
next
  assume cross_mul: "s' \<otimes>\<^bsub>R\<^esub> r = s \<otimes>\<^bsub>R\<^esub> r'"
  from rs rs' have r_in': "r \<in> carrier R" and s'_in': "s' \<in> S"
    by (simp_all add: rel_def)
  have lhs_in': "s' \<otimes>\<^bsub>R\<^esub> r \<in> carrier R"
  proof -
    have "s' \<in> carrier R"
      using s'_in' subset rev_subsetD by auto
    then show ?thesis
      using r_in' by auto
  qed
  have diff_zero: "(s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') = \<zero>"
  proof -
    have "(s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r') = (s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s' \<otimes>\<^bsub>R\<^esub> r)"
      using cross_mul by simp
    also have "\<dots> = (s' \<otimes>\<^bsub>R\<^esub> r) \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> (s' \<otimes>\<^bsub>R\<^esub> r))"
      by (simp add: a_minus_def)
    also have "\<dots> = \<zero>"
      using lhs_in' by (rule r_neg)
    finally show ?thesis .
  qed
  have "(r, s) .=\<^bsub>rel\<^esub> (r', s')"
  proof -
    have "\<one> \<in> S"
      by (rule one_closed)
    moreover have "\<one> \<otimes> ((s' \<otimes>\<^bsub>R\<^esub> r) \<ominus>\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> r')) = \<zero>"
      using diff_zero by simp
    ultimately show ?thesis
      unfolding rel_def using rs rs' by auto
  qed
  then show "(r |\<^bsub>rel\<^esub> s) = (r' |\<^bsub>rel\<^esub> s')"
    using fraction_eq_iff_rel[OF rs rs'] by blast
qed

lemma fraction_eq_zero_iff:
  assumes rs: "(r, s) \<in> carrier rel"
    and zero_notin: "\<zero> \<notin> S"
    and no_zero_div: "\<forall>a \<in> carrier R. \<forall>b \<in> carrier R. a \<otimes> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>"
  shows "(r |\<^bsub>rel\<^esub> s) = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<longleftrightarrow> r = \<zero>"
proof
  from rs have s_in: "s \<in> S"
    by (simp add: rel_def)
  have s_carrier: "s \<in> carrier R"
    using subset s_in by blast
  from rs have r_in: "r \<in> carrier R"
    by (simp add: rel_def)
  have zero_rel: "(\<zero>, \<one>) \<in> carrier rel"
    by (simp add: rel_def one_closed)
  assume hzero: "(r |\<^bsub>rel\<^esub> s) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
  have "(r |\<^bsub>rel\<^esub> s) = (\<zero> |\<^bsub>rel\<^esub> \<one>)"
    using hzero by (simp add: class_of_zero_rng_of_frac[OF one_closed])
  then have "\<one> \<otimes>\<^bsub>R\<^esub> r = s \<otimes>\<^bsub>R\<^esub> \<zero>"
    using fraction_eq_iff_cross_multiply[OF rs zero_rel zero_notin no_zero_div]
    by simp
  then have "r = s \<otimes>\<^bsub>R\<^esub> \<zero>"
    using r_in by simp
  also have "\<dots> = \<zero>"
    using s_carrier by simp
  finally show "r = \<zero>" .
next
  assume "r = \<zero>"
  then have r_zero: "r = \<zero>" .
  have s_in: "s \<in> S"
    using rs by (simp add: rel_def)
  from r_zero s_in show "(r |\<^bsub>rel\<^esub> s) = \<zero>\<^bsub>rec_rng_of_frac\<^esub>"
    by simp
qed

lemma map_eq_zero_iff:
  assumes a_in: "a \<in> carrier R"
    and zero_notin: "\<zero> \<notin> S"
    and no_zero_div: "\<forall>a' \<in> carrier R. \<forall>b' \<in> carrier R. a' \<otimes> b' = \<zero> \<longrightarrow> a' = \<zero> \<or> b' = \<zero>"
  shows "rng_to_rng_of_frac a = \<zero>\<^bsub>rec_rng_of_frac\<^esub> \<longleftrightarrow> a = \<zero>"
proof -
  have a_rel: "(a, \<one>) \<in> carrier rel"
    using a_in one_closed by (simp add: rel_def)
  show ?thesis
    using fraction_eq_zero_iff[OF a_rel zero_notin no_zero_div]
    by (simp add: rng_to_rng_of_frac_def)
qed

lemma dvd_map_iff:
  assumes a_in: "a \<in> carrier R"
    and b_in: "b \<in> carrier R"
    and zero_notin: "\<zero> \<notin> S"
    and no_zero_div: "\<forall>a' \<in> carrier R. \<forall>b' \<in> carrier R. a' \<otimes> b' = \<zero> \<longrightarrow> a' = \<zero> \<or> b' = \<zero>"
  shows "rng_to_rng_of_frac a divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b \<longleftrightarrow> (\<exists>s \<in> S. a divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> b))"
proof
  assume hdiv: "rng_to_rng_of_frac a divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b"
  then obtain x where x_mem: "x \<in> carrier rec_rng_of_frac"
    and hx: "rng_to_rng_of_frac b = rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> x"
    unfolding factor_def by blast
  from fraction_surj[OF x_mem] obtain c where c_in: "c \<in> carrier R"
    and hs: "\<exists>s \<in> S. x = (c |\<^bsub>rel\<^esub> s)"
    by blast
  from hs obtain s where s_in: "s \<in> S" and x_def: "x = (c |\<^bsub>rel\<^esub> s)"
    by blast
  have b_rel: "(b, \<one>) \<in> carrier rel"
    using b_in one_closed by (simp add: rel_def)
  have cs_rel: "(c, s) \<in> carrier rel"
    using c_in s_in by (simp add: rel_def)
  have ac_rel: "(a \<otimes>\<^bsub>R\<^esub> c, s) \<in> carrier rel"
    using a_in c_in s_in by (simp add: rel_def)
  have "(b |\<^bsub>rel\<^esub> \<one>) = (a \<otimes>\<^bsub>R\<^esub> c |\<^bsub>rel\<^esub> s)"
  proof -
    have h1: "rng_to_rng_of_frac b = rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (c |\<^bsub>rel\<^esub> s)"
      using hx x_def by simp
    have h2: "rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (c |\<^bsub>rel\<^esub> s) = (a \<otimes>\<^bsub>R\<^esub> c |\<^bsub>rel\<^esub> s)"
      using map_mul_fraction[OF a_in cs_rel] by simp
    from h1 h2 show ?thesis
      by (simp add: rng_to_rng_of_frac_def)
  qed
  then have "s \<otimes>\<^bsub>R\<^esub> b = \<one> \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> c)"
    using fraction_eq_iff_cross_multiply[OF b_rel ac_rel zero_notin no_zero_div]
    by simp
  then have "s \<otimes>\<^bsub>R\<^esub> b = a \<otimes>\<^bsub>R\<^esub> c"
    using a_in c_in by simp
  then have "a divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> b)"
    unfolding factor_def using c_in by blast
  then show "\<exists>s \<in> S. a divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> b)"
    using s_in by blast
next
  assume hdiv: "\<exists>s \<in> S. a divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> b)"
  then obtain s where s_in: "s \<in> S" and hsab: "a divides\<^bsub>R\<^esub> (s \<otimes>\<^bsub>R\<^esub> b)"
    by blast
  then obtain c where c_in: "c \<in> carrier R" and hc: "s \<otimes>\<^bsub>R\<^esub> b = a \<otimes>\<^bsub>R\<^esub> c"
    unfolding factor_def by blast
  have cs_rel: "(c, s) \<in> carrier rel"
    using c_in s_in by (simp add: rel_def)
  have ac_rel: "(a \<otimes>\<^bsub>R\<^esub> c, s) \<in> carrier rel"
    using a_in c_in s_in by (simp add: rel_def)
  have b_rel: "(b, \<one>) \<in> carrier rel"
    using b_in one_closed by (simp add: rel_def)
  have eq_frac: "(b |\<^bsub>rel\<^esub> \<one>) = (a \<otimes>\<^bsub>R\<^esub> c |\<^bsub>rel\<^esub> s)"
  proof -
    have "s \<otimes>\<^bsub>R\<^esub> b = \<one> \<otimes>\<^bsub>R\<^esub> (a \<otimes>\<^bsub>R\<^esub> c)"
      using hc a_in c_in by simp
    then show ?thesis
      using fraction_eq_iff_cross_multiply[OF b_rel ac_rel zero_notin no_zero_div]
      by blast
  qed
  have frac_mem: "(c |\<^bsub>rel\<^esub> s) \<in> carrier rec_rng_of_frac"
    using cs_rel unfolding rec_rng_of_frac_def set_eq_class_of_rng_of_frac_def
    by auto
  have "rng_to_rng_of_frac b = rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (c |\<^bsub>rel\<^esub> s)"
  proof -
    have h1: "rng_to_rng_of_frac b = (b |\<^bsub>rel\<^esub> \<one>)"
      by (simp add: rng_to_rng_of_frac_def)
    have h2: "(b |\<^bsub>rel\<^esub> \<one>) = (a \<otimes>\<^bsub>R\<^esub> c |\<^bsub>rel\<^esub> s)"
      using eq_frac by simp
    have h3: "rng_to_rng_of_frac a \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (c |\<^bsub>rel\<^esub> s) = (a \<otimes>\<^bsub>R\<^esub> c |\<^bsub>rel\<^esub> s)"
      using map_mul_fraction[OF a_in cs_rel] by simp
    from h1 h2 h3 show ?thesis
      by simp
  qed
  then show "rng_to_rng_of_frac a divides\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac b"
    unfolding factor_def using frac_mem by blast
qed

lemma image_submonoid_is_unit:
  assumes "x \<in> rng_to_rng_of_frac ` S"
  shows "x \<in> Units rec_rng_of_frac"
  using assms by (rule Im_rng_to_rng_of_frac_unit)

lemma map_submonoid_elem_is_unit:
  assumes "s \<in> S"
  shows "rng_to_rng_of_frac s \<in> Units rec_rng_of_frac"
  using assms image_submonoid_is_unit by blast

lemma map_unit_is_unit:
  assumes u_unit: "u \<in> Units R"
  shows "rng_to_rng_of_frac u \<in> Units rec_rng_of_frac"
proof -
  have u_in: "u \<in> carrier R"
    using u_unit by blast
  have inv_u_in: "inv u \<in> carrier R"
    using u_unit by blast
  have map_u_in: "rng_to_rng_of_frac u \<in> carrier rec_rng_of_frac"
    using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom u_in] .
  have map_inv_u_in: "rng_to_rng_of_frac (inv u) \<in> carrier rec_rng_of_frac"
    using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom inv_u_in] .
  have left_inv:
      "rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (inv u) =
        \<one>\<^bsub>rec_rng_of_frac\<^esub>"
  proof -
    have "rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac (inv u) =
        rng_to_rng_of_frac (u \<otimes>\<^bsub>R\<^esub> inv u)"
      using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom u_in inv_u_in]
      by simp
    also have "\<dots> = rng_to_rng_of_frac \<one>"
      using u_unit by simp
    also have "\<dots> = \<one>\<^bsub>rec_rng_of_frac\<^esub>"
      using ring_hom_one[OF rng_to_rng_of_frac_is_ring_hom] .
    finally show ?thesis .
  qed
  have right_inv:
      "rng_to_rng_of_frac (inv u) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac u =
        \<one>\<^bsub>rec_rng_of_frac\<^esub>"
  proof -
    have "rng_to_rng_of_frac (inv u) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac u =
        rng_to_rng_of_frac (inv u \<otimes>\<^bsub>R\<^esub> u)"
      using ring_hom_mult[OF rng_to_rng_of_frac_is_ring_hom inv_u_in u_in]
      by simp
    also have "\<dots> = rng_to_rng_of_frac \<one>"
      using u_unit by simp
    also have "\<dots> = \<one>\<^bsub>rec_rng_of_frac\<^esub>"
      using ring_hom_one[OF rng_to_rng_of_frac_is_ring_hom] .
    finally show ?thesis .
  qed
  show ?thesis
    unfolding Units_def
    using map_u_in map_inv_u_in left_inv right_inv by blast
qed

lemma fraction_unit_numerator_is_unit:
  assumes u_unit: "u \<in> Units R"
    and s_in: "s \<in> S"
  shows "(u |\<^bsub>rel\<^esub> s) \<in> Units rec_rng_of_frac"
proof -
  have u_in: "u \<in> carrier R"
    using Units_closed[OF u_unit] .
  have s_carrier: "s \<in> carrier R"
    using subset s_in by blast
  have u_rel: "(u, \<one>) \<in> carrier rel"
    using u_in one_closed by (simp add: rel_def)
  have one_rel: "(\<one>, s) \<in> carrier rel"
    using s_in by (simp add: rel_def)
  have frac_eq':
      "rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s) =
        (u |\<^bsub>rel\<^esub> s)"
  proof -
    have "rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s) =
        (u |\<^bsub>rel\<^esub> \<one>) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s)"
      by (simp add: rng_to_rng_of_frac_def)
    also have "\<dots> = (u \<otimes>\<^bsub>R\<^esub> \<one> |\<^bsub>rel\<^esub> \<one> \<otimes>\<^bsub>R\<^esub> s)"
      by (rule fraction_mult_rep[OF u_rel one_rel])
    also have "\<dots> = (u |\<^bsub>rel\<^esub> s)"
      using u_in s_carrier by simp
    finally show ?thesis .
  qed
  have frac_eq:
      "(u |\<^bsub>rel\<^esub> s) =
        rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s)"
    using frac_eq' by simp
  have map_unit: "rng_to_rng_of_frac u \<in> Units rec_rng_of_frac"
    using u_unit by (rule map_unit_is_unit)
  have denom_unit: "(\<one> |\<^bsub>rel\<^esub> s) \<in> Units rec_rng_of_frac"
  proof -
    have s_carrier: "s \<in> carrier R"
      using subset s_in by blast
    have s_rel: "(s, \<one>) \<in> carrier rel"
      using s_carrier one_closed by (simp add: rel_def)
    have left_inv:
        "(\<one> |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac s =
          \<one>\<^bsub>rec_rng_of_frac\<^esub>"
    proof -
      have "(\<one> |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> rng_to_rng_of_frac s =
          (\<one> |\<^bsub>rel\<^esub> s) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (s |\<^bsub>rel\<^esub> \<one>)"
        by (simp add: rng_to_rng_of_frac_def)
      also have "\<dots> = (\<one> \<otimes>\<^bsub>R\<^esub> s |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> \<one>)"
        by (rule fraction_mult_rep[OF one_rel s_rel])
      also have "\<dots> = (\<one> |\<^bsub>rel\<^esub> \<one>)"
      proof -
        have one_rel': "(\<one>, \<one>) \<in> carrier rel"
          using one_closed by (simp add: rel_def)
        have "(\<one> |\<^bsub>rel\<^esub> \<one>) = (s \<otimes>\<^bsub>R\<^esub> \<one> |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> \<one>)"
          by (rule fraction_rescale[OF one_rel' s_in])
        then show ?thesis
          using s_carrier by simp
      qed
      also have "\<dots> = \<one>\<^bsub>rec_rng_of_frac\<^esub>"
        by (simp only: rec_rng_of_frac_def ring_record_simps)
      finally show ?thesis .
    qed
    have right_inv:
        "rng_to_rng_of_frac s \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s) =
          \<one>\<^bsub>rec_rng_of_frac\<^esub>"
    proof -
      have "rng_to_rng_of_frac s \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s) =
          (s |\<^bsub>rel\<^esub> \<one>) \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s)"
        by (simp add: rng_to_rng_of_frac_def)
      also have "\<dots> = (s \<otimes>\<^bsub>R\<^esub> \<one> |\<^bsub>rel\<^esub> \<one> \<otimes>\<^bsub>R\<^esub> s)"
        by (rule fraction_mult_rep[OF s_rel one_rel])
      also have "\<dots> = (\<one> |\<^bsub>rel\<^esub> \<one>)"
      proof -
        have one_rel': "(\<one>, \<one>) \<in> carrier rel"
          using one_closed by (simp add: rel_def)
        have "(\<one> |\<^bsub>rel\<^esub> \<one>) = (s \<otimes>\<^bsub>R\<^esub> \<one> |\<^bsub>rel\<^esub> s \<otimes>\<^bsub>R\<^esub> \<one>)"
          by (rule fraction_rescale[OF one_rel' s_in])
        then show ?thesis
          using s_carrier by simp
      qed
      also have "\<dots> = \<one>\<^bsub>rec_rng_of_frac\<^esub>"
        by (simp only: rec_rng_of_frac_def ring_record_simps)
      finally show ?thesis .
    qed
    have frac_in: "(\<one> |\<^bsub>rel\<^esub> s) \<in> carrier rec_rng_of_frac"
    proof -
      have one_s_rel: "(\<one>, s) \<in> carrier rel"
        using s_in by (simp add: rel_def)
      show ?thesis
        using one_s_rel
        unfolding rec_rng_of_frac_def set_eq_class_of_rng_of_frac_def
        by auto
    qed
    have s_carrier: "s \<in> carrier R"
      using s_in subset rev_subsetD by blast
    have map_s_in: "rng_to_rng_of_frac s \<in> carrier rec_rng_of_frac"
      using ring_hom_closed[OF rng_to_rng_of_frac_is_ring_hom s_carrier] .
    show ?thesis
      unfolding Units_def using frac_in map_s_in left_inv right_inv by blast
  qed
  show ?thesis
  proof -
    have "rng_to_rng_of_frac u \<otimes>\<^bsub>rec_rng_of_frac\<^esub> (\<one> |\<^bsub>rel\<^esub> s) \<in> Units rec_rng_of_frac"
      by (rule monoid.Units_m_closed[OF ring.is_monoid[OF rng_rng_of_frac] map_unit denom_unit])
    then show ?thesis
      using frac_eq by simp
  qed
qed

lemma map_inj_on:
  assumes "\<zero> \<notin> S"
    and "\<forall>a \<in> carrier R. \<forall>b \<in> carrier R. a \<otimes> b = \<zero> \<longrightarrow> a = \<zero> \<or> b = \<zero>"
  shows "inj_on rng_to_rng_of_frac (carrier R)"
proof -
  have "a_kernel R rec_rng_of_frac rng_to_rng_of_frac = {\<zero>}"
    using assms by (rule rng_to_rng_of_frac_without_zero_div_is_inj)
  then show ?thesis
    using ring_hom_ring.trivial_ker_imp_inj[
        OF ring_hom_ringI2[OF ring_axioms rng_rng_of_frac rng_to_rng_of_frac_is_ring_hom]
      ]
    by blast
qed

end

end
