theory Gyrotrigonometry
imports Main GyroVectorSpace
begin

datatype 'a otriangle = M_gyrotriangle (A:'a) (B:'a) (C:'a)

context pre_gyrovector_space
begin

definition unit :: "'a \<Rightarrow> 'b" where
  "unit a = to_carrier a /\<^sub>R \<llangle>a\<rrangle>"

lemma norm_inner_le_1:
  fixes a b :: 'b
  assumes "norm a \<le> 1" "norm b \<le> 1"
  shows "norm (inner a b) \<le> 1"
  using assms
  by (smt (verit, ccfv_SIG) Cauchy_Schwarz_ineq2 mult_le_one norm_ge_zero real_norm_def)

lemma norm_inner_unit:
  shows "norm (inner (unit (\<ominus> a \<oplus> b)) (unit (\<ominus> a \<oplus> c))) \<le> 1"
proof-
  have "norm (unit (\<ominus> a \<oplus> b)) = \<llangle>\<ominus> a \<oplus> b\<rrangle> / \<llangle>\<ominus> a \<oplus> b\<rrangle>"
    by (simp add: unit_def gyronorm_def)
  then have "norm (unit (\<ominus> a \<oplus> b)) \<le> 1"
    by simp
  moreover
  have "norm (unit (\<ominus> a \<oplus> c)) = \<llangle>\<ominus> a \<oplus> c\<rrangle> / \<llangle>\<ominus> a \<oplus> c\<rrangle>"
    by (simp add: unit_def gyronorm_def)
  then have "norm (unit (\<ominus> a \<oplus> c)) \<le> 1"
    by simp
  ultimately
  show ?thesis
    using norm_inner_le_1 
    by blast
qed

definition angle :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where 
  "angle a b c = arccos (inner (unit (\<ominus> a \<oplus> b)) (unit (\<ominus> a \<oplus> c)))"

definition o_ray :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "o_ray x p = {s::'a. \<exists>t::real. t \<ge> 0 \<and> s = (x \<oplus> t \<otimes> (\<ominus> x \<oplus> p))}"

lemma T8_5:
  assumes "b2 \<in> o_ray a1 b1" "b2 \<noteq> a1" 
          "c2 \<in> o_ray a1 c1" "c2 \<noteq> a1"
  shows "angle a1 b1 c1 = angle a1 b2 c2"
proof-
  obtain t1::real where t1: "t1 > 0" "b2 = a1 \<oplus> t1 \<otimes> (\<ominus> a1 \<oplus> b1)"
    using assms less_eq_real_def o_ray_def by auto
  then have "\<ominus> a1 \<oplus> b2 = t1 \<otimes> (\<ominus> a1 \<oplus> b1)"
     using gyro_left_cancel' by simp

  obtain t2::real where t2: "t2 > 0" "c2 = a1 \<oplus> t2 \<otimes> (\<ominus> a1 \<oplus> c1)"
    using assms less_eq_real_def o_ray_def by auto
  then have "\<ominus> a1 \<oplus> c2 = t2 \<otimes> (\<ominus> a1 \<oplus> c1)"
    using gyro_left_cancel' by simp

  have "angle a1 b2 c2 =  arccos (inner (to_carrier (\<ominus> a1 \<oplus> b2) /\<^sub>R \<llangle>\<ominus> a1 \<oplus> b2\<rrangle>)
                                        (to_carrier (\<ominus> a1 \<oplus> c2) /\<^sub>R \<llangle>\<ominus> a1 \<oplus> c2\<rrangle>))"
    using angle_def unit_def by presburger
  also have "\<dots> =
              arccos (inner (to_carrier (t1 \<otimes> (\<ominus> a1 \<oplus> b1)) /\<^sub>R \<llangle>t1 \<otimes> (\<ominus> a1 \<oplus> b1)\<rrangle>)
                            (to_carrier (t2 \<otimes> (\<ominus> a1 \<oplus> c1)) /\<^sub>R \<llangle>t2 \<otimes> (\<ominus> a1 \<oplus> c1)\<rrangle>))"
    using \<open>\<ominus> a1 \<oplus> b2 = t1 \<otimes> (\<ominus> a1 \<oplus> b1)\<close> \<open>\<ominus> a1 \<oplus> c2 = t2 \<otimes> (\<ominus> a1 \<oplus> c1)\<close> by auto
  finally show ?thesis
    unfolding angle_def unit_def
    using t1 t2
    by (smt (verit, best) scale_prop1 times_zero)
qed

definition get_a :: "'a otriangle \<Rightarrow> 'a" where
  "get_a t = \<ominus> (C t) \<oplus> (B t)"
definition get_b :: "'a otriangle \<Rightarrow> 'a" where
  "get_b t = \<ominus> (C t) \<oplus> (A t)"
definition get_c :: "'a otriangle \<Rightarrow> 'a" where
  "get_c t = \<ominus> (B t) \<oplus> (A t)"

definition get_alpha :: "'a otriangle \<Rightarrow> real" where
  "get_alpha t = angle (A t) (B t) (C t)"
definition get_beta :: "'a otriangle \<Rightarrow> real" where
  "get_beta t = angle (B t) (C t) (A t)"
definition get_gamma :: "'a otriangle \<Rightarrow> real" where
  "get_gamma t = angle (C t) (A t) (B t)"

definition cong_gyrotriangles :: "'a otriangle \<Rightarrow> 'a otriangle \<Rightarrow> bool" where
  "cong_gyrotriangles t1 t2 \<longleftrightarrow> 
     (\<llangle>get_a t1\<rrangle> = \<llangle>get_a t2\<rrangle> \<and> \<llangle>get_b t1\<rrangle> = \<llangle>get_b t2\<rrangle> \<and> \<llangle>get_c t1\<rrangle> = \<llangle>get_c t2\<rrangle> \<and> 
      (get_alpha t1 = get_alpha t2) \<and> (get_beta t1 = get_beta t2) \<and> (get_gamma t1 = get_gamma t2))"
end

end