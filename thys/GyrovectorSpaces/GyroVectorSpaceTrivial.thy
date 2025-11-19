theory GyroVectorSpaceTrivial
  imports GyroVectorSpace
begin

text \<open>Every group is a gyrogroup with identity gyration\<close>
sublocale group_add \<subseteq> groupGyrogroupoid: gyrogroupoid 0 "(+)"
  by unfold_locales

sublocale group_add \<subseteq> groupGyrogroup: gyrogroup 0 "(+)" "\<lambda> x. - x" "\<lambda> u v x. x"
proof
  fix a
  show "0 + a = a"
    by auto
next
  fix a
  show "- a + a = 0"
    by auto
next
  fix a b z
  show "a + (b + z) = a + b + z"
    by (simp add: add_assoc)
next
  fix a b
  show "(\<lambda> x. x) = (\<lambda> x. x)"
    by auto
next
  fix a b
  show "gyrogroupoid.gyroaut (+) (\<lambda>x. x)"
    unfolding gyrogroupoid.gyroaut_def
    by (auto simp add: bij_def)
qed

locale gyrocarrier_trivial = gyrocarrier' to_carrier for 
  to_carrier :: "'a::{gyrocommutative_gyrogroup, real_inner, real_normed_algebra_1} \<Rightarrow> 'a" + 
  assumes gyr_id: "\<And> u v x. (gyr::'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) u v x = x"
  assumes to_carrier_id: "\<And> x. to_carrier x = x"
  assumes oplus: "\<And> x y::'a . x \<oplus> y = x + y"
  assumes ominus: "\<And> x::'a . \<ominus> x = - x"

sublocale gyrocarrier_trivial \<subseteq> gyrocarrier to_carrier
proof
  fix u v a b
  show "gyr u v a \<cdot> gyr u v b = a \<cdot> b"
    by (simp add: gyr_id)
qed

sublocale gyrocarrier_trivial \<subseteq> pre_gyrovector_space to_carrier "(*\<^sub>R)"
proof
  fix a::'a
  show "1 *\<^sub>R a = a"
    by auto
next
  fix r1 r2 and a::'a
  show "(r1 + r2) *\<^sub>R a = (r1 *\<^sub>R a) \<oplus> (r2 *\<^sub>R a)"
    unfolding oplus
    by (meson scaleR_left_distrib)
next
  fix r1 r2 and a::'a
  show "(r1 * r2) *\<^sub>R a = r1 *\<^sub>R r2 *\<^sub>R a"
    by simp
next
  fix u v a :: 'a and r
  show "gyr u v (r *\<^sub>R a) = r *\<^sub>R gyr u v a"
    unfolding gyr_id
    by simp
next
  fix r1 r2 and v :: 'a
  show "gyr (r1 *\<^sub>R v) (r2 *\<^sub>R v) = id"
    by (auto simp add: gyr_id)
next
  fix r::real and a::'a
  assume "r \<noteq> 0" "a \<noteq> 0\<^sub>g"
  show "to_carrier (\<bar>r\<bar> *\<^sub>R a) /\<^sub>R \<llangle>(r *\<^sub>R a)\<rrangle> = to_carrier a /\<^sub>R \<llangle>a\<rrangle>"
    by (simp add: \<open>r \<noteq> 0\<close> gyronorm_def to_carrier_id)
qed

sublocale gyrocarrier_trivial \<subseteq> TG': gyrocarrier_norms_embed' to_carrier
proof
  show "of_real ` norms \<subseteq> carrier"
    unfolding norms_def carrier_def
    by (simp add: to_carrier_id)
qed

context gyrocarrier_trivial
begin

lemma norms_UNIV:
  shows "norms = UNIV"
  unfolding norms_def
  by (auto, metis eq_abs_iff' gyronorm_def norm_of_real to_carrier_id)

lemma reals_UNIV:
  shows "TG'.reals = of_real ` UNIV"
  unfolding TG'.reals_def norms_UNIV
  using of_carrier to_carrier_id 
  by auto

lemma of_real':
  shows "TG'.of_real' = of_real"
  using TG'.of_real'_def
  using of_carrier to_carrier_id 
  by auto

end

sublocale gyrocarrier_trivial \<subseteq> TG: gyrocarrier_norms_embed to_carrier "(*\<^sub>R)"
proof
  fix a b
  assume "a \<in> TG'.reals" "b \<in> TG'.reals"
  then show "a \<oplus> b \<in> TG'.reals"
    unfolding reals_UNIV oplus
    by (metis Reals_add Reals_def)
next
  fix a
  assume "a \<in> TG'.reals"
  then show "\<ominus> a \<in> TG'.reals"
    unfolding reals_UNIV ominus
    by force
next
  fix a r
  assume "a \<in> TG'.reals"
  then show "r *\<^sub>R a \<in> TG'.reals"
    unfolding reals_UNIV
    by (metis Reals_def Reals_mult Reals_of_real scaleR_conv_of_real)
qed

sublocale gyrocarrier_trivial \<subseteq> gyrovector_space_norms_embed "(*\<^sub>R)" to_carrier
proof
  fix r a
  show "\<llangle>(r *\<^sub>R a)\<rrangle> = TG.otimesR \<bar>r\<bar> (\<llangle>a\<rrangle>)"
    unfolding gyronorm_def TG.otimesR_def of_real'
    by (metis TG'.to_real' UNIV_I norm_scaleR norms_UNIV of_real' of_real_mult scaleR_conv_of_real to_carrier_id)
next
  fix a b
  show "\<llangle>a \<oplus> b\<rrangle> \<le> \<llangle>a\<rrangle> \<oplus>\<^sub>R (\<llangle>b\<rrangle>)"
    by (metis TG'.oplusR_def TG'.to_real' UNIV_I gyronorm_def norm_triangle_ineq norms_UNIV of_real' of_real_add oplus to_carrier_id)    
qed

end