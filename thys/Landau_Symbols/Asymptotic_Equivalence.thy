theory Asymptotic_Equivalence
imports Complex_Main Landau_Symbols_Definition
begin

named_theorems asymp_equiv_intros
named_theorems asymp_equiv_simps

definition asymp_equiv :: "('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> 'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  ("_ \<sim>[_] _" [51, 10, 51] 50)
  where "f \<sim>[F] g \<longleftrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"

abbreviation asymp_equiv_at_top (infix "\<sim>" 51) where
  "f \<sim> g \<equiv> f \<sim>[at_top] g"

lemma asymp_equivI: "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F \<Longrightarrow> f \<sim>[F] g"
  by (simp add: asymp_equiv_def)

lemma asymp_equivD: "f \<sim>[F] g \<Longrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"
  by (simp add: asymp_equiv_def)

lemma asymp_equiv_refl [simp, asymp_equiv_intros]: "f \<sim>[F] f"
proof (intro asymp_equivI)
  have "eventually (\<lambda>x. 1 = (if f x = 0 \<and> f x = 0 then 1 else f x / f x)) F"
    by (intro always_eventually) simp
  moreover have "((\<lambda>_. 1) \<longlongrightarrow> 1) F" by simp
  ultimately show "((\<lambda>x. if f x = 0 \<and> f x = 0 then 1 else f x / f x) \<longlongrightarrow> 1) F"
    by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_symI: 
  assumes "f \<sim>[F] g"
  shows   "g \<sim>[F] f"
  using tendsto_inverse[OF asymp_equivD[OF assms]]
  by (auto intro!: asymp_equivI simp: if_distrib conj_commute cong: if_cong)

lemma asymp_equiv_sym: "f \<sim>[F] g \<longleftrightarrow> g \<sim>[F] f"
  by (blast intro: asymp_equiv_symI)

lemma asymp_equivI': 
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> 1) F"
  shows   "f \<sim>[F] g"
proof (cases "F = bot")
  case False
  have "eventually (\<lambda>x. f x \<noteq> 0) F"
  proof (rule ccontr)
    assume "\<not>eventually (\<lambda>x. f x \<noteq> 0) F"
    hence "frequently (\<lambda>x. f x = 0) F" by (simp add: frequently_def)
    hence "frequently (\<lambda>x. f x / g x = 0) F" by (auto elim!: frequently_elim1)
    from limit_frequently_eq[OF False this assms] show False by simp_all
  qed
  hence "eventually (\<lambda>x. f x / g x = (if f x = 0 \<and> g x = 0 then 1 else f x / g x)) F"
    by eventually_elim simp
  from this and assms show "f \<sim>[F] g" unfolding asymp_equiv_def 
    by (rule Lim_transform_eventually)
qed (simp_all add: asymp_equiv_def)


lemma asymp_equiv_cong:
  assumes "eventually (\<lambda>x. f1 x = f2 x) F" "eventually (\<lambda>x. g1 x = g2 x) F"
  shows   "f1 \<sim>[F] g1 \<longleftrightarrow> f2 \<sim>[F] g2"
  unfolding asymp_equiv_def
proof (rule tendsto_cong, goal_cases)
  case 1
  from assms show ?case by eventually_elim simp
qed

lemma asymp_equiv_eventually_zeros:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f \<sim>[F] g"
  shows   "eventually (\<lambda>x. f x = 0 \<longleftrightarrow> g x = 0) F"
proof -
  let ?h = "\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "eventually (\<lambda>x. x \<noteq> 0) (nhds (1::'b))"
    by (rule t1_space_nhds) auto
  hence "eventually (\<lambda>x. x \<noteq> 0) (filtermap ?h F)"
    using assms unfolding asymp_equiv_def filterlim_def
    by (rule filter_leD [rotated])
  hence "eventually (\<lambda>x. ?h x \<noteq> 0) F" by (simp add: eventually_filtermap)
  thus ?thesis by eventually_elim (auto split: if_splits)
qed

lemma asymp_equiv_transfer:
  assumes "f1 \<sim>[F] g1" "eventually (\<lambda>x. f1 x = f2 x) F" "eventually (\<lambda>x. g1 x = g2 x) F"
  shows   "f2 \<sim>[F] g2"
  using assms(1) asymp_equiv_cong[OF assms(2,3)] by simp

lemma asymp_equiv_transfer_trans [trans]:
  assumes "(\<lambda>x. f x (h1 x)) \<sim>[F] (\<lambda>x. g x (h1 x))"
  assumes "eventually (\<lambda>x. h1 x = h2 x) F"
  shows   "(\<lambda>x. f x (h2 x)) \<sim>[F] (\<lambda>x. g x (h2 x))"
  by (rule asymp_equiv_transfer[OF assms(1)]) (insert assms(2), auto elim!: eventually_mono)

lemma asymp_equiv_trans [trans]:
  fixes f g h
  assumes "f \<sim>[F] g" "g \<sim>[F] h"
  shows   "f \<sim>[F] h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from assms[THEN asymp_equiv_eventually_zeros]
    have "eventually (\<lambda>x. ?T f g x * ?T g h x = ?T f h x) F" by eventually_elim simp
  moreover from tendsto_mult[OF assms[THEN asymp_equivD]] 
    have "((\<lambda>x. ?T f g x * ?T g h x) \<longlongrightarrow> 1) F" by simp
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_trans_lift1 [trans]:
  assumes "a \<sim>[F] f b" "b \<sim>[F] c" "\<And>c d. c \<sim>[F] d \<Longrightarrow> f c \<sim>[F] f d"
  shows   "a \<sim>[F] f c"
  using assms by (blast intro: asymp_equiv_trans)

lemma asymp_equiv_trans_lift2 [trans]:
  assumes "f a \<sim>[F] b" "a \<sim>[F] c" "\<And>c d. c \<sim>[F] d \<Longrightarrow> f c \<sim>[F] f d"
  shows   "f c \<sim>[F] b"
  using asymp_equiv_symI[OF assms(3)[OF assms(2)]] assms(1)
  by (blast intro: asymp_equiv_trans)

(* TODO Move *)
lemma Lim_eventually: "eventually (\<lambda>x. f x = c) F \<Longrightarrow> filterlim f (nhds c) F"
  by (simp add: eventually_mono eventually_nhds_x_imp_x filterlim_iff)

lemma asymp_equivD_const:
  assumes "f \<sim>[F] (\<lambda>_. c)"
  shows   "(f \<longlongrightarrow> c) F"
proof (cases "c = 0")
  case False
  with tendsto_mult_right[OF asymp_equivD[OF assms], of c] show ?thesis by simp
next
  case True
  with asymp_equiv_eventually_zeros[OF assms] show ?thesis
    by (simp add: Lim_eventually)
qed

lemma asymp_equiv_refl_ev:
  assumes "eventually (\<lambda>x. f x = g x) F"
  shows   "f \<sim>[F] g"
  by (intro asymp_equivI Lim_eventually)
     (insert assms, auto elim!: eventually_mono)

lemma asymp_equiv_sandwich:
  fixes f g h :: "'a \<Rightarrow> 'b :: {real_normed_field, order_topology, linordered_field}"
  assumes "eventually (\<lambda>x. f x \<ge> 0) F"
  assumes "eventually (\<lambda>x. f x \<le> g x) F"
  assumes "eventually (\<lambda>x. g x \<le> h x) F"
  assumes "f \<sim>[F] h"
  shows   "g \<sim>[F] f" "g \<sim>[F] h"
proof -
  show "g \<sim>[F] f"
  proof (rule asymp_equivI, rule tendsto_sandwich)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. (if h n = 0 \<and> f n = 0 then 1 else h n / f n) \<ge>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) F"
        by eventually_elim (auto intro!: divide_right_mono)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. 1 \<le>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) F"
        by eventually_elim (auto intro!: divide_right_mono)
  qed (insert asymp_equiv_symI[OF assms(4)], simp_all add: asymp_equiv_def)
  also note \<open>f \<sim>[F] h\<close>
  finally show "g \<sim>[F] h" .
qed


context
begin

private lemma asymp_equiv_add_rightI:
  assumes "f \<sim>[F] g" "h \<in> o[F](g)"
  shows   "(\<lambda>x. f x + h x) \<sim>[F] g"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from landau_o.smallD[OF assms(2) zero_less_one]
    have ev: "eventually (\<lambda>x. g x = 0 \<longrightarrow> h x = 0) F" by eventually_elim auto
  have "(\<lambda>x. f x + h x) \<sim>[F] g \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1) F"
    unfolding asymp_equiv_def using ev
    by (intro tendsto_cong) (auto elim!: eventually_mono simp: divide_simps)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1 + 0) F" by simp
  also have \<dots> by (intro tendsto_intros asymp_equivD assms smalloD_tendsto)
  finally show "(\<lambda>x. f x + h x) \<sim>[F] g" .
qed

lemma asymp_equiv_add_right [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "(\<lambda>x. f x + h x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] g"
proof
  assume "(\<lambda>x. f x + h x) \<sim>[F] g"
  from asymp_equiv_add_rightI[OF this, of "\<lambda>x. -h x"] assms show "f \<sim>[F] g"
    by simp
qed (simp_all add: asymp_equiv_add_rightI assms)

end

lemma asymp_equiv_add_left [asymp_equiv_simps]: 
  assumes "h \<in> o[F](g)"
  shows   "(\<lambda>x. h x + f x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] g"
  using asymp_equiv_add_right[OF assms] by (simp add: add.commute)

lemma asymp_equiv_add_right' [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "g \<sim>[F] (\<lambda>x. f x + h x) \<longleftrightarrow> g \<sim>[F] f"
  using asymp_equiv_add_right[OF assms] by (simp add: asymp_equiv_sym)
  
lemma asymp_equiv_add_left' [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "g \<sim>[F] (\<lambda>x. h x + f x) \<longleftrightarrow> g \<sim>[F] f"
  using asymp_equiv_add_left[OF assms] by (simp add: asymp_equiv_sym)

lemma asymp_equiv_uminus [asymp_equiv_intros]:
  "f \<sim>[F] g \<Longrightarrow> (\<lambda>x. -f x) \<sim>[F] (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_uminus_iff [asymp_equiv_simps]:
  "(\<lambda>x. -f x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_mult [asymp_equiv_intros]:
  fixes f1 f2 g1 g2 :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f1 \<sim>[F] g1" "f2 \<sim>[F] g2"
  shows   "(\<lambda>x. f1 x * f2 x) \<sim>[F] (\<lambda>x. g1 x * g2 x)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  let ?S = "\<lambda>x. (if f1 x = 0 \<and> g1 x = 0 then 1 - ?T f2 g2 x
                   else if f2 x = 0 \<and> g2 x = 0 then 1 - ?T f1 g1 x else 0)"
  let ?S' = "\<lambda>x. ?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) x - ?T f1 g1 x * ?T f2 g2 x"
  {
    fix f g :: "'a \<Rightarrow> 'b" assume "f \<sim>[F] g"
    have "((\<lambda>x. 1 - ?T f g x) \<longlongrightarrow> 0) F"
      by (rule tendsto_eq_intros refl asymp_equivD[OF \<open>f \<sim>[F] g\<close>])+ simp_all
  } note A = this    

  from assms have "((\<lambda>x. ?T f1 g1 x * ?T f2 g2 x) \<longlongrightarrow> 1 * 1) F"
    by (intro tendsto_mult asymp_equivD)
  moreover {
    have "eventually (\<lambda>x. ?S x = ?S' x) F"
      using assms[THEN asymp_equiv_eventually_zeros] by eventually_elim auto
    moreover have "(?S \<longlongrightarrow> 0) F"
      by (intro filterlim_If assms[THEN A, THEN tendsto_mono[rotated]])
         (auto intro: le_infI1 le_infI2)
    ultimately have "(?S' \<longlongrightarrow> 0) F" by (rule Lim_transform_eventually)
  }
  ultimately have "(?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) \<longlongrightarrow> 1 * 1) F"
    by (rule Lim_transform)
  thus ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_power [asymp_equiv_intros]:
  "f \<sim>[F] g \<Longrightarrow> (\<lambda>x. f x ^ n) \<sim>[F] (\<lambda>x. g x ^ n)"
  by (induction n) (simp_all add: asymp_equiv_mult)

lemma asymp_equiv_inverse [asymp_equiv_intros]:
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x))"
proof -
  from tendsto_inverse[OF asymp_equivD[OF assms]]
    have "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) \<longlongrightarrow> 1) F"
    by (simp add: if_distrib cong: if_cong)
  also have "(\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) =
               (\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else inverse (f x) / inverse (g x))"
    by (intro ext) (simp add: field_simps)
  finally show ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_inverse_iff [asymp_equiv_simps]:
  "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<sim>[F] g"
proof
  assume "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x))"
  hence "(\<lambda>x. inverse (inverse (f x))) \<sim>[F] (\<lambda>x. inverse (inverse (g x)))" (is ?P)
    by (rule asymp_equiv_inverse)
  also have "?P \<longleftrightarrow> f \<sim>[F] g" by (intro asymp_equiv_cong) simp_all
  finally show "f \<sim>[F] g" .
qed (simp_all add: asymp_equiv_inverse)

lemma asymp_equiv_divide [asymp_equiv_intros]:
  assumes "f1 \<sim>[F] g1" "f2 \<sim>[F] g2"
  shows   "(\<lambda>x. f1 x / f2 x) \<sim>[F] (\<lambda>x. g1 x / g2 x)"
  using asymp_equiv_mult[OF assms(1) asymp_equiv_inverse[OF assms(2)]] by (simp add: field_simps)

lemma asymp_equiv_compose [asymp_equiv_intros]:
  assumes "f \<sim>[G] g" "filterlim h G F"
  shows   "f \<circ> h \<sim>[F] g \<circ> h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "f \<circ> h \<sim>[F] g \<circ> h \<longleftrightarrow> ((?T f g \<circ> h) \<longlongrightarrow> 1) F"
    by (simp add: asymp_equiv_def o_def)
  also have "\<dots> \<longleftrightarrow> (?T f g \<longlongrightarrow> 1) (filtermap h F)"
    by (rule tendsto_compose_filtermap)
  also have "\<dots>"
    by (rule tendsto_mono[of _ G]) (insert assms, simp_all add: asymp_equiv_def filterlim_def)
  finally show ?thesis .
qed

lemma asymp_equiv_compose':
  assumes "f \<sim>[G] g" "filterlim h G F"
  shows   "(\<lambda>x. f (h x)) \<sim>[F] (\<lambda>x. g (h x))"
  using asymp_equiv_compose[OF assms] by (simp add: o_def)
  
lemma asymp_equiv_powr_real [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<sim>[F] g" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr y) \<sim>[F] (\<lambda>x. g x powr y)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "eventually (\<lambda>x. ?T f g x powr y = ?T (\<lambda>x. f x powr y) (\<lambda>x. g x powr y) x) F"
    using asymp_equiv_eventually_zeros[OF assms(1)] assms(2,3)
    by eventually_elim (auto simp: powr_divide)
  moreover have "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1 powr y) F"
    by (intro tendsto_intros asymp_equivD[OF assms(1)]) simp_all
  hence "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1) F" by simp
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_norm [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. norm (f x)) \<sim>[F] (\<lambda>x. norm (g x))"
  using tendsto_norm[OF asymp_equivD[OF assms]] 
  by (simp add: if_distrib asymp_equiv_def norm_divide cong: if_cong)

lemma asymp_equiv_abs_real [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. \<bar>f x\<bar>) \<sim>[F] (\<lambda>x. \<bar>g x\<bar>)"
  using tendsto_rabs[OF asymp_equivD[OF assms]] 
  by (simp add: if_distrib asymp_equiv_def cong: if_cong)

lemma asymp_equiv_imp_eventually_le:
  assumes "f \<sim>[F] g" "c > 1"
  shows   "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F"
proof -
  from order_tendstoD(2)[OF asymp_equivD[OF asymp_equiv_norm[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_eventually_ge:
  assumes "f \<sim>[F] g" "c < 1"
  shows   "eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F"
proof -
  from order_tendstoD(1)[OF asymp_equivD[OF asymp_equiv_norm[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_bigo:
  assumes "f \<sim>[F] g"
  shows   "f \<in> O[F](g)"
proof (rule bigoI)
  have "(3/2::real) > 1" by simp
  from asymp_equiv_imp_eventually_le[OF assms this]
    show "eventually (\<lambda>x. norm (f x) \<le> 3/2 * norm (g x)) F"
    by eventually_elim simp
qed

lemma asymp_equiv_imp_bigomega:
  "f \<sim>[F] g \<Longrightarrow> f \<in> \<Omega>[F](g)"
  using asymp_equiv_imp_bigo[of g F f] by (simp add: asymp_equiv_sym bigomega_iff_bigo)

lemma asymp_equiv_imp_bigtheta:
  "f \<sim>[F] g \<Longrightarrow> f \<in> \<Theta>[F](g)"
  by (intro bigthetaI asymp_equiv_imp_bigo asymp_equiv_imp_bigomega)
  

lemma asymp_equivI'_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F" "c \<noteq> 0"
  shows   "f \<sim>[F] (\<lambda>x. c * g x)"
  using tendsto_mult[OF assms(1) tendsto_const[of "inverse c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)

lemma asymp_equivI'_inverse_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> inverse c) F" "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) \<sim>[F] g"
  using tendsto_mult[OF assms(1) tendsto_const[of "c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)
  
end
