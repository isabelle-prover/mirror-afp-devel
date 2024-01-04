(*  Author: Ata Keskin, TU München 
*)

theory Eudoxus
  imports Slope
begin

section \<open>Eudoxus Reals\<close>

subsection \<open>Type Definition\<close>

text \<open>Two slopes are said to be equivalent if their difference is bounded.\<close>
definition eudoxus_rel :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> bool" (infix "\<sim>\<^sub>e" 50) where 
  "f \<sim>\<^sub>e g \<equiv> slope f \<and> slope g \<and> bounded (\<lambda>n. f n - g n)"

lemma eudoxus_rel_equivp:
  "part_equivp eudoxus_rel"
proof (rule part_equivpI)
  show "\<exists>x. x \<sim>\<^sub>e x" unfolding eudoxus_rel_def slope_def bounded_def by fast
  show "symp (\<sim>\<^sub>e)"  unfolding eudoxus_rel_def by (force intro: sympI dest: bounded_uminus simp: fun_Compl_def) 
  show "transp (\<sim>\<^sub>e)"  unfolding eudoxus_rel_def by (force intro!: transpI dest: bounded_add)
qed

text \<open>We define the reals as the set of all equivalence classes of the relation \<^term>\<open>eudoxus_rel\<close>.\<close>
quotient_type real = "(int \<Rightarrow> int)" / partial: eudoxus_rel
  by (rule eudoxus_rel_equivp)

lemma real_quot_type: "quot_type (\<sim>\<^sub>e) Abs_real Rep_real"
  using Rep_real Abs_real_inverse Rep_real_inverse Rep_real_inject eudoxus_rel_equivp by (auto intro!: quot_type.intro)

lemma slope_refl: "slope f = (f \<sim>\<^sub>e f)"
  unfolding eudoxus_rel_def by (fastforce simp add: bounded_constant)

declare slope_refl[THEN iffD2, simp]

lemmas slope_reflI = slope_refl[THEN iffD1]

lemma slope_induct[consumes 0, case_names slope]: 
  assumes "\<And>f. slope f \<Longrightarrow> P (abs_real f)"
  shows "P x"
  using assms by induct force

lemma abs_real_eq_iff: "f \<sim>\<^sub>e g \<longleftrightarrow> slope f \<and> slope g \<and> abs_real f = abs_real g" 
  by (metis Quotient_real Quotient_rel slope_refl)

lemma abs_real_eqI[intro]: "f \<sim>\<^sub>e g \<Longrightarrow> abs_real f = abs_real g" using abs_real_eq_iff by blast

lemmas eudoxus_rel_sym[sym] = Quotient_symp[OF Quotient_real, THEN sympD]
lemmas eudoxus_rel_trans[trans] = Quotient_transp[OF Quotient_real, THEN transpD]

lemmas rep_real_abs_real_refl = Quotient_rep_abs[OF Quotient_real, OF slope_refl[THEN iffD1], intro!]
lemmas rep_real_iff = Quotient_rel_rep[OF Quotient_real, iff]

declare Quotient_abs_rep[OF Quotient_real, simp]

lemma slope_rep_real: "slope (rep_real x)" by simp

lemma eudoxus_relI:
  assumes "slope f" "slope g" "\<And>n. n \<ge> N \<Longrightarrow> \<bar>f n - g n\<bar> \<le> C"
  shows "f \<sim>\<^sub>e g"
proof -
  have C_nonneg: "C \<ge> 0" using assms by force

  obtain C_f where C_f: "\<bar>f (n + (- n)) - (f n + f (- n))\<bar> \<le> C_f" "0 \<le> C_f" for n using assms by fast

  obtain C_g where C_g: "\<bar>g (n + (- n)) - (g n + g (- n))\<bar> \<le> C_g" "0 \<le> C_g" for n using assms by fast
  
  have bound: "\<bar>f (- n) - g (- n)\<bar> \<le> \<bar>f n - g n\<bar> + \<bar>f 0\<bar> + \<bar>g 0\<bar> + C_f + C_g" for n using C_f(1)[of n] C_g(1)[of n] by simp

  define C' where "C' = Sup {\<bar>f n - g n\<bar> | n. n \<in> {0..max 0 N}} + C + \<bar>f 0\<bar> + \<bar>g 0\<bar> + C_f + C_g"
  have *: "bdd_above {\<bar>f n - g n\<bar> |n. n \<in> {0..max 0 N}}" by simp
  have "Sup {\<bar>f n - g n\<bar> |n. n \<in> {0..max 0 N}} \<in> {\<bar>f n - g n\<bar> |n. n \<in> {0..max 0 N}}" using C_nonneg by (intro int_Sup_mem[OF _ *]) auto
  hence Sup_nonneg: "Sup {\<bar>f n - g n\<bar> | n. n \<in> {0..max 0 N}} \<ge> 0" by fastforce

  have *: "\<bar>f n - g n\<bar> \<le> Sup {\<bar>f n - g n\<bar> | n. n \<in> {0..max 0 N}} + C" if "n \<ge> 0" for n unfolding C'_def using cSup_upper[OF _ *] that C_nonneg Sup_nonneg by (cases "n \<le> N") (fastforce simp add: add.commute add_increasing2 assms(3))+
  {
    fix n
    have "\<bar>f n - g n\<bar> \<le> C'"
    proof (cases "n \<ge> 0")
      case True
      thus ?thesis unfolding C'_def using * C_f C_g by fastforce
    next
      case False
      hence "- n \<ge> 0" by simp
      hence "\<bar>f (- n) - g (- n)\<bar> \<le> Sup {\<bar>f n - g n\<bar> | n. n \<in> {0..max 0 N}} + C" using *[of "- n"] by blast
      hence "\<bar>f (- (- n)) - g (- (- n))\<bar> \<le> C'" unfolding C'_def using bound[of "- n"] by linarith
      thus ?thesis by simp
    qed
  }
  thus ?thesis using assms unfolding eudoxus_rel_def by (auto intro: boundedI)
qed

subsection \<open>Addition and Subtraction\<close>

text \<open>We define addition, subtraction and the additive identity as follows.\<close>
instantiation real :: "{zero, plus, minus, uminus}"
begin

quotient_definition
  "0 :: real" is "abs_real (\<lambda>_. 0)" .

declare slope_zero[intro!, simp]

lemma zero_iff_bounded: "f \<sim>\<^sub>e (\<lambda>_. 0) \<longleftrightarrow> bounded f" by (metis (no_types, lifting) boundedE boundedI diff_zero eudoxus_rel_def slope_zero bounded_slopeI)
lemma zero_iff_bounded': "x = 0 \<longleftrightarrow> bounded (rep_real x)" by (metis (mono_tags) abs_real_eq_iff id_apply rep_real_abs_real_refl rep_real_iff slope_zero zero_iff_bounded zero_real_def)

lemma zero_def: "0 = abs_real (\<lambda>_. 0)" unfolding zero_real_def by simp

definition eudoxus_plus :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" (infixl "+\<^sub>e" 60) where
  "(f :: int \<Rightarrow> int) +\<^sub>e g = (\<lambda>z. f z + g z)"

declare slope_add[intro, simp]

quotient_definition
  "(+) :: (real \<Rightarrow> real \<Rightarrow> real)" is "(+\<^sub>e)" 
proof -
  fix x x' y y' assume "x \<sim>\<^sub>e x'" "y \<sim>\<^sub>e y'"
  hence rel_x: "slope x" "slope x'" "bounded (\<lambda>z. x z - x' z)" and rel_y: "slope y" "slope y'" "bounded (\<lambda>z. y z - y' z)" unfolding eudoxus_rel_def by blast+
  thus "(x +\<^sub>e y) \<sim>\<^sub>e (x' +\<^sub>e y')" unfolding eudoxus_rel_def eudoxus_plus_def by (fastforce intro: back_subst[of bounded, OF bounded_add[OF rel_x(3) rel_y(3)]])
qed

lemmas eudoxus_plus_cong = apply_rsp'[OF plus_real.rsp, THEN rel_funD, intro]

lemma abs_real_plus[simp]:
  assumes "slope f" "slope g"
  shows "abs_real f + abs_real g = abs_real (f +\<^sub>e g)"
  using assms unfolding plus_real_def by auto

definition eudoxus_uminus :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" ("-\<^sub>e") where
  "-\<^sub>e (f :: int \<Rightarrow> int) = (\<lambda>x. - f x)"

declare slope_uminus'[intro, simp]

quotient_definition
  "(uminus) :: (real \<Rightarrow> real)" is "-\<^sub>e"
proof -
  fix x x' assume "x \<sim>\<^sub>e x'"
  hence rel_x: "slope x" "slope x'" "bounded (\<lambda>z. x z - x' z)" unfolding eudoxus_rel_def by blast+
  thus "-\<^sub>e x \<sim>\<^sub>e -\<^sub>e x'" unfolding eudoxus_rel_def eudoxus_uminus_def by (fastforce intro: back_subst[of bounded, OF bounded_uminus[OF rel_x(3)]])
qed

lemmas eudoxus_uminus_cong = apply_rsp'[OF uminus_real.rsp, simplified, intro]

lemma abs_real_uminus[simp]: 
  assumes "slope f"
  shows "- abs_real f = abs_real (-\<^sub>e f)"
  using assms unfolding uminus_real_def by auto

definition "x - (y::real) = x + - y"

declare slope_minus[intro, simp]

lemma abs_real_minus[simp]:
  assumes "slope g" "slope f"
  shows "abs_real g - abs_real f = abs_real (g +\<^sub>e (-\<^sub>e f))" 
  using assms by (simp add: minus_real_def slope_refl eudoxus_uminus_cong)

instance ..
end

text \<open>The Eudoxus reals equipped with addition and negation specified as above constitute an Abelian group.\<close>
instance real :: ab_group_add
proof
  fix x y z :: real
  show "x + y + z = x + (y + z)" by (induct x, induct y, induct z) (simp add: eudoxus_plus_cong eudoxus_plus_def add.assoc)
  show "x + y = y + x" by (induct x, induct y) (simp add: eudoxus_plus_def add.commute)
  show "0 + x = x" by (induct x) (simp add: zero_real_def eudoxus_plus_def)
  show "- x + x = 0" by (induct x) (simp add: eudoxus_uminus_cong, simp add: zero_real_def eudoxus_plus_def eudoxus_uminus_def)
qed (simp add: minus_real_def)

subsection \<open>Multiplication\<close>

text \<open>We define multiplication as the composition of two slopes.\<close>
instantiation real :: "{one, times}"
begin

quotient_definition
  "1 :: real" is "abs_real id" .

declare slope_one[intro!, simp]

lemma one_def: "1 = abs_real id" unfolding one_real_def by simp

definition eudoxus_times :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" (infixl "*\<^sub>e" 60) where
  "f *\<^sub>e g = f o g"

declare slope_comp[intro, simp]
declare slope_scale[intro, simp]

quotient_definition
  "(*) :: real \<Rightarrow> real \<Rightarrow> real" is "(*\<^sub>e)"
proof -
  fix x x' y y' assume "x \<sim>\<^sub>e x'" "y \<sim>\<^sub>e y'"
  hence rel_x: "slope x" "slope x'" "bounded (\<lambda>z. x z - x' z)" and rel_y: "slope y" "slope y'" "bounded (\<lambda>z. y z - y' z)" unfolding eudoxus_rel_def by blast+

  obtain C where x'_bound: "\<bar>x' (m + n) - (x' m + x' n)\<bar> \<le> C" for m n using rel_x(2) unfolding slope_def by fastforce
  
  obtain A B where x'_lin_bound: "\<bar>x' n\<bar> \<le> A * \<bar>n\<bar> + B" "0 \<le> A" "0 \<le> B" for n using slope_linear_bound[OF rel_x(2)] by blast

  obtain C' where y_y'_bound: "\<bar>y z - y' z\<bar> \<le> C'" for z using rel_y(3) unfolding slope_def by fastforce

  have "bounded (\<lambda>z. x' (y z) - x' (y' z))" 
  proof (rule boundedI)
    fix z
    have "\<bar>x' (y z) - x' (y' z)\<bar> \<le> \<bar>x' (y z - y' z)\<bar> + C" using x'_bound[of "y z - y' z" "y' z"] by fastforce
    also have "... \<le> A * \<bar>y z - y' z\<bar> + B + C" using x'_lin_bound by force
    also have "... \<le> A * C' + B + C" using mult_left_mono[OF y_y'_bound x'_lin_bound(2)] by fastforce
    finally show "\<bar>x' (y z) - x' (y' z)\<bar> \<le> A * C' + B + C" by blast
  qed
  hence "bounded (\<lambda>z. x (y z) - x' (y' z))" using bounded_add[OF bounded_comp(1)[OF rel_x(3), of y]] by force
  thus "(x *\<^sub>e y) \<sim>\<^sub>e (x' *\<^sub>e y')" unfolding eudoxus_rel_def eudoxus_times_def using rel_x rel_y by simp
qed

lemmas eudoxus_times_cong = apply_rsp'[OF times_real.rsp, THEN rel_funD, intro]
lemmas eudoxus_rel_comp = eudoxus_times_cong[unfolded eudoxus_times_def]

lemma eudoxus_times_commute:
  assumes "slope f" "slope g"
  shows "(f *\<^sub>e g) \<sim>\<^sub>e (g *\<^sub>e f)"
  unfolding eudoxus_rel_def eudoxus_times_def
  using slope_comp slope_comp_commute assms by blast

lemma abs_real_times[simp]: 
  assumes "slope f" "slope g"
  shows "abs_real f * abs_real g = abs_real (f *\<^sub>e g)"
  using assms unfolding times_real_def by auto

instance ..
end

lemma neg_one_def: "- 1 = abs_real (-\<^sub>e id)" unfolding one_real_def by (simp add: eudoxus_uminus_def)
lemma slope_neg_one[intro, simp]: "slope (-\<^sub>e id)" using slope_refl by blast

text \<open>With the definitions provided above, the Eudoxus reals are a commutative ring with unity.\<close>
instance real :: comm_ring_1
proof
  fix x y z :: real
  show "x * y * z = x * (y * z)" by (induct x, induct y, induct z) (simp add: eudoxus_times_cong eudoxus_times_def comp_assoc)
  show "x * y = y * x" by (induct x, induct y) (force simp add: slope_refl eudoxus_times_commute)
  show "1 * x = x" by (induct x) (simp add: one_real_def eudoxus_times_def)
  show "(x + y) * z = x * z + y * z" by (induct x, induct y, induct z) (simp add: eudoxus_times_cong eudoxus_plus_cong, simp add: eudoxus_times_def eudoxus_plus_def comp_def)
  have "\<not>bounded (\<lambda>x. x)" by (metis add.inverse_inverse boundedE_strict less_irrefl neg_less_0_iff_less zabs_def)
  thus "(0 :: real) \<noteq> (1 :: real)" using abs_real_eq_iff[of id "\<lambda>_. 0"] unfolding one_real_def zero_real_def eudoxus_rel_def by simp
qed

lemma real_of_nat:
  "of_nat n = abs_real ((*) (of_nat n))"
proof (induction n)
  case 0
  then show ?case by (simp add: zero_real_def)
next
  case (Suc n)
  then show ?case by (simp add: one_real_def distrib_right eudoxus_plus_def)
qed

lemma real_of_int:
  "of_int z = abs_real ((*) z)"
proof (induction z rule: int_induct[where ?k=0])
  case base
  then show ?case by (simp add: zero_real_def)
next
  case (step1 i)
  then show ?case by (simp add: one_real_def distrib_right eudoxus_plus_def)
next
  case (step2 i)
  then show ?case by (simp add: one_real_def eudoxus_plus_def left_diff_distrib eudoxus_uminus_def)
qed

text \<open>The Eudoxus reals are a ring of characteristic \<^term>\<open>0\<close>.\<close>
instance real :: ring_char_0
proof
  show "inj (\<lambda>n. of_nat n :: real)"
  proof (intro inj_onI)
    fix x y assume "(of_nat x :: real) = of_nat y"
    hence "((*) (int x)) \<sim>\<^sub>e ((*) (int y))" unfolding abs_real_eq_iff real_of_nat using slope_scale by blast
    hence "bounded (\<lambda>z. (int x - int y) * z)" unfolding eudoxus_rel_def by (simp add: left_diff_distrib)
    then obtain C where bound: "\<bar>(int x - int y) * z\<bar> \<le> C" and C_nonneg: "0 \<le> C" for z by blast
    hence "\<bar>int x - int y\<bar> * \<bar>C + 1\<bar> \<le> C"  using abs_mult by metis
    hence *: "\<bar>int x - int y\<bar> * (C + 1) \<le> C" using C_nonneg by force
    thus "x = y" using order_trans[OF mult_right_mono *, of 1] C_nonneg by fastforce
  qed
qed

subsection \<open>Ordering\<close>

text \<open>We call a slope positive, if it tends to infinity. Similarly, we call a slope negative if it tends to negative infinity.\<close>
instantiation real :: "{ord, abs, sgn}"
begin

definition pos :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "pos f = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<ge> N. f n \<ge> C)"

definition neg :: "(int \<Rightarrow> int) \<Rightarrow> bool" where
  "neg f = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<ge> N. f n \<le> -C)"
                                  
lemma pos_neg_exclusive: "\<not> (pos f \<and> neg f)" unfolding neg_def pos_def by (metis int_one_le_iff_zero_less linorder_not_less nle_le uminus_int_code(1) zero_less_one_class.zero_le_one)

lemma pos_iff_neg_uminus: "pos f = neg (-\<^sub>e f)" unfolding neg_def pos_def eudoxus_uminus_def by simp

lemma neg_iff_pos_uminus: "neg f = pos (-\<^sub>e f)" unfolding neg_def pos_def eudoxus_uminus_def by fastforce

lemma pos_iff:
  assumes "slope f"
  shows "pos f = infinite (f ` {0..} \<inter> {0<..})" (is "?lhs = ?rhs")
proof (rule iffI)
  assume pos: ?lhs
  {
    fix C assume C_nonneg: "0 \<le> (C :: int)"
    hence "\<exists>z \<ge> 0. (C + 1) \<le> f z" by (metis add_increasing2 nle_le zero_less_one_class.zero_le_one pos pos_def)
    hence "\<exists>z \<ge> 0. C \<le> f z \<and> 0 < f z" using C_nonneg by fastforce
    hence "\<exists>N\<ge>C. \<exists>z. N = f z \<and> 0 < f z \<and> 0 \<le> z" by blast
  }
  thus ?rhs by (blast intro!: int_set_infiniteI)
next
  assume infinite: ?rhs
  then obtain D where D_bound: "\<bar>f (m + n) - (f m + f n)\<bar> < D" "0 < D" for m n using assms by (fastforce simp: slope_def elim: boundedE_strict)
 
  obtain M where M_bound: "\<forall>m>0. (m + 1) * D \<le> f (m * M)" "0 < M" using slope_positive_lower_bound[OF assms infinite] D_bound(2) by blast

  define g where "g = (\<lambda>z. f ((z div M) * M))"
  define E where "E = Sup ((abs o f) ` {z. 0 \<le> z \<and> z < M})"
  
  have E_bound: "\<bar>f (z mod M)\<bar> \<le> E" for z
  proof -
    have "(z mod M) \<in> {z. 0 \<le> z \<and> z < M}" by (simp add: M_bound(2))
    hence "\<bar>f (z mod M)\<bar> \<in> (abs o f) ` {z. 0 \<le> z \<and> z < M}" by fastforce
    thus "\<bar>f (z mod M)\<bar> \<le> E" unfolding E_def by (simp add: le_cSup_finite)
  qed
  hence E_nonneg: "0 \<le> E" by fastforce

  have diff_bound: "\<bar>f z - g z\<bar> \<le> E + D" for z
  proof-
    let ?d = "z div M" and ?r = "z mod M"
    have z_is: "z = ?d * M + ?r" by presburger
    hence "\<bar>f z - g z\<bar> = \<bar>f (?d * M + ?r) - g (?d * M + ?r)\<bar>" by argo
    also have "... = \<bar>(f (?d*M + ?r) - (f (?d * M) + f ?r)) + (f (?d * M) + f ?r) - g (?d * M + ?r)\<bar>" by auto
    also have "... = \<bar>f ?r + (f (?d*M + ?r) - (f (?d * M) + f ?r))\<bar>" unfolding g_def by force
    also have "... \<le> \<bar>f ?r\<bar> + D" using D_bound(1)[of "?d * M" "?r"] by linarith
    also have "... \<le> E + D" using E_bound by simp
    finally show "\<bar>f z - g z\<bar> \<le> E + D" .
  qed
  {
    fix C assume C_nonneg: "0 \<le> (C :: int)"
  
    define n where "n = (E + D + C) div D"
    hence zero_less_n: "n > 0" using D_bound(2) E_nonneg C_nonneg using pos_imp_zdiv_pos_iff by fastforce
   
    have "E + C < E + D + C - (E + D + C) mod D" using diff_strict_left_mono[OF pos_mod_bound[OF D_bound(2)]] by simp
    also have "... = n * D" unfolding n_def using div_mod_decomp_int[of "E + D + C" D] by algebra
    finally have *: "(n + 1) * D > E + D + C" by (simp add: add.commute distrib_right)
  
    have "C \<le> f m" if "m \<ge> n * M" for m
    proof -
      let ?d = "m div M" and ?r = "m mod M"
      have d_pos: "?d > 0" using zero_less_n M_bound that dual_order.trans pos_imp_zdiv_pos_iff by fastforce
      have n_le_d: "?d \<ge> n" using zdiv_mono1 M_bound that by fastforce
      have "E + D + C < (?d + 1) * D" using D_bound n_le_d by (intro *[THEN order.strict_trans2]) simp
      also have "... \<le> g m" unfolding g_def using M_bound d_pos by blast
      finally have "E + D + C < g m" .
      hence "\<bar>f m - g m\<bar> + C < g m" using diff_bound[of m] by fastforce
      thus ?thesis by fastforce
    qed
    hence "\<exists>N. \<forall>p\<ge>N. C \<le> f p" using add1_zle_eq by blast
  }
  thus ?lhs unfolding pos_def by blast
qed

lemma neg_iff:
  assumes "slope f"
  shows "neg f = infinite (f ` {0..} \<inter> {..<0})" (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  hence "infinite ((- f) ` {0..} \<inter> {0<..})" using pos_iff[OF slope_uminus'[OF assms]] unfolding neg_def pos_def by fastforce
  moreover have "inj (uminus :: int \<Rightarrow> int)" by simp
  moreover have "(- f) ` {0..} \<inter> {0<..} = uminus ` (f ` {0..} \<inter> {..<0})" by fastforce
  ultimately show ?rhs using finite_imageD by fastforce
next
  assume ?rhs
  moreover have "inj (uminus :: int \<Rightarrow> int)" by simp
  moreover have "f ` {0..} \<inter> {..<0} = uminus ` ((- f) ` {0..} \<inter> {0<..})" by force
  ultimately have "infinite ((- f) ` {0..} \<inter> {0<..})" using finite_imageD by force
  thus ?lhs using pos_iff[OF slope_uminus'[OF assms]] unfolding pos_def neg_def by fastforce
qed

lemma pos_cong:
  assumes "f \<sim>\<^sub>e g"
  shows "pos f = pos g"
proof -
  { 
    fix x y assume asm: "pos x" "x \<sim>\<^sub>e y"
    fix D assume D: "0 \<le> D" "\<forall>N. \<exists>p\<ge>N. \<not> D \<le> y p"
    obtain C where bounds: "\<forall>n. \<bar>x n - y n\<bar> \<le> C" "0 \<le> C" using asm unfolding eudoxus_rel_def by blast
    obtain N where "\<forall>p\<ge>N. C + D \<le> x p" using D bounds asm by (fastforce simp add: pos_def)
    hence "\<forall>p\<ge>N. \<bar>x p - y p\<bar> + D \<le> x p" by (metis add.commute add_left_mono bounds(1) dual_order.trans)
    hence "\<forall>p\<ge>N. D \<le> y p" by force
    hence False using D by blast
  }
  hence "pos x \<Longrightarrow> pos y" if "x \<sim>\<^sub>e y" for x y using that unfolding pos_def by metis
  thus ?thesis by (metis assms eudoxus_rel_equivp part_equivp_symp)
qed

lemma neg_cong:
  assumes "f \<sim>\<^sub>e g"
  shows "neg f = neg g"
proof -
  { 
    fix x y assume asm: "neg x" "x \<sim>\<^sub>e y"
    fix D assume D: "0 \<le> D" "\<forall>N. \<exists>p\<ge>N. \<not> - D \<ge> y p"
    obtain C where bounds: "\<bar>x n - y n\<bar> \<le> C" "0 \<le> C" for n using asm unfolding eudoxus_rel_def by blast
    obtain N where "\<forall>p\<ge>N. - (C + D) \<ge> x p" using D bounds asm add_increasing2 unfolding neg_def by meson
    hence "\<forall>p\<ge>N. - \<bar>x p - y p\<bar> - D \<ge> x p" using bounds(1)[THEN le_imp_neg_le, THEN diff_right_mono, THEN dual_order.trans] by simp
    hence "\<forall>p\<ge>N. - D \<ge> y p" by force
    hence False using D by blast
  }
  hence "neg x \<Longrightarrow> neg y" if "x \<sim>\<^sub>e y" for x y using that unfolding neg_def by metis
  thus ?thesis by (metis assms eudoxus_rel_equivp part_equivp_symp)
qed

lemma pos_iff_nonneg_nonzero: 
  assumes "slope f"
  shows "pos f \<longleftrightarrow> (\<not> neg f) \<and> (\<not> bounded f)" (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI)
  assume pos: ?lhs
  then obtain N where "\<forall>n\<ge>N. f n > 0" unfolding pos_def by (metis int_one_le_iff_zero_less zero_less_one_class.zero_le_one)
  hence "f (max N m) > 0" for m by simp
  hence "\<not> neg f" unfolding neg_def by (metis add.inverse_neutral dual_order.refl linorder_not_le max.cobounded2)
  thus ?rhs using pos unfolding pos_def bounded_def bdd_above_def by (metis abs_ge_self dual_order.trans gt_ex imageI iso_tuple_UNIV_I order.strict_iff_not)
next
  assume nonneg_nonzero: ?rhs
  hence finite: "finite (f ` {0..} \<inter> {..<0})" using neg_iff assms by blast
  moreover have unbounded: "infinite (f ` {0..})" using nonneg_nonzero bounded_iff_finite_range slope_finite_range_iff assms by blast
  ultimately have "infinite (f ` {0..} \<inter> {0..})" by (metis Compl_atLeast Diff_Diff_Int Diff_eq Diff_infinite_finite)
  moreover have "f ` {0..} \<inter> {0<..} = f ` {0..} \<inter> {0..} - {0}" by force
  ultimately show ?lhs unfolding pos_iff[OF assms] by simp
qed

lemma neg_iff_nonpos_nonzero: 
  assumes "slope f"
  shows "neg f \<longleftrightarrow> (\<not> pos f) \<and> (\<not> bounded f)"
  unfolding pos_iff_nonneg_nonzero[OF assms] neg_iff_pos_uminus uminus_apply 
            eudoxus_uminus_def pos_iff_nonneg_nonzero[OF slope_uminus', OF assms]
  by (force simp add: bounded_def bdd_above_def)

text \<open>We define the sign of a slope to be \<^term>\<open>id\<close> if it is positive, \<^term>\<open>-\<^sub>e id\<close> if it is negative and \<^term>\<open>(\<lambda>_. 0)\<close> otherwise.\<close>
definition eudoxus_sgn :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where 
  "eudoxus_sgn f = (if pos f then id else if neg f then -\<^sub>e id else (\<lambda>_. 0))"

lemma eudoxus_sgn_iff:
  assumes "slope f"
  shows "eudoxus_sgn f = (\<lambda>_. 0) \<longleftrightarrow> bounded f"
        "eudoxus_sgn f = id \<longleftrightarrow> pos f"
        "eudoxus_sgn f = (-\<^sub>e id) \<longleftrightarrow> neg f" 
  using eudoxus_sgn_def neg_one_def one_def zero_def assms neg_iff_nonpos_nonzero pos_iff_nonneg_nonzero by auto

quotient_definition
  "(sgn :: real \<Rightarrow> real)" is eudoxus_sgn
  unfolding eudoxus_sgn_def
  using eudoxus_uminus_cong neg_cong pos_cong slope_one slope_refl by fastforce

lemmas eudoxus_sgn_cong = apply_rsp'[OF sgn_real.rsp, intro]

lemma eudoxus_sgn_cong'[cong]:
  assumes "f \<sim>\<^sub>e g"
  shows "eudoxus_sgn f = eudoxus_sgn g" 
  using assms eudoxus_sgn_def neg_cong pos_cong by presburger 

lemma sgn_range: "sgn (x :: real) \<in> {-1, 0, 1}" unfolding sgn_real_def zero_def one_def neg_one_def eudoxus_sgn_def by simp

lemma sgn_abs_real_zero_iff:
  assumes "slope f"
  shows "sgn (abs_real f) = 0 \<longleftrightarrow> (eudoxus_sgn f = (\<lambda>_. 0))" (is "?lhs \<longleftrightarrow> ?rhs")
  using eudoxus_sgn_cong[OF rep_real_abs_real_refl, OF assms] abs_real_eqI eudoxus_sgn_def neg_one_def one_def zero_def 
  by (auto simp add: sgn_real_def)

lemma sgn_zero_iff[simp]: "sgn (x :: real) = 0 \<longleftrightarrow> x = 0"
  using eudoxus_sgn_iff(1) sgn_abs_real_zero_iff zero_iff_bounded' slope_refl
  by (induct x) (metis (mono_tags) rep_real_abs_real_refl rep_real_iff)

lemma sgn_zero[simp]: "sgn (0 :: real) = 0" by simp

lemma sgn_abs_real_one_iff: 
  assumes "slope f"
  shows "sgn (abs_real f) = 1 \<longleftrightarrow> pos f"
  using eudoxus_sgn_cong[OF rep_real_abs_real_refl, OF assms] abs_real_eqI eudoxus_sgn_def neg_one_def one_def zero_def 
  by (auto simp add: sgn_real_def)

lemmas sgn_pos = sgn_abs_real_one_iff[THEN iffD2, simp]

lemma sgn_one[simp]: "sgn (1 :: real) = 1" by (subst one_def) (fastforce simp add: pos_def iff: sgn_abs_real_one_iff)

lemma sgn_abs_real_neg_one_iff:
  assumes "slope f"
  shows "sgn (abs_real f) = - 1 \<longleftrightarrow> neg f"
  using eudoxus_sgn_cong[OF rep_real_abs_real_refl, OF assms] abs_real_eqI eudoxus_sgn_def neg_one_def one_def zero_def pos_neg_exclusive
  by (auto simp add: sgn_real_def)

lemmas sgn_neg = sgn_abs_real_neg_one_iff[THEN iffD2, simp]

lemma sgn_neg_one[simp]: "sgn (- 1 :: real) = - 1" by (subst neg_one_def) (fastforce simp add: neg_def eudoxus_uminus_def iff: sgn_abs_real_neg_one_iff)

lemma sgn_plus:
  assumes "sgn x = (1 :: real)" "sgn y = 1"
  shows "sgn (x + y) = 1"
proof -
  have pos: "pos (rep_real x)" "pos (rep_real y)" using assms sgn_abs_real_one_iff[OF slope_rep_real] by simp+
  {
    fix C :: int assume C_nonneg: "C \<ge> 0"
    then obtain N M where "\<forall>n\<ge>N. rep_real x n \<ge> C" "\<forall>n\<ge>M. rep_real y n \<ge> C" using pos unfolding pos_def by presburger
    hence "\<forall>n\<ge> max N M. (rep_real x +\<^sub>e rep_real y) n \<ge> C" using C_nonneg unfolding eudoxus_plus_def by fastforce
    hence "\<exists>N. \<forall>n \<ge> N. (rep_real x +\<^sub>e rep_real y) n \<ge> C" by blast
  }
  thus ?thesis using pos_def by (simp add: eudoxus_plus_cong plus_real_def)
qed

lemma sgn_times: "sgn ((x :: real) * y) = sgn x * sgn y"
proof (cases "x = 0 \<or> y = 0")
  case False
  have *: "\<lbrakk>x \<noteq> 0; pos (rep_real y)\<rbrakk> \<Longrightarrow> sgn ((x :: real) * y) = sgn x * sgn y" for x y
  proof (induct x rule: slope_induct, induct y rule: slope_induct)
    case (slope y x)
    hence pos_y: "pos y" using pos_cong by blast
    show ?case
    proof (cases "pos x")
      case pos_x: True
      {
        fix C :: int assume asm: "C \<ge> 0"
        then obtain N where N: "\<forall>n \<ge> N. x n \<ge> C" using pos_x unfolding pos_def by blast
        then obtain N' where "\<forall>n\<ge> N'. y n \<ge> max 0 N" using pos_y unfolding pos_def by (meson max.cobounded1)
        hence "\<exists>N'. \<forall>n\<ge> N'. x (y n) \<ge> C" using N by force
      }
      hence "pos (x *\<^sub>e y)" unfolding pos_def eudoxus_times_def by simp
      thus ?thesis using pos_x pos_y slope by (simp add: eudoxus_times_def)
    next
      case _: False
      hence neg_x: "neg x" using slope by (metis abs_real_eqI neg_iff_nonpos_nonzero zero_def zero_iff_bounded)
      {
        fix C :: int assume "C \<ge> 0"
        then obtain N where N: "\<forall>n \<ge> N. x n \<le> - C" using neg_x unfolding neg_def by blast
        then obtain N' where "\<forall>n\<ge> N'. y n \<ge> max 0 N" using pos_y unfolding pos_def by (meson max.cobounded1)
        hence "\<exists>N'. \<forall>n\<ge> N'. x (y n) \<le> -C" using N by force
      }
      hence "neg (x *\<^sub>e y)" unfolding neg_def eudoxus_times_def by simp
      thus ?thesis using neg_x pos_y slope by (simp add: eudoxus_times_def)
    qed
  qed
  moreover have "sgn ((x :: real) * y) = sgn x * sgn y" if neg_x: "neg (rep_real x)" and neg_y: "neg (rep_real y)" for x y
  proof -
    have pos_uminus_y: "pos (rep_real (- y))" by (metis abs_real_eq_iff eudoxus_uminus_cong map_fun_apply neg_iff_pos_uminus neg_y pos_cong rep_real_abs_real_refl rep_real_iff uminus_real_def)
    moreover have "x \<noteq> 0" using neg_iff_nonpos_nonzero neg_x zero_iff_bounded' by fastforce
    ultimately have "sgn (- (x * y)) = - 1" using sgn_neg[OF slope_rep_real neg_x] sgn_pos[OF slope_rep_real pos_uminus_y] * by fastforce
    hence "pos (rep_real (x * y))" by (metis eudoxus_uminus_cong map_fun_apply pos_iff_neg_uminus sgn_abs_real_neg_one_iff slope_refl slope_rep_real uminus_real_def)
    thus ?thesis using sgn_neg[OF slope_rep_real] sgn_pos[OF slope_rep_real] neg_x neg_y by simp
  qed
  ultimately show ?thesis using False neg_iff_nonpos_nonzero[OF slope_rep_real] zero_iff_bounded'
    by (cases "pos (rep_real x)" ; cases "pos (rep_real y)") (fastforce simp add: mult.commute)+
qed (force)

lemma sgn_uminus: "sgn (- (x :: real)) = - sgn x" by (metis (mono_tags, lifting) mult_minus1 sgn_neg_one sgn_times)

lemma sgn_plus':
  assumes "sgn x = (-1 :: real)" "sgn y = -1"
  shows "sgn (x + y) = -1"
  using assms sgn_uminus[of x] sgn_uminus[of y] sgn_uminus[of "x + y"] sgn_plus[of "- x" "- y"]
  by (simp add: equation_minus_iff)

lemma pos_dual_def: 
  assumes "slope f"
  shows "pos f = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<le> N. f n \<le> -C)"
proof-
  have "pos f = neg (f *\<^sub>e (-\<^sub>e id))" by (metis abs_real_eq_iff abs_real_times add.inverse_inverse assms eudoxus_times_commute mult_minus1_right neg_one_def sgn_abs_real_neg_one_iff sgn_abs_real_one_iff sgn_uminus slope_neg_one)
  also have "... = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<ge> N. (f (- n)) \<le> -C)" unfolding neg_def eudoxus_times_def eudoxus_uminus_def by simp
  also have "... = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<le> N. f n \<le> -C)" by (metis add.inverse_inverse minus_le_iff)
  finally show ?thesis .
qed

lemma neg_dual_def:
  assumes "slope f"
  shows "neg f = (\<forall>C \<ge> 0. \<exists>N. \<forall>n \<le> N. f n \<ge> C)"
  unfolding neg_iff_pos_uminus using assms by (subst pos_dual_def) (auto simp add: eudoxus_uminus_def)

lemma pos_representative:
  assumes "slope f" "pos f"
  obtains g where "f \<sim>\<^sub>e g" "\<And>n. n \<ge> N \<Longrightarrow> g n \<ge> C"
proof -
  obtain N' where N': "\<forall>z\<ge>N'. f z \<ge> max 0 C" using assms unfolding pos_def by (meson max.cobounded1)
  have *: "1 = abs_real (\<lambda>x. x + N' - N)" "slope (\<lambda>x. x + N' - N)" unfolding one_def by (intro abs_real_eqI) (auto simp add: eudoxus_rel_def slope_def intro!: boundedI)
  hence "abs_real f * 1 = abs_real (f *\<^sub>e (\<lambda>x. x + N' - N))" using abs_real_times[OF assms(1) *(2)] by simp
  hence "f \<sim>\<^sub>e (f *\<^sub>e (\<lambda>x. x + N' - N))" using assms * by (metis abs_real_eq_iff eudoxus_times_commute mult.right_neutral)
  moreover have "\<forall>z\<ge>N. (f *\<^sub>e (\<lambda>x. x + N' - N)) z \<ge> C" unfolding eudoxus_times_def using N' by simp
  ultimately show ?thesis using that by blast
qed

lemma pos_representative':
  assumes "slope f" "pos f"
  obtains g where "f \<sim>\<^sub>e g" "\<And>n. g n \<ge> C \<Longrightarrow> n \<ge> N"
proof -
  obtain N' where  "\<forall>z \<le> N'. f z \<le> - (max 0 (- C) + 1)" using assms unfolding pos_dual_def[OF assms(1)] by (metis max.cobounded1 add_increasing2 zero_less_one_class.zero_le_one)
  hence N': "\<forall>z \<le> N'. f z < min 0 C" by fastforce
  have *: "1 = abs_real (\<lambda>x. x + N' - N)" "slope (\<lambda>x. x + N' - N)" unfolding one_def by (intro abs_real_eqI) (auto simp add: eudoxus_rel_def slope_def intro!: boundedI)
  hence "abs_real f * 1 = abs_real (f *\<^sub>e (\<lambda>x. x + N' - N))" using abs_real_times[OF assms(1) *(2)] by simp
  hence "f \<sim>\<^sub>e (f *\<^sub>e (\<lambda>x. x + N' - N))" using assms * by (metis abs_real_eq_iff eudoxus_times_commute mult.right_neutral)
  moreover have "\<forall>z<N. (f *\<^sub>e (\<lambda>x. x + N' - N)) z < C" unfolding eudoxus_times_def using N' by simp
  ultimately show ?thesis using that by (meson linorder_not_less)
qed

lemma neg_representative:
  assumes "slope f" "neg f"
  obtains g where "f \<sim>\<^sub>e g" "\<And>n. n \<ge> N \<Longrightarrow> g n \<le> - C"
proof -
  obtain N' where "\<forall>z\<ge>N'. f z \<le> - max 0 C" using assms unfolding neg_def by (meson max.cobounded1)
  hence N': "\<forall>z\<ge>N'. f z \<le> min 0 (- C)" by force
  have *: "1 = abs_real (\<lambda>x. x + N' - N)" "slope (\<lambda>x. x + N' - N)" unfolding one_def by (intro abs_real_eqI) (auto simp add: eudoxus_rel_def slope_def intro!: boundedI)
  hence "abs_real f * 1 = abs_real (f *\<^sub>e (\<lambda>x. x + N' - N))" using abs_real_times[OF assms(1) *(2)] by simp
  hence "f \<sim>\<^sub>e (f *\<^sub>e (\<lambda>x. x + N' - N))" using assms * by (metis abs_real_eq_iff eudoxus_times_commute mult.right_neutral)
  moreover have "\<forall>z\<ge>N. (f *\<^sub>e (\<lambda>x. x + N' - N)) z \<le> - C" unfolding eudoxus_times_def using N' by simp
  ultimately show ?thesis using that by blast
qed

lemma neg_representative':
  assumes "slope f" "neg f"
  obtains g where "f \<sim>\<^sub>e g" "\<And>n. g n \<le> - C \<Longrightarrow> n \<ge> N"
proof -
  obtain N' where "\<forall>z \<le> N'. f z \<ge> max 0 (- C) + 1" using assms unfolding neg_dual_def[OF assms(1)] by (metis max.cobounded1 add_increasing2 zero_less_one_class.zero_le_one)
  hence N': "\<forall>z \<le> N'. f z > max 0 (- C)" by fastforce
  have *: "1 = abs_real (\<lambda>x. x + N' - N)" "slope (\<lambda>x. x + N' - N)" unfolding one_def by (intro abs_real_eqI) (auto simp add: eudoxus_rel_def slope_def intro!: boundedI)
  hence "abs_real f * 1 = abs_real (f *\<^sub>e (\<lambda>x. x + N' - N))" using abs_real_times[OF assms(1) *(2)] by simp
  hence "f \<sim>\<^sub>e (f *\<^sub>e (\<lambda>x. x + N' - N))" using assms * by (metis abs_real_eq_iff eudoxus_times_commute mult.right_neutral)
  moreover have "\<forall>z < N. (f *\<^sub>e (\<lambda>x. x + N' - N)) z > - C" unfolding eudoxus_times_def using N' by simp
  ultimately show ?thesis using that by (meson linorder_not_less)
qed
                   
text \<open>We call a real \<^term>\<open>x\<close> less than another real \<^term>\<open>y\<close>, if their difference is positive.\<close>
definition
  "x < (y::real) \<equiv> sgn (y - x) = 1"

definition
  "x \<le> (y::real) \<equiv> x < y \<or> x = y"

definition
  abs_real: "\<bar>x :: real\<bar> = (if 0 \<le> x then x else - x)"

instance ..
end

instance real :: linorder
proof
  fix x y z :: real
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eq_real_def less_real_def using sgn_times[of "-1" "x - y"] by fastforce
  show "x \<le> x" unfolding less_eq_real_def by blast
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z" unfolding less_eq_real_def less_real_def using sgn_plus by fastforce
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y" unfolding less_eq_real_def less_real_def using sgn_times[of "-1" "x - y"] by fastforce
  show "x \<le> y \<or> y \<le> x" unfolding less_eq_real_def less_real_def using sgn_times[of "-1" "x - y"] sgn_range by force
qed


lemma real_leI:
  assumes "sgn (y - x) \<in> {0 :: real, 1}"
  shows "x \<le> y"
  using assms unfolding less_eq_real_def less_real_def by force

lemma real_lessI:
  assumes "sgn (y - x) = (1 :: real)"
  shows "x < y"
  using assms unfolding less_real_def by blast

lemma abs_real_leI:
  assumes "slope f" "slope g" "\<And>z. z \<ge> N \<Longrightarrow> f z \<ge> g z"
  shows "abs_real f \<ge> abs_real g"
proof -
  {
    assume "abs_real f \<noteq> abs_real g"
    hence "abs_real (f +\<^sub>e -\<^sub>e g) \<noteq> 0" by (metis abs_real_minus assms(1,2) eq_iff_diff_eq_0)
    hence "\<not> bounded (f +\<^sub>e -\<^sub>e g)" by (metis abs_real_eqI zero_def zero_iff_bounded)
    hence "pos (f +\<^sub>e -\<^sub>e g) \<or> neg (f +\<^sub>e -\<^sub>e g)" using assms eudoxus_plus_cong eudoxus_uminus_cong neg_iff_nonpos_nonzero slope_refl by auto
    moreover
    {
      assume "neg (f +\<^sub>e -\<^sub>e g)"
      then obtain N' where "(f +\<^sub>e -\<^sub>e g) z \<le> - 1" if "z \<ge> N'" for z unfolding neg_def by fastforce
      hence "f z < g z" if "z \<ge> N'" for z using that unfolding eudoxus_plus_def eudoxus_uminus_def by fastforce
      hence False using assms by (metis linorder_not_less nle_le)      
    }
    ultimately have "abs_real f > abs_real g" using assms by (fastforce intro: real_lessI sgn_pos simp add: eudoxus_plus_def eudoxus_uminus_def)
  }
  thus ?thesis unfolding less_eq_real_def by argo
qed

lemma abs_real_lessI:
  assumes "slope f" "slope g" "\<And>z. z \<ge> N \<Longrightarrow> f z \<ge> g z" "\<And>C. C \<ge> 0 \<Longrightarrow> \<exists>z. f z \<ge> g z + C"
  shows "abs_real f > abs_real g"
proof -
  {
    assume "bounded (f +\<^sub>e -\<^sub>e g)"
    then obtain C where "\<bar>f z - g z\<bar> \<le> C" "C \<ge> 0" for z unfolding eudoxus_plus_def eudoxus_uminus_def by auto
    moreover obtain z where "f z \<ge> g z + (C + 1)" using assms(4)[of "C + 1"] calculation by auto
    ultimately have False by (metis abs_le_D1 add.commute dual_order.trans le_diff_eq linorder_not_less zless_add1_eq)
  }
  moreover have "abs_real f \<ge> abs_real g" using assms abs_real_leI by blast
  ultimately show ?thesis by (metis abs_real_minus assms(1,2) eq_iff_diff_eq_0 eudoxus_plus_cong eudoxus_sgn_iff(1) eudoxus_uminus_cong order_le_imp_less_or_eq sgn_abs_real_zero_iff sgn_zero slope_refl)
qed

lemma abs_real_lessD:
  assumes "slope f" "slope g" "abs_real f > abs_real g"
  obtains z where "z \<ge> N" "f z > g z"
proof -
  {
    assume "\<exists>N. \<forall>z\<ge>N. f z \<le> g z"
    then obtain N where "f z \<le> g z" if "z \<ge> N" for z by fastforce
    hence False using assms abs_real_leI by (metis linorder_not_le)
  }
  thus ?thesis using that by fastforce
qed

subsection \<open>Multiplicative Inverse\<close>

text \<open>We now define the multiplicative inverse. We start by constructing a candidate for positive slopes first and then extend it to the entire domain using the choice function \<^term>\<open>Eps\<close>.\<close>
instantiation real :: "{inverse}"
begin

definition eudoxus_pos_inverse :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where
  "eudoxus_pos_inverse f z = sgn z * Inf ({0..} \<inter> {n. f n \<ge> \<bar>z\<bar>})"

lemma eudoxus_pos_inverse:
  assumes "slope f" "pos f"
  obtains g where "f \<sim>\<^sub>e g" "slope (eudoxus_pos_inverse g)" "eudoxus_pos_inverse g *\<^sub>e f \<sim>\<^sub>e id" 
proof -
  let ?\<phi> = eudoxus_pos_inverse
  obtain g where g: "f \<sim>\<^sub>e g" "g z \<ge> 0 \<Longrightarrow> z > 1" for z using pos_representative'[OF assms] by (metis gt_ex order_less_le_trans)
  hence pos_g: "pos g" using assms pos_cong by blast
  have slope_g: "slope g" using g unfolding eudoxus_rel_def by simp

  have "\<exists>n \<ge> 0. g n \<ge> \<bar>z\<bar>" for z using pos_g unfolding pos_def by (metis abs_ge_self order_less_imp_le zero_less_abs_iff)
  hence nonempty_\<phi>: "{0..} \<inter> {n. \<bar>z\<bar> \<le> g n} \<noteq> {}" for z by blast
  have bdd_below_\<phi>: "bdd_below ({0..} \<inter> {n. g n \<ge> \<bar>z\<bar>})" for z by simp
  have \<phi>_bound: "g n \<ge> z \<Longrightarrow> ?\<phi> g z \<le> n" if "z \<ge> 0" "n \<ge> 0" for n z unfolding eudoxus_pos_inverse_def using cInf_lower[OF _ bdd_below_\<phi>, of n z] that abs_of_nonneg zsgn_def by simp
  hence \<phi>_bound': "?\<phi> g z > n \<Longrightarrow> g n < z" if "z \<ge> 0" "n \<ge> 0" for z n using that linorder_not_less by blast

  have \<phi>_mem: "z > 0 \<Longrightarrow> ?\<phi> g z \<in> {0..} \<inter> {n. g n \<ge> \<bar>z\<bar>}" for z unfolding eudoxus_pos_inverse_def using int_Inf_mem[OF nonempty_\<phi> bdd_below_\<phi>, of z] by simp

  obtain L where "\<bar>g (1 + (z - 1)) - (g 1 + g (z - 1))\<bar> \<le> L" for z using slope_g by fast
  hence *: "\<bar>g z - (g 1 + g (z - 1))\<bar> \<le> L" for z by simp
  hence L: "g z \<le> g (z - 1) + (L + g 1)" for z using abs_le_D1 *[of z] by linarith

  let ?\<gamma> = "\<lambda>m n. (g (m + (- n)) - (g m + g (- n))) - (g (n + (- n)) - (g n + g (- n))) + g 0"
  
  obtain c where c: "\<bar>g (m + (- n)) - (g m + g (- n))\<bar> \<le> c" for m n using slope_g by fast
  obtain c' where c': "\<bar>g (n + (- n)) - (g n + g (- n))\<bar> \<le> c'" for n using slope_g by fast
  have "\<bar>?\<gamma> m n\<bar> \<le> \<bar>g (m + (- n)) - (g m + g (- n))\<bar> + \<bar>g (n + (- n)) - (g n + g (- n))\<bar> + \<bar>g 0\<bar>" for m n by linarith
  hence *: "\<bar>?\<gamma> m n\<bar> \<le> c + c' + \<bar>g 0\<bar>" for m n using c[of m n] c'[of n] by linarith

  define C where "C = 2 * (c + c' + \<bar>g 0\<bar>)"
  have "g (m - (n + p)) - (g m - (g n + g p)) = ?\<gamma> (m - n) p + ?\<gamma> m n" for m n p by (simp add: algebra_simps)
  hence "\<bar>g (m - (n + p)) - (g m - (g n + g p))\<bar> \<le> (c + c' + \<bar>g 0\<bar>) + (c + c' + \<bar>g 0\<bar>)" for m n p using *[of "m - n" p] *[of m n] by simp
  hence *: "\<bar>g (m - (n + p)) - (g m - (g n + g p))\<bar> \<le> C" for m n p unfolding C_def by (metis mult_2)
  have C: "g (m - (n + p)) \<le> g m - (g n + g p) + C" "g m - (g n + g p) + (- C) \<le> g (m - (n + p))" for m n p using *[of m n p] abs_le_D1 abs_le_D2 by linarith+

  have bounded: "bounded h" if bounded: "bounded (g o h)" for h :: "'a \<Rightarrow> int"
  proof (rule ccontr)
    assume asm: "\<not> bounded h"
    obtain C where C: "\<bar>g (h z)\<bar> \<le> C" "C \<ge> 0" for z using bounded by fastforce
    obtain N where N: "g z \<ge> C + 1" if "z \<ge> N" for z using C pos_g unfolding pos_def by fastforce
    obtain N' where N': "g z \<le> - (C + 1)" if "z \<le> N'" for z using C pos_g unfolding pos_dual_def[OF slope_g] by (meson add_increasing2 linordered_nonzero_semiring_class.zero_le_one)
    obtain z where "\<bar>h z\<bar> > max \<bar>N\<bar> \<bar>N'\<bar>" using asm unfolding bounded_alt_def by (meson leI)
    hence "h z \<in> {..N'} \<union> {N..}" by fastforce
    hence "g (h z) \<in> {..- (C + 1)} \<union> {C + 1..}" using N N' by blast
    hence "\<bar>g (h z)\<bar> \<ge> C + 1" by fastforce
    thus False using C(1)[of z] by simp
  qed

  define D where "D = max \<bar>- (C + (L + g 1) + (L + g 1))\<bar> \<bar>C + L + g 1\<bar>"
  {
    fix m n :: int
    assume asm: "m > 0" "n > 0"

    have "g (?\<phi> g m) \<ge> m" using \<phi>_mem asm by simp
    moreover have "?\<phi> g m > 1" using calculation g asm by simp
    moreover have "m > g (?\<phi> g m - 1)" using asm calculation by (intro \<phi>_bound') auto
    ultimately have m: "m \<in> {g (?\<phi> g m - 1)<..g (?\<phi> g m)}" by simp

    have "g (?\<phi> g n) \<ge> n" using \<phi>_mem asm by simp
    moreover have "?\<phi> g n > 1" using calculation g asm by simp
    moreover have "n > g (?\<phi> g n - 1)" using asm calculation by (intro \<phi>_bound') auto
    ultimately have n: "n \<in> {g (?\<phi> g n - 1)<..g (?\<phi> g n)}" by simp

    have "g (?\<phi> g (m + n)) \<ge> m + n" using \<phi>_mem asm by simp
    moreover have "?\<phi> g (m + n) > 1" using calculation g asm by simp
    moreover have "(m + n) > g (?\<phi> g (m + n) - 1)" using asm calculation by (intro \<phi>_bound') auto
    ultimately have m_n: "m + n \<in> {g (?\<phi> g (m + n) - 1)<..g (?\<phi> g (m + n))}" by simp

    have *: "g (?\<phi> g (m + n)) - (g (?\<phi> g m - 1) + g (?\<phi> g n - 1)) > 0" "g (?\<phi> g (m + n) - 1) - (g (?\<phi> g m) + g (?\<phi> g n)) < 0" using m_n m n by simp+
    
    have "g (?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)) \<le> g (?\<phi> g (m + n)) - (g (?\<phi> g m) + g (?\<phi> g n)) + C" using C by blast
    also have "... \<le> g (?\<phi> g (m + n) - 1) - g (?\<phi> g m) - g (?\<phi> g n) + (C + L + g 1)" using L by fastforce
    finally have upper: "g (?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)) \<le> C + L + g 1" using * by fastforce

    have "- (C + (L + g 1) + (L + g 1)) \<le> g (?\<phi> g (m + n)) - g (?\<phi> g m - 1) - g (?\<phi> g n - 1) - (C + (L + g 1) + (L + g 1))" using * by linarith
    also have "... \<le> g (?\<phi> g (m + n)) - (g (?\<phi> g m) + g (?\<phi> g n)) + (- C)" using L[THEN le_imp_neg_le, of "?\<phi> g m"] L[THEN le_imp_neg_le, of "?\<phi> g n"] by linarith
    also have "... \<le> g (?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n))" using C by blast
    finally have lower: "- (C + (L + g 1) + (L + g 1)) \<le> g (?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n))" .

    have "\<bar>g (?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n))\<bar> \<le> D" using upper lower unfolding D_def by simp
  }
  hence "bounded (g o (\<lambda>(m, n). ?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)) o (\<lambda>(m, n). (max 1 m, max 1 n)))" by (intro boundedI[of _ D]) auto
  hence "bounded ((\<lambda>(m, n). ?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)) o (\<lambda>(m, n). (max 1 m, max 1 n)))" by (metis (mono_tags, lifting) bounded comp_assoc)
  then obtain C where "\<bar>((\<lambda>(m, n). ?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)) o (\<lambda>(m, n). (max 1 m, max 1 n))) (m, n)\<bar> \<le> C" for m n by blast
  hence "\<bar>?\<phi> g (m + n) - (?\<phi> g m + ?\<phi> g n)\<bar> \<le> C" if "m \<ge> 1" "n \<ge> 1" for m n using that[THEN max_absorb2] by (metis (no_types, lifting) comp_apply prod.case)
  hence slope: "slope (?\<phi> g)" by (intro slope_odd[of _ C]) (auto simp add: eudoxus_pos_inverse_def)
  moreover 
  {
    obtain C where C: "\<bar>g ((?\<phi> g n - 1) + 1) - (g (?\<phi> g n - 1) + g 1)\<bar> \<le> C" for n using slope_g by fast
    have C_bound: "g (?\<phi> g n - 1) \<ge> g (?\<phi> g n) - (\<bar>g 1\<bar> + C)" for n using C[of n] by fastforce
    {
      fix n :: int
      assume asm: "n > 0"
      have upper: "g (?\<phi> g n) \<ge> n" using \<phi>_mem asm by simp
      moreover have "?\<phi> g n > 1" using calculation g asm by simp
      moreover have "n > g (?\<phi> g n - 1)" using calculation asm by (intro \<phi>_bound') auto
      moreover have "n \<ge> g (?\<phi> g n) - (\<bar>g 1\<bar> + C)" using calculation C_bound[of n] by force
      ultimately have "\<bar>g (?\<phi> g n) - n\<bar> \<le> \<bar>g 1\<bar> + C" by simp
    }
    hence id: "g *\<^sub>e ?\<phi> g \<sim>\<^sub>e id" using slope_g slope by (intro eudoxus_relI[of _ _ 1 "\<bar>g 1\<bar> + C"]) (auto simp add: eudoxus_times_def)
  }
  ultimately show ?thesis using g that eudoxus_rel_trans eudoxus_times_cong slope_reflI eudoxus_times_commute[OF slope slope_g] by metis
qed  

definition eudoxus_inverse :: "(int \<Rightarrow> int) \<Rightarrow> (int \<Rightarrow> int)" where
  "eudoxus_inverse f = (if \<not> bounded f then SOME g. slope g \<and> (g *\<^sub>e f) \<sim>\<^sub>e id else (\<lambda>_. 0))"

lemma 
  assumes "slope f"
  shows slope_eudoxus_inverse: "slope (eudoxus_inverse f)" (is "?slope") and
        eudoxus_inverse_id: "\<not> bounded f \<Longrightarrow> eudoxus_inverse f *\<^sub>e f \<sim>\<^sub>e id" (is "\<not> bounded f \<Longrightarrow> ?id")
proof -
  have *: "\<lbrakk>slope g; (g *\<^sub>e f) \<sim>\<^sub>e id\<rbrakk> \<Longrightarrow> ?slope" "\<lbrakk>slope g; (g *\<^sub>e f) \<sim>\<^sub>e id; \<not> bounded f\<rbrakk> \<Longrightarrow> ?id" for g 
    unfolding eudoxus_inverse_def using someI[where ?P="\<lambda>g. slope g \<and> (g *\<^sub>e f) \<sim>\<^sub>e id"] by auto
  {
    assume pos: "pos f"
    then obtain g where "slope (eudoxus_pos_inverse g)" "eudoxus_pos_inverse g *\<^sub>e f \<sim>\<^sub>e id" using eudoxus_pos_inverse[OF assms] by blast
    hence ?slope "\<not> bounded f \<Longrightarrow> ?id" using pos pos_iff_nonneg_nonzero[OF assms] * by blast+
  }
  moreover
  {
    assume nonpos: "\<not> pos f"
    {
      assume nonzero: "\<not> bounded f"
      hence uminus_f: "slope (-\<^sub>e f)" "pos (-\<^sub>e f)" using neg_iff_pos_uminus neg_iff_nonpos_nonzero assms slope_refl nonpos by auto
      then obtain g where g: "slope (eudoxus_pos_inverse g)" "eudoxus_pos_inverse g *\<^sub>e (-\<^sub>e f) \<sim>\<^sub>e id" using eudoxus_pos_inverse by metis
      hence "-\<^sub>e (eudoxus_pos_inverse g) *\<^sub>e f \<sim>\<^sub>e id" by (metis (full_types) uminus_f(1) abs_real_eq_iff abs_real_times abs_real_uminus assms(1) eudoxus_times_commute minus_mult_commute rel_funE uminus_real.rsp)
      moreover have "slope (-\<^sub>e (eudoxus_pos_inverse g))" using uminus_f eudoxus_uminus_cong slope_refl g by presburger
      ultimately have ?slope ?id using * nonzero by blast+
    }
    moreover have "bounded f \<Longrightarrow> ?slope" unfolding eudoxus_inverse_def by simp
    ultimately have ?slope "\<not> bounded f \<Longrightarrow> ?id" by blast+
  }
  ultimately show ?slope "\<not> bounded f \<Longrightarrow> ?id" by blast+
qed

quotient_definition
  "(inverse :: real \<Rightarrow> real)" is eudoxus_inverse
proof -
  fix x x' assume asm: "x \<sim>\<^sub>e x'"
  hence slopes: "slope x" "slope x'" unfolding eudoxus_rel_def by blast+
  show "eudoxus_inverse x \<sim>\<^sub>e eudoxus_inverse x'"
  proof (cases "bounded x")
    case True
    hence "bounded x'" by (meson asm eudoxus_rel_sym eudoxus_rel_trans zero_iff_bounded)
    then show ?thesis unfolding eudoxus_inverse_def using True slope_zero slope_refl by auto
  next
    case False
    hence "\<not> bounded x'" by (meson asm eudoxus_rel_sym eudoxus_rel_trans zero_iff_bounded)
    hence inverses: "eudoxus_inverse x *\<^sub>e x \<sim>\<^sub>e id" "eudoxus_inverse x' *\<^sub>e x' \<sim>\<^sub>e id" using slopes eudoxus_inverse_id False by blast+

    have alt_inverse: "eudoxus_inverse x *\<^sub>e x' \<sim>\<^sub>e id" 
      using inverses eudoxus_times_cong[OF slope_reflI, OF slope_eudoxus_inverse asm, OF slopes(1)]
            eudoxus_rel_sym eudoxus_rel_trans by blast

    have "eudoxus_inverse x \<sim>\<^sub>e eudoxus_inverse x *\<^sub>e (eudoxus_inverse x' *\<^sub>e x')" 
      using eudoxus_times_cong[OF slope_reflI, OF slope_eudoxus_inverse inverses(2)[THEN eudoxus_rel_sym], OF slopes(1)]
      by (simp add: eudoxus_times_def)
    also have "... \<sim>\<^sub>e eudoxus_inverse x' *\<^sub>e (eudoxus_inverse x *\<^sub>e x')"
      using eudoxus_times_commute[OF slope_eudoxus_inverse(1,1), OF slopes, THEN eudoxus_times_cong, OF slope_reflI, OF slopes(2)] 
      by (simp add: eudoxus_times_def comp_assoc)      
    also have "... \<sim>\<^sub>e eudoxus_inverse x' *\<^sub>e id" using alt_inverse eudoxus_times_cong[OF slope_reflI] slope_eudoxus_inverse slopes by blast
    also have "... = eudoxus_inverse x'" unfolding eudoxus_times_def by simp
    finally show ?thesis .
  qed
qed

definition 
  "x div (y::real) = inverse y * x"

instance ..
end

lemmas eudoxus_inverse_cong = apply_rsp'[OF inverse_real.rsp, intro]

lemma eudoxus_inverse_abs[simp]:
  assumes "slope f" "\<not> bounded f"
  shows "inverse (abs_real f) * abs_real f = 1"
  unfolding inverse_real_def using eudoxus_inverse_id[OF assms]
  by (metis abs_real_eqI abs_real_times assms(1) eudoxus_inverse_cong map_fun_apply one_def rep_real_abs_real_refl slope_refl)

text \<open>The Eudoxus reals are a field, with inverses defined as above.\<close>
instance real :: field
proof
  fix x y :: real
  show "x \<noteq> 0 \<Longrightarrow> inverse x * x = 1" using eudoxus_sgn_iff(1) sgn_abs_real_zero_iff by (induct x rule: slope_induct) force
  show "x / y = x * inverse y" unfolding divide_real_def by simp
  show "inverse (0 :: real) = 0" unfolding inverse_real_def eudoxus_inverse_def using zero_def zero_iff_bounded' by auto 
qed

instantiation real :: distrib_lattice
begin

definition
  "(inf :: real \<Rightarrow> real \<Rightarrow> real) = min"
                                   
definition
  "(sup :: real \<Rightarrow> real \<Rightarrow> real) = max"

instance by standard (auto simp: inf_real_def sup_real_def max_min_distrib2)

end

text \<open>The ordering on the Eudoxus reals is linear.\<close>
instance real :: linordered_field
proof
  fix x y z :: real
  show "z + x \<le> z + y" if "x \<le> y"
  proof (cases "x = y")
    case False
    hence "x < y" using that by simp
    thus ?thesis
    proof (induct x rule: slope_induct, induct y rule: slope_induct, induct z rule: slope_induct)
      case (slope h g f)
      hence "pos (g +\<^sub>e (-\<^sub>e f))" unfolding less_real_def using sgn_abs_real_one_iff by (force simp add: eudoxus_plus_def eudoxus_uminus_def) 
      thus ?case by (metis slope(4) less_real_def add_diff_cancel_left nless_le)
    qed
  qed (force)

  show "\<bar>x\<bar> = (if x < 0 then -x else x)" by (metis abs_real less_eq_real_def not_less_iff_gr_or_eq)
  show "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)" using sgn_range sgn_zero_iff by (auto simp: less_real_def)
  show "\<lbrakk>x < y; 0 < z\<rbrakk> \<Longrightarrow> z * x < z * y" by (metis (no_types, lifting) diff_zero less_real_def mult.right_neutral right_diff_distrib' sgn_times)
qed

text \<open>The Eudoxus reals fulfill the Archimedean property.\<close>
instance real :: archimedean_field
proof                         
  fix x :: real
  show "\<exists>z. x \<le> of_int z"
  proof (induct x rule: slope_induct)
    case (slope y)
    then obtain A B where linear_bound: "\<bar>y z\<bar> \<le> A * \<bar>z\<bar> + B" "0 \<le> A" "0 \<le> B" for z using slope_linear_bound by blast
    {
      fix C assume C_nonneg: "0 \<le> (C :: int)"
      {
        fix z assume asm: "z \<ge> B + C"
        have "y z + C \<le> A * \<bar>z\<bar> + B + C" using abs_le_D1 linear_bound by auto
        also have "... \<le> (A + 1) * \<bar>z\<bar>" using C_nonneg linear_bound(2,3) asm by (auto simp: distrib_right)
        finally have "y z + C \<le> (A + 1) * z" using add_nonneg_nonneg[OF C_nonneg linear_bound(3)] abs_of_nonneg[of z] asm by linarith
      }
      hence "\<exists>N. \<forall>x \<ge> N. (((*) (A + 1)) +\<^sub>e -\<^sub>e y) x \<ge> C" unfolding eudoxus_plus_def eudoxus_uminus_def by fastforce
    }
    hence "pos (((*) (A + 1)) +\<^sub>e -\<^sub>e y)" unfolding pos_def by blast
    hence "pos (rep_real (of_int (A + 1) - abs_real y))" unfolding real_of_int using slope by (simp, subst pos_cong[OF rep_real_abs_real_refl]) (auto simp add: eudoxus_plus_def eudoxus_uminus_def)
    hence "abs_real y < of_int (A + 1)" unfolding less_real_def by (metis sgn_pos rep_real_abs_real_refl rep_real_iff slope_rep_real)
    thus ?case unfolding less_eq_real_def by blast
  qed
qed

subsection \<open>Completeness\<close>

text \<open>To show that the Eudoxus reals are complete, we first introduce the floor function.\<close>
instantiation real :: floor_ceiling
begin

definition 
  "(floor :: (real \<Rightarrow> int)) = (\<lambda>x. (SOME z. of_int z \<le> x \<and> x < of_int z + 1))"

instance
proof
  fix x :: real
  show "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)" using someI[of "\<lambda>z. of_int z \<le> x \<and> x < of_int z + 1"] floor_exists by (fastforce simp add: floor_real_def)
qed
end

lemma eudoxus_dense_rational:
  fixes x y :: real
  assumes "x < y"
  obtains m n where "x < (of_int m / of_int n)" "(of_int m / of_int n) < y" "n > 0"
proof -
  obtain n :: int where n: "inverse (y - x) < of_int n" "n > 0" by (metis ex_less_of_int antisym_conv3 dual_order.strict_trans of_int_less_iff)
  hence *: "inverse (of_int n) < y - x" by (metis assms diff_gt_0_iff_gt inverse_inverse_eq inverse_less_iff_less inverse_positive_iff_positive of_int_0_less_iff)
  define m where "m = floor (x * of_int n) + 1"
  {
    assume "y \<le> of_int m / of_int n"
    hence "inverse (of_int n) < of_int m / of_int n - x" using * by linarith
    hence "x < (of_int m - 1) / of_int n" by (simp add: diff_divide_distrib inverse_eq_divide)
    hence False unfolding m_def using n(2) divide_le_eq linorder_not_less by fastforce
  }
  moreover have "x < of_int m / of_int n" unfolding m_def by (meson n(2) floor_correct mult_imp_less_div_pos of_int_pos)
  ultimately show ?thesis using that n by fastforce
qed
         
text \<open>The Eudoxus reals are a complete field.\<close>
lemma eudoxus_complete:
  assumes "S \<noteq> {}" "bdd_above S"
  obtains u :: real where "\<And>s. s \<in> S \<Longrightarrow> s \<le> u" "\<And>y. (\<And>s. s \<in> S \<Longrightarrow> s \<le> y) \<Longrightarrow> u \<le> y"
proof (cases "\<exists>u \<in> S. \<forall>s \<in> S. s \<le> u")
  case False
  hence no_greatest_element: "\<exists>y \<in> S. x < y" if "x \<in> S" for x using that by force
  define u :: "int \<Rightarrow> int" where "u = (\<lambda>z. sgn z * Sup ((\<lambda>x. \<lfloor>of_int \<bar>z\<bar> * x\<rfloor>) ` S))"
  
  have bdd_above_u: "bdd_above ((\<lambda>x. \<lfloor>of_int \<bar>z\<bar> * x\<rfloor>) ` S)" for z by (intro bdd_above_image_mono[OF _ assms(2)] monoI) (simp add: floor_mono mult.commute mult_right_mono)
  
  have u_Sup_nonneg: "z \<ge> 0 \<Longrightarrow> \<lfloor>of_int z * s\<rfloor> \<le> u z" and 
       u_Sup_nonpos: "z \<le> 0 \<Longrightarrow> - \<lfloor>of_int (- z) * s\<rfloor> \<ge> u z" if "s \<in> S" for s z 
    unfolding u_def using cSup_upper[OF _ bdd_above_u, of "\<lfloor>of_int \<bar>z\<bar> * s\<rfloor>" z] that abs_of_nonpos zsgn_def by force+

  have u_mem: "u z \<in> (\<lambda>x. sgn z * \<lfloor>of_int \<bar>z\<bar> * x\<rfloor>) ` S" for z unfolding u_def  using int_Sup_mem[OF _ bdd_above_u, of z] assms by auto

  have slope: "slope u"
  proof -
    {
      fix m n :: int assume asm: "m > 0" "n > 0"
      obtain x_m where x_m: "x_m \<in> S" "u m = \<lfloor>of_int m * x_m\<rfloor>" using u_mem[of m] asm zsgn_def by auto
      obtain x_n where x_n: "x_n \<in> S" "u n = \<lfloor>of_int n * x_n\<rfloor>" using u_mem[of n] asm zsgn_def by auto
      obtain x_m_n where x_m_n: "x_m_n \<in> S" "u (m + n) = \<lfloor>of_int (m + n) * x_m_n\<rfloor>" using u_mem[of "m + n"] asm zsgn_def by auto

      define x where "x = max (max x_m x_n) x_m_n"
      have x: "x \<in> S" unfolding x_def using x_m x_n x_m_n by linarith

      have "x \<ge> x_m" "x \<ge> x_n" "x \<ge> x_m_n" unfolding x_def by linarith+
      hence "u m \<le> \<lfloor>of_int m * x\<rfloor>" "u n \<le> \<lfloor>of_int n * x\<rfloor>" "u (m + n) \<le> \<lfloor>of_int (m + n) * x\<rfloor>" 
        unfolding x_m x_n x_m_n by (meson asm floor_less_cancel linorder_not_less mult_le_cancel_iff2 of_int_0_less_iff add_pos_pos)+       
      hence "u m = \<lfloor>of_int m * x\<rfloor>" "u n = \<lfloor>of_int n * x\<rfloor>" "u (m + n) = \<lfloor>of_int m * x + of_int n * x\<rfloor>" 
        using u_Sup_nonneg[OF x(1), of m] u_Sup_nonneg[OF x(1), of n] u_Sup_nonneg[OF x(1), of "m + n"] asm add_pos_pos[OF asm] by (force simp add: distrib_right)+
      moreover 
      {
        fix a b :: real
        have "a - of_int \<lfloor>a\<rfloor> \<in> {0..<1}" using floor_less_one by fastforce
        moreover have "b - of_int \<lfloor>b\<rfloor> \<in> {0..<1}" using floor_less_one by fastforce
        ultimately have "(a - of_int \<lfloor>a\<rfloor>) + (b - of_int \<lfloor>b\<rfloor>) \<in> {0..<2}" unfolding atLeastLessThan_def by simp
        hence "(a + b) - (of_int \<lfloor>a\<rfloor> + of_int \<lfloor>b\<rfloor>) \<in> {0..<2}" by (simp add: diff_add_eq)
        hence "\<lfloor>a + b - (of_int \<lfloor>a\<rfloor> + of_int \<lfloor>b\<rfloor>)\<rfloor> \<in> {0..<2}" by simp
        hence "\<lfloor>a + b\<rfloor> - (\<lfloor>a\<rfloor> + \<lfloor>b\<rfloor>) \<in> {0..<2}" by (metis floor_diff_of_int of_int_add)
      }
      ultimately have "\<bar>u (m + n) - (u m + u n)\<bar> \<le> 2" by (metis abs_of_nonneg atLeastLessThan_iff nless_le)
    }
    moreover have "u z = - u (- z)" for z unfolding u_def by simp
    ultimately show ?thesis using slope_odd by blast
  qed
  {
    fix s assume "s \<in> S"
    then obtain y where y: "s < y" "y \<in> S" using no_greatest_element by blast
    then obtain m n :: int where *: "s < (of_int m / of_int n)" "(of_int m / of_int n) < y" "n > 0" using eudoxus_dense_rational by blast
    hence n_nonneg: "n \<ge> 0" by simp
    {
      fix z :: int assume z_nonneg: "z \<ge> 0"
      have "z * m = \<lfloor>of_int (z * n) * (of_int m / of_int n) :: real\<rfloor>" using *(3) by simp (auto simp only: of_int_mult[symmetric] floor_of_int)
      also have "... \<le> \<lfloor>of_int (z * n) * y\<rfloor>" using *(2) by (meson floor_mono mult_left_mono n_nonneg nless_le of_int_nonneg z_nonneg zero_le_mult_iff)
      also have "... \<le> u (z * n)" using u_Sup_nonneg[OF y(2)] mult_nonneg_nonneg[OF z_nonneg n_nonneg] by blast
      finally have "u (z * n) \<ge> z * m" .
    }
    hence "abs_real (u *\<^sub>e (*) n) \<ge> of_int m" using slope unfolding real_of_int eudoxus_times_def by (intro abs_real_leI[where ?N=0]) (auto simp add: mult.commute) 
    moreover have "abs_real u * of_int n = abs_real (u *\<^sub>e (*) n)" unfolding real_of_int using slope by (simp add: eudoxus_times_def comp_def)
    ultimately have "s \<le> abs_real u" using * by (metis leI mult_imp_div_pos_le of_int_0_less_iff order_le_less_trans order_less_asym)
  }
  moreover
  {
    fix y assume asm: "s \<le> y" if "s \<in> S" for s
    assume "abs_real u > y"
    then obtain m n :: int where *: "y < (of_int m / of_int n)" "(of_int m / of_int n) < abs_real u" "n > 0" using eudoxus_dense_rational by blast
    hence "of_int m < abs_real u * of_int n" by (simp add: pos_divide_less_eq)
    hence "of_int m < abs_real (u *\<^sub>e (*) n)" unfolding real_of_int using slope by (simp add: eudoxus_times_def comp_def)
    moreover have "slope (u *\<^sub>e (*) n)" using slope by (simp add: eudoxus_times_def)
    ultimately obtain z where z: "(u *\<^sub>e (*) n) z > m * z" "z \<ge> 1" unfolding real_of_int using abs_real_lessD by blast
    hence **: "u (n * z) > m * z" by (simp add: eudoxus_times_def comp_def)

    obtain x where x: "x \<in> S" "u (n * z) = \<lfloor>of_int (n * z) * x\<rfloor>" using u_mem[of "n * z"] zsgn_def[of "n * z"] mult_pos_pos[OF *(3), of z] z(2) by fastforce
    
    have "of_int (n * z) * x \<le> of_int z * of_int n * y" using asm[OF x(1)] using * z by auto
    also have "... < of_int z * of_int m" using * z by (simp add: mult.commute pos_less_divide_eq)
    finally have "of_int (n * z) * x < of_int (m * z)" by (simp add: mult.commute)
    hence False using ** by (metis floor_less_iff less_le_not_le x(2))
  }
  ultimately show ?thesis using that by force
qed blast

end