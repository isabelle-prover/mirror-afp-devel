section \<open>Subgroups of the modular group\<close>
theory Modular_Subgroups
  imports Modular_Group
begin

subsection \<open>Definition and group action on the upper half plane\<close>

locale modgrp_subgroup =
  fixes G :: "modgrp set"
  assumes one_in_G [simp, intro]: "1 \<in> G"
  assumes times_in_G [simp, intro]: "x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> x * y \<in> G"
  assumes inverse_in_G [simp, intro]: "x \<in> G \<Longrightarrow> inverse x \<in> G"
begin

lemma divide_in_G [intro]: "f \<in> G \<Longrightarrow> g \<in> G \<Longrightarrow> f / g \<in> G"
  unfolding divide_modgrp_def by (intro times_in_G inverse_in_G)

lemma power_in_G [intro]: "f \<in> G \<Longrightarrow> f ^ n \<in> G"
  by (induction n) auto

lemma power_int_in_G [intro]: "f \<in> G \<Longrightarrow> f powi n \<in> G"
  by (auto simp: power_int_def)

lemma prod_list_in_G [intro]: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<in> G) \<Longrightarrow> prod_list xs \<in> G"
  by (induction xs) auto

lemma inverse_in_G_iff [simp]: "inverse f \<in> G \<longleftrightarrow> f \<in> G"
  by (metis inverse_in_G modgrp.inverse_inverse)

(* TODO: lift restriction to complex numbers *)
definition rel :: "complex \<Rightarrow> complex \<Rightarrow> bool" where
  "rel x y \<longleftrightarrow> Im x > 0 \<and> Im y > 0 \<and> (\<exists>f\<in>G. apply_modgrp f x = y)"

definition orbit :: "complex \<Rightarrow> complex set" where
  "orbit x = {y. rel x y}"

lemma Im_nonpos_imp_not_rel: "Im x \<le> 0 \<or> Im y \<le> 0 \<Longrightarrow> \<not>rel x y"
  by (auto simp: rel_def)

lemma orbit_empty: "Im x \<le> 0 \<Longrightarrow> orbit x = {}"
  by (auto simp: orbit_def Im_nonpos_imp_not_rel)

lemma rel_imp_Im_pos [dest]:
  assumes "rel x y"
  shows   "Im x > 0" "Im y > 0"
  using assms by (auto simp: rel_def)

lemma rel_refl [simp]: "rel x x \<longleftrightarrow> Im x > 0"
  by (auto simp: rel_def intro!: bexI[of _ 1])

lemma rel_sym:
  assumes "rel x y"
  shows   "rel y x"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from this have "apply_modgrp (inverse f) y = x"
    using pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (intro apply_modgrp_inverse_eqI) (auto simp: complex_is_Real_iff)
  moreover have "inverse f \<in> G"
    using f by auto
  ultimately show ?thesis
    using f by (auto simp: rel_def)
qed

lemma rel_commutes: "rel x y = rel y x"
  using rel_sym by blast

lemma rel_trans [trans]:
  assumes "rel x y" "rel y z"
  shows   "rel x z"
proof -
  from assms obtain f where f: "f \<in> G" "Im x > 0" "Im y > 0" "apply_modgrp f x = y"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  from assms obtain g where g: "Im z > 0" "g \<in> G" "apply_modgrp g y = z"
    by (auto simp: rel_def intro!: bexI[of _ 1])
  have "apply_modgrp (g * f) x = z"
    using f g pole_modgrp_in_Reals[of f, where ?'a = complex]
    by (subst apply_modgrp_mult) (auto simp: complex_is_Real_iff)
  with f g show ?thesis
    unfolding rel_def by blast
qed

lemma relI1 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel x (apply_modgrp f y)"
  using modgrp.Im_transform_pos_iff rel_def rel_trans by blast

lemma relI2 [intro]: "rel x y \<Longrightarrow> f \<in> G \<Longrightarrow> Im x > 0 \<Longrightarrow> rel (apply_modgrp f x) y"
  by (meson relI1 rel_commutes rel_def)

lemma relE:
  assumes "rel x y"
  obtains h where "Im x > 0" "Im y > 0" "h \<in> G" "y = apply_modgrp h x"
  using assms by (auto simp: rel_def)

lemma relE':
  assumes "rel x y"
  obtains h where "Im x > 0" "Im y > 0" "h \<in> G" "x = apply_modgrp h y"
  using rel_sym[OF assms] by (elim relE)

lemma rel_apply_modgrp_left_iff [simp]:
  assumes "f \<in> G"
  shows   "rel (apply_modgrp f x) y \<longleftrightarrow> Im x > 0 \<and> rel x y"
proof safe
  assume "rel (apply_modgrp f x) y"
  thus "rel x y"
    by (meson assms modgrp.Im_transform_pos_iff rel_def rel_trans)
next
  assume "rel x y" "Im x > 0"
  thus "rel (apply_modgrp f x) y"
    by (meson assms relI2 rel_trans)
qed auto

lemma rel_apply_modgrp_right_iff [simp]:
  assumes "f \<in> G"
  shows   "rel y (apply_modgrp f x) \<longleftrightarrow> Im x > 0 \<and> rel y x"
  using assms by (metis rel_apply_modgrp_left_iff rel_sym)

lemma orbit_refl_iff: "x \<in> orbit x \<longleftrightarrow> Im x > 0"
  by (auto simp: orbit_def)

lemma orbit_refl: "Im x > 0 \<Longrightarrow> x \<in> orbit x"
  by (auto simp: orbit_def)

lemma orbit_cong: "rel x y \<Longrightarrow> orbit x = orbit y"
  using rel_trans rel_commutes unfolding orbit_def by blast

lemma orbit_empty_iff [simp]: "orbit x = {} \<longleftrightarrow> Im x \<le> 0" "{} = orbit x \<longleftrightarrow> Im x \<le> 0"
  using orbit_refl orbit_empty by force+

lemmas [simp] = orbit_refl_iff

lemma orbit_eq_iff: "orbit x = orbit y \<longleftrightarrow> Im x \<le> 0 \<and> Im y \<le> 0 \<or> rel x y"
proof (cases "Im y \<le> 0 \<or> Im x \<le> 0")
  case True
  thus ?thesis
    by (auto simp: orbit_empty)
next
  case False
  have "(\<forall>z. rel x z \<longleftrightarrow> rel y z) \<longleftrightarrow> rel x y"
    by (meson False not_le rel_commutes rel_refl rel_trans)
  thus ?thesis
    using False unfolding orbit_def by blast
qed 

lemma orbit_apply_modgrp [simp]: "f \<in> G \<Longrightarrow> orbit (apply_modgrp f z) = orbit z"
  by (subst orbit_eq_iff) auto  

lemma apply_modgrp_in_orbit_iff [simp]: "f \<in> G \<Longrightarrow> apply_modgrp f z \<in> orbit y \<longleftrightarrow> z \<in> orbit y"
  by (auto simp: orbit_def rel_commutes)

lemma orbit_imp_Im_pos: "x \<in> orbit y \<Longrightarrow> Im x > 0"
  by (auto simp: orbit_def)

end


interpretation modular_group: modgrp_subgroup UNIV
  by unfold_locales auto

notation modular_group.rel (infixl "\<sim>\<^sub>\<Gamma>" 49)

lemma (in modgrp_subgroup) rel_imp_rel: "rel x y \<Longrightarrow> x \<sim>\<^sub>\<Gamma> y"
  unfolding rel_def modular_group.rel_def by auto

lemma modular_group_rel_plus_int_iff_right1 [simp]:
  assumes "z \<in> \<int>"
  shows   "x \<sim>\<^sub>\<Gamma> y + z \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  from assms obtain n where n: "z = of_int n"
    by (elim Ints_cases)
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp (shift_modgrp n) y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by (simp add: n)
qed

lemma
  assumes "z \<in> \<int>"
  shows   modular_group_rel_plus_int_iff_right2 [simp]: "x \<sim>\<^sub>\<Gamma> z + y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left1 [simp]:  "z + x \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    and   modular_group_rel_plus_int_iff_left2 [simp]:  "x + z \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_plus_int_iff_right1[OF assms] modular_group.rel_commutes add.commute
  by metis+

lemma modular_group_rel_S_iff_right [simp]: "x \<sim>\<^sub>\<Gamma> -(1/y) \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
proof -
  have "x \<sim>\<^sub>\<Gamma> apply_modgrp S_modgrp y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
    by (subst modular_group.rel_apply_modgrp_right_iff) auto
  thus ?thesis
    by simp
qed

lemma modular_group_rel_S_iff_left [simp]: "-(1/x) \<sim>\<^sub>\<Gamma> y \<longleftrightarrow> x \<sim>\<^sub>\<Gamma> y"
  using modular_group_rel_S_iff_right[of y x] by (metis modular_group.rel_commutes)


text \<open>
  The index of a subgroup is the number of cosets.
\<close>
definition index_modgrp :: "modgrp set \<Rightarrow> nat" where
  "index_modgrp G = card (range (\<lambda>x. (*) x ` G))"


text \<open>
  The following defines the group generated by a set of elements.
\<close>
inductive_set generate_modgrp :: "modgrp set \<Rightarrow> modgrp set" for X :: "modgrp set" where
  "x \<in> X \<Longrightarrow> x \<in> generate_modgrp X"
| "1 \<in> generate_modgrp X"
| "x \<in> generate_modgrp X \<Longrightarrow> y \<in> generate_modgrp X \<Longrightarrow> x * y \<in> generate_modgrp X"
| "x \<in> generate_modgrp X \<Longrightarrow> inverse x \<in> generate_modgrp X"

lemma modgrp_subgroup_generate: "modgrp_subgroup (generate_modgrp X)"
  by standard (auto intro: generate_modgrp.intros)

lemma (in modgrp_subgroup) generate_modgrp_subsetI:
  assumes "X \<subseteq> G"
  shows   "generate_modgrp X \<subseteq> G"
proof
  fix x assume "x \<in> generate_modgrp X"
  thus "x \<in> G"
    by induction (use assms in auto)
qed



subsection \<open>Conjugation\<close>

text \<open>
  The conjugation of a subgroup $G$ w.r.t.\ some $h\in\Gamma$ is $h^{-1}Gh$.
\<close>
definition conj_modgrp :: "modgrp \<Rightarrow> modgrp set \<Rightarrow> modgrp set" where
  "conj_modgrp x G = (\<lambda>y. inverse x * y * x) ` G"

lemma conj_modgrp_mono: "G \<subseteq> H \<Longrightarrow> conj_modgrp x G \<subseteq> conj_modgrp x H"
  by (auto simp: conj_modgrp_def)

lemma conj_modgrp_altdef: "conj_modgrp x G = (\<lambda>y. x * y * inverse x) -` G"
proof -
  have bij: "bij (\<lambda>y. x * y * inverse x)"
    by (rule bij_betwI[of _ _ _ "\<lambda>y. inverse x * y * x"]) (auto simp: mult.assoc)
  hence "(\<lambda>y. x * y * inverse x) -` G = Hilbert_Choice.inv (\<lambda>y. x * y * inverse x) ` G"
    by (rule bij_vimage_eq_inv_image)
  also have "Hilbert_Choice.inv (\<lambda>y. x * y * inverse x) = (\<lambda>y. inverse x * y * x)"
    by (intro inj_imp_inv_eq bij_is_inj bij) (auto simp: mult.assoc)
  finally show ?thesis
    by (simp add: conj_modgrp_def)
qed

lemma conj_modgrp_UNIV [simp]: "conj_modgrp x UNIV = UNIV"
  by (simp add: conj_modgrp_altdef)

lemma in_conj_modgrp_iff: "z \<in> conj_modgrp x G \<longleftrightarrow> x * z * inverse x \<in> G"
  by (auto simp: conj_modgrp_altdef)

lemma conj_modgrp_mult: "conj_modgrp (g * f) G = conj_modgrp f (conj_modgrp g G)"
  by (auto simp: in_conj_modgrp_iff modgrp.inverse_distrib_swap mult.assoc)

lemma conj_modgrp_1 [simp]: "conj_modgrp 1 G = G"
  by (simp add: conj_modgrp_altdef)

context modgrp_subgroup
begin

lemma conj_modgrp_id:
  assumes "x \<in> G"
  shows   "conj_modgrp x G = G"
proof (intro equalityI subsetI)
  fix h assume "h \<in> conj_modgrp x G"
  thus "h \<in> G"
    using assms by (auto simp: conj_modgrp_def)
next
  fix h assume "h \<in> G"
  thus "h \<in> conj_modgrp x G"
    using assms by (auto simp: conj_modgrp_altdef)
qed

lemma modgrp_subgroup_conj: "modgrp_subgroup (conj_modgrp x G)"
proof
  fix f g
  assume "f \<in> conj_modgrp x G" "g \<in> conj_modgrp x G"
  hence "x * f * inverse x \<in> G" "x * g * inverse x \<in> G"
    by (auto simp: in_conj_modgrp_iff)
  from times_in_G[OF this] show "f * g  \<in> conj_modgrp x G"
    by (simp add: in_conj_modgrp_iff mult.assoc)
next
  fix f assume "f \<in> conj_modgrp x G"
  hence "x * f * inverse x \<in> G"
    by (simp add: in_conj_modgrp_iff)
  from inverse_in_G[OF this] show "inverse f \<in> conj_modgrp x G"
    by (simp add: in_conj_modgrp_iff mult.assoc modgrp.inverse_distrib_swap del: inverse_in_G_iff)
qed (auto simp: in_conj_modgrp_iff)

end


subsection \<open>Elliptic points\<close>

text \<open>
  The elliptic order of a point in the complex plane is the size of its stabiliser group
  (modulo $\pm I$).
\<close>
definition ellorder_modgrp :: "modgrp set \<Rightarrow> complex \<Rightarrow> nat" where
  "ellorder_modgrp G z =
     (if Im z > 0 then card {h\<in>G. apply_modgrp h z = z} div card (G \<inter> {1, -1}) else 0)"

lemma (in modgrp_subgroup) ellorder_modgrp_cong:
  assumes "rel w z"
  shows   "ellorder_modgrp G w = ellorder_modgrp G z"
proof -
  from assms obtain h where wz: "h \<in> G" "Im w > 0" "Im z > 0" "apply_modgrp h w = z"
    by (auto simp: rel_def)
  have "ellorder_modgrp G z = 
          card {g \<in> G. apply_modgrp (g * h) w = apply_modgrp h w} div card (G \<inter> {1, -1})"
    unfolding ellorder_modgrp_def wz(4)[symmetric]
    by (subst apply_modgrp_mult [symmetric]) (use wz in auto)
  also have "(\<lambda>g. apply_modgrp (g * h) w = apply_modgrp h w) =
             (\<lambda>g. apply_modgrp (inverse h * (g * h)) w = w)"
    by (subst apply_modgrp_eq_apply_modgrp_iff) (use wz in auto)
  also have "bij_betw (\<lambda>g. inverse h * (g * h))
               {g \<in> G. apply_modgrp (inverse h * (g * h)) w = w} 
               {g \<in> G. apply_modgrp g w = w}"
    by (rule bij_betwI[of _ _ _ "\<lambda>g. h * g * inverse h"])
       (use wz in \<open>auto simp flip: apply_modgrp_mult simp: mult.assoc\<close>)
  hence "card {g \<in> G. apply_modgrp (inverse h * (g * h)) w = w} = 
         card {g \<in> G. apply_modgrp g w = w}"
    by (rule bij_betw_same_card)
  also have "\<dots>  div card (G \<inter> {1, -1}) = ellorder_modgrp G w"
    using wz by (simp add: ellorder_modgrp_def)
  finally show ?thesis ..
qed


text \<open>
  We define the number of elliptic points of a given order, and the number of cusps (sometimes
  seen as elliptic points of order \<open>\<infinity>\<close>).
\<close>
definition ellcount_modgrp :: "modgrp set \<Rightarrow> nat \<Rightarrow> nat" where
  "ellcount_modgrp G k =
     card ({z. Im z > 0 \<and> ellorder_modgrp G z = k} // {(w,z). modgrp_subgroup.rel G w z})"

definition cusp_count_modgrp :: "modgrp set \<Rightarrow> nat" where
  "cusp_count_modgrp G = 1 + card ((-pole_modgrp ` G) // {(w::rat,z). \<exists>h. w = apply_modgrp h z})"


subsection \<open>Subgroups containing shifts\<close>

text \<open>
  We will now look at subgroups that contain some shift operator $T^n$ for $n > 0$.
  The cusp width at infinity is the smallest such $n$ (or equivalently the GCD of all such $n$).

  The cusp width at the other cusps (i.e.\ a rational numbers) is defined in the same way
  after conjugation with a modular transformation that sends the rational number to infinity.
\<close>
definition cusp_width_at_ii_inf :: "modgrp set \<Rightarrow> nat" ("cusp'_width\<^sub>\<infinity>") where
  "cusp_width_at_ii_inf G = nat (Gcd {n. shift_modgrp n \<in> G})"

definition cusp_width_modgrp :: "modgrp \<Rightarrow> modgrp set \<Rightarrow> nat" where
  "cusp_width_modgrp h G = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"

lemma of_nat_cusp_width_at_ii_inf:
  "of_nat (cusp_width_at_ii_inf G) = Gcd {n. shift_modgrp n \<in> G}"
  unfolding cusp_width_at_ii_inf_def by simp

lemma cusp_width_at_ii_inf_UNIV [simp]: "cusp_width_at_ii_inf UNIV = Suc 0"
  by (simp add: cusp_width_at_ii_inf_def)

lemma (in modgrp_subgroup) shift_modgrp_in_G_iff:
  "shift_modgrp n \<in> G \<longleftrightarrow> int (cusp_width_at_ii_inf G) dvd n"
proof -
  let ?A = "{n. shift_modgrp n \<in> G}"
  have "?A = {n. int (cusp_width_at_ii_inf G) dvd n}"
    unfolding of_nat_cusp_width_at_ii_inf
    by (rule ideal_int_conv_Gcd) (auto simp: shift_modgrp_add simp flip: shift_modgrp_power_int)
  thus ?thesis
    by auto
qed

locale modgrp_subgroup_periodic = modgrp_subgroup +
  assumes periodic': "\<exists>n>0. shift_modgrp n \<in> G"
begin

lemma cusp_width_at_ii_inf_pos: "cusp_width_at_ii_inf G > 0"
proof -
  have "Gcd {n. shift_modgrp n \<in> G} \<noteq> 0"
    using periodic' by (auto intro!: Nat.gr0I simp: Gcd_0_iff)
  moreover have "Gcd {n. shift_modgrp n \<in> G} \<ge> 0"
    by simp
  ultimately show ?thesis
    unfolding cusp_width_at_ii_inf_def by linarith
qed

lemma shift_modgrp_in_G_period [intro, simp]:
  "shift_modgrp (int (cusp_width_at_ii_inf G)) \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

lemma shift_modgrp_in_G [intro]:
  "int (cusp_width_at_ii_inf G) dvd n \<Longrightarrow> shift_modgrp n \<in> G"
  by (subst shift_modgrp_in_G_iff) auto

end


subsubsection \<open>Congruence subgroups\<close>

text \<open>
  The principal congruence subgroup $\Gamma(N)$ consists of those modular transformations $A$
  for which $A = I\ (\text{mod}\ N)$ (i.e.\ they look like the identity modulo $N$).
\<close>
lift_definition modgrps_pcong :: "int \<Rightarrow> modgrp set" ("(\<open>notation=\<open>mixfix modgrps_pcong\<close>\<close>\<Gamma>'(_'))") is
  "\<lambda>N. {(a,b,c,d) :: (int \<times> int \<times> int \<times> int) | a b c d. 
         a * d - b * c = 1 \<and> [a = 1] (mod N) \<and> [d = 1] (mod N) \<and> N dvd b \<and> N dvd c}"
  by (auto simp: rel_set_def)

lemma modgrps_pcong_altdef:
  "modgrps_pcong N = {f. [f = 1] (mod\<^sub>\<Gamma> N)}"
  unfolding cong_modgrp_def by transfer (auto simp: cong_0_iff)

lemma modgrps_pcong_abs [simp]: "modgrps_pcong (abs n) = modgrps_pcong n"
  by (auto simp: modgrps_pcong_altdef)

lemma modgrp_in_modgrps_pcong_iff:
  assumes "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_pcong N \<longleftrightarrow> [a = 1] (mod N) \<and> [d = 1] (mod N) \<and> N dvd b \<and> N dvd c"
  using assms
  by (auto simp: modgrps_pcong_altdef modgrp_c_code modgrp_a_code modgrp_b_code modgrp_d_code
                 cong_modgrp_def cong_0_iff)

lemma modgrp_in_modgrps_pcong:
  assumes "[a = 1] (mod N)" "[d = 1] (mod N)" "N dvd b" "N dvd c" "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_pcong N"
  using assms
  by (auto simp: modgrps_pcong_altdef modgrp_c_code modgrp_a_code modgrp_b_code modgrp_d_code
                 cong_modgrp_def cong_0_iff)

lemma modgrp_pcong_0 [simp]: "modgrps_pcong 0 = {1}"
  by (auto simp: modgrps_pcong_altdef modgrp_eq_iff cong_modgrp_def cong_0_iff)

lemma modgrp_pcong_1 [simp]: "modgrps_pcong 1 = UNIV"
  by (auto simp: modgrps_pcong_altdef modgrp_eq_iff cong_modgrp_def cong_0_iff)

lemma modgrps_pcong_mono: "n dvd m \<Longrightarrow> modgrps_pcong m \<subseteq> modgrps_pcong n"
  unfolding modgrps_pcong_altdef by (auto intro: cong_dvd_modulus simp: cong_modgrp_def cong_0_iff)

lemma modgrps_pcong_subset_iff: "modgrps_pcong m \<subseteq> modgrps_pcong n \<longleftrightarrow> n dvd m"
proof
  assume "modgrps_pcong m \<subseteq> modgrps_pcong n"
  have "shift_modgrp m \<in> modgrps_pcong m"
    by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
  also note \<open>modgrps_pcong m \<subseteq> modgrps_pcong n\<close>
  finally show "n dvd m"
    by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
qed (use modgrps_pcong_mono in auto)

lemma shift_in_modgrps_pcong_iff: "shift_modgrp n \<in> modgrps_pcong d \<longleftrightarrow> d dvd n"
  by (auto simp: modgrps_pcong_altdef simp: cong_modgrp_def cong_0_iff)

interpretation modgrps_pcong: modgrp_subgroup "modgrps_pcong N"
proof
  show "inverse x \<in> modgrps_pcong N" if "x \<in> modgrps_pcong N" for x
    using that by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
next
  show "x * y \<in> modgrps_pcong N" if "x \<in> modgrps_pcong N" "y \<in> modgrps_pcong N" for x y
  proof -
    from that have "N dvd modgrp_c x" "N dvd modgrp_c y"
      by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
    have "[modgrp_a x * modgrp_a y + modgrp_b x * modgrp_c y = 1 * 1 + 0 * 0] (mod N)"
      by (intro cong_add cong_mult) 
         (use that in \<open>auto simp: modgrps_pcong_altdef cong_0_iff cong_modgrp_def\<close>)
    moreover have "[modgrp_c x * modgrp_b y + modgrp_d x * modgrp_d y = 0 * 0 + 1 * 1] (mod N)"
      by (intro cong_add cong_mult)
         (use that in \<open>auto simp: modgrps_pcong_altdef cong_0_iff cong_modgrp_def\<close>)
    ultimately show ?thesis using that
      by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
  qed
qed (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)


text \<open>
  The level of a subgroup is the smallest $n$ such that it contains $\Gamma(n)$.
  Equivalently (and more elegantly), it is the GCD of all those numbers $n$.
\<close>
definition level_modgrp where "level_modgrp G = Gcd {n. modgrps_pcong n \<subseteq> G}"

lemma level_modgrp_nonneg: "level_modgrp G \<ge> 0"
  by (auto simp: level_modgrp_def)

lemma level_modgrp_UNIV [simp]: "level_modgrp UNIV = 1"
  by (simp add: level_modgrp_def)

text \<open>
  $\Gamma(n)$ is normal.
\<close>
lemma conj_modgrps_pcong: "conj_modgrp x (modgrps_pcong n) = modgrps_pcong n"
proof -
  have *: "modgrps_pcong n \<subseteq> conj_modgrp x (modgrps_pcong n)" for x
  proof
    fix f assume f: "f \<in> modgrps_pcong n"
    hence "[x * f * inverse x = x * 1 * inverse x] (mod\<^sub>\<Gamma> n)"
      by (intro cong_modgrp_mult) (auto simp: modgrps_pcong_altdef)
    thus "f \<in> conj_modgrp x (modgrps_pcong n)"
      by (simp add: in_conj_modgrp_iff modgrps_pcong_altdef)
  qed

  show ?thesis
  proof
    show "modgrps_pcong n \<subseteq> conj_modgrp x (modgrps_pcong n)"
      by (rule *)
  next
    have "conj_modgrp x (modgrps_pcong n) \<subseteq> 
            conj_modgrp x (conj_modgrp (inverse x) (modgrps_pcong n))"
      by (intro conj_modgrp_mono *)
    also have "\<dots> = modgrps_pcong n"
      by (simp flip: conj_modgrp_mult)
    finally show "conj_modgrp x (modgrps_pcong n) \<subseteq> modgrps_pcong n" .
  qed
qed

text \<open>
  The level of $\Gamma(N)$ is, unsurprisingly, $N$.
\<close>
lemma level_conj_modgrp [simp]: "level_modgrp (conj_modgrp x G) = level_modgrp G"
proof -
  have "modgrps_pcong n \<subseteq> conj_modgrp x G \<longleftrightarrow> modgrps_pcong n \<subseteq> G" for n
  proof
    assume "modgrps_pcong n \<subseteq> G"
    hence "conj_modgrp x (modgrps_pcong n) \<subseteq> conj_modgrp x G"
      by (intro conj_modgrp_mono)
    thus "modgrps_pcong n \<subseteq> conj_modgrp x G"
      by (simp add: conj_modgrps_pcong)
  next
    assume "modgrps_pcong n \<subseteq> conj_modgrp x G"
    hence "conj_modgrp (inverse x) (modgrps_pcong n) \<subseteq> conj_modgrp (inverse x) (conj_modgrp x G)"
      by (intro conj_modgrp_mono)
    thus "modgrps_pcong n \<subseteq> G"
      by (simp flip: conj_modgrp_mult add: conj_modgrps_pcong)
  qed
  thus ?thesis
    by (simp add: level_modgrp_def)
qed

(* TODO: move *)
lemma cong_lcm_iff:
  "[a = (b :: 'a :: {unique_euclidean_ring, ring_gcd})] (mod lcm m n) \<longleftrightarrow> 
     [a = b] (mod m) \<and> [a = b] (mod n)"
proof
  assume "[a = b] (mod lcm m n)"
  thus "[a = b] (mod m) \<and> [a = b] (mod n)"
    by (metis cong_dvd_mono_modulus dvd_lcm1 lcm.commute)
next
  assume "[a = b] (mod m) \<and> [a = b] (mod n)"
  thus "[a = b] (mod lcm m n)"
    by (auto simp: cong_iff_dvd_diff)
qed

text \<open>
  Next we investigate $\Gamma(\text{lcm}(n,m))$ and $\Gamma(\text{gcd}(n,m))$. The former
  is very easy.
\<close>
lemma modgrps_pcong_lcm: "modgrps_pcong (lcm n m) = modgrps_pcong n \<inter> modgrps_pcong m"
  by (auto simp: modgrps_pcong_altdef cong_lcm_iff cong_modgrp_def)

text \<open>
  The case for the GCD is slightly more difficult and requires the Chinese Remainder Theorem
  and the surjectivity of the reduction map.
\<close>
lemma modgrps_pcong_gcd_aux:
  assumes "h \<in> modgrps_pcong (gcd m n)"
  obtains f g where "f \<in> modgrps_pcong m" "g \<in> modgrps_pcong n" "h = f * g"
proof -
  define D where "D = gcd m n"
  define a b c d where abcd: "a = modgrp_a h" "b = modgrp_b h" "c = modgrp_c h" "d = modgrp_d h"
  have abcd_cong: "[a = 1] (mod D)" "D dvd b" "D dvd c" "[d = 1] (mod D)"
    using assms by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff abcd D_def)
  have det: "a * d - b * c = 1"
    unfolding abcd by (rule modgrp_abcd_det)

  obtain a1 where a1: "[a1 = a] (mod m)" "[a1 = 1] (mod n)"
    using chinese_remainder_theorem_gen[of a 1 m n] abcd_cong by (auto simp: D_def)
  obtain b1 where b1: "[b1 = b] (mod m)" "[b1 = 0] (mod n)"
    using chinese_remainder_theorem_gen[of b 0 m n] abcd_cong by (auto simp: D_def cong_0_iff)
  obtain c1 where c1: "[c1 = c] (mod m)" "[c1 = 0] (mod n)"
    using chinese_remainder_theorem_gen[of c 0 m n] abcd_cong by (auto simp: D_def cong_0_iff)
  obtain d1 where d1: "[d1 = d] (mod m)" "[d1 = 1] (mod n)"
    using chinese_remainder_theorem_gen[of d 1 m n] abcd_cong by (auto simp: D_def)
  have det1: "[a1 * d1 - b1 * c1 = 1] (mod lcm m n)"
  proof (rule cong_cong_lcm_int)
    have "[a1 * d1 - b1 * c1 = a * d - b * c] (mod m)"
      by (intro cong_diff cong_mult a1 b1 c1 d1)
    thus "[a1 * d1 - b1 * c1 = 1] (mod m)"
      using det by simp
  next
    have "[a1 * d1 - b1 * c1 = 1 * 1 - 0 * 0] (mod n)"
      by (intro cong_diff cong_mult a1 b1 c1 d1)
    thus "[a1 * d1 - b1 * c1 = 1] (mod n)"
      using det by simp
  qed
  obtain f where "[modgrp_a f = a1] (mod lcm m n)" "[modgrp_b f = b1] (mod lcm m n)"
                 "[modgrp_c f = c1] (mod lcm m n)" "[modgrp_d f = d1] (mod lcm m n)"
    using modgrp_reduction_surj[OF det1] by blast
  hence f: "[f = h] (mod\<^sub>\<Gamma> m)" "[f = 1] (mod\<^sub>\<Gamma> n)"
    using a1 b1 c1 d1 by (auto simp: cong_modgrp_def cong_lcm_iff simp flip: abcd intro: cong_trans)

  define g where "g = h * inverse f"
  have "[g = h * inverse h] (mod\<^sub>\<Gamma> m)"
    unfolding g_def by (intro cong_modgrp_mult cong_modgrp_inverse f cong_modgrp_refl)
  hence g: "[g = 1] (mod\<^sub>\<Gamma> m)"
    by simp
  have gf: "g * f = h"
    by (auto simp: g_def mult.assoc)

  show ?thesis
    using f g gf by (intro that[of g f]) (auto simp: modgrps_pcong_altdef)
qed

lemma (in modgrp_subgroup) modgrps_pcong_gcd:
  fixes m n :: int
  defines "H \<equiv> generate_modgrp (modgrps_pcong m \<union> modgrps_pcong n)"
  shows   "modgrps_pcong (gcd m n) = H"
proof
  show "H \<subseteq> modgrps_pcong (gcd m n)"
    unfolding H_def by (intro modgrps_pcong.generate_modgrp_subsetI Un_least modgrps_pcong_mono) auto
next
  show "modgrps_pcong (gcd m n) \<subseteq> H"
  proof
    fix h assume h: "h \<in> modgrps_pcong (gcd m n)"
    then obtain f g where fg: "h = f * g" "f \<in> modgrps_pcong m" "g \<in> modgrps_pcong n"
      using modgrps_pcong_gcd_aux[of h m n] h by metis
    thus "h \<in> H" unfolding H_def fg(1) 
      by (intro generate_modgrp.intros(2-)) (auto intro: generate_modgrp.intros(1))
  qed
qed

text \<open>
  Finally we prove a key lemma: $\Gamma(N)$ is contained in a subgroup iff $N$ is a multiple
  of the level.
\<close>
lemma (in modgrp_subgroup) contains_modgrps_pcong_iff:
  "modgrps_pcong n \<subseteq> G \<longleftrightarrow> level_modgrp G dvd n"
proof -
  have "{n. modgrps_pcong n \<subseteq> G} = {n. level_modgrp G dvd n}"
    unfolding level_modgrp_def
  proof (rule Gcd_gcd_closed_set_int)
    show "0 \<in> {n. modgrps_pcong n \<subseteq> G}"
      by auto
  next
    fix x y :: int
    assume "x \<in> {n. modgrps_pcong n \<subseteq> G}"
    thus "x * y \<in> {n. modgrps_pcong n \<subseteq> G}"
      using modgrps_pcong_mono[of x "x * y"] by auto
  next
    fix x y
    assume xy: "x \<in> {n. modgrps_pcong n \<subseteq> G}" "y \<in> {n. modgrps_pcong n \<subseteq> G}"
    have "modgrps_pcong (gcd x y) = generate_modgrp (modgrps_pcong x \<union> modgrps_pcong y)"
      by (rule modgrps_pcong_gcd)
    also have "\<dots> \<subseteq> G"
      by (intro generate_modgrp_subsetI) (use xy in auto)
    finally show "gcd x y \<in> {n. modgrps_pcong n \<subseteq> G}"
      by simp
  qed
  thus ?thesis
    by auto
qed

text \<open>
  It is also easy to see that the level is a multiple of all cusp widths.
  It is in fact even exactly the LCM of the cusp widths (as shown by Wohlfahrt), 
  but we do not show this here.
\<close>
(* TODO: cite Wohlfahrt here? *)
(* TODO Prove Wohlfahrt *)
lemma (in modgrp_subgroup) cusp_width_at_ii_inf_dvd_level:
  "cusp_width_at_ii_inf G dvd level_modgrp G"
proof -
  have "Gcd {n. shift_modgrp n \<in> G} dvd level_modgrp G"
  proof (rule Gcd_dvd)
    have "shift_modgrp (level_modgrp G) \<in> modgrps_pcong (level_modgrp G)"
      by (auto simp: modgrps_pcong_altdef cong_modgrp_def cong_0_iff)
    also have "modgrps_pcong (level_modgrp G) \<subseteq> G"
      by (auto simp: contains_modgrps_pcong_iff)
    finally show "level_modgrp G \<in> {n. shift_modgrp n \<in> G}"
      by simp
  qed
  thus ?thesis
    by (simp add: cusp_width_at_ii_inf_def)
qed

lemma level_modgrps_pcong [simp]: "level_modgrp (modgrps_pcong n) = abs n"
proof -
  have "level_modgrp (modgrps_pcong n) dvd n"
    using level_modgrp_def by simp
  moreover have "modgrps_pcong (level_modgrp (modgrps_pcong n)) \<subseteq> modgrps_pcong n"
    by (simp add: modgrps_pcong.contains_modgrps_pcong_iff)
  hence "n dvd level_modgrp (modgrps_pcong n)"
    by (simp add: modgrps_pcong_subset_iff)
  ultimately have "abs (level_modgrp (modgrps_pcong n)) = abs n"
    by (intro zdvd_antisym_abs)
  thus ?thesis
    using level_modgrp_nonneg[of "modgrps_pcong n"] by simp
qed 


text \<open>
  A \<^emph>\<open>congruence subgroup\<close> is a subgroup of the modular group that contains $\Gamma(N)$ for some
  $N > 0$.
\<close>
locale cong_subgroup = modgrp_subgroup +
  assumes level_pos: "level_modgrp G > 0"
begin

definition cusp_width :: "rat \<Rightarrow> nat" where
  "cusp_width x = (let f = modgrp_of_rat x in Gcd {n. inverse f * shift_modgrp (int n) * f \<in> G})"

lemma cong_subgroup_conj: "cong_subgroup (conj_modgrp x G)"
proof -
  interpret conj: modgrp_subgroup "conj_modgrp x G"
    by (rule modgrp_subgroup_conj)
  show ?thesis
  proof
    show "level_modgrp (conj_modgrp x G) > 0"
      by (simp add: level_pos)
  qed
qed

sublocale modgrp_subgroup_periodic G
proof
  have "cusp_width\<^sub>\<infinity> G dvd level_modgrp G"
    by (rule cusp_width_at_ii_inf_dvd_level)
  with level_pos have "cusp_width\<^sub>\<infinity> G > 0"
    by (intro Nat.gr0I) auto
  thus "\<exists>n>0. shift_modgrp n \<in> G"
    by (intro exI[of _ "int (cusp_width_at_ii_inf G)"]) (auto simp: shift_modgrp_in_G_iff)
qed

end

lemma cong_subgroup_pcong: "N > 0 \<Longrightarrow> cong_subgroup (modgrps_pcong N)"
  by standard auto

interpretation modular_group: cong_subgroup UNIV
  rewrites "cusp_width_at_ii_inf UNIV = Suc 0"
  by unfold_locales (auto intro: exI[of _ 1] simp: cusp_width_at_ii_inf_def)

lemma cong_subgroup_UNIV [intro]: "cong_subgroup UNIV" ..


subsubsection \<open>Hecke subgroups $\Gamma_0(N)$\<close>

text \<open>
  The Hecke subgroup of level $N$, $\Gamma_0(N)$, is a superset of $\Gamma(N)$.
  It only requires that $c \equiv 0\ (\text{mod}\ N)$, i.e.\ it consists of the matrices that are
  lower triangular matrices modulo $N$.

  All cusps have width 1 in $\Gamma_0(N)$.
\<close>
lift_definition modgrps_hecke :: "int \<Rightarrow> modgrp set" ("(\<open>notation=\<open>mixfix modgrps_hecke\<close>\<close>\<Gamma>\<^sub>0'(_'))") is
  "\<lambda>N. {(a,b,c,d) :: (int \<times> int \<times> int \<times> int) | a b c d. a * d - b * c = 1 \<and> N dvd c}"
  by (auto simp: rel_set_def)

lemma modgrps_hecke_altdef: "modgrps_hecke q = {f. q dvd modgrp_c f}"
  by transfer' auto

lemma modgrp_in_modgrps_hecke_iff:
  assumes "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_hecke q \<longleftrightarrow> q dvd c"
  using assms by (auto simp: modgrps_hecke_altdef modgrp_c_code)

lemma modgrp_in_modgrps_hecke:
  assumes "q dvd c" "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_hecke q"
  using assms by (auto simp: modgrps_hecke_altdef modgrp_c_code)

lemma shift_in_modgrps_hecke [simp]: "shift_modgrp n \<in> modgrps_hecke q"
  by (auto simp: modgrps_hecke_altdef)

lemma cusp_width_at_ii_inf_hecke [simp]: "cusp_width\<^sub>\<infinity> (modgrps_hecke q) = 1"
  by (simp add: cusp_width_at_ii_inf_def)

lemma S_in_modgrps_hecke_iff [simp]: "S_modgrp \<in> modgrps_hecke q \<longleftrightarrow> is_unit q"
  by (auto simp: modgrps_hecke_altdef)

lemma level_modgrps_hecke [simp]: "level_modgrp (modgrps_hecke N) = abs N"
proof -
  have "modgrps_pcong N \<subseteq> modgrps_hecke N"
    by (auto simp: modgrps_pcong_altdef modgrps_hecke_altdef cong_modgrp_def cong_0_iff)
  hence "level_modgrp (modgrps_hecke N) dvd N"
    by (simp add: level_modgrp_def)
  moreover have "N dvd level_modgrp (modgrps_hecke N)"
    unfolding level_modgrp_def
  proof (rule Gcd_greatest, safe)
    fix n assume "modgrps_pcong n \<subseteq> modgrps_hecke N"
    have "modgrp 1 0 n 1 \<in> modgrps_pcong n"
      by (auto simp: modgrps_pcong_altdef cong_modgrp_def modgrp_abcd_modgrp cong_0_iff)
    also note \<open>modgrps_pcong n \<subseteq> modgrps_hecke N\<close>
    finally show "N dvd n"
      by (auto simp: modgrps_hecke_altdef modgrp_c_modgrp)
  qed
  ultimately have "abs (level_modgrp (modgrps_hecke N)) = abs N"
    using zdvd_antisym_abs by blast
  thus ?thesis
    using level_modgrp_nonneg[of "modgrps_hecke N"] by simp
qed


locale hecke_subgroup =
  fixes q :: int
  assumes q_pos: "q > 0"
begin

definition subgrp ("\<Gamma>''") where "subgrp = modgrps_hecke q"

lemma S_in_subgrp_iff [simp]: "S_modgrp \<in> subgrp \<longleftrightarrow> q = 1"
  using q_pos by (auto simp: subgrp_def)

sublocale modgrp_subgroup \<Gamma>'
proof
  show "inverse x \<in> \<Gamma>'" if "x \<in> \<Gamma>'" for x
  proof -
    from that have "q dvd modgrp_c x"
      by (simp add: modgrps_hecke_altdef subgrp_def)
    hence "q dvd modgrp_c (inverse x)"
      by transfer auto
    thus "inverse x \<in> \<Gamma>'"
      by (simp add: modgrps_hecke_altdef subgrp_def)
  qed
next
  show "x * y \<in> \<Gamma>'" if "x \<in> \<Gamma>'" "y \<in> \<Gamma>'" for x y
  proof -
    from that have "q dvd modgrp_c x" "q dvd modgrp_c y"
      by (auto simp: modgrps_hecke_altdef subgrp_def)
    hence "q dvd modgrp_c (x * y)"
      by transfer auto
    thus ?thesis
      by (auto simp: modgrps_hecke_altdef subgrp_def)
  qed
qed (auto simp: subgrp_def modgrps_hecke_altdef)

sublocale cong_subgroup \<Gamma>'
proof
  show "level_modgrp \<Gamma>' > 0"
    using q_pos by (simp add: subgrp_def)
qed

end


text \<open>
  Next, we focus on the Hecke subgroups of prime d.
\<close>
locale hecke_prime_subgroup =
  fixes p :: int
  assumes p_prime: "prime p"
begin

lemma p_pos: "p > 0"
  using p_prime by (simp add: prime_gt_0_int)

lemma p_not_1 [simp]: "p \<noteq> 1"
  using p_prime by auto

sublocale hecke_subgroup p
  by standard (rule p_pos)

notation subgrp ("\<Gamma>''")

definition S_shift_modgrp where "S_shift_modgrp n = S_modgrp * shift_modgrp n"

(* Theorem 4.1 *)
text \<open>
  Every transformation $f\in\Gamma$ that is \<^emph>\<open>not\<close> in the subgroup can be written as a product
  $f = g S T^k$, where $g$ \<^emph>\<open>is\<close> in the subgroup.
\<close>
lemma modgrp_decompose:
  assumes "f \<notin> \<Gamma>'"
  obtains g k where "g \<in> \<Gamma>'" "k \<in> {0..<p}" "f = g * S_modgrp * shift_modgrp k"
proof -
  define a b c d where "a = modgrp_a f" "b = modgrp_b f" "c = modgrp_c f" "d = modgrp_d f"
  have det: "a * d - b * c = 1"
    unfolding a_b_c_d_def using modgrp_abcd_det[of f] by simp
  have "\<not>p dvd c"
    unfolding a_b_c_d_def using assms by (auto simp: subgrp_def modgrps_hecke_altdef)
  hence "coprime p c"
    using p_prime by (intro prime_imp_coprime) auto
  define k where "k = (modular_inverse p c * d) mod p"
  have "[k * c = (modular_inverse p c * d) mod p * c] (mod p)"
    by (simp add: k_def)
  also have "[(modular_inverse p c * d) mod p * c = modular_inverse p c * d * c] (mod p)"
    by (intro cong_mult cong_mod_leftI cong_refl)
  also have "modular_inverse p c * d * c = modular_inverse p c * c * d"
    by (simp add: mult_ac)
  also have "[\<dots> = 1 * d] (mod p)" using \<open>coprime p c\<close>
    by (intro cong_mult cong_refl cong_modular_inverse2) (auto simp: coprime_commute)
  finally have "[k * c = d] (mod p)"
    by simp
  hence dvd: "p dvd k * c - d"
    by (simp add: cong_iff_dvd_diff)

  have det': "(k * a - b) * c - a * (k * c - d) = 1"
    using det by (simp add: algebra_simps)
  define g where "g = modgrp (k * a - b) a (k * c - d) c"

  show ?thesis
  proof (rule that)
    show "g \<in> \<Gamma>'"
      unfolding subgrp_def g_def using det' dvd
      by (intro modgrp_in_modgrps_hecke) auto
  next
    show "k \<in> {0..<p}"
      unfolding k_def using p_pos by simp
  next
    have "g * S_modgrp * shift_modgrp k = modgrp a b c d" using det
      by (auto simp: g_def S_modgrp_code shift_modgrp_code times_modgrp_code algebra_simps)
    also have "\<dots> = f"
      by (simp add: a_b_c_d_def)
    finally show "f = g * S_modgrp * shift_modgrp k" ..
  qed
qed

lemma modgrp_decompose':
  obtains g h 
    where "g \<in> \<Gamma>'" "h = 1 \<or> (\<exists>k\<in>{0..<p}. h = S_shift_modgrp k)" "f = g * h"
proof (cases "f \<in> \<Gamma>'")
  case True
  thus ?thesis
    using that[of f 1] by auto
next
  case False
  thus ?thesis
    using modgrp_decompose[of f] that modgrp.assoc unfolding S_shift_modgrp_def
    by metis
qed

end


subsection \<open>The subgroups $\Gamma_1(N)$\<close>

text \<open>
  The following subgroups lie inbetween $\Gamma(N)$ and $\Gamma_0(N)$. They consist of those
  matrices that become upper triangular matrices with 1 on the diagonal when reduced modulo $N$.

  These groups do not seem to have a name in the literature. We call them the ``unipotent subgroups
  modulo $N$'' (since upper triangular matrices with 1 on the diagonal are exactly the unipotent
  matrices).

  Again, the level of $\Gamma(N)$ is $N$ and the cusp widths are all 1.
\<close>
lift_definition modgrps_unip :: "int \<Rightarrow> modgrp set" ("(\<open>notation=\<open>mixfix modgrps_unip\<close>\<close>\<Gamma>\<^sub>1'(_'))") is
  "\<lambda>N. {(a,b,c,d) :: (int \<times> int \<times> int \<times> int) | a b c d. a * d - b * c = 1 \<and>
          [a = 1] (mod N) \<and> N dvd c \<and> [d = 1] (mod N)}"
  by auto

lemma modgrps_unip_altdef:
  "modgrps_unip N = {f. [modgrp_a f = 1] (mod N) \<and> [modgrp_d f = 1] (mod N) \<and> N dvd modgrp_c f}"
  by transfer auto

lemma modgrps_unip_subset_hecke: "modgrps_unip N \<subseteq> modgrps_hecke N"
  by (auto simp: modgrps_unip_def modgrps_hecke_def)

lemma modgrp_in_modgrps_unip_iff:
  assumes "a * d - b * c = 1"
  shows   "modgrp a b c d \<in> modgrps_unip N \<longleftrightarrow> [a = 1] (mod N) \<and> [d = 1] (mod N) \<and> N dvd c"
  using assms by (auto simp: modgrps_unip_altdef modgrp_c_code modgrp_a_code modgrp_d_code)

lemma shift_in_modgrps_unip [simp]: "shift_modgrp n \<in> modgrps_unip N"
  by (auto simp: modgrps_unip_altdef)

lemma cusp_width_at_ii_inf_unip [simp]: "cusp_width\<^sub>\<infinity> (modgrps_unip N) = 1"
  by (simp add: cusp_width_at_ii_inf_def)

lemma S_in_modgrps_unip_iff [simp]: "S_modgrp \<in> modgrps_unip N \<longleftrightarrow> is_unit N"
  by (auto simp: modgrps_unip_altdef cong_iff_dvd_diff)

lemma level_modgrps_unip [simp]: "level_modgrp (modgrps_unip N) = abs N"
proof -
  have "modgrps_pcong N \<subseteq> modgrps_unip N"
    by (auto simp: modgrps_pcong_altdef modgrps_unip_altdef cong_modgrp_def cong_0_iff)
  hence "level_modgrp (modgrps_unip N) dvd N"
    by (simp add: level_modgrp_def)
  moreover have "N dvd level_modgrp (modgrps_unip N)"
    unfolding level_modgrp_def
  proof (rule Gcd_greatest, safe)
    fix n assume "modgrps_pcong n \<subseteq> modgrps_unip N"
    have "modgrp 1 0 n 1 \<in> modgrps_pcong n"
      by (auto simp: modgrps_pcong_altdef cong_modgrp_def modgrp_abcd_modgrp cong_0_iff)
    also note \<open>modgrps_pcong n \<subseteq> modgrps_unip N\<close>
    finally show "N dvd n"
      by (auto simp: modgrps_unip_altdef modgrp_c_modgrp)
  qed
  ultimately have "abs (level_modgrp (modgrps_unip N)) = abs N"
    using zdvd_antisym_abs by blast
  thus ?thesis
    using level_modgrp_nonneg[of "modgrps_unip N"] by simp
qed


locale unip_subgroup =
  fixes N :: int
  assumes N_pos: "N > 0"
begin

definition subgrp ("\<Gamma>''") where "subgrp = modgrps_unip N"

lemma S_in_subgrp_iff [simp]: "S_modgrp \<in> subgrp \<longleftrightarrow> N = 1"
  using N_pos by (auto simp: subgrp_def)

sublocale modgrp_subgroup \<Gamma>'
proof
  show "inverse x \<in> \<Gamma>'" if "x \<in> \<Gamma>'" for x
    using that by (auto simp: modgrps_unip_altdef subgrp_def)
next
  show "x * y \<in> \<Gamma>'" if "x \<in> \<Gamma>'" "y \<in> \<Gamma>'" for x y
  proof -
    have c: "N dvd modgrp_c (x * y)"
      using that by (auto simp: subgrp_def modgrps_unip_altdef)
    have "[modgrp_a x * modgrp_a y + modgrp_b x * modgrp_c y = 1 * 1 + modgrp_b x * 0] (mod N)"
      by (intro cong_add cong_mult)
         (use that in \<open>auto simp: subgrp_def modgrps_unip_altdef cong_0_iff\<close>)
    hence a: "[modgrp_a (x * y) = 1] (mod N)"
      by simp
    have "[modgrp_c x * modgrp_b y + modgrp_d x * modgrp_d y = 0 * modgrp_b y + 1 * 1] (mod N)"
      by (intro cong_add cong_mult)
         (use that in \<open>auto simp: subgrp_def modgrps_unip_altdef cong_0_iff\<close>)
    hence d: "[modgrp_d (x * y) = 1] (mod N)"
      by simp   
    show ?thesis using a c d
      by (auto simp: modgrps_unip_altdef subgrp_def)
  qed
qed (auto simp: subgrp_def modgrps_unip_altdef)

sublocale cong_subgroup \<Gamma>'
proof
  show "level_modgrp \<Gamma>' > 0"
    using N_pos by (simp add: subgrp_def)
qed

end

bundle modgrp_notation
begin

notation modular_group.rel (infixl "\<sim>\<^sub>\<Gamma>" 49)
notation modgrps_pcong ("(\<open>notation=\<open>mixfix modgrps_pcong\<close>\<close>\<Gamma>'(_'))")
notation modgrps_hecke ("(\<open>notation=\<open>mixfix modgrps_hecke\<close>\<close>\<Gamma>\<^sub>0'(_'))")
notation modgrps_unip ("(\<open>notation=\<open>mixfix modgrps_unip\<close>\<close>\<Gamma>\<^sub>1'(_'))")

end

unbundle no modgrp_notation

end