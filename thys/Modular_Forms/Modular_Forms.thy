section \<open>Definition of modular forms and related concepts\<close>
theory Modular_Forms
  imports Meromorphic_Upper_Half_Plane Fourier_Expansion_Mero_UHP
begin

named_theorems mform_intros

notation const_mero_uhp ("\<langle>_\<rangle>")

(* TODO Move *)
lemma apply_modgrp_meromorphic [meromorphic_intros]:
  assumes "f meromorphic_on A"
  shows   "(\<lambda>z. apply_modgrp h (f z)) meromorphic_on A"
  unfolding apply_modgrp_altdef 
  by (intro meromorphic_intros moebius_meromorphic assms)

definition zorder_at_cusp_modgrp :: "int \<Rightarrow> modgrp set \<Rightarrow> mero_uhp \<Rightarrow> modgrp \<Rightarrow> int" where
  "zorder_at_cusp_modgrp weight G f h = 
     zorder_at_ii_inf (cusp_width_modgrp h G) (slash_mero_uhp weight h f)"


subsection \<open>Weakly meromorphic forms\<close>

text \<open>
  Weakly modular forms of weight $k$ and level $G$ (where $G$ is congruence subgroup)
  are meromorphic functions on the upper half plane that are invariant under the weight-$k$ slash 
  operator for every $h\in G$.
\<close>
locale weakly_meromorphic_form = cong_subgroup G
  for f :: mero_uhp and weight :: int and G :: "modgrp set" +
  assumes invariant_slash_modgrp: "h \<in> G \<Longrightarrow> slash_mero_uhp weight h f = f"
begin

lemma periodic: "compose_modgrp_mero_uhp f (shift_modgrp (cusp_width\<^sub>\<infinity> G)) = f"
  using invariant_slash_modgrp[of "shift_modgrp (cusp_width\<^sub>\<infinity> G)"]
  by (auto simp: slash_mero_uhp_def)

sublocale fourier_expansion_locale "cusp_width\<^sub>\<infinity> G" f
  by standard (auto simp: cusp_width_at_ii_inf_pos periodic)

lemma mero_uhp_rel_apply_modgrp:
  assumes "h \<in> G"
  shows "mero_uhp_rel (\<lambda>z. eval_mero_uhp f (apply_modgrp h z))
           (\<lambda>z. automorphy_factor h z powi weight * eval_mero_uhp f z)"
proof -
  define j where "j = automorphy_factor h"
  have "mero_uhp_rel (\<lambda>z. eval_mero_uhp f (apply_modgrp h z))
               (\<lambda>z. j z powi weight * (j z powi (-weight) * eval_mero_uhp f (apply_modgrp h z)))"
    by (rule mero_uhp_relI_weak) (auto simp: j_def power_int_minus field_simps)
  also have "mero_uhp_rel \<dots> (\<lambda>z. j z powi weight * slash_mero_uhp weight h f z)"
    unfolding j_def by mero_uhp_rel
  also have "slash_mero_uhp weight h f = f"
    by (rule invariant_slash_modgrp) fact
  finally show ?thesis by (simp add: j_def)
qed

lemma invariant_compose_modgrp:
  assumes "h \<in> G"
  shows   "compose_modgrp_mero_uhp f h = automorphy_factor_mero_uhp h powi weight * f"
proof -
  note [mero_uhp_rel_intros] = mero_uhp_rel_apply_modgrp
  have "mero_uhp_rel (compose_modgrp_mero_uhp f h) 
          (automorphy_factor_mero_uhp h powi weight * f)"
    using assms by mero_uhp_rel
  thus ?thesis
    by (rule mero_uhp_rel_imp_eq_mero_uhp)
qed

lemmas [analytic_intros del] = constant_on_imp_analytic_on

lemma is_pole_apply_modgrp_iff [simp]:
  assumes h: "h \<in> G"
  shows "is_pole (eval_mero_uhp f) (apply_modgrp h z) \<longleftrightarrow> is_pole f z"
proof (cases "Im z > 0")
  case True
  have "is_pole (eval_mero_uhp f) (apply_modgrp h z) \<longleftrightarrow>
        is_pole (eval_mero_uhp f \<circ> apply_modgrp h) z"
  proof (rule is_pole_compose_iff [symmetric])
    show "filtermap (apply_modgrp h) (at z) = at (apply_modgrp h z)"
      using True by (intro filtermap_at_apply_modgrp) auto
  qed
  also have "\<dots> \<longleftrightarrow> is_pole (\<lambda>z. automorphy_factor h z powi weight * eval_mero_uhp f z) z"
  proof (rule is_pole_cong')
    show " \<forall>\<^sub>\<approx>x\<in>{z. Im z > 0}. (eval_mero_uhp f \<circ> apply_modgrp h) x =
                                 automorphy_factor h x powi weight * eval_mero_uhp f x"
      using mero_uhp_rel_apply_modgrp[of h] by (simp add: mero_uhp_rel_def assms)
  qed (use True in \<open>auto simp: open_halfspace_Im_gt\<close>)
  also have "\<dots> \<longleftrightarrow> is_pole (eval_mero_uhp f) z"
    by (rule is_pole_mult_analytic_nonzero1_iff) (use True in \<open>auto intro!: analytic_intros\<close>)
  finally show ?thesis .
next
  case False
  have "\<not>is_pole f z" "\<not>is_pole f (apply_modgrp h z)"
    by (rule not_is_pole_eval_mero_uhp_outside; use False in simp; fail)+
  thus ?thesis
    by simp
qed  

lemma invariant_apply_modgrp [simp]:
  assumes h: "h \<in> G"
  shows "eval_mero_uhp f (apply_modgrp h z) = automorphy_factor h z powi weight * eval_mero_uhp f z"
proof (cases "Im z > 0 \<and> \<not>is_pole (eval_mero_uhp f) z")
  case True
  have "mero_uhp_rel
          (eval_mero_uhp (compose_modgrp_mero_uhp f h - automorphy_factor_mero_uhp h powi weight * f))
          (\<lambda>z. eval_mero_uhp f (apply_modgrp h z) - automorphy_factor h z powi weight * eval_mero_uhp f z)"
    by mero_uhp_rel
  also have "compose_modgrp_mero_uhp f h - automorphy_factor_mero_uhp h powi weight * f = 0"
    using h by (simp add: invariant_compose_modgrp)
  finally have "eval_mero_uhp 0 z =
           eval_mero_uhp f (apply_modgrp h z) - automorphy_factor h z powi weight * eval_mero_uhp f z"
    by (rule mero_uhp_rel_imp_eval_mero_uhp_eq) (use True h in \<open>auto intro!: analytic_intros\<close>)
  thus ?thesis
    using True by auto
next
  case False
  then consider "Im z \<le> 0" | "Im z > 0" "is_pole (eval_mero_uhp f) z"
    by fastforce
  thus ?thesis
    by cases (auto simp: eval_mero_uhp_outside eval_mero_uhp_pole is_pole_apply_modgrp_iff h)
qed

lemma rel_imp_zorder_eq:
  assumes "rel z z'"
  shows   "zorder f z = zorder f z'"
proof (cases "f = 0")
  case True
  hence *: "eval_mero_uhp f = (\<lambda>_. 0)"
    by (intro ext) auto
  thus ?thesis
    by (simp add: zorder_shift')
next
  case False
  from assms obtain g where g: "g \<in> G" "z' = apply_modgrp g z" "Im z > 0" "Im z' > 0"
    by (auto simp: rel_def)
  note z = g(3)
  have ev_nz: "eventually (\<lambda>z. f z \<noteq> 0) (at z)"
    using \<open>f \<noteq> 0\<close> z eventually_eval_mero_uhp_neq_iff[of z f 0] by auto

  have "\<forall>\<^sub>F w in at z. w \<in> {w. Im w > 0} - {z}"
    by (intro eventually_at_in_open open_halfspace_Im_gt) (use g in auto)
  hence ev_nz': "\<forall>\<^sub>F w in at z. apply_modgrp g w \<noteq> apply_modgrp g z"
  proof eventually_elim
    case (elim w)
    with g show ?case 
      by (subst apply_modgrp_eq_iff) auto
  qed

  have "zorder (\<lambda>w. automorphy_factor g w powi weight * f w) z =
        zorder f z + zorder (\<lambda>w. automorphy_factor g w powi weight) z"
  proof (subst zorder_mult)
    have "eventually (\<lambda>z. z \<in> {z. Im z > 0}) (at z)"
      using z by (intro eventually_at_in_open' open_halfspace_Im_gt) auto
    hence "eventually (\<lambda>z. automorphy_factor g z powi weight \<noteq> 0) (at z)"
      by eventually_elim auto
    thus "\<exists>\<^sub>F z in at z. automorphy_factor g z powi weight \<noteq> 0"
      by (intro eventually_frequently) auto
  next
    show "\<exists>\<^sub>F z in at z. eval_mero_uhp f z \<noteq> 0"
      by (intro eventually_frequently ev_nz) auto
  qed (use \<open>Im z > 0\<close> in \<open>auto intro!: meromorphic_intros\<close>)
  also have "zorder (\<lambda>w. automorphy_factor g w powi weight) z = 0"
    by (intro zorder_eq_0I analytic_intros) (use \<open>Im z > 0\<close> in auto)
  also have "zorder (\<lambda>w. automorphy_factor g w powi weight * eval_mero_uhp f w) z =
             zorder (eval_mero_uhp f \<circ> apply_modgrp g) z"
    using g by (simp add: o_def)
  also have "\<dots> = zorder_mero_uhp f (apply_modgrp g z) * zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z"
  proof (rule zorder_compose')
    show "\<forall>\<^sub>F w in at (apply_modgrp g z). eval_mero_uhp f w \<noteq> 0"
      using z eventually_eval_mero_uhp_neq_iff[of "apply_modgrp g z" f 0] \<open>f \<noteq> 0\<close> by auto
  qed (use z ev_nz' in \<open>auto intro!: meromorphic_on_isolated_singularity meromorphic_on_not_essential
                          meromorphic_intros analytic_intros\<close>)
  also have "zorder (\<lambda>x. apply_modgrp g x - apply_modgrp g z) z = 1"
    by (intro zorder_apply_modgrp) (use g in auto)
  finally show ?thesis
    using g by simp
qed

lemma zorder_apply_modgrp:
  assumes "h \<in> G" "Im z > 0"
  shows   "zorder f (apply_modgrp h z) = zorder f z"
  by (intro rel_imp_zorder_eq) (use assms in auto)

lemma rel_imp_is_pole_iff:
  assumes "rel z z'"
  shows   "is_pole f z \<longleftrightarrow> is_pole f z'"
  using assms unfolding rel_def by auto

lemma deriv_apply_modgrp:
  fixes h :: modgrp
  assumes h: "h \<in> G"
  assumes z: "Im z > 0" "\<not>is_pole f z"
  defines "c \<equiv> complex_of_int (modgrp_c h)"
  defines "T \<equiv> automorphy_factor h"
  shows "deriv f (apply_modgrp h z) = 
           T z powi (weight + 2) * (deriv f z + of_int weight * (c / T z) * f z)"
proof -
  note [simp del] = div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1
  note [derivative_intros del] = 
    has_field_derivative_deriv_mero_uhp has_field_derivative_deriv_mero_uhp'
  have [simp]: "T z \<noteq> 0"
    using z by (auto simp: T_def)

  have "f nicely_meromorphic_on {z}" "f nicely_meromorphic_on {apply_modgrp h z}"
    by (rule eval_mero_uhp_nicely_meromorphic; use z in simp; fail)+
  with z h have ana: "f analytic_on {z}" "f analytic_on {apply_modgrp h z}"
    by (simp_all add: nicely_meromorphic_on_imp_analytic_at)
  have [derivative_intros]: "(eval_mero_uhp f has_field_derivative deriv f z) (at z)"
    using z by (intro analytic_derivI ana)

  have "((f \<circ> apply_modgrp h) has_field_derivative 
          (deriv f (apply_modgrp h z) * (1 / T z ^ 2))) (at z)"
    unfolding T_def by (intro DERIV_chain derivative_intros analytic_derivI ana) (use z in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>z. f z * T z powi weight)
                has_field_derivative (deriv f (apply_modgrp h z) / T z ^ 2)) (at z)"
  proof (intro DERIV_cong_ev refl)
    have "eventually (\<lambda>w. w \<in> {w. Im w > 0}) (nhds z)"
      by (rule eventually_nhds_in_open) (use z in \<open>auto simp: open_halfspace_Im_gt\<close>)
    thus "eventually (\<lambda>w. (eval_mero_uhp f \<circ> apply_modgrp h) w =
             eval_mero_uhp f w * T w powi weight) (nhds z)"
    proof eventually_elim
      case (elim w)
      show ?case
        using elim h by (auto simp: invariant_apply_modgrp T_def)
    qed
  qed auto
  finally have 1: "((\<lambda>z. f z * T z powi weight)
                  has_field_derivative (deriv f (apply_modgrp h z) / T z ^ 2)) (at z)" .
  moreover have 2: "((\<lambda>z. f z * T z powi weight) has_field_derivative 
                    (deriv f z * T z powi weight + of_int weight * c * T z powi (weight - 1) * f z)) (at z)"
    using z by (auto intro!: derivative_eq_intros analytic_derivI[of f] simp: c_def T_def)
  ultimately show "deriv f (apply_modgrp h z) = 
                     T z powi (weight + 2) * (deriv f z + of_int weight * (c / T z) * f z)"
    using DERIV_unique[OF 1 2] z
    by (simp add: field_simps power_int_diff power_int_add power2_eq_square)
qed

lemma weakly_meromorphic_form_conj:
  "weakly_meromorphic_form (slash_mero_uhp weight h f) weight (conj_modgrp h G)"
proof -
  interpret conj: cong_subgroup "conj_modgrp h G"
    by (rule cong_subgroup_conj)
  show ?thesis
  proof
    fix g' assume "g' \<in> conj_modgrp h G"
    then obtain g where g: "g \<in> G" "g' = inverse h * g * h"
      by (auto simp: conj_modgrp_def)
    have "slash_mero_uhp weight g' (slash_mero_uhp weight h f) = 
            slash_mero_uhp weight h (slash_mero_uhp weight g f)"
      by (simp add: g mult.assoc flip: slash_mero_uhp_mult)
    also have "slash_mero_uhp weight g f = f"
      by (rule invariant_slash_modgrp) fact
    finally show "slash_mero_uhp weight g' (slash_mero_uhp weight h f) = slash_mero_uhp weight h f" .
  qed
qed

lemma weakly_meromorphic_form_minus [intro]: "weakly_meromorphic_form (-f) weight G"
  by standard (simp_all add: hom_distribs invariant_slash_modgrp)

lemma weakly_meromorphic_form_power [intro]: "weakly_meromorphic_form (f ^ n) (n * weight) G"
  by standard (simp_all add: hom_distribs invariant_slash_modgrp flip: slash_mero_uhp_power)

lemma weakly_meromorphic_form_power_int [intro]: "weakly_meromorphic_form (f powi n) (n * weight) G"
  by standard (simp_all add: hom_distribs invariant_slash_modgrp flip: slash_mero_uhp_power_int)

lemma weakly_meromorphic_form_inverse [intro]: "weakly_meromorphic_form (inverse f) (-weight) G"
  by standard 
     (cases "f = 0", simp_all add: hom_distribs invariant_slash_modgrp flip: slash_mero_uhp_inverse)

end


text \<open>
  We show the usual closure properties for weakly modular forms w.r.t.\ algebraic operations.
\<close>

lemma (in cong_subgroup) weakly_meromorphic_form_0 [intro]:
  "weakly_meromorphic_form 0 weight G"
  by unfold_locales auto

lemma (in cong_subgroup) weakly_meromorphic_form_const [intro]:
  "weakly_meromorphic_form (const_mero_uhp c) 0 G"
  by unfold_locales auto

lemma (in cong_subgroup) weakly_meromorphic_form_1 [intro]:
  "weakly_meromorphic_form 1 0 G"
  by unfold_locales auto


locale weakly_meromorphic_form_weight_0 = weakly_meromorphic_form f 0 G
  for f G
begin

lemma rel_imp_eval_eq:
  assumes "rel z z'"
  shows   "eval_mero_uhp f z = eval_mero_uhp f z'"
  using assms unfolding rel_def by auto

end


locale weakly_meromorphic_form_pair =
  f: weakly_meromorphic_form f weight G + g: weakly_meromorphic_form g weight' G
  for f g weight weight' G
begin

lemma weakly_meromorphic_form_add [intro]:
  "weight = weight' \<Longrightarrow> weakly_meromorphic_form (f + g) weight G"
  by standard (use f.invariant_slash_modgrp g.invariant_slash_modgrp in \<open>simp_all add: hom_distribs\<close>)

lemma weakly_meromorphic_form_diff [intro]:
  "weight = weight' \<Longrightarrow> weakly_meromorphic_form (f - g) weight G"
  by standard (use f.invariant_slash_modgrp g.invariant_slash_modgrp in \<open>simp_all add: hom_distribs\<close>)

lemma weakly_meromorphic_form_mult [intro]: "weakly_meromorphic_form (f * g) (weight + weight') G"
  by standard (use f.invariant_slash_modgrp g.invariant_slash_modgrp
       slash_mero_uhp_mult_right[of weight _ f weight' g, symmetric] in \<open>simp_all add: hom_distribs\<close>)

lemma weakly_meromorphic_form_divide [intro]: "weakly_meromorphic_form (f / g) (weight - weight') G"
  by standard (use f.invariant_slash_modgrp g.invariant_slash_modgrp
       slash_mero_uhp_divide[of weight _ f weight' g, symmetric] in \<open>simp_all add: hom_distribs\<close>)

end


text \<open>
  If the subgroup in question is in fact the full modular group, the following characterisation
  allows us to prove weak modularity more easily by only looking at the two generators $S$ and
  $T$ of the modular group.
\<close>
lemma weakly_meromorphic_formI_generators:
  fixes f :: mero_uhp and g :: "complex \<Rightarrow> complex"
  assumes k: "even k"
  assumes [mero_uhp_rel_intros]: "mero_uhp_rel f g"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> g (z + 1) = g z"
  assumes "\<And>z. Im z > 0 \<Longrightarrow> g (-(1/z)) = z powi k * g z"
  shows   "weakly_meromorphic_form f k UNIV"
proof
  fix h :: modgrp
  write automorphy_factor ("j")
  show "slash_mero_uhp k h f = f"
  proof (induction h rule: modgrp_induct')
    case id
    thus ?case using k by auto
  next
    case (S h)
    have "mero_uhp_rel (slash_mero_uhp k S_modgrp f) 
            (\<lambda>z. j S_modgrp z powi -k * g (apply_modgrp S_modgrp z))"
      by mero_uhp_rel
    also have "mero_uhp_rel \<dots> g"
      by (rule mero_uhp_relI_weak) (use assms in \<open>auto simp: power_int_minus field_simps\<close>)
    also have "mero_uhp_rel g f"
      by mero_uhp_rel
    finally have *: "slash_mero_uhp k S_modgrp f = f"
      by (rule mero_uhp_rel_imp_eq_mero_uhp)
    show ?case
      by (auto simp: slash_mero_uhp_mult k S *)
  next
    case (T h)
    have "mero_uhp_rel (slash_mero_uhp k T_modgrp f) 
            (\<lambda>z. j T_modgrp z powi -k * g (apply_modgrp T_modgrp z))"
      by mero_uhp_rel
    also have "mero_uhp_rel \<dots> g"
      by (rule mero_uhp_relI_weak) (use assms in \<open>auto simp: power_int_minus field_simps\<close>)
    also have "mero_uhp_rel g f"
      by mero_uhp_rel
    finally have *: "slash_mero_uhp k T_modgrp f = f"
      by (rule mero_uhp_rel_imp_eq_mero_uhp)
    show ?case
      by (auto simp: slash_mero_uhp_mult k * T)
  next
    case (inv_T h)
    have shift: "g (z - 1) = g z" if "Im z > 0" for z
      using assms(3)[of "z - 1"] that by auto
    have eq: "inverse T_modgrp = shift_modgrp (-1)"
      by (simp add: shift_modgrp_1 shift_modgrp_minus)
    have "mero_uhp_rel (slash_mero_uhp k (inverse T_modgrp) f) 
            (\<lambda>z. j (inverse T_modgrp) z powi -k * g (apply_modgrp (inverse T_modgrp) z))"
      by mero_uhp_rel
    also have "mero_uhp_rel \<dots> g"
      by (rule mero_uhp_relI_weak) (auto simp: power_int_minus field_simps eq shift)
    also have "mero_uhp_rel g f"
      by mero_uhp_rel
    finally have *: "slash_mero_uhp k (inverse T_modgrp) f = f"
      by (rule mero_uhp_rel_imp_eq_mero_uhp)
    show ?case
      by (auto simp: slash_mero_uhp_mult k * inv_T)
  qed (use \<open>even k\<close> in auto)
qed


definition WMForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("WMForms[_,_]") where
  "WMForms G k = {f. weakly_meromorphic_form f k G}"

abbreviation WMForms' :: "int \<Rightarrow> mero_uhp set" ("WMForms[_]") where
  "WMForms' \<equiv> WMForms UNIV"

lemma weakly_meromorphic_form_WMForms [dest]:
  "f \<in> WMForms[G, k] \<Longrightarrow> weakly_meromorphic_form f k G"
  by (auto simp: WMForms_def)

context
  fixes G
  assumes G: "cong_subgroup G"
begin

interpretation cong_subgroup G
  by (rule G)

lemma WMForms_0 [mform_intros, simp, intro]: "0 \<in> WMForms[G, k]"
  by (auto simp: WMForms_def)

lemma WMForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> WMForms[G, 0]"
  by (auto simp: WMForms_def)

lemma WMForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> WMForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma WMForms_1 [mform_intros, simp, intro]: "1 \<in> WMForms[G, 0]"
  and WMForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> WMForms[G, 0]"
  and WMForms_of_int [mform_intros, simp, intro]: "of_int m \<in> WMForms[G, 0]"
  and WMForms_of_real [mform_intros, simp, intro]: "of_real x \<in> WMForms[G, 0]"
  and WMForms_numeral [mform_intros, simp, intro]: "numeral num \<in> WMForms[G, 0]"
  by (rule WMForms_is_const; simp; fail)+

lemma WMForms_uminus [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> -f \<in> WMForms[G, k]"
  by (auto simp: WMForms_def intro!: weakly_meromorphic_form.weakly_meromorphic_form_minus
         weakly_meromorphic_form.weakly_meromorphic_form_inverse)

lemma WMForms_add [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, k] \<Longrightarrow> f + g \<in> WMForms[G, k]"
  by (auto simp: WMForms_def weakly_meromorphic_form_pair_def
           intro!: weakly_meromorphic_form_pair.weakly_meromorphic_form_add)

lemma WMForms_diff [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, k] \<Longrightarrow> f - g \<in> WMForms[G, k]"
  by (auto simp: WMForms_def weakly_meromorphic_form_pair_def
           intro!: weakly_meromorphic_form_pair.weakly_meromorphic_form_diff)

lemma WMForms_mult [mform_intros]:
  "f \<in> WMForms[G, k] \<Longrightarrow> g \<in> WMForms[G, m - k] \<Longrightarrow> f * g \<in> WMForms[G, m]"
  using weakly_meromorphic_form_pair.weakly_meromorphic_form_mult[of f g k "m - k"]
  by (auto simp: WMForms_def weakly_meromorphic_form_pair_def)

lemma WMForms_inverse [mform_intros]:
  assumes "f \<in> WMForms[G, m]" "f \<noteq> 0" "m = -l"
  shows   "inverse f \<in> WMForms[G, l]"
  using weakly_meromorphic_form.weakly_meromorphic_form_inverse[of f m G] assms
  by (auto simp: WMForms_def)

lemma WMForms_divide [mform_intros]:
  assumes "f \<in> WMForms[G, k]" "g \<in> WMForms[G, k-m]" "g \<noteq> 0"
  shows   "f / g \<in> WMForms[G, m]"
  using weakly_meromorphic_form_pair.weakly_meromorphic_form_divide[of f g k "k - m"] assms
  by (auto simp: WMForms_def weakly_meromorphic_form_pair_def)

lemma WMForms_power [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f ^ n \<in> WMForms[G, m]"
  using weakly_meromorphic_form.weakly_meromorphic_form_power[of f k G n] by (auto simp: WMForms_def)

lemma WMForms_power_int [mform_intros]: "f \<in> WMForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f powi n \<in> WMForms[G, m]"
  using weakly_meromorphic_form.weakly_meromorphic_form_power_int[of f k G n] by (auto simp: WMForms_def)
   
lemma WMForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> WMForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> WMForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros)

lemma WMForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> WMForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> WMForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros)

end



subsection \<open>Meromorphic forms\<close>

text \<open>
  A \<^emph>\<open>meromorphic form\<close> of weight $k$ and level $G$ is a weakly meromorphic form that is 
  additionally meromorphic at all cusps. The ``main'' cusp is located at infinity, and
  meromorphicity at infinity is defined as  meromorphicity of the corresponding Fourier 
  expansion at $q = 0$.

  The other cusps are located at the rational numbers, and the easiest way to define
  meromorphicity at them is to map them to infinity via some unimodular transformation $h$
  and then demand that the transformed form be meromorphic at infinity.
  We simply demand that this work for \<^emph>\<open>all\<close> unimodular transformations $h$, so that we are
  sure to cover all the cusps. In practice it is enough to check one representative per coset 
  of $G$ (of which there are typically finitely many).

  When looking at the Fourier expansion, note that our subgroup only contains \<^emph>\<open>some\<close> shift 
  operator $T^n$ but not necessarily the `shift by 1' operator $T$, the `normal' $q$-expansion 
  w.r.t.\ $q = \exp(2i\pi)$ may not work. We therefore expand w.r.t.\ the smallest positive $n$ 
  such that $T^n\in G$. This is called the \<^emph>\<open>cusp width\<close> of $G$ (at infinity).

  Note that the cusp width may be different at every cusp, since the conjugated group does not
  necessarily contain the same shift operators as the original one.
\<close>


unbundle modfun_region_notation

locale meromorphic_form = weakly_meromorphic_form +
  assumes meromorphic_at_cusps:
    "\<And>h::modgrp. meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp weight h f)"
begin

sublocale fourier_expansion_meromorphic "cusp_width\<^sub>\<infinity> G" f
proof
  show "fourier_expansion (cusp_width\<^sub>\<infinity> G) f meromorphic_on {0}"
    using meromorphic_at_cusps[of 1] by (simp add: meromorphic_at_infinity_def)
qed

lemma rel_imp_eval_eq_0_iff: "rel z z' \<Longrightarrow> f z = 0 \<longleftrightarrow> f z' = 0"
  by (auto simp: rel_def)

lemma eventually_no_poles_at_ii_inf: "eventually (\<lambda>z. \<not>is_pole f z) at_\<i>\<infinity>"
  by (metis (mono_tags, lifting) const_mero_uhp.hom_zero eval_mero_uhp_pole eventually_at_ii_inf_iff
        eventually_neq_at_ii_inf not_pole_0_mero_uhp)

lemma meromorphic_form_conj:
  "meromorphic_form (slash_mero_uhp weight h f) weight (conj_modgrp h G)"
proof -
  interpret conj: weakly_meromorphic_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
    by (rule weakly_meromorphic_form_conj)
  show ?thesis
  proof
    fix h' :: modgrp
    show "meromorphic_at_infinity (conj_modgrp h' (conj_modgrp h G))
            (slash_mero_uhp weight h' (slash_mero_uhp weight h f))"
      using meromorphic_at_cusps[of "h * h'"] by (simp add: conj_modgrp_mult slash_mero_uhp_mult)
  qed
qed

lemma finite_inv_image_mero_uhp:
  assumes "f \<noteq> const_mero_uhp c"
  shows   "finite (inv_image_mero_uhp f c)"
proof -
  have "eventually (\<lambda>z. f z \<noteq> c) at_\<i>\<infinity>"
    by (rule eventually_neq_at_ii_inf) fact
  then obtain y where y: "\<And>z. Im z > y \<Longrightarrow> f z \<noteq> c"
    by (auto simp: eventually_at_ii_inf_iff)
  define R where "R = closure \<R>\<^sub>\<Gamma> \<inter> {z. Im z \<le> y}"
  have "closed R"
    unfolding R_def by (auto intro!: closed_Int closed_halfspace_Im_le)
  moreover have "bounded R"
  proof -
    have "R \<subseteq> cbox (-1) (1 + \<i> * y)"
      by (auto simp: R_def in_closure_std_fund_region_iff in_cbox_complex_iff)
    moreover have "bounded \<dots>"
      by auto
    ultimately show "bounded R"
      using bounded_subset by blast
  qed
  ultimately have "compact R"
    using compact_eq_bounded_closed by blast

  have "\<forall>\<^sub>\<approx>z\<in>\<H>. f z \<noteq> c"
    by (rule eval_mero_uhp_avoid) fact
  hence "{z. f z = c} sparse_in \<H>"
    by (simp add: eventually_cosparse)
  hence "{z. f z = c} sparse_in R"
    by (rule sparse_in_subset) (use closure_std_fund_region_Im_pos in \<open>auto simp: R_def\<close>)
  from this and \<open>compact R\<close> have fin: "finite (R \<inter> {z. f z = c})"
    by (rule sparse_in_compact_finite)
  have "finite (\<R>\<^sub>\<Gamma>' \<inter> {z. \<not>is_pole f z \<and> f z = c})"
    by (rule finite_subset[OF _ fin]) (use std_fund_region'_subset y in \<open>force simp: R_def\<close>)
  also have "\<R>\<^sub>\<Gamma>' \<inter> {z. \<not>is_pole f z \<and> f z = c} = inv_image_mero_uhp f c"
    unfolding inv_image_mero_uhp_def by blast
  finally show ?thesis .
qed    

lemma finite_zeros_mero_uhp [intro]:
  assumes "f \<noteq> 0"
  shows   "finite (zeros_mero_uhp f)"
  using finite_inv_image_mero_uhp[of 0] assms by simp

lemma meromorphic_at_cusps':
  fixes h :: modgrp
  defines "k \<equiv> cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
  shows "fourier_expansion_meromorphic k (slash_mero_uhp weight h f)"
proof -
  define f' where "f' = slash_mero_uhp weight h f"
  interpret conj: weakly_meromorphic_form f' weight "conj_modgrp h G"
    unfolding f'_def by (rule weakly_meromorphic_form_conj)
  show "fourier_expansion_meromorphic k f'"
  proof
    show "k > 0"
      unfolding k_def by (rule conj.cusp_width_at_ii_inf_pos)
  next
    have "compose_modgrp_mero_uhp f' (shift_modgrp k) = 
            slash_mero_uhp weight (shift_modgrp k) f'"
      by (simp add: slash_mero_uhp_mult slash_mero_uhp_shift)
    also have "\<dots> = f'"
      by (rule conj.invariant_slash_modgrp) (auto simp: k_def)
    finally show "compose_modgrp_mero_uhp f' (shift_modgrp (int k)) = f'" .
  next
    show "fourier_expansion k f' meromorphic_on {0}"
      using meromorphic_at_cusps[of h] by (auto simp: meromorphic_at_infinity_def k_def f'_def)
  qed
qed

sublocale fourier_expansion_meromorphic "cusp_width\<^sub>\<infinity> G" f
  using meromorphic_at_cusps'[of 1] by simp

lemma meromorphic_form_minus: "meromorphic_form (-f) weight G"
proof -
  interpret A: weakly_meromorphic_form "-f" weight G
    by (rule weakly_meromorphic_form_minus)
  show ?thesis
  proof
    fix h :: modgrp
    define k where "k = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
    interpret B: fourier_expansion_meromorphic k "slash_mero_uhp weight h f"
      unfolding k_def by (rule meromorphic_at_cusps')
    interpret C: fourier_expansion_meromorphic k "-slash_mero_uhp weight h f"
      by (rule B.fourier_expansion_meromorphic_minus)
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp weight h (-f))"
      using C.fourier_meromorphic_at_0 unfolding meromorphic_at_infinity_def k_def
      by (simp add: hom_distribs)
  qed
qed

lemma meromorphic_form_power_int: "meromorphic_form (f powi n) (n * weight) G"
proof -
  interpret A: weakly_meromorphic_form "f powi n" "n * weight" G
    by (rule weakly_meromorphic_form_power_int)
  show ?thesis
  proof
    fix h :: modgrp
    define k where "k = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
    interpret B: fourier_expansion_meromorphic k "slash_mero_uhp weight h f"
      unfolding k_def by (rule meromorphic_at_cusps')
    interpret C: fourier_expansion_meromorphic k "slash_mero_uhp weight h f powi n"
      by (rule B.fourier_expansion_meromorphic_power_int)
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp (n * weight) h (f powi n))"
      using C.fourier_meromorphic_at_0 unfolding meromorphic_at_infinity_def k_def
      by (simp add: slash_mero_uhp_power_int)
  qed
qed

lemma meromorphic_form_power: "meromorphic_form (f ^ n) (n * weight) G"
  using meromorphic_form_power_int[of "int n"] by simp

lemma meromorphic_form_inverse: "meromorphic_form (inverse f) (-weight) G"
  using meromorphic_form_power_int[of "-1"] by simp

end


lemma (in cong_subgroup) meromorphic_form_0:
  "meromorphic_form 0 weight G"
proof -
  show ?thesis
  proof
    fix h :: modgrp
    interpret conj: cong_subgroup "conj_modgrp h G"
      by (rule cong_subgroup_conj)
    interpret conj: fourier_expansion_context "cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
      by standard (auto simp: conj.cusp_width_at_ii_inf_pos)
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp weight h 0)"
      using conj.const.fourier_meromorphic_at_0[of 0] by (auto simp: meromorphic_at_infinity_def)
  qed auto
qed

lemma (in cong_subgroup) meromorphic_form_const: "meromorphic_form (const_mero_uhp c) 0 G"
proof -
  show ?thesis
  proof
    fix h :: modgrp
    interpret conj: cong_subgroup "conj_modgrp h G"
      by (rule cong_subgroup_conj)
    interpret conj: fourier_expansion_context "cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
      by standard (auto simp: conj.cusp_width_at_ii_inf_pos)
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp 0 h \<langle>c\<rangle>)"
      using conj.const.fourier_meromorphic_at_0[of c] by (auto simp: meromorphic_at_infinity_def)
  qed auto
qed

lemma (in cong_subgroup) meromorphic_form_1: "meromorphic_form 1 0 G"
  using meromorphic_form_const[of 1] by simp

lemmas meromorphic_form_minus = meromorphic_form.meromorphic_form_minus
lemmas meromorphic_form_power = meromorphic_form.meromorphic_form_power
lemmas meromorphic_form_power_int = meromorphic_form.meromorphic_form_power_int
lemmas meromorphic_form_inverse = meromorphic_form.meromorphic_form_inverse

lemma meromorphic_form_add:
  assumes "meromorphic_form f weight G"
  assumes "meromorphic_form g weight G"
  shows   "meromorphic_form (f + g) weight G"
proof -
  interpret f: meromorphic_form f weight G by fact
  interpret g: meromorphic_form g weight G by fact
  interpret fg: weakly_meromorphic_form_pair f g weight weight G ..
  interpret sum: weakly_meromorphic_form "f + g" weight G
    by (rule fg.weakly_meromorphic_form_add) auto

  show ?thesis
  proof
    fix h :: modgrp
    define k where "k = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
    interpret fs: fourier_expansion_meromorphic k "slash_mero_uhp weight h f"
      unfolding k_def by (rule f.meromorphic_at_cusps')
    interpret gs: fourier_expansion_meromorphic k "slash_mero_uhp weight h g"
      unfolding k_def by (rule g.meromorphic_at_cusps')
    interpret ctxt: fourier_expansion_context k
      by standard (use fs.period_pos in auto)
    interpret fgs: fourier_expansion_meromorphic_pair k 
      "slash_mero_uhp weight h f" "slash_mero_uhp weight h g" ..
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp weight h (f + g))"
      using fgs.add.fourier_meromorphic_at_0 unfolding meromorphic_at_infinity_def k_def
      by (simp add: hom_distribs)
  qed
qed

lemma meromorphic_form_diff:
  assumes "meromorphic_form f weight G"
  assumes "meromorphic_form g weight G"
  shows   "meromorphic_form (f - g) weight G"
  using meromorphic_form_add[OF assms(1) meromorphic_form_minus[OF assms(2)]] by simp

lemma meromorphic_form_mult:
  assumes "meromorphic_form f weight1 G"
  assumes "meromorphic_form g weight2 G"
  shows   "meromorphic_form (f * g) (weight1 + weight2) G"
proof -
  interpret f: meromorphic_form f weight1 G by fact
  interpret g: meromorphic_form g weight2 G by fact
  interpret fg: weakly_meromorphic_form_pair f g weight1 weight2 G ..
  interpret prod: weakly_meromorphic_form "f * g" "weight1 + weight2" G
    by (rule fg.weakly_meromorphic_form_mult)

  show ?thesis
  proof
    fix h :: modgrp
    define k where "k = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"
    interpret fs: fourier_expansion_meromorphic k "slash_mero_uhp weight1 h f"
      unfolding k_def by (rule f.meromorphic_at_cusps')
    interpret gs: fourier_expansion_meromorphic k "slash_mero_uhp weight2 h g"
      unfolding k_def by (rule g.meromorphic_at_cusps')
    interpret ctxt: fourier_expansion_context k
      by standard (use fs.period_pos in auto)
    interpret fgs: fourier_expansion_meromorphic_pair k 
      "slash_mero_uhp weight1 h f" "slash_mero_uhp weight2 h g" ..
    show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp (weight1 + weight2) h (f * g))"
      using fgs.mult.fourier_meromorphic_at_0 unfolding meromorphic_at_infinity_def k_def
      by (simp add: slash_mero_uhp_mult_right)
  qed
qed

lemma meromorphic_form_divide:
  assumes "meromorphic_form f weight1 G"
  assumes "meromorphic_form g weight2 G"
  shows   "meromorphic_form (f / g) (weight1 - weight2) G"
  using meromorphic_form_mult[OF assms(1) meromorphic_form_inverse[OF assms(2)]]
  by (simp add: field_simps)

lemma (in cong_subgroup) meromorphic_form_sum:
  assumes "\<And>x. x \<in> A \<Longrightarrow> meromorphic_form (f x) weight G"
  shows   "meromorphic_form (\<Sum>x\<in>A. f x) weight G"
  using assms
  by (induction A rule: infinite_finite_induct)
     (auto intro!: meromorphic_form_add meromorphic_form_0)

lemma (in cong_subgroup) meromorphic_form_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> meromorphic_form (f x) (weight x) G"
  shows   "meromorphic_form (\<Prod>x\<in>A. f x) (\<Sum>x\<in>A. weight x) G"
  using assms
  by (induction A rule: infinite_finite_induct)
     (auto intro!: meromorphic_form_mult meromorphic_form_1)

lemma (in cong_subgroup) meromorphic_form_sum_list:
  assumes "\<And>f. f \<in> set fs \<Longrightarrow> meromorphic_form f weight G"
  shows   "meromorphic_form (sum_list fs) weight G"
  using assms by (induction fs) (auto intro!: meromorphic_form_add meromorphic_form_0)

lemma (in cong_subgroup) meromorphic_form_prod_list:
  assumes "list_all2 (\<lambda>f weight. meromorphic_form f weight G) fs weights"
  shows   "meromorphic_form (prod_list fs) (sum_list weights) G"
  using assms by induction (auto intro!: meromorphic_form_mult meromorphic_form_1)

lemma (in cong_subgroup) meromorphic_form_sum_mset:
  assumes "\<And>f. f \<in># fs \<Longrightarrow> meromorphic_form f weight G"
  shows   "meromorphic_form (sum_mset fs) weight G"
  using assms by (induction fs) (auto intro!: meromorphic_form_add meromorphic_form_0)



lemma (in meromorphic_form) finite_poles_mero_uhp [intro]: "finite (poles_mero_uhp f)"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  interpret inv: meromorphic_form "inverse f" "-weight" G
    by (rule meromorphic_form_inverse)
  have "finite (zeros_mero_uhp (inverse f))"
    using \<open>f \<noteq> 0\<close> by (intro inv.finite_zeros_mero_uhp) auto
  also have "zeros_mero_uhp (inverse f) = poles_mero_uhp f"
    using \<open>f \<noteq> 0\<close> by (simp add: zeros_mero_uhp_inverse)
  finally show ?thesis .  
qed auto


locale meromorphic_form_full = 
  fixes f :: mero_uhp and weight :: int
  assumes meromorphic_form_UNIV: "meromorphic_form f weight UNIV"
begin

sublocale meromorphic_form f weight UNIV
  rewrites "cusp_width\<^sub>\<infinity> UNIV = Suc 0"
  using meromorphic_form_UNIV by auto

end

(* TODO: intro rule collection? *)



locale modular_function = meromorphic_form f 0 G
  for f :: mero_uhp and G :: "modgrp set"
begin

sublocale weakly_meromorphic_form_weight_0 ..

lemmas [simp del] = invariant_apply_modgrp

lemma invariant_apply_modgrp' [simp]:
  assumes "h \<in> G"
  shows   "eval_mero_uhp f (apply_modgrp h z) = eval_mero_uhp f z"
proof (cases "z = 0")
  case False
  thus ?thesis using assms
    by (simp add: invariant_apply_modgrp)
qed (auto simp: eval_mero_uhp_outside) 

lemma modular_function_minus [intro]: "modular_function (-f) G"
  unfolding modular_function_def using meromorphic_form_minus by simp

lemma modular_function_inverse [intro]: "modular_function (inverse f) G"
  unfolding modular_function_def using meromorphic_form_inverse by simp

lemma modular_function_power [intro]: "modular_function (f ^ n) G"
  unfolding modular_function_def using meromorphic_form_power[of n] by simp

lemma modular_function_power_int [intro]: "modular_function (f powi n) G"
  unfolding modular_function_def using meromorphic_form_power_int[of n] by simp

end


context cong_subgroup
begin

lemma modular_function_0 [intro]: "modular_function 0 G"
  unfolding modular_function_def by (rule meromorphic_form_0)

lemma modular_function_1 [intro]: "modular_function 1 G"
  unfolding modular_function_def by (rule meromorphic_form_1)

lemma modular_function_const [intro]: "modular_function (const_mero_uhp c) G"
  unfolding modular_function_def by (rule meromorphic_form_const)

end


context
  fixes f g G
  assumes f: "modular_function f G"
  assumes g: "modular_function g G"
begin

lemma modular_function_add [intro]: "modular_function (f + g) G"
  using meromorphic_form_add[of f 0 G g] f g unfolding modular_function_def by simp

lemma modular_function_diff [intro]: "modular_function (f - g) G"
  using meromorphic_form_diff[of f 0 G g] f g unfolding modular_function_def by simp

lemma modular_function_mult [intro]: "modular_function (f * g) G"
  using meromorphic_form_mult[of f 0 G g 0] f g unfolding modular_function_def by simp

lemma modular_function_divide [intro]: "modular_function (f / g) G"
  using meromorphic_form_divide[of f 0 G g 0] f g unfolding modular_function_def by simp

end

(* TODO: sum, sum_list, etc. *)


definition MeForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("MeForms[_,_]") where
  "MeForms G k = {f. meromorphic_form f k G}"

abbreviation MeForms' :: "int \<Rightarrow> mero_uhp set" ("MeForms[_]") where
  "MeForms' \<equiv> MeForms UNIV"

lemma meromorphic_form_MeForms [dest]: "f \<in> MeForms[G, k] \<Longrightarrow> meromorphic_form f k G"
  by (auto simp: MeForms_def)

lemma MeForms_has_laurent_expansion_at_ii_inf:
  assumes "f \<in> MeForms[G, k]"
  shows   "f has_laurent_expansion_at_\<i>\<infinity>[cusp_width\<^sub>\<infinity> G] laurent_expansion_at_\<i>\<infinity> (cusp_width\<^sub>\<infinity> G) f"
proof -
  interpret meromorphic_form f k G
    using assms by auto
  show ?thesis
    by (rule has_laurent_expansion_at_ii_inf)
qed

lemma MeForms_UNIV_has_laurent_expansion_at_ii_inf:
  assumes "f \<in> MeForms[k]"
  shows   "f has_laurent_expansion_at_\<i>\<infinity> laurent_expansion_at_\<i>\<infinity> (Suc 0) f"
  using MeForms_has_laurent_expansion_at_ii_inf[OF assms] by simp

context
  fixes G
  assumes G: "cong_subgroup G"
begin

interpretation cong_subgroup G
  by (fact G)

lemma MeForms_0 [mform_intros, simp, intro]: "0 \<in> MeForms[G, k]"
  by (auto simp: MeForms_def meromorphic_form_0)

lemma MeForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> MeForms[G, 0]"
  by (auto simp: MeForms_def meromorphic_form_const)

lemma MeForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> MeForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma MeForms_1 [mform_intros, simp, intro]: "1 \<in> MeForms[G, 0]"
  and MeForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> MeForms[G, 0]"
  and MeForms_of_int [mform_intros, simp, intro]: "of_int m \<in> MeForms[G, 0]"
  and MeForms_of_real [mform_intros, simp, intro]: "of_real x \<in> MeForms[G, 0]"
  and MeForms_numeral [mform_intros, simp, intro]: "numeral num \<in> MeForms[G, 0]"
  by (rule MeForms_is_const; simp; fail)+

end

lemma MeForms_uminus [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> -f \<in> MeForms[G, k]"
  by (auto simp: MeForms_def intro!: meromorphic_form.meromorphic_form_minus
         meromorphic_form.meromorphic_form_inverse)

lemma MeForms_add [mform_intros]:
  "f \<in> MeForms[G, k] \<Longrightarrow> g \<in> MeForms[G, k] \<Longrightarrow> f + g \<in> MeForms[G, k]"
  by (auto simp: MeForms_def intro!: meromorphic_form_add)

lemma MeForms_diff [mform_intros]:
  "f \<in> MeForms[G, k] \<Longrightarrow> g \<in> MeForms[G, k] \<Longrightarrow> f - g \<in> MeForms[G, k]"
  by (auto simp: MeForms_def intro!: meromorphic_form_diff)

lemma MeForms_mult [mform_intros]:
  "f \<in> MeForms[G, k1] \<Longrightarrow> g \<in> MeForms[G, k2] \<Longrightarrow> k = k1 + k2 \<Longrightarrow> f * g \<in> MeForms[G, k]"
  by (auto simp: MeForms_def intro!: meromorphic_form_mult)

lemma MeForms_inverse [mform_intros]:
  assumes "f \<in> MeForms[G, m]" "f \<noteq> 0" "m = -l"
  shows   "inverse f \<in> MeForms[G, l]"
  using meromorphic_form.meromorphic_form_inverse[of f m G] assms
  by (auto simp: MeForms_def)

lemma MeForms_divide [mform_intros]:
  assumes "f \<in> MeForms[G, k1]" "g \<in> MeForms[G, k2]" "m = k1 - k2"
  shows   "f / g \<in> MeForms[G, m]"
  unfolding assms(3) using assms(1,2) by (auto simp: MeForms_def intro!: meromorphic_form_divide)

lemma MeForms_power [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f ^ n \<in> MeForms[G, m]"
  using meromorphic_form.meromorphic_form_power[of f k G n] by (auto simp: MeForms_def)

lemma MeForms_power_int [mform_intros]: "f \<in> MeForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f powi n \<in> MeForms[G, m]"
  using meromorphic_form.meromorphic_form_power_int[of f k G n] by (auto simp: MeForms_def)


context
  fixes G
  assumes G: "cong_subgroup G"
begin

lemma MeForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MeForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> MeForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros G)

lemma MeForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MeForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> MeForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros G)

(* TODO *)

end


abbreviation MFuns :: "modgrp set \<Rightarrow> mero_uhp set" ("MFuns[_]") where
  "MFuns G \<equiv> MeForms G 0"

abbreviation MFuns' :: "mero_uhp set" ("MFuns") where
  "MFuns' \<equiv> MFuns[UNIV]"

lemma MFuns_altdef: "MFuns[G] = {f. modular_function f G}"
  by (simp add: MeForms_def modular_function_def)

lemma modular_function_MFuns [dest]: "f \<in> MFuns[G] \<Longrightarrow> modular_function f G"
  by (auto simp: MFuns_altdef)


subsection \<open>Modular forms\<close>

text \<open>
  A modular form is a meromorphic form that is holomorphic on its entire domain, including
  at the cusps.
\<close>

locale modular_form = weakly_meromorphic_form +
  assumes holo_uhp'': "holo_uhp f"
  assumes holomorphic_at_cusps:
    "\<And>h::modgrp. holomorphic_at_infinity (slash_mero_uhp weight h f)"
begin

sublocale fourier_expansion_holomorphic "cusp_width\<^sub>\<infinity> G" f
proof
  show "holomorphic_at_infinity f"
    using holomorphic_at_cusps[of 1] by simp
qed (fact holo_uhp'')

lemma modular_form_conj:
  "modular_form (slash_mero_uhp weight h f) weight (conj_modgrp h G)"
proof -
  interpret conj: weakly_meromorphic_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
    by (rule weakly_meromorphic_form_conj)
  show ?thesis
  proof
    show "holo_uhp (slash_mero_uhp weight h f)"
    proof (rule holo_uhp_mero_uhp_rel_transfer)
      show "mero_uhp_rel (slash_mero_uhp weight h f) 
              (\<lambda>z. automorphy_factor h z powi (-weight) * f (apply_modgrp h z))"
        by mero_uhp_rel
    next
      show "(\<lambda>z. automorphy_factor h z powi (-weight) * f (apply_modgrp h z)) analytic_on {z. Im z > 0}"
        by (intro analytic_intros) auto
    qed
  next
    fix h' :: modgrp
    show "holomorphic_at_infinity (slash_mero_uhp weight h' (slash_mero_uhp weight h f))"
      using holomorphic_at_cusps[of "h * h'"] by (simp add: conj_modgrp_mult slash_mero_uhp_mult)
  qed
qed

sublocale meromorphic_form
proof
  fix h :: modgrp
  interpret conj: modular_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
    by (rule modular_form_conj)
  show "meromorphic_at_infinity (conj_modgrp h G) (slash_mero_uhp weight h f)"
    using conj.fourier_meromorphic_at_0 by (simp add: meromorphic_at_infinity_def)
qed

lemma modular_form_minus: "modular_form (-f) weight G"
proof -
  interpret minus: meromorphic_form "-f" weight G
    by (rule meromorphic_form_minus)
  show ?thesis
  proof
    have ana: "(\<lambda>z. -f z) analytic_on {z. Im z > 0}"
      by (intro analytic_intros) auto
    show "holo_uhp (-f)"
      by (rule holo_uhp_mero_uhp_rel_transfer[OF _ ana]) mero_uhp_rel
  next
    fix h :: modgrp
    define fs where "fs = slash_mero_uhp weight h f"
    interpret fs: modular_form fs weight "conj_modgrp h G"
      unfolding fs_def by (rule modular_form_conj)
    have "(eval_mero_uhp (slash_mero_uhp weight h (-f)) \<longlongrightarrow> -eval_mero_uhp_at_ii_inf fs) at_\<i>\<infinity>"
      using fs.tendsto_at_ii_inf
      by (auto simp: hom_distribs eval_mero_uhp_minus [abs_def] fs_def intro!: tendsto_intros)
    thus "holomorphic_at_infinity (slash_mero_uhp weight h (-f))"
      unfolding holomorphic_at_infinity_def by blast
  qed
qed

end


lemma (in meromorphic_form) modular_form_via_zorder:
  assumes "holo_uhp f"
  assumes "\<And>h::modgrp. zorder_at_cusp_modgrp weight G f h \<ge> 0"
  shows   "modular_form f weight G"
proof
  show "holomorphic_at_infinity (slash_mero_uhp weight h f)" for h
  proof -
    interpret fs: meromorphic_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
      by (rule meromorphic_form_conj)
    show ?thesis
    proof (rule fs.holomorphic_at_infinity_via_zorder)
      show "zorder_at_ii_inf (cusp_width\<^sub>\<infinity> (conj_modgrp h G)) (slash_mero_uhp weight h f) \<ge> 0"
        using assms(2)[of h]
        by (simp add: zorder_at_cusp_modgrp_def cusp_width_modgrp_def)
    qed
  qed
qed fact+

lemma (in cong_subgroup) modular_form_0: "modular_form 0 weight G"
proof -
  interpret meromorphic_form 0 weight G
    by (rule meromorphic_form_0)
  show ?thesis
  proof
    show "holo_uhp 0"
      by (auto simp: holo_uhp_def)
  next
    fix h :: modgrp
    show "holomorphic_at_infinity (slash_mero_uhp weight h 0)"
      unfolding holomorphic_at_infinity_def by auto
  qed
qed

lemma (in cong_subgroup) modular_form_const: "modular_form (const_mero_uhp c) 0 G"
proof -
  interpret meromorphic_form "const_mero_uhp c" 0 G
    by (rule meromorphic_form_const)
  show ?thesis
  proof
    have "mero_uhp_rel (const_mero_uhp c) (\<lambda>_. c)"
      by mero_uhp_rel
    thus "holo_uhp (const_mero_uhp c)"
      by (rule holo_uhp_mero_uhp_rel_transfer) auto
  next
    fix h :: modgrp
    have "(eval_mero_uhp \<langle>c\<rangle> \<longlongrightarrow> c) at_\<i>\<infinity>"
    proof (rule Lim_transform_eventually)
      show "eventually (\<lambda>z. c = eval_mero_uhp (const_mero_uhp c) z) at_\<i>\<infinity>"
        using eventually_at_ii_inf[of 0] by eventually_elim auto
    qed auto
    thus "holomorphic_at_infinity (slash_mero_uhp 0 h (const_mero_uhp c))"
      unfolding holomorphic_at_infinity_def by auto
  qed
qed

lemma (in cong_subgroup) modular_form_1: "modular_form 1 0 G"
  using modular_form_const[of 1] by simp

lemmas modular_form_minus = modular_form.modular_form_minus

lemma modular_form_add:
  assumes "modular_form f weight G" "modular_form g weight G"
  shows   "modular_form (f + g) weight G"
proof -
  interpret f: modular_form f weight G by fact
  interpret g: modular_form g weight G by fact
  interpret sum: meromorphic_form "f + g" weight G
    by (rule meromorphic_form_add) unfold_locales
  show ?thesis
  proof
    have ana: "(\<lambda>z. f z + g z) analytic_on {z. Im z > 0}"
      by (intro analytic_intros) auto
    show "holo_uhp (f + g)"
      by (rule holo_uhp_mero_uhp_rel_transfer[OF _ ana]) mero_uhp_rel
  next
    fix h :: modgrp
    define fs where "fs = slash_mero_uhp weight h f"
    define gs where "gs = slash_mero_uhp weight h g"
    interpret fs: modular_form fs weight "conj_modgrp h G"
      unfolding fs_def by (rule f.modular_form_conj)
    interpret gs: modular_form gs weight "conj_modgrp h G"
      unfolding gs_def by (rule g.modular_form_conj)
    have "(eval_mero_uhp (slash_mero_uhp weight h (f + g)) \<longlongrightarrow> 
             eval_mero_uhp_at_ii_inf fs + eval_mero_uhp_at_ii_inf gs) at_\<i>\<infinity>"
    proof (rule Lim_transform_eventually)
      show "eventually (\<lambda>z. fs z + gs z = eval_mero_uhp (slash_mero_uhp weight h (f + g)) z) at_\<i>\<infinity>"
        using eventually_at_ii_inf[of 0] unfolding hom_distribs
        by eventually_elim (subst eval_mero_uhp_add, auto simp flip: fs_def gs_def)
    next
      show "((\<lambda>z. fs z + gs z) \<longlongrightarrow> eval_mero_uhp_at_ii_inf fs + eval_mero_uhp_at_ii_inf gs) at_\<i>\<infinity>"
        using fs.tendsto_at_ii_inf gs.tendsto_at_ii_inf by (intro tendsto_intros)
    qed
    thus "holomorphic_at_infinity (slash_mero_uhp weight h (f + g))"
      unfolding holomorphic_at_infinity_def by blast
  qed
qed

lemma modular_form_diff:
  assumes "modular_form f weight G" "modular_form g weight G"
  shows   "modular_form (f - g) weight G"
  using modular_form_add[OF assms(1) modular_form_minus[OF assms(2)]] by simp

lemma modular_form_mult:
  assumes "modular_form f weight1 G" "modular_form g weight2 G"
  shows   "modular_form (f * g) (weight1 + weight2) G"
proof -
  interpret f: modular_form f weight1 G by fact
  interpret g: modular_form g weight2 G by fact
  interpret sum: meromorphic_form "f * g" "weight1 + weight2" G
    by (rule meromorphic_form_mult) unfold_locales
  show ?thesis
  proof
    have ana: "(\<lambda>z. f z * g z) analytic_on {z. Im z > 0}"
      by (intro analytic_intros) auto
    show "holo_uhp (f * g)"
      by (rule holo_uhp_mero_uhp_rel_transfer[OF _ ana]) mero_uhp_rel
  next
    fix h :: modgrp
    define fs where "fs = slash_mero_uhp weight1 h f"
    define gs where "gs = slash_mero_uhp weight2 h g"
    interpret fs: modular_form fs weight1 "conj_modgrp h G"
      unfolding fs_def by (rule f.modular_form_conj)
    interpret gs: modular_form gs weight2 "conj_modgrp h G"
      unfolding gs_def by (rule g.modular_form_conj)
    have "(eval_mero_uhp (slash_mero_uhp (weight1 + weight2) h (f * g)) \<longlongrightarrow> 
             eval_mero_uhp_at_ii_inf fs * eval_mero_uhp_at_ii_inf gs) at_\<i>\<infinity>"
    proof (rule Lim_transform_eventually)
      show "eventually (\<lambda>z. fs z * gs z = eval_mero_uhp (slash_mero_uhp (weight1 + weight2) h (f * g)) z) at_\<i>\<infinity>"
        using eventually_at_ii_inf[of 0]
      proof eventually_elim
        case (elim z)
        have "eval_mero_uhp (slash_mero_uhp (weight1 + weight2) h (f * g)) z =
                eval_mero_uhp (fs * gs) z"
          by (simp add: slash_mero_uhp_mult_right fs_def gs_def)
        also have "\<dots> = fs z * gs z"
          by (subst eval_mero_uhp_mult) (use elim in auto)
        finally show ?case ..
      qed
    next
      show "((\<lambda>z. fs z * gs z) \<longlongrightarrow> eval_mero_uhp_at_ii_inf fs * eval_mero_uhp_at_ii_inf gs) at_\<i>\<infinity>"
        using fs.tendsto_at_ii_inf gs.tendsto_at_ii_inf by (intro tendsto_intros)
    qed
    thus "holomorphic_at_infinity (slash_mero_uhp (weight1 + weight2) h (f * g))"
      unfolding holomorphic_at_infinity_def by blast
  qed
qed

lemma modular_form_power:
  assumes "modular_form f weight G"
  shows   "modular_form (f ^ n) (n * weight) G"
proof -
  interpret f: modular_form f weight G
    by fact
  show ?thesis
    by (induction n) (use assms in \<open>auto intro: modular_form_mult f.modular_form_1 simp: ring_distribs\<close>)
qed

lemma modular_form_power_int:
  assumes "modular_form f weight G" "n \<ge> 0"
  shows   "modular_form (f powi n) (n * weight) G"
  using modular_form_power[OF assms(1), of "nat n"] assms(2) by (simp add: power_int_def)

(* TODO: could probably be simplified *)
lemma modular_form_divide:
  fixes G :: "modgrp set"
  assumes "modular_form f weight1 G" "modular_form g weight2 G"
  assumes zorder_le:
     "\<And>z. f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> Im z > 0 \<Longrightarrow> eval_mero_uhp g z = 0 \<Longrightarrow> 
        zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes zorder_at_cusps_le:
    "\<And>h::modgrp. f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow>
       zorder_at_cusp_modgrp weight2 G g h \<le> zorder_at_cusp_modgrp weight1 G f h"
  shows "modular_form (f / g) (weight1 - weight2) G"
proof (cases "f = 0 \<or> g = 0")
  case True
  interpret f: modular_form f weight1 G by fact
  show ?thesis
    using True by (auto intro: f.modular_form_0)
next
  case False
  hence [simp]: "f \<noteq> 0" "g \<noteq> 0"
    by auto
  interpret f: modular_form f weight1 G by fact
  interpret g: modular_form g weight2 G by fact
  interpret meromorphic_form "f / g" "weight1 - weight2" G
    by (rule meromorphic_form_divide) unfold_locales
  show ?thesis
  proof
    have freq: "\<exists>\<^sub>F w in at z. eval_mero_uhp f w \<noteq> 0" "\<exists>\<^sub>F w in at z. eval_mero_uhp g w \<noteq> 0"
      if z: "Im z > 0" for z
      using z by (intro eventually_frequently; simp add: eventually_neq_eval_mero_uhp)+
    have "\<not>is_pole (f / g) z" for z :: complex
    proof (cases "Im z > 0")
      case z: True
      have "mero_uhp_rel (eval_mero_uhp (f / g)) (\<lambda>z. eval_mero_uhp f z / eval_mero_uhp g z)"
        by mero_uhp_rel
      hence "zorder (eval_mero_uhp (f / g)) z = zorder (\<lambda>z. eval_mero_uhp f z / eval_mero_uhp g z) z"
        using z by (intro zorder_cong) (auto simp: mero_uhp_rel_def eventually_cosparse_open_eq open_halfspace_Im_gt)
      also have "\<dots> = zorder f z - zorder g z"
        using freq z by (subst zorder_divide) (auto intro!: meromorphic_intros)
      also have "\<dots> \<ge> 0"
      proof (cases "eval_mero_uhp g z = 0")
        case True
        with zorder_le[of z] z show ?thesis
          by simp
      next
        case False
        have "zorder_mero_uhp f z \<ge> 0"
          using z by (subst zorder_mero_uhp_nonneg_iff) auto
        moreover have "zorder_mero_uhp g z = 0"
          using z False by (subst zorder_mero_uhp_eq_0_iff) auto
        ultimately show ?thesis by simp
      qed
      finally show "\<not>is_pole (f / g) z"
        using z by (subst (asm) zorder_mero_uhp_nonneg_iff) auto
    qed (auto simp: not_is_pole_eval_mero_uhp_outside)
    thus "holo_uhp (f / g)"
      by (auto simp: holo_uhp_def)
  next
    fix h :: modgrp
    define w where "w = cusp_width\<^sub>\<infinity> (conj_modgrp h G)"

    define fs where "fs = slash_mero_uhp weight1 h f"
    define gs where "gs = slash_mero_uhp weight2 h g"
    interpret fs: modular_form fs weight1 "conj_modgrp h G"
      unfolding fs_def by (rule f.modular_form_conj)
    interpret gs: modular_form gs weight2 "conj_modgrp h G"
      unfolding gs_def by (rule g.modular_form_conj)

    define FL where "FL = laurent_expansion (fourier_expansion w fs) 0"
    define GL where "GL = laurent_expansion (fourier_expansion w gs) 0"
    have FG: "fourier_expansion w fs has_laurent_expansion FL"
             "fourier_expansion w gs has_laurent_expansion GL" unfolding FL_def GL_def w_def
      by (auto intro!: meromorphic_on_imp_has_laurent_expansion0[of _ "{0}"] 
                       fs.fourier_meromorphic gs.fourier_meromorphic)
    define c where "c = fls_nth (FL / GL) 0"

    have "fls_subdegree (FL / GL) \<ge> 0"
    proof -
      have [simp]: "fs \<noteq> 0" "FL \<noteq> 0"
        using fs.laurent_expansion_fourier_eq_0_iff0[of FL] FG(1) by (auto simp: w_def fs_def)
      have [simp]: "gs \<noteq> 0" "GL \<noteq> 0"
        using gs.laurent_expansion_fourier_eq_0_iff0[of GL] FG(2) by (auto simp: w_def gs_def)

      have "zorder_at_cusp_modgrp weight2 G g h \<le> zorder_at_cusp_modgrp weight1 G f h"
        by (rule zorder_at_cusps_le) auto
      also have "zorder_at_cusp_modgrp weight1 G f h = zorder (fourier_expansion w fs) 0"
        using fs.zorder_at_ii_inf_conv_fourier
        by (simp add: zorder_at_cusp_modgrp_def fs_def w_def cusp_width_modgrp_def)
      also have "\<dots> = fls_subdegree FL"
        using FG(1) by (intro has_laurent_expansion_zorder_0) auto
      also have "zorder_at_cusp_modgrp weight2 G g h = zorder (fourier_expansion w gs) 0"
        using gs.zorder_at_ii_inf_conv_fourier
        by (simp add: zorder_at_cusp_modgrp_def gs_def w_def cusp_width_modgrp_def)
      also have "\<dots> = fls_subdegree GL"
        using FG(2) by (intro has_laurent_expansion_zorder_0) auto
      finally have "fls_subdegree FL - fls_subdegree GL \<ge> 0"
        by simp
      also have "fls_subdegree FL - fls_subdegree GL = fls_subdegree (FL / GL)"
        by (subst fls_divide_subdegree) auto
      finally show ?thesis .
    qed

    hence "(\<lambda>q. fourier_expansion w fs q / fourier_expansion w gs q) \<midarrow>0\<rightarrow> c" unfolding c_def
      by (intro has_laurent_expansion_imp_tendsto_0 laurent_expansion_intros FG)
    also have "?this \<longleftrightarrow> ((\<lambda>z. eval_mero_uhp fs z / eval_mero_uhp gs z) \<longlongrightarrow> c) at_\<i>\<infinity>"
      by (subst at_ii_inf_filtermap [of w, symmetric])
         (simp_all add: filterlim_filtermap w_def fs.period_pos)
    also have "\<dots> \<longleftrightarrow> ((\<lambda>z. eval_mero_uhp (fs / gs) z) \<longlongrightarrow> c) at_\<i>\<infinity>"
    proof (rule tendsto_cong)
      show "\<forall>\<^sub>F x in at_\<i>\<infinity>. eval_mero_uhp fs x / eval_mero_uhp gs x = eval_mero_uhp (fs / gs) x"
        using eventually_at_ii_inf[of 0] fs.eventually_no_poles gs.eventually_no_isolated_zero
        by eventually_elim (subst eval_mero_uhp_divide, auto)
    qed
    also have "fs / gs = slash_mero_uhp (weight1 - weight2) h (f / g)"
      by (simp add: fs_def gs_def slash_mero_uhp_divide)
    finally show "holomorphic_at_infinity (slash_mero_uhp (weight1 - weight2) h (f / g))"
      by (auto simp: holomorphic_at_infinity_def)
  qed
qed



definition MForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("MForms[_,_]") where
  "MForms G k = {f. modular_form f k G}"

abbreviation MForms' :: "int \<Rightarrow> mero_uhp set" ("MForms[_]") where
  "MForms' \<equiv> MForms UNIV"

lemma modular_form_MForms [dest]: "f \<in> MForms[G, k] \<Longrightarrow> modular_form f k G"
  by (auto simp: MForms_def)

lemma holo_uhp_MForms: "f \<in> MForms[G, k] \<Longrightarrow> holo_uhp f"
  using modular_form.holo_uhp'' by blast

lemma no_poles_MForms: "f \<in> MForms[G, k] \<Longrightarrow> \<not>is_pole f z"
  using holo_uhp_MForms[of f G k] by (auto simp: holo_uhp_def)

lemma MForms_has_fps_expansion_at_ii_inf:
  assumes "f \<in> MForms[G, k]"
  shows   "f has_fps_expansion_at_\<i>\<infinity>[cusp_width\<^sub>\<infinity> G] fps_expansion_at_\<i>\<infinity> (cusp_width\<^sub>\<infinity> G) f"
proof -
  interpret modular_form f k G
    using assms by auto
  show ?thesis
    by (rule has_fps_expansion_at_ii_inf)
qed

lemma MForms_UNIV_has_fps_expansion_at_ii_inf:
  assumes "f \<in> MForms[k]"
  shows   "f has_fps_expansion_at_\<i>\<infinity> fps_expansion_at_\<i>\<infinity> (Suc 0) f"
  using MForms_has_fps_expansion_at_ii_inf[OF assms] by simp

lemma eval_mero_uhp_at_ii_inf_const [simp]: "eval_mero_uhp_at_ii_inf (const_mero_uhp c) = c"
proof -
  interpret modular_form "const_mero_uhp c" 0 UNIV
    by (rule modular_group.modular_form_const)
  interpret ctxt: fourier_expansion_context "cusp_width\<^sub>\<infinity> UNIV"
    by standard (use period_pos in auto)
  show ?thesis
    by (subst ctxt.const.eval_at_ii_inf_conv_fourier, subst ctxt.fourier_const) auto
qed

lemma eval_mero_uhp_at_ii_inf_0 [simp]: "eval_mero_uhp_at_ii_inf 0 = 0"
  and eval_mero_uhp_at_ii_inf_1 [simp]: "eval_mero_uhp_at_ii_inf 1 = 1"
  and eval_mero_uhp_at_ii_inf_of_nat [simp]: "eval_mero_uhp_at_ii_inf (of_nat n) = of_nat n"
  and eval_mero_uhp_at_ii_inf_of_int [simp]: "eval_mero_uhp_at_ii_inf (of_int k) = of_int k"
  and eval_mero_uhp_at_ii_inf_of_numeral [simp]: "eval_mero_uhp_at_ii_inf (numeral num) = numeral num"
  by (metis const_mero_uhp.hom_zero const_mero_uhp.hom_one const_mero_uhp.hom_of_nat
            eval_mero_uhp_at_ii_inf_const const_mero_uhp.hom_of_int const_mero_uhp.hom_numeral)+

context fourier_expansion_meromorphic
begin

lemma eval_mero_uhp_at_ii_inf_minus [simp]:
  assumes "\<not>is_pole_ii_inf f"
  shows   "eval_mero_uhp_at_ii_inf (-f) = -eval_mero_uhp_at_ii_inf f"
proof -
  interpret minus: fourier_expansion_meromorphic period "-f"
    by (rule fourier_expansion_meromorphic_minus)
  show ?thesis
    using fourier_minus_eq[of 0] assms
    by (simp add: is_pole_ii_inf_conv_fourier eval_at_ii_inf_conv_fourier
                  minus.eval_at_ii_inf_conv_fourier)
qed

end


context
  fixes G
  assumes G: "cong_subgroup G"
begin

interpretation cong_subgroup G
  by (fact G)

lemma MForms_0 [mform_intros, simp, intro]: "0 \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_0)

lemma MForms_const [mform_intros, simp, intro]: "const_mero_uhp c \<in> MForms[G, 0]"
  by (auto simp: MForms_def modular_form_const)

lemma MForms_is_const: "is_const_mero_uhp f \<Longrightarrow> f \<in> MForms[G, 0]"
  by (auto simp: is_const_mero_uhp_def)

lemma MForms_1 [mform_intros, simp, intro]: "1 \<in> MForms[G, 0]"
  and MForms_of_nat [mform_intros, simp, intro]: "of_nat n \<in> MForms[G, 0]"
  and MForms_of_int [mform_intros, simp, intro]: "of_int m \<in> MForms[G, 0]"
  and MForms_of_real [mform_intros, simp, intro]: "of_real x \<in> MForms[G, 0]"
  and MForms_numeral [mform_intros, simp, intro]: "numeral num \<in> MForms[G, 0]"
  by (rule MForms_is_const; simp; fail)+

end

lemma MForms_uminus [mform_intros]: "f \<in> MForms[G, k] \<Longrightarrow> -f \<in> MForms[G, k]"
  by (auto simp: MForms_def intro!: modular_form.modular_form_minus modular_form.modular_form_minus)

lemma MForms_add [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> MForms[G, k] \<Longrightarrow> f + g \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_add)

lemma MForms_diff [mform_intros]:
  "f \<in> MForms[G, k] \<Longrightarrow> g \<in> MForms[G, k] \<Longrightarrow> f - g \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_diff)

lemma MForms_mult [mform_intros]:
  "f \<in> MForms[G, k1] \<Longrightarrow> g \<in> MForms[G, k2] \<Longrightarrow> k = k1 + k2 \<Longrightarrow> f * g \<in> MForms[G, k]"
  by (auto simp: MForms_def modular_form_mult)

lemma MForms_power [mform_intros]: "f \<in> MForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f ^ n \<in> MForms[G, m]"
  using modular_form_power[of f k G n] by (auto simp: MForms_def)

lemma MForms_power_int [mform_intros]: "n \<ge> 0 \<Longrightarrow> f \<in> MForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> f powi n \<in> MForms[G, m]"
  using modular_form_power_int[of f k G n] by (auto simp: MForms_def)

context
  fixes G
  assumes G: "cong_subgroup G"
begin

lemma MForms_sum [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> MForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros G)

lemma MForms_prod [mform_intros]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> MForms[G, k x]) \<Longrightarrow> m = (\<Sum>x\<in>A. k x) \<Longrightarrow> (\<Prod>x\<in>A. f x) \<in> MForms[G, m]"
  by (induction A arbitrary: m rule: infinite_finite_induct) (auto intro!: mform_intros G)

end

lemma MForms_divide [mform_intros]:
  fixes G
  assumes "f \<in> MForms[G, k1]" "g \<in> MForms[G, k2]" "k = k1 - k2"
  assumes "\<And>z. f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> Im z > 0 \<Longrightarrow> 
                  zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "\<And>h. f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> 
                  zorder_at_cusp_modgrp k1 G f h \<ge> zorder_at_cusp_modgrp k2 G g h"
  shows   "f / g \<in> MForms[G, k]"
  unfolding MForms_def
proof safe
  interpret f: modular_form f k1 G
    using assms(1) by auto
  interpret g: modular_form g k2 G
    using assms(2) by auto
  have "modular_form (f / g) (k1 - k2) G"
    by (rule modular_form_divide) (use assms in auto)
  thus "modular_form (f / g) k G"
    using \<open>k = k1 - k2\<close> by simp
qed

lemma MForms_UNIV_divide [mform_intros]:
  assumes "f \<in> MForms[k1]" "g \<in> MForms[k2]" "k = k1 - k2"
  assumes "\<And>z. f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> Im z > 0 \<Longrightarrow> 
                  zorder_mero_uhp f z \<ge> zorder_mero_uhp g z"
  assumes "f \<noteq> 0 \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> zorder_at_ii_inf 1 f \<ge> zorder_at_ii_inf 1 g"
  shows   "f / g \<in> MForms[k]"
proof (rule MForms_divide[OF assms(1,2,3)])
  fix h :: modgrp
  assume [simp]: "f \<noteq> 0" "g \<noteq> 0"
  interpret f: modular_form f k1 UNIV using assms(1) by auto
  interpret g: modular_form g k2 UNIV using assms(2) by auto
  show "zorder_at_cusp_modgrp k2 UNIV g h \<le> zorder_at_cusp_modgrp k1 UNIV f h"
    using assms(5)
    by (simp add: zorder_at_cusp_modgrp_def cusp_width_modgrp_def 
                  f.invariant_slash_modgrp g.invariant_slash_modgrp)
qed (use assms(4) in auto)



lemma eval_mero_uhp_at_ii_inf_uminus [simp]:
  assumes "f \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_ii_inf (-f) = -eval_mero_uhp_at_ii_inf f"
proof -
  interpret modular_form f k G
    using assms by auto
  interpret minus: modular_form "-f" k G
    by (rule modular_form_minus)
  show ?thesis
    by (simp add: minus.eval_at_ii_inf_conv_fourier eval_at_ii_inf_conv_fourier fourier_minus_eq)
qed

lemma eval_mero_uhp_at_ii_inf_add [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_ii_inf (f + g) = eval_mero_uhp_at_ii_inf f + eval_mero_uhp_at_ii_inf g"
proof -
  interpret f: modular_form f k G
    using assms by auto
  interpret g: modular_form g k G
    using assms by auto
  interpret add: modular_form "f + g" k G
    by (rule modular_form_add) unfold_locales
  interpret ctxt: fourier_expansion_context "cusp_width\<^sub>\<infinity> G"
    by standard (use f.period_pos in auto)
  interpret fg: fourier_expansion_meromorphic_pair "cusp_width\<^sub>\<infinity> G" f g ..
  show ?thesis
    by (simp add: add.eval_at_ii_inf_conv_fourier fg.fourier_add_eq
                  f.eval_at_ii_inf_conv_fourier g.eval_at_ii_inf_conv_fourier)
qed

lemma eval_mero_uhp_at_ii_inf_diff [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_ii_inf (f - g) = eval_mero_uhp_at_ii_inf f - eval_mero_uhp_at_ii_inf g"
proof -
  have "eval_mero_uhp_at_ii_inf (f + (-g)) = eval_mero_uhp_at_ii_inf f - eval_mero_uhp_at_ii_inf g"
    using assms by (subst eval_mero_uhp_at_ii_inf_add) (auto intro: mform_intros)
  thus ?thesis
    by simp
qed

lemma eval_mero_uhp_at_ii_inf_mult [simp]:
  assumes "f \<in> MForms[G, k]" "g \<in> MForms[G, k']"
  shows   "eval_mero_uhp_at_ii_inf (f * g) = eval_mero_uhp_at_ii_inf f * eval_mero_uhp_at_ii_inf g"
proof -
  interpret f: modular_form f k G
    using assms by auto
  interpret g: modular_form g k' G
    using assms by auto
  interpret ctxt: fourier_expansion_context "cusp_width\<^sub>\<infinity> G"
    by standard (use f.period_pos in auto)
  interpret fg: fourier_expansion_meromorphic_pair "cusp_width\<^sub>\<infinity> G" f g ..
  interpret mult: modular_form "f * g" "k + k'" G
    by (rule modular_form_mult) unfold_locales
  show ?thesis
    by (simp add: fg.mult.eval_at_ii_inf_conv_fourier fg.fourier_mult_eq
                  f.eval_at_ii_inf_conv_fourier g.eval_at_ii_inf_conv_fourier)
qed

lemma eval_mero_uhp_at_ii_inf_power [simp]:
  assumes [mform_intros]: "f \<in> MForms[G, k]"
  shows   "eval_mero_uhp_at_ii_inf (f ^ n) = eval_mero_uhp_at_ii_inf f ^ n"
proof (induction n)
  case (Suc n)
  show ?case
    unfolding power_Suc
    by (subst eval_mero_uhp_at_ii_inf_mult) (auto intro!: mform_intros simp: Suc.IH)
qed auto

lemma eval_mero_uhp_at_ii_inf_power_int [simp]:
  assumes "f \<in> MForms[G, k]" "n \<ge> 0"
  shows   "eval_mero_uhp_at_ii_inf (f powi n) = eval_mero_uhp_at_ii_inf f powi n"
  using assms by (auto simp: power_int_def)

lemma zorder_MForms_nonneg [simp, intro]:
  assumes "f \<in> MForms[G, k]" "Im z > 0" "f \<noteq> 0"
  shows   "zorder f  z \<ge> 0"
proof -
  interpret modular_form f k G
    using assms by auto
  show ?thesis
    using assms by auto
qed

lemma zorder_at_ii_inf_nonneg [simp, intro]:
  assumes "f \<in> MForms[G, k]" "f \<noteq> 0"
  shows   "zorder_at_ii_inf (cusp_width\<^sub>\<infinity> G) f \<ge> 0"
proof -
  interpret modular_form f k G
    using assms by auto
  have "zorder_at_ii_inf (cusp_width\<^sub>\<infinity> G) f = zorder (fourier_expansion (cusp_width\<^sub>\<infinity> G) f) 0"
    using assms zorder_at_ii_inf_conv_fourier by simp
  also have "\<dots> \<ge> 0"
    using assms by simp
  finally show ?thesis .
qed


subsection \<open>Cusp forms\<close>

text \<open>
  A cusp form is a modular form that vanishes at all cusps.
\<close>

locale cusp_form = modular_form +
  assumes vanishes_at_cusps:
    "\<And>h::modgrp. eval_mero_uhp_at_ii_inf (slash_mero_uhp weight h f) = 0"
begin

lemma vanishes_at_infinity [simp]: "eval_mero_uhp_at_ii_inf f = 0"
  using vanishes_at_cusps[of 1] by simp

lemma cusp_form_conj: "cusp_form (slash_mero_uhp weight h f) weight (conj_modgrp h G)"
proof -
  interpret conj: modular_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
    by (rule modular_form_conj)
  show ?thesis
  proof
    fix h' :: modgrp
    show "eval_mero_uhp_at_ii_inf (slash_mero_uhp weight h' (slash_mero_uhp weight h f)) = 0"
      by (simp flip: slash_mero_uhp_mult add: vanishes_at_cusps)
  qed
qed

lemma isolated_zero_fourier:
  assumes "f \<noteq> 0"
  shows   "isolated_zero (fourier_expansion (cusp_width\<^sub>\<infinity> G) f) 0"
proof -
  define w where "w = cusp_width\<^sub>\<infinity> G"
  define f' where "f' = fourier_expansion w f"
  have "f' analytic_on {0}"
    by (auto simp: f'_def w_def intro!: analytic_intros)
  moreover have "f' 0 = 0"
    by (auto simp: f'_def w_def simp flip: eval_at_ii_inf_conv_fourier)
  moreover have "eventually (\<lambda>q. f' q \<noteq> 0) (at 0)"
    using eventually_neq_fourier[of 0 0] assms by (auto simp: f'_def w_def)
  ultimately show "isolated_zero f' 0"
    by (subst isolated_zero_analytic_iff) auto
qed

lemma zorder_at_ii_inf_pos:
  assumes "f \<noteq> 0"
  shows   "zorder_at_ii_inf (cusp_width\<^sub>\<infinity> G) f > 0"
proof -
  define w where "w = cusp_width\<^sub>\<infinity> G"
  define f' where "f' = fourier_expansion w f"
  have "isolated_zero f' 0"
    unfolding f'_def w_def by (rule isolated_zero_fourier) fact+
  hence "zorder f' 0 > 0"
    by (rule zorder_isolated_zero_pos) (auto simp: f'_def w_def intro!: analytic_intros)
  thus ?thesis
    using assms by (simp add: f'_def w_def zorder_at_ii_inf_conv_fourier)
qed

lemma cusp_form_minus: "cusp_form (-f) weight G"
proof -
  interpret minus: modular_form "-f" weight G
    by (rule modular_form_minus)
  show ?thesis
  proof
    fix h :: modgrp
    interpret conj: cusp_form "slash_mero_uhp weight h f" weight "conj_modgrp h G"
      by (rule cusp_form_conj)
    show "eval_mero_uhp_at_ii_inf (slash_mero_uhp weight h (- f)) = 0"
      by (auto simp: hom_distribs vanishes_at_cusps)
  qed
qed

end


lemma (in cong_subgroup) cusp_form_0: "cusp_form 0 weight G"
proof -
  interpret modular_form 0 weight G
    by (rule modular_form_0)
  show ?thesis by standard auto
qed

lemmas cusp_form_minus = cusp_form.cusp_form_minus

lemma cusp_form_add:
  assumes "cusp_form f weight G" "cusp_form g weight G"
  shows   "cusp_form (f + g) weight G"
proof -
  interpret f: cusp_form f weight G by fact
  interpret g: cusp_form g weight G by fact
  interpret sum: modular_form "f + g" weight G
    by (rule modular_form_add) unfold_locales
  show ?thesis
  proof
    fix h :: modgrp
    define w where "w = cusp_width_modgrp h G"
    define fs where "fs = slash_mero_uhp weight h f"
    define gs where "gs = slash_mero_uhp weight h g"
    interpret fs: cusp_form fs weight "conj_modgrp h G" 
      rewrites "cusp_width\<^sub>\<infinity> (conj_modgrp h G) \<equiv> w"
      unfolding fs_def by (rule f.cusp_form_conj) (auto simp: w_def cusp_width_modgrp_def)
    interpret gs: cusp_form gs weight "conj_modgrp h G"
      rewrites "cusp_width\<^sub>\<infinity> (conj_modgrp h G) \<equiv> w"
      unfolding gs_def by (rule g.cusp_form_conj) (auto simp: w_def cusp_width_modgrp_def)
    interpret ctxt: fourier_expansion_context w
      by standard (use fs.period_pos in \<open>auto simp: w_def\<close>)
    interpret fg: fourier_expansion_meromorphic_pair w fs gs ..

    have "eval_mero_uhp_at_ii_inf (slash_mero_uhp weight h (f + g)) =
            eval_mero_uhp_at_ii_inf (fs + gs)"
      by (simp add: fs_def gs_def hom_distribs)
    also have "\<dots> = 0"
      by (simp add: fg.add.eval_at_ii_inf_conv_fourier fg.fourier_add_eq
               flip: fs.eval_at_ii_inf_conv_fourier gs.eval_at_ii_inf_conv_fourier)
    finally show "eval_mero_uhp_at_ii_inf (slash_mero_uhp weight h (f + g)) = 0" .
  qed
qed

lemma cusp_form_diff:
  assumes "cusp_form f weight G" "cusp_form g weight G"
  shows   "cusp_form (f - g) weight G"
  using cusp_form_add[OF assms(1) cusp_form_minus[OF assms(2)]] by simp

lemma cusp_form_mult_left:
  assumes "cusp_form f weight1 G" "modular_form g weight2 G"
  shows   "cusp_form (f * g) (weight1 + weight2) G"
proof -
  interpret f: cusp_form f weight1 G by fact
  interpret g: modular_form g weight2 G by fact
  interpret sum: modular_form "f * g" "weight1 + weight2" G
    by (rule modular_form_mult) unfold_locales
  show ?thesis
  proof
    fix h :: modgrp
    define w where "w = cusp_width_modgrp h G"
    define fs where "fs = slash_mero_uhp weight1 h f"
    define gs where "gs = slash_mero_uhp weight2 h g"
    interpret fs: cusp_form fs weight1 "conj_modgrp h G" 
      rewrites "cusp_width\<^sub>\<infinity> (conj_modgrp h G) \<equiv> w"
      unfolding fs_def by (rule f.cusp_form_conj) (auto simp: w_def cusp_width_modgrp_def)
    interpret gs: modular_form gs weight2 "conj_modgrp h G"
      rewrites "cusp_width\<^sub>\<infinity> (conj_modgrp h G) \<equiv> w"
      unfolding gs_def by (rule g.modular_form_conj) (auto simp: w_def cusp_width_modgrp_def)
    interpret ctxt: fourier_expansion_context w
      by standard (use fs.period_pos in \<open>auto simp: w_def\<close>)
    interpret fg: fourier_expansion_meromorphic_pair w fs gs ..

    have "eval_mero_uhp_at_ii_inf (slash_mero_uhp (weight1 + weight2) h (f * g)) =
            eval_mero_uhp_at_ii_inf (fs * gs)"
      by (simp add: fs_def gs_def slash_mero_uhp_mult_right)
    also have "\<dots> = 0"
      by (simp add: fg.mult.eval_at_ii_inf_conv_fourier fg.fourier_mult_eq
               flip: fs.eval_at_ii_inf_conv_fourier gs.eval_at_ii_inf_conv_fourier)
    finally show "eval_mero_uhp_at_ii_inf (slash_mero_uhp (weight1 + weight2) h (f * g)) = 0" .
  qed
qed

lemma cusp_form_mult_right:
  assumes "modular_form f weight1 G" "cusp_form g weight2 G"
  shows   "cusp_form (f * g) (weight1 + weight2) G"
  using cusp_form_mult_left[OF assms(2,1)] by (simp add: mult.commute add.commute)

lemma cusp_form_power:
  assumes "cusp_form f weight G" "n > 0"
  shows   "cusp_form (f ^ n) (n * weight) G"
proof -
  interpret cusp_form f weight G
    by fact
  have "cusp_form (f * f ^ (n - 1)) (weight + (n - 1) * weight) G"
    by (intro cusp_form_mult_left modular_form_power) unfold_locales
  thus ?thesis
    using \<open>n > 0\<close> by (cases n) (auto simp: algebra_simps)
qed

lemma cusp_form_power_int:
  assumes "cusp_form f weight G" "n > 0"
  shows   "cusp_form (f powi n) (n * weight) G"
  using cusp_form_power[OF assms(1), of "nat n"] assms(2) by (simp add: power_int_def)


definition CForms :: "modgrp set \<Rightarrow> int \<Rightarrow> mero_uhp set" ("CForms[_,_]") where
  "CForms G k = {f. cusp_form f k G}"

abbreviation CForms' :: "int \<Rightarrow> mero_uhp set" ("CForms[_]") where
  "CForms' \<equiv> CForms UNIV"

lemma cusp_form_CForms [dest]: "f \<in> CForms[G, k] \<Longrightarrow> cusp_form f k G"
  by (auto simp: CForms_def cusp_form_def MForms_def)

lemma CForms_MForms [dest]: "f \<in> CForms[G, k] \<Longrightarrow> f \<in> MForms[G, k]"
  by (auto simp: CForms_def cusp_form_def MForms_def)

lemma CForms_UNIV_altdef: "CForms[k] = {f\<in>MForms[k]. eval_mero_uhp_at_ii_inf f = 0}"
proof safe
  fix f assume "f \<in> CForms[k]"
  then interpret cusp_form f k UNIV
    by auto
  show "f \<in> MForms[k]"
    using \<open>f \<in> _\<close> by auto
  show "eval_mero_uhp_at_ii_inf f = 0"
    by (rule vanishes_at_infinity)
next
  fix f assume f: "f \<in> MForms[k]" "eval_mero_uhp_at_ii_inf f = 0"
  from f(1) interpret modular_form f k UNIV
    by auto
  interpret cusp_form f k UNIV
    by standard (auto simp: invariant_slash_modgrp f(2))
  show "f \<in> CForms[k]"
    using cusp_form_axioms by (auto simp: CForms_def)
qed

lemma zorder_at_ii_inf_CForms:
  assumes "f \<in> CForms[G, k]" "f \<noteq> 0"
  shows "zorder_at_ii_inf (cusp_width\<^sub>\<infinity> G) f > 0"
proof -
  interpret cusp_form f k G
    using assms by (auto simp: CForms_def)
  show ?thesis
    using zorder_at_ii_inf_pos assms by simp
qed

context
  fixes G
  assumes G: "cong_subgroup G"
begin

interpretation cong_subgroup G
  by (fact G)

lemma CForms_0 [mform_intros, simp, intro]: "0 \<in> CForms[G, k]"
  using G by (auto simp: CForms_def intro: cusp_form_0)

end

lemma CForms_add [mform_intros]:
  assumes "f \<in> CForms[G, k]" "g \<in> CForms[G, k]"
  shows   "f + g \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: cusp_form_add)

lemma CForms_uminus [mform_intros]:
  assumes "f \<in> CForms[G, k]"
  shows   "-f \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: cusp_form_minus)

lemma CForms_diff [mform_intros]:
  assumes "f \<in> CForms[G, k]" "g \<in> CForms[G, k]"
  shows   "f - g \<in> CForms[G, k]"
  using assms by (auto simp: CForms_def intro: cusp_form_diff)

lemma CForms_mult_left [mform_intros]:
  "f \<in> CForms[G, k1] \<Longrightarrow> g \<in> MForms[G, k2] \<Longrightarrow> k = k1 + k2 \<Longrightarrow> f * g \<in> CForms[G, k]"
  by (auto simp: CForms_def intro: cusp_form_mult_left)

lemma CForms_mult_right [mform_intros]:
  "f \<in> MForms[G, k1] \<Longrightarrow> g \<in> CForms[G, k2] \<Longrightarrow> k = k1 + k2 \<Longrightarrow> f * g \<in> CForms[G, k]"
  by (auto simp: CForms_def intro: cusp_form_mult_right)

lemma CForms_power [mform_intros]: "f \<in> CForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> n > 0 \<Longrightarrow> f ^ n \<in> CForms[G, m]"
  by (auto simp: CForms_def intro: cusp_form_power)

lemma CForms_power_int [mform_intros]: "f \<in> CForms[G, k] \<Longrightarrow> m = n * k \<Longrightarrow> n > 0 \<Longrightarrow> f powi n \<in> CForms[G, m]"
  by (auto simp: power_int_def intro!: CForms_power)

lemma CForms_sum [mform_intros]:
  "cong_subgroup G \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> CForms[G, k]) \<Longrightarrow> (\<Sum>x\<in>A. f x) \<in> CForms[G, k]"
  by (induction A rule: infinite_finite_induct) (auto intro!: mform_intros)

lemma
  assumes "cong_subgroup G"
  shows subspace_WMForms: "mero_uhp.subspace (WMForms[G, k])"
    and subspace_MeForms: "mero_uhp.subspace (MeForms[G, k])"
    and subspace_MForms: "mero_uhp.subspace (MForms[G, k])"
    and subspace_CForms: "mero_uhp.subspace (CForms[G, k])"
  unfolding mero_uhp.subspace_def by (auto intro!: mform_intros assms)

end