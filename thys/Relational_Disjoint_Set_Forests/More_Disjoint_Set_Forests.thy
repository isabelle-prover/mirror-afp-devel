(* Title:      More on Disjoint-Set Forests
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

theory More_Disjoint_Set_Forests

imports Disjoint_Set_Forests

begin

section \<open>More on Array Access and Disjoint-Set Forests\<close>

text \<open>
This section contains further results about directed acyclic graphs and relational array operations.
\<close>

context stone_relation_algebra
begin

text \<open>Theorem 6.4\<close>

lemma update_square:
  assumes "point y"
    shows "x[y\<longmapsto>x[[x[[y]]]]] \<le> x * x \<squnion> x"
proof -
  have "x[y\<longmapsto>x[[x[[y]]]]] = (y \<sqinter> y\<^sup>T * x * x) \<squnion> (-y \<sqinter> x)"
    by (simp add: conv_dist_comp)
  also have "... \<le> (y \<sqinter> y\<^sup>T) * x * x \<squnion> x"
    by (smt assms inf.eq_refl inf.sup_monoid.add_commute inf_le1 sup_mono vector_inf_comp)
  also have "... \<le> x * x \<squnion> x"
    by (smt (z3) assms comp_associative conv_dist_comp coreflexive_comp_top_inf inf.cobounded2 sup_left_isotone symmetric_top_closed)
  finally show ?thesis
    .
qed

text \<open>Theorem 2.13\<close>

lemma update_ub:
  "x[y\<longmapsto>z] \<le> x \<squnion> z\<^sup>T"
  by (meson dual_order.trans inf.cobounded2 le_supI sup.cobounded1 sup_ge2)

text \<open>Theorem 6.7\<close>

lemma update_square_ub:
  "x[y\<longmapsto>(x * x)\<^sup>T] \<le> x \<squnion> x * x"
  by (metis conv_involutive update_ub)

text \<open>Theorem 2.14\<close>

lemma update_same_sub:
  assumes "u \<sqinter> x = u \<sqinter> z"
      and "y \<le> u"
      and "regular y"
    shows "x[y\<longmapsto>z\<^sup>T] = x"
  by (smt (z3) assms conv_involutive inf.sup_monoid.add_commute inf.sup_relative_same_increasing maddux_3_11_pp)

text \<open>Theorem 2.15\<close>

lemma update_point_get:
  "point y \<Longrightarrow> x[y\<longmapsto>z[[y]]] = x[y\<longmapsto>z\<^sup>T]"
  by (metis conv_involutive get_put inf_commute update_inf_same)

text \<open>Theorem 2.11\<close>

lemma update_bot:
  "x[bot\<longmapsto>z] = x"
  by simp

text \<open>Theorem 2.12\<close>

lemma update_top:
  "x[top\<longmapsto>z] = z\<^sup>T"
  by simp

text \<open>Theorem 2.6\<close>

lemma update_same:
  assumes "regular u"
    shows "(x[y\<longmapsto>z])[u\<longmapsto>z] = x[y \<squnion> u\<longmapsto>z]"
proof -
  have "(x[y\<longmapsto>z])[u\<longmapsto>z] = (u \<sqinter> z\<^sup>T) \<squnion> (-u \<sqinter> y \<sqinter> z\<^sup>T) \<squnion> (-u \<sqinter> -y \<sqinter> x)"
    using inf.sup_monoid.add_assoc inf_sup_distrib1 sup_assoc by force
  also have "... = (u \<sqinter> z\<^sup>T) \<squnion> (y \<sqinter> z\<^sup>T) \<squnion> (-(u \<squnion> y) \<sqinter> x)"
    by (metis assms inf_sup_distrib2 maddux_3_21_pp p_dist_sup)
  also have "... = x[y \<squnion> u\<longmapsto>z]"
    using comp_inf.mult_right_dist_sup sup_commute by auto
  finally show ?thesis
    .
qed

lemma update_same_3:
  assumes "regular u"
      and "regular v"
    shows "((x[y\<longmapsto>z])[u\<longmapsto>z])[v\<longmapsto>z] = x[y \<squnion> u \<squnion> v\<longmapsto>z]"
  by (metis assms update_same)

text \<open>Theorem 2.7\<close>

lemma update_split:
  assumes "regular w"
    shows "x[y\<longmapsto>z] = (x[y - w\<longmapsto>z])[y \<sqinter> w\<longmapsto>z]"
  by (smt (z3) assms comp_inf.semiring.distrib_left inf.left_commute inf.sup_monoid.add_commute inf_import_p maddux_3_11_pp maddux_3_12 p_dist_inf sup_assoc)

text \<open>Theorem 2.8\<close>

lemma update_injective_swap:
  assumes "injective x"
      and "point y"
      and "injective z"
      and "vector z"
    shows "injective ((x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]])"
proof -
  have 1: "(z \<sqinter> y\<^sup>T * x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<le> 1"
    using assms(3) injective_inf_closed by auto
  have "(z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<le> (z \<sqinter> y\<^sup>T * x) * (y\<^sup>T \<sqinter> x\<^sup>T * z)"
    by (metis conv_dist_comp conv_involutive conv_order inf.boundedE inf.boundedI inf.cobounded1 inf.cobounded2 mult_right_isotone)
  also have "... = (z \<sqinter> z\<^sup>T * x) * (y\<^sup>T \<sqinter> x\<^sup>T * y)"
    by (smt (z3) assms(2,4) covector_inf_comp_3 inf.left_commute inf.sup_monoid.add_commute comp_associative conv_dist_comp conv_involutive)
  also have "... = (z \<sqinter> z\<^sup>T) * x * x\<^sup>T * (y \<sqinter> y\<^sup>T)"
    by (smt (z3) assms(2,4) comp_associative inf.sup_monoid.add_commute vector_covector vector_inf_comp)
  also have "... \<le> x * x\<^sup>T"
    by (metis assms(2-4) comp_associative comp_right_one coreflexive_comp_top_inf inf.coboundedI2 mult_right_isotone vector_covector)
  also have "... \<le> 1"
    by (simp add: assms(1))
  finally have 2: "(z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<le> 1"
    .
  have "(z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<le> y\<^sup>T * x * (-y\<^sup>T \<sqinter> x\<^sup>T)"
    by (smt comp_isotone conv_complement conv_dist_inf inf.cobounded2 inf.sup_monoid.add_assoc)
  also have "... = y\<^sup>T * x * x\<^sup>T \<sqinter> -y\<^sup>T"
    by (simp add: inf.commute assms(2) covector_comp_inf vector_conv_compl)
  also have "... \<le> y\<^sup>T \<sqinter> -y\<^sup>T"
    by (metis assms(1) comp_associative comp_inf.mult_left_isotone comp_isotone comp_right_one mult_sub_right_one)
  finally have 3: "(z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<le> 1"
    using pseudo_complement by fastforce
  have 4: "(-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<le> 1"
    using 2 conv_dist_comp conv_order by force
  have 5: "(-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<le> 1"
    by (simp add: assms(2) inf_assoc inf_left_commute injective_inf_closed)
  have "(-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<le> z\<^sup>T * x * (-z\<^sup>T \<sqinter> x\<^sup>T)"
    using comp_inf.mult_left_isotone comp_isotone conv_complement conv_dist_inf inf.cobounded1 inf.cobounded2 by auto
  also have "... = z\<^sup>T * x * x\<^sup>T \<sqinter> -z\<^sup>T"
    by (metis assms(4) covector_comp_inf inf.sup_monoid.add_commute vector_conv_compl)
  also have "... \<le> z\<^sup>T \<sqinter> -z\<^sup>T"
    by (metis assms(1) comp_associative comp_inf.mult_left_isotone comp_isotone comp_right_one mult_sub_right_one)
  finally have 6: "(-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<le> 1"
    using pseudo_complement by fastforce
  have 7: "(-z \<sqinter> -y \<sqinter> x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<le> 1"
    using 3 conv_dist_comp coreflexive_symmetric by fastforce
  have 8: "(-z \<sqinter> -y \<sqinter> x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<le> 1"
    using 6 conv_dist_comp coreflexive_symmetric by fastforce
  have 9: "(-z \<sqinter> -y \<sqinter> x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<le> 1"
    using assms(1) inf.sup_monoid.add_commute injective_inf_closed by auto
  have "(x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]] = (z \<sqinter> y\<^sup>T * x) \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x) \<squnion> (-z \<sqinter> -y \<sqinter> x)"
    by (simp add: comp_inf.comp_left_dist_sup conv_dist_comp inf_assoc sup_monoid.add_assoc)
  hence "((x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]]) * ((x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]])\<^sup>T = ((z \<sqinter> y\<^sup>T * x) \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x) \<squnion> (-z \<sqinter> -y \<sqinter> x)) * ((z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x)\<^sup>T)"
    by (simp add: conv_dist_sup)
  also have "... = (z \<sqinter> y\<^sup>T * x) * ((z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x)\<^sup>T) \<squnion>
                   (-z \<sqinter> y \<sqinter> z\<^sup>T * x) * ((z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x)\<^sup>T) \<squnion>
                   (-z \<sqinter> -y \<sqinter> x) * ((z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x)\<^sup>T)"
    using mult_right_dist_sup by auto
  also have "... = (z \<sqinter> y\<^sup>T * x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (z \<sqinter> y\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<squnion>
                   (-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> y \<sqinter> z\<^sup>T * x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T \<squnion>
                   (-z \<sqinter> -y \<sqinter> x) * (z \<sqinter> y\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x) * (-z \<sqinter> y \<sqinter> z\<^sup>T * x)\<^sup>T \<squnion> (-z \<sqinter> -y \<sqinter> x) * (-z \<sqinter> -y \<sqinter> x)\<^sup>T"
    using mult_left_dist_sup sup.left_commute sup_commute by auto
  also have "... \<le> 1"
    using 1 2 3 4 5 6 7 8 9 by simp_all
  finally show ?thesis
    .
qed

lemma update_injective_swap_2:
  assumes "injective x"
    shows "injective ((x[y\<longmapsto>x[[bot]]])[bot\<longmapsto>x[[y]]])"
  by (simp add: assms inf.sup_monoid.add_commute injective_inf_closed)

text \<open>Theorem 2.9\<close>

lemma update_univalent_swap:
  assumes "univalent x"
      and "injective y"
      and "vector y"
      and "injective z"
      and "vector z"
    shows "univalent ((x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]])"
  by (simp add: assms read_injective update_univalent)

text \<open>Theorem 2.10\<close>

lemma update_mapping_swap:
  assumes "mapping x"
      and "point y"
      and "point z"
    shows "mapping ((x[y\<longmapsto>x[[z]]])[z\<longmapsto>x[[y]]])"
  by (simp add: assms bijective_regular read_injective read_surjective update_total update_univalent)

text \<open>Theorem 2.16 \<open>mapping_inf_point_arc\<close> has been moved to theory \<open>Relation_Algebras\<close> in entry \<open>Stone_Relation_Algebras\<close>\<close>

end

context stone_kleene_relation_algebra
begin

lemma omit_redundant_points_2:
  assumes "point p"
  shows "p \<sqinter> x\<^sup>\<star> = (p \<sqinter> 1) \<squnion> (p \<sqinter> x \<sqinter> -p\<^sup>T) * (x \<sqinter> -p\<^sup>T)\<^sup>\<star>"
proof -
  let ?p = "p \<sqinter> 1"
  let ?np = "-p \<sqinter> 1"
  have 1: "p \<sqinter> x\<^sup>\<star> \<sqinter> 1 = p \<sqinter> 1"
    by (metis inf.le_iff_sup inf.left_commute inf.sup_monoid.add_commute star.circ_reflexive)
  have 2: "p \<sqinter> 1 \<sqinter> -p\<^sup>T = bot"
    by (smt (z3) inf_bot_right inf_commute inf_left_commute one_inf_conv p_inf)
  have "p \<sqinter> x\<^sup>\<star> \<sqinter> -1 = p \<sqinter> x\<^sup>\<star> \<sqinter> -p\<^sup>T"
    by (metis assms antisymmetric_inf_diversity inf.cobounded1 inf.sup_relative_same_increasing vector_covector)
  also have "... = (p \<sqinter> 1 \<sqinter> -p\<^sup>T) \<squnion> ((p \<sqinter> x) * (-p \<sqinter> x)\<^sup>\<star> \<sqinter> -p\<^sup>T)"
    by (simp add: assms omit_redundant_points comp_inf.semiring.distrib_right)
  also have "... = (p \<sqinter> x) * (-p \<sqinter> x)\<^sup>\<star> \<sqinter> -p\<^sup>T"
    using 2 by simp
  also have "... = ?p * x * (-p \<sqinter> x)\<^sup>\<star> \<sqinter> -p\<^sup>T"
    by (metis assms vector_export_comp_unit)
  also have "... = ?p * x * (?np * x)\<^sup>\<star> \<sqinter> -p\<^sup>T"
    by (metis assms vector_complement_closed vector_export_comp_unit)
  also have "... = ?p * x * (?np * x)\<^sup>\<star> * ?np"
    by (metis assms conv_complement covector_comp_inf inf.sup_monoid.add_commute mult_1_right one_inf_conv vector_conv_compl)
  also have "... = ?p * x * ?np * (x * ?np)\<^sup>\<star>"
    using star_slide mult_assoc by auto
  also have "... = (?p * x \<sqinter> -p\<^sup>T) * (x * ?np)\<^sup>\<star>"
    by (metis assms conv_complement covector_comp_inf inf.sup_monoid.add_commute mult_1_right one_inf_conv vector_conv_compl)
  also have "... = (?p * x \<sqinter> -p\<^sup>T) * (x \<sqinter> -p\<^sup>T)\<^sup>\<star>"
    by (metis assms conv_complement covector_comp_inf inf.sup_monoid.add_commute mult_1_right one_inf_conv vector_conv_compl)
  also have "... = (p \<sqinter> x \<sqinter> -p\<^sup>T) * (x \<sqinter> -p\<^sup>T)\<^sup>\<star>"
    by (metis assms vector_export_comp_unit)
  finally show ?thesis
    using 1 by (metis maddux_3_11_pp regular_one_closed)
qed

text \<open>Theorem 5.3\<close>

lemma omit_redundant_points_3:
  assumes "point p"
  shows "p \<sqinter> x\<^sup>\<star> = (p \<sqinter> 1) \<squnion> (p \<sqinter> (x \<sqinter> -p\<^sup>T)\<^sup>+)"
  by (simp add: assms inf_assoc vector_inf_comp omit_redundant_points_2)

text \<open>Theorem 6.1\<close>

lemma even_odd_root:
  assumes "acyclic (x - 1)"
      and "regular x"
      and "univalent x"
    shows "(x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star> = (1 \<sqinter> x) * ((x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star>)"
proof -
  have 1: "univalent (x * x)"
    by (simp add: assms(3) univalent_mult_closed)
  have "x \<sqinter> 1 \<le> top * (x \<sqinter> 1)"
    by (simp add: top_left_mult_increasing)
  hence "x \<sqinter> -(top * (x \<sqinter> 1)) \<le> x - 1"
    using assms(2) p_shunting_swap pp_dist_comp by auto
  hence "x\<^sup>\<star> * (x \<sqinter> -(top * (x \<sqinter> 1))) \<le> (x - 1)\<^sup>\<star> * (x - 1)"
    using mult_right_isotone reachable_without_loops by auto
  also have "... \<le> -1"
    by (simp add: assms(1) star_plus)
  finally have "(x \<sqinter> -(top * (x \<sqinter> 1)))\<^sup>T \<le> -x\<^sup>\<star>"
    using schroeder_4_p by force
  hence "x\<^sup>T \<sqinter> x\<^sup>\<star> \<le> (top * (x \<sqinter> 1))\<^sup>T"
    by (smt (z3) assms(2) conv_complement conv_dist_inf p_shunting_swap regular_closed_inf regular_closed_top regular_mult_closed regular_one_closed)
  also have "... = (1 \<sqinter> x) * top"
    by (metis conv_dist_comp conv_dist_inf inf_commute one_inf_conv symmetric_one_closed symmetric_top_closed)
  finally have 2: "(x\<^sup>T \<sqinter> x\<^sup>\<star>) * top \<le> (1 \<sqinter> x) * top"
    by (metis inf.orderE inf.orderI inf_commute inf_vector_comp)
  have "1 \<sqinter> x\<^sup>T\<^sup>+ \<le> (x\<^sup>T \<sqinter> 1 * x\<^sup>\<star>) * x\<^sup>T\<^sup>\<star>"
    by (metis conv_involutive conv_star_commute dedekind_2 inf_commute)
  also have "... \<le> (x\<^sup>T \<sqinter> x\<^sup>\<star>) * top"
    by (simp add: mult_right_isotone)
  also have "... \<le> (1 \<sqinter> x) * top"
    using 2 by simp
  finally have 3: "1 \<sqinter> x\<^sup>T\<^sup>+ \<le> (1 \<sqinter> x) * top"
    .
  have "x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>+ = 1 * x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>\<star> * x\<^sup>T * x\<^sup>T"
    using star_plus mult_assoc by auto
  also have "... = (1 \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>\<star> * x\<^sup>T) * x\<^sup>T"
    using assms(3) injective_comp_right_dist_inf by force
  also have "... \<le> (1 \<sqinter> x\<^sup>T\<^sup>\<star> * x\<^sup>T) * x\<^sup>T"
    by (meson comp_inf.mult_right_isotone comp_isotone inf.eq_refl star.circ_square)
  also have "... \<le> (1 \<sqinter> x) * top * x\<^sup>T"
    using 3 by (simp add: mult_left_isotone star_plus)
  also have "... \<le> (1 \<sqinter> x) * top"
    by (simp add: comp_associative mult_right_isotone)
  finally have 4: "x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>+ \<le> (1 \<sqinter> x) * top"
    .
  have "x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>\<star> = (x\<^sup>T \<sqinter> 1) \<squnion> (x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>+)"
    by (metis inf_sup_distrib1 star_left_unfold_equal)
  also have "... \<le> (1 \<sqinter> x) * top"
    using 4 by (metis inf.sup_monoid.add_commute le_supI one_inf_conv top_right_mult_increasing)
  finally have 4: "x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>\<star> \<le> (1 \<sqinter> x) * top"
    .
  have "x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> \<sqinter> -1 \<le> x\<^sup>T \<sqinter> x\<^sup>\<star> \<sqinter> -1"
    by (simp add: inf.coboundedI2 inf.sup_monoid.add_commute star.circ_square)
  also have "... = (x - 1)\<^sup>\<star> \<sqinter> (x - 1)\<^sup>T"
    using conv_complement conv_dist_inf inf_assoc inf_left_commute reachable_without_loops symmetric_one_closed by auto
  also have "... = bot"
    using assms(1) acyclic_star_below_complement_1 by auto
  finally have 5: "x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> \<sqinter> -1 = bot"
    by (simp add: le_bot)
  have "x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> = (x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> \<sqinter> 1) \<squnion> (x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> \<sqinter> -1)"
    by (metis maddux_3_11_pp regular_one_closed)
  also have "... = x\<^sup>T \<sqinter> (x * x)\<^sup>\<star> \<sqinter> 1"
    using 5 by simp
  also have "... = x\<^sup>T \<sqinter> 1"
    by (metis calculation comp_inf.semiring.distrib_left inf.sup_monoid.add_commute star.circ_transitive_equal star_involutive star_left_unfold_equal sup_inf_absorb)
  finally have "(x\<^sup>T \<sqinter> (x * x)\<^sup>\<star>) \<squnion> (x\<^sup>T \<sqinter> (x\<^sup>T * x\<^sup>T)\<^sup>\<star>) \<le> (1 \<sqinter> x) * top"
    using 4 inf.sup_monoid.add_commute one_inf_conv top_right_mult_increasing by auto
  hence "x\<^sup>T \<sqinter> ((x * x)\<^sup>\<star> \<squnion> (x * x)\<^sup>T\<^sup>\<star>) \<le> (1 \<sqinter> x) * top"
    by (simp add: comp_inf.semiring.distrib_left conv_dist_comp)
  hence 6: "x\<^sup>T \<sqinter> (x * x)\<^sup>T\<^sup>\<star> * (x * x)\<^sup>\<star> \<le> (1 \<sqinter> x) * top"
    using 1 by (simp add: cancel_separate_eq sup_commute)
  have "(x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star> \<le> (x\<^sup>T \<sqinter> (x * x)\<^sup>T\<^sup>\<star> * (x * x)\<^sup>\<star>) * (x * x)\<^sup>T\<^sup>\<star>"
    by (metis conv_involutive conv_star_commute dedekind_2 inf_commute)
  also have "... \<le> (1 \<sqinter> x) * top * (x * x)\<^sup>T\<^sup>\<star>"
    using 6 by (simp add: mult_left_isotone)
  also have "... = (1 \<sqinter> x) * top"
    by (simp add: comp_associative star.circ_left_top)
  finally have "(x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star> = (x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star> \<sqinter> (1 \<sqinter> x) * top"
    using inf.order_iff by auto
  also have "... = (1 \<sqinter> x) * ((x * x)\<^sup>T\<^sup>\<star> \<sqinter> x\<^sup>T * (x * x)\<^sup>T\<^sup>\<star>)"
    by (metis coreflexive_comp_top_inf inf.cobounded1 inf.sup_monoid.add_commute)
  finally show ?thesis
    .
qed

lemma update_square_plus:
  "point y \<Longrightarrow> x[y\<longmapsto>x[[x[[y]]]]] \<le> x\<^sup>+"
  by (meson update_square comp_isotone dual_order.trans le_supI order_refl star.circ_increasing star.circ_mult_increasing)

lemma update_square_ub_plus:
  "x[y\<longmapsto>(x * x)\<^sup>T] \<le> x\<^sup>+"
  by (simp add: comp_isotone inf.coboundedI2 star.circ_increasing star.circ_mult_increasing)

text \<open>Theorem 6.2\<close>

lemma acyclic_square:
  assumes "acyclic (x - 1)"
    shows "x * x \<sqinter> 1 = x \<sqinter> 1"
proof (rule order.antisym)
  have "1 \<sqinter> x * x = 1 \<sqinter> ((x - 1) * x \<squnion> (x \<sqinter> 1) * x)"
    by (metis maddux_3_11_pp regular_one_closed semiring.distrib_right)
  also have "... \<le> 1 \<sqinter> ((x - 1) * x \<squnion> x)"
    by (metis inf.cobounded2 mult_1_left mult_left_isotone inf.sup_right_isotone semiring.add_left_mono)
  also have "... = 1 \<sqinter> ((x - 1) * (x - 1) \<squnion> (x - 1) * (x \<sqinter> 1) \<squnion> x)"
    by (metis maddux_3_11_pp mult_left_dist_sup regular_one_closed)
  also have "... \<le> (1 \<sqinter> (x - 1) * (x - 1)) \<squnion> (x - 1) * (x \<sqinter> 1) \<squnion> x"
    by (metis inf_le2 inf_sup_distrib1 semiring.add_left_mono sup_monoid.add_assoc)
  also have "... \<le> (1 \<sqinter> (x - 1)\<^sup>+) \<squnion> (x - 1) * (x \<sqinter> 1) \<squnion> x"
    by (metis comp_isotone inf.eq_refl inf.sup_right_isotone star.circ_increasing sup_monoid.add_commute sup_right_isotone)
  also have "... = (x - 1) * (x \<sqinter> 1) \<squnion> x"
    by (metis assms inf.le_iff_sup inf.sup_monoid.add_commute inf_import_p inf_p regular_one_closed sup_inf_absorb sup_monoid.add_commute)
  also have "... = x"
    by (metis comp_isotone inf.cobounded1 inf_le2 mult_1_right sup.absorb2)
  finally show "x * x \<sqinter> 1 \<le> x \<sqinter> 1"
    by (simp add: inf.sup_monoid.add_commute)
  show "x \<sqinter> 1 \<le> x * x \<sqinter> 1"
    by (metis coreflexive_idempotent inf_le1 inf_le2 le_infI mult_isotone)
qed

lemma diagonal_update_square_aux:
  assumes "acyclic (x - 1)"
      and "point y"
    shows "1 \<sqinter> y \<sqinter> y\<^sup>T * x * x = 1 \<sqinter> y \<sqinter> x"
proof -
  have 1: "1 \<sqinter> y \<sqinter> x \<le> y\<^sup>T * x * x"
    by (metis comp_isotone coreflexive_idempotent inf.boundedE inf.cobounded1 inf.cobounded2 one_inf_conv)
  have "1 \<sqinter> y \<sqinter> y\<^sup>T * x * x = 1 \<sqinter> (y \<sqinter> y\<^sup>T) * x * x"
    by (simp add: assms(2) inf.sup_monoid.add_assoc vector_inf_comp)
  also have "... = 1 \<sqinter> (y \<sqinter> 1) * x * x"
    by (metis assms(2) inf.cobounded1 inf.sup_monoid.add_commute inf.sup_same_context one_inf_conv vector_covector)
  also have "... \<le> 1 \<sqinter> x * x"
    by (metis comp_left_subdist_inf inf.sup_right_isotone le_infE mult_left_isotone mult_left_one)
  also have "... \<le> x"
    using assms(1) acyclic_square inf.sup_monoid.add_commute by auto
  finally show ?thesis
    using 1 by (metis inf.absorb2 inf.left_commute inf.sup_monoid.add_commute)
qed

text \<open>Theorem 6.5\<close>

lemma diagonal_update_square:
  assumes "acyclic (x - 1)"
      and "point y"
    shows "(x[y\<longmapsto>x[[x[[y]]]]]) \<sqinter> 1 = x \<sqinter> 1"
proof -
  let ?xy = "x[[y]]"
  let ?xxy = "x[[?xy]]"
  let ?xyxxy = "x[y\<longmapsto>?xxy]"
  have "?xyxxy \<sqinter> 1 = ((y \<sqinter> y\<^sup>T * x * x) \<squnion> (-y \<sqinter> x)) \<sqinter> 1"
    by (simp add: conv_dist_comp)
  also have "... = (y \<sqinter> y\<^sup>T * x * x \<sqinter> 1) \<squnion> (-y \<sqinter> x \<sqinter> 1)"
    by (simp add: inf_sup_distrib2)
  also have "... = (y \<sqinter> x \<sqinter> 1) \<squnion> (-y \<sqinter> x \<sqinter> 1)"
    using assms by (smt (verit, ccfv_threshold) diagonal_update_square_aux find_set_precondition_def inf_assoc inf_commute)
  also have "... = x \<sqinter> 1"
    by (metis assms(2) bijective_regular comp_inf.mult_right_dist_sup inf.sup_monoid.add_commute maddux_3_11_pp)
  finally show ?thesis
    .
qed

text \<open>Theorem 6.6\<close>

lemma fc_update_square:
  assumes "mapping x"
      and "point y"
    shows "fc (x[y\<longmapsto>x[[x[[y]]]]]) = fc x"
proof (rule order.antisym)
  let ?xy = "x[[y]]"
  let ?xxy = "x[[?xy]]"
  let ?xyxxy = "x[y\<longmapsto>?xxy]"
  have 1: "y \<sqinter> y\<^sup>T * x * x \<le> x * x"
    by (smt (z3) assms(2) inf.cobounded2 inf.sup_monoid.add_commute inf.sup_same_context mult_1_left one_inf_conv vector_covector vector_inf_comp)
  have 2: "?xyxxy = (y \<sqinter> y\<^sup>T * x * x) \<squnion> (-y \<sqinter> x)"
    by (simp add: conv_dist_comp)
  also have "... \<le> x * x \<squnion> x"
    using 1 inf_le2 sup_mono by blast
  also have "... \<le> x\<^sup>\<star>"
    by (simp add: star.circ_increasing star.circ_mult_upper_bound)
  finally show "fc ?xyxxy \<le> fc x"
    by (metis comp_isotone conv_order conv_star_commute star_involutive star_isotone)
  have 3: "y \<sqinter> x \<sqinter> 1 \<le> fc ?xyxxy"
    using inf.coboundedI1 inf.sup_monoid.add_commute reflexive_mult_closed star.circ_reflexive by auto
  have 4: "y - 1 \<le> -y\<^sup>T"
    using assms(2) p_shunting_swap regular_one_closed vector_covector by auto
  have "y \<sqinter> x \<le> y\<^sup>T * x"
    by (simp add: assms(2) vector_restrict_comp_conv)
  also have "... \<le> y\<^sup>T * x * x * x\<^sup>T"
    by (metis assms(1) comp_associative mult_1_right mult_right_isotone total_var)
  finally have "y \<sqinter> x \<sqinter> -1 \<le> y \<sqinter> -y\<^sup>T \<sqinter> y\<^sup>T * x * x * x\<^sup>T"
    using 4 by (smt (z3) inf.cobounded1 inf.coboundedI2 inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_greatest)
  also have "... = (y \<sqinter> y\<^sup>T * x * x) * x\<^sup>T \<sqinter> -y\<^sup>T"
    by (metis assms(2) inf.sup_monoid.add_assoc inf.sup_monoid.add_commute vector_inf_comp)
  also have "... = (y \<sqinter> y\<^sup>T * x * x) * (x\<^sup>T \<sqinter> -y\<^sup>T)"
    using assms(2) covector_comp_inf vector_conv_compl by auto
  also have "... = (y \<sqinter> y\<^sup>T * x * x) * (-y \<sqinter> x)\<^sup>T"
    by (simp add: conv_complement conv_dist_inf inf_commute)
  also have "... \<le> ?xyxxy * (-y \<sqinter> x)\<^sup>T"
    using 2 by (simp add: comp_left_increasing_sup)
  also have "... \<le> ?xyxxy * ?xyxxy\<^sup>T"
    by (simp add: conv_isotone mult_right_isotone)
  also have "... \<le> fc ?xyxxy"
    using comp_isotone star.circ_increasing by blast
  finally have 5: "y \<sqinter> x \<le> fc ?xyxxy"
    using 3 by (smt (z3) comp_inf.semiring.distrib_left inf.le_iff_sup maddux_3_11_pp regular_one_closed)
  have "x = (y \<sqinter> x) \<squnion> (-y \<sqinter> x)"
    by (metis assms(2) bijective_regular inf.sup_monoid.add_commute maddux_3_11_pp)
  also have "... \<le> fc ?xyxxy"
    using 5 dual_order.trans fc_increasing sup.cobounded2 sup_least by blast
  finally show "fc x \<le> fc ?xyxxy"
    by (smt (z3) assms fc_equivalence fc_isotone fc_wcc read_injective star.circ_decompose_9 star_decompose_1 update_univalent)
qed

text \<open>Theorem 6.2\<close>

lemma acyclic_plus_loop:
  assumes "acyclic (x - 1)"
  shows "x\<^sup>+ \<sqinter> 1 = x \<sqinter> 1"
proof -
  let ?r = "x \<sqinter> 1"
  let ?i = "x - 1"
  have "x\<^sup>+ \<sqinter> 1 = (?i \<squnion> ?r)\<^sup>+ \<sqinter> 1"
    by (metis maddux_3_11_pp regular_one_closed)
  also have "... = ((?i\<^sup>\<star> * ?r)\<^sup>\<star> * ?i\<^sup>+ \<squnion> (?i\<^sup>\<star> * ?r)\<^sup>+) \<sqinter> 1"
    using plus_sup by auto
  also have "... \<le> (?i\<^sup>+ \<squnion> (?i\<^sup>\<star> * ?r)\<^sup>+) \<sqinter> 1"
    by (metis comp_associative dual_order.eq_iff maddux_3_11_pp reachable_without_loops regular_one_closed star.circ_plus_same star.circ_sup_9)
  also have "... = (?i\<^sup>\<star> * ?r)\<^sup>+ \<sqinter> 1"
    by (smt (z3) assms comp_inf.mult_right_dist_sup inf.absorb2 inf.sup_monoid.add_commute inf_le2 maddux_3_11_pp pseudo_complement regular_one_closed)
  also have "... \<le> ?i\<^sup>\<star> * ?r \<sqinter> 1"
    by (metis comp_associative dual_order.eq_iff maddux_3_11_pp reachable_without_loops regular_one_closed star.circ_sup_9 star_slide)
  also have "... = (?r \<squnion> ?i\<^sup>+ * ?r) \<sqinter> 1"
    using comp_associative star.circ_loop_fixpoint sup_commute by force
  also have "... \<le> x \<squnion> (?i\<^sup>+ * ?r \<sqinter> 1)"
    by (metis comp_inf.mult_right_dist_sup inf.absorb1 inf.cobounded1 inf.cobounded2)
  also have "... \<le> x \<squnion> (-1 * ?r \<sqinter> 1)"
    by (meson assms comp_inf.comp_isotone mult_left_isotone order.refl semiring.add_left_mono)
  also have "... = x"
    by (metis comp_inf.semiring.mult_not_zero comp_right_one inf.cobounded2 inf_sup_absorb mult_right_isotone pseudo_complement sup.idem sup_inf_distrib1)
  finally show ?thesis
    by (meson inf.sup_same_context inf_le1 order_trans star.circ_mult_increasing)
qed

lemma star_irreflexive_part_eq:
  "x\<^sup>\<star> - 1 = (x - 1)\<^sup>+ - 1"
  by (metis reachable_without_loops star_plus_without_loops)

text \<open>Theorem 6.3\<close>

lemma star_irreflexive_part:
  "x\<^sup>\<star> - 1 \<le> (x - 1)\<^sup>+"
  using star_irreflexive_part_eq by auto

lemma square_irreflexive_part:
  "x * x - 1 \<le> (x - 1)\<^sup>+"
proof -
  have "x * x = (x \<sqinter> 1) * x \<squnion> (x - 1) * x"
    by (metis maddux_3_11_pp mult_right_dist_sup regular_one_closed)
  also have "... \<le> 1 * x \<squnion> (x - 1) * x"
    using comp_isotone inf.cobounded2 semiring.add_right_mono by blast
  also have "... \<le> 1 \<squnion> (x - 1) \<squnion> (x - 1) * x"
    by (metis inf.cobounded2 maddux_3_11_pp mult_1_left regular_one_closed sup_left_isotone)
  also have "... = (x - 1) * (x \<squnion> 1) \<squnion> 1"
    by (simp add: mult_left_dist_sup sup_assoc sup_commute)
  finally have "x * x - 1 \<le> (x - 1) * (x \<squnion> 1)"
    using shunting_var_p by auto
  also have "... = (x - 1) * (x - 1) \<squnion> (x - 1)"
    by (metis comp_right_one inf.sup_monoid.add_commute maddux_3_21_pp mult_left_dist_sup regular_one_closed sup_commute)
  also have "... \<le> (x - 1)\<^sup>+"
    by (metis mult_left_isotone star.circ_increasing star.circ_mult_increasing star.circ_plus_same sup.bounded_iff)
  finally show ?thesis
    .
qed

text \<open>Theorem 6.3\<close>

lemma square_irreflexive_part_2:
  "x * x - 1 \<le> x\<^sup>\<star> - 1"
  using comp_inf.mult_left_isotone star.circ_increasing star.circ_mult_upper_bound by blast

text \<open>Theorem 6.8\<close>

lemma acyclic_update_square:
  assumes "acyclic (x - 1)"
  shows "acyclic ((x[y\<longmapsto>(x * x)\<^sup>T]) - 1)"
proof -
  have "((x[y\<longmapsto>(x * x)\<^sup>T]) - 1)\<^sup>+ \<le> ((x \<squnion> x * x) - 1)\<^sup>+"
    by (metis comp_inf.mult_right_isotone comp_isotone inf.sup_monoid.add_commute star_isotone update_square_ub)
  also have "... = ((x - 1) \<squnion> (x * x - 1))\<^sup>+"
    using comp_inf.semiring.distrib_right by auto
  also have "... \<le> ((x - 1)\<^sup>+)\<^sup>+"
    by (smt (verit, del_insts) comp_isotone reachable_without_loops star.circ_mult_increasing star.circ_plus_same star.circ_right_slide star.circ_separate_5 star.circ_square star.circ_transitive_equal star.left_plus_circ sup.bounded_iff sup_ge1 square_irreflexive_part)
  also have "... \<le> -1"
    using assms by (simp add: acyclic_plus)
  finally show ?thesis
    .
qed

text \<open>Theorem 6.9\<close>

lemma disjoint_set_forest_update_square:
  assumes "disjoint_set_forest x"
      and "vector y"
      and "regular y"
    shows "disjoint_set_forest (x[y\<longmapsto>(x * x)\<^sup>T])"
proof (intro conjI)
  show "univalent (x[y\<longmapsto>(x * x)\<^sup>T])"
    using assms update_univalent mapping_mult_closed univalent_conv_injective by blast
  show "total (x[y\<longmapsto>(x * x)\<^sup>T])"
    using assms update_total total_conv_surjective total_mult_closed by blast
  show "acyclic ((x[y\<longmapsto>(x * x)\<^sup>T]) - 1)"
    using acyclic_update_square assms(1) by blast
qed

lemma disjoint_set_forest_update_square_point:
  assumes "disjoint_set_forest x"
      and "point y"
    shows "disjoint_set_forest (x[y\<longmapsto>(x * x)\<^sup>T])"
  using assms disjoint_set_forest_update_square bijective_regular by blast

end

section \<open>Verifying Further Operations on Disjoint-Set Forests\<close>

text \<open>
In this section we verify the init-sets, path-halving and path-splitting operations of disjoint-set forests.
\<close>

class choose_point =
  fixes choose_point :: "'a \<Rightarrow> 'a"

text \<open>
Using the \<open>choose_point\<close> operation we define a simple for-each-loop abstraction as syntactic sugar translated to a while-loop.
Regular vector \<open>h\<close> describes the set of all elements that are yet to be processed.
It is made explicit so that the invariant can refer to it.
\<close>

syntax
  "_Foreach" :: "idt \<Rightarrow> idt \<Rightarrow> 'assn \<Rightarrow> 'com \<Rightarrow> 'com"  ("(1FOREACH _/ USING _/ INV {_} //DO _ /OD)" [0,0,0,0] 61)
translations "FOREACH x USING h INV { i } DO c OD" =>
  "h := CONST top;
   WHILE h \<noteq> CONST bot
     INV { CONST regular h \<and> CONST vector h \<and> i }
     VAR { h\<down> }
      DO x := CONST choose_point h;
         c;
         h[x] := CONST bot
      OD"

class stone_kleene_relation_algebra_choose_point_finite_regular = stone_kleene_relation_algebra + finite_regular_p_algebra + choose_point +
  assumes choose_point_point: "vector x \<Longrightarrow> x \<noteq> bot \<Longrightarrow> point (choose_point x)"
  assumes choose_point_decreasing: "choose_point x \<le> --x"
begin

subclass stone_kleene_relation_algebra_tarski_finite_regular
proof unfold_locales
  fix x
  let ?p = "choose_point (x * top)"
  let ?q = "choose_point ((?p \<sqinter> x)\<^sup>T * top)"
  let ?y = "?p \<sqinter> ?q\<^sup>T"
  assume 1: "regular x" "x \<noteq> bot"
  hence 2: "x * top \<noteq> bot"
    using le_bot top_right_mult_increasing by auto
  hence 3: "point ?p"
    by (simp add: choose_point_point comp_associative)
  hence 4: "?p \<noteq> bot"
    using 2 mult_right_zero by force
  have "?p \<sqinter> x \<noteq> bot"
  proof
    assume "?p \<sqinter> x = bot"
    hence 5: "x \<le> -?p"
      using p_antitone_iff pseudo_complement by auto
    have "?p \<le> --(x * top)"
      by (simp add: choose_point_decreasing)
    also have "... \<le> --(-?p * top)"
      using 5 by (simp add: comp_isotone pp_isotone)
    also have "... = -?p * top"
      using regular_mult_closed by auto
    also have "... = -?p"
      using 3 vector_complement_closed by auto
    finally have "?p = bot"
      using inf_absorb2 by fastforce
    thus False
      using 4 by auto
  qed
  hence "(?p \<sqinter> x)\<^sup>T * top \<noteq> bot"
    by (metis comp_inf.semiring.mult_zero_left comp_right_one inf.sup_monoid.add_commute inf_top.left_neutral schroeder_1)
  hence "point ?q"
    using choose_point_point vector_top_closed mult_assoc by auto
  hence 6: "arc ?y"
    using 3 by (smt bijective_conv_mapping inf.sup_monoid.add_commute mapping_inf_point_arc)
  have "?q \<le> --((?p \<sqinter> x)\<^sup>T * top)"
    by (simp add: choose_point_decreasing)
  hence "?y \<le> ?p \<sqinter> --((?p \<sqinter> x)\<^sup>T * top)\<^sup>T"
    by (metis conv_complement conv_isotone inf.sup_right_isotone)
  also have "... = ?p \<sqinter> --(top * (?p \<sqinter> x))"
    by (simp add: conv_dist_comp)
  also have "... = ?p \<sqinter> top * (?p \<sqinter> x)"
    using 1 3 bijective_regular pp_dist_comp by auto
  also have "... = ?p \<sqinter> ?p\<^sup>T * x"
    using 3 by (metis comp_inf_vector conv_dist_comp inf.sup_monoid.add_commute inf_top_right symmetric_top_closed)
  also have "... = (?p \<sqinter> ?p\<^sup>T) * x"
    using 3 by (simp add: vector_inf_comp)
  also have "... \<le> 1 * x"
    using 3 point_antisymmetric mult_left_isotone by blast
  finally have "?y \<le> x"
    by simp
  thus "top * x * top = top"
    using 6 by (smt (verit, ccfv_SIG) mult_assoc le_iff_sup mult_left_isotone semiring.distrib_left sup.orderE top.extremum)
qed

subsection \<open>Init-Sets\<close>

text \<open>
A disjoint-set forest is initialised by applying \<open>make_set\<close> to each node.
We prove that the resulting disjoint-set forest is the identity relation.
\<close>

theorem init_sets:
  "VARS h p x
  [ True ]
  FOREACH x
    USING h
      INV { p - h = 1 - h }
       DO p := make_set p x
       OD
  [ p = 1 \<and> disjoint_set_forest p \<and> h = bot ]"
proof vcg_tc_simp
  fix h p
  let ?x = "choose_point h"
  let ?m = "make_set p ?x"
  assume 1: "regular h \<and> vector h \<and> p - h = 1 - h \<and> h \<noteq> bot"
  show "vector (-?x \<sqinter> h) \<and>
        ?m \<sqinter> (--?x \<squnion> -h) = 1 \<sqinter> (--?x \<squnion> -h) \<and>
        card { x . regular x \<and> x \<le> -?x \<and> x \<le> h } < h\<down>"
  proof (intro conjI)
    show "vector (-?x \<sqinter> h)"
      using 1 choose_point_point vector_complement_closed vector_inf_closed by blast
    have 2: "point ?x \<and> regular ?x"
      using 1 bijective_regular choose_point_point by blast
    have 3: "-h \<le> -?x"
      using choose_point_decreasing p_antitone_iff by auto
    have 4: "?x \<sqinter> ?m = ?x * ?x\<^sup>T \<and> -?x \<sqinter> ?m = -?x \<sqinter> p"
      using 1 choose_point_point make_set_function make_set_postcondition_def by auto
    have "?m \<sqinter> (--?x \<squnion> -h) = (?m \<sqinter> ?x) \<squnion> (?m - h)"
      using 2 comp_inf.comp_left_dist_sup by auto
    also have "... = ?x * ?x\<^sup>T \<squnion> (?m \<sqinter> -?x \<sqinter> -h)"
      using 3 4 by (smt (z3) inf_absorb2 inf_assoc inf_commute)
    also have "... = ?x * ?x\<^sup>T \<squnion> (1 - h)"
      using 1 3 4 inf.absorb2 inf.sup_monoid.add_assoc inf_commute by auto
    also have "... = (1 \<sqinter> ?x) \<squnion> (1 - h)"
      using 2 by (metis inf.cobounded2 inf.sup_same_context one_inf_conv vector_covector)
    also have "... = 1 \<sqinter> (--?x \<squnion> -h)"
      using 2 comp_inf.semiring.distrib_left by auto
    finally show "?m \<sqinter> (--?x \<squnion> -h) = 1 \<sqinter> (--?x \<squnion> -h)"
      .
    have 5: "\<not> ?x \<le> -?x"
      using 1 2 by (metis comp_commute_below_diversity conv_order inf.cobounded2 inf_absorb2 pseudo_complement strict_order_var top.extremum)
    have 6: "?x \<le> h"
      using 1 by (metis choose_point_decreasing)
    show "card { x . regular x \<and> x \<le> -?x \<and> x \<le> h } < h\<down>"
      apply (rule psubset_card_mono)
      using finite_regular apply simp
      using 2 5 6 by auto
  qed
qed

end

subsection \<open>Path Halving\<close>

text \<open>
Path halving is a variant of the path compression technique.
Similarly to path compression, we implement path halving independently of find-set, using a second while-loop which iterates over the same path to the root.
We prove that path halving preserves the equivalence-relational semantics of the disjoint-set forest and also preserves the roots of the component trees.
Additionally we prove the exact effect of path halving, which is to replace every other parent pointer with a pointer to the respective grandparent.
\<close>

context stone_kleene_relation_algebra_tarski_finite_regular
begin

definition "path_halving_invariant p x y p0 \<equiv> 
  find_set_precondition p x \<and> point y \<and> y \<le> p\<^sup>T\<^sup>\<star> * x \<and> y \<le> (p0 * p0)\<^sup>T\<^sup>\<star> * x \<and>
  p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * y\<longmapsto>(p0 * p0)\<^sup>T] = p \<and>
  disjoint_set_forest p0"
definition "path_halving_postcondition p x y p0 \<equiv> 
  path_compression_precondition p x y \<and> p \<sqinter> 1 = p0 \<sqinter> 1 \<and> fc p = fc p0 \<and>
  p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p"

lemma path_halving_invariant_aux_1:
  assumes "point x"
      and "point y"
      and "disjoint_set_forest p0"
  shows "p0 \<le> wcc (p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * y\<longmapsto>(p0 * p0)\<^sup>T])"
proof -
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?p2ts = "?p2t\<^sup>\<star>"
  let ?px = "?p2ts * x"
  let ?py = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  have 1: "regular ?pxy"
    using assms(1,3) bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_halving_invariant_def by auto
  have 2: "vector x \<and> vector ?px \<and> vector ?py"
    using assms(1,2) find_set_precondition_def vector_complement_closed vector_mult_closed path_halving_invariant_def by auto
  have 3: "?pxy \<sqinter> p0 \<sqinter> -?p2 \<le> -?px\<^sup>T"
  proof -
    have 4: "injective x \<and> univalent ?p2 \<and> regular p0"
      using assms(1,3) find_set_precondition_def mapping_regular univalent_mult_closed path_halving_invariant_def by auto
    have "?p2\<^sup>\<star> * p0 \<sqinter> 1 \<le> p0\<^sup>+ \<sqinter> 1"
      using comp_inf.mult_left_isotone comp_isotone comp_right_one mult_sub_right_one star.circ_square star_slide by auto
    also have "... \<le> p0"
      using acyclic_plus_loop assms(3) path_halving_invariant_def by auto
    finally have 5: "?p2\<^sup>\<star> * p0 \<sqinter> 1 \<le> p0"
      .
    hence 6: "?p2ts * (1 - p0) \<le> -p0"
      by (smt (verit, ccfv_SIG) conv_star_commute dual_order.trans inf.sup_monoid.add_assoc order.refl p_antitone_iff pseudo_complement schroeder_4_p schroeder_6_p)
    have "?p2t\<^sup>+ * p0 \<sqinter> 1 = ?p2ts * p0\<^sup>T * (p0\<^sup>T * p0) \<sqinter> 1"
      by (metis conv_dist_comp star_plus mult_assoc)
    also have "... \<le> ?p2ts * p0\<^sup>T \<sqinter> 1"
      by (metis assms(3) comp_inf.mult_left_isotone comp_isotone comp_right_one mult_sub_right_one)
    also have "... \<le> p0"
      using 5 by (metis conv_dist_comp conv_star_commute inf_commute one_inf_conv star_slide)
    finally have "?p2t\<^sup>+ * p0 \<le> -1 \<squnion> p0"
      by (metis regular_one_closed shunting_var_p sup_commute)
    hence 7: "?p2\<^sup>+ * (1 - p0) \<le> -p0"
      by (smt (z3) conv_dist_comp conv_star_commute half_shunting inf.sup_monoid.add_assoc inf.sup_monoid.add_commute pseudo_complement schroeder_4_p schroeder_6_p star.circ_plus_same)
    have "(1 \<sqinter> ?px) * top * (1 \<sqinter> ?px \<sqinter> -p0) = ?px \<sqinter> top * (1 \<sqinter> ?px \<sqinter> -p0)"
      using 2 by (metis inf_commute vector_inf_one_comp mult_assoc)
    also have "... = ?px \<sqinter> ?px\<^sup>T * (1 - p0)"
      using 2 by (smt (verit, ccfv_threshold) covector_inf_comp_3 inf.sup_monoid.add_assoc inf.sup_monoid.add_commute inf_top.left_neutral)
    also have "... = ?px \<sqinter> x\<^sup>T * ?p2\<^sup>\<star> * (1 - p0)"
      by (simp add: conv_dist_comp conv_star_commute)
    also have "... = (?px \<sqinter> x\<^sup>T) * ?p2\<^sup>\<star> * (1 - p0)"
      using 2 vector_inf_comp by auto
    also have "... = ?p2ts * (x * x\<^sup>T) * ?p2\<^sup>\<star> * (1 - p0)"
      using 2 vector_covector mult_assoc by auto
    also have "... \<le> ?p2ts * ?p2\<^sup>\<star> * (1 - p0)"
      using 4 by (metis inf.order_lesseq_imp mult_left_isotone star.circ_mult_upper_bound star.circ_reflexive)
    also have "... = (?p2ts \<squnion> ?p2\<^sup>\<star>) * (1 - p0)"
      using 4 by (simp add: cancel_separate_eq)
    also have "... = (?p2ts \<squnion> ?p2\<^sup>+) * (1 - p0)"
      by (metis star.circ_plus_one star_plus_loops sup_assoc sup_commute)
    also have "... \<le> -p0"
      using 6 7 by (simp add: mult_right_dist_sup)
    finally have "(1 \<sqinter> ?px)\<^sup>T * p0 * (1 \<sqinter> ?px \<sqinter> -p0)\<^sup>T \<le> bot"
      by (smt (z3) inf.boundedI inf_p top.extremum triple_schroeder_p)
    hence 8: "(1 \<sqinter> ?px) * p0 * (1 \<sqinter> ?px \<sqinter> -p0) = bot"
      by (simp add: coreflexive_inf_closed coreflexive_symmetric le_bot)
    have "?px \<sqinter> p0 \<sqinter> ?px\<^sup>T = (1 \<sqinter> ?px) * p0 \<sqinter> ?px\<^sup>T"
      using 2 inf_commute vector_inf_one_comp by fastforce
    also have "... = (1 \<sqinter> ?px) * p0 * (1 \<sqinter> ?px)"
      using 2 by (metis comp_inf_vector mult_1_right vector_conv_covector)
    also have "... = (1 \<sqinter> ?px) * p0 * (1 \<sqinter> ?px \<sqinter> p0) \<squnion> (1 \<sqinter> ?px) * p0 * (1 \<sqinter> ?px \<sqinter> -p0)"
      using 4 by (metis maddux_3_11_pp mult_left_dist_sup)
    also have "... = (1 \<sqinter> ?px) * p0 * (1 \<sqinter> ?px \<sqinter> p0)"
      using 8 by simp
    also have "... \<le> ?p2"
      by (metis comp_isotone coreflexive_comp_top_inf inf.cobounded1 inf.cobounded2)
    finally have "?px \<sqinter> p0 \<sqinter> -?p2 \<le> -?px\<^sup>T"
      using 4 p_shunting_swap regular_mult_closed by fastforce
    thus ?thesis
      by (meson comp_inf.mult_left_isotone dual_order.trans inf.cobounded1)
  qed
  have "p0 \<le> ?p2 * p0\<^sup>T"
    by (metis assms(3) comp_associative comp_isotone comp_right_one eq_refl total_var)
  hence "?pxy \<sqinter> p0 \<sqinter> -?p2 \<le> ?p2 * p0\<^sup>T"
    by (metis inf.coboundedI1 inf.sup_monoid.add_commute)
  hence "?pxy \<sqinter> p0 \<sqinter> -?p2 \<le> ?pxy \<sqinter> ?p2 * p0\<^sup>T \<sqinter> -?px\<^sup>T"
    using 3 by (meson dual_order.trans inf.boundedI inf.cobounded1)
  also have "... = (?pxy \<sqinter> ?p2) * p0\<^sup>T \<sqinter> -?px\<^sup>T"
    using 2 vector_inf_comp by auto
  also have "... = (?pxy \<sqinter> ?p2) * (-?px \<sqinter> p0)\<^sup>T"
    using 2 by (simp add: covector_comp_inf inf.sup_monoid.add_commute vector_conv_compl conv_complement conv_dist_inf)
  also have "... \<le> ?p * (-?px \<sqinter> p0)\<^sup>T"
    using comp_left_increasing_sup by auto
  also have "... \<le> ?p * ?p\<^sup>T"
    by (metis comp_inf.mult_right_isotone comp_isotone conv_isotone inf.eq_refl inf.sup_monoid.add_commute le_supI1 p_antitone_inf sup_commute)
  also have "... \<le> wcc ?p"
    using star.circ_sub_dist_2 by auto
  finally have 9: "?pxy \<sqinter> p0 \<sqinter> -?p2 \<le> wcc ?p"
    .
  have "p0 = (?pxy \<sqinter> p0) \<squnion> (-?pxy \<sqinter> p0)"
    using 1 by (metis inf.sup_monoid.add_commute maddux_3_11_pp)
  also have "... \<le> (?pxy \<sqinter> p0) \<squnion> ?p"
    using sup_right_isotone by auto
  also have "... = (?pxy \<sqinter> p0 \<sqinter> -?p2) \<squnion> (?pxy \<sqinter> p0 \<sqinter> ?p2) \<squnion> ?p"
    by (smt (z3) assms(3) maddux_3_11_pp mapping_regular pp_dist_comp path_halving_invariant_def)
  also have "... \<le> (?pxy \<sqinter> p0 \<sqinter> -?p2) \<squnion> (?pxy \<sqinter> ?p2) \<squnion> ?p"
    by (meson comp_inf.comp_left_subdist_inf inf.boundedE semiring.add_left_mono semiring.add_right_mono)
  also have "... = (?pxy \<sqinter> p0 \<sqinter> -?p2) \<squnion> ?p"
    using sup_assoc by auto
  also have "... \<le> wcc ?p \<squnion> ?p"
    using 9 sup_left_isotone by blast
  also have "... \<le> wcc ?p"
    by (simp add: star.circ_sub_dist_1)
  finally show ?thesis
    .
qed

lemma path_halving_invariant_aux:
  assumes "path_halving_invariant p x y p0"
  shows "p[[y]] = p0[[y]]"
    and "p[[p[[y]]]] = p0[[p0[[y]]]]"
    and "p[[p[[p[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    and "p \<sqinter> 1 = p0 \<sqinter> 1"
    and "fc p = fc p0"
proof -
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?p2ts = "?p2t\<^sup>\<star>"
  let ?px = "?p2ts * x"
  let ?py = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  have "?p[[y]] = p0[[y]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_halving_invariant_def apply force
    by (meson inf.cobounded2 order_lesseq_imp p_antitone_iff path_compression_1b)
  thus 1: "p[[y]] = p0[[y]]"
    using assms path_halving_invariant_def by auto
  have "?p[[p0[[y]]]] = p0[[p0[[y]]]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_halving_invariant_def apply force
    by (metis comp_isotone inf.boundedE inf.coboundedI2 inf.eq_refl p_antitone_iff selection_closed_id star.circ_increasing)
  thus 2: "p[[p[[y]]]] = p0[[p0[[y]]]]"
    using 1 assms path_halving_invariant_def by auto
  have "?p[[p0[[p0[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_halving_invariant_def apply force
    by (metis comp_associative comp_isotone conv_dist_comp conv_involutive conv_order inf.coboundedI2 inf.le_iff_sup mult_left_isotone p_antitone_iff p_antitone_inf star.circ_increasing star.circ_transitive_equal)
  thus "p[[p[[p[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    using 2 assms path_halving_invariant_def by auto
  have 3: "regular ?pxy"
    using assms bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_halving_invariant_def by auto
  have "p \<sqinter> 1 = ?p \<sqinter> 1"
    using assms path_halving_invariant_def by auto
  also have "... = (?pxy \<sqinter> ?p2 \<sqinter> 1) \<squnion> (-?pxy \<sqinter> p0 \<sqinter> 1)"
    using comp_inf.semiring.distrib_right conv_involutive by auto
  also have "... = (?pxy \<sqinter> p0 \<sqinter> 1) \<squnion> (-?pxy \<sqinter> p0 \<sqinter> 1)"
    using assms acyclic_square path_halving_invariant_def inf.sup_monoid.add_assoc by auto
  also have "... = (?pxy \<squnion> -?pxy) \<sqinter> p0 \<sqinter> 1"
    using inf_sup_distrib2 by auto
  also have "... = p0 \<sqinter> 1"
    using 3 by (metis inf.sup_monoid.add_commute inf_sup_distrib1 maddux_3_11_pp)
  finally show "p \<sqinter> 1 = p0 \<sqinter> 1"
    .
  have "p \<le> p0\<^sup>+"
    by (metis assms path_halving_invariant_def update_square_ub_plus)
  hence 4: "fc p \<le> fc p0"
    using conv_plus_commute fc_isotone star.left_plus_circ by fastforce
  have "wcc p0 \<le> wcc ?p"
    by (meson assms wcc_below_wcc path_halving_invariant_aux_1 path_halving_invariant_def find_set_precondition_def)
  hence "fc p0 \<le> fc ?p"
    using assms find_set_precondition_def path_halving_invariant_def fc_wcc by auto
  thus "fc p = fc p0"
    using 4 assms path_halving_invariant_def by auto
qed

lemma path_halving_1:
  "find_set_precondition p0 x \<Longrightarrow> path_halving_invariant p0 x x p0"
proof -
  assume 1: "find_set_precondition p0 x"
  show "path_halving_invariant p0 x x p0"
  proof (unfold path_halving_invariant_def, intro conjI)
    show "find_set_precondition p0 x"
      using 1 by simp
    show "vector x" "injective x" "surjective x"
      using 1 find_set_precondition_def by auto
    show "x \<le> p0\<^sup>T\<^sup>\<star> * x"
      by (simp add: path_compression_1b)
    show "x \<le> (p0 * p0)\<^sup>T\<^sup>\<star> * x"
      by (simp add: path_compression_1b)
    have "(p0 * p0)\<^sup>T\<^sup>\<star> * x \<le> p0\<^sup>T\<^sup>\<star> * x"
      by (simp add: conv_dist_comp mult_left_isotone star.circ_square)
    thus "p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p0"
      by (smt (z3) inf.le_iff_sup inf_commute maddux_3_11_pp p_antitone_inf pseudo_complement)
    show "univalent p0" "total p0" "acyclic (p0 - 1)"
      using 1 find_set_precondition_def by auto
  qed
qed

lemma path_halving_2:
  "path_halving_invariant p x y p0 \<and> y \<noteq> p[[y]] \<Longrightarrow> path_halving_invariant (p[y\<longmapsto>p[[p[[y]]]]]) x ((p[y\<longmapsto>p[[p[[y]]]]])[[y]]) p0 \<and> ((p[y\<longmapsto>p[[p[[y]]]]])\<^sup>T\<^sup>\<star> * ((p[y\<longmapsto>p[[p[[y]]]]])[[y]]))\<down> < (p\<^sup>T\<^sup>\<star> * y)\<down>"
proof -
  let ?py = "p[[y]]"
  let ?ppy = "p[[?py]]"
  let ?pyppy = "p[y\<longmapsto>?ppy]"
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?p2ts = "?p2t\<^sup>\<star>"
  let ?px = "?p2ts * x"
  let ?py2 = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py2"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  let ?pty = "p0\<^sup>T * y"
  let ?pt2y = "p0\<^sup>T * p0\<^sup>T * y"
  let ?pt2sy = "p0\<^sup>T\<^sup>\<star> * p0\<^sup>T * p0\<^sup>T * y"
  assume 1: "path_halving_invariant p x y p0 \<and> y \<noteq> ?py"
  have 2: "point ?pty \<and> point ?pt2y"
    using 1 by (smt (verit) comp_associative read_injective read_surjective path_halving_invariant_def)
  show "path_halving_invariant ?pyppy x (?pyppy[[y]]) p0 \<and> (?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]]))\<down> < (p\<^sup>T\<^sup>\<star> * y)\<down>"
  proof
    show "path_halving_invariant ?pyppy x (?pyppy[[y]]) p0"
    proof (unfold path_halving_invariant_def, intro conjI)
      show 3: "find_set_precondition ?pyppy x"
      proof (unfold find_set_precondition_def, intro conjI)
        show "univalent ?pyppy"
          using 1 find_set_precondition_def read_injective update_univalent path_halving_invariant_def by auto
        show "total ?pyppy"
          using 1 bijective_regular find_set_precondition_def read_surjective update_total path_halving_invariant_def by force
        show "acyclic (?pyppy - 1)"
          apply (rule update_acyclic_3)
          using 1 find_set_precondition_def path_halving_invariant_def apply blast
          using 1 2 comp_associative path_halving_invariant_aux(2) apply force
          using 1 path_halving_invariant_def apply blast
          by (metis inf.order_lesseq_imp mult_isotone star.circ_increasing star.circ_square mult_assoc)
        show "vector x" "injective x" "surjective x"
          using 1 find_set_precondition_def path_halving_invariant_def by auto
      qed
      show "vector (?pyppy[[y]])"
        using 1 comp_associative path_halving_invariant_def by auto
      show "injective (?pyppy[[y]])"
        using 1 3 read_injective path_halving_invariant_def find_set_precondition_def by auto
      show "surjective (?pyppy[[y]])"
        using 1 3 read_surjective path_halving_invariant_def find_set_precondition_def by auto
      show "?pyppy[[y]] \<le> ?pyppy\<^sup>T\<^sup>\<star> * x"
      proof -
        have "y = (y \<sqinter> p\<^sup>T\<^sup>\<star>) * x"
          using 1 le_iff_inf vector_inf_comp path_halving_invariant_def by auto
        also have "... = ((y \<sqinter> 1) \<squnion> (y \<sqinter> (p\<^sup>T \<sqinter> -y\<^sup>T)\<^sup>+)) * x"
          using 1 omit_redundant_points_3 path_halving_invariant_def by auto
        also have "... \<le> (1 \<squnion> (y \<sqinter> (p\<^sup>T \<sqinter> -y\<^sup>T)\<^sup>+)) * x"
          using 1 sup_inf_distrib2 vector_inf_comp path_halving_invariant_def by auto
        also have "... \<le> (1 \<squnion> (p\<^sup>T \<sqinter> -y\<^sup>T)\<^sup>+) * x"
          by (simp add: inf.coboundedI2 mult_left_isotone)
        also have "... = (p \<sqinter> -y)\<^sup>T\<^sup>\<star> * x"
          by (simp add: conv_complement conv_dist_inf star_left_unfold_equal)
        also have "... \<le> ?pyppy\<^sup>T\<^sup>\<star> * x"
          by (simp add: conv_isotone inf.sup_monoid.add_commute mult_left_isotone star_isotone)
        finally show ?thesis
          by (metis mult_isotone star.circ_increasing star.circ_transitive_equal mult_assoc)
      qed
      show "?pyppy[[y]] \<le> ?px"
      proof -
        have "?pyppy[[y]] = p[[?py]]"
          using 1 put_get vector_mult_closed path_halving_invariant_def by force
        also have "... = p0[[p0[[y]]]]"
          using 1 path_halving_invariant_aux(2) by blast
        also have "... = ?p2t * y"
          by (simp add: conv_dist_comp mult_assoc)
        also have "... \<le> ?p2t * ?px"
          using 1 path_halving_invariant_def comp_associative mult_right_isotone by force
        also have "... \<le> ?px"
          by (metis comp_associative mult_left_isotone star.left_plus_below_circ)
        finally show ?thesis
          .
      qed
      show "p0[?px - p0\<^sup>T\<^sup>\<star> * (?pyppy[[y]])\<longmapsto>?p2t] = ?pyppy"
      proof -
        have "?px \<sqinter> ?pty = ?px \<sqinter> p0\<^sup>T * ?px \<sqinter> ?pty"
          using 1 inf.absorb2 inf.sup_monoid.add_assoc mult_right_isotone path_halving_invariant_def by force
        also have "... = (?p2ts \<sqinter> p0\<^sup>T * ?p2ts) * x \<sqinter> ?pty"
          using 3 comp_associative find_set_precondition_def injective_comp_right_dist_inf by auto
        also have "... = (1 \<sqinter> p0) * (?p2ts \<sqinter> p0\<^sup>T * ?p2ts) * x \<sqinter> ?pty"
          using 1 even_odd_root mapping_regular path_halving_invariant_def by auto
        also have "... \<le> (1 \<sqinter> p0) * top \<sqinter> ?pty"
          by (metis comp_associative comp_inf.mult_left_isotone comp_inf.star.circ_sub_dist_2 comp_left_subdist_inf dual_order.trans mult_right_isotone)
        also have 4: "... = (1 \<sqinter> p0\<^sup>T) * ?pty"
          using coreflexive_comp_top_inf one_inf_conv by auto
        also have "... \<le> ?pt2y"
          by (simp add: mult_assoc mult_left_isotone)
        finally have 5: "?px \<sqinter> ?pty \<le> ?pt2y"
          .
        have 6: "p[?px \<sqinter> -?pt2sy \<sqinter> ?pty\<longmapsto>?p2t] = p"
        proof (cases "?pty \<le> ?px \<sqinter> -?pt2sy")
          case True
          hence "?pty \<le> ?pt2y"
            using 5 conv_dist_comp inf.absorb2 by auto
          hence 7: "?pty = ?pt2y"
            using 2 epm_3 by fastforce
          have "p[?px \<sqinter> -?pt2sy \<sqinter> ?pty\<longmapsto>?p2t] = p[?pty\<longmapsto>?p2t]"
            using True inf.absorb2 by auto
          also have "... = p[?pty\<longmapsto>?p2[[?pty]]]"
            using 2 update_point_get by auto
          also have "... = p[?pty\<longmapsto>p0\<^sup>T * p0\<^sup>T * p0\<^sup>T * y]"
            using comp_associative conv_dist_comp by auto
          also have "... = p[?pty\<longmapsto>?pt2y]"
            using 7 mult_assoc by simp
          also have "... = p[?pty\<longmapsto>p[[?pty]]]"
            using 1 path_halving_invariant_aux(1,2) mult_assoc by force
          also have "... = p"
            using 2 get_put by auto
          finally show ?thesis
            .
        next
          case False
          have "mapping ?p2"
            using 1 mapping_mult_closed path_halving_invariant_def by blast
          hence 8: "regular (?px \<sqinter> -?pt2sy)"
            using 1 bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_halving_invariant_def by auto
          have "vector (?px \<sqinter> -?pt2sy)"
            using 1 find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_halving_invariant_def by force
          hence "?pty \<le> -(?px \<sqinter> -?pt2sy)"
            using 2 8 point_in_vector_or_complement False by blast
          hence "?px \<sqinter> -?pt2sy \<sqinter> ?pty = bot"
            by (simp add: p_antitone_iff pseudo_complement)
          thus ?thesis
            by simp
        qed
        have 9: "p[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t] = ?pyppy"
        proof (cases "y \<le> -?pt2sy")
          case True
          hence "p[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t] = p[y\<longmapsto>?p2t]"
            using 1 inf.absorb2 path_halving_invariant_def by auto
          also have "... = ?pyppy"
            using 1 by (metis comp_associative conv_dist_comp path_halving_invariant_aux(2) path_halving_invariant_def update_point_get)
          finally show ?thesis
            .
        next
          case False
          have "vector (-?pt2sy)"
            using 1 vector_complement_closed vector_mult_closed path_halving_invariant_def by blast
          hence 10: "y \<le> ?pt2sy"
            using 1 by (smt (verit, del_insts) False bijective_regular point_in_vector_or_complement regular_closed_star regular_mult_closed total_conv_surjective univalent_conv_injective path_halving_invariant_def)
          hence "?px \<sqinter> -?pt2sy \<sqinter> y = bot"
            by (simp add: inf.coboundedI2 p_antitone pseudo_complement)
          hence 11: "p[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t] = p"
            by simp
          have "y \<le> p0\<^sup>T\<^sup>+ * y"
            using 10 by (metis mult_left_isotone order_lesseq_imp star.circ_plus_same star.left_plus_below_circ)
          hence 12: "y = root p0 y"
            using 1 loop_root_2 path_halving_invariant_def by blast
          have "?pyppy = p[y\<longmapsto>p0[[p0[[y]]]]]"
            using 1 path_halving_invariant_aux(2) by force
          also have "... = p[y\<longmapsto>p0[[y]]]"
            using 1 12 by (metis root_successor_loop path_halving_invariant_def)
          also have "... = p[y\<longmapsto>?py]"
            using 1 path_halving_invariant_aux(1) by force
          also have "... = p"
            using 1 get_put path_halving_invariant_def by blast
          finally show ?thesis
            using 11 by simp
        qed
        have 13: "-?pt2sy = -(p0\<^sup>T\<^sup>\<star> * y) \<squnion> (-?pt2sy \<sqinter> ?pty) \<squnion> (-?pt2sy \<sqinter> y)"
        proof (rule order.antisym)
          have 14: "regular (p0\<^sup>T\<^sup>\<star> * y) \<and> regular ?pt2sy"
            using 1 by (metis order.antisym conv_complement conv_dist_comp conv_involutive conv_star_commute forest_components_increasing mapping_regular pp_dist_star regular_mult_closed top.extremum path_halving_invariant_def)
          have "p0\<^sup>T\<^sup>\<star> = p0\<^sup>T\<^sup>\<star> * p0\<^sup>T * p0\<^sup>T \<squnion> p0\<^sup>T \<squnion> 1"
            using star.circ_back_loop_fixpoint star.circ_plus_same star_left_unfold_equal sup_commute by auto
          hence "p0\<^sup>T\<^sup>\<star> * y \<le> ?pt2sy \<squnion> ?pty \<squnion> y"
            by (metis inf.eq_refl mult_1_left mult_right_dist_sup)
          also have "... = ?pt2sy \<squnion> (-?pt2sy \<sqinter> ?pty) \<squnion> y"
            using 14 by (metis maddux_3_21_pp)
          also have "... = ?pt2sy \<squnion> (-?pt2sy \<sqinter> ?pty) \<squnion> (-?pt2sy \<sqinter> y)"
            using 14 by (smt (z3) maddux_3_21_pp sup.left_commute sup_assoc)
          hence "p0\<^sup>T\<^sup>\<star> * y \<sqinter> -?pt2sy \<le> (-?pt2sy \<sqinter> ?pty) \<squnion> (-?pt2sy \<sqinter> y)"
            using calculation half_shunting sup_assoc sup_commute by auto
          thus "-?pt2sy \<le> -(p0\<^sup>T\<^sup>\<star> * y) \<squnion> (-?pt2sy \<sqinter> ?pty) \<squnion> (-?pt2sy \<sqinter> y)"
            using 14 by (smt (z3) inf.sup_monoid.add_commute shunting_var_p sup.left_commute sup_commute)
          have "-(p0\<^sup>T\<^sup>\<star> * y) \<le> -?pt2sy"
            by (meson mult_left_isotone order.trans p_antitone star.right_plus_below_circ)
          thus "-(p0\<^sup>T\<^sup>\<star> * y) \<squnion> (-?pt2sy \<sqinter> ?pty) \<squnion> (-?pt2sy \<sqinter> y) \<le> -?pt2sy"
            by simp
        qed
        have "regular ?px" "regular ?pty" "regular y"
          using 1 bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_halving_invariant_def by auto
        hence 15: "regular (?px \<sqinter> -?pt2sy \<sqinter> ?pty)" "regular (?px \<sqinter> -?pt2sy \<sqinter> y)"
          by auto
        have "p0[?px - p0\<^sup>T\<^sup>\<star> * (?pyppy[[y]])\<longmapsto>?p2t] = p0[?px - p0\<^sup>T\<^sup>\<star> * (p[[?py]])\<longmapsto>?p2t]"
          using 1 put_get vector_mult_closed path_halving_invariant_def by auto
        also have "... = p0[?px - ?pt2sy\<longmapsto>?p2t]"
          using 1 comp_associative path_halving_invariant_aux(2) by force
        also have "... = p0[?pxy \<squnion> (?px \<sqinter> -?pt2sy \<sqinter> ?pty) \<squnion> (?px \<sqinter> -?pt2sy \<sqinter> y)\<longmapsto>?p2t]"
          using 13 by (metis comp_inf.semiring.distrib_left inf.sup_monoid.add_assoc)
        also have "... = (?p[?px \<sqinter> -?pt2sy \<sqinter> ?pty\<longmapsto>?p2t])[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t]"
          using 15 by (smt (z3) update_same_3 comp_inf.semiring.mult_not_zero inf.sup_monoid.add_assoc inf.sup_monoid.add_commute)
        also have "... = (p[?px \<sqinter> -?pt2sy \<sqinter> ?pty\<longmapsto>?p2t])[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t]"
          using 1 path_halving_invariant_def by auto
        also have "... = p[?px \<sqinter> -?pt2sy \<sqinter> y\<longmapsto>?p2t]"
          using 6 by simp
        also have "... = ?pyppy"
          using 9 by auto
        finally show ?thesis
          .
      qed
      show "univalent p0" "total p0" "acyclic (p0 - 1)"
        using 1 path_halving_invariant_def by auto
    qed
    let ?s = "{ z . regular z \<and> z \<le> p\<^sup>T\<^sup>\<star> * y }"
    let ?t = "{ z . regular z \<and> z \<le> ?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]]) }"
    have "?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]]) = ?pyppy\<^sup>T\<^sup>\<star> * (p[[?py]])"
      using 1 put_get vector_mult_closed path_halving_invariant_def by force
    also have "... \<le> p\<^sup>+\<^sup>T\<^sup>\<star> * (p[[?py]])"
      using 1 path_halving_invariant_def update_square_plus conv_order mult_left_isotone star_isotone by force
    also have "... = p\<^sup>T\<^sup>\<star> * p\<^sup>T * p\<^sup>T * y"
      by (simp add: conv_plus_commute star.left_plus_circ mult_assoc)
    also have "... \<le> p\<^sup>T\<^sup>+ * y"
      by (metis mult_left_isotone star.left_plus_below_circ star_plus)
    finally have 16: "?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]]) \<le> p\<^sup>T\<^sup>+ * y"
      .
    hence "?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]]) \<le> p\<^sup>T\<^sup>\<star> * y"
      using mult_left_isotone order_lesseq_imp star.left_plus_below_circ by blast
    hence 17: "?t \<subseteq> ?s"
      using order_trans by auto
    have 18: "y \<in> ?s"
      using 1 bijective_regular path_compression_1b path_halving_invariant_def by force
    have 19: "\<not> y \<in> ?t"
    proof
      assume "y \<in> ?t"
      hence "y \<le> ?pyppy\<^sup>T\<^sup>\<star> * (?pyppy[[y]])"
        by simp
      hence "y \<le> p\<^sup>T\<^sup>+ * y"
        using 16 dual_order.trans by blast
      hence "y = root p y"
        using 1 find_set_precondition_def loop_root_2 path_halving_invariant_def by blast
      hence "y = ?py"
        using 1 by (metis find_set_precondition_def root_successor_loop path_halving_invariant_def)
      thus False
        using 1 by simp
    qed
    show "card ?t < card ?s"
      apply (rule psubset_card_mono)
      subgoal using finite_regular by simp
      subgoal using 17 18 19 by auto
      done
  qed
qed

lemma path_halving_3:
  "path_halving_invariant p x y p0 \<and> y = p[[y]] \<Longrightarrow> path_halving_postcondition p x y p0"
proof -
  assume 1: "path_halving_invariant p x y p0 \<and> y = p[[y]]"
  show "path_halving_postcondition p x y p0"
  proof (unfold path_halving_postcondition_def path_compression_precondition_def, intro conjI)
    show "univalent p" "total p" "acyclic (p - 1)"
      using 1 find_set_precondition_def path_halving_invariant_def by blast+
    show "vector x" "injective x" "surjective x"
      using 1 find_set_precondition_def path_halving_invariant_def by blast+
    show 2: "vector y" "injective y" "surjective y"
      using 1 path_halving_invariant_def by blast+
    have "find_set_invariant p x y"
      using 1 find_set_invariant_def path_halving_invariant_def by blast
    thus "y = root p x"
      using 1 find_set_3 find_set_postcondition_def by blast
    show "p \<sqinter> 1 = p0 \<sqinter> 1"
      using 1 path_halving_invariant_aux(4) by blast
    show "fc p = fc p0"
      using 1 path_halving_invariant_aux(5) by blast
    have 3: "y = p0[[y]]"
      using 1 path_halving_invariant_aux(1) by auto
    hence "p0\<^sup>T\<^sup>\<star> * y = y"
      using order.antisym path_compression_1b star_left_induct_mult_equal by auto
    hence 4: "p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x - y\<longmapsto>(p0 * p0)\<^sup>T] = p"
      using 1 path_halving_invariant_def by auto
    have "(p0 * p0)\<^sup>T * y = y"
      using 3 mult_assoc conv_dist_comp by auto
    hence "y \<sqinter> p0 * p0 = y \<sqinter> p0"
      using 2 3 by (metis update_postcondition)
    hence 5: "y \<sqinter> p = y \<sqinter> p0 * p0"
      using 1 2 3 by (smt update_postcondition)
    have "p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = (p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x - y\<longmapsto>(p0 * p0)\<^sup>T])[(p0 * p0)\<^sup>T\<^sup>\<star> * x \<sqinter> y\<longmapsto>(p0 * p0)\<^sup>T]"
      using 1 bijective_regular path_halving_invariant_def update_split by blast
    also have "... = p[(p0 * p0)\<^sup>T\<^sup>\<star> * x \<sqinter> y\<longmapsto>(p0 * p0)\<^sup>T]"
      using 4 by simp
    also have "... = p"
      apply (rule update_same_sub)
      using 5 apply simp
      apply simp
      using 1 bijective_regular inf.absorb2 path_halving_invariant_def by auto
    finally show "p0[(p0 * p0)\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p"
      .
  qed
qed

theorem find_path_halving:
  "VARS p y
  [ find_set_precondition p x \<and> p0 = p ]
  y := x;
  WHILE y \<noteq> p[[y]]
    INV { path_halving_invariant p x y p0 }
    VAR { (p\<^sup>T\<^sup>\<star> * y)\<down> }
     DO p[y] := p[[p[[y]]]];
        y := p[[y]]
     OD
  [ path_halving_postcondition p x y p0 ]"
  apply vcg_tc_simp
    apply (fact path_halving_1)
   apply (fact path_halving_2)
  by (fact path_halving_3)

subsection \<open>Path Splitting\<close>

text \<open>
Path splitting is another variant of the path compression technique.
We implement it again independently of find-set, using a second while-loop which iterates over the same path to the root.
We prove that path splitting preserves the equivalence-relational semantics of the disjoint-set forest and also preserves the roots of the component trees.
Additionally we prove the exact effect of path splitting, which is to replace every parent pointer with a pointer to the respective grandparent.
\<close>

definition "path_splitting_invariant p x y p0 \<equiv> 
  find_set_precondition p x \<and> point y \<and> y \<le> p0\<^sup>T\<^sup>\<star> * x \<and>
  p0[p0\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * y\<longmapsto>(p0 * p0)\<^sup>T] = p \<and>
  disjoint_set_forest p0"
definition "path_splitting_postcondition p x y p0 \<equiv> 
  path_compression_precondition p x y \<and> p \<sqinter> 1 = p0 \<sqinter> 1 \<and> fc p = fc p0 \<and>
  p0[p0\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p"

lemma path_splitting_invariant_aux_1:
  assumes "point x"
      and "point y"
      and "disjoint_set_forest p0"
    shows "(p0[p0\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * y\<longmapsto>(p0 * p0)\<^sup>T]) \<sqinter> 1 = p0 \<sqinter> 1"
      and "fc (p0[p0\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * y\<longmapsto>(p0 * p0)\<^sup>T]) = fc p0"
      and "p0\<^sup>T\<^sup>\<star> * x \<le> p0\<^sup>\<star> * root p0 x"
proof -
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?px = "p0\<^sup>T\<^sup>\<star> * x"
  let ?py = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py"
  let ?q1 = "?pxy \<sqinter> p0"
  let ?q2 = "-?pxy \<sqinter> p0"
  let ?q3 = "?pxy \<sqinter> ?p2"
  let ?q4 = "-?pxy \<sqinter> ?p2"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  let ?r0 = "root p0 x"
  let ?rp = "root ?p x"
  have 1: "regular ?px \<and> regular (p0\<^sup>T\<^sup>\<star> * y) \<and> regular ?pxy"
    using assms bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_halving_invariant_def regular_closed_inf by auto
  have 2: "vector x \<and> vector ?px \<and> vector ?py \<and> vector ?pxy"
    using assms(1,2) find_set_precondition_def vector_complement_closed vector_mult_closed path_halving_invariant_def vector_inf_closed by auto
  have 3: "?r0 \<le> p0 * ?r0"
    by (metis assms(3) dedekind_1 inf.le_iff_sup root_successor_loop top_greatest)
  hence "?pxy \<sqinter> p0 * ?r0 \<le> ?pxy \<sqinter> ?p2 * ?r0"
    by (metis comp_associative inf.eq_refl inf.sup_right_isotone mult_isotone)
  hence 4: "?q1 * ?r0 \<le> ?q3 * ?r0"
    using 2 by (simp add: vector_inf_comp)
  have 5: "?q1 * ?q2 \<le> ?q3"
    using 2 by (smt (z3) comp_isotone inf.cobounded1 inf.cobounded2 inf_greatest vector_export_comp)
  have "?q1 * ?q2\<^sup>\<star> * ?r0 = ?q1 * ?r0 \<squnion> ?q1 * ?q2 * ?q2\<^sup>\<star> * ?r0"
    by (metis comp_associative semiring.distrib_left star.circ_loop_fixpoint sup_commute)
  also have "... \<le> ?q1 * ?r0 \<squnion> ?q3 * ?q2\<^sup>\<star> * ?r0"
    using 5 by (meson mult_left_isotone sup_right_isotone)
  also have "... \<le> ?q3 * ?r0 \<squnion> ?q3 * ?q2\<^sup>\<star> * ?r0"
    using 4 sup_left_isotone by blast
  also have "... = ?q3 * ?q2\<^sup>\<star> * ?r0"
    by (smt (verit, del_insts) comp_associative semiring.distrib_left star.circ_loop_fixpoint star.circ_transitive_equal star_involutive sup_commute)
  finally have 6: "?q1 * ?q2\<^sup>\<star> * ?r0 \<le> ?q3 * ?q2\<^sup>\<star> * ?r0"
    .
  have "?q1 * (-?pxy \<sqinter> p0\<^sup>+) * ?pxy \<le> (?px \<sqinter> p0) * (-?pxy \<sqinter> p0\<^sup>+) * ?pxy"
    by (meson comp_inf.comp_left_subdist_inf inf.boundedE mult_left_isotone)
  also have "... \<le> (?px \<sqinter> p0) * (-?pxy \<sqinter> p0\<^sup>+) * ?py"
    by (simp add: mult_right_isotone)
  also have "... \<le> ?px\<^sup>T * (-?pxy \<sqinter> p0\<^sup>+) * ?py"
  proof -
    have "?px \<sqinter> p0 \<le> ?px\<^sup>T * p0"
      using 2 by (simp add: vector_restrict_comp_conv)
    also have "... \<le> ?px\<^sup>T"
      by (metis comp_associative conv_dist_comp conv_involutive conv_star_commute mult_right_isotone star.circ_increasing star.circ_transitive_equal)
    finally show ?thesis
      using mult_left_isotone by auto
  qed
  also have "... = top * (?px \<sqinter> -?pxy \<sqinter> p0\<^sup>+) * ?py"
    using 2 by (smt (z3) comp_inf.star_plus conv_dist_inf covector_inf_comp_3 inf_top.right_neutral vector_complement_closed vector_inf_closed)
  also have "... \<le> top * (-?py \<sqinter> p0\<^sup>+) * ?py"
    by (metis comp_inf.comp_isotone comp_isotone inf.cobounded2 inf.eq_refl inf_import_p)
  also have "... = top * (-?py \<sqinter> p0\<^sup>+ \<sqinter> ?py\<^sup>T) * top"
    using 2 by (simp add: comp_associative covector_inf_comp_3)
  also have "... = bot"
  proof -
    have "p0\<^sup>T\<^sup>\<star> * y - y\<^sup>T * p0\<^sup>\<star> = p0\<^sup>T\<^sup>\<star> * y * y\<^sup>T * -p0\<^sup>\<star>"
      using 2 by (metis assms(2) bijective_conv_mapping comp_mapping_complement vector_covector vector_export_comp vector_mult_closed)
    also have "... \<le> p0\<^sup>T\<^sup>\<star> * -p0\<^sup>\<star>"
      by (meson assms(2) mult_left_isotone order_refl shunt_bijective)
    also have "... \<le> -p0\<^sup>\<star>"
      by (simp add: conv_complement conv_star_commute pp_increasing schroeder_6_p star.circ_transitive_equal)
    also have "... \<le> -p0\<^sup>+"
      by (simp add: p_antitone star.left_plus_below_circ)
    finally have "-?py \<sqinter> p0\<^sup>+ \<sqinter> ?py\<^sup>T = bot"
      by (metis comp_inf.p_pp_comp conv_complement conv_dist_comp conv_involutive conv_star_commute p_shunting_swap pp_isotone pseudo_complement_pp regular_closed_p)
    thus ?thesis
      by simp
  qed
  finally have 7: "?q1 * (-?pxy \<sqinter> p0\<^sup>+) * ?pxy = bot"
    using le_bot by blast
  have "?q2\<^sup>+ \<le> -?pxy"
    using 2 by (smt (z3) comp_isotone complement_conv_sub inf.order_trans inf.sup_right_divisibility inf_commute symmetric_top_closed top_greatest)
  hence "?q2\<^sup>+ \<le> -?pxy \<sqinter> p0\<^sup>+"
    by (simp add: comp_isotone star_isotone)
  hence 8: "?q1 * ?q2\<^sup>+ * ?pxy = bot"
    using 7 mult_left_isotone mult_right_isotone le_bot by auto
  have "?q1 * ?q2\<^sup>+ * ?q3\<^sup>\<star> = ?q1 * ?q2\<^sup>+ \<squnion> ?q1 * ?q2\<^sup>+ * ?q3\<^sup>+"
    by (smt (z3) comp_associative star.circ_back_loop_fixpoint star.circ_plus_same sup_commute)
  also have "... \<le> ?q1 * ?q2\<^sup>+ \<squnion> ?q1 * ?q2\<^sup>+ * ?pxy"
    using 2 by (smt (z3) inf.cobounded1 mult_right_isotone sup_right_isotone vector_inf_comp)
  finally have 9: "?q1 * ?q2\<^sup>+ * ?q3\<^sup>\<star> \<le> ?q1 * ?q2\<^sup>+"
    using 8 by simp
  have 10: "?q1 * ?q4 * ?pxy = bot"
  proof -
    have "?p2 \<le> p0\<^sup>+"
      by (simp add: mult_right_isotone star.circ_increasing)
    thus ?thesis
      using 7 by (metis mult_left_isotone mult_right_isotone le_bot comp_inf.comp_isotone eq_refl)
  qed
  have 11: "?q1 * ?q2 * ?pxy = bot"
  proof -
    have "p0 \<le> p0\<^sup>+"
      by (simp add: star.circ_mult_increasing)
    thus ?thesis
      using 7 by (metis mult_left_isotone mult_right_isotone le_bot comp_inf.comp_isotone eq_refl)
  qed
  have 12: "?q2 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (smt (verit, del_insts) conv_dist_comp conv_order conv_star_commute inf.coboundedI1 inf.orderE inf.sup_monoid.add_commute path_compression_1b)
  have "?q3 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> = ?q1 * p0 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    using 2 vector_inf_comp by auto
  also have "... = ?q1 * (?q3 \<squnion> ?q4) * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    using 1 by (smt (z3) comp_associative comp_inf.mult_right_dist_sup comp_inf.star_slide inf_top.right_neutral regular_complement_top)
  also have "... = ?q1 * ?q3 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    using mult_left_dist_sup mult_right_dist_sup by auto
  also have "... \<le> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (smt (z3) mult_left_isotone mult_left_sub_dist_sup_right sup_left_isotone sup_right_divisibility mult_assoc star.left_plus_below_circ)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q3\<^sup>+ * ?q2\<^sup>\<star>"
    by (smt (z3) semiring.combine_common_factor star.circ_back_loop_fixpoint star_plus sup_monoid.add_commute mult_assoc)
  also have "... \<le> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?pxy * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (smt (verit, ccfv_threshold) comp_isotone inf.sup_right_divisibility inf_commute order.refl semiring.add_left_mono mult_assoc)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q4 * ?q2\<^sup>\<star>"
    using 10 by simp
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * p0 * ?q2\<^sup>\<star>"
    using 2 by (smt vector_complement_closed vector_inf_comp mult_assoc)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * (?q2 \<squnion> ?q1) * ?q2\<^sup>\<star>"
    using 1 by (smt (z3) comp_associative comp_inf.mult_right_dist_sup comp_inf.star_slide inf_top.right_neutral regular_complement_top)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * ?q2 * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * ?q1 * ?q2\<^sup>\<star>"
    using mult_left_dist_sup mult_right_dist_sup sup_commute sup_left_commute by auto
  also have "... \<le> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * ?q2 * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * ?pxy * ?q2\<^sup>\<star>"
    by (smt (verit, ccfv_threshold) comp_isotone inf.sup_right_divisibility inf_commute order.refl semiring.add_left_mono mult_assoc)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2 * ?q2 * ?q2\<^sup>\<star>"
    using 11 by simp
  also have "... \<le> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q1 * ?q2\<^sup>\<star>"
    by (smt comp_associative comp_isotone mult_right_isotone star.circ_increasing star.circ_transitive_equal star.left_plus_below_circ sup_right_isotone)
  also have "... = ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (smt (verit, best) comp_associative semiring.distrib_left star.circ_loop_fixpoint star.circ_transitive_equal star_involutive)
  finally have 13: "?q3 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (meson inf.cobounded2 mult_left_isotone order_lesseq_imp)
  hence "?q3 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> \<squnion> ?q2 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    using 12 by simp
  hence "?q3\<^sup>\<star> * ?q2 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (simp add: star_left_induct mult_assoc)
  hence "?q1 * ?q3\<^sup>\<star> * ?q2 \<le> ?q1 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone)
  hence "?q1 * ?q3\<^sup>\<star> * ?q2 \<le> ?q3\<^sup>+ * ?q2\<^sup>\<star>"
    using 2 by (simp add: vector_inf_comp)
  hence 14: "?q1 * ?q3\<^sup>\<star> * ?q2 \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star>"
    using mult_left_isotone order_lesseq_imp star.left_plus_below_circ by blast
  have "p0 * ?r0 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (metis comp_associative mult_1_right mult_left_isotone mult_right_isotone reflexive_mult_closed star.circ_reflexive)
  hence 15: "?r0 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 3 dual_order.trans by blast
  have "?q3 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 13 mult_left_isotone by blast
  hence "?q3 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?r0 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 15 by simp
  hence "?q3\<^sup>\<star> * ?r0 \<le> p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (simp add: star_left_induct mult_assoc)
  hence "?q1 * ?q3\<^sup>\<star> * ?r0 \<le> ?q1 * p0 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (simp add: comp_associative mult_right_isotone)
  hence "?q1 * ?q3\<^sup>\<star> * ?r0 \<le> ?q3\<^sup>+ * ?q2\<^sup>\<star> * ?r0"
    using 2 by (simp add: vector_inf_comp)
  hence 16: "?q1 * ?q3\<^sup>\<star> * ?r0 \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using mult_left_isotone order_lesseq_imp star.left_plus_below_circ by blast
  have "?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 = ?q1 * ?q3\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>+ * ?r0"
    by (smt (z3) comp_associative mult_right_dist_sup star.circ_back_loop_fixpoint star.circ_plus_same sup_commute)
  also have "... \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>+ * ?r0"
    using 16 sup_left_isotone by blast
  also have "... \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 14 by (smt (z3) inf.eq_refl semiring.distrib_right star.circ_transitive_equal sup.absorb2 sup_monoid.add_commute mult_assoc)
  also have "... = ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (simp add: comp_associative star.circ_transitive_equal)
  finally have 17: "?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    .
  have "?r0 \<le> ?q2\<^sup>\<star> * ?r0"
    using star.circ_loop_fixpoint sup_right_divisibility by auto
  also have "... \<le> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using comp_associative star.circ_loop_fixpoint sup_right_divisibility by force
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using comp_associative star.circ_loop_fixpoint sup_right_divisibility by force
  finally have 18: "?r0 \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    .
  have "p0 * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 = (?q2 \<squnion> ?q1) * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 1 by (smt (z3) comp_inf.mult_right_dist_sup comp_inf.star_plus inf_top.right_neutral regular_complement_top)
  also have "... = ?q2 * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using mult_right_dist_sup by auto
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (smt (z3) comp_left_increasing_sup star.circ_loop_fixpoint sup_left_isotone mult_assoc)
  also have "... = ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q2\<^sup>+ * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (smt (z3) mult_left_dist_sup semiring.combine_common_factor star.circ_loop_fixpoint sup_monoid.add_commute mult_assoc)
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q2\<^sup>+ * ?q2\<^sup>\<star> * ?r0"
    using 9 mult_left_isotone sup_right_isotone by auto
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q2\<^sup>\<star> * ?r0"
    by (smt (z3) comp_associative comp_isotone inf.eq_refl semiring.add_right_mono star.circ_transitive_equal star.left_plus_below_circ sup_commute)
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q1 * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q3 * ?q2\<^sup>\<star> * ?r0"
    using 6 sup_right_isotone by blast
  also have "... = ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q3 * ?q2\<^sup>\<star> * ?r0"
    using 17 by (smt (z3) le_iff_sup semiring.combine_common_factor semiring.distrib_right star.circ_loop_fixpoint sup_monoid.add_commute)
  also have "... \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (meson mult_left_isotone star.circ_increasing sup_right_isotone)
  also have "... = ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (smt (z3) comp_associative star.circ_loop_fixpoint star.circ_transitive_equal star_involutive)
  finally have "p0 * ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0 \<squnion> ?r0 \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    using 18 sup.boundedI by blast
  hence "p0\<^sup>\<star> * ?r0 \<le> ?q2\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (simp add: comp_associative star_left_induct)
  also have "... \<le> ?p\<^sup>\<star> * ?q3\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (metis mult_left_isotone star.circ_sub_dist sup_commute)
  also have "... \<le> ?p\<^sup>\<star> * ?p\<^sup>\<star> * ?q2\<^sup>\<star> * ?r0"
    by (simp add: mult_left_isotone mult_right_isotone star_isotone)
  also have "... \<le> ?p\<^sup>\<star> * ?p\<^sup>\<star> * ?p\<^sup>\<star> * ?r0"
    by (metis mult_isotone order.refl star.circ_sub_dist sup_commute)
  finally have 19: "p0\<^sup>\<star> * ?r0 \<le> ?p\<^sup>\<star> * ?r0"
    by (simp add: star.circ_transitive_equal)
  have 20: "?p\<^sup>\<star> \<le> p0\<^sup>\<star>"
    by (metis star.left_plus_circ star_isotone update_square_ub_plus)
  hence 21: "p0\<^sup>\<star> * ?r0 = ?p\<^sup>\<star> * ?r0"
    using 19 order.antisym mult_left_isotone by auto
  have "?p \<sqinter> 1 = (?q3 \<sqinter> 1) \<squnion> (?q2 \<sqinter> 1)"
    using comp_inf.semiring.distrib_right conv_involutive by auto
  also have "... = (?q1 \<sqinter> 1) \<squnion> (?q2 \<sqinter> 1)"
    using assms(3) acyclic_square path_splitting_invariant_def inf.sup_monoid.add_assoc by auto
  also have "... = (?pxy \<squnion> -?pxy) \<sqinter> p0 \<sqinter> 1"
    using inf_sup_distrib2 by auto
  also have "... = p0 \<sqinter> 1"
    using 1 by (metis inf.sup_monoid.add_commute inf_sup_distrib1 maddux_3_11_pp)
  finally show 22: "?p \<sqinter> 1 = p0 \<sqinter> 1"
    .
  have "?p\<^sup>T\<^sup>\<star> * x \<le> p0\<^sup>T\<^sup>\<star> * x"
    using 20 by (metis conv_isotone conv_star_commute mult_left_isotone)
  hence 23: "?rp \<le> ?r0"
    using 22 comp_inf.mult_left_isotone by auto
  have 24: "disjoint_set_forest ?p"
    using 1 2 assms(3) disjoint_set_forest_update_square by blast
  hence 25: "point ?rp"
    using root_point assms(1) by auto
  have "?r0 * ?rp\<^sup>T = ?r0 * x\<^sup>T * ?p\<^sup>\<star> * (?p \<sqinter> 1)"
    by (smt (z3) comp_associative conv_dist_comp conv_dist_inf conv_involutive conv_star_commute inf.sup_monoid.add_commute one_inf_conv root_var star_one star_sup_one wcc_one)
  also have "... \<le> (p0 \<sqinter> 1) * p0\<^sup>T\<^sup>\<star> * 1 * ?p\<^sup>\<star> * (?p \<sqinter> 1)"
    by (smt (z3) assms(1) comp_associative mult_left_isotone mult_right_isotone root_var)
  also have "... \<le> (p0 \<sqinter> 1) * p0\<^sup>T\<^sup>\<star> * p0\<^sup>\<star> * (p0 \<sqinter> 1)"
    using 20 22 comp_isotone by force
  also have "... = (p0 \<sqinter> 1) * p0\<^sup>\<star> * (p0 \<sqinter> 1) \<squnion> (p0 \<sqinter> 1) * p0\<^sup>T\<^sup>\<star> * (p0 \<sqinter> 1)"
    by (simp add: assms(3) cancel_separate_eq sup_monoid.add_commute mult_assoc mult_left_dist_sup semiring.distrib_right)
  also have "... = (p0 \<sqinter> 1) * (p0 \<sqinter> 1) \<squnion> (p0 \<sqinter> 1) * p0\<^sup>T\<^sup>\<star> * (p0 \<sqinter> 1)"
    using univalent_root_successors assms(3) by simp
  also have "... = (p0 \<sqinter> 1) * (p0 \<sqinter> 1) \<squnion> (p0 \<sqinter> 1) * ((p0 \<sqinter> 1) * p0\<^sup>\<star>)\<^sup>T"
    by (smt (z3) comp_associative conv_dist_comp conv_dist_inf conv_star_commute inf.sup_monoid.add_commute one_inf_conv star_one star_sup_one wcc_one)
  also have "... = (p0 \<sqinter> 1) * (p0 \<sqinter> 1)"
    by (metis univalent_root_successors assms(3) conv_dist_inf inf.sup_monoid.add_commute one_inf_conv sup_idem symmetric_one_closed)
  also have "... \<le> 1"
    by (simp add: coreflexive_mult_closed)
  finally have "?r0 * ?rp\<^sup>T \<le> 1"
    .
  hence "?r0 \<le> 1 * ?rp"
    using 25 shunt_bijective by blast
  hence 26: "?r0 = ?rp"
    using 23 order.antisym by simp
  have "?px * ?r0\<^sup>T = ?px * x\<^sup>T * p0\<^sup>\<star> * (p0 \<sqinter> 1)"
    by (smt (z3) comp_associative conv_dist_comp conv_dist_inf conv_involutive conv_star_commute inf.sup_monoid.add_commute one_inf_conv root_var star_one star_sup_one wcc_one)
  also have "... \<le> p0\<^sup>T\<^sup>\<star> * 1 * p0\<^sup>\<star> * (p0 \<sqinter> 1)"
    by (smt (z3) assms(1) comp_associative mult_left_isotone mult_right_isotone root_var)
  also have "... = p0\<^sup>\<star> * (p0 \<sqinter> 1) \<squnion> p0\<^sup>T\<^sup>\<star> * (p0 \<sqinter> 1)"
    by (simp add: assms(3) cancel_separate_eq sup_monoid.add_commute mult_right_dist_sup)
  also have "... = p0\<^sup>\<star> * (p0 \<sqinter> 1) \<squnion> ((p0 \<sqinter> 1) * p0\<^sup>\<star>)\<^sup>T"
    by (smt (z3) conv_dist_comp conv_dist_inf conv_star_commute inf.sup_monoid.add_commute one_inf_conv star_one star_sup_one wcc_one)
  also have "... = p0\<^sup>\<star> * (p0 \<sqinter> 1) \<squnion> (p0 \<sqinter> 1)"
    by (metis univalent_root_successors assms(3) conv_dist_inf inf.sup_monoid.add_commute one_inf_conv symmetric_one_closed)
  also have "... = p0\<^sup>\<star> * (p0 \<sqinter> 1)"
    by (metis conv_involutive path_compression_1b sup.absorb2 sup_commute)
  also have "... \<le> p0\<^sup>\<star>"
    by (simp add: inf.coboundedI1 star.circ_increasing star.circ_mult_upper_bound)
  finally have 27: "?px * ?r0\<^sup>T \<le> p0\<^sup>\<star>"
    .
  thus 28: "?px \<le> p0\<^sup>\<star> * ?r0"
    by (simp add: assms(1,3) root_point shunt_bijective)
  have 29: "point ?r0"
    using root_point assms(1,3) by auto
  hence 30: "mapping (?r0\<^sup>T)"
    using bijective_conv_mapping by blast
  have "?r0 * (?px \<sqinter> p0) = ?r0 * top * (?px \<sqinter> p0)"
    using 29 by force
  also have "... = ?r0 * ?px\<^sup>T * p0"
    using 29 by (metis assms(1) covector_inf_comp_3 vector_covector vector_mult_closed)
  also have "... = ?r0 * x\<^sup>T * p0\<^sup>\<star> * p0"
    using comp_associative conv_dist_comp conv_star_commute by auto
  also have "... \<le> ?r0 * x\<^sup>T * p0\<^sup>\<star>"
    by (simp add: comp_associative mult_right_isotone star.circ_plus_same star.left_plus_below_circ)
  also have "... = ?r0 * ?px\<^sup>T"
    by (simp add: comp_associative conv_dist_comp conv_star_commute)
  also have "... = (?px * ?r0\<^sup>T)\<^sup>T"
    by (simp add: conv_dist_comp)
  also have "... \<le> p0\<^sup>T\<^sup>\<star>"
    using 27 conv_isotone conv_star_commute by fastforce
  finally have "?r0 * (?px \<sqinter> p0) \<le> p0\<^sup>T\<^sup>\<star>"
    .
  hence "?px \<sqinter> p0 \<le> ?r0\<^sup>T * p0\<^sup>T\<^sup>\<star>"
    using 30 shunt_mapping by auto
  hence "?px \<sqinter> p0 \<le> p0\<^sup>\<star> * ?r0 \<sqinter> ?r0\<^sup>T * p0\<^sup>T\<^sup>\<star>"
    using 28 inf.coboundedI2 inf.sup_monoid.add_commute by fastforce
  also have "... = p0\<^sup>\<star> * ?r0 * ?r0\<^sup>T * p0\<^sup>T\<^sup>\<star>"
    using 29 by (smt (z3) vector_covector vector_inf_comp vector_mult_closed)
  also have "... = ?p\<^sup>\<star> * ?r0 * ?r0\<^sup>T * ?p\<^sup>T\<^sup>\<star>"
    using 21 by (smt comp_associative conv_dist_comp conv_star_commute)
  also have "... = ?p\<^sup>\<star> * ?rp * ?rp\<^sup>T * ?p\<^sup>T\<^sup>\<star>"
    using 26 by auto
  also have "... \<le> ?p\<^sup>\<star> * 1 * ?p\<^sup>T\<^sup>\<star>"
    using 25 by (smt (z3) comp_associative mult_left_isotone mult_right_isotone)
  finally have 31: "?px \<sqinter> p0 \<le> fc ?p"
    by auto
  have "-?px \<sqinter> p0 \<le> ?p"
    by (simp add: inf.sup_monoid.add_commute le_supI1 sup_commute)
  also have "... \<le> fc ?p"
    using fc_increasing by auto
  finally have "p0 \<le> fc ?p"
    using 1 31 by (smt (z3) inf.sup_monoid.add_commute maddux_3_11_pp semiring.add_left_mono sup.orderE sup_commute)
  also have "... \<le> wcc ?p"
    using star.circ_sub_dist_3 by auto
  finally have 32: "wcc p0 \<le> wcc ?p"
    using wcc_below_wcc by blast
  have "?p \<le> wcc p0"
    by (simp add: inf.coboundedI1 inf.sup_monoid.add_commute star.circ_mult_upper_bound star.circ_sub_dist_1)
  hence "wcc ?p \<le> wcc p0"
    using wcc_below_wcc by blast
  hence "wcc ?p = wcc p0"
    using 32 order.antisym by blast
  thus "fc ?p = fc p0"
    using 24 assms(3) fc_wcc by auto
qed

lemma path_splitting_invariant_aux:
  assumes "path_splitting_invariant p x y p0"
  shows "p[[y]] = p0[[y]]"
    and "p[[p[[y]]]] = p0[[p0[[y]]]]"
    and "p[[p[[p[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    and "p \<sqinter> 1 = p0 \<sqinter> 1"
    and "fc p = fc p0"
proof -
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?px = "p0\<^sup>T\<^sup>\<star> * x"
  let ?py = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  have "?p[[y]] = p0[[y]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_splitting_invariant_def apply force
    by (meson inf.cobounded2 order_lesseq_imp p_antitone_iff path_compression_1b)
  thus 1: "p[[y]] = p0[[y]]"
    using assms path_splitting_invariant_def by auto
  have "?p[[p0[[y]]]] = p0[[p0[[y]]]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_splitting_invariant_def apply force
    by (metis comp_isotone inf.boundedE inf.coboundedI2 inf.eq_refl p_antitone_iff selection_closed_id star.circ_increasing)
  thus 2: "p[[p[[y]]]] = p0[[p0[[y]]]]"
    using 1 assms path_splitting_invariant_def by auto
  have "?p[[p0[[p0[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    apply (rule put_get_different_vector)
    using assms find_set_precondition_def vector_complement_closed vector_inf_closed vector_mult_closed path_splitting_invariant_def apply force
    by (metis comp_associative comp_isotone conv_dist_comp conv_involutive conv_order inf.coboundedI2 inf.le_iff_sup mult_left_isotone p_antitone_iff p_antitone_inf star.circ_increasing star.circ_transitive_equal)
  thus "p[[p[[p[[y]]]]]] = p0[[p0[[p0[[y]]]]]]"
    using 2 assms path_splitting_invariant_def by auto
  show "p \<sqinter> 1 = p0 \<sqinter> 1"
    using assms path_splitting_invariant_aux_1(1) path_splitting_invariant_def find_set_precondition_def by auto
  show "fc p = fc p0"
    using assms path_splitting_invariant_aux_1(2) path_splitting_invariant_def find_set_precondition_def by auto
qed

lemma path_splitting_1:
  "find_set_precondition p0 x \<Longrightarrow> path_splitting_invariant p0 x x p0"
proof -
  assume 1: "find_set_precondition p0 x"
  show "path_splitting_invariant p0 x x p0"
  proof (unfold path_splitting_invariant_def, intro conjI)
    show "find_set_precondition p0 x"
      using 1 by simp
    show "vector x" "injective x" "surjective x"
      using 1 find_set_precondition_def by auto
    show "x \<le> p0\<^sup>T\<^sup>\<star> * x"
      by (simp add: path_compression_1b)
    have "(p0 * p0)\<^sup>T\<^sup>\<star> * x \<le> p0\<^sup>T\<^sup>\<star> * x"
      by (simp add: conv_dist_comp mult_left_isotone star.circ_square)
    thus "p0[p0\<^sup>T\<^sup>\<star> * x - p0\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p0"
      by (smt (z3) inf.le_iff_sup inf_commute maddux_3_11_pp p_antitone_inf pseudo_complement)
    show "univalent p0" "total p0" "acyclic (p0 - 1)"
      using 1 find_set_precondition_def by auto
  qed
qed

lemma path_splitting_2:
  "path_splitting_invariant p x y p0 \<and> y \<noteq> p[[y]] \<Longrightarrow> path_splitting_invariant (p[y\<longmapsto>p[[p[[y]]]]]) x (p[[y]]) p0 \<and> ((p[y\<longmapsto>p[[p[[y]]]]])\<^sup>T\<^sup>\<star> * (p[[y]]))\<down> < (p\<^sup>T\<^sup>\<star> * y)\<down>"
proof -
  let ?py = "p[[y]]"
  let ?ppy = "p[[?py]]"
  let ?pyppy = "p[y\<longmapsto>?ppy]"
  let ?p2 = "p0 * p0"
  let ?p2t = "?p2\<^sup>T"
  let ?p2ts = "?p2t\<^sup>\<star>"
  let ?px = "p0\<^sup>T\<^sup>\<star> * x"
  let ?py2 = "-(p0\<^sup>T\<^sup>\<star> * y)"
  let ?pxy = "?px \<sqinter> ?py2"
  let ?p = "p0[?pxy\<longmapsto>?p2t]"
  let ?pty = "p0\<^sup>T * y"
  let ?pt2y = "p0\<^sup>T * p0\<^sup>T * y"
  let ?pt2sy = "p0\<^sup>T\<^sup>\<star> * p0\<^sup>T * p0\<^sup>T * y"
  let ?ptpy = "p0\<^sup>T\<^sup>+ * y"
  assume 1: "path_splitting_invariant p x y p0 \<and> y \<noteq> ?py"
  have 2: "point ?pty \<and> point ?pt2y"
    using 1 by (smt (verit) comp_associative read_injective read_surjective path_splitting_invariant_def)
  show "path_splitting_invariant ?pyppy x (p[[y]]) p0 \<and> (?pyppy\<^sup>T\<^sup>\<star> * (p[[y]]))\<down> < (p\<^sup>T\<^sup>\<star> * y)\<down>"
  proof
    show "path_splitting_invariant ?pyppy x (p[[y]]) p0"
    proof (unfold path_splitting_invariant_def, intro conjI)
      show 3: "find_set_precondition ?pyppy x"
      proof (unfold find_set_precondition_def, intro conjI)
        show "univalent ?pyppy"
          using 1 find_set_precondition_def read_injective update_univalent path_splitting_invariant_def by auto
        show "total ?pyppy"
          using 1 bijective_regular find_set_precondition_def read_surjective update_total path_splitting_invariant_def by force
        show "acyclic (?pyppy - 1)"
          apply (rule update_acyclic_3)
          using 1 find_set_precondition_def path_splitting_invariant_def apply blast
          using 1 2 comp_associative path_splitting_invariant_aux(2) apply force
          using 1 path_splitting_invariant_def apply blast
          by (metis inf.order_lesseq_imp mult_isotone star.circ_increasing star.circ_square mult_assoc)
        show "vector x" "injective x" "surjective x"
          using 1 find_set_precondition_def path_splitting_invariant_def by auto
      qed
      show "vector (p[[y]])"
        using 1 comp_associative path_splitting_invariant_def by auto
      show "injective (p[[y]])"
        using 1 3 read_injective path_splitting_invariant_def find_set_precondition_def by auto
      show "surjective (p[[y]])"
        using 1 3 read_surjective path_splitting_invariant_def find_set_precondition_def by auto
      show "p[[y]] \<le> ?px"
      proof -
        have "p[[y]] = p0[[y]]"
          using 1 path_splitting_invariant_aux(1) by blast
        also have "... \<le> p0\<^sup>T * ?px"
          using 1 path_splitting_invariant_def mult_right_isotone by force
        also have "... \<le> ?px"
          by (metis comp_associative mult_left_isotone star.left_plus_below_circ)
        finally show ?thesis
          .
      qed
      show "p0[?px - p0\<^sup>T\<^sup>\<star> * (p[[y]])\<longmapsto>?p2t] = ?pyppy"
      proof -
        have 4: "p[?px \<sqinter> -?ptpy \<sqinter> y\<longmapsto>?p2t] = ?pyppy"
        proof (cases "y \<le> -?ptpy")
          case True
          hence "p[?px \<sqinter> -?ptpy \<sqinter> y\<longmapsto>?p2t] = p[y\<longmapsto>?p2t]"
            using 1 inf.absorb2 path_splitting_invariant_def by auto
          also have "... = ?pyppy"
            using 1 by (metis comp_associative conv_dist_comp path_splitting_invariant_aux(2) path_splitting_invariant_def update_point_get)
          finally show ?thesis
            .
        next
          case False
          have "vector (-?ptpy)"
            using 1 vector_complement_closed vector_mult_closed path_splitting_invariant_def by blast
          hence 5: "y \<le> ?ptpy"
            using 1 by (smt (verit, del_insts) False bijective_regular point_in_vector_or_complement regular_closed_star regular_mult_closed total_conv_surjective univalent_conv_injective path_splitting_invariant_def)
          hence "?px \<sqinter> -?ptpy \<sqinter> y = bot"
            by (simp add: inf.coboundedI2 p_antitone pseudo_complement)
          hence 6: "p[?px \<sqinter> -?ptpy \<sqinter> y\<longmapsto>?p2t] = p"
            by simp
          have 7: "y = root p0 y"
            using 1 5 loop_root_2 path_splitting_invariant_def by blast
          have "?pyppy = p[y\<longmapsto>p0[[p0[[y]]]]]"
            using 1 path_splitting_invariant_aux(2) by force
          also have "... = p[y\<longmapsto>p0[[y]]]"
            using 1 7 by (metis root_successor_loop path_splitting_invariant_def)
          also have "... = p[y\<longmapsto>?py]"
            using 1 path_splitting_invariant_aux(1) by force
          also have "... = p"
            using 1 get_put path_splitting_invariant_def by blast
          finally show ?thesis
            using 6 by simp
        qed
        have 8: "-?ptpy = ?py2 \<squnion> (-?ptpy \<sqinter> y)"
        proof (rule order.antisym)
          have 9: "regular (p0\<^sup>T\<^sup>\<star> * y) \<and> regular ?ptpy"
            using 1 bijective_regular mapping_conv_bijective pp_dist_star regular_mult_closed path_splitting_invariant_def by auto
          have "p0\<^sup>T\<^sup>\<star> * y \<le> ?ptpy \<squnion> y"
            by (simp add: star.circ_loop_fixpoint mult_assoc)
          also have "... = ?ptpy \<squnion> (-?ptpy \<sqinter> y)"
            using 9 by (metis maddux_3_21_pp)
          hence "p0\<^sup>T\<^sup>\<star> * y \<sqinter> -?ptpy \<le> -?ptpy \<sqinter> y"
            using calculation half_shunting sup_commute by auto
          thus "-?ptpy \<le> ?py2 \<squnion> (-?ptpy \<sqinter> y)"
            using 9 by (smt (z3) inf.sup_monoid.add_commute shunting_var_p sup.left_commute sup_commute)
          have "-(p0\<^sup>T\<^sup>\<star> * y) \<le> -?ptpy"
            by (simp add: comp_isotone p_antitone star.left_plus_below_circ)
          thus "-(p0\<^sup>T\<^sup>\<star> * y) \<squnion> (-?ptpy \<sqinter> y) \<le> -?ptpy"
            by simp
        qed
        have "regular ?px" "regular y"
          using 1 bijective_regular find_set_precondition_def mapping_regular pp_dist_comp regular_closed_star regular_conv_closed path_splitting_invariant_def by auto
        hence 10: "regular (?px \<sqinter> -?ptpy \<sqinter> y)"
          by auto
        have "p0[?px \<sqinter> -(p0\<^sup>T\<^sup>\<star> * (p[[y]]))\<longmapsto>?p2t] = p0[?px \<sqinter> -?ptpy\<longmapsto>?p2t]"
          using 1 by (smt comp_associative path_splitting_invariant_aux(1) star_plus)
        also have "... = p0[?pxy \<squnion> (?px \<sqinter> -?ptpy \<sqinter> y)\<longmapsto>?p2t]"
          using 8 by (metis comp_inf.semiring.distrib_left inf.sup_monoid.add_assoc)
        also have "... = ?p[?px \<sqinter> -?ptpy \<sqinter> y\<longmapsto>?p2t]"
          using 10 by (smt (z3) update_same comp_inf.semiring.mult_not_zero inf.sup_monoid.add_assoc inf.sup_monoid.add_commute)
        also have "... = p[?px \<sqinter> -?ptpy \<sqinter> y\<longmapsto>?p2t]"
          using 1 path_splitting_invariant_def by auto
        also have "... = ?pyppy"
          using 4 by auto
        finally show ?thesis
          .
      qed
      show "univalent p0" "total p0" "acyclic (p0 - 1)"
        using 1 path_splitting_invariant_def by auto
    qed
    let ?s = "{ z . regular z \<and> z \<le> p\<^sup>T\<^sup>\<star> * y }"
    let ?t = "{ z . regular z \<and> z \<le> ?pyppy\<^sup>T\<^sup>\<star> * (p[[y]]) }"
    have "?pyppy\<^sup>T\<^sup>\<star> * (p[[y]]) \<le> p\<^sup>+\<^sup>T\<^sup>\<star> * (p[[y]])"
      using 1 path_splitting_invariant_def update_square_plus conv_order mult_left_isotone star_isotone by force
    also have "... = p\<^sup>T\<^sup>\<star> * p\<^sup>T * y"
      by (simp add: conv_plus_commute star.left_plus_circ mult_assoc)
    also have "... = p\<^sup>T\<^sup>+ * y"
      by (simp add: star_plus)
    finally have 11: "?pyppy\<^sup>T\<^sup>\<star> * (p[[y]]) \<le> p\<^sup>T\<^sup>+ * y"
      .
    hence "?pyppy\<^sup>T\<^sup>\<star> * (p[[y]]) \<le> p\<^sup>T\<^sup>\<star> * y"
      using mult_left_isotone order_lesseq_imp star.left_plus_below_circ by blast
    hence 12: "?t \<subseteq> ?s"
      using order_trans by auto
    have 13: "y \<in> ?s"
      using 1 bijective_regular path_compression_1b path_splitting_invariant_def by force
    have 14: "\<not> y \<in> ?t"
    proof
      assume "y \<in> ?t"
      hence "y \<le> ?pyppy\<^sup>T\<^sup>\<star> * (p[[y]])"
        by simp
      hence "y \<le> p\<^sup>T\<^sup>+ * y"
        using 11 dual_order.trans by blast
      hence "y = root p y"
        using 1 find_set_precondition_def loop_root_2 path_splitting_invariant_def by blast
      hence "y = ?py"
        using 1 by (metis find_set_precondition_def root_successor_loop path_splitting_invariant_def)
      thus False
        using 1 by simp
    qed
    show "card ?t < card ?s"
      apply (rule psubset_card_mono)
      subgoal using finite_regular by simp
      subgoal using 12 13 14 by auto
      done
  qed
qed

lemma path_splitting_3:
  "path_splitting_invariant p x y p0 \<and> y = p[[y]] \<Longrightarrow> path_splitting_postcondition p x y p0"
proof -
  assume 1: "path_splitting_invariant p x y p0 \<and> y = p[[y]]"
  show "path_splitting_postcondition p x y p0"
  proof (unfold path_splitting_postcondition_def path_compression_precondition_def, intro conjI)
    show "univalent p" "total p" "acyclic (p - 1)"
      using 1 find_set_precondition_def path_splitting_invariant_def by blast+
    show "vector x" "injective x" "surjective x"
      using 1 find_set_precondition_def path_splitting_invariant_def by blast+
    show 2: "vector y" "injective y" "surjective y"
      using 1 path_splitting_invariant_def by blast+
    show 3: "p \<sqinter> 1 = p0 \<sqinter> 1"
      using 1 path_splitting_invariant_aux(4) by blast
    show 4: "fc p = fc p0"
      using 1 path_splitting_invariant_aux(5) by blast
    have "y \<le> p0\<^sup>T\<^sup>\<star> * x"
      using 1 path_splitting_invariant_def by simp
    hence 5: "y * x\<^sup>T \<le> fc p0"
      using 1 by (metis dual_order.trans fc_wcc find_set_precondition_def shunt_bijective star.circ_decompose_11 star_decompose_1 star_outer_increasing path_splitting_invariant_def)
    have 6: "y = p0[[y]]"
      using 1 path_splitting_invariant_aux(1) by auto
    hence "y = root p0 y"
      using 2 loop_root by auto
    also have "... = root p0 x"
      using 1 2 5 find_set_precondition_def path_splitting_invariant_def same_component_same_root by auto
    also have "... = root p x"
      using 1 3 4 by (metis find_set_precondition_def path_splitting_invariant_def same_root)
    finally show "y = root p x"
      .
    have "p0\<^sup>T\<^sup>\<star> * y = y"
      using 6 order.antisym path_compression_1b star_left_induct_mult_equal by auto
    hence 7: "p0[p0\<^sup>T\<^sup>\<star> * x - y\<longmapsto>(p0 * p0)\<^sup>T] = p"
      using 1 path_splitting_invariant_def by auto
    have "(p0 * p0)\<^sup>T * y = y"
      using 6 mult_assoc conv_dist_comp by auto
    hence "y \<sqinter> p0 * p0 = y \<sqinter> p0"
      using 2 6 by (metis update_postcondition)
    hence 8: "y \<sqinter> p = y \<sqinter> p0 * p0"
      using 1 2 6 by (smt update_postcondition)
    have "p0[p0\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = (p0[p0\<^sup>T\<^sup>\<star> * x - y\<longmapsto>(p0 * p0)\<^sup>T])[p0\<^sup>T\<^sup>\<star> * x \<sqinter> y\<longmapsto>(p0 * p0)\<^sup>T]"
      using 1 bijective_regular path_splitting_invariant_def update_split by blast
    also have "... = p[p0\<^sup>T\<^sup>\<star> * x \<sqinter> y\<longmapsto>(p0 * p0)\<^sup>T]"
      using 7 by simp
    also have "... = p"
      apply (rule update_same_sub)
      using 8 apply simp
      apply simp
      using 1 bijective_regular inf.absorb2 path_splitting_invariant_def by auto
    finally show "p0[p0\<^sup>T\<^sup>\<star> * x\<longmapsto>(p0 * p0)\<^sup>T] = p"
      .
  qed
qed

theorem find_path_splitting:
  "VARS p t y
  [ find_set_precondition p x \<and> p0 = p ]
  y := x;
  WHILE y \<noteq> p[[y]]
    INV { path_splitting_invariant p x y p0 }
    VAR { (p\<^sup>T\<^sup>\<star> * y)\<down> }
     DO t := p[[y]];
        p[y] := p[[p[[y]]]];
        y := t
     OD
  [ path_splitting_postcondition p x y p0 ]"
  apply vcg_tc_simp
    apply (fact path_splitting_1)
   apply (fact path_splitting_2)
  by (fact path_splitting_3)

end

section \<open>Verifying Union by Rank\<close>

text \<open>
In this section we verify the union-by-rank operation of disjoint-set forests.
The rank of a node is an upper bound of the height of the subtree rooted at that node.
The rank array of a disjoint-set forest maps each node to its rank.
This can be represented as a homogeneous relation since the possible rank values are $0, \dots, n-1$ where $n$ is the number of nodes of the disjoint-set forest.
\<close>

subsection \<open>Peano structures\<close>

text \<open>
Since ranks are natural numbers we start by introducing basic Peano arithmetic.
Numbers are represented as (relational) points.
Constant \<open>Z\<close> represents the number $0$.
Constant \<open>S\<close> represents the successor function.
The successor of a number $x$ is obtained by the relational composition \<open>S\<^sup>T * x\<close>.
The composition \<open>S * x\<close> results in the predecessor of $x$.
\<close>

class peano_signature =
  fixes Z :: "'a"
  fixes S :: "'a"

text \<open>
The numbers will be used in arrays, which are represented by homogeneous finite relations.
Such relations can only represent finitely many numbers.
This means that we weaken the Peano axioms, which are usually used to obtain (infinitely many) natural numbers.
Axiom \<open>Z_point\<close> specifies that $0$ is a number.
Axiom \<open>S_univalent\<close> specifies that every number has at most one `successor'.
Together with axiom \<open>S_total\<close>, which is added later, this means that every number has exactly one `successor'.
Axiom \<open>S_injective\<close> specifies that numbers with the same successor are equal.
Axiom \<open>S_star_Z_top\<close> specifies that every number can be obtained from $0$ by finitely many applications of the successor.
We omit the Peano axiom \<open>S * Z = bot\<close> which would specify that $0$ is not the successor of any number.
Since only finitely many numbers will be represented, the remaining axioms will model successor modulo $m$ for some $m$ depending on the carrier of the algebra.
That is, the algebra will be able to represent numbers $0, \dots, m-1$ where the successor of $m-1$ is $0$.
\<close>

class skra_peano_1 = stone_kleene_relation_algebra_tarski_consistent + peano_signature +
  assumes Z_point: "point Z"
  assumes S_univalent: "univalent S"
  assumes S_injective: "injective S"
  assumes S_star_Z_top: "S\<^sup>T\<^sup>\<star> * Z = top"
begin

lemma conv_Z_Z:
  "Z\<^sup>T * Z = top"
  by (simp add: Z_point point_conv_comp)

text \<open>Theorem 9.2\<close>

lemma Z_below_S_star:
  "Z \<le> S\<^sup>\<star>"
proof -
  have "top * Z\<^sup>T \<le> S\<^sup>T\<^sup>\<star>"
    using S_star_Z_top Z_point shunt_bijective by blast
  thus ?thesis
    using Z_point conv_order conv_star_commute vector_conv_covector by force
qed

text \<open>Theorem 9.3\<close>

lemma S_connected:
  "S\<^sup>T\<^sup>\<star> * S\<^sup>\<star> = top"
  by (metis Z_below_S_star S_star_Z_top mult_left_dist_sup sup.orderE sup_commute top.extremum)

text \<open>Theorem 9.4\<close>

lemma S_star_connex:
  "S\<^sup>\<star> \<squnion> S\<^sup>T\<^sup>\<star> = top"
  using S_connected S_univalent cancel_separate_eq sup_commute by auto

text \<open>Theorem 9.5\<close>

lemma Z_sup_conv_S_top:
  "Z \<squnion> S\<^sup>T * top = top"
  using S_star_Z_top star.circ_loop_fixpoint sup_commute by auto

lemma top_S_sup_conv_Z:
  "top * S \<squnion> Z\<^sup>T = top"
  by (metis S_star_Z_top conv_dist_comp conv_involutive conv_star_commute star.circ_back_loop_fixpoint symmetric_top_closed)

text \<open>Theorem 9.1\<close>

lemma S_inf_1_below_Z:
  "S \<sqinter> 1 \<le> Z"
proof -
  have "(S \<sqinter> 1) * S\<^sup>T \<le> S \<sqinter> 1"
    by (metis S_injective conv_dist_comp coreflexive_symmetric inf.boundedI inf.cobounded1 inf.cobounded2 injective_codomain)
  hence "(S \<sqinter> 1) * S\<^sup>T\<^sup>\<star> \<le> S \<sqinter> 1"
    using star_right_induct_mult by blast
  hence "(S \<sqinter> 1) * S\<^sup>T\<^sup>\<star> * Z \<le> (S \<sqinter> 1) * Z"
    by (simp add: mult_left_isotone)
  also have "... \<le> Z"
    by (metis comp_left_subdist_inf inf.boundedE mult_1_left)
  finally show ?thesis
    using S_star_Z_top inf.order_trans top_right_mult_increasing mult_assoc by auto
qed

lemma S_inf_1_below_conv_Z:
  "S \<sqinter> 1 \<le> Z\<^sup>T"
  using S_inf_1_below_Z conv_order coreflexive_symmetric by fastforce

text \<open>
The successor operation provides a convenient way to compare two natural numbers.
Namely, $k < m$ if $m$ can be reached from $k$ by finitely many applications of the successor, formally \<open>m \<le> S\<^sup>T\<^sup>\<star> * k\<close> or \<open>k \<le> S\<^sup>\<star> * m\<close>.
This does not work for numbers modulo $m$ since comparison depends on the chosen representative.
We therefore work with a modified successor relation \<open>S'\<close>, which is a partial function that computes the successor for all numbers except $m-1$.
If $S$ is surjective, the point \<open>M\<close> representing the greatest number $m-1$ is the predecessor of $0$ under \<open>S\<close>.
If $S$ is not surjective (like for the set of all natural numbers), \<open>M = bot\<close>.
\<close>

abbreviation "S' \<equiv> S - Z\<^sup>T"
abbreviation "M \<equiv> S * Z"

text \<open>Theorem 11.1\<close>

lemma M_point_iff_S_surjective:
  "point M \<longleftrightarrow> surjective S"
proof
  assume 1: "point M"
  hence "1 \<le> Z\<^sup>T * S\<^sup>T * S * Z"
    using comp_associative conv_dist_comp surjective_var by auto
  hence "Z \<le> S\<^sup>T * S * Z"
    using 1 Z_point bijective_reverse mult_assoc by auto
  also have "... \<le> S\<^sup>T * top"
    by (simp add: comp_isotone mult_assoc)
  finally have "S\<^sup>T * S\<^sup>T * top \<squnion> Z \<le> S\<^sup>T * top"
    using mult_isotone mult_assoc by force
  hence "S\<^sup>T\<^sup>\<star> * Z \<le> S\<^sup>T * top"
    by (simp add: star_left_induct mult_assoc)
  thus "surjective S"
    by (simp add: S_star_Z_top order.antisym surjective_conv_total)
next
  assume "surjective S"
  thus "point M"
    by (metis S_injective Z_point comp_associative injective_mult_closed)
qed

text \<open>Theorem 10.1\<close>

lemma S'_univalent:
  "univalent S'"
  by (simp add: S_univalent univalent_inf_closed)

text \<open>Theorem 10.2\<close>

lemma S'_injective:
  "injective S'"
  by (simp add: S_injective injective_inf_closed)

text \<open>Theorem 10.9\<close>

lemma S'_Z:
  "S' * Z = bot"
  by (simp add: Z_point covector_vector_comp injective_comp_right_dist_inf)

text \<open>Theorem 10.4\<close>

lemma S'_irreflexive:
  "irreflexive S'"
  using S_inf_1_below_conv_Z order_lesseq_imp p_shunting_swap pp_increasing by blast

end

class skra_peano_2 = skra_peano_1 +
  assumes S_total: "total S"
begin

lemma S_mapping:
  "mapping S"
  by (simp add: S_total S_univalent)

text \<open>Theorem 11.2\<close>

lemma M_bot_iff_S_not_surjective:
  "M \<noteq> bot \<longleftrightarrow> surjective S"
proof
  assume "M \<noteq> bot"
  hence "top * S * Z = top"
    by (metis S_mapping Z_point bijective_regular comp_associative mapping_regular regular_mult_closed tarski)
  hence "Z\<^sup>T \<le> top * S"
    using M_point_iff_S_surjective S_injective Z_point comp_associative injective_mult_closed by auto
  thus "surjective S"
    using sup.orderE top_S_sup_conv_Z by fastforce
next
  assume "surjective S"
  thus "M \<noteq> bot"
    using M_point_iff_S_surjective consistent covector_bot_closed by force
qed

text \<open>Theorem 11.3\<close>

lemma M_point_or_bot:
  "point M \<or> M = bot"
  using M_bot_iff_S_not_surjective M_point_iff_S_surjective by blast

text \<open>Alternative way to express \<open>S'\<close>\<close>

text \<open>Theorem 12.1\<close>

lemma S'_var:
  "S' = S - M"
proof -
  have "S' = S * (1 - Z\<^sup>T)"
    by (simp add: Z_point covector_comp_inf vector_conv_compl)
  also have "... = S * (1 - Z)"
    by (metis conv_complement one_inf_conv)
  also have "... = S * 1 \<sqinter> S * -Z"
    by (simp add: S_mapping univalent_comp_left_dist_inf)
  also have "... = S - M"
    by (simp add: comp_mapping_complement S_mapping)
  finally show ?thesis
    .
qed

text \<open>Special case of just $1$ number\<close>

text \<open>Theorem 12.2\<close>

lemma M_is_Z_iff_1_is_top:
  "M = Z \<longleftrightarrow> 1 = top"
proof
  assume "M = Z"
  hence "Z = S\<^sup>T * Z"
    by (metis S_mapping Z_point order.antisym bijective_reverse inf.eq_refl shunt_mapping)
  thus "1 = top"
    by (metis S_star_Z_top Z_point inf.eq_refl star_left_induct sup.absorb2 symmetric_top_closed top_le)
next
  assume "1 = top"
  thus "M = Z"
    using S_mapping comp_right_one mult_1_left by auto
qed

text \<open>Theorem 12.3\<close>

lemma S_irreflexive:
  assumes "M \<noteq> Z"
  shows "irreflexive S"
proof -
  have "(S \<sqinter> 1) * S\<^sup>T \<le> S \<sqinter> 1"
    by (smt (z3) S_injective S_mapping coreflexive_comp_top_inf dual_order.eq_iff inf.cobounded1 inf.sup_monoid.add_commute inf.sup_same_context mult_left_isotone one_inf_conv top_right_mult_increasing total_var)
  hence "(S \<sqinter> 1) * S\<^sup>T\<^sup>\<star> \<le> S \<sqinter> 1"
    using star_right_induct_mult by blast
  hence "(S \<sqinter> 1) * S\<^sup>T\<^sup>\<star> * Z \<le> (S \<sqinter> 1) * Z"
    by (simp add: mult_left_isotone)
  also have "... = M \<sqinter> Z"
    by (simp add: Z_point injective_comp_right_dist_inf)
  also have "... = bot"
    by (smt (verit, ccfv_threshold) M_point_or_bot assms Z_point bijective_one_closed bijective_regular comp_associative conv_complement coreflexive_comp_top_inf epm_3 inf.sup_monoid.add_commute one_inf_conv regular_mult_closed star.circ_increasing star.circ_zero tarski vector_conv_covector vector_export_comp_unit)
  finally have "S \<sqinter> 1 \<le> bot"
    using S_star_Z_top comp_associative le_bot top_right_mult_increasing by fastforce
  thus ?thesis
    using le_bot pseudo_complement by blast
qed

text \<open>
We show that \<open>S'\<close> satisfies most properties of \<open>S\<close>.
\<close>

lemma M_regular:
  "regular M"
  using S_mapping Z_point bijective_regular mapping_regular regular_mult_closed by blast

lemma S'_regular:
  "regular S'"
  using S_mapping mapping_regular by auto

text \<open>Theorem 10.3\<close>

lemma S'_star_Z_top:
  "S'\<^sup>T\<^sup>\<star> * Z = top"
proof -
  have "S\<^sup>T\<^sup>\<star> * Z = (S' \<squnion> (S \<sqinter> M))\<^sup>T\<^sup>\<star> * Z"
    by (metis M_regular maddux_3_11_pp S'_var)
  also have "... \<le> S'\<^sup>T\<^sup>\<star> * Z"
  proof (cases "M = bot")
    case True
    thus ?thesis
      by simp
  next
    case False
    hence "point M"
      using M_point_or_bot by auto
    hence "arc (S \<sqinter> M)"
      using S_mapping mapping_inf_point_arc by blast
    hence 1: "arc ((S \<sqinter> M)\<^sup>T)"
      using conv_involutive by auto
    have 2: "S \<sqinter> M \<le> Z\<^sup>T"
      by (metis S'_var Z_point bijective_regular conv_complement inf.cobounded2 p_shunting_swap)
    have "(S' \<squnion> (S \<sqinter> M))\<^sup>T\<^sup>\<star> * Z = (S'\<^sup>T \<squnion> (S \<sqinter> M)\<^sup>T)\<^sup>\<star> * Z"
      by (simp add: S'_var conv_dist_sup)
    also have "... = (S'\<^sup>T\<^sup>\<star> * (S \<sqinter> M)\<^sup>T * S'\<^sup>T\<^sup>\<star> \<squnion> S'\<^sup>T\<^sup>\<star>) * Z"
      using 1 star_arc_decompose sup_commute by auto
    also have "... = S'\<^sup>T\<^sup>\<star> * (S \<sqinter> M)\<^sup>T * S'\<^sup>T\<^sup>\<star> * Z \<squnion> S'\<^sup>T\<^sup>\<star> * Z"
      using mult_right_dist_sup by auto
    also have "... \<le> S'\<^sup>T\<^sup>\<star> * Z\<^sup>T\<^sup>T * S'\<^sup>T\<^sup>\<star> * Z \<squnion> S'\<^sup>T\<^sup>\<star> * Z"
      using 2 by (meson comp_isotone conv_isotone inf.eq_refl semiring.add_mono)
    also have "... \<le> S'\<^sup>T\<^sup>\<star> * Z"
      by (metis Z_point comp_associative conv_involutive le_supI mult_right_isotone top.extremum)
    finally show ?thesis
      .
  qed
  finally show ?thesis
    using S_star_Z_top top_le by auto
qed

text \<open>Theorem 10.5\<close>

lemma Z_below_S'_star:
  "Z \<le> S'\<^sup>\<star>"
  by (metis S'_star_Z_top Z_point comp_associative comp_right_one conv_order conv_star_commute mult_right_isotone vector_conv_covector)

text \<open>Theorem 10.6\<close>

lemma S'_connected:
  "S'\<^sup>T\<^sup>\<star> * S'\<^sup>\<star> = top"
  by (metis Z_below_S'_star S'_star_Z_top mult_left_dist_sup sup.orderE sup_commute top.extremum)

text \<open>Theorem 10.7\<close>

lemma S'_star_connex:
  "S'\<^sup>\<star> \<squnion> S'\<^sup>T\<^sup>\<star> = top"
  using S'_connected S'_univalent cancel_separate_eq sup_commute by auto

text \<open>Theorem 10.8\<close>

lemma Z_sup_conv_S'_top:
  "Z \<squnion> S'\<^sup>T * top = top"
  using S'_star_Z_top star.circ_loop_fixpoint sup_commute by auto

lemma top_S'_sup_conv_Z:
  "top * S' \<squnion> Z\<^sup>T = top"
  by (metis S'_star_Z_top conv_dist_comp conv_involutive conv_star_commute star.circ_back_loop_fixpoint symmetric_top_closed)

lemma S_power_point_or_bot:
  assumes "regular S'"
  shows "point (S'\<^sup>T ^ n * Z) \<or> S'\<^sup>T ^ n * Z = bot"
proof -
  have 1: "regular (S'\<^sup>T ^ n * Z)"
    using assms Z_point bijective_regular regular_conv_closed regular_mult_closed regular_power_closed by auto
  have "injective (S'\<^sup>T ^ n)"
    by (simp add: injective_power_closed S'_univalent)
  hence "injective (S'\<^sup>T ^ n * Z)"
    using Z_point injective_mult_closed by blast
  thus ?thesis
    using 1 Z_point comp_associative tarski by force
qed

end

subsection \<open>Initialising Ranks\<close>

text \<open>
We show that the rank array satisfies three properties which are established/preserved by the union-find operations.
First, every node has a rank, that is, the rank array is a mapping.
Second, the rank of a node is strictly smaller than the rank of its parent, except if the node is a root.
This implies that the rank of a node is an upper bound on the height of its subtree.
Third, the number of roots in the disjoint-set forest (the number of disjoint sets) is not larger than $m-k$ where $m$ is the total number of nodes and $k$ is the maximum rank of any node.
The third property is useful to show that ranks never overflow (exceed $m-1$).
To compare the number of roots and $m-k$ we use the existence of an injective univalent relation between the set of roots and the set of $m-k$ largest numbers, both represented as vectors.
The three properties are captured in \<open>rank_property\<close>.
\<close>

class skra_peano_3 = stone_kleene_relation_algebra_tarski_finite_regular + skra_peano_2
begin

definition "card_less_eq v w \<equiv> \<exists>i . injective i \<and> univalent i \<and> regular i \<and> v \<le> i * w"
definition "rank_property p rank \<equiv> mapping rank \<and> (p - 1) * rank \<le> rank * S'\<^sup>+ \<and> card_less_eq (roots p) (-(S'\<^sup>+ * rank\<^sup>T * top))"

end

class skra_peano_4 = stone_kleene_relation_algebra_choose_point_finite_regular + skra_peano_2
begin

subclass skra_peano_3 ..

text \<open>
The initialisation loop is augmented by setting the rank of each node to $0$.
The resulting rank array satisfies the desired properties explained above.
\<close>

theorem init_ranks:
  "VARS h p x rank
  [ True ]
  FOREACH x
    USING h
      INV { p - h = 1 - h \<and> rank - h = Z\<^sup>T - h }
       DO p := make_set p x;
          rank[x] := Z
       OD
  [ p = 1 \<and> disjoint_set_forest p \<and> rank = Z\<^sup>T \<and> rank_property p rank \<and> h = bot ]"
proof vcg_tc_simp
  fix h p rank
  let ?x = "choose_point h"
  let ?m = "make_set p ?x"
  let ?rank = "rank[?x\<longmapsto>Z]"
  assume 1: "regular h \<and> vector h \<and> p - h = 1 - h \<and> rank - h = Z\<^sup>T - h \<and> h \<noteq> bot"
  show "vector (-?x \<sqinter> h) \<and>
        ?m \<sqinter> (--?x \<squnion> -h) = 1 \<sqinter> (--?x \<squnion> -h) \<and>
        ?rank \<sqinter> (--?x \<squnion> -h) = Z\<^sup>T \<sqinter> (--?x \<squnion> -h) \<and>
        card { x . regular x \<and> x \<le> -?x \<and> x \<le> h } < h\<down>"
  proof (intro conjI)
    show "vector (-?x \<sqinter> h)"
      using 1 choose_point_point vector_complement_closed vector_inf_closed by blast
    have 2: "point ?x \<and> regular ?x"
      using 1 bijective_regular choose_point_point by blast
    have 3: "-h \<le> -?x"
      using choose_point_decreasing p_antitone_iff by auto
    have 4: "?x \<sqinter> ?m = ?x * ?x\<^sup>T \<and> -?x \<sqinter> ?m = -?x \<sqinter> p"
      using 1 choose_point_point make_set_function make_set_postcondition_def by auto
    have "?m \<sqinter> (--?x \<squnion> -h) = (?m \<sqinter> ?x) \<squnion> (?m - h)"
      using 2 comp_inf.comp_left_dist_sup by auto
    also have "... = ?x * ?x\<^sup>T \<squnion> (?m \<sqinter> -?x \<sqinter> -h)"
      using 3 4 by (smt (z3) inf_absorb2 inf_assoc inf_commute)
    also have "... = ?x * ?x\<^sup>T \<squnion> (1 - h)"
      using 1 3 4 inf.absorb2 inf.sup_monoid.add_assoc inf_commute by auto
    also have "... = (1 \<sqinter> ?x) \<squnion> (1 - h)"
      using 2 by (metis inf.cobounded2 inf.sup_same_context one_inf_conv vector_covector)
    also have "... = 1 \<sqinter> (--?x \<squnion> -h)"
      using 2 comp_inf.semiring.distrib_left by auto
    finally show "?m \<sqinter> (--?x \<squnion> -h) = 1 \<sqinter> (--?x \<squnion> -h)"
      .
    have 5: "?x \<sqinter> ?rank = ?x \<sqinter> Z\<^sup>T \<and> -?x \<sqinter> ?rank = -?x \<sqinter> rank"
      by (smt (z3) inf_commute order_refl update_inf_different update_inf_same)
    have "?rank \<sqinter> (--?x \<squnion> -h) = (?rank \<sqinter> ?x) \<squnion> (?rank - h)"
      using 2 comp_inf.comp_left_dist_sup by auto
    also have "... = (?x \<sqinter> Z\<^sup>T) \<squnion> (?rank \<sqinter> -?x \<sqinter> -h)"
      using 3 5 by (smt (z3) inf_absorb2 inf_assoc inf_commute)
    also have "... = (Z\<^sup>T \<sqinter> ?x) \<squnion> (Z\<^sup>T - h)"
      using 1 3 5 inf.absorb2 inf.sup_monoid.add_assoc inf_commute by auto
    also have "... = Z\<^sup>T \<sqinter> (--?x \<squnion> -h)"
      using 2 comp_inf.semiring.distrib_left by auto
    finally show "?rank \<sqinter> (--?x \<squnion> -h) = Z\<^sup>T \<sqinter> (--?x \<squnion> -h)"
      .
    have 5: "\<not> ?x \<le> -?x"
      using 1 2 by (metis comp_commute_below_diversity conv_order inf.cobounded2 inf_absorb2 pseudo_complement strict_order_var top.extremum)
    have 6: "?x \<le> h"
      using 1 by (metis choose_point_decreasing)
    show "card { x . regular x \<and> x \<le> -?x \<and> x \<le> h } < h\<down>"
      apply (rule psubset_card_mono)
      using finite_regular apply simp
      using 2 5 6 by auto
  qed
next
  show "rank_property 1 (Z\<^sup>T)"
  proof (unfold rank_property_def, intro conjI)
    show "univalent (Z\<^sup>T)" "total (Z\<^sup>T)"
      using Z_point surjective_conv_total by auto
    show "(1 - 1) * (Z\<^sup>T) \<le> (Z\<^sup>T) * S'\<^sup>+"
      by simp
    have "top \<le> 1 * -(S'\<^sup>+ * Z * top)"
      by (simp add: S'_Z comp_associative star_simulation_right_equal)
    thus "card_less_eq (roots 1) (-(S'\<^sup>+ * Z\<^sup>T\<^sup>T * top))"
      by (metis conv_involutive inf.idem mapping_one_closed regular_one_closed card_less_eq_def bijective_one_closed)
  qed
qed

end

subsection \<open>Union by Rank\<close>

text \<open>
We show that path compression and union-by-rank preserve the rank property.
\<close>

context stone_kleene_relation_algebra_tarski_finite_regular
begin

lemma union_sets_1_swap:
  assumes "union_sets_precondition p0 x y"
    and "path_compression_postcondition p1 x r p0"
    and "path_compression_postcondition p2 y s p1"
  shows "union_sets_postcondition (p2[s\<longmapsto>r]) x y p0"
proof (unfold union_sets_postcondition_def union_sets_precondition_def, intro conjI)
  let ?p = "p2[s\<longmapsto>r]"
  have 1: "disjoint_set_forest p1 \<and> point r \<and> r = root p1 x \<and> p1 \<sqinter> 1 = p0 \<sqinter> 1 \<and> fc p1 = fc p0"
    using assms(2) path_compression_precondition_def path_compression_postcondition_def by auto
  have 2: "disjoint_set_forest p2 \<and> point s \<and> s = root p2 y \<and> p2 \<sqinter> 1 = p1 \<sqinter> 1 \<and> fc p2 = fc p1"
    using assms(3) path_compression_precondition_def path_compression_postcondition_def by auto
  hence 3: "fc p2 = fc p0"
    using 1 by simp
  show 4: "univalent ?p"
    using 1 2 update_univalent by blast
  show "total ?p"
    using 1 2 bijective_regular update_total by blast
  show "acyclic (?p - 1)"
  proof (cases "r = s")
    case True
    thus ?thesis
      using 2 update_acyclic_5 by fastforce
  next
    case False
    hence "bot = s \<sqinter> r"
      using 1 2 distinct_points inf_commute by blast
    also have "... = s \<sqinter> p1\<^sup>T\<^sup>\<star> * r"
      using 1 by (smt root_transitive_successor_loop)
    also have "... = s \<sqinter> p2\<^sup>T\<^sup>\<star> * r"
      using 1 2 by (smt (z3) inf_assoc inf_commute same_root)
    finally have "r \<sqinter> p2\<^sup>\<star> * s = bot"
      using schroeder_1 conv_star_commute inf.sup_monoid.add_commute by fastforce
    thus ?thesis
      using 1 2 update_acyclic_4 by blast
  qed
  show "vector x"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "injective x"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "surjective x"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "vector y"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "injective y"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "surjective y"
    using assms(1) by (simp add: union_sets_precondition_def)
  show "fc ?p = wcc (p0 \<squnion> x * y\<^sup>T)"
  proof (rule order.antisym)
    have "s = p2[[s]]"
      using 2 by (metis root_successor_loop)
    hence "s * s\<^sup>T \<le> p2\<^sup>T"
      using 2 eq_refl shunt_bijective by blast
    hence "s * s\<^sup>T \<le> p2"
      using 2 conv_order coreflexive_symmetric by fastforce
    hence "s \<le> p2 * s"
      using 2 shunt_bijective by blast
    hence 5: "p2[[s]] \<le> s"
      using 2 shunt_mapping by blast
    have "s \<sqinter> p2 \<le> s * (top \<sqinter> s\<^sup>T * p2)"
      using 2 by (metis dedekind_1)
    also have "... = s * s\<^sup>T * p2"
      by (simp add: mult_assoc)
    also have "... \<le> s * s\<^sup>T"
      using 5 by (metis comp_associative conv_dist_comp conv_involutive conv_order mult_right_isotone)
    also have "... \<le> 1"
      using 2 by blast
    finally have 6: "s \<sqinter> p2 \<le> 1"
      by simp
    have "p0 \<le> wcc p0"
      by (simp add: star.circ_sub_dist_1)
    also have "... = wcc p2"
      using 3 by (simp add: star_decompose_1)
    also have 7: "... \<le> wcc ?p"
    proof -
      have "wcc p2 = wcc ((-s \<sqinter> p2) \<squnion> (s \<sqinter> p2))"
        using 2 by (metis bijective_regular inf.sup_monoid.add_commute maddux_3_11_pp)
      also have "... \<le> wcc ((-s \<sqinter> p2) \<squnion> 1)"
        using 6 wcc_isotone sup_right_isotone by simp
      also have "... = wcc (-s \<sqinter> p2)"
        using wcc_with_loops by simp
      also have "... \<le> wcc ?p"
        using wcc_isotone sup_ge2 by blast
      finally show ?thesis
        by simp
    qed
    finally have 8: "p0 \<le> wcc ?p"
      by force
    have "s \<le> p2\<^sup>T\<^sup>\<star> * y"
      using 2 by (metis inf_le1)
    hence 9: "s * y\<^sup>T \<le> p2\<^sup>T\<^sup>\<star>"
      using assms(1) shunt_bijective union_sets_precondition_def by blast
    hence "y * s\<^sup>T \<le> p2\<^sup>\<star>"
      using conv_dist_comp conv_order conv_star_commute by force
    also have "... \<le> wcc p2"
      by (simp add: star.circ_sub_dist)
    also have "... \<le> wcc ?p"
      using 7 by simp
    finally have 10: "y * s\<^sup>T \<le> wcc ?p"
      by simp
    have 11: "s * r\<^sup>T \<le> wcc ?p"
      using 1 2 star.circ_sub_dist_1 sup_assoc vector_covector by auto
    have "r \<le> p1\<^sup>T\<^sup>\<star> * x"
      using 1 by (metis inf_le1)
    hence 12: "r * x\<^sup>T \<le> p1\<^sup>T\<^sup>\<star>"
      using assms(1) shunt_bijective union_sets_precondition_def by blast
    also have "... \<le> wcc p1"
      using star_isotone sup_ge2 by blast
    also have "... = wcc p2"
      using 2 by (simp add: star_decompose_1)
    also have "... \<le> wcc ?p"
      using 7 by simp
    finally have 13: "r * x\<^sup>T \<le> wcc ?p"
      by simp
    have "x \<le> x * r\<^sup>T * r \<and> y \<le> y * s\<^sup>T * s"
      using 1 2 shunt_bijective by blast
    hence "y * x\<^sup>T \<le> y * s\<^sup>T * s * (x * r\<^sup>T * r)\<^sup>T"
      using comp_isotone conv_isotone by blast
    also have "... = y * s\<^sup>T * s * r\<^sup>T * r * x\<^sup>T"
      by (simp add: comp_associative conv_dist_comp)
    also have "... \<le> wcc ?p * (s * r\<^sup>T) * (r * x\<^sup>T)"
      using 10 by (metis mult_left_isotone mult_assoc)
    also have "... \<le> wcc ?p * wcc ?p * (r * x\<^sup>T)"
      using 11 by (metis mult_left_isotone mult_right_isotone)
    also have "... \<le> wcc ?p * wcc ?p * wcc ?p"
      using 13 by (metis mult_right_isotone)
    also have "... = wcc ?p"
      by (simp add: star.circ_transitive_equal)
    finally have "x * y\<^sup>T \<le> wcc ?p"
      by (metis conv_dist_comp conv_involutive conv_order wcc_equivalence)
    hence "p0 \<squnion> x * y\<^sup>T \<le> wcc ?p"
      using 8 by simp
    hence "wcc (p0 \<squnion> x * y\<^sup>T) \<le> wcc ?p"
      using wcc_below_wcc by simp
    thus "wcc (p0 \<squnion> x * y\<^sup>T) \<le> fc ?p"
      using 4 fc_wcc by simp
    have "-s \<sqinter> p2 \<le> wcc p2"
      by (simp add: inf.coboundedI2 star.circ_sub_dist_1)
    also have "... = wcc p0"
      using 3 by (simp add: star_decompose_1)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by (simp add: wcc_isotone)
    finally have 14: "-s \<sqinter> p2 \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by simp
    have "s * y\<^sup>T \<le> wcc p2"
      using 9 inf.order_trans star.circ_sub_dist sup_commute by fastforce
    also have "... = wcc p0"
      using 1 2 by (simp add: star_decompose_1)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by (simp add: wcc_isotone)
    finally have 15: "s * y\<^sup>T \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by simp
    have 16: "y * x\<^sup>T \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      using le_supE star.circ_sub_dist_1 by blast
    have "x * r\<^sup>T \<le> p1\<^sup>\<star>"
      using 12 conv_dist_comp conv_order conv_star_commute by fastforce
    also have "... \<le> wcc p1"
      using star.circ_sub_dist sup_commute by fastforce
    also have "... = wcc p0"
      using 1 by (simp add: star_decompose_1)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by (simp add: wcc_isotone)
    finally have 17: "x * r\<^sup>T \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      by simp
    have "r \<le> r * x\<^sup>T * x \<and> s \<le> s * y\<^sup>T * y"
      using assms(1) shunt_bijective union_sets_precondition_def by blast
    hence "s * r\<^sup>T \<le> s * y\<^sup>T * y * (r * x\<^sup>T * x)\<^sup>T"
      using comp_isotone conv_isotone by blast
    also have "... = s * y\<^sup>T * y * x\<^sup>T * x * r\<^sup>T"
      by (simp add: comp_associative conv_dist_comp)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T) * (y * x\<^sup>T) * (x * r\<^sup>T)"
      using 15 by (metis mult_left_isotone mult_assoc)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T) * wcc (p0 \<squnion> y * x\<^sup>T) * (x * r\<^sup>T)"
      using 16 by (metis mult_left_isotone mult_right_isotone)
    also have "... \<le> wcc (p0 \<squnion> y * x\<^sup>T) * wcc (p0 \<squnion> y * x\<^sup>T) * wcc (p0 \<squnion> y * x\<^sup>T)"
      using 17 by (metis mult_right_isotone)
    also have "... = wcc (p0 \<squnion> y * x\<^sup>T)"
      by (simp add: star.circ_transitive_equal)
    finally have "?p \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      using 1 2 14 vector_covector by auto
    hence "wcc ?p \<le> wcc (p0 \<squnion> y * x\<^sup>T)"
      using wcc_below_wcc by blast
    also have "... = wcc (p0 \<squnion> x * y\<^sup>T)"
      using conv_dist_comp conv_dist_sup sup_assoc sup_commute by auto
    finally show "fc ?p \<le> wcc (p0 \<squnion> x * y\<^sup>T)"
      using 4 fc_wcc by simp
  qed
qed

lemma union_sets_1_skip:
  assumes "union_sets_precondition p0 x y"
    and "path_compression_postcondition p1 x r p0"
    and "path_compression_postcondition p2 y r p1"
  shows "union_sets_postcondition p2 x y p0"
proof (unfold union_sets_postcondition_def union_sets_precondition_def, intro conjI)
  have 1: "point r \<and> r = root p1 x \<and> fc p1 = fc p0 \<and> disjoint_set_forest p2 \<and> r = root p2 y \<and> fc p2 = fc p1"
    using assms(2,3) path_compression_precondition_def path_compression_postcondition_def by auto
  thus "univalent p2" "total p2" "acyclic (p2 - 1)"
    by auto
  show "vector x" "injective x" "surjective x" "vector y" "injective y" "surjective y"
    using assms(1) union_sets_precondition_def by auto
  have "r \<le> p1\<^sup>T\<^sup>\<star> * x"
    using 1 by (metis inf_le1)
  hence "r * x\<^sup>T \<le> p1\<^sup>T\<^sup>\<star>"
    using assms(1) shunt_bijective union_sets_precondition_def by blast
  hence 2: "x * r\<^sup>T \<le> p1\<^sup>\<star>"
    using conv_dist_comp conv_order conv_star_commute by force
  have "r \<le> p2\<^sup>T\<^sup>\<star> * y"
    using 1 by (metis inf_le1)
  hence 3: "r * y\<^sup>T \<le> p2\<^sup>T\<^sup>\<star>"
    using assms(1) shunt_bijective union_sets_precondition_def by blast
  have "x * y\<^sup>T \<le> x * r\<^sup>T * r * y\<^sup>T"
    using 1 mult_left_isotone shunt_bijective by blast
  also have "... \<le> p1\<^sup>\<star> * p2\<^sup>T\<^sup>\<star>"
    using 2 3 by (metis comp_associative comp_isotone)
  also have "... \<le> wcc p0"
    using 1 by (metis star.circ_mult_upper_bound star_decompose_1 star_isotone sup_ge2 star.circ_sub_dist)
  finally show "fc p2 = wcc (p0 \<squnion> x * y\<^sup>T)"
    using 1 by (smt (z3) fc_star star_decompose_1 sup_absorb1 wcc_sup_wcc star.circ_sub_dist_3 sup_commute wcc_equivalence)
qed

end

syntax
  "_Cond1" :: "'bexp \<Rightarrow> 'com \<Rightarrow> 'com"  ("(1IF _/ THEN _/ FI)" [0,0] 61)
translations "IF b THEN c FI" == "IF b THEN c ELSE SKIP FI"

context skra_peano_3
begin

lemma path_compression_preserves_rank_property:
  assumes "path_compression_postcondition p x y p0"
      and "disjoint_set_forest p0"
      and "rank_property p0 rank"
    shows "rank_property p rank"
proof (unfold rank_property_def, intro conjI)
  let ?px = "p0\<^sup>T\<^sup>\<star> * x"
  have 1: "point y"
    using assms(1,2) path_compression_postcondition_def path_compression_precondition_def root_point by auto
  have 2: "vector ?px"
    using assms(1) comp_associative path_compression_postcondition_def path_compression_precondition_def by auto
  have "root p0 x = root p x"
    by (smt (verit) assms(1,2) path_compression_postcondition_def path_compression_precondition_def same_root)
  hence "root p0 x = y"
    using assms(1) path_compression_postcondition_def path_compression_precondition_def by auto
  hence "?px \<le> p0\<^sup>\<star> * y"
    by (meson assms(1,2) path_splitting_invariant_aux_1(3) path_compression_precondition_def path_compression_postcondition_def)
  hence "?px * y\<^sup>T \<le> p0\<^sup>\<star>"
    using 1 shunt_bijective by blast
  hence "?px \<sqinter> y\<^sup>T \<le> p0\<^sup>\<star>"
    using 1 2 by (simp add: vector_covector)
  also have "... = (p0 - 1)\<^sup>+ \<squnion> 1"
    using reachable_without_loops star_left_unfold_equal sup_commute by fastforce
  finally have 3: "?px \<sqinter> y\<^sup>T \<sqinter> -1 \<le> (p0 - 1)\<^sup>+"
    using half_shunting by blast
  have "p0[?px\<longmapsto>y] = p"
    using assms(1) path_compression_postcondition_def by simp
  hence "(p - 1) * rank = (?px \<sqinter> y\<^sup>T \<sqinter> -1) * rank \<squnion> (-?px \<sqinter> p0 \<sqinter> -1) * rank"
    using inf_sup_distrib2 mult_right_dist_sup by force
  also have "... \<le> (?px \<sqinter> y\<^sup>T \<sqinter> -1) * rank \<squnion> (p0 - 1) * rank"
    by (meson comp_inf.mult_semi_associative le_infE mult_left_isotone sup_right_isotone)
  also have "... \<le> (?px \<sqinter> y\<^sup>T \<sqinter> -1) * rank \<squnion> rank * S'\<^sup>+"
    using assms(3) rank_property_def sup_right_isotone by auto
  also have "... \<le> (p0 - 1)\<^sup>+ * rank \<squnion> rank * S'\<^sup>+"
    using 3 mult_left_isotone sup_left_isotone by blast
  also have "... \<le> rank * S'\<^sup>+"
  proof -
    have "(p0 - 1)\<^sup>\<star> * rank \<le> rank * S'\<^sup>\<star>"
      using assms(3) rank_property_def star_simulation_left star.left_plus_circ by fastforce
    hence "(p0 - 1)\<^sup>+ * rank \<le> (p0 - 1) * rank * S'\<^sup>\<star>"
      by (simp add: comp_associative mult_right_isotone)
    also have "... \<le> rank * S'\<^sup>+"
      by (smt (z3) assms(3) rank_property_def comp_associative comp_left_subdist_inf inf.boundedE inf.sup_right_divisibility star.circ_transitive_equal)
    finally show ?thesis
      by simp
  qed
  finally show "(p - 1) * rank \<le> rank * S'\<^sup>+"
    .
  show "univalent rank" "total rank"
    using rank_property_def assms(3) by auto
  show "card_less_eq (roots p) (-(S'\<^sup>+ * rank\<^sup>T * top))"
    using assms(1,3) path_compression_postcondition_def rank_property_def by auto
qed

theorem union_sets_by_rank:
  "VARS p r s rank
  [ union_sets_precondition p x y \<and> rank_property p rank \<and> p0 = p ]
  r := find_set p x;
  p := path_compression p x r;
  s := find_set p y;
  p := path_compression p y s;
  IF r \<noteq> s THEN
    IF rank[[r]] \<le> S'\<^sup>+ * (rank[[s]]) THEN
      p[r] := s
    ELSE
      p[s] := r;
      IF rank[[r]] = rank[[s]] THEN
        rank[r] := S'\<^sup>T * (rank[[r]])
      FI
    FI
  FI
  [ union_sets_postcondition p x y p0 \<and> rank_property p rank ]"
proof vcg_tc_simp
  fix rank
  let ?r = "find_set p0 x"
  let ?p1 = "path_compression p0 x ?r"
  let ?s = "find_set ?p1 y"
  let ?p2 = "path_compression ?p1 y ?s"
  let ?p5 = "path_compression ?p1 y ?r"
  let ?rr = "rank[[?r]]"
  let ?rs = "rank[[?s]]"
  let ?rank = "rank[?r\<longmapsto>S'\<^sup>T * ?rs]"
  let ?p3 = "?p2[?r\<longmapsto>?s]"
  let ?p4 = "?p2[?s\<longmapsto>?r]"
  assume 1: "union_sets_precondition p0 x y \<and> rank_property p0 rank"
  hence 2: "path_compression_postcondition ?p1 x ?r p0"
    using find_set_function find_set_postcondition_def find_set_precondition_def path_compression_function path_compression_precondition_def union_sets_precondition_def by auto
  hence 3: "path_compression_postcondition ?p2 y ?s ?p1"
    using 1 find_set_function find_set_postcondition_def find_set_precondition_def path_compression_function path_compression_precondition_def union_sets_precondition_def path_compression_postcondition_def by meson
  have "rank_property ?p1 rank"
    using 1 2 path_compression_preserves_rank_property union_sets_precondition_def by blast
  hence 4: "rank_property ?p2 rank"
    using 1 2 3 by (meson path_compression_preserves_rank_property path_compression_postcondition_def path_compression_precondition_def)
  have 5: "point ?r" "point ?s"
    using 2 3 path_compression_postcondition_def path_compression_precondition_def by auto
  hence 6: "point ?rr" "point ?rs"
    using 1 comp_associative read_injective read_surjective rank_property_def by auto
  have "top \<le> S'\<^sup>\<star> \<squnion> S'\<^sup>+\<^sup>T"
    by (metis S'_star_connex conv_dist_comp conv_star_commute eq_refl star.circ_reflexive star_left_unfold_equal star_simulation_right_equal sup.orderE sup_monoid.add_assoc)
  hence 7: "-S'\<^sup>+\<^sup>T \<le> S'\<^sup>\<star>"
    by (metis comp_inf.case_split_left comp_inf.star.circ_plus_one comp_inf.star.circ_sup_2 half_shunting)
  show "(?r \<noteq> ?s \<longrightarrow> (?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> union_sets_postcondition ?p3 x y p0 \<and> rank_property ?p3 rank) \<and>
                      (\<not> ?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> ((?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank) \<and>
                                              (?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank)))) \<and>
        (?r = ?s \<longrightarrow> union_sets_postcondition ?p5 x y p0 \<and> rank_property ?p5 rank)"
  proof
    show "?r \<noteq> ?s \<longrightarrow> (?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> union_sets_postcondition ?p3 x y p0 \<and> rank_property ?p3 rank) \<and>
                      (\<not> ?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> ((?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank) \<and>
                                              (?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank)))"
    proof
      assume 8: "?r \<noteq> ?s"
      show "(?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> union_sets_postcondition ?p3 x y p0 \<and> rank_property ?p3 rank) \<and>
            (\<not> ?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> ((?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank) \<and>
                                    (?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank)))"
      proof
        show "?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> union_sets_postcondition ?p3 x y p0 \<and> rank_property ?p3 rank"
        proof
          assume 9: "?rr \<le> S'\<^sup>+ * ?rs"
          show "union_sets_postcondition ?p3 x y p0 \<and> rank_property ?p3 rank"
          proof
            show "union_sets_postcondition ?p3 x y p0"
              using 1 2 3 by (simp add: union_sets_1)
            show "rank_property ?p3 rank"
            proof (unfold rank_property_def, intro conjI)
              show "univalent rank" "total rank"
                using 1 rank_property_def by auto
              have "?s \<le> -?r"
                using 5 8 by (meson order.antisym bijective_regular point_in_vector_or_complement point_in_vector_or_complement_2)
              hence "?r \<sqinter> ?s\<^sup>T \<sqinter> 1 = bot"
                by (metis (full_types) bot_least inf.left_commute inf.sup_monoid.add_commute one_inf_conv pseudo_complement)
              hence "?p3 \<sqinter> 1 \<le> ?p2"
                by (smt half_shunting inf.cobounded2 pseudo_complement regular_one_closed semiring.add_mono sup_commute)
              hence "roots ?p3 \<le> roots ?p2"
                by (simp add: mult_left_isotone)
              thus "card_less_eq (roots ?p3) (-(S'\<^sup>+ * rank\<^sup>T * top))"
                using 4 by (meson rank_property_def card_less_eq_def order_trans)
              have "(?p3 - 1) * rank = (?r \<sqinter> ?s\<^sup>T \<sqinter> -1) * rank \<squnion> (-?r \<sqinter> ?p2 \<sqinter> -1) * rank"
                using comp_inf.semiring.distrib_right mult_right_dist_sup by auto
              also have "... \<le> (?r \<sqinter> ?s\<^sup>T \<sqinter> -1) * rank \<squnion> (?p2 - 1) * rank"
                using comp_inf.mult_semi_associative mult_left_isotone sup_right_isotone by auto
              also have "... \<le> (?r \<sqinter> ?s\<^sup>T \<sqinter> -1) * rank \<squnion> rank * S'\<^sup>+"
                using 4 sup_right_isotone rank_property_def by blast
              also have "... \<le> (?r \<sqinter> ?s\<^sup>T) * rank \<squnion> rank * S'\<^sup>+"
                using inf_le1 mult_left_isotone sup_left_isotone by blast
              also have "... = ?r * ?s\<^sup>T * rank \<squnion> rank * S'\<^sup>+"
                using 5 by (simp add: vector_covector)
              also have "... = rank * S'\<^sup>+"
              proof -
                have "rank\<^sup>T * ?r \<le> S'\<^sup>+ * rank\<^sup>T * ?s"
                  using 9 comp_associative by auto
                hence "?r \<le> rank * S'\<^sup>+ * rank\<^sup>T * ?s"
                  using 4 shunt_mapping comp_associative rank_property_def by auto
                hence "?r * ?s\<^sup>T \<le> rank * S'\<^sup>+ * rank\<^sup>T"
                  using 5 shunt_bijective by blast
                hence "?r * ?s\<^sup>T * rank \<le> rank * S'\<^sup>+"
                  using 4 shunt_bijective rank_property_def mapping_conv_bijective by auto
                thus ?thesis
                  using sup_absorb2 by blast
              qed
              finally show "(?p3 - 1) * rank \<le> rank * S'\<^sup>+"
                .
            qed
          qed
        qed
        show "\<not> ?rr \<le> S'\<^sup>+ * ?rs \<longrightarrow> ((?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank) \<and>
                                     (?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank))"
        proof
          assume "\<not> ?rr \<le> S'\<^sup>+ * ?rs"
          hence "?rr \<le> -(S'\<^sup>+ * ?rs)"
            using 6 by (meson point_in_vector_or_complement S'_regular bijective_regular regular_closed_star regular_mult_closed vector_mult_closed)
          also have "... = -S'\<^sup>+ * ?rs"
            using 6 comp_bijective_complement by simp
          finally have "?rs \<le> -S'\<^sup>+\<^sup>T * ?rr"
            using 6 by (metis bijective_reverse conv_complement)
          also have "... \<le> S'\<^sup>\<star> * ?rr"
            using 7 by (simp add: mult_left_isotone)
          also have "... = S'\<^sup>+ * ?rr \<squnion> ?rr"
            using star.circ_loop_fixpoint mult_assoc by auto
          finally have 10: "?rs - ?rr \<le> S'\<^sup>+ * ?rr"
            using half_shunting by blast
          show "((?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank) \<and>
                 (?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank))"
          proof
            show "?rr = ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank"
            proof
              assume 11: "?rr = ?rs"
              show "union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 ?rank"
              proof
                show "union_sets_postcondition ?p4 x y p0"
                  using 1 2 3 by (simp add: union_sets_1_swap)
                show "rank_property ?p4 ?rank"
                proof (unfold rank_property_def, intro conjI)
                  show "univalent ?rank"
                    using 4 5 6 by (meson S'_univalent read_injective update_univalent rank_property_def)
                  have "card_less_eq (roots ?p2) (-(S'\<^sup>+ * rank\<^sup>T * top))"
                    using 4 rank_property_def by blast
                  from this obtain i where 12: "injective i \<and> univalent i \<and> regular i \<and> roots ?p2 \<le> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                    using card_less_eq_def by blast
                  let ?i = "(i[?s\<longmapsto>i[[i * ?rr]]])[i * ?rr\<longmapsto>i[[?s]]]"
                  have 13: "?i = (i * ?rr \<sqinter> ?s\<^sup>T * i) \<squnion> (-(i * ?rr) \<sqinter> ?s \<sqinter> ?rr\<^sup>T * i\<^sup>T * i) \<squnion> (-(i * ?rr) \<sqinter> -?s \<sqinter> i)"
                    by (smt (z3) conv_dist_comp conv_involutive inf.sup_monoid.add_assoc inf_sup_distrib1 sup_assoc)
                  have 14: "injective ?i"
                    apply (rule update_injective_swap)
                    subgoal using 12 by simp
                    subgoal using 5 by simp
                    subgoal using 6 12 injective_mult_closed by simp
                    subgoal using 5 comp_associative by simp
                    done
                  have 15: "univalent ?i"
                    apply (rule update_univalent_swap)
                    subgoal using 12 by simp
                    subgoal using 5 by simp
                    subgoal using 5 by simp
                    subgoal using 6 12 injective_mult_closed by simp
                    subgoal using 5 comp_associative by simp
                    done
                  have 16: "regular ?i"
                    using 5 6 12 by (smt (z3) bijective_regular p_dist_inf p_dist_sup pp_dist_comp regular_closed_inf regular_conv_closed)
                  have 17: "regular (i * ?rr)"
                    using 6 12 bijective_regular regular_mult_closed by blast
                  have 18: "find_set_precondition ?p1 y"
                    using 2 3 find_set_precondition_def path_compression_postcondition_def path_compression_precondition_def by blast
                  hence "?s = root ?p1 y"
                    by (meson find_set_function find_set_postcondition_def)
                  also have "... = root ?p2 y"
                    using 3 18 by (smt (z3) find_set_precondition_def path_compression_postcondition_def path_compression_precondition_def same_root)
                  also have "... \<le> roots ?p2"
                    by simp
                  also have "... \<le> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                    using 12 by simp
                  finally have 19: "?s \<le> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                    .
                  have "roots ?p4 \<le> ?i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                  proof -
                    have "?r \<le> -?s"
                      using 5 8 by (meson order.antisym bijective_regular point_in_vector_or_complement point_in_vector_or_complement_2)
                    hence "?s \<sqinter> ?r\<^sup>T \<sqinter> 1 = bot"
                      by (metis (full_types) bot_least inf.left_commute inf.sup_monoid.add_commute one_inf_conv pseudo_complement)
                    hence "?p4 \<sqinter> 1 \<le> -?s \<sqinter> ?p2"
                      by (smt (z3) bot_least comp_inf.semiring.distrib_left inf.cobounded2 inf.sup_monoid.add_commute le_supI)
                    hence "roots ?p4 \<le> roots (-?s \<sqinter> ?p2)"
                      by (simp add: mult_left_isotone)
                    also have "... = -?s \<sqinter> roots ?p2"
                      using 5 inf_assoc vector_complement_closed vector_inf_comp by auto
                    also have "... = (i * ?rr \<sqinter> -?s \<sqinter> roots ?p2) \<squnion> (-(i * ?rr) \<sqinter> -?s \<sqinter> roots ?p2)"
                      using 17 by (smt (z3) comp_inf.star_plus inf_sup_distrib2 inf_top.right_neutral regular_complement_top)
                    also have "... \<le> ?i * (-(S'\<^sup>+ * ?rank\<^sup>T * top))"
                    proof (rule sup_least)
                      have "?rank\<^sup>T * top = (?r \<sqinter> (S'\<^sup>T * ?rs)\<^sup>T)\<^sup>T * top \<squnion> (-?r \<sqinter> rank)\<^sup>T * top"
                        using conv_dist_sup mult_right_dist_sup by auto
                      also have "... = (?r\<^sup>T \<sqinter> S'\<^sup>T * ?rs) * top \<squnion> (-?r\<^sup>T \<sqinter> rank\<^sup>T) * top"
                        using conv_complement conv_dist_inf conv_involutive by auto
                      also have "... = S'\<^sup>T * ?rs * (?r \<sqinter> top) \<squnion> (-?r\<^sup>T \<sqinter> rank\<^sup>T) * top"
                        using 5 by (smt (z3) covector_inf_comp_3 inf_commute)
                      also have "... = S'\<^sup>T * ?rs * (?r \<sqinter> top) \<squnion> rank\<^sup>T * (-?r \<sqinter> top)"
                        using 5 by (smt (z3) conv_complement vector_complement_closed covector_inf_comp_3 inf_commute)
                      also have "... = S'\<^sup>T * ?rs * ?r \<squnion> rank\<^sup>T * -?r"
                        by simp
                      also have "... \<le> S'\<^sup>T * ?rs * ?r \<squnion> rank\<^sup>T * top"
                        using mult_right_isotone sup_right_isotone by force
                      also have "... \<le> S'\<^sup>T * ?rs \<squnion> rank\<^sup>T * top"
                        using 5 6 by (metis inf.eq_refl mult_assoc)
                      finally have "S'\<^sup>+ * ?rank\<^sup>T * top \<le> S'\<^sup>+ * S'\<^sup>T * ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        by (smt comp_associative mult_left_dist_sup mult_right_isotone)
                      also have "... = S'\<^sup>\<star> * (S' * S'\<^sup>T) * ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        by (smt star_plus mult_assoc)
                      also have "... \<le> S'\<^sup>\<star> * ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        by (metis S'_injective comp_right_one mult_left_isotone mult_right_isotone sup_left_isotone)
                      also have "... = ?rs \<squnion> S'\<^sup>+ * ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        using comp_associative star.circ_loop_fixpoint sup_commute by fastforce
                      also have "... = ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        by (smt (verit, del_insts) comp_associative mult_left_dist_sup sup.orderE sup_assoc sup_commute top.extremum)
                      finally have 20: "S'\<^sup>+ * ?rank\<^sup>T * top \<le> ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                        .
                      have "?s * ?s\<^sup>T = (?s \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top)) * ?s\<^sup>T"
                        using 19 inf.orderE by fastforce
                      also have "... = (?s \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top)) * top \<sqinter> ?s\<^sup>T"
                        using 5 by (smt (z3) covector_comp_inf vector_conv_covector vector_covector vector_top_closed)
                      also have "... = ?s \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top) * top \<sqinter> ?s\<^sup>T"
                        using 5 vector_inf_comp by auto
                      also have "... \<le> 1 \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top) * top"
                        using 5 by (smt (verit, ccfv_SIG) inf.cobounded1 inf.cobounded2 inf_greatest order_trans vector_covector)
                      also have "... = 1 \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using comp_associative vector_complement_closed vector_top_closed by auto
                      also have "... \<le> 1 \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T)"
                        by (meson comp_inf.mult_right_isotone mult_right_isotone p_antitone top_right_mult_increasing)
                      also have "... \<le> 1 \<sqinter> i * S'\<^sup>\<star>\<^sup>T * rank\<^sup>T"
                      proof -
                        have "S'\<^sup>\<star>\<^sup>T * rank\<^sup>T \<squnion> S'\<^sup>+ * rank\<^sup>T = (S'\<^sup>T\<^sup>\<star> \<squnion> S'\<^sup>+) * rank\<^sup>T"
                          by (simp add: conv_star_commute mult_right_dist_sup)
                        also have "... = (S'\<^sup>T\<^sup>\<star> \<squnion> S'\<^sup>\<star>) * rank\<^sup>T"
                          by (smt (z3) comp_associative semiring.distrib_right star.circ_loop_fixpoint sup.left_commute sup_commute sup_idem)
                        also have "... = top * rank\<^sup>T"
                          by (simp add: S'_star_connex sup_commute)
                        also have "... = top"
                          using 4 rank_property_def total_conv_surjective by blast
                        finally have "-(S'\<^sup>+ * rank\<^sup>T) \<le> S'\<^sup>\<star>\<^sup>T * rank\<^sup>T"
                          by (metis half_shunting inf.idem top_greatest)
                        thus ?thesis
                          using comp_associative inf.sup_right_isotone mult_right_isotone by auto
                      qed
                      also have "... = 1 \<sqinter> rank * S'\<^sup>\<star> * i\<^sup>T"
                        by (metis comp_associative conv_dist_comp conv_involutive one_inf_conv)
                      also have "... \<le> rank * S'\<^sup>\<star> * i\<^sup>T"
                        by simp
                      finally have "?s \<le> rank * S'\<^sup>\<star> * i\<^sup>T * ?s"
                        using 5 shunt_bijective by auto
                      hence "?rs \<le> S'\<^sup>\<star> * i\<^sup>T * ?s"
                        using 4 shunt_mapping comp_associative rank_property_def by auto
                      hence "?s * (i * ?rr \<sqinter> -?s \<sqinter> roots ?p2) \<le> ?s * (i * S'\<^sup>\<star> * i\<^sup>T * ?s \<sqinter> -?s \<sqinter> roots ?p2)"
                        using 11 comp_associative comp_inf.mult_left_isotone comp_isotone inf.eq_refl by auto
                      also have "... = ?s * ((i * S'\<^sup>+ * i\<^sup>T * ?s \<squnion> i * i\<^sup>T * ?s) \<sqinter> -?s \<sqinter> roots ?p2)"
                        by (metis comp_associative mult_left_dist_sup star.circ_loop_fixpoint)
                      also have "... \<le> ?s * ((i * S'\<^sup>+ * i\<^sup>T * ?s \<squnion> 1 * ?s) \<sqinter> -?s \<sqinter> roots ?p2)"
                        using 12 by (metis mult_left_isotone sup_right_isotone comp_inf.mult_left_isotone mult_right_isotone)
                      also have "... = ?s * (i * S'\<^sup>+ * i\<^sup>T * ?s \<sqinter> -?s \<sqinter> roots ?p2)"
                        using comp_inf.comp_right_dist_sup by simp
                      also have "... \<le> ?s * (i * S'\<^sup>+ * i\<^sup>T * ?s \<sqinter> roots ?p2)"
                        using comp_inf.mult_left_isotone inf.cobounded1 mult_right_isotone by blast
                      also have "... \<le> ?s * (i * S'\<^sup>+ * i\<^sup>T * ?s \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top))"
                        using 12 comp_inf.mult_right_isotone mult_right_isotone by auto
                      also have "... = ?s * (i * S'\<^sup>+ * i\<^sup>T * ?s \<sqinter> i) * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 5 by (simp add: comp_associative vector_inf_comp)
                      also have "... = (?s \<sqinter> (i * S'\<^sup>+ * i\<^sup>T * ?s)\<^sup>T) * i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 5 covector_inf_comp_3 mult_assoc by auto
                      also have "... = (?s \<sqinter> ?s\<^sup>T * i * S'\<^sup>+\<^sup>T * i\<^sup>T) * i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using conv_dist_comp conv_involutive mult_assoc by auto
                      also have "... = (?s \<sqinter> ?s\<^sup>T) * i * S'\<^sup>+\<^sup>T * i\<^sup>T * i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 5 vector_inf_comp by auto
                      also have "... \<le> i * S'\<^sup>+\<^sup>T * i\<^sup>T * i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 5 by (metis point_antisymmetric mult_left_isotone mult_left_one)
                      also have "... \<le> i * S'\<^sup>+\<^sup>T * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 12 by (smt mult_left_isotone mult_right_isotone mult_assoc comp_right_one)
                      also have "... \<le> i * -(S'\<^sup>\<star> * rank\<^sup>T * top)"
                      proof -
                        have "S'\<^sup>+ * S'\<^sup>\<star> * rank\<^sup>T * top \<le> S'\<^sup>+ * rank\<^sup>T * top"
                          by (simp add: comp_associative star.circ_transitive_equal)
                        hence "S'\<^sup>+\<^sup>T * -(S'\<^sup>+ * rank\<^sup>T * top) \<le> -(S'\<^sup>\<star> * rank\<^sup>T * top)"
                          by (smt (verit, ccfv_SIG) comp_associative conv_complement_sub_leq mult_right_isotone order.trans p_antitone)
                        thus ?thesis
                          by (simp add: comp_associative mult_right_isotone)
                      qed
                      also have "... \<le> i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                      proof -
                        have "S'\<^sup>+ * ?rank\<^sup>T * top \<le> ?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                          using 20 by simp
                        also have "... \<le> rank\<^sup>T * top \<squnion> S'\<^sup>+ * rank\<^sup>T * top"
                          using mult_right_isotone sup_left_isotone top.extremum by blast
                        also have "... = S'\<^sup>\<star> * rank\<^sup>T * top"
                          using comp_associative star.circ_loop_fixpoint sup_commute by auto
                        finally show ?thesis
                          using mult_right_isotone p_antitone by blast
                      qed
                      finally have "?s * (i * ?rr \<sqinter> -?s \<sqinter> roots ?p2) \<le> i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        .
                      hence "i * ?rr \<sqinter> -?s \<sqinter> roots ?p2 \<le> ?s\<^sup>T * i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        using 5 shunt_mapping bijective_conv_mapping mult_assoc by auto
                      hence "i * ?rr \<sqinter> -?s \<sqinter> roots ?p2 \<le> i * ?rr \<sqinter> ?s\<^sup>T * i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        by (simp add: inf.sup_monoid.add_assoc)
                      also have "... = (i * ?rr \<sqinter> ?s\<^sup>T * i) * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        using 6 vector_inf_comp vector_mult_closed by simp
                      also have "... \<le> ?i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        using 13 comp_left_increasing_sup sup_assoc by auto
                      finally show "i * ?rr \<sqinter> -?s \<sqinter> roots ?p2 \<le> ?i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        .
                      have "-(i * ?rr) \<sqinter> roots ?p2 \<le> -(i * ?rr) \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                        using 12 inf.sup_right_isotone by auto
                      also have "... \<le> -(i * ?rr) \<sqinter> i * -(?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top)"
                      proof -
                        have 21: "regular (?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top)"
                          using 4 6 rank_property_def mapping_regular S'_regular pp_dist_star regular_conv_closed regular_mult_closed bijective_regular regular_closed_sup by auto
                        have "?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top \<le> S'\<^sup>+ * rank\<^sup>T * top \<squnion> ?rr"
                          using 11 by simp
                        hence "(?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top) - S'\<^sup>+ * rank\<^sup>T * top \<le> ?rr"
                          using half_shunting sup_commute by auto
                        hence "-(S'\<^sup>+ * rank\<^sup>T * top) \<le> -(?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top) \<squnion> ?rr"
                          using 21 by (metis inf.sup_monoid.add_commute shunting_var_p sup_commute)
                        hence "i * -(S'\<^sup>+ * rank\<^sup>T * top) \<le> i * -(?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top) \<squnion> i * ?rr"
                          by (metis mult_left_dist_sup mult_right_isotone)
                        hence "-(i * ?rr) \<sqinter> i * -(S'\<^sup>+ * rank\<^sup>T * top) \<le> i * -(?rs \<squnion> S'\<^sup>+ * rank\<^sup>T * top)"
                          using half_shunting inf.sup_monoid.add_commute by fastforce
                        thus ?thesis
                          using inf.le_sup_iff by blast
                      qed
                      also have "... \<le> -(i * ?rr) \<sqinter> i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        using 20 by (meson comp_inf.mult_right_isotone mult_right_isotone p_antitone)
                      finally have "-(i * ?rr) \<sqinter> -?s \<sqinter> roots ?p2 \<le> -(i * ?rr) \<sqinter> -?s \<sqinter> i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        by (smt (z3) inf.boundedI inf.cobounded1 inf.coboundedI2 inf.sup_monoid.add_assoc inf.sup_monoid.add_commute)
                      also have "... \<le> ?i * (-(S'\<^sup>+ * ?rank\<^sup>T * top))"
                        using 5 6 13 by (smt (z3) sup_commute vector_complement_closed vector_inf_comp vector_mult_closed comp_left_increasing_sup)
                      finally show "-(i * ?rr) \<sqinter> -?s \<sqinter> roots ?p2 \<le> ?i * -(S'\<^sup>+ * ?rank\<^sup>T * top)"
                        .
                    qed
                    finally show ?thesis
                      .
                  qed
                  thus "card_less_eq (roots ?p4) (-(S'\<^sup>+ * ?rank\<^sup>T * top))"
                    using 14 15 16 card_less_eq_def by auto
                  have "?s \<le> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                    using 19 by simp
                  also have "... \<le> i * -(S'\<^sup>+ * ?rr)"
                    using mult_right_isotone p_antitone top.extremum mult_assoc by auto
                  also have "... = i * -S'\<^sup>+ * ?rr"
                    using 6 comp_bijective_complement mult_assoc by fastforce
                  finally have "?rr \<le> -S'\<^sup>T\<^sup>+ * i\<^sup>T * ?s"
                    using 5 6 by (metis conv_complement conv_dist_comp conv_plus_commute bijective_reverse)
                  also have "... \<le> S'\<^sup>\<star> * i\<^sup>T * ?s"
                    using 7 conv_plus_commute mult_left_isotone by auto
                  finally have 22: "?rr \<le> S'\<^sup>\<star> * i\<^sup>T * ?s"
                    .
                  have "?r = root ?p1 x"
                    using 2 path_compression_postcondition_def path_compression_precondition_def by blast
                  also have "... = root ?p2 x"
                    using 3 18 by (smt (z3) find_set_precondition_def path_compression_postcondition_def path_compression_precondition_def same_root)
                  also have "... \<le> roots ?p2"
                    by simp
                  also have "... \<le> i * -(S'\<^sup>+ * rank\<^sup>T * top)"
                    using 12 by simp
                  also have "... \<le> i * -(S'\<^sup>+ * ?rr)"
                    using mult_right_isotone p_antitone top.extremum mult_assoc by auto
                  also have "... = i * -S'\<^sup>+ * ?rr"
                    using 6 comp_bijective_complement mult_assoc by fastforce
                  finally have "?rr \<le> -S'\<^sup>T\<^sup>+ * i\<^sup>T * ?r"
                    using 5 6 by (metis conv_complement conv_dist_comp conv_plus_commute bijective_reverse)
                  also have "... \<le> S'\<^sup>\<star> * i\<^sup>T * ?r"
                    using 7 conv_plus_commute mult_left_isotone by auto
                  finally have "?rr \<le> S'\<^sup>\<star> * i\<^sup>T * ?r"
                    .
                  hence "?rr \<le> S'\<^sup>\<star> * i\<^sup>T * ?r \<sqinter> S'\<^sup>\<star> * i\<^sup>T * ?s"
                    using 22 inf.boundedI by blast
                  also have "... = (S'\<^sup>+ * i\<^sup>T * ?r \<squnion> i\<^sup>T * ?r) \<sqinter> S'\<^sup>\<star> * i\<^sup>T * ?s"
                    by (simp add: star.circ_loop_fixpoint mult_assoc)
                  also have "... \<le> S'\<^sup>+ * i\<^sup>T * ?r \<squnion> (i\<^sup>T * ?r \<sqinter> S'\<^sup>\<star> * i\<^sup>T * ?s)"
                    by (metis comp_inf.mult_right_dist_sup eq_refl inf.cobounded1 semiring.add_mono)
                  also have "... \<le> S' * top \<squnion> (i\<^sup>T * ?r \<sqinter> S'\<^sup>\<star> * i\<^sup>T * ?s)"
                    using comp_associative mult_right_isotone sup_left_isotone top.extremum by auto
                  also have "... = S' * top \<squnion> (i\<^sup>T * ?r \<sqinter> (S'\<^sup>+ * i\<^sup>T * ?s \<squnion> i\<^sup>T * ?s))"
                    by (simp add: star.circ_loop_fixpoint mult_assoc)
                  also have "... \<le> S' * top \<squnion> S'\<^sup>+ * i\<^sup>T * ?s \<squnion> (i\<^sup>T * ?r \<sqinter> i\<^sup>T * ?s)"
                    by (smt (z3) comp_inf.semiring.distrib_left inf.sup_right_divisibility star.circ_loop_fixpoint sup_assoc sup_commute sup_inf_distrib1)
                  also have "... \<le> S' * top \<squnion> (i\<^sup>T * ?r \<sqinter> i\<^sup>T * ?s)"
                    by (metis comp_associative mult_right_isotone order.refl sup.orderE top.extremum)
                  also have "... = S' * top \<squnion> i\<^sup>T * (?r \<sqinter> ?s)"
                    using 12 conv_involutive univalent_comp_left_dist_inf by auto
                  also have "... = S' * top"
                    using 5 8 distinct_points by auto
                  finally have "top \<le> ?rr\<^sup>T * S' * top"
                    using 6 by (smt conv_involutive shunt_mapping bijective_conv_mapping mult_assoc)
                  hence "surjective (S'\<^sup>T * ?rs)"
                    using 6 11 by (smt conv_dist_comp conv_involutive point_conv_comp top_le)
                  thus "total ?rank"
                    using 4 5 bijective_regular update_total rank_property_def by blast
                  show "(?p4 - 1) * ?rank \<le> ?rank * S'\<^sup>+"
                  proof -
                    have 23: "univalent ?p2"
                      using 3 path_compression_postcondition_def path_compression_precondition_def by blast
                    have 24: "?r \<sqinter> (?p4 - 1) * ?rank \<le> ?s\<^sup>T * rank * S' * S'\<^sup>+"
                    proof -
                      have "?r \<sqinter> (?p4 - 1) * ?rank = (?r \<sqinter> ?p4 \<sqinter> -1) * ?rank"
                        using 5 vector_complement_closed vector_inf_comp inf_assoc by auto
                      also have "... = (?r \<sqinter> -?s \<sqinter> ?p4 \<sqinter> -1) * ?rank"
                          using 5 8 by (smt (z3) order.antisym bijective_regular point_in_vector_or_complement point_in_vector_or_complement_2 inf_absorb1)
                      also have "... = (?r \<sqinter> -?s \<sqinter> ?p2 \<sqinter> -1) * ?rank"
                        by (simp add: inf.left_commute inf.sup_monoid.add_commute inf_sup_distrib1 inf_assoc)
                      also have "... \<le> (?r \<sqinter> ?p2 \<sqinter> -1) * ?rank"
                        using inf.sup_left_isotone inf_le1 mult_left_isotone by blast
                      also have "... = bot"
                      proof -
                        have "?r = root ?p1 x"
                          using 2 path_compression_postcondition_def path_compression_precondition_def by blast
                        also have "... = root ?p2 x"
                          using 3 18 by (smt (z3) find_set_precondition_def path_compression_postcondition_def path_compression_precondition_def same_root)
                        also have "... \<le> roots ?p2"
                          by simp
                        finally have "?r \<sqinter> ?p2 \<le> roots ?p2 \<sqinter> ?p2"
                          using inf.sup_left_isotone by blast
                        also have "... \<le> (?p2 \<sqinter> 1) * (?p2 \<sqinter> 1)\<^sup>T * ?p2"
                          by (smt (z3) comp_associative comp_inf.star_plus dedekind_1 inf_top_right order_lesseq_imp)
                        also have "... = (?p2 \<sqinter> 1) * (?p2 \<sqinter> 1) * ?p2"
                          using coreflexive_symmetric by force
                        also have "... \<le> (?p2 \<sqinter> 1) * ?p2"
                          by (metis coreflexive_comp_top_inf inf.cobounded2 mult_left_isotone)
                        also have "... \<le> ?p2 \<sqinter> 1"
                          by (smt 23 comp_inf.mult_semi_associative conv_dist_comp conv_dist_inf conv_order equivalence_one_closed inf.absorb1 inf.sup_monoid.add_assoc injective_codomain)
                        also have "... \<le> 1"
                          by simp
                        finally have "?r \<sqinter> ?p2 \<le> 1"
                          .
                        thus ?thesis
                          by (metis pseudo_complement regular_one_closed semiring.mult_not_zero)
                      qed
                      finally show ?thesis
                        using bot_least le_bot by blast
                    qed
                    have 25: "-?r \<sqinter> (?p4 - 1) * ?rank \<le> rank * S'\<^sup>+"
                    proof -
                      have "-?r \<sqinter> (?p4 - 1) * ?rank = (-?r \<sqinter> ?p4 \<sqinter> -1) * ?rank"
                        using 5 vector_complement_closed vector_inf_comp inf_assoc by auto
                      also have "... = (-?r \<sqinter> (?s \<squnion> -?s) \<sqinter> ?p4 \<sqinter> -1) * ?rank"
                        using 5 bijective_regular inf_top_right regular_complement_top by auto
                      also have "... = (-?r \<sqinter> ?s \<sqinter> ?p4 \<sqinter> -1) * ?rank \<squnion> (-?r \<sqinter> -?s \<sqinter> ?p4 \<sqinter> -1) * ?rank"
                        by (smt (z3) inf_sup_distrib1 inf_sup_distrib2 mult_right_dist_sup)
                      also have "... = (-?r \<sqinter> ?s \<sqinter> ?r\<^sup>T \<sqinter> -1) * ?rank \<squnion> (-?r \<sqinter> -?s \<sqinter> ?p2 \<sqinter> -1) * ?rank"
                        using 5 by (smt (z3) bijective_regular comp_inf.comp_left_dist_sup inf_assoc inf_commute inf_top_right mult_right_dist_sup regular_complement_top)
                      also have "... \<le> (?s \<sqinter> ?r\<^sup>T \<sqinter> -1) * ?rank \<squnion> (-?s \<sqinter> ?p2 \<sqinter> -1) * ?rank"
                        by (smt (z3) comp_inf.semiring.distrib_left inf.cobounded2 inf.sup_monoid.add_assoc mult_left_isotone mult_right_dist_sup)
                      also have "... \<le> (?s \<sqinter> ?r\<^sup>T) * ?rank \<squnion> (?p2 - 1) * ?rank"
                        by (smt (z3) inf.cobounded1 inf.cobounded2 inf.sup_monoid.add_assoc mult_left_isotone semiring.add_mono)
                      also have "... = ?s * (?r \<sqinter> ?rank) \<squnion> (?p2 - 1) * ?rank"
                        using 5 by (simp add: covector_inf_comp_3)
                      also have "... = ?s * (?r \<sqinter> (S'\<^sup>T * ?rs)\<^sup>T) \<squnion> (?p2 - 1) * ?rank"
                        using inf_commute update_inf_same mult_assoc by force
                      also have "... = ?s * (?r \<sqinter> ?s\<^sup>T * rank * S') \<squnion> (?p2 - 1) * ?rank"
                        using comp_associative conv_dist_comp conv_involutive by auto
                      also have "... \<le> ?s * ?s\<^sup>T * rank * S' \<squnion> (?p2 - 1) * ?rank"
                        using comp_associative inf.cobounded2 mult_right_isotone semiring.add_right_mono by auto
                      also have "... \<le> 1 * rank * S' \<squnion> (?p2 - 1) * ?rank"
                        using 5 by (meson mult_left_isotone order.refl semiring.add_mono)
                      also have "... = rank * S' \<squnion> (?p2 - 1) * (?r \<sqinter> (S'\<^sup>T * ?rr)\<^sup>T) \<squnion> (?p2 - 1) * (-?r \<sqinter> rank)"
                        using 11 comp_associative mult_1_left mult_left_dist_sup sup_assoc by auto
                      also have "... \<le> rank * S' \<squnion> (?p2 - 1) * (?r \<sqinter> ?r\<^sup>T * rank * S') \<squnion> (?p2 - 1) * rank"
                        using comp_associative conv_dist_comp conv_involutive inf.cobounded1 inf.sup_monoid.add_commute mult_right_isotone semiring.add_left_mono by auto
                      also have "... = rank * S' \<squnion> (?p2 - 1) * (?r \<sqinter> ?r\<^sup>T) * rank * S' \<squnion> (?p2 - 1) * rank"
                        using 5 comp_associative vector_inf_comp by auto
                      also have "... \<le> rank * S' \<squnion> (?p2 - 1) * rank * S' \<squnion> (?p2 - 1) * rank"
                        using 5 by (metis point_antisymmetric mult_left_isotone mult_right_isotone sup_left_isotone sup_right_isotone comp_right_one)
                      also have "... \<le> rank * S' \<squnion> rank * S'\<^sup>+ * S' \<squnion> (?p2 - 1) * rank"
                        using 4 by (metis rank_property_def mult_left_isotone sup_left_isotone sup_right_isotone)
                      also have "... \<le> rank * S' \<squnion> rank * S'\<^sup>+ * S' \<squnion> rank * S'\<^sup>+"
                        using 4 by (metis rank_property_def sup_right_isotone)
                      also have "... \<le> rank * S'\<^sup>+"
                        using comp_associative eq_refl le_sup_iff mult_right_isotone star.circ_mult_increasing star.circ_plus_same star.left_plus_below_circ by auto
                      finally show ?thesis
                        .
                    qed
                    have "(?p4 - 1) * ?rank = (?r \<sqinter> (?p4 - 1) * ?rank) \<squnion> (-?r \<sqinter> (?p4 - 1) * ?rank)"
                      using 5 by (smt (verit, ccfv_threshold) bijective_regular inf_commute inf_sup_distrib2 inf_top_right regular_complement_top)
                    also have "... \<le> (?r \<sqinter> ?s\<^sup>T * rank * S' * S'\<^sup>+) \<squnion> (-?r \<sqinter> rank * S'\<^sup>+)"
                      using 24 25 by (meson inf.boundedI inf.cobounded1 semiring.add_mono)
                    also have "... = (?r \<sqinter> ?s\<^sup>T * rank * S') * S'\<^sup>+ \<squnion> (-?r \<sqinter> rank) * S'\<^sup>+"
                      using 5 vector_complement_closed vector_inf_comp by auto
                    also have "... = ?rank * S'\<^sup>+"
                      using conv_dist_comp mult_right_dist_sup by auto
                    finally show ?thesis
                      .
                  qed
                qed
              qed
            qed
            show "?rr \<noteq> ?rs \<longrightarrow> union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank"
            proof
              assume "?rr \<noteq> ?rs"
              hence "?rs \<sqinter> ?rr = bot"
                using 6 by (meson bijective_regular dual_order.eq_iff point_in_vector_or_complement point_in_vector_or_complement_2 pseudo_complement)
              hence 26: "?rs \<le> S'\<^sup>+ * ?rr"
                using 10 le_iff_inf pseudo_complement by auto
              show "union_sets_postcondition ?p4 x y p0 \<and> rank_property ?p4 rank"
              proof
                show "union_sets_postcondition ?p4 x y p0"
                  using 1 2 3 by (simp add: union_sets_1_swap)
                show "rank_property ?p4 rank"
                proof (unfold rank_property_def, intro conjI)
                  show "univalent rank" "total rank"
                    using 1 rank_property_def by auto
                  have "?r \<le> -?s"
                    using 5 8 by (meson order.antisym bijective_regular point_in_vector_or_complement point_in_vector_or_complement_2)
                  hence "?s \<sqinter> ?r\<^sup>T \<sqinter> 1 = bot"
                    by (metis (full_types) bot_least inf.left_commute inf.sup_monoid.add_commute one_inf_conv pseudo_complement)
                  hence "?p4 \<sqinter> 1 \<le> ?p2"
                    by (smt half_shunting inf.cobounded2 pseudo_complement regular_one_closed semiring.add_mono sup_commute)
                  hence "roots ?p4 \<le> roots ?p2"
                    by (simp add: mult_left_isotone)
                  thus "card_less_eq (roots ?p4) (-(S'\<^sup>+ * rank\<^sup>T * top))"
                    using 4 by (meson rank_property_def card_less_eq_def order_trans)
                  have "(?p4 - 1) * rank = (?s \<sqinter> ?r\<^sup>T \<sqinter> -1) * rank \<squnion> (-?s \<sqinter> ?p2 \<sqinter> -1) * rank"
                    using comp_inf.semiring.distrib_right mult_right_dist_sup by auto
                  also have "... \<le> (?s \<sqinter> ?r\<^sup>T \<sqinter> -1) * rank \<squnion> (?p2 - 1) * rank"
                    using comp_inf.mult_semi_associative mult_left_isotone sup_right_isotone by auto
                  also have "... \<le> (?s \<sqinter> ?r\<^sup>T \<sqinter> -1) * rank \<squnion> rank * S'\<^sup>+"
                    using 4 sup_right_isotone rank_property_def by blast
                  also have "... \<le> (?s \<sqinter> ?r\<^sup>T) * rank \<squnion> rank * S'\<^sup>+"
                    using inf_le1 mult_left_isotone sup_left_isotone by blast
                  also have "... = ?s * ?r\<^sup>T * rank \<squnion> rank * S'\<^sup>+"
                    using 5 by (simp add: vector_covector)
                  also have "... = rank * S'\<^sup>+"
                  proof -
                    have "rank\<^sup>T * ?s \<le> S'\<^sup>+ * rank\<^sup>T * ?r"
                      using 26 comp_associative by auto
                    hence "?s \<le> rank * S'\<^sup>+ * rank\<^sup>T * ?r"
                      using 4 shunt_mapping comp_associative rank_property_def by auto
                    hence "?s * ?r\<^sup>T \<le> rank * S'\<^sup>+ * rank\<^sup>T"
                      using 5 shunt_bijective by blast
                    hence "?s * ?r\<^sup>T * rank \<le> rank * S'\<^sup>+"
                      using 4 shunt_bijective rank_property_def mapping_conv_bijective by auto
                    thus ?thesis
                      using sup_absorb2 by blast
                  qed
                  finally show "(?p4 - 1) * rank \<le> rank * S'\<^sup>+"
                    .
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    show "?r = ?s \<longrightarrow> union_sets_postcondition ?p5 x y p0 \<and> rank_property ?p5 rank"
    proof
      assume 27: "?r = ?s"
      show "union_sets_postcondition ?p5 x y p0 \<and> rank_property ?p5 rank"
      proof
        show "union_sets_postcondition ?p5 x y p0"
          using 1 2 3 27 by (simp add: union_sets_1_skip)
        show "rank_property ?p5 rank"
          using 4 27 by simp
      qed
    qed
  qed
qed

end

end

