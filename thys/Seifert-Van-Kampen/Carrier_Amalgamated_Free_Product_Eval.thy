theory Carrier_Amalgamated_Free_Product_Eval
  imports Carrier_Amalgamated_Free_Product Carrier_Group_Scaffold
begin

section \<open>Evaluating carrier amalgamated free-product words\<close>

text \<open>
  Once the carrier-side amalgamated words have been defined, one still needs a
  way to evaluate them in a target carrier group. The evaluation locale proved
  here is the algebraic engine behind the later decoding maps in both the
  topological and classical Seifert--van Kampen statements.
\<close>

locale carrier_full_amalg_word_eval =
  Grp1: carrier_group G1 mult1 one1 inv1 +
  Grp2: carrier_group G2 mult2 one2 inv2 +
  Cod: carrier_group K multK oneK invK +
  J1: carrier_group_hom G1 mult1 one1 inv1 K multK oneK invK j1 +
  J2: carrier_group_hom G2 mult2 one2 inv2 K multK oneK invK j2
  for G1 :: "'a set"
    and mult1 :: "'a => 'a => 'a"
    and one1 :: "'a"
    and inv1 :: "'a => 'a"
    and G2 :: "'b set"
    and mult2 :: "'b => 'b => 'b"
    and one2 :: "'b"
    and inv2 :: "'b => 'b"
    and H :: "'h set"
    and i1 :: "'h => 'a"
    and i2 :: "'h => 'b"
    and K :: "'k set"
    and multK :: "'k => 'k => 'k"
    and oneK :: "'k"
    and invK :: "'k => 'k"
    and j1 :: "'a => 'k"
    and j2 :: "'b => 'k" +
  assumes i1_closed: "h \<in> H \<Longrightarrow> i1 h \<in> G1"
    and i2_closed: "h \<in> H \<Longrightarrow> i2 h \<in> G2"
    and agree: "h \<in> H \<Longrightarrow> j1 (i1 h) = j2 (i2 h)"
begin

fun carrier_full_amalg_eval :: "('a, 'b) free_product_word => 'k" where
  "carrier_full_amalg_eval WordNil = oneK"
| "carrier_full_amalg_eval (WordLeft a rest) =
    multK (j1 a) (carrier_full_amalg_eval rest)"
| "carrier_full_amalg_eval (WordRight b rest) =
    multK (j2 b) (carrier_full_amalg_eval rest)"

lemma carrier_full_amalg_eval_in_carrier:
  assumes "fpw_in_space G1 G2 w"
  shows "carrier_full_amalg_eval w \<in> K"
  using assms
proof (induction w)
  case WordNil
  then show ?case
    by simp
next
  case (WordLeft a rest)
  then have a_in: "a \<in> G1" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule WordLeft.IH[OF rest_in])
  then show ?case
    using a_in eval_rest_in by (simp add: Cod.mult_closed J1.map_closed)
next
  case (WordRight b rest)
  then have b_in: "b \<in> G2" and rest_in: "fpw_in_space G1 G2 rest"
    by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule WordRight.IH[OF rest_in])
  then show ?case
    using b_in eval_rest_in by (simp add: Cod.mult_closed J2.map_closed)
qed

lemma carrier_amalgam_step_preserves_space_iff:
  assumes step: "carrier_amalgam_step H i1 i2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
  using step
proof cases
  case (identify h rest)
  then show ?thesis
    using i1_closed[OF \<open>h \<in> H\<close>] i2_closed[OF \<open>h \<in> H\<close>] by simp
qed

lemma carrier_amalgam_equiv_preserves_space_iff:
  assumes rel: "carrier_amalgam_equiv H i1 i2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
  using rel
proof (induction rule: carrier_amalgam_equiv.induct)
  case (refl w)
  then show ?case
    by simp
next
  case (sym u v)
  then show ?case
    by simp
next
  case (trans u v w)
  then show ?case
    by blast
next
  case (step u v)
  then show ?case
    by (rule carrier_amalgam_step_preserves_space_iff)
next
  case (left_context u v a)
  then show ?case
    by simp
next
  case (right_context u v b)
  then show ?case
    by simp
qed

lemma carrier_amalgam_step_preserves_eval:
  assumes step: "carrier_amalgam_step H i1 i2 u v"
  shows "carrier_full_amalg_eval u = carrier_full_amalg_eval v"
  using step
proof cases
  case (identify h rest)
  then show ?thesis
    using agree[OF \<open>h \<in> H\<close>]
    by (simp add: J1.map_closed J2.map_closed)
qed

lemma carrier_amalgam_equiv_preserves_eval:
  assumes rel: "carrier_amalgam_equiv H i1 i2 u v"
  shows "carrier_full_amalg_eval u = carrier_full_amalg_eval v"
  using rel
proof (induction rule: carrier_amalgam_equiv.induct)
  case (refl w)
  then show ?case
    by simp
next
  case (sym u v)
  then show ?case
    by simp
next
  case (trans u v w)
  then show ?case
    by simp
next
  case (step u v)
  then show ?case
    by (rule carrier_amalgam_step_preserves_eval)
next
  case (left_context u v a)
  then show ?case
    by auto
next
  case (right_context u v b)
  then show ?case
    by auto
qed

lemma carrier_fpw_reduction_step_preserves_eval:
  assumes step: "carrier_fpw_reduction_step G1 G2 mult1 one1 mult2 one2 u v"
  shows "carrier_full_amalg_eval u = carrier_full_amalg_eval v"
  using step
proof (induction rule: carrier_fpw_reduction_step.induct)
  case (combine_left a b rest)
  have a_in: "a \<in> G1" and b_in: "b \<in> G1" and rest_in: "fpw_in_space G1 G2 rest"
    using combine_left by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule carrier_full_amalg_eval_in_carrier[OF rest_in])
  have ja_in: "j1 a \<in> K"
    by (rule J1.map_closed[OF a_in])
  have jb_in: "j1 b \<in> K"
    by (rule J1.map_closed[OF b_in])
  show ?case
    using a_in b_in eval_rest_in ja_in jb_in
    by (simp add: J1.map_mult Cod.mult_assoc[symmetric])
next
  case (combine_right a b rest)
  have a_in: "a \<in> G2" and b_in: "b \<in> G2" and rest_in: "fpw_in_space G1 G2 rest"
    using combine_right by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule carrier_full_amalg_eval_in_carrier[OF rest_in])
  have ja_in: "j2 a \<in> K"
    by (rule J2.map_closed[OF a_in])
  have jb_in: "j2 b \<in> K"
    by (rule J2.map_closed[OF b_in])
  show ?case
    using a_in b_in eval_rest_in ja_in jb_in
    by (simp add: J2.map_mult Cod.mult_assoc[symmetric])
next
  case (remove_left_one rest)
  have rest_in: "fpw_in_space G1 G2 rest"
    using remove_left_one by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule carrier_full_amalg_eval_in_carrier[OF rest_in])
  show ?case
    using eval_rest_in
    by (simp add: J1.map_one Cod.mult_one_left)
next
  case (remove_right_one rest)
  have rest_in: "fpw_in_space G1 G2 rest"
    using remove_right_one by auto
  have eval_rest_in: "carrier_full_amalg_eval rest \<in> K"
    by (rule carrier_full_amalg_eval_in_carrier[OF rest_in])
  show ?case
    using eval_rest_in
    by (simp add: J2.map_one Cod.mult_one_left)
next
  case (context_left a u v)
  then show ?case
    by simp
next
  case (context_right b u v)
  then show ?case
    by simp
qed

lemmas carrier_fpw_reduction_space_iff =
  Carrier_Amalgamated_Free_Product.carrier_fpw_reduction_preserves_space_iff

lemma carrier_fpw_reduction_preserves_space_iff:
  assumes rel: "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
proof -
  show ?thesis
    by (rule carrier_fpw_reduction_space_iff[OF rel])
qed

lemma carrier_fpw_reduction_preserves_eval:
  assumes rel: "carrier_fpw_reduction G1 G2 mult1 one1 mult2 one2 u v"
  shows "carrier_full_amalg_eval u = carrier_full_amalg_eval v"
  using rel
proof (induction rule: carrier_fpw_reduction.induct)
  case (refl w)
  then show ?case
    by simp
next
  case (sym u v)
  then show ?case
    by simp
next
  case (trans u v w)
  then show ?case
    by simp
next
  case (step u v)
  then show ?case
    by (rule carrier_fpw_reduction_step_preserves_eval)
qed

lemma carrier_full_amalg_equiv_preserves_space_iff:
  assumes rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "fpw_in_space G1 G2 u \<longleftrightarrow> fpw_in_space G1 G2 v"
  using rel
proof (induction rule: carrier_full_amalg_equiv.induct)
  case (refl w)
  then show ?case
    by simp
next
  case (sym u v)
  then show ?case
    by simp
next
  case (trans u v w)
  then show ?case
    by blast
next
  case (of_amalg u v)
  then show ?case
    by (rule carrier_amalgam_equiv_preserves_space_iff)
next
  case (of_reduction u v)
  then show ?case
    by (rule carrier_fpw_reduction_preserves_space_iff)
qed

lemma carrier_full_amalg_equiv_preserves_eval:
  assumes rel: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "carrier_full_amalg_eval u = carrier_full_amalg_eval v"
  using rel
proof (induction rule: carrier_full_amalg_equiv.induct)
  case (refl w)
  then show ?case
    by simp
next
  case (sym u v)
  then show ?case
    by simp
next
  case (trans u v w)
  then show ?case
    by simp
next
  case (of_amalg u v)
  then show ?case
    by (rule carrier_amalgam_equiv_preserves_eval)
next
  case (of_reduction u v)
  then show ?case
    by (rule carrier_fpw_reduction_preserves_eval)
qed

definition carrier_full_amalg_has_good_rep :: "('a, 'b) free_product_word => bool" where
  "carrier_full_amalg_has_good_rep w \<longleftrightarrow>
    (\<exists>v. carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 w v
      \<and> fpw_in_space G1 G2 v)"

definition carrier_full_amalg_some_good_rep ::
  "('a, 'b) free_product_word => ('a, 'b) free_product_word"
where
  "carrier_full_amalg_some_good_rep w =
    (SOME v. carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 w v
      \<and> fpw_in_space G1 G2 v)"

definition carrier_full_amalg_decode :: "('a, 'b) free_product_word => 'k" where
  "carrier_full_amalg_decode w =
    (if carrier_full_amalg_has_good_rep w
     then carrier_full_amalg_eval (carrier_full_amalg_some_good_rep w)
     else oneK)"

lemma carrier_full_amalg_has_good_repI:
  assumes "fpw_in_space G1 G2 w"
  shows "carrier_full_amalg_has_good_rep w"
  using assms unfolding carrier_full_amalg_has_good_rep_def by auto

lemma carrier_full_amalg_some_good_rep:
  assumes "carrier_full_amalg_has_good_rep w"
  shows "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      w (carrier_full_amalg_some_good_rep w)"
    and "fpw_in_space G1 G2 (carrier_full_amalg_some_good_rep w)"
proof - 
  from assms obtain v where
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 w v"
      and "fpw_in_space G1 G2 v"
    unfolding carrier_full_amalg_has_good_rep_def by blast
  then have ex:
      "\<exists>v. carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 w v
        \<and> fpw_in_space G1 G2 v"
    by blast
  then have
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
         w (carrier_full_amalg_some_good_rep w)
        \<and> fpw_in_space G1 G2 (carrier_full_amalg_some_good_rep w)"
    unfolding carrier_full_amalg_some_good_rep_def
    by (rule someI_ex)
  then show
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
         w (carrier_full_amalg_some_good_rep w)"
    and "fpw_in_space G1 G2 (carrier_full_amalg_some_good_rep w)"
    by auto
qed

lemma carrier_full_amalg_has_good_rep_respects:
  assumes uv: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "carrier_full_amalg_has_good_rep u \<longleftrightarrow> carrier_full_amalg_has_good_rep v"
proof
  assume "carrier_full_amalg_has_good_rep u"
  then obtain w where
      uw: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u w"
      and w_in: "fpw_in_space G1 G2 w"
    unfolding carrier_full_amalg_has_good_rep_def by blast
  have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 v w"
    using uv uw
    by (meson carrier_full_amalg_equiv.sym carrier_full_amalg_equiv.trans)
  then show "carrier_full_amalg_has_good_rep v"
    using w_in unfolding carrier_full_amalg_has_good_rep_def by blast
next
  assume "carrier_full_amalg_has_good_rep v"
  then obtain w where
      vw: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 v w"
      and w_in: "fpw_in_space G1 G2 w"
    unfolding carrier_full_amalg_has_good_rep_def by blast
  have "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u w"
    using uv vw
    by (meson carrier_full_amalg_equiv.trans)
  then show "carrier_full_amalg_has_good_rep u"
    using w_in unfolding carrier_full_amalg_has_good_rep_def by blast
qed

lemma carrier_full_amalg_decode_in_carrier:
  "carrier_full_amalg_decode w \<in> K"
proof (cases "carrier_full_amalg_has_good_rep w")
  case True
  then have good_rep:
      "fpw_in_space G1 G2 (carrier_full_amalg_some_good_rep w)"
    by (rule carrier_full_amalg_some_good_rep)
  show ?thesis
    unfolding carrier_full_amalg_decode_def
    using True carrier_full_amalg_eval_in_carrier[OF good_rep] by simp
next
  case False
  then show ?thesis
    unfolding carrier_full_amalg_decode_def by simp
qed

lemma carrier_full_amalg_decode_respects:
  assumes uv: "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2 u v"
  shows "carrier_full_amalg_decode u = carrier_full_amalg_decode v"
proof (cases "carrier_full_amalg_has_good_rep u")
  case False
  then have "\<not> carrier_full_amalg_has_good_rep v"
    using carrier_full_amalg_has_good_rep_respects[OF uv] by blast
  then show ?thesis
    unfolding carrier_full_amalg_decode_def using False by simp
next
  case True
  then have v_has: "carrier_full_amalg_has_good_rep v"
    using carrier_full_amalg_has_good_rep_respects[OF uv] by blast
  have u_rep_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
         u (carrier_full_amalg_some_good_rep u)"
    using True by (rule carrier_full_amalg_some_good_rep)+
  have v_rep_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
         v (carrier_full_amalg_some_good_rep v)"
    using v_has by (rule carrier_full_amalg_some_good_rep)+
  have rep_eq:
    "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
      (carrier_full_amalg_some_good_rep u)
      (carrier_full_amalg_some_good_rep v)"
    using u_rep_rel v_rep_rel uv
    by (meson carrier_full_amalg_equiv.sym carrier_full_amalg_equiv.trans)
  have eval_eq:
    "carrier_full_amalg_eval (carrier_full_amalg_some_good_rep u) =
      carrier_full_amalg_eval (carrier_full_amalg_some_good_rep v)"
    by (rule carrier_full_amalg_equiv_preserves_eval[OF rep_eq])
  show ?thesis
    unfolding carrier_full_amalg_decode_def
    using True v_has eval_eq by simp
qed

lemma carrier_full_amalg_decode_eq_eval:
  assumes w_in: "fpw_in_space G1 G2 w"
  shows "carrier_full_amalg_decode w = carrier_full_amalg_eval w"
proof -
  have has: "carrier_full_amalg_has_good_rep w"
    by (rule carrier_full_amalg_has_good_repI[OF w_in])
  have rep_rel:
      "carrier_full_amalg_equiv G1 G2 H i1 i2 mult1 one1 mult2 one2
         w (carrier_full_amalg_some_good_rep w)"
    using has by (rule carrier_full_amalg_some_good_rep)+
  have eval_eq:
    "carrier_full_amalg_eval w =
      carrier_full_amalg_eval (carrier_full_amalg_some_good_rep w)"
    by (rule carrier_full_amalg_equiv_preserves_eval[OF rep_rel])
  show ?thesis
    unfolding carrier_full_amalg_decode_def
    using has eval_eq by simp
qed

end

end
