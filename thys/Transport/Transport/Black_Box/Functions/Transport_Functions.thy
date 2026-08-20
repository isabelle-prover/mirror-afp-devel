\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Transport_Functions
  imports
    Transport_Functions_Galois_Equivalence
    Transport_Functions_Galois_Relator
    Transport_Functions_Order_Base
    Transport_Functions_Order_Equivalence
    Transport_Functions_Relation_Simplifications
begin

paragraph \<open>Summary\<close>
text \<open>Composition under (dependent) (monotone) function relators.
Refer to \<^cite>\<open>"transport"\<close> for more details.\<close>

subsection \<open>Summary of Main Results\<close>

text \<open>More precise results can be found in the corresponding subtheories.\<close>

paragraph \<open>Monotone Dependent Function Relator\<close>

context transport_Mono_Dep_Fun_Rel
begin

interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

subparagraph \<open>Closure of Order and Galois Concepts\<close>

theorem preorder_galois_connection_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)"
  and "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<stileturn> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2\<^bsub>x' x\<^esub> r2\<^bsub>x x'\<^esub>"
  and "((_ x2 \<Colon> (\<le>\<^bsub>L1\<^esub>)) \<Rightarrow> \<lparr>x3 x4 \<Colon> (\<le>\<^bsub>L1\<^esub>) | x2 \<le>\<^bsub>L1\<^esub> x3 \<and> x4 \<le>\<^bsub>L1\<^esub> \<eta>\<^sub>1 x3\<rparr> \<Rrightarrow> (\<ge>)) L2"
  and "((x1' x2' \<Colon> (\<le>\<^bsub>R1\<^esub>) | \<epsilon>\<^sub>1 x2' \<le>\<^bsub>R1\<^esub> x1') \<Rightarrow> \<lparr>x3' _ \<Colon> (\<le>\<^bsub>R1\<^esub>) | x2' \<le>\<^bsub>R1\<^esub> x3'\<rparr> \<Rrightarrow> (\<le>)) R2"
  and tdfr.mono_conds_fun
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2 x1 x2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2 x1' x2'\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_galois_connectionI
    galois_connection_left_right_if_mono_if_galois_connectionI'
    preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
    tdfr.transitive_leftI' flip.tdfr.transitive_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on
      in_field_if_in_dom in_field_if_in_codom)

theorem preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2\<^bsub>x' x\<^esub> r2\<^bsub>x x'\<^esub>"
  and tdfr.mono_conds
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_equivalence_if_galois_equivalenceI
    galois_equivalence_if_mono_if_preorder_equivalenceI'
    preorder_on_in_field_leftI flip.preorder_on_in_field_leftI
    tdfr.transitive_leftI' flip.tdfr.transitive_leftI
    tdfr.transitive_left2_if_preorder_equivalenceI
    tdfr.transitive_right2_if_preorder_equivalenceI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_leftI
    tdfr.left_rel_right_iff_left_right_rel_if_galois_prop_le_assms_rightI
    tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
    flip.tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI)
  (auto 4 4 intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom in_field_if_in_codom)

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2\<^bsub>x' x\<^esub> r2\<^bsub>x x'\<^esub>"
  and tdfr.mono_conds
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms
  by (intro partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalence_if_mono_if_preorder_equivalenceI'
    tdfr.transitive_left2_if_preorder_equivalenceI
    tdfr.transitive_right2_if_preorder_equivalenceI
    partial_equivalence_rel_leftI flip.partial_equivalence_rel_leftI
    tdfr.partial_equivalence_rel_left2_if_partial_equivalence_rel_equivalenceI
    tdfr.partial_equivalence_rel_right2_if_partial_equivalence_rel_equivalenceI)
  (auto 4 4 elim!: tdfr.mono_condsE tdfr.mono_conds_relE)

subparagraph \<open>Simplification of Left and Right Relations\<close>

text \<open>See @{thm "left_rel_eq_tdfr_leftI_if_equivalencesI"}.\<close>


subparagraph \<open>Simplification of Galois relator\<close>

text \<open>See
@{thm "left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_mono_if_galois_connectionI"
"left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_preorder_equivalenceI"
"left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_preorder_equivalenceI'"
"Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI"
"Dep_Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq"}\<close>

end


paragraph \<open>Monotone Function Relator\<close>

context transport_Mono_Fun_Rel
begin

interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

subparagraph \<open>Closure of Order and Galois Concepts\<close>

lemma preorder_galois_connection_if_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_codom (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)" "reflexive_on (in_dom (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<stileturn> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tmdfr.preorder_galois_connectionI
    galois_connection_left_rightI
    tmdfr.preorder_on_in_field_leftI flip.tmdfr.preorder_on_in_field_leftI
    tfr.transitive_leftI' flip.tfr.transitive_leftI)
  auto

theorem preorder_galois_connectionI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<stileturn>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_galois_connection_if_galois_connectionI)
  (auto 6 0 intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom in_field_if_in_codom
    dest!: tdfrs.t1.left_Galois_left_if_left_relI tdfrs.t1.right_left_Galois_if_right_relI)

theorem preorder_equivalence_if_galois_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "reflexive_on (in_field (\<le>\<^bsub>L1\<^esub>)) (\<le>\<^bsub>L1\<^esub>)" "reflexive_on (in_field (\<le>\<^bsub>R1\<^esub>)) (\<le>\<^bsub>R1\<^esub>)"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^sub>G (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  and "\<And>x1 x2. x1 \<le>\<^bsub>L1\<^esub> x2 \<Longrightarrow> transitive (\<le>\<^bsub>L2\<^esub>)"
  and "\<And>x1' x2'. x1' \<le>\<^bsub>R1\<^esub> x2' \<Longrightarrow> transitive (\<le>\<^bsub>R2\<^esub>)"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tmdfr.preorder_equivalence_if_galois_equivalenceI
    galois_equivalenceI
    tmdfr.preorder_on_in_field_leftI flip.tmdfr.preorder_on_in_field_leftI
    tfr.transitive_leftI flip.tfr.transitive_leftI)
  (auto intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom)

theorem preorder_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>pre\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro preorder_equivalence_if_galois_equivalenceI)
  (auto 8 0 dest!: tdfrs.t1.left_Galois_left_if_left_relI tdfrs.t1.right_left_Galois_if_right_relI)

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and per2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
  using assms by (intro tmdfr.partial_equivalence_rel_equivalence_if_galois_equivalenceI
    galois_equivalenceI
    partial_equivalence_rel_leftI flip.partial_equivalence_rel_leftI)
  (auto 8 0 dest!: per2 tdfrs.t1.left_Galois_left_if_left_relI
    tdfrs.t1.right_left_Galois_if_right_relI)


subparagraph \<open>Simplification of Left and Right Relations\<close>

text \<open>See @{thm "left_rel_eq_tfr_leftI"}.\<close>


subparagraph \<open>Simplification of Galois relator\<close>

text \<open>See @{thm "left_Galois_eq_Fun_Rel_left_Galois_restrictI"
"Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI"
"Fun_Rel_left_Galois_restrict_left_right_restrict_left_right_eq"}.\<close>

end


paragraph \<open>Dependent Function Relator\<close>

text \<open>While a general transport of functions is only possible for the monotone
function relator (see above), the locales @{locale "transport_Dep_Fun_Rel"} and
@{locale "transport_Fun_Rel"} contain special cases to transport functions
that are proven to be monotone using the standard function space.

Moreover, in the special case of equivalences on partial equivalence relations,
the standard function space is monotone - see
@{thm "transport_Mono_Dep_Fun_Rel.left_rel_eq_tdfr_leftI_if_equivalencesI"}
As such, we can derive general transport theorems from the monotone cases
above.\<close>

context transport_Dep_Fun_Rel
begin

interpretation tmdfr : transport_Mono_Dep_Fun_Rel L1 R1 l1 r1 L2 R2 l2 r2 .
interpretation flip : transport_Mono_Dep_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2
  rewrites "flip.t1.counit \<equiv> \<eta>\<^sub>1" and "flip.t1.unit \<equiv> \<epsilon>\<^sub>1"
  by (simp_all only: t1.flip_counit_eq_unit t1.flip_unit_eq_counit)

theorem partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2\<^bsub>x' x\<^esub> r2\<^bsub>x x'\<^esub>"
  and mono_conds
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  from assms have "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) = (tmdfr.L \<equiv>\<^bsub>PER\<^esub> tmdfr.R)"
    by (subst tmdfr.left_rel_eq_tdfr_leftI_if_equivalencesI
        flip.left_rel_eq_tdfr_leftI_if_equivalencesI,
      auto 0 4 intro!: partial_equivalence_rel_left2_if_partial_equivalence_rel_equivalenceI
        partial_equivalence_rel_right2_if_partial_equivalence_rel_equivalenceI
      iff: t1.galois_equivalence_right_left_iff_galois_equivalence_left_right)+
  with assms show ?thesis
    by (auto intro!: tmdfr.partial_equivalence_rel_equivalenceI)
qed

theorem left_Galois_eq_Dep_Fun_Rel_left_Galois_if_partial_equivalence_rel_equivalenceI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2 x (r1 x')\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2 (l1 x) x'\<^esub>)) l2\<^bsub>x' x\<^esub> r2\<^bsub>x x'\<^esub>"
  and mono_conds
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)) \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
proof -
  from assms have rel_eqs: "(\<le>\<^bsub>L\<^esub>) = tmdfr.L" "(\<le>\<^bsub>R\<^esub>) = tmdfr.R"
    by (subst tmdfr.left_rel_eq_tdfr_leftI_if_equivalencesI flip.left_rel_eq_tdfr_leftI_if_equivalencesI,
      auto 0 4 intro!: partial_equivalence_rel_left2_if_partial_equivalence_rel_equivalenceI
        partial_equivalence_rel_right2_if_partial_equivalence_rel_equivalenceI
      iff: t1.galois_equivalence_right_left_iff_galois_equivalence_left_right)+
  then have "(\<^bsub>L\<^esub>\<lessapprox>) = tmdfr.Galois" by simp
  also with assms have "... = ((x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)) \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom tmdfr.L\<^esub>\<upharpoonleft>\<^bsub>in_codom tmdfr.R\<^esub>"
    by (intro tmdfr.left_Galois_eq_Dep_Fun_Rel_left_Galois_restrict_if_preorder_equivalenceI
      transitive_left2_if_preorder_equivalenceI)
    (auto 6 2 intro!: partial_equivalence_rel_left2_if_partial_equivalence_rel_equivalenceI)
  also from rel_eqs have "... = ((x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)) \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>" by simp
  also with assms have "... = ((x x' \<Colon> (\<^bsub>L1\<^esub>\<lessapprox>)) \<Rrightarrow> (\<^bsub>L2 x x'\<^esub>\<lessapprox>))"
    by (intro Dep_Fun_Rel_left_Galois_restrict_left_right_eq_Dep_Fun_Rel_left_GaloisI'
      transitive_left2_if_preorder_equivalenceI transitive_right2_if_preorder_equivalenceI
      galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI
      flip.tdfr.galois_equivalence_if_mono_if_galois_equivalence_mono_assms_leftI)
    (auto 4 4 iff: t1.galois_equivalence_right_left_iff_galois_equivalence_left_right, fast?)
  finally show ?thesis .
qed

end

paragraph \<open>Function Relator\<close>

context transport_Fun_Rel
begin

interpretation tmfr : transport_Mono_Fun_Rel L1 R1 l1 r1 L2 R2 l2 r2 .
interpretation flip : transport_Mono_Fun_Rel R1 L1 r1 l1 R2 L2 r2 l2 .

theorem partial_equivalence_rel_equivalenceI:
  assumes per1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and per2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) l r"
proof -
  have "((\<le>\<^bsub>L\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R\<^esub>)) = (tmfr.tmdfr.L \<equiv>\<^bsub>PER\<^esub> tmfr.tmdfr.R)" using per1
    by (subst tmfr.left_rel_eq_tfr_leftI flip.left_rel_eq_tfr_leftI;
      auto 8 0 dest!: per2 tdfrs.t1.left_Galois_left_if_left_relI
        tdfrs.t1.right_left_Galois_if_right_relI)+
  with assms show ?thesis by (auto intro!: tmfr.partial_equivalence_rel_equivalenceI)
qed

theorem left_Galois_eq_Fun_Rel_left_Galois_if_partial_equivalence_rel_equivalenceI:
  assumes per1: "((\<le>\<^bsub>L1\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R1\<^esub>)) l1 r1"
  and per2: "\<And>x x'. x \<^bsub>L1\<^esub>\<lessapprox> x' \<Longrightarrow> ((\<le>\<^bsub>L2\<^esub>) \<equiv>\<^bsub>PER\<^esub> (\<le>\<^bsub>R2\<^esub>)) l2 r2"
  shows "(\<^bsub>L\<^esub>\<lessapprox>) = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
proof -
  have rel_eqs: "(\<le>\<^bsub>L\<^esub>) = tmfr.tmdfr.L" "(\<le>\<^bsub>R\<^esub>) = tmfr.tmdfr.R" using per1
    by (subst tmfr.left_rel_eq_tfr_leftI flip.left_rel_eq_tfr_leftI;
      auto 8 0 dest!: per2 tdfrs.t1.left_Galois_left_if_left_relI
        tdfrs.t1.right_left_Galois_if_right_relI)+
  then have "(\<^bsub>L\<^esub>\<lessapprox>) = tmfr.tmdfr.Galois" by simp
  also with assms have "... = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom tmfr.tmdfr.L\<^esub>\<upharpoonleft>\<^bsub>in_codom tmfr.tmdfr.R\<^esub>"
    by (intro tmfr.left_Galois_eq_Fun_Rel_left_Galois_restrictI)
      (auto 8 0 intro: reflexive_on_if_le_pred_if_reflexive_on in_field_if_in_dom
        dest!: per2 tdfrs.t1.left_Galois_left_if_left_relI tdfrs.t1.right_left_Galois_if_right_relI)
  also from rel_eqs have "... = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))\<restriction>\<^bsub>in_dom (\<le>\<^bsub>L\<^esub>)\<^esub>\<upharpoonleft>\<^bsub>in_codom (\<le>\<^bsub>R\<^esub>)\<^esub>" by simp
  also with assms have "... = ((\<^bsub>L1\<^esub>\<lessapprox>) \<Rrightarrow> (\<^bsub>L2\<^esub>\<lessapprox>))"
    by (intro Fun_Rel_left_Galois_restrict_left_right_eq_Fun_Rel_left_GaloisI) fastforce+
  finally show ?thesis .
qed

end


end