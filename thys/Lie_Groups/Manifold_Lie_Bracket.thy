(*  Title:       Manifold_Lie_Bracket
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

section \<open>The Lie bracket of smooth vector fields\<close>
theory Manifold_Lie_Bracket
imports
  Smooth_Vector_Fields
  Algebra_On
begin

definition lie_bracket_of_smooth_vector_fields :: "'a vector_field \<Rightarrow> 'a vector_field \<Rightarrow> 'a vector_field"
  where "lie_bracket_of_smooth_vector_fields X Y \<equiv> \<lambda>p::'a. \<lambda>f::'a\<Rightarrow>real. X p (Y \<hungarumlaut> f) - Y p (X \<hungarumlaut> f)"

notation lie_bracket_of_smooth_vector_fields (\<open>[_;_]\<close> [65,65])

lemma lie_bracket_def: "[X;Y] p f = X p (Y\<hungarumlaut>f) - Y p (X\<hungarumlaut>f)"
  unfolding lie_bracket_of_smooth_vector_fields_def by simp

context c_manifold begin

subsection \<open>General lemmas\<close>

lemma is_derivation_uminus: "is_derivation (-x) p" if x: "is_derivation x p"
  using is_derivation_scaleR[OF x, of "-1"] by simp

lemma is_derivation_minus: "is_derivation (x - y) p"
  if x: "is_derivation x p" and y: "is_derivation y p"
  using is_derivation_add[OF x is_derivation_uminus[OF y]] by simp

lemma diff_fun_space_minus: "f - g \<in> diff_fun_space"
  if "f \<in> diff_fun_space" "g \<in> diff_fun_space"
  by (simp add: diff_fun_space.m1.subspace_UNIV diff_fun_space.m1.subspace_diff that(1) that(2))

lemma rough_vector_field_add:
  assumes "rough_vector_field X" "rough_vector_field Y"
  shows "rough_vector_field (X+Y)"
  using assms rough_vector_field_def tangent_space.mem_add by force

abbreviation (input) "scaleR_vf \<equiv> scaleR :: real \<Rightarrow> 'a vector_field \<Rightarrow> 'a vector_field"

lemma scaleR_vf: "scaleR_vf = (\<lambda>r X p f. r * X p f)" by fastforce

lemma rough_vector_field_scaleR:
  assumes "rough_vector_field X"
  shows "rough_vector_field (scaleR_vf a X)"
  using assms tangent_space.mem_scale by (simp add: rough_vector_field_def)



subsection \<open>Properties of the Lie bracket on \<^term>\<open>\<XX>\<close>\<close>

lemma lie_bracket_antisym: "[X;Y] = -[Y;X]"
  unfolding lie_bracket_def by fastforce


lemma ext0_lie_bracket:
  shows "extensional0 carrier X \<Longrightarrow> extensional0 carrier Y \<Longrightarrow> extensional0 carrier [X;Y]"
    and "rough_vector_field X \<Longrightarrow> rough_vector_field Y \<Longrightarrow> extensional0 diff_fun_space (vec_field_apply_fun [X;Y])"
proof -
  show "extensional0 carrier X \<Longrightarrow> extensional0 carrier Y \<Longrightarrow> extensional0 carrier [X;Y]"
    unfolding lie_bracket_def extensional0_def by auto
  assume asm: "rough_vector_field X" "rough_vector_field Y"
  then show "extensional0 diff_fun_space (vec_field_apply_fun [X;Y])"
  proof - \<comment> \<open>This proof was fiddly to get into a form where methods would not time out.\<close>
  (* TODO is this due to the abbreviation vec_field_apply_fun? Preferences? *)
    note vf_0 = linear_on.linear_0[OF linear_on_vec_field]
    have "\<forall>p. (X \<hungarumlaut> 0) p - (Y \<hungarumlaut> 0) p = 0"
      using vf_0[OF asm(1)] vf_0[OF asm(2)] by (metis diff_0_right zero_fun_apply)
    then have 0: "(\<lambda>p. (X \<hungarumlaut> 0) p - (Y \<hungarumlaut> 0) p) = 0" by auto
    thus ?thesis
      using ext0_vec_field_apply_fun asm unfolding lie_bracket_def extensional0_def by presburger
  qed
qed

end


context smooth_manifold begin

text \<open>A nice computational proof that I try to keep close-ish to Lee's
  original pen-and-paper \cite[p.~186]{lee_2012}.\<close>
lemma product_rule_lie_bracket:
  assumes X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
    and diff_funs: "f\<in>diff_fun_space" "g\<in>diff_fun_space"
  shows "[X;Y] \<hungarumlaut> (f * g) = f * [X;Y] \<hungarumlaut> g + g * [X;Y] \<hungarumlaut> f"
proof -
  have rough_vf[simp]: "rough_vector_field X" "rough_vector_field Y"
    using smooth_vector_field_def assms by auto
  interpret linear_X: linear_on diff_fun_space diff_fun_space scaleR scaleR "vec_field_apply_fun X"
    using linear_on_vec_field[OF rough_vf(1)] .
  interpret linear_Y: linear_on diff_fun_space diff_fun_space scaleR scaleR "vec_field_apply_fun Y"
    using linear_on_vec_field[OF rough_vf(2)] .

  note [simp] = diff_funs diff_fun_space.m1.mem_add diff_fun_space_times
  have local_simps [simp]:
    "\<And>f. f\<in>diff_fun_space \<Longrightarrow> X \<hungarumlaut> f \<in> diff_fun_space"
    "\<And>f. f\<in>diff_fun_space \<Longrightarrow> Y \<hungarumlaut> f \<in> diff_fun_space"
      using X Y by (simp_all add: vector_field_smooth_iff(1))

  have "([X;Y] \<hungarumlaut> (f*g)) = X \<hungarumlaut> (Y\<hungarumlaut>(f*g)) - Y \<hungarumlaut> (X\<hungarumlaut>(f*g))"
    unfolding lie_bracket_def by (simp add: fun_diff_def)
  also have "\<dots> = X \<hungarumlaut> (f*Y\<hungarumlaut>g + g*Y\<hungarumlaut>f) - Y \<hungarumlaut> (f*X\<hungarumlaut>g + g*X\<hungarumlaut>f)"
    using rough_vf diff_funs product_rule_vf by presburger
  also have "\<dots> = X \<hungarumlaut> (f*Y\<hungarumlaut>g) + X \<hungarumlaut> (g*Y\<hungarumlaut>f) - Y \<hungarumlaut> (f*X\<hungarumlaut>g) - Y \<hungarumlaut> (g*X\<hungarumlaut>f)"
    \<comment> \<open>Extra step to invoke linearity of both \<^term>\<open>X\<close> and \<^term>\<open>Y\<close>.\<close>
    using linear_X.add linear_Y.add by simp
  also have "\<dots> = (f * X\<hungarumlaut>(Y\<hungarumlaut>g)) + (g * X\<hungarumlaut>(Y\<hungarumlaut>f)) - (f * Y\<hungarumlaut>(X\<hungarumlaut>g)) - (g * Y\<hungarumlaut>(X\<hungarumlaut>f))"
    \<comment> \<open>No separate step for term cancellation.\<close>
    using product_rule_vf by auto
  finally show ?thesis
    by (simp add: lie_bracket_def fun_diff_def add_diff_eq diff_add_eq plus_fun_def
        vector_space_over_itself.scale_right_diff_distrib)
qed


lemma lie_bracket_is_derivation_on:
  assumes X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
  shows "is_derivation_on (\<lambda>f. [X;Y] \<hungarumlaut> f)"
proof (unfold is_derivation_on_def, safe)
  have 0: "(\<lambda>p. Y p (\<lambda>p. X p f)) \<in> diff_fun_space" "(\<lambda>p. X p (\<lambda>p. Y p f)) \<in> diff_fun_space"
      if f: "f \<in> diff_fun_space" for f
    using smooth_vf_diff_fun_space[OF Y smooth_vf_diff_fun_space[OF X f]]
    using smooth_vf_diff_fun_space[OF X smooth_vf_diff_fun_space[OF Y f]] by simp_all
  show 1: "[X;Y] \<hungarumlaut> f \<in> diff_fun_space" if f: "f \<in> diff_fun_space" for f
    using 0[OF f] diff_fun_space_minus by (simp add: fun_diff_def lie_bracket_def)
  thus 2: "[X;Y] \<hungarumlaut> (f*g) = f * ([X;Y]\<hungarumlaut>g) + g * ([X;Y]\<hungarumlaut>f)"
    if f: "f \<in> diff_fun_space" and g: "g \<in> diff_fun_space" for f g
    using product_rule_lie_bracket[OF X Y f g] by simp
  show 3: "linear_on diff_fun_space diff_fun_space scaleR scaleR (\<lambda>f. [X;Y] \<hungarumlaut> f)"
  proof -
    have lin_X: "real_linear_on diff_fun_space diff_fun_space (\<lambda>f. X\<hungarumlaut>f)"
      using linear_on_vec_field X[unfolded smooth_vector_field_def] by simp
    have lin_Y: "real_linear_on diff_fun_space diff_fun_space (\<lambda>f. Y\<hungarumlaut>f)"
      using linear_on_vec_field Y[unfolded smooth_vector_field_def] by simp
    have lin_XY: "real_linear_on diff_fun_space diff_fun_space ((vec_field_apply_fun X) \<circ> (vec_field_apply_fun Y))"
      using smooth_vf_diff_fun_space[OF Y] by (auto intro: linear_on_compose[OF lin_Y lin_X])
    have lin_YX: "real_linear_on diff_fun_space diff_fun_space ((vec_field_apply_fun Y) \<circ> (vec_field_apply_fun X))"
      using smooth_vf_diff_fun_space[OF X] by (auto intro: linear_on_compose[OF lin_X lin_Y])
    have "real_linear_on diff_fun_space diff_fun_space (\<lambda>x. (X \<hungarumlaut> (Y \<hungarumlaut> x)) - (Y \<hungarumlaut> (X \<hungarumlaut> x)))"
      apply (intro vector_space_pair_on.linear_compose_sub[OF _ _ _ lin_XY lin_YX, simplified])
      using linear_on.vector_space_pair_on[OF lin_X] 0 by auto
    then show ?thesis by (simp add: lie_bracket_def fun_diff_def)
  qed
qed


text \<open>This is Lee's \cite[Lemma~8.25]{lee_2012}.\<close>
lemma lie_bracket_closed:
  assumes X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
  shows "smooth_vector_field [X;Y]"
  using extensional_derivation_is_smooth_vector_field lie_bracket_is_derivation_on
    ext0_lie_bracket assms smooth_vector_field_def rough_vector_fieldE(2) by auto


lemma
  assumes X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
    and Z: "smooth_vector_field Z"
  shows lie_bracket_add_left: "[X+Y;Z] = [X;Z] + [Y;Z]"
    and lie_bracket_add_right: "[X;Y+Z] = ([X;Y] + [X;Z])"
proof -
  have distrib_left: "[X+Y;Z] = ([X;Z] + [Y;Z])"
    if X: "smooth_vector_field X"
      and Y: "smooth_vector_field Y"
      and Z: "smooth_vector_field Z"
    for X Y Z
  proof (standard+)
    fix p f
    show "[X+Y;Z] p f = ([X;Z] + [Y;Z]) p f"
    proof (cases "p\<in>carrier \<and> f\<in>diff_fun_space")
      text \<open>We deal with the cases outside our interest off the bat. This is just taking care of
            \<^term>\<open>extensional0\<close> in both (point and function) arguments of the vector field.\<close>
      case False
      then show ?thesis
        apply (cases "p\<in>carrier", simp_all)
        subgoal
          using False X Y Z smooth_vector_field_def rough_vector_field_add[of X Y]
          using extensional0_outside[OF _ ext0_lie_bracket(2)]
            extensional0_add[OF smooth_vector_fieldE(2)[OF X] smooth_vector_fieldE(2)[OF Y]]
          by (smt (verit, ccfv_SIG) zero_fun_apply)
        using X Y Z smooth_vector_fieldE(2) extensional0_outside[OF _ ext0_lie_bracket(1)] by force
    next
      text \<open>The rest of this proof is just linearity of the tangent vector \<^term>\<open>Z p\<close>.\<close>
      case True hence p: "p\<in>carrier" and f: "f\<in>diff_fun_space" by simp+
      interpret linZ: linear_on diff_fun_space UNIV scaleR scaleR "Z p"
        using tangent_spaceD(1)[OF smooth_vector_fieldE(1)[OF Z]] by blast
      show ?thesis
        using linZ.add X Y smooth_vf_diff_fun_space f by (auto simp: lie_bracket_def plus_fun_def)
    qed
  qed
  thus "[X+Y;Z] = [X;Z] + [Y;Z]" using assms by blast
  show "[X;Y+Z] = ([X;Y] + [X;Z])"
    using distrib_left[OF Y Z X] lie_bracket_antisym by (metis minus_add_distrib)
qed


lemma
  assumes X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
  shows lie_bracket_scale_left: "[scaleR_vf a X; Y] = scaleR_vf a [X; Y]"
    and lie_bracket_scale_right: "[X; scaleR_vf a Y] = scaleR_vf a [X; Y]"
proof -
  text \<open>We proceed as above, dealing with extensionality before using an existing linearity result.\<close>
  have scaleR_vf_left: "[scaleR_vf a X; Y] = scaleR_vf a [X; Y]"
    if X: "smooth_vector_field X"
      and Y: "smooth_vector_field Y"
    for X Y a
  proof (standard+)
    fix p f
    show "[scaleR_vf a X; Y] p f = scaleR_vf a [X; Y] p f"
    proof (cases "p\<in>carrier \<and> f\<in>diff_fun_space")
      case False
      then show ?thesis 
        apply (cases "p\<in>carrier")
        subgoal
          using False X Y smooth_vector_field_def rough_vector_field_scaleR
          using extensional0_outside[OF _ ext0_lie_bracket(2)] extensional0_scaleR
          by (smt (verit, del_insts) scaleR_cancel_right scaleR_fun_beta scaleR_zero_left)
        using smooth_vector_fieldE(2) X Y extensional0_outside[OF _ ext0_lie_bracket(1)] by simp
    next
      case True hence f: "f\<in>diff_fun_space" by simp+
      interpret linY: linear_on diff_fun_space UNIV scaleR scaleR "Y p"
        using tangent_spaceD(1)[OF smooth_vector_fieldE(1)[OF Y]] by blast
      show ?thesis
        using linY.scale[OF smooth_vf_diff_fun_space, OF X f]
        by (auto simp: lie_bracket_def scaleR_fun_def right_diff_distrib)
    qed
  qed
  thus "[scaleR_vf a X; Y] = scaleR_vf a [X; Y]" by (simp add: X Y)
  show "[X; scaleR_vf a Y] = scaleR_vf a [X; Y]"
    apply (simp only: lie_bracket_antisym[of X "scaleR_vf a Y"] lie_bracket_antisym[of X Y])
    using scaleR_vf_left[OF Y X] by fastforce
qed


lemmas lie_bracket_bilinear_simps [simp] = lie_bracket_scale_left
                                           lie_bracket_scale_right
                                           lie_bracket_add_left
                                           lie_bracket_add_right

lemma (in module_hom_on) diff:
  "b1 \<in> S1 \<Longrightarrow> b2 \<in> S1 \<Longrightarrow> f (b1 - b2) = f b1 - f b2"
  by (metis add diff_eq_eq m1.subspace_UNIV m1.subspace_diff set_eq_subset)


lemma lie_bracket_jacobi: "[X; [Y;Z]] + [Y;[Z;X]] + [Z;[X;Y]] = 0"
  if X: "smooth_vector_field X"
    and Y: "smooth_vector_field Y"
    and Z: "smooth_vector_field Z"
proof -
  have rough_vf: "rough_vector_field X" "rough_vector_field Y" "rough_vector_field Z"
    using smooth_vector_field_def that by auto
  interpret linear_X: linear_on diff_fun_space diff_fun_space scaleR scaleR "vec_field_apply_fun X"
    using linear_on_vec_field[OF rough_vf(1)] .
  interpret linear_Y: linear_on diff_fun_space diff_fun_space scaleR scaleR "vec_field_apply_fun Y"
    using linear_on_vec_field[OF rough_vf(2)] .
  interpret linear_Z: linear_on diff_fun_space diff_fun_space scaleR scaleR "vec_field_apply_fun Z"
    using linear_on_vec_field[OF rough_vf(3)] .

  have local_simps:
    "\<And>f. f\<in>diff_fun_space \<Longrightarrow> X \<hungarumlaut> f \<in> diff_fun_space"
    "\<And>f. f\<in>diff_fun_space \<Longrightarrow> Y \<hungarumlaut> f \<in> diff_fun_space"
    "\<And>f. f\<in>diff_fun_space \<Longrightarrow> Z \<hungarumlaut> f \<in> diff_fun_space"
    using X Y Z by (simp_all add: vector_field_smooth_iff rough_vf)

  {
    fix f assume f: "f\<in>diff_fun_space"
    have "[X; [Y;Z]] \<hungarumlaut> f + [Y;[Z;X]] \<hungarumlaut> f + [Z;[X;Y]] \<hungarumlaut> f =
        X \<hungarumlaut> ([Y;Z]\<hungarumlaut>f) - [Y;Z] \<hungarumlaut> (X\<hungarumlaut>f) + Y \<hungarumlaut> ([Z;X]\<hungarumlaut>f) - [Z;X] \<hungarumlaut> (Y\<hungarumlaut>f) + Z \<hungarumlaut> ([X;Y]\<hungarumlaut>f) - [X;Y] \<hungarumlaut> (Z\<hungarumlaut>f)"
      unfolding lie_bracket_def by auto
    also have "\<dots> = X\<hungarumlaut>(Y\<hungarumlaut>(Z\<hungarumlaut>f)) - X\<hungarumlaut>(Z\<hungarumlaut>(Y\<hungarumlaut>f))
                  - Y\<hungarumlaut>(Z\<hungarumlaut>(X\<hungarumlaut>f)) + Z\<hungarumlaut>(Y\<hungarumlaut>(X\<hungarumlaut>f))
                  + Y\<hungarumlaut>(Z\<hungarumlaut>(X\<hungarumlaut>f)) - Y\<hungarumlaut>(X\<hungarumlaut>(Z\<hungarumlaut>f))
                  - Z\<hungarumlaut>(X\<hungarumlaut>(Y\<hungarumlaut>f)) + X\<hungarumlaut>(Z\<hungarumlaut>(Y\<hungarumlaut>f))
                  + Z\<hungarumlaut>(X\<hungarumlaut>(Y\<hungarumlaut>f)) - Z\<hungarumlaut>(Y\<hungarumlaut>(X\<hungarumlaut>f))
                  - X\<hungarumlaut>(Y\<hungarumlaut>(Z\<hungarumlaut>f)) + Y\<hungarumlaut>(X\<hungarumlaut>(Z\<hungarumlaut>f))"
      using linear_X.diff linear_Y.diff linear_Z.diff by (auto simp: f fun_diff_def lie_bracket_def local_simps)
    finally have "[X; [Y;Z]] \<hungarumlaut> f + [Y;[Z;X]] \<hungarumlaut> f + [Z;[X;Y]] \<hungarumlaut> f = 0" by simp
  } moreover {
    fix f assume f: "f \<notin> diff_fun_space"
    have "[X; [Y;Z]] \<hungarumlaut> f = 0" "[Y; [Z;X]] \<hungarumlaut> f = 0" "[Z;[X;Y]] \<hungarumlaut> f = 0"
      using ext0_lie_bracket(2)[OF smooth_vector_fieldE(3) smooth_vector_fieldE(3)] X Y Z
      using lie_bracket_closed(1)[OF Y Z] lie_bracket_closed(1)[OF Z X] lie_bracket_closed(1)[OF X Y]
      by (simp_all add: extensional0_def f smooth_vector_field_alt)
    hence "[X; [Y;Z]] \<hungarumlaut> f + [Y;[Z;X]] \<hungarumlaut> f + [Z;[X;Y]] \<hungarumlaut> f = 0" by simp
  } ultimately have "\<And>p f. [X; [Y;Z]] p f + [Y;[Z;X]] p f + [Z;[X;Y]] p f = 0"
    by (smt (verit, best) plus_fun_apply zero_fun_apply) 
  thus ?thesis by (intro HOL.ext) fastforce
qed


definition "SVF \<equiv> {X. smooth_vector_field X}"


lemma lie_algebra_of_smooth_vector_fields: "lie_algebra SVF scaleR_vf lie_bracket_of_smooth_vector_fields"
proof -
  note svf_if_derivI = extensional_derivation_is_smooth_vector_field[unfolded is_derivation_on_def]

  have svf_0: "smooth_vector_field 0"
    apply (intro svf_if_derivI, safe, unfold_locales)
    apply auto[3]
    using diff_fun_space.m1.mem_zero uminus_apply apply fastforce
    using extensional0_def zero_fun_def by auto

  have local_simps: "(\<lambda>r f p. r * f (p::'a)) = scaleR"
    by fastforce

  have svf_scaleR: "smooth_vector_field (a *\<^sub>R X)"
    if X: "smooth_vector_field X"  for a X
  proof (intro svf_if_derivI, intro conjI ballI)
    show "extensional0 carrier (a *\<^sub>R X)" by (simp add: smooth_vector_fieldE(2) that)
    have derX: "linear_on diff_fun_space diff_fun_space scaleR scaleR (\<lambda>f p. X p f)"
        "(\<And>f g. f\<in>diff_fun_space \<Longrightarrow> g\<in>diff_fun_space \<Longrightarrow> X \<hungarumlaut> (f * g) = f * (X \<hungarumlaut> g) + g * (X \<hungarumlaut> f))"
        "(\<lambda>f p. X p f) ` diff_fun_space \<subseteq> diff_fun_space"
      using X vector_field_is_derivation unfolding is_derivation_on_def by auto
    show "real_linear_on diff_fun_space diff_fun_space (\<lambda>f p. (a *\<^sub>R X) p f)"
        using linear_on_compose[OF derX(1) diff_fun_space.m1.linear_scale_self derX(3)]
        by (simp add: o_def, metis local_simps)
    show "(\<lambda>p. (a *\<^sub>R X) p (f * g)) = f * (\<lambda>p. (a *\<^sub>R X) p g) + g * (\<lambda>p. (a *\<^sub>R X) p f)"
      if "f\<in>diff_fun_space" "g\<in>diff_fun_space" for f g
    proof -
      have "(\<lambda>p. a * X p (f * g)) = (\<lambda>x. a) * (\<lambda>p. X p (f * g))" by auto
      then show "(\<lambda>p. (a *\<^sub>R X) p (f * g)) = f * (\<lambda>p. (a *\<^sub>R X) p g) + g * (\<lambda>p. (a *\<^sub>R X) p f)"
        using derX(2)[OF that] by (auto simp: distrib_left)
    qed
    show "(\<lambda>f p. (a *\<^sub>R X) p f) ` diff_fun_space \<subseteq> diff_fun_space"
      using derX(3) diff_fun_space.m1.mem_scale by (auto, metis image_subset_iff local_simps)
    show "extensional0 diff_fun_space (\<lambda>f p. (a *\<^sub>R X) p f)"
      using X[unfolded smooth_vector_field_def] ext0_vec_field_apply_fun
      by (meson extensional0_scaleR rough_vector_field_scaleR)
  qed

  have svf_add: "smooth_vector_field (X + Y)"
    if X: "smooth_vector_field X" and Y: "smooth_vector_field Y"
    for X Y
  proof (intro svf_if_derivI, intro conjI ballI)
    have derX: "real_linear_on diff_fun_space diff_fun_space (\<lambda>f p. X p f)"
        "(\<And>f g. f\<in>diff_fun_space \<Longrightarrow> g\<in>diff_fun_space \<Longrightarrow> X \<hungarumlaut> (f * g) = f * (X \<hungarumlaut> g) + g * (X \<hungarumlaut> f))"
        "(\<lambda>f p. X p f) ` diff_fun_space \<subseteq> diff_fun_space"
      and derY: "real_linear_on diff_fun_space diff_fun_space (\<lambda>f p. Y p f)"
        "(\<And>f g. f\<in>diff_fun_space \<Longrightarrow> g\<in>diff_fun_space \<Longrightarrow> Y \<hungarumlaut> (f * g) = f * (Y \<hungarumlaut> g) + g * (Y \<hungarumlaut> f))"
        "(\<lambda>f p. Y p f) ` diff_fun_space \<subseteq> diff_fun_space"
      using X Y vector_field_is_derivation unfolding is_derivation_on_def by auto

    interpret D: vector_space_pair_on diff_fun_space diff_fun_space scaleR scaleR by unfold_locales

    show "real_linear_on diff_fun_space diff_fun_space (\<lambda>f p. (X + Y) p f)"
      apply (simp, intro D.linear_compose_add[unfolded plus_fun_def])
      using derX(1,3) derY(1,3) by auto
    show "(\<lambda>p. (X + Y) p (f * g)) = f * (\<lambda>p. (X + Y) p g) + g * (\<lambda>p. (X + Y) p f)"
      if "f \<in> diff_fun_space"  "g \<in> diff_fun_space" for f g
      using derX(2)[OF that] derY(2)[OF that]
      by (simp add: plus_fun_def distrib_left, metis (no_types) add.commute add.left_commute)
    show "(\<lambda>f p. (X + Y) p f) ` diff_fun_space \<subseteq> diff_fun_space"
      using derX(3) derY(3) diff_fun_space.m1.mem_add by (auto simp: plus_fun_def)
    show "extensional0 diff_fun_space (\<lambda>f p. (X + Y) p f)"
      using X Y ext0_vec_field_apply_fun rough_vector_field_add smooth_vector_field_def by blast
    show "extensional0 carrier (X + Y)" by (simp add: X Y smooth_vector_fieldE(2))
  qed

  interpret vector_space_svf: vector_space_on SVF scaleR_vf
    using svf_0 svf_scaleR svf_add SVF_def
    by (unfold_locales, auto simp: scaleR_right_distrib scaleR_left_distrib)

  have lie_bracket_antisym': "[X;X] = 0"
    if X: "smooth_vector_field X" "extensional0 carrier X" for X
    using lie_bracket_antisym by (metis one_neq_neg_one scaleR_cancel_right scaleR_minus1_left scaleR_one)

  show ?thesis
    apply (intro vector_space_svf.lie_algebraI, unfold SVF_def)
    using lie_bracket_closed lie_bracket_antisym' lie_bracket_jacobi
    by (simp_all add: smooth_vector_fieldE(2))
qed

end

end