(*  Title:       Smooth_Vector_Fields
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

section \<open>Smooth vector fields\<close>
theory Smooth_Vector_Fields
  imports
    More_Manifolds
begin

text \<open>Type synonyms for use later: these already follow our later split between defining
  ``charts'' for the tangent bundle as a product, and talking about vector fields as maps
  $p \mapsto v \in T_pM$ as well as sections of the tangent bundle $M \to TM$.\<close>

type_synonym 'a tangent_bundle = "'a \<times> (('a\<Rightarrow>real)\<Rightarrow>real)"
type_synonym 'a vector_field = "'a \<Rightarrow> (('a\<Rightarrow>real)\<Rightarrow>real)"

subsection \<open>(Smooth) vector fields on an (entire) manifold.\<close>

text \<open>
  Since we only get an isomorphism between tangent vectors and directional derivatives
  in the smooth case of \<^term>\<open>k = \<infinity>\<close>, we create a locale for infinitely smooth manifolds.
\<close>
locale smooth_manifold = c_manifold charts \<infinity> for charts

context c_manifold begin

subsubsection \<open>Charts for the tangent bundle\<close>

definition in_TM :: "'a \<Rightarrow> (('a\<Rightarrow>real)\<Rightarrow>real) \<Rightarrow> bool"
  where "in_TM p v \<equiv> p\<in>carrier \<and> v \<in> tangent_space p"

abbreviation "TM \<equiv> {(p,v). in_TM p v}"

lemma in_TM_E [elim]:
  assumes "in_TM p v"
  shows "v \<in> tangent_space p" "p\<in>carrier"
  using assms unfolding in_TM_def by auto

lemma TM_PairE [elim]:
  assumes "(p,v) \<in> TM"
  shows "v \<in> tangent_space p" "p\<in>carrier"
  using assms unfolding in_TM_def by auto

lemma TM_E [elim]:
  assumes "x \<in> TM"
  shows "snd x \<in> tangent_space (fst x)" "fst x \<in> carrier"
  using assms by auto

text \<open>We can construct a chart for \<^term>\<open>tangent_space p\<close> given a chart around \<^term>\<open>p\<close>.
  Notice the appearance of \<^term>\<open>charts\<close> in the definition, which specifies that we're charting
  the set \<^term>\<open>tangent_space p\<close>, \emph{not} \<^term>\<open>c_manifold.tangent_space (charts_submanifold c) \<infinity> p\<close>.\<close>
definition apply_chart_TM :: "('a,'b)chart \<Rightarrow> 'a tangent_bundle \<Rightarrow> 'b \<times> 'b"
  where "apply_chart_TM c \<equiv> \<lambda>(p,v). (c p  ,  c_manifold_point.tangent_chart_fun charts \<infinity> c p v)"

definition inv_chart_TM :: "('a,'b)chart \<Rightarrow> ('b \<times> 'b) \<Rightarrow> 'a \<times> (('a \<Rightarrow> real) \<Rightarrow> real)"
  where "inv_chart_TM c \<equiv> \<lambda>((p::'b),(v::'b)). (inv_chart c p  ,  c_manifold_point.coordinate_vector charts \<infinity> c (inv_chart c p) v)"

definition domain_TM :: "('a,'b) chart \<Rightarrow> ('a \<times> (('a \<Rightarrow> real) \<Rightarrow> real)) set"
  where "domain_TM c \<equiv> {(p, v). p \<in> domain c \<and> v \<in> tangent_space p}"

definition codomain_TM :: "('a,'b) chart \<Rightarrow> ('b\<times>'b) set"
  where "codomain_TM c \<equiv> {(p, v). p \<in> codomain c}"

definition "restrict_chart_TM S c \<equiv> apply_chart_TM (restrict_chart S c)"
definition "restrict_domain_TM S c \<equiv> domain_TM (restrict_chart S c)"
definition "restrict_codomain_TM S c \<equiv> codomain_TM (restrict_chart S c)"
definition "restrict_inv_chart_TM S c \<equiv> inv_chart_TM (restrict_chart S c)"


subsubsection \<open>Proofs about \<^term>\<open>apply_chart_TM\<close> that mimic the properties of \<^typ>\<open>('a,'b)chart\<close>.\<close>

lemma domain_TM:
  assumes "c \<in> atlas"
  shows "domain_TM c \<subseteq> TM"
  unfolding domain_TM_def in_TM_def using assms by auto

lemma codomain_TM_alt: "codomain_TM c = codomain c \<times> (UNIV :: 'b set)"
  unfolding codomain_TM_def by auto

lemma open_codomain_TM:
  assumes "c \<in> atlas"
  shows "open (codomain_TM c)"
  using codomain_TM_alt open_Times[OF open_codomain open_UNIV] by auto

end


context smooth_manifold begin

lemma apply_chart_TM_inverse [simp]:
  assumes c: "c \<in> atlas"
  shows "\<And>p v. (p,v) \<in> domain_TM c \<Longrightarrow> inv_chart_TM c (apply_chart_TM c (p,v)) = (p,v)"
    and "\<And>x u. (x,u) \<in> codomain_TM c \<Longrightarrow> apply_chart_TM c (inv_chart_TM c (x,u)) = (x,u)"
proof -
  fix p v assume "(p,v) \<in> domain_TM c"
  then have asm: "c \<in> atlas" "p \<in> domain c" "v \<in> tangent_space p"
    using c by (auto simp add: domain_TM_def)
  interpret p: c_manifold_point charts \<infinity> c p
    using c_manifold_point[OF asm(1,2)] by simp
  have "v \<in> p.T\<^sub>pM" using asm(3) by simp
  from p.coordinate_vector_inverse(1)[OF _ this] show "inv_chart_TM c (apply_chart_TM c (p,v)) = (p,v)"
    by (simp add: inv_chart_TM_def apply_chart_TM_def p.tangent_chart_fun_def)
next
  fix x u assume "(x,u) \<in> codomain_TM c"
  then have asm: "c \<in> atlas" "x \<in> codomain c"
    using c by (auto simp add: codomain_TM_def)
  interpret x: c_manifold_point charts \<infinity> c "inv_chart c x"
    using c_manifold_point[OF asm(1)] by (simp add: asm(2))
  from x.coordinate_vector_inverse(2) show "apply_chart_TM c (inv_chart_TM c (x,u)) = (x,u)"
    by (simp add: inv_chart_TM_def apply_chart_TM_def x.tangent_chart_fun_def asm(2))
qed

lemma image_domain_TM_eq:
  assumes "c \<in> atlas"
  shows "apply_chart_TM c ` domain_TM c = codomain_TM c"
proof -
  { fix x :: "'b \<times> 'b" assume x: "x \<in> codomain c \<times> UNIV"
    obtain y\<^sub>1 y\<^sub>2 where y: "y\<^sub>1 = inv_chart c (fst x)" "y\<^sub>2 = c_manifold_point.coordinate_vector charts \<infinity> c y\<^sub>1 (snd x)"
      by simp
    have "y\<^sub>1 \<in> domain c" using y(1) x by auto
    then interpret y\<^sub>1: c_manifold_point charts \<infinity> c y\<^sub>1
      by (simp add: assms(1) c_manifold_point)
    have "y\<^sub>2 \<in> tangent_space y\<^sub>1"
      using y(2) x assms y\<^sub>1.coordinate_vector_surj by blast
    then have "(y\<^sub>1,y\<^sub>2) \<in> {(p, v). p \<in> domain c \<and> v \<in> tangent_space p}"
      using \<open>y\<^sub>1 \<in> domain c\<close> by simp
    moreover have "fst x = c y\<^sub>1" "snd x = c_manifold_point.tangent_chart_fun charts \<infinity> c y\<^sub>1 y\<^sub>2"
      using y x assms y\<^sub>1.tangent_chart_fun_inverse(2) by auto
    ultimately have "x \<in> (\<lambda>(p, v). (c p, c_manifold_point.tangent_chart_fun charts \<infinity> c p v)) ` {(p, v). p \<in> domain c \<and> v \<in> tangent_space p}"
      by (metis (no_types, lifting) pair_imageI prod.collapse) }
  thus ?thesis by (auto simp: apply_chart_TM_def domain_TM_def codomain_TM_alt)
qed

lemma inv_image_codomain_TM_eq:
  assumes "c \<in> atlas"
  shows "inv_chart_TM c ` codomain_TM c = domain_TM c"
  apply (subst image_domain_TM_eq[OF assms, symmetric])
  using apply_chart_TM_inverse(1)[OF assms] by force


lemma (in c_manifold) restrict_domain_TM_intersection:
  shows "restrict_domain_TM (domain c1 \<inter> domain c2) c1 = domain_TM c1 \<inter> domain_TM c2"
  unfolding restrict_domain_TM_def by (auto simp: domain_TM_def open_Int)


lemma (in c_manifold) restrict_domain_TM_intersection':
  shows "restrict_domain_TM (domain c1 \<inter> domain c2) c2 = domain_TM c1 \<inter> domain_TM c2"
  unfolding restrict_domain_TM_def by (auto simp: domain_TM_def open_Int)


lemma (in c_manifold) restrict_domain_TM:
  assumes "open S" "S \<subseteq> domain c"
  shows "restrict_domain_TM S c = {(p, v). p \<in> S \<and> v \<in> tangent_space p}"
  unfolding restrict_domain_TM_def domain_TM_def using domain_restrict_chart assms by auto


lemma image_restrict_domain_TM_eq:
  assumes "c \<in> atlas"
  shows "restrict_chart_TM S c ` restrict_domain_TM S c = restrict_codomain_TM S c"
  unfolding restrict_chart_TM_def restrict_domain_TM_def restrict_codomain_TM_def
  using image_domain_TM_eq assms restrict_chart_in_atlas by blast


lemma inv_image_restrict_codomain_TM_eq:
  assumes "c \<in> atlas"
  shows "restrict_inv_chart_TM S c ` restrict_codomain_TM S c = restrict_domain_TM S c"
  by (metis (no_types, lifting) inv_image_codomain_TM_eq assms restrict_chart_in_atlas
      restrict_codomain_TM_def restrict_domain_TM_def restrict_inv_chart_TM_def)


lemma codomain_restrict_chart_TM[simp]:
  assumes "c \<in> atlas" "open S"
  shows "restrict_codomain_TM S c = codomain_TM c \<inter> inv_chart_TM c -` {(p, v). p \<in> S \<and> v \<in> tangent_space p}"
proof -
  {
    fix a b p v
    assume asm: "a \<in> codomain c" "inv_chart_TM c (a, b) = (p, v)"
    interpret p: c_manifold_point charts \<infinity> c "inv_chart c a"
      using asm(1) assms c_manifold_point[OF assms(1), of "inv_chart c a" for a] by blast
    have "p.coordinate_vector b \<in> tangent_space (inv_chart c a)"
      using bij_betwE[OF p.coordinate_vector_bij] by simp
    then have "inv_chart c a \<in> S \<Longrightarrow> v \<in> tangent_space p"
      and "inv_chart c a \<in> S \<Longrightarrow> p \<in> S"
      and "\<lbrakk>p\<in>S; v \<in> tangent_space p\<rbrakk> \<Longrightarrow> inv_chart c a \<in> S"
      subgoal using inv_chart_TM_def inv_image_codomain_TM_eq[OF assms(1)] asm by auto
      subgoal using asm(2) by (auto simp add: assms(2) inv_chart_TM_def)
      subgoal using asm(2) c_manifold.inv_chart_TM_def[OF c_manifold_axioms] by simp
      done
  }
  thus ?thesis by (auto simp add: restrict_codomain_TM_def codomain_TM_def assms(2))
qed

lemma (in c_manifold) image_subset_TM_eq [simp]:
  assumes "S \<subseteq> domain_TM c"
  shows "apply_chart_TM c ` S \<subseteq> codomain_TM c"
  using assms unfolding apply_chart_TM_def codomain_TM_def domain_TM_def by auto

lemma (in c_manifold) image_subset_restrict_TM_eq [simp]:
  assumes "T \<subseteq> restrict_domain_TM S c"
  shows "restrict_chart_TM S c ` T \<subseteq> restrict_codomain_TM S c"
  using assms unfolding restrict_chart_TM_def restrict_codomain_TM_def restrict_domain_TM_def by auto


lemma restrict_chart_domain_Int:
  assumes "c1 \<in> atlas"
  shows "apply_chart_TM c1 ` (domain_TM c1 \<inter> domain_TM c2) = restrict_chart_TM (domain c1 \<inter> domain c2) c1 ` (restrict_domain_TM (domain c1 \<inter> domain c2) c1)"
    (is \<open>?TM_dom_Int = ?restr_TM_dom\<close>)
proof (intro subset_antisym)
  have dom_eq: "domain (restrict_chart (domain c1 \<inter> domain c2) c1) = domain c1 \<inter> domain c2"
    using domain_restrict_chart[OF open_domain] by (metis inf.left_idem)

  { fix x assume "x \<in> (domain_TM c1 \<inter> domain_TM c2)"
    then obtain p v where x: "x = (p,v)" "p \<in> domain c1" "p \<in> domain c2" "v \<in> tangent_space p"
      unfolding domain_TM_def by blast
    interpret p1: c_manifold_point charts \<infinity> c1 p using c_manifold_point[OF assms(1) x(2)] by simp
    interpret p2: c_manifold_point charts \<infinity> "restrict_chart (domain c1 \<inter> domain c2) c1" p
      using c_manifold_point[OF assms(1) x(2)] restrict_chart_in_atlas[OF assms(1)] domain_restrict_chart[OF open_domain]
      by (metis IntI c_manifold_point p1.p x(3))

    have [simp]: "p2.sub_\<psi>.sub.restrict_codomain_TM (domain c1 \<inter> domain c2) c1 =
        {(p, v). p \<in> codomain (restrict_chart (domain c1 \<inter> domain c2) c1)}"
      unfolding p2.sub_\<psi>.sub.restrict_codomain_TM_def p2.sub_\<psi>.sub.codomain_TM_def by simp
      
    have "apply_chart_TM c1 x \<in> ?restr_TM_dom"
      apply (simp add: x(1) image_restrict_domain_TM_eq[OF assms(1)])
      unfolding apply_chart_TM_def using p2.\<psi>p_in by (auto simp: p1.euclidean_coordinates_eq_iff) }
  thus "?TM_dom_Int \<subseteq> ?restr_TM_dom" by auto

  { fix x assume "x \<in> restrict_domain_TM (domain c1 \<inter> domain c2) c1"
    then obtain p v where x: "x = (p,v)" "p \<in> domain c1" "p \<in> domain c2" "v \<in> tangent_space p"
      unfolding restrict_domain_TM_def domain_TM_def by (auto simp: dom_eq)
    interpret p1: c_manifold_point charts \<infinity> c1 p using c_manifold_point[OF assms(1) x(2)] by simp
    interpret p2: c_manifold_point charts \<infinity> "restrict_chart (domain c1 \<inter> domain c2) c1" p
      using c_manifold_point[OF assms(1) x(2)] restrict_chart_in_atlas[OF assms(1)] domain_restrict_chart[OF open_domain]
      by (metis IntI c_manifold_point p1.p x(3))
    have "restrict_chart_TM (domain c1 \<inter> domain c2) c1 x \<in> ?TM_dom_Int"
    proof -
      have "apply_chart c1 p \<in> apply_chart c1 ` (domain c1 \<inter> domain c2)"
        using p1.p x(3) by blast
      moreover have "p2.tangent_chart_fun v \<in> c_manifold_point.tangent_chart_fun charts \<infinity> c1 p ` {v. v\<in>tangent_space p}"
        using p1.coordinate_vector_surj p1.tangent_chart_fun_inverse(2) by fastforce
      ultimately show ?thesis
        apply (simp add: apply_chart_TM_def)
        apply (simp add: x(1) restrict_chart_TM_def)
        apply (simp add: apply_chart_TM_def apply_chart_restrict_chart[of "domain c1 \<inter> domain c2" c1])
        unfolding domain_TM_def by force
    qed }
  thus "?restr_TM_dom \<subseteq> ?TM_dom_Int" by blast
qed


lemma open_intersection_TM:
  assumes "c1 \<in> atlas"
  shows "open (apply_chart_TM c1 ` (domain_TM c1 \<inter> domain_TM c2))"
  using restrict_chart_domain_Int image_restrict_domain_TM_eq restrict_chart_in_atlas assms
  by (auto simp: restrict_codomain_TM_def open_codomain_TM)


lemma apply_restrict_chart_TM:
  assumes c: "c \<in> atlas" and S: "open S" "S \<subseteq> domain c" "x \<in> restrict_domain_TM S c"
  shows "apply_chart_TM c x =  restrict_chart_TM S c x"
proof -
  { fix p v assume x: "x = (p,v)" "p \<in> S" "v \<in> tangent_space p"
    interpret p1: c_manifold_point charts \<infinity> c p
      using c_manifold_point[OF c] x(2) S(2) by blast
    interpret p2: c_manifold_point charts \<infinity> "restrict_chart S c" p
      apply (rule c_manifold.c_manifold_point, unfold_locales)
      using S(1) x(2) by (auto simp add: restrict_chart_in_atlas)
    have T\<^sub>pM_eq: "p2.T\<^sub>pM = tangent_space p" by simp
    have "p1.tangent_chart_fun v = p2.tangent_chart_fun v"
      unfolding p1.tangent_chart_fun_def p2.tangent_chart_fun_def
      using p1.component_function_restrict_chart[OF x(2) S(1)] T\<^sub>pM_eq x(3) by simp }
  thus ?thesis
    using S(3) restrict_domain_TM[OF S(1,2)] unfolding restrict_chart_TM_def apply_chart_TM_def by auto
qed


lemma inverse_restrict_chart_TM:
  assumes c: "c \<in> atlas" and S: "open S" "S \<subseteq> domain c" "x \<in> restrict_codomain_TM S c"
  shows "inv_chart_TM c x =  restrict_inv_chart_TM S c x"
proof -
  { fix p v assume x: "x = (p,v)" "p \<in> c`S"
    interpret p1: c_manifold_point charts \<infinity> c "inv_chart c p"
      using c_manifold_point[OF c] x(2) S(2) by blast
    have pS: "inv_chart c p \<in> S"
      using restrict_chart_in_atlas x(2) S(2) image_domain_eq by auto
    interpret p2: c_manifold_point charts \<infinity> "restrict_chart S c" "inv_chart c p"
      apply (rule c_manifold.c_manifold_point, unfold_locales)
      using pS restrict_chart_in_atlas S(1) by auto
    have "p1.coordinate_vector v = p2.coordinate_vector v"
      using p1.coordinate_vector_restrict_chart[OF pS S(1)]
      using p1.coordinate_vector_def p2.coordinate_vector_def by presburger }
  thus ?thesis
    using S(3) inv_chart_TM_def apply_chart_TM_def
    apply (simp add: codomain_restrict_chart_TM[OF c S(1)] restrict_inv_chart_TM_def)
    using apply_chart_TM_inverse(2)[OF c] surj_pair by (smt (verit) case_prod_conv image_eqI)
qed


lemma (in c_manifold_point) d\<kappa>_inv_directional_derivative_eq:
  assumes "k = \<infinity>"
  shows "d\<kappa>\<inverse> (directional_derivative k (\<psi> p) x) = restrict0 (diffeo_\<psi>.dest.diff_fun_space) (\<lambda>f. frechet_derivative f (at (\<psi> p)) x)"
proof -

  let ?is_ext = "\<lambda>f f'. f\<in>diffeo_\<psi>.dest.diff_fun_space \<and> f' \<in> manifold_eucl.dest.diff_fun_space \<and> f' \<in> diffeo_\<psi>.dest.diff_fun_space \<and>
    (\<exists>N. \<psi> p \<in> N \<and> open N \<and> closure N \<subseteq> diffeo_\<psi>.dest.carrier \<and> (\<forall>x\<in>closure N. f' x = f x) \<and>
      (\<forall>v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U. v f = v f') \<and> (\<forall>v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U. v f' = d\<kappa> v f') \<and> (\<forall>v\<in>T\<^sub>\<psi>\<^sub>pE. d\<kappa>\<inverse> v f = v f'))"
  let ?extend = "\<lambda>f. SOME f'. ?is_ext f f'"
  obtain extend where extend_def: "extend \<equiv> ?extend" by blast
  have extend: "?is_ext f (extend f)" "?is_ext f (?extend f)"
    if "f\<in>diffeo_\<psi>.dest.diff_fun_space" for f
  proof -
    show "?is_ext f (?extend f)"
      by (rule someI_ex[of "\<lambda>f'. ?is_ext f f'"]) (smt (verit) that extension_lemma_localE2)
    thus "?is_ext f (extend f)" unfolding extend_def by blast
  qed

  have "extend ` diffeo_\<psi>.dest.diff_fun_space \<subseteq> manifold_eucl.dest.diff_fun_space"
    using extend by blast

  have "d\<kappa>\<inverse> (directional_derivative k (\<psi> p) x) f = restrict0 (diffeo_\<psi>.dest.diff_fun_space) (\<lambda>f. frechet_derivative f (at (\<psi> p)) x) f"
    for f
  proof (cases "f \<in> diffeo_\<psi>.dest.diff_fun_space")
    case True
    have frechet_derivative_extend: "frechet_derivative f (at (\<psi> p)) x = frechet_derivative (extend f) (at (\<psi> p)) x"
      if f: "f\<in>diffeo_\<psi>.dest.diff_fun_space" for f
    proof -
      obtain N where N: "\<psi> p \<in> N \<and> open N \<and> closure N \<subseteq> diffeo_\<psi>.dest.carrier \<and> (\<forall>x\<in>closure N. (extend f) x = f x) \<and>
        (\<forall>v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U. v f = v (extend f)) \<and> (\<forall>v\<in>T\<^sub>\<psi>\<^sub>p\<psi>U. v (extend f) = d\<kappa> v (extend f)) \<and> (\<forall>v\<in>T\<^sub>\<psi>\<^sub>pE. d\<kappa>\<inverse> v f = v (extend f))"
        using extend(1)[OF f] by presburger
      show ?thesis
        apply (rule frechet_derivative_transform_within_open_ext[where f=f and g="extend f" and X=N for f])
        using sub_eucl.submanifold_atlasI sub_eucl.sub_diff_fun_differentiable_at
            [OF diffeo_\<psi>.dest.diff_fun_spaceD[OF f], of "restrict_chart (codomain \<psi>) chart_eucl"]
          apply (simp add: id_def[symmetric] assms)
        using N by simp_all
      qed
    have "d\<kappa>\<inverse> (directional_derivative k (\<psi> p) x) f = (directional_derivative k (\<psi> p) x) (extend f)"
      using assms eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion eq_T\<^sub>\<psi>\<^sub>pE_range_inclusion2 extend(1) True by blast
    also have "\<dots> = frechet_derivative (extend f) (at (\<psi> p)) x"
      unfolding directional_derivative_def using extend(1)[OF True] by simp
    finally show ?thesis
      using True frechet_derivative_extend by simp
  next
    case False
    then show ?thesis
    proof -
      have RHS_0: "restrict0 diffeo_\<psi>.dest.diff_fun_space (\<lambda>f. frechet_derivative f (at (\<psi> p)) x) f = 0"
        using restrict0_apply_out[OF False] by blast
      moreover have LHS_0: "d\<kappa>\<inverse> (directional_derivative k (\<psi> p) x) f = 0"
        using bij_betwE[OF bij_betw_d\<kappa>_inv] bij_betwE[OF bij_betw_directional_derivative[OF assms]]
        using diffeo_\<psi>.dest.tangent_spaceD extensional0_outside[OF False] by blast
      ultimately show ?thesis by simp
    qed
  qed
  thus ?thesis by blast
qed




lemma smooth_on_compat_charts_TM:
  assumes "c1 \<in> atlas" "c2 \<in> atlas"
  shows "smooth_on (c1 ` (domain c1 \<inter> domain c2) \<times> UNIV)
      (\<lambda>x. frechet_derivative ((\<lambda>y. (restrict_chart (domain c1 \<inter> domain c2) c2) y \<bullet> i) \<circ> inv_chart (restrict_chart (domain c1 \<inter> domain c2) c1)) (at (fst x)) (snd x))"
    (is \<open>smooth_on ?D (\<lambda>x. frechet_derivative ((\<lambda>y. ?r2 y \<bullet> i) \<circ> ?r1i) (at (fst x)) (snd x))\<close>)
proof -
  let ?dom_Int = "domain c1 \<inter> domain c2"
  have open_simps[simp]: "open ?dom_Int" "open ?D"
    by (auto simp: open_Int open_Times)

  have smooth_on_1: "smooth_on (fst`?D) ((\<lambda>y. ?r2 y \<bullet> i) \<circ> ?r1i)" for i
    apply simp
    apply (rule smooth_on_cong'[of _ "c1 ` (domain c1 \<inter> domain c2)"])
    apply (rule smooth_on_cong[of _ _ "(\<lambda>y. c2 (inv_chart c1 y) \<bullet> i)"])
    apply (rule smooth_on_inner[OF _ smooth_on_const[of _ _ i]])
    using atlas_is_atlas[unfolded smooth_compat_def o_def, OF assms(1,2)] apply auto[4]
    unfolding restrict_codomain_TM_def codomain_TM_alt using image_domain_eq by fastforce
  have smooth_on_2: "smooth_on ?D (\<lambda>x. frechet_derivative ((\<lambda>y. (?r2 y) \<bullet> i) \<circ> ?r1i) (at (fst x)) v)" for v i
    apply (rule smooth_on_compose2[OF derivative_is_smooth, unfolded o_def, where S=UNIV and T="fst`?D"])
    using smooth_on_fst smooth_on_1 by (auto simp: open_image_fst)

  have r2_r1i_differentiable: "(\<lambda>x. ?r2 (?r1i x) \<bullet> i) differentiable (at (fst p))" if "p \<in> ?D" for i::'b and p
  proof -
    have 1: "open (c1 ` (domain c1 \<inter> domain c2))"
      and 2: "c1 (inv_chart c1 (fst p)) = fst p"
      and 3: "inv_chart c1 (fst p) \<in> ?dom_Int" using that by auto
    show ?thesis
      using smooth_on_imp_differentiable_on[unfolded differentiable_on_def, OF smooth_on_1]
      by (simp add: o_def) (metis at_within_open image_eqI 1 2 3)
  qed

  show ?thesis
    unfolding o_def
    apply (rule smooth_on_cong[OF _ _ frechet_derivative_componentwise[OF r2_r1i_differentiable]])
    apply (rule smooth_on_sum)
    apply (rule smooth_on_times_fun[of \<infinity> ?D, unfolded times_fun_def])
    subgoal by (auto intro!: smooth_on_inner smooth_on_snd)
    subgoal using smooth_on_2[unfolded o_def] by simp
    by simp_all
qed


\<comment> \<open>The charts defined above for the tangent bundle of an infinitly smooth manifold are compatible
  (see \<^term>\<open>smooth_compat\<close>) if the charts used for the construction are compatible.
  Thus, we can construct an atlas (up to type class issues) for $TM$ from the atlas of the manifold.\<close>
lemma atlas_TM:
  assumes "c1 \<in> atlas" "c2 \<in> atlas"
  shows "smooth_on ((apply_chart_TM c1) ` (domain_TM c1 \<inter> domain_TM c2)) ((apply_chart_TM c2) \<circ> (inv_chart_TM c1))"
    (is \<open>smooth_on (?c1 ` (?dom1 \<inter> ?dom2)) ((?c2) \<circ> (?i1))\<close>)
proof -
  let ?dom_Int = "domain c1 \<inter> domain c2"

  have dom_eq: "?dom1 \<inter> ?dom2 = {(p,v). p \<in> domain c1 \<and> p \<in> domain c2 \<and> v \<in> tangent_space p}"
    unfolding domain_TM_def by auto
  have open_Int_dom[simp]: "open (domain c1 \<inter> domain c2)" by blast
  have open_image_dom_TM[simp]: "open (apply_chart_TM c1 ` (domain_TM c1 \<inter> domain_TM c2))"
    using assms open_intersection_TM by blast
  have inv_chart_x_in: "(inv_chart c1 x) \<in> domain c1 \<inter> domain c2"
      if "x \<in> c1 ` (domain c1 \<inter> domain c2)" for x
    using that by force

  let ?snd_c2i1 = "\<lambda>(p, v). c_manifold_point.tangent_chart_fun charts \<infinity> c2 (inv_chart c1 p)
                        (c_manifold_point.coordinate_vector charts \<infinity> c1 (inv_chart c1 p) v)"

  let ?R1i = "restrict_inv_chart_TM (domain c1 \<inter> domain c2) c1"
    and ?R1 = "restrict_chart_TM (domain c1 \<inter> domain c2) c1"
    and ?R2 = "restrict_chart_TM (domain c1 \<inter> domain c2) c2"
    and ?r1 = "restrict_chart ?dom_Int c1"
    and ?r2 = "restrict_chart ?dom_Int c2"
    and ?r1i = "inv_chart (restrict_chart ?dom_Int c1)"
    and ?r2i = "inv_chart (restrict_chart ?dom_Int c2)"

  show ?thesis
  proof (subst restrict_chart_domain_Int[OF assms(1)], subst image_restrict_domain_TM_eq[OF assms(1)], rule smooth_on_cong)
    fix x assume x: "x \<in> restrict_codomain_TM (domain c1 \<inter> domain c2) c1"
    then have y: "(?R1i x) \<in> restrict_domain_TM (domain c1 \<inter> domain c2) c2"
      using inv_image_restrict_codomain_TM_eq[OF assms(1)]
      using restrict_domain_TM_intersection restrict_domain_TM_intersection'
      by blast
    show "(apply_chart_TM c2 \<circ> inv_chart_TM c1) x = (?R2 \<circ> ?R1i) x"
      using inverse_restrict_chart_TM apply_restrict_chart_TM open_Int_dom x y assms(1,2) by simp
  next
    show open_restrict_codomain[simp]: "open (restrict_codomain_TM (domain c1 \<inter> domain c2) c1)"
      by (simp add: image_restrict_domain_TM_eq[OF assms(1), symmetric] restrict_chart_domain_Int[OF assms(1), symmetric])
    show "smooth_on (restrict_codomain_TM (domain c1 \<inter> domain c2) c1) (?R2 \<circ> ?R1i)"
    proof (rule smooth_on_Pair'[OF open_restrict_codomain])
      have fst_eq: "fst \<circ> (?R2 \<circ> ?R1i) = ?r2 \<circ> ?r1i \<circ> fst"
        unfolding restrict_chart_TM_def restrict_inv_chart_TM_def apply_chart_TM_def inv_chart_TM_def by auto
      show "smooth_on (restrict_codomain_TM (domain c1 \<inter> domain c2) c1) (fst \<circ> (?R2 \<circ> ?R1i))"
        apply (simp add: fst_eq)
        apply (rule smooth_on_compose[of _ "c1 ` (domain c1 \<inter> domain c2)"])
        subgoal using atlas_is_atlas assms smooth_compat_D1 by blast
        subgoal by (auto intro: smooth_on_fst)
        subgoal by simp
        subgoal by simp
        subgoal unfolding restrict_codomain_TM_def codomain_TM_alt using image_domain_eq by fastforce
        done

      let ?g = "\<lambda>x. (\<Sum>i\<in>Basis. (frechet_derivative ((\<lambda>y. (?r2 y) \<bullet> i) \<circ> ?r1i) (at (fst x)) (snd x)) *\<^sub>R i)"

      have local_simps: "?r2 \<circ> ?r1i = (\<lambda>x. ?r2 (?r1i x))"
          and [simp]: "domain c2 \<inter> (domain c1 \<inter> domain c2) = domain c1 \<inter> domain c2"
        by auto
      have r2_r1i_differentiable: "(\<lambda>x. ?r2 (?r1i x) \<bullet> i) differentiable (at (?r1 p))" if "p \<in> ?dom_Int" for i::'b and p
        apply (rule differentiable_compose[of "\<lambda>x. x \<bullet> i"], simp)
        apply (subst local_simps(1)[symmetric])
        apply (rule c_manifold.diff_fun_differentiable_at[of "charts_submanifold ?dom_Int" \<infinity>])
        subgoal using atlas_is_atlas charts_submanifold_def in_charts_in_atlas restrict_chart_in_atlas by unfold_locales (auto)
        subgoal unfolding diff_fun_def using diff_apply_chart[of ?r2] assms(2) restrict_chart_in_atlas by simp
        subgoal using restrict_chart_in_atlas[OF assms(1)] c_manifold_local.sub_\<psi>
          by (metis c_manifold_point.axioms(1)[OF c_manifold_point] domain_restrict_chart inf.left_idem open_Int_dom that)
        using that by auto
      have r2p_deriv: "frechet_derivative (\<lambda>x. - (?r2 p) \<bullet> i) (at (?r1 p)) = 0"for i::'b and p by auto
      hence r2p_differentiable: "(\<lambda>x. - (?r2 p) \<bullet> i) differentiable (at (?r1 p))" for i::'b and p by simp

      show "smooth_on (restrict_codomain_TM (domain c1 \<inter> domain c2) c1) (snd \<circ> (?R2 \<circ> ?R1i))"
      proof (rule smooth_on_cong[of _ _ ?g, OF _ open_restrict_codomain])
        fix x assume x: "x \<in> restrict_codomain_TM (domain c1 \<inter> domain c2) c1"
        then obtain x\<^sub>p x\<^sub>v where Pair_x: "x = (x\<^sub>p,x\<^sub>v)" and x\<^sub>p: "x\<^sub>p \<in> codomain c1" "x\<^sub>p \<in> inv_chart c1 -` ?dom_Int"
          unfolding restrict_codomain_TM_def codomain_TM_alt
          using codomain_restrict_chart[OF open_Int_dom, of c1] by blast

        obtain p where p_def: "p = inv_chart ?r1 x\<^sub>p" and p[simp]: "p \<in> ?dom_Int"
          using x\<^sub>p(2) by auto

        interpret p1: c_manifold_point charts \<infinity> ?r1 p
          using x\<^sub>p(2) by (auto intro!: c_manifold_point simp add: restrict_chart_in_atlas assms(1) p_def)
        interpret p2: c_manifold_point charts \<infinity> ?r2 p
          using x\<^sub>p(2) by (auto intro!: c_manifold_point simp add: restrict_chart_in_atlas assms(2) p_def)

        let ?v = "p1.coordinate_vector x\<^sub>v"
        obtain v where v_def: "v = p1.coordinate_vector x\<^sub>v" and v[simp]: "v \<in> tangent_space p"
          using p1.coordinate_vector_surj by blast

        have pvx: "?R1 (p,v) = x"
          using Pair_x x\<^sub>p(1) p1.tangent_chart_fun_inverse(2)
          by (auto simp: p_def v_def restrict_chart_TM_def apply_chart_TM_def)

        have p1_coord_in_Tp2M: "p1.coordinate_vector x\<^sub>v \<in> p2.T\<^sub>pM"
          using v v_def by auto

        have diff_fun_spaces_eq[simp]:  "p2.sub_\<psi>.sub.diff_fun_space = p1.sub_\<psi>.sub.diff_fun_space"
          unfolding p2.sub_\<psi>.sub.diff_fun_space_def p1.sub_\<psi>.sub.diff_fun_space_def by simp
        have TpU_eq[simp]: "p2.T\<^sub>pU = p1.T\<^sub>pU"
          unfolding p2.sub_\<psi>.sub.tangent_space_def p1.sub_\<psi>.sub.tangent_space_def by simp
        have sub_carriers_eq[simp]: "p2.sub_\<psi>.sub.carrier = p1.sub_\<psi>.sub.carrier"
          unfolding p2.sub_\<psi>.sub.carrier_def p1.sub_\<psi>.sub.carrier_def by simp

        have in_diff_fun_space: "restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i) \<in> p1.sub_\<psi>.sub.diff_fun_space"
          for i::'b
        proof -
          have "diff_fun \<infinity> (charts_submanifold ?dom_Int) (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)"
          proof (rule diff_fun.diff_fun_cong)
            show "diff_fun \<infinity> (charts_submanifold ?dom_Int) ((\<lambda>x. x \<bullet> i) \<circ> ((\<lambda>x. (x - ?r2 p)) \<circ> ?r2))"
            proof (intro diff_fun_compose diff_compose)
          \<comment> \<open>This result could easily be an instance of an axiom of Lie groups.
              However, I think it may be harder to start from differentiability of a binary
              operation on the product manifold than it is to just use composition
              of basic smooth operations.\<close>
              have eucl_diff_add_uminus: "diff \<infinity> charts_eucl charts_eucl (\<lambda>y. y + - x)"
                if x: "x \<in> manifold_eucl.carrier" for x::'b
                apply (intro diff_fun_charts_euclI[unfolded diff_fun_def])
                using smooth_on_add[OF smooth_on_id smooth_on_const[of \<infinity> UNIV "-x"]] open_UNIV by simp
              show "diff \<infinity> (charts_submanifold ?dom_Int) (manifold_eucl.dest.charts_submanifold (codomain ?r2)) ?r2"
                using p2.diffeo_\<psi>.diff_axioms by auto
              show "diff \<infinity> (manifold_eucl.dest.charts_submanifold (codomain ?r2)) charts_eucl (\<lambda>x. x - ?r2 p)"
                using eucl_diff_add_uminus[of "?r2 p"] diff.diff_submanifold p2.sub_eucl.open_submanifold by auto
              show "diff_fun \<infinity> charts_eucl (\<lambda>x. x \<bullet> i)"
                using smooth_on_inner_const by (simp add: diff_fun_charts_euclI)
            qed
          qed (simp)
          moreover have "(?r2 x - ?r2 p) \<bullet> i = (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)) x"
            if "x \<in> manifold.carrier (charts_submanifold ?dom_Int)" for x
            using p1.sub_\<psi>_carrier that by auto
          ultimately show ?thesis
            using p1.sub_\<psi>.sub.restrict0_in_fun_space p2.sub_\<psi>_carrier by auto
        qed

        have p2_comp_p1_coord_x\<^sub>v: "p2.component_function (p1.coordinate_vector x\<^sub>v) i =
            frechet_derivative ((\<lambda>y. (?r2 y) \<bullet> i) \<circ> ?r1i) (at (?r1 p)) x\<^sub>v" for i::'b
        proof -
          have 1: "p2.component_function (p1.coordinate_vector x\<^sub>v) i =
              (p1.differential_inv_chart (p1.dRestr (directional_derivative \<infinity> (?r1 p) x\<^sub>v))) (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
          proof -
            have "p2.component_function (p1.coordinate_vector x\<^sub>v) i =
                  p2.dRestr2 (p1.coordinate_vector x\<^sub>v) (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
              using p2.component_function_apply_in_T\<^sub>pM[OF p1_coord_in_Tp2M]
              by (simp add: Int_absorb1)
            also have "\<dots> = p1.dRestr2 (p1.coordinate_vector x\<^sub>v) (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
              unfolding the_inv_into_def by simp
            also have "\<dots> = (p1.differential_inv_chart (p1.dRestr (directional_derivative \<infinity> (?r1 p) x\<^sub>v)))
                (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
              using the_inv_into_f_f[OF bij_betw_imp_inj_on[OF p1.tangent_submanifold_isomorphism(1)]]
              using bij_betwE[OF p1.bij_betw_d\<psi>_inv] bij_betwE[OF p1.bij_betw_d\<kappa>_inv] p1_coord_in_Tp2M
              by (auto simp: p1.coordinate_vector_apply)
            finally show ?thesis .
          qed
          also have "\<dots> = frechet_derivative (restrict0 p1.diffeo_\<psi>.dest.carrier ((restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)) \<circ> ?r1i)) (at (?r1 p)) x\<^sub>v"
          proof -
            have "\<dots> = (p1.differential_inv_chart (restrict0 (p1.diffeo_\<psi>.dest.diff_fun_space) (\<lambda>f. frechet_derivative f (at (?r1 p)) x\<^sub>v)))
                (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
              using p1.d\<kappa>_inv_directional_derivative_eq by simp
            also have "\<dots> = (\<lambda>g. restrict0 p1.diffeo_\<psi>.dest.diff_fun_space (\<lambda>f. frechet_derivative f (at (?r1 p)) x\<^sub>v)
                (restrict0 p1.diffeo_\<psi>.dest.carrier (g \<circ> ?r1i)))
              (restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i))"
              unfolding p1.diffeo_\<psi>.inv.push_forward_def using in_diff_fun_space by simp
            also have "\<dots> = (\<lambda>f. frechet_derivative f (at (?r1 p)) x\<^sub>v)
                (restrict0 p1.diffeo_\<psi>.dest.carrier ((restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)) \<circ> ?r1i))"
              using in_diff_fun_space p1.diffeo_\<psi>.inv.restrict_compose_in_diff_fun_space by auto
            finally show ?thesis by simp
          qed
          also have "\<dots> = frechet_derivative ((\<lambda>x. (?r2 x) \<bullet> i) \<circ> ?r1i) (at (?r1 p)) x\<^sub>v"
          proof -
            let ?X = "p1.diffeo_\<psi>.dest.carrier"
            have X_eq_codomain_r1[simp]: "p1.diffeo_\<psi>.dest.carrier = codomain ?r1"
              using chart_eucl_simps(1) manifold.carrier_def
              by (metis (no_types, lifting) Int_UNIV_right Int_commute ccpo_Sup_singleton
                  image_insert image_is_empty p1.sub_eucl.carrier_submanifold)
            have 1: "frechet_derivative (restrict0 p1.diffeo_\<psi>.dest.carrier ((restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)) \<circ> ?r1i)) (at (?r1 p)) =
                frechet_derivative ((\<lambda>x. (?r2 x - ?r2 p) \<bullet> i) \<circ> ?r1i) (at (?r1 p))"
                (is \<open>frechet_derivative ?f\<^sub>L (at _) = frechet_derivative ?f\<^sub>R (at _)\<close>)
            proof (rule frechet_derivative_transform_within_open)
              show "?f\<^sub>L x = ?f\<^sub>R x" if "x\<in>?X" for x
                using X_eq_codomain_r1 that by simp
              show "open ?X" by blast
              show "?r1 p \<in> ?X" using p1.\<psi>p_in by blast
              let ?f\<^sub>L' = "(restrict0 ?dom_Int (\<lambda>x. (?r2 x - ?r2 p) \<bullet> i)) \<circ> ?r1i"
              show "?f\<^sub>L differentiable at (?r1 p)"
                apply (rule differentiable_transform_within_open[of ?f\<^sub>L' _ _ ?X])
                apply (rule p1.sub_\<psi>.sub_diff_fun_differentiable_at)
                using p1.\<psi>p_in p1.diffeo_\<psi>.dest.open_carrier in_diff_fun_space p1.sub_\<psi> p1.p p1.sub_\<psi>.sub.diff_fun_spaceD by auto
            qed
            also have 2: "\<dots> = frechet_derivative ((\<lambda>x. (?r2 x) \<bullet> i) \<circ> ?r1i) (at (?r1 p))"
            proof -
              have "frechet_derivative ((\<lambda>x. (?r2 x - ?r2 p) \<bullet> i) \<circ> ?r1i) (at (?r1 p)) =
                         frechet_derivative ((\<lambda>x. ?r2 (?r1i x) \<bullet> i) + (\<lambda>x. - (?r2 p) \<bullet> i)) (at (?r1 p))"
                by (simp add: plus_fun_def inner_diff_left) (meson comp_apply)
              also have "\<dots> = frechet_derivative (\<lambda>x. ?r2 (?r1i x) \<bullet> i) (at (?r1 p)) + (frechet_derivative (\<lambda>x. - (?r2 p) \<bullet> i) (at (?r1 p)))"
                  using r2_r1i_differentiable[OF p] r2p_differentiable by (auto simp: frechet_derivative_plus_fun)
              finally show "frechet_derivative ((\<lambda>x. (?r2 x - ?r2 p) \<bullet> i) \<circ> ?r1i) (at (?r1 p)) =
                  frechet_derivative ((\<lambda>x. ?r2 x \<bullet> i) \<circ> ?r1i) (at (?r1 p))"
              using r2p_deriv by simp (metis comp_apply)
            qed
            finally show ?thesis using 1 by presburger
          qed
          finally show "p2.component_function (p1.coordinate_vector x\<^sub>v) i = frechet_derivative ((\<lambda>x. (?r2 x) \<bullet> i) \<circ> ?r1i) (at (?r1 p)) x\<^sub>v" .
        qed

        have "(snd \<circ> (?R2 \<circ> ?R1i)) x = (p2.tangent_chart_fun \<circ> p1.coordinate_vector) x\<^sub>v"
          unfolding restrict_chart_TM_def restrict_inv_chart_TM_def
          unfolding apply_chart_TM_def inv_chart_TM_def by (simp add: Pair_x p_def)
        then show "(snd \<circ> (?R2 \<circ> ?R1i)) x = ?g x"
          unfolding p2.tangent_chart_fun_def using p2_comp_p1_coord_x\<^sub>v p_def p Pair_x x\<^sub>p(1) by auto
      next
        let ?D = "restrict_codomain_TM (domain c1 \<inter> domain c2) c1"
        show "smooth_on ?D ?g"
        proof (rule smooth_on_sum, rule smooth_on_scaleR)
          fix i::'b assume i: "i\<in>Basis"
          have D_product: "?D = c1 ` (domain c1 \<inter> domain c2) \<times> UNIV"
            unfolding restrict_codomain_TM_def codomain_TM_def
            by auto (metis IntI chart_inverse_inv_chart imageI inv_chart_in_domain)
          show "smooth_on ?D (\<lambda>x. frechet_derivative ((\<lambda>y. (?r2 y) \<bullet> i) \<circ> ?r1i) (at (fst x)) (snd x))"
            unfolding D_product by (rule smooth_on_compat_charts_TM[OF assms])
        qed (auto)
      qed
    qed
  qed
qed

lemma atlas_TM':
  assumes "c1 \<in> atlas" "c2 \<in> atlas"
  shows "smooth_on ((apply_chart_TM c2) ` (domain_TM c1 \<inter> domain_TM c2)) ((apply_chart_TM c1) \<circ> (inv_chart_TM c2))"
  using atlas_TM[OF assms(2,1)] by (simp add: Int_commute)

end


subsubsection \<open>Differentiability of vector fields\<close>
context c_manifold begin

abbreviation k_diff_from_M_to_TM_at_in :: "enat \<Rightarrow> 'a \<Rightarrow> ('a,'b)chart \<Rightarrow> ('a \<Rightarrow> 'a tangent_bundle) \<Rightarrow> bool"
  where "k_diff_from_M_to_TM_at_in k' x c X  \<equiv> x \<in> domain c \<and> X ` domain c \<subseteq> domain_TM c \<and> k'-smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c)"

\<comment> \<open>Compare this definition to @{thm diff_axioms_def}. It's the same, except the charts for TM
  aren't of type \<^typ>\<open>('a,'b)chart\<close>.\<close>
definition k_diff_from_M_to_TM (\<open>_-diff'_from'_M'_to'_TM\<close> [1000])
  where diff_from_M_to_TM_def: "k'-diff_from_M_to_TM X \<equiv> \<forall>x. x \<in> carrier \<longrightarrow>
    (\<exists>c\<in>atlas. k_diff_from_M_to_TM_at_in k' x c X)"

abbreviation "continuous_from_M_to_TM \<equiv> 0-diff_from_M_to_TM"
abbreviation (in smooth_manifold) "smooth_from_M_to_TM \<equiv> k_diff_from_M_to_TM \<infinity>"

lemma diff_from_M_to_TM_E:
  assumes "k'-diff_from_M_to_TM X" "x \<in> carrier"
  obtains c where "c\<in>atlas" "x \<in> domain c" "X ` domain c \<subseteq> domain_TM c" "k'-smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
  using assms unfolding diff_from_M_to_TM_def by auto

lemma continuous_from_M_to_TM_D:
  assumes "continuous_from_M_to_TM X" "x \<in> carrier"
  obtains c where "c\<in>atlas" "x \<in> domain c" "X ` domain c \<subseteq> domain_TM c" "continuous_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
  using assms by (meson diff_from_M_to_TM_E smooth_on_imp_continuous_on that)

definition section_of_TM_def: "section_of_TM_on S X \<equiv> \<forall>p\<in>S. (X p) \<in> TM \<and> fst (X p) = p"

abbreviation "section_of_TM \<equiv> section_of_TM_on carrier"

lemma section_of_TM_subset:
  assumes "section_of_TM_on S X" "T \<subseteq> S"
  shows "section_of_TM_on T X"
  using assms unfolding section_of_TM_def by force

lemma section_domain_TM:
  assumes "section_of_TM_on (domain c) X"
  shows "X ` domain c \<subseteq> domain_TM c"
  using assms unfolding domain_TM_def section_of_TM_def in_TM_def by auto

lemma section_domain_TM':
  assumes "section_of_TM X" "c \<in> atlas"
  shows "X ` domain c \<subseteq> domain_TM c"
  using assms section_domain_TM section_of_TM_subset by blast

lemma section_vimage_domain_TM:
  assumes "section_of_TM X" "c\<in>atlas"
  shows "carrier \<inter> X -` domain_TM c = domain c"
  using assms unfolding domain_TM_def section_of_TM_def in_TM_def
  by simp force

end


context smooth_manifold begin

text \<open>Show that a smooth/differentiable vector field is smooth in any chart.
  This would be @{thm diff.diff_chartsD} if we could write $TM$ as a \<^locale>\<open>c_manifold\<close>;
  it relies on the compatibility of charts for $TM$ given in @{thm smooth_manifold.atlas_TM}.\<close>
lemma diff_from_M_to_TM_chartsD:
  assumes X: "k_diff_from_M_to_TM k' X" "section_of_TM X" and c: "c \<in> atlas"
  shows "k'-smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
proof -
  have codom_simp: "codomain c \<inter> inv_chart c -` (carrier \<inter> X -` domain_TM c) = codomain c"
    using section_vimage_domain_TM[OF X(2) c] by (simp add: Int_absorb2 subset_vimage_iff)
  { fix y assume "y \<in> codomain c \<inter> inv_chart c -` (carrier \<inter> X -` domain_TM c)"
    then have y: "X (inv_chart c y) \<in> domain_TM c" "y \<in> codomain c"
      by auto
    then obtain x where x: "c x = y" "x \<in> domain c"
      by force
    then have "x \<in> carrier" using assms by force
    obtain c1 where "c1 \<in> atlas"
      and fc1: "X ` domain c1 \<subseteq> domain_TM c1"
      and xc1: "x \<in> domain c1"
      and d: "k'-smooth_on (codomain c1) (apply_chart_TM c1 \<circ> X \<circ> inv_chart c1)"
      by (meson \<open>x \<in> carrier\<close> assms(1) diff_from_M_to_TM_E)
    have fc1' [simp]: "x \<in> domain c1 \<Longrightarrow> X x \<in> domain_TM c1" for x using fc1 by auto
    have r1: "k'-smooth_on (c ` (domain c \<inter> domain c1)) (c1 \<circ> inv_chart c)"
      using smooth_compat_D1[OF smooth_compat_le[OF atlas_is_atlas[OF c \<open>c1 \<in> atlas\<close>]]] by force
    \<comment> \<open>Important: this is where we use @{thm smooth_manifold.atlas_TM}.\<close>
    have r2: "k'-smooth_on (apply_chart_TM c1 ` (domain_TM c \<inter> domain_TM c1)) (apply_chart_TM c \<circ> inv_chart_TM c1)"
      apply (rule smooth_on_le[OF atlas_TM'[OF c \<open>c1 \<in> atlas\<close>]]) by simp
  
    define T where "T = c ` (domain c \<inter> domain c1)  \<inter>  inv_chart c -` (carrier \<inter> (X -` domain_TM c))"
  
    have simps_1: "(apply_chart_TM c1 \<circ> X \<circ> inv_chart c1) ` (apply_chart c1 \<circ> inv_chart c) ` T = (apply_chart_TM c1 \<circ> X \<circ> inv_chart c) ` T"
      if "inv_chart c ` T \<subseteq> domain c1" for T
      unfolding image_comp[symmetric] using that by auto
        (smt (verit) image_eqI image_subset_iff inv_chart_inverse)
    have "inv_chart c ` T \<subseteq> domain c1"
      by (auto simp: T_def)
    note T_simps = simps_1[OF this] section_vimage_domain_TM[OF X(2) c]
    have "open T"
      by (auto intro!: open_continuous_vimage' continuous_intros simp: T_simps(2) T_def)
  
    have T_subset: "T \<subseteq> apply_chart c ` (domain c \<inter> domain c1)"
      by (auto simp: T_def)
    have opens: "open (c1 ` inv_chart c ` T)" "open (apply_chart_TM c1 ` (domain_TM c \<inter> domain_TM c1))"
      using T_subset fc1 \<open>open T\<close>\<open>inv_chart c ` T \<subseteq> domain c1\<close> apply blast
      by (metis Int_commute \<open>c1 \<in> atlas\<close> open_intersection_TM)
    have "k'-smooth_on ((apply_chart c1 \<circ> inv_chart c) ` T) (apply_chart_TM c \<circ> inv_chart_TM c1 \<circ> (apply_chart_TM c1 \<circ> X \<circ> inv_chart c1))"
      using r2 d opens unfolding image_comp[symmetric] apply (rule smooth_on_compose2)
      by (auto simp: T_def) (metis IntI fc1 image_subset_iff subset_refl)
    from this r1 \<open>open T\<close> opens(1) have "k'-smooth_on T
        ((apply_chart_TM c \<circ> inv_chart_TM c1) \<circ> (apply_chart_TM c1 \<circ> X \<circ> inv_chart c1) \<circ> (c1 \<circ> inv_chart c))"
      unfolding image_comp[symmetric]
      by (rule smooth_on_compose2) (force simp: T_def)+
    then have "k'-smooth_on T (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
      using \<open>open T\<close> apply (rule smooth_on_cong)
      using apply_chart_TM_inverse(1)[of c1 "fst (X xa)" "snd (X xa)" for xa] fc1' \<open>c1 \<in> atlas\<close>
      by (auto simp: T_def)
    moreover have "y \<in> T"
      using x xc1 fc1 y \<open>c1 \<in> atlas\<close> by (auto simp: T_def)
    ultimately have "\<exists>T. y \<in> T \<and> open T \<and> k'-smooth_on T (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
      using \<open>open T\<close> by metis }
  thus ?thesis
    apply (rule smooth_on_open_subsetsI)
    using codom_simp by simp
qed


definition "smooth_section_of_TM X \<equiv> section_of_TM X \<and> smooth_from_M_to_TM X"

abbreviation set_of_smooth_sections_of_TM (\<open>\<XX>\<close>)
  where "set_of_smooth_sections_of_TM \<equiv> {X. smooth_section_of_TM X}"

lemma in\<XX>_E:
  assumes "X \<in> \<XX>" "p\<in>carrier"
  shows "(\<exists>c\<in>atlas. p \<in> domain c \<and> X ` domain c \<subseteq> domain_TM c \<and> smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c))"
    and "snd (X p) \<in> tangent_space p"
    and "fst (X p) = p"
  using assms TM_E[of "X p" for p]
  by (auto simp: smooth_section_of_TM_def section_of_TM_def diff_from_M_to_TM_def) (metis)

lemma in\<XX>_chartsD:
  assumes "X \<in> \<XX>" "c\<in>atlas"
  shows "smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c)"
  using diff_from_M_to_TM_chartsD[of \<infinity> X c] assms smooth_section_of_TM_def by auto

end


text \<open>A vector field is smooth if it is smooth as a map $M \to TM$. As a shortcut, we define a
  smooth vector field as one that is smooth in the chart - this avoids problems with defining
  a \<^typ>\<open>('a \<times> (('a \<Rightarrow> real) \<Rightarrow> real), 'b) chart\<close>. We also introduce a duality of
  predicates with strongly related meaning: this allows us to consider vector fields as either
  maps \<^typ>\<open>'a \<Rightarrow> (('a\<Rightarrow>real)\<Rightarrow>real)\<close>, i.e. mapping a point to a vector; or
  maps \<^typ>\<open>'a \<Rightarrow> ('a \<times> (('a\<Rightarrow>real)\<Rightarrow>real))\<close>, i.e. sections of $TM$ properly speaking.\<close>

context c_manifold begin

definition rough_vector_field :: "'a vector_field \<Rightarrow> bool"
  where "rough_vector_field X \<equiv> extensional0 carrier X \<and> (\<forall>p\<in>carrier. X p \<in> tangent_space p)"

lemma rough_vector_fieldE [elim]:
  assumes "rough_vector_field X"
  shows "\<And>p. X p \<in> tangent_space p" "extensional0 carrier X"
  using assms by (auto simp: rough_vector_field_def extensional0_outside tangent_space.mem_zero)

lemma rough_vector_field_subset:
  assumes "rough_vector_field X" "T \<subseteq> carrier"
  shows "rough_vector_field (restrict0 T X)"
  unfolding rough_vector_field_def using assms rough_vector_fieldE tangent_space.mem_zero
  by (metis (no_types, lifting) extensional0_def restrict0_def)

end (* c_manifold *)



abbreviation (input) vec_field_apply_fun :: "'a vector_field \<Rightarrow> ('a\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real)" (infix \<open>\<hungarumlaut>\<close> 100)
  where "vec_field_apply_fun X f \<equiv> \<lambda>p. X p f"

lemma (in c_manifold) vec_field_apply_fun_cong:
  assumes X: "rough_vector_field X" and U: "open U" "U \<subseteq> carrier" "\<forall>x\<in>U. f x = g x"
    and f: "f \<in> diff_fun_space" and g: "g \<in> diff_fun_space"
  shows "\<forall>p\<in>U. X p f = X p g"
  using assms by (auto intro: derivation_eq_localI simp: rough_vector_field_def)

lemma (in c_manifold) ext0_vec_field_apply_fun:
  assumes X: "rough_vector_field X"
  shows "extensional0 diff_fun_space (vec_field_apply_fun X)"
  using rough_vector_fieldE[OF X] unfolding tangent_space_def extensional0_def by fastforce


subsection \<open>Smoothness criterion for a vector field in a single chart.\<close>

text \<open>A smooth vector field is one that is infinitely differentiable when expanded in the
  charting Euclidean space using @{thm c_manifold_point.coordinate_vector_representation}.
  This should be the chart that makes each tangent space into a manifold anyway,
  but the type constraints are tricky to satisfy.\<close>
text \<open>Since tangent spaces at the same point differ between a manifold and a submanifold,
  it's important to note that the differentiability condition can be relaxed to only apply to a
  subset, but the tangent bundle is always the disjoint union of tangent spaces of the
  \emph{entire} manifold, which implies the chart function for the tangent space
  is defined in the entire manifold, not a submanifold.\<close>

locale smooth_vector_field_local = c_manifold_local charts \<infinity> \<psi> for charts \<psi> +
  fixes X
  assumes vector_field: "\<forall>p\<in>domain \<psi>. X p \<in> tangent_space p"
    and smooth_in_chart: "diff_fun \<infinity> (charts_submanifold (domain \<psi>)) (\<lambda>p. (c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p) (X p))"
begin
lemma rough_vector_field: "rough_vector_field (restrict0 (domain \<psi>) X)"
  apply (simp only: rough_vector_field_def, intro conjI)
  using extensional0_def sub_\<psi>_carrier apply fastforce
  using vector_field by (metis restrict0_apply_in restrict0_apply_out tangent_space.mem_zero)
end


subsubsection \<open>Connecting the types \<^typ>\<open>'a \<Rightarrow> ('a\<Rightarrow>real)\<Rightarrow>real\<close> (used for \<^term>\<open>smooth_vector_field_local\<close>)
  and \<^typ>\<open>'a \<Rightarrow> 'a\<times>(('a\<Rightarrow>real)\<Rightarrow>real)\<close> (used for \<^term>\<open>c_manifold.section_of_TM\<close>).\<close>
context c_manifold begin

lemma fst_apply_chart_TM_id [simp]: "(fst \<circ> (apply_chart_TM \<psi> \<circ> X \<circ> inv_chart \<psi>)) x = x"
  if "section_of_TM_on (domain \<psi>) X" "\<psi>\<in>atlas" "x\<in>codomain \<psi>" for x
  using that by (simp add: case_prod_beta' apply_chart_TM_def section_of_TM_def)

text \<open>The justification for the definition of \<^locale>\<open>smooth_vector_field_local\<close> is the lemma below,
  connecting it to the smoothness requirement used to define the set of smooth sections \<^term>\<open>\<XX>\<close>.\<close>
lemma apply_chart_TM_chartX:
  fixes X :: "('a \<Rightarrow> 'a \<times> (('a \<Rightarrow> real) \<Rightarrow> real))" and c :: "('a, 'b) chart" and chart_X :: "'a \<Rightarrow> 'b"
  defines "chart_X \<equiv> \<lambda>p. (c_manifold_point.tangent_chart_fun charts \<infinity> c p) (snd (X p))"
  assumes k: "k=\<infinity>" and X: "section_of_TM_on (domain c) X" and c: "c \<in> atlas"
  shows "smooth_on (codomain c) (apply_chart_TM c \<circ> X \<circ> inv_chart c) \<longleftrightarrow> diff_fun \<infinity> (charts_submanifold (domain c)) chart_X"
    (is \<open>?smooth_in_chart_TM c X \<longleftrightarrow> ?diff_domain c chart_X\<close>)
proof -

  interpret c: c_manifold_local charts \<infinity> c
    using k c pairwise_compat by unfold_locales simp_all
  have p: "c_manifold_point charts \<infinity> c p" if "p\<in>domain c" for p
    using that by unfold_locales simp
  have X_in_TM: "fst (X p) = p" "snd (X p) \<in> tangent_space p" if "p\<in>domain c" for p
    using that X c.\<psi> in_TM_E(1) by (auto simp: section_of_TM_def)
  have chart_X_alt: "chart_X p = (snd \<circ> (c.apply_chart_TM c \<circ> X)) p" if "p \<in> domain c" for p
    by (simp add: that chart_X_def c.apply_chart_TM_def X_in_TM(1) split_beta)
  have smooth_comp_snd: "smooth_on (codomain c) (snd\<circ>f)" if "smooth_on (codomain c) f" for f :: "'b \<Rightarrow> 'b\<times>'b"
    using open_codomain that by (auto intro!: smooth_on_snd simp: comp_def)
  have c_in_sub_atlas: "c \<in> c.sub_\<psi>.sub.atlas"
    by (metis c.\<psi> c.atlas_is_atlas c.sub_\<psi>.sub.maximal_atlas c.sub_\<psi>.submanifold_atlasE c.sub_\<psi>_carrier set_eq_subset)

  show ?thesis
  proof

    assume asm: "?smooth_in_chart_TM c X"
    have 1: "smooth_on (codomain c) (snd \<circ> (c.apply_chart_TM c \<circ> X \<circ> inv_chart c))"
      using smooth_comp_snd[OF asm] by (simp only: comp_assoc)
    have 2: "smooth_on (codomain c) ((\<lambda>x. x) \<circ> chart_X \<circ> inv_chart c)"
      by (auto intro!: smooth_on_cong[OF 1] simp: chart_X_alt)
    {
      fix x assume "x \<in> domain c"
      then interpret x: c_manifold_point charts \<infinity> c x using p by blast
      have "\<exists>c1 \<in> c.sub_\<psi>.sub.atlas. \<exists>c2 \<in> manifold_eucl.atlas \<infinity>.
          x \<in> domain c1 \<and> chart_X ` domain c1 \<subseteq> domain c2 \<and>
          smooth_on (codomain c1) (apply_chart c2 \<circ> chart_X \<circ> inv_chart c1)"
        using 2 c_in_sub_atlas by (intro bexI) auto
    }

    then show "?diff_domain c chart_X"
      unfolding diff_fun_def diff_def diff_axioms_def
      using c.sub_\<psi>.sub.manifold_eucl.c_manifolds_axioms c.sub_\<psi>_carrier by blast
  next

    assume asm: "?diff_domain c chart_X"
    interpret asm_df: diff_fun \<infinity> "charts_submanifold (domain c)" "snd \<circ> (c.apply_chart_TM c \<circ> X)"
      using diff_fun.diff_fun_cong[OF asm chart_X_alt] by fastforce
    have codomain_c_eq: "codomain c = codomain c \<inter> inv_chart c -` (c.sub_\<psi>.sub.carrier \<inter> (snd \<circ> (c.apply_chart_TM c \<circ> X)) -` domain chart_eucl)"
      using c.\<psi> by (simp, blast)
    let ?X = "(c.apply_chart_TM c \<circ> X \<circ> inv_chart c)"
    let ?X' = "\<lambda>x. (x, (snd\<circ>?X) x)"
    have X_eq: "?X x = ?X' x" if "x\<in>codomain c" for x
      using c.fst_apply_chart_TM_id X k that by (metis c comp_apply prod.collapse)
    have smooth_on_snd_chart_TM: "smooth_on (codomain c) (snd \<circ> ?X)"
      using asm_df.diff_chartsD[OF c_in_sub_atlas, of chart_eucl] codomain_c_eq
      by (auto simp add: comp_assoc smooth_on_cong)

    show "?smooth_in_chart_TM c X"
      apply (rule smooth_on_cong[OF _ _ X_eq])
      using smooth_on_Pair smooth_on_id smooth_on_snd_chart_TM by blast+
    qed
qed

end (* c_manifold *)



context smooth_vector_field_local begin

definition "chart_X \<equiv> \<lambda>p. (c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p) (X p)"

lemma smooth_in_chart_X [simp]: "diff_fun \<infinity> (charts_submanifold (domain \<psi>)) chart_X"
  unfolding chart_X_def using smooth_in_chart by simp

lemma apply_chart_TM_chart_X:
  "smooth_on (codomain \<psi>) (apply_chart_TM \<psi> \<circ> (\<lambda>p. (p, X p)) \<circ> inv_chart \<psi>) \<longleftrightarrow> diff_fun \<infinity> (charts_submanifold (domain \<psi>)) chart_X"
  unfolding chart_X_def
  apply (rule apply_chart_TM_chartX[of \<psi> "\<lambda>p. (p, X p)", simplified])
  unfolding section_of_TM_def in_TM_def apply (clarsimp, intro conjI)
  using \<psi> vector_field by (blast, auto)

end


subsubsection \<open>Some theorems about smooth vector fields, locally and globally.\<close>
context c_manifold_local begin
text \<open>It is often convenient to keep a stronger handle on which chart we're (locally) working in.
  Since the first component of the \<^term>\<open>apply_chart_TM\<close> is just the identity,
  we can safely omit it for a lot of our reasoning about smoothness in a chart
  (see @{thm fst_apply_chart_TM_id} and @{thm apply_chart_TM_chartX}).\<close>

definition vector_field_component :: "('a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real)) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> real"
  where "vector_field_component X i \<equiv> \<lambda>p. (c_manifold_point.component_function charts k \<psi> p) (X p) i"
definition coordinate_vector_field :: "'b \<Rightarrow> ('a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real))"
  where "coordinate_vector_field i p \<equiv> c_manifold_point.coordinate_vector charts k \<psi> p i"


text \<open>Eqn. 8.2, page 175, Lee 2012\<close>
lemma vector_field_local_representation:
  assumes k: "k = \<infinity>" and X: "rough_vector_field X" and p: "p\<in>domain \<psi>"
  shows "X p = (\<Sum>i\<in>Basis. (vector_field_component X i p) *\<^sub>R (coordinate_vector_field i p))"
  unfolding vector_field_component_def coordinate_vector_field_def
  apply (rule c_manifold_point.coordinate_vector_representation)
  apply unfold_locales
  subgoal using p rough_vector_fieldE[OF X] sub_\<psi>_carrier by blast
  subgoal using p rough_vector_fieldE[OF X] in_carrier_atlasI[OF \<psi>] by blast
  by (simp add: k)


definition local_coord_at :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> real"
  where "local_coord_at q i \<equiv> restrict0 (domain \<psi>) (\<lambda>y::'a. (\<psi> y - \<psi> q) \<bullet> i)"

lemma local_coord_diff_fun:
  assumes k: "k=\<infinity>" and q: "q \<in> domain \<psi>"
  shows "local_coord_at q i \<in> sub_\<psi>.sub.diff_fun_space"
proof -
  note local_simps[simp] = local_coord_at_def
  have "diff_fun k (charts_submanifold (domain \<psi>)) ((\<lambda>y::'a. (\<psi> y - \<psi> q) \<bullet> i))"
    apply (rule diff_fun_compose[unfolded o_def, of k _ charts_eucl \<psi>])
    using diff_fun_\<psi>.diff_axioms k by (auto intro!: diff_fun_charts_euclI smooth_on_inner smooth_on_minus)
  from diff_fun.diff_fun_cong[OF this] q
  have "diff_fun k (charts_submanifold (domain \<psi>)) (local_coord_at q i)" by simp
  then show "local_coord_at q i \<in> sub_\<psi>.sub.diff_fun_space"
    by auto (metis restrict0_subset sub_\<psi> sub_\<psi>.sub.domain_atlas_subset_carrier sub_\<psi>.sub.restrict0_in_fun_space)
qed


lemma vector_apply_coord_at:
  fixes x\<^sub>\<psi> defines [simp]: "x\<^sub>\<psi> \<equiv> local_coord_at"
  assumes q: "q\<in>domain \<psi>" and p:"p\<in>domain \<psi>" and X: "X \<in> tangent_space q" and k: "k=\<infinity>"
  shows "(d\<iota>\<inverse> q) X (x\<^sub>\<psi> p i) = (d\<iota>\<inverse> q) X (x\<^sub>\<psi> q i)"
proof -
  note local_simps[simp] = local_coord_at_def
  have diff_x\<^sub>\<psi>i': "x\<^sub>\<psi> q i \<in> sub_\<psi>.sub.diff_fun_space" if "q \<in> domain \<psi>" for i q
    using local_coord_diff_fun[OF k that] by simp
  
  interpret q: c_manifold_point charts k \<psi> q using q \<psi> by unfold_locales simp
  let ?x\<^sub>q = "x\<^sub>\<psi> q"
  have Xq: "q.dRestr2 X \<in> q.T\<^sub>pU"
    using bij_betwE[OF q.bij_betw_d\<iota>_inv] X by simp
  {
    fix x' b assume "x' \<in> domain \<psi>"
    have Dp_simp: "frechet_derivative ((x\<^sub>\<psi> p' i) \<circ> inv_chart \<psi>) (at (\<psi> x')) = frechet_derivative ((\<lambda>y. y \<bullet> i)) (at (\<psi> x'))" for p'
    proof -
      have "frechet_derivative ((x\<^sub>\<psi> p' i) \<circ> inv_chart \<psi>) (at (\<psi> x')) = frechet_derivative ((\<lambda>y. (y - \<psi> p') \<bullet> i)) (at (\<psi> x'))"
        apply (rule frechet_derivative_transform_within_open[OF _ open_codomain[of \<psi>], symmetric])
        by (simp_all add: \<open>x' \<in> domain \<psi>\<close>)
      then show ?thesis
        by (auto simp: algebra_simps zero_fun_def
            intro!: frechet_derivative_at[symmetric] has_derivative_diff[where g'=0, simplified] derivative_intros)
    qed
    have "frechet_derivative ((x\<^sub>\<psi> p i) \<circ> inv_chart \<psi>) (at (\<psi> x')) b = frechet_derivative ((x\<^sub>\<psi> q i) \<circ> inv_chart \<psi>) (at (\<psi> x')) b"
      by (simp only: Dp_simp)
  } note deriv_eq = this
  show ?thesis
    apply (rule sub_\<psi>.sub.derivation_eq_localI'[OF k q _ _ Xq, of \<psi>])
    using local_coord_diff_fun diff_x\<^sub>\<psi>i' k deriv_eq sub_\<psi>
    by (auto simp: p sub_\<psi>.sub.diff_fun_space_def)
qed

end (*c_manifold_local*)


context c_manifold begin

abbreviation (input) "real_linear_on S1 S2 \<equiv> linear_on S1 S2 scaleR scaleR"

\<comment> \<open>Sometimes we want to apply a vector field meaningfully to a function that is in the
  \<^term>\<open>c_manifold.diff_fun_space\<close> of a submanifold (e.g. a single chart). For this to make sense,
  the function has to be in the correct space, and the submanifold's carrier set has to be open.\<close>
definition vec_field_apply_fun_in_at :: "('a vector_field) \<Rightarrow> ('a\<Rightarrow>real) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real"
  where "vec_field_apply_fun_in_at X f U q = restrict0 (tangent_space q)
      (the_inv_into
        (c_manifold.tangent_space (charts_submanifold U) k q)
        (diff.push_forward k (charts_submanifold U) charts (\<lambda>x. x)))
      (X q) f"

abbreviation vec_field_restr :: "('a vector_field) \<Rightarrow> 'a set \<Rightarrow> ('a vector_field)"
  where "vec_field_restr X U q f \<equiv> restrict0 U (vec_field_apply_fun_in_at X f U) q"
notation vec_field_restr (\<open>_\<restriction>_\<close> [60,60])

lemma (in smooth_manifold) vec_field_restr: "(X\<restriction>U) p \<in> c_manifold.tangent_space (charts_submanifold U) \<infinity> p"
  if "open U" "U \<subseteq> carrier" "rough_vector_field X" for U X
proof -
  interpret U: submanifold charts \<infinity> U
    by (unfold_locales, simp add: that)
  have U_simps[simp]: "U.sub.carrier  = U"
    using that by auto
  show ?thesis
    apply (cases "p\<in>U")
    subgoal
      apply (simp add: vec_field_apply_fun_in_at_def)
      using bij_betwE[OF U.bij_betw_d\<iota>_inv] that rough_vector_fieldE(1) by auto
    by (simp add: U.sub.diff_fun_space.linear_zero U.sub.tangent_spaceI extensional0_def)
qed

lemma vec_field_apply_fun_alt':
  assumes "open U" "q\<in>U" "f \<in> c_manifold.diff_fun_space (charts_submanifold U) k" "rough_vector_field X"
  shows "vec_field_apply_fun_in_at X f U q = (the_inv_into (c_manifold.tangent_space (charts_submanifold U) k q) (diff.push_forward k (charts_submanifold U) charts (\<lambda>x. x))) (X q) f"
  using rough_vector_fieldE(1)[OF assms(4)] by (auto simp: vec_field_apply_fun_in_at_def  assms(1-3))

lemma vec_field_apply_fun_alt:
  assumes "open U" "q\<in>U" "f \<in> c_manifold.diff_fun_space (charts_submanifold U) k" "rough_vector_field X"
  shows "vec_field_restr X U q f = (the_inv_into (c_manifold.tangent_space (charts_submanifold U) k q) (diff.push_forward k (charts_submanifold U) charts (\<lambda>x. x))) (X q) f"
  using rough_vector_fieldE(1)[OF assms(4)] by (auto simp: vec_field_apply_fun_in_at_def  assms(1-3))

lemma (in submanifold) vec_field_apply_fun_sub:
  assumes "q\<in>carrier" "q\<in>S" "f \<in> sub.diff_fun_space" "rough_vector_field X"
  shows "vec_field_apply_fun_in_at X f (S\<inter>carrier) q = (the_inv_into (sub.tangent_space q) inclusion.push_forward) (X q) f"
  using assms charts_submanifold_Int_carrier sub.open_carrier vec_field_apply_fun_alt by auto

lemma vec_field_apply_fun_in_open[simp]: "vec_field_apply_fun_in_at X f' U p = X p f"
    if U: "p \<in> U" "open U" "U \<subseteq> carrier"
      and f: "f \<in> diff_fun_space" "f' \<in> c_manifold.diff_fun_space (charts_submanifold U) k" "\<forall>x\<in>U. f x = f' x"
      and X: "rough_vector_field X"
proof -
  interpret U: submanifold charts k U using U(2) by unfold_locales
  show ?thesis
    using U.vec_field_apply_fun_sub[OF subsetD[OF U(3,1)] U(1) f(2) X] U.vector_apply_sub_eq_localI(2)
    using rough_vector_fieldE(1)[OF X] that(1,3-6) by (auto simp: Int_absorb2[OF U(3)] U.open_submanifold)
qed


lemma open_imp_submanifold: "submanifold charts k S" if "open S"
  using that by unfold_locales

lemmas charts_submanifold = submanifold.charts_submanifold[OF open_imp_submanifold]

lemma charts_submanifold_Int:
  "manifold.charts_submanifold (charts_submanifold U) N = charts_submanifold (N \<inter> U)"
  if "open N" "open U"
  using restrict_chart_restrict_chart[OF that] by (auto simp add: image_def manifold.charts_submanifold_def)


lemma vec_field_apply_fun_in_restrict0[simp]:
    "vec_field_restr X U p f = vec_field_restr X N p (restrict0 N f)"
    if U: "open U" "U \<subseteq> carrier" and N: "p\<in>N" "N \<subseteq> U" "open N"
      and f: "f \<in> c_manifold.diff_fun_space (charts_submanifold U) k"
      and X: "rough_vector_field X"
proof -
  let ?f = "restrict0 N f"
  have f_diff_N: "diff_fun k (charts_submanifold N) f"
    using diff_fun.diff_fun_submanifold[OF c_manifold.diff_fun_spaceD[OF charts_submanifold[OF U(1)]], OF f N(3)]
    by (simp only: charts_submanifold_Int[OF N(3) U(1)] Int_absorb2[OF N(2)])
  have f': "?f \<in> c_manifold.diff_fun_space (charts_submanifold N) k"
    unfolding c_manifold.diff_fun_space_def[OF charts_submanifold[OF N(3)]] apply (safe, rule diff_fun.diff_fun_cong)
    using f_diff_N submanifold.carrier_submanifold[OF open_imp_submanifold[OF N(3)]]
    by (auto simp: Int_absorb2[OF subset_trans, OF N(2) U(2)])
  have p: "p\<in>U" "p\<in>carrier" using U N by auto
  have N_carrier [simp]: "manifold.carrier (charts_submanifold N) = N"
    using submanifold.carrier_submanifold open_imp_submanifold N(3) Int_absorb2 N(2) U(2)
    by (metis subset_trans)

  obtain N' where N': "p\<in>N'" "open N'" "compact (closure N')" "closure N' \<subseteq> N"
    using manifold.precompact_neighborhoodE[of p "charts_submanifold N", simplified, OF N(1)] by blast
  from submanifold.extension_lemma_submanifoldE[OF open_imp_submanifold[OF N(3)] f_diff_N closed_closure] this(4)
  obtain g where  g: "diff_fun k charts g" "\<And>x. x \<in> closure N' \<Longrightarrow> g x = f x" "csupport_on carrier g \<inter> carrier \<subseteq> N"
    by auto
  let ?g = "restrict0 carrier g"
  have diff_g': "diff_fun k charts ?g" "?g \<in> diff_fun_space"
    subgoal by (rule diff_fun.diff_fun_cong[OF g(1)]) simp
    subgoal unfolding diff_fun_space_def using \<open>diff_fun k charts ?g\<close> by simp
    done

  note [simp] = charts_submanifold_Int[OF N(3) U(1)] Int_absorb2[OF N(2)] rough_vector_fieldE(1)[OF X]
    vec_field_apply_fun_alt[OF N(3,1) f'] vec_field_apply_fun_alt[OF U(1) p(1) f]
  note Xp_eq_localI = submanifold.vector_apply_sub_eq_localI(2)
    [OF open_imp_submanifold N'(1) _ N'(2)
        subset_trans[OF closure_subset, OF subset_trans[OF N'(4)]]
        diff_g'(2) _ _ rough_vector_fieldE(1)[OF X]]

  have f_eq: "restrict0 carrier g x = f x" "restrict0 carrier g x = restrict0 N f x"
    if "x\<in>N'" for x
  proof -
    have "x \<in> carrier" "x \<in> N"
      using that N'(4) N(2) U(2) by auto
    thus "restrict0 carrier g x = f x" "restrict0 carrier g x = restrict0 N f x"
      using that g(2) by auto
  qed

  show ?thesis
    using Xp_eq_localI[OF N(3) subset_trans[OF N(2)], OF U(2) _ f' f_eq(2)] Xp_eq_localI[OF U N(2) f f_eq(1)]
    by (simp add: X f' that(3) that(5) vec_field_apply_fun_alt')
qed


lemma (in submanifold) vec_field_apply_fun_in_open[simp]:
    "vec_field_restr X S p f' = X p f"
    if S: "S \<subseteq> carrier"
      and N: "open N" "N\<subseteq>S" "p \<in> N"
      and f: "f \<in> diff_fun_space" "f' \<in> sub.diff_fun_space" "\<forall>x\<in>N. f x = f' x"
      and X: "rough_vector_field X"
  using vector_apply_sub_eq_localI(2)[OF N(3) S N(1,2) f(1,2)] that(3,4,6,7,8)
  by (auto simp: vec_field_apply_fun_alt' rough_vector_fieldE(1) open_submanifold)


lemma (in smooth_manifold) vec_field_apply_fun_in_restrict0':
    "restrict0 U (X\<hungarumlaut>f) = X\<restriction>U \<hungarumlaut> (restrict0 U f)"
    if U: "open U" "U \<subseteq> carrier" and f: "f \<in> diff_fun_space" and X: "rough_vector_field X"
    for U X f
proof
  fix p
  interpret U: submanifold charts \<infinity> U
    by (unfold_locales, simp add: U)
  have U_simps[simp]: "U.sub.carrier  = U"
    using U by auto

  show "restrict0 U (X\<hungarumlaut>f) p = X\<restriction>U p (restrict0 U f)" (is \<open>?LHS = ?RHS\<close>)
    by (metis (mono_tags, lifting) U.open_submanifold X U(2) charts_submanifold_carrier
        diff.defined diff_id f image_ident open_carrier open_imp_submanifold restrict0_def
        submanifold.vec_field_apply_fun_in_open vec_field_apply_fun_in_restrict0)
qed


lemma (in submanifold) vec_field_apply_fun_in_open'[simp]:
    "vec_field_restr X S p f' = X p f"
    if S: "p \<in> S" "S \<subseteq> carrier"
      and f: "f \<in> diff_fun_space" "f' \<in> sub.diff_fun_space" "\<forall>x\<in>S. f x = f' x"
      and X: "rough_vector_field X"
  using vec_field_apply_fun_in_open[OF S(2) open_submanifold _ S(1) f X] by simp


lemma (in c_manifold) vec_field_apply_fun_in_chart[simp]:
    "vec_field_apply_fun_in_at X f (domain c) p = X p f"
    if p: "p \<in> domain c" and c: "c \<in> atlas"
      and f: "f \<in> diff_fun_space" "f \<in> c_manifold.diff_fun_space (charts_submanifold (domain c)) k"
      and X: "rough_vector_field X"
  using vec_field_apply_fun_in_open that by blast

end (*c_manifold*)



context c_manifold_local begin

lemma vec_field_apply_fun_eq_component:
  fixes x\<^sub>\<psi> defines [simp]: "x\<^sub>\<psi> \<equiv> local_coord_at"
  assumes q: "q\<in>domain \<psi>" and p:"p\<in>domain \<psi>" and X: "rough_vector_field X" and k: "k=\<infinity>"
  shows "vec_field_apply_fun_in_at X (x\<^sub>\<psi> q i) (domain \<psi>) q = vector_field_component X i q"
proof -
  note [simp] = local_coord_at_def sub_\<psi>.sub.diff_fun_space_def vector_field_component_def
  interpret q: c_manifold_point charts k \<psi> q using q \<psi> by unfold_locales simp
  let ?x\<^sub>q = "x\<^sub>\<psi> q"
  have Xq: "X q \<in> q.T\<^sub>pM" "q.dRestr2 (X q) \<in> q.T\<^sub>pU"
    subgoal using rough_vector_fieldE[OF X] q \<psi> by blast
    using bij_betwE[OF q.bij_betw_d\<iota>_inv] \<open>X q \<in> q.T\<^sub>pM\<close> by simp
  note 1 = vector_apply_coord_at[OF q p Xq(1) k]
  have 2: "q.dRestr2 (X q) (local_coord_at q i) = vector_field_component X i q"
    using q.component_function_apply_in_T\<^sub>pM[OF Xq(1)] by simp
  show ?thesis
    apply (simp only: 2[symmetric] 1[symmetric] restrict0_apply_in[OF Xq(1)])
    using vec_field_apply_fun_alt'[OF open_domain q] local_coord_diff_fun[OF k q] X x\<^sub>\<psi>_def
    by blast
qed


text \<open>Prop 8.1, page 175, Lee 2012.
  The main difference is that our vector field $X$ here is only a map $M \to snd`TM$, not a section
  $M to TM$ properly speaking. See also @{thm apply_chart_TM_chartX}.\<close>
lemma vector_field_smooth_local_iff:
  assumes k: "k = \<infinity>" and X: "\<forall>p\<in>domain \<psi>. X p \<in> tangent_space p"
  shows "smooth_vector_field_local charts \<psi> X \<longleftrightarrow> (\<forall>i\<in>Basis. diff_fun_on (domain \<psi>) (vector_field_component X i))"
    (is \<open>?smooth_vf X \<longleftrightarrow> (\<forall>i\<in>Basis. ?diff_component X i)\<close>)
proof -

  text \<open>A bit of house-keeping. Maybe having both \<^term>\<open>vector_field_component\<close> and
    \<^term>\<open>c_manifold_point.tangent_chart_fun\<close> is redundant,
    or maybe the second statement below could be a simp rule (probably in the opposite direction).\<close>
  have cpt1: "c_manifold_point charts k \<psi> a" if "a\<in>domain \<psi>" for a
    apply unfold_locales by (simp_all add: sub_\<psi> that)
  have vfc_tcf: "(\<Sum>i\<in>Basis. vector_field_component X i p *\<^sub>R i) = c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p (X p)"
    if "p \<in> domain \<psi>" for p
    using c_manifold_point.tangent_chart_fun_def[of charts k \<psi>] vector_field_component_def cpt1 k that by auto

  show ?thesis
  proof
    assume asm: "?smooth_vf X"
    then interpret smooth_X_local: smooth_vector_field_local charts \<psi> X
      unfolding smooth_vector_field_local_def .

    text \<open>Notice we don't even need our Euclidean representation theorem @{thm vector_field_local_representation}.
      The crux is that we already know differentiability works well with components: @{thm diff_fun_components_iff}.\<close>
    have "\<forall>i\<in>Basis. diff_fun \<infinity> (charts_submanifold (domain \<psi>)) (vector_field_component X i)"
      apply (subst smooth_X_local.sub_\<psi>.sub.diff_fun_components_iff[of "vector_field_component X", symmetric])
      using smooth_X_local.smooth_in_chart_X[unfolded smooth_X_local.chart_X_def]
      by (auto intro: diff_fun.diff_fun_cong[OF _ vfc_tcf[symmetric]])

    then show "\<forall>i\<in>Basis. ?diff_component X i"
      using diff_fun_onI[of "domain \<psi>" "domain \<psi>" f f for f] domain_atlas_subset_carrier k by auto
  next
    assume asm: "\<forall>i\<in>Basis. ?diff_component X i"
    interpret local_\<psi>: c_manifold_local charts \<infinity> \<psi> using c_manifold_local_axioms k by auto

    have 2: "diff_fun \<infinity> (charts_submanifold (domain \<psi>)) (\<lambda>p. c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p (X p))"
      apply (rule diff_fun.diff_fun_cong[OF _ vfc_tcf])
      using sub_\<psi>.sub.diff_fun_components_iff[of "vector_field_component X"] k asm diff_fun_on_open
      by auto
    have 1: "smooth_on (codomain \<psi>) ((\<lambda>p. c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p (X p)) \<circ> inv_chart \<psi>)"
      if "x \<in> domain \<psi>" for x
      apply (rule diff_fun.diff_fun_between_chartsD[of _ "charts_submanifold (domain \<psi>)"])
      using 2 that by (auto simp: local_\<psi>.sub_\<psi>)

    show "?smooth_vf X"
      apply unfold_locales
      using 1 X k by (auto intro!: bexI[of _ \<psi>] bexI[of _ chart_eucl] simp: local_\<psi>.sub_\<psi> id_comp[unfolded id_def])
  qed
qed


end (* c_manifold_local *)


lemma (in smooth_vector_field_local) diff_component':
  fixes i :: 'b
  assumes "i \<in> Basis"
  shows "diff_fun_on (domain \<psi>) (vector_field_component X i)"
  using vector_field_smooth_local_iff[OF _ vector_field] smooth_vector_field_local_axioms assms by auto



context smooth_manifold begin

text \<open>Prop. 8.8 in Lee 2012.\<close>
text \<open>Do we want extensional0 vector fields? It would make the usual simplification for writing
  addition and scaling by real numbers. So \<open>\<XX>\<close> could be a vector space under \<open>(+)\<close> and \<open>scaleR\<close>?
  Maybe a double problem:
    * \<^cancel>\<open>0::'a\<Rightarrow>('a\<times>(('a\<Rightarrow>real)\<Rightarrow>real))\<close> is ill-defined when \<^typ>\<open>'a\<close> is not of the sort \<^class>\<open>zero\<close>.
    * Also I think the function \<open>0\<close> always assigns zero, i.e. for a pair it returns
      the constant \<open>(0,0)\<close>. We would want the zero vector field to be $p \mapsto (p,0)$ instead.\<close>
text \<open>We will need to use locales anyway if we also want to talk about \<open>\<XX>\<close> as a module over
  \<open>diff_fun_space\<close>, since that is a set already. - Actually, probably not true, because
  \<^term>\<open>extensional0\<close> works out quite neatly.\<close>

text \<open>A predicate analogous to \<^term>\<open>smooth_vector_field_local\<close>, but for the entire manifold.\<close>
definition smooth_vector_field :: "'a vector_field \<Rightarrow> bool"
  where "smooth_vector_field X \<equiv> rough_vector_field X \<and> smooth_from_M_to_TM (\<lambda>p. (p, X p))"

lemma smooth_vector_field_alt:
  "smooth_vector_field X \<equiv> (\<lambda>p. (p, X p)) \<in> \<XX> \<and> extensional0 carrier X"
  by (auto simp: smooth_vector_field_def smooth_section_of_TM_def section_of_TM_def
      rough_vector_field_def in_TM_def, linarith)

\<comment> \<open>For displaying.\<close>
lemma "smooth_vector_field X \<equiv> (\<forall>p\<in>carrier. X p \<in> tangent_space p) \<and>
                                smooth_from_M_to_TM (\<lambda>p. (p, X p)) \<and>
                                extensional0 carrier X"
  by (auto simp: smooth_vector_field_def smooth_section_of_TM_def section_of_TM_def
      rough_vector_field_def in_TM_def, linarith)

lemma smooth_vector_fieldE [elim]:
  assumes "smooth_vector_field X"
  shows "\<And>p. X p \<in> tangent_space p" "extensional0 carrier X" "rough_vector_field X" "smooth_from_M_to_TM (\<lambda>p. (p, X p))"
  using rough_vector_fieldE assms unfolding smooth_vector_field_def by auto

lemma smooth_vector_field_imp_local:
  assumes "smooth_vector_field X" "\<psi> \<in> atlas"
  shows "smooth_vector_field_local charts \<psi> X"
proof -
  interpret \<psi>: c_manifold_local charts \<infinity> \<psi> using assms(2) by unfold_locales
  have 1: "section_of_TM (\<lambda>p. (p, X p))"
    using assms(1,2) smooth_section_of_TM_def smooth_vector_field_alt by blast
  have 2: "smooth_from_M_to_TM (\<lambda>p. (p, X p))"
    using assms(1) smooth_vector_field_def by auto
  have vec_field_X: "\<forall>p\<in>domain \<psi>. X p \<in> tangent_space p"
    using assms(1) by (auto simp: smooth_vector_field_def)
  moreover have diff_fun_X: "diff_fun \<infinity> (charts_submanifold (domain \<psi>)) (\<lambda>p. c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p (X p))"
    using apply_chart_TM_chartX diff_from_M_to_TM_chartsD[OF 2 1, of \<psi>] section_of_TM_subset[OF 1]
    using \<psi>.\<psi> by (simp add: domain_atlas_subset_carrier)
  ultimately show ?thesis
    using \<psi>.c_manifold_local_axioms by (auto simp: smooth_vector_field_local_def smooth_vector_field_local_axioms_def)
qed

lemma smooth_vector_field_imp_local':
  fixes X \<psi> X\<^sub>\<psi> defines "X\<^sub>\<psi> \<equiv> restrict0 (domain \<psi>) X"
  assumes "smooth_vector_field X" "\<psi> \<in> atlas"
  shows "smooth_vector_field_local charts \<psi> X\<^sub>\<psi>"
  unfolding smooth_vector_field_local_def smooth_vector_field_local_axioms_def assms(1)
  using smooth_vector_field_imp_local[OF assms(2-)] apply safe
  subgoal using smooth_vector_field_local.axioms(1) by blast
  subgoal using rough_vector_fieldE(1) smooth_vector_field_local.rough_vector_field by blast
  apply (rule diff_fun.diff_fun_cong[of _ _ "(\<lambda>p. c_manifold_point.tangent_chart_fun charts \<infinity> \<psi> p (X p))"])
  subgoal by (simp add: assms(2,3) smooth_vector_field_imp_local smooth_vector_field_local.smooth_in_chart)
  subgoal by (metis IntD2 inf_sup_aci(1) open_domain open_imp_submanifold restrict0_apply_in submanifold.carrier_submanifold)
  done


lemma smooth_vector_field_if_local:
  assumes "\<forall>p\<in>carrier. \<exists>c\<in>atlas. p \<in> domain c \<and> smooth_vector_field_local charts c X" "extensional0 carrier X"
  shows "smooth_vector_field X"
proof (unfold smooth_vector_field_def diff_from_M_to_TM_def, intro conjI allI impI)
  show vec_field_X: "rough_vector_field X"
    by (metis assms(1,2) rough_vector_field_def smooth_vector_field_local.vector_field)
  fix p assume "p\<in>carrier"
  then obtain c where c: "c \<in> atlas" and p: "p \<in> domain c" and X: "smooth_vector_field_local charts c X"
    using assms(1) by blast
  interpret X: smooth_vector_field_local charts c X using X .
  have im_domain: "(\<lambda>p. (p, X p)) ` domain c \<subseteq> domain_TM c"
    using rough_vector_fieldE[OF vec_field_X] in_carrier_atlasI[OF c] by (auto simp: domain_TM_def)
  have smooth_X: "smooth_on (codomain c) (apply_chart_TM c \<circ> (\<lambda>p. (p, X p)) \<circ> inv_chart c)"
    using X.apply_chart_TM_chart_X X.smooth_in_chart_X by blast
  show "\<exists>c\<in>atlas. p \<in> domain c \<and> (\<lambda>p. (p, X p)) ` domain c \<subseteq> domain_TM c \<and>
      smooth_on (codomain c) (apply_chart_TM c \<circ> (\<lambda>p. (p, X p)) \<circ> inv_chart c)"
    using c p im_domain smooth_X by blast
qed


lemma smooth_vector_field_iff_local:
  assumes "extensional0 carrier X"
  shows "(\<forall>c\<in>atlas. smooth_vector_field_local charts c X) \<longleftrightarrow> smooth_vector_field X"
  using smooth_vector_field_imp_local smooth_vector_field_if_local by (meson assms atlasE)


\<comment> \<open>For display mostly.\<close>
lemma (in smooth_manifold) smooth_vector_field_local:
  assumes "c \<in> atlas" "\<forall>p\<in>domain c. X p \<in> tangent_space p"
  shows "smooth_vector_field_local charts c X \<longleftrightarrow>
    smooth_on (codomain c) (apply_chart_TM c \<circ> (\<lambda>p. (p, X p)) \<circ> inv_chart c)"
  (* unfolding smooth_vector_field_local_def smooth_vector_field_local_axioms_def *)
  (* apply (intro iffI) *)
  (* using smooth_vector_field_local.apply_chart_TM_chart_X smooth_vector_field_local.intro smooth_vector_field_local.smooth_in_chart_X smooth_vector_field_local_axioms_def apply blast *)
  (* apply (simp add: assms c_manifold_axioms c_manifold_local.intro c_manifold_local_axioms.intro) *)
  (* apply (rule c_manifold.diff_funI[OF charts_submanifold, OF open_domain[of c]]) *)
  (* unfolding apply_chart_TM_def apply (simp add: o_def) *)
  (* apply (rule bexI[of _ c "c_manifold.atlas (charts_submanifold (domain c)) \<infinity>"]) *)
proof -
  interpret c: submanifold charts \<infinity> "domain c"
    using open_domain by unfold_locales simp
  let ?c1 = "\<lambda>x. c (inv_chart c x)"
  let ?c2 = "\<lambda>x. c_manifold_point.tangent_chart_fun charts \<infinity> c (inv_chart c x) (X (inv_chart c x))"
  {
    fix x assume smoothTM: "smooth_on (codomain c) (\<lambda>x. (?c1 x, ?c2 x))" and x: "x \<in> c.sub.carrier"
    have loc_simp: "snd \<circ> (\<lambda>x. (?c1 x, ?c2 x)) = ?c2" by auto
    have "x \<in> domain c \<and> c \<in> c.sub.atlas \<and> smooth_on (codomain c) ?c2"
      using x apply (simp add: assms(1) atlas_is_atlas c.sub.maximal_atlas c.submanifold_atlasE domain_atlas_subset_carrier)
      apply (subst loc_simp[symmetric, unfolded o_def])
      apply (rule smooth_on_snd[of \<infinity>, OF _ open_codomain[of c]])
      using smoothTM .
  }
  thus ?thesis
    unfolding smooth_vector_field_local_def smooth_vector_field_local_axioms_def
    apply (intro iffI)
    using smooth_vector_field_local.apply_chart_TM_chart_X smooth_vector_field_local.intro smooth_vector_field_local.smooth_in_chart_X smooth_vector_field_local_axioms_def apply blast
    apply (simp add: assms c_manifold_axioms c_manifold_local.intro c_manifold_local_axioms.intro)
    apply (rule c_manifold.diff_funI[OF charts_submanifold, OF open_domain[of c]])
    unfolding apply_chart_TM_def apply (simp add: o_def)
    apply (rule bexI[of _ c "c_manifold.atlas (charts_submanifold (domain c)) \<infinity>"])
    by blast+
qed


lemma (in c_manifold) diff_fun_deriv_chart':
  fixes i::'b
  assumes c:"c\<in>atlas" and f:"diff_fun_on (domain c) f" and k: "k>0"
  shows "diff_fun (k-1) (charts_submanifold (domain c)) (\<lambda>x. frechet_derivative (f \<circ> inv_chart c) (at (c x)) i)"
proof -
  have local_simps [simp]: "k - 1 + 1 = k"
    using k by (metis add.commute add_diff_assoc_enat add_diff_cancel_enat ileI1 infinity_ne_i1 one_eSuc)
  interpret c1: c_manifold_local charts "k-1" c
    apply unfold_locales
    apply (metis c_manifold_def c_manifold_order_le le_iff_add local_simps)
    by (metis c in_atlas_order_le le_iff_add local_simps)
  interpret f': diff_fun k "charts_submanifold (domain c)" f
    using diff_fun_on_open[of "domain c" f] f by simp
  { fix x and j::'b assume x: "x\<in>domain c" "x\<in>carrier"
    have "(k-1)-smooth_on (codomain c) (\<lambda>y. frechet_derivative (f \<circ> (inv_chart c)) (at y) j)"
      apply (rule derivative_is_smooth'[of _ "codomain c"], simp)
      apply (rule f'.diff_fun_between_chartsD)
      using c c_manifold_local.sub_\<psi> c_manifold_point c_manifold_point.axioms(1) k x(1) by blast+
    then have "(k-1)-smooth_on (codomain c) (\<lambda>x. frechet_derivative (\<lambda>x. f (inv_chart c x)) (at (c (inv_chart c x))) j)"
      by (auto intro: smooth_on_cong simp: o_def) }
  then show ?thesis
    by (auto intro!: c1.sub_\<psi>.sub.diff_funI bexI[of _ c] simp: o_def c1.sub_\<psi>)
qed

lemma diff_fun_deriv_chart:
  fixes i::'b
  assumes c:"c\<in>atlas" and f:"diff_fun_on (domain c) f"
  shows "diff_fun \<infinity> (charts_submanifold (domain c)) (\<lambda>x. frechet_derivative (f \<circ> inv_chart c) (at (c x)) i)"
  using diff_fun_deriv_chart'[OF assms] by auto


lemma (in c_manifolds) diff_localI2: "diff k charts1 charts2 f"
  if "\<forall>x\<in>src.carrier. (\<exists>U. diff k (src.charts_submanifold U) charts2 f \<and> open U \<and> x \<in> U)"
  using diff_localI that by metis


subsection \<open>Smooth vector fields as maps $C^\infty(M) \to C^\infty(M)$.\<close>

text \<open>Proposition 8.14 in Lee 2012.\<close>
lemma vector_field_smooth_iff:
  assumes X: "rough_vector_field X"
  shows "smooth_vector_field X \<longleftrightarrow> (\<forall>f\<in>diff_fun_space. (X \<hungarumlaut> f) \<in> diff_fun_space)"
      (is \<open>?LHS \<longleftrightarrow> ?RHS1\<close>)
    and "smooth_vector_field X \<longleftrightarrow> (\<forall>U f. open U \<and> U \<subseteq> carrier \<and> f\<in>(c_manifold.diff_fun_space (charts_submanifold U) \<infinity>) \<longrightarrow>
                                          diff_fun \<infinity> (charts_submanifold U) (vec_field_apply_fun_in_at X f U))"
      (is \<open>?LHS \<longleftrightarrow> ?RHS2\<close>)
proof -
  text \<open>Prove a chain of implications \<^term>\<open>?LHS \<longrightarrow> ?RHS1 \<longrightarrow> ?RHS2 \<longrightarrow> ?LHS\<close>
    to conclude both equivalences, following Lee 2012, pp.~180--181.\<close>

  have "?RHS1" if smooth_X: "?LHS"
  proof (*(intro ballI)*)
    fix f assume f: "f \<in> diff_fun_space"
    { fix p assume p: "p\<in>carrier"
      obtain c where c: "p \<in> domain c" "c \<in> atlas" using atlasE p by blast
      interpret p: c_manifold_point charts \<infinity> c p by (simp add: p c_manifold_point c)
      { fix x assume x: "x \<in> domain c"
        interpret x: c_manifold_point charts \<infinity> c x by (simp add: x c_manifold_point)
        have Xxf_1: "X x f = (\<Sum>i\<in>Basis. p.vector_field_component X i x *\<^sub>R p.coordinate_vector_field i x) f"
          by (simp only: p.vector_field_local_representation[OF _ X x])
        then have Xxf_2: "X x f = (\<Sum>i\<in>Basis. p.vector_field_component X i x *\<^sub>R (frechet_derivative (f \<circ> inv_chart c) (at (c x)) i))"
          using x.coordinate_vector_apply_in[OF _ f] by (simp add: sum_apply p.coordinate_vector_field_def)
      }
      then have Xxf: "X x f = (\<Sum>i\<in>Basis. p.vector_field_component X i x *\<^sub>R frechet_derivative (f \<circ> inv_chart c) (at (c x)) i)"
        if "x \<in> p.sub_\<psi>.sub.carrier" for x using that by simp
      have diff_components_X: "(\<forall>i\<in>Basis. diff_fun_on (domain c) (p.vector_field_component X i))"
        using p.vector_field_smooth_local_iff rough_vector_field_subset[OF X] smooth_X
          domain_atlas_subset_carrier p.\<psi> smooth_vector_field_imp_local
        by (meson smooth_vector_field_local.diff_component')
      have "diff_fun_on (domain c) f"
        using diff_fun.diff_fun_submanifold[OF diff_fun_spaceD[OF f]]
        by (simp add: diff_fun_on_open domain_atlas_subset_carrier)
      note diff_fun_deriv_chart_f = diff_fun_deriv_chart[OF c(2) this]
      have diff_Xf: "diff_fun \<infinity> (charts_submanifold (domain c)) (X\<hungarumlaut>f)"
        apply (rule diff_fun.diff_fun_cong[OF _ Xxf[symmetric]])
        apply (rule p.sub_\<psi>.sub.diff_fun_sum)
        apply (rule p.sub_\<psi>.sub.diff_fun_scaleR)
        using diff_components_X diff_fun_deriv_chart_f by (simp_all add: diff_fun_on_open)
      have "smooth_on (codomain c) ((X\<hungarumlaut>f) \<circ> inv_chart c)"
        using diff_Xf apply (rule diff_fun.diff_fun_between_chartsD)
        using p.sub_\<psi> c(1) by (simp, blast)
      hence "\<exists>c1\<in>atlas. p \<in> domain c1 \<and> \<infinity>-smooth_on (codomain c1) ((X\<hungarumlaut>f) \<circ> inv_chart c1)"
        using c by blast }
    moreover have "extensional0 carrier (X \<hungarumlaut> f)"
      using rough_vector_fieldE(2)[OF X] by (simp add: extensional0_def)
    ultimately show "(X \<hungarumlaut> f) \<in> diff_fun_space"
      unfolding diff_fun_space_def by (auto intro: diff_funI)
  qed

  moreover have "?RHS2" if "?RHS1"
  proof (safe)
    fix U f
    assume U: "open U" "U \<subseteq> carrier"
      and f: "f \<in> c_manifold.diff_fun_space (charts_submanifold U) \<infinity>"
    interpret U: submanifold charts \<infinity> U using U(1) by unfold_locales simp

    show "diff_fun \<infinity> (charts_submanifold U) (vec_field_apply_fun_in_at X f U)"
    proof (intro U.sub.manifold_eucl.diff_localI2 ballI)
      fix x assume x: "x \<in> U.sub.carrier"
      from U.sub.precompact_neighborhoodE[OF this]
      obtain C where C: "x \<in> C" "open C" "compact (closure C)" "closure C \<subseteq> U.sub.carrier" .
      from U.extension_lemma_submanifoldE[OF U.sub.diff_fun_spaceD[OF f] closed_closure C(4)]
      obtain f' where f': "diff_fun \<infinity> charts f'" "(\<And>x. x \<in> closure C \<Longrightarrow> f' x = f x)"
        "csupport_on carrier f' \<inter> carrier \<subseteq> U.sub.carrier" by blast

      let ?f' = "restrict0 U f'"
      have 1: "?f' \<in> diff_fun_space"
        unfolding diff_fun_space_def apply safe
        subgoal
          apply (rule diff_fun.diff_fun_cong[OF f'(1)])
          using f'(2,3) by (metis (no_types) IntE IntI U.carrier_submanifold not_in_csupportD restrict0_def subset_iff)
        subgoal
          using U(2) extensional0_subset by blast
        done

      show "\<exists>C. diff \<infinity> (U.sub.charts_submanifold C) charts_eucl (vec_field_apply_fun_in_at X f U) \<and>
                open C \<and> x \<in> C"
      proof (intro exI conjI)
        have carrier_UsubC [simp]: "manifold.carrier (U.sub.charts_submanifold C) = C"
          by (metis C(2,4) Int_absorb2 U.sub.open_imp_submanifold closure_subset submanifold.carrier_submanifold subset_trans)
        have "diff_fun \<infinity> (U.sub.charts_submanifold C) (vec_field_apply_fun_in_at X f U)"
        proof (rule diff_fun.diff_fun_cong[where f="X\<hungarumlaut>?f'"])
          have "diff_fun \<infinity> charts (\<lambda>p. X p ?f')" using 1 that by (simp add: diff_fun_spaceD)
          from diff_fun.diff_fun_submanifold[OF this]
          show "diff_fun \<infinity> (U.sub.charts_submanifold C) (\<lambda>p. X p ?f')"
            by (simp add: C(2) U.open_submanifold charts_submanifold_Int open_Int)
          show "X x (restrict0 U f') = vec_field_apply_fun_in_at X f U x"
            if "x \<in> manifold.carrier (U.sub.charts_submanifold C)" for x
          proof -
            have "X p ?f' = vec_field_apply_fun_in_at X f U p" if p: "p\<in>C" for p
              using U.vec_field_apply_fun_in_open[OF U(2) C(2) _ _ 1 f _ X, symmetric]
              using C p f f'(2) C(4) by (auto simp: subset_iff)
            thus ?thesis using that by simp
          qed
        qed
        thus "diff \<infinity> (U.sub.charts_submanifold C) charts_eucl (vec_field_apply_fun_in_at X f U)"
          unfolding diff_fun_def .
      qed (simp_all add: C(1,2))
    qed
  qed

  moreover have "?LHS" if diff_apply_fun: "?RHS2"
  proof (intro smooth_vector_field_if_local ballI)
    fix p assume p: "p\<in>carrier"
    obtain c where c: "c\<in>atlas" "p\<in>domain c" using p atlasE by blast
    then interpret p: c_manifold_point charts \<infinity> c p using c_manifold_point by blast

    have vf_smooth_local_iff: "smooth_vector_field_local charts c X"
      if "(\<forall>i\<in>Basis. diff_fun_on (domain c) (p.vector_field_component X i))"
      using p.vector_field_smooth_local_iff rough_vector_field_subset[OF X]
      by (meson assms in_carrier_atlasI p.\<psi> rough_vector_field_def that)
    have "smooth_vector_field_local charts c X"
    proof (rule vf_smooth_local_iff, intro ballI)
      fix i::'b assume i: "i\<in>Basis"

    \<comment> \<open>Add simp rules to make \<^term>\<open>diff_fun_on\<close> equivalent to \<^term>\<open>diff_fun\<close> on \<^term>\<open>domain c\<close>.\<close>
      note local_simps[simp] = diff_fun_on_open domain_atlas_subset_carrier

      define apply_X_in_c_at (\<open>X\<^sub>c\<hungarumlaut> _ _\<close> [80,80])
        where [simp]: "apply_X_in_c_at \<equiv> \<lambda>f q. vec_field_apply_fun_in_at X f (domain c) q"

      have "(X\<restriction>(domain c)) q (p.local_coord_at p i) = p.vector_field_component X i q"
        if "q\<in>domain c" for q
      proof -
        interpret q: c_manifold_point charts \<infinity> c q using that c by unfold_locales simp_all
        have Xq: "X q \<in> q.T\<^sub>pM" using rough_vector_fieldE[OF X] that c(1) by blast
        show ?thesis
          using vec_field_apply_fun_alt[OF open_domain that] apply (simp add: p.local_coord_diff_fun X)
          using restrict0_apply_in[OF Xq]
          using p.vector_apply_coord_at p.p that q.component_function_apply_in_T\<^sub>pM
          by (smt (verit, best) Xq assms c_manifold_local.vec_field_apply_fun_eq_component p.c_manifold_local_axioms p.local_coord_diff_fun)
      qed
      moreover have "diff_fun_on (domain c) (\<lambda>q. X\<^sub>c\<hungarumlaut> (p.local_coord_at p i) q)"
        using diff_apply_fun by (simp add: p.local_coord_diff_fun)

      ultimately show "diff_fun_on (domain c) (p.vector_field_component X i)"
        by (simp add: diff_fun_on_def)
    qed
    with c show "\<exists>c\<in>atlas. p \<in> domain c \<and> smooth_vector_field_local charts c X" by blast
  qed (simp add: assms rough_vector_fieldE(2))

  ultimately show "?LHS \<longleftrightarrow> ?RHS1" "?LHS \<longleftrightarrow> ?RHS2" by auto
qed


lemma vector_field_smooth_iff':
  fixes C_inf
  defines "\<And>U. C_inf U \<equiv> c_manifold.diff_fun_space (charts_submanifold U) \<infinity>"
  assumes X: "rough_vector_field X"
  shows "smooth_vector_field X \<longleftrightarrow> (\<forall>f\<in>diff_fun_space. (X \<hungarumlaut> f) \<in> diff_fun_space)"
    and "smooth_vector_field X \<longleftrightarrow> (\<forall>U f. open U \<and> U \<subseteq> carrier \<and> f \<in> C_inf U \<longrightarrow>
                                          diff_fun_on U (X\<restriction>U \<hungarumlaut> f))"
proof -
  show "smooth_vector_field X = (\<forall>U f. open U \<and> U \<subseteq> carrier \<and> f \<in> C_inf U \<longrightarrow> diff_fun_on U (\<lambda>p. X\<restriction>U p f))"
    apply (simp add: diff_fun_on_open assms(1))
    using vector_field_smooth_iff(2)[OF assms(2-)]
    by (smt (verit, ccfv_SIG) Un_Int_eq(4) diff_fun.diff_fun_cong open_imp_submanifold
        restrict0_apply_in submanifold.carrier_submanifold sup.order_iff)
qed (simp add: vector_field_smooth_iff(1)[OF assms(2-)])
  

lemma smooth_vf_diff_fun_space:
  assumes X: "smooth_vector_field X"
    and f: "f\<in>diff_fun_space"
  shows "X\<hungarumlaut>f \<in> diff_fun_space"
  using vector_field_smooth_iff(1) smooth_vector_field_def X f rough_vector_fieldE
  by (auto simp: diff_fun_space_def extensional0_def)

end (* smooth_manifold *)



subsection \<open>Smooth vector fields are derivations\<close>
context c_manifold begin

\<comment> \<open>Generalising \<^term>\<open>is_derivation\<close> (which might have been called \<open>is_derivation_at\<close>)
    over the carrier set. Relative to that definition, we also add a condition on the codomain.\<close>
definition is_derivation_on :: "(('a\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real)) \<Rightarrow> bool" where
  "is_derivation_on D \<equiv> real_linear_on diff_fun_space diff_fun_space D \<and>
                        (\<forall>f\<in>diff_fun_space. \<forall>g\<in>diff_fun_space. D (f*g) = f*(D g) + g*(D f)) \<and>
                        D ` diff_fun_space \<subseteq> diff_fun_space"


lemma vec_field_linear_on:
  assumes X: "rough_vector_field X"
    and b: "b1 \<in> diff_fun_space" "b2 \<in> diff_fun_space"
  shows "X \<hungarumlaut> (b1+b2) = (X\<hungarumlaut>b1 + X\<hungarumlaut>b2)" "X \<hungarumlaut> (r *\<^sub>R b1) = (r *\<^sub>R (X\<hungarumlaut>b1))"
  using tangent_space_linear_on[OF rough_vector_fieldE(1)[OF X]]
  by (auto simp: linear_on_def module_hom_on_def module_hom_on_axioms_def assms(2-))

lemma linear_on_vec_field:
  assumes "rough_vector_field X"
  shows "real_linear_on diff_fun_space diff_fun_space ((\<hungarumlaut>) X)"
  using vec_field_linear_on[OF assms] by (unfold_locales, auto)

lemma product_rule_vf:
  assumes X: "rough_vector_field X"
    and "f \<in> diff_fun_space" "g \<in> diff_fun_space"
  shows "X \<hungarumlaut> (f*g) = f * (X \<hungarumlaut> g) + g * (X \<hungarumlaut> f)"
  using tangent_space_derivation rough_vector_fieldE(1) assms by auto

end


context smooth_manifold begin

lemma vector_field_is_derivation:
  assumes X: "smooth_vector_field X"
  shows "is_derivation_on (\<lambda>f. X\<hungarumlaut>f)"
  using linear_on_vec_field product_rule_vf vector_field_smooth_iff(1)
  using smooth_vector_field_def assms unfolding is_derivation_on_def by auto



subsection \<open>Derivations are smooth vector fields\<close>
\<comment> \<open>Proposition 8.15 of Lee 2015 (p.~181).\<close>

lemma extensional_derivation_is_smooth_vector_field:
  fixes D :: "('a\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real)" and X :: "'a\<Rightarrow>('a\<Rightarrow>real) \<Rightarrow> real"
  defines [simp]: "X \<equiv> \<lambda>p. \<lambda>f. D f p"
  assumes der_D: "is_derivation_on D"
    and ext_X: "extensional0 carrier X"
    and ext_D: "extensional0 diff_fun_space D"
  shows "smooth_vector_field X"
proof -
  have rough_vf_X: "rough_vector_field X"
  proof (unfold rough_vector_field_def tangent_space_def is_derivation_def, safe)
    fix p assume p: "p\<in>carrier"
    show "extensional0 diff_fun_space (\<lambda>f. X p f)"
      by (simp, metis (mono_tags, lifting) ext_D extensional0_def zero_fun_apply)
    show "real_linear_on diff_fun_space UNIV (\<lambda>f. X p f)"
      using der_D[unfolded is_derivation_on_def]
      unfolding linear_on_def module_hom_on_def module_hom_on_axioms_def
      using manifold_eucl.diff_fun_space.m2.module_on_axioms by auto
    fix f g assume "f \<in> diff_fun_space" "g \<in> diff_fun_space"
    thus "X p (f * g) = f p * X p g + g p * X p f"
      using der_D[unfolded is_derivation_on_def] by simp
  qed (rule ext_X)
  show "smooth_vector_field X"
    unfolding vector_field_smooth_iff(1)[OF rough_vf_X]
    using der_D[unfolded is_derivation_on_def] diff_fun_spaceD X_def by blast
qed

lemma extensional_derivation_is_smooth_vector_field':
  fixes D :: "('a\<Rightarrow>real) \<Rightarrow> ('a\<Rightarrow>real)"
  assumes der_D: "is_derivation_on D"
    and ext_X: "extensional0 carrier (\<lambda>p f. D f p)"
    and ext_D: "extensional0 diff_fun_space D"
  obtains X where "smooth_vector_field X" and "\<forall>f\<in>diff_fun_space. D f = X\<hungarumlaut>f"
  using extensional_derivation_is_smooth_vector_field[OF assms] by auto

theorem smooth_vector_field_iff_derivation:
  fixes extensional_derivation defines "\<And>D. extensional_derivation D \<equiv>
    is_derivation_on D \<and> extensional0 carrier (\<lambda>p f. D f p) \<and> extensional0 diff_fun_space D"
  shows "smooth_vector_field X \<Longrightarrow> extensional_derivation (\<lambda>f. X \<hungarumlaut> f)"
    and "extensional_derivation D \<Longrightarrow> smooth_vector_field (\<lambda>p f. D f p)"
  unfolding assms(1) using vector_field_is_derivation extensional_derivation_is_smooth_vector_field
  by (simp_all add: ext0_vec_field_apply_fun smooth_vector_fieldE(2,3))

end (* smooth_manifold *)

end