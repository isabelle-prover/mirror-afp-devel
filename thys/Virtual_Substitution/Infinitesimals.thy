subsection "Infinitesimals"
theory Infinitesimals
  imports ExecutiblePolyProps LinearCase QuadraticCase NegInfinity Debruijn
begin

lemma freeIn_substInfinitesimalQuadratic :
  assumes "var \<notin> vars a"
    "var \<notin> vars b"
    "var \<notin> vars c"
    "var \<notin> vars d"
  shows "freeIn var (substInfinitesimalQuadratic var a b c d At)"
proof(cases At)
  case (Less p)
  show ?thesis unfolding substInfinitesimalQuadratic.simps Less
    using assms free_in_quad_fm by auto
next
  case (Eq p)
  then show ?thesis
    using freeIn_allzero by auto
next
  case (Leq p)
  then show ?thesis unfolding substInfinitesimalQuadratic.simps Leq freeIn.simps
    using free_in_quad_fm[of var a b c d "(convertDerivative var p)", OF assms]
    using freeIn_allzero by blast
next
  case (Neq p)
  then show ?thesis
    using not_in_isovarspar by (auto simp add:neg_def freeIn_list_conj)
qed

lemma freeIn_substInfinitesimalQuadratic_fm :
  assumes "var \<notin> vars a" "var \<notin> vars b" "var \<notin> vars c" "var \<notin> vars d"
  shows "freeIn var (substInfinitesimalQuadratic_fm var a b c d F)"
proof-
  have "freeIn (var+z)
     (liftmap
       (\<lambda>x. substInfinitesimalQuadratic (var + x) (liftPoly 0 x a) (liftPoly 0 x b)
              (liftPoly 0 x c) (liftPoly 0 x d))
       F z)" for z
  proof (induction F arbitrary:z)
    case (Atom x)
    then show ?case
      by (simp add: assms freeIn_substInfinitesimalQuadratic not_in_lift)
  next
    case (ExQ F)
    then show ?case
      apply simp
      by (metis (lifting) add_Suc_right)
  next
    case (AllQ F)
    then show ?case 
      apply simp
      by (metis (lifting) add_Suc_right)
  qed (auto simp: add.assoc)
  then show ?thesis 
    unfolding substInfinitesimalQuadratic_fm.simps
    by (metis (no_types, lifting) add.right_neutral) 
qed

lemma freeIn_substInfinitesimalLinear:
  assumes "var \<notin> vars a" "var \<notin> vars b"
  shows "freeIn var (substInfinitesimalLinear var a b At)"
proof(cases At)
  case (Less p)
  show ?thesis unfolding Less substInfinitesimalLinear.simps
    using var_not_in_linear_fm[of var a b "(convertDerivative var p)", OF assms]
    unfolding linear_substitution_fm.simps linear_substitution_fm_helper.simps .
next
  case (Eq p)
  then show ?thesis apply simp apply(rule freeIn_list_conj)
    apply auto
    using not_in_isovarspar by simp_all
next
  case (Leq p)
  show ?thesis unfolding Leq substInfinitesimalLinear.simps freeIn.simps
    using var_not_in_linear_fm[of var a b "(convertDerivative var p)", OF assms]
    unfolding linear_substitution_fm.simps linear_substitution_fm_helper.simps apply simp apply(rule freeIn_list_conj)
    apply auto
    using not_in_isovarspar by simp_all
next
  case (Neq p)
  then show ?thesis apply (auto simp add:neg_def) apply(rule freeIn_list_conj)
    apply auto
    using not_in_isovarspar by simp_all
qed

lemma freeIn_substInfinitesimalLinear_fm:
  assumes "var \<notin> vars a" "var \<notin> vars b"
  shows "freeIn var (substInfinitesimalLinear_fm var a b F)"
proof-
  {fix z
    have "freeIn (var+z)
     (liftmap (\<lambda>x. substInfinitesimalLinear (var + x) (liftPoly 0 x a) (liftPoly 0 x b)) F z)"
      apply(induction F arbitrary:z) apply auto
      apply(rule freeIn_substInfinitesimalLinear)
      apply (simp_all add: assms not_in_lift)
      apply (metis (full_types) Suc_eq_plus1 ab_semigroup_add_class.add_ac(1))
      apply (metis (full_types) Suc_eq_plus1 ab_semigroup_add_class.add_ac(1))
      apply (simp add: add.assoc)
      by (simp add: add.assoc)
  }
  then show ?thesis
    unfolding substInfinitesimalLinear_fm.simps
    by (metis (no_types, lifting) add.right_neutral)
qed

end
