section \<open>Nullable Set\<close>

theory Nullable_Set
imports Grammar
begin


definition lhSet :: "('n, 't) prods \<Rightarrow> 'n set" where
  "lhSet ps = set (map fst ps)"

fun nullableGamma :: "('n, 't) rhs \<Rightarrow> 'n set \<Rightarrow> bool" where
  "nullableGamma [] _ = True"
| "nullableGamma ((T _)#_) _ = False"
| "nullableGamma ((NT x)#gamma') nu = (if x \<in> nu then nullableGamma gamma' nu else False)"

definition updateNu :: "('n, 't) prod \<Rightarrow> 'n set \<Rightarrow> 'n set" where
  "updateNu \<equiv> \<lambda>(x, gamma) nu. (if nullableGamma gamma nu then insert x nu else nu)"

definition nullablePass :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
  "nullablePass ps nu = foldr updateNu ps nu"

function mkNullableSet' :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
  "mkNullableSet' ps nu = (let nu' = nullablePass ps nu in
  (if nu=nu' then nu else mkNullableSet' ps nu'))"
  by auto

definition mkNullableSet :: "('n, 't) grammar \<Rightarrow> 'n set" where
  "mkNullableSet g = mkNullableSet' (prods g) {}"


subsection \<open>Termination\<close>

definition countNullCands :: "('n, 't) prods \<Rightarrow> 'n set \<Rightarrow> nat" where
  "countNullCands ps nu = (let candidates = lhSet ps in card (candidates - nu))"

lemma nullablePass_subset: "(nu::'n set) \<subseteq> (nullablePass ps nu)"
  by (induction ps) (auto simp add: nullablePass_def updateNu_def)

lemma nullablePass_Nil[simp]: "nullablePass [] nu = nu"
  by (simp add: nullablePass_def)

lemma nullablePass_cons[simp]: "nullablePass ((y,gamma)#ps') nu =
  (if nullableGamma gamma (nullablePass ps' nu) then insert y else id) (nullablePass ps' nu)"
  by (simp add: nullablePass_def updateNu_def)

lemma nullable_pass_mono:
  "nullablePass ps nu \<subseteq> nullablePass (qs @ ps) nu"
  by (induction qs) (auto simp add: nullablePass_def updateNu_def)

lemma nullablePass_subset_lhSet:
  "nullablePass ps nu \<subseteq> lhSet ps \<union> nu"
  by (induction ps arbitrary: nu; fastforce split: if_split_asm simp: lhSet_def)

lemma nullablePass_neq_candidates_lt:
  assumes "nu \<noteq> nullablePass ps nu"
  shows "countNullCands ps (nullablePass ps nu) < countNullCands ps nu"
proof -
  have "finite (lhSet ps)" by (simp add: lhSet_def)
  then have A: "finite (lhSet ps - nu)" using finite_subset[where B = "lhSet ps"] lhSet_def by auto
  moreover have B: "lhSet ps - nullablePass ps nu \<subset> lhSet ps - nu"
    using nullablePass_subset nullablePass_subset_lhSet assms by fastforce
  ultimately show ?thesis unfolding countNullCands_def by (simp add: Let_def psubset_card_mono)
qed

termination mkNullableSet'
  using nullablePass_neq_candidates_lt
  by (relation "measure (\<lambda>(ps, nu). countNullCands ps nu)") force+

subsection \<open>Correctness Definitions\<close>

definition nullable_set_sound :: "'n set \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "nullable_set_sound nu g = (\<forall>x \<in> nu. nullable_sym g (NT x))"

definition nullable_set_complete :: "'n set \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "nullable_set_complete nu g = (\<forall>x. nullable_sym g (NT x) \<longrightarrow> x \<in> nu)"

abbreviation nullable_set_for :: "'n set \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool" where
  "nullable_set_for nu g \<equiv> nullable_set_sound nu g \<and> nullable_set_complete nu g"


subsection \<open>Soundness\<close>

lemma nu_sound_nullableGamma_sound:
  "nullable_set_sound nu g \<Longrightarrow> nullableGamma gamma nu \<Longrightarrow> nullable_gamma g gamma"
  by (induction rule: nullableGamma.induct)
     (auto
       intro: nullable_sym_nullable_gamma.intros split: if_split_asm simp: nullable_set_sound_def)

lemma nullablePass_preserves_soundness':
  "nullable_set_sound nu g \<Longrightarrow> set ps \<subseteq> set (prods g)
  \<Longrightarrow> nullable_set_sound (nullablePass ps nu) g"
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain x gamma where p_def: "p = (x, gamma)" by fastforce
  show ?case
  proof (cases "nullableGamma gamma (nullablePass ps nu)")
    case True
    have "nullable_set_sound (nullablePass ps nu) g"
      using Cons.IH Cons.prems(1,2) by force
    moreover have "nullablePass (p # ps) nu \<subseteq> nullablePass ps nu \<union> {x}"
      by (cases "nullableGamma gamma (nullablePass ps nu)")
        (auto simp add: \<open>p = (x, gamma)\<close>)
    ultimately show ?thesis
      using Cons.prems(2) True nu_sound_nullableGamma_sound nullable_sym.simps p_def
      by (fastforce simp add: nullable_set_sound_def)
  next
    case False
    then show ?thesis using Cons p_def by force
  qed
qed

lemma nullablePass_preserves_soundness:
  "nullable_set_sound nu g \<Longrightarrow> nullable_set_sound (nullablePass (prods g) nu) g"
  using nullablePass_preserves_soundness' by auto

lemmas [simp del] = mkNullableSet'.simps

lemma mkNullableSet'_preserves_soundness:
  "nullable_set_sound nu g \<Longrightarrow> nullable_set_sound (mkNullableSet' (prods g) nu) g"
  by (induction "prods g" nu rule: mkNullableSet'.induct)
     (subst mkNullableSet'.simps, auto intro: nullablePass_preserves_soundness simp: Let_def)

lemma empty_nu_sound: "nullable_set_sound {} g"
  by (simp add: nullable_set_sound_def)

theorem mkNullableSet_sound: "nullable_set_sound (mkNullableSet g) g"
  unfolding mkNullableSet_def using empty_nu_sound by (rule mkNullableSet'_preserves_soundness)


subsection \<open>Completeness\<close>

lemma nullablePass_add_equal: "x \<in> nu \<Longrightarrow> nullablePass ps nu = insert x (nullablePass ps nu)"
  using nullablePass_subset by fastforce

lemma nullable_gamma_nullableGamma_true:
  "nullable_gamma g ys \<Longrightarrow> \<forall>x. (NT x) \<in> set ys \<longrightarrow> x \<in> nu \<Longrightarrow> nullableGamma ys nu"
  by (induction rule: nullableGamma.induct; force elim: nullable_gamma.cases nullable_sym.cases)

lemma nullableGamma_saturated_if_nullablePass_fixpoint:
  assumes "nu = nullablePass ps nu"
  shows "\<forall>(x, gamma) \<in> set ps. nullableGamma gamma nu \<longrightarrow> x \<in> nu"
  using assms nullablePass_add_equal by (induction ps) (fastforce split: if_split_asm)+

lemma nullablePass_equal_complete':
  assumes "nu = nullablePass (prods g) nu"
  shows "nullable_sym g s \<Longrightarrow> \<forall>y. s = NT y \<longrightarrow> y \<in> nu"
    "nullable_gamma g ys \<Longrightarrow> \<forall>y. NT y \<in> set ys \<longrightarrow> y \<in> nu"
  using assms
proof (induction rule: nullable_sym_nullable_gamma.inducts)
  case (NullableSym x gamma)
  then show ?case
    using nullableGamma_saturated_if_nullablePass_fixpoint nullable_gamma_nullableGamma_true
    by force
qed auto

lemma nullablePass_equal_complete: "nu = (nullablePass (prods g) nu) \<Longrightarrow> nullable_set_complete nu g"
  by (simp add: nullablePass_equal_complete' nullable_set_complete_def)

lemma mkNullableSet'_complete: "nullable_set_complete (mkNullableSet' (prods g) nu) g"
proof (induction "prods g" nu rule: mkNullableSet'.induct)
  case (1 nu)
  then show ?case
    by (subst mkNullableSet'.simps)
      (simp add: Let_def nullable_set_complete_def nullablePass_equal_complete')
qed

theorem mkNullableSet_complete: "nullable_set_complete (mkNullableSet g) g"
  unfolding mkNullableSet_def
  using mkNullableSet'_complete by blast

theorem mkNullableSet_correct: "nullable_set_for (mkNullableSet g) g"
  using mkNullableSet_sound mkNullableSet_complete by auto

end