(* Title:     MiniML/Generalize.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Generalizing type schemes with respect to a context"

theory Generalize
imports Instance
begin

\<comment> \<open>@{text gen}: binding (generalising) the variables which are not free in the context\<close>

type_synonym ctxt = "type_scheme list"
    
primrec gen :: "[ctxt, typ] => type_scheme" where
  "gen A (TVar n) = (if (n:(free_tv A)) then (FVar n) else (BVar n))"
| "gen A (t1 -> t2) = (gen A t1) =-> (gen A t2)"

\<comment> \<open>executable version of @{text gen}: implementation with @{text free_tv_ML}\<close>

primrec gen_ML_aux :: "[nat list, typ] => type_scheme" where
  "gen_ML_aux A (TVar n) = (if (n: set A) then (FVar n) else (BVar n))"
| "gen_ML_aux A (t1 -> t2) = (gen_ML_aux A t1) =-> (gen_ML_aux A t2)"

definition gen_ML :: "[ctxt, typ] => type_scheme" where
  gen_ML_def: "gen_ML A t = gen_ML_aux (free_tv_ML A) t"

declare equalityE [elim!]

lemma gen_eq_on_free_tv: 
    "free_tv A = free_tv B \<Longrightarrow> gen A t = gen B t"
  by (induct t) simp_all

lemma gen_without_effect [simp]:
    "(free_tv t) \<subseteq> (free_tv sch) \<Longrightarrow> gen sch t = (mk_scheme t)"
  by (induct t) auto

lemma free_tv_gen [simp]: 
  "free_tv (gen ($ S A) t) = free_tv t Int free_tv ($ S A)"
by (induct t) auto

lemma free_tv_gen_cons [simp]: 
  "free_tv (gen ($ S A) t # $ S A) = free_tv ($ S A)"
  by fastforce

lemma bound_tv_gen [simp]: 
  "bound_tv (gen A t) = free_tv t - free_tv A"
by (induction t) auto

lemma new_tv_compatible_gen: "new_tv n t \<Longrightarrow> new_tv n (gen A t)"
by (induction t) auto

lemma gen_eq_gen_ML: "gen A t = gen_ML A t"
  unfolding gen_ML_def
  by (induct t) (auto simp: free_tv_ML_scheme_list)

lemma gen_subst_commutes: 
  "free_tv S \<inter> (free_tv t - free_tv A) = {} \<Longrightarrow> gen ($ S A) ($ S t) = $ S (gen A t)"
proof (induct t)
  case (TVar x)
  show ?case
  proof (cases "x \<in> free_tv A")
    case True
    then show ?thesis
      by simp  
  next
    case False
    then have "x \<notin> free_tv S"
      using TVar Type.free_tv_TVar by blast
    then show ?thesis
      using False free_tv_app_subst_scheme_list free_tv_subst not_free_impl_id
      by fastforce
  qed
next
  case (Fun t1 t2)
  then show ?case
    by (simp add: Diff_eq Int_Un_distrib2 disjoint_iff)
qed

lemma gen_bound_typ_instance:  "gen ($ S A) ($ S t) \<le> $ S (gen A t)"
proof -
  have "bound_typ_inst R (gen ($ S A) ($ S t)) =
       bound_typ_inst (\<lambda>a. bound_typ_inst R (gen ($ S A) (S a)))
        ($ S (gen A t))" for R
    by (induction t) auto
  then show ?thesis
    using is_bound_typ_instance le_type_scheme_def by auto
qed

lemma free_tv_subset_gen_le: 
  assumes "free_tv B \<subseteq> free_tv A"
  shows "gen A t \<le> gen B t"
proof -
  have "bound_typ_inst S (gen A t) =
       bound_typ_inst (\<lambda>b. if b \<in> free_tv A then TVar b else S b) (gen B t)" for S
    using assms
    by (induction t) force+
  then show ?thesis
    using is_bound_typ_instance le_type_scheme_def by auto
qed

lemma gen_t_le_gen_alpha_t [simp]: 
  assumes "new_tv n A"
  shows "gen A t \<le> gen A ($ (\<lambda>x. TVar (if x \<in> free_tv A then x else n + x)) t)"
proof -
  have "bound_typ_inst S (gen A t) =
       bound_typ_inst (\<lambda>x. S (if n \<le> x then x - n else x))
        (gen A ($ (\<lambda>x. TVar (if x \<in> free_tv A then x else n + x)) t))" for S
  proof (induction t)
    case (TVar x)
    then show ?case
      using assms free_tv_le_new_tv by auto
  next
    case (Fun t1 t2)
    then show ?case
      by force
  qed
  then show ?thesis
    using is_bound_typ_instance le_type_scheme_def by auto
qed

end
