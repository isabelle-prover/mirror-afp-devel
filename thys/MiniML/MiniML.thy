(* Title:     MiniML/MiniML.thy
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "MiniML with type inference rules"

theory MiniML
imports Generalize
begin

\<comment> \<open>expressions\<close>
datatype
  expr = Var nat | Abs expr | App expr expr | LET expr expr

\<comment> \<open>type inference rules\<close>
inductive
  has_type :: "[ctxt, expr, typ] => bool"
                  (\<open>((_) \<turnstile>/ (_) :: (_))\<close> [60,0,60] 60)
where
  VarI: "[| n < length A; t <| A!n |] ==> A \<turnstile> Var n :: t"
| AbsI: "[| (mk_scheme t1)#A \<turnstile> e :: t2 |] ==> A \<turnstile> Abs e :: t1 -> t2"
| AppI: "[| A \<turnstile> e1 :: t2 -> t1; A \<turnstile> e2 :: t2 |] 
         ==> A \<turnstile> App e1 e2 :: t1"
| LETI: "[| A \<turnstile> e1 :: t1; (gen A t1)#A \<turnstile> e2 :: t |] ==> A \<turnstile> LET e1 e2 :: t"

declare has_type.intros [simp]
declare Un_upper1 [simp] Un_upper2 [simp]
declare is_bound_typ_instance_closed_subst [simp]

lemma s'_t_equals_s_t[simp]: 
  "\<And>t::typ. $(\<lambda>n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) t = $S t"
  using UnCI eq_free_eq_subst_te by fastforce

lemma s'_a_equals_s_a [simp]: 
  "\<And>A::type_scheme list. $(\<lambda>n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) A = $S A"
  using eq_free_eq_subst_scheme_list by fastforce

lemma replace_s_by_s': 
   "$(\<lambda>n. if n \<in> free_tv A \<union> free_tv t then S n else TVar n) A
     \<turnstile> e :: $(\<lambda>n. if n \<in> free_tv A \<union> free_tv t then S n else TVar n) t  
  \<Longrightarrow> $S A \<turnstile> e :: $S t"
  by (metis (mono_tags, lifting) s'_a_equals_s_a s'_t_equals_s_t)

lemma alpha_A': 
  "\<And>A::type_scheme list. $ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) A = $ id_subst A"
  by (simp add: eq_free_eq_subst_scheme_list id_subst_def)

lemma alpha_A: 
  "\<And>A::type_scheme list. $ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) A = A"
  by (simp add: alpha_A')

lemma S_o_alpha_typ: 
  "$ (S \<circ> alpha) (t::typ) = $ S ($ (\<lambda>x. TVar (alpha x)) t)"
  by (induct_tac "t") auto

lemma S_o_alpha_type_scheme: 
  "$ (S \<circ> alpha) (sch::type_scheme) = $ S ($ (\<lambda>x. TVar (alpha x)) sch)"
  by (induct_tac "sch") auto

lemma S_o_alpha_type_scheme_list: 
  "$ (S \<circ> alpha) (A::type_scheme list) = $ S ($ (\<lambda>x. TVar (alpha x)) A)"
proof (induction "A")
  case Nil
  then show ?case by auto
next
  case (Cons a A)
  then show ?case
    by (metis S_o_alpha_type_scheme app_subst_Cons)
qed

lemma S'_A_eq_S'_alpha_A: "\<And>A::type_scheme list.  
      $ (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) A =  
      $ ((\<lambda>x. if x : free_tv A Un free_tv t then S x else TVar x) \<circ>  
         (\<lambda>x. if x : free_tv A then x else n + x)) A"
  using eq_free_eq_subst_scheme_list by fastforce

lemma dom_S': 
 "dom (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq> free_tv A Un free_tv t"
  using Type.dom_def by auto

lemma cod_S': 
  "\<And>(A::type_scheme list) (t::typ).   
   cod (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq>  
   free_tv ($ S A) Un free_tv ($ S t)"
  unfolding free_tv_subst cod_def subset_eq Type.dom_def
  by (smt (verit, del_insts)  UN_iff Un_iff
      free_tv_of_substitutions_extend_to_scheme_lists
      free_tv_of_substitutions_extend_to_types mem_Collect_eq subsetD)

lemma free_tv_S': 
 "\<And>(A::type_scheme list) (t::typ).  
  free_tv (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq>  
  free_tv A Un free_tv ($ S A) Un free_tv t Un free_tv ($ S t)"
  unfolding free_tv_subst
  using dom_S' cod_S' by blast

lemma free_tv_alpha: 
  fixes t1::"typ"
  shows "(free_tv ($ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) t1) - free_tv A) \<subseteq>  
          {x. \<exists>y. x = n + y}" 
  by (induction t1) auto

lemma new_tv_Int_free_tv_empty_type: "new_tv n t \<Longrightarrow> {x. \<exists>y. x = n + y} \<inter> free_tv t = {}"
  using free_tv_le_new_tv by fastforce

lemma new_tv_Int_free_tv_empty_scheme_list:
  fixes A :: "type_scheme list"
  shows "new_tv n A \<Longrightarrow> {x. \<exists>y. x = n + y} \<inter> free_tv A = {}"
proof (induction A)
  case Nil
  then show ?case
    by auto
next
  case (Cons a A)
  then show ?case
    using new_tv_Int_free_tv_empty_type by blast
qed

declare has_type.intros [intro!]

lemma has_type_le_env: "A \<turnstile> e::t \<Longrightarrow> A \<le> B \<Longrightarrow> B \<turnstile> e::t"
proof (induction arbitrary: B rule: has_type.induct)
  case (VarI n A t)
  then show ?case
    by (simp add: le_env_def le_type_scheme_def)
next
  case (LETI A e1 t1 e2 t)
  then show ?case
    by (meson free_tv_subset_gen_le has_type.LETI le_env_Cons le_env_free_tv)
qed auto

\<comment> \<open>@{text has_type} is closed w.r.t. substitution\<close>
lemma has_type_cl_sub: "A \<turnstile> e :: t \<Longrightarrow> $S A \<turnstile> e :: $S t"
proof (induction arbitrary: S rule: has_type.induct)
  case (LETI A e1 t1 e2 t)
  obtain n where n: "new_tv n ($ S A)" "new_tv n A" "new_tv n t"
                    "new_tv n ($ S t)"
    using ex_fresh_variable by blast
  define F where "F \<equiv> \<lambda>i. if i \<in> free_tv A \<union> free_tv t then S i else TVar i"
  define G where "G \<equiv> \<lambda>i. if i \<in> free_tv A then i else n + i"
  have 1: "$ (F \<circ> G) A \<turnstile> e1 :: $ (F \<circ> G) t1"
    by (simp add: LETI.IH)
  have "free_tv F \<subseteq> free_tv A Un free_tv ($ S A) Un free_tv t Un free_tv ($ S t)"
    using F_def free_tv_S' by presburger
  moreover
  have "(free_tv ($ (\<lambda>i. TVar (G i)) t1) - free_tv A) \<subseteq> {x. \<exists>y. x = n + y}"
    by (simp add: G_def free_tv_alpha)
  ultimately
  have "free_tv F \<inter> (free_tv ($ (\<lambda>i. TVar (G i)) t1) - free_tv A) = {}"
    using not_add_less1 n by (fastforce simp: new_tv_def)
  moreover
  have "gen A t \<le> gen A ($ (\<lambda>i. TVar (G i)) t)" for t
    using n(2) by (auto simp: G_def)
  then have "$ F (gen A ($ (\<lambda>i. TVar (G i)) t1)) # $ F A \<turnstile> e2 :: $ F t"
    using LETI.IH(2) S_compatible_le_scheme has_type_le_env by fastforce
  ultimately have "$ F A \<turnstile> LET e1 e2 :: $ F t"
    by (metis (mono_tags, lifting) "1" G_def has_type.LETI S_o_alpha_typ
        comp_apply eq_free_eq_subst_scheme_list gen_subst_commutes)
  then show ?case
    by (metis F_def Un_iff eq_free_eq_subst_scheme_list typ_substitutions_only_on_free_variables)
qed (auto simp: nth_subst)

end
