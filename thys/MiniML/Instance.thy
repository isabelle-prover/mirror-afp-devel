(* Title:     MiniML/Instance.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Instances of type schemes"

theory Instance
imports Type
begin

primrec bound_typ_inst :: "[subst, type_scheme] => typ" where
  "bound_typ_inst S (FVar n) = (TVar n)"
| "bound_typ_inst S (BVar n) = (S n)"
| "bound_typ_inst S (sch1 =-> sch2) = ((bound_typ_inst S sch1) -> (bound_typ_inst S sch2))"

primrec bound_scheme_inst :: "[nat => type_scheme, type_scheme] => type_scheme" where
  "bound_scheme_inst S (FVar n) = (FVar n)"
| "bound_scheme_inst S (BVar n) = (S n)"
| "bound_scheme_inst S (sch1 =-> sch2) = ((bound_scheme_inst S sch1) =-> (bound_scheme_inst S sch2))"
  
definition is_bound_typ_instance :: "[typ, type_scheme] => bool"  (infixr \<open><|\<close> 70) where
  is_bound_typ_instance: "t <| sch = (\<exists>S. t = (bound_typ_inst S sch))"

instantiation type_scheme :: ord
begin

definition
  le_type_scheme_def: "sch' \<le> (sch::type_scheme) \<longleftrightarrow> (\<forall>t. t <| sch' \<longrightarrow> t <| sch)"

definition
  "(sch' < (sch :: type_scheme)) \<longleftrightarrow> sch' \<le> sch \<and> sch' \<noteq> sch"

instance ..

end

primrec subst_to_scheme :: "[nat => type_scheme, typ] => type_scheme" where
  "subst_to_scheme B (TVar n) = (B n)"
| "subst_to_scheme B (t1 -> t2) = ((subst_to_scheme B t1) =-> (subst_to_scheme B t2))"
  
instantiation list :: (ord) ord
begin

definition
  le_env_def: "A \<le> B \<longleftrightarrow> length B = length A \<and> (\<forall>i. i < length A \<longrightarrow> A!i \<le> B!i)"

definition
  "(A < (B :: 'a list)) \<longleftrightarrow> A \<le> B \<and> A \<noteq> B"

instance ..

end

text "lemmas for instatiation"

lemma bound_typ_inst_mk_scheme [simp]: "bound_typ_inst S (mk_scheme t) = t"
  by (induct t) simp_all

lemma bound_typ_inst_composed_subst [simp]:
    "bound_typ_inst ($S \<circ> R) ($S sch) = $S (bound_typ_inst R sch)"
  by (induct sch) simp_all

lemma bound_typ_inst_eq:
    "S = S' \<Longrightarrow> sch = sch' \<Longrightarrow> bound_typ_inst S sch = bound_typ_inst S' sch'"
  by simp

lemma bound_scheme_inst_mk_scheme [simp]:
    "bound_scheme_inst B (mk_scheme t) = mk_scheme t"
  by (induct t) simp_all

lemma substitution_lemma: "$S (bound_scheme_inst B sch) = (bound_scheme_inst ($S \<circ> B) ($ S sch))"
  by (induct sch) simp_all

lemma bound_scheme_inst_type:
    "mk_scheme t = bound_scheme_inst B sch \<Longrightarrow>
          (\<exists>S. \<forall>x\<in>bound_tv sch. B x = mk_scheme (S x))"
proof (induction "sch" arbitrary: t)
  case (BVar x)
  then show ?case
    by (force intro: sym)
next
  case (SFun type_scheme1 type_scheme2 t)
  obtain S1 where S1: "\<forall>x\<in>bound_tv type_scheme1. B x = mk_scheme (S1 x)"
    by (metis SFun.IH(1) SFun.prems bound_scheme_inst.simps(3) mk_scheme_Fun)
  obtain S2 where S2: "\<forall>x\<in>bound_tv type_scheme2. B x = mk_scheme (S2 x)"
    by (metis SFun.IH(2) SFun.prems bound_scheme_inst.simps(3) mk_scheme_Fun)
  let ?S = "\<lambda>x. if x:bound_tv type_scheme1 then (S1 x) else (S2 x)"
  show ?case
  proof
    show "\<forall>x\<in>bound_tv (type_scheme1 =-> type_scheme2). B x = mk_scheme (?S x)"
      using S1 S2 by auto
  qed
qed auto

lemma subst_to_scheme_inverse: 
  "new_tv n sch \<Longrightarrow>
    subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k)  
      (bound_typ_inst (\<lambda>k. TVar (k + n)) sch) = sch"
by (induction sch) auto

lemma aux: "t = t' \<Longrightarrow>  
      subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) t =  
      subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) t'"
  by blast

lemma aux2: "new_tv n sch \<Longrightarrow>
  subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) (bound_typ_inst S sch) =  
    bound_scheme_inst ((subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k)) \<circ> S) sch"
    by (induct sch) auto

lemma le_type_scheme_def2:
  fixes sch sch' :: type_scheme
  shows "(sch' \<le> sch) = (\<exists>B. sch' = bound_scheme_inst B sch)"
proof -
  have *: "bound_typ_inst S (bound_scheme_inst B sch) =
           bound_typ_inst (\<lambda>n. bound_typ_inst S (B n)) sch" for S B
    by (induction sch) auto
  show ?thesis
    by (metis (no_types, lifting) "*" aux2 fresh_variable_type_schemes
        is_bound_typ_instance le_type_scheme_def new_tv_Fun2 subst_to_scheme_inverse)
qed

lemma le_type_eq_is_bound_typ_instance: "(mk_scheme t) \<le> sch = t <| sch"
  using bound_typ_inst_mk_scheme is_bound_typ_instance le_type_scheme_def by presburger

lemma le_env_Cons [iff]: 
  "(sch # A \<le> sch' # B) = (sch \<le> (sch'::type_scheme) \<and> A \<le> B)"
proof (intro iffI)
  assume "sch # A \<le> sch' # B" then show "sch \<le> sch' \<and> A \<le> B"
    by (smt (verit) Suc_length_conv Suc_mono le_env_def nat.inject nth_Cons_0
      nth_Cons_Suc zero_less_Suc)
next
  assume "sch \<le> sch' \<and> A \<le> B" then show "sch # A \<le> sch' # B"
    by (smt (verit, ccfv_SIG) le_env_def length_Cons less_Suc_eq_0_disj nth_Cons_0
        nth_Cons_Suc)
qed

lemma is_bound_typ_instance_closed_subst: "t <| sch \<Longrightarrow> $S t <| $S sch"
  by (metis bound_typ_inst_composed_subst is_bound_typ_instance)

lemma S_compatible_le_scheme:
  fixes sch sch' :: type_scheme
  shows "sch' \<le> sch \<Longrightarrow> $S sch' \<le> $ S sch"
  using le_type_scheme_def2 substitution_lemma
  by force

lemma S_compatible_le_scheme_lists: 
  fixes A A' :: "type_scheme list"
  shows "A' \<le> A \<Longrightarrow> $S A' \<le> $ S A"
  by (simp add: S_compatible_le_scheme le_env_def nth_subst)

lemma bound_typ_instance_trans: "[| t <| sch; sch \<le> sch' |] ==> t <| sch'"
  unfolding le_type_scheme_def by blast

lemma le_type_scheme_refl [iff]: "sch \<le> (sch::type_scheme)"
  unfolding le_type_scheme_def by blast

lemma le_env_refl [iff]: "A \<le> (A::type_scheme list)"
  unfolding le_env_def by blast

lemma bound_typ_instance_BVar [iff]: "sch \<le> BVar n"
  using le_type_scheme_def2 by auto

lemma le_FVar [simp]: "(sch \<le> FVar n) = (sch = FVar n)"
  by (simp add: le_type_scheme_def2)

lemma not_FVar_le_Fun [iff]: "~(FVar n \<le> sch1 =-> sch2)"
  unfolding le_type_scheme_def is_bound_typ_instance by simp

lemma not_BVar_le_Fun [iff]: "~(BVar n \<le> sch1 =-> sch2)"
  by (simp add: le_type_scheme_def2)

lemma Fun_le_FunD: 
  "(sch1 =-> sch2 \<le> sch1' =-> sch2') \<Longrightarrow> sch1 \<le> sch1' \<and> sch2 \<le> sch2'"
  unfolding le_type_scheme_def is_bound_typ_instance by fastforce

lemma scheme_le_Fun: "(sch' \<le> sch1 =-> sch2) \<Longrightarrow> \<exists>sch'1 sch'2. sch' = sch'1 =-> sch'2"
  by (induct sch') auto

lemma le_type_scheme_free_tv:
  fixes sch'::type_scheme
  shows "sch \<le> sch' \<Longrightarrow> free_tv sch' \<le> free_tv sch"
proof (induction "sch" arbitrary: sch')
  case (FVar x)
  then show ?case
    by (induction "sch'") auto
next
  case (BVar x)
  then show ?case
    by (induction "sch'") auto
next
  case (SFun sch1 sch2)
  then show ?case
  proof (induction sch')
    case (SFun sch'1 sch'2)
    then show ?case
      by (metis Fun_le_FunD Un_mono free_tv_type_scheme.simps(3))
  qed auto
qed

lemma le_env_free_tv:
  fixes A :: "type_scheme list"
  assumes "A \<le> B"
  shows "free_tv B \<le> free_tv A"
  using assms
proof (induction B arbitrary: A)
  case Nil
  then show ?case
    by auto
next
  case (Cons b B)
  then obtain a A' where "A = a # A'" "a \<le> b" "A' \<le> B"
    by (metis le_env_Cons le_env_def length_0_conv neq_Nil_conv)
  with Cons show ?case
    using le_type_scheme_free_tv by fastforce
qed

end
