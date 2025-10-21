theory Datalog imports Main begin


section \<open>Datalog programs and their solutions\<close>

datatype (vars_id: 'x,'c) id = 
  is_Var: Var 'x 
  | is_Cst: Cst (the_Cst: 'c)

datatype (preds_rh: 'p,'x,'c) rh = 
  Eql "('x,'c) id" "('x,'c) id" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'c) id" "('x,'c) id" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosLit 'p "('x,'c) id list" ("\<^bold>+ _ _" [61, 61] 61)
  | NegLit 'p "('x,'c) id list" ("\<^bold>\<not> _ _" [61, 61] 61)

type_synonym ('p,'x,'c) lh = "'p \<times> ('x,'c) id list"

fun preds_lh :: "('p,'x,'c) lh \<Rightarrow> 'p set" where 
  "preds_lh (p,ids) = {p}"

datatype (preds_cls: 'p, 'x,'c) clause = Cls 'p "('x,'c) id list" (the_rhs: "('p,'x,'c) rh list")

fun the_lh where
  "the_lh (Cls p ids rhs) = (p,ids)"

type_synonym ('p,'x,'c) dl_program = "('p,'x,'c) clause set"

definition "preds_dl dl = \<Union>{preds_cls c| c. c \<in> dl}"

lemma preds_dl_union[simp]: "preds_dl (dl1 \<union> dl2) = preds_dl dl1 \<union> preds_dl dl2"
  unfolding preds_dl_def by auto

type_synonym ('x,'c) var_val = "'x \<Rightarrow> 'c"

type_synonym ('p,'c) pred_val = "'p \<Rightarrow> 'c list set"


fun eval_id :: "('x,'c) id \<Rightarrow> ('x,'c) var_val \<Rightarrow> 'c" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d") where
  "\<lbrakk>Var x\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<sigma> x"
| "\<lbrakk>Cst c\<rbrakk>\<^sub>i\<^sub>d \<sigma> = c"

fun eval_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) var_val \<Rightarrow> 'c list" ("\<lbrakk>_\<rbrakk>\<^sub>i\<^sub>d\<^sub>s") where
  "\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>) ids"

fun meaning_rh :: "('p,'x,'c) rh \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h") where
  "\<lbrakk>a \<^bold>= a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma> = \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>a \<^bold>\<noteq> a'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma>  \<noteq> \<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
| "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"
| "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<not> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>r\<^sub>h\<^sub>s") where
  "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<forall>rh \<in> set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

fun meaning_lh :: "('p,'x,'c) lh \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>l\<^sub>h") where
  "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma> \<longleftrightarrow> \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<in> \<rho> p"

fun meaning_cls :: "('p,'x,'c) clause \<Rightarrow> ('p,'c) pred_val \<Rightarrow> ('x,'c) var_val \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>\<^sub>c\<^sub>l\<^sub>s") where
  "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma> \<longleftrightarrow> (\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma> \<longrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)" 

fun solves_lh :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) lh \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>l\<^sub>h" 91) where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p,ids) \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>)"

fun solves_rh :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) rh \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>r\<^sub>h" 91) where 
  "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>)"

definition solves_cls :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) clause \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>c\<^sub>l\<^sub>s" 91) where
  "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> (\<forall>\<sigma>. \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>)"

definition solves_program :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>d\<^sub>l" 91) where
  "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> (\<forall>c \<in> dl. \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c)"


section \<open>Substitutions\<close>

type_synonym ('x,'c) subst = "'x \<Rightarrow> ('x,'c) id"

fun subst_id :: "('x,'c) id \<Rightarrow> ('x,'c) subst \<Rightarrow> ('x,'c) id" (infix "\<cdot>\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>i\<^sub>d \<eta>  = \<eta> x"
| "(Cst e) \<cdot>\<^sub>i\<^sub>d \<eta> = (Cst e)"

fun subst_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) subst \<Rightarrow> ('x,'c) id list" (infix "\<cdot>\<^sub>i\<^sub>d\<^sub>s" 50) where
  "ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>i\<^sub>d \<eta>) ids"

fun subst_rh :: "('p,'x,'c) rh \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) rh" (infix "\<cdot>\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>= a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>r\<^sub>h \<eta> = (a \<cdot>\<^sub>i\<^sub>d \<eta> \<^bold>\<noteq> a' \<cdot>\<^sub>i\<^sub>d \<eta>)"
| "(\<^bold>+ p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (\<^bold>+ p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>r\<^sub>h \<eta> = (\<^bold>\<not> p ( ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>))"

fun subst_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) rh list" (infix "\<cdot>\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta> = map (\<lambda>a. a \<cdot>\<^sub>r\<^sub>h \<eta>) rhs"

fun subst_lh :: "('p,'x,'c) lh \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) lh" (infix "\<cdot>\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>l\<^sub>h \<eta> = (p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>)"

fun subst_cls :: "('p,'x,'c) clause \<Rightarrow> ('x,'c) subst \<Rightarrow> ('p,'x,'c) clause" (infix "\<cdot>\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta>  = Cls p (ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>) (rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>)"

definition compose :: "('x,'c) subst \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) var_val" (infix "\<circ>\<^sub>s\<^sub>v" 50) where
  "(\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) x = \<lbrakk>(\<eta> x)\<rbrakk>\<^sub>i\<^sub>d \<sigma>"


section \<open>Substituting variable valuations\<close>

fun substv_id :: "('x,'c) id \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) id" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d" 70) where
  "(Var x) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = Cst (\<sigma> x)"
| "(Cst e) \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> = (Cst e)"

fun substv_ids :: "('x,'c) id list \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('x,'c) id list" (infix "\<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s" 50) where
  "ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>) ids"

fun substv_rh :: "('p,'x,'c) rh \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) rh" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h" 50) where
  "(a \<^bold>= a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>= a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(a \<^bold>\<noteq> a') \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma> \<^bold>\<noteq> a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
| "(\<^bold>+ p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (\<^bold>+ p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"
| "(\<^bold>\<not> p ids) \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma> = (\<^bold>\<not> p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>))"

definition substv_rhs :: "('p,'x,'c) rh list \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) rh list" (infix "\<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s" 50) where
  "rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma> = map (\<lambda>a. a \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma>) rhs"

fun substv_lh :: "('p,'x,'c) lh \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) lh" (infix "\<cdot>\<^sub>v\<^sub>l\<^sub>h" 50) where
  "(p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma> = (p, ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"

fun substv_cls :: "('p,'x,'c) clause \<Rightarrow> ('x,'c) var_val \<Rightarrow> ('p,'x,'c) clause" (infix "\<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s" 50) where
  "(Cls p ids rhs) \<cdot>\<^sub>v\<^sub>c\<^sub>l\<^sub>s \<sigma>  = Cls p (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>) (rhs \<cdot>\<^sub>v\<^sub>r\<^sub>h\<^sub>s \<sigma>)"


section \<open>Datalog lemmas\<close>

subsection \<open>Variable valuations\<close>

lemma substv_id_is_Cst_eval_id:
  "a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>' = Cst (\<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>')"
  by (cases a') auto

lemma eval_id_is_substv_id:
  "\<lbrakk>a'\<rbrakk>\<^sub>i\<^sub>d \<sigma>' = \<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d \<sigma> \<longleftrightarrow> (a' \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>') = (a \<cdot>\<^sub>v\<^sub>i\<^sub>d \<sigma>)"
  by (cases a'; cases a) auto

lemma eval_ids_is_substv_ids:
  "\<lbrakk>ids'\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>' = \<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma> \<longleftrightarrow> (ids' \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>') = (ids \<cdot>\<^sub>v\<^sub>i\<^sub>d\<^sub>s \<sigma>)"
proof (induction ids' arbitrary: ids)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a ids')
  note Cons_outer = Cons
  show ?case
  proof (cases ids)
    case Nil
    then show ?thesis
      using Cons_outer by auto
  next
    case (Cons a list)
    then show ?thesis
      using eval_id_is_substv_id Cons_outer by force
  qed
qed

lemma solves_rh_substv_rh_if_meaning_rh:
  assumes "\<lbrakk>a\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h (a \<cdot>\<^sub>v\<^sub>r\<^sub>h \<sigma>)"
using assms proof (induction a)
  case (Eql a a')
  then show ?case 
    by (auto simp add: eval_id_is_substv_id)
next
  case (Neql a a')
  then show ?case
    using eval_id_is_substv_id by (auto simp add: substv_id_is_Cst_eval_id) 
next
  case (PosLit p ids)
  then show ?case 
    by (auto simp add: substv_id_is_Cst_eval_id comp_def eval_id_is_substv_id) 
next
  case (NegLit p ids)
  then show ?case 
    by (auto simp add: substv_id_is_Cst_eval_id comp_def eval_id_is_substv_id) 
qed

lemma solves_lh_substv_lh_if_meaning_lh:
  assumes "\<lbrakk>a\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (a \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
proof -
  obtain p ids where a_split: "a = (p, ids)"
    by (cases a)
  show ?thesis
    using assms unfolding a_split
    by (auto simp add: substv_id_is_Cst_eval_id comp_def eval_id_is_substv_id) 
qed


subsection \<open>Solve lhs\<close>

lemma solves_lh_iff_solves_lh: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>+ p ids)"
  using solves_cls_def by force

lemma solves_lh_lh:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args []"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, args)"
  using assms unfolding solves_cls_def by auto

lemmas solve_lhs = solves_lh_iff_solves_lh solves_lh_lh


subsection \<open>Propositional inferences\<close>


subsubsection \<open>Of last right hand\<close>

lemma prop_inf_last_from_cls_rh_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids (rhs @ [rh])"
  assumes "\<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  using assms unfolding solves_cls_def by auto

lemma prop_inf_last_from_cls_lh_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids (rhs @ [\<^bold>+ p ids])"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  using assms by (force simp add: solves_cls_def)

lemmas prop_inf_last = prop_inf_last_from_cls_rh_to_cls prop_inf_last_from_cls_lh_to_cls


subsubsection \<open>Of only right hand\<close>

lemma modus_ponens_rh:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [\<^bold>+ p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p', ids')"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  using assms
proof -
  from assms(2) have "\<forall>\<sigma>. \<lbrakk>\<^bold>+ p' ids'\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    by fastforce
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
    using assms(1) self_append_conv2 solves_rh.elims(3) prop_inf_last_from_cls_rh_to_cls by metis 
  then show "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
    by (meson solves_lh_lh)
qed

lemma prop_inf_only_from_cls_cls_to_cls:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids [\<^bold>+ p' ids']"
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p' ids' []"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids []"
  by (metis append_self_conv2 assms prop_inf_last_from_cls_rh_to_cls solves_lh_iff_solves_lh)

lemmas prop_inf_only = modus_ponens_rh prop_inf_only_from_cls_cls_to_cls


subsubsection \<open>Of all right hands\<close>

lemma modus_ponens:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  assumes "\<forall>rh\<in>set rhs. \<rho> \<Turnstile>\<^sub>r\<^sub>h rh"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids)"
  using assms unfolding solves_cls_def meaning_lh.simps by force

lemmas prop_inf_all = modus_ponens

lemmas prop_inf = prop_inf_last prop_inf_only prop_inf_all

subsection \<open>Substitution\<close>

lemma substitution_lemma_id: "\<lbrakk>a\<rbrakk>\<^sub>i\<^sub>d (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>a \<cdot>\<^sub>i\<^sub>d \<eta>\<rbrakk>\<^sub>i\<^sub>d \<sigma>"
  by (cases a) (auto simp add: compose_def)

lemma substitution_lemma_ids: "\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>"
  using substitution_lemma_id by auto

lemma substitution_lemma_lh: "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>(p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta> )\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  by (metis meaning_lh.simps substitution_lemma_ids)

lemma substitution_lemma_rh:"\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>rh \<cdot>\<^sub>r\<^sub>h \<eta>\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (induction rh)
  case (Eql a a')
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (Neql a a')
  then show ?case
    by (simp add: substitution_lemma_id)
next
  case (PosLit p ids)
  then show ?case
    using substitution_lemma_lh by fastforce
next
  case (NegLit p ids)
  then show ?case
    using substitution_lemma_lh by fastforce
qed

lemma substitution_lemma_rhs: "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) \<longleftrightarrow> \<lbrakk>rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
  by (simp add: substitution_lemma_rh) 

lemma substitution_lemma_cls:
  "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>c \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta>\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof (induction c)
  case (Cls p ids rhs)
  have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>rhs \<cdot>\<^sub>r\<^sub>h\<^sub>s \<eta>\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
    using substitution_lemma_rhs by blast
  moreover
  have  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>) = \<lbrakk>(p, ids \<cdot>\<^sub>i\<^sub>d\<^sub>s \<eta>)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    using substitution_lemma_lh by metis
  ultimately
  show ?case
    unfolding meaning_cls.simps by auto
qed

lemma substitution_lemma:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s (c \<cdot>\<^sub>c\<^sub>l\<^sub>s (\<eta>::('x,'c) subst))"
proof -
  show ?thesis
    unfolding solves_cls_def
  proof
    fix \<sigma> :: "'x \<Rightarrow> 'c"
    from assms have "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<eta> \<circ>\<^sub>s\<^sub>v \<sigma>)"
      using solves_cls_def by auto
    then show "\<lbrakk>c \<cdot>\<^sub>c\<^sub>l\<^sub>s \<eta> \<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
      using substitution_lemma_cls by blast
  qed
qed


section \<open>Stratification and solutions to stratified datalog programs\<close>

type_synonym 'p strat = "'p \<Rightarrow> nat"

fun rnk :: "'p strat \<Rightarrow> ('p,'x,'c) rh \<Rightarrow> nat" where
  "rnk s (a \<^bold>= a') = 0"
| "rnk s (a \<^bold>\<noteq> a') = 0"
| "rnk s (\<^bold>+ p ids) = s p"
| "rnk s (\<^bold>\<not> p ids) = 1 + s p"

fun strat_wf_cls :: "'p strat \<Rightarrow> ('p,'x,'c) clause \<Rightarrow> bool" where
  "strat_wf_cls s (Cls p ids rhs) \<longleftrightarrow> (\<forall>rh \<in> set rhs. s p \<ge> rnk s rh)"

definition strat_wf :: "'p strat \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> bool" where
  "strat_wf s dl \<longleftrightarrow> (\<forall>c \<in> dl. strat_wf_cls s c)"

definition max_stratum :: "'p strat \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> nat" where
  "max_stratum s dl = Max {s p | p ids rhs. Cls p ids rhs \<in> dl}"

fun pred_val_lte_stratum :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'c) pred_val" 
  ("_ \<le>\<le>\<le>_\<le>\<le>\<le> _" 0) where 
  "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) p = (if s p \<le> n then \<rho> p else {})"

fun dl_program_lte_stratum :: "('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'c) dl_program" 
  ("_ \<le>\<le>_\<le>\<le> _" 0) where 
  "(dl \<le>\<le>s\<le>\<le> n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p \<le> n}"

fun dl_program_on_stratum :: "('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> nat \<Rightarrow> ('p,'x,'c) dl_program" 
  ("_ ==_== _" 0) where 
  "(dl ==s== n) = {(Cls p ids rhs)| p ids rhs . (Cls p ids rhs) \<in> dl \<and> s p = n}"

\<comment> \<open>The ordering on predicate valuations from
     Flemming Nielson and Hanne Riis Nielson. 
     Program analysis (an appetizer). 
     CoRR,abs/2012.10086, 2020.\<close>
definition lt :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'c) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset> _") where
  "(\<rho> \<sqsubset>s\<sqsubset> \<rho>') \<longleftrightarrow> (\<exists>p. \<rho> p \<subset> \<rho>' p \<and>
                       (\<forall>p'. s p' = s p \<longrightarrow> \<rho> p' \<subseteq> \<rho>' p') \<and>
                       (\<forall>p'. s p' < s p \<longrightarrow> \<rho> p' = \<rho>' p'))"

\<comment> \<open>The ordering on predicate valuations from
     Teodor C. Przymusinski.
     On the declarative semantics of deductive databases and logic programs.
     In Jack Minker, editor, Foundations of Deductive Databases and Logic Programming,
       pages 193–216. Morgan Kaufmann, 1988.\<close>
definition lt_prz :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'c) pred_val \<Rightarrow> bool" ("_ \<sqsubset>_\<sqsubset>\<^sub>p\<^sub>r\<^sub>z _") where
  "(\<rho>\<^sub>M \<sqsubset>s\<sqsubset>\<^sub>p\<^sub>r\<^sub>z \<rho>\<^sub>N) \<longleftrightarrow> \<rho>\<^sub>N \<noteq> \<rho>\<^sub>M \<and> 
                     (\<forall>p\<^sub>A c\<^sub>A. c\<^sub>A \<in> \<rho>\<^sub>N p\<^sub>A - \<rho>\<^sub>M p\<^sub>A \<longrightarrow> (\<exists>p\<^sub>B c\<^sub>B. c\<^sub>B \<in> \<rho>\<^sub>M p\<^sub>B - \<rho>\<^sub>N p\<^sub>B \<and> s p\<^sub>A > s p\<^sub>B))"

definition lte :: "('p,'c) pred_val \<Rightarrow> 'p strat \<Rightarrow> ('p,'c) pred_val \<Rightarrow> bool" ("_ \<sqsubseteq>_\<sqsubseteq> _") where
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> = \<rho>' \<or> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"

definition least_solution :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool" 
  ("_ \<Turnstile>\<^sub>l\<^sub>s\<^sub>t") where
  "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>')"

definition minimal_solution :: "('p,'c) pred_val \<Rightarrow> ('p,'x,'c) dl_program \<Rightarrow> 'p strat \<Rightarrow> bool"
  ("_ \<Turnstile>\<^sub>m\<^sub>i\<^sub>n") where
  "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl \<and> (\<nexists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho>)"

lemma lte_def2:
  "(\<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>') \<longleftrightarrow> \<rho> \<noteq> \<rho>' \<longrightarrow> (\<rho> \<sqsubset>s\<sqsubset> \<rho>')"
  unfolding lte_def by auto


subsection \<open>Solving lower strata\<close>

lemma strat_wf_lte_if_strat_wf_lte:
  assumes "n > m"
  assumes "strat_wf s (dl \<le>\<le>s\<le>\<le> n)"
  shows "strat_wf s (dl \<le>\<le>s\<le>\<le> m)"
  using assms unfolding strat_wf_def by fastforce

lemma strat_wf_lte_if_strat_wf:
  assumes "strat_wf s dl"
  shows "strat_wf s (dl \<le>\<le>s\<le>\<le> n)"
  using assms unfolding strat_wf_def by auto

lemma meaning_lte_m_iff_meaning_rh:
  assumes "rnk s rh \<le> n"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  using assms equals0D meaning_rh.elims(3) pred_val_lte_stratum.simps by fastforce

lemma meaning_lte_m_iff_meaning_lh:
  assumes "s p \<le> m"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<sigma> \<longleftrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  using assms by auto

lemma meaning_lte_m_iff_meaning_cls:
  assumes "strat_wf_cls s (Cls p ids rhs)"
  assumes "s p \<le> m"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof -
  have p_leq_m: "s p \<le> m"
    using assms by fastforce
  have rh_leq_m: "\<forall>rh \<in> set rhs. rnk s rh \<le> m"
    using assms assms(2) dual_order.trans by (metis (no_types, lifting) p_leq_m strat_wf_cls.simps)

  show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    using meaning_lte_m_iff_meaning_rh[of s _ m \<rho> \<sigma>] p_leq_m rh_leq_m assms(2) by force
qed

lemma solves_lte_m_iff_solves_cls:
  assumes "strat_wf_cls s (Cls p ids rhs)"
  assumes "s p \<le> m"
  shows "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
  by (meson assms meaning_lte_m_iff_meaning_cls solves_cls_def)
                                          
lemma downward_lte_solves:
  assumes "n > m"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
  assumes "strat_wf s dl"
  shows "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)"
  unfolding solves_program_def
proof
  fix c
  assume a: "c \<in> (dl \<le>\<le>s\<le>\<le> m)"
  obtain p ids rhs where c_split: "c = Cls p ids rhs"
    by (cases c) auto

  have "m < n"
    using assms(1) by blast
  moreover
  have "strat_wf_cls s (Cls p ids rhs)"
    using a assms(3) c_split strat_wf_lte_if_strat_wf strat_wf_def by blast
  moreover
  have "s p \<le> m"
    using a c_split by force
  moreover
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    using c_split assms a unfolding solves_program_def by force  
  ultimately
  show "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_split by (simp add: solves_lte_m_iff_solves_cls)
qed

lemma downward_solves:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  assumes "strat_wf s dl"
  shows "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)"
  unfolding solves_program_def
proof
  fix c
  assume a: "c \<in> (dl \<le>\<le>s\<le>\<le> m)"
  then obtain p ids rhs where c_def: "c = Cls p ids rhs"
    by (cases c) auto

  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using \<open>c \<in> (dl \<le>\<le>s\<le>\<le> m)\<close> assms(1) solves_program_def by auto

  have "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
    using \<open>\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c\<close> a assms(2) c_def solves_lte_m_iff_solves_cls strat_wf_def by fastforce
  then show "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using c_def by auto
qed


subsection \<open>Least solutions\<close>


subsubsection \<open>Existence of least solutions\<close>

definition Inter' :: "('a \<Rightarrow> 'b set) set \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<^bold>\<Inter>") where 
  "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{\<rho> p | \<rho>. \<rho> \<in> \<rho>s})"

lemma Inter'_def2: "(\<^bold>\<Inter> \<rho>s) = (\<lambda>p. \<Inter>{m. \<exists>\<rho> \<in> \<rho>s. m = \<rho> p})"
  unfolding Inter'_def by auto

lemma member_Inter':
  assumes "\<forall>p \<in> ps. y \<in> p x"
  shows "y \<in> (\<^bold>\<Inter> ps) x"
  using assms unfolding Inter'_def by auto

lemma member_if_member_Inter':
  assumes "y \<in> (\<^bold>\<Inter> ps) x"
  assumes "p \<in> ps"
  shows "y \<in> p x"
  using assms unfolding Inter'_def by auto

lemma member_Inter'_iff:
  "(\<forall>p \<in> ps. y \<in> p x) \<longleftrightarrow> y \<in> (\<^bold>\<Inter> ps) x"
  unfolding Inter'_def by auto

lemma intersection_valuation_subset_valuation:
  assumes "P \<rho>"
  shows "\<^bold>\<Inter> {\<rho>'. P  \<rho>'} p \<subseteq> \<rho> p"
  using assms unfolding Inter'_def by auto

fun solve_pg where
  "solve_pg s dl 0 = (\<^bold>\<Inter> {\<rho>. \<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)})"
| "solve_pg s dl (Suc n) = (\<^bold>\<Inter> {\<rho>. \<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<and> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n})"

definition least_rank_p_st :: "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> ('p \<Rightarrow> nat) \<Rightarrow> bool" where 
  "least_rank_p_st P p s \<longleftrightarrow> P p \<and> (\<forall>p'. P p' \<longrightarrow> s p \<le> s p')"

lemma least_rank_p_st_exists:
  assumes "P p"
  shows "\<exists>p''. least_rank_p_st P p'' s"
  using assms
proof (induction "s p" arbitrary: p rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists>p''. s p'' < s p \<and> P p''")
    case True
    then show ?thesis
      using less by auto
  next
    case False
    then show ?thesis
      by (metis least_rank_p_st_def less.prems linorder_not_le)
  qed
qed

lemma below_least_rank_p_st:
  assumes "least_rank_p_st P p'' s"
  assumes "s p < s p''"
  shows "\<not>P p"
  using assms 
proof (induction "s p''")
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis least_rank_p_st_def linorder_not_le)
qed

lemma lt_if_lt_prz:
  assumes "\<rho>\<^sub>M \<sqsubset>s\<sqsubset>\<^sub>p\<^sub>r\<^sub>z \<rho>\<^sub>N"
  shows "\<rho>\<^sub>N \<sqsubset>s\<sqsubset> \<rho>\<^sub>M"
proof -
  from assms have unf: 
    "\<rho>\<^sub>N \<noteq> \<rho>\<^sub>M"
    "\<forall>p\<^sub>A c\<^sub>A. c\<^sub>A \<in> \<rho>\<^sub>N p\<^sub>A - \<rho>\<^sub>M p\<^sub>A \<longrightarrow> (\<exists>p\<^sub>B c\<^sub>B. c\<^sub>B \<in> \<rho>\<^sub>M p\<^sub>B - \<rho>\<^sub>N p\<^sub>B \<and> s p\<^sub>B < s p\<^sub>A)"
    unfolding lt_prz_def by auto
  then have "\<exists>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p"
    by auto
  then have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p) p s"
    using least_rank_p_st_exists by smt
  then obtain p where "least_rank_p_st (\<lambda>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p) p s"
    by auto
  have "\<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p"
    by (metis (mono_tags, lifting) \<open>least_rank_p_st (\<lambda>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p) p s\<close> least_rank_p_st_def)
  then have "(\<exists>c. c \<in> \<rho>\<^sub>M p \<and> c \<notin> \<rho>\<^sub>N p) \<or> (\<exists>c. c \<in> \<rho>\<^sub>N p \<and> c \<notin> \<rho>\<^sub>M p)"
    by auto
  then show "\<rho>\<^sub>N \<sqsubset>s\<sqsubset> \<rho>\<^sub>M"
  proof 
    assume "\<exists>c. c \<in> \<rho>\<^sub>M p \<and> c \<notin> \<rho>\<^sub>N p"
    then obtain c where "c \<in> \<rho>\<^sub>M p" "c \<notin> \<rho>\<^sub>N p"
      by auto
    have "(\<forall>p'. s p' < s p \<longrightarrow> \<rho>\<^sub>N p' = \<rho>\<^sub>M p')"
      using \<open>least_rank_p_st (\<lambda>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p) p s\<close> below_least_rank_p_st by fastforce
    have "(\<forall>p'. s p' = s p \<longrightarrow> \<rho>\<^sub>N p' \<subseteq> \<rho>\<^sub>M p')"
      using \<open>\<forall>p'. s p' < s p \<longrightarrow> \<rho>\<^sub>N p' = \<rho>\<^sub>M p'\<close> unf by auto
    then show ?thesis
      unfolding lt_def using \<open>\<forall>p'. s p' < s p \<longrightarrow> \<rho>\<^sub>N p' = \<rho>\<^sub>M p'\<close> \<open>\<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p\<close> by blast
  next 
    assume "\<exists>c. c \<in> \<rho>\<^sub>N p \<and> c \<notin> \<rho>\<^sub>M p"
    then obtain c where "c \<in> \<rho>\<^sub>N p \<and> c \<notin> \<rho>\<^sub>M p"
      by auto
    then have "\<exists>p\<^sub>B c\<^sub>B. c\<^sub>B \<in> \<rho>\<^sub>M p\<^sub>B - \<rho>\<^sub>N p\<^sub>B \<and> s p\<^sub>B < s p"
      using unf by auto
    then obtain p\<^sub>B c\<^sub>B where "c\<^sub>B \<in> \<rho>\<^sub>M p\<^sub>B - \<rho>\<^sub>N p\<^sub>B" "s p\<^sub>B < s p"
      by auto
    then have "False"
      using \<open>least_rank_p_st (\<lambda>p. \<rho>\<^sub>N p \<noteq> \<rho>\<^sub>M p) p s\<close> below_least_rank_p_st by fastforce
    then show ?thesis
      by auto
  qed
qed

lemma lt_prz_if_lt_if:
  assumes "\<rho>\<^sub>M \<sqsubset>s\<sqsubset> \<rho>\<^sub>N"
  shows "\<rho>\<^sub>N \<sqsubset>s\<sqsubset>\<^sub>p\<^sub>r\<^sub>z \<rho>\<^sub>M"
proof -
  have "\<rho>\<^sub>M \<noteq> \<rho>\<^sub>N"
    using assms lt_def by fastforce
  moreover
  have "(\<forall>p\<^sub>A c\<^sub>A. c\<^sub>A \<in> \<rho>\<^sub>M p\<^sub>A - \<rho>\<^sub>N p\<^sub>A \<longrightarrow> (\<exists>p\<^sub>B c\<^sub>B. c\<^sub>B \<in> \<rho>\<^sub>N p\<^sub>B - \<rho>\<^sub>M p\<^sub>B \<and> s p\<^sub>B < s p\<^sub>A))"
  proof (rule, rule, rule)
    fix p\<^sub>A c\<^sub>A
    assume "c\<^sub>A \<in> \<rho>\<^sub>M p\<^sub>A - \<rho>\<^sub>N p\<^sub>A"
    then show "\<exists>p\<^sub>B c\<^sub>B. c\<^sub>B \<in> \<rho>\<^sub>N p\<^sub>B - \<rho>\<^sub>M p\<^sub>B \<and> s p\<^sub>B < s p\<^sub>A"
      by (smt (verit) DiffD1 DiffD2 antisym_conv3 assms lt_def psubset_imp_ex_mem subsetD)
  qed
  ultimately
  show "\<rho>\<^sub>N \<sqsubset>s\<sqsubset>\<^sub>p\<^sub>r\<^sub>z \<rho>\<^sub>M"
    unfolding lt_prz_def by auto
qed

lemma lt_prz_iff_lt:
  "\<rho>\<^sub>M \<sqsubset>s\<sqsubset> \<rho>\<^sub>N \<longleftrightarrow> \<rho>\<^sub>N \<sqsubset>s\<sqsubset>\<^sub>p\<^sub>r\<^sub>z \<rho>\<^sub>M"
  using lt_if_lt_prz lt_prz_if_lt_if by blast

lemma solves_leq:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)"
  assumes "n \<le> m"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
  using assms unfolding solves_program_def by auto

lemma solves_Suc:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> Suc n)"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
  by (meson assms lessI less_imp_le_nat solves_leq)

lemma solve_pg_0_subset:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0)"
  shows "(solve_pg s dl 0) p \<subseteq> \<rho> p"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_Suc_subset:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
  assumes "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n"
  shows "(solve_pg s dl (Suc n)) p \<subseteq> \<rho> p"
  using assms by (force simp add: Inter'_def2)

lemma solve_pg_0_empty:
  assumes "s p > 0"
  shows "(solve_pg s dl 0) p = {}"
proof -
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = (solve_pg s dl 0)"
  define \<rho>' :: "'a \<Rightarrow> 'b list set" where "\<rho>' = (\<lambda>p. if s p = 0 then UNIV else {})"
  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)"
    unfolding solves_program_def solves_cls_def 
  proof (rule, rule)
    fix c \<sigma>
    assume c_dl0: "c \<in> (dl ==s== 0)"
    obtain p' ids rhs where c_split: "c = Cls p' ids rhs"
      by (cases c) auto
    then have sp'0: "s p' = 0" 
      using c_dl0 by auto
    have "\<lbrakk>Cls p' ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding meaning_cls.simps
    proof (rule) 
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      show "\<lbrakk>(p', ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using \<rho>'_def sp'0 by force
    qed
    then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding c_split by auto
  qed
  have "\<rho>'' p \<subseteq> \<rho>' p"
    using \<open>\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== 0)\<close> \<rho>''_def solve_pg_0_subset by fastforce
  then have "\<rho>'' p = {}"
    unfolding \<rho>'_def using assms(1) by simp
  then show ?thesis 
    unfolding \<rho>''_def by auto
qed

lemma solve_pg_above_empty:
  assumes "s p > n"
  shows "(solve_pg s dl n) p = {}"
  using assms proof (induction n arbitrary: p)
  case 0
  then show ?case
    using solve_pg_0_empty by metis
next
  case (Suc n)
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where 
    "\<rho>'' = (solve_pg s dl (Suc n))"
  define \<rho>' :: "'a \<Rightarrow> 'b list set" where 
    "\<rho>' = (\<lambda>p. if s p < Suc n then (solve_pg s dl n) p else if s p = Suc n then UNIV else {})"

  have \<rho>'_solves: "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
    unfolding solves_program_def solves_cls_def 
  proof (rule, rule)
    fix c \<sigma>
    assume c_dlSucn: "c \<in> (dl ==s== Suc n)"
    obtain p' ids rhs where c_split: "c = Cls p' ids rhs"
      by (cases c) auto
    then have sp'Sucn: "s p' = Suc n" 
      using c_dlSucn by auto
    have "\<lbrakk>Cls p' ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding meaning_cls.simps
    proof (rule)
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      show "\<lbrakk>(p', ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using \<rho>'_def sp'Sucn by auto[]
    qed
    then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
      unfolding c_split by auto
  qed
  have "\<forall>p. (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) p = (solve_pg s dl n) p"
    using Suc by (auto simp add: \<rho>'_def)
  then have "\<rho>'' p \<subseteq> \<rho>' p"
    using solve_pg_Suc_subset[of \<rho>' dl s n  p] \<rho>'_solves \<rho>''_def by force
  then have "\<rho>'' p = {}"
    unfolding \<rho>'_def using assms(1) Suc by simp
  then show ?case
    unfolding \<rho>''_def by auto
qed

lemma exi_sol_n: 
  "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) = solve_pg s dl m"
proof -
  define \<rho>' where 
    "\<rho>' = (\<lambda>p. (if s p < Suc m then (solve_pg s dl m) p else if s p = Suc m then UNIV else {}))"

  have "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m)"
    unfolding \<rho>'_def solves_cls_def solves_program_def by fastforce
  moreover
  have "\<forall>p. (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) p = solve_pg s dl m p"
    unfolding \<rho>'_def using solve_pg_above_empty[of m s _ dl] by auto
  ultimately
  show ?thesis 
    by force
qed

lemma solve_pg_agree_above:
  assumes "s p \<le> m"
  shows "(solve_pg s dl m) p = (solve_pg s dl (s p)) p"
  using assms 
proof (induction m)
  case 0
  then show ?case
    by force
next
  case (Suc m)
  show ?case
  proof (cases "s p = Suc m")
    case True
    then show ?thesis by auto
  next
    case False
    then have s_p: "s p \<le> m"
      using Suc by auto
    then have solve_pg_sp_m: "(solve_pg s dl (s p)) p = (solve_pg s dl m) p"
      using Suc by auto
    have \<rho>'_solve_pg: "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<longrightarrow>
                           (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) = solve_pg s dl m \<longrightarrow>
                           \<rho>' p = solve_pg s dl m p"
      by (metis pred_val_lte_stratum.simps s_p)
    have "\<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) = solve_pg s dl m} p =
          solve_pg s dl (s p) p"
    proof (rule; rule)
      fix x 
      assume "x \<in> \<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) = solve_pg s dl m} p"
      then show "x \<in> solve_pg s dl (s p) p"
        by (metis (mono_tags) CollectI \<rho>'_solve_pg exi_sol_n member_if_member_Inter' solve_pg_sp_m)
    next
      fix x
      assume "x \<in> solve_pg s dl (s p) p"
      then show "x \<in> \<^bold>\<Inter> {\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc m) \<and> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> m) = solve_pg s dl m} p"
        by (simp add: \<rho>'_solve_pg member_Inter' solve_pg_sp_m)
    qed
    then show ?thesis
      by simp
  qed
qed

lemma solve_pg_two_agree_above:
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "(solve_pg s dl m) p = (solve_pg s dl n) p"
  using assms solve_pg_agree_above by metis

lemma pos_rhs_stratum_leq_clause_stratum:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "\<^bold>+ p' ids' \<in> set rhs"
  shows "s p' \<le> s p"
  using assms unfolding strat_wf_def by fastforce

lemma neg_rhs_stratum_less_clause_stratum:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' < s p"
  using assms unfolding strat_wf_def by fastforce

lemma solve_pg_two_agree_above_on_rh:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  assumes "rh \<in> set rhs"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl m) \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>"
proof (cases rh)
  case (Eql a a')
  then show ?thesis
    using assms by auto
next
  case (Neql a a')
  then show ?thesis 
    using assms by auto
next
  case (PosLit p' ids')
  then have "s p' \<le> m"
    using assms pos_rhs_stratum_leq_clause_stratum by fastforce
  moreover
  from PosLit have "s p' \<le> n"
    using assms pos_rhs_stratum_leq_clause_stratum by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: PosLit)
next
  case (NegLit p' ids)
  then have "s p' < m"
    using assms neg_rhs_stratum_less_clause_stratum by fastforce
  moreover
  from NegLit have "s p' < n"
    using assms neg_rhs_stratum_less_clause_stratum by fastforce
  ultimately
  have "solve_pg s dl m p' = solve_pg s dl n p'"
    using solve_pg_two_agree_above[of s p' n m dl] by force
  then show ?thesis
    by (simp add: NegLit)
qed

lemma solve_pg_two_agree_above_on_lh:
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl m) \<sigma> \<longleftrightarrow> \<lbrakk>(p,ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
  by (metis assms meaning_lh.simps solve_pg_two_agree_above)

lemma solve_pg_two_agree_above_on_cls:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  assumes "s p \<le> m"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl m) \<sigma>"
  using assms solve_pg_two_agree_above_on_rh solve_pg_two_agree_above_on_lh
  by (meson meaning_rhs.simps meaning_cls.simps)

lemma solve_pg_two_agree_above_on_cls_Suc:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p \<le> n"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl (Suc n)) \<sigma> \<longleftrightarrow> \<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  using solve_pg_two_agree_above_on_cls[OF assms(1,2,3), of "Suc n" \<sigma>] assms(3) by auto

lemma stratum0_no_neg':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p = 0"
  assumes "rh \<in> set rhs"
  shows "\<nexists>p' ids. rh = \<^bold>\<not> p' ids"
  by (metis One_nat_def add_eq_0_iff_both_eq_0 assms bot_nat_0.extremum_uniqueI 
      bot_nat_0.not_eq_extremum rnk.simps(4) strat_wf_cls.simps strat_wf_def zero_less_Suc)

lemma stratumSuc_less_neg':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> dl"
  assumes "s p = Suc n"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' \<le> n"
  using assms unfolding strat_wf_def by force

lemma stratum0_no_neg:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> 0)"
  assumes "rh \<in> set rhs"
  shows "\<nexists>p' ids. rh = \<^bold>\<not> p ids"
  using assms stratum0_no_neg' by fastforce 

lemma stratumSuc_less_neg:
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> Suc n)"
  assumes "\<^bold>\<not> p' ids' \<in> set rhs"
  shows "s p' \<le> n"
  using assms neg_rhs_stratum_less_clause_stratum by fastforce

lemma all_meaning_rh_if_solve_pg_0:
  assumes "strat_wf s dl"
  assumes "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl 0) \<sigma>"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0)"
  assumes "rh \<in> set rhs"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> 0)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (cases rh)
  case (Eql a1 a2)
  then show ?thesis
    using assms by auto
next
  case (Neql a1 a2)
  then show ?thesis
    using assms by auto
next
  case (PosLit p ids)
  then show ?thesis
    using assms meaning_rh.simps(3) solve_pg_0_subset by fastforce
next
  case (NegLit p ids)
  then show ?thesis
    using assms stratum0_no_neg' by fastforce
qed

lemma all_meaning_rh_if_solve_pg_Suc:
  assumes "strat_wf s dl"
  assumes "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n)"
  assumes "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n"
  assumes "rh \<in> set rhs"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> Suc n)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
proof (cases rh)
  case (Eql a a')
  then show ?thesis
    using assms(2) by auto
next
  case (Neql a a')
  then show ?thesis
    using assms(2) by force
next
  case (PosLit p' ids')
  then show ?thesis
    using assms solve_pg_Suc_subset by fastforce
next
  case (NegLit p' ids')
  then have "s p' \<le> n"
    using stratumSuc_less_neg[OF assms(1) assms(6), of p'] assms(5) by auto
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>"
    by (metis NegLit assms(2) le_imp_less_Suc less_imp_le_nat meaning_rh.simps(4) 
        solve_pg_two_agree_above)
  then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) \<sigma>"
    using assms(4) by presburger
  then show ?thesis
    by (simp add: NegLit \<open>s p' \<le> n\<close>)
qed

lemma solve_pg_0_if_all_meaning_lh:
  assumes "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma all_meaning_lh_if_solve_pg_0:
  assumes "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
  shows "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_0_iff_all_meaning_lh:
  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma> \<longleftrightarrow> (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>)"
  using solve_pg_0_if_all_meaning_lh all_meaning_lh_if_solve_pg_0 by metis

lemma solve_pg_Suc_if_all_meaning_lh:
  assumes "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma all_meaning_if_solve_pg_Suc_lh:
  assumes "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
  shows "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
  using assms by (auto simp add: Inter'_def)

lemma solve_pg_Suc_iff_all_meaning_lh:
  "(\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>) \<longleftrightarrow>
   (\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>)"
  by (auto simp add: Inter'_def)

lemma solve_pg_0_meaning_cls':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> 0)"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl 0) \<sigma>"
  unfolding meaning_cls.simps
proof
  define \<rho>'' :: "'a \<Rightarrow> 'c list set" where "\<rho>'' = (solve_pg s dl 0)"
  assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (solve_pg s dl 0) \<sigma>"
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0) \<longrightarrow> (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
    using all_meaning_rh_if_solve_pg_0[OF assms(1), of _ \<sigma> _ rhs p ids, OF _ _ _ assms(2)] 
    by auto
  then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h  \<rho>' \<sigma>"
    by (metis assms(2) meaning_cls.simps solves_cls_def solves_program_def meaning_rhs.simps)
  then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl 0) \<sigma>"
    using solve_pg_0_if_all_meaning_lh by auto
qed

lemma solve_pg_meaning_cls':
  assumes "strat_wf s dl"
  assumes "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> n)"
  shows "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  unfolding meaning_cls.simps
  using assms
proof (induction n)
  case 0
  then show ?case
    using solve_pg_0_meaning_cls' unfolding meaning_cls.simps by metis 
next
  case (Suc n)
  have leq_n: "s p \<le> Suc n"
    using Suc.prems(2) by auto

  have cls_in: "Cls p ids rhs \<in> dl"
    using assms(2) by force

  show ?case
  proof (cases "s p = Suc n")
    case True
    have cls_in_Suc: "Cls p ids rhs \<in> (dl ==s== Suc n)"
      by (simp add: True cls_in)
    show ?thesis
    proof
      define \<rho>'' :: "'a \<Rightarrow> 'c list set" where "\<rho>'' = (solve_pg s dl (Suc n))"
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (solve_pg s dl (Suc n)) \<sigma>"
      then have 
        "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow> 
              (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n \<longrightarrow> 
              (\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>)"
        using all_meaning_rh_if_solve_pg_Suc[OF assms(1) _ _ _ _ Suc(3), of _ \<sigma>] 
        by auto
      then have "\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl ==s== Suc n) \<longrightarrow>
                 (\<rho>' \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n \<longrightarrow> 
                 \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using meaning_cls.simps solves_cls_def solves_program_def cls_in_Suc meaning_rhs.simps by metis
      then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl (Suc n)) \<sigma>"
        using solve_pg_Suc_if_all_meaning_lh[of dl s n p ids \<sigma>] by auto
    qed
  next
    case False
    then have False': "s p < Suc n"
      using leq_n by auto
    then have s_p_n: "s p \<le> n"
      by auto
    then have "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> n)"
      by (simp add: cls_in)
    then have "(\<forall>rh\<in>set rhs. \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (solve_pg s dl n) \<sigma>) \<longrightarrow> \<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h (solve_pg s dl n) \<sigma>"
      using Suc by auto
    then show ?thesis
      using False' meaning_cls.simps solve_pg_two_agree_above_on_cls_Suc assms cls_in s_p_n 
        meaning_rhs.simps by metis
  qed
qed

lemma solve_pg_meaning_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl \<le>\<le>s\<le>\<le> n)"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s (solve_pg s dl n) \<sigma>"
  using assms solve_pg_meaning_cls'[of s dl] by (cases c) metis

lemma solve_pg_solves_cls:
  assumes "strat_wf s dl"
  assumes "c \<in> (dl \<le>\<le>s\<le>\<le> n)"
  shows "solve_pg s dl n \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
  unfolding solves_cls_def using solve_pg_meaning_cls assms by blast

lemma solve_pg_solves_dl:
  assumes "strat_wf s dl"
  shows "solve_pg s dl n \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
proof -
  have "\<forall>c \<in> (dl \<le>\<le>s\<le>\<le> n). (solve_pg s dl n) \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
    using assms solve_pg_solves_cls[of s dl] by auto
  then show "solve_pg s dl n \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
    using solves_program_def by blast
qed

lemma disjE3:
  assumes major: "P \<or> Q \<or> Z"
    and minorP: "P \<Longrightarrow> R"
    and minorQ: "Q \<Longrightarrow> R"
    and minorZ: "Z \<Longrightarrow> R"
  shows R
  using assms by auto

lemma solve_pg_0_below_solution:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> 0)"
  shows "(solve_pg s dl 0) \<sqsubseteq>s\<sqsubseteq> \<rho>"
proof -
  define \<rho>'' :: "'a \<Rightarrow> 'b list set" where "\<rho>'' = solve_pg s dl 0"

  have "\<rho>'' \<noteq> \<rho> \<longrightarrow> \<rho>'' \<sqsubset>s\<sqsubset> \<rho>"
  proof 
    assume "\<rho>'' \<noteq> \<rho>"
    have \<rho>''_subs_\<rho>: "\<forall>p. \<rho>'' p \<subseteq> \<rho> p"
      using solve_pg_0_subset unfolding \<rho>''_def using assms(1) by force
    have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by (meson \<open>\<rho>'' \<noteq> \<rho>\<close> ext least_rank_p_st_exists)
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>'' p \<noteq> \<rho> p) p s"
      by auto
    then have "\<rho>'' p \<subset> \<rho> p"
      by (metis (mono_tags, lifting) \<rho>''_subs_\<rho> least_rank_p_st_def psubsetI)
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p'"
      using \<rho>''_subs_\<rho> by auto
    moreover
    have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p'"
      using below_least_rank_p_st[OF p_p] by auto
    ultimately
    show "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>"
      unfolding lt_def by auto
  qed
  then show ?thesis
    using \<rho>''_def lte_def by auto
qed

lemma least_disagreement_proper_subset:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  shows "\<rho>''n p \<subset> \<rho> p"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    by (metis (mono_tags, lifting) assms(2) least_rank_p_st_def psubsetI)
qed

lemma subset_on_least_disagreement:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  assumes "s p' = s p"
  shows "\<rho>''n p' \<subseteq> \<rho> p'"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    using assms by metis
qed

lemma equal_below_least_disagreement:
  assumes "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
  assumes "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
  assumes "s p' < s p"
  shows "\<rho>''n p' = \<rho> p'"
proof -
  from assms obtain p'' where p''_p:
    "\<rho>''n p'' \<subset> \<rho> p''"
    "(\<forall>p'. s p' = s p'' \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p')"
    "(\<forall>p'. s p' < s p'' \<longrightarrow> \<rho>''n p' = \<rho> p')"
    unfolding lt_def by auto
  moreover
  from p''_p have "s p'' = s p"
    by (metis (mono_tags, lifting) antisym_conv2 assms(2) least_rank_p_st_def)
  ultimately
  show ?thesis
    using assms by metis
qed

lemma solution_on_subset_solution_below:
  "(dl ==s== n) \<subseteq> (dl \<le>\<le>s\<le>\<le> n)"
  by fastforce

lemma solves_program_mono:
  assumes "dl \<subseteq> dl'"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl'"
  shows "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  by (meson assms in_mono solves_program_def)

lemma solution_on_if_solution_below:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
  shows  "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl ==s== n)"
  by (meson assms solves_program_mono solution_on_subset_solution_below)

lemma solve_pg_Suc_subset_solution:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> Suc n)"
  assumes "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n"
  shows "solve_pg s dl (Suc n) p \<subseteq> \<rho> p"
  by (meson assms solution_on_if_solution_below solve_pg_Suc_subset)

lemma solve_pg_subset_solution:
  assumes "m > n"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)"
  assumes "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n"
  shows "solve_pg s dl (Suc n) p \<subseteq> \<rho> p"
  by (meson Suc_leI assms solve_pg_Suc_subset_solution solves_leq)

lemma below_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  assumes "s p' < s p"
  shows "\<rho>' p' = \<rho> p'"
  using assms below_least_rank_p_st by fastforce

definition agree_below_eq :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below_eq \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p \<le> n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_below :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_below \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p < n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool"  where
  "agree_above \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p > n \<longrightarrow> \<rho> p = \<rho>' p)"

definition agree_above_eq :: "('p,'c) pred_val \<Rightarrow> ('p,'c) pred_val \<Rightarrow> nat \<Rightarrow> 'p strat \<Rightarrow> bool" where
  "agree_above_eq \<rho> \<rho>' n s \<longleftrightarrow> (\<forall>p. s p \<ge> n \<longrightarrow> \<rho> p = \<rho>' p)"

lemma agree_below_trans:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_below_eq \<rho>' \<rho>'' n s"
  shows "agree_below_eq \<rho> \<rho>'' n s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_eq_less_eq:
  assumes "l \<le> n"
  assumes "agree_below_eq \<rho> \<rho>' n s"
  shows "agree_below_eq \<rho> \<rho>' l s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_trans':
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_below_eq \<rho>' \<rho>'' m s"
  assumes "l \<le> n"
  assumes "l \<le> m"
  shows "agree_below_eq \<rho> \<rho>'' l s"
  using assms unfolding agree_below_eq_def by auto

lemma agree_below_eq_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  assumes "n < s p"
  shows "agree_below_eq \<rho>' \<rho> n s"
  using agree_below_eq_def assms(1) assms(2) below_least_rank_p_st by fastforce

lemma agree_below_least_disagreement:
  assumes "least_rank_p_st (\<lambda>p. \<rho>' p \<noteq> \<rho> p) p s"
  shows "agree_below \<rho>' \<rho> (s p) s"
  using agree_below_def assms below_least_rank_p_st by fastforce

lemma eq_if_agree_below_eq_agree_above:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_above \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (metis agree_above_def agree_below_eq_def assms ext le_eq_less_or_eq nat_le_linear)

lemma eq_if_agree_below_agree_above_eq:
  assumes "agree_below \<rho> \<rho>' n s"
  assumes "agree_above_eq \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (metis agree_above_eq_def agree_below_def assms ext le_eq_less_or_eq nat_le_linear)
  

lemma eq_if_agree_below_eq_agree_above_eq:
  assumes "agree_below_eq \<rho> \<rho>' n s"
  assumes "agree_above_eq \<rho> \<rho>' n s"
  shows "\<rho> = \<rho>'"
  by (meson agree_above_def agree_above_eq_def eq_if_agree_below_eq_agree_above assms 
      less_imp_le_nat)

lemma agree_below_eq_pred_val_lte_stratum:
  "agree_below_eq \<rho> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) n s"
  by (simp add: agree_below_eq_def)

lemma agree_below_eq_pred_val_lte_stratum_less_eq:
  assumes "m \<le> n"
  shows "agree_below_eq \<rho> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) m s"
  using agree_below_eq_less_eq agree_below_eq_pred_val_lte_stratum assms by blast

lemma agree_below_eq_solve_pg:
  assumes "l \<le> m"
  assumes "l \<le> n"
  shows "agree_below_eq (solve_pg s dl n) (solve_pg s dl m) l s"
  unfolding agree_below_eq_def by (meson assms dual_order.trans solve_pg_two_agree_above)    

lemma solve_pg_below_solution:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
  shows "solve_pg s dl n \<sqsubseteq>s\<sqsubseteq> \<rho>"
  using assms
proof (induction n arbitrary: \<rho>)
  case 0
  then show ?case
    using solve_pg_0_below_solution by blast
next
  case (Suc n)
  define \<rho>''n :: "'a \<Rightarrow> 'b list set" where "\<rho>''n = solve_pg s dl n"
  define \<rho>''n1 :: "'a \<Rightarrow> 'b list set" where "\<rho>''n1 = solve_pg s dl (Suc n)"

  have \<rho>''n_below_\<rho>: "\<rho>''n \<sqsubseteq>s\<sqsubseteq> \<rho>"
    using Suc.IH Suc.prems \<rho>''n_def solves_Suc by blast

  have agree_\<rho>''n1_\<rho>''n: "agree_below_eq \<rho>''n1 \<rho>''n n s"
    unfolding \<rho>''n_def \<rho>''n1_def using agree_below_eq_solve_pg using le_Suc_eq by blast

  have "\<rho>''n1 \<sqsubseteq>s\<sqsubseteq> \<rho>"
    unfolding lte_def2
  proof
    assume "\<rho>''n1 \<noteq> \<rho>"
    then have "\<exists>p. least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      using least_rank_p_st_exists[of "(\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p)"] by force
    then obtain p where p_p: "least_rank_p_st (\<lambda>p. \<rho>''n1 p \<noteq> \<rho> p) p s"
      by blast
    then have dis: "\<rho>''n1 p \<noteq> \<rho> p"
      unfolding least_rank_p_st_def by auto
    from p_p have agg: "agree_below \<rho>''n1 \<rho> (s p) s"
      by (simp add: agree_below_least_disagreement)

    define i where "i = s p"
    have "i < Suc n \<or> Suc n \<le> i"
      by auto
    then show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
    proof (rule disjE)
      assume "i < Suc n"
      then have "s p \<le> n"
        unfolding i_def by auto
      then have "\<rho>''n p \<noteq> \<rho> p"
        by (metis agree_\<rho>''n1_\<rho>''n agree_below_eq_def dis)

      have "\<rho>''n \<sqsubset>s\<sqsubset> \<rho>"
        by (metis \<rho>''n_below_\<rho> \<open>\<rho>''n p \<noteq> \<rho> p\<close> lte_def)
      moreover
      have "\<forall>p'. \<rho>''n p' \<noteq> \<rho> p' \<longrightarrow> s p \<le> s p'"
        by (metis agree_\<rho>''n1_\<rho>''n \<open>s p \<le> n\<close> agg agree_below_def agree_below_eq_def le_trans 
            linorder_le_cases linorder_le_less_linear)
      then have "least_rank_p_st (\<lambda>p. \<rho>''n p \<noteq> \<rho> p) p s"
          using \<open>\<rho>''n p \<noteq> \<rho> p\<close> unfolding least_rank_p_st_def by auto
      ultimately
      have "\<rho>''n p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n p' \<subseteq> \<rho> p') \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n p' = \<rho> p')"
        using least_disagreement_proper_subset[of \<rho>''n s \<rho> p]
          subset_on_least_disagreement[of \<rho>''n s \<rho> p] equal_below_least_disagreement[of \<rho>''n s \<rho> p] 
        by metis
      then have "\<rho>''n1 p \<subset> \<rho> p \<and>
           (\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p') \<and>
           (\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1 p' = \<rho> p')"
        using agree_\<rho>''n1_\<rho>''n \<open>s p \<le> n\<close> by (simp add: agree_below_eq_def)
      then show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
    next
      assume "Suc n \<le> i"
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> Suc n)"
        using Suc.prems by auto
      moreover
      have "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = (solve_pg s dl n)"
      proof -
        have "agree_below_eq \<rho>''n \<rho>''n1 n s"
          by (metis agree_\<rho>''n1_\<rho>''n agree_below_eq_def)
        moreover
        have "agree_below_eq \<rho>''n1 \<rho> n s"
          using \<open>Suc n \<le> i\<close> agree_below_eq_least_disagreement i_def p_p by fastforce
        moreover
        have "agree_below_eq \<rho> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) n s"
          by (simp add: agree_below_eq_pred_val_lte_stratum)
        ultimately
        have "agree_below_eq \<rho>''n (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) n s"
          using agree_below_trans by metis
        moreover
        have "agree_above \<rho>''n (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) n s"
          using \<rho>''n_def by (simp add: agree_above_def solve_pg_above_empty)
        ultimately
        have "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = \<rho>''n"
           using eq_if_agree_below_eq_agree_above by blast
        then show "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = (solve_pg s dl n)"
          using \<rho>''n_def by metis
      qed
      ultimately
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> Suc n) \<and> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n"
        by auto
      then have "\<rho>''n1 p \<subseteq> \<rho> p"
        using solve_pg_subset_solution[of n "Suc n" \<rho> dl s p]
        using \<rho>''n1_def by fastforce 
      then have "\<rho>''n1 p \<subset> \<rho> p"
        using dis by auto
      moreover
      have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>''n1 p' \<subseteq> \<rho> p'"
        using \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> Suc n) \<and> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> n) = solve_pg s dl n\<close> \<rho>''n1_def 
          solve_pg_subset_solution by fastforce
      moreover
      have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>''n1 p' = \<rho> p'"
        using below_least_rank_p_st p_p by fastforce
      ultimately
      show "\<rho>''n1 \<sqsubset>s\<sqsubset> \<rho>"
        unfolding lt_def by auto
    qed
  qed
  then show ?case
    unfolding \<rho>''n1_def by auto
qed

lemma solve_pg_least_solution':
  assumes "strat_wf s dl"
  shows "solve_pg s dl n \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> n) s"
  using assms least_solution_def solve_pg_below_solution solve_pg_solves_dl by blast 

lemma stratum_less_eq_max_stratum:
  assumes "finite dl"
  assumes "Cls p ids rhs \<in> dl"
  shows "s p \<le> max_stratum s dl"
proof -
  have "s p \<in> {s p | p ids rhs. Cls p ids rhs \<in> dl}"
    using assms(2) by auto
  moreover
  have "{s p | p ids rhs. Cls p ids rhs \<in> dl} = (\<lambda>c. (case c of Cls p ids rhs \<Rightarrow> s p)) ` dl"
    unfolding image_def by (metis (mono_tags, lifting) clause.case the_lh.cases)
  then have "finite {s p | p ids rhs. Cls p ids rhs \<in> dl}"
    by (simp add: assms(1))
  ultimately
  show ?thesis
    unfolding max_stratum_def using Max.coboundedI by auto
qed

lemma finite_above_max_stratum:
  assumes "finite dl"
  assumes "max_stratum s dl \<le> n"
  shows "(dl \<le>\<le>s\<le>\<le> n) = dl"
proof (rule; rule)
  fix c
  assume "c \<in> (dl \<le>\<le>s\<le>\<le> n)"
  then show "c \<in> dl"
    by auto
next
  fix c
  assume c_in_dl: "c \<in> dl"
  then obtain p ids rhs where c_split: "c = Cls p ids rhs"
    by (cases c) auto
  then have c_in_dl': "Cls p ids rhs \<in> dl"
    using c_in_dl by auto
  then have "s p \<le> max_stratum s dl"
    using stratum_less_eq_max_stratum assms by metis
  then have "Cls p ids rhs \<in> (dl \<le>\<le>s\<le>\<le> n)"
    using c_in_dl' assms(2) by auto 
  then show "c \<in> (dl \<le>\<le>s\<le>\<le> n)"
    unfolding c_split by auto
qed 

lemma finite_max_stratum:
  assumes "finite dl"
  shows "(dl \<le>\<le>s\<le>\<le> max_stratum s dl) = dl"
  using assms finite_above_max_stratum[of dl s "max_stratum s dl"] by auto 

lemma solve_pg_least_solution:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "solve_pg s dl (max_stratum s dl) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
proof -
  have "solve_pg s dl (max_stratum s dl) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> (max_stratum s dl)) s"
    using solve_pg_least_solution' assms by auto
  then show ?thesis
    using finite_max_stratum assms by metis
qed

lemma exi_least_solution:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "\<exists>\<rho>. \<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  using assms solve_pg_least_solution by metis


subsubsection \<open>Equality of least and minimal solution\<close>

lemma least_iff_minimal:
  assumes "finite dl"
  assumes "strat_wf s dl"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
proof
  assume "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  then have \<rho>_least: "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl" "(\<forall>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<sigma>')"
    unfolding least_solution_def by auto
  then have "(\<nexists>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<and> \<rho>' \<sqsubset>s\<sqsubset> \<rho>)"
    by (metis (full_types) \<open>\<forall>\<rho>'. \<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longrightarrow> \<rho> \<sqsubseteq>s\<sqsubseteq> \<rho>'\<close> lt_def lte_def nat_neq_iff psubsetE)
  then show "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
    unfolding minimal_solution_def using \<rho>_least by metis
next
  assume min: "\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n dl s"
  have "\<exists>\<rho>'. \<rho>' \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
    using solve_pg_least_solution assms by metis
  then show "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
    by (metis min least_solution_def lte_def minimal_solution_def)
qed


subsubsection \<open>Least solution on lower strata\<close>

lemma below_subset:
  "(dl \<le>\<le>s\<le>\<le> n) \<subseteq> dl"
  by auto

lemma finite_below_finite:
  assumes "finite dl"
  shows "finite (dl \<le>\<le>s\<le>\<le> n)"
  using assms finite_subset below_subset by metis

lemma downward_least_solution:
  assumes "finite dl"
  assumes "n > m"
  assumes "strat_wf s dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> n) s"
  shows "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> m) s"
proof (rule ccontr)
  assume a: "\<not> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> m) s"
  have s_dl_m: "strat_wf s (dl \<le>\<le>s\<le>\<le> m)"
    using assms strat_wf_lte_if_strat_wf by auto
  have strat_wf_n: "strat_wf s (dl \<le>\<le>s\<le>\<le> n)"
    using assms strat_wf_lte_if_strat_wf by auto
  from a have "\<not> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl \<le>\<le>s\<le>\<le> m) s"
    using least_iff_minimal s_dl_m assms(1) finite_below_finite by metis
  moreover 
  have "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)"
    using assms downward_lte_solves least_solution_def by blast
  ultimately
  have "(\<exists>\<sigma>'. \<sigma>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m) \<and> (\<sigma>' \<sqsubset>s\<sqsubset> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m)))"
    unfolding minimal_solution_def by auto
  then obtain \<rho>' where \<rho>'_p1: "\<rho>' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> m)" and \<rho>'_p2: "(\<rho>' \<sqsubset>s\<sqsubset> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m))"
    by auto
  then have "\<exists>p. \<rho>' p \<subset> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p \<and>
                    (\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p') \<and>
                    (\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p')"
    unfolding lt_def by auto
  then obtain p where p_p1: "\<rho>' p \<subset> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p" and
    p_p2: "\<forall>p'. s p' = s p \<longrightarrow> \<rho>' p' \<subseteq> (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p'" and
    p_p3: "\<forall>p'. s p' < s p \<longrightarrow> \<rho>' p' = (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) p'"
    by auto
  define \<rho>'' where "\<rho>'' == \<lambda>p. if s p \<le> m then \<rho>' p else UNIV"

  have "s p \<le> m"
    using p_p1 by auto
  then have "\<rho>'' p \<subset> \<rho> p"
    unfolding \<rho>''_def using p_p1 by auto
  moreover
  have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho> p'"
    using p_p2
    by (metis \<rho>''_def calculation pred_val_lte_stratum.simps top.extremum_strict)
  moreover
  have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho> p'"
    using \<rho>''_def p_p3 calculation(1) by force
  ultimately
  have "(\<rho>'' \<sqsubset>s\<sqsubset> \<rho>)"
    by (metis lt_def)
  moreover
  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l (dl \<le>\<le>s\<le>\<le> n)"
    unfolding solves_program_def
  proof
    fix c
    assume c_in_dl_n: "c \<in> (dl \<le>\<le>s\<le>\<le> n)"
    then obtain p ids rhs where c_def: "c = Cls p ids rhs"
      by (cases c) auto

    have "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p ids rhs"
      unfolding solves_cls_def
    proof
      fix \<sigma>
      show "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>"
      proof (cases "s p \<le> m")
        case True
        then have "c \<in> (dl \<le>\<le>s\<le>\<le> m)"
          using c_in_dl_n c_def by auto
        then have "\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
          using \<rho>'_p1 c_def solves_cls_def solves_program_def by blast
        
        show ?thesis
          unfolding meaning_cls.simps
        proof
          assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>"
          have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
            unfolding meaning_rhs.simps
          proof
            fix rh
            assume "rh \<in> set rhs"
            then have "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>"
              using \<open>\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>\<close> by force
            then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>"
            proof (cases rh)
              case (Eql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (Neql a a')
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> by auto
            next
              case (PosLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl \<le>\<le>s\<le>\<le> m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def assms(3) c_def 
                  pos_rhs_stratum_leq_clause_stratum by fastforce
            next
              case (NegLit p ids)
              then show ?thesis
                using \<open>\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>'' \<sigma>\<close> \<open>c \<in> (dl \<le>\<le>s\<le>\<le> m)\<close> \<open>rh \<in> set rhs\<close> \<rho>''_def c_def 
                  neg_rhs_stratum_less_clause_stratum s_dl_m by fastforce
            qed
          qed
          then have "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
            using \<open>\<lbrakk>Cls p ids rhs\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>\<close> by force
          then show  "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>"
            using \<rho>''_def by force
        qed
      next
        case False
        then show ?thesis
          by (simp add: \<rho>''_def)
      qed
    qed
    then show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using c_def by blast
  qed
  ultimately
  have "\<not>\<rho> \<Turnstile>\<^sub>m\<^sub>i\<^sub>n (dl \<le>\<le>s\<le>\<le> n) s"
    unfolding minimal_solution_def by auto
  then have "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> n) s" 
    using least_iff_minimal strat_wf_n finite_below_finite assms by metis
  then show "False"
    using assms by auto
qed

lemma downward_least_solution_same_stratum:
  assumes "finite dl"
  assumes "strat_wf s dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  shows "(\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> m) \<Turnstile>\<^sub>l\<^sub>s\<^sub>t (dl \<le>\<le>s\<le>\<le> m) s"
proof (cases "m < max_stratum s dl")
  case True
  have "(dl \<le>\<le>s\<le>\<le> max_stratum s dl) = dl"
    using assms(1) finite_max_stratum by blast
  with True show ?thesis
    using downward_least_solution[of dl m "max_stratum s dl" s \<rho>]
      assms by auto
next
  case False
  then have "max_stratum s dl \<le> m"
    by auto
  moreover
  have "(dl \<le>\<le>s\<le>\<le> m) = dl"
    using assms(1) calculation finite_above_max_stratum by blast
  then
  show ?thesis
    using assms below_subset downward_least_solution least_solution_def lessI less_imp_le_nat 
      solves_leq[of _ dl s _ m] solves_program_mono[of _ dl \<rho> ] by metis
qed


subsection \<open>Negation\<close>

definition agree_var_val :: "'x set \<Rightarrow> ('x, 'c) var_val \<Rightarrow> ('x, 'c) var_val \<Rightarrow> bool " where
  "agree_var_val xs \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x \<in> xs. \<sigma> x = \<sigma>' x)"

fun vars_ids :: "('a, 'b) id list \<Rightarrow> 'a set" where
  "vars_ids ids = \<Union>(vars_id ` set ids)"

fun vars_lh :: "('p,'x,'c) lh \<Rightarrow> 'x set" where
  "vars_lh (p,ids) = vars_ids ids"

definition lh_consequence :: "('p, 'c) pred_val \<Rightarrow> ('p, 'x, 'c) clause \<Rightarrow> ('p, 'x, 'c) lh \<Rightarrow> bool" 
  where
  "lh_consequence \<rho> c lh \<longleftrightarrow> (\<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = lh \<and> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"

lemma meaning_rh_iff_meaning_rh_pred_val_lte_stratum:
  assumes "c \<in> (dl \<le>\<le>s\<le>\<le> s p)"
  assumes "strat_wf s dl"
  assumes "rh \<in> set (the_rhs c)"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>' \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
proof (cases rh)
  case (Eql a a')
  then show ?thesis 
    by auto
next
  case (Neql a a')
  then show ?thesis 
    by auto
next
  case (PosLit p' ids)
  show ?thesis
  proof
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
      using PosLit assms pos_rhs_stratum_leq_clause_stratum by fastforce
  next
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
      by (metis PosLit equals0D meaning_rh.simps(3) pred_val_lte_stratum.simps)
  qed
next
  case (NegLit p' ids)
  show ?thesis
  proof
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
      using NegLit assms by fastforce
  next
    assume "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
    then show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>'"
      using NegLit assms(1) assms(2) assms(3) neg_rhs_stratum_less_clause_stratum by fastforce
  qed
qed

lemma meaning_rhs_iff_meaning_rhs_pred_val_lte_stratum:
  assumes "c \<in> (dl \<le>\<le>s\<le>\<le> s p)"
  assumes "strat_wf s dl"
  shows "\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>' \<longleftrightarrow> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p) \<sigma>'"
  by (meson assms(1) assms(2) meaning_rh_iff_meaning_rh_pred_val_lte_stratum meaning_rhs.simps)

lemma meaning_rhs_if_meaning_rhs_with_removed_top_strata:
  assumes "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s (\<rho>'(p := \<rho>' p - {\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>})) \<sigma>'"
  assumes "strat_wf s dl"
  assumes c_dl': "Cls p' ids' rhs \<in> (dl \<le>\<le>s\<le>\<le> s p)"
  shows "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'"
proof -
  have "\<forall>rh' \<in> set rhs. rnk s rh' \<le> s p'"
    using assms c_dl' in_mono strat_wf_cls.simps strat_wf_def by fastforce

  show ?thesis
    unfolding meaning_rhs.simps
  proof
    fix rh
    assume "rh \<in> set rhs"
    show "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma>'"
    proof (cases rh)
      case (Eql a a')
      then show ?thesis
        using \<open>rh \<in> set rhs\<close> assms by auto
    next
      case (Neql a a')
      then show ?thesis
        using \<open>rh \<in> set rhs\<close> assms by auto
    next
      case (PosLit p'' ids'')
      then show ?thesis
        by (metis Diff_empty Diff_insert0 \<open>rh \<in> set rhs\<close> assms fun_upd_other fun_upd_same insertCI 
            insert_Diff meaning_rh.simps(3) meaning_rhs.elims(2))
    next
      case (NegLit p'' ids'')
      have "p'' \<noteq> p"
        using NegLit One_nat_def \<open>\<forall>rh'\<in>set rhs. rnk s rh' \<le> s p'\<close> \<open>rh \<in> set rhs\<close> c_dl' by fastforce
      then show ?thesis
        using NegLit  \<open>rh \<in> set rhs\<close> assms by auto
    qed
  qed
qed

lemma meaning_PosLit_least':
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  shows "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
proof (rule ccontr)
  assume "\<not>(\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>))"
  then have "\<not>(\<exists>c \<in> dl. \<exists>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<and> (\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'))"
    unfolding lh_consequence_def by auto
  then have a: "\<forall>c \<in> dl. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>')"
    by metis

  define \<rho>' where "\<rho>' = (\<rho> \<le>\<le>\<le>s\<le>\<le>\<le> s p)"
  define dl' where "dl' = (dl \<le>\<le>s\<le>\<le> s p)"

  have \<rho>'_least: "\<rho>' \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl' s"
    using downward_solves[of \<rho> dl s] assms downward_least_solution_same_stratum 
    unfolding \<rho>'_def dl'_def by blast
  moreover
  have no_match: "\<forall>c \<in> dl'. \<forall>\<sigma>'. ((the_lh c) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) \<longrightarrow> \<not>(\<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>')"
    using a
    unfolding dl'_def \<rho>'_def
    by (meson assms(3) below_subset meaning_rhs_iff_meaning_rhs_pred_val_lte_stratum in_mono)

  define \<rho>'' where "\<rho>'' = \<rho>'(p := \<rho>' p - {\<lbrakk>ids\<rbrakk>\<^sub>i\<^sub>d\<^sub>s \<sigma>})"
    

  have "\<rho>'' \<Turnstile>\<^sub>d\<^sub>l dl'"
    unfolding solves_program_def
  proof
    fix c
    assume c_dl': "c \<in> dl'"
    obtain p' ids' rhs' where c_split: "c = Cls p' ids' rhs'"
      by (cases c)
    show "\<rho>'' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      unfolding solves_cls_def
    proof
      fix \<sigma>'
      have "\<lbrakk>Cls p' ids' rhs'\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding meaning_cls.simps
      proof
        assume "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>'' \<sigma>'"
        then have rhs'_true: "\<lbrakk>rhs'\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>'" 
          using meaning_rhs_if_meaning_rhs_with_removed_top_strata[of rhs' \<rho>' p ids \<sigma> \<sigma>']
            \<rho>''_def assms(3) c_dl' c_split dl'_def using \<rho>''_def by force 
        have "\<lbrakk>(p',ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>'"
          by (metis rhs'_true c_split c_dl' \<rho>'_least clause.inject least_solution_def 
              meaning_cls.elims(2) solves_cls_def solves_program_def)
        moreover
        have "((p', ids') \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') \<noteq> ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
          using no_match rhs'_true c_split c_dl' by fastforce
        ultimately
        show "\<lbrakk>(p', ids')\<rbrakk>\<^sub>l\<^sub>h \<rho>'' \<sigma>'"
          using  \<rho>''_def eval_ids_is_substv_ids by auto
      qed
      then show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>'' \<sigma>'"
        unfolding c_split by auto
    qed
  qed
  moreover
  have "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
  proof -
    have "\<rho>'' p \<subset> \<rho>' p"
      unfolding \<rho>'_def
      using DiffD2 \<open>\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>\<close> \<rho>''_def \<rho>'_def by auto
    moreover
    have "\<forall>p'. s p' = s p \<longrightarrow> \<rho>'' p' \<subseteq> \<rho>' p'"
      unfolding \<rho>'_def
      by (simp add: \<rho>''_def \<rho>'_def)
    moreover
    have "\<forall>p'. s p' < s p \<longrightarrow> \<rho>'' p' = \<rho>' p'"
      using \<rho>''_def by force
    ultimately
    show "\<rho>'' \<sqsubset>s\<sqsubset> \<rho>'"
      unfolding lt_def by auto
  qed
  ultimately
  show "False"
    by (metis assms(1,3) dl'_def finite_below_finite least_iff_minimal minimal_solution_def 
        strat_wf_lte_if_strat_wf)
qed

lemma meaning_lh_least':
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  shows "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
  using assms meaning_PosLit_least' by fastforce

lemma meaning_lh_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  shows "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma> \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>))"
proof
  assume "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
  then show "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
    by (meson assms meaning_lh_least')
next
  assume "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
  then show "\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
    unfolding lh_consequence_def
    using assms(2) eval_ids_is_substv_ids least_solution_def meaning_cls.simps meaning_lh.simps 
      solves_cls_def solves_program_def clause.exhaust clause.sel(3) prod.inject substv_lh.simps 
      the_lh.simps by metis
qed

lemma meaning_PosLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  shows "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>))"
proof
  assume "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  then show "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
    by (meson assms(1,2,3) meaning_PosLit_least')
next
  assume "\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)"
  then show "\<lbrakk>\<^bold>+ p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    unfolding lh_consequence_def
    using assms(2) eval_ids_is_substv_ids least_solution_def meaning_cls.simps meaning_lh.simps 
      solves_cls_def solves_program_def clause.exhaust clause.sel(3) meaning_rh.simps(3) prod.inject 
      substv_lh.simps the_lh.simps by metis
qed

lemma meaning_NegLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  shows "\<lbrakk>\<^bold>\<not> p ids\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma> \<longleftrightarrow> (\<not>(\<exists>c \<in> dl. lh_consequence \<rho> c ((p,ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>)))"
  by (metis assms(1,2,3) meaning_PosLit_least meaning_rh.simps(3) meaning_rh.simps(4))

lemma solves_PosLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>a \<in> set ids. is_Cst a"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>+ p ids) \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c (p,ids))"
proof -
  have "\<forall>\<sigma>. ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = (p, ids)"
    using assms(4) by (induction ids) (auto simp add: is_Cst_def)
  then show ?thesis
    by (metis assms(1,2,3) meaning_PosLit_least solves_rh.simps)
qed

lemma solves_lh_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>a \<in> set ids. is_Cst a"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h (p, ids) \<longleftrightarrow> (\<exists>c \<in> dl. lh_consequence \<rho> c (p,ids))"
proof -
  have "\<forall>\<sigma>. ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = (p, ids)"
    using assms(4) by (induction ids) (auto simp add: is_Cst_def)
  then show ?thesis
    by (metis assms(1,2,3) meaning_lh_least solves_lh.simps)
qed

lemma solves_NegLit_least:
  assumes "finite dl"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t dl s"
  assumes "strat_wf s dl"
  assumes "\<forall>a \<in> set ids. is_Cst a"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h (\<^bold>\<not> p ids) \<longleftrightarrow> \<not>(\<exists>c \<in> dl. lh_consequence \<rho> c (p,ids))"
proof -
  have "\<forall>\<sigma>. ((p, ids) \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = (p, ids)"
    using assms(4) by (induction ids) (auto simp add: is_Cst_def)
  then show ?thesis
    by (metis assms(1,2,3) meaning_NegLit_least solves_rh.simps)
qed

end
