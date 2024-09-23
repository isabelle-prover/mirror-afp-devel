section \<open>Linear Diophantine Equations and Inequalities\<close>

text \<open>We just represent equations and inequalities as polynomials, i.e., 
  \<open>p = 0\<close> or \<open>p \<le> 0\<close>. There is no need for strict inequalities \<open>p < 0\<close> 
  since for integers this is equivalent to \<open>p + 1 \<le> 0\<close>.\<close>

theory Diophantine_Eqs_and_Ineqs
  imports Linear_Polynomial
begin

type_synonym 'v dleq = "(int,'v) lpoly"
type_synonym 'v dlineq = "(int,'v) lpoly"

definition satisfies_dleq :: "(int,'v) assign \<Rightarrow> 'v dleq \<Rightarrow> bool" where
  "satisfies_dleq \<alpha> p = (eval_l \<alpha> p = 0)" 

definition satisfies_dlineq :: "(int,'v) assign \<Rightarrow> 'v dlineq \<Rightarrow> bool" where
  "satisfies_dlineq \<alpha> p = (eval_l \<alpha> p \<le> 0)" 

abbreviation satisfies_eq_ineqs :: "(int,'v) assign \<Rightarrow> 'v dleq set \<Rightarrow> 'v dlineq set \<Rightarrow> bool" (\<open>_ \<Turnstile>\<^sub>d\<^sub>i\<^sub>o '(_,_')\<close>) where
  "satisfies_eq_ineqs \<alpha> eqs ineqs \<equiv> Ball eqs (satisfies_dleq \<alpha>) \<and> Ball ineqs (satisfies_dlineq \<alpha>)" 
 
definition trivial_ineq :: "(int,'v :: linorder)lpoly \<Rightarrow> bool option" where
  "trivial_ineq c = (if vars_l_list c = [] then Some (constant_l c \<le> 0) else None)" 

lemma trivial_ineq_None: "trivial_ineq c = None \<Longrightarrow> vars_l c \<noteq> {}" 
  unfolding trivial_ineq_def unfolding vars_l_list[symmetric] by fastforce

lemma trivial_ineq_Some: assumes "trivial_ineq c = Some b"
  shows "b = satisfies_dlineq \<alpha> c" 
proof -
  from assms[unfolded trivial_ineq_def] have vars: "vars_l c = {}" and b: "b = (constant_l c \<le> 0)" 
    by (auto split: if_splits simp: vars_l_list_def)
  show ?thesis unfolding satisfies_dlineq_def eval_l_def vars using b by auto
qed

fun trivial_ineq_filter :: "'v :: linorder dlineq list \<Rightarrow> 'v dlineq list option" 
  where "trivial_ineq_filter [] = Some []" 
  | "trivial_ineq_filter (c # cs) = (case trivial_ineq c of Some True \<Rightarrow> trivial_ineq_filter cs
      | Some False \<Rightarrow> None
      | None \<Rightarrow> map_option ((#) c) (trivial_ineq_filter cs))" 

lemma trivial_ineq_filter: "trivial_ineq_filter cs = None \<Longrightarrow> (\<nexists> \<alpha>. \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set cs))" 
  "trivial_ineq_filter cs = Some ds \<Longrightarrow> 
     Ball (set ds) (\<lambda> c. vars_l c \<noteq> {}) \<and> 
     (\<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set cs) \<longleftrightarrow> \<alpha> \<Turnstile>\<^sub>d\<^sub>i\<^sub>o ({}, set ds)) \<and> 
     length ds \<le> length cs" 
proof (atomize(full), induct cs arbitrary: ds)
  case IH: (Cons c cs)
  let ?t = "trivial_ineq c" 
  consider (T) "?t = Some True" | (F) "?t = Some False" | (V) "?t = None" by (cases ?t, auto)
  thus ?case
  proof cases
    case F
    from trivial_ineq_Some[OF F] F show ?thesis by auto
  next
    case T
    from trivial_ineq_Some[OF T] T IH show ?thesis by force
  next
    case V
    from trivial_ineq_None[OF V] V IH show ?thesis by auto
  qed
qed simp

lemma trivial_lhe: assumes "vars_l p = {}" 
  shows "eval_l \<alpha> p = constant_l p"  
    "satisfies_dleq \<alpha> p \<longleftrightarrow> p = 0" 
proof -
  show id: "eval_l \<alpha> p = constant_l p" 
    by (subst eval_l_mono[of "{}"], insert assms, auto)
  show "satisfies_dleq \<alpha> p \<longleftrightarrow> p = 0" 
    unfolding satisfies_dleq_def id using assms
    apply (transfer)
    by (metis (mono_tags, lifting) Collect_empty_eq not_None_eq)
qed


end