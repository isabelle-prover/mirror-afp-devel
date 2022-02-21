theory Eval_FO
  imports Infinite FO
begin

datatype 'a eval_res = Fin "'a table" | Infin | Wf_error

locale eval_fo =
  fixes wf :: "('a :: infinite, 'b) fo_fmla \<Rightarrow> ('b \<times> nat \<Rightarrow> 'a list set) \<Rightarrow> 't \<Rightarrow> bool"
    and abs :: "('a fo_term) list \<Rightarrow> 'a table \<Rightarrow> 't"
    and rep :: "'t \<Rightarrow> 'a table"
    and res :: "'t \<Rightarrow> 'a eval_res"
    and eval_bool :: "bool \<Rightarrow> 't"
    and eval_eq :: "'a fo_term \<Rightarrow> 'a fo_term \<Rightarrow> 't"
    and eval_neg :: "nat list \<Rightarrow> 't \<Rightarrow> 't"
    and eval_conj :: "nat list \<Rightarrow> 't \<Rightarrow> nat list \<Rightarrow> 't \<Rightarrow> 't"
    and eval_ajoin :: "nat list \<Rightarrow> 't \<Rightarrow> nat list \<Rightarrow> 't \<Rightarrow> 't"
    and eval_disj :: "nat list \<Rightarrow> 't \<Rightarrow> nat list \<Rightarrow> 't \<Rightarrow> 't"
    and eval_exists :: "nat \<Rightarrow> nat list \<Rightarrow> 't \<Rightarrow> 't"
    and eval_forall :: "nat \<Rightarrow> nat list \<Rightarrow> 't \<Rightarrow> 't"
  assumes fo_rep: "wf \<phi> I t \<Longrightarrow> rep t = proj_sat \<phi> I"
  and fo_res_fin: "wf \<phi> I t \<Longrightarrow> finite (rep t) \<Longrightarrow> res t = Fin (rep t)"
  and fo_res_infin: "wf \<phi> I t \<Longrightarrow> \<not>finite (rep t) \<Longrightarrow> res t = Infin"
  and fo_abs: "finite (I (r, length ts)) \<Longrightarrow> wf (Pred r ts) I (abs ts (I (r, length ts)))"
  and fo_bool: "wf (Bool b) I (eval_bool b)"
  and fo_eq: "wf (Eqa trm trm') I (eval_eq trm trm')"
  and fo_neg: "wf \<phi> I t \<Longrightarrow> wf (Neg \<phi>) I (eval_neg (fv_fo_fmla_list \<phi>) t)"
  and fo_conj: "wf \<phi> I t\<phi> \<Longrightarrow> wf \<psi> I t\<psi> \<Longrightarrow> (case \<psi> of Neg \<psi>' \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow>
    wf (Conj \<phi> \<psi>) I (eval_conj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>)"
  and fo_ajoin: "wf \<phi> I t\<phi> \<Longrightarrow> wf \<psi>' I t\<psi>' \<Longrightarrow>
    wf (Conj \<phi> (Neg \<psi>')) I (eval_ajoin (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>') t\<psi>')"
  and fo_disj: "wf \<phi> I t\<phi> \<Longrightarrow> wf \<psi> I t\<psi> \<Longrightarrow>
    wf (Disj \<phi> \<psi>) I (eval_disj (fv_fo_fmla_list \<phi>) t\<phi> (fv_fo_fmla_list \<psi>) t\<psi>)"
  and fo_exists: "wf \<phi> I t \<Longrightarrow> wf (Exists i \<phi>) I (eval_exists i (fv_fo_fmla_list \<phi>) t)"
  and fo_forall: "wf \<phi> I t \<Longrightarrow> wf (Forall i \<phi>) I (eval_forall i (fv_fo_fmla_list \<phi>) t)"
begin

fun eval_fmla :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> 't" where
  "eval_fmla (Pred r ts) I = abs ts (I (r, length ts))"
| "eval_fmla (Bool b) I = eval_bool b"
| "eval_fmla (Eqa t t') I = eval_eq t t'"
| "eval_fmla (Neg \<phi>) I = eval_neg (fv_fo_fmla_list \<phi>) (eval_fmla \<phi> I)"
| "eval_fmla (Conj \<phi> \<psi>) I = (let ns\<phi> = fv_fo_fmla_list \<phi>; ns\<psi> = fv_fo_fmla_list \<psi>;
    X\<phi> = eval_fmla \<phi> I in
  case \<psi> of Neg \<psi>' \<Rightarrow> let X\<psi>' = eval_fmla \<psi>' I in
    eval_ajoin ns\<phi> X\<phi> (fv_fo_fmla_list \<psi>') X\<psi>'
  | _ \<Rightarrow> eval_conj ns\<phi> X\<phi> ns\<psi> (eval_fmla \<psi> I))"
| "eval_fmla (Disj \<phi> \<psi>) I = eval_disj (fv_fo_fmla_list \<phi>) (eval_fmla \<phi> I)
    (fv_fo_fmla_list \<psi>) (eval_fmla \<psi> I)"
| "eval_fmla (Exists i \<phi>) I = eval_exists i (fv_fo_fmla_list \<phi>) (eval_fmla \<phi> I)"
| "eval_fmla (Forall i \<phi>) I = eval_forall i (fv_fo_fmla_list \<phi>) (eval_fmla \<phi> I)"

lemma eval_fmla_correct:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "wf_fo_intp \<phi> I"
  shows "wf \<phi> I (eval_fmla \<phi> I)"
  using assms
proof (induction \<phi> I rule: eval_fmla.induct)
  case (1 r ts I)
  then show ?case
    using fo_abs
    by auto
next
  case (2 b I)
  then show ?case
    using fo_bool
    by auto
next
  case (3 t t' I)
  then show ?case
    using fo_eq
    by auto
next
  case (4 \<phi> I)
  then show ?case
    using fo_neg
    by auto
next
  case (5 \<phi> \<psi> I)
  have fins: "wf_fo_intp \<phi> I" "wf_fo_intp \<psi> I"
    using 5(10)
    by auto
  have eval\<phi>: "wf \<phi> I (eval_fmla \<phi> I)"
    using 5(1)[OF _ _ fins(1)]
    by auto
  show ?case
  proof (cases "\<exists>\<psi>'. \<psi> = Neg \<psi>'")
    case True
    then obtain \<psi>' where \<psi>_def: "\<psi> = Neg \<psi>'"
      by auto
    have fin: "wf_fo_intp \<psi>' I"
      using fins(2)
      by (auto simp: \<psi>_def)
    have eval\<psi>': "wf \<psi>' I (eval_fmla \<psi>' I)"
      using 5(5)[OF _ _ _ \<psi>_def fin]
      by auto
    show ?thesis
      unfolding \<psi>_def
      using fo_ajoin[OF eval\<phi> eval\<psi>']
      by auto
  next
    case False
    then have eval\<psi>: "wf \<psi> I (eval_fmla \<psi> I)"
      using 5 fins(2)
      by (cases \<psi>) auto
    have eval: "eval_fmla (Conj \<phi> \<psi>) I = eval_conj (fv_fo_fmla_list \<phi>) (eval_fmla \<phi> I)
      (fv_fo_fmla_list \<psi>) (eval_fmla \<psi> I)"
      using False
      by (auto simp: Let_def split: fo_fmla.splits)
    show "wf (Conj \<phi> \<psi>) I (eval_fmla (Conj \<phi> \<psi>) I)"
      using fo_conj[OF eval\<phi> eval\<psi>, folded eval] False
      by (auto split: fo_fmla.splits)
  qed
next
  case (6 \<phi> \<psi> I)
  then show ?case
    using fo_disj
    by auto
next
  case (7 i \<phi> I)
  then show ?case
    using fo_exists
    by auto
next
  case (8 i \<phi> I)
  then show ?case
    using fo_forall
    by auto
qed

definition eval :: "('a, 'b) fo_fmla \<Rightarrow> ('a table, 'b) fo_intp \<Rightarrow> 'a eval_res" where
  "eval \<phi> I = (if wf_fo_intp \<phi> I then res (eval_fmla \<phi> I) else Wf_error)"

lemma eval_fmla_proj_sat:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "wf_fo_intp \<phi> I"
  shows "rep (eval_fmla \<phi> I) = proj_sat \<phi> I"
  using eval_fmla_correct[OF assms]
  by (auto simp: fo_rep)

lemma eval_sound:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "eval \<phi> I = Fin Z"
  shows "Z = proj_sat \<phi> I"
proof -
  have "wf \<phi> I (eval_fmla \<phi> I)"
    using eval_fmla_correct assms
    by (auto simp: eval_def split: if_splits)
  then show ?thesis
    using assms fo_res_fin fo_res_infin
    by (fastforce simp: eval_def fo_rep split: if_splits)
qed

lemma eval_complete:
  fixes \<phi> :: "('a :: infinite, 'b) fo_fmla"
  assumes "eval \<phi> I = Infin"
  shows "infinite (proj_sat \<phi> I)"
proof -
  have "wf \<phi> I (eval_fmla \<phi> I)"
    using eval_fmla_correct assms
    by (auto simp: eval_def split: if_splits)
  then show ?thesis
    using assms fo_res_fin
    by (auto simp: eval_def fo_rep split: if_splits)
qed

end

end
