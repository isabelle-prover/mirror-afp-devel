chapter "Adaptations for Isabelle"

theory Semantic_Extras
imports
  "generated/CakeML/BigStep"
  "generated/CakeML/SemanticPrimitivesAuxiliary"
  "generated/CakeML/AstAuxiliary"
  "generated/CakeML/Evaluate"
  "HOL-Library.Simps_Case_Conv"
begin

hide_const (open) sem_env.v

code_pred
  (modes: evaluate: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as compute
      and evaluate_list: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool
      and evaluate_match: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) evaluate .

case_of_simps do_log_alt_def: do_log.simps

lemma size_list_rev[simp]: "size_list f (rev xs) = size_list f xs"
by (auto simp: size_list_conv_sum_list rev_map[symmetric])

lemma do_if_cases:
  obtains
    (none) "do_if v e1 e2 = None"
  | (true) "do_if v e1 e2 = Some e1"
  | (false) "do_if v e1 e2 = Some e2"
unfolding do_if_def
by meson

case_of_simps do_con_check_alt_def: do_con_check.simps
case_of_simps list_result_alt_def: list_result.simps

context begin

private fun_cases do_logE: "do_log op v e = res"

lemma do_log_exp: "do_log op v e = Some (Exp e') \<Longrightarrow> e = e'"
by (erule do_logE)
   (auto split: v.splits option.splits if_splits tid_or_exn.splits id0.splits list.splits)

end

lemma do_log_cases:
  obtains
    (none) "do_log op v e = None"
  | (val) v' where "do_log op v e = Some (Val v')"
  | (exp) "do_log op v e = Some (Exp e)"
proof (cases "do_log op v e")
  case None
  then show ?thesis using none by metis
next
  case (Some res)
  with val exp show ?thesis
    by (cases res) (metis do_log_exp)+
qed

context begin

private fun_cases do_opappE: "do_opapp vs = Some res"

lemma do_opapp_cases:
  assumes "do_opapp vs = Some (env', exp')"
  obtains (closure) env n v0
            where "vs = [Closure env n exp', v0]"
                  "env' = (env \<lparr> sem_env.v := nsBind n v0 (sem_env.v env) \<rparr> )"
        | (recclosure) env funs name n v0
            where "vs = [Recclosure env funs name, v0]"
              and "allDistinct (map (\<lambda>(f, _, _). f) funs)"
              and "find_recfun name funs = Some (n, exp')"
              and "env' = (env \<lparr> sem_env.v := nsBind n v0 (build_rec_env funs env (sem_env.v env)) \<rparr> )"
proof -
  show thesis
    using assms
    apply (rule do_opappE)
    apply (rule closure; auto)
    apply (auto split: if_splits option.splits)
    apply (rule recclosure)
    apply auto
    done
qed

end

lemmas evaluate_induct =
  evaluate_match_evaluate_list_evaluate.inducts[split_format(complete)]

lemma evaluate_clock_mono:
  "evaluate_match ck env s v pes v' (s', r1) \<Longrightarrow> ck \<Longrightarrow> clock s' \<le> clock s"
  "evaluate_list ck env s es (s', r2) \<Longrightarrow> ck \<Longrightarrow> clock s' \<le> clock s"
  "evaluate ck env s e (s', r3) \<Longrightarrow> ck \<Longrightarrow> clock s' \<le> clock s"
by (induction rule: evaluate_induct)
   (auto simp del: do_app.simps simp: datatype_record_update split: state.splits)

lemma evaluate_list_singleton_valE:
  assumes "evaluate_list ck env s [e] (s', Rval vs)"
  obtains v where "vs = [v]" "evaluate ck env s e (s', Rval v)"
using assms
by (auto elim: evaluate_list.cases)

lemma evaluate_list_singleton_errD:
  assumes "evaluate_list ck env s [e] (s', Rerr err)"
  shows "evaluate ck env s e (s', Rerr err)"
using assms
by (auto elim: evaluate_list.cases)

lemma evaluate_list_singleton_cases:
  assumes "evaluate_list ck env s [e] res"
  obtains (val) s' v where "res = (s', Rval [v])" "evaluate ck env s e (s', Rval v)"
        | (err) s' err where "res = (s', Rerr err)" "evaluate ck env s e (s', Rerr err)"
using assms
apply -
apply (ind_cases "evaluate_list ck env s [e] res")
apply auto
apply (ind_cases "evaluate_list ck env s2 [] (s3, Rval vs)" for s2 s3 vs)
apply auto
apply (ind_cases " evaluate_list ck env s2 [] (s3, Rerr err) " for s2 s3 err)
done

lemma evaluate_list_singletonI:
  assumes "evaluate ck env s e (s', r)"
  shows "evaluate_list ck env s [e] (s', list_result r)"
using assms
by (cases r) (auto intro: evaluate_match_evaluate_list_evaluate.intros)

lemma prod_result_cases:
  obtains (val) s v where "r = (s, Rval v)"
        | (err) s err where "r = (s, Rerr err)"
apply (cases r)
subgoal for _ b
  apply (cases b)
  by auto
done

lemma do_con_check_build_conv: "do_con_check (c env) cn (length es) \<Longrightarrow> build_conv (c env) cn vs \<noteq> None"
by (cases cn) (auto split: option.splits)

end