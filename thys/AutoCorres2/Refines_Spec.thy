(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter \<open>TS phase: Type Strengthening (find suitable target monad)\<close>

theory Refines_Spec
  imports
  Option_MonadND
  L2ExceptionRewrite
begin


(* TODO: where to put these? *)

lemma gets_the_ocondition: 
  "Spec_Monad.gets_the (ocondition C T F) =
    Spec_Monad.condition C (Spec_Monad.gets_the T) (Spec_Monad.gets_the F)"
  by (simp add: spec_monad_ext_iff ocondition_def run_condition)

lemma gets_the_oreturn: 
  "Spec_Monad.gets_the (oreturn x) = Spec_Monad.return x"
  by (simp add: spec_monad_ext_iff)

lemma gets_the_obind: 
  "Spec_Monad.gets_the (obind f g) =
    Spec_Monad.bind (Spec_Monad.gets_the f) (\<lambda>x. Spec_Monad.gets_the (g x))"
  by (simp add: spec_monad_ext_iff run_bind obind_def split: option.splits)

setup \<open>
let open Mutual_CCPO_Rec in
  add_ccpo "spec_monad_gfp" (fn ctxt => fn (T as \<^Type>\<open>spec_monad E A S\<close>)  => 
    let
    in 
      synth_gfp ctxt T
    end) 
  |> Context.theory_map
end
\<close>

lemma rel_map_the_Result[simp]: "rel_map the_Result (Result v) b \<longleftrightarrow> v = b"
  by (auto simp add: rel_map_def)

lemma holds_partial_post_state_Inf:
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> holds_partial_post_state P x"
  shows "holds_partial_post_state P (\<Sqinter> X)"
  apply (clarsimp simp add: Inf_post_state_def vimage_def)
  subgoal premises prems for p x
    using X[of "Success x"] prems by auto
  done

lemma holds_post_state_Inf:
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> holds_post_state P x"
  shows "X \<noteq> {} \<Longrightarrow> holds_post_state P (\<Sqinter> X)"
  apply (clarsimp simp add: Inf_post_state_def vimage_def, safe)
  subgoal for x using X[of x] by (cases x) auto
  subgoal using assms by force
  done

lemma admissible_runs_to[corres_admissible]:
  "ccpo.admissible Inf (\<lambda>x y. y \<le> x) (\<lambda>x. x \<bullet> s \<lbrace> Q \<rbrace>)"
  apply (simp add: ccpo.admissible_def chain_def)
  apply transfer
  apply (auto intro: holds_post_state_Inf)
  done
  
lemma spec_monad_Inf_run: "(run (\<Sqinter>A) s) = \<Sqinter> ((\<lambda>f. (run f s)) ` A)"
  by (metis INF_apply Inf_spec_monad.rep_eq)

lemma outcomes_Inf_run_succeeds_conv:
  "outcomes (\<Sqinter>f\<in>A. run f t) =  outcomes (\<Sqinter>f \<in> {f. f \<in> A \<and> succeeds f t}. run f t)"
  apply (clarsimp simp add: Inf_post_state_def succeeds_def top_post_state_def)
  apply fastforce
  done

lemma succeeds_outcomes_Inf_Inter_conv:
  "g \<in> A \<Longrightarrow> succeeds g t \<Longrightarrow> outcomes (\<Sqinter>f \<in> {f \<in> A. succeeds f t}. run f t) =
         (\<Inter>f\<in>{f \<in> A. succeeds f t}. outcomes (run f t))"
  apply (clarsimp simp add: Inf_post_state_def succeeds_def top_post_state_def, intro impI conjI set_eqI iffI)
  subgoal by (auto simp add: vimage_def image_def split: post_state.splits)
  subgoal by (smt (verit, ccfv_SIG) INF_top_conv(2) Inf_post_state_def mem_Collect_eq top_post_state_def)
  subgoal by (smt (verit) Success_vimage_image_cancel image_cong mem_Collect_eq outcomes_succeeds_run_conv succeeds_def top_post_state_def)
  subgoal by (smt (verit, best) Success_vimage_image_cancel image_cong mem_Collect_eq outcomes_succeeds_run_conv succeeds_def top_post_state_def)
  done


lemma admissible_refines_spec_fun_of_rel:
  assumes prj: "fun_of_rel R prj"
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('e::default, 'a, 's) spec_monad) . refines C A s t (rel_prod R (=)))"
proof (rule ccpo.admissibleI)
  fix A::"('e, 'a, 's) spec_monad set"
  assume A_prop: "\<forall>g\<in>A. refines C g s t (rel_prod R (=))"
  assume chain: "Complete_Partial_Order.chain (\<ge>) A"
  assume non_empty: "A \<noteq> {}"
  have Inf_lower: "\<And>g. g \<in> A \<Longrightarrow> \<Sqinter> A \<le> g"
    by (simp add: Inf_lower)

  hence run_Inf_lower: "\<And>g s. g \<in> A \<Longrightarrow> run ( \<Sqinter> A) s \<le> run g s"
    by (simp add: le_funD less_eq_spec_monad.rep_eq)


  have "(\<And>s. (\<And>g. g \<in> A \<Longrightarrow> run g s = Failure) \<Longrightarrow> run (\<Sqinter>A) s = Failure)"
    apply (simp add: spec_monad_Inf_run)
    by (simp add: non_empty)

  hence succeeds: "\<And>s. succeeds (\<Sqinter>A) s \<Longrightarrow> (\<exists>g \<in> A. succeeds g s)"
    by (auto simp add: succeeds_def top_post_state_def)

  show "refines C (\<Sqinter> A) s t (rel_prod R (=))"
    apply (clarsimp simp add: refines_def_old reaches_def)
    apply (intro conjI allI impI)
  proof -
    assume  "succeeds (\<Sqinter> A) t" then
    show "succeeds C s"
      using succeeds A_prop non_empty 
      by (auto simp add: refines_def_old)
  next
    fix r s'
    assume succeeds_Inf: "succeeds (\<Sqinter> A) t"
    then obtain g where g: "g \<in> A" and succeeds_g: "succeeds g t"
      using succeeds by blast

    assume res: "(r, s') \<in> outcomes (run C s)"
    show   "\<exists>r'. (r', s') \<in> outcomes (run (\<Sqinter> A) t) \<and> R r r'"
    proof -
      from A_prop res prj
      have prj_prop: "\<And>g. g \<in> A \<Longrightarrow> succeeds g t \<Longrightarrow> (prj r, s') \<in> outcomes (run g t) \<and> R r (prj r)"
        apply (clarsimp simp add: refines_def_old )
        using fun_of_rel_def
        by (smt (verit) reaches_def)
      hence "(prj r, s') \<in> outcomes (run (\<Sqinter> A) t)"
        apply (simp add: spec_monad_Inf_run)
        apply (subst outcomes_Inf_run_succeeds_conv)
        apply (subst succeeds_outcomes_Inf_Inter_conv [OF g succeeds_g])
        apply auto
        done
      moreover from prj_prop g succeeds_g have "R r (prj r)" by blast
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma admissible_refines_spec_funp:
  assumes "funp R"
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('e::default, 'a, 's) spec_monad) . refines C A s t (rel_prod R (=)))"
proof -
  from assms obtain prj where "fun_of_rel R prj"
    by (auto simp add: funp_def)
  then show ?thesis
    by (rule admissible_refines_spec_fun_of_rel)
qed

lemma admissible_refines_spec_res[corres_admissible]:
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('a, 's) res_monad) . refines C A s t (rel_prod (rel_liftE ) (=)))"
  by (rule admissible_refines_spec_funp) (intro funp_intros)

lemma admissible_refines_spec_exit_eq[corres_admissible]:
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('e, 'a, 's) exn_monad) . refines C A s t (rel_prod (rel_xval (=) (=)) (=)))"
  by (rule admissible_refines_spec_funp) (intro funp_intros)

lemma admissible_refines_spec_exit_the_Nonlocal[corres_admissible]:
  shows "ccpo.admissible Inf (\<ge>)
           (\<lambda>(A::('e, 'a, 's) exn_monad) . refines C A s t (rel_prod ((rel_xval (rel_Nonlocal) (=))) (=)))"
  by (rule admissible_refines_spec_funp) (intro funp_intros)


lemma gen_admissible_refines_gets_the[corres_admissible]:
  shows "ccpo.admissible option.lub_fun option.le_fun (\<lambda>A. refines C (gets_the A) s t (rel_prod (rel_liftE) (=)))"
  apply (clarsimp simp add: refines_def_old relcompp.simps rel_liftE_def rel_map_def
    split: option.splits)
  by (smt (verit) ccpo.admissibleI chain_fun flat_lub_in_chain fun_lub_def mem_Collect_eq option.discI)

theorem refines_option_top [corres_top]: "refines f (gets_the Map.empty) s t R"
  by (auto simp add: refines_def_old)

section \<open>Synthesize Rules Setup\<close>

text \<open>Canonical format for the currently supported monads:
\<^term>\<open>refines C (lift_to_spec A) s t (rel_prod rel_res (=))\<close>
where \<^term>\<open>lift_spec\<close>, \<^term>\<open>rel_res\<close> is
\<^item> pure (Pure function): \<^term>\<open>return\<close>, \<^term>\<open>rel_liftE\<close>
\<^item> gets (Reader monad): \<^term>\<open>gets\<close>,\<^term>\<open>rel_liftE\<close>
\<^item> option (Option monad):  \<^term>\<open>gets_the\<close>,\<^term>\<open>rel_liftE\<close>
\<^item> nondet: \<^term>\<open>id\<close> (ommitted),\<^term>\<open>rel_liftE\<close>
\<^item> exit:
  \<^item> \<^term>\<open>id\<close> (ommitted),\<^term>\<open>rel_xval rel_Nonlocal (=)\<close>
  \<^item> \<^term>\<open>id\<close> (ommitted),\<^term>\<open>rel_xval (=) (=)\<close> for those function that were
     lifted by the IO phase.
\<close>

synthesize_rules pure and reader and option and nondet and exit

add_synthesize_pattern pure and reader and option and nondet and exit where
  refines_pure_synth = \<open>Trueprop (refines ?f ((return ?f')::(?'a, ?'s) res_monad) _ _ ?R)\<close> (f')
 
add_synthesize_pattern reader and option and nondet and exit where
  refines_reader_synth = \<open>Trueprop (refines ?f (gets ?f') _ _ ?R)\<close> (f')

add_synthesize_pattern option where
  refines_option_synth = \<open>Trueprop (refines ?f (gets_the ?f') _ _ ?R)\<close> (f')

add_synthesize_pattern nondet and exit where
  refines_nondet_synth = \<open>Trueprop (refines ?f ?f' _ _ ?R)\<close> (f') and

  rel_liftE_nondet_synth = \<open>Trueprop (rel_liftE ?x ?x')\<close> (x') and
  rel_sum_nondet_synth = \<open>Trueprop (rel_sum _ _ ?x ?x')\<close> (x') and
  rel_sum_nondet_synth = \<open>Trueprop (rel_xval _ _ ?x ?x')\<close> (x') and
  rel_compp_nondet_synth = \<open>Trueprop ((_ OO _) ?x ?x')\<close> (x') and
  rel_map_synth = \<open>Trueprop (rel_map ?f ?x ?x')\<close> (x') and
  rel_eq_nondet_synth = \<open>Trueprop (?x = ?x')\<close> (x')

add_synthesize_pattern exit where
  rel_Nondet_exit_synth = \<open>Trueprop (rel_Nonlocal ?x ?x')\<close> (x')

text \<open>
Recursive functions are defined using @{command fixed_point}.
The option, nondet and exit monad are setup to handle these definitions. Hence the minimal
monad for recursive functions is the option monad.
\<close>

section \<open>Pure Monad\<close>


lemma refines_L2_call_embed_pure:
  assumes f: "refines f (return f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_call f emb ns) (return (L2_VARS f' ns)::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  unfolding L2_VARS_def L2_call_def
  using f
  apply (clarsimp simp add: refines_def_old reaches_map_value map_exn_def rel_liftE_def split: xval_splits)
  apply (metis Exn_def default_option_def exception_or_result_cases not_Some_eq)+
  done

lemma refines_L2_gets_pure:
  "refines (L2_gets (\<lambda>_. v) ns) (return (L2_VARS v ns)::('a,'s) res_monad) s s (rel_prod (rel_liftE) (=))"
  unfolding L2_VARS_def L2_defs gets_return
  by (auto intro: refines_yield)


lemma refines_L2_seq_pure:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (g v) (return (g' v)::('a,'s) res_monad) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def, rule_format]: "PROP THIN (Trueprop (refines f ((return f')::('b,'s) res_monad) s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_seq f g) (return (let v = f' in (g' v))::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs
  apply (clarsimp simp add: refines_def_old reaches_bind succeeds_bind rel_liftE_def default_option_def split: exception_or_result_splits)
  apply (metis default_option_def exception_or_result_cases option.exhaust_sel)+
  done

lemma refines_L2_condition_pure:
  assumes g: "refines g (return g'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  assumes f: "refines f (return f'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  shows "refines (L2_condition (\<lambda>_. c) f g) (return (if c then f' else g')::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs
  by (auto intro: refines_condition)

lemma refines_L2_try_L2_throw_pure:
  shows "refines (L2_try (L2_throw (Inr r) ns)) (return (L2_VARS r ns)::('a,'s)res_monad) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_VARS_def
  by (auto simp add: refines_def_old reaches_try rel_liftE_def unnest_exn_def)

lemma refines_L2_try_L2_seq_pure:
  assumes g: "\<And>v t. refines (L2_try (g v)) (return (g' v)::('a,'s) res_monad) t t (rel_prod rel_liftE (=))"
  assumes f: "refines f (return f'::('b,'s) res_monad) s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try (L2_seq f g)) (return (let v = f' in (g' v))::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs try_def refines_map_value_left_iff return_let_bind
  apply (rule refines_bind [OF f])
  subgoal by auto
  subgoal by (auto simp add: default_option_def Exn_def[symmetric] rel_liftE_def)
  subgoal by auto
  subgoal using g [simplified L2_defs try_def refines_map_value_left_iff] by auto
  done

lemma refines_L2_try_L2_condition_pure:
  assumes f: "refines (L2_try f) (return f'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  assumes g: "refines (L2_try g) (return g'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try (L2_condition (\<lambda>_. c) f g)) (return (if c then f' else g')::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  using f g unfolding L2_defs
  apply (auto simp add: refines_def_old reaches_try reaches_bind succeeds_bind rel_liftE_def unnest_exn_def
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  done

lemma refines_L2_try_pure:
  assumes f: "refines f (return f'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try f) (return f'::('a,'s) res_monad) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_guarded_def try_def using f
  apply (clarsimp simp add: refines_def_old reaches_try reaches_map_value rel_liftE_def unnest_exn_def
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  by (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel sum_all_ex(2))

print_synthesize_rules pure

lemmas refines_monad_pure =
  refines_L2_call_embed_pure [synthesize_rule pure and reader and option and nondet and exit priority:510]
  refines_L2_gets_pure [synthesize_rule pure and reader and option and nondet and exit priority:510]
  refines_L2_seq_pure [synthesize_rule pure and reader and option and nondet and exit priority:510 split: g and g']
  refines_L2_condition_pure [synthesize_rule pure and reader and option and nondet and exit priority:510]
  refines_L2_try_L2_throw_pure [synthesize_rule pure and reader and option and nondet and exit priority:520]
  refines_L2_try_L2_seq_pure [synthesize_rule pure and reader and option and nondet and exit priority:520 split: g and g']
  refines_L2_try_L2_condition_pure [synthesize_rule pure and reader and option and nondet and exit priority:520]
  refines_L2_try_pure [synthesize_rule pure and reader and option and nondet and exit priority:510]

print_synthesize_rules pure

section \<open>Reader Monad (Gets)\<close>

lemma refines_L2_call_embed_reader:
  assumes f: "refines f (gets f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_call f emb ns) (gets (L2_VARS f' ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_call_def liftE_def L2_VARS_def using f
  apply (clarsimp simp add: refines_def_old reaches_try reaches_map_value rel_liftE_def map_exn_def
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  by (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)


lemma refines_L2_gets_reader:
  "refines (L2_gets f ns) (gets (L2_VARS f ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_VARS_def liftE_def
  by (auto intro: refines_gets)

lemma refines_lift_pure_reader:
  assumes f: "refines f (return f') s s (rel_prod rel_liftE (=))"
  shows "refines f (gets (\<lambda>_. f')) s s (rel_prod rel_liftE (=))"
  using f unfolding liftE_def
  by (simp add: gets_return)

lemma refines_L2_seq_reader:
  assumes g: "\<And>v t. refines (g v) (gets (g' v)) t t (rel_prod rel_liftE (=))"
  assumes f: "refines f (gets f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_seq f g) (gets (\<lambda>s. let v = f' s in (g' v s))) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs liftE_def
  apply (clarsimp simp add: refines_def_old reaches_bind succeeds_bind rel_liftE_def 
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  apply (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)+
  done

lemma refines_L2_condition_reader:
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines g (gets g') s s (rel_prod rel_liftE (=))))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f (gets f') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_condition c f g) (gets (\<lambda>s. if c s then f' s else g' s)) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs liftE_def
  apply (auto simp add: refines_def_old reaches_bind succeeds_bind rel_liftE_def 
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  done

lemma refines_L2_try_L2_throw_reader:
  shows "refines (L2_try (L2_throw (Inr r) ns)) (gets (L2_VARS (\<lambda>_. r) ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_VARS_def liftE_def
  apply (auto simp add: refines_def_old reaches_try reaches_map_value rel_liftE_def map_exn_def
      default_option_def Exn_def [symmetric]
      split: xval_split exception_or_result_splits sum.splits)
  done

lemma refines_L2_try_L2_seq_reader:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (L2_try (g v)) (gets (g' v)) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f (gets f') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_seq f g)) (gets (\<lambda>s. let v = f' s in (g' v s))) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs try_def refines_map_value_left_iff gets_let_bind
  apply (rule refines_bind [OF f])
  subgoal by auto
  subgoal by (auto simp add: default_option_def Exn_def [symmetric] rel_liftE_def)
  subgoal by auto
  subgoal using g [unfolded L2_defs try_def refines_map_value_left_iff ] by auto
  done

lemma refines_L2_try_L2_condition_reader:
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try f) (gets f') s s (rel_prod rel_liftE (=))))"
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try g) (gets g') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_condition (c) f g)) (gets (\<lambda>s. if c s then f' s else g' s)) s s (rel_prod rel_liftE (=))"
  using f g unfolding L2_defs liftE_def
  apply (auto simp add: refines_def_old reaches_try)
  done

lemma refines_L2_try_reader:
  assumes f: "refines f (gets f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try f) (gets f') s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_guarded_def try_def liftE_def using f
  by (auto simp add: refines_def_old reaches_map_value rel_liftE_def unnest_exn_def split: xval_splits)
   (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)+

lemmas refines_monad_reader =
  refines_L2_call_embed_reader [synthesize_rule reader and option and nondet and exit priority:410]
  refines_L2_gets_reader [synthesize_rule reader and option and nondet and exit priority:410]
  refines_lift_pure_reader [synthesize_rule reader and option and nondet and exit priority:440]
  refines_L2_seq_reader [synthesize_rule reader and option and nondet and exit priority:410 split: g and g']
  refines_L2_condition_reader [synthesize_rule reader and option and nondet and exit priority:410]
  refines_L2_try_L2_throw_reader [synthesize_rule reader and option and nondet and exit priority:420]
  refines_L2_try_L2_seq_reader [synthesize_rule reader and option and nondet and exit priority:420 split: g and g']
  refines_L2_try_L2_condition_reader [synthesize_rule reader and option and nondet and exit priority:420]
  refines_L2_try_reader [synthesize_rule reader and option and nondet and exit priority:410]

section \<open>Option (Reader) Monad \<close>

lemma refines_lift_reader_option:
  assumes f: "refines f (gets f') s s (rel_prod rel_liftE (=))"
  shows "refines f (gets_the (ogets f')) s s (rel_prod rel_liftE (=))"
  using f 
  apply (auto simp add: refines_def_old rel_liftE_def ogets_def)
  done

lemma refines_L2_call_embed_option:
  assumes f: "refines f (gets_the f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_call f emb ns) (gets_the (L2_VARS f' ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_VARS_def L2_call_def L2_defs using f
  apply (clarsimp simp add: refines_def_old reaches_map_value map_exn_def rel_liftE_def split: xval_splits)
  apply (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)+
  done

lemma refines_L2_gets_option:
  "refines (L2_gets v ns) (gets_the (L2_VARS (ogets v) ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_VARS_def L2_defs liftE_def
  apply (auto simp add: refines_def_old rel_liftE_def ogets_def)
  done

lemma refines_L2_seq_option:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (g v) (gets_the (g' v)) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f (gets_the f') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_seq f g) (gets_the (f' |>> g')) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs obind_def [abs_def]
  by (fastforce simp add: refines_def_old reaches_bind succeeds_bind rel_liftE_def split: xval_splits option.splits)

lemma refines_L2_condition_option:
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines g (gets_the g') s s (rel_prod rel_liftE (=))))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f (gets_the f') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_condition c f g) (gets_the (ocondition c f' g')) s s (rel_prod rel_liftE (=))"
  using g f unfolding L2_defs ocondition_def
  by (auto simp add: refines_def_old rel_liftE_def split: xval_splits option.splits)

lemma refines_L2_try_L2_throw_option:
  shows "refines (L2_try (L2_throw (Inr r) ns)) (gets_the (L2_VARS (oreturn r) ns)) s s (rel_prod rel_liftE  (=))"
  unfolding L2_defs L2_VARS_def oreturn_def K_def
  by (auto simp add: refines_def_old reaches_try unnest_exn_def rel_liftE_def split: xval_splits)


lemma refines_L2_try_L2_seq_option:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (L2_try (g v)) (gets_the (g' v)) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f (gets_the f') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_seq f g)) (gets_the (f' |>> g')) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs try_def refines_map_value_left_iff
  apply (simp add: gets_the_obind)
  apply (rule refines_bind [OF f])
  subgoal by auto
  subgoal by (auto simp add: default_option_def Exn_def [symmetric] rel_liftE_def)
  subgoal by auto
  subgoal using g [simplified L2_defs try_def refines_map_value_left_iff] by auto
  done

lemma refines_L2_try_L2_condition_option:
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try f) (gets_the f') s s (rel_prod rel_liftE (=))))"
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try g) (gets_the g') s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_condition c f g)) (gets_the (ocondition c f' g')) s s (rel_prod rel_liftE (=))"
  using f g unfolding L2_defs ocondition_def
  apply (auto simp add: refines_def_old reaches_try)
  done

lemma refines_L2_try_option:
  assumes f: "refines f (gets_the f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try f) (gets_the f') s s (rel_prod rel_liftE (=))"
  unfolding L2_defs using f
  apply (clarsimp simp add: refines_def_old reaches_try unnest_exn_def rel_liftE_def split: xval_splits)
  apply (metis Exn_def default_option_def exception_or_result_cases not_None_eq)+
  done

lemma le_whileLoop_succeeds_terminatesI:
  assumes "\<And>s. run (whileLoop C B r) s \<noteq> \<top> \<Longrightarrow> run f s \<le> run (whileLoop C B r) s"
  shows "f \<le> whileLoop C B r"
proof (rule le_spec_monad_runI)
  fix s
  show "run f s \<le> run (whileLoop C B r) s"
  proof (cases "run (whileLoop C B r) s = \<top>")
    case False then show ?thesis by (rule assms)
  qed simp
qed

lemma gets_the_whileLoop:
  fixes C :: "'a \<Rightarrow> 's \<Rightarrow> bool" 
  shows "whileLoop C (\<lambda>a. gets_the (B a)) r =
    ((gets_the (owhile C B r))::('e::default, 'a, 's) spec_monad)"
proof (rule antisym)
  show "(whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r::('e, 'a, 's) spec_monad) \<le> 
        Spec_Monad.gets_the (owhile C B r)"

  proof -
    {
      fix s v
      assume "(Some r, Some v) \<in> option_while' (\<lambda>a. C a s) (\<lambda>a. B a s)" 
      then have "run ((whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r)::('e, 'a, 's) spec_monad) s \<le> Success {(Result v, s)}"
      proof (induct "Some r" "Some v" arbitrary: r )
        assume "\<not> C v s" 
        then
        show "run (whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) v) s \<le> Success {(Result v, s)}"
          by (subst whileLoop_unroll) simp
      next
        fix r r'
        assume "C r s"
        and "B r s = Some r'"
        and "(Some r', Some v) \<in> option_while' (\<lambda>a. C a s) (\<lambda>a. B a s)"
        and "run ((whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r')::('e, 'a, 's) spec_monad) s \<le> Success {(Result v, s)}"
        thus "run ((whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r)::('e, 'a, 's) spec_monad) s \<le> Success {(Result v, s)}"
          by (subst whileLoop_unroll) (simp add: run_bind)
      qed      
    } note * = this
    show ?thesis
      apply (rule le_spec_monad_runI)
      apply simp
      apply (clarsimp simp add: owhile_def option_while_def option_while'_THE pure_post_state_def
          split: option.splits)
      by (rule *)
  qed
next
  show "Spec_Monad.gets_the (owhile C B r) \<le> ((whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r)::('e, 'a, 's) spec_monad)"
  proof (rule le_whileLoop_succeeds_terminatesI)
    fix s 
    assume "run (whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r) s \<noteq> \<top>" 
    then show "run (Spec_Monad.gets_the (owhile C B r)) s 
               \<le> run ((whileLoop C (\<lambda>a. Spec_Monad.gets_the (B a)) r)::('e, 'a, 's) spec_monad) s"
    proof (induction rule: whileLoop_ne_top_induct)
      case (step a s) then show ?case
        apply (subst owhile_unroll)
        apply (subst whileLoop_unroll)
        apply (auto simp add: gets_the_obind gets_the_ocondition gets_the_oreturn run_condition
            run_bind runs_to_holds_def
            split: option.split)
        done
    qed
  qed
qed

lemma refines_L2_while_option:
  assumes f [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (b v) (gets_the (b' v)) t t (rel_prod rel_liftE (=)))"
  shows "refines (L2_while c b i ns) (gets_the (L2_VARS (owhile c b' i) ns)) s s (rel_prod rel_liftE (=))"
  unfolding L2_while_def L2_VARS_def gets_the_whileLoop[symmetric]
  apply (rule refines_whileLoop)
  using f
  apply (simp_all add: rel_liftE_def)
  done

lemma refines_L2_fail_option:
  shows "refines L2_fail (gets_the ofail) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  by (auto simp add: refines_def_old)


lemma refines_L2_guard_option:
  shows "refines (L2_guard g) (gets_the (oguard g)) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  by (auto simp add: refines_def_old oguard_def)

lemma refines_L2_guarded:
  assumes f: "g s \<Longrightarrow> refines f (gets_the f') s s (rel_prod rel_liftE (=))"
  shows "refines (L2_guarded g f) (gets_the (oguard g |>> (\<lambda>_. f'))) s s (rel_prod rel_liftE  (=))"
  unfolding L2_defs L2_guarded_def using f
  by (auto simp add: refines_def_old reaches_bind succeeds_bind obind_def oguard_def split: option.splits)

lemmas refines_monad_option =
  refines_lift_reader_option [synthesize_rule option priority:350]
  refines_L2_call_embed_option [synthesize_rule option priority:310]
  refines_L2_gets_option [synthesize_rule option priority:310]

  refines_L2_seq_option [synthesize_rule option priority:310 split: g and g']
  refines_L2_condition_option [synthesize_rule option priority:310]
  refines_L2_try_L2_throw_option [synthesize_rule option priority:320]
  refines_L2_try_L2_seq_option [synthesize_rule option priority:320 split: g and g']
  refines_L2_try_L2_condition_option [synthesize_rule option priority:320]

  refines_L2_try_option [synthesize_rule option priority:310]
  refines_L2_while_option [synthesize_rule option priority:310 split: b and b']
  refines_L2_fail_option [synthesize_rule option priority:310]
  refines_L2_guard_option [synthesize_rule option priority:310]
  refines_L2_guarded [synthesize_rule option priority:310]

section \<open>Nondet Monad\<close>

text \<open>Note that \<^const>\<open>L2_catch\<close> is already replaced by \<^const>\<open>L2_try\<close> during exception rewriting in phase L2.\<close>

lemma refines_L2_call_embed_nondet:
  assumes f: "refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines (L2_call f emb ns) (L2_VARS f' ns) s s (rel_prod rel_liftE (=))"
  using f unfolding L2_call_def L2_VARS_def 
  apply (clarsimp simp add: refines_def_old reaches_map_value map_exn_def rel_liftE_def split: xval_splits) 
  by (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)


lemma refines_L2_call_embed_exn:
  assumes f: "refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines (L2_call f emb ns) (liftE (L2_VARS f' ns)) s s (rel_prod (rel_xval L (=)) (=))"
  using f unfolding L2_call_def L2_VARS_def 
  apply (clarsimp simp add: refines_def_old reaches_map_value map_exn_def reaches_liftE
      rel_liftE_def rel_xval.simps split: xval_splits) 
  by (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)

lemma refines_liftE_exn:
  assumes f: "refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines f (liftE f') s s (rel_prod (rel_xval L (=)) (=))"
  using f
  by (fastforce simp add: refines_def_old reaches_map_value map_exn_def reaches_liftE
      rel_liftE_def rel_xval.simps split: xval_splits)

lemma refines_L2_seq_nondet_polymorphic:
  assumes r [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (g v) (g' v) t t (rel_prod rel_liftE  (=)))"
  assumes f [unfolded THIN_def, rule_format]: "PROP THIN (Trueprop (refines f f' s s (rel_prod rel_liftE  (=))))"
  shows "refines (L2_seq f g) (bind f' g') s s (rel_prod rel_liftE (=))"
  unfolding L2_seq_def
  apply (rule refines_bind [OF f])
     apply (auto simp add: r rel_liftE_def)
  done

lemma refines_L2_seq_nondet:
  fixes f':: "('a, 's) res_monad"
  assumes r [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (g v) (g' v) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def, rule_format]: "PROP THIN (Trueprop (refines f f' s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_seq f g) ((bind f' g')::('b, 's) res_monad) s s (rel_prod rel_liftE (=))"
  using assms
  by (rule refines_L2_seq_nondet_polymorphic)


lemma refines_L2_seq_exn:
  assumes g [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (g v) (g' v) t t (rel_prod (rel_xval L (=)) (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_xval L (=)) (=))))"
  shows "refines (L2_seq f g) (bind f' g') s s (rel_prod (rel_xval L (=)) (=))"
  unfolding L2_seq_def
  apply (rule refines_bind [OF f])
     apply (auto simp add: g rel_xval.simps default_option_def Exn_def)
  done

lemma refines_try_bind_rel_liftE':
  assumes g : "\<And>v s t. S s t \<Longrightarrow> refines (try (g v)) (g' v) s t (rel_prod rel_liftE S)"
  assumes f: "refines f f' s t (rel_prod rel_liftE S)"
  shows "refines (try (bind f g)) (bind f' g') s t (rel_prod rel_liftE S)"
  unfolding try_def refines_map_value_left_iff
  apply (rule refines_bind [OF f])
  subgoal by auto
  subgoal by (auto simp add: default_option_def Exn_def [symmetric] rel_liftE_def)
  subgoal by auto
  subgoal 
    using g [simplified L2_defs try_def refines_map_value_left_iff]
    by auto
  done

lemma refines_try_bind_rel_liftE:
  assumes g : "\<And>v t. refines (try (g v)) (g' v) t t (rel_prod rel_liftE (=))"
  assumes f: "refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines (try (bind f g)) (bind f' g') s s (rel_prod rel_liftE (=))"
  apply (rule refines_try_bind_rel_liftE' [OF _ f]) 
  using g by simp

lemma refines_L2_try_L2_seq_nondet:
  assumes g [unfolded THIN_def L2_defs, rule_format]: "PROP THIN (\<And>v t. refines (L2_try (g v)) (g' v) t t (rel_prod rel_liftE (=)))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f f' s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_seq f g)) (bind f' g') s s (rel_prod rel_liftE (=))"
  unfolding L2_defs using g f
  by (rule refines_try_bind_rel_liftE)
  

lemma refines_L2_try_L2_condition_nondet:
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try f) f' s s (rel_prod rel_liftE (=))))"
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try g) g' s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_try (L2_condition c f g)) (condition c f' g') s s (rel_prod rel_liftE (=))"
  using f g unfolding L2_defs
  apply (auto simp add: refines_def_old succeeds_condition_iff reaches_condition_iff reaches_try)
  done

lemma refines_L2_try_rel_LiftE_nondet:
  assumes f: "refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines (L2_try f) f' s s (rel_prod rel_liftE (=))"
  using f unfolding L2_defs
  apply (clarsimp simp add: refines_def_old reaches_try rel_liftE_def unnest_exn_def split: xval_splits)
  by (metis Exn_def default_option_def exception_or_result_cases option.exhaust_sel)

lemma refines_try_finally_rel_liftE:
  assumes f: "refines f f' s s (rel_prod (rel_xval rel_liftE' (=)) (=))"
  shows "refines (try f) (finally f') s s (rel_prod rel_liftE (=))"
  using f unfolding try_def finally_def
  apply (rule refines_map_value)
  apply (auto simp add: unnest_exn_def unite_def rel_liftE'_def split: xval_splits sum.splits)
  done

lemma refines_L2_try_finally_nondet:
  assumes f: "refines f f' s s (rel_prod (rel_xval rel_liftE' (=)) (=))"
  shows "refines (L2_try f) (finally f') s s (rel_prod rel_liftE (=))"
  using f unfolding L2_defs
  by (rule refines_try_finally_rel_liftE)


lemma refines_L2_try_exn:
  assumes f: "refines f f' s s (rel_prod (rel_xval (rel_sum L (=)) (=)) (=))"
  shows "refines (L2_try f) (try f') s s (rel_prod (rel_xval L (=))  (=))"
  using f unfolding L2_defs try_def
  apply (rule refines_map_value)
  apply (auto simp add: unnest_exn_def split: xval_splits sum.splits)
  done

lemma refines_L2_condition_nondet:
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines g g' s s (rel_prod V (=))))"
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines f f' s s (rel_prod V (=))))"
  shows "refines (L2_condition c f g) (condition c f' g') s s (rel_prod V (=))"
  unfolding L2_condition_def using g f
  apply (auto intro: refines_condition)
  done

lemma refines_L2_while_nondet:
  assumes b [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (b v) (b' v) t t (rel_prod rel_liftE (=)))"
  shows "refines (L2_while c b i ns) (L2_VARS (whileLoop c b' i) ns) s s (rel_prod rel_liftE (=))"
  unfolding L2_while_def L2_VARS_def
  apply (rule refines_whileLoop'')
  subgoal
    by (auto)
  subgoal
    by (auto intro: b)
  subgoal
    by auto
  subgoal
    by (auto simp add: rel_liftE_def rel_exception_or_result.simps)
  done

lemma refines_L2_while_exn:
  assumes b [unfolded THIN_def, rule_format]: "PROP THIN (\<And>v t. refines (b v) (b' v) t t (rel_prod (rel_xval L (=)) (=)))"
  shows "refines (L2_while c b i ns) (L2_VARS (whileLoop c b' i) ns) s s (rel_prod ((rel_xval L (=))) (=))"
  unfolding L2_while_def L2_VARS_def
  apply (rule refines_whileLoop_exn)
      apply (auto simp add: b)
  done

lemma refines_L2_unknown_nondet:
  shows "refines (L2_unknown ns) (L2_VARS (select UNIV) ns) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_VARS_def
  apply (auto intro: refines_select)
  done


lemma refines_L2_unknown_exn:
  shows "refines (L2_unknown ns) (L2_VARS (select UNIV) ns) s s (rel_prod (rel_xval L (=))  (=))"
  unfolding L2_defs L2_VARS_def
  apply (auto intro: refines_select)
  done


lemma refines_L2_modify_nondet:
  shows "refines (L2_modify f) (modify f) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  apply (auto intro: refines_modify)
  done

lemma refines_L2_gets_nondet:
  shows "refines (L2_gets f ns) (L2_VARS (gets f) ns) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs L2_VARS_def
  apply (auto intro: refines_gets)
  done


lemma refines_L2_throw_exn:
  "L x x' \<Longrightarrow>
   refines (L2_throw x ns) (L2_VARS (throw x') ns) s s (rel_prod (rel_xval L (=)) (=))"
  unfolding L2_throw_def  L2_VARS_def
  apply (auto simp add: refines_def_old rel_xval.simps Exn_def) 
  done

lemma refines_L2_spec_nondet:
  shows "refines (L2_spec r) (assert_result_and_state (\<lambda>s. {(v, t). (s, t) \<in> r})) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  apply (auto simp add: refines_def_old reaches_bind succeeds_bind)
  done

lemma refines_L2_assume_nondet:
  shows "refines (L2_assume r) (assume_result_and_state r) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  apply (auto simp add: refines_def_old reaches_bind succeeds_bind)
  done

lemma refines_L2_guard_nondet:
  shows "refines (L2_guard c) (guard c) s s (rel_prod rel_liftE (=))"
  unfolding L2_defs
  by (auto intro: refines_guard)

lemma refines_L2_guarded_nondet:
  assumes f: "c s \<Longrightarrow> refines f f' s s (rel_prod rel_liftE (=))"
  shows "refines (L2_guarded c f) (bind (guard c) (\<lambda>_. f')) s s (rel_prod rel_liftE (=))"
  unfolding L2_guarded_def L2_seq_def L2_guard_def using f
  apply (auto simp add: refines_def_old succeeds_bind reaches_bind)
  done

lemma refines_L2_guarded_exn:
  assumes f: "c s \<Longrightarrow> refines f f' s s (rel_prod (rel_xval L (=)) (=))"
  shows "refines (L2_guarded c f) (bind (guard c) (\<lambda>_. f')) s s (rel_prod (rel_xval L (=)) (=))"
  unfolding L2_guarded_def L2_seq_def L2_guard_def using f
  apply (auto simp add: refines_def_old succeeds_bind reaches_bind)
  done

lemma refines_L2_fail_nondet:
  shows "refines L2_fail fail s s (rel_prod R (=))"
  by simp
 

lemma refines_exec_concrete_gen_nondet:
  assumes f: "\<And>s. refines f f' s s (rel_prod R (=))"
  shows "refines (exec_concrete st f) (exec_concrete st f') s s (rel_prod R (=))"
  using f
  by (fastforce simp add: refines_def_old reaches_exec_concrete succeeds_exec_concrete_iff)


lemmas refines_exec_concrete_nondet = refines_exec_concrete_gen_nondet [where R="rel_liftE"]
lemmas refines_exec_concrete_exit = refines_exec_concrete_gen_nondet [where R="rel_xval L (=)"] for L

lemma refines_exec_abstract_gen_nondet:
  assumes f: "\<And>s. refines f f' s s (rel_prod R (=))"
  shows "refines (exec_abstract st f) (exec_abstract st f') s s (rel_prod R (=))"
  using f
  by (fastforce simp add: refines_def_old reaches_exec_abstract)


lemmas refines_exec_abstract_nondet = refines_exec_abstract_gen_nondet [where R="rel_liftE"]
lemmas refines_exec_abstract_exit = refines_exec_abstract_gen_nondet [where R="rel_xval L (=)"] for L

lemma rel_map_ResultI: 
  "rel_map Result x (Result x)"
  by (simp add: rel_map_def)

lemma rel_map_to_xval_InlI: 
  "rel_map to_xval (Inl l) (Exn l)"
  by (simp add: rel_map_def)

lemma rel_map_to_xval_InrI: 
  "rel_map to_xval (Inr r) (Result r)"
  by (simp add: rel_map_def)

lemma refines_rel_prod_eq_guard_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod Q (=))"
  shows "refines
        (guard_on_exit f\<^sub>c grd cleanup)
        (guard_on_exit f\<^sub>a grd cleanup) s s
        (rel_prod Q (=))"
  unfolding guard_on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result_strong [OF f])
  apply clarsimp
  apply (rule refines_bind_no_throw [where Q="rel_prod \<top> (=)"] )
     apply simp
    apply simp
   apply (rule refines_guard)
    apply simp
   apply simp
  apply (rule refines_bind_no_throw )
     apply simp
  apply simp
    apply (clarsimp)
   apply (rule refines_state_select_same)
  apply clarsimp
  done

lemma refines_rel_prod_eq_assume_on_exit:
  assumes f: "refines f\<^sub>c f\<^sub>a s s (rel_prod Q (=))"
  shows "refines
        (assume_on_exit f\<^sub>c grd cleanup)
        (assume_on_exit f\<^sub>a grd cleanup) s s
        (rel_prod Q (=))"
  unfolding assume_on_exit_bind_exception_or_result_conv
  apply (rule refines_bind_exception_or_result_strong [OF f])
  apply clarsimp
  apply (rule refines_bind_no_throw [where Q="rel_prod \<top> (=)"] )
     apply simp
    apply simp
  subgoal
    by (auto simp add: refines_def_old)
  apply (rule refines_bind_no_throw )
     apply simp
  apply simp
    apply (clarsimp)
   apply (rule refines_state_select_same)
  apply clarsimp
  done

context stack_heap_state
begin

thm refines_rel_prod_with_fresh_stack_ptr
lemma refines_rel_prod_L2_try_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (L2_try (f\<^sub>c p)) (f\<^sub>a p) s s (rel_prod Q (=))"
  shows 
    "refines 
       (L2_try (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))) 
       (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s 
       (rel_prod Q (=))"
  apply (simp add: L2_try_with_fresh_stack_ptr L2_VARS_def)
  apply (rule refines_rel_prod_with_fresh_stack_ptr [unfolded L2_VARS_def])
   apply (rule init_eq)
  apply (rule f)
  done
end

context typ_heap_typing
begin

lemma refines_rel_prod_guard_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (guard_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
       (guard_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: guard_with_fresh_stack_ptr_def L2_VARS_def assume_stack_alloc_def)
  apply (rule refines_bind')
  apply (subst refines_assume_result_and_state_iff)
  apply (subst init_eq)
  apply (intro sim_set_refl)
  apply clarsimp
  apply (rule refines_on_exit')
  apply (rule refines_weaken[OF f])
  apply simp
  apply (rule refines_bind'[OF refines_guard])
  apply simp_all
  apply (rule refines_assert_result_and_state)
  apply auto
  done

lemma refines_rel_prod_assume_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (assume_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
       (assume_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: assume_with_fresh_stack_ptr_def L2_VARS_def assume_stack_alloc_def)
  apply (rule refines_bind')
  apply (subst refines_assume_result_and_state_iff)
  apply (subst init_eq)
  apply (intro sim_set_refl)
  apply clarsimp
  apply (rule refines_on_exit')
  apply (rule refines_weaken[OF f])
  apply simp
  apply (rule refines_bind'[OF refines_assuming])
  apply simp_all
  apply (rule refines_assert_result_and_state)
  apply auto
  done

lemma refines_rel_prod_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (f\<^sub>c p) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))
       (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: with_fresh_stack_ptr_def L2_VARS_def assume_stack_alloc_def)
  apply (rule refines_bind_no_throw )
     apply simp
    apply simp
   apply (rule refines_assume_result_and_state_same')
   apply (simp only: init_eq)
  apply clarsimp
  apply (rule refines_rel_prod_eq_on_exit)
  apply (rule f)
  done


lemma refines_rel_prod_L2_try_guard_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (L2_try (f\<^sub>c p)) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (L2_try (guard_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm)))
       (guard_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: L2_try_guard_with_fresh_stack_ptr L2_VARS_def)
  apply (rule refines_rel_prod_guard_with_fresh_stack_ptr [unfolded L2_VARS_def])
   apply (rule init_eq)
  apply (rule f)
  done

lemma refines_rel_prod_L2_try_assume_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (L2_try (f\<^sub>c p)) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (L2_try (assume_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm)))
       (assume_with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: L2_try_assume_with_fresh_stack_ptr L2_VARS_def)
  apply (rule refines_rel_prod_assume_with_fresh_stack_ptr [unfolded L2_VARS_def])
   apply (rule init_eq)
  apply (rule f)
  done

lemma refines_rel_prod_L2_try_with_fresh_stack_ptr:
  assumes init_eq: "init\<^sub>c s = init\<^sub>a s"
  assumes f: "\<And>s p. refines (L2_try (f\<^sub>c p)) (f\<^sub>a p) s s (rel_prod L (=))"
  shows
    "refines
       (L2_try (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm)))
       (with_fresh_stack_ptr n init\<^sub>a (L2_VARS f\<^sub>a nm)) s s
       (rel_prod L (=))"
  apply (simp add: L2_try_with_fresh_stack_ptr L2_VARS_def)
  apply (rule refines_rel_prod_with_fresh_stack_ptr [unfolded L2_VARS_def])
   apply (rule init_eq)
  apply (rule f)
  done

end

(* c is the synthesize var, so a is concrete and we have to ensure to derive "r a b" first *)

lemma relcomppI_swapped: "s b c \<Longrightarrow> r a b \<Longrightarrow> (r OO s) a c"
  by (rule relcomppI)

lemmas refines_monad_nondet =
  refines_L2_call_embed_nondet [synthesize_rule nondet and exit priority:210]
  refines_L2_call_embed_exn [synthesize_rule nondet and exit priority:210]

  refines_liftE_exn [synthesize_rule nondet and exit priority:250]
  refines_L2_seq_nondet [synthesize_rule nondet and exit priority:210 split: g and g']
  refines_L2_seq_exn [synthesize_rule nondet and exit priority:210 split: g and g']

  refines_L2_try_L2_seq_nondet [synthesize_rule nondet and exit priority:230 split: g and g']
  refines_L2_try_L2_condition_nondet [synthesize_rule nondet and exit priority:230]
  refines_L2_try_rel_LiftE_nondet [synthesize_rule nondet and exit priority:220]
  refines_L2_try_finally_nondet [synthesize_rule nondet and exit priority:210]
  refines_L2_try_exn [synthesize_rule nondet and exit priority:210]

  refines_L2_condition_nondet [synthesize_rule nondet and exit priority:210]
  refines_L2_while_nondet [synthesize_rule nondet and exit priority:210 split: b and b']
  refines_L2_while_exn [synthesize_rule nondet and exit priority:210 split: b and b']

  refines_L2_unknown_nondet [synthesize_rule nondet and exit priority:210]
  refines_L2_unknown_exn [synthesize_rule nondet and exit priority:210]

  refines_L2_modify_nondet [synthesize_rule nondet and exit priority:210]

  refines_L2_gets_nondet [synthesize_rule nondet and exit priority:210]

  refines_L2_throw_exn [synthesize_rule nondet and exit priority:210]

  refines_L2_spec_nondet [synthesize_rule nondet and exit priority:210]

  refines_L2_assume_nondet [synthesize_rule nondet and exit priority:210]

  refines_L2_guard_nondet [synthesize_rule nondet and exit priority:210]

  refines_L2_guarded_nondet [synthesize_rule nondet and exit priority:210]
  refines_L2_guarded_exn [synthesize_rule nondet and exit priority:210]

  refines_L2_fail_nondet [synthesize_rule nondet and exit priority:210]

  refines_exec_concrete_nondet [synthesize_rule nondet and exit priority:210]
  refines_exec_concrete_exit [synthesize_rule nondet and exit priority:210]

  refines_exec_abstract_nondet [synthesize_rule nondet and exit priority:210]
  refines_exec_abstract_exit [synthesize_rule nondet and exit priority:210]

  rel_liftE_trivial [synthesize_rule nondet and exit priority:210]
  rel_liftE'_Inr [synthesize_rule nondet and exit priority:210]
  rel_sum_Inl [synthesize_rule nondet and exit priority:210]
  rel_sum_Inr [synthesize_rule nondet and exit priority:210]
  rel_xval_Exn [synthesize_rule nondet and exit priority:210]
  rel_xval_Result [synthesize_rule nondet and exit priority:210]

  relcomppI_swapped [synthesize_rule nondet and exit priority:210]
  rel_map_ResultI [synthesize_rule nondet and exit priority:210]
  rel_map_to_xval_InlI [synthesize_rule nondet and exit priority:210]
  rel_map_to_xval_InrI [synthesize_rule nondet and exit priority:210]

  refl [synthesize_rule nondet and exit priority: 210]

context typ_heap_typing
begin
lemmas refines_monad_nondet =
  refines_rel_prod_L2_try_guard_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:232]
  refines_rel_prod_L2_try_assume_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:232]
  refines_rel_prod_L2_try_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:232]
  refines_rel_prod_guard_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
  refines_rel_prod_assume_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
  refines_rel_prod_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
  refines_rel_xval_guard_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
  refines_rel_xval_assume_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
  refines_rel_xval_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
end

context stack_heap_state
begin
lemmas refines_nondet_monad =
  refines_rel_prod_L2_try_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:232]
  refines_rel_prod_with_fresh_stack_ptr [synthesize_rule nondet and exit priority:210]
end

add_synthesize_pattern nondet and exit where
  rel_throwE_nondet_synth = \<open>Trueprop (rel_throwE _ ?x ?x')\<close> (x')


subsection \<open>Elimination of \<open>L2_try\<close> in the Error Monad\<close>

subsubsection \<open>Eliminate Inner Exception\<close>

text \<open>rules for elimination of \<open>L2_try\<close> when the inner exception layer is not needed, i.e.,
  \<open>rel_sum (rel_throwE L) (=)\<close>\<close>

lemma bind_bind_exception_or_result_conv: 
  "(f \<bind> g) = (bind_exception_or_result f (\<lambda>Exception e \<Rightarrow> yield (Exception e) | Result v \<Rightarrow> g v))"
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old split: exception_or_result_splits)
  done

lemma rel_throwE'_rel_throwE_conv: "rel_throwE' L = (rel_map to_xval OO rel_throwE L)"
  apply (rule ext)+
  apply (auto simp add: rel_throwE_def rel_throwE'_def rel_xval.simps relcompp.simps 
      rel_map_def to_xval_def split: sum.splits)
  done

lemma "rel_throwE (rel_throwE' L) = (rel_throwE (rel_map to_xval OO rel_throwE L))"
  apply (rule ext)+
  apply (auto simp add: rel_throwE_def rel_throwE'_def rel_xval.simps relcompp.simps 
      rel_map_def to_xval_def split: sum.splits)
  done

lemma refines_L2_try_L2_seq_exn:
  fixes f::" (('b + 'c), 'f, 'a) exn_monad"
    and g::"'f \<Rightarrow> ( ('b + 'c), 'c, 'a) exn_monad"
  assumes g [unfolded THIN_def L2_defs, rule_format]:
    "PROP THIN (\<And>v t. refines (L2_try (g v)) (g' v) t t (rel_prod ((rel_xval L R)) (=)))"
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_xval (rel_throwE' L) (=)) (=))))"
  shows "refines (L2_try (L2_seq f g)) (bind f' g') s s (rel_prod (rel_xval L R) (=))"
  unfolding L2_try_def L2_seq_def try_nested_bind_exception_or_result_conv
  apply (simp add: bind_bind_exception_or_result_conv)
  apply (rule refines_bind_exception_or_result)
  apply (rule refines_weaken [OF f])
  apply (auto split: xval_splits sum.splits simp: rel_xval.simps rel_prod.simps g)
  done

lemma refines_L2_try_L2_condition_exit:
  assumes f [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try f) f' s s (rel_prod R (=))))"
  assumes g [unfolded THIN_def]: "PROP THIN (Trueprop (refines (L2_try g) g' s s (rel_prod R (=))))"
  shows "refines (L2_try (L2_condition c f g)) (condition c f' g') s s (rel_prod R (=))"
  using f g unfolding L2_defs L2_try_def
  apply (auto simp add: refines_def_old succeeds_condition_iff reaches_condition_iff reaches_try)
  done

lemma refines_try_rel_xval_rel_throwE':
  assumes "refines f f' s s (rel_prod (rel_xval (rel_throwE' A) B) S)"
  shows "refines (try f) f' s s (rel_prod (rel_xval A B) S)"
  unfolding try_def refines_map_value_left_iff
  apply (rule refines_weaken [OF assms])
  apply (auto simp add: unnest_exn_def rel_xval.simps split: xval_splits sum.splits )
  done

lemma refines_L2_try_rel_sum_rel_throwE_nondet:
  assumes "refines f f' s s (rel_prod (rel_xval (rel_throwE' A) B)  (=))"
  shows "refines (L2_try f) f' s s (rel_prod (rel_xval A B) (=))"
  using assms unfolding L2_defs
  by (rule refines_try_rel_xval_rel_throwE')

lemma refines_try_rel_throwE:
  assumes "refines f f' s s (rel_prod (rel_throwE (rel_throwE' L)) S)"
  shows "refines (try f) f' s s (rel_prod (rel_throwE L) S)"
  unfolding try_def
  apply (simp add: refines_map_value_left_iff)
  apply (rule refines_weaken [OF assms])
  apply (auto simp add: unnest_exn_def split: xval_splits sum.splits)
  done

lemma refines_L2_try_rel_throwE_nondet:
  assumes "refines f f' s s (rel_prod (rel_throwE (rel_throwE' L)) (=))"
  shows "refines (L2_try f) f' s s (rel_prod (rel_throwE L) (=))"
  using assms unfolding L2_defs
  by (rule refines_try_rel_throwE)

lemmas ts_L2_try_inner_exception =
  rel_throwE'_Inl[synthesize_rule nondet and exit]
  rel_throwE_Exn[synthesize_rule nondet and exit]
  refines_L2_try_L2_seq_exn        [synthesize_rule nondet and exit priority: 218 split: g and g']
  refines_L2_try_L2_condition_exit [synthesize_rule nondet and exit priority: 218]
  refines_L2_try_rel_throwE_nondet [synthesize_rule nondet and exit priority: 216]
  refines_L2_try_rel_sum_rel_throwE_nondet [synthesize_rule nondet and exit priority: 215]
bundle del_ts_L2_try_inner_exception =
  rel_throwE'_Inl[synthesize_rule nondet and exit del]
  rel_throwE_Exn[synthesize_rule nondet and exit del]
  refines_L2_try_L2_seq_exn        [synthesize_rule nondet and exit priority: 218 split: g and g' del]
  refines_L2_try_L2_condition_exit [synthesize_rule nondet and exit priority: 218 del]
  refines_L2_try_rel_throwE_nondet [synthesize_rule nondet and exit priority: 216 del]
  refines_L2_try_rel_sum_rel_throwE_nondet [synthesize_rule nondet and exit priority: 215 del]

print_synthesize_rules exit \<open>Trueprop (refines (L2_seq _ _) _ _ _ (rel_prod rel_liftE (=))) \<close>

subsubsection \<open>Eliminate \<open>L2_try\<close> over exiting branches\<close>

text \<open>
  Eliminate \<open>L2_try\<close> over a condition, when one branch always exits (\<open>rel_throwE (rel_sum L R)\<close>)
\<close>

lemma rel_map_to_xval_rel_xval_rel_sum_conv: 
  "rel_map to_xval OO rel_xval L R = rel_sum L R OO rel_map to_xval"
  apply (rule ext)+
  apply (auto simp add: rel_sum.simps rel_xval.simps relcompp.simps 
      rel_map_def to_xval_def split: sum.splits)
  done

lemma refines_L2_try_L2_seq_L2_condition_exit1:
  assumes g [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines (L2_try (L2_seq g h)) gh' s s (rel_prod LR (=))))"
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_throwE (rel_map to_xval OO LR)) (=))))"
  shows "refines (L2_try (L2_seq (L2_condition c f g) h)) (condition c f' gh') s s (rel_prod LR (=))"
  using g f
  apply (simp add: L2_defs try_def refines_map_value_left_iff refines_condition_bind_left
      refines_condition_false)
  apply (intro impI refines_condition_true)
  apply assumption
  subgoal premises prems
  proof -
    have "refines (f >>= h) (f' \<bind> return) s s (\<lambda>(x, s) (y, t). LR (unnest_exn x) y \<and> s = t)"
      apply (intro refines_bind[OF prems(2)])
      apply (auto simp: rel_throwE_def rel_map_def unnest_exn_def
                  split: xval_splits sum.splits)
      done
    then show ?thesis by simp
  qed
  done

lemma refines_L2_try_L2_seq_L2_condition_exit2:
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines (L2_try (L2_seq f h)) fh' s s (rel_prod LR (=))))"
  assumes g [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines g g' s s (rel_prod (rel_throwE (rel_map to_xval OO LR))  (=))))"
  shows "refines (L2_try (L2_seq (L2_condition c f g) h)) (condition c fh' g') s s (rel_prod LR (=))"
  using assms
  unfolding L2_defs
  apply (subst (1 2) condition_swap)
  apply  (erule (1) refines_L2_try_L2_seq_L2_condition_exit1[unfolded L2_defs])
  done

lemma refines_L2_seq_L2_condition_rel_throwE1:
  assumes g [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines (L2_seq g h) gh' s s (rel_prod (rel_throwE LR)(=))))"
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_throwE LR) (=))))"
  shows "refines (L2_seq (L2_condition c f g) h) (condition c f' gh') s s (rel_prod (rel_throwE LR) (=))"
proof cases
  assume "c s"
  from this f
  show ?thesis
    unfolding L2_defs
    by (auto simp add: refines_def_old reaches_condition_iff succeeds_condition_iff succeeds_bind reaches_bind rel_throwE_def 
        default_option_def Exn_def 
        split: xval_splits exception_or_result_splits)
      (metis default_option_def the_Exception_simp exception_or_result_cases option.exhaust_sel)+
next
  assume "\<not>c s"
  then have *: 
    "run ((condition c f g) >>= h) s = run (g >>= h) s"
    "run (condition c f' gh') s = run gh' s"
    by (auto simp add: run_condition run_bind)
 
  from g show ?thesis
    unfolding refines_def_old succeeds_def reaches_def 
       L2_defs *  .
qed



lemma refines_L2_seq_L2_condition_rel_throwE2:
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines (L2_seq f h) fh' s s (rel_prod (rel_throwE LR) (=))))"
  assumes g [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines g g' s s (rel_prod (rel_throwE LR) (=))))"
  shows "refines (L2_seq (L2_condition c f g) h) (condition c fh' g') s s (rel_prod (rel_throwE LR) (=))"
  using assms
  unfolding L2_defs
  by (subst (1 2) condition_swap)
    (erule (1) refines_L2_seq_L2_condition_rel_throwE1[unfolded L2_defs])

lemma refines_bind_rel_throwE_first:
  assumes f: "refines f f' s s (rel_prod (rel_throwE LR) S)"
  shows "refines (f >>= g) f' s s (rel_prod (rel_throwE LR) S)"
  using f unfolding L2_defs
  by (auto simp add: refines_def_old  succeeds_bind reaches_bind rel_throwE_def 
      default_option_def Exn_def 
      split: xval_splits exception_or_result_splits)
    (metis default_option_def the_Exception_simp exception_or_result_cases option.exhaust_sel)+

lemma refines_L2_seq_rel_throwE_throwE:
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_throwE LR) (=))))"
  shows "refines (L2_seq f g) f' s s (rel_prod (rel_throwE LR)  (=))"
  unfolding L2_defs using f
  by (rule refines_bind_rel_throwE_first)

lemma refines_L2_seq_rel_throwE_throwE1:
  assumes g[unfolded THIN_def, rule_format] :
    "PROP THIN (\<And>v t. refines (g v) (g' v) t t (rel_prod (rel_throwE (rel_map to_xval OO rel_xval L R))  (=)))"
  assumes f [unfolded THIN_def, rule_format]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod (rel_xval (rel_throwE' L) (=)) (=))))"
  shows "refines (L2_seq f g) (bind f' g') s s (rel_prod (rel_throwE (rel_map to_xval OO rel_xval L R)) (=))"
  unfolding L2_defs
  apply (rule refines_bind_bind_exn [OF f])
  apply (auto simp: g rel_throwE'_iff)
  done

lemma refines_L2_seq_rel_throwE_liftE:
  assumes g [unfolded THIN_def, rule_format]:
    "PROP THIN (\<And>v t. refines (g v) (g' v) t t (rel_prod (rel_throwE LR) (=)))"
  assumes f [unfolded THIN_def]:
    "PROP THIN (Trueprop (refines f f' s s (rel_prod rel_liftE (=))))"
  shows "refines (L2_seq f g) (bind f' g') s s (rel_prod (rel_throwE LR) (=))"
  using g f unfolding L2_defs
  apply (clarsimp simp add: refines_def_old succeeds_bind reaches_bind reaches_try succeeds_condition_iff reaches_condition_iff
           rel_throwE_def rel_throwE'_def relcompp.simps rel_liftE_def rel_xval.simps
           split: xval_splits sum.splits, safe ) 
    apply (metis the_Result_simp )
   apply (smt (verit) case_exception_or_result_Result case_xval_simps(1))
  by (metis (no_types, lifting) case_exception_or_result_Result case_xval_simps(2))

lemma refines_L2_throw_rel_throwE_Inl:
  assumes "L l l'"
  shows "refines (L2_throw (Inl l) ns) (throw (L2_VARS l' ns)) s s (rel_prod (rel_throwE  (rel_map to_xval OO rel_xval L R)) (=))"
  using assms unfolding L2_defs L2_VARS_def
  by (auto simp add: refines_def_old rel_throwE_def rel_xval.simps relcompp.simps rel_map_def to_xval_def Exn_def
      split: sum.splits)

lemma refines_L2_throw_rel_throwE_Inr:
  assumes "R r r'"
  shows "refines (L2_throw (Inr r) ns) (return (L2_VARS r' ns)) s s (rel_prod (rel_throwE ((rel_map to_xval OO rel_xval L R))) (=))"
  using assms unfolding L2_defs L2_VARS_def
  by (auto simp add: refines_def_old rel_throwE_def rel_xval.simps relcompp.simps rel_map_def to_xval_def Exn_def
      split: sum.splits)

lemma refines_L2_throw_rel_throwE:
  assumes "R r (Result r')"
  shows "refines (L2_throw r ns) (L2_VARS (return r') ns) s s (rel_prod (rel_throwE R) (=))"
  using assms unfolding L2_defs L2_VARS_def
  by (auto simp add: refines_def_old rel_throwE_def rel_sum.simps relcompp.simps rel_map_def to_xval_def Exn_def
      split: sum.splits)

lemmas ts_L2_try_condition_exit =
  (* splitting off no-return *)
  refines_L2_try_L2_seq_L2_condition_exit1[synthesize_rule nondet and exit priority:217]
  refines_L2_try_L2_seq_L2_condition_exit2[synthesize_rule nondet and exit priority:217]
  (* solving no-return*)
  refines_L2_seq_L2_condition_rel_throwE1[synthesize_rule nondet and exit priority:216]
  \<comment> \<open>Note that 
   1. this together with @{thm refines_L2_try_rel_throwE_nondet} does not replace
   2. @{thm refines_L2_try_L2_seq_L2_condition_exit1} and vice versa. 1 is more compositional
   and also works deeply nested but only handles the case \<^const>\<open>rel_throwE\<close>, whereas 2
   also handles \<^const>\<open>rel_liftE\<close> and \<^const>\<open>rel_sum\<close> by pushing down \<^const>\<open>L2_try\<close> into the
   branch of the conditional.\<close> 
  refines_L2_seq_L2_condition_rel_throwE2[synthesize_rule nondet and exit priority:216]
  refines_L2_seq_rel_throwE_throwE [synthesize_rule nondet and exit priority:213]
  refines_L2_seq_rel_throwE_throwE1[synthesize_rule nondet and exit priority:212 split: g and g']
  refines_L2_seq_rel_throwE_liftE  [synthesize_rule nondet and exit priority:212 split: g and g']
  refines_L2_throw_rel_throwE_Inl  [synthesize_rule nondet and exit priority:212]
  refines_L2_throw_rel_throwE_Inr  [synthesize_rule nondet and exit priority:212]
  refines_L2_throw_rel_throwE      [synthesize_rule nondet and exit priority:212]
bundle del_ts_L2_try_condition_exit =
  refines_L2_try_L2_seq_L2_condition_exit1[synthesize_rule nondet and exit priority:217 del]
  refines_L2_try_L2_seq_L2_condition_exit2[synthesize_rule nondet and exit priority:217 del]
  refines_L2_seq_L2_condition_rel_throwE1[synthesize_rule nondet and exit priority:216 del]
  refines_L2_seq_L2_condition_rel_throwE2[synthesize_rule nondet and exit priority:216 del]
  refines_L2_seq_rel_throwE_throwE [synthesize_rule nondet and exit priority:213 del]
  refines_L2_seq_rel_throwE_throwE1[synthesize_rule nondet and exit priority:212 split: g and g' del]
  refines_L2_seq_rel_throwE_liftE  [synthesize_rule nondet and exit priority:212 split: g and g' del]
  refines_L2_throw_rel_throwE_Inl  [synthesize_rule nondet and exit priority:212 del]
  refines_L2_throw_rel_throwE_Inr  [synthesize_rule nondet and exit priority:212 del]
  refines_L2_throw_rel_throwE      [synthesize_rule nondet and exit priority:212 del]

section \<open>Error Monad (exit)\<close>

lemma refines_L2_call_embed_exit:
  assumes f: "refines f f' s s (rel_prod (rel_xval rel_Nonlocal (=))  (=))"
  assumes emb: "\<And>e'. L (emb (Nonlocal e')) (emb' e')"
  shows "refines (L2_call f emb ns) (L2_VARS (map_value (map_exn emb') f') ns) s s (rel_prod (rel_xval L (=)) (=))"
  unfolding L2_defs L2_VARS_def L2_call_def
  apply (rule refines_map_value [OF f] )
  using emb  
  by (auto simp add: rel_xval.simps  map_exn_def rel_Nonlocal_conv)


lemma refines_L2_call_embed_exit_in_out:
  assumes emb: "\<And>e'. L (emb e') (emb' e')"
  assumes f: "refines f f' s s (rel_prod (rel_xval (=) (=)) (=))"
  shows "refines (L2_call f emb ns) (L2_VARS (map_value (map_exn emb') f') ns) s s (rel_prod (rel_xval L (=)) (=))"
  unfolding L2_defs L2_VARS_def L2_call_def
  apply (rule refines_map_value [OF f] )
  using emb  
  by (auto simp add: rel_xval.simps  map_exn_def rel_Nonlocal_conv)

lemma refines_L2_catch_exit:
  assumes f: "refines f f' s s (rel_prod (rel_xval (=) R) (=))"
  assumes h: "\<And>s' v. refines (h v) (h' v) s' s' (rel_prod (rel_xval L R) (=))"
  shows "refines (L2_catch f h) (catch f' h') s s (rel_prod (rel_xval L R) (=))"
  unfolding L2_catch_def
  using f h
  apply (auto intro!: refines_catch)
  done

lemma rel_xval_eq_refl: "rel_xval (=) (=) x x"
  by (auto simp add: rel_xval_eq)

lemmas refines_monad_exit =
  refines_L2_call_embed_exit [synthesize_rule exit priority:110]
  refines_L2_call_embed_exit_in_out [synthesize_rule exit priority:109 split: emb and emb']
  refines_L2_catch_exit [synthesize_rule exit priority:110 split: h and h']
  rel_Nonlocal_Nonlocal [synthesize_rule exit priority:110]
  rel_sum_eq [synthesize_rule exit priority:210]
  rel_xval_eq_refl [synthesize_rule exit priority:210]

print_synthesize_rules exit

end

