(*<*)
theory Results
imports Examples
begin
(*>*)

section \<open>Collected Results from the ICDT'22 Paper\<close>

global_interpretation icdt22: simplification "\<lambda>x. x" "\<lambda>x. True"
  by standard auto

lemma cov_eval_fin:
  assumes "cov x (Q :: ('a :: {infinite, linorder}, 'b :: linorder) fmla) G" "x \<in> fv Q"
    "finite (adom I)" "\<And>\<sigma>. \<not> sat (Q \<^bold>\<bottom> x) I \<sigma>"
  shows "eval Q I = eval (Disj (Conj Q (DISJ (qps G))) (DISJ ((\<lambda>y. Conj (cp (Q[x \<^bold>\<rightarrow> y])) (x \<approx> y)) ` eqs x G))) I"
  using assms
  by (intro trans[OF icdt22.cov_eval_fin[OF assms]])
    (auto 0 3 simp: eval_def fv_subst intro!: arg_cong[of _ _ "\<lambda>X. eval_on X _ _"]
    dest!: fv_DISJ[THEN set_mp, rotated 1] fv_cp[THEN set_mp]
    dest: cov_fv[OF _ _ qps_in] cov_fv[OF _ _ eqs_in])

text \<open>Remapping the formalization statements to the lemma's from the paper:\<close>

lemmas icdt22_lemma_1 = gen_fv gen_sat gen_cp_erase
lemmas icdt22_definition_2 = sub.simps nongens_def rrb_def sr_def
lemmas icdt22_lemma_3 = ex_cov cov_sat_erase
lemmas icdt22_lemma_4 = cov_fv cov_equiv[OF _ refl]
lemmas icdt22_lemma_5 = icdt22.cov_Exists_equiv
lemmas icdt22_example_6 = ex_rb_Q_susp_user[unfolded
  Q_susp_user_def Q_susp_user_rb_def]
lemmas icdt22_lemma_7 = cov_eval_fin cov_eval_inf
lemmas icdt22_lemma_8 = inres_SPEC[OF _ icdt22.rb_correct[unfolded icdt22.rb_spec_def, simplified], of Q Q' for Q Q']
lemmas icdt22_lemma_9 = inres_SPEC[OF _ icdt22.split_correct[unfolded icdt22.split_spec_def FV_def EVAL_def, simplified],
  of Q "(Qfin, Qinf)" for Q Qfin Qinf, simplified]
lemmas icdt22_example_10 = ex_split_Q_disj[unfolded
  Q_disj_def Q_disj_split_fin_def Q_disj_split_inf_def]
lemmas icdt22_example_11 = ex_split_Q_eq[unfolded
  Q_eq_def Q_eq_split_fin_def Q_eq_split_inf_def]
lemmas icdt22_example_12 = ex_split_Q_susp_user[unfolded
  Q_susp_user_def Q_susp_user_split_fin_def Q_susp_user_split_inf_def]


text \<open>Additionally, here are the correctness statements for the algorithm variants with
  intermediate constant propagation (which are used in the examples):\<close>

lemmas icdt22_lemma_8' = inres_SPEC[OF _ extra_cp.RB_correct[unfolded extra_cp.rb_spec_def], simplified, of Q Q' for Q Q']
lemmas icdt22_lemma_9' = inres_SPEC[OF _ extra_cp.SPLIT_correct[unfolded extra_cp.split_spec_def FV_def EVAL_def, simplified],
  of Q "(Qfin, Qinf)" for Q Qfin Qinf, simplified]

text \<open>Now, we summarize the formally verified results from
our ICDT'22 paper~\<^cite>\<open>"DBLP:conf/icdt/RaszykBKT22"\<close>:
\begin{description}
\item[@{thm [source] icdt22_lemma_1}:] @{thm icdt22_lemma_1[no_vars]}
\item[@{thm [source] icdt22_definition_2}:] @{thm icdt22_definition_2[no_vars]}
\item[@{thm [source] icdt22_lemma_3}:] @{thm icdt22_lemma_3[no_vars]}
\item[@{thm [source] icdt22_lemma_4}:] @{thm icdt22_lemma_4[no_vars]}
\item[@{thm [source] icdt22_lemma_5}:] @{thm icdt22_lemma_5[no_vars]}
\item[@{thm [source] icdt22_example_6}:] @{thm icdt22_example_6[no_vars]}
\item[@{thm [source] icdt22_lemma_7}:] @{thm icdt22_lemma_7[no_vars]}
\item[@{thm [source] icdt22_lemma_8}:] @{thm icdt22_lemma_8[no_vars]}
\item[@{thm [source] icdt22_lemma_9}:] @{thm icdt22_lemma_9[no_vars]}
\item[@{thm [source] icdt22_lemma_8'}:] @{thm icdt22_lemma_8'[no_vars]}
\item[@{thm [source] icdt22_lemma_9'}:] @{thm icdt22_lemma_9'[no_vars]}
\item[@{thm [source] icdt22_example_10}:] @{thm icdt22_example_10[no_vars]}
\item[@{thm [source] icdt22_example_11}:] @{thm icdt22_example_11[no_vars]}
\item[@{thm [source] icdt22_example_12}:] @{thm icdt22_example_12[no_vars]}
\end{description}
\<close>

(*<*)
end
(*>*)