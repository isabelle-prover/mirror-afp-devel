(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Unfolding Optimisation\<close>

theory LTL_Rabin_Unfold_Opt
  imports Main LTL_Rabin
begin

subsection \<open>Transition Functions\<close>

subsubsection \<open>Unfolding\<close>

fun Unf :: "'a ltl \<Rightarrow> 'a ltl"
where
  "Unf (F \<phi>) = F \<phi> or Unf \<phi>"
| "Unf (G \<phi>) = G \<phi> and Unf \<phi>" 
| "Unf (\<phi> U \<psi>) = (\<phi> U \<psi> and Unf \<phi>) or Unf \<psi>"
| "Unf (\<phi> and \<psi>) = Unf \<phi> and Unf \<psi>"
| "Unf (\<phi> or \<psi>) = Unf \<phi> or Unf \<psi>"
| "Unf \<phi> = \<phi>"

fun Unf\<^sub>G :: "'a ltl \<Rightarrow> 'a ltl"
where
  "Unf\<^sub>G (F \<phi>) = F \<phi> or Unf\<^sub>G \<phi>"
| "Unf\<^sub>G (G \<phi>) = G \<phi>" 
| "Unf\<^sub>G (\<phi> U \<psi>) = (\<phi> U \<psi> and Unf\<^sub>G \<phi>) or Unf\<^sub>G \<psi>"
| "Unf\<^sub>G (\<phi> and \<psi>) = Unf\<^sub>G \<phi> and Unf\<^sub>G \<psi>"
| "Unf\<^sub>G (\<phi> or \<psi>) = Unf\<^sub>G \<phi> or Unf\<^sub>G \<psi>"
| "Unf\<^sub>G \<phi> = \<phi>"

subsubsection \<open>Step\<close>

fun step :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "step p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "step (np(a)) \<nu> = (if a \<notin> \<nu> then true else false)"
| "step (X \<phi>) \<nu> = \<phi>"
| "step (\<phi> and \<psi>) \<nu> = step \<phi> \<nu> and step \<psi> \<nu>"
| "step (\<phi> or \<psi>) \<nu> = step \<phi> \<nu> or step \<psi> \<nu>"
| "step \<phi> \<nu> = \<phi>"

fun af_letter_opt
where
  "af_letter_opt \<phi> \<nu> = Unf (step \<phi> \<nu>)"

fun af_G_letter_opt
where
  "af_G_letter_opt \<phi> \<nu> = Unf\<^sub>G (step \<phi> \<nu>)"

subsubsection \<open>Combinations\<close>

abbreviation af_opt :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af\<^sub>\<UU>")
where
  "af\<^sub>\<UU> \<phi> w \<equiv> (foldl af_letter_opt \<phi> w)"

abbreviation af_G_opt :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af\<^sub>G\<^sub>\<UU>")
where
  "af\<^sub>G\<^sub>\<UU> \<phi> w \<equiv> (foldl af_G_letter_opt \<phi> w)"

lemma af_letter_alt_def:
  "af_letter \<phi> \<nu> = step (Unf \<phi>) \<nu>"
  "af_G_letter \<phi> \<nu> = step (Unf\<^sub>G \<phi>) \<nu>"
  by (induction \<phi>) simp_all

lemma af_to_af_opt:
  "Unf (af \<phi> w) = af\<^sub>\<UU> (Unf \<phi>) w"
  "Unf\<^sub>G (af\<^sub>G \<phi> w) = af\<^sub>G\<^sub>\<UU> (Unf\<^sub>G \<phi>) w"
  by (induction w arbitrary: \<phi>)
     (simp_all add: af_letter_alt_def)

lemma decomposable_function_subst:
  assumes "f true = true"
      and "f false = false"
      and "(\<And>\<phi> \<psi>. f (\<phi> and \<psi>) = f \<phi> and f \<psi>)"
      and "(\<And>\<phi> \<psi>. f (\<phi> or \<psi>) = f \<phi> or f \<psi>)"
  shows "f \<phi> = subst \<phi> (\<lambda>\<chi>. Some (f \<chi>))"
  using assms by (induction \<phi>) simp_all

lemma af_opt_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter_opt \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter_opt \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter_opt \<phi> \<nu> \<equiv>\<^sub>P af_letter_opt \<psi> \<nu>"
  using decomposable_function_subst[of "\<lambda>\<chi>. af_letter_opt \<chi> \<nu>", simplified] 
  using subst_respects_ltl_prop_entailment af_letter_opt.simps by metis+

lemma af_G_opt_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter_opt \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter_opt \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter_opt \<phi> \<nu> \<equiv>\<^sub>P af_G_letter_opt \<psi> \<nu>"
  using decomposable_function_subst[of "\<lambda>\<chi>. af_G_letter_opt \<chi> \<nu>", simplified] 
  using subst_respects_ltl_prop_entailment af_G_letter_opt.simps by metis+

lemma step_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> step \<phi> \<nu> \<longrightarrow>\<^sub>P step \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> step \<phi> \<nu> \<equiv>\<^sub>P step \<psi> \<nu>"
  using decomposable_function_subst[of "\<lambda>\<chi>. step \<chi> \<nu>", simplified] 
  using subst_respects_ltl_prop_entailment by metis+

lemma Unf\<^sub>G_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> Unf\<^sub>G \<phi> \<longrightarrow>\<^sub>P Unf\<^sub>G \<psi>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> Unf\<^sub>G \<phi> \<equiv>\<^sub>P Unf\<^sub>G \<psi>"
  using decomposable_function_subst[of Unf\<^sub>G, simplified] 
  using subst_respects_ltl_prop_entailment by metis+

lemma step_nested_propos:
  "nested_propos (step \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

lemma Unf_nested_propos:
  "nested_propos (Unf \<phi>) \<subseteq> nested_propos \<phi>"
  "nested_propos (Unf\<^sub>G \<phi>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

lemma af_opt_nested_propos:
  "nested_propos (af_letter_opt \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  "nested_propos (af_G_letter_opt \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  using step_nested_propos Unf_nested_propos by force+

lemma af_equiv:
  "af \<phi> (w @ [\<nu>]) = step (af\<^sub>\<UU> (Unf \<phi>) w) \<nu>"
  using af_to_af_opt(1) by (metis af_letter_alt_def(1) foldl_Cons foldl_Nil foldl_append)

lemma af_equiv':
  "af \<phi> (w [0 \<rightarrow> Suc i]) = step (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i])) (w i)"
  using af_equiv by auto

text \<open>Lift transformer and bind to a new name\<close>

interpretation af_abs_opt: lift_ltl_transformer af_letter_opt
  using lift_ltl_transformer_def af_opt_respectfulness af_opt_nested_propos by blast

definition af_letter_abs_opt ("\<up>af\<^sub>\<UU>")
where
  "\<up>af\<^sub>\<UU> \<equiv> af_abs_opt.f_abs"

interpretation af_G_abs_opt: lift_ltl_transformer af_G_letter_opt
  using lift_ltl_transformer_def af_G_opt_respectfulness af_opt_nested_propos by blast

definition af_G_letter_abs_opt ("\<up>af\<^sub>G\<^sub>\<UU>")
where
  "\<up>af\<^sub>G\<^sub>\<UU> \<equiv> af_G_abs_opt.f_abs"

interpretation step_abs: lift_ltl_transformer step
  using lift_ltl_transformer_def step_respectfulness step_nested_propos by blast

definition step_abs ("\<up>step")
where
  "\<up>step \<equiv> step_abs.f_abs"

lift_definition Unf\<^sub>G_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P" ("\<up>Unf\<^sub>G") is Unf\<^sub>G
  by (insert Unf\<^sub>G_respectfulness)

lemma af_G_letter_abs_opt_split:
  "\<up>Unf\<^sub>G (\<up>step \<Phi> \<nu>) = \<up>af\<^sub>G\<^sub>\<UU> \<Phi> \<nu>"
  unfolding af_G_letter_abs_opt_def step_abs_def comp_def af_G_abs_opt.f_abs_def step_abs.f_abs_def
  using map_fun_apply Unf\<^sub>G_abs.abs_eq af_G_letter_opt.simps by auto

lemma af_G_letter_opt_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af_G_letter_opt \<phi> \<nu>"
  by (induction \<phi>) auto 

lemma af_G_letter_opt_sat_core_lifted:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep (\<up>af\<^sub>G\<^sub>\<UU> \<phi> \<nu>)"
  unfolding af_G_letter_abs_opt_def
  by (metis af_G_letter_opt_sat_core Quotient_ltl_prop_equiv_quotient[THEN Quotient_rep_abs] Quotient3_ltl_prop_equiv_quotient[THEN Quotient3_abs_rep] af_G_abs_opt.f_abs.abs_eq ltl_prop_equiv_def) 

lemma finite_reach_af_opt:
  "finite (reach \<Sigma> \<up>af\<^sub>\<UU> (Abs \<phi>))"
proof (cases "\<Sigma> \<noteq> {}")
  case True
    thus ?thesis
      using af_abs_opt.finite_abs_reach unfolding af_abs_opt.abs_reach_def reach_foldl_def[OF True]
      using finite_subset[of "{foldl \<up>af\<^sub>\<UU> (Abs \<phi>) w |w. set w \<subseteq> \<Sigma>}" "{foldl \<up>af\<^sub>\<UU> (Abs \<phi>) w |w. True}"] 
      unfolding af_letter_abs_opt_def
      by blast
qed (simp add: reach_def)

lemma finite_reach_af_G_opt:
  "finite (reach \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>))"
proof (cases "\<Sigma> \<noteq> {}")
  case True
    thus ?thesis
      using af_G_abs_opt.finite_abs_reach unfolding af_G_abs_opt.abs_reach_def reach_foldl_def[OF True]
      using finite_subset[of "{foldl \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w |w. set w \<subseteq> \<Sigma>}" "{foldl \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w |w. True}"] 
      unfolding af_G_letter_abs_opt_def
      by blast
qed (simp add: reach_def)

lemma wellformed_mojmir_opt:
  assumes "Only_G \<G>"
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  shows "mojmir \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) w {q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof -
  have "\<forall>q \<nu>. q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<longrightarrow> af_G_letter_abs_opt q \<nu> \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
    using `Only_G \<G>` af_G_letter_opt_sat_core_lifted by auto
  thus "?thesis"
    using finite_reach_af_G_opt assms by (unfold_locales; auto)
qed
 
lemma Rep_Abs_equiv: "Rep (Abs \<phi>) \<equiv>\<^sub>P \<phi>"
  using Rep_Abs_prop_entailment unfolding ltl_prop_equiv_def by auto

lemma Rep_step: "Rep (\<up>step \<Phi> \<nu>) \<equiv>\<^sub>P step (Rep \<Phi>) \<nu>"
  by (metis step_abs_def Quotient3_abs_rep Quotient3_ltl_prop_equiv_quotient ltl_prop_equiv_quotient.abs_eq_iff step_abs.f_abs.abs_eq)

lemma Rep_unf: "Rep (Unf\<^sub>G_abs \<Phi>) \<equiv>\<^sub>P Unf\<^sub>G (Rep \<Phi>)"
  by (simp add: Rep_Abs_equiv Unf\<^sub>G_abs_def)

lemma step_\<G>:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P step \<phi> \<nu>"
  by (induction \<phi>) auto

lemma Unf\<^sub>G_\<G>:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Unf\<^sub>G \<phi>"
  by (induction \<phi>) auto

locale ltl_FG_to_rabin_opt_def = 
  fixes 
    \<Sigma> :: "'a set set"
  fixes
    \<phi> :: "'a ltl"
  fixes
    \<G> :: "'a ltl set"
  fixes 
    w :: "'a set word"
begin

sublocale mojmir_to_rabin_def \<Sigma> "\<up>af\<^sub>G\<^sub>\<UU>" "Abs (Unf\<^sub>G \<phi>)" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}" .

--\<open>Import abbreviations from parent locale to simplify terms\<close>
abbreviation "\<delta>\<^sub>R \<equiv> step"
abbreviation "q\<^sub>R \<equiv> initial"
abbreviation "Acc\<^sub>R j \<equiv> (fail\<^sub>R \<union> merge\<^sub>R j, succeed\<^sub>R j)"
abbreviation "max_rank\<^sub>R \<equiv> max_rank"
abbreviation "smallest_accepting_rank\<^sub>R \<equiv> smallest_accepting_rank"
abbreviation "accept\<^sub>R' \<equiv> accept"

end

locale ltl_FG_to_rabin_opt = ltl_FG_to_rabin_opt_def +
  assumes 
    wellformed_\<G>: "Only_G \<G>"
  assumes
    wellformed_w: "range w \<subseteq> \<Sigma>"
  assumes
    finite_\<Sigma>: "finite \<Sigma>"
begin
  
sublocale mojmir_to_rabin \<Sigma> "\<up>af\<^sub>G\<^sub>\<UU>" "Abs (Unf\<^sub>G \<phi>)" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof
  show "\<And>q \<nu>. q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> \<up>af\<^sub>G\<^sub>\<UU> q \<nu> \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
    using wellformed_\<G> af_G_letter_opt_sat_core_lifted by auto
  have nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
    using wellformed_w by blast
  show "finite (reach \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G \<phi>)))" (is "finite ?A")
    using finite_reach_af_G_opt wellformed_\<G> by blast
qed (insert finite_\<Sigma> wellformed_w)

--\<open>Import lemmas from parent locale to simplify assumptions\<close>
lemmas state_rank_step_foldl = state_rank_step_foldl
lemmas wellformed_\<R> = wellformed_\<R>

end

lemma step_Abs_eq:
  "Abs (step \<phi> \<nu>) = \<up>step (Abs \<phi>) \<nu>"
  by (simp add: step_abs.f_abs.abs_eq step_abs_def)

subsection \<open>Equivalences between the standard and the optimised Mojmir construction\<close>

context
  fixes 
    \<Sigma> :: "'a set set"
  fixes 
    \<phi> :: "'a ltl"
  fixes
    \<G> :: "'a ltl set"
  fixes
    w :: "'a set word"
  assumes 
    context_assms: "Only_G \<G>" "finite \<Sigma>" "range w \<subseteq> \<Sigma>"
begin

--\<open>Create an interpretation of the mojmir locale for the standard construction\<close>
interpretation \<MM>: ltl_FG_to_rabin \<Sigma> \<phi> \<G> w
  apply unfold_locales using context_assms by auto

--\<open>Create an interpretation of the mojmir locale for the optimised construction\<close>
interpretation \<UU>: ltl_FG_to_rabin_opt \<Sigma> \<phi> \<G> w
  apply unfold_locales using context_assms by auto

lemma unfold_token_run_eq:
  assumes "x \<le> n"
  shows "\<MM>.token_run x (Suc n) = \<up>step (\<UU>.token_run x n) (w n)" 
  (is "?lhs = ?rhs")
proof -
  have "x + (n - x) = n" and "x + (Suc n - x) = Suc n"
   using assms by arith+
  have "w [x \<rightarrow> Suc n] = w [x \<rightarrow> n] @ [w n]"
    unfolding subsequence_def upt_Suc using assms by simp

  have "af\<^sub>G \<phi> (w [x \<rightarrow> Suc n]) = step (af\<^sub>G\<^sub>\<UU> (Unf\<^sub>G \<phi>) (w [x \<rightarrow> n])) (w n)" (is "?l = ?r")
    unfolding af_to_af_opt[symmetric] `w [x \<rightarrow> Suc n] = w [x \<rightarrow> n] @ [w n]` foldl_append
    using af_letter_alt_def by auto
  moreover
  have "?lhs = Abs ?l"
    unfolding \<MM>.token_run.simps run_foldl subsequence_def[symmetric]
    unfolding subsequence_shift `x + (Suc n - x) = Suc n` Nat.add_0_right   
    by (metis af_G_abs.f_foldl_abs_alt_def af_G_abs.f_foldl_abs.abs_eq af_G_letter_abs_def) 
  moreover
  have "Abs ?r = ?rhs"
    unfolding \<UU>.token_run.simps run_foldl 
    unfolding  `x + (n - x) = n` Nat.add_0_right af_G_letter_abs_opt_def  
    unfolding step_Abs_eq  af_G_abs_opt.f_foldl_abs_alt_def[unfolded af_G_abs_opt.f_foldl_abs.abs_eq] 
    using subsequence_prefix_suffix subsequence_def by metis
  ultimately
  show "?lhs = ?rhs"
    by presburger
qed

lemma unfold_token_succeeds_eq:
  "\<MM>.token_succeeds x = \<UU>.token_succeeds x"
proof 
  assume "\<MM>.token_succeeds x"

  then obtain n where "\<And>m. m > n \<Longrightarrow> \<MM>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" 
    unfolding \<MM>.token_succeeds_alt_def MOST_nat by blast
  then obtain n where "\<MM>.token_run x (Suc n) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" and "x \<le> n" 
    by (cases "x \<le> n") auto

  hence 1: "\<G> \<Turnstile>\<^sub>P Rep (step_abs (\<UU>.token_run x n) (w n))"
    using unfold_token_run_eq by fastforce
  moreover
  have "Suc n - x = Suc (n - x)" and "x + (n - x) = n"
    using `x \<le> n` by arith+
  ultimately
  have "\<UU>.token_run x (Suc n) = Unf\<^sub>G_abs (step_abs (\<UU>.token_run x n) (w n))"
    unfolding af_G_letter_abs_opt_split by simp
  
  hence "\<G> \<Turnstile>\<^sub>P Rep (\<UU>.token_run x (Suc n))"
    using 1 Unf\<^sub>G_\<G>[OF `Only_G \<G>`] Rep_unf[unfolded ltl_prop_equiv_def] by auto
  thus "\<UU>.token_succeeds x"
    unfolding \<UU>.token_succeeds_def by blast
next
  assume "\<UU>.token_succeeds x"

  then obtain n where "\<And>m. m > n \<Longrightarrow> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" 
    unfolding \<UU>.token_succeeds_alt_def MOST_nat by blast
  then obtain n where "\<UU>.token_run x n \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}" and "x \<le> n"
    by (cases "x \<le> n") (fastforce, auto)

  hence "\<G> \<Turnstile>\<^sub>P Rep (step_abs (\<UU>.token_run x n) (w n))"
    using step_\<G>[OF `Only_G \<G>`] Rep_step[unfolded ltl_prop_equiv_def] by blast
  thus "\<MM>.token_succeeds x"
    unfolding \<MM>.token_succeeds_def unfold_token_run_eq[OF `x \<le> n`, symmetric] by blast
qed    

lemma unfold_accept_eq:
  "\<MM>.accept = \<UU>.accept"
  unfolding \<MM>.accept_def \<UU>.accept_def MOST_nat_le unfold_token_succeeds_eq ..

lemma unfold_\<S>_eq:
  assumes "\<MM>.accept"
  shows "\<forall>\<^sub>\<infinity>n. \<MM>.\<S> (Suc n) = (\<lambda>q. step_abs q (w n)) ` (\<UU>.\<S> n) \<union> {Abs \<phi>} \<union> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof -
  --\<open>Obtain lower bounds for proof\<close>
  obtain i\<^sub>\<MM> where i\<^sub>\<MM>_def: "\<MM>.smallest_accepting_rank = Some i\<^sub>\<MM>"
    using assms unfolding \<MM>.smallest_accepting_rank_def by simp
  obtain n\<^sub>\<MM> where n\<^sub>\<MM>_def: "\<And>x m. m \<ge> n\<^sub>\<MM> \<Longrightarrow> \<MM>.token_succeeds x = (m < x \<or> (\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x m = Some j) \<or> \<MM>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q})"
    using \<MM>.token_smallest_accepting_rank[OF i\<^sub>\<MM>_def] unfolding MOST_nat_le by metis

  have "\<UU>.accept"
    using assms unfold_accept_eq by simp
  obtain i\<^sub>\<UU> where i\<^sub>\<UU>_def: "\<UU>.smallest_accepting_rank = Some i\<^sub>\<UU>"
    using `\<UU>.accept` unfolding \<UU>.smallest_accepting_rank_def by simp
  obtain n\<^sub>\<UU> where n\<^sub>\<UU>_def: "\<And>x m. m \<ge> n\<^sub>\<UU> \<Longrightarrow> \<UU>.token_succeeds x = (m < x \<or> (\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q})"
    using \<UU>.token_smallest_accepting_rank[OF i\<^sub>\<UU>_def] unfolding MOST_nat_le by metis
  
  show ?thesis
  proof (unfold MOST_nat_le, rule, rule, rule)
    fix m 
    assume "m \<ge> max n\<^sub>\<MM> n\<^sub>\<UU>"
    hence "m \<ge> n\<^sub>\<MM>" and "m \<ge> n\<^sub>\<UU>" and "Suc m \<ge> n\<^sub>\<MM>" 
      by simp+
    --\<open>Using the properties of @{term n\<^sub>\<MM>} and @{term n\<^sub>\<UU>} and the lemma @{thm unfold_token_succeeds_eq}, 
       we prove that the behaviour of x in @{text \<MM>} and @{text \<UU>} is similar in regards to 
       creation time, accepting rank or final states.\<close>
    hence token_trans: "\<And>x. Suc m < x \<or> (\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j) \<or> \<MM>.token_run x (Suc m) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}
      \<longleftrightarrow> m < x \<or> (\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
      using n\<^sub>\<MM>_def n\<^sub>\<UU>_def unfolding unfold_token_succeeds_eq by presburger

    show "\<MM>.\<S> (Suc m) = (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m) \<union> {Abs \<phi>} \<union> {q. \<G> \<Turnstile>\<^sub>P Rep q}" (is "?lhs = ?rhs")
    proof 
      {
        fix q assume "\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.state_rank q (Suc m) = Some j"
        moreover
        then obtain x where q_def: "q = \<MM>.token_run x (Suc m)" and "x \<le> Suc m"
           using \<MM>.push_down_state_rank_tokens by fastforce
        ultimately
        have "\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j"
          using \<MM>.rank_eq_state_rank by metis
        hence token_cases: "(\<exists>j\<ge>i\<^sub>\<UU>. \<UU>.rank x m = Some j) \<or> \<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<or> x = Suc m"
          using token_trans[of x] \<MM>.rank_Some_time by fastforce
        have "q \<in> ?rhs"
        proof (cases "x \<noteq> Suc m")
          case True
            hence "x \<le> m"
              using `x \<le> Suc m` by arith
            have "\<UU>.token_run x m \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep q"
              unfolding `q = \<MM>.token_run x (Suc m)` unfold_token_run_eq[OF `x \<le> m`]
              using Rep_step[unfolded ltl_prop_equiv_def] step_\<G>[OF `Only_G \<G>`] by blast
            moreover
            {
              assume "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.rank x m = Some j"
              moreover
              def q' \<equiv> "\<UU>.token_run x m"
              ultimately
              have "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.state_rank q' m = Some j"
                unfolding \<UU>.rank_eq_state_rank[OF `x \<le> m`] q'_def by blast
              hence "q' \<in> \<UU>.\<S> m"
                using assms i\<^sub>\<UU>_def by simp
              moreover
              have "q = step_abs q' (w m)"
                unfolding q_def q'_def unfold_token_run_eq[OF `x \<le> m`] ..
              ultimately
              have "q \<in> (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m)"
                by blast
            }
            ultimately
            show ?thesis 
              using token_cases True by blast
        qed (simp add: q_def)
      }
      thus "?lhs \<subseteq> ?rhs"   
        unfolding \<MM>.\<S>.simps i\<^sub>\<MM>_def option.sel by blast
    next   
      {
        fix q
        assume "q \<in> (\<lambda>q. step_abs q (w m)) ` (\<UU>.\<S> m)"
        then obtain q' where q_def: "q = step_abs q' (w m)" and "q' \<in> \<UU>.\<S> m"
          by blast
        hence "q \<in> ?lhs"
        proof (cases "\<G> \<Turnstile>\<^sub>P Rep q'")
          case False
            hence "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.state_rank q' m = Some j"
              using `q' \<in> \<UU>.\<S> m` unfolding \<UU>.\<S>.simps i\<^sub>\<UU>_def option.sel by blast
            moreover
            then obtain x where q'_def: "q' = \<UU>.token_run x m" and "x \<le> m" and "x \<le> Suc m"
              using \<UU>.push_down_state_rank_tokens by force
            ultimately
            have "\<exists>j \<ge> i\<^sub>\<UU>. \<UU>.rank x m = Some j" 
              unfolding \<UU>.rank_eq_state_rank[OF `x \<le> m`] q'_def by blast
            hence "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank x (Suc m) = Some j) \<or> \<MM>.token_run x (Suc m) \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
              using token_trans[of x] \<UU>.rank_Some_time by fastforce
            moreover
            have "\<MM>.token_run x (Suc m) = q"
              unfolding q_def q'_def unfold_token_run_eq[OF `x \<le> m`] ..
            ultimately
            have "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.state_rank q (Suc m) = Some j) \<or> q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
              using \<MM>.rank_eq_state_rank[OF `x \<le> Suc m`] by metis
            thus ?thesis
              unfolding \<MM>.\<S>.simps option.sel i\<^sub>\<MM>_def by blast
        qed (insert step_\<G>[OF `Only_G \<G>`, of "Rep q'"], unfold q_def Rep_step[unfolded ltl_prop_equiv_def, rule_format, symmetric], auto)
      }
      moreover
      have "(\<exists>j\<ge>i\<^sub>\<MM>. \<MM>.rank (Suc m) (Suc m) = Some j) \<or> \<G> \<Turnstile>\<^sub>P Rep (Abs \<phi>)" 
        using token_trans[of "Suc m"] by simp
      hence "Abs \<phi> \<in> ?lhs"
        using i\<^sub>\<MM>_def \<MM>.rank_eq_state_rank[OF order_refl] by (cases "\<G> \<Turnstile>\<^sub>P Rep (Abs \<phi>)") simp+
      ultimately
      show "?lhs \<supseteq> ?rhs"   
        unfolding \<MM>.\<S>.simps by blast
    qed
  qed
qed

end

subsection \<open>Automaton Definition\<close>

fun ltl_to_generalised_rabin_unf_initial_state ("\<iota>\<^sub>\<UU>")
where
  "\<iota>\<^sub>\<UU> \<phi> = (Abs (Unf \<phi>), \<iota>\<^sub>\<times> (\<^bold>G \<phi>) (\<lambda>\<chi>. ltl_FG_to_rabin_opt_def.q\<^sub>R (theG \<chi>)))"

fun ltl_to_generalised_rabin_unf_transition_function ("\<delta>\<^sub>\<UU>")
where
  "\<delta>\<^sub>\<UU> \<Sigma> = \<up>af\<^sub>\<UU> \<times> (\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_opt_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>)))"

context
  fixes 
    \<Sigma> :: "'a set set"
begin

fun Acc\<^sub>\<UU>_fin
where
  "Acc\<^sub>\<UU>_fin \<pi> \<chi> = \<Union>(embed_transition_snd ` \<Union>(embed_transition \<chi> ` (fst (ltl_FG_to_rabin_opt_def.Acc\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>) (the (\<pi> \<chi>))))))"

fun Acc\<^sub>\<UU>_inf
where
  "Acc\<^sub>\<UU>_inf \<pi> \<chi> = \<Union>(embed_transition_snd ` \<Union>(embed_transition \<chi> ` (snd (ltl_FG_to_rabin_opt_def.Acc\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>) (the (\<pi> \<chi>))))))"

fun M\<^sub>\<UU>_fin :: "('a ltl \<rightharpoonup> nat) \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) transition set"
where
  "M\<^sub>\<UU>_fin \<pi> = {((\<phi>', m), \<nu>, p). \<not>(\<forall>S. (\<forall>\<chi> \<in> (dom \<pi>). S \<up>\<Turnstile>\<^sub>P Abs \<chi> \<and> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (Abs (theG \<chi>)) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (m \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (\<up>step q \<nu>))) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P (\<up>step \<phi>' \<nu>))}"

fun ltl_to_generalised_rabin_unf_acceptance_condition :: "'a ltl \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) generalized_rabin_condition" ("F\<^sub>\<UU>")
where
  "F\<^sub>\<UU> \<phi> = {(M\<^sub>\<UU>_fin \<pi> \<union> \<Union>{Acc\<^sub>\<UU>_fin \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc\<^sub>\<UU>_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}) | \<pi>. dom \<pi> \<subseteq> \<^bold>G \<phi> \<and> (\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>))}"

fun ltl_to_generalised_rabin_opt :: "'a ltl \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) generalized_rabin_automaton" ("\<A>\<^sub>\<UU>")
where
  "\<A>\<^sub>\<UU> \<phi> = (\<delta>\<^sub>\<UU> \<Sigma>, \<iota>\<^sub>\<UU> \<phi>, F\<^sub>\<UU> \<phi>)"

abbreviation Acc\<^sub>\<UU>
where
  "Acc\<^sub>\<UU> \<pi> \<chi> \<equiv> (Acc\<^sub>\<UU>_fin \<pi> \<chi>, Acc\<^sub>\<UU>_inf \<pi> \<chi>)" 

subsection \<open>Properties\<close>

context
  fixes 
    \<phi> :: "'a ltl"
  fixes 
    w :: "'a set word"
  assumes 
    finite_\<Sigma>: "finite \<Sigma>"
  assumes
    bounded_w: "range w \<subseteq> \<Sigma>"
begin

lemma ltl_to_generalised_rabin_unf_wellformed:
  "finite (reach \<Sigma> (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>))"
  apply (cases "\<Sigma> = {}")
    apply (simp add: reach_def)
    apply (simp only: ltl_to_generalised_rabin_unf_initial_state.simps ltl_to_generalised_rabin_unf_transition_function.simps)
    apply (rule finite_reach_simple_product[OF finite_reach_af_opt finite_reach_product])
      apply (auto simp add: dom_def intro: G_nested_finite finite_\<Sigma> ltl_FG_to_rabin_opt.wellformed_\<R>[unfolded ltl_FG_to_rabin_opt_def])
  done

lemma run_limit_not_empty:
  "limit (run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w) \<noteq> {}"
  by (metis bounded_w emptyE finite_\<Sigma> limit_nonemptyE ltl_to_generalised_rabin_unf_wellformed run\<^sub>t_finite) 

lemma accept\<^sub>G\<^sub>R_\<UU>_I:
  assumes "accept\<^sub>G\<^sub>R (\<A>\<^sub>\<UU> \<phi>) w"
  obtains \<pi> where "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
    and "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>, UNIV) w"
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> \<chi>) w"
proof -
  from assms obtain P where "P \<in> F\<^sub>\<UU> \<phi>" and "accepting_pair\<^sub>G\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) P w"
    unfolding accept\<^sub>G\<^sub>R_def ltl_to_generalised_rabin_opt.simps fst_conv snd_conv by blast 
  moreover
  then obtain \<pi> where "dom \<pi> \<subseteq> \<^bold>G \<phi>" and "\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
    and P_def: "P = (M\<^sub>\<UU>_fin \<pi> \<union> \<Union>{Acc\<^sub>\<UU>_fin \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc\<^sub>\<UU>_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>})"
    by auto
  have "limit (run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w) \<inter> UNIV \<noteq> {}"
    using run_limit_not_empty by simp
  ultimately
  have "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>, UNIV) w" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> \<chi>) w"
    unfolding P_def accepting_pair\<^sub>G\<^sub>R_simp accepting_pair\<^sub>R_simp by blast+ (* Slow... *)
  thus ?thesis
    using that `dom \<pi> \<subseteq> \<^bold>G \<phi>` `\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)` by blast
qed

lemma \<UU>_run:
  defines "r \<equiv> run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w"
  shows "fst (fst (r i)) = Abs (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i]))" (is "?t1")
    and "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (snd (fst (r i)) \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w q i"
proof -
  have "run (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w i = 
    (Abs (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i])), \<lambda>\<chi>. if \<chi> \<in> \<^bold>G \<phi> then Some (\<lambda>\<psi>. foldl (ltl_FG_to_rabin_opt_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>)) (ltl_FG_to_rabin_opt_def.q\<^sub>R (theG \<chi>)) (map w [0..< i]) \<psi>) else None)"
  proof (induction i)
    case (Suc i) 
      have X: "Abs (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> Suc i])) = \<up>af\<^sub>\<UU> (Abs (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i]))) (w i)"
        by (simp add: af_abs_opt.f_abs.abs_eq af_letter_abs_opt_def) 
      show ?case 
        unfolding run_foldl upt_Suc list.simps less_eq_nat.simps(1) if_True map_append foldl_append Suc[unfolded run_foldl] X by auto
  qed (unfold run_foldl upt_0 list.simps foldl.simps, force)
  moreover
  have X: "ltl_FG_to_rabin_opt \<Sigma> {} w"
    using `finite \<Sigma>` `range w \<subseteq> \<Sigma>` ltl_FG_to_rabin_opt_def by auto
  ultimately
  have state_run: "run (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w i = 
    (Abs (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i])), \<lambda>\<chi>. if \<chi> \<in> \<^bold>G \<phi> then Some (\<lambda>\<psi>. semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w \<psi> i) else None)" 
    using ltl_FG_to_rabin_opt.state_rank_step_foldl[OF X] by auto
   
  show ?t1
    unfolding r_def run\<^sub>t.simps using state_run by fastforce
  show "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (snd (fst (r i)) \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w q i"
    unfolding r_def run\<^sub>t.simps state_run by force
qed

context
  fixes 
    \<psi> :: "'a ltl"
  fixes 
    \<pi> :: "'a ltl \<Rightarrow> nat option"
  assumes
    "G \<psi> \<in> dom \<pi>"
  assumes
    "dom \<pi> \<subseteq> \<^bold>G \<phi>"
begin

interpretation ltl_FG_to_rabin_opt \<Sigma> \<psi> "dom \<pi>"
  by (unfold_locales; insert finite_\<Sigma> bounded_w `dom \<pi> \<subseteq> \<^bold>G \<phi>` \<G>_elements; blast)

lemma \<UU>_Acc_property:
  "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> (G \<psi>)) w \<longleftrightarrow> accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) w"
  (is "?Acc = ?Acc\<^sub>\<R>")
proof -  
  def r \<equiv> "run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w" and r\<^sub>\<psi> \<equiv> "run\<^sub>t \<delta>\<^sub>\<R> q\<^sub>\<R> w"
  hence "finite (range r)"
    using run\<^sub>t_finite[OF ltl_to_generalised_rabin_unf_wellformed] `range w \<subseteq> \<Sigma>` `finite \<Sigma>`
    by (blast dest: finite_subset) 

  have "\<And>S. limit r\<^sub>\<psi> \<inter> S = {} \<longleftrightarrow> limit r \<inter> \<Union>(embed_transition_snd ` (\<Union> ((embed_transition (G \<psi>)) ` S))) = {}"
  proof -
    fix S
    have 1: "snd (\<iota>\<^sub>\<UU> \<phi>) (G \<psi>) = Some q\<^sub>\<R>"
      using `G \<psi> \<in> dom \<pi>` `dom \<pi> \<subseteq> \<^bold>G \<phi>` by auto
    have 2: "finite (range (run\<^sub>t (\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_opt_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>))) (snd (\<iota>\<^sub>\<UU> \<phi>)) w))"
      using `finite (range r)` r_def by (auto intro: product_run_finite_snd)
    show "?thesis S"
      unfolding r_def r\<^sub>\<psi>_def product_run_embed_limit_finiteness[OF 1 2, unfolded ltl.sel, symmetric] ltl_to_generalised_rabin_unf_initial_state.simps ltl_to_generalised_rabin_unf_transition_function.simps
      using product_run_embed_limit_finiteness_snd[OF `finite (range r)`[unfolded r_def ltl_to_generalised_rabin_unf_initial_state.simps ltl_to_generalised_rabin_unf_transition_function.simps]] by auto
  qed
  hence "limit r \<inter> fst (Acc\<^sub>\<UU> \<pi> (G \<psi>)) = {} \<and> limit r \<inter> snd (Acc\<^sub>\<UU> \<pi> (G \<psi>)) \<noteq> {} 
     \<longleftrightarrow> limit r\<^sub>\<psi> \<inter> fst (Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) = {} \<and> limit r\<^sub>\<psi> \<inter> snd (Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) \<noteq> {}"
    by force
  thus "?Acc \<longleftrightarrow> ?Acc\<^sub>\<R>" 
    unfolding r\<^sub>\<psi>_def r_def accepting_pair\<^sub>R_def by blast 
qed

lemma \<UU>_Acc_to_rabin_accept:
  "\<lbrakk>accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> (G \<psi>)) w; the (\<pi> (G \<psi>)) < max_rank\<rbrakk> \<Longrightarrow> accept\<^sub>R \<R> w"
  unfolding \<UU>_Acc_property by auto

lemma \<UU>_Acc_to_mojmir_accept:
  "\<lbrakk>accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> (G \<psi>)) w; the (\<pi> (G \<psi>)) < max_rank\<rbrakk> \<Longrightarrow> accept"
  using \<UU>_Acc_to_rabin_accept unfolding mojmir_accept_iff_rabin_accept by auto

lemma \<UU>_rabin_accept_to_Acc:
  "\<lbrakk>accept\<^sub>R \<R> w; \<pi> (G \<psi>) = smallest_accepting_rank\<rbrakk> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> (G \<psi>)) w"
  unfolding \<UU>_Acc_property Mojmir_rabin_smallest_accepting_rank 
  using smallest_accepting_rank\<^sub>\<R>_properties smallest_accepting_rank\<^sub>\<R>_def  
  by (metis (no_types, lifting) option.sel)

lemma \<UU>_mojmir_accept_to_Acc:
  "\<lbrakk>accept; \<pi> (G \<psi>) = smallest_accepting_rank\<rbrakk> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> (G \<psi>)) w"
  unfolding mojmir_accept_iff_rabin_accept by (blast dest: \<UU>_rabin_accept_to_Acc)

end

lemma \<UU>_normalise_\<pi>:
  assumes dom_subset: "dom \<pi> \<subseteq> \<^bold>G \<phi>"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
  assumes "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>, UNIV) w"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> \<chi>) w"
  obtains \<pi>\<^sub>\<A> where "dom \<pi> = dom \<pi>\<^sub>\<A>"
    and "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = ltl_FG_to_rabin_opt_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>\<^sub>\<A>) w"
    and "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<A>, UNIV) w" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi>\<^sub>\<A> \<chi>) w"
proof -
  def \<G> \<equiv> "dom \<pi>"
  note \<G>_properties[OF dom_subset]

  def \<pi>\<^sub>\<A> \<equiv> "(\<lambda>\<chi>. ltl_FG_to_rabin_opt_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>) w) |` \<G>"

  moreover
  
  {
    fix \<chi> assume "\<chi> \<in> dom \<pi>"
  
    interpret ltl_FG_to_rabin_opt \<Sigma> "theG \<chi>" "dom \<pi>"
      apply (unfold_locales)
      using `finite \<Sigma>` dom_subset \<G>_elements bounded_w by (auto, blast)
  
    from `\<chi> \<in> dom \<pi>` have "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> \<chi>) w"
      using assms(4) by blast
    hence "accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> (the (\<pi> \<chi>))) w" 
      by (metis `\<chi> \<in> dom \<pi>` \<UU>_Acc_property[OF _ dom_subset] `Only_G (dom \<pi>)` ltl.sel(8))
    moreover
    hence "accept\<^sub>R (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {Acc\<^sub>\<R> j | j. j < max_rank}) w"
      using assms(2)[OF `\<chi> \<in> dom \<pi>`]by auto
    ultimately
    have "the (smallest_accepting_rank\<^sub>\<R>) \<le> the (\<pi> \<chi>)" and "smallest_accepting_rank \<noteq> None"
      using Least_le[of _ "the (\<pi> \<chi>)"] assms(2)[OF `\<chi> \<in> dom \<pi>`] mojmir_accept_iff_rabin_accept option.distinct(1) smallest_accepting_rank_def 
      by (simp add: smallest_accepting_rank\<^sub>\<R>_def)+
    hence "the (\<pi>\<^sub>\<A> \<chi>) \<le> the (\<pi> \<chi>)" and "\<chi> \<in> dom \<pi>\<^sub>\<A>"
      unfolding \<pi>\<^sub>\<A>_def dom_restrict using assms(2) `\<chi> \<in> dom \<pi>` by (simp add: Mojmir_rabin_smallest_accepting_rank \<G>_def, subst dom_def, simp add: \<G>_def)
  }
  
  hence "dom \<pi> = dom \<pi>\<^sub>\<A>"
    unfolding \<pi>\<^sub>\<A>_def dom_restrict \<G>_def by auto
  
  moreover
  
  note \<G>_properties[OF dom_subset, unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`]
  
  have "M\<^sub>\<UU>_fin \<pi>\<^sub>\<A> \<subseteq> M\<^sub>\<UU>_fin \<pi>" 
    using `\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi>\<^sub>\<A> \<chi>) \<le> the (\<pi> \<chi>)` unfolding M\<^sub>\<UU>_fin.simps `dom \<pi> = dom \<pi>\<^sub>\<A>` apply simp unfolding Collect_mono_iff case_prod_beta by (meson le_trans) 
  hence "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<A>, UNIV) w"
    using assms unfolding accepting_pair\<^sub>R_simp by blast
   
  moreover

  --\<open>Goal 2\<close>
  {
    fix \<chi> assume "\<chi> \<in> dom \<pi>\<^sub>\<A>"
    hence "\<chi> = G (theG \<chi>)"
      unfolding `dom \<pi> = dom \<pi>\<^sub>\<A>`[symmetric] `Only_G (dom \<pi>)` by (metis `Only_G (dom \<pi>\<^sub>\<A>)` `\<chi> \<in> dom \<pi>\<^sub>\<A>` ltl.collapse(6) ltl.disc(58)) 
    moreover
    hence "G (theG \<chi>) \<in> dom \<pi>\<^sub>\<A>"
      using `\<chi> \<in> dom \<pi>\<^sub>\<A>` by simp
    moreover
    hence X: "ltl_FG_to_rabin_opt_def.accept\<^sub>R' (theG \<chi>) (dom \<pi>) w"
      by (metis (no_types, lifting) assms(1,2,4) `dom \<pi> \<subseteq> \<^bold>G \<phi>` ltl.sel(8) \<UU>_Acc_to_mojmir_accept `dom \<pi> = dom \<pi>\<^sub>\<A>`) 
    have Y: "\<pi>\<^sub>\<A> (G theG \<chi>) = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
      using `G (theG \<chi>) \<in> dom \<pi>\<^sub>\<A>` `\<chi> = G (theG \<chi>)` \<pi>\<^sub>\<A>_def `dom \<pi> = dom \<pi>\<^sub>\<A>`[symmetric] by simp
    ultimately
    have "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi>\<^sub>\<A> \<chi>) w"
      using \<UU>_mojmir_accept_to_Acc[OF `G (theG \<chi>) \<in> dom \<pi>\<^sub>\<A>` `dom \<pi> \<subseteq> \<^bold>G \<phi>`[unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`] X[unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`] Y] by simp
  }

  ultimately

  show ?thesis
    using that[of \<pi>\<^sub>\<A>] restrict_in unfolding `dom \<pi> = dom \<pi>\<^sub>\<A>` \<G>_def 
    by (metis (no_types, lifting))
qed

subsection \<open>Correctness Theorem\<close>

lemma unfold_optimisation_correct_M:
  assumes "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>"
  assumes "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<Turnstile>\<^sub>P Rep q}"
  shows "accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w \<longleftrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w"
proof -
  --\<open>Preliminary Facts\<close>
  note \<G>_properties[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>`]

  --\<open>Define constants for both runs\<close>
  def r\<^sub>\<A> \<equiv> "run\<^sub>t (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) w" and r\<^sub>\<UU> \<equiv> "run\<^sub>t (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) w"
  hence "finite (range r\<^sub>\<A>)" and "finite (range r\<^sub>\<UU>)"
    using run\<^sub>t_finite[OF ltl_to_generalised_rabin_wellformed] run\<^sub>t_finite[OF ltl_to_generalised_rabin_unf_wellformed] 
    using `range w \<subseteq> \<Sigma>` `finite \<Sigma>` by (blast dest: finite_subset)+

  --\<open>Prove that the limit of both runs behave the same in respect to the M acceptance condition\<close>
  have "limit r\<^sub>\<A> \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> limit r\<^sub>\<UU> \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
  proof -
    have "ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w"
      by (unfold_locales; insert \<G>_elements[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>`] finite_\<Sigma> bounded_w) 
    hence X: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> mojmir_def.accept \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
      by (metis assms(3) ltl_FG_to_rabin.smallest_accepting_rank_properties(1) domD)
    have "\<forall>\<^sub>\<infinity>i. \<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} (Suc i)
       = (\<lambda>q. step_abs q (w i)) ` (mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} i) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
      using almost_all_commutative'[OF `finite (dom \<pi>\<^sub>\<A>)`] X unfold_\<S>_eq[OF `Only_G (dom \<pi>\<^sub>\<A>)`] finite_\<Sigma> bounded_w by simp
    
    then obtain i where i_def: "\<And>j \<chi>. j \<ge> i \<Longrightarrow> \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} (Suc j)
       = (\<lambda>q. step_abs q (w j)) ` (mojmir_def.\<S> \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} j) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
       unfolding MOST_nat_le by blast

    obtain j where "limit r\<^sub>\<A> = range (suffix j r\<^sub>\<A>)"
      and "limit r\<^sub>\<UU> = range (suffix j r\<^sub>\<UU>)"
      using `finite (range r\<^sub>\<A>)` `finite (range r\<^sub>\<UU>)` 
      by (rule common_range_limit)
    hence "limit r\<^sub>\<A> = range (suffix (j + i + 1) r\<^sub>\<A>)"
      and "limit r\<^sub>\<UU> = range (suffix (j + i) r\<^sub>\<UU>)"
      by (metis limit_range_suffix)+
    moreover
    have "\<And>j. j \<ge> i \<Longrightarrow> r\<^sub>\<A> (Suc j) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> r\<^sub>\<UU> j \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
    proof -
      fix j
      assume "j \<ge> i"
       
      obtain \<phi>\<^sub>\<A> m\<^sub>\<A> x where r\<^sub>\<A>_def': "r\<^sub>\<A> (Suc j) = ((\<phi>\<^sub>\<A>, m\<^sub>\<A>), w (Suc j), x)"
        unfolding r\<^sub>\<A>_def run\<^sub>t.simps using PairE by fastforce

      obtain \<phi>\<^sub>\<UU> m\<^sub>\<UU> y where r\<^sub>\<UU>_def': "r\<^sub>\<UU> j = ((\<phi>\<^sub>\<UU>, m\<^sub>\<UU>), w j, y)"
        unfolding r\<^sub>\<UU>_def run\<^sub>t.simps using PairE by fastforce

      have m\<^sub>\<A>_def: "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (m\<^sub>\<A> \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w q (Suc j)"
        using \<A>_run(2)[OF finite_\<Sigma> bounded_w, of _ \<phi> "Suc j"] unfolding r\<^sub>\<A>_def'[unfolded r\<^sub>\<A>_def] prod.sel by simp

      have m\<^sub>\<UU>_def: "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (m\<^sub>\<UU> \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w q j"
        using \<UU>_run(2)[of _ j] unfolding r\<^sub>\<UU>_def'[unfolded r\<^sub>\<UU>_def] prod.sel by simp

      {
        have "Rep (fst (fst (r\<^sub>\<A> (Suc j)))) \<equiv>\<^sub>P step (Rep (fst (fst (r\<^sub>\<UU> j)))) (w j)"
          using \<A>_run(1)[OF finite_\<Sigma> bounded_w, of \<phi> "Suc j"] \<UU>_run(1) step_abs.f_abs.abs_eq r\<^sub>\<A>_def r\<^sub>\<UU>_def 
          by (metis Rep_step `fst (fst (run\<^sub>t (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) w (Suc j))) = Abs (af \<phi> (w [0 \<rightarrow> Suc j]))` af_equiv' step_abs_def)
        hence A: "\<And>S. S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A> \<longleftrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j)"
          unfolding r\<^sub>\<A>_def' r\<^sub>\<UU>_def' prod.sel ltl_prop_equiv_def ..
        
        {
          fix S assume "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi>"
          hence "dom \<pi>\<^sub>\<A> \<subseteq> S"
            using `Only_G (dom \<pi>\<^sub>\<A>)` assms by (metis ltl_prop_entailment.simps(8) subsetI)
          {
            fix \<chi> assume "\<chi> \<in> dom \<pi>\<^sub>\<A>"
          

            interpret \<MM>: ltl_FG_to_rabin \<Sigma> "theG \<chi>" "dom \<pi>\<^sub>\<A>" 
              by (unfold_locales, insert `Only_G (dom \<pi>\<^sub>\<A>)` bounded_w finite_\<Sigma>)
            interpret \<UU>: ltl_FG_to_rabin_opt \<Sigma> "theG \<chi>" "dom \<pi>\<^sub>\<A>"
              by (unfold_locales, insert `Only_G (dom \<pi>\<^sub>\<A>)` bounded_w finite_\<Sigma>)
  
            have "\<And>q \<nu>. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q \<Longrightarrow> dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep (step_abs q \<nu>)"
              using `Only_G (dom \<pi>\<^sub>\<A>)` by (metis ltl_prop_equiv_def Rep_step step_\<G>) 
            then have subsetStep: "\<And>\<nu>. (\<lambda>q. step_abs q \<nu>) ` {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} \<subseteq> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
              by auto
               
            let ?P = "\<lambda>q. S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q)"
            have "\<And>q \<nu>. (dom \<pi>\<^sub>\<A>) \<Turnstile>\<^sub>P Rep q \<Longrightarrow> ?P q"
              using `Only_G (dom \<pi>\<^sub>\<A>)` eval\<^sub>G_prop_entailment `(dom \<pi>\<^sub>\<A>) \<subseteq> S` by blast 
            hence "\<And>q. q \<in> {q. (dom \<pi>\<^sub>\<A>) \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> ?P q"
              by simp
            moreover
            have Y: "\<MM>.\<S> (Suc j) = (\<lambda>q. step_abs q (w j)) ` (\<UU>.\<S> j) \<union> {Abs (theG \<chi>)} \<union> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
              using i_def[OF `j \<ge> i` `\<chi> \<in> dom \<pi>\<^sub>\<A>`] by simp
            
            have 1: "\<MM>.smallest_accepting_rank = (\<pi>\<^sub>\<A> \<chi>)"
              and 2: "\<UU>.smallest_accepting_rank = (\<pi>\<^sub>\<UU> \<chi>)"
              and 3: "\<chi> \<in> \<^bold>G \<phi>"
              using `\<chi> \<in> dom \<pi>\<^sub>\<A>` assms by auto
            ultimately
            have "(\<forall>q \<in> \<MM>.\<S> (Suc j). ?P q) = (\<forall>q \<in> (\<lambda>q. step_abs q (w j)) ` (\<UU>.\<S> j) \<union> {Abs (theG \<chi>)}. ?P q)"
              unfolding Y by blast
            hence 4: "(\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> ?P q) = ((\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> ?P (step_abs q (w j))) \<and> ?P (Abs (theG \<chi>)))"
              using `\<And>q. q \<in> {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> ?P q` subsetStep
              unfolding m\<^sub>\<A>_def[OF 3, symmetric] m\<^sub>\<UU>_def[OF 3, symmetric] \<MM>.\<S>.simps \<UU>.\<S>.simps 1 2 Set.image_Un option.sel by blast
            have "S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q)) \<longleftrightarrow>
              S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (step (Rep q) (w j)))"
              unfolding 4 using eval\<^sub>G_respectfulness(2)[OF Rep_Abs_equiv, unfolded ltl_prop_equiv_def]
              using eval\<^sub>G_respectfulness(2)[OF Rep_step, unfolded ltl_prop_equiv_def] by blast
          }
          hence "((\<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) \<longrightarrow> S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A>)
            \<longleftrightarrow> ((\<forall>\<chi> \<in> dom \<pi>\<^sub>\<UU>. S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (step (Rep q) (w j)))) \<longrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j))"
            by (simp add: `\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> (S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j\<ge>the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) = (S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j\<ge>the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (step (Rep q) (w j))))` A assms(2))
        }
        hence "(\<forall>S. (\<forall>\<chi> \<in> dom \<pi>\<^sub>\<A>. S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<A> \<chi>). the (m\<^sub>\<A> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<A>) (Rep q))) \<longrightarrow> S \<Turnstile>\<^sub>P Rep \<phi>\<^sub>\<A>) \<longleftrightarrow> 
        (\<forall>S. (\<forall>\<chi> \<in> dom \<pi>\<^sub>\<UU>. S \<Turnstile>\<^sub>P \<chi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (theG \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi>\<^sub>\<UU> \<chi>). the (m\<^sub>\<UU> \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (dom \<pi>\<^sub>\<UU>) (step (Rep q) (w j)))) \<longrightarrow> S \<Turnstile>\<^sub>P step (Rep \<phi>\<^sub>\<UU>) (w j))"
          unfolding assms by auto
      }
      hence "((\<phi>\<^sub>\<A>, m\<^sub>\<A>), w (Suc j), x) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> ((\<phi>\<^sub>\<UU>, m\<^sub>\<UU>), w j, y) \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
        unfolding M_fin.simps M\<^sub>\<UU>_fin.simps ltl_prop_entails_abs.abs_eq[symmetric] eval\<^sub>G_abs.abs_eq[symmetric] step_Abs_eq ltl\<^sub>P_abs_rep by blast
      thus "?thesis j" 
        unfolding r\<^sub>\<A>_def' r\<^sub>\<UU>_def' .
    qed 
    hence "\<And>n. r\<^sub>\<A> (j + i + 1 + n) \<in> M_fin \<pi>\<^sub>\<A> \<longleftrightarrow> r\<^sub>\<UU> (j + i + n) \<in> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>"
      by simp
    hence "range (suffix (j + i + 1) r\<^sub>\<A>) \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> range (suffix (j + i) r\<^sub>\<UU>) \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
      unfolding suffix_def by blast
    ultimately
    show "limit r\<^sub>\<A> \<inter> M_fin \<pi>\<^sub>\<A> = {} \<longleftrightarrow> limit r\<^sub>\<UU> \<inter> M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU> = {}"
      by force
  qed
  moreover
  have "limit r\<^sub>\<A> \<inter> UNIV \<noteq> {}" and "limit r\<^sub>\<UU> \<inter> UNIV \<noteq> {}"
    using limit_nonempty `finite (range r\<^sub>\<UU>)` `finite (range r\<^sub>\<A>)` by auto
  ultimately
  show ?thesis
    unfolding accepting_pair\<^sub>R_def fst_conv snd_conv r\<^sub>\<A>_def[symmetric] r\<^sub>\<UU>_def[symmetric] Let_def by blast
qed

theorem unfold_optimisation_correct:
  "accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin \<Sigma> \<phi>) w \<longleftrightarrow> accept\<^sub>G\<^sub>R (\<A>\<^sub>\<UU> \<phi>) w" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain \<pi> where I: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
    and II:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
    and III: "accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>, UNIV) w"
    and IV:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
    by (blast intro: accept\<^sub>G\<^sub>R_\<A>_I[OF finite_\<Sigma> bounded_w])

  --\<open>Normalise @{text \<pi>} to the smallest accepting ranks\<close>
  then obtain \<pi>\<^sub>\<A> where A: "dom \<pi> = dom \<pi>\<^sub>\<A>"
    and B: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
    and C: "accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w" 
    and D: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
    using \<A>_normalise_\<pi>[OF finite_\<Sigma> bounded_w ] by blast

  --\<open>Properties about the domain of @{text \<pi>}\<close>
  note \<G>_properties[OF `dom \<pi> \<subseteq> \<^bold>G \<phi>`]
  hence \<MM>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs (Abs (theG \<chi>)) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q}"
    using I II IV \<A>_Acc_to_mojmir_accept[OF finite_\<Sigma> bounded_w] by (metis ltl.sel(8)) 
  hence \<UU>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q}"
    using unfold_accept_eq[OF `Only_G (dom \<pi>)` finite_\<Sigma> bounded_w] by blast

  --\<open>Define @{text \<pi>} for the other automaton\<close>
  def \<pi>\<^sub>\<UU> \<equiv> "\<lambda>\<chi>. if \<chi> \<in> dom \<pi> then mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q} else None"
  
  have 1: "dom \<pi>\<^sub>\<UU> = dom \<pi>"
    using \<UU>_Accept by (auto simp add: \<pi>\<^sub>\<UU>_def dom_def mojmir_def.smallest_accepting_rank_def)   
  hence "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>" and "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>" and "dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>"
    using A `dom \<pi> \<subseteq> \<^bold>G \<phi>` by blast+
  have 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<Turnstile>\<^sub>P Rep q}"
    using 1 unfolding `dom \<pi>\<^sub>\<UU> = dom \<pi>` \<pi>\<^sub>\<UU>_def by simp
  hence 3: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> the (\<pi>\<^sub>\<UU> \<chi>) < semi_mojmir_def.max_rank \<Sigma> af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) "
    using wellformed_mojmir_opt[OF \<G>_elements[OF `dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>`] finite_\<Sigma> bounded_w, THEN mojmir.smallest_accepting_rank_properties(6)] by fastforce

  --\<open>Use correctness of the translation of individual accepting pairs\<close>
  have Acc: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi>\<^sub>\<UU> \<chi>) w"
    using \<UU>_mojmir_accept_to_Acc[OF _ `dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>`] \<G>_elements[OF `dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>`] 
    using 1 2[of "G _"] 3[of "G _"] \<UU>_Accept[of "G _"] ltl.sel(8) by metis 
  have M: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w"
    using unfold_optimisation_correct_M[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>` `dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>` B 2] C
    using `dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>` by blast+

  show ?rhs
    using Acc 3 `dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>` combine_rabin_pairs_UNIV[OF M combine_rabin_pairs] 
    by (simp only: ltl_to_generalised_rabin_opt.simps accept\<^sub>G\<^sub>R_def fst_conv snd_conv ltl_to_generalised_rabin_unf_acceptance_condition.simps) blast
next
  assume ?rhs
  then obtain \<pi> where I: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
    and II:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_opt_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
    and III: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>, UNIV) w"
    and IV:  "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi> \<chi>) w"
    by (blast intro: accept\<^sub>G\<^sub>R_\<UU>_I)

  --\<open>Normalise @{text \<pi>} to the smallest accepting ranks\<close>
  then obtain \<pi>\<^sub>\<UU> where A: "dom \<pi> = dom \<pi>\<^sub>\<UU>"
    and B: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> \<pi>\<^sub>\<UU> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G\<^sub>\<UU> (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi>\<^sub>\<UU> \<Turnstile>\<^sub>P Rep q}"
    and C: "accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (M\<^sub>\<UU>_fin \<pi>\<^sub>\<UU>, UNIV) w" 
    and D: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<UU> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<UU> \<Sigma>) (\<iota>\<^sub>\<UU> \<phi>) (Acc\<^sub>\<UU> \<pi>\<^sub>\<UU> \<chi>) w"
    using \<UU>_normalise_\<pi> by blast

  --\<open>Properties about the domain of @{text \<pi>}\<close>
  note \<G>_properties[OF `dom \<pi> \<subseteq> \<^bold>G \<phi>`]
  hence \<UU>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs_opt (Abs (Unf\<^sub>G (theG \<chi>))) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q}"
    using I II IV \<UU>_Acc_to_mojmir_accept by (metis ltl.sel(8)) 
  hence \<MM>_Accept: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> mojmir_def.accept af_G_letter_abs (Abs (theG \<chi>)) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q}"
    using unfold_accept_eq[OF `Only_G (dom \<pi>)` finite_\<Sigma> bounded_w] by blast

  --\<open>Define @{text \<pi>} for the other automaton\<close>
  def \<pi>\<^sub>\<A> \<equiv> "\<lambda>\<chi>. if \<chi> \<in> dom \<pi> then mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi> \<Turnstile>\<^sub>P Rep q} else None"
  
  have 1: "dom \<pi>\<^sub>\<A> = dom \<pi>"
    using \<MM>_Accept by (auto simp add: \<pi>\<^sub>\<A>_def dom_def mojmir_def.smallest_accepting_rank_def)   
  hence "dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>" and "dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>" and "dom \<pi>\<^sub>\<UU> \<subseteq> \<^bold>G \<phi>"
    using A `dom \<pi> \<subseteq> \<^bold>G \<phi>` by blast+
  hence "ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w"
    by (unfold_locales; insert \<G>_elements[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>`] finite_\<Sigma> bounded_w) 
  have 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<Turnstile>\<^sub>P Rep q}"
    using 1 unfolding `dom \<pi>\<^sub>\<A> = dom \<pi>` \<pi>\<^sub>\<A>_def by simp
  hence 3: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> the (\<pi>\<^sub>\<A> \<chi>) < semi_mojmir_def.max_rank \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>))"
    using ltl_FG_to_rabin.smallest_accepting_rank_properties(6)[OF `ltl_FG_to_rabin \<Sigma> (dom \<pi>\<^sub>\<A>) w`] by fastforce

  --\<open>Use correctness of the translation of individual accepting pairs\<close>
  have Acc: "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
    using \<A>_mojmir_accept_to_Acc[OF finite_\<Sigma> bounded_w _ `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>`] \<G>_elements[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>`] 
    using 1 2[of "G _"] 3[of "G _"] \<MM>_Accept[of "G _"] ltl.sel(8) by metis 
  have M: "accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w" 
    using unfold_optimisation_correct_M[OF `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>` `dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>` 2 B] C
    using `dom \<pi>\<^sub>\<UU> = dom \<pi>\<^sub>\<A>` by blast+

  show ?lhs
    using Acc 3 `dom \<pi>\<^sub>\<A> \<subseteq> \<^bold>G \<phi>` combine_rabin_pairs_UNIV[OF M combine_rabin_pairs]
    by (simp only: ltl_to_generalized_rabin.simps accept\<^sub>G\<^sub>R_def fst_conv snd_conv ltl_to_generalised_rabin_acceptance_condition.simps) blast
qed

end

end

thm unfold_optimisation_correct

end