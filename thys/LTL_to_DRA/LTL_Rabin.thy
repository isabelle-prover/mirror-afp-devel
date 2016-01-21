(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Translation from LTL to (Deterministic Transitions-Based) Generalised Rabin Automata\<close>

theory LTL_Rabin
  imports Main Mojmir_Rabin Logical_Characterization
begin

subsection \<open>Preliminary Facts\<close>

lemma run_af_G_letter_abs_eq_Abs_af_G_letter:
  "run \<up>af\<^sub>G (Abs \<phi>) w i = Abs (run af_G_letter \<phi> w i)"
  by (induction i) (simp, metis af_G_abs.f_foldl_abs.abs_eq af_G_abs.f_foldl_abs_alt_def run_foldl af_G_letter_abs_def)

lemma finite_reach_af:
  "finite (reach \<Sigma> \<up>af (Abs \<phi>))"
proof (cases "\<Sigma> \<noteq> {}")
  case True
    thus ?thesis
      using af_abs.finite_abs_reach unfolding af_abs.abs_reach_def reach_foldl_def[OF True]
      using finite_subset[of "{foldl \<up>af (Abs \<phi>) w |w. set w \<subseteq> \<Sigma>}" "{foldl \<up>af(Abs \<phi>) w |w. True}"] 
      unfolding af_letter_abs_def
      by (blast)
qed (simp add: reach_def)

lemma ltl_semi_mojmir: 
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  shows "semi_mojmir \<Sigma> \<up>af\<^sub>G (Abs \<psi>) w"
proof 
  fix \<psi>
  have nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
    using assms by auto
  show "finite (reach \<Sigma> \<up>af\<^sub>G (Abs \<psi>))" (is "finite ?A")
    using af_G_abs.finite_abs_reach finite_subset[where A = ?A, where B = "lift_ltl_transformer.abs_reach af_G_letter (Abs \<psi>)"]
    unfolding af_G_abs.abs_reach_def af_G_letter_abs_def reach_foldl_def[OF nonempty_\<Sigma>] by blast
qed (insert assms, auto)

subsection \<open>Single Secondary Automaton\<close>

locale ltl_FG_to_rabin_def = 
  fixes 
    \<Sigma> :: "'a set set"
  fixes
    \<phi> :: "'a ltl"
  fixes
    \<G> :: "'a ltl set"
  fixes 
    w :: "'a set word"
begin

sublocale mojmir_to_rabin_def \<Sigma> "\<up>af\<^sub>G" "Abs \<phi>" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}" .

--\<open>Import abbreviations from parent locale to simplify terms\<close>
abbreviation "\<delta>\<^sub>R \<equiv> step"
abbreviation "q\<^sub>R \<equiv> initial"
abbreviation "Acc\<^sub>R j \<equiv> (fail\<^sub>R \<union> merge\<^sub>R j, succeed\<^sub>R j)"
abbreviation "max_rank\<^sub>R \<equiv> max_rank"
abbreviation "smallest_accepting_rank\<^sub>R \<equiv> smallest_accepting_rank"
abbreviation "accept\<^sub>R' \<equiv> accept"
abbreviation "\<S>\<^sub>R \<equiv> \<S>"

lemma Rep_token_run_af:
  "Rep (token_run x n) \<equiv>\<^sub>P af\<^sub>G \<phi> (w [x \<rightarrow> n])"
proof -
  have "token_run x n = Abs (af\<^sub>G \<phi> ((suffix x w) [0 \<rightarrow> (n - x)]))"
    by (simp add: subsequence_def run_foldl; metis af_G_abs.f_foldl_abs.abs_eq af_G_abs.f_foldl_abs_alt_def af_G_letter_abs_def) 
  hence "Rep (token_run x n) \<equiv>\<^sub>P af\<^sub>G \<phi> ((suffix x w) [0 \<rightarrow> (n - x)])"
    using ltl\<^sub>P_abs_rep ltl_prop_equiv_quotient.abs_eq_iff by auto
  thus ?thesis
    unfolding ltl_prop_equiv_def subsequence_shift by (cases "x \<le> n"; simp add: subsequence_def)
qed

end

locale ltl_FG_to_rabin = ltl_FG_to_rabin_def +
  assumes 
    wellformed_\<G>: "Only_G \<G>"
  assumes
    bounded_w: "range w \<subseteq> \<Sigma>"
  assumes
    finite_\<Sigma>: "finite \<Sigma>"
begin
  
sublocale mojmir_to_rabin \<Sigma> "\<up>af\<^sub>G" "Abs \<phi>" w "{q. \<G> \<Turnstile>\<^sub>P Rep q}"
proof
  show "\<And>q \<nu>. q \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q} \<Longrightarrow> \<up>af\<^sub>Gq \<nu> \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q}"
    using wellformed_\<G> af_G_letter_sat_core_lifted by auto
  have nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
    using bounded_w by blast
  show "finite (reach \<Sigma> \<up>af\<^sub>G(Abs \<phi>))" (is "finite ?A")
    using af_G_abs.finite_abs_reach finite_subset[where A = ?A, where B = "lift_ltl_transformer.abs_reach af_G_letter (Abs \<phi>)"]
    unfolding af_G_abs.abs_reach_def af_G_letter_abs_def reach_foldl_def[OF nonempty_\<Sigma>] by blast
qed (insert finite_\<Sigma> bounded_w)

lemma ltl_to_rabin_correct_exposed':
  "\<PP>\<^sub>\<infinity> \<phi> \<G> w \<longleftrightarrow> accept"
proof -
  {
    fix i
    have "(\<exists>j. \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (map w [i + 0..<i + (j - i)])) = \<PP> \<phi> \<G> w i"
        by (auto simp add: subsequence_def, metis add_diff_cancel_left' le_Suc_ex nat_le_linear upt_conv_Nil )
    hence "(\<exists>j. \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j])) \<longleftrightarrow> (\<exists>j. \<G> \<Turnstile>\<^sub>P run af_G_letter \<phi> (suffix i w) (j-i))" 
      (is "?l \<longleftrightarrow> _") 
      unfolding run_foldl using subsequence_shift subsequence_def by metis
    also
    have "\<dots> \<longleftrightarrow> (\<exists>j. \<G> \<Turnstile>\<^sub>P Rep (run \<up>af\<^sub>G(Abs \<phi>) (suffix i w) (j-i)))"
      using Quotient3_ltl_prop_equiv_quotient[THEN Quotient3_rep_abs] 
      unfolding ltl_prop_equiv_def run_af_G_letter_abs_eq_Abs_af_G_letter by blast
    also
    have "\<dots> \<longleftrightarrow> (\<exists>j. token_run i j \<in> {q. \<G> \<Turnstile>\<^sub>P Rep q})"
      by simp
    also
    have "\<dots> \<longleftrightarrow> token_succeeds i"
      (is "_ \<longleftrightarrow> ?r")
      unfolding token_succeeds_def by auto
    finally
    have "?l \<longleftrightarrow> ?r" .
  }
  thus "?thesis"
    by (simp only: almost_all_eventually_provable_def accept_def)
qed

lemma ltl_to_rabin_correct_exposed:
  "\<PP>\<^sub>\<infinity> \<phi> \<G> w \<longleftrightarrow> accept\<^sub>R (\<delta>\<^sub>R, q\<^sub>R, {Acc\<^sub>R i | i. i < max_rank\<^sub>R}) w"  
  unfolding ltl_to_rabin_correct_exposed' mojmir_accept_iff_rabin_accept ..

--\<open>Import lemmas from parent locale to simplify assumptions\<close>
lemmas max_rank_lowerbound = max_rank_lowerbound
lemmas state_rank_step_foldl = state_rank_step_foldl
lemmas smallest_accepting_rank_properties = smallest_accepting_rank_properties 
lemmas wellformed_\<R> = wellformed_\<R>

end

fun ltl_to_rabin
where
  "ltl_to_rabin \<Sigma> \<phi> \<G> = (ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> \<phi>, ltl_FG_to_rabin_def.q\<^sub>R \<phi>, {ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> \<phi> \<G> i | i. i < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> \<phi>})"

context
  fixes 
    \<Sigma> :: "'a set set"
  assumes 
    finite_\<Sigma>: "finite \<Sigma>"
begin

lemma ltl_to_rabin_correct:
  assumes "range w \<subseteq> \<Sigma>"
  shows "w \<Turnstile> F G \<phi> = (\<exists>\<G> \<subseteq> \<^bold>G (G \<phi>). G \<phi> \<in> \<G> \<and> (\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w))"
proof -
  have "\<And>\<G> \<psi>. \<G> \<subseteq> \<^bold>G (G \<phi>) \<Longrightarrow> G \<psi> \<in> \<G> \<Longrightarrow> (\<PP>\<^sub>\<infinity> \<psi> \<G> w \<longleftrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w)" 
  proof -
    fix \<G> \<psi>
    assume "\<G> \<subseteq> \<^bold>G (G \<phi>)" "G \<psi> \<in> \<G>"
    then interpret ltl_FG_to_rabin \<Sigma> \<psi> \<G>
      using finite_\<Sigma> assms G_nested_propos_alt_def 
      by (unfold_locales; auto)
    show "(\<PP>\<^sub>\<infinity> \<psi> \<G> w \<longleftrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w)" 
      using ltl_to_rabin_correct_exposed by simp
  qed
  thus ?thesis
    using \<G>_elements[of _ "G \<phi>"] \<G>_finite[of _ "G \<phi>"]
    unfolding ltl_FG_logical_characterization G_nested_propos.simps 
    by meson
qed

end

subsubsection \<open>LTL-to-Mojmir Lemmas\<close> 
                        
lemma \<F>_eq_\<S>:
  assumes finite_\<Sigma>: "finite \<Sigma>"
  assumes bounded_w: "range w \<subseteq> \<Sigma>"
  assumes "closed \<G> w"
  assumes "G \<psi> \<in> \<G>"
  shows "\<forall>\<^sub>\<infinity>j. (\<forall>S. (S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j \<and> \<G> \<subseteq> S) \<longleftrightarrow> (\<forall>q. q \<in> (ltl_FG_to_rabin_def.\<S>\<^sub>R \<Sigma> \<psi> \<G> w j) \<longrightarrow> S \<Turnstile>\<^sub>P Rep q))"
proof -
  let ?F = "{q. \<G> \<Turnstile>\<^sub>P Rep q}"

  def k \<equiv> "the (threshold \<psi> w \<G>)"
  hence "threshold \<psi> w \<G> = Some k"
    using assms unfolding threshold.simps index.simps almost_all_eventually_provable_def  by simp

  have "Only_G \<G>"
    using assms G_nested_propos_alt_def by blast
  then interpret ltl_FG_to_rabin \<Sigma> \<psi> \<G> w
    using finite_\<Sigma> bounded_w by (unfold_locales, auto)

  have "accept"
    using ltl_to_rabin_correct_exposed' assms by blast
  then obtain i where "smallest_accepting_rank = Some i"
    unfolding smallest_accepting_rank_def by force
  
  (* Wait until succeeding states can be recognised *)
  obtain n\<^sub>1 where "\<And>m q. m \<ge> n\<^sub>1 \<Longrightarrow> ((\<exists>x \<in> configuration q m. token_succeeds x) \<longrightarrow> q \<in> \<S> m) \<and> (q \<in> \<S> m \<longrightarrow> (\<forall>x \<in> configuration q m. token_succeeds x))"
    using succeeding_states[OF `smallest_accepting_rank = Some i`] unfolding MOST_nat_le by blast
  (* Wait until all "early" succeeding tokens reached the final states *)
  obtain n\<^sub>2 where "\<And>x. x < k \<Longrightarrow> token_succeeds x \<Longrightarrow> token_run x n\<^sub>2 \<in> ?F"
    by (induction k) (simp, metis token_stays_in_final_states add.commute le_neq_implies_less not_less not_less_eq token_succeeds_def) 
  
  def n \<equiv> "Max {n\<^sub>1, n\<^sub>2, k}"
  
  (* Prove properties for the larger n *)
  {
    fix m q
    assume "n \<le> m"
    hence "n\<^sub>1 \<le> m"
      unfolding n_def by simp
    hence "((\<exists>x \<in> configuration q m. token_succeeds x) \<longrightarrow> q \<in> \<S> m) \<and> (q \<in> \<S> m \<longrightarrow> (\<forall>x \<in> configuration q m. token_succeeds x))"
      using `\<And>m q. m \<ge> n\<^sub>1 \<Longrightarrow> ((\<exists>x \<in> configuration q m. token_succeeds x) \<longrightarrow> q \<in> \<S> m) \<and> (q \<in> \<S> m \<longrightarrow> (\<forall>x \<in> configuration q m. token_succeeds x))` by blast
  }
  hence n_def_1: "\<And>m q. m \<ge> n \<Longrightarrow> ((\<exists>x \<in> configuration q m. token_succeeds x) \<longrightarrow> q \<in> \<S> m) \<and> (q \<in> \<S> m \<longrightarrow> (\<forall>x \<in> configuration q m. token_succeeds x))"
    by presburger
  have n_def_2: "\<And>x m. x < k \<Longrightarrow> m \<ge> n \<Longrightarrow> token_succeeds x \<Longrightarrow> token_run x m \<in> ?F"
    using `\<And>x. x < k \<Longrightarrow> token_succeeds x \<Longrightarrow> token_run x n\<^sub>2 \<in> ?F` Max.coboundedI[of "{n\<^sub>1, n\<^sub>2, k}"] 
    using token_stays_in_final_states[of _ n\<^sub>2] le_Suc_ex unfolding n_def by force
  
  {
    fix S m
    assume "n \<le> m"
    hence "k \<le> m" "n \<le> Suc m"
      using n_def by simp+

    {
      assume "S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> m" "\<G> \<subseteq> S"
      hence "\<And>x. k \<le> x \<Longrightarrow> x \<le> Suc m \<Longrightarrow> S \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [x \<rightarrow> m])"
        unfolding And_prop_entailment \<F>_def k_def[symmetric] subsequence_def
        using `k \<le> m` by auto
      fix q assume "q \<in> \<S> m"

      have "S \<Turnstile>\<^sub>P Rep q"
      proof (cases "q \<in> ?F")
        case False
          moreover
          then obtain j where "state_rank q m = Some j" and "j \<ge> i"
            using `q \<in> \<S> m` `smallest_accepting_rank = Some i` by force
          then obtain x where "x \<in> configuration q m" and "token_run x m = q" 
            by force
          moreover
          hence "token_succeeds x" 
            using n_def_1[OF `n \<le> m`] `q \<in> \<S> m` by blast
          ultimately
          have "S \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [x \<rightarrow> m])"
            using `\<And>x. k \<le> x \<Longrightarrow> x \<le> Suc m \<Longrightarrow> S \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [x \<rightarrow> m])`[of x] n_def_2[OF _ `n \<le> m`] by fastforce
          thus ?thesis
            using Rep_token_run_af unfolding `token_run x m = q`[symmetric] ltl_prop_equiv_def by simp
       qed (insert `\<G> \<subseteq> S`, blast)
    }
    
    moreover

    {
      assume "\<And>q. q \<in> \<S> m \<Longrightarrow> S \<Turnstile>\<^sub>P Rep q"
      hence "\<And>q. q \<in> ?F \<Longrightarrow> S \<Turnstile>\<^sub>P Rep q" 
        by simp
      have "\<G> \<subseteq> S"
      proof 
        fix x assume "x \<in> \<G>"
        with `Only_G \<G>` show "x \<in> S"
          using `\<And>q. q \<in> ?F \<Longrightarrow> S \<Turnstile>\<^sub>P Rep q`[of "Abs x"] by auto
      qed

      { 
        fix x assume "k \<le> x" "x \<le> m"
        def q \<equiv> "token_run x m"

        hence "token_succeeds x"
          using threshold_properties[OF `threshold \<psi> w \<G> = Some k`] `x \<ge> k` Rep_token_run_af  
          unfolding token_succeeds_def ltl_prop_equiv_def by blast
        hence "q \<in> \<S> m"
          using n_def_1[OF `n \<le> m`, of q] `x \<le> m`
          unfolding q_def configuration.simps by blast
        hence "S \<Turnstile>\<^sub>P Rep q"
          by (rule `\<And>q. q \<in> \<S> m \<Longrightarrow> S \<Turnstile>\<^sub>P Rep q`)
        hence "S \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [x \<rightarrow> m])"
          using Rep_token_run_af unfolding q_def ltl_prop_equiv_def by simp
      }
      hence "\<forall>x \<in> (set (map (\<lambda>i. af\<^sub>G \<psi> (w [i \<rightarrow> m])) [k..<Suc m])). S \<Turnstile>\<^sub>P x"
        unfolding set_map set_upt by fastforce
      hence "S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> m" and "\<G> \<subseteq> S"
        unfolding \<F>_def And_prop_entailment[of S] k_def[symmetric] 
        using `k \<le> m` `\<G> \<subseteq> S` by simp+ 
    }
    ultimately
    have "(S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> m \<and> \<G> \<subseteq> S) \<longleftrightarrow> (\<forall>q. q \<in> \<S> m \<longrightarrow> S \<Turnstile>\<^sub>P Rep q)"
      by blast
  }
  thus ?thesis
    unfolding MOST_nat_le by blast
qed

lemma \<F>_eq_\<S>_generalized:
  assumes finite_\<Sigma>: "finite \<Sigma>"
  assumes bounded_w: "range w \<subseteq> \<Sigma>"
  assumes "closed \<G> w"
  shows "\<forall>\<^sub>\<infinity>j. \<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> (\<forall>S. (S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j \<and> \<G> \<subseteq> S) \<longleftrightarrow> (\<forall>q. q \<in> (ltl_FG_to_rabin_def.\<S>\<^sub>R \<Sigma> \<psi> \<G>) w j \<longrightarrow> S \<Turnstile>\<^sub>P Rep q))"
proof -
  have "Only_G \<G>" and "finite \<G>"
    using assms by simp+
  show ?thesis
    using almost_all_commutative''[OF `finite \<G>` `Only_G \<G>`] \<F>_eq_\<S>[OF assms] by simp
qed

subsection \<open>Product of Secondary Automata\<close>

context
  fixes 
    \<Sigma> :: "'a set set"
begin

fun product_initial_state :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" ("\<iota>\<^sub>\<times>")
where
  "\<iota>\<^sub>\<times> K q\<^sub>m = (\<lambda>k. if k \<in> K then Some (q\<^sub>m k) else None)" 

fun combine_pairs :: "(('a, 'b) transition set \<times> ('a, 'b) transition set) set \<Rightarrow> (('a, 'b) transition set \<times> ('a, 'b) transition set set)"
where
  "combine_pairs P = (\<Union>(fst ` P), snd ` P)"

fun combine_pairs' :: "(('a ltl \<Rightarrow> ('a ltl_prop_equiv_quotient \<Rightarrow> nat option) option, 'a set) transition set \<times> ('a ltl \<Rightarrow> ('a ltl_prop_equiv_quotient \<Rightarrow> nat option) option, 'a set) transition set) set \<Rightarrow> (('a ltl \<Rightarrow> ('a ltl_prop_equiv_quotient \<Rightarrow> nat option) option, 'a set) transition set \<times> ('a ltl \<Rightarrow> ('a ltl_prop_equiv_quotient \<Rightarrow> nat option) option, 'a set) transition set set)"
where
  "combine_pairs' P = (\<Union>(fst ` P), snd ` P)"

lemma combine_pairs_prop: 
  "(\<forall>P \<in> \<P>. accepting_pair\<^sub>R \<delta> q\<^sub>0 P w) = accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (combine_pairs \<P>) w"
  by auto

lemma combine_pairs2:
  "combine_pairs \<P> \<in> \<alpha> \<Longrightarrow> (\<And>P. P \<in> \<P> \<Longrightarrow> accepting_pair\<^sub>R \<delta> q\<^sub>0 P w ) \<Longrightarrow> accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w"
  using combine_pairs_prop[of \<P> \<delta> q\<^sub>0 w] by fastforce

lemma combine_pairs'_prop: 
  "(\<forall>P \<in> \<P>. accepting_pair\<^sub>R \<delta> q\<^sub>0 P w) = accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (combine_pairs' \<P>) w"
  by auto

fun ltl_FG_to_generalized_rabin :: "'a ltl \<Rightarrow> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat, 'a set) generalized_rabin_automaton" ("\<P>")
where
  "ltl_FG_to_generalized_rabin \<phi> = (
    \<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>)), 
    \<iota>\<^sub>\<times> (\<^bold>G (G \<phi>)) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>)),
    {combine_pairs' {embed_pair \<chi> (ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> (theG \<chi>) \<G> (\<pi> \<chi>)) | \<chi>. \<chi> \<in> \<G>} 
      | \<G> \<pi>. \<G> \<subseteq> \<^bold>G (G \<phi>) \<and> G \<phi> \<in> \<G> \<and> (\<forall>\<chi>. \<pi> \<chi> < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>))})"

context
  assumes 
    finite_\<Sigma>: "finite \<Sigma>"
begin

lemma ltl_FG_to_generalized_rabin_wellformed:
  "finite (reach \<Sigma> (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))))"
proof (cases "\<Sigma> = {}")
  case False
    have "finite (reach \<Sigma> (\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>))) (fst (snd (\<P> \<phi>))))"
    proof (rule finite_reach_product, goal_cases)
      case 1
        show ?case
          using G_nested_finite(1) by (auto simp add: dom_def LTL_Rabin.product_initial_state.simps) 
    next
      case (2 x)
        hence "the (fst (snd (\<P> \<phi>)) x) = ltl_FG_to_rabin_def.q\<^sub>R (theG x)" 
          by (auto simp add: LTL_Rabin.product_initial_state.simps) 
        thus ?case
          using ltl_FG_to_rabin.wellformed_\<R>[unfolded ltl_FG_to_rabin_def, of "{}" _ \<Sigma> "theG x"] finite_\<Sigma> False by fastforce
    qed
    thus ?thesis
      by fastforce
qed (simp add: reach_def)

theorem ltl_FG_to_generalized_rabin_correct:
  assumes "range w \<subseteq> \<Sigma>"
  shows "w \<Turnstile> F G \<phi> = accept\<^sub>G\<^sub>R (\<P> \<phi>) w"
  (is "?lhs = ?rhs")
proof
  def r \<equiv> "run\<^sub>t (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) w"

  have [intro]: "\<And>i. w i \<in> \<Sigma>" and "\<Sigma> \<noteq> {}"
    using assms by auto

  {
    let ?S = "(reach \<Sigma> (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) ) \<times> \<Sigma> \<times> (reach \<Sigma> (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))))"

    have "\<And>n. r n \<in> ?S"
      unfolding run\<^sub>t.simps run_foldl reach_foldl_def[OF `\<Sigma> \<noteq> {}`] r_def by fastforce 
    hence "range r \<subseteq> ?S" and  "finite ?S"
      using ltl_FG_to_generalized_rabin_wellformed assms `finite \<Sigma>` by (blast, fast)
  }
  hence "finite (range r)"
    by (blast dest: finite_subset)

  {
    assume ?lhs
    then obtain \<G> where "\<G> \<subseteq> \<^bold>G (G \<phi>)" and "G \<phi> \<in> \<G>" and "\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w"
      unfolding ltl_to_rabin_correct[OF `finite \<Sigma>` `range w \<subseteq> \<Sigma>`] unfolding ltl_to_rabin.simps by auto
    
    note \<G>_properties[OF `\<G> \<subseteq> \<^bold>G (G \<phi>)`]
    hence "ltl_FG_to_rabin \<Sigma> \<G> w"
      using `finite \<Sigma>` `range w \<subseteq> \<Sigma>` unfolding ltl_FG_to_rabin_def by auto

    def \<pi> \<equiv> "\<lambda>\<psi>. if \<psi> \<in> \<G> then the (ltl_FG_to_rabin_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<psi>) \<G> w) else 0"
    let ?P' = "{\<^bold>\<upharpoonleft>\<^sub>\<chi> (ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> (theG \<chi>) \<G> (\<pi> \<chi>)) | \<chi>. \<chi> \<in> \<G>}"
     
    have "\<forall>P \<in> ?P'. accepting_pair\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w"
    proof 
      fix P
      assume "P \<in> ?P'"
      then obtain \<chi> where P_def: "P = \<^bold>\<upharpoonleft>\<^sub>\<chi> (ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> (theG \<chi>) \<G> (\<pi> \<chi>))"
        and "\<chi> \<in> \<G>"
        by blast
      hence "\<exists>\<chi>'. \<chi> = G \<chi>'"
        using `\<G> \<subseteq> \<^bold>G (G \<phi>)` G_nested_propos_alt_def by auto
      
      interpret ltl_FG_to_rabin \<Sigma> "theG \<chi>" \<G> w
        by (insert `ltl_FG_to_rabin \<Sigma> \<G> w`)
     
      def r\<^sub>\<chi> \<equiv> "run\<^sub>t \<delta>\<^sub>\<R> q\<^sub>\<R> w"
      
      moreover

      have "accept" and "accept\<^sub>R (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {Acc\<^sub>\<R> j | j. j < max_rank}) w" 
        using `\<chi> \<in> \<G>` `\<exists>\<chi>'. \<chi> = G \<chi>'` `\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w` 
        using mojmir_accept_iff_rabin_accept by auto

      hence "smallest_accepting_rank\<^sub>\<R> = Some (\<pi> \<chi>)"
        unfolding \<pi>_def smallest_accepting_rank_def Mojmir_rabin_smallest_accepting_rank[symmetric] 
        using `\<chi> \<in> \<G>` by simp
      hence "accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> (\<pi> \<chi>)) w"
        using `accept\<^sub>R (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {Acc\<^sub>\<R> j | j. j < max_rank}) w` LeastI[of "\<lambda>i. accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> i) w"] 
        by (auto simp add: smallest_accepting_rank\<^sub>\<R>_def)

      ultimately

      have "limit r\<^sub>\<chi> \<inter> fst (Acc\<^sub>\<R> (\<pi> \<chi>)) = {}" and "limit r\<^sub>\<chi> \<inter> snd (Acc\<^sub>\<R> (\<pi> \<chi>)) \<noteq> {}"
        by simp+

      moreover

      have 1: "(\<iota>\<^sub>\<times> (\<^bold>G (G \<phi>)) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>))) \<chi> = Some q\<^sub>\<R>"
        using `\<chi> \<in> \<G>` `\<G> \<subseteq> \<^bold>G (G \<phi>)` by (simp add: LTL_Rabin.product_initial_state.simps subset_iff) 
      have 2: "finite (range (run\<^sub>t 
              (\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>)))
              (\<iota>\<^sub>\<times> (\<^bold>G (G \<phi>)) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>))) 
              w))"
        using `finite (range r)`[unfolded r_def] by simp
      
      ultimately
      have "limit r \<inter> fst P = {}" and "limit r \<inter> snd P \<noteq> {}"
        using product_run_embed_limit_finiteness[OF 1 2] 
        unfolding r_def r\<^sub>\<chi>_def P_def by auto
      thus "accepting_pair\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w"
        unfolding P_def r_def by simp
    qed
    hence "accepting_pair\<^sub>G\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) (combine_pairs' ?P') w"  
      using combine_pairs'_prop by blast
    moreover
    {
      fix \<psi>
      assume "\<psi> \<in> \<G>"
      hence "\<exists>\<chi>. \<psi> = G \<chi>" 
        using `\<G> \<subseteq> \<^bold>G (G \<phi>)` G_nested_propos_alt_def by auto

      interpret ltl_FG_to_rabin \<Sigma> "theG \<psi>" \<G> w
        by (insert `ltl_FG_to_rabin \<Sigma> \<G> w`)

      have "accept"
        using `\<psi> \<in> \<G>` `\<exists>\<chi>. \<psi> = G \<chi>` `\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w`  mojmir_accept_iff_rabin_accept by auto
      then obtain i where "smallest_accepting_rank = Some i" 
        unfolding smallest_accepting_rank_def by fastforce
      hence "\<pi> \<psi> < max_rank\<^sub>R"
        using smallest_accepting_rank_properties \<pi>_def `\<psi> \<in> \<G>` by auto
    }
    hence "\<And>\<chi>. \<pi> \<chi> < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
      unfolding \<pi>_def using ltl_FG_to_rabin.max_rank_lowerbound[OF `ltl_FG_to_rabin \<Sigma> \<G> w`] by force
    hence "combine_pairs' ?P' \<in> snd (snd (\<P> \<phi>))"
      using `\<G> \<subseteq> \<^bold>G (G \<phi>)` `G \<phi> \<in> \<G>` by auto
    ultimately
    show ?rhs
      unfolding accept\<^sub>G\<^sub>R_simp2 ltl_FG_to_generalized_rabin.simps fst_conv snd_conv by blast
  }
  
  {
    assume ?rhs
    then obtain \<G> \<pi> P where "P = combine_pairs' {\<^bold>\<upharpoonleft>\<^sub>\<chi> (ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> (theG \<chi>) \<G> (\<pi> \<chi>)) | \<chi>. \<chi> \<in> \<G>}" (is "P = combine_pairs' ?P'") 
      and "accepting_pair\<^sub>G\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w"
      and "\<G> \<subseteq> \<^bold>G (G \<phi>)" and "G \<phi> \<in> \<G>" and "\<And>\<chi>. \<pi> \<chi> < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
      unfolding accept\<^sub>G\<^sub>R_def by auto
    moreover
    hence P'_def: "\<And>P. P \<in> ?P' \<Longrightarrow> accepting_pair\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w"
      using combine_pairs'_prop by meson
    note \<G>_properties[OF `\<G> \<subseteq> \<^bold>G (G \<phi>)`]
    hence "ltl_FG_to_rabin \<Sigma> \<G> w"
      using `finite \<Sigma>` `range w \<subseteq> \<Sigma>` unfolding ltl_FG_to_rabin_def by auto
    have "\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w"
    proof (rule+)
      fix \<psi>
      assume "G \<psi> \<in> \<G>"
      def \<chi> \<equiv> "G \<psi>" 
      def P \<equiv> "\<^bold>\<upharpoonleft>\<^sub>\<chi> (ltl_FG_to_rabin_def.Acc\<^sub>R \<Sigma> \<psi> \<G> (\<pi> \<chi>))"
      hence "\<chi> \<in> \<G>" and "theG \<chi> = \<psi>" 
        using \<chi>_def `G \<psi> \<in> \<G>` by simp+
      hence "P \<in> ?P'" 
        unfolding P_def by auto
      hence "accepting_pair\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w"
        using P'_def by blast

      interpret ltl_FG_to_rabin \<Sigma> \<psi> \<G> w
        by (insert `ltl_FG_to_rabin \<Sigma> \<G> w`)

      def r\<^sub>\<chi> \<equiv> "run\<^sub>t \<delta>\<^sub>\<R> q\<^sub>\<R> w"
      
      have "limit r \<inter> fst P = {}" and "limit r \<inter> snd P \<noteq> {}"
        using `accepting_pair\<^sub>R (fst (\<P> \<phi>)) (fst (snd (\<P> \<phi>))) P w` 
        unfolding r_def accepting_pair\<^sub>R_def by metis+

      moreover

      have 1: "(\<iota>\<^sub>\<times> (\<^bold>G (G \<phi>)) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>))) (G \<psi>) = Some q\<^sub>\<R>"
        using `G \<psi> \<in> \<G>` `\<G> \<subseteq> \<^bold>G (G \<phi>)` by (auto simp add: LTL_Rabin.product_initial_state.simps subset_iff)
      have 2: "finite (range (run\<^sub>t (\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>))) (\<iota>\<^sub>\<times> (\<^bold>G (G \<phi>)) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>)))  w))"
        using `finite (range r)`[unfolded r_def] by simp
      have "\<And>S. limit r \<inter> (\<Union> (\<upharpoonleft>\<^sub>\<chi> ` S)) = {} \<longleftrightarrow> limit r\<^sub>\<chi> \<inter> S = {}"
        using product_run_embed_limit_finiteness[OF 1 2] by (simp add: r_def r\<^sub>\<chi>_def \<chi>_def)

      ultimately
      have "limit r\<^sub>\<chi> \<inter> fst (Acc\<^sub>\<R> (\<pi> \<chi>)) = {}" and "limit r\<^sub>\<chi> \<inter> snd (Acc\<^sub>\<R> (\<pi> \<chi>)) \<noteq> {}"
        unfolding P_def fst_conv snd_conv embed_pair.simps by meson+
      hence "accepting_pair\<^sub>R \<delta>\<^sub>\<R> q\<^sub>\<R> (Acc\<^sub>\<R> (\<pi> \<chi>)) w"
        unfolding r\<^sub>\<chi>_def by simp 
      hence "accept\<^sub>R (\<delta>\<^sub>\<R>, q\<^sub>\<R>, {Acc\<^sub>\<R> j | j. j < max_rank}) w"
        using `\<And>\<chi>. \<pi> \<chi> < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)` `theG \<chi> = \<psi>` 
        unfolding accept\<^sub>R_simp accepting_pair\<^sub>R_def fst_conv snd_conv by blast 
      thus "accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w"
        by simp
    qed
    ultimately
    show ?lhs
      unfolding ltl_to_rabin_correct[OF `finite \<Sigma>` assms] by auto
  }
qed 

end

end

subsection \<open>Automaton Template\<close>

-- \<open>This locale provides the construction template for all composed constructions.\<close>

locale ltl_to_rabin_base_def =
  fixes
    \<delta> :: "'a ltl\<^sub>P \<Rightarrow> 'a set \<Rightarrow> 'a ltl\<^sub>P"
  fixes
    \<delta>\<^sub>M :: "'a ltl\<^sub>P \<Rightarrow> 'a set \<Rightarrow> 'a ltl\<^sub>P"
  fixes
    q\<^sub>0 :: "'a ltl \<Rightarrow> 'a ltl\<^sub>P"
  fixes 
    q\<^sub>0\<^sub>M :: "'a ltl \<Rightarrow> 'a ltl\<^sub>P"
  fixes
    M_fin :: "('a ltl \<rightharpoonup> nat) \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) transition set"
begin

-- \<open>Transition Function and Initial State\<close>

fun delta
where
  "delta \<Sigma> = \<delta> \<times> \<Delta>\<^sub>\<times> (semi_mojmir_def.step \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)"

fun initial
where
  "initial \<phi> = (q\<^sub>0 \<phi>, \<iota>\<^sub>\<times> (\<^bold>G \<phi>) (semi_mojmir_def.initial o q\<^sub>0\<^sub>M o theG))"

-- \<open>Acceptance Condition\<close>

definition max_rank_of
where
  "max_rank_of \<Sigma> \<psi> \<equiv> semi_mojmir_def.max_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<psi>))"

fun Acc_fin
where
  "Acc_fin \<Sigma> \<pi> \<chi> = \<Union>(embed_transition_snd ` \<Union>(embed_transition \<chi> ` 
     (mojmir_to_rabin_def.fail\<^sub>R \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}
     \<union> mojmir_to_rabin_def.merge\<^sub>R \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} (the (\<pi> \<chi>)))))"

fun Acc_inf
where
  "Acc_inf \<pi> \<chi> = \<Union>(embed_transition_snd ` \<Union>(embed_transition \<chi> ` 
    (mojmir_to_rabin_def.succeed\<^sub>R \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} (the (\<pi> \<chi>)))))"

abbreviation Acc
where
  "Acc \<Sigma> \<pi> \<chi> \<equiv> (Acc_fin \<Sigma> \<pi> \<chi>, Acc_inf \<pi> \<chi>)" 

fun rabin_pairs :: "'a set set \<Rightarrow> 'a ltl \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) generalized_rabin_condition"
where
  "rabin_pairs \<Sigma> \<phi> = {(M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}) 
    | \<pi>. dom \<pi> \<subseteq> \<^bold>G \<phi> \<and> (\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>)}"

fun ltl_to_generalized_rabin :: "'a set set \<Rightarrow> 'a ltl \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) generalized_rabin_automaton" ("\<A>")
where
  "\<A> \<Sigma> \<phi> = (delta \<Sigma>, initial \<phi>, rabin_pairs \<Sigma> \<phi>)"

end

locale ltl_to_rabin_base = ltl_to_rabin_base_def +
  fixes
    \<Sigma> :: "'a set set" 
  fixes
    w :: "'a set word"
  assumes
    finite_\<Sigma>: "finite \<Sigma>"
  assumes
    bounded_w: "range w \<subseteq> \<Sigma>"
  assumes
    M_fin_monotonic: "dom \<pi> = dom \<pi>' \<Longrightarrow> (\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) \<le> the (\<pi>' \<chi>)) \<Longrightarrow> M_fin \<pi> \<subseteq> M_fin \<pi>'"
  assumes 
    finite_reach': "finite (reach \<Sigma> \<delta> (q\<^sub>0 \<phi>))"
  assumes
    mojmir_to_rabin: "Only_G \<G> \<Longrightarrow> mojmir_to_rabin \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M \<psi>) w {q. \<G> \<up>\<Turnstile>\<^sub>P q}" 
begin 

lemma semi_mojmir:
  "semi_mojmir \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M \<psi>) w"
  using mojmir_to_rabin[of "{}"] by (simp add: mojmir_to_rabin_def mojmir_def)

lemma finite_reach:
  "finite (reach \<Sigma> (delta \<Sigma>) (initial \<phi>))"
  apply (cases "\<Sigma> = {}")
    apply (simp add: reach_def)
    apply (simp only: ltl_to_rabin_base_def.initial.simps ltl_to_rabin_base_def.delta.simps)
    apply (rule finite_reach_simple_product[OF finite_reach' finite_reach_product])
      apply (insert mojmir_to_rabin[of "{}", unfolded mojmir_to_rabin_def mojmir_def])
      apply (auto simp add: dom_def intro: G_nested_finite semi_mojmir.wellformed_\<R>) 
  done

lemma run_limit_not_empty:
  "limit (run\<^sub>t (delta \<Sigma>) (initial \<phi>) w) \<noteq> {}"
  by (metis emptyE finite_\<Sigma> limit_nonemptyE finite_reach bounded_w run\<^sub>t_finite) 

lemma run_properties:
  fixes \<phi>
  defines "r \<equiv> run (delta \<Sigma>) (initial \<phi>) w"
  shows "fst (r i) = foldl \<delta> (q\<^sub>0 \<phi>) (w [0 \<rightarrow> i])"
    and "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (snd (r i) \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w q i"
proof -
  have sm: "\<And>\<psi>. semi_mojmir \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M \<psi>) w"
    using mojmir_to_rabin[of "{}"] unfolding mojmir_to_rabin_def mojmir_def by simp
  have "r i = (foldl \<delta> (q\<^sub>0 \<phi>) (w [0 \<rightarrow> i]), 
    \<lambda>\<chi>. if \<chi> \<in> \<^bold>G \<phi> then Some (\<lambda>\<psi>. foldl (semi_mojmir_def.step \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>))) (semi_mojmir_def.initial (q\<^sub>0\<^sub>M (theG \<chi>))) (map w [0..< i]) \<psi>) else None)"
  proof (induction i)
    case (Suc i) 
      show ?case 
        unfolding r_def run_foldl upt_Suc less_eq_nat.simps if_True map_append foldl_append 
        unfolding Suc[unfolded r_def run_foldl] subsequence_def by auto
  qed (auto simp add: subsequence_def r_def)
  hence state_run: "r i = (foldl \<delta> (q\<^sub>0 \<phi>) (w [0 \<rightarrow> i]), 
    \<lambda>\<chi>. if \<chi> \<in> \<^bold>G \<phi> then Some (\<lambda>\<psi>. semi_mojmir_def.state_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w \<psi> i) else None)"
    unfolding semi_mojmir.state_rank_step_foldl[OF sm] r_def by simp

  show "fst (r i) = foldl \<delta> (q\<^sub>0 \<phi>) (w [0 \<rightarrow> i])"
    using state_run by fastforce
  show "\<And>\<chi> q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (snd (r i) \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w q i"
    unfolding state_run by force
qed

lemma accept\<^sub>G\<^sub>R_I:
  assumes "accept\<^sub>G\<^sub>R (\<A> \<Sigma> \<phi>) w"
  obtains \<pi> where "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
    and "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>, UNIV) w"
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
proof -
  from assms obtain P where "P \<in> rabin_pairs \<Sigma> \<phi>" and "accepting_pair\<^sub>G\<^sub>R (delta \<Sigma>) (initial \<phi>) P w"
    unfolding accept\<^sub>G\<^sub>R_def ltl_to_generalized_rabin.simps fst_conv snd_conv by blast 
  moreover
  then obtain \<pi> where "dom \<pi> \<subseteq> \<^bold>G \<phi>" and "\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
    and P_def: "P = (M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>})"
    by auto
  have "limit (run\<^sub>t (delta \<Sigma>) (initial \<phi>) w) \<inter> UNIV \<noteq> {}"
    using run_limit_not_empty assms by simp
  ultimately
  have "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>, UNIV) w" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
    unfolding P_def accepting_pair\<^sub>G\<^sub>R_simp accepting_pair\<^sub>R_simp by blast+ (* Slow... *)
  thus ?thesis
    using that `dom \<pi> \<subseteq> \<^bold>G \<phi>` `\<forall>\<chi> \<in> dom \<pi>. the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>` by blast
qed

context
  fixes
    \<phi> :: "'a ltl"
begin

context
  fixes 
    \<psi> :: "'a ltl"
  fixes 
    \<pi> :: "'a ltl \<rightharpoonup> nat"
  assumes
    "G \<psi> \<in> dom \<pi>"
  assumes
    "dom \<pi> \<subseteq> \<^bold>G \<phi>"
begin

interpretation \<MM>: mojmir_to_rabin \<Sigma> \<delta>\<^sub>M "q\<^sub>0\<^sub>M \<psi>" w "{q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
  by (metis mojmir_to_rabin `dom \<pi> \<subseteq> \<^bold>G \<phi>` \<G>_elements)

lemma Acc_property:
  "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> (G \<psi>)) w \<longleftrightarrow> accepting_pair\<^sub>R \<MM>.\<delta>\<^sub>\<R> \<MM>.q\<^sub>\<R> (\<MM>.Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) w"
  (is "?Acc = ?Acc\<^sub>\<R>")
proof -  
  def r \<equiv> "run\<^sub>t (delta \<Sigma>) (initial \<phi>) w" and r\<^sub>\<psi> \<equiv> "run\<^sub>t \<MM>.\<delta>\<^sub>\<R> \<MM>.q\<^sub>\<R> w"
  hence "finite (range r)"
    using run\<^sub>t_finite[OF finite_reach] `range w \<subseteq> \<Sigma>` `finite \<Sigma>`
    by (blast dest: finite_subset) 

  have "\<And>S. limit r\<^sub>\<psi> \<inter> S = {} \<longleftrightarrow> limit r \<inter> \<Union>(embed_transition_snd ` (\<Union> ((embed_transition (G \<psi>)) ` S))) = {}"
  proof -
    fix S
    have 1: "snd (initial \<phi>) (G \<psi>) = Some \<MM>.q\<^sub>\<R>"
      using `G \<psi> \<in> dom \<pi>` `dom \<pi> \<subseteq> \<^bold>G \<phi>` by auto
    have 2: "finite (range (run\<^sub>t (\<Delta>\<^sub>\<times> (semi_mojmir_def.step \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)) (snd (initial \<phi>)) w))"
      using `finite (range r)` r_def comp_apply by (auto intro: product_run_finite_snd)
    show "?thesis S"
      unfolding r_def r\<^sub>\<psi>_def product_run_embed_limit_finiteness[OF 1 2, unfolded ltl.sel comp_def, symmetric] 
      using product_run_embed_limit_finiteness_snd[OF  `finite (range r)`[unfolded r_def delta.simps initial.simps]]
      by (simp del: simple_product.simps product.simps product_initial_state.simps add: comp_def) fast
  qed
  hence "limit r \<inter> fst (Acc \<Sigma> \<pi> (G \<psi>)) = {} \<and> limit r \<inter> snd (Acc \<Sigma> \<pi> (G \<psi>)) \<noteq> {} 
     \<longleftrightarrow> limit r\<^sub>\<psi> \<inter> fst (\<MM>.Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) = {} \<and> limit r\<^sub>\<psi> \<inter> snd (\<MM>.Acc\<^sub>\<R> (the (\<pi> (G \<psi>)))) \<noteq> {}"
    unfolding fst_conv snd_conv by simp
  thus "?Acc \<longleftrightarrow> ?Acc\<^sub>\<R>" 
    unfolding r\<^sub>\<psi>_def r_def accepting_pair\<^sub>R_def by blast 
qed

lemma Acc_to_rabin_accept:
  "\<lbrakk>accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> (G \<psi>)) w; the (\<pi> (G \<psi>)) < \<MM>.max_rank\<rbrakk> \<Longrightarrow> accept\<^sub>R \<MM>.\<R> w"
  unfolding Acc_property by auto

lemma Acc_to_mojmir_accept:
  "\<lbrakk>accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> (G \<psi>)) w; the (\<pi> (G \<psi>)) < \<MM>.max_rank\<rbrakk> \<Longrightarrow> \<MM>.accept"
  using Acc_to_rabin_accept unfolding \<MM>.mojmir_accept_iff_rabin_accept by auto

lemma rabin_accept_to_Acc:
  "\<lbrakk>accept\<^sub>R \<MM>.\<R> w; \<pi> (G \<psi>) = \<MM>.smallest_accepting_rank\<rbrakk> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> (G \<psi>)) w"
  unfolding Acc_property \<MM>.Mojmir_rabin_smallest_accepting_rank 
  using \<MM>.smallest_accepting_rank\<^sub>\<R>_properties \<MM>.smallest_accepting_rank\<^sub>\<R>_def  
  by (metis (no_types, lifting) option.sel)

lemma mojmir_accept_to_Acc:
  "\<lbrakk>\<MM>.accept; \<pi> (G \<psi>) = \<MM>.smallest_accepting_rank\<rbrakk> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> (G \<psi>)) w"
  unfolding \<MM>.mojmir_accept_iff_rabin_accept by (blast dest: rabin_accept_to_Acc)

end

lemma normalize_\<pi>:
  assumes dom_subset: "dom \<pi> \<subseteq> \<^bold>G \<phi>"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
  assumes "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>, UNIV) w"
  assumes "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
  obtains \<pi>\<^sub>\<A> where "dom \<pi> = dom \<pi>\<^sub>\<A>"
    and "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> \<pi>\<^sub>\<A> \<chi> = mojmir_def.smallest_accepting_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<up>\<Turnstile>\<^sub>P q}"
    and "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w" 
    and "\<And>\<chi>. \<chi> \<in> dom \<pi>\<^sub>\<A> \<Longrightarrow> accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
proof -
  def \<G> \<equiv> "dom \<pi>"
  note \<G>_properties[OF dom_subset]

  def \<pi>\<^sub>\<A> \<equiv> "(\<lambda>\<chi>.  mojmir_def.smallest_accepting_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}) |` \<G>"

  moreover
  
  {
    fix \<chi> assume "\<chi> \<in> dom \<pi>"
  
    interpret \<MM>: mojmir_to_rabin \<Sigma> \<delta>\<^sub>M "q\<^sub>0\<^sub>M (theG \<chi>)" w "{q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      by (metis mojmir_to_rabin `dom \<pi> \<subseteq> \<^bold>G \<phi>` \<G>_elements)
  
    from `\<chi> \<in> dom \<pi>` have "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
      using assms(4) by blast
    hence "accepting_pair\<^sub>R \<MM>.\<delta>\<^sub>\<R> \<MM>.q\<^sub>\<R> (\<MM>.Acc\<^sub>\<R> (the (\<pi> \<chi>))) w" 
      by (metis `\<chi> \<in> dom \<pi>` Acc_property[OF _ dom_subset] `Only_G (dom \<pi>)` ltl.sel(8))
    moreover
    hence "accept\<^sub>R (\<MM>.\<delta>\<^sub>\<R>, \<MM>.q\<^sub>\<R>, {\<MM>.Acc\<^sub>\<R> j | j. j < \<MM>.max_rank}) w"
      using assms(2)[OF `\<chi> \<in> dom \<pi>`] unfolding max_rank_of_def by auto
    ultimately
    have "the (\<MM>.smallest_accepting_rank\<^sub>\<R>) \<le> the (\<pi> \<chi>)" and "\<MM>.smallest_accepting_rank \<noteq> None"
      using Least_le[of _ "the (\<pi> \<chi>)"] assms(2)[OF `\<chi> \<in> dom \<pi>`] \<MM>.mojmir_accept_iff_rabin_accept option.distinct(1) \<MM>.smallest_accepting_rank_def 
      by (simp add: \<MM>.smallest_accepting_rank\<^sub>\<R>_def)+
    hence "the (\<pi>\<^sub>\<A> \<chi>) \<le> the (\<pi> \<chi>)" and "\<chi> \<in> dom \<pi>\<^sub>\<A>"
      unfolding \<pi>\<^sub>\<A>_def dom_restrict using assms(2) `\<chi> \<in> dom \<pi>` by (simp add: \<MM>.Mojmir_rabin_smallest_accepting_rank \<G>_def, subst dom_def, simp add: \<G>_def)
  }
  
  hence "dom \<pi> = dom \<pi>\<^sub>\<A>"
    unfolding \<pi>\<^sub>\<A>_def dom_restrict \<G>_def by auto
  
  moreover
  
  note \<G>_properties[OF dom_subset, unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`]
  
  have "M_fin \<pi>\<^sub>\<A> \<subseteq> M_fin \<pi>" 
    using `dom \<pi> = dom \<pi>\<^sub>\<A>` by (simp add: M_fin_monotonic `\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi>\<^sub>\<A> \<chi>) \<le> the (\<pi> \<chi>)`)
  hence "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>\<^sub>\<A>, UNIV) w"
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
    hence X: "mojmir_def.accept \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q}"
      using assms(1,2,4) `dom \<pi> \<subseteq> \<^bold>G \<phi>` ltl.sel(8) Acc_to_mojmir_accept `dom \<pi> = dom \<pi>\<^sub>\<A>` by (metis max_rank_of_def)  
    have Y: "\<pi>\<^sub>\<A> (G theG \<chi>) = mojmir_def.smallest_accepting_rank \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) w {q. dom \<pi>\<^sub>\<A> \<up>\<Turnstile>\<^sub>P q}"
      using `G (theG \<chi>) \<in> dom \<pi>\<^sub>\<A>` `\<chi> = G (theG \<chi>)` \<pi>\<^sub>\<A>_def `dom \<pi> = dom \<pi>\<^sub>\<A>`[symmetric] by simp
    ultimately
    have "accepting_pair\<^sub>R (delta \<Sigma>) (initial \<phi>) (Acc \<Sigma> \<pi>\<^sub>\<A> \<chi>) w"
      using mojmir_accept_to_Acc[OF `G (theG \<chi>) \<in> dom \<pi>\<^sub>\<A>` `dom \<pi> \<subseteq> \<^bold>G \<phi>`[unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`] X[unfolded `dom \<pi> = dom \<pi>\<^sub>\<A>`] Y] by simp
  }

  ultimately

  show ?thesis
    using that[of \<pi>\<^sub>\<A>] restrict_in unfolding `dom \<pi> = dom \<pi>\<^sub>\<A>` \<G>_def 
    by (metis (no_types, lifting))
qed

end

end

subsection \<open>Generalized Deterministic Rabin Automaton\<close>

-- \<open>Instantiate Automaton Template\<close>

subsubsection \<open>Definition\<close>

fun M_fin :: "('a ltl \<rightharpoonup> nat) \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl \<rightharpoonup> 'a ltl\<^sub>P \<rightharpoonup> nat), 'a set) transition set"
where
  "M_fin \<pi> = {((\<phi>', m), \<nu>, p). 
    \<not>(\<forall>S. (\<forall>\<chi> \<in> dom \<pi>. S \<up>\<Turnstile>\<^sub>P Abs \<chi> \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (m \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<phi>')}"

locale ltl_to_rabin_af = ltl_to_rabin_base "\<up>af" "\<up>af\<^sub>G" "Abs" "Abs" M_fin begin

abbreviation "\<delta>\<^sub>\<A> \<equiv> delta"
abbreviation "\<iota>\<^sub>\<A> \<equiv> initial"
abbreviation "Acc\<^sub>\<A> \<equiv> Acc"
abbreviation "F\<^sub>\<A> \<equiv> rabin_pairs"
abbreviation "\<A> \<equiv> ltl_to_generalized_rabin"

subsubsection \<open>Correctness Theorem\<close>

theorem ltl_to_generalized_rabin_correct:
  "w \<Turnstile> \<phi> = accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin \<Sigma> \<phi>) w"
  (is "?lhs = ?rhs")
proof
  let ?\<Delta> = "\<delta>\<^sub>\<A> \<Sigma>"
  let ?q\<^sub>0 = "\<iota>\<^sub>\<A> \<phi>"
  let ?F = "F\<^sub>\<A> \<Sigma> \<phi>"
 
  --\<open>Preliminary facts needed by both proof directions\<close>
  def r \<equiv> "run\<^sub>t ?\<Delta> ?q\<^sub>0 w"
  have r_alt_def': "\<And>i. fst (fst (r i)) = Abs (af \<phi> (w [0 \<rightarrow> i]))"
    using run_properties(1) unfolding r_def run\<^sub>t.simps fst_conv
    by (metis af_abs.f_foldl_abs.abs_eq af_abs.f_foldl_abs_alt_def af_letter_abs_def) 
  have r_alt_def'': "\<And>\<chi> i q. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> the (snd (fst (r i)) \<chi>) q = semi_mojmir_def.state_rank \<Sigma> \<up>af\<^sub>G(Abs (theG \<chi>)) w q i"
    using run_properties(2) r_def by force
  have \<phi>'_def: "\<And>i. af \<phi> (w [0 \<rightarrow> i]) \<equiv>\<^sub>P Rep (fst (fst (r i)))"
    by (metis r_alt_def' Quotient3_ltl_prop_equiv_quotient ltl_prop_equiv_quotient.abs_eq_iff Quotient3_abs_rep)
 
  have "finite (range r)"
    using run\<^sub>t_finite[OF finite_reach] bounded_w finite_\<Sigma>
    by (simp add: r_def)

  --\<open>Assuming @{term "w \<Turnstile> \<phi>"} holds, we prove that @{term "ltl_to_generalized_rabin \<Sigma> \<phi>"} accepts @{term w}\<close>
  {
    assume ?lhs
    then obtain \<G> where "\<G> \<subseteq> \<^bold>G \<phi>" and "accept\<^sub>M \<phi> \<G> w" and "closed \<G> w"
      unfolding ltl_logical_characterization by blast
    
    note \<G>_properties[OF `\<G> \<subseteq> \<^bold>G \<phi>`]
    hence "ltl_FG_to_rabin \<Sigma> \<G> w"
      using finite_\<Sigma> bounded_w unfolding ltl_FG_to_rabin_def by auto

    def \<pi> \<equiv> "\<lambda>\<chi>. if \<chi> \<in> \<G> then (ltl_FG_to_rabin_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<chi>) \<G> w) else None"
    
    have \<MM>_accept: "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> ltl_FG_to_rabin_def.accept\<^sub>R' \<psi> \<G> w"
      using `closed \<G> w` `ltl_FG_to_rabin \<Sigma> \<G> w` ltl_FG_to_rabin.ltl_to_rabin_correct_exposed' by blast
    have "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w"
      using `closed \<G> w` unfolding ltl_FG_to_rabin.ltl_to_rabin_correct_exposed[OF `ltl_FG_to_rabin \<Sigma> \<G> w`] by simp

    {
      fix \<psi> assume "G \<psi> \<in> \<G>"
      interpret \<MM>: ltl_FG_to_rabin \<Sigma> \<psi> \<G> w
        by (insert `ltl_FG_to_rabin \<Sigma> \<G> w`)
      obtain i where "\<MM>.smallest_accepting_rank = Some i"
        using \<MM>_accept[OF `G \<psi> \<in> \<G>`]
        unfolding \<MM>.smallest_accepting_rank_def by fastforce
      hence "the (\<pi> (G \<psi>)) < \<MM>.max_rank" and "\<pi> (G \<psi>) \<noteq> None"
        using \<MM>.smallest_accepting_rank_properties `G \<psi> \<in> \<G>`
        unfolding \<pi>_def by simp+
    }
    hence "\<G> = dom \<pi>" and "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)" 
      using `Only_G \<G>` \<pi>_def unfolding dom_def by auto

    hence "(M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}) \<in> ?F"
      using `\<G> \<subseteq> \<^bold>G \<phi>` max_rank_of_def by auto

    moreover

    {
      have "accepting_pair\<^sub>R ?\<Delta> ?q\<^sub>0 (M_fin \<pi>, UNIV) w"
      proof -
        (* Wait until the Mojmir automata provide enough information *)
        obtain i where i_def: 
          "\<And>j. j \<ge> i \<Longrightarrow> \<forall>S. (\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)) \<longrightarrow> S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j])"
          using `accept\<^sub>M \<phi> \<G> w` unfolding MOST_nat_le accept\<^sub>M_def by blast
  
        (* Wait until the states with succeeding tokens are (prop.) equivalent to \<F> *)
        obtain i' where i'_def: 
          "\<And>j \<psi> S. j \<ge> i' \<Longrightarrow> G \<psi> \<in> \<G> \<Longrightarrow> (S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j \<and> \<G> \<subseteq> S) = (\<forall>q. q \<in> ltl_FG_to_rabin_def.\<S>\<^sub>R \<Sigma> \<psi> \<G> w j \<longrightarrow> S \<Turnstile>\<^sub>P Rep q)"
          using \<F>_eq_\<S>_generalized[OF finite_\<Sigma> bounded_w `closed \<G> w`] unfolding MOST_nat_le by presburger 
  
        (* From now on the run does not visit forbidden states *)  
        have "\<And>j. j \<ge> max i i' \<Longrightarrow> r j \<notin> M_fin \<pi>"
        proof - 
          fix j
          assume "j \<ge> max i i'"
  
          let ?\<phi>' = "fst (fst (r j))"
          let ?m = "snd (fst (r j))"
          
          {
            fix S
            assume "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> S \<up>\<Turnstile>\<^sub>P Abs \<chi>"
            hence assm1: "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi>"
              using ltl_prop_entails_abs.abs_eq by blast 
            assume "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> \<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G \<G> q"
            hence assm2: "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> \<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m \<chi>) q = Some j) \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (Rep q)"
              unfolding ltl_prop_entails_abs.rep_eq eval\<^sub>G_abs_def by simp
  
            {
              fix \<psi>
              assume "G \<psi> \<in> \<G>"
              hence "G \<psi> \<in> \<^bold>G \<phi>" and "\<G> \<subseteq> S"
                using `\<G> \<subseteq> \<^bold>G \<phi>` assm1 `Only_G \<G>` by (blast, force)
  
              interpret \<MM>: ltl_FG_to_rabin \<Sigma> \<psi> \<G> w
                by (unfold_locales; insert `Only_G \<G>` finite_\<Sigma> bounded_w; blast) 
    
              have "\<And>S. (\<And>q. q \<in> \<MM>.\<S> j \<Longrightarrow> S \<Turnstile>\<^sub>P Rep q) \<Longrightarrow> S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j"
                using i'_def `G \<psi> \<in> \<G>` `j \<ge> max i i'` max.bounded_iff by metis
              hence "\<And>S. (\<And>q. q \<in> Rep ` \<MM>.\<S> j \<Longrightarrow> S \<Turnstile>\<^sub>P q) \<Longrightarrow> S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j"
                by simp
  
              moreover
  
              have \<S>_def: "\<MM>.\<S> j = {q. \<G> \<Turnstile>\<^sub>P Rep q} \<union> {q . \<exists>j'. the (\<pi> (G \<psi>)) \<le> j' \<and> the (?m (G \<psi>)) q = Some j'}"
                using r_alt_def''[OF `G \<psi> \<in> \<^bold>G \<phi>`, unfolded ltl.sel, of j] `G \<psi> \<in> \<G>` by (simp add: \<pi>_def)
              have "\<And>q. \<G> \<Turnstile>\<^sub>P Rep q \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (Rep q)"
                using `\<G> \<subseteq> S` eval\<^sub>G_prop_entailment by blast
              hence "\<And>q. q \<in> Rep ` \<MM>.\<S> j \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> q"
                using assm2 `G \<psi> \<in> \<G>` unfolding \<S>_def by auto
  
              ultimately
              have "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)"
                by (rule eval\<^sub>G_respectfulness_generalized)
            }
            hence "S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j])"
              by (metis max.bounded_iff i_def `j \<ge> max i i'` `\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi>`)
            hence "S \<Turnstile>\<^sub>P Rep ?\<phi>'"
              using \<phi>'_def ltl_prop_equiv_def by blast
            hence "S \<up>\<Turnstile>\<^sub>P ?\<phi>'"
              using ltl_prop_entails_abs.rep_eq by blast 
          }
          thus "r j \<notin> M_fin \<pi>"
            using `\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)` `\<G> = dom \<pi>` by fastforce 
        qed
        hence "range (suffix (max i i') r) \<inter> M_fin \<pi> = {}"
          unfolding suffix_def by (blast intro: le_add1 elim: rangeE) 
        hence "limit r \<inter> M_fin \<pi> = {}"
          using limit_in_range_suffix[of r] by blast
        moreover
        have "limit r \<inter> UNIV \<noteq> {}"
          using `finite (range r)` by (simp, metis empty_iff limit_nonemptyE) 
        ultimately
        show ?thesis
          unfolding r_def accepting_pair\<^sub>R_simp ..
      qed
  
      moreover
  
      have "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> accepting_pair\<^sub>R ?\<Delta> ?q\<^sub>0 (Acc \<Sigma> \<pi> \<chi>) w"
      proof -
        fix \<chi> assume "\<chi> \<in> \<G>"
        then obtain \<psi> where "\<chi> = G \<psi>" and "G \<psi> \<in> \<G>" 
          using `Only_G \<G>` by fastforce 
        thus "?thesis \<chi>"
          using `\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> accept\<^sub>R (ltl_to_rabin \<Sigma> \<psi> \<G>) w`[OF `G \<psi> \<in> \<G>`]
          using rabin_accept_to_Acc[of \<psi> \<pi>] `G \<psi> \<in> \<G>` `\<G> \<subseteq> \<^bold>G \<phi>` `\<chi> \<in> \<G>`
          unfolding ltl.sel unfolding `\<chi> = G \<psi>` `\<G> = dom \<pi>` using \<pi>_def `\<G> = dom \<pi>` ltl.sel(8) unfolding ltl_prop_entails_abs.rep_eq ltl_to_rabin.simps
          by (metis (no_types, lifting) Collect_cong)
      qed
      ultimately
      have "accepting_pair\<^sub>G\<^sub>R ?\<Delta> ?q\<^sub>0 (M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}) w"
        unfolding accepting_pair\<^sub>G\<^sub>R_def accepting_pair\<^sub>R_def fst_conv snd_conv `\<G> = dom \<pi>` by blast
    }
    ultimately
    show ?rhs
      unfolding ltl_to_rabin_base_def.ltl_to_generalized_rabin.simps accept\<^sub>G\<^sub>R_def fst_conv snd_conv by blast
  }

  -- \<open>Assuming @{term "ltl_to_generalized_rabin \<Sigma> \<phi>"} accepts @{term w}, we prove that @{term "w \<Turnstile> \<phi>"} holds\<close>
  {
    assume ?rhs
    obtain \<pi>' where 0: "dom \<pi>' \<subseteq> \<^bold>G \<phi>"
      and 1: "\<And>\<chi>. \<chi> \<in> dom \<pi>' \<Longrightarrow> the (\<pi>' \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
      and 2: "accepting_pair\<^sub>R ?\<Delta> ?q\<^sub>0 (M_fin \<pi>', UNIV) w"
      and 3: "\<And>\<chi>. \<chi> \<in> dom \<pi>' \<Longrightarrow> accepting_pair\<^sub>R ?\<Delta> ?q\<^sub>0 (Acc \<Sigma> \<pi>' \<chi>) w"
      using accept\<^sub>G\<^sub>R_I[OF `?rhs`] unfolding max_rank_of_def by blast

    def \<G> \<equiv> "dom \<pi>'"
    hence "\<G> \<subseteq> \<^bold>G \<phi>"
     using `dom \<pi>' \<subseteq> \<^bold>G \<phi>` by simp

    moreover
    
    note \<G>_properties[OF `dom \<pi>' \<subseteq> \<^bold>G \<phi>`[unfolded \<G>_def[symmetric]]]
    ultimately
    have \<MM>_Accept: "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> ltl_FG_to_rabin_def.accept\<^sub>R' (theG \<chi>) \<G> w"
      using Acc_to_mojmir_accept[OF _ 0 3, of "theG _"] 1[of "G theG _", unfolded ltl.sel] \<G>_def 
      unfolding ltl_prop_entails_abs.rep_eq by (metis (no_types) ltl.sel(8)) 
 
    --\<open>Normalise @{text \<pi>} to the smallest accepting ranks\<close>
    obtain \<pi> where "dom \<pi>' = dom \<pi>"
      and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> \<pi> \<chi> = ltl_FG_to_rabin_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>) w"
      and "accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi>, UNIV) w" 
      and "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> accepting_pair\<^sub>R (\<delta>\<^sub>\<A> \<Sigma>) (\<iota>\<^sub>\<A> \<phi>) (Acc \<Sigma> \<pi> \<chi>) w"
      using normalize_\<pi>[OF 0 _ 2 3] 1 unfolding max_rank_of_def ltl_prop_entails_abs.rep_eq by blast

    have "ltl_FG_to_rabin \<Sigma> \<G> w"
      using finite_\<Sigma> bounded_w `Only_G \<G>` unfolding ltl_FG_to_rabin_def by auto

    have "closed \<G> w"
      using \<MM>_Accept `Only_G \<G>` ltl.sel(8) `finite \<G>` 
      unfolding ltl_FG_to_rabin.ltl_to_rabin_correct_exposed'[OF `ltl_FG_to_rabin \<Sigma> \<G> w`, symmetric] by fastforce

    moreover
    
    have "accept\<^sub>M \<phi> \<G> w"
    proof -
      (* Wait until the run gets trapped in the "good" states *)
      obtain i where i_def: "\<And>j. j \<ge> i \<Longrightarrow> r j \<notin> M_fin \<pi>"
        using `accepting_pair\<^sub>R  ?\<Delta> ?q\<^sub>0 (M_fin \<pi>, UNIV) w` limit_inter_empty[OF `finite (range r)`, of "M_fin \<pi>"]
        unfolding r_def[symmetric] MOST_nat_le accepting_pair\<^sub>R_def by auto
      
      (* Wait until the states with succeeding tokens are (prop.) equivalent to \<F> *)
      obtain i' where i'_def: 
        "\<And>j \<psi> S. j \<ge> i' \<Longrightarrow> G \<psi> \<in> \<G> \<Longrightarrow> (S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j \<and> \<G> \<subseteq> S) = (\<forall>q. q \<in> ltl_FG_to_rabin_def.\<S>\<^sub>R \<Sigma> \<psi> \<G> w j \<longrightarrow> S \<Turnstile>\<^sub>P Rep q)"
        using \<F>_eq_\<S>_generalized[OF finite_\<Sigma> bounded_w `closed \<G> w`] unfolding MOST_nat_le by presburger 

      {
        fix j S
        assume "j \<ge> max i i'"
        hence "j \<ge> i" and "j \<ge> i'"
          by simp+
        assume \<G>_def': "\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)"
        
        let ?\<phi>' = "fst (fst (r j))"
        let ?m = "snd (fst (r j))"
        
        have "\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi>"
          using \<G>_def' `\<G> \<subseteq> \<^bold>G \<phi>` unfolding G_nested_propos_alt_def by auto
        moreover

        (* Proof that the chosen S propositionally implies all succeeding states of the projected Mojmir automaton *)
        { 
          fix \<chi>
          assume "\<chi> \<in> \<G>"
          then obtain \<psi> where "\<chi> = G \<psi>" and "G \<psi> \<in> \<G>"
            using `Only_G \<G>` by auto
          hence "G \<psi> \<in> \<^bold>G \<phi>"
            using `\<G> \<subseteq> \<^bold>G \<phi>` by blast
          
          interpret \<MM>: ltl_FG_to_rabin \<Sigma> \<psi> \<G> w
            by (insert `ltl_FG_to_rabin \<Sigma> \<G> w`)

          {
            fix q
            assume "q \<in> \<MM>.\<S> j"
            hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)"
              using \<G>_def' `G \<psi> \<in> \<G>` by simp
            moreover 
            have "S \<supseteq> \<G>"
              using \<G>_def' `Only_G \<G>` by auto
            hence "\<And>x. x \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> x"
              using `Only_G \<G>` `S \<supseteq> \<G>` by fastforce
            moreover
            {
              fix S
              assume "\<And>x. x \<in> \<G> \<union> {\<F> \<psi> w \<G> j} \<Longrightarrow> S \<Turnstile>\<^sub>P x" 
              hence "\<G> \<subseteq> S" and "S \<Turnstile>\<^sub>P \<F> \<psi> w \<G> j"
                using `Only_G \<G>` by fastforce+
              hence "S \<Turnstile>\<^sub>P Rep q"
                using `q \<in> ltl_FG_to_rabin_def.\<S>\<^sub>R \<Sigma> \<psi> \<G> w j`
                using i'_def[OF `j \<ge> i'` `G \<psi> \<in> \<G>`] by blast
            }
            ultimately
            have "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (Rep q)"
              using eval\<^sub>G_respectfulness_generalized[of "\<G> \<union> {\<F> \<psi> w \<G> j}" "Rep q" S \<G>] 
              by blast
          }
          moreover 
          have "\<MM>.\<S> j = {q. \<G> \<Turnstile>\<^sub>P Rep q} \<union> {q . \<exists>j'. the \<MM>.smallest_accepting_rank \<le> j' \<and> the (?m (G \<psi>)) q = Some j'}"
            unfolding \<MM>.\<S>.simps using run_properties(2)[OF `G \<psi> \<in> \<^bold>G \<phi>`] r_def by simp
          ultimately
          have "\<And>q j. j \<ge> the (\<pi> \<chi>) \<Longrightarrow> the (?m \<chi>) q = Some j \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (Rep q)"
            using  `\<chi> \<in> \<G>`[unfolded \<G>_def `dom \<pi>' = dom \<pi>`]
            unfolding `\<chi> = G \<psi>` `\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> \<pi> \<chi> = ltl_FG_to_rabin_def.smallest_accepting_rank\<^sub>R \<Sigma> (theG \<chi>) (dom \<pi>) w`[OF `\<chi> \<in> \<G>`[unfolded \<G>_def `dom \<pi>' = dom \<pi>`], unfolded `\<chi> = G \<psi>`] ltl.sel(8)
            unfolding  `\<G> \<equiv> dom \<pi>'`[symmetric] `dom \<pi>' = dom \<pi>`[symmetric] by blast
        }
        moreover 

        have "(\<And>\<chi>. \<chi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P \<chi> \<and> (\<forall>q. \<forall>j' \<ge> the (\<pi> \<chi>). the (?m \<chi>) q = Some j' \<longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (Rep q))) \<Longrightarrow> S \<Turnstile>\<^sub>P Rep ?\<phi>'"
          apply (insert i_def[OF `j \<ge> i`])
          apply (simp add: eval\<^sub>G_abs_def ltl_prop_entails_abs.rep_eq case_prod_beta option.case_eq_if)
          apply (unfold `\<G> \<equiv> dom \<pi>'`[symmetric] `dom \<pi>' = dom \<pi>`[symmetric])
          apply meson
          done
        
        ultimately

        have "S \<Turnstile>\<^sub>P Rep ?\<phi>'"
          by fast
        hence "S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j])"
          using \<phi>'_def ltl_prop_equiv_def by blast
      }
      thus "accept\<^sub>M \<phi> \<G> w"
        unfolding accept\<^sub>M_def MOST_nat_le by blast
    qed

    ultimately
    show ?lhs
      using `\<G> \<subseteq> \<^bold>G \<phi>` ltl_logical_characterization by blast
  }
qed

end

fun ltl_to_generalized_rabin_af
where
  "ltl_to_generalized_rabin_af \<Sigma> \<phi> = ltl_to_rabin_base_def.ltl_to_generalized_rabin \<up>af \<up>af\<^sub>G Abs Abs M_fin \<Sigma> \<phi>"  

lemma ltl_to_generalized_rabin_af_wellformed:
  "finite \<Sigma> \<Longrightarrow> range w \<subseteq> \<Sigma> \<Longrightarrow> ltl_to_rabin_af \<Sigma> w"
  apply (unfold_locales)
  apply (auto simp add: af_G_letter_sat_core_lifted ltl_prop_entails_abs.rep_eq intro: finite_reach_af) 
  apply (meson le_trans ltl_semi_mojmir[unfolded semi_mojmir_def])+
  done

theorem ltl_to_generalized_rabin_af_correct:
  assumes "finite \<Sigma>"
  assumes "range w \<subseteq> \<Sigma>"
  shows "w \<Turnstile> \<phi> = accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin_af \<Sigma> \<phi>) w"
  using ltl_to_generalized_rabin_af_wellformed[OF assms, THEN ltl_to_rabin_af.ltl_to_generalized_rabin_correct] by simp

thm ltl_to_generalized_rabin_af_correct ltl_FG_to_generalized_rabin_correct

end