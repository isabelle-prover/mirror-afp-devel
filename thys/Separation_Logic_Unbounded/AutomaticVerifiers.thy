section \<open>Fractional Predicates and Magic Wands in Automatic Separation Logic Verifiers\<close>

text \<open>This section corresponds to Section 5 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theory AutomaticVerifiers
  imports FixedPoint WandProperties
begin

context logic
begin

subsection \<open>Syntactic multiplication\<close>

text \<open>The following definition corresponds to Figure 6 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

fun syn_mult :: "'b \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> ('a, 'b, 'c, 'd) assertion" where
  "syn_mult \<pi> (Star A B) = Star (syn_mult \<pi> A) (syn_mult \<pi> B)"
| "syn_mult \<pi> (Wand A B) = Wand (syn_mult \<pi> A) (syn_mult \<pi> B)"
| "syn_mult \<pi> (Or A B) = Or (syn_mult \<pi> A) (syn_mult \<pi> B)"
| "syn_mult \<pi> (And A B) = And (syn_mult \<pi> A) (syn_mult \<pi> B)"
| "syn_mult \<pi> (Imp A B) = Imp (syn_mult \<pi> A) (syn_mult \<pi> B)"
| "syn_mult \<pi> (Mult \<alpha> A) = syn_mult (smult \<alpha> \<pi>) A"
| "syn_mult \<pi> (Exists x A) = Exists x (syn_mult \<pi> A)"
| "syn_mult \<pi> (Forall x A) = Forall x (syn_mult \<pi> A)"
| "syn_mult \<pi> (Wildcard A) = Wildcard A"
| "syn_mult \<pi> A = Mult \<pi> A"

definition div_state where
  "div_state \<pi> \<sigma> = (SOME r. \<sigma> = \<pi> \<odot> r)"

lemma div_state_ok:
  "\<sigma> = \<pi> \<odot> (div_state \<pi> \<sigma>)"
  by (metis (mono_tags) div_state_def someI_ex unique_inv)

text \<open>The following theorem corresponds to Theorem 6 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem syn_sen_mult_same:
  "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> A \<longleftrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Mult \<pi> A"
proof (induct A arbitrary: \<sigma> \<pi> s)
  case (Exists x A)
  show ?case (is "?A \<longleftrightarrow> ?B")
  proof
    show "?B \<Longrightarrow> ?A"
      using Exists.hyps by auto
    show "?A \<Longrightarrow> ?B"
      using Exists.hyps by fastforce
  qed
next
  case (Forall x A)
  then show ?case
    by (metis dot_forall1 dot_forall2 entails_def sat.simps(9) syn_mult.simps(8))
next
  case (Star A B)
  show ?case (is "?P \<longleftrightarrow> ?Q")
  proof
    show "?P \<Longrightarrow> ?Q"
    proof -
      assume ?P
      then obtain a b where "a, s, \<Delta> \<Turnstile> syn_mult \<pi> A" "b, s, \<Delta> \<Turnstile> syn_mult \<pi> B"
      "Some \<sigma> = a \<oplus> b" by auto
      then obtain "a, s, \<Delta> \<Turnstile> Mult \<pi> A" "b, s, \<Delta> \<Turnstile> Mult \<pi> B"
        using Star.hyps(1) Star.hyps(2) Star.prems by blast
      then show ?Q
        by (meson \<open>Some \<sigma> = a \<oplus> b\<close> dot_star2 entails_def sat.simps(2))
    qed
    assume ?Q
    then obtain a b where "a, s, \<Delta> \<Turnstile> Mult \<pi> A" "b, s, \<Delta> \<Turnstile> Mult \<pi> B" "Some \<sigma> = a \<oplus> b"
      by (meson dot_star1 entails_def sat.simps(2))
    then show ?P
      using Star.hyps(1) Star.hyps(2) Star.prems by force
  qed
next
  case (Mult p A)
  show ?case (is "?P \<longleftrightarrow> ?Q")
  proof
    show "?P \<Longrightarrow> ?Q"
    proof -
      assume ?P
      then have "\<sigma>, s, \<Delta> \<Turnstile> syn_mult (smult p \<pi>) A" by auto
      then have "\<sigma>, s, \<Delta> \<Turnstile> Mult (smult p \<pi>) A"
        using Mult.hyps by blast
      then show ?Q
        by (metis dot_mult2 logic.entails_def logic_axioms smult_comm)
    qed
    assume ?Q
    then obtain a where "a, s, \<Delta> \<Turnstile> A" "\<sigma> = \<pi> \<odot> (p \<odot> a)" by auto
    then show ?P
      using Mult.hyps double_mult smult_comm by auto
  qed
next
  case (Wand A B)
  show ?case (is "?P \<longleftrightarrow> ?Q")
  proof
    show "?P \<Longrightarrow> ?Q"
    proof -
      assume "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> (Wand A B)"
      then have "\<sigma>, s, \<Delta> \<Turnstile> Wand (syn_mult \<pi> A) (syn_mult \<pi> B)"
        by auto
      moreover have "div_state \<pi> \<sigma>, s, \<Delta> \<Turnstile> Wand A B"
      proof (rule sat_wand)
        fix a b
        assume "a, s, \<Delta> \<Turnstile> A \<and> Some b = div_state \<pi> \<sigma> \<oplus> a"
        then have "Some (\<pi> \<odot> b) = \<sigma> \<oplus> (\<pi> \<odot> a)"
          using div_state_ok plus_mult by presburger
        moreover have "\<pi> \<odot> a, s, \<Delta> \<Turnstile> Mult \<pi> A"
          using \<open>a, s, \<Delta> \<Turnstile> A \<and> Some b = div_state \<pi> \<sigma> \<oplus> a\<close> by auto
        then have "\<pi> \<odot> a, s, \<Delta> \<Turnstile> syn_mult \<pi> A"
          using Wand.hyps(1) Wand.prems by blast
        then have "\<pi> \<odot> b, s, \<Delta> \<Turnstile> syn_mult \<pi> B"
          using \<open>\<sigma>, s, \<Delta> \<Turnstile> Wand (syn_mult \<pi> A) (syn_mult \<pi> B)\<close> calculation by auto
        ultimately show "b, s, \<Delta> \<Turnstile> B"
          by (metis Wand.hyps(2) Wand.prems can_divide sat.simps(1))
      qed
      then show "\<sigma>, s, \<Delta> \<Turnstile> Mult \<pi> (Wand A B)"
        by (metis div_state_ok sat.simps(1))
    qed
    assume "\<sigma>, s, \<Delta> \<Turnstile> Mult \<pi> (Wand A B)"
    then have "div_state \<pi> \<sigma>, s, \<Delta> \<Turnstile> Wand A B"
      by (metis div_state_ok can_divide sat.simps(1))
    have "\<sigma>, s, \<Delta> \<Turnstile> Wand (syn_mult \<pi> A) (syn_mult \<pi> B)"
    proof (rule sat_wand)
      fix a b assume "a, s, \<Delta> \<Turnstile> syn_mult \<pi> A \<and> Some b = \<sigma> \<oplus> a"
      then have "Some (div_state \<pi> b) = div_state \<pi> \<sigma> \<oplus> div_state \<pi> a"
        by (metis div_state_ok plus_mult unique_inv)
      then have "div_state \<pi> b, s, \<Delta> \<Turnstile> B"
        by (metis (no_types, lifting) Wand.hyps(1) \<open>a, s, \<Delta> \<Turnstile> syn_mult \<pi> A \<and> Some b = \<sigma> \<oplus> a\<close> \<open>div_state \<pi> \<sigma>, s, \<Delta> \<Turnstile> Wand A B\<close> div_state_ok logic.can_divide logic_axioms sat.simps(1) sat.simps(3))
      then show "b, s, \<Delta> \<Turnstile> syn_mult \<pi> B"
        using Wand.hyps(2) div_state_ok sat.simps(1) by blast
    qed
    then show "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> (Wand A B)"
      by simp
  qed
next
  case (And A B)
  show ?case (is "?P \<longleftrightarrow> ?Q")
  proof
    show "?P \<Longrightarrow> ?Q"
    proof -
      assume ?P
      then obtain "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> A" "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> B"
        by auto
      then show ?Q
        by (meson And.hyps(1) And.hyps(2) dot_and2 logic.entails_def logic_axioms sat.simps(7))
    qed
    assume ?Q then show ?P
      using And.hyps(1) And.hyps(2) And.prems by auto
  qed
next
  case (Imp A B)
  show ?case (is "?P \<longleftrightarrow> ?Q")
  proof
    show "?P \<Longrightarrow> ?Q"
      by (metis Imp.hyps(1) Imp.hyps(2) sat.simps(1) sat.simps(5) syn_mult.simps(5) unique_inv)
    assume ?Q then show ?P
      by (metis Imp.hyps(1) Imp.hyps(2) Imp.prems can_divide sat.simps(1) sat.simps(5) syn_mult.simps(5))
  qed
next
  case (Wildcard A)
  then show ?case
    by (metis DotWild entails_def equivalent_def syn_mult.simps(9))
qed (auto)



subsection \<open>Monotonicity and fixed point\<close>

(* Bool means positive *)
fun pos_neg_rec_call :: "bool \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "pos_neg_rec_call b Pred \<longleftrightarrow> b"
| "pos_neg_rec_call b (Mult _ A) \<longleftrightarrow> pos_neg_rec_call b A"
| "pos_neg_rec_call b (Exists _ A) \<longleftrightarrow> pos_neg_rec_call b A"
| "pos_neg_rec_call b (Forall _ A) \<longleftrightarrow> pos_neg_rec_call b A"
| "pos_neg_rec_call b (Star A B) \<longleftrightarrow> pos_neg_rec_call b A \<and> pos_neg_rec_call b B"
| "pos_neg_rec_call b (Or A B) \<longleftrightarrow> pos_neg_rec_call b A \<and> pos_neg_rec_call b B"
| "pos_neg_rec_call b (And A B) \<longleftrightarrow> pos_neg_rec_call b A \<and> pos_neg_rec_call b B"
| "pos_neg_rec_call b (Wand A B) \<longleftrightarrow> pos_neg_rec_call (\<not> b) A \<and> pos_neg_rec_call b B"
| "pos_neg_rec_call b (Imp A B) \<longleftrightarrow> pos_neg_rec_call (\<not> b) A \<and> pos_neg_rec_call b B"
| "pos_neg_rec_call _ (Sem _) \<longleftrightarrow> True"
| "pos_neg_rec_call b (Bounded A) \<longleftrightarrow> pos_neg_rec_call b A"
| "pos_neg_rec_call b (Wildcard A) \<longleftrightarrow> pos_neg_rec_call b A"


lemma pos_neg_rec_call_mono:
  assumes "pos_neg_rec_call b A"
  shows "(b \<longrightarrow> monotonic (applies_eq A)) \<and> (\<not> b \<longrightarrow> non_increasing (applies_eq A))"
  using assms
proof (induct A arbitrary: b)
  case (Exists x A)
  then show ?case
    by (meson mono_exists non_increasing_exists pos_neg_rec_call.simps(3))
next
  case (Forall x A)
  then show ?case
    by (meson mono_forall non_increasing_forall pos_neg_rec_call.simps(4))
next
  case (Sem x)
  then show ?case
    by (metis applies_eq.simps mem_Collect_eq mono_sem non_increasingI sat.simps(4) smaller_interp_def subsetI)
next
  case (Mult x1a A)
  then show ?case
    using mono_mult non_increasing_mult pos_neg_rec_call.simps(2) by blast
next
  case (Star A1 A2)
  then show ?case
    by (metis mono_star non_inc_star pos_neg_rec_call.simps(5))
next
  case (Wand A1 A2)
  then show ?case
    by (metis mono_wand non_increasing_wand pos_neg_rec_call.simps(8))
next
  case (Or A1 A2)
  then show ?case
    by (metis mono_or non_increasing_or pos_neg_rec_call.simps(6))
next
  case (And A1 A2)
  then show ?case
    by (metis mono_and non_increasing_and pos_neg_rec_call.simps(7))
next
  case (Imp A1 A2)
  then show ?case
    by (metis mono_imp non_increasing_imp pos_neg_rec_call.simps(9))
next
  case Pred
  then show ?case
    using mono_interp pos_neg_rec_call.simps(1) by blast
next
  case (Bounded A)
  then show ?case
    using mono_bounded non_increasing_bounded pos_neg_rec_call.simps(11) by blast
next
  case (Wildcard A)
  then show ?case
    using mono_wild non_increasing_wild pos_neg_rec_call.simps(12) by blast
qed


text \<open>The following theorem corresponds to Theorem 7 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem exists_lfp_gfp:
  assumes "pos_neg_rec_call True A"
  shows "\<sigma>, s, LFP (applies_eq A) \<Turnstile> A \<longleftrightarrow> \<sigma> \<in> LFP (applies_eq A) s"
    and "\<sigma>, s, GFP (applies_eq A) \<Turnstile> A \<longleftrightarrow> \<sigma> \<in> GFP (applies_eq A) s"
   apply (metis LFP_is_FP applies_eq.simps assms mem_Collect_eq pos_neg_rec_call_mono)
  by (metis GFP_is_FP applies_eq.simps assms mem_Collect_eq pos_neg_rec_call_mono)





subsection \<open>Combinability\<close>

definition combinable_sem :: "(('d \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "combinable_sem B \<longleftrightarrow> (\<forall>a b x s \<alpha> \<beta>. B s a \<and> B s b \<and> sadd \<alpha> \<beta> = one \<and> Some x = \<alpha> \<odot> a \<oplus> \<beta> \<odot> b  \<longrightarrow> B s x)"

fun wf_assertion :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "wf_assertion Pred \<longleftrightarrow> True"
| "wf_assertion (Sem B) \<longleftrightarrow> combinable_sem B"
| "wf_assertion (Mult _ A) \<longleftrightarrow> wf_assertion A"
| "wf_assertion (Forall _ A) \<longleftrightarrow> wf_assertion A"
| "wf_assertion (Exists x A) \<longleftrightarrow> wf_assertion A \<and> (\<forall>\<Delta>. unambiguous \<Delta> A x)"
| "wf_assertion (Star A B) \<longleftrightarrow> wf_assertion A \<and> wf_assertion B"
| "wf_assertion (And A B) \<longleftrightarrow> wf_assertion A \<and> wf_assertion B"
| "wf_assertion (Wand A B) \<longleftrightarrow> wf_assertion B"
| "wf_assertion (Imp A B) \<longleftrightarrow> pure A \<and> wf_assertion B"
| "wf_assertion (Wildcard A) \<longleftrightarrow> wf_assertion A"
| "wf_assertion _ \<longleftrightarrow> False"



lemma wf_implies_combinable:
  assumes "wf_assertion A"
      and "sem_combinable \<Delta>"
  shows "combinable \<Delta> A"
  using assms
proof (induct A)
  case (Exists x A)
  then show ?case
    by (meson combinable_exists wf_assertion.simps(5))
next
  case (Forall x A)
  then show ?case
    by (meson combinable_forall wf_assertion.simps(4))
next
  case (Sem B)
  show ?case
  proof (rule combinableI)
    fix a b p q x \<sigma> s
    assume "a, s, \<Delta> \<Turnstile> Sem B \<and> b, s, \<Delta> \<Turnstile> Sem B \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
    then show "x, s, \<Delta> \<Turnstile> Sem B"
      by (metis Sem.prems(1) combinable_sem_def sat.simps(4) wf_assertion.simps(2))
  qed
next
  case (Mult x1a A)
  then show ?case
    using combinable_mult wf_assertion.simps(3) by blast
next
  case (Star A1 A2)
  then show ?case
    using combinable_star wf_assertion.simps(6) by blast
next
  case (Wand A1 A2)
  then show ?case
    using combinable_wand wf_assertion.simps(8) by blast
next
  case (And A1 A2)
  then show ?case
    using combinable_and by auto
next
  case (Imp A1 A2)
  then show ?case
    using combinable_imp by auto
next
  case Pred
  show ?case
  proof (rule combinableI)
    fix a b p q x \<sigma> s
    assume "a, s, \<Delta> \<Turnstile> Pred \<and> b, s, \<Delta> \<Turnstile> Pred \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
    then show "x, s, \<Delta> \<Turnstile> Pred"
      using assms(2) sat.simps(10) sem_combinableE by metis
  qed
next
  case (Wildcard A)
  then show ?case
    using combinable_wildcard wf_assertion.simps(10) by blast
qed (auto)





subsection \<open>Theorems\<close>

text \<open>The following two theorems correspond to the rules shown in Section 5.1 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem apply_wand:
  "Star (syn_mult \<pi> A) (Mult \<pi> (Wand A B)), \<Delta> \<turnstile> syn_mult \<pi> B"
proof (rule entailsI)
  fix \<sigma> s
  assume asm: "\<sigma>, s, \<Delta> \<Turnstile> Star (syn_mult \<pi> A) (Mult \<pi> (Wand A B))"
  then obtain x y where "Some \<sigma> = x \<oplus> y" "x, s, \<Delta> \<Turnstile> syn_mult \<pi> A" "y, s, \<Delta> \<Turnstile> Mult \<pi> (Wand A B)"
    by auto
  then have "y, s, \<Delta> \<Turnstile> Wand (syn_mult \<pi> A) (syn_mult \<pi> B)"
    by (metis syn_mult.simps(2) syn_sen_mult_same)
  then show "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> B"
    using \<open>Some \<sigma> = x \<oplus> y\<close> \<open>x, s, \<Delta> \<Turnstile> syn_mult \<pi> A\<close> \<open>y, s, \<Delta> \<Turnstile> Wand (syn_mult \<pi> A) (syn_mult \<pi> B)\<close> commutative by auto
qed

theorem package_wand:
  assumes "Star F (syn_mult \<pi> A), \<Delta> \<turnstile> syn_mult \<pi> B"
  shows "F, \<Delta> \<turnstile> Mult \<pi> (Wand A B)"
  by (metis adjunct2 assms entails_def syn_mult.simps(2) syn_sen_mult_same)

text \<open>The following four theorems correspond to the rules shown in Section 5.2 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem fold_lfp:
  assumes "pos_neg_rec_call True A"
    shows "syn_mult \<pi> A, LFP (applies_eq A) \<turnstile> Mult \<pi> Pred"
  by (simp add: assms entails_def exists_lfp_gfp(1) syn_sen_mult_same)

theorem unfold_lfp:
  assumes "pos_neg_rec_call True A"
    shows "Mult \<pi> Pred, LFP (applies_eq A) \<turnstile> syn_mult \<pi> A"
  by (simp add: assms entails_def exists_lfp_gfp(1) syn_sen_mult_same)

theorem fold_gfp:
  assumes "pos_neg_rec_call True A"
    shows "syn_mult \<pi> A, GFP (applies_eq A) \<turnstile> Mult \<pi> Pred"
  by (simp add: assms entails_def exists_lfp_gfp(2) syn_sen_mult_same)

theorem unfold_gfp:
  assumes "pos_neg_rec_call True A"
    shows "Mult \<pi> Pred, GFP (applies_eq A) \<turnstile> syn_mult \<pi> A"
  by (simp add: assms entails_def exists_lfp_gfp(2) syn_sen_mult_same)

text \<open>The following theorems correspond to the rule shown in Section 5.3 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theorem wf_assertion_combinable_lfp:
  assumes "wf_assertion A"
      and "pos_neg_rec_call True A"
    shows "sem_combinable (LFP (applies_eq A))"
proof -
  let ?f = "\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
  have "set_closure_property ?f (LFP (applies_eq A))"
  proof (rule FP_preserves_set_closure_property(2))
    show "monotonic (applies_eq A)"
      using assms(2) pos_neg_rec_call_mono by blast
    fix \<Delta> :: "('d, 'c, 'a) interp" assume asm0: "set_closure_property ?f \<Delta>"
    then have "sem_combinable \<Delta>"
      by (metis combinable_set_closure)
    then show "set_closure_property ?f (applies_eq A \<Delta>)"
      by (metis assms(1) combinable_set_closure sem_combinable_equiv wf_implies_combinable)
  qed
  then show ?thesis using combinable_set_closure by metis
qed


theorem wf_assertion_combinable_gfp:
  assumes "wf_assertion A"
      and "pos_neg_rec_call True A"
    shows "sem_combinable (GFP (applies_eq A))"
proof -
  let ?f = "\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b}"
  have "set_closure_property ?f (GFP (applies_eq A))"
  proof (rule FP_preserves_set_closure_property(1))
    show "monotonic (applies_eq A)"
      using assms(2) pos_neg_rec_call_mono by blast
    fix \<Delta> :: "('d, 'c, 'a) interp" assume asm0: "set_closure_property ?f \<Delta>"
    then have "sem_combinable \<Delta>"
      by (metis combinable_set_closure)
    then show "set_closure_property ?f (applies_eq A \<Delta>)"
      by (metis assms(1) combinable_set_closure sem_combinable_equiv wf_implies_combinable)
  qed
  then show ?thesis using combinable_set_closure by metis
qed

theorem wf_combine:
  assumes "wf_assertion A"
      and "pos_neg_rec_call True A"
    shows "Star (Mult \<alpha> Pred) (Mult \<beta> Pred), LFP (applies_eq A) \<turnstile> Mult (sadd \<alpha> \<beta>) Pred"
    and "Star (Mult \<alpha> Pred) (Mult \<beta> Pred), GFP (applies_eq A) \<turnstile> Mult (sadd \<alpha> \<beta>) Pred"
  apply (metis assms(1) assms(2) logic.combinable_def logic.wf_implies_combinable logic_axioms wf_assertion.simps(1) wf_assertion_combinable_lfp)
  by (metis assms(1) assms(2) logic.combinable_def logic.wf_implies_combinable logic_axioms wf_assertion.simps(1) wf_assertion_combinable_gfp)

end

end