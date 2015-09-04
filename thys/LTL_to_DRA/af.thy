(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>af - Unfolding Functions\<close>

theory af
  imports Main "Aux/Words2" LTL
begin

subsection \<open>af\<close>

fun af_letter :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "af_letter true \<nu> = true"
| "af_letter false \<nu> = false"
| "af_letter p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_letter (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_letter (\<phi> and \<psi>) \<nu> = (af_letter \<phi> \<nu>) and (af_letter \<psi> \<nu>)"
| "af_letter (\<phi> or \<psi>) \<nu> = (af_letter \<phi> \<nu>) or (af_letter \<psi> \<nu>)"
| "af_letter (X \<phi>) \<nu> = \<phi>"
| "af_letter (G \<phi>) \<nu> = (G \<phi>) and (af_letter \<phi> \<nu>)"
| "af_letter (F \<phi>) \<nu> = (F \<phi>) or (af_letter \<phi> \<nu>)"
| "af_letter (\<phi> U \<psi>) \<nu> = (\<phi> U \<psi> and (af_letter \<phi> \<nu>)) or (af_letter \<psi> \<nu>)"

abbreviation af :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af")
where
  "af \<phi> w \<equiv> (foldl af_letter \<phi> w)"

lemma af_decompose:
  "af (\<phi> and \<psi>) w = (af \<phi> w) and (af \<psi> w)"
  "af (\<phi> or \<psi>) w = (af \<phi> w) or (af \<psi> w)"
  by (induction w rule: rev_induct) simp_all

lemma af_simps[simp]:
  "af true w = true"
  "af false w = false"
  "af (X \<phi>) (x#xs) = af \<phi> (xs)"
  by (induction w) simp_all

lemma af_F:
  "af (F \<phi>) w = Or (F \<phi> # map (af \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af (F \<phi>) (x # xs) = af (af_letter (F \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af (F \<phi>) xs) or (af (af_letter (\<phi>) x) xs)"
      unfolding af_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af_G:
  "af (G \<phi>) w = And (G \<phi> # map (af \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af (G \<phi>) (x # xs) = af (af_letter (G \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af (G \<phi>) xs) and (af (af_letter (\<phi>) x) xs)"
      unfolding af_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af_U:
  "af (\<phi> U \<psi>) (x#xs) = (af (\<phi> U \<psi>) xs and af \<phi> (x#xs)) or af \<psi> (x#xs)"
  by (induction xs) (simp add: af_decompose)+

lemma af_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<equiv>\<^sub>P af_letter \<psi> \<nu>"
proof -
  { 
    fix \<phi> 
    have "af_letter \<phi> \<nu> = subst \<phi> (\<lambda>\<chi>. Some (af_letter \<chi> \<nu>))" 
      by (induction \<phi>) auto 
  }
  thus "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter \<psi> \<nu>"
    and "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<equiv>\<^sub>P af_letter \<psi> \<nu>"
    using subst_respects_ltl_prop_entailment by metis+
qed

lemma af_respectfulness':
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<longrightarrow>\<^sub>P af \<psi> w"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<equiv>\<^sub>P af \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_respectfulness, fastforce+)

lemma af_nested_propos:
  "nested_propos (af_letter \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

subsection \<open>$af_G$\<close>

fun af_G_letter :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "af_G_letter true \<nu> = true"
| "af_G_letter false \<nu> = false"
| "af_G_letter p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_G_letter (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_G_letter (\<phi> and \<psi>) \<nu> = (af_G_letter \<phi> \<nu>) and (af_G_letter \<psi> \<nu>)"
| "af_G_letter (\<phi> or \<psi>) \<nu> = (af_G_letter \<phi> \<nu>) or (af_G_letter \<psi> \<nu>)"
| "af_G_letter (X \<phi>) \<nu> = \<phi>"
| "af_G_letter (G \<phi>) \<nu> = (G \<phi>)"
| "af_G_letter (F \<phi>) \<nu> = (F \<phi>) or (af_G_letter \<phi> \<nu>)"
| "af_G_letter (\<phi> U \<psi>) \<nu> = (\<phi> U \<psi> and (af_G_letter \<phi> \<nu>)) or (af_G_letter \<psi> \<nu>)"

abbreviation af\<^sub>G :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl"
where
  "af\<^sub>G \<phi> w \<equiv> (foldl af_G_letter \<phi> w)"

lemma af\<^sub>G_decompose:
  "af\<^sub>G (\<phi> and \<psi>) w = (af\<^sub>G \<phi> w) and (af\<^sub>G \<psi> w)"
  "af\<^sub>G (\<phi> or \<psi>) w = (af\<^sub>G \<phi> w) or (af\<^sub>G \<psi> w)"
  by (induction w rule: rev_induct) simp_all

lemma af\<^sub>G_simps[simp]:
  "af\<^sub>G true w = true"
  "af\<^sub>G false w = false"
  "af\<^sub>G (G \<phi>) w = G \<phi>"
  "af\<^sub>G (X \<phi>) (x#xs) = af\<^sub>G \<phi> (xs)"
  by (induction w) simp_all

lemma af\<^sub>G_F:
  "af\<^sub>G (F \<phi>) w = Or (F \<phi> # map (af\<^sub>G \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af\<^sub>G (F \<phi>) (x # xs) = af\<^sub>G (af_G_letter (F \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af\<^sub>G (F \<phi>) xs) or (af\<^sub>G (af_G_letter (\<phi>) x) xs)"
      unfolding af\<^sub>G_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af\<^sub>G_U:
  "af\<^sub>G (\<phi> U \<psi>) (x#xs) = (af\<^sub>G (\<phi> U \<psi>) xs and af\<^sub>G \<phi> (x#xs)) or af\<^sub>G \<psi> (x#xs)"
  by (simp add: af\<^sub>G_decompose)

lemma af\<^sub>G_subsequence_U:
  "af\<^sub>G (\<phi> U \<psi>) (w [0 \<rightarrow> Suc n]) = (af\<^sub>G (\<phi> U \<psi>) (w [1 \<rightarrow> Suc n]) and af\<^sub>G \<phi> (w [0 \<rightarrow> Suc n])) or af\<^sub>G \<psi> (w [0 \<rightarrow> Suc n])"
proof -
  have "\<And>n. w [0 \<rightarrow> Suc n] = w 0 # w [1 \<rightarrow> Suc n]"
    using subsequence_empty subsequence_append[of w 1] by (simp add: upt_conv_Cons) 
  thus ?thesis
    using af\<^sub>G_U by metis
qed

lemma af_G_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<equiv>\<^sub>P af_G_letter \<psi> \<nu>"
proof -
  { 
    fix \<phi> 
    have "af_G_letter \<phi> \<nu> = subst \<phi> (\<lambda>\<chi>. Some (af_G_letter \<chi> \<nu>))" 
      by (induction \<phi>) auto 
  }
  thus "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter \<psi> \<nu>"
    and "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<equiv>\<^sub>P af_G_letter \<psi> \<nu>"
    using subst_respects_ltl_prop_entailment by metis+
qed

lemma af_G_respectfulness':
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af\<^sub>G \<phi> w \<longrightarrow>\<^sub>P af\<^sub>G \<psi> w"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af\<^sub>G \<phi> w \<equiv>\<^sub>P af\<^sub>G \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_G_respectfulness, fastforce+) 

lemma af_G_nested_propos:
  "nested_propos (af_G_letter \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

lemma af_G_letter_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af_G_letter \<phi> \<nu>"
  by (induction \<phi>) (simp_all, blast+)

lemma af\<^sub>G_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> w"
  using af_G_letter_sat_core by (induction w rule: rev_induct) (simp_all, blast)

lemma af\<^sub>G_sat_core_generalised:
  "Only_G \<G> \<Longrightarrow> i \<le> j \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> i]) \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j])"
  by (metis af\<^sub>G_sat_core foldl_append subsequence_append le_add_diff_inverse)

lemma af\<^sub>G_eval\<^sub>G:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G (eval\<^sub>G \<G> \<phi>) w \<longleftrightarrow> \<G> \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w)" 
  by (induction \<phi>) (simp_all add: eval\<^sub>G_prop_entailment af\<^sub>G_decompose)

lemma af\<^sub>G_keeps_F_and_S:
  assumes "ys \<noteq> []"
  assumes "S \<Turnstile>\<^sub>P af\<^sub>G \<phi> ys"
  shows "S \<Turnstile>\<^sub>P af\<^sub>G (F \<phi>) (xs @ ys)"
proof -
  have "af\<^sub>G \<phi> ys \<in> set (map (af\<^sub>G \<phi>) (suffixes (xs @ ys)))"
    using assms(1) unfolding suffixes_append map_append
    by (induction ys rule: List.list_nonempty_induct) auto
  thus ?thesis
    unfolding af\<^sub>G_F Or_prop_entailment using assms(2) by force
qed

subsection \<open>G-Subformulae Simplification\<close>

lemma G_af_simp[simp]:
  "\<^bold>G (af \<phi> w) = \<^bold>G \<phi>"
proof -
  { fix \<phi> \<nu> have "\<^bold>G (af_letter \<phi> \<nu>) = \<^bold>G \<phi>" by (induction \<phi>) auto }
  thus ?thesis
    by (induction w arbitrary: \<phi> rule: rev_induct) fastforce+
qed

lemma G_af\<^sub>G_simp[simp]:
  "\<^bold>G (af\<^sub>G \<phi> w) = \<^bold>G \<phi>"
proof -
  { fix \<phi> \<nu> have "\<^bold>G (af_G_letter \<phi> \<nu>) = \<^bold>G \<phi>" by (induction \<phi>) auto }
  thus ?thesis
    by (induction w arbitrary: \<phi> rule: rev_induct) fastforce+
qed

subsection \<open>Relation between af and $af_G$\<close>

lemma af_G_letter_free_F:
  "\<^bold>G \<phi> = {} \<Longrightarrow> \<^bold>G (af_letter \<phi> \<nu>) = {}"
  "\<^bold>G \<phi> = {} \<Longrightarrow> \<^bold>G (af_G_letter \<phi> \<nu>) = {}"
  by (induction \<phi>) auto

lemma af_G_free:
  assumes "\<^bold>G \<phi> = {}"
  shows "af \<phi> w = af\<^sub>G \<phi> w"
  using assms
proof (induction w arbitrary: \<phi>)
  case (Cons x xs)
    hence "af (af_letter \<phi> x) xs = af\<^sub>G (af_letter \<phi> x) xs"
      using af_G_letter_free_F[OF Cons.prems, THEN Cons.IH] by blast
    moreover
    have "af_letter \<phi> x = af_G_letter \<phi> x"
      using Cons.prems by (induction \<phi>) auto
    ultimately
    show ?case 
      by simp
qed simp

lemma af_equals_af\<^sub>G_base_cases:
  "af true w = af\<^sub>G true w"
  "af false w = af\<^sub>G false w"
  "af p(a) w = af\<^sub>G p(a) w"
  "af (np(a)) w = af\<^sub>G (np(a)) w"
  by (auto intro: af_G_free)

lemma af_implies_af\<^sub>G:
  "S \<Turnstile>\<^sub>P af \<phi> w \<Longrightarrow> S \<Turnstile>\<^sub>P af\<^sub>G \<phi> w"
proof (induction w arbitrary: S rule: rev_induct)
  case (snoc x xs)
    hence "S \<Turnstile>\<^sub>P af_letter (af \<phi> xs) x"
      by simp
    hence "S \<Turnstile>\<^sub>P af_letter (af\<^sub>G \<phi> xs) x"
      using af_respectfulness(1) snoc.IH unfolding ltl_prop_implies_def by blast
    moreover
    {
      fix \<phi> 
      have "\<And>\<nu>. S \<Turnstile>\<^sub>P af_letter \<phi> \<nu> \<Longrightarrow> S \<Turnstile>\<^sub>P af_G_letter \<phi> \<nu>"
        by (induction \<phi>) auto
    }
    ultimately
    show ?case
      using snoc.prems foldl_append by simp
qed simp

lemma af_implies_af\<^sub>G_2:
  "w \<Turnstile> af \<phi> xs \<Longrightarrow> w \<Turnstile> af\<^sub>G \<phi> xs"
  by (metis ltl_prop_implication_implies_ltl_implication af_implies_af\<^sub>G ltl_prop_implies_def)

lemma af\<^sub>G_implies_af_eval\<^sub>G':
  assumes "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w)"
  assumes "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi>"
  assumes "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length w \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i w))" 
  shows   "S \<Turnstile>\<^sub>P af \<phi> w"
  using assms
proof (induction \<phi> arbitrary: w)
  case (LTLGlobal \<phi>)
    hence "G \<phi> \<in> \<G>"
      unfolding af\<^sub>G_simps eval\<^sub>G.simps by (cases "G \<phi> \<in> \<G>") simp+
    hence "S \<Turnstile>\<^sub>P G \<phi>"
      using LTLGlobal by simp
    moreover
    {
      fix x
      assume "x \<in> set (map (af \<phi>) (suffixes w))"
      then obtain w' where "x = af \<phi> w'" and "w' \<in> set (suffixes w)"
        by auto
      then obtain i where "w' = drop i w" and "i < length w"
        unfolding suffixes_alt_def set_rev by auto
      hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')"
        using LTLGlobal.prems `G \<phi> \<in> \<G>` by simp
      hence "S \<Turnstile>\<^sub>P x"
        using LTLGlobal(1)[OF `S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')`] LTLGlobal(3-4) drop_drop
        unfolding `x = af \<phi> w'` `w' = drop i w` by simp
    }
    ultimately
    show ?case
      unfolding af_G eval\<^sub>G_And_map And_prop_entailment by simp
next
  case (LTLFinal \<phi>)
    then obtain x where x_def: "x \<in> set (F \<phi> # map (eval\<^sub>G \<G> o af\<^sub>G \<phi>) (suffixes w))" 
      and "S \<Turnstile>\<^sub>P x"
      unfolding Or_prop_entailment af\<^sub>G_F eval\<^sub>G_Or_map by force
    hence "\<exists>y \<in> set (F \<phi> # map (af \<phi>) (suffixes w)). S \<Turnstile>\<^sub>P y"
    proof (cases "x \<noteq> F \<phi>")
      case True
        then obtain w' where "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')" and "w' \<in> set (suffixes w)"
          using x_def `S \<Turnstile>\<^sub>P x` by auto
        hence "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length w' \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i w'))"
          using LTLFinal.prems unfolding suffixes_alt_def set_rev by auto
        moreover
        have "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (G \<psi>)"
          using LTLFinal by simp
        ultimately
        have "S \<Turnstile>\<^sub>P af \<phi> w'"
          using LTLFinal.IH[OF `S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')`] using assms(2) by blast 
        thus ?thesis
          using `w' \<in> set (suffixes w)` by auto
    qed simp
    thus ?case
      unfolding af_F Or_prop_entailment eval\<^sub>G_Or_map by simp
next
  case (LTLNext \<phi>)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        {
          fix \<psi> i
          assume "G \<psi> \<in> \<G>" and "Suc i < length (x#xs)"
          hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop (Suc i) (x#xs)))"
            using LTLNext.prems unfolding Cons by blast
          hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i xs))"
            by simp
        }
        hence "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length xs \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i xs))"
          by simp
        thus ?thesis
          using LTLNext Cons by simp
    qed simp
next
  case (LTLUntil \<phi> \<psi>)
    thus ?case
    proof (induction w)
      case (Cons x xs)
        {
          assume "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (x # xs))"
          moreover
          have "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length (x#xs) \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i (x#xs)))"
            using Cons by simp
          ultimately
          have "S \<Turnstile>\<^sub>P af \<psi> (x # xs)"
            using Cons.prems by blast
          hence ?case
            unfolding af_U by simp
        }
        moreover
        {
          assume "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G (\<phi> U \<psi>) xs)" and "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (x # xs))"
          moreover
          have "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length (x#xs) \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i (x#xs)))"
            using Cons by simp
          ultimately
          have "S \<Turnstile>\<^sub>P af \<phi> (x # xs)" and "S \<Turnstile>\<^sub>P af (\<phi> U \<psi>) xs"  
            using Cons by (blast, force) 
          hence ?case
            unfolding af_U by simp
        }
        ultimately
        show ?case
          using Cons(4) unfolding af\<^sub>G_U by auto
    qed simp
next
  case (LTLProp a)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        thus ?thesis
          using LTLProp by (cases "a \<in> x") simp+
    qed simp
next
  case (LTLPropNeg a)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        thus ?thesis
          using LTLPropNeg by (cases "a \<in> x") simp+
    qed simp
qed (unfold af_equals_af\<^sub>G_base_cases af\<^sub>G_decompose af_decompose, auto)

lemma af\<^sub>G_implies_af_eval\<^sub>G:
  assumes "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [0\<rightarrow>j]))"
  assumes "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi>"
  assumes "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i \<le> j \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (w [i \<rightarrow> j]))" 
  shows "S \<Turnstile>\<^sub>P af \<phi> (w [0\<rightarrow>j])"
  using af\<^sub>G_implies_af_eval\<^sub>G'[OF assms(1-2), unfolded subsequence_length subsequence_drop] assms(3) by force 

subsection \<open>Continuation\<close>

-- \<open>af fulfills the infinite continuation w' of a word after skipping some finite prefix w.
    Corresponds to Lemma 7 in arXiv: 1402.3388v2\<close>

lemma af_ltl_continuation:
  "(w \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> w' \<Turnstile> af \<phi> w"
proof (induction w arbitrary: \<phi> w')
  case (Cons x xs)
    have "((x # xs) \<frown> w') 0 = x"
      unfolding conc_def nth_Cons_0 by simp
    moreover
    have "suffix 1 ((x # xs) \<frown> w') = xs \<frown> w'"
      unfolding suffix_def conc_def by fastforce
    moreover
    {
      fix \<phi> :: "'a ltl"
      have "\<And>w. w \<Turnstile> \<phi> \<longleftrightarrow> suffix 1 w \<Turnstile> af_letter \<phi> (w 0)"
        by (induction \<phi>) ((unfold LTL_F_one_step_unfolding LTL_G_one_step_unfolding LTL_U_one_step_unfolding)?, auto)
    }
    ultimately
    have "((x # xs) \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> (xs \<frown> w') \<Turnstile> af_letter \<phi> x"
      by metis
    also
    have "\<dots> \<longleftrightarrow> w' \<Turnstile> af \<phi> (x#xs)"
      using Cons.IH by simp
    finally
    show ?case .
qed simp

lemma af_ltl_continuation_suffix:
  "w \<Turnstile> \<phi> \<longleftrightarrow> suffix i w \<Turnstile> af \<phi> (w[0 \<rightarrow> i])"
  using af_ltl_continuation prefix_suffix2 prefix_is_subsequence by metis

lemma af_G_ltl_continuation:
  "\<forall>\<psi> \<in> \<^bold>G \<phi>. w' \<Turnstile> \<psi> = (w \<frown> w') \<Turnstile> \<psi> \<Longrightarrow> (w \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> w' \<Turnstile> af\<^sub>G \<phi> w"
proof (induction w arbitrary: w' \<phi>)
  case (Cons x xs)
    {
      fix \<psi> :: "'a ltl" fix  w w' w'' 
      assume "w'' \<Turnstile> G \<psi> = ((w @ w') \<frown> w'') \<Turnstile> G \<psi>"
      hence "w'' \<Turnstile> G \<psi> = (w' \<frown>  w'') \<Turnstile> G \<psi>" and "(w' \<frown> w'') \<Turnstile> G \<psi> = ((w @ w') \<frown> w'') \<Turnstile> G \<psi>"
        by (induction w' arbitrary: w) (metis LTL_suffix_G suffix_conc conc_conc)+
    }
    note G_stable = this
    have A: "\<forall>\<psi>\<in>\<^bold>G (af\<^sub>G \<phi> [x]). w' \<Turnstile> \<psi> = (xs conc w') \<Turnstile> \<psi>"
      using G_stable(1)[of w' _ "[x]"] Cons.prems unfolding G_af\<^sub>G_simp conc_conc append.simps unfolding G_nested_propos_alt_def by blast
    have B: "\<forall>\<psi>\<in>\<^bold>G \<phi>. ([x] \<frown> xs \<frown> w') \<Turnstile> \<psi> = (xs conc w') \<Turnstile> \<psi>"
      using G_stable(2)[of w' _ "[x]"] Cons.prems unfolding conc_conc append.simps unfolding G_nested_propos_alt_def by blast 
    hence "([x] \<frown> xs \<frown> w') \<Turnstile> \<phi> = (xs \<frown> w') \<Turnstile> af\<^sub>G \<phi> [x]"
    proof (induction \<phi>)
      case (LTLFinal \<phi>)
        thus ?case
          unfolding LTL_F_one_step_unfolding
          by (auto simp add: suffix_conc[of "[x]", simplified])
    next
      case (LTLUntil \<phi> \<psi>)
        thus ?case
          unfolding LTL_U_one_step_unfolding
          by (auto simp add: suffix_conc[of "[x]", simplified])
    qed (auto simp add: conc_fst[of 0 "[x]"] suffix_conc[of "[x]", simplified])
    also
    have "... = w' \<Turnstile> af\<^sub>G \<phi> (x # xs)"
      using Cons.IH[of "af\<^sub>G \<phi> [x]" w'] A by simp
    finally
    show ?case unfolding conc_conc 
      by simp
qed simp

lemma af\<^sub>G_ltl_continuation_suffix:
  "\<forall>\<psi> \<in> \<^bold>G \<phi>. w \<Turnstile> \<psi> = (suffix i w) \<Turnstile> \<psi> \<Longrightarrow> w \<Turnstile> \<phi> \<longleftrightarrow> suffix i w \<Turnstile> af\<^sub>G \<phi> (w [0 \<rightarrow> i])"  
  by (metis af_G_ltl_continuation[of \<phi> "suffix i w"] diff_zero prefix_suffix2 subsequence_prefix_suffix suffix_0)

end