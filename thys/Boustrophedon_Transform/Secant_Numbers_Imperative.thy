subsection \<open>Imperative in-place computation\<close>
theory Secant_Numbers_Imperative
  imports Secant_Numbers "Refine_Monadic.Refine_Monadic" "Refine_Imperative_HOL.IICF"
"HOL-Library.Code_Target_Numeral"
begin

text \<open>
  We will now formalise and verify the imperative in-place version of the algorithm given by
  Brent et al.~\<^cite>\<open>brent\<close>. We use as storage only an array of $n$ numbers, 
  which will also contain the results in the end. Note however that the size of these numbers
  grows enormously the longer the algorithm runs.
\<close>

locale secant_numbers_imperative
begin

context
  fixes n :: nat
begin

definition I_init :: "nat list \<times> nat \<Rightarrow> bool" where
  "I_init = (\<lambda>(xs, i). 
     (i \<in> {1..n+1} \<and> xs = map fact [0..<i] @ replicate (n+1-i) 0))"

definition init_loop_aux :: "nat list nres" where
  "init_loop_aux = 
     do {xs \<leftarrow> RETURN (op_array_replicate (n+1) 0);
         ASSERT (length xs > 0);
         RETURN (xs[0 := 1])}"

definition init_loop :: "nat list nres" where
  "init_loop =
     do {
       xs \<leftarrow> init_loop_aux;
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_init\<^esup>
           (\<lambda>(_, i). i \<le> n)
           (\<lambda>(xs, i). do {
             ASSERT (i - 1 < length xs);
             x \<leftarrow> RETURN (xs ! (i - 1));
             ASSERT (i < length xs);
             RETURN (xs[i := i * x], i + 1)
           })
           (xs, 1);
       RETURN xs'
     }"

definition I_inner where
  "I_inner xs i = (\<lambda>(xs', j). j \<in> {i+1..n+1} \<and> length xs' = n+1 \<and>
     (\<forall>k\<le>n. xs' ! k = (if k\<in>{i..<j} then secant_number_aux (k+Suc i-1) (k+1-Suc i) else xs ! k)))"

definition inner_loop :: "nat list \<Rightarrow> nat \<Rightarrow> nat list nres" where
  "inner_loop xs i =
     do {
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_inner xs i\<^esup> (\<lambda>(_, j). j \<le> n)
         (\<lambda>(xs, j). do {
           ASSERT (j - 1 < length xs);
           x \<leftarrow> RETURN (xs ! (j - 1));
           ASSERT (j < length xs);
           y \<leftarrow> RETURN (xs ! j);
           RETURN (xs[j := (j - i) * x + (j - i + 1) * y], j + 1)
         })
         (xs, i + 1);
       RETURN xs'
     }"

definition I_compute :: "nat list \<times> nat \<Rightarrow> bool" where
  "I_compute = (\<lambda>(xs, i).
     (i \<in> {1..n+1} \<and> xs = map (\<lambda>k. if k < i then secant_number k else secant_number_aux (k+i-1) (k+1-i)) [0..<Suc n]))"

definition compute :: "nat list nres" where
  "compute =
     do {
       xs \<leftarrow> init_loop;
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_compute\<^esup>
           (\<lambda>(_, i). i \<le> n)
           (\<lambda>(xs, i). do { xs' \<leftarrow> inner_loop xs i; RETURN (xs', i + 1) })
           (xs, 1);
       RETURN xs'
     }"

lemma init_loop_aux_correct [refine_vcg]:
  "init_loop_aux \<le> SPEC (\<lambda>xs. xs = (replicate (n+1) 0)[0 := 1])"
  unfolding init_loop_aux_def
  by refine_vcg auto

lemma init_loop_correct [refine_vcg]: "init_loop \<le> SPEC (\<lambda>xs. xs = map fact [0..<n+1])"
  unfolding init_loop_def
  apply refine_vcg
  apply (rule wf_measure[of "\<lambda>(_, i). n + 1 - i"])
  subgoal
    by (auto simp: I_init_def nth_list_update' intro!: nth_equalityI)
  subgoal
    by (auto simp: I_init_def)
  subgoal
    by (auto simp: I_init_def)
  subgoal
    by (auto simp: I_init_def nth_list_update' fact_reduce nth_Cons nth_append
             intro!: nth_equalityI split: nat.splits)
  subgoal
    by auto
  subgoal
    by (auto simp: I_init_def le_Suc_eq simp del: upt_Suc)
  done

lemma I_inner_preserve:
  assumes invar: "I_inner xs i (xs', j)" and invar': "I_compute (xs, i)"
  assumes j: "j \<le> n"
  defines "y \<equiv> (j - i) * xs' ! (j - 1) + (j - i + 1) * xs' ! j"
  defines "xs'' \<equiv> list_update xs' j y"
  shows   "I_inner xs i (xs'', j + 1)"
  unfolding I_inner_def
proof safe
  show "j + 1 \<in> {i+1..n+1}" "length xs'' = n + 1"
    using invar j by (simp_all add: xs''_def I_inner_def)
next
  fix k assume k: "k \<le> n"
  define S where "S = secant_number_aux"
  have ij: "1 \<le> i" "i < j" "j \<le> n"
    using invar invar' j by (auto simp: I_inner_def I_compute_def)
  have nth_xs': "xs' ! k = (if k \<in> {i..<j} then S (k + Suc i-1) (k + 1 - Suc i) else xs ! k)"
    if "k \<le> n" for k using invar that unfolding I_inner_def S_def by blast
  have nth_xs: "xs ! k = (if k < i then secant_number k else S (k + i - 1) (k + 1 - i))"
    if "k \<le> n" for k using invar' that unfolding I_compute_def S_def by (auto simp del: upt_Suc)
  have [simp]: "length xs' = n + 1"
    using invar by (simp add: I_inner_def)

  consider "k = j" | "k \<in> {i..<j}" | "k \<notin> {i..j}"
    by force
  thus "xs'' ! k = (if k \<in> {i..<j + 1} then S (k + Suc i - 1) (k + 1 - Suc i) else xs ! k)"
  proof cases
    assume [simp]: "k = j"
    have "xs'' ! k = y"
      using ij by (simp add: xs''_def)
    also have "\<dots> = (j - i) * xs' ! (j - 1) + (j - i + 1) * xs' ! j"
      by (simp add: y_def)
    also have "xs' ! j = xs ! j"
      using ij by (subst nth_xs') auto
    also have "\<dots> = S (j + i - 1) (j + 1 - i)"
      using ij by (subst nth_xs) auto
    also have "xs' ! (j - 1) = S (j + i - 1) (j - Suc i)"
      using ij by (subst nth_xs') (auto simp: Suc_diff_Suc)
    also have "(j - i) * S (j + i - 1) (j - Suc i) + (j - i + 1) * S (j + i - 1) (j + 1 - i) =
               S (j + i) (j - i)"
      unfolding S_def by (subst (3) secant_number_aux_rec') (use ij in auto)
    finally show ?thesis
      using ij by simp
  next
    assume k: "k \<in> {i..<j}"
    hence "xs'' ! k = xs' ! k"
      unfolding xs''_def by auto
    also have "\<dots> = S (k + i) (k - i)"
      by (subst nth_xs') (use k ij in auto)
    finally show ?thesis
      using k by simp
  next
    assume k: "k \<notin> {i..j}"
    hence "xs'' ! k = xs' ! k"
      using ij unfolding xs''_def by auto
    also have "xs' ! k = xs ! k"
      using k \<open>k \<le> n\<close> by (subst nth_xs') auto
    finally show ?thesis
      using k by auto
  qed
qed

lemma inner_loop_correct [refine_vcg]:
  assumes "I_compute (xs, i)" "i \<le> n"
  shows "inner_loop xs i \<le> SPEC (\<lambda>xs'. xs' = 
           map (\<lambda>k. if k \<ge> i then secant_number_aux (k+Suc i-1) (k+1-Suc i) else xs ! k) [0..<Suc n])"
  unfolding inner_loop_def
  apply refine_vcg
  apply (rule wf_measure[of "\<lambda>(_, j). n + 1 - j"])
  subgoal
    unfolding I_inner_def
    by clarify (use assms in \<open>simp_all add: mult_2 I_compute_def del: upt_Suc\<close>)
  subgoal
    using assms unfolding I_inner_def by auto
  subgoal
    using assms unfolding I_inner_def by auto
  subgoal for s xs' j
    using I_inner_preserve[of xs i xs' j] assms by auto
  subgoal
    by auto
  subgoal using assms
    by (auto simp: I_inner_def intro!: nth_equalityI simp del: upt_Suc)
  done

lemma compute_correct [refine_vcg]: "compute \<le> SPEC (\<lambda>xs'. xs' = secant_numbers n)"
  unfolding compute_def
  apply refine_vcg
      apply (rule wf_measure[of "\<lambda>(_, i). n + 1 - i"])
  subgoal
    by (auto simp: I_compute_def secant_number_aux_last' simp del: upt_Suc)
  subgoal
    by (auto simp: I_compute_def secant_number_conv_aux less_Suc_eq mult_2)
  subgoal
    by (auto simp: I_compute_def simp del: upt_Suc)
  subgoal
    by (auto simp: I_compute_def secant_number_conv_aux less_Suc_eq mult_2 simp del: upt_Suc
             intro!: nth_equalityI)
  subgoal
    by auto
  subgoal
    by (auto simp: I_compute_def secant_numbers_def intro!: nth_equalityI simp del: upt_Suc)
  done

lemmas defs = 
  compute_def inner_loop_def init_loop_def init_loop_aux_def

end

sepref_definition compute_imp is
  "secant_numbers_imperative.compute" ::
     "nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding secant_numbers_imperative.defs by sepref

lemma imp_correct':
  "(compute_imp, \<lambda>n. RETURN (secant_numbers n)) \<in> nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
proof -
  have *: "(compute, \<lambda>n. RETURN (secant_numbers n)) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    by refine_vcg simp?
  show ?thesis
    using compute_imp.refine[FCOMP *] .
qed

theorem imp_correct:
   "<nat_assn n n> compute_imp n <array_assn nat_assn (secant_numbers n)>\<^sub>t"
proof -
  have [simp]: "nofail (compute n)"
    using compute_correct[of n] le_RES_nofailI by blast
  have 1: "xs = secant_numbers n" if "RETURN xs \<le> compute n" for xs
    using that compute_correct[of n] by (simp add: pw_le_iff)
  note rl = compute_imp.refine[THEN hfrefD, of n n, THEN hn_refineD, simplified]
  show ?thesis
    apply (rule cons_rule[OF _ _ rl])
    apply (sep_auto simp: pure_def)
    apply (sep_auto simp: pure_def dest!: 1)
    done    
qed

end

lemmas [code] = secant_numbers_imperative.compute_imp_def

end