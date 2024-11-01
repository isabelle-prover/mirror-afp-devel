subsection \<open>Imperative in-place computation\<close>
theory Tangent_Numbers_Imperative
  imports Tangent_Numbers "Refine_Monadic.Refine_Monadic" "Refine_Imperative_HOL.IICF"
"HOL-Library.Code_Target_Numeral"
begin

text \<open>
  We will now formalise and verify the imperative in-place version of the algorithm given by
  Brent et al.~\<^cite>\<open>brent\<close>. We use as storage only an array of $n$ numbers, 
  which will also contain the results in the end. Note however that the size of these numbers
  grows enormously the longer the algorithm runs.
\<close>

locale tangent_numbers_imperative
begin

context
  fixes n :: nat
begin

definition I_init :: "nat list \<times> nat \<Rightarrow> bool" where
  "I_init = (\<lambda>(xs, i). 
     (n = 0 \<and> i = 1 \<and> xs = []) \<or> 
     (i \<in> {1..n} \<and> xs = map fact [0..<i] @ replicate (n-i) 0))"

definition init_loop_aux :: "nat list nres" where
  "init_loop_aux = 
     do {xs \<leftarrow> RETURN (op_array_replicate n 0);
         (if n = 0 then RETURN xs else do {ASSERT (length xs > 0); RETURN (xs[0 := 1])})}"

definition init_loop :: "nat list nres" where
  "init_loop =
     do {
       xs \<leftarrow> init_loop_aux;
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_init\<^esup>
           (\<lambda>(_, i). i < n)
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
  "I_inner xs i = (\<lambda>(xs', j). j \<in> {i..n} \<and> length xs' = n \<and>
     (\<forall>k<n. xs' ! k = (if k\<in>{i..<j} then tangent_number_aux (k+Suc i-1) (k+2-Suc i) else xs ! k)))"

definition inner_loop :: "nat list \<Rightarrow> nat \<Rightarrow> nat list nres" where
  "inner_loop xs i =
     do {
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_inner xs i\<^esup> (\<lambda>(_, j). j < n)
         (\<lambda>(xs, j). do {
           ASSERT (j - 1 < length xs);
           x \<leftarrow> RETURN (xs ! (j - 1));
           ASSERT (j < length xs);
           y \<leftarrow> RETURN (xs ! j);
           RETURN (xs[j := (j - i) * x + (j - i + 2) * y], j + 1)
         })
         (xs, i);
       RETURN xs'
     }"

definition I_compute :: "nat list \<times> nat \<Rightarrow> bool" where
  "I_compute = (\<lambda>(xs, i). (n = 0 \<and> i = 1 \<and> xs = []) \<or>
     (i \<in> {1..n} \<and> xs = map (\<lambda>k. if k < i then tangent_number (k+1) else tangent_number_aux (k+i-1) (k+2-i)) [0..<n]))"

definition compute :: "nat list nres" where
  "compute =
     do {
       xs \<leftarrow> init_loop;
       (xs', _) \<leftarrow>
         WHILE\<^sub>T\<^bsup>I_compute\<^esup>
           (\<lambda>(_, i). i < n)
           (\<lambda>(xs, i). do { xs' \<leftarrow> inner_loop xs i; RETURN (xs', i + 1) })
           (xs, 1);
       RETURN xs'
     }"

lemma init_loop_aux_correct [refine_vcg]:
  "init_loop_aux \<le> SPEC (\<lambda>xs. xs = (replicate n 0)[0 := 1])"
  unfolding init_loop_aux_def
  by refine_vcg auto

lemma init_loop_correct [refine_vcg]: "init_loop \<le> SPEC (\<lambda>xs. xs = map fact [0..<n])"
  unfolding init_loop_def
  apply refine_vcg
  apply (rule wf_measure[of "\<lambda>(_, i). n - i"])
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
    by (auto simp: I_init_def)
  done

lemma I_inner_preserve:
  assumes invar: "I_inner xs i (xs', j)" and invar': "I_compute (xs, i)"
  assumes j: "j < n"
  defines "y \<equiv> (j - i) * xs' ! (j - 1) + (j - i + 2) * xs' ! j"
  defines "xs'' \<equiv> list_update xs' j y"
  shows   "I_inner xs i (xs'', j + 1)"
  unfolding I_inner_def
proof safe
  show "j + 1 \<in> {i..n}" "length xs'' = n"
    using invar j by (simp_all add: xs''_def I_inner_def)
next
  fix k assume k: "k < n"
  define T where "T = tangent_number_aux"
  have ij: "1 \<le> i" "i \<le> j" "j < n"
    using invar invar' j by (auto simp: I_inner_def I_compute_def)
  have nth_xs': "xs' ! k = (if k \<in> {i..<j} then T (k + Suc i - 1) (k + 2 - Suc i) else xs ! k)"
    if "k < n" for k using invar that unfolding I_inner_def T_def by blast
  have nth_xs: "xs ! k = (if k < i then tangent_number (k + 1)
                             else T (k + i - 1) (k + 2 - i))"
    if "k < n" for k using invar' that unfolding I_compute_def T_def by auto
  have [simp]: "length xs' = n"
    using invar by (simp add: I_inner_def)

  consider "k = j" | "k \<in> {i..<j}" | "k \<notin> {i..j}"
    by force
  thus "xs'' ! k = (if k \<in> {i..<j + 1} then T (k + Suc i - 1) (k + 2 - Suc i) else xs ! k)"
  proof cases
    assume [simp]: "k = j"
    have "xs'' ! k = y"
      using ij by (simp add: xs''_def)
    also have "\<dots> = (j - i) * xs' ! (j - 1) + (j - i + 2) * xs' ! j"
      by (simp add: y_def)
    also have "xs' ! j = xs ! j"
      using ij by (subst nth_xs') auto
    also have "\<dots> = T (j + i - 1) (j + 2 - i)"
      using ij by (subst nth_xs) auto
    also have "xs' ! (j - 1) = (if i = j then xs ! (i - 1) else T (j + i - 1) (j - i))"
      using ij by (subst nth_xs')  auto
    also have "xs ! (i - 1) = T (2 * i - 1) 0"
      using ij by (subst nth_xs) (auto simp: tangent_number_conv_aux T_def)
    also have "(if i = j then T (2 * i - 1) 0 else T (j + i - 1) (j - i)) = T (j + i - 1) (j - i)"
      by (auto simp: mult_2)
    also have "(j - i) * T (j + i - 1) (j - i) + (j - i + 2) * T (j + i - 1) (j + 2 - i) =
               T (j + i) (j + 1 - i)"
      unfolding T_def by (subst (3) tangent_number_aux_rec') (use ij in auto)
    finally show ?thesis
      using ij by simp
  next
    assume k: "k \<in> {i..<j}"
    hence "xs'' ! k = xs' ! k"
      unfolding xs''_def by auto
    also have "\<dots> = T (k + i) (Suc k - i)"
      by (subst nth_xs') (use k ij in auto)
    finally show ?thesis
      using k by simp
  next
    assume k: "k \<notin> {i..j}"
    hence "xs'' ! k = xs' ! k"
      using ij unfolding xs''_def by auto
    also have "xs' ! k = xs ! k"
      using k \<open>k < n\<close> by (subst nth_xs') auto
    finally show ?thesis
      using k by auto
  qed
qed

lemma inner_loop_correct [refine_vcg]:
  assumes "I_compute (xs, i)" "i < n"
  shows "inner_loop xs i \<le> SPEC (\<lambda>xs'. xs' = 
           map (\<lambda>k. if k \<ge> i then tangent_number_aux (k+Suc i-1) (k+2-Suc i) else xs ! k) [0..<n])"
  unfolding inner_loop_def
  apply refine_vcg
        apply (rule wf_measure[of "\<lambda>(_, j). n - j"])
  subgoal
    using assms by (auto simp: I_inner_def I_compute_def)
  subgoal
    using assms unfolding I_inner_def by auto
  subgoal
    using assms unfolding I_inner_def by auto
  subgoal for s xs' j
    using I_inner_preserve[of xs i xs' j] assms by auto
  subgoal
    by auto
  subgoal using assms
    by (auto simp: I_inner_def intro!: nth_equalityI)
  done

lemma compute_correct [refine_vcg]: "compute \<le> SPEC (\<lambda>xs'. xs' = tangent_numbers n)"
  unfolding compute_def
  apply refine_vcg
      apply (rule wf_measure[of "\<lambda>(_, i). n - i"])
  subgoal
    by (auto simp: I_compute_def tangent_number_aux_last')
  subgoal
    by (auto simp: I_compute_def tangent_number_conv_aux less_Suc_eq mult_2)
  subgoal
    by auto
  subgoal
    by (auto simp: I_compute_def tangent_number_conv_aux less_Suc_eq mult_2 intro!: nth_equalityI)
  subgoal
    by auto
  subgoal
    by (auto simp: I_compute_def tangent_numbers_def intro!: nth_equalityI simp del: upt_Suc)
  done

lemmas defs = 
  compute_def inner_loop_def init_loop_def init_loop_aux_def

end

sepref_definition compute_imp is
  "tangent_numbers_imperative.compute" ::
     "nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding tangent_numbers_imperative.defs by sepref

lemma imp_correct':
  "(compute_imp, \<lambda>n. RETURN (tangent_numbers n)) \<in> nat_assn\<^sup>d \<rightarrow>\<^sub>a array_assn nat_assn"
proof -
  have *: "(compute, \<lambda>n. RETURN (tangent_numbers n)) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
    by refine_vcg simp?
  show ?thesis
    using compute_imp.refine[FCOMP *] .
qed

theorem imp_correct:
   "<nat_assn n n> compute_imp n <array_assn nat_assn (tangent_numbers n)>\<^sub>t"
proof -
  have [simp]: "nofail (compute n)"
    using compute_correct[of n] le_RES_nofailI by blast
  have 1: "xs = tangent_numbers n" if "RETURN xs \<le> compute n" for xs
    using that compute_correct[of n] by (simp add: pw_le_iff)
  note rl = compute_imp.refine[THEN hfrefD, of n n, THEN hn_refineD, simplified]
  show ?thesis
    apply (rule cons_rule[OF _ _ rl])
    apply (sep_auto simp: pure_def)
    apply (sep_auto simp: pure_def dest!: 1)
    done    
qed

end

lemmas [code] = tangent_numbers_imperative.compute_imp_def

end