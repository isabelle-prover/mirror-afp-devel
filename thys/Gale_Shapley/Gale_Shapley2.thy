(*
Stepwise refinement of the Gale-Shapley algorithm down to executable code.

Author: Tobias Nipkow
*)

section \<open>Part 2: Refinement from lists to arrays\<close>

theory Gale_Shapley2
imports Gale_Shapley1 "Collections.Diff_Array"
begin

text \<open>Refinement from lists to arrays,
resulting in a linear (in the input size, which is \<open>n^2\<close>) time algorithm.\<close>

abbreviation "array \<equiv> new_array"
notation array_get (infixl "!!" 100)
notation array_set ("_[_ ::= _]" [1000,0,0] 900)
abbreviation "list \<equiv> list_of_array"

lemma list_array: "list (array x n) = replicate n x"
by (simp add: new_array_def)

lemma array_get: "a !! i = list a ! i"
by (cases a) simp

context Pref
begin

subsection \<open>Algorithm 7: Arrays\<close>

definition "match_array A a = P ! a ! (A !! a)"

lemma match_array: "match_array A a = match (list A) a"
by(cases A) (simp add: match_array_def match_def)

lemmas array_abs = match_array array_list_of_set array_get

lemma Gale_Shapley7:
assumes "R = map ranking Q"
shows
"VARS A B N ai a a' b r
 [ai = 0 \<and> A = array 0 n \<and> B = array 0 n \<and> N = array False n]
 WHILE ai < n
 INV { invar1 (list A) (list B) (list N) ai }
 VAR {z = n - ai}
 DO a := ai; b := match_array A a;
  WHILE N !! b
  INV { invar2 (list A) (list B) (list N) ai a \<and> b = match_array A a \<and> z = n-ai }
  VAR {var (list A) {<ai}}
  DO a' := B !! b; r := R ! match_array A a';
     IF r ! a < r ! a'
     THEN B := B[b ::= a]; A := A[a' ::= A !! a' + 1]; a := a'
     ELSE A := A[a ::= A !! a + 1]
     FI;
     b := match_array A a
  OD;
  B := B[b ::= a]; N := N[b ::= True]; ai := ai+1
 OD
 [matching (list A) {<n} \<and> stable (list A) {<n} \<and> opti\<^sub>a (list A)]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case  (* outer invar holds initially *)
   by(auto simp:  pref_match_def P_set card_distinct match_def list_array index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 2 (* outer invar and b implies inner invar *)
  thus ?case by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
next
  case 3 (* preservation of inner invar *)
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R ! b ! a1 < R ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q ranking_iff_pref)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, goal_cases)
    case 1 show ?case using inner_pres[OF R _ _ refl refl refl] 3
      unfolding array_abs by blast
  qed
next
  case 4 (* inner invar' and not b implies outer invar *)
  show ?case
  proof (simp only: mem_Collect_eq prod.case, rule conjI, goal_cases)
    case 1 show ?case using 4 inner_to_outer unfolding array_abs by blast
  next
    case 2 thus ?case using 4 by auto
  qed
next
  case 5 (* outer invar and not b ibplies post *)
  thus ?case using pref_match_stable unfolding invAM_def invar1_def by(metis le_neq_implies_less)
qed


subsection \<open>Algorithm 7.1: single-loop variant\<close>

lemma Gale_Shapley7_1:
assumes "R = map ranking Q"
shows "VARS A B N a a' ai b r
 [ai = 0 \<and> a = 0 \<and> A = array 0 n \<and> B = array 0 n \<and> N = array False n]
 WHILE ai < n
 INV { invar2' (list A) (list B) (list N) ai a }
 VAR {var (list A) ({<ai+1} - {a})}
 DO b := match_array A a;
  IF \<not> N !! b
  THEN B := B[b ::= a]; N := N[b ::= True]; ai := ai + 1; a := ai
  ELSE a' := B !! b; r := R ! match_array A a';
       IF r ! a < r ! a'
       THEN B := B[b ::= a]; A := A[a' ::= A!!a' + 1]; a := a'
       ELSE A := A[a ::= A!!a + 1]
       FI
  FI
 OD
 [matching (list A) {<n} \<and> stable (list A) {<n} \<and> opti\<^sub>a (list A)]"
proof (vcg_tc, goal_cases)
  case 1 thus ?case
   by(auto simp:  pref_match_def P_set card_distinct match_def list_array index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case 3 thus ?case using pref_match_stable atLeast0_lessThan_Suc[of n] by force
next
  case (2 v A B N a a' ai)
  have R': "N !! match_array A a \<Longrightarrow>
    (R ! match_array A (B !! match_array A a) ! a < R ! match_array A (B !! match_array A a) ! (B !! match_array A a)) =
     (Q ! match_array A (B !! match_array A a) \<turnstile> a < B !! match_array A a)"
    using R_iff_P 2 assms by (metis array_abs)
  show ?case
    apply(simp only:mem_Collect_eq prod.case)
    using 2 R' pres2'[of "list A" "list B" "list N" ai a] by (metis array_abs)
qed

end


subsection \<open>Executable functional Code\<close>

definition gs_inner where
"gs_inner P R N =
  while (\<lambda>(A,B,a,b). N !! b)
    (\<lambda>(A,B,a,b).
      let a' = B !! b;
          r = R !! (P !! a' !! (A !! a')) in
      let (A, B, a) =
        if r !! a < r !! a'
        then (A[a' ::= A !! a' + 1], B[b ::= a], a')
        else (A[a ::= A !! a + 1], B, a)
      in (A, B, a, P !! a !! (A !! a)))"

definition gs :: "nat \<Rightarrow> nat array array \<Rightarrow> nat array array
  \<Rightarrow> nat array \<times> nat array \<times> bool array \<times> nat" where
"gs n P R =
  while (\<lambda>(A,B,N,ai). ai < n)
   (\<lambda>(A,B,N,ai).
     let (A,B,a,b) = gs_inner P R N (A, B, ai, P !! ai !! (A !! ai))
     in (A, B[b ::= a], N[b::=True], ai+1))
  (array 0 n, array 0 n, array False n, 0)"


definition gs1 :: "nat \<Rightarrow> nat array array \<Rightarrow> nat array array
  \<Rightarrow> nat array \<times> nat array \<times> bool array \<times> nat \<times> nat"  where
"gs1 n P R =
  while (\<lambda>(A,B,N,ai,a). ai < n)
   (\<lambda>(A,B,N,ai,a).
     let b = P !! a !! (A !! a)
     in if \<not> N !! b
        then (A, B[b ::= a], N[b ::= True], ai+1, ai+1)
        else let a' = B !! b;
                 r = R !! (P !! a' !! (A !! a'))
             in if r !!  a < r !! a'
                then (A[a' ::= A!!a' + 1], B[b ::= a], N, ai, a')
                else (A[a ::= A!!a + 1], B, N, ai, a))
  (array 0 n, array 0 n, array False n, 0, 0)"


definition "pref_array = array_of_list o map array_of_list"

lemma list_list_pref_array: "i < length Pa \<Longrightarrow> list (list (pref_array Pa) ! i) = Pa ! i"
by(simp add: pref_array_def)

fun rk_of_pref :: "nat \<Rightarrow> nat array \<Rightarrow> nat list \<Rightarrow> nat array" where
"rk_of_pref r rs (n#ns) = (rk_of_pref (r+1) rs ns)[n ::= r]" |
"rk_of_pref r rs [] = rs"

definition rank_array1 :: "nat list \<Rightarrow> nat array" where
"rank_array1 P = rk_of_pref 0 (array 0 (length P)) P"

definition rank_array :: "nat list list \<Rightarrow> nat array array" where
"rank_array = array_of_list o map rank_array1"

lemma length_rk_of_pref[simp]: "array_length(rk_of_pref v vs P) = array_length vs"
by(induction P arbitrary: v)(auto)

lemma nth_rk_of_pref:
 "\<lbrakk> length P \<le> array_length rs; i \<in> set P; distinct P; set P \<subseteq> {<array_length rs} \<rbrakk>
 \<Longrightarrow> rk_of_pref r rs P !! i = index P i + r"
by(induction P arbitrary: r i) (auto simp add: array_get_array_set_other)

lemma rank_array1_iff_pref:  "\<lbrakk> set P = {<length P}; i < length P; j < length P \<rbrakk>
 \<Longrightarrow> rank_array1 P !! i < rank_array1 P !! j \<longleftrightarrow> P \<turnstile> i < j"
by(simp add: rank_array1_def prefers_def nth_rk_of_pref card_distinct)

definition Gale_Shapley where
"Gale_Shapley P Q =
  (if Pref P Q
   then Some (fst (gs (length P) (pref_array P) (rank_array Q)))
   else None)"

definition Gale_Shapley1 where
"Gale_Shapley1 P Q =
  (if Pref P Q
   then Some (fst (gs1 (length P) (pref_array P) (rank_array Q)))
   else None)"

(*export_code Gale_Shapley_array in SML*)

context Pref
begin

lemma gs_inner:
assumes "R = rank_array Q"
assumes "invar2 (list A) (list B) (list N) ai a" "b = match_array A a"
shows "gs_inner (pref_array P) R N (A, B, a, b) = (A',B',a',b')
  \<longrightarrow> invar1 (list A') ((list B')[b' := a']) ((list N)[b' := True]) (ai+1)"
unfolding gs_inner_def
proof(rule while_rule2[where
     P = "\<lambda>(A,B,a,b). invar2 (list A) (list B) (list N) ai a \<and> b = match_array A a"
 and r = "measure (\<lambda>(A, B, a, b). Pref.var0 P (list A) {<n})"], goal_cases)
  case 1
  show ?case using assms unfolding var_def by simp
next
  case inv: (2 s)
  obtain A B a b where s: "s =  (A, B, a, b)"
    using prod_cases4 by blast
  show ?case
  proof(rule, goal_cases)
    case 1
    have *: "a < n" using s inv(1)[unfolded invar2_def] by (auto)
    hence 2: "list A ! a < n" using s inv(1)[unfolded invar2_def]
      apply simp using "*" wf_less_n by presburger
    hence "match (list A) a < n"
      by (metis "*" P_set atLeast0LessThan lessThan_iff match_def nth_mem)
    from this have **: "list B ! match (list A) a < n" using s inv[unfolded invar2_def]
      apply (simp add: array_abs ran_def) using atLeast0LessThan by blast
    have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. map list (list R) ! b ! a1 < map list (list R) ! b ! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    using rank_array1_iff_pref by(simp add: \<open>R = _\<close> length_Q array_get Q_set rank_array_def)
    have ***: "match (list A) (list B ! b) < length (list R)"  using s inv(1)[unfolded invar2_def]
      using ** by(simp add: \<open>R = _\<close> rank_array_def match_array match_less_n length_Q)
    show ?case
    using inv apply(simp only: s prod.case Let_def split: if_split)
    using inner_pres[OF R _ _ refl refl refl refl refl, of "list A" "list B" "list N" ai a b]
    unfolding invar2_def array_abs
      list_list_pref_array[OF **[unfolded n_def]] list_list_pref_array[OF *[unfolded n_def]] nth_map[OF ***]
    unfolding match_def by presburger
    case 2 show ?case
    using inv apply(simp only: s prod.case Let_def in_measure split: if_split)
    using inner_pres2[OF R _ _ refl refl refl refl refl, of "list A" "list B" "list N" ai a b]
    unfolding invar2_def array_abs
      list_list_pref_array[OF **[unfolded n_def]] list_list_pref_array[OF *[unfolded n_def]] nth_map[OF ***]
    unfolding match_def by presburger
  qed
next
  case 3
  show ?case
  proof (rule, goal_cases)
    case 1 show ?case by(rule inner_to_outer[OF 3[unfolded 1 prod.case array_abs]])
  qed
next
  case 4
  show ?case by simp
qed

lemma gs: assumes "R = rank_array Q"
shows "gs n (pref_array P) R = (A,B,N,ai) \<longrightarrow> matching (list A) {<n} \<and> stable (list A) {<n} \<and> opti\<^sub>a (list A)"
unfolding gs_def
proof(rule while_rule2[where P = "\<lambda>(A,B,N,ai). invar1 (list A) (list B) (list N) ai"
  and r = "measure(\<lambda>(A,B,N,ai). n - ai)"], goal_cases)
  case 1 show ?case
   by(auto simp: pref_match_def P_set card_distinct match_def list_array index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case (2 s)
  obtain A B N ai where s: "s =  (A, B, N, ai)"
    using prod_cases4 by blast
  have 1: "invar2 (list A) (list B) (list N) ai ai" using 2 s
    by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
  hence "ai < n" by(simp)
  show ?case using 2 s gs_inner[OF \<open>R = _ \<close> 1]
    by (auto simp: array_abs match_def list_list_pref_array[OF \<open>ai < n\<close>[unfolded n_def]]
             simp del: invar1_def split: prod.split)
next
  case 3
  thus ?case using pref_match_stable by auto
next
  case 4
  show ?case by simp
qed


lemma R_iff_P:
assumes "R = rank_array Q" "invar2' A B N ai a" "ai < n" "N ! match A a"
  "b = match A a" "a' = B ! b"
shows "(list (list R ! match A a') ! a < list (list R ! match A a') ! a')
       = (Q ! match A a' \<turnstile> a < a')"
proof -
  have R: "\<forall>b<n. \<forall>a1<n. \<forall>a2<n. R !! b !! a1 < R !! b !! a2 \<longleftrightarrow> Q ! b \<turnstile> a1 < a2"
    by (simp add: Q_set \<open>R = _\<close> length_Q array_of_list_def rank_array_def rank_array1_iff_pref)
  let ?M = "{<ai+1} - {a}"
  have A: "wf A" and M: "?M \<subseteq> {<n}" and as: "a < n" and invAB: "invAB2 A B N ?M"
      using assms(2,3) by auto
  have a': "B ! match A a \<in> ?M"
    using invAB match_less_n[OF A] as \<open>N!match A a\<close> by (metis \<alpha>_Some ranI)
  hence "B ! match A a < n" using M by auto
  thus ?thesis using assms match_less_n R by simp (metis array_get as)
qed


lemma gs1: assumes "R = rank_array Q"
shows "gs1 n (pref_array P) R = (A,B,N,ai,a) \<longrightarrow> matching (list A) {<n} \<and> stable (list A) {<n} \<and> opti\<^sub>a (list A)"
unfolding gs1_def
proof(rule while_rule2[where P = "\<lambda>(A,B,N,ai,a). invar2' (list A) (list B) (list N) ai a"
  and r = "measure(\<lambda>(A,B,N,ai,a). Pref.var P (list A) ({<ai+1} - {a}))"], goal_cases)
  case 1 show ?case
   by(auto simp: pref_match_def P_set card_distinct match_def list_array index_nth_id prefers_def opti\<^sub>a_def \<alpha>_def cong: conj_cong)
next
  case (2 s)
  obtain A B N ai a where s: "s =  (A, B, N, ai, a)"
    using prod_cases5 by blast
  have 1: "invar2' (list A) (list B) (list N) ai a" using 2(1) s
    by (auto simp: atLeastLessThanSuc_atLeastAtMost simp flip: atLeastLessThan_eq_atLeastAtMost_diff)
  have "ai < n" using 2(2) s by(simp)
  hence "a < n" using 1 by simp
  hence "match (list A) a < n" using 1 match_less_n by auto
  hence *: "list N ! match (list A) a \<Longrightarrow> list B ! match (list A) a < n"
    using s 1[unfolded invar2'_def] apply (simp add: array_abs ran_def)
    using atLeast0LessThan by blast
  have R': "list N ! match (list A) a \<Longrightarrow>
    (list (list R ! match (list A) (list B ! match (list A) a)) ! a
     < list (list R ! match (list A) (list B ! match (list A) a)) ! (list B ! match (list A) a)) =
     (Q ! match (list A) (list B ! match (list A) a) \<turnstile> a < list B ! match (list A) a)"
    using R_iff_P \<open>R = _\<close> 1 \<open>ai < n\<close> by blast
  show ?case
    using s apply (simp add: Let_def)
    unfolding list_list_pref_array[OF \<open>a < n\<close>[unfolded n_def]] array_abs
    using list_list_pref_array[OF *[unfolded n_def]] (* conditional, cannot unfold :-( *)
      pres2'[OF 1 \<open>ai < n\<close> refl refl refl refl refl] R'
    apply(intro conjI impI) by (auto simp: match_def)
    (* w/o intro too slow because of conditional eqn above *)
next
  case 3 thus ?case using pref_match_stable atLeast0_lessThan_Suc[of n] by force
next
  case 4 show ?case by simp
qed

end

theorem gs: "\<lbrakk> Pref P Q; n = length P \<rbrakk> \<Longrightarrow>
 \<exists>A. Gale_Shapley P Q = Some A
   \<and> Pref.matching P (list A) {<n} \<and> Pref.stable P Q (list A) {<n} \<and> Pref.opti\<^sub>a P Q (list A)"
unfolding Gale_Shapley_def using Pref.gs
by (metis fst_conv surj_pair)

theorem gs1: "\<lbrakk> Pref P Q; n = length P \<rbrakk> \<Longrightarrow>
 \<exists>A. Gale_Shapley1 P Q = Some A
   \<and> Pref.matching P (list A) {<n} \<and> Pref.stable P Q (list A) {<n} \<and> Pref.opti\<^sub>a P Q (list A)"
unfolding Gale_Shapley1_def using Pref.gs1
by (metis fst_conv surj_pair)


text \<open>Two examples from Gusfield and Irving:\<close>

lemma "list_of_array (the (Gale_Shapley
  [[3,0,1,2], [1,2,0,3], [1,3,2,0], [2,0,3,1]] [[3,0,2,1], [0,2,1,3], [0,1,2,3], [3,0,2,1]]))
  = [0,1,0,1]"
by eval

lemma "list_of_array (the (Gale_Shapley
  [[4,6,0,1,5,7,3,2], [1,2,6,4,3,0,7,5], [7,4,0,3,5,1,2,6], [2,1,6,3,0,5,7,4],
   [6,1,4,0,2,5,7,3], [0,5,6,4,7,3,1,2], [1,4,6,5,2,3,7,0], [2,7,3,4,6,1,5,0]]
  [[4,2,6,5,0,1,7,3], [7,5,2,4,6,1,0,3], [0,4,5,1,3,7,6,2], [7,6,2,1,3,0,4,5],
   [5,3,6,2,7,0,1,4], [1,7,4,2,3,5,6,0], [6,4,1,0,7,5,3,2], [6,3,0,4,1,2,5,7]]))
  = [0, 1, 0, 5, 0, 0, 0, 2]"
by eval

end