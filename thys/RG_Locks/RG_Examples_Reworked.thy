
(*
Title:         RG Examples Reworked
Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
Year:          2026
License:       BSD 2-Clause
Maintainer(s): Robert Colvin <r.colvin@uq.edu.au>
               Peter Hoefner <peter@hoefner-online.de>
               Roger Su <roger.c.su@proton.me>
*)

section \<open>Examples Reworked\<close>

text \<open>Reworking of the examples in the original library, using our new
framework's syntax and tactics.\<close>

theory RG_Examples_Reworked
  imports RG_Annotated_Methods
begin

(*============================================================================*)
subsection \<open>Set Elements of an Array to Zero\<close>

record Example1 =
  A :: "nat list"

theorem Example1:
  "global_init: \<lbrace> n < length \<acute>A \<rbrace>
   global_rely: id(A)
    \<parallel> i < n @

   { \<lbrace> i < length \<acute>A \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rbrace> }

     \<acute>A := \<acute>A[i := 0]

   { \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j<n. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rbrace>,
     \<lbrace> \<acute>A ! i = 0 \<rbrace> }

   global_guar: \<lbrace> True \<rbrace>
   global_post: \<lbrace> \<forall>i < n. \<acute>A ! i = 0 \<rbrace>"
  by method_rg_try_each

theorem Example1':
  "global_init: \<lbrace> N = length \<acute>A \<rbrace>
   global_rely: \<lbrace> \<ordmasculine>A = \<ordfeminine>A \<rbrace>
   \<parallel> i < N @
   { \<lbrace> True \<rbrace>,
     \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rbrace> }
     \<acute>A := \<acute>A [i := f i] \<sslash> \<lbrace> i < N \<and> N = length \<acute>A \<rbrace>
   { \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rbrace>,
     \<lbrace> \<acute>A ! i = f i \<rbrace> }
   global_guar: \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<rbrace>
   global_post: \<lbrace> take N \<acute>A = map f [0 ..< N] \<rbrace>"
proof method_multi_parallel
  case post
  then show ?case
    apply clarsimp
    apply standard
     apply standard
     apply force
    by (clarsimp simp add: map_upt_eqI)
qed (fastforce+)

theorem Example1'':
  "valid_multipar: annotated 
  global_init: \<lbrace> length \<acute>A = Nz \<rbrace> 
  global_rely: \<lbrace> \<ordfeminine>A = \<ordmasculine>A \<rbrace>
   \<parallel> i < Nz @
   { \<lbrace> True \<rbrace>,
     \<lbrace>  length \<ordfeminine>A = length \<ordmasculine>A \<and> \<ordfeminine>A ! i = \<ordmasculine>A ! i\<rbrace> }
     (\<acute>A := \<acute>A [i := f i])- \<sslash> \<lbrace> length \<acute>A = Nz \<rbrace>
   { \<lbrace> length \<ordfeminine>A = length \<ordmasculine>A \<and> (\<forall>j. i \<noteq> j \<longrightarrow>   \<ordfeminine>A ! j = \<ordmasculine>A ! j ) \<rbrace>,
     \<lbrace> \<acute>A ! i = f i \<rbrace> }
   global_guar: \<lbrace> length \<ordmasculine>A = Nz \<longrightarrow> length \<ordfeminine>A = length \<ordmasculine>A\<rbrace>
   global_post: \<lbrace> take Nz \<acute>A = map f [0 ..< Nz] \<rbrace>"
  apply (decompose_and_discharge simps: atLeast_upt; simp_divide_blast)
  by (simp add: map_upt_eqI)

text \<open>These examples demonstrate the syntax for using a range for process ids starting somewhere other than 0\<close>
lemma Example1_parameterized:
  assumes "k < t"
  shows "valid_multipar: annotated
    global_init: \<lbrace>t*n < length \<acute>A\<rbrace>
    global_rely: \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>i<n. \<ordmasculine>A!(k*n+i)=\<ordfeminine>A!(k*n+i))\<rbrace>
    \<parallel> k*n \<le> i < (Suc k) *n @
      {\<lbrace>t*n < length \<acute>A\<rbrace>,
       \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> \<ordmasculine>A!i = \<ordfeminine>A!i\<rbrace>}
        (\<acute>A:=\<acute>A[i:=0])-
      {\<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>j<length \<ordmasculine>A . i\<noteq>j \<longrightarrow> \<ordmasculine>A!j = \<ordfeminine>A!j)\<rbrace>,
      \<lbrace>\<acute>A!i=0\<rbrace>}   
    global_guar: \<lbrace>t*n < length \<ordmasculine>A \<and> length \<ordmasculine>A=length \<ordfeminine>A \<and>
                  (\<forall>i<length \<ordmasculine>A . (i<k*n \<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i) \<and> 
                  ((Suc k)*n \<le> i \<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i))\<rbrace>
    global_post: \<lbrace>\<forall>i<n. \<acute>A!(k*n+i) = 0\<rbrace>"
  apply (decompose_and_discharge ; simp_divide_blast)
    apply (metis Groups.mult_ac(2) Suc_leI assms less_add_same_cancel1 less_le_not_le linear nat_0_less_mult_iff nat_mult_less_cancel1 nth_list_update_eq order_le_less_trans times_nat.simps(2) trans_less_add2)
   apply (metis add.commute add_less_imp_less_left le_iff_add)
  by (smt  Suc_leI assms dual_order.strict_trans1 less_or_eq_imp_le mult_Suc mult_le_mono1)

lemma Example1_parameterized_with_invariant:
  assumes "k < t"
  shows "valid_multipar: annotated
  global_init: \<lbrace>t*n < length \<acute>A\<rbrace>
  global_rely: \<lbrace>length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>i<n. \<ordmasculine>A!(k*n+i)=\<ordfeminine>A!(k*n+i))\<rbrace>
  \<parallel> k*n \<le> i < (Suc k) *n @
    {UNIV,
    \<lbrace>length \<ordmasculine>A=length \<ordfeminine>A \<and> \<ordmasculine>A!i = \<ordfeminine>A!i\<rbrace>}
      (\<acute>A:=\<acute>A[i:=0])- \<sslash> \<lbrace>t*n < length \<acute>A\<rbrace>
    {\<lbrace>length \<ordmasculine>A=length \<ordfeminine>A \<and> (\<forall>j<length \<ordmasculine>A . i\<noteq>j \<longrightarrow> \<ordmasculine>A!j = \<ordfeminine>A!j)\<rbrace>,
    \<lbrace>\<acute>A!i=0\<rbrace>}
   
  global_guar: \<lbrace>t*n < length \<ordmasculine>A \<longrightarrow> length \<ordmasculine>A=length \<ordfeminine>A \<and>
                (\<forall>i<length \<ordmasculine>A . (i<k*n \<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i) \<and> 
                ((Suc k)*n \<le> i \<longrightarrow> \<ordmasculine>A!i = \<ordfeminine>A!i))\<rbrace>
  global_post: \<lbrace>\<forall>i<n. \<acute>A!(k*n+i) = 0\<rbrace>"
  apply (decompose_and_discharge ; simp_divide_blast)
    apply (metis Groups.mult_ac(2) Suc_leI assms less_add_same_cancel1 less_le_not_le linear nat_0_less_mult_iff nat_mult_less_cancel1 nth_list_update_eq order_le_less_trans times_nat.simps(2) trans_less_add2)
   apply (metis add.commute add_less_imp_less_left le_iff_add)
  by (smt (verit) Suc_leI assms less_or_eq_imp_le mult.commute mult_Suc_right nat_mult_le_cancel_disj order_le_less_trans) 

(*============================================================================*)
subsection \<open>Increment a Variable in Parallel\<close>

record Example2 =
  x   :: nat (* shared var *)
  c_0 :: nat (* aux var of Thread 0 *)
  c_1 :: nat (* aux var of Thread 1 *)

theorem Example2b:
  "validpar: 
  {\<lbrace> \<acute>c_0 = 0 \<and> \<acute>c_1 = 0 \<and> \<acute>x = 0\<rbrace>, ids({c_0, c_1, x})}
    {\<lbrace> \<acute>c_0 = 0 \<rbrace>, id(c_0)  }
      \<langle>\<acute>x := \<acute>x + 1 ;; \<acute>c_0 := 1\<rangle>a \<sslash> \<lbrace> \<acute>x = \<acute>c_0 + \<acute>c_1 \<rbrace>
   { id(c_1), \<lbrace> \<acute>c_0 = 1 \<rbrace>} 
  \<parallel>a
    {\<lbrace> \<acute>c_1 = 0 \<rbrace>, id(c_1)}
      \<langle>\<acute>x := \<acute>x + 1 ;; \<acute>c_1 := 1\<rangle>a \<sslash> \<lbrace> \<acute>x = \<acute>c_0 + \<acute>c_1 \<rbrace>
   { id(c_0), \<lbrace> \<acute>c_1 = 1 \<rbrace>}
  { UNIV, \<lbrace> \<acute>x = 2 \<rbrace> }"
  by (decompose_and_discharge intros: valid_binary_par; simp_divide_blast)

text \<open>Intuition of the lemma below:
Consider the sum of a function "b(k)" with "k" ranging from 0 to n-1.
Let "j" be an index in this range, and assume "b(j) = 0".
Then, replacing b(j) with 1 in the sum, the result is the same as
adding 1 to the original sum.\<close>

lemma sum_split:
  "(j::nat) < (n::nat)
  \<Longrightarrow> sum a {0..<n} = sum a {0..<j} + a j + sum a {j+1..<n}"
  by (metis Suc_eq_plus1 bot_nat_0.extremum group_cancel.add1 le_eq_less_or_eq sum.atLeastLessThan_concat sum.atLeast_Suc_lessThan)

lemma Example2_lemma2_replace:
  assumes "(j::nat) < n"
      and "b' = b(j:=xx::nat)"
    shows "(\<Sum> i = 0 ..< n. b' i) = (\<Sum> i = 0 ..< n. b i) - b j + xx"
  using assms sum_split[of j n b] sum_split[of j n b'] by auto

lemma Example2_lemma2_Suc0[simp]:
  assumes "(j::nat) < n"
      and "b j = 0"
      and "b' = b(j:=1)"
    shows "Suc (\<Sum> i::nat = 0 ..< n. b i) = (\<Sum> i = 0 ..< n. b' i)"
  by (metis assms Example2_lemma2_replace Suc_eq_plus1 diff_zero)

record Example2_param =
  y ::  nat         (* shared var *)
  C :: "nat \<Rightarrow> nat" (* aux var for each thread *)

lemma Example2_local:
  "i < n \<Longrightarrow>
  { \<lbrace> \<acute>C i = 0 \<rbrace>,
     id(C @ i) }

    Basic ((\<acute>y \<leftarrow> \<acute>y + 1) \<circ>> (\<acute>C \<leftarrow> \<acute>C(i:=1)))
    \<sslash> \<lbrace> \<acute>y = (\<Sum> k::nat = 0 ..< n. \<acute>C k) \<rbrace>

   { \<lbrace> \<forall> j < n. i \<noteq> j \<longrightarrow> \<ordmasculine>C j = \<ordfeminine>C j \<rbrace>,
     \<lbrace> \<acute>C i = 1 \<rbrace> }"
  by method_rg_try_each

theorem Example2_param:
  assumes "0 < n" shows
  "global_init: \<lbrace> \<acute>y = 0 \<and> sum \<acute>C {0 ..< n} = 0 \<rbrace>
   global_rely: id(C) \<inter> id(y)
    \<parallel> i < n @
   { \<lbrace> \<acute>C i = 0 \<rbrace>,
     id(C @ i) }
     Basic ((\<acute>y \<leftarrow> \<acute>y + 1) \<circ>> (\<acute>C \<leftarrow> \<acute>C(i:=1)))
     \<sslash> \<lbrace> \<acute>y = sum \<acute>C {0 ..< n} \<rbrace>
   { \<lbrace> \<forall> j < n. i \<noteq> j \<longrightarrow> \<ordmasculine>C j = \<ordfeminine>C j \<rbrace>,
     \<lbrace> \<acute>C i = 1 \<rbrace> }
   global_guar: \<lbrace> True \<rbrace>
   global_post: \<lbrace> \<acute>y = n \<rbrace>"
proof method_multi_parallel
  case post show ?case using assms by auto
qed (fastforce+)

text "As above, but using an explicit annotation and a different method."

theorem Example2_param_with_expansion:
  assumes "0 < n" shows "valid_multipar: annotated
  global_init: \<lbrace> \<acute>y = 0 \<and> sum \<acute>C {0 ..< n} = 0 \<rbrace>
  global_rely: id(C) \<inter> id(y)
    \<parallel> i < n @
  { \<lbrace> \<acute>C i = 0 \<rbrace>, id(C @ i) }
    \<langle>\<acute>y := \<acute>y + 1 ;; \<acute>C[i] := 1\<rangle>a \<sslash> \<lbrace> \<acute>y = sum \<acute>C {0 ..< n} \<rbrace>
  { \<lbrace> \<forall> j < n. i \<noteq> j \<longrightarrow> \<ordmasculine>C j = \<ordfeminine>C j \<rbrace>, \<lbrace> \<acute>C i = 1 \<rbrace> }
  global_guar: UNIV
  global_post: \<lbrace> \<acute>y = n \<rbrace>"
  by (decompose_and_discharge ; simp_divide_blast useful: assms)

(*============================================================================*)
subsection \<open>FindP\<close>

text \<open>Titled "Find Least Element" in the original.\<close>

text "This helper lemma is an equivalent version of @{text mod_aux} found in the original"

lemma mod_aux :
  "a mod (n::nat) = i \<Longrightarrow>  a < j \<and> j < a + n \<Longrightarrow> j mod n \<noteq> i"
  using mod_eq_dvd_iff_nat nat_dvd_not_less by force

text \<open>This is the "findP" problem. Assuming that n divides m,
we divide the search for a P-element, by partitioning the indices into the
congruence classes modulo n, and letting Thread i search through the indices
that are "i mod n". 

m: the size of the array (arraySize)
n: the number of threads (numThreads)

P: the predicate
B: the array

X: "X i" is the next index to be checked by Thread i
Y: "Y i" is either
   the out-of-bound default "m + i" if Thread i hasn't found a P-element,
   or the index of the first P-element found by Thread i.

Assume: n divides m.
\<close>

record Example3 = (* see above for comments *)
  X :: "nat \<Rightarrow> nat"
  Y :: "nat \<Rightarrow> nat"

lemma Example3:
  (* assumes "m mod n=0" *) (* Assumption not needed *)
  shows "valid_multipar: annotated
  global_init: \<lbrace>\<forall>i < n. \<acute>X i = i \<and> \<acute>Y i = m + i \<rbrace>
  global_rely: \<lbrace> \<ordmasculine>X = \<ordfeminine>X \<and> \<ordmasculine>Y = \<ordfeminine>Y\<rbrace>
    \<parallel> i < n @

  { \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i)\<rbrace>,
    \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordfeminine>Y j \<le> \<ordmasculine>Y j) \<and> \<ordmasculine>X i = \<ordfeminine>X i \<and> \<ordmasculine>Y i = \<ordfeminine>Y i\<rbrace> } 

    WHILEa (\<forall> j < n. \<acute>X i < \<acute>Y j) DO
      {stable_guard: \<lbrace>\<acute>X i < \<acute>Y i\<rbrace>} 
      IF. P(B!(\<acute>X i)) THEN 
        \<acute>Y[i] := \<acute>X i 
      ELSE 
        \<acute>X[i] := \<acute>X i + n
      FI 
    OD

  { \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordmasculine>X j = \<ordfeminine>X j \<and> \<ordmasculine>Y j = \<ordfeminine>Y j) \<and> \<ordfeminine>Y i \<le> \<ordmasculine>Y i\<rbrace>,
    \<lbrace> (\<acute>X i) mod n = i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j))
    \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i)
    \<and> (\<exists>j<n. \<acute>Y j \<le> \<acute>X i) \<rbrace> }

  global_guar: \<lbrace>True\<rbrace>
  global_post: \<lbrace> \<forall> i < n. (\<acute>X i) mod n=i
               \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j))
               \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and>\<acute>Y i\<le> m+i)
               \<and> (\<exists>j<n. \<acute>Y j \<le> \<acute>X i) \<rbrace>"
  apply (decompose_and_discharge )
      apply (metis order_trans)
    using linorder_not_le apply blast
   apply (metis linorder_neqE_nat mod_aux)
  by force


text "Below is the original version of the theorem, and is immediately
derivable from the above. We include some formatting changes (such as
line breaks) for better readability."

lemma Example3_original: "m mod n=0 \<Longrightarrow>
 \<turnstile> COBEGIN SCHEME [0\<le>i<n]

  (WHILE (\<forall> j < n. \<acute>X i < \<acute>Y j) DO
     IF P(B!(\<acute>X i)) THEN \<acute>Y:=\<acute>Y (i:=\<acute>X i) ELSE \<acute>X:= \<acute>X (i:=(\<acute>X i)+ n) FI
   OD,

 \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i)\<rbrace>,

 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordfeminine>Y j \<le> \<ordmasculine>Y j) \<and> \<ordmasculine>X i = \<ordfeminine>X i \<and> \<ordmasculine>Y i = \<ordfeminine>Y i\<rbrace>,

 \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordmasculine>X j = \<ordfeminine>X j \<and> \<ordmasculine>Y j = \<ordfeminine>Y j) \<and> \<ordfeminine>Y i \<le> \<ordmasculine>Y i\<rbrace>,

 \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i) \<and> (\<exists>j<n. \<acute>Y j \<le> \<acute>X i) \<rbrace>)

 COEND
 SAT [
   \<lbrace> \<forall> i < n. \<acute>X i = i \<and> \<acute>Y i = m+i \<rbrace>,

   \<lbrace>\<ordmasculine>X=\<ordfeminine>X \<and> \<ordmasculine>Y=\<ordfeminine>Y\<rbrace>,

   \<lbrace>True\<rbrace>,

   \<lbrace>\<forall> i < n. (\<acute>X i) mod n=i \<and>
             (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and>
             (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and>\<acute>Y i\<le> m+i) \<and>
             (\<exists>j<n. \<acute>Y j \<le> \<acute>X i)\<rbrace>]"
  by (rule valid_multipar_with_internal_rg[OF Example3]; simp)

end
