(* Title:      	   Reworked RG Examples
   Author(s):     Robert Colvin, Scott Heiner, Peter Hoefner, Roger Su
   License:       BSD 2-Clause
   Maintainer(s): Roger Su <roger.c.su@proton.me>
                  Peter Hoefner <peter@hoefner-online.de>
*)

section \<open>Examples Reworked\<close>

text \<open>The examples in the original library~\cite{RGinIsabelle}, 
expressed using our new syntax, and proved using our new tactics.\<close>

theory RG_Examples_Reworked

imports RG_Annotated_Commands

begin
declare [[syntax_ambiguity_warning = false]]
(*============================================================================*)
subsection \<open>Setting Elements of an Array to Zero\<close>

record Example1 =
  A :: "nat list"

theorem Example1:
  "global_init: \<lbrace> n < length \<acute>A \<rbrace>
   global_rely: id(A)
    \<parallel> i < n @
     { \<lbrace> i < length \<acute>A \<rbrace>,
       \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> \<ordmasculine>A ! i = \<ordfeminine>A ! i \<rbrace> }
   \<acute>A := \<acute>A[i := 0]
     { \<lbrace> length \<ordmasculine>A = length \<ordfeminine>A \<and> (\<forall>j < n. i \<noteq> j \<longrightarrow> \<ordmasculine>A ! j = \<ordfeminine>A ! j) \<rbrace>,
       \<lbrace> \<acute>A ! i = 0 \<rbrace> }
   global_guar: \<lbrace> True \<rbrace>
   global_post: \<lbrace> \<forall>i < n. \<acute>A ! i = 0 \<rbrace>"
  by method_rg_try_each

theorem Example1'':
  "annotated global_init: \<lbrace> length \<acute>A = N \<rbrace> global_rely: \<lbrace> \<ordfeminine>A = \<ordmasculine>A \<rbrace>
   \<parallel> i < N @
   { \<lbrace> True \<rbrace>,
     \<lbrace>  length \<ordfeminine>A = length \<ordmasculine>A \<and> \<ordfeminine>A ! i = \<ordmasculine>A ! i\<rbrace> }
     (\<acute>A := \<acute>A [i := f i])- \<sslash> \<lbrace>length \<acute>A = N \<rbrace>
   { \<lbrace> length \<ordfeminine>A = length \<ordmasculine>A \<and> (\<forall>j. i \<noteq> j \<longrightarrow>   \<ordfeminine>A ! j = \<ordmasculine>A ! j ) \<rbrace>,
     \<lbrace> \<acute>A ! i = f i \<rbrace> }
   global_guar: \<lbrace> length \<ordfeminine>A = length \<ordmasculine>A\<rbrace>
   global_post: \<lbrace> take N \<acute>A = map f [0 ..< N] \<rbrace>"
  apply rg_proof_expand
  by (fastforce split: if_splits simp: map_upt_eqI)

(*============================================================================*)
subsection \<open>Incrementing a Variable in Parallel\<close>

text \<open>Two Components\<close>

record Example2 =
  x   :: nat (* shared var *)
  c_0 :: nat (* aux var of Thread 0 *)
  c_1 :: nat (* aux var of Thread 1 *)

lemma ex2_leftside:  
  "{ \<lbrace> \<acute>c_0 = 0 \<rbrace>, id(c_0) }
     Basic ((\<acute>x \<leftarrow> \<acute>x + 1) \<circ>> (\<acute>c_0 \<leftarrow> 1))
   \<sslash> \<lbrace> \<acute>x = \<acute>c_0 + \<acute>c_1 \<rbrace>
   { id(c_1), \<lbrace> \<acute>c_0 = 1 \<rbrace>}"
  by method_rg_try_each

lemma ex2_rightside:  
  "{ \<lbrace> \<acute>c_1 = 0 \<rbrace>, id(c_1) }
     Basic ((\<acute>x \<leftarrow> \<acute>x + 1) \<circ>> (\<acute>c_1 \<leftarrow> 1))
   \<sslash> \<lbrace> \<acute>x = \<acute>c_0 + \<acute>c_1 \<rbrace>
   { id(c_0), \<lbrace> \<acute>c_1 = 1 \<rbrace>}"
  by method_rg_try_each

theorem Example2b:
  "{ \<lbrace> \<acute>c_0 = 0 \<and> \<acute>c_1 = 0 \<rbrace>, ids({c_0, c_1}) }
   (Basic ((\<acute>x \<leftarrow> \<acute>x + 1) \<circ>> (\<acute>c_0 \<leftarrow> 1))) \<parallel> (Basic ((\<acute>x \<leftarrow> \<acute>x + 1) \<circ>> (\<acute>c_1 \<leftarrow> 1)))
   \<sslash> \<lbrace> \<acute>x = \<acute>c_0 + \<acute>c_1 \<rbrace>
   { UNIV, \<lbrace> True \<rbrace> }"
  using ex2_leftside ex2_rightside (* needs to instantiate *)
  by (rule rg_binary_parallel_invar_conseq; blast)

text \<open>Parameterised\<close>

lemma sum_split:
  "(j::nat) < (n::nat)
  \<Longrightarrow> sum a {0..<n} = sum a {0..<j} + a j + sum a {j+1..<n}"
  by (metis Suc_eq_plus1 bot_nat_0.extremum group_cancel.add1 le_eq_less_or_eq sum.atLeastLessThan_concat sum.atLeast_Suc_lessThan)

text \<open>Intuition of the lemma above:
Consider the sum of a function @{term \<open>b k\<close>} with @{term k} ranging 
from 0 to @{term \<open>n - 1\<close>}.
Let @{term j} be an index in this range, and assume @{term \<open>b j = 0\<close>}.
Then, replacing @{term \<open>b j\<close>} with 1 in the sum, the result is the
same as adding 1 to the original sum.\<close>

lemma Example2_lemma2_replace:
  assumes "(j::nat) < n"
      and "b' = b(j:=xx::nat)"
    shows "(\<Sum> i = 0 ..< n. b' i) = (\<Sum> i = 0 ..< n. b i) - b j + xx"
  apply (subst sum_split, rule assms(1))
  apply (subst sum_split, rule assms(1))
  using assms(2) by clarsimp

lemma Example2_lemma2_Suc0[simp]:
  assumes "(j::nat) < n"
      and "b j = 0"
      and "b' = b(j:=1)"
    shows "Suc (\<Sum> i::nat = 0 ..< n. b i) = (\<Sum> i = 0 ..< n. b' i)"
  using assms  Example2_lemma2_replace 
  by fastforce

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
  case post
  then show ?case
    using assms by (clarsimp, fastforce)
next
  case body
  then show ?case
    by method_rg_try_each
qed (fastforce+)

text \<open>As above, but using an explicit annotation and a different method.\<close>

theorem Example2_param_with_expansion:
  assumes "0 < n" shows "annotated
  global_init: \<lbrace> \<acute>y = 0 \<and> sum \<acute>C {0 ..< n} = 0 \<rbrace>
  global_rely: id(C) \<inter> id(y)
    \<parallel> i < n @
  { \<lbrace> \<acute>C i = 0 \<rbrace>,
    id(C @ i) }
    (Basic ((\<acute>y \<leftarrow> \<acute>y + 1) \<circ>> (\<acute>C \<leftarrow> \<acute>C(i:=1))))-
    \<sslash> \<lbrace> \<acute>y = sum \<acute>C {0 ..< n} \<rbrace>
  { \<lbrace> \<forall> j < n. i \<noteq> j \<longrightarrow> \<ordmasculine>C j = \<ordfeminine>C j \<rbrace>,
    \<lbrace> \<acute>C i = 1 \<rbrace> }
  global_guar: \<lbrace> True \<rbrace>
  global_post: \<lbrace> \<acute>y = n \<rbrace>"
  apply rg_proof_expand
  using assms by (fastforce split: if_splits)

(*============================================================================*)
subsection \<open>FindP\<close>

text \<open>Titled ``Find Least Element'' in the original~\cite{RGinIsabelle},
the "findP" problem assumes that @{text n} divides @{text m},
and runs @{text n} threads in parallel 
to search through a length-@{text m} array @{text B} 
for an element that satisfies a predicate @{text P}. 
The indices of the array @{text B} are partitioned 
into the congruence-classes modulo @{text n},
where Thread @{text i} searches through the indices
that are congruent to @{text i} mod @{text n}.

In the program, @{term \<open>X i\<close>} is the next index to be checked by 
Thread @{text i}. Meanwhile, @{term \<open>Y i\<close>} is either
the out-of-bound default @{term \<open>m + i\<close>} if Thread @{text i} has not 
found a @{text P}-element,
or the index of the first @{text P}-element found by Thread @{text i}.\<close>

text \<open>The first helper lemma: an equivalent version of @{text mod_aux}
found in the original.\<close>

lemma mod_aux :
  "a mod (n::nat) = i \<Longrightarrow>  a < j \<and> j < a + n \<Longrightarrow> j mod n \<noteq> i"
  using mod_eq_dvd_iff_nat nat_dvd_not_less by force

record Example3 =
  X :: "nat \<Rightarrow> nat"
  Y :: "nat \<Rightarrow> nat"

lemma Example3:
  assumes "m mod n=0" shows "annotated
  global_init: \<lbrace>\<forall>i < n. \<acute>X i = i \<and> \<acute>Y i = m + i \<rbrace>
  global_rely: \<lbrace> \<ordmasculine>X = \<ordfeminine>X \<and> \<ordmasculine>Y = \<ordfeminine>Y\<rbrace>
    \<parallel> i < n @

  { \<lbrace>(\<acute>X i) mod n=i \<and> (\<forall>j<\<acute>X i. j mod n=i \<longrightarrow> \<not>P(B!j)) \<and> (\<acute>Y i<m \<longrightarrow> P(B!(\<acute>Y i)) \<and> \<acute>Y i\<le> m+i)\<rbrace>,
    \<lbrace>(\<forall>j<n. i\<noteq>j \<longrightarrow> \<ordfeminine>Y j \<le> \<ordmasculine>Y j) \<and> \<ordmasculine>X i = \<ordfeminine>X i \<and> \<ordmasculine>Y i = \<ordfeminine>Y i\<rbrace> } 

    WHILEa (\<forall> j < n. \<acute>X i < \<acute>Y j) DO
      {stable_guard: \<lbrace>\<acute>X i < \<acute>Y i\<rbrace>} 
      IFa P(B!(\<acute>X i)) THEN 
        (\<acute>Y[i] := \<acute>X i)- 
      ELSE 
        (\<acute>X[i] := \<acute>X i + n)-
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
  apply rg_proof_expand (* takes a bit long *)
           apply fastforce+
    apply (metis linorder_neqE_nat mod_aux)
   apply (metis antisym_conv3 mod_aux)
  by (metis leD mod_less_eq_dividend)

text \<open>Below is the original version of the theorem, and is immediately
derivable from the above. We include some formatting changes (such as
line breaks) for better readability.\<close>

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
