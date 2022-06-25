section \<open>Examples\label{sec:examples}\<close>

theory Examples
  imports Prefix_Free_Code_Combinators
begin

text \<open>The following introduces a few examples for encoders:\<close>

notepad
begin \<^marker>\<open>tag visible\<close>
  define example1 where "example1 = N\<^sub>e \<times>\<^sub>e N\<^sub>e"

  text \<open>This is an encoder for a pair of natural numbers using exponential Golomb codes.\<close>

  text \<open>Given a pair it is possible to estimate the number of bits necessary to
    encode it using the @{term "bit_count"} lemmas.\<close>

  have "bit_count (example1 (0,1)) = 4"
    by (simp add:example1_def dependent_bit_count exp_golomb_bit_count_exact)

  text \<open>Note that a finite bit count automatically implies that the encoded element is in the domain
  of the encoding function. This means usually it is possible to establish a bound on the size of
  the datastructure and verify that the value is encodable simultaneously.\<close>

  hence "(0,1) \<in> dom example1"
    by (intro bit_count_finite_imp_dom, simp)

  define example2
    where "example2 = [0..<42] \<rightarrow>\<^sub>e Nb\<^sub>e 314"

  text \<open>The second example illustrates the use of the combinator @{term "(\<rightarrow>\<^sub>e)"}, which allows
  encoding functions with a known finite encodable domain, here we assume the values are smaller
  than @{term "314"} on the domain @{term "{..<42}"}.\<close>

  have "bit_count (example2 f) = 42*9" (is "?lhs = ?rhs")
    if a:"f \<in> {0..<42} \<rightarrow>\<^sub>E {0..<314}" for f
  proof -
    have "?lhs = (\<Sum>x\<leftarrow>[0..<42]. bit_count (Nb\<^sub>e 314 (f x)))"
      using a by (simp add:example2_def fun_bit_count PiE_def)
    also have "... = (\<Sum>x\<leftarrow>[0..<42]. ereal (floorlog 2 313))"
      using a Pi_def PiE_def bounded_nat_bit_count
      by (intro arg_cong[where f="sum_list"] map_cong, auto)
    also have "... = ?rhs"
      by (simp add: compute_floorlog sum_list_triv)
    finally show ?thesis by simp
  qed

  define example3
    where "example3 = N\<^sub>e \<Join>\<^sub>e (\<lambda>n. [0..<42] \<rightarrow>\<^sub>e Nb\<^sub>e n)"

  text \<open>The third example is more complex and illustrates the use of dependent encoders, consider
  a function with domain @{term "{..<(42::nat)}"} whose values are natural numbers in the interval
  @{term "{..<n::nat}"}. Let us assume the bound is not known in advance and needs to be encoded
  as well. This can be done using a dependent product encoding, where the first component encodes
  the bound and the second component is an encoder parameterized by that value.\<close>

end

end