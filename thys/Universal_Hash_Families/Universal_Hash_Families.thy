section \<open>Introduction and Definition\<close>

theory Universal_Hash_Families
  imports "HOL-Probability.Independent_Family"
begin

text \<open>Universal hash families are commonly used in randomized algorithms and data structures to
randomize the input of algorithms, such that probabilistic methods can be employed without requiring
any assumptions about the input distribution.

If we regard a family of hash functions from a domain $D$ to a finite range $R$ as a uniform probability
space, then the family is $k$-universal if:
\begin{itemize}
\item For each $x \in D$ the evaluation of the functions at $x$ forms a uniformly distributed random variable on $R$.
\item The evaluation random variables for $k$ or fewer distinct domain elements form an
independent family of random variables.
\end{itemize}

This definition closely follows the definition from Vadhan~\<^cite>\<open>\<open>\textsection 3.5.5\<close> in "vadhan2012"\<close>, with the minor
modification that independence is required not only for exactly $k$, but also for \emph{fewer} than $k$ distinct
domain elements. The correction is due to the fact that in the corner case where $D$ has fewer than $k$ elements,
the second part of their definition becomes void. In the formalization this helps avoid an unnecessary assumption in
the theorems.

The following definition introduces the notion of $k$-wise independent random variables:\<close>

definition (in prob_space) k_wise_indep_vars where
  "k_wise_indep_vars k M' X I =
    (\<forall>J \<subseteq> I. card J \<le> k \<longrightarrow> finite J \<longrightarrow> indep_vars M' X J)"

lemma (in prob_space) k_wise_indep_vars_subset:
  assumes "k_wise_indep_vars k M' X I"
  assumes "J \<subseteq> I"
  assumes "finite J"
  assumes "card J \<le> k"
  shows "indep_vars M' X J"
  using assms
  by (simp add:k_wise_indep_vars_def)

text \<open>Similarly for a finite non-empty set $A$ the predicate @{term "uniform_on X A"} indicates that
the random variable is uniformly distributed on $A$:\<close>

definition (in prob_space) "uniform_on X A = (
  distr M (count_space UNIV) X = uniform_measure (count_space UNIV) A \<and>
  A \<noteq> {} \<and> finite A \<and> random_variable (count_space UNIV) X)"

lemma (in prob_space) uniform_onD:
  assumes "uniform_on X A"
  shows "prob {\<omega> \<in> space M. X \<omega> \<in> B} = card (A \<inter> B) / card A"
proof -
  have "prob {\<omega> \<in> space M. X \<omega> \<in> B} = prob (X -` B \<inter> space M)"
    by (subst Int_commute, simp add:vimage_def Int_def)
  also have "... = measure (distr M (count_space UNIV) X) B"
    using assms by (subst measure_distr, auto simp:uniform_on_def)
  also have "... = measure (uniform_measure (count_space UNIV) A) B"
    using assms by (simp add:uniform_on_def)
  also have "... = card (A \<inter> B) / card A"
    using assms by (subst measure_uniform_measure, auto simp:uniform_on_def)+
  finally show ?thesis by simp
qed

text \<open>With the two previous definitions it is possible to define the $k$-universality condition for a family
of hash functions from $D$ to $R$:\<close>

definition (in prob_space) "k_universal k X D R = (
  k_wise_indep_vars k (\<lambda>_. count_space UNIV) X D \<and>
  (\<forall>i \<in> D. uniform_on (X i) R))"

text \<open>Note: The definition is slightly more generic then the informal specification from above.
This is because usually a family is formed by a single function with a variable seed parameter. Instead of
choosing a random function from a probability space, a random seed is chosen from the probability space
which parameterizes the hash function.

The following section contains some preliminary results about independent families
of random variables.
Section~\ref{sec:carter_wegman} introduces the Carter-Wegman hash family, which is an
explicit construction of $k$-universal families for arbitrary $k$ using polynomials over finite fields.
The last section contains a proof that the factor ring of the integers modulo a prime ideal is a finite field,
followed by an isomorphic construction of prime fields over an initial segment of the natural numbers.\<close>

end
