section \<open>Set Reconciliation Algorithm\<close>

theory Set_Reconciliation
  imports
    "HOL-Library.FuncSet"
    "HOL-Computational_Algebra.Polynomial"
    "Factorisation"
    "Rational_Function_Interpolation"
begin

hide_const (open) up_ring.monom

text \<open>The following locale introduces the context for the reconciliation algorithm. It fixes 
parameters that are assumed to be known in advance, in particular:
\begin{itemize}
\item a bound @{term "m"} on the symmetric difference: represented using the type variable @{typ "'m"} 
\item the finite field used to represent the elements of the sets: represented using the type variable @{typ "'a"}
\item the evaluation points used (which must be choosen outside of the domain used to represent the
elements of the sets): represented using the variable @{term "E"}
\end{itemize}

To preserve generality as much as possible, we only present an interaction protocol that
allows one party Alice to send a message to the second party Bob, who can reconstruct the set Alice
has, assuming Bob holds a set himself, whose symmetric difference does not exceed @{term "m"}.

Note that using this primitive, it is possible for Bob to compute the union of the sets, and of 
course the algorithm can also be used to send a message from Bob to Alice, such that Alice can do 
so as well. However, the primitive we describe can be used in many other scenarios.\<close>


locale set_reconciliation_algorithm =
  fixes E :: "'a :: prime_card mod_ring list"
  fixes phantom_m :: "'m::mod_type itself"
  assumes type_m: "phantom_m = TYPE('m)"
  assumes distinct_E: "distinct E"
  assumes card_m: "CARD('m) = length E"
begin

text \<open>The algorithm---or, more precisely the protocol---is represented using a pair of algorithms.
The first is the encoding function which Alice used to create the message she sends. The second is
the decoding algorithm, which Bob can use to reconstruct the set Alice has.\<close>

definition encode where
  "encode A = (card A, \<lambda> x \<in> set E. poly (set_to_poly A) x)"

definition decode where
  "decode B R =
    (let
      (n, f\<^sub>A) = R;
      f\<^sub>B = (\<lambda> x \<in> set E. poly (set_to_poly B) x);
      d\<^sub>A = nat \<lfloor>(real (length E) + n - card B) / 2\<rfloor>;
      d\<^sub>B = nat \<lfloor>(real (length E) + card B - n) / 2\<rfloor>;
      (p\<^sub>A,p\<^sub>B) = interpolate_rat_fun E (\<lambda>x. f\<^sub>A x / f\<^sub>B x) d\<^sub>A d\<^sub>B phantom_m;
      r\<^sub>A = proots_eff p\<^sub>A;
      r\<^sub>B = proots_eff p\<^sub>B
    in
      set_mset (r\<^sub>A - r\<^sub>B) \<union> (B - (set_mset (r\<^sub>B - r\<^sub>A))))"

subsection \<open>Informal Description of the Algorithm\<close>

text \<open>The protocol works as follows:

We association with each set $A$ a polynomial $\chi_A(x) := \prod_{s \in A} (x-s)$ in the finite
field $F$. As mentioned before we reserve a set of $m$ evaluation points $E$, which can be arbitrary 
prearranged points, as long as they are field elements not used to represent set elements.

Then Alice sends the size of its set |A| and the evaluation of its characteristic polynomial on $E$.

Bob computes
\begin{eqnarray*} 
  d_A & := & \left\lfloor \frac{|E| + |A| - |B|}{2} \right\rfloor \\
  d_B & := & \left\lfloor \frac{|E| + |B| - |A|}{2} \right\rfloor
\end{eqnarray*}

Then Bob finds monic polynomials $p_A$, $p_B$ of degree $d_A$ and $d_B$ fulfilling the condition:
\begin{equation}\label{eq:bob_system}
  p_A(x) \chi_B(x) = p_B(x) \chi_A(X) \textrm{ for all } x \in E
\end{equation}
The above results in a system of linear equations, which can be solved using Gaussian elimination.
It is easy to show that the system is solvable since:
\begin{eqnarray*}
  p_A & := & \chi_{A-B}(x) x^r \\
  p_B & := & \chi_{B-A}(x) x^r
\end{eqnarray*}
is a solution, where $r := d_A - |A-B| = d_B - |B-A|$.

The equation (Eq.~\ref{eq:bob_system}) implies also:
\begin{equation}\label{eq:bob_system_2}
  p_A(x) \chi_{B-A}(x) = p_B(x) \chi_{A-B}(x) \textrm{ for all } x \in E
\end{equation}
since $\chi_A(x) = \chi_{A-B}(x) \chi_{A \cap B}(x)$,
$\chi_B(x) = \chi_{B-A}(x) \chi_{A \cap B}(x)$, and $\chi_{A \cap B}(x) \neq 0$, because of our
constraint that $E$ is outside of the universe of the set elements.
Btw.\ in general
\[
\chi_{U \cup V} = \chi_U \chi_V \textrm{ for any disjoint } U,V \textrm{.}
\]

Because the polynomials on both sides of Eq.~\ref{eq:bob_system_2} are \emph{monic} polynomials of
the same degree $m'$, where $m' \leq m$, and agree on $m$ points, they must be equal.

This implies in particular, that for the order of any root x (denoted by $\mathrm{ord}_x$), we have:
\[
  \mathrm{ord}_x (p_A \chi_{B-A}) =  \mathrm{ord}_x (p_B \chi_{A-B})
\]
which implies:
\[
  \mathrm{ord}_x (p_A) - \mathrm{ord}_x (p_B) =
  \mathrm{ord}_x(\chi_{B-A}) - \mathrm{ord}_x (\chi_{A-B}) \textrm{.}
\]
Note that by definition the right hand side is equal to $+1$ if $x \in B-A$, $-1$ if $x \in A-B$ and
$0$ otherwise. Thus Bob can compute $A$ using 
\[
  A := \{x | \mathrm{ord}_x (p_A) - \mathrm{ord}_x (p_B) > 0\}
  \cup (B - \{x | \mathrm{ord}_x (p_A) - \mathrm{ord}_x (p_B) < 0\}) \textrm{.}
\]
\<close>

subsection "Lemmas"

text "This is no longer used, but it will be needed if you implement decode
using an interpolation algorithm that does not return monic polynomials."
lemma interpolated_rational_function_eq:
  assumes
    "\<forall> x \<in> set E. poly (set_to_poly A) x * poly p\<^sub>B x = poly (set_to_poly B) x * poly p\<^sub>A x"
    "degree p\<^sub>A \<le> (real (length E) + card A - card B)/2"
    "degree p\<^sub>B \<le> (real (length E) + card B - card A)/2"
    "card (sym_diff A B) < length E"
    "set E \<inter> A = {}" "set E \<inter> B = {}"
  shows "set_to_poly (A-B) * p\<^sub>B = set_to_poly (B-A) * p\<^sub>A"
proof -
  have fin: "finite A" "finite B"
    by simp+

  have dA: "degree p\<^sub>A \<le> (real (length E) + card (A-B) - card (B-A))/2"
    using assms(2) card_sub_int_diff_finite[OF fin] by simp
  have dB: "degree p\<^sub>B \<le> (real (length E) + card (B-A) - card (A-B))/2"
    using assms card_sub_int_diff_finite[OF fin] by simp

  have "set_to_poly A = set_to_poly (A-B) * set_to_poly (A \<inter> B)"
    using set_to_poly_mult_distinct
    by (metis Int_Diff_Un Int_Diff_disjoint mult.commute)
  moreover have "set_to_poly B = set_to_poly (B-A) * set_to_poly (A \<inter> B)"
    using set_to_poly_mult_distinct
    by (metis Int_Diff_Un Int_Diff_disjoint Int_commute mult.commute)
  ultimately have inE: "poly (set_to_poly (A-B) * p\<^sub>B) x = poly (set_to_poly (B-A) * p\<^sub>A) x"
      if "x \<in> set E" for x
    using that assms by (auto simp: in_set_to_poly)

  have "real (degree (set_to_poly (A-B) * p\<^sub>B)) \<le> real (card (A-B)) + degree p\<^sub>B"
    by (metis of_nat_add of_nat_le_iff degree_mult_le set_to_poly_degree)
  also have "\<dots> \<le> (real (length E) + (real(card (B-A)) + card (A-B)))/2"
    using dB by simp
  also have "\<dots> < (length E + length E) / 2"
    using assms(4) card_sym_diff_finite[OF fin] by simp
  also have "\<dots> = length E" by simp
  finally have l: "degree (set_to_poly (A-B) * p\<^sub>B) < length E"
    by simp

  have "real (degree (set_to_poly (B-A) * p\<^sub>A)) \<le> real (card (B-A)) + degree p\<^sub>A"
    by (metis of_nat_add of_nat_le_iff degree_mult_le set_to_poly_degree)
  also have "\<dots> \<le> (length E + (card (B-A) + card (A-B)))/2"
    using dA by simp
  also have "\<dots> < (length E + length E) / 2"
    using assms(4) card_sym_diff_finite[OF fin] by simp
  also have "\<dots> = length E" by simp
  finally have r: "degree (set_to_poly (B-A) * p\<^sub>A) < length E"
    by simp

  have "set_to_poly (A-B) * p\<^sub>B = set_to_poly (B-A) * p\<^sub>A"
    using l r inE poly_eqI_degree distinct_card[OF distinct_E]
    by (intro poly_eqI_degree[where A="set E"]) auto
  then show ?thesis .
qed

text "This is a specialized version of interpolated-rational-function-eq.
Here the interpolated function are monic with exact degrees."
lemma monic_interpolated_rational_function_eq:
  assumes
    "\<forall> x \<in> set E. poly (set_to_poly A) x * poly p\<^sub>B x = poly (set_to_poly B) x * poly p\<^sub>A x"
    "degree p\<^sub>A = \<lfloor>(real (length E) + card A - card B)/2\<rfloor>"
    "degree p\<^sub>B = \<lfloor>(real (length E) + card B - card A)/2\<rfloor>"
    "card (sym_diff A B) \<le> length E"
    "set E \<inter> A = {}" "set E \<inter> B = {}"
    "monic p\<^sub>A" "monic p\<^sub>B"
  shows "set_to_poly (A-B) * p\<^sub>B = set_to_poly (B-A) * p\<^sub>A" (is "?lhs = ?rhs")
proof -
  have fin: "finite A" "finite B"
    by simp+
  have p0: "p\<^sub>A \<noteq> 0" "p\<^sub>B \<noteq> 0"
    using assms(7, 8) by auto

  define m' where "m' = \<lfloor>(real (length E) + card (B-A) + card (A-B))/2\<rfloor>"

  note s1 = card_sub_int_diff_finite_real[OF fin]
  note s2 = card_sub_int_diff_finite_real[OF fin(2,1)]

  have "int (degree ?lhs) = int (card (A-B)) + degree p\<^sub>B" 
    using set_to_poly_degree  p0 set_to_poly_not0 by (subst degree_mult_eq) auto
  also have "\<dots> = \<lfloor>card (A-B) + (real (length E) + card (B-A) - card (A-B))/2\<rfloor>"
    using assms(3) s2 by (simp add: group_cancel.sub1)
  also have "\<dots> = m'" unfolding m'_def by argo
  finally have a:"int (degree ?lhs) = m'" by simp

  have "int (degree ?rhs) = int (card (B-A)) + degree p\<^sub>A" 
    using set_to_poly_degree  p0 set_to_poly_not0 by (subst degree_mult_eq) auto
  also have "\<dots> = \<lfloor>card (B-A) + (real (length E) + card (A-B) - card (B-A))/2\<rfloor>"
    using assms(2) s1 by (simp add: group_cancel.sub1)
  also have "\<dots> = m'" unfolding m'_def by argo
  finally have b:"int (degree ?rhs) = m'" by simp

  have "of_int m' \<le> (real (length E) + card (B-A) + card (A-B))/2"
    unfolding m'_def by linarith
  also have "\<dots> \<le> (real (length E) + real (length E))/2"
    using assms(4) card_sym_diff_finite[OF fin] by simp
  also have "\<dots> \<le> real (length E)" by simp
  also have "\<dots> = real (card (set E))" using distinct_E by (simp add: distinct_card)
  finally have c: "m' \<le> card (set E)" by simp

  have t1: "set_to_poly A = set_to_poly (A-B) * set_to_poly (A \<inter> B)"
    by (subst set_to_poly_mult_distinct) (auto intro!:arg_cong[where f="set_to_poly"])

  have t2: "set_to_poly B = set_to_poly (B-A) * set_to_poly (A \<inter> B)"
    by (subst set_to_poly_mult_distinct) (auto intro!:arg_cong[where f="set_to_poly"])

  have d: "poly (set_to_poly (A-B) * p\<^sub>B) x = poly (set_to_poly (B-A) * p\<^sub>A) x" if "x \<in> set E" for x
  proof -
    have "poly (set_to_poly (A \<inter> B)) x \<noteq> 0"
      using in_set_to_poly assms(5,6) that by (metis IntE disjoint_iff)
    thus ?thesis using that assms(1) unfolding t1 t2 by auto
  qed

  show ?thesis
    apply (intro poly_eqI_degree_monic[where A= "set E"])
    subgoal using a b by simp
    subgoal using a c by simp
    subgoal using set_to_poly_lead_coeff monic_mult assms(8) by auto
    subgoal using set_to_poly_lead_coeff monic_mult assms(7) by auto
    using d by auto
qed

subsection "Main Result"

text \<open>This is the main result of the entry. We show that the decoding algorithm, Bob uses, can 
reconstruct the set Alice has, if she has encoded with the encoding algorithm.
Assuming the symmetric difference between the sets does not exceed the given bound.\<close>

theorem decode_encode_correct:
  assumes
    "card (sym_diff A B) \<le> length E"
    "set E \<inter> A = {}" "set E \<inter> B = {}"
  shows "decode B (encode A) = A"
proof -
  let ?f\<^sub>A = "(\<lambda> x \<in> set E. poly (set_to_poly A) x)"
  let ?f\<^sub>B = "(\<lambda> x \<in> set E. poly (set_to_poly B) x)"
  let ?d\<^sub>A = "(real (length E) + card A - card B) / 2"
  let ?d\<^sub>B = "(real (length E) + card B - card A) / 2"

  define p where def_pq: "p = interpolate_rat_fun E (\<lambda>x. ?f\<^sub>A x / ?f\<^sub>B x) (nat \<lfloor>?d\<^sub>A\<rfloor>) (nat \<lfloor>?d\<^sub>B\<rfloor>) TYPE('m)"
  define p\<^sub>A p\<^sub>B where def_p_q: "p\<^sub>A = fst p" "p\<^sub>B = snd p"

  have "monic_interpolated_rational_function (fst p) (snd p) (set E) ?f\<^sub>A ?f\<^sub>B ?d\<^sub>A ?d\<^sub>B"
    unfolding def_pq
    using assms card_m by (intro rational_function_interpolation_correct_real) auto
  then have "monic_interpolated_rational_function p\<^sub>A p\<^sub>B (set E) ?f\<^sub>A ?f\<^sub>B ?d\<^sub>A ?d\<^sub>B"
    using def_p_q by simp

  then have irf: "\<forall> e \<in> set E. ?f\<^sub>A e * poly p\<^sub>B e = ?f\<^sub>B e * poly p\<^sub>A e"
      "degree p\<^sub>A = floor ?d\<^sub>A" "degree p\<^sub>B = floor ?d\<^sub>B"
      "monic p\<^sub>A" "monic p\<^sub>B"
    unfolding monic_interpolated_rational_function_def by auto

  have n0: "p\<^sub>A \<noteq> 0" "p\<^sub>B \<noteq> 0"
    using monic0 irf by auto

  have "\<forall>x\<in> set E. poly (set_to_poly A) x * poly p\<^sub>B x = poly (set_to_poly B) x * poly p\<^sub>A x"
    using irf(1) by simp
  then have ieq: "set_to_poly (A-B) * p\<^sub>B = set_to_poly (B-A) * p\<^sub>A"
    using assms irf by (intro monic_interpolated_rational_function_eq) auto

  have "order x (set_to_poly (A-B) * p\<^sub>B) = order x (set_to_poly (A-B)) + order x p\<^sub>B" for x
    using irf(5) n0 by (simp add: order_mult)
  moreover have "order x (set_to_poly (B-A) * p\<^sub>A) = order x (set_to_poly (B-A)) + order x p\<^sub>A" for x
    using irf(4) n0 by (simp add: order_mult)
  ultimately have "order x (set_to_poly (A-B)) + order x p\<^sub>B =
                   order x (set_to_poly (B-A)) + order x p\<^sub>A" for x
    using ieq by simp
  hence "int (order x (set_to_poly (A-B))) + int (order x p\<^sub>B) =
         int (order x (set_to_poly (B-A))) + int (order x p\<^sub>A)" for x
    using of_nat_add by metis
  then have oif: "int (order x (set_to_poly (A-B))) - int (order x (set_to_poly (B-A))) =
                  int (order x p\<^sub>A) - int (order x p\<^sub>B)" for x
    by (simp add:field_simps)

  have "int (order x p\<^sub>A) - int (order x p\<^sub>B) \<ge> 1 \<longleftrightarrow> x \<in> (A-B)" for x
    unfolding oif[symmetric] set_to_poly_order by simp
  hence a_minus_b: "{x. order x p\<^sub>A > order x p\<^sub>B} = A-B" by force

  have "int (order x p\<^sub>A) - int (order x p\<^sub>B) \<le> -1 \<longleftrightarrow> x \<in> (B-A)" for x
    unfolding oif[symmetric] set_to_poly_order by simp
  hence b_minus_a: "{x. order x p\<^sub>B > order x p\<^sub>A} = B-A" by force

  have "{x. order x p\<^sub>A > order x p\<^sub>B} \<union> (B - {x. order x p\<^sub>A < order x p\<^sub>B}) = A"
    unfolding a_minus_b b_minus_a by auto

  moreover have "decode B (encode A) =
      set_mset (proots_eff p\<^sub>A - proots_eff p\<^sub>B) \<union> (B - (set_mset (proots_eff p\<^sub>B - proots_eff p\<^sub>A)))"
    unfolding decode_def encode_def Let_def def_p_q def_pq
    using type_m by (simp add:case_prod_beta del:proots_eff.simps)
  moreover have "\<dots> = {x. order x  p\<^sub>A > order x p\<^sub>B}  \<union> (B - {x. order x  p\<^sub>B > order x p\<^sub>A})"
    unfolding proots_eff_correct [symmetric]
    using irf(4,5) n0 by (auto simp: set_mset_diff)

  ultimately show ?thesis by argo
qed

end

end
