section \<open>The Original CVM Algorithm\label{sec:cvm_original}\<close>

text \<open>In this section, we verify the algorithm as presented by Chakrabory et
al.~\cite{chakraborty2022} (replicated, here, in Algorithm~\ref{alg:cvm_classic}),
with the following caveat:

In the original algorithm the elements are removed with probability $f := \frac{1}{2}$ in the
subsampling step. The version verified here allows for any $f \in [\frac{1}{2},e^{-1/12}]$.

\begin{algorithm}[h!]
	\caption{Original CVM algorithm.\label{alg:cvm_classic}}
	\begin{algorithmic}[1]
  \Require Stream elements $a_1,\ldots,a_l$, $0 < \varepsilon$, $0 < \delta < 1$, $f$ subsampling param.
  \Ensure An estimate $R$, s.t., $\prob \left( | R - |A| | > \varepsilon |A| \right) \leq \delta$ where $A := \{a_1,\ldots,a_l\}.$
  \State $\chi \gets \{\}, p \gets 1, n \geq \left\lceil \frac{12}{\varepsilon^2} \ln(\frac{6l}{\delta}) \right\rceil$
  \For{$i \gets 1$ to $l$}
    \State $b \getsr \Ber(p)$ \Comment insert $a_i$ with probability $p$ (and remove it otherwise)
    \If{$b$}
      \State $\chi \gets \chi \cup \{a_i\}$
    \Else
      \State $\chi \gets \chi - \{a_i\}$
    \EndIf
    \If{$|\chi| = n$}
      \State $\chi \getsr \mathrm{subsample}(\chi)$ \Comment keep each element of $\chi$ indep. with prob. $f$
      \State $p \gets p f$
    \EndIf
    \If{$|\chi| = n$}
      \State \Return $\bot$
    \EndIf
  \EndFor
  \State \Return $\frac{|\chi|}{p}$ \Comment estimate cardinality of $A$
\end{algorithmic}
\end{algorithm}

The first step of the proof is identical to the original proof~\cite{chakraborty2022}, where the
above algorithm is approximated by a second algorithm, where lines 11--12 are removed, i.e., the two
algorithms behave identically, unless the very improbable event---where the subsampling step fails
to remove any elements---occurs. It is possible to show that the total variational distance between
the two algorithms is at most $\frac{\delta}{2}$.

In the second step, we verify that the probability that the second algorithm returns an estimate
outside of the desired interval is also at most $\frac{\delta}{2}$. This, of course, works by
noticing that it is an instance of the abstract algorithm we introduced in
Section~\ref{sec:cvm_abs}. In combination, we conclude a failure probability of $\delta$ for the
unmodified version of the algorithm.

On the other hand, the fact that the number of elements in the buffer is at most $n$ can be seen
directly from Algorithm~\ref{alg:cvm_classic}.\<close>

theory CVM_Original_Algorithm
  imports CVM_Abstract_Algorithm
begin

context
  fixes f :: real
  fixes n :: nat
  assumes f_range: \<open>f \<in> {1/2..exp(-1/12)}\<close>
  assumes n_gt_0: \<open>n > 0\<close>
begin

text \<open>Line 1:\<close>
definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state = State {} 1\<close>

text \<open>Lines 3--7:\<close>
fun step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_1 a (State \<chi> p) =
    do {
      b \<leftarrow> bernoulli_pmf p;
      let \<chi> = (if b then \<chi> \<union> {a} else \<chi> - {a});

      return_spmf (State \<chi> p)
    }\<close>

definition subsample :: \<open>'a set \<Rightarrow> 'a set spmf\<close> where
  \<open>subsample \<chi> =
    do {
      keep_in_\<chi> \<leftarrow> prod_pmf \<chi> (\<lambda>_. bernoulli_pmf f);
      return_spmf (Set.filter keep_in_\<chi> \<chi>)
    }\<close>

text \<open>Lines 8--10:\<close>
fun step_2 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_2 (State \<chi> p) =
    do {
      if card \<chi> = n then do {
        \<chi> \<leftarrow> subsample \<chi>;
        return_spmf (State \<chi> (p * f))
      } else
        return_spmf (State \<chi> p)
    }\<close>

text \<open>Lines 11--12:\<close>
fun step_3 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_3 (State \<chi> p) =
    do {
      if card \<chi> = n
      then fail_spmf
      else return_spmf (State \<chi> p)
    }\<close>

text \<open>Lines 1--12:\<close>
definition run_steps :: \<open>'a list \<Rightarrow> 'a state spmf\<close> where
  \<open>run_steps xs \<equiv> foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2 \<bind> step_3) xs initial_state\<close>

text \<open>Line 13:\<close>
definition estimate :: \<open>'a state \<Rightarrow> real\<close> where
  \<open>estimate \<sigma> = card (state_\<chi> \<sigma>) / state_p \<sigma>\<close>

definition run_algo :: \<open>'a list \<Rightarrow> real spmf\<close> where
  \<open>run_algo xs = map_spmf estimate (run_steps xs)\<close>


schematic_goal step_1_m_def: \<open>step_1 x \<sigma> = ?x\<close>
  by (subst state.collapse[symmetric], subst step_1.simps, rule refl)

schematic_goal step_2_m_def: \<open>step_2 \<sigma> = ?x\<close>
  by (subst state.collapse[symmetric], subst step_2.simps, rule refl)

schematic_goal step_3_m_def: \<open>step_3 \<sigma> = ?x\<close>
  by (subst state.collapse[symmetric], subst step_3.simps, rule refl)

lemma ord_spmf_remove_step3:
  \<open>ord_spmf (=) (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) (step_1 x \<sigma> \<bind> step_2)\<close>
proof -
  have \<open>ord_spmf (=) (step_2 x \<bind> step_3) (step_2 x)\<close> for x :: \<open>'a state\<close>
  proof -
    have \<open>ord_spmf (=) (step_2 x \<bind> step_3) (step_2 x \<bind> return_spmf)\<close>
      by (intro bind_spmf_mono') (simp_all add:step_3_m_def)
    thus ?thesis by simp
  qed
  thus ?thesis unfolding bind_spmf_assoc by (intro bind_spmf_mono') simp_all
qed

lemma ord_spmf_run_steps:
  \<open>ord_spmf (=) (run_steps xs) (foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state)\<close>
  unfolding run_steps_def
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  show ?case
    unfolding run_steps_def foldM_spmf_snoc
    by (intro ord_spmf_remove_step3 bind_spmf_mono' snoc)
qed

lemma f_range_simple: \<open>f \<in> {1/2..<1}\<close>
proof -
  have \<open>exp (- 1 / 12) < (1::real)\<close> by (approximation 5)
  from dual_order.strict_trans2[OF this]
  show ?thesis using f_range by auto
qed

text \<open>Main result:\<close>

theorem correctness:
  fixes xs :: \<open>'a list\<close>
  assumes \<open>\<epsilon> \<in> {0<..<1}\<close> \<open>\<delta> \<in> {0<..<1}\<close>
  assumes \<open>real n \<ge> 12 / \<epsilon>\<^sup>2 * ln (6 * real (length xs) / \<delta>)\<close>
  defines \<open>A \<equiv> real (card (set xs))\<close>
  shows \<open>\<P>(\<omega> in run_algo xs. fails_or_satisfies (\<lambda>R. \<bar>R - A\<bar> > \<epsilon> * A) \<omega>) \<le> \<delta>\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  define abs_subsample where
    \<open>abs_subsample \<chi> = map_pmf (\<lambda>\<omega>. Set.filter \<omega> \<chi>) (prod_pmf \<chi> (\<lambda>_. bernoulli_pmf f))\<close>
    for \<chi> :: \<open>'a set\<close>

  interpret abs:cvm_algo_abstract n f abs_subsample
    rewrites \<open>abs.estimate = estimate\<close>
  proof -
    show abs:\<open>cvm_algo_abstract n f abs_subsample\<close>
    proof (unfold_locales, goal_cases)
      case 1 thus ?case by (rule n_gt_0)
    next
      case 2 thus ?case using f_range_simple by auto
    next
      case (3 U x)
      then show ?case unfolding abs_subsample_def by auto
    next
      case (4 g \<chi> S)
      hence fin_U: \<open>finite \<chi>\<close> using n_gt_0 card_gt_0_iff by metis
      note conv = Pi_pmf_subset[OF this 4(1)]

      have \<open>(\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> \<omega>)) \<partial>abs_subsample \<chi>) =
        (\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> \<chi> \<and> \<omega> s)) \<partial>prod_pmf \<chi> (\<lambda>_. bernoulli_pmf f))\<close>
        unfolding abs_subsample_def by (simp cong:prod.cong)
      also have \<open>\<dots> = (\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> \<chi> \<and> \<omega> s)) \<partial>prod_pmf S (\<lambda>_. bernoulli_pmf f))\<close>
        unfolding conv by simp
      also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g (s \<in> \<chi> \<and> \<omega>) \<partial>bernoulli_pmf f))\<close>
        using fin_U finite_subset[OF 4(1)]
        by (intro expectation_prod_Pi_pmf integrable_measure_pmf_finite) auto
      also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close>
        using 4(1) by (intro prod.cong refl) auto
      finally show ?case by simp
    qed
    show \<open>cvm_algo_abstract.estimate = (estimate :: 'a state \<Rightarrow> real)\<close>
      unfolding cvm_algo_abstract.estimate_def[OF abs] estimate_def by simp
  qed

  have a: \<open>step_1 \<sigma> x = spmf_of_pmf (abs.step_1 \<sigma> x)\<close> for \<sigma> x
    unfolding step_1_m_def abs.step_1_def Let_def spmf_of_pmf_def by (simp add:map_bind_pmf)

  have b: \<open>step_2 \<sigma> = map_pmf Some (abs.step_2 \<sigma>)\<close> for \<sigma>
    unfolding step_2_m_def abs.step_2_def subsample_def abs_subsample_def Let_def
    by (simp add:map_bind_pmf bind_pmf_return_spmf)

  have c: \<open>abs.initial_state = initial_state\<close>
    unfolding initial_state_def abs.initial_state_def by simp

  have d: \<open>subsample \<chi> = spmf_of_pmf (abs_subsample \<chi>)\<close> for \<chi>
    unfolding subsample_def abs_subsample_def map_pmf_def[symmetric]
    by (simp add:spmf_of_pmf_def map_pmf_comp)

  define \<alpha> :: real where \<open>\<alpha> = f ^ n\<close>

  have \<alpha>_range: \<open>\<alpha> \<in> {0..1}\<close>
    using f_range_simple unfolding \<alpha>_def by (auto intro:power_le_one)
  hence [simp]: \<open>\<bar>\<alpha>\<bar> \<le> 1\<close> by auto

  have \<open>(\<integral>x. (if card x = n then 1 else 0) \<partial>abs_subsample \<chi>) \<le> \<alpha>\<close> (is \<open>?L1 \<le> _\<close>)
    if that': \<open>card \<chi> = n\<close> for \<chi>
  proof -
    have fin_U: \<open>finite \<chi>\<close> using n_gt_0 that card_gt_0_iff by metis

    have \<open>(\<Prod>s\<in>\<chi>. of_bool (s \<in> x)::real) = of_bool(card x = n)\<close>
      if \<open>x \<in> set_pmf (abs_subsample \<chi>)\<close> for x
    proof -
      have x_ran: \<open>x \<subseteq> \<chi>\<close> using that unfolding abs_subsample_def by auto

      have \<open>(\<Prod>s\<in>\<chi>. of_bool (s \<in> x)::real) = of_bool(x = \<chi>)\<close>
        using fin_U x_ran by (induction \<chi> rule:finite_induct) auto
      also have \<open>\<dots> = of_bool (card x = card \<chi>)\<close>
        using x_ran fin_U card_subset_eq by (intro arg_cong[where f=\<open>of_bool\<close>]) blast
      also have \<open>\<dots> = of_bool (card x = n)\<close> using that' by simp
      finally show ?thesis by auto
    qed
    hence \<open>?L1 = (\<integral>x. (\<Prod>s \<in> \<chi>. of_bool(s \<in> x)) \<partial>abs_subsample \<chi>)\<close>
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have \<open>\<dots> \<le> (\<Prod>s \<in> \<chi>. (\<integral>x. of_bool x \<partial>bernoulli_pmf f))\<close>
      by (intro abs.subsample_inequality that) auto
    also have \<open>\<dots> = f ^ card \<chi>\<close> using f_range_simple by simp
    also have \<open>\<dots> = \<alpha>\<close> unfolding \<alpha>_def that by simp
    finally show ?thesis by simp
  qed
  hence e: \<open>pmf (step_2 \<sigma> \<bind> step_3) None \<le> \<alpha>\<close> for \<sigma> :: \<open>'a state\<close>
    using \<alpha>_range unfolding step_2_m_def step_3_m_def d Let_def
    by (simp add:pmf_bind bind_pmf_return_spmf if_distrib if_distribR cong:if_cong)

  have \<open>pmf (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) None \<le> \<alpha>\<close> for \<sigma> and x :: 'a
  proof-
    have \<open>pmf (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) None \<le> 0 + (\<integral>_. \<alpha> \<partial> measure_spmf (step_1 x \<sigma>))\<close>
      unfolding bind_spmf_assoc pmf_bind_spmf_None[where p=\<open>step_1 x \<sigma>\<close>]
      by (intro add_mono integral_mono_AE measure_spmf.integrable_const_bound[where B=\<open>1\<close>]
          iffD2[OF AE_measure_spmf_iff] ballI e)
         (simp_all add:pmf_le_1 step_1_m_def map_pmf_def[symmetric] pmf_map vimage_def Let_def)
    also have \<open>\<dots> \<le> \<alpha>\<close> using \<alpha>_range by (simp add: mult_left_le_one_le weight_spmf_le_1)
    finally show ?thesis by simp
  qed
  hence \<open>prob_fail (run_steps xs) \<le> length xs * \<alpha>\<close>
    unfolding run_steps_def by (intro prob_fail_foldM_spmf_le[where P=\<open>\<lambda>_. True\<close>]) auto
  also have \<open>\<dots> \<le> \<delta> / 2\<close>
  proof (cases \<open>xs = []\<close>)
    case True
    thus ?thesis using assms(2) by auto
  next
    case False
    have \<open>\<delta> \<le> 6 * 1\<close> using assms(2) by simp
    also have \<open>\<dots> \<le> 6 * real (length xs)\<close>
      using False by (intro mult_mono order.refl) (cases xs, auto)
    finally have [simp]: \<open> \<delta> \<le> 6 * real (length xs)\<close> by simp
    have \<open>2 * real (length xs) * f ^ n \<le> 2 * real (length xs) * exp (-1/12)^n\<close>
      using f_range by (intro mult_left_mono power_mono) auto
    also have \<open>\<dots> =  2 * real (length xs) * exp (-real n / 12)\<close>
      unfolding exp_of_nat_mult[symmetric] by simp
    also have \<open>\<dots> \<le> 2 * real (length xs) * exp (-(12 / \<epsilon> ^ 2 * ln (6 * real (length xs) / \<delta>))/12)\<close>
      using assms(3) by (intro mult_left_mono iffD2[OF exp_le_cancel_iff] divide_right_mono) auto
    also have \<open>\<dots> = 2 * real (length xs) * exp (-ln (6 * real (length xs) / \<delta>) / \<epsilon>^2 )\<close>
      by auto
    also have \<open>\<dots> \<le> 2 * real (length xs) * exp (-ln (6 * real (length xs) / \<delta>) / 1 )\<close>
      using assms(1,2) False
      by (intro mult_left_mono iffD2[OF exp_le_cancel_iff] divide_left_mono_neg power_le_one)
        (auto intro!:ln_ge_zero simp:divide_simps)
    also have \<open>\<dots> = 2 * real (length xs) * exp (ln (inverse (6 * real (length xs) / \<delta>)))\<close>
      using False assms(2) by (subst ln_inverse[symmetric]) auto
    also have \<open>\<dots> = 2 * real (length xs) / (6 * real (length xs) / \<delta>)\<close>
      using assms(1,2) False by (subst exp_ln) auto
    also have \<open>\<dots> = \<delta> / 3\<close> using False assms(2) by auto
    also have \<open>\<dots> \<le> \<delta>\<close> using assms(2) by auto
    finally have \<open>2 * real (length xs) * f^n \<le> \<delta>\<close> by simp
    thus ?thesis unfolding \<alpha>_def by simp
  qed
  finally have f:\<open>prob_fail (run_steps xs) \<le> \<delta> / 2\<close> by simp

  have g:\<open>spmf_of_pmf (abs.run_steps xs) = foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state\<close>
    unfolding abs.run_steps_def foldM_spmf_of_pmf_eq(2)[symmetric]
    unfolding spmf_of_pmf_def map_pmf_def c b a
    by (simp add:bind_assoc_pmf bind_spmf_def bind_return_pmf)

  have \<open>?L \<le> measure (run_steps xs) {None} +
    measure (measure_spmf (run_steps xs)) {x. \<bar>estimate x - A\<bar> > \<epsilon> * A}\<close>
    unfolding run_algo_def measure_measure_spmf_conv_measure_pmf measure_map_pmf
    by (intro pmf_add) (auto split:option.split_asm)
  also have \<open>\<dots> \<le> \<delta> / 2 + measure (measure_spmf (run_steps xs)) {x. \<bar>estimate x - A\<bar> > \<epsilon> * A}\<close>
    unfolding measure_pmf_single by (intro add_mono f order.refl)
  also have \<open>\<dots> \<le> \<delta>/2+measure(measure_spmf (spmf_of_pmf (abs.run_steps xs))) {x. \<bar>estimate x-A\<bar>>\<epsilon>*A}\<close>
    using ord_spmf_eqD_emeasure[OF ord_spmf_run_steps] unfolding measure_spmf.emeasure_eq_measure g
    by (intro add_mono) auto
  also have \<open>\<dots> \<le> \<delta> / 2 + measure (abs.run_steps xs) {x. \<bar>estimate x - A\<bar> > \<epsilon> * A}\<close>
    using measure_spmf_map_pmf_Some spmf_of_pmf_def by auto
  also have \<open>\<dots> \<le> \<delta> / 2 + \<delta> / 2\<close>
    using assms(1-3) unfolding A_def by (intro add_mono abs.correctness) auto
  finally show ?thesis by simp
qed

lemma space_usage:
  \<open>AE \<sigma> in measure_spmf (run_steps xs). card (state_\<chi> \<sigma>) < n \<and> finite (state_\<chi> \<sigma>)\<close>
proof (induction xs rule:rev_induct)
  case Nil thus ?case using n_gt_0 by (simp add:run_steps_def initial_state_def)
next
  case (snoc x xs)
  define p1 where \<open>p1 = run_steps xs \<bind> step_1 x\<close>
  define p2 where \<open>p2 = p1 \<bind> step_2\<close>
  define p3 where \<open>p3 = p2 \<bind> step_3\<close>

  have a:\<open>run_steps (xs@[x]) = p3\<close>
    unfolding run_steps_def p1_def p2_def p3_def foldM_spmf_snoc by (simp add:bind_assoc_pmf)

  have \<open>card (state_\<chi> \<sigma>) \<le> n \<and> finite (state_\<chi> \<sigma>)\<close> if \<open>\<sigma> \<in> set_spmf p1\<close> for \<sigma>
    using snoc that less_imp_le unfolding p1_def
    by (auto simp: step_1_m_def set_bind_spmf set_spmf_bind_pmf Let_def card_insert_if)+

  hence \<open>card (state_\<chi> \<sigma>) \<le> n \<and> finite (state_\<chi> \<sigma>)\<close> if \<open>\<sigma> \<in> set_spmf p2\<close> for \<sigma>
    using that card_filter_mono unfolding p2_def
    by (auto intro!:card_filter_mono simp:step_2_m_def set_bind_spmf set_spmf_bind_pmf
        subsample_def Let_def if_distrib)

  hence \<open>card (state_\<chi> \<sigma>) < n \<and> finite (state_\<chi> \<sigma>)\<close> if \<open>\<sigma> \<in> set_spmf p3\<close> for \<sigma>
    using that unfolding p3_def
    by (auto intro:le_neq_implies_less simp:step_3_m_def set_bind_spmf if_distrib)

  thus ?case unfolding a by simp
qed

end (* context *)

end (* theory *)