section \<open>Abstract Algorithm\label{sec:cvm_abs}\<close>

text \<open>This section verifies an abstract version of the CVM algorithm, where the subsampling step
can be an arbitrary randomized algorithm fulfilling an expectation invariant.

The abstract algorithm is presented in Algorithm~\ref{alg:cvm_abs}.

\begin{algorithm}[h!]
	\caption{Abstract CVM algorithm.\label{alg:cvm_abs}}
	\begin{algorithmic}[1]
  \Require Stream elements $a_1,\ldots,a_l$, $0 < \varepsilon$, $0 < \delta < 1$, $\frac{1/2} \leq f < 1$
  \Ensure An estimate $R$, s.t., $\prob \left( | R - |A| | > \varepsilon |A| \right) \leq \delta$ where $A := \{a_1,\ldots,a_l\}.$
  \State $\chi \gets \{\}, p \gets 1, n \geq \left\lceil \frac{12}{\varepsilon^2} \ln(\frac{3l}{\delta}) \right\rceil$
  \For{$i \gets 1$ to $l$}
    \State $b \getsr \Ber(p)$ \Comment insert $a_i$ with probability $p$ (and remove it otherwise)
    \If{$b$}
      \State $\chi \gets \chi \cup \{a_i\}$
    \Else
      \State $\chi \gets \chi - \{a_i\}$
    \EndIf
    \If{$|\chi| = n$}
      \State $\chi \getsr \mathrm{subsample}(\chi)$ \Comment abstract subsampling step
      \State $p \gets p f$
    \EndIf
  \EndFor
  \State \Return $\frac{|\chi|}{p}$ \Comment estimate cardinality of $A$
\end{algorithmic}
\end{algorithm}

For the subsampling step we assume that it fulfills the following inequality:

\begin{equation}
\label{eq:subsample_condition}
\int_{\mathrm{subsample}(\chi)} \left(\prod_{i \in S} g(i \in \omega) \right)\, d \omega \leq
  \prod_{i \in S} \left(\int_{Ber(f)} g(\omega)\, d\omega\right)
\end{equation}
for all non-negative functions $g$ and $S \subseteq \chi$,
where $\mathrm{Ber}(p)$ denotes the Bernoulli-distribution.

The original CVM algorithm uses a subsampling step where each element of $\chi$ is retained
independently with probability $f$. It is straightforward to see that this fulfills the above
condition (with equality).

The new CVM algorithm variant proposed in this work uses a subsampling step where a random
$nf$-sized subset of $\chi$ is kept. This also fulfills the above inequality, although this is
harder to prove and will be explained in more detail in Section~\ref{sec:cvm_new}.

In this section, we will verify that the above abstract algorithm indeed fulfills the desired
conditions on its estimate, as well as unbiasedness, i.e., that: $\expect [R] = |A|$.
The part that is not going to be verified in this section, is the fact that the algorithm keeps at
most $n$ elements in the state $\chi$, because it is not unconditionally true, but will be ensured
(by different means) for the concrete instantiations in the following sections.

An informal version of this proof is presented in Appendix~\ref{apx:informal_proof}.
For important lemmas and theorems, we include a reference to the corresponding statement in the
appendix.\<close>

theory CVM_Abstract_Algorithm

imports
  "HOL-Decision_Procs.Approximation"
  CVM_Preliminary
  Finite_Fields.Finite_Fields_More_PMF
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
begin

unbundle no_vec_syntax

datatype 'a state = State (state_\<chi>: \<open>'a set\<close>) (state_p: real)

datatype 'a run_state = FinalState \<open>'a list\<close> | IntermState \<open>'a list\<close> \<open>'a\<close>

lemma run_state_induct:
  assumes \<open>P (FinalState [])\<close>
  assumes \<open>\<And>xs x. P (FinalState xs) \<Longrightarrow> P (IntermState xs x)\<close>
  assumes \<open>\<And>xs x. P (IntermState xs x) \<Longrightarrow> P (FinalState (xs@[x]))\<close>
  shows \<open>P result\<close>
proof -
  have \<open>P (FinalState xs) \<and> P (IntermState xs x)\<close> for xs x
    using assms by (induction xs rule:rev_induct) auto
  thus ?thesis by (cases result) auto
qed

locale cvm_algo_abstract =
  fixes n :: nat and f :: real and subsample :: \<open>'a set \<Rightarrow> 'a set pmf\<close>
  assumes n_gt_0: \<open>n > 0\<close>
  assumes f_range: \<open>f \<in> {1/2..<1}\<close>
  assumes subsample:
    \<open>\<And>U x. card U = n \<Longrightarrow> x \<in> set_pmf (subsample U) \<Longrightarrow> x \<subseteq> U\<close>
  assumes subsample_inequality:
    \<open>\<And>g U S. S \<subseteq> U
      \<Longrightarrow> card U = n
      \<Longrightarrow> range g \<subseteq> {0::real..}
      \<Longrightarrow> (\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close>
begin

text \<open>Line 1 of Algorithm~\ref{alg:cvm_abs}:\<close>
definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> State {} 1\<close>

text \<open>Lines 3--7:\<close>
fun step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1 a (State \<chi> p) =
    do {
      b \<leftarrow> bernoulli_pmf p;
      let \<chi> = (if b then \<chi> \<union> {a} else \<chi> - {a});

      return_pmf (State \<chi> p)
    }\<close>

text \<open>Lines 8--10:\<close>
fun step_2 :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2 (State \<chi> p) = do {
    if card \<chi> = n
    then do {
      \<chi> \<leftarrow> subsample \<chi>;
      return_pmf (State \<chi> (p*f))
    } else do {
      return_pmf (State \<chi> p)
    }
  }\<close>

schematic_goal step_1_def: \<open>step_1 x \<sigma> = ?x\<close>
  by (subst state.collapse[symmetric], subst step_1.simps, rule refl)

schematic_goal step_2_def: \<open>step_2 \<sigma> = ?x\<close>
  by (subst state.collapse[symmetric], subst step_2.simps, rule refl)

text \<open>Lines 1--10:\<close>
definition run_steps :: \<open>'a list \<Rightarrow> 'a state pmf\<close> where
  \<open>run_steps xs \<equiv> foldM_pmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state\<close>

text \<open>Line 11:\<close>
definition estimate :: \<open>'a state \<Rightarrow> real\<close> where
  \<open>estimate \<sigma> = card (state_\<chi> \<sigma>) / state_p \<sigma>\<close>

lemma run_steps_snoc: \<open>run_steps (xs @[x]) = run_steps xs \<bind> step_1 x \<bind> step_2\<close>
  unfolding run_steps_def foldM_pmf_snoc by (simp add:bind_assoc_pmf)

fun run_state_pmf where
  \<open>run_state_pmf (FinalState xs) = run_steps xs\<close> |
  \<open>run_state_pmf (IntermState xs x) = run_steps xs \<bind> step_1 x\<close>

fun len_run_state where
  \<open>len_run_state (FinalState xs) = length xs\<close> |
  \<open>len_run_state (IntermState xs x) = length xs\<close>

fun run_state_set where
  \<open>run_state_set (FinalState xs) = set xs\<close> |
  \<open>run_state_set (IntermState xs x) = set xs \<union> {x}\<close>

lemma finite_run_state_set[simp]: \<open>finite (run_state_set \<sigma>)\<close> by (cases \<sigma>) auto

lemma subsample_finite_pmf:
  assumes \<open>card U = n\<close>
  shows \<open>finite (set_pmf (subsample U))\<close>
proof-
  have \<open>finite (Pow U)\<close> unfolding finite_Pow_iff using assms n_gt_0 card_gt_0_iff by blast
  from finite_subset[OF _ this] show ?thesis using subsample[OF assms] by auto
qed

lemma finite_run_state_pmf: \<open>finite (set_pmf (run_state_pmf \<rho>))\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def)
next
  case (2 xs x) thus ?case by (simp add:step_1_def Let_def)
next
  case (3 xs x)
  have a: \<open>run_state_pmf (FinalState (xs@[x])) = run_state_pmf (IntermState xs x) \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case unfolding a using 3 subsample_finite_pmf
    by (auto simp:step_2_def simp del:run_state_pmf.simps)
qed

lemma state_\<chi>_run_state_pmf: \<open>AE \<sigma> in run_state_pmf \<rho>. state_\<chi> \<sigma> \<subseteq> run_state_set \<rho>\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def AE_measure_pmf_iff initial_state_def)
next
  case (2 xs x)
  then show ?case by (simp add:AE_measure_pmf_iff Let_def step_1_def) auto
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case unfolding b using subsample 3 by (simp add:AE_measure_pmf_iff step_2_def Let_def) blast
qed

lemma state_\<chi>_finite: \<open>AE \<sigma> in run_state_pmf \<rho>. finite (state_\<chi> \<sigma>)\<close>
  using finite_subset[OF _ finite_run_state_set]
  by (intro AE_mp[OF state_\<chi>_run_state_pmf AE_I2]) auto

lemma state_p_range: \<open>AE \<sigma> in run_state_pmf \<rho>. state_p \<sigma> \<in> {0<..1}\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def AE_measure_pmf_iff initial_state_def)
next
  case (2 xs x)
  then show ?case by (simp add:AE_measure_pmf_iff Let_def step_1_def)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  have \<open>x * f \<le> 1\<close> if \<open>x \<in> {0<..1}\<close> for x using f_range that by (intro mult_le_one) auto
  thus ?case unfolding b using 3 f_range by (simp add:AE_measure_pmf_iff step_2_def Let_def)
qed

text \<open>Lemma~\ref{le:prob_invariant}:\<close>
lemma run_steps_preserves_expectation_le:
  fixes \<phi> :: \<open>real \<Rightarrow> bool \<Rightarrow> real\<close>
  assumes phi :
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close>
    \<open>\<And> p x. \<lbrakk>0 < p; p \<le> 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> (\<integral>\<omega>. \<phi> x \<omega> \<partial>bernoulli_pmf p) \<le> \<phi> (x / p) True\<close>
    \<open>mono_on {0..1} (\<lambda>x. \<phi> x False)\<close>
  defines \<open>aux \<equiv> \<lambda> S \<sigma>. (\<Prod> x \<in> S. \<phi> (state_p \<sigma>) (x \<in> state_\<chi> \<sigma>))\<close>
  assumes \<open>S \<subseteq> run_state_set \<rho>\<close>
  shows \<open>measure_pmf.expectation (run_state_pmf \<rho>) (aux S) \<le> \<phi> 1 True ^ card S\<close>
  using assms(5)
proof (induction \<rho> arbitrary: S rule: run_state_induct)
  case 1 thus ?case by (simp add:aux_def)
next
  case (2 xs x)

  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have fin_S: \<open>finite S\<close> using finite_run_state_set 2(2) finite_subset by auto

  have a: \<open>aux S \<omega> = aux (S - {x}) \<omega> * aux (S \<inter> {x}) \<omega>\<close> for \<omega> :: \<open>'a state\<close>
    unfolding aux_def using fin_S by (subst prod.union_disjoint[symmetric]) (auto intro:prod.cong)

  have b: \<open>finite (set_pmf (run_steps xs \<bind> step_1 x))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>IntermState xs x\<close>] by simp

  have c:\<open>(\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<le> \<phi> 1 True^(card (S \<inter> {x}))\<close>  (is \<open>?L \<le> ?R\<close>)
    if \<open>\<tau> \<in> set_pmf (run_steps xs)\<close> for \<tau>
  proof(cases \<open>x \<in> S\<close>)
    case True
    have p_range: \<open>state_p \<tau> \<in> {0<..1}\<close>
      using state_p_range[where \<rho>=\<open>FinalState xs\<close>] that by (auto simp: AE_measure_pmf_iff)
    have \<open>?L = measure_pmf.expectation (bernoulli_pmf (state_p \<tau>)) (\<lambda>x. \<phi> (state_p \<tau>) x)\<close>
      unfolding step_1_def Let_def map_pmf_def[symmetric] integral_map_pmf aux_def using True
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have \<open>\<dots> \<le> \<phi> (state_p \<tau> / state_p \<tau>) True\<close> using p_range by (intro phi(2)) auto
    also have \<open>\<dots> \<le> \<phi> 1 True\<close> using p_range by simp
    also have \<open>\<dots> = \<phi> 1 True ^ card (S \<inter> {x})\<close> using True by simp
    finally show ?thesis by simp
  next
    case False thus ?thesis by (simp add:aux_def)
  qed

  have d: \<open>aux (S-{x}) \<tau> \<ge> 0\<close> if \<open>\<tau> \<in> set_pmf (run_steps xs)\<close> for \<tau>
    using state_p_range[where \<rho>=\<open>FinalState xs\<close>] that unfolding aux_def
    by (intro prod_nonneg phi(1) power_le_one) (auto simp: AE_measure_pmf_iff)

  have \<open>(\<integral>\<tau>. aux S \<tau> \<partial>(bind_pmf (run_steps xs) (step_1 x))) =
    (\<integral>\<tau>. (\<integral>u. aux (S - {x}) \<tau> * aux (S \<inter> {x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)\<close>
    unfolding integral_bind_pmf[OF bounded_finite[OF b]] a
    by (intro integral_cong_AE AE_pmfI arg_cong2[where f=\<open>(*)\<close>] prod.cong)
      (auto simp:step_1_def aux_def Let_def)
  also have \<open>\<dots> = (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)\<close>
    by simp
  also have \<open>\<dots> \<le> (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<phi> 1 True)^ card (S\<inter>{x}) \<partial>run_steps xs)\<close>
    by (intro integral_mono_AE AE_pmfI mult_left_mono c d) auto
  also have \<open>\<dots> = (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<integral>\<tau>. aux (S-{x}) \<tau> \<partial>(run_state_pmf (FinalState xs)))\<close>
    by simp
  also have \<open>\<dots> \<le> (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<phi> 1 True)^ card (S - {x})\<close>
    using phi(1) 2(2) by (intro mult_left_mono 2(1)) auto
  also have \<open>\<dots> = (\<phi> 1 True) ^ (card ((S\<inter>{x}) \<union> (S-{x})))\<close>
    using fin_S by (subst card_Un_disjoint) (auto simp add:power_add)
  also have \<open>\<dots> = (\<phi> 1 True) ^ card S\<close> by (auto intro!:arg_cong2[where f=\<open>\<lambda>x y. x ^ (card y)\<close>])
  finally show ?case by simp
next
  case (3 xs x)
  define p where  \<open>p = run_state_pmf (IntermState xs x)\<close>
  have a: \<open>run_state_pmf (FinalState (xs@[x])) = p \<bind> step_2\<close>
    by (simp add:run_steps_snoc p_def)

  have fin_S: \<open>finite S\<close> using finite_run_state_set 3(2) finite_subset by auto

  have \<open>finite (set_pmf p)\<close>
    using finite_run_state_pmf[where \<rho>=\<open>IntermState xs x\<close>] by (simp add:p_def)
  note [simp] = integrable_measure_pmf_finite[OF this]

  have b:\<open>finite (set_pmf (p \<bind> step_2))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState (xs@[x])\<close>] a by simp

  have c: \<open>(\<integral>u. (\<Prod>s\<in>S. \<phi> (f * state_p \<tau>) (s \<in> u)) \<partial>subsample (state_\<chi> \<tau>)) \<le> aux S \<tau>\<close>
    (is \<open>?L \<le> ?R\<close>) if that': \<open>card(state_\<chi> \<tau>) = n\<close> \<open>\<tau> \<in> set_pmf p\<close> for \<tau>
  proof -
    let ?q = \<open>subsample (state_\<chi> \<tau>)\<close>
    let ?U = \<open>state_\<chi> \<tau>\<close>

    define p' where \<open>p' = f * state_p \<tau>\<close>

    have d: \<open>y \<subseteq> state_\<chi> \<tau>\<close> if \<open>y \<in> set_pmf (subsample (state_\<chi> \<tau>))\<close> for y
      using subsample[OF that'(1)] that by auto

    have e: \<open>state_p \<tau> \<in> {0<..1}\<close>
      using that(2) unfolding p_def using state_p_range by (meson AE_measure_pmf_iff)
    hence f: \<open>p' \<in> {0<..1}\<close> unfolding p'_def using f_range by (auto intro:mult_le_one)

    have \<open>?L = (\<integral>u. (\<Prod>s\<in>(S-?U) \<union> (S\<inter>?U). \<phi> p' (s\<in>u)) \<partial>?q)\<close>
      using fin_S p'_def by (intro integral_cong_AE prod.cong AE_pmfI) auto
    also have \<open>\<dots> = (\<integral>u. (\<Prod>s\<in>S-?U. \<phi> p' (s\<in>u)) * (\<Prod>s\<in>(S\<inter>?U). \<phi> p' (s\<in>u)) \<partial>?q)\<close>
      using fin_S by (subst prod.union_disjoint) auto
    also have \<open>\<dots> = (\<integral>u. (\<Prod>s\<in>S-?U. \<phi> p' False) * (\<Prod>s\<in>(S\<inter>?U). \<phi> p' (s\<in>u)) \<partial>?q)\<close>
      using d by (intro integral_cong_AE AE_pmfI arg_cong2[where f=\<open>(*)\<close>] prod.cong
          arg_cong2[where f=\<open>\<phi>\<close>]) auto
    also have \<open>\<dots> = (\<Prod>s\<in>S-?U. \<phi> p' False) * (\<integral>u. (\<Prod>s\<in>S\<inter>?U. \<phi> p' (s\<in>u)) \<partial>?q)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> p' False) * (\<Prod>s\<in>S\<inter>?U. (\<integral>u. \<phi> p' u \<partial>bernoulli_pmf f))\<close>
      using that f by (intro mult_left_mono subsample_inequality prod_nonneg) (auto intro!:phi(1))
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> p' False) * (\<Prod>s\<in>S\<inter>?U. \<phi> (p'/f) True)\<close>
      using f f_range
      by (intro mult_left_mono prod_mono phi(2) conjI integral_nonneg_AE AE_pmfI phi(1) prod_nonneg)
         auto
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> (state_p \<tau>) False) * (\<Prod>s\<in>S\<inter>?U. \<phi> (state_p \<tau>) True)\<close>
      using e f f_range unfolding p'_def
      by (intro mult_mono prod_mono conjI phi(1) mono_onD[OF phi(3)] prod_nonneg power_le_one) auto
    also have \<open>\<dots> = (\<Prod>s\<in>S-?U. \<phi>(state_p \<tau>) (s \<in> ?U)) * (\<Prod>s\<in>S\<inter>?U. \<phi>(state_p \<tau>) (s \<in> ?U))\<close>
      by simp
    also have \<open>\<dots> = (\<Prod>s\<in>(S-?U)\<union>(S\<inter>?U). \<phi>(state_p \<tau>) (s \<in> ?U))\<close>
      using fin_S by (subst prod.union_disjoint[symmetric]) (auto)
    also have \<open>\<dots> = aux S \<tau>\<close> unfolding aux_def by (intro prod.cong) auto
    finally show ?thesis by simp
  qed

  have \<open>(\<integral>\<tau>. aux S \<tau> \<partial>run_state_pmf (FinalState (xs@[x]))) = (\<integral>\<tau>. aux S \<tau> \<partial>bind_pmf p step_2)\<close>
    unfolding a by simp
  also have \<open>\<dots> = (\<integral>\<tau>. (\<integral>u. aux S u \<partial>step_2 \<tau>) \<partial>p)\<close> by (intro integral_bind_pmf bounded_finite b)
  also have \<open>\<dots> = (\<integral>\<tau>. (if card(state_\<chi> \<tau>) = n then
    (\<integral>u. (\<Prod>s\<in>S. \<phi> (f * state_p \<tau>) (s \<in> u)) \<partial>subsample (state_\<chi> \<tau>)) else aux S \<tau>) \<partial>p)\<close>
    unfolding step_2_def map_pmf_def[symmetric] Let_def aux_def
    by (simp add:if_distrib if_distribR ac_simps cong:if_cong)
  also have \<open>\<dots> \<le> (\<integral>\<tau>. (if card(state_\<chi> \<tau>) < n then aux S \<tau> else aux S \<tau>) \<partial>p)\<close>
    using c by (intro integral_mono_AE AE_pmfI) auto
  also have \<open>\<dots> = (\<integral>\<tau>. aux S \<tau> \<partial>p)\<close> by simp
  also have \<open>\<dots> \<le> \<phi> 1 True ^ card S\<close> using 3(2) unfolding p_def by (intro 3(1)) auto
  finally show ?case by simp
qed

text \<open>Lemma~\ref{le:prob_invariant_simple}:\<close>
lemma run_steps_preserves_expectation_le' :
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes h:
    \<open>0 < q\<close> \<open>q \<le> 1\<close>
    \<open>concave_on {0 .. 1 / q} h\<close>
    \<open>\<And> x. \<lbrakk>0 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
  defines
    \<open>aux \<equiv> \<lambda>S \<sigma>. (\<Prod>x \<in> S. of_bool (state_p \<sigma> \<ge> q) * h (of_bool (x \<in> state_\<chi> \<sigma>) / state_p \<sigma>))\<close>

  assumes \<open>S \<subseteq> run_state_set \<rho>\<close>
  shows \<open>(\<integral>\<tau>. aux S \<tau> \<partial>run_state_pmf \<rho>) \<le> (h 1) ^ card S\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  define \<phi> where \<open>\<phi> = (\<lambda>p e. of_bool (q \<le> p) * h(of_bool e / p))\<close>
  have \<phi>_1: \<open>\<phi> x b \<ge> 0\<close> if \<open>x > 0\<close> \<open>x \<le> 1\<close> for x b
    using h(1,4) that unfolding \<phi>_def by simp
  have \<phi>_2: \<open>\<phi> x True * p + \<phi> x False * (1 - p) \<le> \<phi> (x / p) True\<close> if \<open>x \<in> {0<..1}\<close> \<open>p \<in> {0<..1}\<close>
    for x p
  proof (cases \<open> 1 / x \<in> {0..1 / q}\<close>)
    case True
    hence a:\<open>q \<le> x\<close> using that(1) h(1) by (simp add:divide_simps)
    also have \<open>\<dots> \<le> x/p\<close> using that by (auto simp add:divide_simps)
    finally have b:\<open>q \<le> x / p\<close> by simp
    show ?thesis
      unfolding \<phi>_def using that concave_onD[OF h(3) _ _ _ True, where t=\<open>p\<close> and x=\<open>0\<close>] a b h(1)
      by (auto simp:algebra_simps)
  next
    case False
    hence a:\<open>q > x\<close> using that h(1) by (auto simp add:divide_simps)
    hence \<open>q \<le> x/p \<Longrightarrow> 0 \<le> h (p / x)\<close> using that by (intro h(4)) (auto simp:field_simps)
    thus ?thesis using a by (simp add:\<phi>_def)
  qed
  have \<phi>_3: \<open>\<phi> x False \<le> \<phi> y False\<close> if \<open>x \<le> y\<close> for x y
     using that by (auto intro:h(4) simp add:\<phi>_def)

  have \<open>?L = (\<integral>\<tau>. (\<Prod>x\<in>S. \<phi> (state_p \<tau>) (x \<in> state_\<chi> \<tau>)) \<partial>run_state_pmf \<rho>)\<close>
    unfolding \<phi>_def by (simp add:state_p_def aux_def)
  also have \<open>\<dots> \<le> \<phi> 1 True^ card S\<close> using \<phi>_1 \<phi>_2 \<phi>_3
    by (intro run_steps_preserves_expectation_le assms ) (auto intro:mono_onI)
  also have \<open>\<dots> = h 1 ^ card S\<close> using h unfolding \<phi>_def by simp
  finally show ?thesis by simp
qed

text \<open>Analysis of the case where @{term \<open>card (set xs) \<ge> n\<close>}:\<close>

context
  fixes xs :: \<open>'a list\<close>
begin

private abbreviation \<open>A \<equiv> real (card (set xs))\<close>

context
  assumes set_larger_than_n: \<open>card (set xs) \<ge> n\<close>
begin

private definition \<open>q = real n / (4 * card (set xs))\<close>

lemma q_range: \<open>q \<in> {0<..1/4}\<close>
  using set_larger_than_n n_gt_0 unfolding q_def by auto

lemma mono_nonnegI:
  assumes \<open>\<And>x. x \<in> I \<Longrightarrow> h' x \<ge> 0\<close>
  assumes \<open>\<And>x. x \<in> I \<Longrightarrow> (h has_real_derivative (h' x)) (at x)\<close>
  assumes \<open>x \<in> I \<inter> {0..}\<close> \<open>convex I\<close> \<open>0 \<in> I\<close> \<open>h 0 \<ge> 0\<close>
  shows \<open>h x \<ge> 0\<close>
proof -
  have h_mono: \<open>h x \<le> h y\<close> if that': \<open>x \<le> y\<close> \<open>x \<in> I\<close> \<open>y \<in> I\<close> for x y
  proof -
    have \<open>{x..y} \<subseteq> I\<close> unfolding closed_segment_eq_real_ivl1[OF that(1),symmetric]
      by (intro closed_segment_subset assms that)
    from subsetD[OF this]
    show ?thesis using assms(1,2) by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) auto
  qed

  have \<open>0 \<le> h 0\<close> using assms by simp
  also have \<open>\<dots> \<le> h x\<close> using assms by (intro h_mono) auto
  finally show ?thesis by simp
qed

lemma upper_tail_bound_helper:
  assumes \<open>x \<in> {0<..1::real}\<close>
  defines \<open>h \<equiv> (\<lambda>x. - q * x\<^sup>2 / 3 - ln (1 + q * x) + q * ln (1 + x) * (1 + x))\<close>
  shows \<open>h x \<ge> 0\<close>
proof -
  define h' where \<open>h' x = -2*x*q/3 - q/(1+q*x) + q*ln(1+x) + q\<close> for x :: real

  have a: \<open>(h has_real_derivative (h' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>0 < (1::real) + 0\<close> by simp
    also have \<open>\<dots> \<le> 1 + q * x\<close> using that q_range by (intro add_mono mult_nonneg_nonneg) auto
    finally have \<open>0 < 1 + q * x\<close> by simp
    thus ?thesis
      using that q_range unfolding h_def h'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have b: \<open>h' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>exp(2*x/3) = exp( (1-x) *\<^sub>R 0 + x *\<^sub>R (2/3))\<close> by simp
    also have \<open>\<dots> \<le> (1-x) * exp 0 + x * exp(2/3)\<close>
      using that by (intro convex_onD[OF exp_convex]) auto
    also have \<open>\<dots> = 1 + x * (exp (2/3)-exp 0)\<close> by (simp add:algebra_simps)
    also have \<open>\<dots> \<le> 1 + x * 1\<close> by (intro that add_mono order.refl mult_left_mono) (approximation 5)
    finally have \<open>exp(2*x/3) \<le> exp (ln (1+x))\<close> using that by simp
    hence \<open>0 \<le> ln (1+x) - 2 * x / 3\<close> by simp
    also have \<open>\<dots> = ln (1+x) + 1 - 2*x/3 - 1\<close> by simp
    also have \<open>\<dots> \<le> ln (1+x) + 1 - 2*x/3 - 1/(1+q*x)\<close>
      using q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have c: \<open>0 \<le> ln (1+x) + 1 - 2*x/3 - 1/(1+q*x)\<close> by simp

    have \<open>h' x = q * (-2*x/3 - 1/(1+q*x) + ln (1+x) + 1)\<close>
      unfolding h'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close> using c q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  show ?thesis by (rule mono_nonnegI[where I=\<open>{0..1}\<close>, OF b a]) (use assms(1) h_def in simp_all)
qed

private definition \<theta> where \<open>\<theta> t x = 1 + q * x * (exp (t / q) - 1)\<close>

lemma \<theta>_concave: \<open>concave_on {0..1 / q} (\<theta> t)\<close>
  unfolding \<theta>_def by (intro concave_on_linorderI) (auto simp:algebra_simps)

lemma \<theta>_ge_exp_1:
  assumes \<open>x \<in> {0..1/q}\<close>
  shows \<open>exp (t * x) \<le> \<theta> t x\<close>
proof -
  have \<open>exp (t * x) = exp ((1-q*x) *\<^sub>R 0 + (q*x) *\<^sub>R (t/q))\<close> using q_range by simp
  also have \<open>\<dots> \<le> (1-q*x) * exp 0 + (q*x) * exp (t/q)\<close> using assms q_range
    by (intro convex_onD[OF exp_convex]) (auto simp:field_simps)
  also have \<open>\<dots> = \<theta> t x\<close> unfolding \<theta>_def by (simp add:algebra_simps)
  finally show ?thesis by simp
qed

lemma \<theta>_ge_exp:
  assumes \<open>y \<ge> q\<close>
  shows \<open>exp (t / y) \<le> \<theta> t (1 / y)\<close>
  using assms \<theta>_ge_exp_1[where x=\<open>1/y\<close> and t=t] q_range by (auto simp:field_simps)

lemma \<theta>_nonneg:
  assumes \<open>x \<in> {0..1/q}\<close>
  shows \<open>\<theta> t x \<ge> 0\<close> \<open>\<theta> t x > 0\<close>
proof -
  have \<open>0 < exp (t * x)\<close> by simp
  also have \<open>\<dots> \<le> \<theta> t x\<close> by (intro \<theta>_ge_exp_1 assms)
  finally show \<open>\<theta> t x > 0\<close> by simp
  thus \<open>\<theta> t x \<ge> 0\<close> by simp
qed

lemma \<theta>_0: \<open>\<theta> t 0 = 1\<close> unfolding \<theta>_def by simp

lemma tail_bound_aux:
  assumes \<open>run_state_set \<rho> \<subseteq> set xs\<close> \<open>c > 0\<close>
  defines \<open>A' \<equiv> real (card (run_state_set \<rho>))\<close>
  shows \<open>measure (run_state_pmf \<rho>) {\<omega>. exp (t * estimate \<omega>) \<ge> c \<and> state_p \<omega> \<ge> q} \<le> \<theta> t 1 powr A'/c\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf \<rho>\<close>
  note [simp] = integrable_measure_pmf_finite[OF finite_run_state_pmf]

  let ?A' = \<open>run_state_set \<rho>\<close>
  let ?X = \<open>\<lambda>i \<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega>\<close>

  have a: \<open>0 < \<theta> t 1\<close> using q_range by (intro \<theta>_nonneg) auto

  have \<open>?L \<le> \<P>(\<omega> in ?p. of_bool(state_p \<omega> \<ge> q) * exp (t*estimate \<omega>) \<ge> c)\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp (t*estimate \<omega>) \<partial>?p) / c\<close>
    by (intro integral_Markov_inequality_measure[where A=\<open>{}\<close>] assms(2)) simp_all
  also have \<open>\<dots> = (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp((\<Sum>i\<in>?A'. t * ?X i \<omega>)) \<partial>?p)/c\<close>
    using state_\<chi>_run_state_pmf[where \<rho>=\<open>\<rho>\<close>] Int_absorb1
    unfolding sum_divide_distrib[symmetric] sum_distrib_left[symmetric] estimate_def
    by (intro integral_cong_AE arg_cong2[where f=\<open>(/)\<close>])
      (auto simp:AE_measure_pmf_iff intro!:arg_cong[where f=\<open>card\<close>])
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q) * exp(t * ?X i \<omega>)) \<partial>?p) / c\<close>
    unfolding exp_sum[OF finite_run_state_set] prod.distrib using assms(2)
    by (intro divide_right_mono integral_mono_AE AE_pmfI)
      (auto intro!:mult_nonneg_nonneg prod_nonneg)
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q) * \<theta> t (?X i \<omega>)) \<partial>?p) / c\<close>
    using assms(2) \<theta>_ge_exp \<theta>_0 by (intro divide_right_mono integral_mono_AE AE_pmfI prod_mono) auto
  also have \<open>\<dots> \<le> \<theta> t 1 ^ card ?A' / c\<close> using q_range \<theta>_concave assms(2)
    by (intro divide_right_mono run_steps_preserves_expectation_le' \<theta>_nonneg)
     (auto intro!:\<theta>_nonneg simp:field_simps)
  also have \<open>\<dots> \<le> ?R\<close>
    unfolding A'_def using card_mono[OF _ assms(1)] assms(2) a
    by (subst powr_realpow) (auto intro!:power_increasing divide_right_mono)
  finally show ?thesis by simp
qed

text \<open>Lemma \ref{le:upper_tail}:\<close>
lemma upper_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..1::real}\<close>
  assumes \<open>run_state_set \<rho> \<subseteq> set xs\<close>
  shows \<open>measure (run_state_pmf \<rho>) {\<omega>. estimate \<omega> \<ge> (1+\<epsilon>)*A \<and> state_p \<omega> \<ge> q} \<le> exp(-real n/12*\<epsilon>\<^sup>2)\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf \<rho>\<close>
  define t where \<open>t = q * ln (1+\<epsilon>)\<close>

  have t_gt_0: \<open>t > 0\<close> unfolding t_def using q_range assms(1) by auto

  have mono_exp_t: \<open>strict_mono (\<lambda>(x::real). exp (t * x))\<close>
    using t_gt_0 by (intro strict_monoI) auto

  have a: \<open>\<theta> t 1 = 1 + q * \<epsilon>\<close> using assms(1) unfolding \<theta>_def t_def by simp
  have b: \<open>\<theta> t 1 \<ge> 1\<close> unfolding a using q_range assms(1) by auto

  have c: \<open>ln (\<theta> t 1) - t * (1 + \<epsilon>) \<le> - q * \<epsilon>^2 / 3\<close>
    using upper_tail_bound_helper[OF assms(1)]
    unfolding a unfolding t_def by (simp add:algebra_simps)

  have \<open>?L = measure ?p {\<omega>. exp (t * estimate \<omega>) \<ge> exp (t*((1+\<epsilon>)* A))\<and>state_p \<omega>\<ge> q}\<close>
    by (subst strict_mono_less_eq[OF mono_exp_t]) simp
  also have \<open>\<dots> \<le> \<theta> t 1 powr real (card (run_state_set \<rho>)) / exp (t * ((1+\<epsilon>)* A))\<close>
    by (intro tail_bound_aux assms) auto
  also have \<open>\<dots> \<le> \<theta> t 1 powr A / exp (t * ((1+\<epsilon>)* A))\<close>
    using card_mono[OF finite_set assms(2)] b
    by (intro powr_mono divide_right_mono) auto
  also have \<open>\<dots> = exp (A * (ln (\<theta> t 1) - t * (1 + \<epsilon>)))\<close>
    using b unfolding powr_def by (simp add:algebra_simps exp_diff)
  also have \<open>\<dots> \<le> exp (A * (-q * \<epsilon>^2/3))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono c) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_n n_gt_0 unfolding q_def by auto
  finally show ?thesis by simp
qed

text \<open>Lemma~\ref{le:low_p}:\<close>
lemma low_p:
  shows \<open>measure (run_steps xs) {\<sigma>. state_p \<sigma> < q} \<le> real (length xs) * exp(-real n/12)\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  define \<rho> where \<open>\<rho> = FinalState xs\<close>

  have ih: \<open>run_state_set \<rho> \<subseteq> set xs\<close> unfolding \<rho>_def by simp

  have \<open>?L = measure (run_state_pmf \<rho>) {\<omega>. state_p \<omega> < q}\<close>
    unfolding \<rho>_def run_state_pmf.simps by simp
  also have \<open>\<dots> \<le> real (len_run_state \<rho>) * exp(- real n/12)\<close>
    using ih
  proof (induction \<rho> rule:run_state_induct)
    case 1
    then show ?case using q_range by (simp add:run_steps_def initial_state_def)
  next
    case (2 ys x)
    let ?pmf = \<open>run_state_pmf (IntermState ys x)\<close>
    have a:\<open>run_state_set (FinalState ys) \<subseteq> set xs\<close> using 2(2) by auto

    have \<open>measure ?pmf {\<omega>. state_p \<omega> < q} = (\<integral>\<sigma>. of_bool (state_p \<sigma> < q) \<partial>run_steps ys)\<close>
      unfolding run_state_pmf.simps step_1_def Let_def by (simp add:measure_bind_pmf indicator_def)
    also have \<open>\<dots> = (\<integral>\<sigma>. indicator {\<omega>. (state_p \<omega> < q)} \<sigma> \<partial>run_steps ys)\<close>
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have \<open>\<dots> = measure (run_steps ys) {\<omega>. (state_p \<omega> < q)}\<close> by simp
    also have \<open>\<dots> \<le> real (len_run_state (IntermState ys x)) * exp (- real n / 12)\<close>
      using 2(1)[OF a] by simp
    finally show ?case by simp
  next
    case (3 ys x)
    define p where \<open>p = run_state_pmf (IntermState ys x)\<close>

    have \<open>finite (set_pmf p)\<close> unfolding p_def by (intro finite_run_state_pmf)
    note [simp] = integrable_measure_pmf_finite[OF this]

    have a: \<open>run_state_pmf (FinalState (ys@[x])) = p \<bind> step_2\<close> (is \<open>?pmf= _\<close>)
      by (simp add:run_steps_snoc p_def)

    have b: \<open>run_state_set (IntermState ys x) \<subseteq> set xs\<close>
      using 3(2) by simp

    have c:\<open>measure (step_2 \<sigma>) {\<sigma>. state_p \<sigma> < q} \<le>
      indicator {\<sigma>. state_p \<sigma> < q \<or> (card (state_\<chi> \<sigma>) = n \<and> state_p \<sigma> \<in> {q..<q/f}) } \<sigma>\<close>
      for \<sigma> :: \<open>'a state\<close>
      using f_range
      by (simp add:step_2_def Let_def indicator_def map_pmf_def[symmetric] divide_simps)

    have d: \<open>2 * real (card (set xs)) \<le> real n / \<alpha>\<close> if \<open>\<alpha> \<in> {q..<q / f}\<close> for \<alpha>
    proof -
      have \<open>\<alpha> \<le> q * (1/f)\<close> using that by simp
      also have \<open>\<dots> \<le> q * 2\<close> using q_range f_range by (intro mult_left_mono) (auto simp:divide_simps)
      finally have \<open>\<alpha> \<le> 2*q\<close> by simp
      hence \<open>\<alpha> \<le> real n / (2 * real (card (set xs)))\<close>
        using set_larger_than_n n_gt_0 unfolding q_def by (simp add:divide_simps)
      thus ?thesis
        using set_larger_than_n n_gt_0 that q_range by (simp add:field_simps)
    qed

    hence \<open>measure p {\<sigma>. card (state_\<chi> \<sigma>) = n \<and> state_p \<sigma> \<in> {q..<q/f}} \<le>
      measure p {\<sigma>. (1+1) * A \<le> estimate \<sigma> \<and> q \<le> state_p \<sigma>}\<close>
      unfolding estimate_def by (intro pmf_mono) (simp add:estimate_def)
    also have \<open>\<dots> \<le> exp (- real n / 12 * 1^2)\<close>
      unfolding p_def by (intro upper_tail_bound b) simp
    finally have e:
      \<open>measure p {\<sigma>. card (state_\<chi> \<sigma>) = n \<and> state_p \<sigma> \<in> {q..<q/f}} \<le> exp (- real n / 12)\<close>
      by simp

    have \<open>measure (run_state_pmf (FinalState (ys @ [x]))) {\<omega>. state_p \<omega> < q} =
      (\<integral>s. measure (step_2 s) {\<omega>. state_p \<omega> < q} \<partial>p)\<close>
      unfolding a by (simp add:measure_bind_pmf)
    also have \<open>\<dots> \<le> (\<integral>s. indicator {\<omega>. state_p \<omega> < q \<or> card (state_\<chi> \<omega>) = n \<and> state_p \<omega> \<in> {q..<q/f}} s \<partial>p)\<close>
      by (intro integral_mono_AE AE_pmfI c) simp_all
    also have \<open>\<dots> = measure p {\<omega>. state_p \<omega> < q \<or> card (state_\<chi> \<omega>) = n \<and> state_p \<omega> \<in> {q..<q/f}}\<close>
      by simp
    also have \<open>\<dots> \<le>measure p {\<omega>. state_p \<omega><q}+measure p {\<omega>. card(state_\<chi> \<omega>)=n\<and>state_p \<omega>\<in>{q..<q/f}}\<close>
      by (intro pmf_add) auto
    also have \<open>\<dots> \<le> length ys * exp (- real n / 12) + exp (- real n / 12)\<close>
      using 3(1)[OF b] by (intro add_mono e) (simp add:p_def)
    also have \<open>\<dots> = real (len_run_state (FinalState (ys @ [x]))) * exp (- real n / 12)\<close>
      by (simp add:algebra_simps)
    finally show ?case by simp
  qed
  also have \<open>\<dots> = real (length xs) * exp(- real n/12)\<close> by (simp add:\<rho>_def)
  finally show ?thesis by simp
qed

lemma lower_tail_bound_helper:
  assumes \<open>x \<in> {0<..<1::real}\<close>
  defines \<open>h \<equiv> (\<lambda>x. - q * x\<^sup>2 / 2 - ln (1 - q * x) + q * ln (1 - x) * (1 - x))\<close>
  shows \<open>h x \<ge> 0\<close>
proof -
  define h' where \<open>h' x = -x*q + q/(1-q*x) - q*ln(1-x) - q\<close> for x

  have a: \<open>(h has_real_derivative (h' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have \<open>q * x < 1\<close> by simp
    thus ?thesis
      using that q_range unfolding h_def h'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have b: \<open>h' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have a:\<open>q * x < 1\<close> by simp

    have \<open>0 \<le> - ln (1 - x) - x\<close> using ln_one_minus_pos_upper_bound[OF that] by simp
    also have \<open>\<dots> = - ln (1 - x) - 1 - x + 1\<close> by simp
    also have \<open>\<dots> \<le> - ln (1 - x) - 1 - x + 1 / (1 - q * x)\<close>
      using a q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have b: \<open>0 \<le> - ln (1 - x) - 1 - x + 1 / (1 - q * x)\<close> by simp

    have \<open>h' x = q * (-x + 1 / (1 - q * x) - ln (1 - x) - 1)\<close>
      unfolding h'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close>  using b q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  show ?thesis by (rule mono_nonnegI[where I=\<open>{0..<1}\<close>, OF b a]) (use assms(1) h_def in simp_all)
qed

text \<open>Lemma~\ref{le:lower_tail}:\<close>
lemma lower_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..<1::real}\<close>
  shows \<open>measure (run_steps xs) {\<omega>. estimate \<omega> \<le> (1-\<epsilon>) * A \<and> state_p \<omega> \<ge> q} \<le> exp(-real n/8*\<epsilon>\<^sup>2)\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf (FinalState xs)\<close>
  define t where \<open>t = q * ln (1-\<epsilon>)\<close>

  have t_lt_0: \<open>t < 0\<close>
    unfolding t_def using q_range assms(1) by (intro mult_pos_neg ln_less_zero) auto

  have mono_exp_t: \<open>exp (t * x) \<le> exp (t * y) \<longleftrightarrow> y \<le> x\<close> for x y using t_lt_0 by auto

  have a: \<open>\<theta> t 1 = 1 - q * \<epsilon>\<close> using assms(1) unfolding \<theta>_def t_def by simp
  have \<open>\<epsilon> * (q * 4) \<le> 1 * 1\<close> using q_range assms(1) by (intro mult_mono) auto
  hence b: \<open>\<theta> t 1 \<ge> 3/4\<close> unfolding a by (auto simp:algebra_simps)

  have c: \<open>ln (\<theta> t 1) - t * (1 - \<epsilon>) \<le> - q * \<epsilon>^2 / 2\<close>
    unfolding a unfolding t_def using lower_tail_bound_helper[OF assms(1)]
    by (simp add:divide_simps)

  have \<open>?L = measure ?p {\<omega>. exp (t * estimate \<omega>) \<ge> exp (t * ((1-\<epsilon>) * A)) \<and> state_p \<omega> \<ge> q}\<close>
    by (subst mono_exp_t) simp
  also have \<open>\<dots> \<le> \<theta> t 1 powr card (run_state_set (FinalState xs)) / exp (t * ((1 - \<epsilon>) * A))\<close>
    by (intro tail_bound_aux assms) auto
  also have \<open>\<dots> \<le> \<theta> t 1 powr A / exp (t * ((1 - \<epsilon>) * A))\<close> by simp
  also have \<open>\<dots> = exp (A * (ln (\<theta> t 1) - t * (1 - \<epsilon>)))\<close>
    using b unfolding powr_def by (simp add:algebra_simps exp_add[symmetric] exp_diff)
  also have \<open>\<dots> \<le> exp (A * (- q * \<epsilon> ^ 2 / 2))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono c) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_n n_gt_0 unfolding q_def by auto
  finally show ?thesis by simp
qed

lemma correctness_aux:
  assumes \<open>\<epsilon> \<in> {0<..<1::real}\<close> \<open>\<delta> \<in> {0<..<1::real}\<close>
  assumes \<open>real n \<ge> 12/\<epsilon>^2 * ln (3*real (length xs) /\<delta>)\<close>
  shows \<open>measure (run_steps xs) {\<omega>. \<bar>estimate \<omega> - A\<bar> > \<epsilon>*A } \<le> \<delta>\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?pmf = \<open>run_steps xs\<close>
  let ?pmf' = \<open>run_state_pmf (FinalState xs)\<close>
  let ?p = \<open>state_p\<close>
  let ?l = \<open>real (length xs)\<close>
  have l_gt_0: \<open>length xs > 0\<close> using set_larger_than_n n_gt_0 by auto
  hence l_ge_1: \<open>?l \<ge> 1\<close>  by linarith

  have a:\<open>ln (3 * real (length xs) / \<delta>) = - ln (\<delta> / (3 * ?l))\<close>
    using l_ge_1 assms(2) by (subst (1 2) ln_div) auto

  have \<open>exp (- real n / 12 * 1) \<le> exp (- real n / 12 * \<epsilon> ^ 2)\<close>
    using assms(1) by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg power_le_one) auto
  also have \<open>\<dots> \<le>  \<delta> / (3 * ?l)\<close>
    using assms(1-3) l_ge_1 unfolding a by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  finally have \<open>exp (- real n / 12) \<le> \<delta> / (3*?l)\<close> by simp
  hence b: \<open>?l * exp (- real n / 12) \<le> \<delta> / 3\<close> using l_gt_0 by (auto simp:field_simps)

  have \<open>exp(-real n/12 * \<epsilon>^2) \<le> \<delta> / (3*?l)\<close>
    using assms(1-3) l_ge_1 unfolding a by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  also have \<open>\<dots> \<le> \<delta> / 3\<close> using assms(1-3) l_ge_1 by (intro divide_left_mono) auto
  finally have c: \<open>exp(-real n/12 * \<epsilon>^2) \<le> \<delta> / 3\<close> by simp

  have \<open>exp(-real n/8 * \<epsilon>^2) \<le> exp(-real n/12 * \<epsilon>^2)\<close> by (intro iffD2[OF exp_le_cancel_iff]) auto
  also have \<open>\<dots> \<le> \<delta>/3\<close> using c by simp
  finally have d: \<open>exp(-real n/8 * \<epsilon>^2) \<le> \<delta> / 3\<close> by simp

  have \<open>?L \<le> measure ?pmf {\<omega>. \<bar>estimate \<omega> - A\<bar> \<ge> \<epsilon> * A}\<close> by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. \<bar>estimate \<omega> - A\<bar> \<ge> \<epsilon>*A \<and> ?p \<omega> \<ge> q} + measure ?pmf {\<omega>. ?p \<omega> < q}\<close>
    by (intro pmf_add) auto
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. (estimate \<omega> \<le> (1-\<epsilon>) * A \<or> estimate \<omega> \<ge> (1+\<epsilon>) * A) \<and> ?p \<omega> \<ge> q} +
    ?l * exp(-real n/12)\<close>
    by (intro pmf_mono add_mono low_p) (auto simp:abs_real_def algebra_simps split:if_split_asm)
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. estimate \<omega> \<le> (1-\<epsilon>) * A \<and> state_p \<omega> \<ge> q} +
    measure ?pmf' {\<omega>. estimate \<omega> \<ge> (1+\<epsilon>) * A \<and> state_p \<omega> \<ge> q} + \<delta>/3\<close>
    unfolding run_state_pmf.simps by (intro add_mono pmf_add b) auto
  also have \<open>\<dots> \<le> exp(-real n/8 * \<epsilon> ^ 2) + exp(-real n/12 * \<epsilon> ^ 2) + \<delta> / 3\<close>
    using assms(1) by (intro upper_tail_bound add_mono lower_tail_bound) auto
  also have \<open>\<dots> \<le> \<delta> / 3 +  \<delta> / 3 + \<delta> / 3\<close> by (intro  add_mono d c) auto
  finally show ?thesis by simp
qed

end

lemma deterministic_phase:
  assumes \<open>card (run_state_set \<sigma>) < n\<close>
  shows \<open>run_state_pmf \<sigma> = return_pmf (State (run_state_set \<sigma>) 1)\<close>
  using assms
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def initial_state_def)
next
  case (2 xs x)
  have \<open>card (set xs) < n\<close> using 2(2) by (simp add:card_insert_if) presburger
  moreover have \<open>bernoulli_pmf 1 = return_pmf True\<close>
    by (intro pmf_eqI) (auto simp:bernoulli_pmf.rep_eq)
  ultimately show ?case using 2(1) by (simp add:step_1_def bind_return_pmf)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have a: \<open>card (run_state_set (IntermState xs x)) < n\<close> using 3(2) by simp
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case
    using 3(2) unfolding b 3(1)[OF a] by (simp add:step_2_def bind_return_pmf Let_def)
qed

text \<open>Theorem~\ref{th:concentration}:\<close>
theorem correctness:
  fixes \<epsilon> \<delta> :: real
  assumes \<open>\<epsilon> \<in> {0<..<1}\<close> \<open>\<delta> \<in> {0<..<1}\<close>
  assumes \<open>real n \<ge> 12 / \<epsilon>\<^sup>2 * ln (3 * real (length xs) / \<delta>)\<close>
  shows \<open>measure (run_steps xs) {\<omega>. \<bar>estimate \<omega> - A\<bar> > \<epsilon> * A} \<le> \<delta>\<close>
proof (cases \<open>card (set xs) \<ge> n\<close>)
  case True
  show ?thesis by (intro correctness_aux True assms)
next
  case False
  hence \<open>run_steps xs = return_pmf (State (set xs) 1)\<close>
    using deterministic_phase[where \<sigma>=\<open>FinalState xs\<close>] by simp
  thus ?thesis using assms(1,2) by (simp add:indicator_def estimate_def not_less)
qed

lemma p_pos: \<open>\<exists>M\<in>{0<..1}. AE \<omega> in run_steps xs. state_p \<omega> \<ge> M\<close>
proof -
  have fin:\<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  define M where \<open>M = (MIN \<sigma> \<in> set_pmf (run_steps xs). state_p \<sigma>)\<close>
  have \<open>M \<in> state_p ` set_pmf (run_steps xs)\<close>
    using fin set_pmf_not_empty unfolding M_def by (intro Min_in) auto
  also have \<open>\<dots> \<subseteq> {0<..1}\<close>
    using state_p_range[where \<rho>=\<open>FinalState xs\<close>]
    by (intro image_subsetI) (simp add:AE_measure_pmf_iff)
  finally have \<open>M \<in> {0<..1}\<close> by simp

  moreover have \<open>AE \<omega> in run_steps xs. state_p \<omega> \<ge> M\<close>
    using fin unfolding AE_measure_pmf_iff M_def by (intro ballI Min_le) auto
  ultimately show ?thesis by auto
qed

lemma run_steps_expectation_sing:
  assumes i: \<open>i \<in> set xs\<close>
  shows \<open>measure_pmf.expectation (run_steps xs) (\<lambda>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega>) = 1\<close>
  (is \<open>?L = _\<close>)
proof -
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note int = integrable_measure_pmf_finite[OF this]

  obtain M where *: \<open>AE \<sigma> in run_steps xs. M \<le> state_p \<sigma>\<close> and M_range: \<open>M \<in> {0<..1}\<close>
    using p_pos by blast
  then have \<open>?L = (\<integral>\<tau>. (\<Prod>x\<in>{i}. of_bool (M \<le> state_p \<tau>) * (of_bool (x \<in> state_\<chi> \<tau>) / state_p \<tau>))
      \<partial>run_state_pmf (FinalState xs))\<close>
    by (auto intro!: integral_cong_AE)

  also have \<open>\<dots> \<le> 1 ^ card {i}\<close>
    using M_range i by (intro run_steps_preserves_expectation_le') (auto simp:concave_on_iff)
  finally have le: \<open>?L \<le> 1\<close> by auto

  have concave: \<open>concave_on {0..1 / M} ((-) (1 / M + 1))\<close>
    unfolding concave_on_iff
    using M_range apply (clarsimp simp add: field_simps)
    by (metis combine_common_factor distrib_right linear mult_1_left)

  have \<open>1 / M + 1 - ?L = (\<integral>\<omega>. 1 / M + 1 - of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega> \<partial>run_steps xs)\<close>
    by (auto simp:int)
  also have \<open>\<dots> = (\<integral>\<tau>. (\<Prod>x\<in>{i}. of_bool (M \<le> state_p \<tau>) *
    (1 / M + 1 - of_bool (x \<in> state_\<chi> \<tau>) / state_p \<tau>)) \<partial>run_state_pmf (FinalState xs))\<close>
    using * by (auto intro!: integral_cong_AE)
  also have \<open>\<dots> \<le> (1 / M + 1 - 1) ^ card {i}\<close>
    using i M_range
    by (intro run_steps_preserves_expectation_le'[OF _ _ concave]) (auto simp: field_simps)
  also have \<open>\<dots> = 1 / M\<close> by auto
  finally have ge:\<open> -?L \<le> -1\<close> by auto
  show ?thesis using le ge by auto
qed

text \<open>Subsection~\ref{sec:unbiasedness}:\<close>
corollary unbiasedness:
  fixes \<sigma> :: \<open>'a run_state\<close>
  shows \<open>measure_pmf.expectation (run_steps xs) estimate = real (card (set xs))\<close>
    (is \<open>?L = _\<close>)
proof -
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have s: \<open>AE \<omega> in run_steps xs. state_\<chi> \<omega> \<subseteq> set xs\<close>
    by (metis run_state_pmf.simps(1) run_state_set.simps(1) state_\<chi>_run_state_pmf)

  have \<open>?L = (\<integral>\<omega>. (\<Sum>i\<in>set xs. of_bool (i \<in> state_\<chi> \<omega>)) / state_p \<omega> \<partial>run_steps xs)\<close>
    unfolding estimate_def state_p_def[symmetric]
    by (auto intro!: integral_cong_AE intro: AE_mp[OF s] simp add: Int_absorb1)

  also have \<open>\<dots> = (\<integral>\<omega>. (\<Sum>i\<in>set xs. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega>) \<partial>run_steps xs)\<close>
    by (metis (no_types) sum_divide_distrib)
  also have \<open>\<dots> = (\<Sum>i\<in>set xs. (\<integral>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega> \<partial>run_steps xs))\<close>
    by (auto intro: Bochner_Integration.integral_sum)
  also have \<open>\<dots> = (\<Sum>i\<in>set xs. 1)\<close>
    using run_steps_expectation_sing by (auto cong:sum.cong)
  finally show ?thesis by auto
qed

end (* fixes xs *)

end (* cvm_algo_abstract *)

end (* theory *)
