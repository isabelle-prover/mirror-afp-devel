section \<open>Randomized Algorithms (Internal Representation)\label{sec:randomized_algorithm_internal}\<close>

theory Randomized_Algorithm_Internal
  imports
    "HOL-Probability.Probability"
    "Coin_Space"
    "Tau_Additivity"
    "Zeta_Function.Zeta_Library"
    (* The last import is to pull set_nn_integral_cong which should be in
    HOL-Analysis.Set_Integral. *)
begin

text \<open>This section introduces the internal representation for randomized algorithms. For ease of
use, we will introduce in Section~\ref{sec:randomized_algorithm} a @{command "typedef"} for the
monad which is easier to work with.\<close>

text \<open>This is the inverse of @{term "set_option"}\<close>

definition the_elem_opt :: "'a set \<Rightarrow> 'a option"
  where "the_elem_opt S = (if Set.is_singleton S then Some (the_elem S) else None)"

lemma the_elem_opt_empty[simp]: "the_elem_opt {} = None"
  unfolding the_elem_opt_def is_singleton_def by (simp split:if_split_asm)

lemma the_elem_opt_single[simp]: "the_elem_opt {x} = Some x"
  unfolding the_elem_opt_def by simp

definition at_most_one :: "'a set \<Rightarrow> bool"
  where "at_most_one S \<longleftrightarrow> (\<forall>x y. x \<in> S \<and> y \<in> S \<longrightarrow> x = y)"

lemma at_most_one_cases[consumes 1]:
  assumes "at_most_one S"
  assumes "P {the_elem S}"
  assumes "P {}"
  shows "P S"
proof (cases "S = {}")
  case True
  then show ?thesis using assms by auto
next
  case False
  then obtain x where "x \<in> S" by auto
  hence "S = {x}" using assms(1) unfolding at_most_one_def by auto
  thus ?thesis using assms(2) by simp
qed

lemma the_elem_opt_Some_iff[simp]: "at_most_one S \<Longrightarrow> the_elem_opt S = Some x \<longleftrightarrow> S = {x}"
  by (induction S rule:at_most_one_cases) auto

lemma the_elem_opt_None_iff[simp]: "at_most_one S \<Longrightarrow> the_elem_opt S = None \<longleftrightarrow> S = {}"
  by (induction S rule:at_most_one_cases) auto

text \<open>The following is the fundamental type of the randomized algorithms, which are represented
as functions that take an infinite stream of coin flips and return the unused suffix of coin-flips
together with the result. We use the @{typ "'a option"} type to be able to introduce the
denotational semantics for the monad.\<close>

type_synonym 'a random_alg_int = "coin_stream \<Rightarrow> ('a \<times> coin_stream) option"

text \<open>The @{term "return_rai"} combinator, does not consume any coin-flips and thus returns the
entire stream together with the result.\<close>

definition return_rai :: "'a \<Rightarrow> 'a random_alg_int"
  where "return_rai x bs = Some (x, bs)"

text \<open>The @{term "bind_rai"} combinator passes the coin-flips to the first algorithm, then passes
the remaining coin flips to the second function, and returns the unused coin-flips from both
steps.\<close>

definition bind_rai :: "'a random_alg_int \<Rightarrow> ('a \<Rightarrow> 'b random_alg_int) \<Rightarrow> 'b random_alg_int"
  where "bind_rai m f bs =
    do {
      (r, bs') \<leftarrow> m bs;
      f r bs'
    }"

adhoc_overloading Monad_Syntax.bind bind_rai


text \<open>The @{term "coin_rai"} combinator consumes one coin-flip and return it as the result, while the
tail of the coin flips are returned as unused.\<close>

definition coin_rai :: "bool random_alg_int"
  where "coin_rai bs = Some (chd bs, ctl bs)"

text \<open>This representation is similar to the model proposed by Hurd~\cite{hurd2003formal}
\footnote{Although we were not aware of the technical report, when initially considering this
representation.}. It is also closely related to the construction of parser monads in functional
languages~\cite{hutton1998}.

We also had following alternatives considered, with various advantages and drawbacks:

\begin{itemize}
\item \emph{Returning the count of used coin flips:} Instead of returning a suffix of the input
stream a randomized algorithm could also return the number of used coin flips, which then would
allow the definition of the bind function, in a way that performs the appropriate shift in the
stream according to the returned number. An advantage of this model, is that it makes the number
of used coin-flips immediately available. (As we will see below, this is still possible
even in the formalized model, albeit with some more work.) The main disadvantage of this model is
that in scenarios, where the coin-flips cannot be computed in a random-access way, it leads to
performance degradation. Indeed it is easy to construct example algorithms, which incur
asymptotically quadratic slow-down compared to the formalized model.
\item \emph{Trees of coin-flips:} Another model we were considering is to require an infinite tree
of coin-flips as input instead of a stream. Here the idea is that each bind operation would pass
the left sub-tree to the first algorithm and the right sub-tree to the second algorithm. This
model has the dis-advantage that the resulting `'monad'', does not fulfill the associativity law.
Moreover many PRG's are designed and tested in the streaming sense, and there is not a lot of
research into the performance of PRGs with tree structured output. (A related idea was to still
use a stream as input, and split it into two sub-streams for example by the parity of the stream
position. This alternative also suffers from the lack of associativity problem and may lead to
a lot of unused coin flips.)
\end{itemize}

Another reason for using the formalized representation is compatibility with
linear types~\cite{bernardy2018}, if support for them are introduced in Isabelle in future.\<close>

text \<open>Monad laws:\<close>

lemma return_bind_rai: "bind_rai (return_rai x) g = g x"
  unfolding bind_rai_def return_rai_def by simp

lemma bind_rai_assoc: "bind_rai (bind_rai f g) h = bind_rai f (\<lambda>x. bind_rai (g x) h)"
  unfolding bind_rai_def by (simp add:case_prod_beta')

lemma bind_return_rai: "bind_rai m return_rai = m"
  unfolding bind_rai_def return_rai_def by simp

definition wf_on_prefix :: "'a random_alg_int \<Rightarrow> bool list \<Rightarrow> 'a \<Rightarrow> bool" where
  "wf_on_prefix f p r = (\<forall>cs. f (cshift p cs) = Some (r,cs))"

definition wf_random :: "'a random_alg_int \<Rightarrow> bool" where
  "wf_random f \<longleftrightarrow> (\<forall>bs.
      case f bs of
        None \<Rightarrow> True |
        Some (r,bs') \<Rightarrow> (\<exists>p. cprefix p bs \<and> wf_on_prefix f p r))"

definition range_rm :: "'a random_alg_int \<Rightarrow> 'a set"
  where "range_rm f = Some -` (range (map_option fst \<circ> f))"

lemma in_range_rmI:
  assumes "r bs = Some (y, n)"
  shows   "y \<in> range_rm r"
proof -
  have "Some (y, n) \<in> range r"
    using assms[symmetric] by auto
  thus ?thesis
    unfolding range_rm_def using fun.set_map by force
qed

definition distr_rai :: "'a random_alg_int \<Rightarrow> 'a option measure"
  where "distr_rai f = distr \<B> \<D> (map_option fst \<circ> f)"

lemma wf_randomI:
  assumes "\<And>bs. f bs \<noteq> None \<Longrightarrow> (\<exists>p r. cprefix p bs \<and> wf_on_prefix f p r)"
  shows "wf_random f"
proof -
  have "\<exists>p. cprefix p bs \<and> wf_on_prefix f p r" if 0:"f bs = Some (r, bs')"  for bs r bs'
  proof -
    obtain p r' where 1:"cprefix p bs" and 2:"wf_on_prefix f p r'"
      using assms 0 by force
    have "f bs = f (cshift p (cdrop (length p) bs))"
      using 1 unfolding cprefix_def by (metis ctake_cdrop)
    also have "... = Some (r', cdrop (length p) bs)"
      using 2 unfolding wf_on_prefix_def by auto
    finally have "f bs = Some (r', cdrop (length p) bs)"
      by simp
    hence "r = r'" using 0 by simp
    thus ?thesis using 1 2 by auto
  qed
  thus ?thesis
    unfolding wf_random_def by (auto split:option.split)
qed

lemma wf_on_prefix_bindI:
  assumes "wf_on_prefix m p r"
  assumes "wf_on_prefix (f r) q s"
  shows "wf_on_prefix (m \<bind> f) (p@q) s"
proof -
  have "(m \<bind> f) (cshift (p@q) cs) = Some (s, cs)" for cs
  proof -
    have "(m \<bind> f) (cshift (p@q) cs) = (m \<bind> f) (cshift p (cshift q cs))"
      by simp
    also have "... = (f r) (cshift q cs)"
      using assms unfolding wf_on_prefix_def bind_rai_def by simp
    also have "... = Some (s,cs)"
      using assms unfolding wf_on_prefix_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding wf_on_prefix_def by simp
qed

lemma wf_bind:
  assumes "wf_random m"
  assumes "\<And>x. x \<in> range_rm m \<Longrightarrow> wf_random (f x)"
  shows "wf_random (m \<bind> f)"
proof (rule wf_randomI)
  fix bs
  assume "(m \<bind> f) bs \<noteq> None"
  then obtain x bs' y bs'' where 1: "m bs = Some (x,bs')" and 2:"f x bs' = Some (y, bs'')"
    unfolding bind_rai_def by (cases "m bs") auto
  hence wf: "wf_random (f x)"
    by (intro assms(2) in_range_rmI) auto
  obtain p where 5:"wf_on_prefix m p x" and 3:"cprefix p bs"
    using assms(1) 1 unfolding wf_random_def by (auto split:option.split_asm)
  have 4:"bs = cshift p (cdrop (length p) bs)"
    using 3 unfolding cprefix_def by (metis ctake_cdrop)
  hence "m bs = Some (x, cdrop (length p) bs)"
    using 5 unfolding wf_on_prefix_def by metis
  hence "bs' = cdrop (length p) bs"
    using 1 by auto
  hence 6:"bs = cshift p bs'"
    using 4 by auto

  obtain q where 7:"wf_on_prefix (f x) q y" and 8:"cprefix q bs'"
    using wf 2 unfolding wf_random_def by (auto split:option.split_asm)

  have "cprefix (p@q) bs"
    unfolding 6 using 8 unfolding cprefix_def by auto

  moreover have "wf_on_prefix (m \<bind> f) (p@q) y"
    by (intro wf_on_prefix_bindI[OF 5] 7)
  ultimately show "\<exists>p r. cprefix p bs \<and> wf_on_prefix (m \<bind> f) p r"
    by auto
qed

lemma wf_return:
  "wf_random (return_rai x)"
proof (rule wf_randomI)
  fix bs assume "return_rai x bs \<noteq> None"
  have "wf_on_prefix (return_rai x) [] x"
    unfolding wf_on_prefix_def return_rai_def by auto
  moreover have "cprefix [] bs"
    unfolding cprefix_def by auto
  ultimately show "\<exists>p r. cprefix p bs \<and> wf_on_prefix (return_rai x) p r"
    by auto
qed

lemma wf_coin:
  "wf_random (coin_rai)"
proof (rule wf_randomI)
  fix bs assume "coin_rai bs \<noteq> None"
  have "wf_on_prefix coin_rai [chd bs] (chd bs)"
    unfolding wf_on_prefix_def coin_rai_def by auto
  moreover have "cprefix [chd bs] bs"
    unfolding cprefix_def by auto
  ultimately show "\<exists>p r. cprefix p bs \<and> wf_on_prefix coin_rai p r"
    by auto
qed

definition ptree_rm :: "'a random_alg_int \<Rightarrow> bool list set"
  where "ptree_rm f = {p. \<exists>r. wf_on_prefix f p r}"

definition eval_rm :: "'a random_alg_int \<Rightarrow> bool list \<Rightarrow> 'a" where
  "eval_rm f p = fst (the (f (cshift p (cconst False))))"

lemma eval_rmD:
  assumes "wf_on_prefix f p r"
  shows "eval_rm f p = r"
  using assms unfolding wf_on_prefix_def eval_rm_def by auto

lemma wf_on_prefixD:
  assumes "wf_on_prefix f p r"
  assumes "cprefix p bs"
  shows "f bs = Some (eval_rm f p, cdrop (length p) bs)"
proof -
  have 0:"bs = cshift p (cdrop (length p) bs)"
    using assms(2) unfolding cprefix_def by (metis ctake_cdrop)
  hence "f bs = Some (r, cdrop (length p) bs)"
    using assms(1) 0 unfolding wf_on_prefix_def by metis
  thus ?thesis
    using eval_rmD[OF assms(1)] by simp
qed

lemma prefixes_parallel_helper:
  assumes "p \<in> ptree_rm f"
  assumes "q \<in> ptree_rm f"
  assumes "prefix p q"
  shows "p = q"
proof -
  obtain h where 0:"q = p@h"
    using assms(3) prefixE that by auto
  obtain r1 where 1:"wf_on_prefix f p r1"
    using assms(1) unfolding ptree_rm_def by auto
  obtain r2 where 2:"wf_on_prefix f q r2"
    using assms(2) unfolding ptree_rm_def by auto
  have "x = cshift h x" for x :: "coin_stream"
  proof -
    have "Some (r2, x) = f (cshift q x)"
      using 2 unfolding wf_on_prefix_def by auto
    also have "... = f (cshift p (cshift h x))"
      using 0 by auto
    also have "... = Some (r1, cshift h x)"
      using 1 unfolding wf_on_prefix_def by auto
    finally show "x = cshift h x"
      by simp
  qed
  hence "h = []"
    using empty_if_shift_idem by simp
  thus ?thesis using 0 by simp
qed

lemma prefixes_parallel:
  assumes "p \<in> ptree_rm f"
  assumes "q \<in> ptree_rm f"
  shows "p = q \<or> p \<parallel> q"
  using prefixes_parallel_helper assms by blast

lemma prefixes_singleton:
  assumes "p \<in> {p. p \<in> ptree_rm f \<and> cprefix p bs}"
  shows "{p \<in> ptree_rm f. cprefix p bs} = {p}"
proof
  have "q = p" if "q \<in> ptree_rm f" "cprefix q bs" for q
    using same_prefix_not_parallel assms prefixes_parallel that by blast
  thus "{p \<in> ptree_rm f. cprefix p bs} \<subseteq> {p}"
    by (intro subsetI) simp
next
  show "{p} \<subseteq> {p \<in> ptree_rm f. cprefix p bs}"
    using assms by auto
qed

lemma prefixes_at_most_one:
  "at_most_one {p \<in> ptree_rm f. cprefix p x}"
  unfolding at_most_one_def using same_prefix_not_parallel prefixes_parallel by blast

definition "consumed_prefix f bs = the_elem_opt {p \<in> ptree_rm f. cprefix p bs}"

lemma wf_random_alt:
  assumes "wf_random f"
  shows "f bs = map_option (\<lambda>p. (eval_rm f p, cdrop (length p) bs)) (consumed_prefix f bs)"
proof (cases "f bs")
  case None
  have "False" if p_in: "p \<in> ptree_rm f" and p_pref: "cprefix p bs" for p
  proof -
    obtain r where wf: "wf_on_prefix f p r" using that p_in unfolding ptree_rm_def by auto
    have "bs = cshift p (cdrop (length p) bs)"
      using p_pref unfolding cprefix_def by (metis ctake_cdrop)
    hence "f bs \<noteq> None"
      using wf unfolding wf_on_prefix_def
      by (metis option.simps(3))
    thus "False" using  None by simp
  qed
  hence 0:"{p \<in> ptree_rm f. cprefix p bs} = {}"
    by auto
  show ?thesis unfolding 0 None consumed_prefix_def by simp
next
  case (Some a)
  moreover obtain r cs where "a = (r, cs)" by (cases a) auto
  ultimately have "f bs = Some (r, cs)" by simp
  hence "\<exists>p. cprefix p bs \<and> wf_on_prefix f p r"
    using assms(1) unfolding wf_random_def by (auto split:option.split_asm)
  then obtain p where sp: "cprefix p bs" and wf: "wf_on_prefix f p r"
    by auto
  hence "p \<in> {p \<in> ptree_rm f. cprefix p bs}"
    unfolding ptree_rm_def by auto
  hence 0:"{p \<in> ptree_rm f. cprefix p bs} = {p}"
    using prefixes_singleton by auto
  show ?thesis unfolding 0 wf_on_prefixD[OF wf sp] consumed_prefix_def by simp
qed

lemma range_rm_alt:
  assumes "wf_random f"
  shows "range_rm f = eval_rm f ` ptree_rm f" (is "?L = ?R")
proof -
  have 0:"cprefix p (cshift p (cconst False))" for p
    unfolding cprefix_def by auto
  have "?L = {x. \<exists>bs. map_option (eval_rm f) (consumed_prefix f bs) = Some x}"
    unfolding range_rm_def comp_def by (subst wf_random_alt[OF assms])
      (simp add:map_option.compositionality comp_def vimage_def image_iff eq_commute)
  also have "... = {x. \<exists>p bs. x = eval_rm f p \<and> consumed_prefix f bs = Some p}"
    unfolding map_option_eq_Some
    by (intro Collect_cong) metis
  also have "... = {x. \<exists>p. p \<in>ptree_rm f \<and> x = eval_rm f p}"
    unfolding consumed_prefix_def the_elem_opt_Some_iff[OF prefixes_at_most_one]
    using 0 prefixes_singleton
    by (intro Collect_cong) blast
  also have "... = ?R"
    by auto
  finally show ?thesis
    by simp
qed

lemma consumed_prefix_some_iff:
  "consumed_prefix f bs = Some p \<longleftrightarrow> (p \<in> ptree_rm f \<and> cprefix p bs)"
proof -
  have "p \<in> ptree_rm f \<Longrightarrow> cprefix p bs \<Longrightarrow> x \<in> ptree_rm f \<Longrightarrow> cprefix x bs \<Longrightarrow> x = p" for x
    using same_prefix_not_parallel prefixes_parallel by blast
  thus ?thesis
    unfolding consumed_prefix_def the_elem_opt_Some_iff[OF prefixes_at_most_one]
    by auto
qed

definition consumed_bits where
  "consumed_bits f bs = map_option length (consumed_prefix f bs)"

definition used_bits_distr :: "'a random_alg_int \<Rightarrow> nat option measure"
  where "used_bits_distr f = distr \<B> \<D> (consumed_bits f)"

lemma wf_random_alt2:
  assumes "wf_random f"
  shows "f bs = map_option (\<lambda>n. (eval_rm f (ctake n bs), cdrop n bs)) (consumed_bits f bs)"
    (is "?L = ?R")
proof -
  have 0:"cprefix x bs" if "consumed_prefix f bs = Some x" for x
    using that the_elem_opt_Some_iff[OF prefixes_at_most_one] unfolding consumed_prefix_def by auto
  have "?L = map_option (\<lambda>p. (eval_rm f p, cdrop (length p) bs)) (consumed_prefix f bs)"
    by (subst wf_random_alt[OF assms])  simp
  also have "... = ?R"
    using 0 unfolding consumed_bits_def map_option.compositionality comp_def cprefix_def
    by (cases "consumed_prefix f bs") auto
  finally show ?thesis by simp
qed

lemma consumed_prefix_none_iff:
  assumes "wf_random f"
  shows "f bs = None \<longleftrightarrow> consumed_prefix f bs = None"
    using wf_random_alt[OF assms] by (simp)

lemma consumed_bits_inf_iff:
  assumes "wf_random f"
  shows "f bs = None \<longleftrightarrow> consumed_bits f bs = None"
    using wf_random_alt2[OF assms] by (simp)

lemma consumed_bits_enat_iff:
  "consumed_bits f bs = Some n \<longleftrightarrow> ctake n bs \<in> ptree_rm f" (is "?L = ?R")
proof
  assume "consumed_bits f bs = Some n"
  then obtain p where "the_elem_opt {p \<in> ptree_rm f. cprefix p bs} = Some p" and 0: "length p = n"
    unfolding consumed_bits_def consumed_prefix_def by (auto split:option.split_asm)
  hence "p \<in> ptree_rm f" "cprefix p bs"
    unfolding the_elem_opt_Some_iff[OF prefixes_at_most_one] by auto
  thus "ctake n bs \<in> ptree_rm f"
    using 0 unfolding cprefix_def by auto
next
  assume "ctake n bs \<in> ptree_rm f"
  hence "ctake n bs \<in> {p \<in> ptree_rm f. cprefix p bs}"
    unfolding cprefix_def by auto
  hence "{p \<in> ptree_rm f. cprefix p bs} = {ctake n bs}"
    using prefixes_singleton by auto
  thus "consumed_bits f bs = Some n"
    unfolding consumed_bits_def consumed_prefix_def by simp
qed

lemma consumed_bits_measurable: "consumed_bits f \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have 0: "consumed_bits f -` {x} \<inter> space \<B> \<in> sets \<B>" (is "?L \<in> _")
    if x_ne_inf: "x \<noteq> None" for x
  proof -
    obtain n where x_def: "x = Some n"
      using x_ne_inf that by auto

    have "?L = {bs. \<exists>z. consumed_prefix f bs = Some z \<and> length z = n}"
      unfolding consumed_bits_def vimage_def space_coin_space x_def by simp
    also have "... = {bs. \<exists>p. {p \<in> ptree_rm f. cprefix p bs} = {p} \<and> length p = n}"
      unfolding consumed_prefix_def x_def the_elem_opt_Some_iff[OF prefixes_at_most_one] by simp
    also have "... = {bs. \<exists>p. cprefix p bs \<and> length p = n \<and> p \<in> ptree_rm f}"
      using prefixes_singleton by (intro Collect_cong ex_cong1) auto
    also have "... = {bs. ctake n bs \<in> ptree_rm f}"
      unfolding cprefix_def by (intro Collect_cong) (metis length_ctake)
    also have "... \<in> sets \<B>"
      by (intro measurable_sets_coin_space[OF ctake_measurable]) simp
    finally show ?thesis
      by simp
  qed

  thus ?thesis
    by (intro measurable_sigma_sets_with_exception[where d="None"])
qed

lemma R_sets:
  assumes wf:"wf_random f"
  shows "{bs. f bs = None} \<in> sets \<B>" "{bs. f bs \<noteq> None} \<in> sets \<B>"
proof -
  show 0: "{bs. f bs = None} \<in> sets \<B>"
    unfolding consumed_bits_inf_iff[OF wf]
    by (intro measurable_sets_coin_space[OF consumed_bits_measurable]) simp
  have "{bs. f bs \<noteq> None} = space \<B> - {bs. f bs = None}"
    unfolding space_coin_space by (simp add:set_eq_iff del:not_None_eq)
  also have "... \<in> sets \<B>"
    by (intro sets.compl_sets 0)
  finally show "{bs. f bs \<noteq> None} \<in> sets \<B>"
    by simp
qed

lemma countable_range:
  assumes wf:"wf_random f"
  shows "countable (range_rm f)"
proof -
  have "countable (eval_rm f ` UNIV)"
    by (intro countable_image) simp
  moreover have "range_rm f \<subseteq> eval_rm f ` UNIV"
    unfolding range_rm_alt[OF wf] by auto
  ultimately show ?thesis using countable_subset by blast
qed

lemma consumed_prefix_continuous:
  "continuous_map euclidean option_ud (consumed_prefix f)"
proof (intro contionuos_into_option_udI)
  fix x :: "bool list"

  have "open ((consumed_prefix f) -` {Some x})" (is "open ?T")
  proof (cases "x \<in> ptree_rm f")
    case True
    hence 0:"?T = {bs. cprefix x bs}"
      unfolding vimage_def comp_def by (simp add:consumed_prefix_some_iff)
    show ?thesis
      unfolding 0 by (intro coin_steam_open)
  next
    case False
    hence "?T = {}"
      unfolding vimage_def comp_def by (simp add:consumed_prefix_some_iff)
    thus ?thesis
      by simp
  qed
  thus "openin euclidean ((consumed_prefix f) -` {Some x} \<inter> topspace euclidean)"
    by simp
qed

text \<open>Randomized algorithms are continuous with respect to the product topology on the domain
and the upper topology on the range.\<close>

lemma f_continuous:
  assumes wf:"wf_random f"
  shows "continuous_map euclidean option_ud (map_option fst \<circ> f)"
proof -
  have 0: "map_option fst \<circ> (\<lambda>bs. f bs) =
    map_option (eval_rm f) \<circ> (consumed_prefix f)"
    by (subst wf_random_alt[OF wf]) (simp add:map_option.compositionality comp_def)

  show ?thesis unfolding 0
    by (intro continuous_map_compose[OF consumed_prefix_continuous] map_option_continuous)
qed

lemma none_measure_subprob_algebra:
  "return \<D> None \<in> space (subprob_algebra \<D>)"
  by (metis measure_subprob return_pmf.rep_eq)

context
  fixes f :: "'a random_alg_int"
  fixes R
  assumes wf: "wf_random f"
  defines "R \<equiv> restrict_space \<B> {bs. f bs \<noteq> None}"
begin

lemma the_f_measurable: "the \<circ> f \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
proof -
  define h where "h = the \<circ> consumed_bits f"
  define g where "g bs = (ctake (h bs) bs, cdrop (h bs) bs)" for bs

  have "consumed_bits f bs \<noteq> None" if "bs \<in> space R" for bs
    using that consumed_bits_inf_iff[OF wf] unfolding R_def space_restrict_space space_coin_space
    by (simp del:not_infinity_eq not_None_eq)

  hence 0:"the (f bs) = map_prod (eval_rm f) id (g bs)" if "bs \<in> space R" for bs
    unfolding g_def h_def using that
    by (subst wf_random_alt2[OF wf]) (cases "consumed_bits f bs", auto simp del: not_None_eq)

  have 1:"h \<in> R \<rightarrow>\<^sub>M \<D>"
    unfolding R_def h_def
    by (intro measurable_restrict_space1 measurable_comp[OF consumed_bits_measurable]) simp

  have "ctake k \<in> R \<rightarrow>\<^sub>M \<D>" for k
    unfolding R_def  by (intro measurable_restrict_space1 ctake_measurable)
  moreover have "cdrop k \<in> R \<rightarrow>\<^sub>M \<B>" for k
    unfolding R_def by (intro measurable_restrict_space1 cdrop_measurable)
  ultimately have "g \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    unfolding g_def
    by (intro measurable_Pair measurable_Pair_compose_split[OF  _ 1 measurable_id]) simp_all
  hence "(map_prod (eval_rm f) id \<circ> g) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    by (intro measurable_comp[where N="\<D> \<Otimes>\<^sub>M \<B>"] map_prod_measurable) auto
  moreover have "(the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B> \<longleftrightarrow> (map_prod  (eval_rm f) id \<circ> g) \<in> R \<rightarrow>\<^sub>M \<D> \<Otimes>\<^sub>M \<B>"
    using 0 by (intro measurable_cong) (simp add:comp_def)
  ultimately show ?thesis
    by auto
qed

lemma distr_rai_measurable: "map_option fst \<circ> f \<in> \<B> \<rightarrow>\<^sub>M \<D>"
proof -
  have 0:"countable {{bs. f bs \<noteq> None}, {bs. f bs = None}}"
    by simp

  have 1: "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>"
    if "\<Omega> \<in> {{bs. f bs \<noteq> None}, {bs. f bs = None}}" for \<Omega>
  proof (cases "\<Omega> = {bs. f bs \<noteq> None}")
    case True
    have "Some \<circ> fst \<circ> (the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D>"
      by (intro measurable_comp[OF the_f_measurable]) auto
    hence "map_option fst \<circ> f \<in> R \<rightarrow>\<^sub>M \<D>"
      unfolding R_def by (subst measurable_cong[where g="Some \<circ> fst \<circ> (the \<circ> f)"])
        (auto simp add: space_restrict_space space_coin_space)
    thus "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>"
      unfolding R_def True using R_sets[OF wf] by auto
  next
    case False
    hence 2:"\<Omega> = {bs. f bs = None}"
      using that by simp

    have "map_option fst \<circ> f \<in> restrict_space \<B> {bs. f bs = None} \<rightarrow>\<^sub>M \<D>"
      by (subst measurable_cong[where g="\<lambda>_. None"])
       (simp_all add:space_restrict_space)

    thus "\<Omega> \<in> sets \<B> \<and> map_option fst \<circ> f \<in> restrict_space \<B> \<Omega> \<rightarrow>\<^sub>M \<D>"
      unfolding 2 using R_sets[OF wf] by auto
  qed

  have 3: "space \<B> \<subseteq> \<Union> {{bs. f bs \<noteq> None}, {bs. f bs = None}}"
    unfolding space_coin_space by auto

  show ?thesis
    by (rule measurable_piecewise_restrict[OF 0]) (use 1 3 space_coin_space in \<open>auto\<close>)
qed

lemma distr_rai_subprob_space:
  "distr_rai f \<in> space (subprob_algebra \<D>)"
proof -
  have "prob_space (distr_rai f)"
    unfolding distr_rai_def using distr_rai_measurable
    by (intro coin_space.prob_space_distr ) auto
  moreover have "sets (distr_rai f) = \<D>"
    unfolding distr_rai_def by simp
  ultimately show ?thesis
    unfolding space_subprob_algebra using prob_space_imp_subprob_space
    by auto
qed

lemma fst_the_f_measurable: "fst \<circ> the \<circ> f \<in> R \<rightarrow>\<^sub>M \<D>"
proof -
  have "fst \<circ> (the \<circ> f) \<in> R \<rightarrow>\<^sub>M \<D>"
    by (intro measurable_comp[OF the_f_measurable]) simp
  thus ?thesis by (simp add:comp_def)
qed

lemma prob_space_distr_rai:
  "prob_space (distr_rai f)"
  unfolding distr_rai_def by (intro coin_space.prob_space_distr distr_rai_measurable)

text \<open>This is the central correctness property for the monad. The returned stream of coins
is independent of the result of the randomized algorithm.\<close>

lemma remainder_indep:
  "distr R (\<D> \<Otimes>\<^sub>M \<B>) (the \<circ> f) = distr R \<D> (fst \<circ> the \<circ> f) \<Otimes>\<^sub>M \<B>"
proof -
  define C where "C k = consumed_bits f -` {Some k}" for k

  have 2: "(\<exists>k. x \<in> C k) \<longleftrightarrow> f x \<noteq> None" for x
    using consumed_bits_inf_iff[OF wf] unfolding C_def
    by auto

  hence 5: "C k \<subseteq> space R" for k
    unfolding R_def space_restrict_space space_coin_space
    by auto

  have 1:"{bs. f bs \<noteq> None} \<inter> space \<B> \<in> sets \<B>"
    using R_sets[OF wf] by simp

  have 6: "C k \<in> sets \<B>" for k
    unfolding C_def vimage_def
    by (intro measurable_sets_coin_space[OF consumed_bits_measurable]) simp

  have 8: "x \<in> C k \<longleftrightarrow> ctake k x \<in> ptree_rm f" for x k
    unfolding C_def using consumed_bits_enat_iff by auto

  have 7: "the (f (cshift (ctake k x) y)) = (fst (the (f x)), y)" if "x \<in> C k" for x y k
  proof -
    have "cshift (ctake k x) y \<in> C k"
       using that 8 by simp
    hence "the (f (cshift (ctake k x) y)) = (eval_rm f (ctake k x), y)"
      using wf_random_alt2[OF wf] unfolding C_def by simp
    also have "... = (fst (the (f x)), y)"
      using that wf_random_alt2[OF wf] unfolding C_def by simp
    finally show ?thesis by simp
  qed

  have C_disj: "disjoint_family C"
    unfolding disjoint_family_on_def C_def by auto

  have 0:
    "emeasure (distr R (\<D> \<Otimes>\<^sub>M \<B>) (the \<circ> f)) (A \<times> B) =
     emeasure (distr R \<D> (fst \<circ> the \<circ> f)) A * emeasure \<B> B"
    (is "?L = ?R") if "A \<in> sets \<D>" "B \<in> sets \<B>" for A B
  proof -
    have 3: "{bs. fst (the (f bs)) \<in> A \<and> bs \<in> C k} \<in> sets \<B>" (is "?L1 \<in> _") for k
    proof -
      have "?L1 = (fst \<circ> the \<circ> f) -` A \<inter> space (restrict_space R (C k))"
        using 5 unfolding vimage_def space_restrict_space R_def space_coin_space by auto
      also have "... \<in> sets (restrict_space R (C k))"
        by (intro measurable_sets[OF _ that(1)] measurable_restrict_space1 fst_the_f_measurable)
      also have "... = sets (restrict_space \<B> (C k))"
        using 5 unfolding R_def sets_restrict_restrict_space space_restrict_space space_coin_space
        by (intro arg_cong2[where f="restrict_space"] arg_cong[where f="sets"] refl) auto
      finally have "?L1 \<in> sets (restrict_space \<B> (C k))"
        by simp
      thus "?L1 \<in> sets \<B>"
        using 6 space_coin_space sets_restrict_space_iff[where M="\<B>" and \<Omega>="C k"] by auto
    qed

    have 4: "{bs. the (f bs) \<in> A \<times> B \<and> bs \<in> C k} \<in> sets \<B>" (is "?L1 \<in> _") for k
    proof -
      have "?L1 = (the \<circ> f) -` (A \<times> B) \<inter> space (restrict_space R (C k))"
        using 5 unfolding vimage_def space_restrict_space R_def space_coin_space by auto
      also have "... \<in> sets (restrict_space R (C k))"
        using that by (intro measurable_sets[where A="\<D> \<Otimes>\<^sub>M \<B>"] measurable_restrict_space1
                       the_f_measurable) auto
      also have "... = sets (restrict_space \<B> (C k))"
        using 5 unfolding R_def sets_restrict_restrict_space space_restrict_space space_coin_space
        by (intro arg_cong2[where f="restrict_space"] arg_cong[where f="sets"] refl) auto
      finally have "?L1 \<in> sets (restrict_space \<B> (C k))"
        by simp
      thus "?L1 \<in> sets \<B>"
        using 6 space_coin_space sets_restrict_space_iff[where M="\<B>" and \<Omega>="C k"] by auto
    qed

    have "?L = emeasure R ((the \<circ> f) -` (A \<times> B) \<inter> space R)"
      using that the_f_measurable by (intro emeasure_distr) auto
    also have "... = emeasure R {x. the (f x) \<in> A \<times> B \<and> f x \<noteq> None}"
      unfolding vimage_def R_def Int_def
      by (simp add:space_restrict_space space_coin_space)
    also have "... = emeasure \<B> {x. the (f x) \<in> A \<times> B \<and> (\<exists>k. x \<in> C k)}"
      unfolding R_def 2 using 1 by (intro emeasure_restrict_space) auto
    also have "... = emeasure \<B> (\<Union>k. {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      by (intro arg_cong2[where f="emeasure"]) auto
    also have "... = (\<Sum>k. emeasure \<B> {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      using 4 C_disj
      by (intro suminf_emeasure[symmetric] subsetI) (auto simp:disjoint_family_on_def)
    also have "... = (\<Sum>k. emeasure (distr (\<B> \<Otimes>\<^sub>M \<B>) \<B> (\<lambda>(x,y). (cshift (ctake k x) y)))
      {x. the (f x) \<in> A \<times> B \<and> x \<in> C k})"
      by (intro suminf_cong arg_cong2[where f="emeasure"] branch_coin_space(2)[symmetric] refl)
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>)
      {x. the (f (cshift (ctake k (fst x)) (snd x))) \<in> A \<times> B \<and> (cshift (ctake k (fst x)) (snd x)) \<in> C k})"
      using branch_coin_space(1) 4 by (subst emeasure_distr)
        (simp_all add:case_prod_beta Int_def space_pair_measure space_coin_space)
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>)
      {x. the (f (cshift (ctake k (fst x)) (snd x))) \<in> A \<times> B \<and> fst x \<in> C k})"
      using 8 by (intro suminf_cong arg_cong2[where f="emeasure"] refl Collect_cong) auto
    also have "... = (\<Sum>k. emeasure (\<B> \<Otimes>\<^sub>M \<B>) ({x. fst (the (f x)) \<in> A \<and> x \<in> C k} \<times> B))"
      using 7 by (intro suminf_cong arg_cong2[where f="emeasure"] refl)
        (auto simp add:mem_Times_iff set_eq_iff)
    also have "... = (\<Sum>k. emeasure \<B> {x. fst (the (f x)) \<in> A \<and> x \<in> C k} * emeasure \<B> B)"
      using 3 that(2)
      by (intro suminf_cong coin_space.emeasure_pair_measure_Times) auto
    also have "... = (\<Sum>k. emeasure \<B> {x. fst (the (f x)) \<in> A \<and> x \<in> C k}) * emeasure \<B> B"
      by simp
    also have "... = emeasure \<B> (\<Union>k. {x. fst (the (f x)) \<in> A \<and> x \<in> C k}) * emeasure \<B> B"
      using 3 C_disj
      by (intro arg_cong2[where f="(*)"] suminf_emeasure refl image_subsetI)
       (auto simp add:disjoint_family_on_def)
    also have "... = emeasure \<B> {x. fst (the (f x)) \<in> A \<and> (\<exists>k. x \<in> C k)} * emeasure \<B> B"
      by (intro arg_cong2[where f="emeasure"] arg_cong2[where f="(*)"]) auto
    also have "... = emeasure R {x. fst (the (f x)) \<in> A \<and> f x \<noteq> None} * emeasure \<B> B"
      unfolding R_def 2 using 1
      by (intro arg_cong2[where f="(*)"] emeasure_restrict_space[symmetric] subsetI) simp_all
    also have "... = emeasure R ((fst \<circ> the \<circ> f) -` A \<inter> space R) * emeasure \<B> B"
      unfolding vimage_def R_def Int_def by (simp add:space_restrict_space space_coin_space)
    also have "... = ?R"
      using that
      by (intro arg_cong2[where f="(*)"] emeasure_distr[symmetric] fst_the_f_measurable) auto
    finally show ?thesis by simp
  qed

  have "finite_measure R"
    using 1 unfolding R_def space_coin_space
    by (intro finite_measure_restrict_space) simp_all
  hence "finite_measure (distr R \<D> (fst \<circ> the \<circ> f))"
    by (intro finite_measure.finite_measure_distr fst_the_f_measurable)
  hence 1:"sigma_finite_measure (distr R \<D> (fst \<circ> the \<circ> f))"
    unfolding finite_measure_def by auto

  have 2:"sigma_finite_measure \<B>"
    using prob_space_imp_sigma_finite[OF coin_space.prob_space_axioms] by simp

  show ?thesis
    using 0 by (intro pair_measure_eqI[symmetric] 1 2) (simp_all add:sets_pair_measure)
qed

end

lemma distr_rai_bind:
  assumes wf_m: "wf_random m"
  assumes wf_f: "\<And>x. x \<in> range_rm m \<Longrightarrow> wf_random (f x)"
  shows "distr_rai (m \<bind> f) = distr_rai m \<bind>
    (\<lambda>x. if x \<in> Some ` range_rm m then distr_rai (f (the x)) else return \<D> None)"
    (is "?L = ?RHS")
proof (rule measure_eqI)
  have "sets ?L = UNIV"
    unfolding distr_rai_def by simp
  also have "... = sets ?RHS"
    unfolding distr_rai_def by (subst sets_bind[where N="\<D>"])
      (simp_all add:option.case_distrib option.case_eq_if)
  finally show "sets ?L = sets ?RHS" by simp
next
  let ?m = "distr_rai"
  let ?H = "count_space (range_rm m)"
  let ?R = "restrict_space \<B> {bs. m bs \<noteq> None}"

  fix A assume "A \<in> sets (distr_rai (m \<bind> f))"
  define N where "N = {x. m x \<noteq> None}"

  have N_meas: "N \<in> sets coin_space"
    unfolding N_def using R_sets[OF wf_m] by simp

  hence N_meas': "-N \<in> sets coin_space"
    unfolding Compl_eq_Diff_UNIV using space_coin_space by (metis sets.compl_sets)

  have wf_bind: "wf_random (m \<bind> f)"
    using wf_bind[OF assms] by auto

  have 0: "(map_option fst \<circ> (m \<bind> f)) \<in> coin_space \<rightarrow>\<^sub>M \<D>"
    using distr_rai_measurable[OF wf_bind] by auto
  have 1: "(map_option fst \<circ> (m \<bind> f)) -` A \<in> sets \<B>"
    unfolding vimage_def by (intro measurable_sets_coin_space[OF 0]) simp

  have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} =
    (map_option fst \<circ> case_prod f) -` A \<inter> space (?H \<Otimes>\<^sub>M \<B>)"
    unfolding vimage_def space_pair_measure space_coin_space by auto
  also have "... \<in> sets (?H \<Otimes>\<^sub>M \<B>)"
    using distr_rai_measurable[OF wf_f]
    by (intro measurable_sets[where A="\<D>"] measurable_pair_measure_countable1 countable_range wf_m)
      (simp_all add:comp_def)
  also have "... = sets (restrict_space \<D> (range_rm m) \<Otimes>\<^sub>M \<B>)"
    unfolding restrict_count_space inf_top_right by simp
  also have "... = sets (restrict_space (\<D> \<Otimes>\<^sub>M \<B>) (range_rm m \<times> space coin_space))"
    by (subst coin_space.restrict_space_pair_lift) auto
  finally have "{(v, bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} \<in>
    sets (restrict_space (\<D> \<Otimes>\<^sub>M \<B>) (range_rm m \<times> UNIV))"
    unfolding space_coin_space by simp
  moreover have "range_rm m \<times> space coin_space \<in> sets (\<D> \<Otimes>\<^sub>M \<B>)"
    by (intro pair_measureI sets.top) auto
  ultimately have 2: "{(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in> range_rm m} \<in> sets (\<D> \<Otimes>\<^sub>M \<B>)"
    by (subst (asm) sets_restrict_space_iff) (auto simp: space_coin_space)

  have space_R: "space ?R = {x. m x \<noteq> None}"
    by (simp add:space_restrict_space space_coin_space)

  have 3: "distr_rai (f (the x)) \<in> space (subprob_algebra \<D>)"
    if "x \<in> Some ` range_rm m" for x
    using distr_rai_subprob_space[OF wf_f] that by fastforce

  have "(\<lambda>x. emeasure (distr_rai (f (fst (the (m x))))) A * indicator N x) =
    (\<lambda>x. emeasure (if m x \<noteq> None then distr_rai (f (fst (the (m x)))) else null_measure \<D>) A)"
    unfolding N_def by (intro ext) simp
  also have "... = (\<lambda>v. emeasure (if v\<in>Some`range_rm m then ?m (f (the v)) else null_measure \<D>) A)
    \<circ> (map_option fst \<circ> m)"
    unfolding comp_def by (intro ext arg_cong2[where f="emeasure"] refl if_cong)
      (auto intro:in_range_rmI simp add:vimage_def image_iff)
  also have "... \<in> borel_measurable coin_space"
    using 3 by (intro distr_rai_measurable[OF wf_m] measurable_comp[where N="\<D>"]
        measurable_emeasure_kernel[where N="\<D>"]) simp_all
  finally have 4:"(\<lambda>x. emeasure (distr_rai (f (fst (the (m x))))) A * indicator N x)
    \<in> coin_space \<rightarrow>\<^sub>M borel" by simp

  let ?N = "emeasure \<B> {bs. bs \<notin> N \<and> None \<in> A}"

  have "emeasure ?L A = emeasure \<B> ((map_option fst \<circ> (m \<bind> f)) -` A)"
    unfolding distr_rai_def using 0 by (subst emeasure_distr) (simp_all add:space_coin_space)
  also have "... =
    emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A \<inter> -N) + emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A \<inter> N)"
    using N_meas N_meas' 1
    by (subst emeasure_Un'[symmetric]) (simp_all add:Int_Un_distrib[symmetric])
  also have "... =
    emeasure \<B> ((map_option fst\<circ>(m\<bind>f))-`A\<inter> -N) + emeasure ?R ((map_option fst\<circ>(m\<bind>f))-`A\<inter> N)"
    using N_meas unfolding N_def
    by (intro arg_cong2[where f="(+)"] refl emeasure_restrict_space[symmetric]) simp_all
  also have "... =?N + emeasure ?R ((the \<circ> m) -`
    {(v, bs). map_option fst (f v bs) \<in> A \<and> v\<in> range_rm m} \<inter> space ?R)"
    unfolding bind_rai_def N_def space_R apfst_def
    by (intro arg_cong2[where f="(+)"] arg_cong2[where f="emeasure"])
     (simp_all add: set_eq_iff in_range_rmI split:option.split bind_splits)
  also have "... = ?N + emeasure (distr ?R (\<D>\<Otimes>\<^sub>M\<B>) (the \<circ> m))
    {(v,bs). map_option fst (f v bs)\<in>A \<and> v\<in> range_rm m}"
    using 2 by (intro arg_cong2[where f="(+)"] emeasure_distr[symmetric]
          the_f_measurable map_prod_measurable wf_m) simp_all
  also have "... = ?N + emeasure (distr ?R \<D> (fst \<circ> the \<circ> m) \<Otimes>\<^sub>M \<B>)
    {(v,bs). map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m}"
    unfolding N_def remainder_indep[OF wf_m] by simp
  also have "... =  ?N + \<integral>\<^sup>+ v. emeasure \<B>
    {bs. map_option fst (f v bs) \<in> A \<and> v \<in> range_rm m} \<partial>distr ?R \<D> (fst \<circ> (the \<circ> m))"
    using 2 by (subst coin_space.emeasure_pair_measure_alt) (simp_all add:vimage_def comp_assoc)
  also have "... =  ?N + \<integral>\<^sup>+ x. emeasure \<B>
    {bs. map_option fst (f ((fst \<circ> (the \<circ> m)) x) bs) \<in> A \<and> (fst \<circ> (the \<circ> m)) x \<in> range_rm m} \<partial>?R"
    using the_f_measurable[OF wf_m]
    by (intro arg_cong2[where f="(+)"] refl nn_integral_distr) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}. emeasure \<B>
    {bs. map_option fst (f (fst (the (m x))) bs) \<in> A \<and> fst (the (m x)) \<in> range_rm m} \<partial>\<B>)"
    using N_meas unfolding N_def using nn_integral_restrict_space
    by (subst nn_integral_restrict_space) simp_all
  also have "... = ?N + (\<integral>\<^sup>+x\<in>{bs. m bs \<noteq> None}.
    emeasure \<B> ((map_option fst \<circ> f (fst (the (m x)))) -` A \<inter> space \<B>) \<partial>\<B>)"
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl arg_cong2[where f="emeasure"])
     (auto intro:in_range_rmI simp:space_coin_space)
  also have "... = ?N + (\<integral>\<^sup>+x\<in>N. emeasure (distr_rai(f(fst(the(m x))))) A \<partial>\<B>)"
    unfolding distr_rai_def N_def
    by (intro arg_cong2[where f="(+)"] set_nn_integral_cong refl emeasure_distr[symmetric]
        distr_rai_measurable[OF wf_f]) (auto intro:in_range_rmI)
  also have "... = (\<integral>\<^sup>+x. (indicator {bs. bs \<notin> N \<and> None \<in> A}) x  \<partial>\<B>) +
    (\<integral>\<^sup>+x\<in>N. emeasure (distr_rai(f(fst(the(m x))))) A \<partial>\<B>)"
    using N_meas N_meas'
    by (intro arg_cong2[where f="(+)"] nn_integral_indicator[symmetric] refl)
     (cases "None \<in> A"; auto simp:Collect_neg_eq)
  also have "... = \<integral>\<^sup>+ x. indicator {bs. bs \<notin> N \<and> None \<in> A} x +
           emeasure (distr_rai (f (fst (the (m x))))) A * indicator N x \<partial>\<B>"
    using N_meas' N_meas by (intro nn_integral_add[symmetric] 4) simp
  also have "... =  \<integral>\<^sup>+ x. indicator (-N) x * indicator A None +
    indicator N x * emeasure (distr_rai (f (fst (the (m x))))) A \<partial>\<B>"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext refl arg_cong2[where f="(+)"])
      (simp_all split:split_indicator)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (case m x of None \<Rightarrow> return \<D> None | Some x \<Rightarrow> distr_rai (f (fst x))) A \<partial>\<B>"
    unfolding N_def by (intro arg_cong2[where f="nn_integral"] ext)
      (auto split:split_indicator option.split)
  also have "... = \<integral>\<^sup>+ x. emeasure (if (map_option fst \<circ> m) x \<in> Some ` range_rm m
    then distr_rai (f (the ((map_option fst \<circ> m) x)))
    else return \<D> None) A \<partial>\<B>"
    by (intro arg_cong2[where f="nn_integral"] arg_cong2[where f="emeasure"] refl ext)
     (auto simp add: in_range_rmI vimage_def split:option.splits)
  also have "... =
    \<integral>\<^sup>+ x. emeasure (if x \<in> Some ` range_rm m then ?m (f (the x)) else return \<D> None) A \<partial>?m m"
    unfolding distr_rai_def using distr_rai_measurable[OF wf_m]
    by (intro nn_integral_distr[symmetric]) (simp_all add:comp_def)
  also have "... = emeasure ?RHS A"
    using 3 none_measure_subprob_algebra
    by (intro emeasure_bind[symmetric, where N="\<D>"]) (auto simp add:distr_rai_def Pi_def)
  finally show "emeasure ?L A = emeasure ?RHS A"
    by simp
qed

lemma return_discrete: "return \<D> x = return_pmf x"
  by (intro measure_eqI) auto

lemma distr_rai_return: "distr_rai (return_rai x) = return \<D> (Some x)"
  unfolding return_rai_def distr_rai_def by (simp add:comp_def)

lemma distr_rai_return': "distr_rai (return_rai x) = return_spmf x"
  unfolding distr_rai_return return_discrete by auto

lemma distr_rai_coin: "distr_rai coin_rai = coin_spmf" (is "?L = ?R")
proof -
  have "?L = distr \<B> \<D> (\<lambda>x. Some (chd x))"
    unfolding coin_rai_def distr_rai_def by (simp add:comp_def)
  also have "... = distr (distr \<B> \<D> chd) \<D> Some"
    by (subst distr_distr) (auto simp add:comp_def chd_measurable)
  also have "... = map_pmf Some (pmf_of_set UNIV)"
    unfolding distr_shd  map_pmf_rep_eq by simp
  also have "... = spmf_of_pmf (pmf_of_set UNIV)"
    by (simp add:spmf_of_pmf_def)
  also have "... = coin_spmf"
    by auto
  finally show ?thesis by simp
qed

definition ord_rai  :: "'a random_alg_int \<Rightarrow> 'a random_alg_int \<Rightarrow> bool"
  where "ord_rai = fun_ord (flat_ord None)"

definition lub_rai  :: "'a random_alg_int set \<Rightarrow> 'a random_alg_int"
  where "lub_rai = fun_lub (flat_lub None)"

lemma random_alg_int_pd_fact:
  "partial_function_definitions ord_rai lub_rai"
  unfolding ord_rai_def lub_rai_def
  by (intro partial_function_lift flat_interpretation)

interpretation random_alg_int_pd: partial_function_definitions "ord_rai" "lub_rai"
  by (rule random_alg_int_pd_fact)

lemma wf_lub_helper:
  assumes "ord_rai f g"
  assumes "wf_on_prefix f p r"
  shows "wf_on_prefix g p r"
proof -
  have "g (cshift p cs) = Some (r, cs)" for cs
  proof -
    have "f (cshift p cs) = Some (r,cs)"
      using assms(2) unfolding wf_on_prefix_def by auto
    moreover have "flat_ord None (f (cshift p cs)) (g (cshift p cs))"
      using assms(1) unfolding ord_rai_def fun_ord_def by simp
    ultimately show ?thesis
      unfolding flat_ord_def by auto
  qed
  thus ?thesis
    unfolding wf_on_prefix_def by auto
qed

lemma wf_lub:
  assumes "Complete_Partial_Order.chain ord_rai R"
  assumes "\<And>r. r \<in> R \<Longrightarrow> wf_random r"
  shows "wf_random (lub_rai R)"
proof (rule wf_randomI)
  fix bs
  assume a:"lub_rai R bs \<noteq> None"
  define S where "S = ((\<lambda>x. x bs) ` R)"
  have 0:"lub_rai R bs = flat_lub None S"
    unfolding S_def lub_rai_def fun_lub_def
    by (intro arg_cong2[where f="flat_lub"]) auto

  have "lub_rai R bs = None" if "S \<subseteq> {None}"
    using that unfolding 0 flat_lub_def by auto
  hence "\<not> (S \<subseteq> {None})"
    using a by auto
  then obtain r where 1:"r \<in> R" and 2: "r bs \<noteq> None"
    unfolding S_def by blast
  then obtain p y where 3:"cprefix p bs" and 4:"wf_on_prefix r p y"
    using assms(2)[OF 1] 2 unfolding wf_random_def by (auto split:option.split_asm)
  have "wf_on_prefix (lub_rai R) p y"
    by (intro wf_lub_helper[OF _ 4] random_alg_int_pd.lub_upper 1 assms(1))
  thus "\<exists>p r. cprefix p bs \<and> wf_on_prefix (lub_rai R) p r "
    using 3 by auto
qed

lemma ord_rai_mono:
  assumes "ord_rai f g"
  assumes "\<not> (P None)"
  assumes "P (f bs)"
  shows "P (g bs)"
  using assms unfolding ord_rai_def fun_ord_def flat_ord_def by metis

lemma lub_rai_empty:
  "lub_rai {} = Map.empty"
  unfolding lub_rai_def fun_lub_def flat_lub_def by simp

lemma distr_rai_lub:
  assumes "F \<noteq> {}"
  assumes "Complete_Partial_Order.chain ord_rai F"
  assumes wf_f: "\<And>f. f \<in> F \<Longrightarrow> wf_random f"
  assumes "None \<notin> A"
  shows "emeasure (distr_rai (lub_rai F)) A = (SUP f \<in> F. emeasure (distr_rai f) A)" (is "?L = ?R")
proof -
  have wf_lub: "wf_random (lub_rai F)"
    by (intro wf_lub assms)

  have 4: "ord_rai f (lub_rai F)" if "f \<in> F" for f
    using that random_alg_int_pd.lub_upper[OF assms(2)] by simp

  have 0:"map_option fst (lub_rai F bs) \<in> A \<longleftrightarrow> (\<exists>f \<in> F. map_option fst (f bs) \<in> A)" for bs
  proof
    assume "\<exists>f\<in>F. map_option fst (f bs) \<in> A"
    then obtain f where 3:"map_option fst (f bs) \<in> A" and 5:"f \<in> F"
      by auto
    show "map_option fst (lub_rai F bs) \<in> A"
      by (rule ord_rai_mono[OF 4[OF 5]]) (use 3 assms(4) in auto)
  next
    assume "map_option fst (lub_rai F bs) \<in> A"
    then obtain y where 6:"lub_rai F bs = Some y" "Some (fst y) \<in> A"
      using assms(4) by (cases "lub_rai F bs") auto
    hence "f bs = None \<or> f bs = Some y" if "f \<in> F" for f
      using 4[OF that] unfolding ord_rai_def fun_ord_def flat_ord_def by auto
    moreover have "lub_rai F bs = None" if "\<And>f. f \<in> F \<Longrightarrow> f bs = None"
      using that unfolding lub_rai_def flat_lub_def fun_lub_def by auto
    ultimately obtain f where "f bs = Some y" "f \<in> F"
      using 6(1) by auto
    thus "\<exists>f\<in>F. map_option fst (f bs) \<in> A"
      using 6(2) by force
  qed

  have 1: "Complete_Partial_Order.chain (\<subseteq>) ((\<lambda>f. {bs. map_option fst (f bs) \<in> A}) ` F)"
    using assms(4) by (intro chain_imageI[OF assms(2)] Collect_mono impI) (auto intro:ord_rai_mono)

  have 2: "open {bs. map_option fst (f bs) \<in> A}" (is "open ?T") if "f \<in> F" for f
  proof -
    have wf_f': "wf_random f"
      by (intro assms that)
    have 4:"?T = {bs \<in> topspace euclidean. (map_option fst \<circ> f) bs \<in> A}"
      by simp
    have "openin option_ud A"
      using assms(4) unfolding openin_option_ud by simp
    hence "openin euclidean ?T"
      unfolding 4 by (intro openin_continuous_map_preimage[OF f_continuous] wf_f')
    thus ?thesis
      using open_openin by simp
  qed

  have 3: "{bs. map_option fst (f bs) \<in> A} \<in> sets \<B>" (is "?L1 \<in> _") if "wf_random f" for f
    using distr_rai_measurable[OF that]
    by (intro measurable_sets_coin_space[where P="\<lambda>x. x \<in> A" and A="\<D>"]) (auto simp:comp_def)

  have "?L = emeasure \<B> ((map_option fst \<circ> lub_rai F) -` A \<inter> space \<B>)"
    unfolding distr_rai_def by (intro emeasure_distr distr_rai_measurable[OF wf_lub]) auto
  also have "... = emeasure \<B> {x. map_option fst (lub_rai F x) \<in> A}"
    unfolding space_coin_space by (simp add:vimage_def)
  also have "... = emeasure \<B> (\<Union>f \<in> F. {bs. map_option fst (f bs) \<in> A})"
    unfolding 0 by (intro arg_cong2[where f="emeasure"]) auto
  also have "... = Sup (emeasure \<B> ` (\<lambda>f. {bs. map_option fst (f bs) \<in> A}) ` F)"
    using 2 by (intro tau_additivity[OF coin_space_is_borel_measure] chain_imp_union_stable 1) auto
  also have "... = (SUP f \<in> F. (emeasure \<B> {bs. map_option fst (f bs) \<in> A}))"
    unfolding image_image by simp
  also have "... = (SUP f\<in>F. emeasure \<B> ((map_option fst \<circ> f) -` A \<inter> space \<B>))"
    by (simp add:image_image space_coin_space vimage_def)
  also have "... = ?R"
    unfolding distr_rai_def using distr_rai_measurable[OF wf_f]
    by (intro arg_cong[where f="(Sup)"] image_cong ext emeasure_distr[symmetric]) auto
  finally show ?thesis
    by simp
qed

lemma distr_rai_ord_rai_mono:
  assumes "wf_random f" "wf_random g" "ord_rai f g"
  assumes "None \<notin> A"
  shows "emeasure (distr_rai f) A \<le> emeasure (distr_rai g) A" (is "?L \<le> ?R")
proof -
  have 0:"Complete_Partial_Order.chain ord_rai {f,g}"
    using assms(3) unfolding Complete_Partial_Order.chain_def
    using random_alg_int_pd.leq_refl by auto
  have "ord_rai (lub_rai {f,g}) g"
    using assms(3) random_alg_int_pd.leq_refl
    by (intro random_alg_int_pd.lub_least 0) auto
  moreover have "ord_rai g (lub_rai {f,g})"
    by (intro random_alg_int_pd.lub_upper 0) simp
  ultimately have 1:"g = lub_rai {f,g}"
    by (intro random_alg_int_pd.leq_antisym) auto

  have "emeasure (distr_rai f) A \<le> (SUP x \<in> {f,g}. emeasure (distr_rai x) A)"
    using prob_space_distr_rai assms(1,2) prob_space.measure_le_1
    by (intro cSup_upper bdd_aboveI[where M="1"]) auto
  also have "... = emeasure (distr_rai (lub_rai {f,g})) A"
    using assms by (intro distr_rai_lub[symmetric] 0) auto
  also have "... = emeasure (distr_rai g) A"
    using 1 by auto
  finally show ?thesis
    by simp
qed

lemma distr_rai_None: "distr_rai (\<lambda>_. None) = measure_pmf (return_pmf (None :: 'a option))"
proof -
  have "emeasure (distr_rai Map.empty) A = emeasure (measure_pmf (return_pmf None)) A"
    for A :: "'a option set"
    using coin_space.emeasure_space_1 unfolding distr_rai_def
    by (subst emeasure_distr) simp_all
  thus ?thesis
    by (intro measure_eqI) (simp_all add:distr_rai_def)
qed

lemma bind_rai_mono:
  assumes "ord_rai f1 f2" "\<And>y. ord_rai (g1 y) (g2 y)"
  shows "ord_rai (bind_rai f1 g1) (bind_rai f2 g2)"
proof -
  have "flat_ord None (bind_rai f1 g1 bs) (bind_rai f2 g2 bs)" for bs
  proof (cases "(f1 \<bind> g1) bs")
    case None
    then show ?thesis by (simp add:flat_ord_def)
  next
    case (Some a)
    then obtain y bs' where 0: "f1 bs = Some (y,bs')" and 1:"g1 y bs' \<noteq> None" and "f1 bs \<noteq> None"
      by (cases "f1 bs", auto simp:bind_rai_def)
    hence "f2 bs = f1 bs"
      using assms(1) unfolding ord_rai_def fun_ord_def flat_ord_def by metis
    hence "f2 bs = Some (y,bs')"
      using 0 by auto
    moreover have "g1 y bs' = g2 y bs'"
      using assms(2) 1 unfolding ord_rai_def fun_ord_def flat_ord_def by metis
    ultimately have "(f1 \<bind> g1) bs = (f2 \<bind> g2) bs"
      unfolding bind_rai_def 0 by auto
    thus ?thesis unfolding flat_ord_def by auto
  qed
  thus ?thesis
    unfolding ord_rai_def fun_ord_def by simp
qed

end
