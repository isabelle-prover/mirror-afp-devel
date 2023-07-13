section \<open>Basic Randomized Algorithms\label{sec:basic_randomized_algorithms}\<close>

text \<open>This section introduces a few randomized algorithms for well-known distributions. These both
serve as building blocks for more complex algorithms and as examples describing how to use the
framework.\<close>

theory Basic_Randomized_Algorithms
  imports
    Randomized_Algorithm
    Probabilistic_While.Bernoulli
    Probabilistic_While.Geometric
    Permuted_Congruential_Generator
begin

text \<open>A simple example: Here we define a randomized algorithm that can sample uniformly from
@{term "pmf_of_set {..<(2::nat)^n}"}. (The same problem for general ranges is discussed in
Section~\ref{sec:dice_roll}).\<close>

fun binary_dice_roll :: "nat \<Rightarrow> nat random_alg"
  where
    "binary_dice_roll 0 = return_ra 0" |
    "binary_dice_roll (Suc n) =
      do { h \<leftarrow> binary_dice_roll n;
           c \<leftarrow> coin_ra;
           return_ra (of_bool c + 2 * h)
        }"

text \<open>Because the algorithm terminates unconditionally it is easy to verify that
@{term "binary_dice_roll"} terminates almost surely:\<close>

lemma binary_dice_roll_terminates: "terminates_almost_surely (binary_dice_roll n)"
  by (induction n) (auto intro:terminates_almost_surely_intros)

text \<open>The corresponding PMF can be written as:\<close>

fun binary_dice_roll_pmf :: "nat \<Rightarrow> nat pmf"
  where
    "binary_dice_roll_pmf 0 = return_pmf 0" |
    "binary_dice_roll_pmf (Suc n) =
      do { h \<leftarrow> binary_dice_roll_pmf n;
           c \<leftarrow> coin_pmf;
           return_pmf (of_bool c + 2 * h)
        }"

text \<open>To verify that the distribution of the result of @{term "binary_dice_roll"} is
@{term "binary_dice_roll_pmf"} we can rely on the @{thm [source] pmf_of_ra_simps} simp rules
and the @{thm [source] "terminates_almost_surely_intros"} introduction rules:\<close>

lemma "pmf_of_ra (binary_dice_roll n) = binary_dice_roll_pmf n"
  using binary_dice_roll_terminates
  by (induction n) (simp_all add:terminates_almost_surely_intros pmf_of_ra_simps)

text \<open>Let us now consider an algorithm that does not terminate unconditionally but just almost
surely:\<close>

partial_function (random_alg) binary_geometric :: "nat \<Rightarrow> nat random_alg"
  where
    "binary_geometric n =
      do { c \<leftarrow> coin_ra;
           if c then (return_ra n) else binary_geometric (n+1)
        }"

text \<open>This is necessary for running randomized algorithms defined with the
@{command "partial_function"} directive:\<close>
declare binary_geometric.simps[code]

text \<open>In this case, we need to map to an SPMF:\<close>

partial_function (spmf) binary_geometric_spmf :: "nat \<Rightarrow> nat spmf"
  where
    "binary_geometric_spmf n =
      do { c \<leftarrow> coin_spmf;
           if c then (return_spmf n) else binary_geometric_spmf (n+1)
        }"

text \<open>We use the transfer rules for @{term "spmf_of_ra"} to show the correspondence:\<close>

lemma binary_geometric_ra_correct:
  "spmf_of_ra (binary_geometric x) = binary_geometric_spmf x"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) binary_geometric_spmf binary_geometric"
    unfolding binary_geometric_def binary_geometric_spmf_def
    apply (rule fixp_ra_parametric[OF binary_geometric_spmf.mono binary_geometric.mono])
    by transfer_prover
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by auto
qed

text \<open>Bernoulli distribution: For this example we show correspondence with the already existing
definition of @{term "bernoulli"} SPMF.\<close>

partial_function (random_alg) bernoulli_ra :: "real \<Rightarrow> bool random_alg" where
  "bernoulli_ra p = do {
     b \<leftarrow> coin_ra;
     if b then return_ra (p \<ge> 1 / 2)
     else if p < 1 / 2 then bernoulli_ra (2 * p)
     else bernoulli_ra (2 * p - 1)
   }"

declare bernoulli_ra.simps[code]

text \<open>The following is a different technique to show equivalence of an SPMF with a randomized
algorithm. It only works if the SPMF has weight $1$. First we show that the SPMF is a lower
bound:\<close>

lemma bernoulli_ra_correct_aux: "ord_spmf (=) (bernoulli x) (spmf_of_ra (bernoulli_ra x))"
proof (induction arbitrary:x rule:bernoulli.fixp_induct)
  case 1
  thus ?case by simp
next
  case 2
  thus ?case by simp
next
  case (3 p)
  thus ?case by (subst bernoulli_ra.simps)
      (auto intro:ord_spmf_bind_reflI simp:spmf_of_ra_simps)
qed

text \<open>Then relying on the fact that the SPMF has weight one, we can derive equivalence:\<close>

lemma bernoulli_ra_correct: "bernoulli x = spmf_of_ra (bernoulli_ra x)"
  using lossless_bernoulli weight_spmf_le_1 unfolding lossless_spmf_def
  by (intro eq_iff_ord_spmf[OF _ bernoulli_ra_correct_aux]) auto

text \<open>Because @{term "bernoulli p"} is a lossless SPMF equivalent to
@{term "spmf_of_pmf (bernoulli_pmf p)"} it is also possible to express the above, without referring
to SPMFs:\<close>

lemma
  "terminates_almost_surely (bernoulli_ra p)"
  "bernoulli_pmf p = pmf_of_ra (bernoulli_ra p)"
  unfolding terminates_almost_surely_def pmf_of_ra_def bernoulli_ra_correct[symmetric]
  by (simp_all add: bernoulli_eq_bernoulli_pmf pmf_of_spmf)

context
  includes lifting_syntax
begin

lemma bernoulli_ra_transfer [transfer_rule]:
  "((=) ===> rel_spmf_of_ra) bernoulli bernoulli_ra"
  unfolding rel_fun_def rel_spmf_of_ra_def bernoulli_ra_correct by simp

end

text \<open>Using the randomized algorithm for the Bernoulli distribution, we can introduce one for the
general geometric distribution:\<close>

partial_function (random_alg) geometric_ra :: "real \<Rightarrow> nat random_alg" where
  "geometric_ra p = do {
     b \<leftarrow> bernoulli_ra p;
     if b then return_ra 0 else map_ra ((+) 1) (geometric_ra p)
  }"
declare geometric_ra.simps[code]

lemma geometric_ra_correct: "spmf_of_ra (geometric_ra x) = geometric_spmf x"
proof -
  include lifting_syntax
  have "((=) ===> rel_spmf_of_ra) geometric_spmf geometric_ra"
    unfolding geometric_ra_def geometric_spmf_def
    apply (rule fixp_ra_parametric[OF geometric_spmf.mono geometric_ra.mono])
    by transfer_prover
  thus ?thesis
    unfolding rel_fun_def rel_spmf_of_ra_def by auto
qed

text \<open>Replication of a distribution\<close>

fun replicate_ra :: "nat \<Rightarrow> 'a random_alg \<Rightarrow> 'a list random_alg"
  where
    "replicate_ra 0 f = return_ra []" |
    "replicate_ra (Suc n) f = do { xh \<leftarrow> f; xt \<leftarrow> replicate_ra n f; return_ra (xh#xt) }"

fun replicate_spmf :: "nat \<Rightarrow> 'a spmf \<Rightarrow> 'a list spmf"
  where
    "replicate_spmf 0 f = return_spmf []" |
    "replicate_spmf (Suc n) f = do { xh \<leftarrow> f; xt \<leftarrow> replicate_spmf n f; return_spmf (xh#xt) }"

lemma replicate_ra_correct: "spmf_of_ra (replicate_ra n f) = replicate_spmf n (spmf_of_ra f)"
  by (induction n) (auto simp :spmf_of_ra_simps)

lemma replicate_spmf_of_pmf: "replicate_spmf n (spmf_of_pmf f) = spmf_of_pmf (replicate_pmf n f)"
  by (induction n) (simp_all add:spmf_of_pmf_bind)

text \<open>Binomial distribution\<close>

definition binomial_ra :: "nat \<Rightarrow> real \<Rightarrow> nat random_alg"
  where "binomial_ra n p = map_ra (length \<circ> filter id) (replicate_ra n (bernoulli_ra p))"

lemma
  assumes "p \<in> {0..1}"
  shows "spmf_of_ra (binomial_ra n p) = spmf_of_pmf (binomial_pmf n p)"
proof -
  have "spmf_of_ra (replicate_ra n (bernoulli_ra p))=spmf_of_pmf(replicate_pmf n (bernoulli_pmf p))"
    unfolding replicate_ra_correct bernoulli_ra_correct[symmetric] bernoulli_eq_bernoulli_pmf
    by (simp add:replicate_spmf_of_pmf)

  thus ?thesis
    unfolding binomial_pmf_altdef[OF assms] binomial_ra_def
    by (simp flip:map_spmf_of_pmf add:spmf_of_ra_map)
qed

text \<open>Running randomized algorithms: Here we use the PRG introduced in
Section~\ref{sec:permuted_congruential_generator}.\<close>

value "run_ra (binomial_ra 10 0.5) (random_coins 42)"

value "run_ra (replicate_ra 20 (bernoulli_ra 0.3)) (random_coins 42)"

end