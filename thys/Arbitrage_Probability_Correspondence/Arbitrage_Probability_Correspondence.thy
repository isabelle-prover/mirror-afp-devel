section \<open>Introduction\<close>

theory Arbitrage_Probability_Correspondence
  imports
    "Probability_Inequality_Completeness.Probability_Inequality_Completeness"
    "HOL.Real"
begin

subsection \<open>Motivation\<close>

text \<open>
 Consider a \<^emph>\<open>fixed-odds gambling market\<close> where participants trade bets on arbitrary
 logical propositions.

 In this setting, every bet pays out exactly \<open>$1\<close> if the proposition is true and \<open>$0\<close>
 otherwise. Unlike traditional prediction markets like \<^emph>\<open>PredictIt\<close> or \<^emph>\<open>Polymarket\<close>,
 which usually limit trading to mutually exclusive outcomes, we assume a market that
 allows bets on any combination of logical operators: \<open>AND\<close> (\<open>\<sqinter>\<close>), \<open>OR\<close> (\<open>\<squnion>\<close>), and
 \<open>NOT\<close> (\<open>\<sim>\<close>).

 To understand the relationship between market liquidity and probability logic, imagine
 two events:

   \<^item> \<open>A :: "The NASDAQ will go up 1% by Friday"\<close>
   \<^item> \<open>B :: "The S&P500 will go up 1% by Friday"\<close>

 Suppose the market order book contains the following quotes:

   \<^item> \<open>ASK\<close> for \<open>A\<close> at \<open>$0.40\<close> (Someone is selling/offering a bet on \<open>A\<close>).
   \<^item> \<open>ASK\<close> for \<open>B\<close> at \<open>$0.50\<close> (Someone is selling/offering a bet on \<open>B\<close>).
   \<^item> \<open>BID\<close> for \<open>A \<sqinter> B\<close> at \<open>$0.30\<close> (Someone wants to buy a bet on \<open>A AND B\<close>).
   \<^item> \<open>BID\<close> for \<open>A \<squnion> B\<close> at \<open>$0.70\<close> (Someone wants to buy a bet on \<open>A OR B\<close>).

  An arbitrageur can exploit these prices to guarantee a risk-free profit.

  They act as a \<^emph>\<open>market taker\<close> for the \<open>ASK\<close>s (buying \<open>A\<close> and \<open>B\<close>) and as a
  \<^emph>\<open>market maker\<close> for the BIDs (selling \<open>A AND B\<close> and \<open>A OR B\<close>).

  The initial cash flow is positive:

  \<open>Profit = (BID(A \<sqinter> B) + BID(A \<squnion> B)) - (ASK(A) + ASK(B))\<close>
  \<open>Profit = ($0.30 + $0.70) - ($0.40 + $0.50) = $1.00 - $0.90 = $0.10\<close>

  Crucially, this profit is safe regardless of the outcome. The arbitrageur holds long
  positions in \<open>A\<close> and \<open>B\<close>, and short positions in \<open>A \<sqinter> B\<close> and \<open>A \<squnion> B\<close>.

  \<^item> If both rise (True, True): The arbitrageur wins \<open>$2\<close> on longs, pays \<open>$2\<close> on shorts.
    Net: \<open>$0\<close> payout.
  \<^item> If only one rises (True, False): The arbitrageur wins \<open>$1\<close> on longs, pays \<open>$1\<close> on
    short (the \<open>OR\<close> bet). Net: \<open>$0\<close> payout.
  \<^item> If neither rises (False, False): The arbitrageur wins \<open>$0\<close>, pay \<open>$0\<close>.
    Net: \<open>$0\<close> payout.

  The arbitrage exists because the market prices violate the probability identity:

  \<open>Pr(A) + Pr(B) = Pr(A \<sqinter> B) + Pr(A \<squnion> B)\<close>

  The central result of this work generalizes this intuition:

  \<^emph>\<open>Every arbitrage opportunity corresponds to a probability inequality identity.\<close>
\<close>

subsection \<open>Overview of Results\<close>

text \<open>
  The central result of this work is as follows:

  \<^emph>\<open>Proving a strategy will always yield a profit (if completely matched) in a
    fixed-odds gambling market over arbitrary logical propositions corresponds to
    proving an inequality identity in probability logic, and also corresponds to a
    bounded MaxSAT problem.\<close>

  Such strategies are referred to as \<^emph>\<open>arbitrage strategies\<close>.

  We also consider the \<^emph>\<open>dual\<close> problem of identifying if a trading strategy will never
  make a profit. Strategies that will never logically yield a profit are called
  \<^emph>\<open>incoherent\<close>.
\<close>

subsection \<open>Prior Work\<close>

text \<open>
  Two results that appear to be related at first glance are \<^emph>\<open>The Fundamental Theorem(s)
  of Asset Pricing\<close> (FTAP) \<^cite>\<open>varianArbitragePrincipleFinancial1987\<close> and the
  \<^emph>\<open>Dutch Book Theorem\<close> \<^cite>\<open>definettiSuiPassaggiLimite1930 and
  kemenyFairBetsInductive1955 and lehmanConfirmationRationalBetting1955 and
  ramseyChapterTruthProbability1931\<close>. While the connection to FTAP is purely
  superficial, the results are close in spirit to the Dutch Book tradition: we study
  when a collection of fixed-odds commitments can be  combined into a strategy that is
  guaranteed to lose (or, dually, guaranteed to profit), and we treat such strategies
  as computational objects.

  The Fundamental Theorems of Asset Pricing (FTAP) connect a suitable notion of
  \<^emph>\<open>no-arbitrage\<close> to the existence of a pricing functional (or, in stochastic
  settings, an equivalent martingale measure) in an idealized, frictionless market. In
  their classical formulations, the objects being priced are standard financial assets
  (e.g., securities or commodities) represented by a spot price or a price process,
  and the market model abstracts away from microstructure: order placement, order
  matching, bid/ask discreteness, and fixed-odds quoting are not part of the primitive
  data. By contrast, we work directly with fixed-odds markets for wagers on arbitrary
  logical propositions, where the microstructure of how orders compose into strategies
  is central, and we connect ``no-arbitage'' strategies to the existence of some
  scenario where the strategy doesn't always lose, which falls out of a certain
  bounded MaxSAT calculation.

  The Dutch Book literature shares more of our vocabulary. Philosophical treatments
  emphasize \<^emph>\<open>coherence\<close> and the avoidance of a \<^emph>\<open>bad book\<close>: a collection of
  bets that guarantees a loss. Following H\'ajek's terminology
  \<^cite>\<open>hajekScotchingDutchBooks2005\<close>, one may also speak of \<^emph>\<open>good books\<close>. In this
  development, we adopt finance-oriented language and refer to these objects as
  (loss-guaranteeing) \<^emph>\<open>arbitrage strategies\<close>, because they are assembled from posted
  odds and executed mechanically once the relevant orders are matched. We also work with
  possibility-style representations in the spirit of Lehman, generalized to any instance
  of a \<^class>\<open>classical_logic\<close>.

  Our main contribution is not a normative thesis that rational agents ought to
  conform their degrees of belief to probability theory. Instead, we make explicit a
  three-way correspondence between:

    \<^enum> checking whether a bounded family of fixed-odds commitments is coherent (i.e.,
      not loss-guaranteeing),

    \<^enum> feasibility of a bounded MaxSAT instance derived from the same commitments, and

    \<^enum> certain inequalities that hold for all probability functions over the same set
      of propositions.

  Operationally, we only require the first criterion: there must exist a scenario in
  which the strategy does not always lose. The MaxSAT formulation supplies a concrete
  decision procedure, and the coNP-hardness of the resulting feasibility questions
  explains why coherence checking is not a task one should expect to perform reliably by
  hand.

  We also study the \<^emph>\<open>dual\<close> problem: identifying strategies that are pure
  arbitrages (guaranteed nonnegative payoff with strictly positive payoff in some
  outcome). Such strategies are useful not merely as pathologies, but as mechanisms
  for creating market depth. Intuitively, they can match \<open>BID\<close> interest in one venue
  with \<open>ASK\<close> interest in another, improving execution for multiple participants.
  From a microeconomic perspective, this can increase surplus by enabling trades that
  would otherwise fail to clear.
\<close>

section \<open>Fixed Odds Markets\<close>

notation Probability_Inequality_Completeness.relative_maximals (\<open>\<M>\<close>)

unbundle no funcset_syntax

subsection \<open>Orders and Trading Strategies\<close>

text \<open>
  In this section, we model a \<^emph>\<open>fixed odds market\<close> where each bet pays out \<open>$0\<close> or \<open>$1\<close>,
  and people make and take bets. For simplicity, we consider \<open>BID\<close> and \<open>ASK\<close> limit
  orders of a single unit (i.e., trades such that if they match, then they are
  completely cleared). In an ordinary central limit order book, such \<open>BID\<close> and \<open>ASK\<close>
  orders would have prices in the interval \<open>(0,1)\<close>, but we do not make use of this
  assumption in our proofs, as it is not necessary.
\<close>

record 'p bet_offer =
  bet :: 'p
  price :: real

text \<open>
  A trading strategy is a collection of \<open>BID\<close> and \<open>ASK\<close> orders that are to be matched
  atomically.

  \<^emph>\<open>Making\<close> a bet is when you \<^emph>\<open>ask\<close> a bet on the market, while \<^emph>\<open>taking\<close> a bet is when
  you \<^emph>\<open>bid\<close> a bet on the market.

  A \<^emph>\<open>market maker\<close> is one who puts up capital and asks bets, while a \<^emph>\<open>market taker\<close> is
  one who bids bets.

  In a trading strategy, the market participant acts as a market maker for the \<open>ASK\<close>
  orders they are willing make and as a market taker for the \<open>BID\<close> orders they are
  willing to make.
\<close>

record 'p strategy =
  asks ::  "('p bet_offer) list"
  bids :: "('p bet_offer) list"

subsection \<open>Possibility Functions\<close>

text \<open>
  Possibility functions are states of affairs that determine the outcomes of bets.
  They were first used in Lehman's formulation of the Dutch Book Theorem
  \<^cite>\<open>lehmanConfirmationRationalBetting1955\<close>. Our approach diverges from Lehman's.
  Lehman uses linear programming to prove his result. Our formulation is pure
  probability logic.
\<close>

text \<open>
  We give our definition of a possibility function as follows:
\<close>

definition (in classical_logic) possibility :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  [simp]: "possibility p \<equiv>
                \<not> (p \<bottom>)
              \<and> (\<forall> \<phi>. \<turnstile> \<phi> \<longrightarrow> p \<phi>)
              \<and> (\<forall> \<phi> \<psi> . p (\<phi> \<rightarrow> \<psi>) \<longrightarrow> p \<phi> \<longrightarrow> p \<psi>)
              \<and> (\<forall> \<phi> . p \<phi> \<or> p (\<sim> \<phi>))"

text \<open>
  Our formulation of possibility functions generalizes Lehman's. Lehman restricts his
  definition to the language of classical propositional logic formulae. We define ours
  over any arbitrary classical logic satisfying the axioms of the \<^class>\<open>classical_logic\<close>
  class.
\<close>

definition (in classical_logic) possibilities :: "('a \<Rightarrow> bool) set" where
  [simp]: "possibilities = {p. possibility p}"

lemma (in classical_logic) possibility_negation:
  assumes "possibility p"
  shows "p (\<phi> \<rightarrow> \<bottom>) = (\<not> p \<phi>)"
proof
  assume "p (\<phi> \<rightarrow> \<bottom>)"
  show "\<not> p \<phi>"
  proof
    assume "p \<phi>"
    have "\<turnstile> \<phi> \<rightarrow> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>"
      by (simp add: double_negation_converse)
    hence "p ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<bottom>)"
      using \<open>p \<phi>\<close> \<open>possibility p\<close> by auto
    thus "False" using \<open>p (\<phi> \<rightarrow> \<bottom>)\<close> \<open>possibility p\<close> by auto
  qed
next
  show "\<not> p \<phi> \<Longrightarrow> p (\<phi> \<rightarrow> \<bottom>)"
    using \<open>possibility p\<close> negation_def by fastforce
qed

lemma (in classical_logic) possibilities_logical_closure:
  assumes "possibility p"
      and "{x. p x} \<tturnstile> \<phi>"
    shows "p \<phi>"
proof -
  {
    fix \<Gamma>
    assume "set \<Gamma> \<subseteq> Collect p"
    hence "\<forall> \<phi>. \<Gamma> :\<turnstile> \<phi> \<longrightarrow> p \<phi>"
    proof (induct \<Gamma>)
      case Nil
      have "\<forall>\<phi>. \<turnstile> \<phi> \<longrightarrow> p \<phi>"
        using \<open>possibility p\<close> by auto
      then show ?case
        using list_deduction_base_theory by blast
    next
      case (Cons \<gamma> \<Gamma>)
      hence "p \<gamma>"
        by simp
      have "\<forall> \<phi>. \<Gamma> :\<turnstile> \<gamma> \<rightarrow> \<phi> \<longrightarrow> p (\<gamma> \<rightarrow> \<phi>)"
        using Cons.hyps Cons.prems by auto
      then show ?case
        by (meson
              \<open>p \<gamma>\<close>
              \<open>possibility p\<close>
              list_deduction_theorem
              possibility_def)
    qed
  }
  thus ?thesis
    using \<open>Collect p \<tturnstile> \<phi>\<close> set_deduction_def by auto
qed

text \<open>
  The next two lemmas establish that possibility functions are equivalent to maximally
  consistent sets.
\<close>

lemma (in classical_logic) possibilities_are_MCS:
  assumes "possibility p"
  shows "MCS {x. p x}"
  using assms
  by (metis
        (mono_tags, lifting)
        formula_consistent_def
        formula_maximally_consistent_set_def_def
        maximally_consistent_set_def
        possibilities_logical_closure
        possibility_def
        mem_Collect_eq
        negation_def)

lemma (in classical_logic) MCSs_are_possibilities:
  assumes "MCS s"
  shows "possibility (\<lambda> x. x \<in> s)"
proof -
  have "\<bottom> \<notin> s"
    using \<open>MCS s\<close>
          formula_consistent_def
          formula_maximally_consistent_set_def_def
          maximally_consistent_set_def
          set_deduction_reflection
    by blast
  moreover have "\<forall> \<phi>. \<turnstile> \<phi> \<longrightarrow> \<phi> \<in> s"
    using \<open>MCS s\<close>
          formula_maximally_consistent_set_def_reflection
          maximally_consistent_set_def
          set_deduction_weaken
    by blast
  moreover have "\<forall> \<phi> \<psi>. (\<phi> \<rightarrow> \<psi>) \<in> s \<longrightarrow> \<phi> \<in> s \<longrightarrow> \<psi> \<in> s"
    using \<open>MCS s\<close>
          formula_maximal_consistency
          formula_maximally_consistent_set_def_implication
    by blast
  moreover have "\<forall> \<phi>. \<phi> \<in> s \<or> (\<phi> \<rightarrow> \<bottom>) \<in> s"
    using assms
          formula_maximally_consistent_set_def_implication
          maximally_consistent_set_def
    by blast
  ultimately show ?thesis by (simp add: negation_def)
qed

subsection \<open>Payoff Functions\<close>

text \<open>
  Given a market strategy and a possibility function, we can define the \<^emph>\<open>payoff\<close> of
  that strategy if all the bet positions in that strategy were matched and settled at
  the particular state of affairs given by the possibility function.

  Recall that in a trading strategy, we act as a market \<^emph>\<open>maker\<close> for ask positions,
  meaning we payout if the proposition behind the bet we are asking evaluates to
  \<^emph>\<open>true\<close>.

  Payoff is revenue from won bets minus costs of the \<open>BID\<close>s for those bets, plus revenue
  from sold \<open>ASK\<close> bets minus payouts from bets lost.
\<close>

definition payoff :: "('p \<Rightarrow> bool) \<Rightarrow> 'p strategy \<Rightarrow> real" ("\<pi>") where
  [simp]: "\<pi> s strategy \<equiv>
    (\<Sum> i \<leftarrow> bids strategy. (if s (bet i) then 1 else 0) - price i)
    + (\<Sum> i \<leftarrow> asks strategy. price i - (if s (bet i) then 1 else 0))"

text \<open>
  Alternate definitions of the payout function \<^term>\<open>\<pi>\<close> are to use the notion of
  \<^emph>\<open>settling\<close> bets given a state of affairs. Settling is just paying out those bets that
  came true.
\<close>

definition settle_bet :: "('p \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> real" where
  "settle_bet s \<phi> \<equiv> if (s \<phi>) then 1 else 0"

lemma payoff_alt_def1:
  "\<pi> s strategy =
      (\<Sum> i \<leftarrow> bids strategy. settle_bet s (bet i) - price i)
    + (\<Sum> i \<leftarrow> asks strategy. price i - settle_bet s (bet i))"
  unfolding settle_bet_def
  by simp

definition settle :: "('p \<Rightarrow> bool) \<Rightarrow> 'p bet_offer list \<Rightarrow> real" where
  "settle s bets \<equiv> \<Sum> b \<leftarrow> bets. settle_bet s (bet b)"

lemma settle_alt_def:
  "settle q bets = length [\<phi> \<leftarrow> [ bet b . b \<leftarrow> bets ] . q \<phi>]"
  unfolding settle_def settle_bet_def
  by (induct bets, simp+)

definition total_price :: "('p bet_offer) list \<Rightarrow> real" where
  "total_price offers \<equiv> \<Sum> i \<leftarrow> offers. price i"

lemma payoff_alt_def2:
  "\<pi> s strategy = settle s (bids strategy)
                    - settle s (asks strategy)
                    + total_price (asks strategy)
                    - total_price (bids strategy)"
  unfolding payoff_alt_def1 total_price_def settle_def
  by (simp add: sum_list_subtractf)

subsection \<open>Revenue Equivalence\<close>

text \<open>
  When evaluating a payout function, we can essentially convert \<open>BID\<close> orders to \<open>ASK\<close>
  orders in a strategy, provided we properly account for locked capital when
  calculating the effective prices for the new \<open>ASK\<close> positions.
\<close>

definition (in classical_logic) negate_bets ("_\<^sup>\<sim>") where
  "bets\<^sup>\<sim> = [b \<lparr> bet := \<sim> (bet b) \<rparr>. b \<leftarrow> bets]"

lemma (in classical_logic) ask_revenue_equivalence:
  assumes "possibility p"
  shows   "  \<pi> p \<lparr> asks = asks', bids = bids' \<rparr>
           = - settle p (bids'\<^sup>\<sim> @ asks')
             + total_price asks'
             + length bids'
             - total_price bids'"
proof (induct bids')
  case Nil
  then show ?case
    unfolding
      payoff_alt_def2
      negate_bets_def
      total_price_def
      settle_def
    by simp
next
  case (Cons bid' bids')
  have "p (\<sim> (bet bid')) = (\<not> (p (bet bid')))"
    using assms negation_def by auto
  moreover have
    "total_price ((bid' # bids') @ asks')
       = price bid' + total_price bids' + total_price asks'"
    unfolding total_price_def
    by (induct asks', induct bids', auto)
  ultimately show ?case
    using Cons
    unfolding payoff_alt_def2 negate_bets_def settle_def settle_bet_def
    by simp
qed

text \<open>
  The dual is also true: when evaluating a payout function, we can, in a sense, treat
  \<open>ASK\<close> as \<open>BID\<close> positions with proper accounting.
\<close>

lemma (in classical_logic) bid_revenue_equivalence:
  assumes "possibility p"
  shows   "   \<pi> p \<lparr> asks = asks', bids = bids' \<rparr>
            =   settle p (asks'\<^sup>\<sim> @ bids')
              + total_price asks'
              - total_price bids'
              - length asks'"
proof (induct asks')
  case Nil
  then show ?case
    unfolding
      payoff_alt_def2
      negate_bets_def
      total_price_def
      settle_def
      settle_bet_def
    by simp
next
  case (Cons s asks')
  have "p (\<sim> (bet s)) = (\<not> (p (bet s)))" using assms negation_def by auto
  moreover have "  total_price ((s # asks') @ bids')
                 = price s + total_price asks' + total_price bids'"
    unfolding total_price_def
    by (induct bids', induct asks', auto)
  ultimately show ?case
    using Cons
    unfolding payoff_alt_def2 negate_bets_def settle_def settle_bet_def
    by simp
qed

section \<open>Arbitrage Strategies\<close>

subsection \<open>Introduction\<close>

text \<open>
  In this section, we consider the problem of computing whether a strategy will always
  yield a profit. Such strategies are referred to as \<^emph>\<open>arbitrage strategies\<close>.
\<close>

subsection \<open>Minimum Payoff\<close>

text \<open>
  When computing whether a strategy is suited to arbitrage trading, we need to know the
  \<^emph>\<open>minimum payoff\<close> of that strategy given every possible scenario.
\<close>

definition (in consistent_classical_logic)
  minimum_payoff :: "'a strategy \<Rightarrow> real" ("\<pi>\<^sub>m\<^sub>i\<^sub>n") where
  "\<pi>\<^sub>m\<^sub>i\<^sub>n b \<equiv> THE x. (\<exists> p \<in> possibilities. \<pi> p b = x)
                   \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q b)"

text \<open>
  Since our definition of \<^term>\<open>\<pi>\<^sub>m\<^sub>i\<^sub>n\<close> relies on a definite descriptor, we need the
  following theorem to prove it is well-defined.
\<close>

lemma (in consistent_classical_logic) minimum_payoff_existence:
  "\<exists>! x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q bets)"
proof (rule ex_ex1I)
  show "\<exists>x. (\<exists>p\<in>possibilities. \<pi> p bets = x) \<and> (\<forall>q\<in>possibilities. x \<le> \<pi> q bets)"
  proof (rule ccontr)
    obtain bids' asks' where "bets = \<lparr> asks = asks', bids = bids' \<rparr>"
      by (metis strategy.cases)
    assume "\<nexists>x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q bets)"
    hence "\<forall>x. (\<exists> p \<in> possibilities. \<pi> p bets = x) \<longrightarrow> (\<exists> q \<in> possibilities. \<pi> q bets < x)"
      by (meson le_less_linear)
    hence \<star>: "\<forall>p \<in> possibilities. \<exists> q \<in> possibilities. \<pi> q bets < \<pi> p bets"
      by blast
    have \<lozenge>: "\<forall> p \<in> possibilities. \<exists> q \<in> possibilities.
                    settle q (asks'\<^sup>\<sim> @ bids') < settle p (asks'\<^sup>\<sim> @ bids')"
    proof
      fix p
      assume "p \<in> possibilities"
      from this obtain q where "q \<in> possibilities" and "\<pi> q bets < \<pi> p bets"
        using \<star> by blast
      hence
        "  settle q (asks'\<^sup>\<sim> @ bids')
             + total_price asks'
             - total_price bids'
             - length asks'
         < settle p (asks'\<^sup>\<sim> @ bids')
             + total_price asks'
             - total_price bids'
             - length asks'"
        by (metis \<open>\<pi> q bets < \<pi> p bets\<close>
                  \<open>bets = \<lparr>asks = asks', bids = bids'\<rparr>\<close>
                  \<open>p \<in> possibilities\<close>
                  possibilities_def
                  bid_revenue_equivalence
                  mem_Collect_eq)
      hence "settle q (asks'\<^sup>\<sim> @ bids') < settle p (asks'\<^sup>\<sim> @ bids')"
        by simp
      thus "\<exists>q\<in>possibilities. settle q (asks'\<^sup>\<sim> @ bids') < settle p (asks'\<^sup>\<sim> @ bids')"
        using \<open>q \<in> possibilities\<close> by blast
    qed
    {
      fix bets :: "('a bet_offer) list"
      fix s :: "'a \<Rightarrow> bool"
      have "\<exists> n \<in> \<nat>. settle s bets = real n"
        unfolding settle_def settle_bet_def
        by (induct bets, auto, metis Nats_1 Nats_add Suc_eq_plus1_left of_nat_Suc)
    } note \<dagger> = this
    {
      fix n :: "nat"
      have "    (\<exists> p \<in> possibilities. settle p (asks'\<^sup>\<sim> @ bids') \<le> n)
            \<longrightarrow> (\<exists> q \<in> possibilities. settle q (asks'\<^sup>\<sim> @ bids') < 0)"
            (is "_ \<longrightarrow> ?consequent")
      proof (induct n)
        case 0
        {
          fix p :: "'a \<Rightarrow> bool"
          assume "p \<in> possibilities" and "settle p (asks'\<^sup>\<sim> @ bids') \<le> 0"
          from this obtain q where
            "q \<in> possibilities"
            "settle q (asks'\<^sup>\<sim> @ bids') < settle p (asks'\<^sup>\<sim> @ bids')"
            using \<lozenge> by blast
          hence ?consequent
            by (metis
                  \<dagger>
                  \<open>settle p (asks'\<^sup>\<sim> @ bids') \<le> 0\<close>
                  of_nat_0_eq_iff
                  of_nat_le_0_iff)
        }
        then show ?case by auto
      next
        case (Suc n)
        {
          fix p :: "'a \<Rightarrow> bool"
          assume"p \<in> possibilities" and "settle p (asks'\<^sup>\<sim> @ bids') \<le> Suc n"
          from this obtain q\<^sub>1 where
            "q\<^sub>1 \<in> possibilities"
            "settle q\<^sub>1 (asks'\<^sup>\<sim> @ bids') < Suc n"
            by (metis \<lozenge> antisym_conv not_less)
          from this obtain q\<^sub>2 where
            "q\<^sub>2 \<in> possibilities"
            "settle q\<^sub>2 (asks'\<^sup>\<sim> @ bids') < n"
            using \<lozenge>
            by (metis
                  \<dagger>
                  add.commute
                  nat_le_real_less
                  nat_less_le
                  of_nat_Suc
                  of_nat_less_iff)
          hence ?consequent
            by (metis \<dagger> Suc.hyps nat_less_le of_nat_le_iff of_nat_less_iff)
        }
        then show ?case by auto
      qed
    }
    hence "\<nexists> p. p \<in> possibilities"
      by (metis \<dagger> not_less0 of_nat_0 of_nat_less_iff order_refl)
    moreover
    have "\<not> {} \<tturnstile> \<bottom>"
      using consistency set_deduction_base_theory by auto
    from this obtain \<Gamma> where "MCS \<Gamma>"
      by (meson formula_consistent_def
                formula_maximal_consistency
                formula_maximally_consistent_extension)
    hence "(\<lambda> \<gamma>. \<gamma> \<in> \<Gamma>) \<in> possibilities"
      using MCSs_are_possibilities possibilities_def by blast
    ultimately show False
      by blast
  qed
next
  fix x y
  assume A: "(\<exists>p \<in> possibilities. \<pi> p bets = x) \<and> (\<forall>q \<in> possibilities. x \<le> \<pi> q bets)"
  and B: "(\<exists>p \<in> possibilities. \<pi> p bets = y) \<and> (\<forall>q \<in> possibilities. y \<le> \<pi> q bets)"
  from this obtain p\<^sub>x p\<^sub>y where
    "p\<^sub>x \<in> possibilities"
    "p\<^sub>y \<in> possibilities"
    "\<pi> p\<^sub>x bets = x"
    "\<pi> p\<^sub>y bets = y"
    by blast
  with A B have "x \<le> y" "y \<le> x"
    by blast+
  thus "x = y" by linarith
qed

subsection \<open>Bounding Minimum Payoffs Below Using MaxSAT\<close>

text \<open>
  Below, we present our second major theorem: computing a lower bound to a strategy's
  minimum payoff is equivalent to checking a bounded MaxSAT problem.

  A concrete implementation of this algorithm would enable software search for trading
  strategies that can convert orders from one central limit order book to another.

  As in the previous section, we prove our theorem in the general case of an arbitrary
  \<open>k\<close>, but in practice users will want to set \<open>k = 0\<close> to check if their strategy is an
  arbitrage strategy.
\<close>

theorem (in consistent_classical_logic) arbitrageur_maxsat:
  "  ((k :: real) \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> asks = asks', bids = bids' \<rparr>)
   = (  MaxSAT [bet b . b \<leftarrow> bids'\<^sup>\<sim> @ asks']
      \<le> total_price asks' + length bids' - total_price bids' - k )"
  (is "(k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets) = (MaxSAT ?props \<le> total_price _ + _ - _ - _)")
proof
  assume "k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets"
  let ?P = "\<lambda> x . (\<exists> p \<in> possibilities. \<pi> p ?bets = x)
                       \<and> (\<forall> q \<in> possibilities. x \<le> \<pi> q ?bets)"
  obtain p where
      "possibility p" and
      "\<forall> q \<in> possibilities. \<pi> p ?bets \<le> \<pi> q ?bets"
    using \<open>k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets\<close>
          minimum_payoff_existence [of ?bets]
    by (metis possibilities_def mem_Collect_eq)
  hence "?P (\<pi> p ?bets)"
    using possibilities_def by blast
  hence "\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> p ?bets"
    unfolding minimum_payoff_def
    using minimum_payoff_existence [of ?bets]
          the1_equality [where P = ?P and a = "\<pi> p ?bets"]
    by blast

  let ?\<Phi> = "[\<phi> \<leftarrow> ?props. p \<phi>]"

  have "mset ?\<Phi> \<subseteq># mset ?props"
    by(induct ?props,
       auto,
       simp add: subset_mset.add_mono)
  moreover
  have "\<not> (?\<Phi> :\<turnstile> \<bottom>)"
  proof -
    have "set ?\<Phi> \<subseteq> {x. p x}"
      by auto
    hence "\<not> (set ?\<Phi> \<tturnstile> \<bottom>)"
      by (meson \<open>possibility p\<close>
                possibilities_are_MCS [of p]
                formula_consistent_def
                formula_maximally_consistent_set_def_def
                maximally_consistent_set_def
                list_deduction_monotonic
                set_deduction_def)
    thus ?thesis
      using set_deduction_def by blast
  qed
  moreover
  {
    fix \<Psi>
    assume "mset \<Psi> \<subseteq># mset ?props" and "\<not> \<Psi> :\<turnstile> \<bottom>"
    from this obtain \<Omega>\<^sub>\<Psi> where "MCS \<Omega>\<^sub>\<Psi>" and "set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>"
      by (meson formula_consistent_def
                formula_maximal_consistency
                formula_maximally_consistent_extension
                list_deduction_monotonic
                set_deduction_def)
    let ?q = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Psi>"
    have "possibility ?q"
      using \<open>MCS \<Omega>\<^sub>\<Psi>\<close> MCSs_are_possibilities by blast
    hence "\<pi> p ?bets \<le> \<pi> ?q ?bets"
      using \<open>\<forall>q\<in>possibilities. \<pi> p ?bets \<le> \<pi> q ?bets\<close>
            possibilities_def
      by blast
    let ?c = "total_price asks' + length bids' - total_price bids'"
    have "- settle p (bids'\<^sup>\<sim> @ asks') + ?c \<le> - settle ?q (bids'\<^sup>\<sim> @ asks') + ?c"
      using \<open>\<pi> p ?bets \<le> \<pi> ?q ?bets\<close>
            \<open>possibility p\<close>
            ask_revenue_equivalence [of p asks' bids']
            \<open>possibility ?q\<close>
            ask_revenue_equivalence [of ?q asks' bids']
      by linarith
    hence "settle ?q (bids'\<^sup>\<sim> @ asks') \<le> settle p (bids'\<^sup>\<sim> @ asks')"
      by linarith
    let ?\<Psi>' = "[\<phi> \<leftarrow> ?props. ?q \<phi>]"
    have "length ?\<Psi>' \<le> length ?\<Phi>"
      using \<open>settle ?q (bids'\<^sup>\<sim> @ asks') \<le> settle p (bids'\<^sup>\<sim> @ asks')\<close>
      unfolding settle_alt_def
      by simp
    moreover
    have "length \<Psi> \<le> length ?\<Psi>'"
    proof -
      have "mset [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<subseteq># mset ?\<Psi>'"
      proof -
        {
          fix props :: "'a list"
          have "\<forall> \<Psi>. \<forall> \<Omega>. mset \<Psi> \<subseteq># mset props \<longrightarrow>
                            mset [\<psi> \<leftarrow> \<Psi>. \<psi> \<in> \<Omega>] \<subseteq># mset [\<phi> \<leftarrow> props. \<phi> \<in> \<Omega>]"
            by (simp add: multiset_filter_mono)
        }
        thus ?thesis
          using \<open>mset \<Psi> \<subseteq># mset ?props\<close> by blast
      qed
      hence "length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<le> length ?\<Psi>'"
        by (metis (no_types, lifting) length_sub_mset mset_eq_length nat_less_le not_le)
      moreover have "length \<Psi> = length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>]"
        using \<open>set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>\<close>
        by (induct \<Psi>, simp+)
      ultimately show ?thesis by linarith
    qed
    ultimately have "length \<Psi> \<le> length ?\<Phi>" by linarith
  }
  ultimately have "?\<Phi> \<in> \<M> ?props \<bottom>"
    unfolding relative_maximals_def
    by blast
  hence "MaxSAT ?props = length ?\<Phi>"
    using relative_MaxSAT_intro by presburger
  hence "MaxSAT ?props = settle p (bids'\<^sup>\<sim> @ asks')"
    unfolding settle_alt_def
    by simp
  thus "MaxSAT ?props \<le> total_price asks' + length bids' - total_price bids' - k"
    using ask_revenue_equivalence [of p asks' bids']
          \<open>k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets\<close>
          \<open>\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> p ?bets\<close>
          \<open>possibility p\<close>
    by linarith
next
  let ?c = "total_price asks' + length bids' - total_price bids'"
  assume "MaxSAT ?props \<le> total_price asks' + length bids' - total_price bids' - k"
  from this obtain \<Phi> where "\<Phi> \<in> \<M> ?props \<bottom>" and "length \<Phi> + k \<le> ?c"
    using
      consistency
      relative_MaxSAT_intro
      relative_maximals_existence
    by fastforce
  hence "\<not> \<Phi> :\<turnstile> \<bottom>"
    using relative_maximals_def by blast
  from this obtain \<Omega>\<^sub>\<Phi> where "MCS \<Omega>\<^sub>\<Phi>" and "set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>"
    by (meson formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_extension
              list_deduction_monotonic
              set_deduction_def)
  let ?p = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Phi>"
  have "possibility ?p"
    using \<open>MCS \<Omega>\<^sub>\<Phi>\<close> MCSs_are_possibilities by blast
  have "mset \<Phi> \<subseteq># mset ?props"
    using \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close> relative_maximals_def by blast
  have "mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]"
    by (metis \<open>mset \<Phi> \<subseteq># mset ?props\<close>
              \<open>set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>\<close>
              filter_True
              mset_filter
              multiset_filter_mono
              subset_code(1))
  have "mset \<Phi> = mset [ b \<leftarrow> ?props. ?p b]"
  proof (rule ccontr)
    assume "mset \<Phi> \<noteq> mset [ b \<leftarrow> ?props. ?p b]"
    hence "length \<Phi> < length [ b \<leftarrow> ?props. ?p b]"
      using
        \<open>mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]\<close>
        length_sub_mset not_less
      by blast
    moreover
    have "\<not> [ b \<leftarrow> ?props. ?p b] :\<turnstile> \<bottom>"
      by (metis
            IntE
            \<open>MCS \<Omega>\<^sub>\<Phi>\<close>
            inter_set_filter
            formula_consistent_def
            formula_maximally_consistent_set_def_def
            maximally_consistent_set_def
            set_deduction_def
            subsetI)
    hence "length [ b \<leftarrow> ?props. ?p b] \<le> length \<Phi>"
      by (metis
            (mono_tags, lifting)
            \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close>
            relative_maximals_def [of ?props \<bottom>]
            mem_Collect_eq
            mset_filter
            multiset_filter_subset)
    ultimately show "False"
      using not_le by blast
  qed
  hence "length \<Phi> = settle ?p (bids'\<^sup>\<sim> @ asks')"
    unfolding settle_alt_def
    using mset_eq_length
    by metis
  hence "k \<le> settle ?p (bids'\<^sup>\<sim> @ asks')
             + total_price asks' + length bids' - total_price bids'"
    using \<open>length \<Phi> + k \<le> ?c\<close> by linarith
  hence "k \<le> \<pi> ?p ?bets"
    using \<open>possibility ?p\<close>
          ask_revenue_equivalence [of ?p asks' bids']
          \<open>length \<Phi> + k \<le> ?c\<close>
          \<open>length \<Phi> = settle ?p (bids'\<^sup>\<sim> @ asks')\<close>
    by linarith
  have "\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets"
  proof
    {
      fix x :: 'a
      fix P A
      have "x \<in> Set.filter P A \<longleftrightarrow> x \<in> A \<and> P x"
        by (simp add: filter_def)
    }
    note member_filter = this
    fix q
    assume "q \<in> possibilities"
    hence "\<not> [ b \<leftarrow> ?props. q b] :\<turnstile> \<bottom>"
      unfolding possibilities_def
      by (metis filter_set
                possibilities_logical_closure
                possibility_def
                set_deduction_def
                mem_Collect_eq
                member_filter
                subsetI)
    hence "length [ b \<leftarrow> ?props. q b] \<le> length \<Phi>"
      by (metis (mono_tags, lifting)
                \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close>
                relative_maximals_def
                mem_Collect_eq
                mset_filter
                multiset_filter_subset)
    hence
      "  - settle ?p (bids'\<^sup>\<sim> @ asks')
           + total_price asks'
           + length bids'
           - total_price bids'
       \<le> - settle q (bids'\<^sup>\<sim> @ asks')
           + total_price asks'
           + length bids'
           - total_price bids'"
      using \<open>length \<Phi> = settle ?p (bids'\<^sup>\<sim> @ asks')\<close>
            settle_alt_def [of q "bids'\<^sup>\<sim> @ asks'"]
      by linarith
    thus "\<pi> ?p ?bets \<le> \<pi> q ?bets"
      using ask_revenue_equivalence [of ?p asks' bids']
            ask_revenue_equivalence [of q asks' bids']
            \<open>possibility ?p\<close>
            \<open>q \<in> possibilities\<close>
      unfolding possibilities_def
      by (metis mem_Collect_eq)
  qed
  have "\<pi>\<^sub>m\<^sub>i\<^sub>n ?bets = \<pi> ?p ?bets"
    unfolding minimum_payoff_def
  proof
    show "(\<exists>p\<in>possibilities. \<pi> p ?bets = \<pi> ?p ?bets)
             \<and> (\<forall>q\<in>possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets)"
      using \<open>\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets\<close>
            \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
  next
    fix n
    assume \<star>: "(\<exists>p\<in>possibilities. \<pi> p ?bets = n) \<and> (\<forall>q\<in>possibilities. n \<le> \<pi> q ?bets)"
    from this obtain p where "\<pi> p ?bets = n" and "possibility p"
      using possibilities_def by blast
    hence "\<pi> p ?bets \<le> \<pi> ?p ?bets"
      using \<star> \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
    moreover have "\<pi> ?p ?bets \<le> \<pi> p ?bets"
      using \<open>\<forall> q \<in> possibilities. \<pi> ?p ?bets \<le> \<pi> q ?bets\<close>
            \<open>possibility p\<close>
      unfolding possibilities_def
      by blast
    ultimately show "n = \<pi> ?p ?bets" using \<open>\<pi> p ?bets = n\<close> by linarith
  qed
  thus "k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n ?bets"
    using \<open>k \<le> \<pi> ?p ?bets\<close>
    by auto
qed

section \<open>Coherence Checking\<close>

subsection \<open>Introduction\<close>

text \<open>
  In this section, we give an abstract algorithm for traders to use to detect if a
  strategy they want to employ will \<^emph>\<open>always lose\<close>, i.e., is \<^emph>\<open>incoherent\<close>.
\<close>

subsection \<open>Maximum Payoff\<close>

text \<open>
  The key to figuring out if a trading strategy will not always lose is computing the
  strategy's \<^emph>\<open>maximum payoff\<close>.

  Below, we define the maximum payoff using a definite description.
\<close>

definition (in consistent_classical_logic)
  maximum_payoff :: "'a strategy \<Rightarrow> real" ("\<pi>\<^sub>m\<^sub>a\<^sub>x") where
  "\<pi>\<^sub>m\<^sub>a\<^sub>x b \<equiv> THE x. (\<exists> p \<in> possibilities. \<pi> p b = x)
                   \<and> (\<forall> q \<in> possibilities. \<pi> q b \<le> x)"

text \<open>
  The following lemma establishes that our definition of \<^term>\<open>\<pi>\<^sub>m\<^sub>a\<^sub>x\<close> is well-defined.
\<close>

lemma (in consistent_classical_logic) maximum_payoff_existence:
  "\<exists>! x. (\<exists> p \<in> possibilities. \<pi> p bets = x)
          \<and> (\<forall> q \<in> possibilities. \<pi> q bets \<le> x)"
proof (rule ex_ex1I)
  show "\<exists>x. (\<exists> p \<in>possibilities. \<pi> p bets = x)
             \<and> (\<forall> q \<in> possibilities. \<pi> q bets \<le> x)"
  proof (rule ccontr)
    obtain bids' asks' where "bets = \<lparr> asks = asks', bids = bids' \<rparr>"
      by (metis strategy.cases)
    assume "\<nexists>x. (\<exists>p\<in>possibilities. \<pi> p bets = x)
                   \<and> (\<forall>q\<in>possibilities. \<pi> q bets \<le> x)"
    hence "\<forall>x. (\<exists> p \<in> possibilities. \<pi> p bets = x)
                  \<longrightarrow> (\<exists> q \<in> possibilities. x < \<pi> q bets)"
      by (meson le_less_linear)
    hence \<star>: "\<forall>p \<in> possibilities. \<exists> q \<in> possibilities. \<pi> p bets < \<pi> q bets"
      by blast
    have \<lozenge>: "\<forall> p \<in> possibilities. \<exists> q \<in> possibilities.
                    settle p (asks'\<^sup>\<sim> @ bids') < settle q (asks'\<^sup>\<sim> @ bids')"
    proof
      fix p
      assume "p \<in> possibilities"
      from this obtain q where "q \<in> possibilities" and "\<pi> p bets < \<pi> q bets"
        using \<star> by blast
      hence
        "     settle p (asks'\<^sup>\<sim> @ bids')
            + total_price asks'
            - total_price bids'
            - length asks'
         <    settle q (asks'\<^sup>\<sim> @ bids')
            + total_price asks'
            - total_price bids'
            - length asks'"
        by (metis \<open>\<pi> p bets < \<pi> q bets\<close>
                  \<open>bets = \<lparr>asks = asks', bids = bids'\<rparr>\<close>
                  \<open>p \<in> possibilities\<close>
                  possibilities_def
                  bid_revenue_equivalence
                  mem_Collect_eq)
      hence "settle p (asks'\<^sup>\<sim> @ bids') < settle q (asks'\<^sup>\<sim> @ bids')"
        by simp
      thus "\<exists>q\<in>possibilities.   settle p (asks'\<^sup>\<sim> @ bids')
                              < settle q (asks'\<^sup>\<sim> @ bids')"
        using \<open>q \<in> possibilities\<close> by blast
    qed
    {
      fix bets :: "('a bet_offer) list"
      fix s :: "'a \<Rightarrow> bool"
      have "\<exists> n \<in> \<nat>. settle s bets = real n"
        unfolding settle_def settle_bet_def
        by (induct bets,
            auto,
            metis
              Nats_1
              Nats_add
              Suc_eq_plus1_left of_nat_Suc)
    } note \<dagger> = this
    {
      fix n :: "nat"
      have "\<exists> q \<in> possibilities. n \<le> settle q (asks'\<^sup>\<sim> @ bids')"
        by (induct n,
            metis
              \<dagger>
              MCSs_are_possibilities
              consistency
              formula_consistent_def
              formula_maximal_consistency
              formula_maximally_consistent_extension
              possibilities_def
              set_deduction_base_theory
              mem_Collect_eq
              of_nat_0
              of_nat_0_le_iff,
            metis \<lozenge> \<dagger> le_antisym not_less not_less_eq_eq of_nat_less_iff)
    }
    moreover
    {
      fix bets :: "('a bet_offer) list"
      fix s :: "'a \<Rightarrow> bool"
      have "settle s bets \<le> length bets"
        unfolding settle_def settle_bet_def
        by (induct bets, auto)
    }
    ultimately show False
      by (metis \<dagger> not_less_eq_eq of_nat_le_iff)
  qed
next
  fix x y
  assume A: "(\<exists>p\<in>possibilities. \<pi> p bets = x) \<and> (\<forall>q\<in>possibilities. \<pi> q bets \<le> x)"
  and B: "(\<exists>p\<in>possibilities. \<pi> p bets = y) \<and> (\<forall>q\<in>possibilities. \<pi> q bets \<le> y)"
  from this obtain p\<^sub>x p\<^sub>y where
    "p\<^sub>x \<in> possibilities"
    "p\<^sub>y \<in> possibilities"
    "\<pi> p\<^sub>x bets = x"
    "\<pi> p\<^sub>y bets = y"
    by blast
  with A B have "x \<le> y" "y \<le> x"
    by blast+
  thus "x = y" by linarith
qed

subsection \<open>Bounding Maximum Payoffs Above Using MaxSAT\<close>

text \<open>
  Below, we present our first major theorem: computing an upper bound to a strategy's
  maximum payoff is equivalent to a bounded MaxSAT problem.

  Given a software MaxSAT implementation, a trader can use this equivalence to run a
  program to check whether the way they arrive at their strategies has a bug.

  Note that while the theorem below is formulated using an arbitrary \<open>k\<close> constant, in
  practice users will want to check their strategies are safe by using \<open>k = 0\<close>.
\<close>

theorem (in consistent_classical_logic) coherence_maxsat:
  "  (\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr> asks = asks', bids = bids' \<rparr> \<le> (k :: real))
   = (MaxSAT [bet b . b \<leftarrow> asks'\<^sup>\<sim> @ bids']
        \<le> k - total_price asks' + total_price bids' + length asks')"
  (is "(\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets \<le> k) = (MaxSAT ?props \<le> _ - total_price _ + _ + _)")
proof
  assume "\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets \<le> k"
  let ?P = "\<lambda> x . (\<exists> p \<in> possibilities. \<pi> p ?bets = x)
                       \<and> (\<forall> q \<in> possibilities. \<pi> q ?bets \<le> x)"
  obtain p where
      "possibility p" and
      "\<forall> q \<in> possibilities. \<pi> q ?bets \<le> \<pi> p ?bets"
    using \<open>\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets \<le> k\<close>
          maximum_payoff_existence [of ?bets]
    by (metis possibilities_def mem_Collect_eq)
  hence "?P (\<pi> p ?bets)"
    using possibilities_def by blast
  hence "\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets = \<pi> p ?bets"
    unfolding maximum_payoff_def
    using maximum_payoff_existence [of ?bets]
          the1_equality [where P = ?P and a = "\<pi> p ?bets"]
    by blast

  let ?\<Phi> = "[\<phi> \<leftarrow> ?props. p \<phi>]"

  have "mset ?\<Phi> \<subseteq># mset ?props"
    by(induct ?props,
       auto,
       simp add: subset_mset.add_mono)
  moreover
  have "\<not> (?\<Phi> :\<turnstile> \<bottom>)"
  proof -
    have "set ?\<Phi> \<subseteq> {x. p x}"
      by auto
    hence "\<not> (set ?\<Phi> \<tturnstile> \<bottom>)"
      by (meson
            \<open>possibility p\<close>
            possibilities_are_MCS [of p]
            formula_consistent_def
            formula_maximally_consistent_set_def_def
            maximally_consistent_set_def
            list_deduction_monotonic
            set_deduction_def)
    thus ?thesis
      using set_deduction_def by blast
  qed
  moreover
  {
    fix \<Psi>
    assume "mset \<Psi> \<subseteq># mset ?props" and "\<not> \<Psi> :\<turnstile> \<bottom>"
    from this obtain \<Omega>\<^sub>\<Psi> where "MCS \<Omega>\<^sub>\<Psi>" and "set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>"
      by (meson
            formula_consistent_def
            formula_maximal_consistency
            formula_maximally_consistent_extension
            list_deduction_monotonic
            set_deduction_def)
    let ?q = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Psi>"
    have "possibility ?q"
      using \<open>MCS \<Omega>\<^sub>\<Psi>\<close> MCSs_are_possibilities by blast
    hence "\<pi> ?q ?bets \<le> \<pi> p ?bets"
      using \<open>\<forall>q\<in>possibilities. \<pi> q ?bets \<le> \<pi> p ?bets\<close>
            possibilities_def
      by blast
    let ?c = "total_price asks' - total_price bids' - length asks'"
    have "settle ?q (asks'\<^sup>\<sim> @ bids') + ?c \<le> settle p (asks'\<^sup>\<sim> @ bids') + ?c"
      using \<open>\<pi> ?q ?bets \<le> \<pi> p ?bets\<close>
            \<open>possibility p\<close>
            bid_revenue_equivalence [of p asks' bids']
            \<open>possibility ?q\<close>
            bid_revenue_equivalence [of ?q asks' bids']
      by linarith
    hence "settle ?q (asks'\<^sup>\<sim> @ bids') \<le> settle p (asks'\<^sup>\<sim> @ bids')"
      by linarith
    let ?\<Psi>' = "[\<phi> \<leftarrow> ?props. ?q \<phi>]"
    have "length ?\<Psi>' \<le> length ?\<Phi>"
      using \<open>settle ?q (asks'\<^sup>\<sim> @ bids') \<le> settle p (asks'\<^sup>\<sim> @ bids')\<close>
      unfolding settle_alt_def
      by simp
    moreover
    have "length \<Psi> \<le> length ?\<Psi>'"
    proof -
      have "mset [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<subseteq># mset ?\<Psi>'"
      proof -
        {
          fix props :: "'a list"
          have "\<forall> \<Psi>. \<forall> \<Omega>.
                  mset \<Psi> \<subseteq># mset props
                    \<longrightarrow> mset [\<psi> \<leftarrow> \<Psi>. \<psi> \<in> \<Omega>] \<subseteq># mset [\<phi> \<leftarrow> props. \<phi> \<in> \<Omega>]"
            by (simp add: multiset_filter_mono)
        }
        thus ?thesis
          using \<open>mset \<Psi> \<subseteq># mset ?props\<close> by blast
      qed
      hence "length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>] \<le> length ?\<Psi>'"
        by (metis
              (no_types, lifting)
              length_sub_mset
              mset_eq_length
              nat_less_le
              not_le)
      moreover have "length \<Psi> = length [\<psi> \<leftarrow> \<Psi>. ?q \<psi>]"
        using \<open>set \<Psi> \<subseteq> \<Omega>\<^sub>\<Psi>\<close>
        by (induct \<Psi>, simp+)
      ultimately show ?thesis by linarith
    qed
    ultimately have "length \<Psi> \<le> length ?\<Phi>" by linarith
  }
  ultimately have "?\<Phi> \<in> \<M> ?props \<bottom>"
    unfolding relative_maximals_def
    by blast
  hence "MaxSAT ?props = length ?\<Phi>"
    using relative_MaxSAT_intro by presburger
  hence "MaxSAT ?props = settle p (asks'\<^sup>\<sim> @ bids')"
    unfolding settle_alt_def
    by simp
  thus "MaxSAT ?props
          \<le> k - total_price asks' + total_price bids' + length asks'"
    using bid_revenue_equivalence [of p asks' bids']
          \<open>\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets \<le> k\<close>
          \<open>\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets = \<pi> p ?bets\<close>
          \<open>possibility p\<close>
    by linarith
next
  let ?c = "- total_price asks' + total_price bids' + length asks'"
  assume "MaxSAT ?props
            \<le> k - total_price asks' + total_price bids' + length asks'"
  from this obtain \<Phi> where "\<Phi> \<in> \<M> ?props \<bottom>" and "length \<Phi> \<le> k + ?c"
    using
      consistency
      relative_MaxSAT_intro
      relative_maximals_existence
    by fastforce
  hence "\<not> \<Phi> :\<turnstile> \<bottom>"
    using relative_maximals_def by blast
  from this obtain \<Omega>\<^sub>\<Phi> where "MCS \<Omega>\<^sub>\<Phi>" and "set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>"
    by (meson
          formula_consistent_def
          formula_maximal_consistency
          formula_maximally_consistent_extension
          list_deduction_monotonic
          set_deduction_def)
  let ?p = "\<lambda>\<phi> . \<phi> \<in> \<Omega>\<^sub>\<Phi>"
  have "possibility ?p"
    using \<open>MCS \<Omega>\<^sub>\<Phi>\<close> MCSs_are_possibilities by blast
  have "mset \<Phi> \<subseteq># mset ?props"
    using \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close> relative_maximals_def by blast
  have "mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]"
    by (metis
          \<open>mset \<Phi> \<subseteq># mset ?props\<close>
          \<open>set \<Phi> \<subseteq> \<Omega>\<^sub>\<Phi>\<close>
          filter_True
          mset_filter
          multiset_filter_mono
          subset_code(1))
  have "mset \<Phi> = mset [ b \<leftarrow> ?props. ?p b]"
  proof (rule ccontr)
    assume "mset \<Phi> \<noteq> mset [ b \<leftarrow> ?props. ?p b]"
    hence "length \<Phi> < length [ b \<leftarrow> ?props. ?p b]"
      using
        \<open>mset \<Phi> \<subseteq># mset [ b \<leftarrow> ?props. ?p b]\<close>
        length_sub_mset not_less
      by blast
    moreover
    have "\<not> [ b \<leftarrow> ?props. ?p b] :\<turnstile> \<bottom>"
      by (metis
            IntE
            \<open>MCS \<Omega>\<^sub>\<Phi>\<close>
            inter_set_filter
            formula_consistent_def
            formula_maximally_consistent_set_def_def
            maximally_consistent_set_def
            set_deduction_def
            subsetI)
    hence "length [ b \<leftarrow> ?props. ?p b] \<le> length \<Phi>"
      by (metis
            (mono_tags, lifting)
            \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close>
            relative_maximals_def [of ?props \<bottom>]
            mem_Collect_eq
            mset_filter
            multiset_filter_subset)
    ultimately show "False"
      using not_le by blast
  qed
  hence "length \<Phi> = settle ?p (asks'\<^sup>\<sim> @ bids')"
    unfolding settle_alt_def
    using mset_eq_length
    by metis
  hence "settle ?p (asks'\<^sup>\<sim> @ bids') \<le> k + ?c"
    using \<open>length \<Phi> \<le> k + ?c\<close> by linarith
  hence "\<pi> ?p ?bets \<le> k"
    using \<open>possibility ?p\<close>
          bid_revenue_equivalence [of ?p asks' bids']
          \<open>length \<Phi> \<le> k + ?c\<close>
          \<open>length \<Phi> = settle ?p (asks'\<^sup>\<sim> @ bids')\<close>
    by linarith
  have "\<forall> q \<in> possibilities. \<pi> q ?bets \<le> \<pi> ?p ?bets"
  proof
    {
      fix x :: 'a
      fix P A
      have "x \<in> Set.filter P A \<longleftrightarrow> x \<in> A \<and> P x"
        by (simp add: filter_def)
    }
    note member_filter = this
    fix q
    assume "q \<in> possibilities"
    hence "possibility q" unfolding possibilities_def by auto
    hence "\<not> [ b \<leftarrow> ?props. q b] :\<turnstile> \<bottom>"
      by (metis filter_set
                possibilities_logical_closure
                possibility_def
                set_deduction_def
                mem_Collect_eq
                member_filter
                subsetI)
    hence "length [ b \<leftarrow> ?props. q b] \<le> length \<Phi>"
      by (metis (mono_tags, lifting)
                \<open>\<Phi> \<in> \<M> ?props \<bottom>\<close>
                relative_maximals_def
                mem_Collect_eq
                mset_filter
                multiset_filter_subset)
    hence "settle q (asks'\<^sup>\<sim> @ bids') \<le> length \<Phi>"
      by (metis of_nat_le_iff settle_alt_def)
    thus "\<pi> q ?bets \<le> \<pi> ?p ?bets"
      using bid_revenue_equivalence [OF \<open>possibility ?p\<close>]
            bid_revenue_equivalence [OF \<open>possibility q\<close>]
            \<open>length \<Phi> = settle ?p (asks'\<^sup>\<sim> @ bids')\<close>
      by force
  qed
  have "\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets = \<pi> ?p ?bets"
    unfolding maximum_payoff_def
  proof
    show "(\<exists>p\<in>possibilities. \<pi> p ?bets = \<pi> ?p ?bets)
          \<and> (\<forall>q\<in>possibilities. \<pi> q ?bets \<le> \<pi> ?p ?bets)"
      using \<open>\<forall> q \<in> possibilities. \<pi> q ?bets \<le> \<pi> ?p ?bets\<close>
            \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
  next
    fix n
    assume \<star>: "(\<exists>p\<in>possibilities. \<pi> p ?bets = n)
               \<and> (\<forall>q\<in>possibilities. \<pi> q ?bets \<le> n)"
    from this obtain p where "\<pi> p ?bets = n" and "possibility p"
      using possibilities_def by blast
    hence "\<pi> ?p ?bets \<le> \<pi> p ?bets"
      using \<star> \<open>possibility ?p\<close>
      unfolding possibilities_def
      by blast
    moreover have "\<pi> p ?bets \<le> \<pi> ?p ?bets"
      using \<open>\<forall> q \<in> possibilities. \<pi> q ?bets \<le> \<pi> ?p ?bets\<close>
            \<open>possibility p\<close>
      unfolding possibilities_def
      by blast
    ultimately show "n = \<pi> ?p ?bets" using \<open>\<pi> p ?bets = n\<close> by linarith
  qed
  thus "\<pi>\<^sub>m\<^sub>a\<^sub>x ?bets \<le> k"
    using \<open>\<pi> ?p ?bets \<le> k\<close>
    by auto
qed


section \<open>Probability Inequality Identity Correspondence\<close>

subsection \<open>Introduction\<close>

text \<open>
  In this section, we prove two forms of the probability inequality identity
  correspondence theorem.

  The two forms relate to \<^term>\<open>\<pi>\<^sub>m\<^sub>i\<^sub>n\<close> (i.e., arbitrage strategy determination) and
  \<^term>\<open>\<pi>\<^sub>m\<^sub>a\<^sub>x\<close> (i.e., coherence testing).

  In each case, the form follows from the reduction to bounded MaxSAT previously
  presented, and the reduction of bounded MaxSAT to probability logic, we
  established in
  \<^theory>\<open>Probability_Inequality_Completeness.Probability_Inequality_Completeness\<close>.
\<close>

subsection \<open>Arbitrage Strategies and Minimum Payoff\<close>

text \<open>
  First, we connect checking if a strategy is an arbitrage strategy and probability
  identities.
\<close>

lemma (in consistent_classical_logic) arbitrageur_nonstrict_correspondence:
  "  (k \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> asks = asks', bids = bids' \<rparr>)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + total_price bids' + k
       \<le> (\<Sum>s\<leftarrow>bids'. \<P> (bet s)) + total_price asks')"
  (is "?lhs = _")
proof -
  let ?tot_bs = "total_price bids'" and ?tot_ss = "total_price asks'"
  let ?c = "?tot_bs - ?tot_ss + k"
  have "[bet b . b \<leftarrow> bids'\<^sup>\<sim> @ asks'] = \<^bold>\<sim> [bet s. s \<leftarrow> bids'] @ [bet b. b \<leftarrow> asks']"
    (is "_ = \<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s")
    unfolding negate_bets_def
    by (induct bids', simp+)
  hence
    "?lhs = (\<forall> \<P> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) + ?c \<le> (\<Sum>\<gamma>\<leftarrow>?bid_\<phi>s. \<P> \<gamma>))"
    using
      dirac_inequality_equiv [of ?ask_\<phi>s ?c ?bid_\<phi>s]
      arbitrageur_maxsat [of k asks' bids']
    by force
  moreover
  {
    fix \<P> :: "'a \<Rightarrow> real"
    have "(\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) = (\<Sum>b\<leftarrow>asks'. \<P> (bet b))"
         "(\<Sum>\<gamma>\<leftarrow>?bid_\<phi>s. \<P> \<gamma>) = (\<Sum>s\<leftarrow>bids'. \<P> (bet s))"
      by (simp add: comp_def)+
    hence "  ((\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) + ?c \<le> (\<Sum>\<gamma>\<leftarrow>?bid_\<phi>s. \<P> \<gamma>))
           = (  (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + ?tot_bs + k
              \<le> (\<Sum>s\<leftarrow>bids'. \<P> (bet s)) + ?tot_ss)"
      by linarith
  }
  ultimately show ?thesis
    by (meson dirac_measures_subset dirac_ceiling dirac_collapse subset_eq)
qed


lemma (in consistent_classical_logic) arbitrageur_strict_correspondence:
  "  (k < \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> asks = asks', bids = bids' \<rparr>)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + total_price bids' + k
       < (\<Sum>s\<leftarrow>bids'. \<P> (bet s)) + total_price asks')"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  from this obtain \<epsilon> where "0 < \<epsilon>" "k + \<epsilon> \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr>asks = asks', bids = bids'\<rparr>"
    using less_diff_eq by fastforce
  hence "\<forall>\<P> \<in> probabilities.
            (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + total_price bids' + (k + \<epsilon>)
          \<le> (\<Sum>s\<leftarrow>bids'. \<P> (bet s)) + total_price asks'"
    using arbitrageur_nonstrict_correspondence [of "k + \<epsilon>" asks' bids'] by auto
  thus ?rhs
    using \<open>0 < \<epsilon>\<close> by auto
next
  have "[bet b . b \<leftarrow> bids'\<^sup>\<sim> @ asks'] = \<^bold>\<sim> [bet s. s \<leftarrow> bids'] @ [bet b. b \<leftarrow> asks']"
    (is "_ = \<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s")
    unfolding negate_bets_def
    by (induct bids', simp+)
  {
    fix \<P> :: "'a \<Rightarrow> real"
    have "(\<Sum>b\<leftarrow>asks'. \<P> (bet b)) = (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>)"
         "(\<Sum>b\<leftarrow>bids'. \<P> (bet b)) = (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>)"
      by (induct asks', auto, induct bids', auto)
  }
  note \<star> =  this
  let ?tot_bs = "total_price bids'" and ?tot_ss = "total_price asks'"
  let ?c = "?tot_bs + k - ?tot_ss"
  assume ?rhs
  have "\<forall> \<P> \<in> probabilities. (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + ?c < (\<Sum>s\<leftarrow>bids'. \<P> (bet s))"
    using \<open>?rhs\<close> by fastforce
  hence "\<forall> \<P> \<in> probabilities. (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) + ?c < (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>)"
    using \<star> by auto
  hence "\<forall> \<P> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) + (\<lfloor>?c\<rfloor> + 1) \<le> (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>)"
    using strict_dirac_collapse [of ?ask_\<phi>s ?c ?bid_\<phi>s]
    by auto
  hence "MaxSAT (\<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s) + (\<lfloor>?c\<rfloor> + 1) \<le> length ?bid_\<phi>s"
    by (metis floor_add_int floor_mono floor_of_nat dirac_inequality_equiv)
  hence "MaxSAT (\<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s) + ?c < length ?bid_\<phi>s"
    by linarith
  from this obtain \<epsilon> :: real where
    "0 < \<epsilon>"
    "MaxSAT (\<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s) + (k + \<epsilon>) \<le> ?tot_ss + length bids' - ?tot_bs"
    using less_diff_eq by fastforce
  hence "k + \<epsilon> \<le> \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr>asks = asks', bids = bids'\<rparr>"
    using \<open>[bet b . b \<leftarrow> bids'\<^sup>\<sim> @ asks'] = \<^bold>\<sim> ?bid_\<phi>s @ ?ask_\<phi>s\<close>
          arbitrageur_maxsat [of "k + \<epsilon>" asks' bids']
    by simp
  thus ?lhs
    using \<open>0 < \<epsilon>\<close> by linarith
qed

text \<open>
  Below is our central result regarding checking if a strategy is an arbitrage strategy:

  \<^emph>\<open>A strategy is an arbitrage strategy if and only if there is a corresponding identity
    in probability theory that reflects it.\<close>
\<close>

theorem (in consistent_classical_logic) arbitrageur_correspondence:
  "  (0 < \<pi>\<^sub>m\<^sub>i\<^sub>n \<lparr> asks = asks', bids = bids' \<rparr>)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>asks'. \<P> (bet b)) + total_price bids'
       < (\<Sum>s\<leftarrow>bids'. \<P> (bet s)) + total_price asks')"
  by (simp add: arbitrageur_strict_correspondence)

subsection \<open>Coherence Checking and Maximum Payoff\<close>

text \<open>
  Finally, we show the connection between coherence checking and probability identities.
\<close>

lemma (in consistent_classical_logic) coherence_nonstrict_correspondence:
  "  (\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr> asks = asks', bids = bids' \<rparr> \<le> k)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + total_price asks'
       \<le> (\<Sum>s\<leftarrow>asks'. \<P> (bet s)) + total_price bids' + k)"
  (is "?lhs = _")
proof -
  let ?tot_bs = "total_price bids'" and ?tot_ss = "total_price asks'"
  let ?c = "?tot_ss - ?tot_bs - k"
  have "[bet b . b \<leftarrow> asks'\<^sup>\<sim> @ bids'] = \<^bold>\<sim> [bet s. s \<leftarrow> asks'] @ [bet b. b \<leftarrow> bids']"
    (is "_ = \<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s")
    unfolding negate_bets_def
    by (induct bids', simp+)
  hence
    "?lhs = (\<forall> \<P> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>) + ?c \<le> (\<Sum>\<gamma>\<leftarrow>?ask_\<phi>s. \<P> \<gamma>))"
    using
      dirac_inequality_equiv [of ?bid_\<phi>s ?c ?ask_\<phi>s]
      coherence_maxsat [of asks' bids' k]
    by force
  moreover
  {
    fix \<P> :: "'a \<Rightarrow> real"
    have "(\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>) = (\<Sum>b\<leftarrow>asks'. \<P> (bet b))"
         "(\<Sum>\<gamma>\<leftarrow>?bid_\<phi>s. \<P> \<gamma>) = (\<Sum>s\<leftarrow>bids'. \<P> (bet s))"
      by (simp add: comp_def)+
    hence "  ((\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>) + ?c \<le> (\<Sum>\<gamma>\<leftarrow>?ask_\<phi>s. \<P> \<gamma>))
           = ((\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + ?tot_ss
                 \<le> (\<Sum>s\<leftarrow>asks'. \<P> (bet s)) + ?tot_bs + k)"
      by linarith
  }
  ultimately show ?thesis
    by (meson dirac_measures_subset dirac_ceiling dirac_collapse subset_eq)
qed

lemma (in consistent_classical_logic) coherence_strict_correspondence:
  "  (\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr> asks = asks', bids = bids' \<rparr> < k)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + total_price asks'
       < (\<Sum>s\<leftarrow>asks'. \<P> (bet s)) + total_price bids' + k)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  from this obtain \<epsilon> where "0 < \<epsilon>" "\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr>asks = asks', bids = bids'\<rparr> + \<epsilon> \<le> k"
    using less_diff_eq by fastforce
  hence "\<forall>\<P> \<in> probabilities.
              (\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + total_price asks' + \<epsilon>
           \<le> (\<Sum>s\<leftarrow>asks'. \<P> (bet s)) + total_price bids' + k"
    using coherence_nonstrict_correspondence [of asks' bids' "k - \<epsilon>"] by auto
  thus ?rhs
    using \<open>0 < \<epsilon>\<close> by auto
next
  have "[bet b . b \<leftarrow> asks'\<^sup>\<sim> @ bids'] = \<^bold>\<sim> [bet s. s \<leftarrow> asks'] @ [bet b. b \<leftarrow> bids']"
    (is "_ = \<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s")
    unfolding negate_bets_def
    by (induct bids', simp+)
  {
    fix \<P> :: "'a \<Rightarrow> real"
    have "(\<Sum>b\<leftarrow>asks'. \<P> (bet b)) = (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>)"
         "(\<Sum>b\<leftarrow>bids'. \<P> (bet b)) = (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>)"
      by (induct asks', auto, induct bids', auto)
  }
  note \<star> =  this
  let ?tot_bs = "total_price bids'" and ?tot_ss = "total_price asks'"
  let ?c = "?tot_ss - ?tot_bs - k"
  assume ?rhs
  have "\<forall> \<P> \<in> probabilities. (\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + ?c < (\<Sum>s\<leftarrow>asks'. \<P> (bet s))"
    using \<open>?rhs\<close> by fastforce
  hence "\<forall> \<P> \<in> probabilities. (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>) + ?c < (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>)"
    using \<star> by auto
  hence "\<forall> \<P> \<in> dirac_measures. (\<Sum>\<phi>\<leftarrow>?bid_\<phi>s. \<P> \<phi>) + (\<lfloor>?c\<rfloor> + 1) \<le> (\<Sum>\<phi>\<leftarrow>?ask_\<phi>s. \<P> \<phi>)"
    using strict_dirac_collapse [of ?bid_\<phi>s ?c ?ask_\<phi>s]
    by auto
  hence "MaxSAT (\<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s) + (\<lfloor>?c\<rfloor> + 1) \<le> length ?ask_\<phi>s"
    by (metis floor_add_int floor_mono floor_of_nat dirac_inequality_equiv)
  hence "MaxSAT (\<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s) + ?c < length ?ask_\<phi>s"
    by linarith
  from this obtain \<epsilon> :: real where
    "0 < \<epsilon>"
    "MaxSAT (\<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s) + ?c + \<epsilon> \<le> length asks'"
    using less_diff_eq by fastforce
  hence "\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr>asks = asks', bids = bids'\<rparr> \<le> k - \<epsilon> "
    using \<open>[bet b . b \<leftarrow> asks'\<^sup>\<sim> @ bids'] = \<^bold>\<sim> ?ask_\<phi>s @ ?bid_\<phi>s\<close>
          coherence_maxsat [of asks' bids' "k - \<epsilon>"]
    by auto
  thus ?lhs using \<open>0 < \<epsilon>\<close> by linarith
qed

text \<open>
  Below is our central result regarding coherence testing:

  \<^emph>\<open>A strategy is incoherent if and only if there is a corresponding identity in
    probability theory that reflects it.\<close>
\<close>

theorem (in consistent_classical_logic) coherence_correspondence:
  "  (\<pi>\<^sub>m\<^sub>a\<^sub>x \<lparr> asks = asks', bids = bids' \<rparr> < 0)
   = (\<forall> \<P> \<in> probabilities.
         (\<Sum>b\<leftarrow>bids'. \<P> (bet b)) + total_price asks'
       < (\<Sum>s\<leftarrow>asks'. \<P> (bet s)) + total_price bids')"
  using coherence_strict_correspondence by force

no_notation Probability_Inequality_Completeness.relative_maximals (\<open>\<M>\<close>)

end
