theory Risk_Free_Lending
  imports
    Complex_Main
    "HOL-Cardinals.Cardinals"
begin

section \<open>Accounts \label{sec:accounts}\<close>

text \<open>We model accounts as functions from \<^typ>\<open>nat\<close> to \<^typ>\<open>real\<close> with
      \<^emph>\<open>finite support\<close>.\<close>

text \<open>Index @{term [show_types] "0 :: nat"} corresponds to an account's
      \<^emph>\<open>cash\<close> reserve (see \S\ref{sec:cash} for details).\<close>

text \<open>An index greater than \<^term>\<open>0::nat\<close> may be regarded as corresponding to
      a financial product. Such financial products are similar to \<^emph>\<open>notes\<close>.
      Our notes are intended to be as easy to use for exchange as cash.
      Positive values are debited. Negative values are credited.\<close>

text \<open>We refer to our new financial products as \<^emph>\<open>risk-free loans\<close>, because
      they may be regarded as 0\% APY loans that bear interest for the debtor.
      They are \<^emph>\<open>risk-free\<close> because we prove a \<^emph>\<open>safety\<close> theorem for them.
      Our safety theorem proves no account will ``be in the red'', with more
      credited loans than debited loans, provided an invariant is maintained.
      We call this invariant \<^emph>\<open>strictly solvent\<close>. See \S\ref{sec:bulk-update}
      for   details on our safety proof.\<close>

text \<open>Each risk-free loan index corresponds to a progressively shorter
      \<^emph>\<open>loan period\<close>. Informally, a loan period is the time it takes for 99\%
      of a loan to be returned given a \<^emph>\<open>rate function\<close> \<^term>\<open>\<rho>\<close>. Rate
      functions are introduced in \S\ref{sec:update}.\<close>

text \<open>It is unnecessary to track counter-party obligations so we do not.
      See \S\ref{subsec:balanced-ledgers} and \S\ref{subsec:transfers} for
      details.\<close>

typedef account = "(fin_support 0 UNIV) :: (nat \<Rightarrow> real) set"
proof -
  have "(\<lambda> _ . 0) \<in> fin_support 0 UNIV"
    unfolding fin_support_def support_def
    by simp
  thus "\<exists>x :: nat \<Rightarrow> real. x \<in> fin_support 0 UNIV" by fastforce
qed

text \<open>The type definition for \<^typ>\<open>account\<close> automatically generates two
      functions: @{term [show_types] "Rep_account"} and
      @{term [show_types] "Rep_account"}. \<^term>\<open>Rep_account\<close> is a left inverse
      of \<^term>\<open>Abs_account\<close>. For convenience we introduce the following
      shorthand notation:\<close>

notation Rep_account ("\<pi>")
notation Abs_account ("\<iota>")

text \<open>Accounts form an Abelian group. \<^emph>\<open>Summing\<close> accounts will be helpful in
      expressing how all credited and debited loans can cancel across a
      ledger. This is done in \S\ref{subsec:balanced-ledgers}.\<close>

text \<open>It is also helpful to think of an account as a transferable quantity.
      Transferring subtracts values under indexes from one account and adds
      them to another. Transfers are presented in \S\ref{subsec:transfers}.\<close>

instantiation account :: ab_group_add
begin

definition "0 = \<iota> (\<lambda> _ . 0)"
definition "- \<alpha> = \<iota> (\<lambda> n . - \<pi> \<alpha> n)"
definition "\<alpha>\<^sub>1 + \<alpha>\<^sub>2 = \<iota> (\<lambda> n. \<pi> \<alpha>\<^sub>1 n + \<pi> \<alpha>\<^sub>2 n)"
definition "(\<alpha>\<^sub>1 :: account) - \<alpha>\<^sub>2 = \<alpha>\<^sub>1 + - \<alpha>\<^sub>2"

lemma Rep_account_zero [simp]: "\<pi> 0 = (\<lambda> _ . 0)"
proof -
  have "(\<lambda> _ . 0) \<in> fin_support 0 UNIV"
    unfolding fin_support_def support_def
    by simp
  thus ?thesis
    unfolding zero_account_def
    using Abs_account_inverse by blast
qed

lemma Rep_account_uminus [simp]:
  "\<pi> (- \<alpha>) = (\<lambda> n . - \<pi> \<alpha> n)"
proof -
  have "\<pi> \<alpha> \<in> fin_support 0 UNIV"
    using Rep_account by blast
  hence "(\<lambda>x. - \<pi> \<alpha> x) \<in> fin_support 0 UNIV"
    unfolding fin_support_def support_def
    by force
  thus ?thesis
    unfolding uminus_account_def
    using Abs_account_inverse by blast
qed

lemma fin_support_closed_under_addition:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<in> fin_support 0 A"
  and "g \<in> fin_support 0 A"
  shows "(\<lambda> x . f x + g x) \<in> fin_support 0 A"
  using assms
  unfolding fin_support_def support_def
  by (metis (mono_tags) mem_Collect_eq sum.finite_Collect_op)

lemma Rep_account_plus [simp]:
  "\<pi> (\<alpha>\<^sub>1 + \<alpha>\<^sub>2) = (\<lambda> n. \<pi> \<alpha>\<^sub>1 n + \<pi> \<alpha>\<^sub>2 n)"
  unfolding plus_account_def
  by (metis (full_types)
        Abs_account_cases
        Abs_account_inverse
        fin_support_closed_under_addition)

instance
proof(standard)
  fix a b c :: account
  have "\<forall>n. \<pi> (a + b) n + \<pi> c n = \<pi> a n + \<pi> (b + c) n"
    using Rep_account_plus plus_account_def
    by auto
  thus "a + b + c = a + (b + c)"
    unfolding plus_account_def
    by force
next
  fix a b :: account
  show "a + b = b + a"
    unfolding plus_account_def
    by (simp add: add.commute)
next
  fix a :: account
  show "0 + a = a"
    unfolding plus_account_def Rep_account_zero
    by (simp add: Rep_account_inverse)
next
  fix a :: account
  show "- a + a = 0"
    unfolding plus_account_def zero_account_def Rep_account_uminus
    by (simp add: Abs_account_inverse)
next
  fix a b :: account
  show "a - b = a + - b"
    using minus_account_def by blast
qed

end

section \<open>Strictly Solvent\<close>

text \<open>An account is \<^emph>\<open>strictly solvent\<close> when, for every loan period, the sum of
      all the debited and credited loans for longer periods is positive.
      This implies that the \<^emph>\<open>net asset value\<close> for the account is positive.
      The net asset value is the sum of all of the credit and debit in the
      account. We prove \<open>strictly_solvent \<alpha> \<Longrightarrow> 0 \<le> net_asset_value \<alpha>\<close> in
      \S\ref{subsubsec:net-asset-value-properties}.\<close>

definition strictly_solvent :: "account \<Rightarrow> bool" where
  "strictly_solvent \<alpha> \<equiv> \<forall> n . 0 \<le> (\<Sum> i\<le>n . \<pi> \<alpha> i)"

lemma additive_strictly_solvent:
  assumes "strictly_solvent \<alpha>\<^sub>1" and "strictly_solvent \<alpha>\<^sub>2"
  shows "strictly_solvent (\<alpha>\<^sub>1 + \<alpha>\<^sub>2)"
  using assms Rep_account_plus
  unfolding strictly_solvent_def plus_account_def
  by (simp add: Abs_account_inverse sum.distrib)

text \<open>The notion of strictly solvent generalizes to a partial order, making
      \<^typ>\<open>account\<close> an ordered Abelian group.\<close>

instantiation account :: ordered_ab_group_add
begin

definition less_eq_account :: "account \<Rightarrow> account \<Rightarrow> bool" where
  "less_eq_account \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<equiv> \<forall> n . (\<Sum> i\<le>n . \<pi> \<alpha>\<^sub>1 i) \<le> (\<Sum> i\<le>n . \<pi> \<alpha>\<^sub>2 i)"

definition less_account :: "account \<Rightarrow> account \<Rightarrow> bool" where
  "less_account \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<equiv> (\<alpha>\<^sub>1 \<le> \<alpha>\<^sub>2 \<and> \<not> \<alpha>\<^sub>2 \<le> \<alpha>\<^sub>1)"

instance
proof(standard)
  fix x y :: account
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_account_def ..
next
  fix x :: account
  show "x \<le> x"
    unfolding less_eq_account_def by auto
next
  fix x y z :: account
  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z"
    unfolding less_eq_account_def
    by (meson order_trans)
next
  fix x y :: account
  assume "x \<le> y" and "y \<le> x"
  hence \<star>: "\<forall> n . (\<Sum> i\<le>n . \<pi> x i) = (\<Sum> i\<le>n . \<pi> y i)"
    unfolding less_eq_account_def
    using dual_order.antisym by blast
  {
    fix n
    have "\<pi> x n = \<pi> y n"
    proof (cases "n = 0")
      case True
      then show ?thesis using \<star>
        by (metis
              atMost_0
              empty_iff
              finite.intros(1)
              group_cancel.rule0
              sum.empty sum.insert)
    next
      case False
      from this obtain m where
        "n = m + 1"
        by (metis Nat.add_0_right Suc_eq_plus1 add_eq_if)
      have "(\<Sum> i\<le>n . \<pi> x i) = (\<Sum> i\<le>n . \<pi> y i)"
        using \<star> by auto
      hence
        "(\<Sum> i\<le>m . \<pi> x i) + \<pi> x n =
         (\<Sum> i\<le>m . \<pi> y i) + \<pi> y n"
        using \<open>n = m + 1\<close>
        by simp
      moreover have "(\<Sum> i\<le>m . \<pi> x i) = (\<Sum> i\<le>m . \<pi> y i)"
        using \<star> by auto
      ultimately show ?thesis by linarith
    qed
  }
  hence "\<pi> x = \<pi> y" by auto
  thus "x = y"
    by (metis Rep_account_inverse)
next
  fix x y z :: account
  assume "x \<le> y"
  {
    fix n :: nat
    have
      "(\<Sum> i\<le>n . \<pi> (z + x) i) =
       (\<Sum> i\<le>n . \<pi> z i) + (\<Sum> i\<le>n . \<pi> x i)"
    and
      "(\<Sum> i\<le>n . \<pi> (z + y) i) =
       (\<Sum> i\<le>n . \<pi> z i) + (\<Sum> i\<le>n . \<pi> y i)"
      unfolding Rep_account_plus
      by (simp add: sum.distrib)+
    moreover have "(\<Sum> i\<le>n . \<pi> x i) \<le> (\<Sum> i\<le>n . \<pi> y i)"
      using \<open>x \<le> y\<close>
      unfolding less_eq_account_def by blast
    ultimately have
      "(\<Sum> i\<le>n . \<pi> (z + x) i) \<le> (\<Sum> i\<le>n . \<pi> (z + y) i)"
      by linarith
  }
  thus "z + x \<le> z + y"
    unfolding
      less_eq_account_def by auto
qed
end

text \<open>An account is strictly solvent exactly when it is
      \<^emph>\<open>greater than or equal to\<close> @{term [show_types] "0 :: account"},
      according to the partial order just defined.\<close>

lemma strictly_solvent_alt_def: "strictly_solvent \<alpha> = (0 \<le> \<alpha>)"
  unfolding
    strictly_solvent_def
    less_eq_account_def
  using zero_account_def
  by force

section \<open>Cash \label{sec:cash}\<close>

text \<open>The \<^emph>\<open>cash reserve\<close> in an account is the value under index 0.\<close>

text \<open>Cash is treated with distinction. For instance it grows with interest
      (see \S\ref{sec:interest}). When we turn to balanced ledgers in
      \S\ref{subsec:balanced-ledgers}, we will see that cash is the only
      quantity that does not cancel out.\<close>

definition cash_reserve :: "account \<Rightarrow> real" where
  "cash_reserve \<alpha> = \<pi> \<alpha> 0"

text \<open>If \<open>\<alpha>\<close> is strictly solvent then it has non-negative cash reserves.\<close>

lemma strictly_solvent_non_negative_cash:
  assumes "strictly_solvent \<alpha>"
  shows "0 \<le> cash_reserve \<alpha>"
  using assms
  unfolding strictly_solvent_def cash_reserve_def
  by (metis
        atMost_0
        empty_iff
        finite.emptyI
        group_cancel.rule0
        sum.empty
        sum.insert)

text \<open>An account consists of \<^emph>\<open>just cash\<close> when it has no other credit or debit
      other than under the first index.\<close>

definition just_cash :: "real \<Rightarrow> account" where
  "just_cash c = \<iota> (\<lambda> n . if n = 0 then c else 0)"

lemma Rep_account_just_cash [simp]:
  "\<pi> (just_cash c) = (\<lambda> n . if n = 0 then c else 0)"
proof(cases "c = 0")
  case True
  hence "just_cash c = 0"
    unfolding just_cash_def zero_account_def
    by force
  then show ?thesis
    using Rep_account_zero True by force
next
  case False
  hence "finite (support 0 UNIV (\<lambda> n :: nat . if n = 0 then c else 0))"
    unfolding support_def
    by auto
  hence "(\<lambda> n :: nat . if n = 0 then c else 0) \<in> fin_support 0 UNIV"
    unfolding fin_support_def
    by blast
  then show ?thesis
    unfolding just_cash_def
    using Abs_account_inverse by auto
qed

section \<open>Ledgers\<close>

text \<open>We model a \<^emph>\<open>ledger\<close> as a function from an index type \<^typ>\<open>'a\<close> to
      an \<^typ>\<open>account\<close>. A ledger could be thought of as an \<^emph>\<open>indexed set\<close> of
      accounts.\<close>

type_synonym 'a ledger = "'a \<Rightarrow> account"

subsection \<open>Balanced Ledgers \label{subsec:balanced-ledgers}\<close>

text \<open>We say a ledger is \<^emph>\<open>balanced\<close> when all of the debited and credited
      loans cancel, and all that is left is just cash.\<close>

text \<open>Conceptually, given a balanced ledger we are justified in not tracking
      counter-party obligations.\<close>

definition (in finite) balanced :: "'a ledger \<Rightarrow> real \<Rightarrow> bool" where
  "balanced \<L> c \<equiv> (\<Sum> a \<in> UNIV. \<L> a) = just_cash c"

text \<open>Provided the total cash is non-negative, a balanced ledger is a special
      case of a ledger which is globally strictly solvent.\<close>

lemma balanced_strictly_solvent:
  assumes "0 \<le> c" and "balanced \<L> c"
  shows "strictly_solvent (\<Sum> a \<in> UNIV. \<L> a)"
  using assms
  unfolding balanced_def strictly_solvent_def
  by simp

lemma (in finite) finite_Rep_account_ledger [simp]:
  "\<pi> (\<Sum> a \<in> (A :: 'a set). \<L> a) n = (\<Sum> a \<in> A. \<pi> (\<L> a) n)"
  using finite
  by (induct A rule: finite_induct, auto)

text \<open>An alternate definition of balanced is that the \<^term>\<open>cash_reserve\<close>
      for each account sums to \<open>c\<close>, and all of the other credited and debited
      assets cancels out.\<close>

lemma (in finite) balanced_alt_def:
  "balanced \<L> c =
     ((\<Sum> a \<in> UNIV. cash_reserve (\<L> a)) = c
      \<and> (\<forall> n > 0. (\<Sum> a \<in> UNIV. \<pi> (\<L> a) n) = 0))"
  (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  hence "(\<Sum> a \<in> UNIV. cash_reserve (\<L> a)) = c"
    unfolding balanced_def cash_reserve_def
    by (metis Rep_account_just_cash finite_Rep_account_ledger)
  moreover
  {
    fix n :: "nat"
    assume "n > 0"
    with \<open>?lhs\<close> have "(\<Sum> a \<in> UNIV. \<pi> (\<L> a) n) = 0"
      unfolding balanced_def
      by (metis
            Rep_account_just_cash
            less_nat_zero_code
            finite_Rep_account_ledger)
  }
  ultimately show ?rhs by auto
next
  assume ?rhs
  have "cash_reserve (just_cash c) = c"
    unfolding cash_reserve_def
    using Rep_account_just_cash
    by presburger
  also have "... = (\<Sum>a\<in>UNIV. cash_reserve (\<L> a))" using \<open>?rhs\<close> by auto
  finally have
    "cash_reserve (\<Sum> a \<in> UNIV. \<L> a) = cash_reserve (just_cash c)"
    unfolding cash_reserve_def
    by auto
  moreover
  {
    fix n :: "nat"
    assume "n > 0"
    hence "\<pi> (\<Sum> a \<in> UNIV. \<L> a) n = 0" using \<open>?rhs\<close> by auto
    hence "\<pi> (\<Sum> a \<in> UNIV. \<L> a) n = \<pi> (just_cash c) n"
      unfolding Rep_account_just_cash using \<open>n > 0\<close> by auto
  }
  ultimately have
    "\<forall> n . \<pi> (\<Sum> a \<in> UNIV. \<L> a) n = \<pi> (just_cash c) n"
    unfolding cash_reserve_def
    by (metis gr_zeroI)
  hence "\<pi> (\<Sum> a \<in> UNIV. \<L> a) = \<pi> (just_cash c)"
    by auto
  thus ?lhs
    unfolding balanced_def
    using Rep_account_inject
    by blast
qed

subsection \<open>Transfers \label{subsec:transfers}\<close>

text \<open>A \<^emph>\<open>transfer amount\<close> is the same as an \<^typ>\<open>account\<close>. It is just a
      function from \<^typ>\<open>nat\<close> to \<^typ>\<open>real\<close> with finite support.\<close>

type_synonym transfer_amount = "account"

text \<open>When transferring between accounts in a ledger we make use of the
      Abelian group operations defined in \S\ref{sec:accounts}.\<close>

definition transfer :: "'a ledger \<Rightarrow> transfer_amount \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a ledger" where
  "transfer \<L> \<tau> a b x = (if a = b then \<L> x
                             else if x = a then \<L> a - \<tau>
                             else if x = b then \<L> b + \<tau>
                             else \<L> x)"

text \<open>Transferring from an account to itself is a no-op.\<close>

lemma transfer_collapse:
  "transfer \<L> \<tau> a a = \<L>"
  unfolding transfer_def by auto

text \<open>After a transfer, the sum totals of all credited and debited assets are
      preserved.\<close>

lemma (in finite) sum_transfer_equiv:
  fixes x y :: "'a"
  shows "(\<Sum> a \<in> UNIV. \<L> a) = (\<Sum> a \<in> UNIV. transfer \<L> \<tau> x y a)"
  (is "_ = (\<Sum> a \<in> UNIV. ?\<L>' a)")
proof (cases "x = y")
  case True
  show ?thesis
    unfolding \<open>x = y\<close> transfer_collapse ..
next
  case False
  let ?sum_\<L> = "(\<Sum> a \<in> UNIV - {x,y}. \<L> a)"
  let ?sum_\<L>' = "(\<Sum> a \<in> UNIV - {x,y}. ?\<L>' a)"
  have "\<forall> a \<in> UNIV - {x,y}. ?\<L>' a = \<L> a "
    by (simp add: transfer_def)
  hence "?sum_\<L>' = ?sum_\<L>"
    by (meson sum.cong)
  have "{x,y} \<subseteq> UNIV" by auto
  have "(\<Sum> a \<in> UNIV. ?\<L>' a) = ?sum_\<L>' + (\<Sum> a \<in> {x,y}. ?\<L>' a)"
    using finite_UNIV sum.subset_diff [OF \<open>{x,y} \<subseteq> UNIV\<close>]
    by fastforce
  also have "... = ?sum_\<L>' + ?\<L>' x + ?\<L>' y"
    using
      \<open>x \<noteq> y\<close>
      finite
      Diff_empty
      Diff_insert_absorb
      Diff_subset
      group_cancel.add1
      insert_absorb
      sum.subset_diff
    by (simp add: insert_Diff_if)
  also have "... = ?sum_\<L>' + \<L> x - \<tau> + \<L> y + \<tau>"
    unfolding transfer_def
    using \<open>x \<noteq> y\<close>
    by auto
  also have "... = ?sum_\<L>' + \<L> x + \<L> y"
    by simp
  also have "... = ?sum_\<L> + \<L> x + \<L> y"
    unfolding \<open>?sum_\<L>' = ?sum_\<L>\<close> ..
  also have "... = ?sum_\<L> + (\<Sum> a \<in> {x,y}. \<L> a)"
    using
      \<open>x \<noteq> y\<close>
      finite
      Diff_empty
      Diff_insert_absorb
      Diff_subset
      group_cancel.add1
      insert_absorb
      sum.subset_diff
    by (simp add: insert_Diff_if)
  ultimately show ?thesis
    by (metis local.finite sum.subset_diff top_greatest)
qed

text \<open>Since the sum totals of all credited and debited assets are preserved
      after transfer, a ledger is balanced if and only if it is balanced after
      transfer.\<close>

lemma (in finite) balanced_transfer:
  "balanced \<L> c = balanced (transfer \<L> \<tau> a b) c"
  unfolding balanced_def
  using sum_transfer_equiv
  by force

text \<open>Similarly, the sum total of a ledger is strictly solvent if and only if
      it is strictly solvent after transfer.\<close>

lemma (in finite) strictly_solvent_transfer:
  fixes x y :: "'a"
  shows "strictly_solvent (\<Sum> a \<in> UNIV. \<L> a) =
           strictly_solvent (\<Sum> a \<in> UNIV. transfer \<L> \<tau> x y a)"
  using sum_transfer_equiv
  by presburger

subsection \<open>The Valid Transfers Protocol\<close>

text \<open>In this section we give a \<^emph>\<open>protocol\<close> for safely transferring value
      from one account to another.\<close>

text \<open>We enforce that every transfer is \<^emph>\<open>valid\<close>. Valid transfers are
      intended to be intuitive. For instance one cannot transfer negative
      cash. Nor is it possible for an account that only has \$50 to loan out
      \$5,000,000.\<close>

text \<open>A transfer is valid just in case the \<^typ>\<open>transfer_amount\<close> is strictly
      solvent and the account being credited the transfer will be strictly
      solvent afterwards.\<close>

definition valid_transfer :: "account \<Rightarrow> transfer_amount \<Rightarrow> bool" where
  "valid_transfer \<alpha> \<tau> = (strictly_solvent \<tau> \<and> strictly_solvent (\<alpha> - \<tau>))"

lemma valid_transfer_alt_def: "valid_transfer \<alpha> \<tau> = (0 \<le> \<tau> \<and> \<tau> \<le> \<alpha>)"
  unfolding valid_transfer_def strictly_solvent_alt_def
  by simp

text \<open>Only strictly solvent accounts can make valid transfers to begin with.\<close>

lemma only_strictly_solvent_accounts_can_transfer:
  assumes "valid_transfer \<alpha> \<tau>"
  shows "strictly_solvent \<alpha>"
  using assms
  unfolding strictly_solvent_alt_def valid_transfer_alt_def
  by auto

text \<open>We may now give a key result: accounts remain strictly solvent given a
      valid transfer.\<close>

theorem strictly_solvent_still_strictly_solvent_after_valid_transfer:
  assumes "valid_transfer (\<L> a) \<tau>"
  and "strictly_solvent (\<L> b)"
  shows
    "strictly_solvent ((transfer \<L> \<tau> a b) a)"
    "strictly_solvent ((transfer \<L> \<tau> a b) b)"
  using assms
  unfolding
    strictly_solvent_alt_def
    valid_transfer_alt_def
    transfer_def
  by (cases "a = b", auto)

subsection \<open>Embedding Conventional Cash-Only Ledgers\<close>

text \<open>We show that in a sense the ledgers presented generalize conventional
      ledgers which only track cash.\<close>

text \<open>An account consisting of just cash is strictly solvent if and only if
      it consists of a non-negative amount of cash.\<close>

lemma strictly_solvent_just_cash_equiv:
  "strictly_solvent (just_cash c) = (0 \<le> c)"
  unfolding strictly_solvent_def
  using Rep_account_just_cash just_cash_def by force

text \<open>An empty account corresponds to @{term [show_types] "0 :: account"};
      the account with no cash or debit or credit.\<close>

lemma zero_account_alt_def: "just_cash 0 = 0"
  unfolding zero_account_def just_cash_def
  by simp

text \<open>Building on @{thm zero_account_alt_def}, we have that \<^term>\<open>just_cash\<close>
      is an embedding into an ordered subgroup. This means that \<^term>\<open>just_cash\<close>
      is an order-preserving group homomorphism from the reals to the universe
      of accounts.\<close>

lemma just_cash_embed: "(a = b) = (just_cash a = just_cash b)"
proof (rule iffI)
  assume "a = b"
  thus "just_cash a = just_cash b"
    by force
next
  assume "just_cash a = just_cash b"
  hence "cash_reserve (just_cash a) = cash_reserve (just_cash b)"
    by presburger
  thus "a = b"
    unfolding Rep_account_just_cash cash_reserve_def
    by auto
qed

lemma partial_nav_just_cash [simp]:
 "(\<Sum> i\<le>n . \<pi> (just_cash a) i) = a"
  unfolding Rep_account_just_cash
  by (induct n, auto)

lemma just_cash_order_embed: "(a \<le> b) = (just_cash a \<le> just_cash b)"
  unfolding less_eq_account_def
  by simp

lemma just_cash_plus [simp]: "just_cash a + just_cash b = just_cash (a + b)"
proof -
  {
    fix x
    have "\<pi> (just_cash a + just_cash b) x = \<pi> (just_cash (a + b)) x"
    proof (cases "x = 0")
      case True
      then show ?thesis
        using Rep_account_just_cash just_cash_def by force
    next
      case False
      then show ?thesis by simp
    qed
  }
  hence "\<pi> (just_cash a + just_cash b) = \<pi> (just_cash (a + b))"
    by auto
  thus ?thesis
    by (metis Rep_account_inverse)
qed

lemma just_cash_uminus [simp]: "- just_cash a = just_cash (- a)"
proof -
  {
    fix x
    have "\<pi> (- just_cash a) x = \<pi> (just_cash (- a)) x"
    proof (cases "x = 0")
      case True
      then show ?thesis
        using Rep_account_just_cash just_cash_def by force
    next
      case False
      then show ?thesis by simp
    qed
  }
  hence "\<pi> (- just_cash a) = \<pi> (just_cash (- a))"
    by auto
  thus ?thesis
    by (metis Rep_account_inverse)
qed

lemma just_cash_subtract [simp]:
  "just_cash a - just_cash b = just_cash (a - b)"
  by (simp add: minus_account_def)

text \<open>Valid transfers as per @{thm valid_transfer_alt_def} collapse into
      inequalities over the real numbers.\<close>

lemma just_cash_valid_transfer:
  "valid_transfer (just_cash c) (just_cash t) = ((0 :: real) \<le> t \<and> t \<le> c)"
  unfolding valid_transfer_alt_def
  by (simp add: less_eq_account_def)

text \<open>Finally a ledger consisting of accounts with only cash is trivially
      \<^term>\<open>balanced\<close>.\<close>

lemma (in finite) just_cash_summation:
  fixes A :: "'a set"
  assumes "\<forall> a \<in> A. \<exists> c . \<L> a = just_cash c"
  shows "\<exists> c . (\<Sum> a \<in> A . \<L> a) = just_cash c"
  using finite assms
  by (induct A rule: finite_induct, auto, metis zero_account_alt_def)

lemma (in finite) just_cash_UNIV_is_balanced:
  assumes "\<forall> a . \<exists> c . \<L> a = just_cash c"
  shows "\<exists> c . balanced \<L> c"
    unfolding balanced_def
    using
      assms
      just_cash_summation [where A=UNIV]
    by simp

section \<open>Interest \label{sec:interest}\<close>

text \<open>In this section we discuss how to calculate the interest accrued by
      an account for a period. This is done by looking at the sum of all of
      the credit and debit in an account. This sum is called the
      \<^emph>\<open>net asset value\<close> of an account.\<close>

subsection \<open>Net Asset Value \label{subsec:net-asset-value}\<close>

text \<open>The net asset value of an account is the sum of all of the non-zero
      entries. Since accounts have finite support this sum is always well
      defined.\<close>

definition net_asset_value :: "account \<Rightarrow> real" where
  "net_asset_value \<alpha> = (\<Sum> i | \<pi> \<alpha> i \<noteq> 0 . \<pi> \<alpha> i)"

subsubsection \<open>The Shortest Period for Credited \& Debited Assets in an
               Account\<close>

text \<open>Higher indexes for an account correspond to shorter loan periods.
      Since accounts only have a finite number of entries, it makes sense to
      talk about the \<^emph>\<open>shortest\<close> period an account has an entry for. The net
      asset value for an account has a simpler expression in terms of that
      account's shortest period.\<close>

definition shortest_period :: "account \<Rightarrow> nat" where
  "shortest_period \<alpha> =
    (if (\<forall> i. \<pi> \<alpha> i = 0)
     then 0
     else Max {i . \<pi> \<alpha> i \<noteq> 0})"

lemma shortest_period_uminus:
  "shortest_period (- \<alpha>) = shortest_period \<alpha>"
  unfolding shortest_period_def
  using Rep_account_uminus uminus_account_def
  by force

lemma finite_account_support:
  "finite {i . \<pi> \<alpha> i \<noteq> 0}"
proof -
  have "\<pi> \<alpha> \<in> fin_support 0 UNIV"
    by (simp add: Rep_account)
  thus ?thesis
    unfolding fin_support_def support_def
    by fastforce
qed

lemma shortest_period_plus:
  "shortest_period (\<alpha> + \<beta>) \<le> max (shortest_period \<alpha>) (shortest_period \<beta>)"
  (is "_ \<le> ?MAX")
proof (cases "\<forall> i . \<pi> (\<alpha> + \<beta>) i = 0")
  case True
  then show ?thesis unfolding shortest_period_def by auto
next
  case False
  have "shortest_period \<alpha> \<le> ?MAX" and "shortest_period \<beta> \<le> ?MAX"
    by auto
  moreover
  have "\<forall> i > shortest_period \<alpha> . \<pi> \<alpha> i = 0"
  and "\<forall> i > shortest_period \<beta> . \<pi> \<beta> i = 0"
    unfolding shortest_period_def
    using finite_account_support Max.coboundedI leD Collect_cong
    by auto
  ultimately
  have "\<forall> i > ?MAX . \<pi> \<alpha> i = 0"
  and "\<forall> i > ?MAX . \<pi> \<beta> i = 0"
    by simp+
  hence "\<forall> i > ?MAX . \<pi> (\<alpha> + \<beta>) i = 0"
    by simp
  hence "\<forall> i . \<pi> (\<alpha> + \<beta>) i \<noteq> 0 \<longrightarrow> i \<le> ?MAX"
    by (meson not_le)
  thus ?thesis
    unfolding shortest_period_def
    using
      finite_account_support [where \<alpha> = "\<alpha> + \<beta>"]
      False
    by simp
qed

lemma shortest_period_\<pi>:
  assumes "\<pi> \<alpha> i \<noteq> 0"
  shows "\<pi> \<alpha> (shortest_period \<alpha>) \<noteq> 0"
proof -
  let ?support = "{i . \<pi> \<alpha> i \<noteq> 0}"
  have A: "finite ?support"
    using finite_account_support by blast
  have B: "?support \<noteq> {}" using assms by auto
  have "shortest_period \<alpha> = Max ?support"
    using assms
    unfolding shortest_period_def
    by auto
  have "shortest_period \<alpha> \<in> ?support"
    unfolding \<open>shortest_period \<alpha> = Max ?support\<close>
    using Max_in [OF A B] by auto
  thus ?thesis
    by auto
qed

lemma shortest_period_bound:
  assumes "\<pi> \<alpha> i \<noteq> 0"
  shows "i \<le> shortest_period \<alpha>"
proof -
  let ?support = "{i . \<pi> \<alpha> i \<noteq> 0}"
  have "shortest_period \<alpha> = Max ?support"
    using assms
    unfolding shortest_period_def
    by auto
  have "shortest_period \<alpha> \<in> ?support"
    using assms shortest_period_\<pi> by force
  thus ?thesis
    unfolding \<open>shortest_period \<alpha> = Max ?support\<close>
    by (simp add: assms finite_account_support)
qed

text \<open>Using \<^term>\<open>shortest_period\<close> we may give an alternate definition for
     \<^term>\<open>net_asset_value\<close>.\<close>

lemma net_asset_value_alt_def:
  "net_asset_value \<alpha> = (\<Sum> i \<le> shortest_period \<alpha>. \<pi> \<alpha> i)"
proof -
  let ?support = "{i . \<pi> \<alpha> i \<noteq> 0}"
  {
    fix k
    have "(\<Sum> i | i \<le> k \<and> \<pi> \<alpha> i \<noteq> 0 . \<pi> \<alpha> i) = (\<Sum> i \<le> k. \<pi> \<alpha> i)"
    proof (induct k)
      case 0
      thus ?case
      proof (cases "\<pi> \<alpha> 0 = 0")
        case True
        then show ?thesis
          by fastforce
      next
        case False
        {
          fix i
          have "(i \<le> 0 \<and> \<pi> \<alpha> i \<noteq> 0) = (i \<le> 0)"
            using False
            by blast
        }
        hence "(\<Sum> i | i \<le> 0 \<and> \<pi> \<alpha> i \<noteq> 0. \<pi> \<alpha> i) =
                 (\<Sum>i | i \<le> 0. \<pi> \<alpha> i)"
          by presburger
        also have "... = (\<Sum>i \<le> 0. \<pi> \<alpha> i)"
          by simp
        ultimately show ?thesis
          by simp
      qed
    next
      case (Suc k)
      then show ?case
      proof (cases "\<pi> \<alpha> (Suc k) = 0")
        case True
        {
          fix i
          have "(i \<le> Suc k \<and> \<pi> \<alpha> i \<noteq> 0) =
                  (i \<le> k \<and> \<pi> \<alpha> i \<noteq> 0)"
            using True le_Suc_eq by blast
        }
        hence "(\<Sum>i | i \<le> Suc k \<and> \<pi> \<alpha> i \<noteq> 0. \<pi> \<alpha> i) =
                 (\<Sum>i | i \<le> k \<and> \<pi> \<alpha> i \<noteq> 0. \<pi> \<alpha> i)"
          by presburger
        also have "... = (\<Sum> i \<le> k. \<pi> \<alpha> i)"
          using Suc by blast
        ultimately show ?thesis using True
          by simp
      next
        let ?A = "{i . i \<le> Suc k \<and> \<pi> \<alpha> i \<noteq> 0}"
        let ?A' = "{i . i \<le> k \<and> \<pi> \<alpha> i \<noteq> 0}"
        case False
        hence "?A = {i . (i \<le> k \<and> \<pi> \<alpha> i \<noteq> 0) \<or> i = Suc k}"
          by auto
        hence "?A = ?A' \<union> {i . i = Suc k}"
          by (simp add: Collect_disj_eq)
        hence \<star>: "?A = ?A' \<union> {Suc k}"
          by simp
        hence \<heartsuit>: "finite (?A' \<union> {Suc k})"
          using finite_nat_set_iff_bounded_le
          by blast
        hence
          "(\<Sum>i | i \<le> Suc k \<and> \<pi> \<alpha> i \<noteq> 0. \<pi> \<alpha> i) =
             (\<Sum> i \<in> ?A' \<union> {Suc k}. \<pi> \<alpha> i)"
          unfolding \<star>
          by auto
        also have "... = (\<Sum> i \<in> ?A'. \<pi> \<alpha> i) + (\<Sum> i \<in> {Suc k}. \<pi> \<alpha> i)"
          using \<heartsuit>
          by force
        also have "... = (\<Sum> i \<in> ?A'. \<pi> \<alpha> i) + \<pi> \<alpha> (Suc k)"
          by simp
        ultimately show ?thesis
          by (simp add: Suc)
      qed
    qed
  }
  hence \<dagger>:
    "(\<Sum>i | i \<le> shortest_period \<alpha> \<and> \<pi> \<alpha> i \<noteq> 0. \<pi> \<alpha> i) =
            (\<Sum> i \<le> shortest_period \<alpha>. \<pi> \<alpha> i)"
    by auto
  {
    fix i
    have "(i \<le> shortest_period \<alpha> \<and> \<pi> \<alpha> i \<noteq> 0) = (\<pi> \<alpha> i \<noteq> 0)"
      using shortest_period_bound by blast
  }
  note \<bullet> = this
  show ?thesis
    using \<dagger>
    unfolding \<bullet> net_asset_value_def
    by blast
qed

lemma greater_than_shortest_period_zero:
  assumes "shortest_period \<alpha> < m"
  shows "\<pi> \<alpha> m = 0"
proof -
  let ?support = "{i . \<pi> \<alpha> i \<noteq> 0}"
  have "\<forall> i \<in> ?support . i \<le> shortest_period \<alpha>"
    by (simp add: finite_account_support shortest_period_def)
  then show ?thesis
    using assms
    by (meson CollectI leD)
qed

text \<open>An account's \<^term>\<open>net_asset_value\<close> does not change when summing beyond
      its \<^term>\<open>shortest_period\<close>. This is helpful when computing aggregate
      net asset values across multiple accounts.\<close>

lemma net_asset_value_shortest_period_ge:
  assumes "shortest_period \<alpha> \<le> n"
  shows "net_asset_value \<alpha> = (\<Sum> i \<le> n. \<pi> \<alpha> i)"
proof (cases "shortest_period \<alpha> = n")
  case True
  then show ?thesis
    unfolding net_asset_value_alt_def by auto
next
  case False
  hence "shortest_period \<alpha> < n" using assms by auto
  hence "(\<Sum> i=shortest_period \<alpha> + 1.. n. \<pi> \<alpha> i) = 0"
    (is "?\<Sigma>extra = 0")
    using greater_than_shortest_period_zero
    by auto
  moreover have "(\<Sum> i \<le> n. \<pi> \<alpha> i) =
                  (\<Sum> i \<le> shortest_period \<alpha>. \<pi> \<alpha> i) + ?\<Sigma>extra"
    (is "?lhs = ?\<Sigma>shortest_period + _")
    by (metis
          \<open>shortest_period \<alpha> < n\<close>
          Suc_eq_plus1
          less_imp_add_positive
          sum_up_index_split)
  ultimately have "?lhs = ?\<Sigma>shortest_period"
    by linarith
  then show ?thesis
    unfolding net_asset_value_alt_def by auto
qed

subsubsection \<open>Net Asset Value Properties \label{subsubsec:net-asset-value-properties}\<close>

text \<open>In this section we explore how \<^term>\<open>net_asset_value\<close> forms an
      order-preserving group homomorphism from the universe of accounts to the
      real numbers.\<close>

text \<open>We first observe that \<^term>\<open>strictly_solvent\<close> implies the more
      conventional notion of solvent, where an account's net asset value is
      non-negative.\<close>

lemma strictly_solvent_net_asset_value:
  assumes "strictly_solvent \<alpha>"
  shows "0 \<le> net_asset_value \<alpha>"
  using assms strictly_solvent_def net_asset_value_alt_def by auto

text \<open>Next we observe that \<^term>\<open>net_asset_value\<close> is a order preserving
      group homomorphism from the universe of accounts to \<^term>\<open>real\<close>.\<close>

lemma net_asset_value_zero [simp]: "net_asset_value 0 = 0"
  unfolding net_asset_value_alt_def
  using zero_account_def by force

lemma net_asset_value_mono:
  assumes "\<alpha> \<le> \<beta>"
  shows "net_asset_value \<alpha> \<le> net_asset_value \<beta>"
proof -
  let ?r = "max (shortest_period \<alpha>) (shortest_period \<beta>)"
  have "shortest_period \<alpha> \<le> ?r" and "shortest_period \<beta> \<le> ?r" by auto
  hence "net_asset_value \<alpha> = (\<Sum> i \<le> ?r. \<pi> \<alpha> i)"
  and "net_asset_value \<beta> = (\<Sum> i \<le> ?r. \<pi> \<beta> i)"
    using net_asset_value_shortest_period_ge by presburger+
  thus ?thesis using assms unfolding less_eq_account_def by auto
qed

lemma net_asset_value_uminus: "net_asset_value (- \<alpha>) = - net_asset_value \<alpha>"
  unfolding
    net_asset_value_alt_def
    shortest_period_uminus
    Rep_account_uminus
  by (simp add: sum_negf)

lemma net_asset_value_plus:
  "net_asset_value (\<alpha> + \<beta>) = net_asset_value \<alpha> + net_asset_value \<beta>"
  (is "?lhs = ?\<Sigma>\<alpha> + ?\<Sigma>\<beta>")
proof -
  let ?r = "max (shortest_period \<alpha>) (shortest_period \<beta>)"
  have  A: "shortest_period (\<alpha> + \<beta>) \<le> ?r"
    and B: "shortest_period \<alpha> \<le> ?r"
    and C: "shortest_period \<beta> \<le> ?r"
    using shortest_period_plus by presburger+
  have "?lhs = (\<Sum> i \<le> ?r. \<pi> (\<alpha> + \<beta>) i)"
    using net_asset_value_shortest_period_ge [OF A] .
  also have "\<dots> = (\<Sum> i \<le> ?r. \<pi> \<alpha> i + \<pi> \<beta> i)"
    using Rep_account_plus by presburger
  ultimately show ?thesis
    using
      net_asset_value_shortest_period_ge [OF B]
      net_asset_value_shortest_period_ge [OF C]
    by (simp add: sum.distrib)
qed

lemma net_asset_value_minus:
  "net_asset_value (\<alpha> - \<beta>) = net_asset_value \<alpha> - net_asset_value \<beta>"
  using additive.diff additive.intro net_asset_value_plus by blast

text \<open>Finally we observe that \<^term>\<open>just_cash\<close> is the right inverse of
      \<^term>\<open>net_asset_value\<close>.\<close>

lemma net_asset_value_just_cash_left_inverse:
  "net_asset_value (just_cash c) = c"
  using net_asset_value_alt_def partial_nav_just_cash by presburger

subsection \<open>Distributing Interest\<close>

text \<open>We next show that the total interest accrued for a ledger at
      distribution does not change when one account makes a transfer to
      another.\<close>

definition (in finite) total_interest :: "'a ledger \<Rightarrow> real \<Rightarrow> real"
  where "total_interest \<L> i = (\<Sum> a \<in> UNIV. i * net_asset_value (\<L> a))"

lemma (in finite) total_interest_transfer:
  "total_interest (transfer \<L> \<tau> a b) i = total_interest \<L> i"
  (is "total_interest ?\<L>' i = _")
proof (cases "a = b")
  case True
  show ?thesis
    unfolding \<open>a = b\<close> transfer_collapse ..
next
  case False
  have "total_interest ?\<L>' i = (\<Sum> a \<in> UNIV . i * net_asset_value (?\<L>' a))"
    unfolding total_interest_def ..
  also have "\<dots> = (\<Sum> a \<in> UNIV - {a, b} \<union> {a,b}. i * net_asset_value (?\<L>' a))"
    by (metis Un_Diff_cancel2 Un_UNIV_left)
  also have "\<dots> = (\<Sum> a \<in> UNIV - {a, b}. i * net_asset_value (?\<L>' a)) +
                   i * net_asset_value (?\<L>' a) + i * net_asset_value (?\<L>' b)"
    (is "_ = ?\<Sigma> + _ + _")
    using \<open>a \<noteq> b\<close>
    by simp
  also have "\<dots> = ?\<Sigma> +
                    i * net_asset_value (\<L> a - \<tau>) +
                    i * net_asset_value (\<L> b + \<tau>)"
    unfolding transfer_def
    using \<open>a \<noteq> b\<close>
    by auto
  also have "\<dots> = ?\<Sigma> +
                  i * net_asset_value (\<L> a) +
                  i * net_asset_value (- \<tau>) +
                  i * net_asset_value (\<L> b) +
                  i * net_asset_value \<tau>"
    unfolding minus_account_def net_asset_value_plus
    by (simp add: distrib_left)
  also have "\<dots> = ?\<Sigma> +
                  i * net_asset_value (\<L> a) +
                  i * net_asset_value (\<L> b)"
    unfolding net_asset_value_uminus
    by linarith
  also have "\<dots> = (\<Sum> a \<in> UNIV - {a, b}. i * net_asset_value (\<L> a)) +
                  i * net_asset_value (\<L> a) +
                  i * net_asset_value (\<L> b)"
    unfolding transfer_def
    using \<open>a \<noteq> b\<close>
    by force
  also have "\<dots> = (\<Sum> a \<in> UNIV - {a, b} \<union> {a,b}. i * net_asset_value (\<L> a))"
    using \<open>a \<noteq> b\<close> by force
  ultimately show ?thesis
    unfolding total_interest_def
    by (metis Diff_partition Un_commute top_greatest)
qed

section \<open>Update \label{sec:update}\<close>

text \<open>Periodically the ledger is \<^emph>\<open>updated\<close>. When this happens interest is
      distributed and loans are returned. Each time loans are returned, a
      fixed fraction of each loan for each period is returned.\<close>

text \<open>The fixed fraction for returned loans is given by a \<^emph>\<open>rate function\<close>.
      We denote rate functions with @{term [show_types] "\<rho> :: nat \<Rightarrow> real"}.
      In principle this function obeys the rules:
       \<^item> \<^term>\<open>\<rho> (0::nat) = (0 ::real)\<close> -- Cash is not returned.
       \<^item> \<^term>\<open>\<forall>n ::nat . \<rho> n < (1 :: real)\<close> -- The fraction of a loan
         returned never exceeds 1.
       \<^item> \<^term>\<open>\<forall>n m :: nat. n < m \<longrightarrow> ((\<rho> n) :: real) < \<rho> m\<close> -- Higher indexes
         correspond to shorter loan periods. This in turn corresponds to
         a higher fraction of loans returned at update for higher indexes.
     \<close>

text \<open>In practice, rate functions determine the time it takes for 99\%
      of the loan to be returned. However, the presentation here abstracts
      away from time. In \S\ref{subsec:bulk-update-closed-form} we establish
      a closed form for updating. This permits for a production implementation
      to efficiently (albeit \<^emph>\<open>lazily\<close>) update ever \<^emph>\<open>millisecond\<close> if so
      desired.\<close>

definition return_loans :: "(nat \<Rightarrow> real) \<Rightarrow> account \<Rightarrow> account" where
  "return_loans \<rho> \<alpha> = \<iota> (\<lambda> n . (1 - \<rho> n) * \<pi> \<alpha> n)"

lemma Rep_account_return_loans [simp]:
  "\<pi> (return_loans \<rho> \<alpha>) = (\<lambda> n . (1 - \<rho> n) * \<pi> \<alpha> n)"
proof -
  have "(support 0 UNIV (\<lambda> n . (1 - \<rho> n) * \<pi> \<alpha> n)) \<subseteq>
          (support 0 UNIV (\<pi> \<alpha>))"
    unfolding support_def
    by (simp add: Collect_mono)
  moreover have "finite (support 0 UNIV (\<pi> \<alpha>))"
    using Rep_account
    unfolding fin_support_def by auto
  ultimately have "finite (support 0 UNIV (\<lambda> n . (1 - \<rho> n) * \<pi> \<alpha> n))"
    using infinite_super by blast
  hence "(\<lambda> n . (1 - \<rho> n) * \<pi> \<alpha> n) \<in> fin_support 0 UNIV"
    unfolding fin_support_def by auto
  thus ?thesis
    using
      Rep_account
      Abs_account_inject
      Rep_account_inverse
      return_loans_def
    by auto
qed

text \<open>As discussed, updating an account involves distributing interest and
      returning its credited and debited loans.\<close>

definition update_account :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> account \<Rightarrow> account" where
  "update_account \<rho> i \<alpha> = just_cash (i * net_asset_value \<alpha>) + return_loans \<rho> \<alpha>"

definition update_ledger :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> 'a ledger \<Rightarrow> 'a ledger"
  where
    "update_ledger \<rho> i \<L> a = update_account \<rho> i (\<L> a)"

subsection \<open>Update Preserves Ledger Balance\<close>

text \<open>A key theorem is that if all credit and debit in a ledger cancel,
      they will continue to cancel after update. In this sense the monetary
      supply grows with the interest rate, but is otherwise conserved.\<close>

text \<open>A consequence of this theorem is that while counter-party obligations
      are not explicitly tracked by the ledger, these obligations are fulfilled
      as funds are returned by the protocol.\<close>

definition shortest_ledger_period :: "'a ledger \<Rightarrow> nat" where
  "shortest_ledger_period \<L> = Max (image shortest_period (range \<L>))"

lemma (in finite) shortest_ledger_period_bound:
  fixes \<L> :: "'a ledger"
  shows "shortest_period (\<L> a) \<le> shortest_ledger_period \<L>"
proof -
  {
    fix \<alpha> :: account
    fix S :: "account set"
    assume "finite S" and "\<alpha> \<in> S"
    hence "shortest_period \<alpha> \<le> Max (shortest_period ` S)"
    proof (induct S rule: finite_induct)
      case empty
      then show ?case by auto
      next
      case (insert \<beta> S)
      then show ?case
      proof (cases "\<alpha> = \<beta>")
        case True
        then show ?thesis
          by (simp add: insert.hyps(1))
      next
        case False
        hence "\<alpha> \<in> S"
          using insert.prems by fastforce
        then show ?thesis
          by (meson
                Max_ge
                finite_imageI
                finite_insert
                imageI
                insert.hyps(1)
                insert.prems)
      qed
    qed
  }
  moreover
  have "finite (range \<L>)"
    by force
  ultimately show ?thesis
    by (simp add: shortest_ledger_period_def)
qed

theorem (in finite) update_balanced:
  assumes "\<rho> 0 = 0" and "\<forall>n. \<rho> n < 1" and "0 \<le> i"
  shows "balanced \<L> c = balanced (update_ledger \<rho> i \<L>) ((1 + i) * c)"
    (is "_ = balanced ?\<L>' ((1 + i) * c)")
proof
  assume "balanced \<L> c"
  have "\<forall>n>0. (\<Sum>a\<in>UNIV. \<pi> (?\<L>' a) n) = 0"
  proof (rule allI, rule impI)
    fix n :: nat
    assume "n > 0"
    {
      fix a
      let ?\<alpha>' = "\<lambda>n. (1 - \<rho> n) * \<pi> (\<L> a) n"
      have "\<pi> (?\<L>' a) n = ?\<alpha>' n"
        unfolding
          update_ledger_def
          update_account_def
          Rep_account_plus
          Rep_account_just_cash
          Rep_account_return_loans
        using plus_account_def \<open>n > 0\<close>
        by simp
    }
    hence "(\<Sum>a\<in>UNIV. \<pi> (?\<L>' a) n) =
             (1 - \<rho> n) * (\<Sum>a\<in>UNIV. \<pi> (\<L> a) n)"
      using finite_UNIV
      by (metis (mono_tags, lifting) sum.cong sum_distrib_left)
    thus "(\<Sum>a\<in>UNIV. \<pi> (?\<L>' a) n) = 0"
      using \<open>0 < n\<close> \<open>balanced \<L> c\<close> local.balanced_alt_def by force
  qed
  moreover
  {
    fix S :: "'a set"
    let ?\<omega> = "shortest_ledger_period \<L>"
    assume "(\<Sum>a\<in>S. cash_reserve (\<L> a)) = c"
    and "\<forall>n>0. (\<Sum>a\<in>S. \<pi> (\<L> a) n) = 0"
    have "(\<Sum>a\<in>S. cash_reserve (?\<L>' a)) =
              (\<Sum>a\<in>S. i * (\<Sum> n \<le> ?\<omega>. \<pi> (\<L> a) n) +
                   cash_reserve (\<L> a))"
    using finite
    proof (induct S arbitrary: c rule: finite_induct)
      case empty
      then show ?case
        by auto
    next
      case (insert x S)
      have "(\<Sum>a\<in>insert x S. cash_reserve (?\<L>' a)) =
              (\<Sum>a\<in>insert x S. i * (\<Sum> n \<le> ?\<omega>. \<pi> (\<L> a) n) +
                    cash_reserve (\<L> a))"
        unfolding update_ledger_def update_account_def cash_reserve_def
        by (simp add: \<open>\<rho> 0 = 0\<close>,
            metis (no_types)
                  shortest_ledger_period_bound
                  net_asset_value_shortest_period_ge)
      thus ?case .
    qed
    also have "... = (\<Sum>a\<in>S. i * (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n) +
                          i * cash_reserve (\<L> a) + cash_reserve (\<L> a))"
      unfolding cash_reserve_def
      by (simp add:
            add.commute
            distrib_left
            sum.atMost_shift
            sum_bounds_lt_plus1)
    also have "... = (\<Sum>a\<in>S. i * (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n) +
                         (1 + i) * cash_reserve (\<L> a))"
      using finite
      by (induct S rule: finite_induct, auto, simp add: distrib_right)
    also have "... = i * (\<Sum>a\<in>S. (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n)) +
                        (1 + i) * (\<Sum>a\<in>S. cash_reserve (\<L> a))"
      by (simp add: sum.distrib sum_distrib_left)
    also have "... = i * (\<Sum> n = 1 .. ?\<omega>. (\<Sum>a\<in>S. \<pi> (\<L> a) n)) +
                        (1 + i) * c"
      using \<open>(\<Sum>a\<in>S. cash_reserve (\<L> a)) = c\<close> sum.swap by force
    finally have "(\<Sum>a\<in>S. cash_reserve (?\<L>' a)) = c * (1 + i)"
      using \<open>\<forall>n>0. (\<Sum>a\<in>S. \<pi> (\<L> a) n) = 0\<close>
      by simp
  }
  hence "(\<Sum>a\<in>UNIV. cash_reserve (?\<L>' a)) = c * (1 + i)"
    using \<open>balanced \<L> c\<close>
    unfolding balanced_alt_def
    by fastforce
  ultimately show "balanced ?\<L>' ((1 + i) * c)"
    unfolding balanced_alt_def
    by auto
next
  assume "balanced ?\<L>' ((1 + i) * c)"
  have \<star>: "\<forall>n>0. (\<Sum>a\<in>UNIV. \<pi> (\<L> a) n) = 0"
  proof (rule allI, rule impI)
    fix n :: nat
    assume "n > 0"
    hence "0 = (\<Sum>a\<in>UNIV. \<pi> (?\<L>' a) n)"
      using \<open>balanced ?\<L>' ((1 + i) * c)\<close>
      unfolding balanced_alt_def
      by auto
    also have "\<dots> = (\<Sum>a\<in>UNIV. (1 - \<rho> n) * \<pi> (\<L> a) n)"
      unfolding
        update_ledger_def
        update_account_def
        Rep_account_return_loans
        Rep_account_just_cash
      using \<open>n > 0\<close>
      by auto
    also have "\<dots> = (1 - \<rho> n) * (\<Sum>a\<in>UNIV. \<pi> (\<L> a) n)"
      by (simp add: sum_distrib_left)
    finally show "(\<Sum>a\<in>UNIV. \<pi> (\<L> a) n) = 0"
      by (metis
            \<open>\<forall> r . \<rho> r < 1\<close>
            diff_gt_0_iff_gt
            less_numeral_extra(3)
            mult_eq_0_iff)
  qed
  moreover
  {
    fix S :: "'a set"
    let ?\<omega> = "shortest_ledger_period \<L>"
    assume "(\<Sum>a\<in>S. cash_reserve (?\<L>' a)) = (1 + i) * c"
    and "\<forall>n>0. (\<Sum>a\<in>S. \<pi> (\<L> a) n) = 0"
    hence "(1 + i) * c = (\<Sum>a\<in>S. cash_reserve (?\<L>' a))"
      by auto
    also have "\<dots> = (\<Sum>a\<in>S. i * (\<Sum> n \<le> ?\<omega>. \<pi> (\<L> a) n) +
                         cash_reserve (\<L> a))"
    using finite
    proof (induct S rule: finite_induct)
      case empty
      then show ?case
        by auto
    next
      case (insert x S)
      have "(\<Sum>a\<in>insert x S. cash_reserve (?\<L>' a)) =
              (\<Sum>a\<in>insert x S.
                  i * (\<Sum> n \<le> ?\<omega>. \<pi> (\<L> a) n) + cash_reserve (\<L> a))"
        unfolding update_ledger_def update_account_def cash_reserve_def
        by (simp add: \<open>\<rho> 0 = 0\<close>,
            metis (no_types)
                  shortest_ledger_period_bound
                  net_asset_value_shortest_period_ge)
      thus ?case .
    qed
    also have "\<dots> = (\<Sum>a\<in>S. i * (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n) +
                               i * cash_reserve (\<L> a) + cash_reserve (\<L> a))"
      unfolding cash_reserve_def
      by (simp add:
            add.commute
            distrib_left
            sum.atMost_shift
            sum_bounds_lt_plus1)
    also have "\<dots> = (\<Sum>a\<in>S. i * (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n) +
                           (1 + i) * cash_reserve (\<L> a))"
      using finite
      by (induct S rule: finite_induct, auto, simp add: distrib_right)
    also have "\<dots> = i * (\<Sum>a\<in>S. (\<Sum> n = 1 .. ?\<omega>. \<pi> (\<L> a) n)) +
                        (1 + i) * (\<Sum>a\<in>S. cash_reserve (\<L> a))"
      by (simp add: sum.distrib sum_distrib_left)
    also have "\<dots> =  i * (\<Sum> n = 1 .. ?\<omega>. (\<Sum>a\<in>S. \<pi> (\<L> a) n)) +
                       (1 + i) * (\<Sum>a\<in>S. cash_reserve (\<L> a))"
      using sum.swap by force
    also have "\<dots> = (1 + i) * (\<Sum>a\<in>S. cash_reserve (\<L> a))"
      using \<open>\<forall>n>0. (\<Sum>a\<in>S. \<pi> (\<L> a) n) = 0\<close>
      by simp
    finally have "c = (\<Sum>a\<in>S. cash_reserve (\<L> a))"
      using \<open>0 \<le> i\<close>
      by force
  }
  hence "(\<Sum>a\<in>UNIV. cash_reserve (\<L> a)) = c"
    unfolding cash_reserve_def
    by (metis
          Rep_account_just_cash
          \<open>balanced ?\<L>' ((1 + i) * c)\<close>
          \<star>
          balanced_def
          finite_Rep_account_ledger)
  ultimately show "balanced \<L> c"
    unfolding balanced_alt_def
    by auto
qed

subsection \<open>Strictly Solvent is Forever Strictly Solvent\<close>

text \<open>The final theorem presented in this section is that if an account is
      strictly solvent, it will still be strictly solvent after update.\<close>

text \<open>This theorem is the key to how the system avoids counter party risk.
      Provided the system enforces that all accounts are strictly solvent and
      transfers are \<^emph>\<open>valid\<close> (as discussed in \S\ref{subsec:transfers}),
      all accounts will remain strictly solvent forever.\<close>

text \<open>We first prove that \<^term>\<open>return_loans\<close> is a group homomorphism.\<close>

text \<open>It is order preserving given certain assumptions.\<close>

lemma return_loans_plus:
  "return_loans \<rho> (\<alpha> + \<beta>) = return_loans \<rho> \<alpha> + return_loans \<rho> \<beta>"
proof -
  let ?\<alpha> = "\<pi> \<alpha>"
  let ?\<beta> = "\<pi> \<beta>"
  let ?\<rho>\<alpha>\<beta> = "\<lambda>n. (1 - \<rho> n) * (?\<alpha> n + ?\<beta> n)"
  let ?\<rho>\<alpha> = "\<lambda>n. (1 - \<rho> n) * ?\<alpha> n"
  let ?\<rho>\<beta> = "\<lambda>n. (1 - \<rho> n) * ?\<beta> n"
  have "support 0 UNIV ?\<rho>\<alpha> \<subseteq> support 0 UNIV ?\<alpha>"
       "support 0 UNIV ?\<rho>\<beta> \<subseteq> support 0 UNIV ?\<beta>"
       "support 0 UNIV ?\<rho>\<alpha>\<beta> \<subseteq> support 0 UNIV ?\<alpha> \<union> support 0 UNIV ?\<beta>"
    unfolding support_def
    by auto
  moreover have
    "?\<alpha> \<in> fin_support 0 UNIV"
    "?\<beta> \<in> fin_support 0 UNIV"
    using Rep_account by force+
  ultimately have \<star>:
    "?\<rho>\<alpha> \<in> fin_support 0 UNIV"
    "?\<rho>\<beta> \<in> fin_support 0 UNIV"
    "?\<rho>\<alpha>\<beta> \<in> fin_support 0 UNIV"
    unfolding fin_support_def
    using finite_subset by auto+
  {
    fix n
    have "\<pi> (return_loans \<rho> (\<alpha> + \<beta>)) n =
          \<pi> (return_loans \<rho> \<alpha> + return_loans \<rho> \<beta>) n"
      unfolding return_loans_def Rep_account_plus
      using \<star> Abs_account_inverse distrib_left by auto
  }
  hence "\<pi> (return_loans \<rho> (\<alpha> + \<beta>)) =
         \<pi> (return_loans \<rho> \<alpha> + return_loans \<rho> \<beta>)"
    by auto
  thus ?thesis
    by (metis Rep_account_inverse)
qed

lemma return_loans_zero [simp]: "return_loans \<rho> 0 = 0"
proof -
  have "(\<lambda>n. (1 - \<rho> n) * 0) = (\<lambda>_. 0)"
    by force
  hence "\<iota> (\<lambda>n. (1 - \<rho> n) * 0) = 0"
    unfolding zero_account_def
    by presburger
  thus ?thesis
    unfolding return_loans_def Rep_account_zero .
qed

lemma return_loans_uminus: "return_loans \<rho> (- \<alpha>) = - return_loans \<rho> \<alpha>"
  by (metis
        add.left_cancel
        diff_self
        minus_account_def
        return_loans_plus
        return_loans_zero)

lemma return_loans_subtract:
  "return_loans \<rho> (\<alpha> - \<beta>) = return_loans \<rho> \<alpha> - return_loans \<rho> \<beta>"
  by (simp add: additive.diff additive_def return_loans_plus)

text \<open>As presented in \S\ref{sec:accounts}, each index corresponds to a
      progressively shorter loan period. This is captured by a monotonicity
      assumption on the rate function @{term [show_types] "\<rho> :: nat \<Rightarrow> real"}.
      In particular, provided \<^term>\<open>\<forall> n . \<rho> n < (1 :: real)\<close> and
      \<^term>\<open>\<forall> n m :: nat . n < m \<longrightarrow> \<rho> n < (\<rho> m :: real)\<close> then we know that
      all outstanding credit is going away faster than loans debited for
      longer periods.\<close>

text \<open>Given the monotonicity assumptions for a rate function
      @{term [show_types] "\<rho> :: nat \<Rightarrow> real"}, we may in turn prove monotonicity
      for \<^term>\<open>return_loans\<close> over \<open>(\<le>)::account \<Rightarrow> account \<Rightarrow> bool\<close>.\<close>

lemma return_loans_mono:
  assumes "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m"
  and "\<alpha> \<le> \<beta>"
  shows "return_loans \<rho> \<alpha> \<le> return_loans \<rho> \<beta>"
proof -
  {
    fix \<alpha> :: account
    assume "0 \<le> \<alpha>"
    {
      fix n :: nat
      let ?\<alpha> = "\<pi> \<alpha>"
      let ?\<rho>\<alpha> = "\<lambda>n. (1 - \<rho> n) * ?\<alpha> n"
      have "\<forall> n . 0 \<le> (\<Sum> i\<le>n . ?\<alpha> i)"
        using \<open>0 \<le> \<alpha>\<close>
        unfolding less_eq_account_def Rep_account_zero
        by simp
      hence "0 \<le> (\<Sum> i\<le>n . ?\<alpha> i)" by auto
      moreover have "(1 - \<rho> n) * (\<Sum> i\<le>n . ?\<alpha> i) \<le> (\<Sum> i\<le>n . ?\<rho>\<alpha> i)"
      proof (induct n)
        case 0
        then show ?case by simp
      next
        case (Suc n)
        have "0 \<le> (1 - \<rho> (Suc n))"
          by (simp add: \<open>\<forall> n . \<rho> n < 1\<close> less_eq_real_def)
        moreover have "(1 - \<rho> (Suc n)) \<le> (1 - \<rho> n)"
          using \<open>\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m\<close>
          by simp
        ultimately have
          "(1 - \<rho> (Suc n)) * (\<Sum> i\<le>n . ?\<alpha> i) \<le> (1 - \<rho> n) * (\<Sum> i\<le>n . ?\<alpha> i)"
          using \<open>\<forall> n . 0 \<le> (\<Sum> i\<le>n . ?\<alpha> i)\<close>
          by (meson le_less mult_mono')
        hence
          "(1 - \<rho> (Suc n)) * (\<Sum> i\<le> Suc n . ?\<alpha> i) \<le>
           (1 - \<rho> n) * (\<Sum> i\<le>n . ?\<alpha> i) + (1 - \<rho> (Suc n)) * (?\<alpha> (Suc n))"
          (is "_ \<le> ?X")
          by (simp add: distrib_left)
        moreover have
          "?X \<le> (\<Sum> i\<le> Suc n . ?\<rho>\<alpha> i)"
          using Suc.hyps by fastforce
        ultimately show ?case by auto
      qed
      moreover have "0 < 1 - \<rho> n"
        by (simp add: \<open>\<forall> n . \<rho> n < 1\<close>)
      ultimately have "0 \<le> (\<Sum> i\<le>n . ?\<rho>\<alpha> i)"
        using dual_order.trans by fastforce
    }
    hence "strictly_solvent (return_loans \<rho> \<alpha>)"
      unfolding strictly_solvent_def Rep_account_return_loans
      by auto
  }
  hence "0 \<le> return_loans \<rho> (\<beta> - \<alpha>)"
    using \<open>\<alpha> \<le> \<beta>\<close>
    by (simp add: strictly_solvent_alt_def)
  thus ?thesis
    by (metis
          add_diff_cancel_left'
          diff_ge_0_iff_ge
          minus_account_def
          return_loans_plus)
qed

lemma return_loans_just_cash:
  assumes "\<rho> 0 = 0"
  shows "return_loans \<rho> (just_cash c) = just_cash c"
proof -
  have "(\<lambda>n. (1 - \<rho> n) * \<pi> (\<iota> (\<lambda>n. if n = 0 then c else 0)) n)
        = (\<lambda>n. if n = 0 then (1 - \<rho> n) * c else 0)"
    using Rep_account_just_cash just_cash_def by force
  also have "\<dots> = (\<lambda>n. if n = 0 then c else 0)"
    using \<open>\<rho> 0 = 0\<close>
    by force
  finally show ?thesis
  unfolding return_loans_def just_cash_def
  by presburger
qed

lemma distribute_interest_plus:
   "just_cash (i * net_asset_value (\<alpha> + \<beta>)) =
      just_cash (i * net_asset_value \<alpha>) +
      just_cash (i * net_asset_value \<beta>)"
  unfolding just_cash_def net_asset_value_plus
  by (metis
        distrib_left
        just_cash_plus
        just_cash_def)

text \<open>We now prove that \<^term>\<open>update_account\<close> is an order-preserving group
      homomorphism just as \<^term>\<open>just_cash\<close>, \<^term>\<open>net_asset_value\<close>, and
      \<^term>\<open>return_loans\<close> are.\<close>

lemma update_account_plus:
  "update_account \<rho> i (\<alpha> + \<beta>) =
     update_account \<rho> i \<alpha> + update_account \<rho> i \<beta>"
  unfolding
    update_account_def
    return_loans_plus
    distribute_interest_plus
  by simp

lemma update_account_zero [simp]: "update_account \<rho> i 0 = 0"
  by (metis add_cancel_right_left update_account_plus)

lemma update_account_uminus:
  "update_account \<rho> i (-\<alpha>) = - update_account \<rho> i \<alpha>"
  unfolding update_account_def
  by (simp add: net_asset_value_uminus return_loans_uminus)

lemma update_account_subtract:
  "update_account \<rho> i (\<alpha> - \<beta>) =
     update_account \<rho> i \<alpha> - update_account \<rho> i \<beta>"
  by (simp add: additive.diff additive.intro update_account_plus)

lemma update_account_mono:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m"
  and "\<alpha> \<le> \<beta>"
  shows "update_account \<rho> i \<alpha> \<le> update_account \<rho> i \<beta>"
proof -
  have "net_asset_value \<alpha> \<le> net_asset_value \<beta>"
    using \<open>\<alpha> \<le> \<beta>\<close> net_asset_value_mono by presburger
  hence "i * net_asset_value \<alpha> \<le> i * net_asset_value \<beta>"
    by (simp add: \<open>0 \<le> i\<close> mult_left_mono)
  hence "just_cash (i * net_asset_value \<alpha>) \<le>
         just_cash (i * net_asset_value \<beta>)"
    by (simp add: just_cash_order_embed)
  moreover
  have "return_loans \<rho> \<alpha> \<le> return_loans \<rho> \<beta>"
    using assms return_loans_mono by presburger
  ultimately show ?thesis unfolding update_account_def
    by (simp add: add_mono)
qed

text \<open>It follows from monotonicity and @{thm update_account_zero [no_vars]} that
      strictly solvent accounts remain strictly solvent after update.\<close>

lemma update_preserves_strictly_solvent:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m"
  and "strictly_solvent \<alpha>"
  shows "strictly_solvent (update_account \<rho> i \<alpha>)"
  using assms
  unfolding strictly_solvent_alt_def
  by (metis update_account_mono update_account_zero)

section \<open>Bulk Update \label{sec:bulk-update}\<close>

text \<open>In this section we demonstrate there exists a closed form for
      bulk-updating an account.\<close>

primrec bulk_update_account ::
   "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> account \<Rightarrow> account"
   where
   "bulk_update_account 0 _ _ \<alpha> = \<alpha>"
 | "bulk_update_account (Suc n) \<rho> i \<alpha> =
      update_account \<rho> i (bulk_update_account n \<rho> i \<alpha>)"

text \<open>As with \<^term>\<open>update_account\<close>, \<^term>\<open>bulk_update_account\<close> is an
      order-preserving group homomorphism.\<close>

text \<open>We now prove that \<^term>\<open>update_account\<close> is an order-preserving group
      homomorphism just as \<^term>\<open>just_cash\<close>, \<^term>\<open>net_asset_value\<close>, and
      \<^term>\<open>return_loans\<close> are.\<close>

lemma bulk_update_account_plus:
  "bulk_update_account n \<rho> i (\<alpha> + \<beta>) =
     bulk_update_account n \<rho> i \<alpha> + bulk_update_account n \<rho> i \<beta>"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using bulk_update_account.simps(2) update_account_plus by presburger
qed

lemma bulk_update_account_zero [simp]: "bulk_update_account n \<rho> i 0 = 0"
  by (metis add_cancel_right_left bulk_update_account_plus)

lemma bulk_update_account_uminus:
  "bulk_update_account n \<rho> i (-\<alpha>) = - bulk_update_account n \<rho> i \<alpha>"
  by (metis add_eq_0_iff bulk_update_account_plus bulk_update_account_zero)


lemma bulk_update_account_subtract:
  "bulk_update_account n \<rho> i (\<alpha> - \<beta>) =
     bulk_update_account n \<rho> i \<alpha> - bulk_update_account n \<rho> i \<beta>"
  by (simp add: additive.diff additive_def bulk_update_account_plus)

lemma bulk_update_account_mono:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m"
  and "\<alpha> \<le> \<beta>"
  shows "bulk_update_account n \<rho> i \<alpha> \<le> bulk_update_account n \<rho> i \<beta>"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using bulk_update_account.simps(2) update_account_mono by presburger
qed

text \<open>In follows from the fact that \<^term>\<open>bulk_update_account\<close> is an
      order-preserving group homomorphism that the update protocol is \<^emph>\<open>safe\<close>.
      Informally this means that provided we enforce every account is strictly
      solvent then no account will ever have negative net asset value
      (ie, be in the red).\<close>

theorem bulk_update_safety:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n \<le> m \<longrightarrow> \<rho> n \<le> \<rho> m"
  and "strictly_solvent \<alpha>"
  shows "0 \<le> net_asset_value (bulk_update_account n \<rho> i \<alpha>)"
  using assms
  by (metis
        bulk_update_account_mono
        bulk_update_account_zero
        strictly_solvent_alt_def
        strictly_solvent_net_asset_value)

subsection \<open>Decomposition\<close>

text \<open>In order to express \<^term>\<open>bulk_update_account\<close> using a closed
      formulation, we first demonstrate how to \<^emph>\<open>decompose\<close> an account
      into a summation of credited and debited loans for different periods.\<close>

definition loan :: "nat \<Rightarrow> real \<Rightarrow> account" ("\<delta>")
  where
    "\<delta> n x = \<iota> (\<lambda> m . if n = m then x else 0)"

lemma loan_just_cash: "\<delta> 0 c = just_cash c"
  unfolding just_cash_def loan_def
  by force

lemma Rep_account_loan [simp]:
  "\<pi> (\<delta> n x) = (\<lambda> m . if n = m then x else 0)"
proof -
  have "(\<lambda> m . if n = m then x else 0) \<in> fin_support 0 UNIV"
    unfolding fin_support_def support_def
    by force
  thus ?thesis
    unfolding loan_def
    using Abs_account_inverse by blast
qed

lemma loan_zero [simp]: "\<delta> n 0 = 0"
  unfolding loan_def
  using zero_account_def by fastforce

lemma shortest_period_loan:
  assumes "c \<noteq> 0"
  shows "shortest_period (\<delta> n c) = n"
  using assms
  unfolding shortest_period_def Rep_account_loan
  by simp

lemma net_asset_value_loan [simp]: "net_asset_value (\<delta> n c) = c"
proof (cases "c = 0")
  case True
  then show ?thesis by simp
next
  case False
  hence "shortest_period (\<delta> n c) = n" using shortest_period_loan by blast
  then show ?thesis unfolding net_asset_value_alt_def by simp
qed

lemma return_loans_loan [simp]: "return_loans \<rho> (\<delta> n c) = \<delta> n ((1 - \<rho> n) * c)"
proof -
  have "return_loans \<rho> (\<delta> n c) =
          \<iota> (\<lambda>na. (if n = na then (1 - \<rho> n) * c else 0))"
    unfolding return_loans_def
    by (metis Rep_account_loan mult.commute mult_zero_left)
  thus ?thesis
    by (simp add: loan_def)
qed

lemma account_decomposition:
  "\<alpha> = (\<Sum> i \<le> shortest_period \<alpha>. \<delta> i (\<pi> \<alpha> i))"
proof -
  let ?p = "shortest_period \<alpha>"
  let ?\<pi>\<alpha> = "\<pi> \<alpha>"
  let ?\<Sigma>\<delta> = "\<Sum> i \<le> ?p. \<delta> i (?\<pi>\<alpha> i)"
  {
    fix n m :: nat
    fix f :: "nat \<Rightarrow> real"
    assume "n > m"
    hence "\<pi> (\<Sum> i \<le> m. \<delta> i (f i)) n = 0"
      by (induct m, simp+)
  }
  note \<bullet> = this
  {
    fix n :: nat
    have "\<pi> ?\<Sigma>\<delta> n = ?\<pi>\<alpha> n"
    proof (cases "n \<le> ?p")
      case True
      {
        fix n m :: nat
        fix f :: "nat \<Rightarrow> real"
        assume "n \<le> m"
        hence "\<pi> (\<Sum> i \<le> m. \<delta> i (f i)) n = f n"
        proof (induct m)
          case 0
          then show ?case by simp
        next
          case (Suc m)
          then show ?case
          proof (cases "n = Suc m")
            case True
            then show ?thesis using \<bullet> by auto
          next
            case False
            hence "n \<le> m"
              using Suc.prems le_Suc_eq by blast
            then show ?thesis
              by (simp add: Suc.hyps)
          qed
        qed
      }
      then show ?thesis using True by auto
    next
      case False
      have "?\<pi>\<alpha> n = 0"
        unfolding shortest_period_def
        using False shortest_period_bound by blast
      thus ?thesis using False \<bullet> by auto
    qed
  }
  thus ?thesis
    by (metis Rep_account_inject ext)
qed

subsection \<open>Simple Transfers\<close>

text \<open>Building on our decomposition, we can understand the necessary and
      sufficient conditions to transfer a loan of \<^term>\<open>\<delta> n c\<close>.\<close>

text \<open>We first give a notion of the \<^emph>\<open>reserves for a period \<open>n\<close>\<close>. This
      characterizes the available funds for a loan of period \<open>n\<close> that an
      account \<open>\<alpha>\<close> possesses.\<close>

definition reserves_for_period :: "account \<Rightarrow> nat \<Rightarrow> real" where
  "reserves_for_period \<alpha> n =
      fold
        min
        [(\<Sum> i\<le>k . \<pi> \<alpha> i) . k \<leftarrow> [n..<shortest_period \<alpha>+1]]
        (\<Sum> i\<le>n . \<pi> \<alpha> i)"

lemma nav_reserves_for_period:
  assumes "shortest_period \<alpha> \<le> n"
  shows "reserves_for_period \<alpha> n = net_asset_value \<alpha>"
proof cases
  assume "shortest_period \<alpha> = n"
  hence "[n..<shortest_period \<alpha>+1] = [n]"
    by simp
  hence "[(\<Sum> i\<le>k . \<pi> \<alpha> i) . k \<leftarrow> [n..<shortest_period \<alpha>+1]] =
           [(\<Sum> i\<le>n . \<pi> \<alpha> i)]"
    by simp
  then show ?thesis
    unfolding reserves_for_period_def
    by (simp add: \<open>shortest_period \<alpha> = n\<close> net_asset_value_alt_def)
next
  assume "shortest_period \<alpha> \<noteq> n"
  hence "shortest_period \<alpha> < n"
    using assms order_le_imp_less_or_eq by blast
  hence "[(\<Sum> i\<le>k . \<pi> \<alpha> k) . k \<leftarrow> [n..<shortest_period \<alpha>+1]] = []"
    by force
  hence "reserves_for_period \<alpha> n = (\<Sum> i\<le>n . \<pi> \<alpha> i)"
    unfolding reserves_for_period_def by auto
  then show ?thesis
    using assms net_asset_value_shortest_period_ge by presburger
qed

lemma reserves_for_period_exists:
  "\<exists>m\<ge>n. reserves_for_period \<alpha> n = (\<Sum> i\<le>m . \<pi> \<alpha> i)
         \<and> (\<forall>u\<ge>n. (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i))"
proof -
  {
    fix j
    have "\<exists>m\<ge>n. (\<Sum> i\<le>m . \<pi> \<alpha> i) =
                  fold
                    min
                    [(\<Sum> i\<le>k . \<pi> \<alpha> i) . k \<leftarrow> [n..<j]]
                    (\<Sum> i\<le>n . \<pi> \<alpha> i)
                 \<and> (\<forall>u\<ge>n. u < j \<longrightarrow> (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i))"
    proof (induct j)
      case 0
      then show ?case by auto
    next
      case (Suc j)
      then show ?case
      proof cases
        assume "j \<le> n"
        thus ?thesis
          by (simp, metis dual_order.refl le_less_Suc_eq)
      next
        assume "\<not>(j \<le> n)"
        hence "n < j" by auto
        obtain m where
          "m \<ge> n"
          "\<forall>u\<ge>n. u < j \<longrightarrow> (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
          "(\<Sum> i\<le>m . \<pi> \<alpha> i) =
                    fold
                      min
                      [(\<Sum> i\<le>k . \<pi> \<alpha> i) . k \<leftarrow> [n..<j]]
                      (\<Sum> i\<le>n . \<pi> \<alpha> i)"
          using Suc by blast
        note \<heartsuit> = this
        hence \<dagger>: "min (\<Sum> i\<le>m . \<pi> \<alpha> i) (\<Sum> i\<le>j . \<pi> \<alpha> i) =
                fold
                  min
                  [(\<Sum> i\<le>k . \<pi> \<alpha> i) . k \<leftarrow> [n..<Suc j]]
                  (\<Sum> i\<le>n . \<pi> \<alpha> i)"
          (is "_ = ?fold")
          using \<open>n < j\<close> by simp
        show ?thesis
        proof cases
          assume "(\<Sum> i\<le>m . \<pi> \<alpha> i) < (\<Sum> i\<le>j . \<pi> \<alpha> i)"
          hence
            "\<forall>u\<ge>n. u < Suc j \<longrightarrow> (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
            by (metis
                  \<heartsuit>(2)
                  dual_order.order_iff_strict
                  less_Suc_eq)
          thus ?thesis
            using \<dagger> \<open>m \<ge> n\<close> by auto
        next
          assume \<star>: "\<not> ((\<Sum> i\<le>m . \<pi> \<alpha> i) < (\<Sum> i\<le>j . \<pi> \<alpha> i))"
          hence
            "\<forall>u\<ge>n. u < j \<longrightarrow> (\<Sum> i\<le>j . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
            using \<heartsuit>(2)
            by auto
          hence
            "\<forall>u\<ge>n. u < Suc j \<longrightarrow> (\<Sum> i\<le>j . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
            by (simp add: less_Suc_eq)
          also have "?fold = (\<Sum> i\<le>j . \<pi> \<alpha> i)"
            using \<dagger> \<star> by linarith
          ultimately show ?thesis
            by (metis \<open>n < j\<close> less_or_eq_imp_le)
        qed
      qed
    qed
  }
  from this obtain m where
      "m \<ge> n"
      "(\<Sum> i\<le>m . \<pi> \<alpha> i) = reserves_for_period \<alpha> n"
      "\<forall>u\<ge>n. u < shortest_period \<alpha> + 1
              \<longrightarrow> (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
    unfolding reserves_for_period_def
    by blast
  note \<diamondsuit> = this
  hence "(\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>shortest_period \<alpha> . \<pi> \<alpha> i)"
    by (metis
          less_add_one
          nav_reserves_for_period
          net_asset_value_alt_def
          nle_le)
  hence "\<forall>u\<ge>shortest_period \<alpha>. (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
    by (metis
          net_asset_value_alt_def
          net_asset_value_shortest_period_ge)
  hence "\<forall>u\<ge>n. (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
    by (metis \<diamondsuit>(3) Suc_eq_plus1 less_Suc_eq linorder_not_le)
  thus ?thesis
    using \<diamondsuit>(1) \<diamondsuit>(2)
    by metis
qed

lemma permissible_loan_converse:
  assumes "strictly_solvent (\<alpha> - \<delta> n c)"
  shows "c \<le> reserves_for_period \<alpha> n"
proof -
  obtain m where
    "n \<le> m"
    "reserves_for_period \<alpha> n = (\<Sum> i\<le>m . \<pi> \<alpha> i)"
    using reserves_for_period_exists by blast
  have "(\<Sum> i\<le>m . \<pi> (\<alpha> - \<delta> n c) i) = (\<Sum> i\<le>m . \<pi> \<alpha> i) - c"
    using \<open>n \<le> m\<close>
  proof (induct m)
    case 0
    hence "n = 0" by auto
    have "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) 0 = \<pi> (\<alpha> - \<delta> n c) 0 + \<pi> (\<delta> n c) 0"
      using Rep_account_plus by presburger
    thus ?case
      unfolding \<open>n = 0\<close>
      by simp
  next
    case (Suc m)
    then show ?case
    proof cases
      assume "n = Suc m"
      hence "m < n" by auto
      hence "(\<Sum> i\<le>m . \<pi> (\<alpha> - \<delta> n c) i) = (\<Sum> i\<le>m . \<pi> \<alpha> i)"
      proof(induct m)
        case 0
        then show ?case
          by (metis
                (no_types, opaque_lifting)
                Rep_account_loan
                Rep_account_plus
                atMost_0 bot_nat_0.not_eq_extremum
                diff_0_right
                diff_add_cancel
                empty_iff
                finite.intros(1)
                sum.empty
                sum.insert)
      next
        case (Suc m)
        hence "m < n" and "n \<noteq> Suc m"
          using Suc_lessD by blast+
        moreover have
          "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) (Suc m) =
              \<pi> (\<alpha> - \<delta> n c) (Suc m) + \<pi> (\<delta> n c) (Suc m)"
          using Rep_account_plus by presburger
        ultimately show ?case by (simp add: Suc.hyps)
      qed
      moreover
      have "\<pi> (\<alpha> - \<delta> (Suc m) c + \<delta> (Suc m) c) (Suc m) =
              \<pi> (\<alpha> - \<delta> (Suc m) c) (Suc m) + \<pi> (\<delta> (Suc m) c) (Suc m)"
        by (meson Rep_account_plus)
      ultimately show ?thesis
        unfolding \<open>n = Suc m\<close>
        by simp
    next
      assume "n \<noteq> Suc m"
      hence "n \<le> m"
        using Suc.prems le_SucE by blast
      have "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) (Suc m) =
              \<pi> (\<alpha> - \<delta> n c) (Suc m) + \<pi> (\<delta> n c) (Suc m)"
        by (meson Rep_account_plus)
      moreover have "0 = (if n = Suc m then c else 0)"
        using \<open>n \<noteq> Suc m\<close> by presburger
      ultimately show ?thesis
        by (simp add: Suc.hyps \<open>n \<le> m\<close>)
    qed
  qed
  hence "0 \<le> (\<Sum> i\<le>m . \<pi> \<alpha> i) - c"
    by (metis assms strictly_solvent_def)
  thus ?thesis
    by (simp add: \<open>reserves_for_period \<alpha> n = sum (\<pi> \<alpha>) {..m}\<close>)
qed

lemma permissible_loan:
  assumes "strictly_solvent \<alpha>"
  shows "strictly_solvent (\<alpha> - \<delta> n c) = (c \<le> reserves_for_period \<alpha> n)"
proof
  assume "strictly_solvent (\<alpha> - \<delta> n c)"
  thus "c \<le> reserves_for_period \<alpha> n"
    using permissible_loan_converse by blast
next
  assume "c \<le> reserves_for_period \<alpha> n"
  {
    fix j
    have "0 \<le> (\<Sum> i\<le>j . \<pi> (\<alpha> - \<delta> n c) i)"
    proof cases
      assume "j < n"
      hence "(\<Sum> i\<le>j . \<pi> (\<alpha> - \<delta> n c) i) = (\<Sum> i\<le>j . \<pi> \<alpha> i)"
      proof (induct j)
        case 0
        then show ?case
          by (simp,
              metis
                Rep_account_loan
                Rep_account_plus
                \<open>j < n\<close>
                add.commute
                add_0
                diff_add_cancel
                gr_implies_not_zero)
      next
        case (Suc j)
        moreover have "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) (Suc j) =
                         \<pi> (\<alpha> - \<delta> n c) (Suc j) + \<pi> (\<delta> n c) (Suc j)"
          using Rep_account_plus by presburger
        ultimately show ?case by simp
      qed
      thus ?thesis
        by (metis assms strictly_solvent_def)
    next
      assume "\<not> (j < n)"
      hence "n \<le> j" by auto
      obtain m where
        "reserves_for_period \<alpha> n = (\<Sum> i\<le>m . \<pi> \<alpha> i)"
        "\<forall>u\<ge>n. (\<Sum> i\<le>m . \<pi> \<alpha> i) \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
        using reserves_for_period_exists by blast
      hence "\<forall>u\<ge>n. c \<le> (\<Sum> i\<le>u . \<pi> \<alpha> i)"
        using \<open>c \<le> reserves_for_period \<alpha> n\<close>
        by auto
      hence "c \<le> (\<Sum> i\<le>j . \<pi> \<alpha> i)"
        using \<open>n \<le> j\<close> by presburger
      hence "0 \<le> (\<Sum> i\<le>j . \<pi> \<alpha> i) - c"
        by force
      moreover have "(\<Sum> i\<le>j . \<pi> \<alpha> i) - c = (\<Sum> i\<le>j . \<pi> (\<alpha> - \<delta> n c) i)"
        using \<open>n \<le> j\<close>
      proof (induct j)
        case 0
        hence "n = 0" by auto
        have "\<pi> (\<alpha> - \<delta> 0 c + \<delta> 0 c) 0 = \<pi> (\<alpha> - \<delta> 0 c) 0 + \<pi> (\<delta> 0 c) 0"
          using Rep_account_plus by presburger
        thus ?case unfolding \<open>n = 0\<close> by simp
      next
        case (Suc j)
        then show ?case
        proof cases
          assume "n = Suc j"
          hence "j < n"
            by blast
          hence "(\<Sum> i\<le>j . \<pi> (\<alpha> - \<delta> n c) i) = (\<Sum> i\<le>j . \<pi> \<alpha> i)"
          proof (induct j)
            case 0
            then show ?case
              by (simp,
                  metis
                    Rep_account_loan
                    Rep_account_plus
                    \<open>j < n\<close>
                    add.commute
                    add_0
                    diff_add_cancel
                    gr_implies_not_zero)
          next
            case (Suc j)
            moreover have "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) (Suc j) =
                             \<pi> (\<alpha> - \<delta> n c) (Suc j) + \<pi> (\<delta> n c) (Suc j)"
              using Rep_account_plus by presburger
            ultimately show ?case by simp
          qed
          moreover have
            "\<pi> (\<alpha> - \<delta> (Suc j) c + \<delta> (Suc j) c) (Suc j) =
               \<pi> (\<alpha> - \<delta> (Suc j) c) (Suc j) + \<pi> (\<delta> (Suc j) c) (Suc j)"
            using Rep_account_plus by presburger
          ultimately show ?thesis
            unfolding \<open>n = Suc j\<close>
            by simp
        next
          assume "n \<noteq> Suc j"
          hence "n \<le> j"
            using Suc.prems le_SucE by blast
          hence "(\<Sum> i\<le>j . \<pi> \<alpha> i) - c = (\<Sum> i\<le>j . \<pi> (\<alpha> - \<delta> n c) i)"
            using Suc.hyps by blast
          moreover have "\<pi> (\<alpha> - \<delta> n c + \<delta> n c) (Suc j) =
                           \<pi> (\<alpha> - \<delta> n c) (Suc j) + \<pi> (\<delta> n c) (Suc j)"
            using Rep_account_plus by presburger
          ultimately show ?thesis
            by (simp add: \<open>n \<noteq> Suc j\<close>)
        qed
      qed
      ultimately show ?thesis by auto
    qed
  }
  thus "strictly_solvent (\<alpha> - \<delta> n c)"
    unfolding strictly_solvent_def
    by auto
qed


subsection \<open>Closed Forms \label{subsec:bulk-update-closed-form}\<close>

text \<open>We first give closed forms for loans \<^term>\<open>\<delta> n c\<close>.  The simplest closed
      form is for \<^term>\<open>just_cash\<close>. Here the closed form is just the compound
      interest accrued from each update.\<close>

lemma bulk_update_just_cash_closed_form:
  assumes "\<rho> 0 = 0"
  shows "bulk_update_account n \<rho> i (just_cash c) =
           just_cash ((1 + i) ^ n * c)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "return_loans \<rho> (just_cash ((1 + i) ^ n * c)) =
          just_cash ((1 + i) ^ n * c)"
    using assms return_loans_just_cash by blast
  thus ?case
    using Suc net_asset_value_just_cash_left_inverse
    by (simp add: update_account_def,
        metis
          add.commute
          mult.commute
          mult.left_commute
          mult_1
          ring_class.ring_distribs(2))
qed

lemma bulk_update_loan_closed_form:
  assumes "\<rho> k \<noteq> 1"
  and "\<rho> k > 0"
  and "\<rho> 0 = 0"
  and "i \<ge> 0"
  shows "bulk_update_account n \<rho> i (\<delta> k c) =
           just_cash (c * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n) / (i + \<rho> k))
           + \<delta> k ((1 - \<rho> k) ^ n * c)"
proof (induct n)
  case 0
  then show ?case
    by (simp add: zero_account_alt_def)
next
  case (Suc n)
  have "i + \<rho> k > 0"
    using assms(2) assms(4) by force
  hence "(i + \<rho> k) / (i + \<rho> k) = 1"
    by force
  hence "bulk_update_account (Suc n) \<rho> i (\<delta> k c) =
            just_cash
              ((c * i) / (i + \<rho> k) * (1 + i) * ((1 + i) ^ n - (1 - \<rho> k) ^ n) +
               c * i * (1 - \<rho> k) ^ n * ((i + \<rho> k) / (i + \<rho> k)))
            + \<delta> k ((1 - \<rho> k) ^ (n + 1) * c)"
    using Suc
    by (simp add:
            return_loans_plus
            \<open>\<rho> 0 = 0\<close>
            return_loans_just_cash
            update_account_def
            net_asset_value_plus
            net_asset_value_just_cash_left_inverse
            add.commute
            add.left_commute
            distrib_left
            mult.assoc
            add_divide_distrib
            distrib_right
            mult.commute
            mult.left_commute)
  also have
    "\<dots> =
      just_cash
        ((c * i) / (i + \<rho> k) * (1 + i) * ((1 + i) ^ n - (1 - \<rho> k) ^ n) +
         (c * i) / (i + \<rho> k) * (1 - \<rho> k) ^ n * (i + \<rho> k))
      + \<delta> k ((1 - \<rho> k) ^ (n + 1) * c)"
    by (metis (no_types, lifting) times_divide_eq_left times_divide_eq_right)
  also have
    "\<dots> =
      just_cash
        ((c * i) / (i + \<rho> k) * (
              (1 + i) * ((1 + i) ^ n - (1 - \<rho> k) ^ n)
            + (1 - \<rho> k) ^ n * (i + \<rho> k)))
      + \<delta> k ((1 - \<rho> k) ^ (n + 1) * c)"
    by (metis (no_types, lifting) mult.assoc ring_class.ring_distribs(1))
  also have
    "\<dots> =
      just_cash
        ((c * i) / (i + \<rho> k) * ((1 + i) ^ (n + 1) - (1 - \<rho> k) ^ (n + 1)))
      + \<delta> k ((1 - \<rho> k) ^ (n + 1) * c)"
    by (simp add: mult.commute mult_diff_mult)
  ultimately show ?case by simp
qed

text \<open>We next give an \<^emph>\<open>algebraic\<close> closed form. This uses the ordered
      abelian group that \<^typ>\<open>account\<close>s form.\<close>

lemma bulk_update_algebraic_closed_form:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n < m \<longrightarrow> \<rho> n < \<rho> m"
  and "\<rho> 0 = 0"
  shows "bulk_update_account n \<rho> i \<alpha>
           = just_cash (
                (1 + i) ^ n * (cash_reserve \<alpha>)
                + (\<Sum> k = 1..shortest_period \<alpha>.
                      (\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n)
                         / (i + \<rho> k))
             )
             + (\<Sum>k = 1..shortest_period \<alpha>. \<delta> k ((1 - \<rho> k) ^ n * \<pi> \<alpha> k))"
proof -
  {
    fix m
    have "\<forall> k \<in> {1..m}. \<rho> k \<noteq> 1 \<and> \<rho> k > 0"
      by (metis
            assms(2)
            assms(3)
            assms(4)
            atLeastAtMost_iff
            dual_order.refl
            less_numeral_extra(1)
            linorder_not_less
            not_gr_zero)
    hence \<star>: "\<forall> k \<in> {1..m}.
                 bulk_update_account n \<rho> i (\<delta> k (\<pi> \<alpha> k))
               = just_cash ((\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n)
                               / (i + \<rho> k))
                 + \<delta> k ((1 - \<rho> k) ^ n * (\<pi> \<alpha> k))"
      using assms(1) assms(4) bulk_update_loan_closed_form by blast
    have "bulk_update_account n \<rho> i (\<Sum> k \<le> m. \<delta> k (\<pi> \<alpha> k))
            = (\<Sum> k \<le> m. bulk_update_account n \<rho> i (\<delta> k (\<pi> \<alpha> k)))"
      by (induct m, simp, simp add: bulk_update_account_plus)
    also have
      "\<dots> =   bulk_update_account n \<rho> i (\<delta> 0 (\<pi> \<alpha> 0))
            + (\<Sum> k = 1..m. bulk_update_account n \<rho> i (\<delta> k (\<pi> \<alpha> k)))"
      by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
    also have
      "\<dots> =   just_cash ((1 + i) ^ n * cash_reserve \<alpha>)
            + (\<Sum> k = 1..m. bulk_update_account n \<rho> i (\<delta> k (\<pi> \<alpha> k)))"
      using
        \<open>\<rho> 0 = 0\<close>
        bulk_update_just_cash_closed_form
        loan_just_cash
        cash_reserve_def
      by presburger
    also have
      "\<dots> =   just_cash ((1 + i) ^ n * cash_reserve \<alpha>)
            + (\<Sum> k = 1..m.
                  just_cash ((\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n)
                                 / (i + \<rho> k))
                  + \<delta> k ((1 - \<rho> k) ^ n * (\<pi> \<alpha> k)))"
      using \<star> by auto
    also have
      "\<dots> =   just_cash ((1 + i) ^ n * cash_reserve \<alpha>)
            + (\<Sum> k = 1..m.
                  just_cash ((\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n)
                                 / (i + \<rho> k)))
            + (\<Sum> k = 1..m. \<delta> k ((1 - \<rho> k) ^ n * (\<pi> \<alpha> k)))"
      by (induct m, auto)
    also have
      "\<dots> =   just_cash ((1 + i) ^ n * cash_reserve \<alpha>)
            + just_cash
                (\<Sum> k = 1..m.
                   (\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n) / (i + \<rho> k))
            + (\<Sum> k = 1..m. \<delta> k ((1 - \<rho> k) ^ n * (\<pi> \<alpha> k)))"
      by (induct m, auto, metis (no_types, lifting) add.assoc just_cash_plus)
    ultimately have
      "bulk_update_account n \<rho> i (\<Sum> k \<le> m. \<delta> k (\<pi> \<alpha> k)) =
          just_cash (
              (1 + i) ^ n * cash_reserve \<alpha>
            + (\<Sum> k = 1..m.
                  (\<pi> \<alpha> k) * i * ((1 + i) ^ n - (1 - \<rho> k) ^ n) / (i + \<rho> k)))
        + (\<Sum> k = 1..m. \<delta> k ((1 - \<rho> k) ^ n * (\<pi> \<alpha> k)))"
     by simp
  }
  note \<bullet> = this
  have
    "bulk_update_account n \<rho> i \<alpha>
       = bulk_update_account n \<rho> i (\<Sum> k \<le> shortest_period \<alpha>. \<delta> k (\<pi> \<alpha> k))"
    using account_decomposition by presburger
  thus ?thesis unfolding \<bullet> .
qed

text \<open>We finally give a \<^emph>\<open>functional\<close> closed form for bulk updating an
      account. Since the form is in terms of exponentiation, we may
      efficiently compute the bulk update output using
      \<^emph>\<open>exponentiation-by-squaring\<close>.\<close>

theorem bulk_update_closed_form:
  assumes "0 \<le> i"
  and "\<forall> n . \<rho> n < 1"
  and "\<forall> n m . n < m \<longrightarrow> \<rho> n < \<rho> m"
  and "\<rho> 0 = 0"
  shows "bulk_update_account n \<rho> i \<alpha>
           = \<iota> ( \<lambda> k .
                if k = 0 then
                  (1 + i) ^ n * (cash_reserve \<alpha>)
                  + (\<Sum> j = 1..shortest_period \<alpha>.
                        (\<pi> \<alpha> j) * i * ((1 + i) ^ n - (1 - \<rho> j) ^ n)
                           / (i + \<rho> j))
                else
                  (1 - \<rho> k) ^ n * \<pi> \<alpha> k
               )"
  (is "_ = \<iota> ?\<nu>")
proof -
  obtain \<nu> where X: "\<nu> = ?\<nu>" by blast
  moreover obtain \<nu>' where Y:
    "\<nu>' = \<pi> ( just_cash (
                (1 + i) ^ n * (cash_reserve \<alpha>)
                + (\<Sum> j = 1..shortest_period \<alpha>.
                      (\<pi> \<alpha> j) * i * ((1 + i) ^ n - (1 - \<rho> j) ^ n)
                         / (i + \<rho> j))
              )
              + (\<Sum>j = 1..shortest_period \<alpha>. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)))"
    by blast
  moreover
  {
    fix k
    have "\<forall> k > shortest_period \<alpha> . \<nu> k = \<nu>' k"
    proof (rule allI, rule impI)
      fix k
      assume "shortest_period \<alpha> < k"
      hence "\<nu> k = 0"
        unfolding X
        by (simp add: greater_than_shortest_period_zero)
      moreover have "\<nu>' k = 0"
      proof -
        have "\<forall> c. \<pi> (just_cash c) k = 0"
          using
            Rep_account_just_cash
            \<open>shortest_period \<alpha> < k\<close>
            just_cash_def
          by auto
        moreover
        have "\<forall> m < k. \<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k = 0"
        proof (rule allI, rule impI)
          fix m
          assume "m < k"
          let ?\<pi>\<Sigma>\<delta> = "\<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j))"
          have "?\<pi>\<Sigma>\<delta> k = (\<Sum>j = 1..m. \<pi> (\<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k)"
            by (induct m, auto)
          also have "\<dots> = (\<Sum>j = 1..m. 0)"
            using \<open>m < k\<close>
            by (induct m, simp+)
          finally show "?\<pi>\<Sigma>\<delta> k = 0"
            by force
        qed
        ultimately show ?thesis unfolding Y
          using \<open>shortest_period \<alpha> < k\<close> by force
      qed
      ultimately show "\<nu> k = \<nu>' k" by auto
    qed
    moreover have "\<forall> k . 0 < k \<longrightarrow> k \<le> shortest_period \<alpha> \<longrightarrow> \<nu> k = \<nu>' k"
    proof (rule allI, (rule impI)+)
      fix k
      assume "0 < k"
      and "k \<le> shortest_period \<alpha>"
      have "\<nu> k = (1 - \<rho> k) ^ n * \<pi> \<alpha> k"
        unfolding X
        using \<open>0 < k\<close> by fastforce
      moreover have "\<nu>' k = (1 - \<rho> k) ^ n * \<pi> \<alpha> k"
      proof -
        have "\<forall> c. \<pi> (just_cash c) k = 0"
          using \<open>0 < k\<close> by auto
        moreover
        {
          fix m
          assume "k \<le> m"
          have "  \<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k
                = (\<Sum>j = 1..m. \<pi> (\<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k)"
            by (induct m, auto)
          also
          have "\<dots> = (1 - \<rho> k) ^ n * \<pi> \<alpha> k"
            using \<open>0 < k\<close> \<open>k \<le> m\<close>
          proof (induct m)
            case 0
            then show ?case by simp
          next
            case (Suc m)
            then show ?case
            proof (cases "k = Suc m")
              case True
              hence "k > m" by auto
              hence "(\<Sum>j = 1..m. \<pi> (\<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k) = 0"
                by (induct m, auto)
              then show ?thesis
                using \<open>k > m\<close> \<open>k = Suc m\<close>
                by simp
            next
              case False
              hence "(\<Sum>j = 1..m. \<pi> (\<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k)
                       = (1 - \<rho> k) ^ n * \<pi> \<alpha> k"
                using Suc.hyps Suc.prems(1) Suc.prems(2) le_Suc_eq by blast
              moreover have "k \<le> m"
                using False Suc.prems(2) le_Suc_eq by blast
              ultimately show ?thesis using \<open>0 < k\<close> by simp
            qed
          qed
          finally have
            "\<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k
                 = (1 - \<rho> k) ^ n * \<pi> \<alpha> k" .
        }
        hence
          "\<forall> m \<ge> k.
              \<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) k
            = (1 - \<rho> k) ^ n * \<pi> \<alpha> k" by auto
        ultimately show ?thesis
          unfolding Y
          using \<open>k \<le> shortest_period \<alpha>\<close>
          by force
      qed
      ultimately show "\<nu> k = \<nu>' k"
        by fastforce
    qed
    moreover have "\<nu> 0 = \<nu>' 0"
    proof -
      have "\<nu> 0 = (1 + i) ^ n * (cash_reserve \<alpha>)
                  + (\<Sum> j = 1..shortest_period \<alpha>.
                        (\<pi> \<alpha> j) * i * ((1 + i) ^ n - (1 - \<rho> j) ^ n)
                           / (i + \<rho> j))"
        using X by presburger
      moreover
      have "\<nu>' 0 = (1 + i) ^ n * (cash_reserve \<alpha>)
                   + (\<Sum> j = 1..shortest_period \<alpha>.
                         (\<pi> \<alpha> j) * i * ((1 + i) ^ n - (1 - \<rho> j) ^ n)
                            / (i + \<rho> j))"
      proof -
        {
          fix m
          have "\<pi> (\<Sum>j = 1..m. \<delta> j ((1 - \<rho> j) ^ n * \<pi> \<alpha> j)) 0 = 0"
            by (induct m, simp+)
        }
        thus ?thesis unfolding Y
          by simp
      qed
      ultimately show ?thesis by auto
    qed
    ultimately have "\<nu> k = \<nu>' k"
      by (metis linorder_not_less not_gr0)
  }
  hence "\<iota> \<nu> = \<iota> \<nu>'"
    by presburger
  ultimately show ?thesis
    using
      Rep_account_inverse
      assms
      bulk_update_algebraic_closed_form
    by presburger
qed

end
