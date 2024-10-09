section \<open>\<open>Wlog_Examples\<close> – Examples how to use \texttt{wlog}\<close>

theory Wlog_Examples
  imports Wlog Complex_Main
begin

text \<open>The theorem @{thm [source] Complex.card_nth_roots} has the additional assumption \<^term>\<open>n > 0\<close>.
  We use exactly the same proof except for stating that w.l.o.g., \<^term>\<open>n > 0\<close>.\<close>
lemma card_nth_roots_strengthened:
  assumes "c \<noteq> 0"
  shows   "card {z::complex. z ^ n = c} = n"
proof -
  wlog n_pos: "n > 0"
    using negation by (simp add: infinite_UNIV_char_0)
  have "card {z. z ^ n = c} = card {z::complex. z ^ n = 1}"
    by (rule sym, rule bij_betw_same_card, rule bij_betw_nth_root_unity) fact+
  also have "\<dots> = n" by (rule card_roots_unity_eq) fact+
  finally show ?thesis .
qed

text \<open>This example very roughly follows Harrison \<^cite>\<open>"harrison-wlog"\<close>:\<close>
lemma schur_ineq:
  fixes a b c :: \<open>'a :: linordered_idom\<close> and k :: nat
  assumes a0: \<open>a \<ge> 0\<close> and b0: \<open>b \<ge> 0\<close> and c0: \<open>c \<ge> 0\<close>
  shows \<open>a^k * (a - b) * (a - c) + b^k * (b - a) * (b - c) + c^k * (c - a) * (c - b) \<ge> 0\<close>
    (is \<open>?lhs \<ge> 0\<close>)
proof -
  wlog ordered[simp]: \<open>a \<le> b\<close> \<open>b \<le> c\<close> generalizing a b c keeping a0 b0 c0
    apply (rule rev_mp[OF c0]; rule rev_mp[OF b0]; rule rev_mp[OF a0])
    apply (rule linorder_wlog_3[of _ a b c])
     apply (simp add: algebra_simps)
    by (simp add: hypothesis)

  from ordered have [simp]: \<open>a \<le> c\<close>
    by linarith

  have \<open>?lhs = (c - b) * (c^k * (c - a) - b^k * (b - a)) + a^k * (c - a) * (b - a)\<close>
    by (simp add: algebra_simps)
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: add_nonneg_nonneg mult_nonneg_nonneg mult_mono power_mono zero_le_power simp: a0 b0 c0)
  finally show \<open>?lhs \<ge> 0\<close>
    by -
qed

text \<open>The following illustrates how facts already proven before a @{command wlog} can be still be used after the wlog.
  The example does not do anything useful.\<close>
lemma \<open>A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close>
proof -
  have test1: \<open>1=1\<close> by simp
  assume a: \<open>A\<close>
  then have test2: \<open>A \<or> 1\<noteq>2\<close> by simp
      \<comment> \<open>Isabelle marks this as being potentially based on assumption @{thm [source] a}.
          (Note: this is not done by actual dependency tracking. Anything that is proven after the @{command assume} command can depend on the assumption.)\<close>
  assume b: \<open>B\<close>
  with a have test3: \<open>A \<and> B\<close> by simp
      \<comment> \<open>Isabelle marks this as being potentially based on assumption @{thm [source] a}, @{thm [source] b}\<close>
  wlog true: \<open>True\<close> generalizing A B keeping b
    \<comment> \<open>A pointless wlog: we can wlog assume \<^term>\<open>True\<close>.
       Notice: we only keep the assumption @{thm [source] b} around.\<close>
    using negation by blast
  text \<open>The already proven theorems cannot be accessed directly anymore (wlog starts a new proof block).
        Recovered versions are available, however:\<close>
  thm wlog_keep.test1
    \<comment> \<open>The fact is fully recovered since it did not depend on any assumptions.\<close>
  thm wlog_keep.test2
    \<comment> \<open>This fact depended on assumption \<open>a\<close> which we did not keep. So the original fact might not hold anymore.
        Therefore, @{thm [source] wlog_keep.test2} becomes \<^term>\<open>A \<Longrightarrow> A \<or> 1 \<noteq> 2\<close>. (Note the added \<^term>\<open>A\<close> premise.)\<close>
  thm wlog_keep.test3
    \<comment> \<open>This fact depended on assumptions \<open>a\<close> and \<open>b\<close>. But we kept @{thm [source] b}.
        Therefore, @{thm [source] wlog_keep.test2} becomes \<^term>\<open>A \<Longrightarrow> A \<and> B\<close>. (Note that only \<^term>\<open>A\<close> is added as a premise.)\<close>
  oops
    \<comment> \<open>Aborting the proof here because we cannot prove \<^term>\<open>A \<and> B\<close> anymore since we dropped assumption \<open>a\<close> for demonstration purposes.\<close>

end
