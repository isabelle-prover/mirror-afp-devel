theory Aho_Corasick
  imports "HOL-Library.Sublist"
begin

section \<open>Aho-Corasick String Matching\<close>

text \<open>
  The original Aho-Corasick string matching algorithm was introduced by Aho
  and Corasick \<^cite>\<open>AhoCorasick1975\<close>.  It searches for all occurrences of
  a finite dictionary of patterns in a text.  Its central automaton invariant
  is that, after reading a text prefix, the current state is the longest suffix
  of the processed text that is also a prefix of a dictionary pattern.

  This theory formalizes that canonical Aho-Corasick state and an executable
  reference search procedure over arbitrary lists.  For each consumed text
  prefix, the reference transition recomputes the canonical state by scanning
  the finite list of pattern prefixes; this is the abstract automaton semantics
  that the usual failure-link implementation realizes more efficiently.  We
  also derive a state-only transition theorem, a fold-based scan invariant, and
  a recursive failure-link transition that refines the canonical transition.
  The main theorem proves that the reports produced by the search are exactly
  the pattern occurrences ending at each text position.

  AI assistance was used for proof engineering.  The final definitions,
  statements, and proofs are checked by Isabelle.
\<close>

subsection \<open>Pattern-prefix states\<close>

definition ac_states :: "'a list list \<Rightarrow> 'a list list" where
  "ac_states pats = remdups ([] # concat (map prefixes pats))"

lemma set_ac_states:
  "set (ac_states pats) = insert [] {q. \<exists>p\<in>set pats. prefix q p}"
  by (auto simp: ac_states_def)

lemma Nil_in_ac_states [simp]: "[] \<in> set (ac_states pats)"
  by (simp add: set_ac_states)

fun longest_list :: "'a list list \<Rightarrow> 'a list" where
  "longest_list [] = []"
| "longest_list (x # xs) =
     (let y = longest_list xs in if length x < length y then y else x)"

lemma longest_list_member:
  assumes "xs \<noteq> []"
  shows "longest_list xs \<in> set xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True
    then show ?thesis by simp
  next
    case False
    let ?y = "longest_list xs"
    from False have y_mem: "?y \<in> set xs"
      using Cons.IH by simp
    show ?thesis
    proof (cases "length x < length ?y")
      case True
      then show ?thesis using y_mem by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
qed

lemma longest_list_longest:
  assumes "x \<in> set xs"
  shows "length x \<le> length (longest_list xs)"
  using assms
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis using Cons.prems by auto
  next
    case False
    let ?z = "longest_list ys"
    have z_long: "\<And>u. u \<in> set ys \<Longrightarrow> length u \<le> length ?z"
      using Cons.IH by blast
    show ?thesis
    proof (cases "length y < length ?z")
      case True
      then show ?thesis using Cons.prems z_long by auto
    next
      case le: False
      then have z_le_y: "length ?z \<le> length y" by simp
      show ?thesis
      proof (cases "x = y")
        case True
        then show ?thesis using le by auto
      next
        case neq: False
        then have "x \<in> set ys"
          using Cons.prems by simp
        then have "length x \<le> length ?z"
          using z_long by simp
        also have "\<dots> \<le> length y"
          using z_le_y .
        finally show ?thesis using le by auto
      qed
    qed
  qed
qed


subsection \<open>The canonical Aho-Corasick state\<close>

text \<open>
  The canonical state for a word \<open>w\<close> is chosen among the finite list of all
  pattern prefixes.  Since the empty list is always a state and always a suffix,
  the candidate list is nonempty.  The selected state is therefore a suffix of
  \<open>w\<close>, a valid pattern-prefix state, and at least as long as any other valid
  suffix state.
\<close>

definition state_candidates :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "state_candidates pats w = filter (\<lambda>q. suffix q w) (ac_states pats)"

definition ac_state :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ac_state pats w = longest_list (state_candidates pats w)"

lemma state_candidates_nonempty: "state_candidates pats w \<noteq> []"
proof -
  have "[] \<in> set (state_candidates pats w)"
    by (simp add: state_candidates_def)
  then show ?thesis by auto
qed

lemma ac_state_in_states: "ac_state pats w \<in> set (ac_states pats)"
  using longest_list_member[OF state_candidates_nonempty]
  by (auto simp: ac_state_def state_candidates_def)

lemma ac_state_suffix: "suffix (ac_state pats w) w"
  using longest_list_member[OF state_candidates_nonempty]
  by (auto simp: ac_state_def state_candidates_def)

lemma ac_state_longest:
  assumes "q \<in> set (ac_states pats)"
  assumes "suffix q w"
  shows "length q \<le> length (ac_state pats w)"
  using assms longest_list_longest[of q "state_candidates pats w"]
  by (auto simp: ac_state_def state_candidates_def)

lemma pattern_is_state:
  assumes "p \<in> set pats"
  shows "p \<in> set (ac_states pats)"
  using assms by (auto simp: set_ac_states)

lemma ac_state_snoc_prefix_closed:
  assumes "r @ [x] \<in> set (ac_states pats)"
  shows "r \<in> set (ac_states pats)"
  using assms by (auto simp: set_ac_states dest: append_prefixD)

lemma pattern_suffix_ac_state_iff:
  assumes "p \<in> set pats"
  shows "suffix p (ac_state pats w) \<longleftrightarrow> suffix p w"
proof
  assume "suffix p (ac_state pats w)"
  then show "suffix p w"
    using ac_state_suffix suffix_order.order_trans by blast
next
  assume p_suffix: "suffix p w"
  have "length p \<le> length (ac_state pats w)"
    using ac_state_longest[OF pattern_is_state[OF assms] p_suffix] .
  then show "suffix p (ac_state pats w)"
    using suffix_length_suffix[OF p_suffix ac_state_suffix] by blast
qed

lemma ac_state_Nil [simp]: "ac_state pats [] = []"
  using ac_state_suffix[of pats "[]"] by simp


subsection \<open>State-only transition\<close>

text \<open>
  The next theorem captures the automaton nature of the construction.  Although
  the canonical state is defined from the whole consumed text prefix, the next
  canonical state can be computed from only the current state and the next
  symbol.
\<close>

definition ac_step :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "ac_step pats q x = ac_state pats (q @ [x])"

lemma suffix_snoc_mono:
  assumes "suffix q w"
  shows "suffix (q @ [x]) (w @ [x])"
  using assms by (auto simp: suffix_def)

lemma state_suffix_next_window:
  assumes q: "q = ac_state pats w"
  assumes r_state: "r \<in> set (ac_states pats)"
  assumes r_suffix: "suffix r (w @ [x])"
  shows "suffix r (q @ [x])"
proof (cases r rule: rev_cases)
  case Nil
  then show ?thesis by simp
next
  case (snoc r' y)
  from r_suffix snoc have y: "y = x" and r'_suffix: "suffix r' w"
    by auto
  have r'_state: "r' \<in> set (ac_states pats)"
    using r_state snoc by (auto intro: ac_state_snoc_prefix_closed)
  have "length r' \<le> length q"
    using ac_state_longest[OF r'_state r'_suffix] q by simp
  moreover have "suffix q w"
    using q ac_state_suffix by simp
  ultimately have "suffix r' q"
    using suffix_length_suffix[OF r'_suffix] by blast
  with snoc y show ?thesis by simp
qed

theorem ac_state_snoc:
  "ac_state pats (w @ [x]) = ac_step pats (ac_state pats w) x"
proof -
  let ?q = "ac_state pats w"
  let ?left = "ac_state pats (w @ [x])"
  let ?right = "ac_state pats (?q @ [x])"
  have left_in: "?left \<in> set (ac_states pats)"
    by (rule ac_state_in_states)
  have left_suffix_full: "suffix ?left (w @ [x])"
    by (rule ac_state_suffix)
  have left_suffix_q: "suffix ?left (?q @ [x])"
    using state_suffix_next_window[
      where q="?q" and pats=pats and w=w and r="?left" and x=x]
      left_in left_suffix_full by simp
  have right_suffix_q: "suffix ?right (?q @ [x])"
    by (rule ac_state_suffix)
  have left_le_right: "length ?left \<le> length ?right"
    using ac_state_longest[OF left_in left_suffix_q] .
  have left_suffix_right: "suffix ?left ?right"
    using suffix_length_suffix[OF left_suffix_q right_suffix_q left_le_right] .

  have q_suffix: "suffix ?q w"
    by (rule ac_state_suffix)
  have right_in: "?right \<in> set (ac_states pats)"
    by (rule ac_state_in_states)
  have right_suffix_w: "suffix ?right (w @ [x])"
    using suffix_snoc_mono[OF q_suffix, of x] right_suffix_q
      suffix_order.order_trans by blast
  have right_le_left: "length ?right \<le> length ?left"
    using ac_state_longest[OF right_in right_suffix_w] .
  have right_suffix_left: "suffix ?right ?left"
    using suffix_length_suffix[OF right_suffix_w ac_state_suffix right_le_left] .
  have "?left = ?right"
    using left_suffix_right right_suffix_left by (rule suffix_order.antisym)
  then show ?thesis
    by (simp add: ac_step_def)
qed

text \<open>
  Iterating the state transition over a text fragment therefore tracks the
  canonical state for the whole consumed prefix.
\<close>

theorem ac_state_foldl_from:
  assumes "q = ac_state pats w"
  shows "foldl (ac_step pats) q xs = ac_state pats (w @ xs)"
  using assms
proof (induction xs arbitrary: w q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?w' = "w @ [x]"
  have step: "ac_step pats q x = ac_state pats ?w'"
    using Cons.prems ac_state_snoc[of pats w x] by simp
  have "foldl (ac_step pats) (ac_state pats ?w') xs =
      ac_state pats (?w' @ xs)"
    using Cons.IH[where w="?w'" and q="ac_state pats ?w'"] by simp
  then show ?case
    using step by simp
qed

theorem ac_state_foldl:
  "foldl (ac_step pats) [] xs = ac_state pats xs"
  using ac_state_foldl_from[where pats=pats and w="[]" and q="[]" and xs=xs]
  by simp

theorem ac_state_foldl_take:
  "foldl (ac_step pats) [] (take i text) = ac_state pats (take i text)"
  by (simp add: ac_state_foldl)


subsection \<open>Failure-link transition refinement\<close>

text \<open>
  The failure link of a state is the longest proper suffix that is also a
  pattern-prefix state.  The recursive failure-link transition follows these
  links until it finds a state that can consume the next symbol, or returns to
  the empty state.  The main theorem of this subsection proves that this
  recognizable Aho-Corasick transition refines the canonical transition above.
\<close>

definition proper_suffix_state_candidates :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "proper_suffix_state_candidates pats q =
     filter (\<lambda>r. suffix r q \<and> r \<noteq> q) (ac_states pats)"

definition ac_fail :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ac_fail pats q = longest_list (proper_suffix_state_candidates pats q)"

lemma proper_suffix_state_candidates_nonempty:
  assumes "q \<noteq> []"
  shows "proper_suffix_state_candidates pats q \<noteq> []"
proof -
  have "[] \<in> set (proper_suffix_state_candidates pats q)"
    using assms by (simp add: proper_suffix_state_candidates_def)
  then show ?thesis by auto
qed

lemma ac_fail_in_states:
  assumes "q \<noteq> []"
  shows "ac_fail pats q \<in> set (ac_states pats)"
  using longest_list_member[OF proper_suffix_state_candidates_nonempty[OF assms]]
  by (auto simp: ac_fail_def proper_suffix_state_candidates_def)

lemma ac_fail_suffix:
  assumes "q \<noteq> []"
  shows "suffix (ac_fail pats q) q"
  using longest_list_member[OF proper_suffix_state_candidates_nonempty[OF assms]]
  by (auto simp: ac_fail_def proper_suffix_state_candidates_def)

lemma ac_fail_proper:
  assumes "q \<noteq> []"
  shows "ac_fail pats q \<noteq> q"
  using longest_list_member[OF proper_suffix_state_candidates_nonempty[OF assms]]
  by (auto simp: ac_fail_def proper_suffix_state_candidates_def)

lemma length_ac_fail_less:
  assumes "q \<noteq> []"
  shows "length (ac_fail pats q) < length q"
proof -
  obtain zs where q: "q = zs @ ac_fail pats q"
    using ac_fail_suffix[OF assms] by (auto simp: suffix_def)
  have zs_ne: "zs \<noteq> []"
  proof
    assume "zs = []"
    then have "ac_fail pats q = q"
      using q by simp
    then show False
      using ac_fail_proper[OF assms] by simp
  qed
  have "length q = length zs + length (ac_fail pats q)"
    by (subst q, simp)
  moreover have "0 < length zs"
    using zs_ne by simp
  ultimately show ?thesis
    by simp
qed

lemma ac_fail_longest:
  assumes "r \<in> set (ac_states pats)"
  assumes "suffix r q"
  assumes "r \<noteq> q"
  shows "length r \<le> length (ac_fail pats q)"
  using assms longest_list_longest[of r "proper_suffix_state_candidates pats q"]
  by (auto simp: ac_fail_def proper_suffix_state_candidates_def)

lemma ac_state_self_if_state:
  assumes "q \<in> set (ac_states pats)"
  shows "ac_state pats q = q"
proof -
  have q_le_state: "length q \<le> length (ac_state pats q)"
    using ac_state_longest[OF assms, of q] by simp
  have state_suffix_q: "suffix (ac_state pats q) q"
    by (rule ac_state_suffix)
  have q_suffix_state: "suffix q (ac_state pats q)"
    using suffix_length_suffix[OF _ state_suffix_q q_le_state] by simp
  show ?thesis
    using state_suffix_q q_suffix_state by (rule suffix_order.antisym)
qed

lemma ac_state_singleton_if_no_state:
  assumes "[x] \<notin> set (ac_states pats)"
  shows "ac_state pats [x] = []"
proof -
  have state: "ac_state pats [x] \<in> set (ac_states pats)"
    by (rule ac_state_in_states)
  have suffix: "suffix (ac_state pats [x]) [x]"
    by (rule ac_state_suffix)
  have "ac_state pats [x] = [] \<or> ac_state pats [x] = [x]"
  proof -
    obtain zs where "[x] = zs @ ac_state pats [x]"
      using suffix by (auto simp: suffix_def)
    then show ?thesis
      by (cases zs; cases "ac_state pats [x]") auto
  qed
  then show ?thesis
    using assms state by auto
qed

lemma state_suffix_fail_next:
  assumes q_ne: "q \<noteq> []"
  assumes qx_not_state: "q @ [x] \<notin> set (ac_states pats)"
  assumes r_state: "r \<in> set (ac_states pats)"
  assumes r_suffix: "suffix r (q @ [x])"
  shows "suffix r (ac_fail pats q @ [x])"
proof (cases r rule: rev_cases)
  case Nil
  then show ?thesis by simp
next
  case (snoc r' y)
  from r_suffix snoc have y: "y = x" and r'_suffix: "suffix r' q"
    by auto
  have r'_state: "r' \<in> set (ac_states pats)"
    using r_state snoc by (auto intro: ac_state_snoc_prefix_closed)
  have r'_proper: "r' \<noteq> q"
    using qx_not_state r_state snoc y by auto
  have "length r' \<le> length (ac_fail pats q)"
    using ac_fail_longest[OF r'_state r'_suffix r'_proper] .
  moreover have "suffix (ac_fail pats q) q"
    using ac_fail_suffix[OF q_ne] .
  ultimately have "suffix r' (ac_fail pats q)"
    using suffix_length_suffix[OF r'_suffix] by blast
  with snoc y show ?thesis by simp
qed

lemma ac_step_fail_eq:
  assumes q_state: "q \<in> set (ac_states pats)"
  assumes q_ne: "q \<noteq> []"
  assumes qx_not_state: "q @ [x] \<notin> set (ac_states pats)"
  shows "ac_step pats (ac_fail pats q) x = ac_step pats q x"
proof -
  let ?fail = "ac_fail pats q"
  let ?left = "ac_state pats (q @ [x])"
  let ?right = "ac_state pats (?fail @ [x])"
  have left_in: "?left \<in> set (ac_states pats)"
    by (rule ac_state_in_states)
  have left_suffix_q: "suffix ?left (q @ [x])"
    by (rule ac_state_suffix)
  have left_suffix_fail: "suffix ?left (?fail @ [x])"
    using state_suffix_fail_next[OF q_ne qx_not_state left_in left_suffix_q] .
  have right_suffix_fail: "suffix ?right (?fail @ [x])"
    by (rule ac_state_suffix)
  have left_le_right: "length ?left \<le> length ?right"
    using ac_state_longest[OF left_in left_suffix_fail] .
  have left_suffix_right: "suffix ?left ?right"
    using suffix_length_suffix[OF left_suffix_fail right_suffix_fail left_le_right] .

  have fail_suffix_q: "suffix ?fail q"
    using ac_fail_suffix[OF q_ne] .
  have right_in: "?right \<in> set (ac_states pats)"
    by (rule ac_state_in_states)
  have right_suffix_q: "suffix ?right (q @ [x])"
    using suffix_snoc_mono[OF fail_suffix_q, of x] right_suffix_fail
      suffix_order.order_trans by blast
  have right_le_left: "length ?right \<le> length ?left"
    using ac_state_longest[OF right_in right_suffix_q] .
  have right_suffix_left: "suffix ?right ?left"
    using suffix_length_suffix[OF right_suffix_q ac_state_suffix right_le_left] .
  have "?left = ?right"
    using left_suffix_right right_suffix_left by (rule suffix_order.antisym)
  then show ?thesis
    by (simp add: ac_step_def)
qed

function ac_fail_step :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "ac_fail_step pats q x =
     (if q @ [x] \<in> set (ac_states pats) then q @ [x]
      else if q = [] then []
      else ac_fail_step pats (ac_fail pats q) x)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(pats, q, x). length q)")
    (auto simp: length_ac_fail_less)

theorem ac_fail_step_refines:
  assumes "q \<in> set (ac_states pats)"
  shows "ac_fail_step pats q x = ac_step pats q x"
  using assms
proof (induction pats q x rule: ac_fail_step.induct)
  case (1 pats q x)
  show ?case
  proof -
    consider
      (next_state) "q @ [x] \<in> set (ac_states pats)"
    | (root) "q @ [x] \<notin> set (ac_states pats)" "q = []"
    | (fail) "q @ [x] \<notin> set (ac_states pats)" "q \<noteq> []"
      by blast
    then show ?thesis
    proof cases
      case next_state
      then show ?thesis
        by (simp add: ac_step_def ac_state_self_if_state)
    next
      case root
      then show ?thesis
        using ac_state_singleton_if_no_state[of x pats]
        by (simp add: ac_step_def)
    next
      case fail
      have fail_state: "ac_fail pats q \<in> set (ac_states pats)"
        using ac_fail_in_states[OF fail(2)] .
      have "ac_fail_step pats q x = ac_fail_step pats (ac_fail pats q) x"
        using fail by simp
      also have "\<dots> = ac_step pats (ac_fail pats q) x"
        using "1.IH"[OF fail fail_state] .
      also have "\<dots> = ac_step pats q x"
        using ac_step_fail_eq[OF "1.prems" fail(2) fail(1)] .
      finally show ?thesis .
    qed
  qed
qed

theorem ac_fail_state_foldl_from:
  assumes "q = ac_state pats w"
  shows "foldl (ac_fail_step pats) q xs = ac_state pats (w @ xs)"
  using assms
proof (induction xs arbitrary: w q)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?w' = "w @ [x]"
  have q_state: "q \<in> set (ac_states pats)"
    using Cons.prems ac_state_in_states by simp
  have step: "ac_fail_step pats q x = ac_state pats ?w'"
    using ac_fail_step_refines[OF q_state, of x] Cons.prems ac_state_snoc[of pats w x]
    by simp
  have rec: "foldl (ac_fail_step pats) (ac_state pats ?w') xs =
      ac_state pats (?w' @ xs)"
    by (rule Cons.IH) simp
  have "foldl (ac_fail_step pats) q (x # xs) =
      foldl (ac_fail_step pats) (ac_state pats ?w') xs"
    by (simp only: foldl.simps step)
  also have "\<dots> = ac_state pats (?w' @ xs)"
    using rec .
  also have "\<dots> = ac_state pats (w @ x # xs)"
    by simp
  finally show ?case .
qed

theorem ac_fail_state_foldl:
  "foldl (ac_fail_step pats) [] xs = ac_state pats xs"
  using ac_fail_state_foldl_from[where pats=pats and w="[]" and q="[]" and xs=xs]
  by simp

theorem ac_fail_state_foldl_take:
  "foldl (ac_fail_step pats) [] (take i text) = ac_state pats (take i text)"
  by (simp add: ac_fail_state_foldl)


subsection \<open>Search and correctness\<close>

text \<open>
  The output function filters the dictionary to the patterns that are suffixes
  of the current state.  By the canonical-state invariant, this is equivalent
  to filtering the dictionary to the patterns that occur ending at the current
  text position.
\<close>

definition ac_output :: "'a list list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "ac_output pats q = filter (\<lambda>p. suffix p q) pats"

theorem ac_output_state:
  "set (ac_output pats (ac_state pats w)) =
     {p. p \<in> set pats \<and> suffix p w}"
  by (auto simp: ac_output_def pattern_suffix_ac_state_iff)

fun ac_search_from ::
  "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list"
where
  "ac_search_from pats w i [] = []"
| "ac_search_from pats w i (x # xs) =
     (let w' = w @ [x];
          q = ac_state pats w'
      in map (\<lambda>p. (p, i)) (ac_output pats q) @
         ac_search_from pats w' (Suc i) xs)"

definition ac_search :: "'a list list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list" where
  "ac_search pats text = ac_search_from pats [] 0 text"

fun ac_search_states_from ::
  "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list"
where
  "ac_search_states_from pats q i [] = []"
| "ac_search_states_from pats q i (x # xs) =
     (let q' = ac_step pats q x in
        map (\<lambda>p. (p, i)) (ac_output pats q') @
        ac_search_states_from pats q' (Suc i) xs)"

definition ac_search_states :: "'a list list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list" where
  "ac_search_states pats text = ac_search_states_from pats [] 0 text"

fun ac_search_fail_from ::
  "'a list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list"
where
  "ac_search_fail_from pats q i [] = []"
| "ac_search_fail_from pats q i (x # xs) =
     (let q' = ac_fail_step pats q x in
        map (\<lambda>p. (p, i)) (ac_output pats q') @
        ac_search_fail_from pats q' (Suc i) xs)"

definition ac_search_fail :: "'a list list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) list" where
  "ac_search_fail pats text = ac_search_fail_from pats [] 0 text"

lemma ac_search_states_from_eq:
  assumes "q = ac_state pats w"
  shows "ac_search_states_from pats q i xs = ac_search_from pats w i xs"
  using assms
proof (induction xs arbitrary: w q i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?w' = "w @ [x]"
  have step: "ac_step pats q x = ac_state pats ?w'"
    using Cons.prems ac_state_snoc[of pats w x] by simp
  have rec:
    "ac_search_states_from pats (ac_state pats ?w') (Suc i) xs =
      ac_search_from pats ?w' (Suc i) xs"
    using Cons.IH[where w="?w'" and q="ac_state pats ?w'" and i="Suc i"] by simp
  show ?case
    using step rec by (simp add: Let_def)
qed

theorem ac_search_states_eq:
  "ac_search_states pats text = ac_search pats text"
  unfolding ac_search_states_def ac_search_def
  by (rule ac_search_states_from_eq) simp

lemma ac_search_fail_from_eq:
  assumes "q = ac_state pats w"
  shows "ac_search_fail_from pats q i xs = ac_search_from pats w i xs"
  using assms
proof (induction xs arbitrary: w q i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?w' = "w @ [x]"
  have q_state: "q \<in> set (ac_states pats)"
    using Cons.prems ac_state_in_states by simp
  have step: "ac_fail_step pats q x = ac_state pats ?w'"
    using ac_fail_step_refines[OF q_state, of x] Cons.prems ac_state_snoc[of pats w x]
    by simp
  have rec:
    "ac_search_fail_from pats (ac_state pats ?w') (Suc i) xs =
      ac_search_from pats ?w' (Suc i) xs"
    using Cons.IH[where w="?w'" and q="ac_state pats ?w'" and i="Suc i"] by simp
  show ?case
    using step rec by (simp add: Let_def)
qed

theorem ac_search_fail_eq:
  "ac_search_fail pats text = ac_search pats text"
  unfolding ac_search_fail_def ac_search_def
  by (rule ac_search_fail_from_eq) simp

subsection \<open>Executable example\<close>

text \<open>
  The following concrete input exercises overlapping dictionary patterns for
  both executable search procedures.  The \<open>eval\<close> proof method compiles the
  definitions to ML, evaluates them, and checks the resulting equations.
\<close>

lemma ac_search_states_example:
  "ac_search_states [[0], [0,1], [1,0,1], [1,2], [1,2,0], [2], [2,0,0]]
     [0,1,2,2,0,1::nat] =
   [([0], 0), ([0, 1], 1), ([1, 2], 2), ([2], 2), ([2], 3), ([0], 4), ([0, 1], 5)]"
  by eval

lemma ac_search_fail_example:
  "ac_search_fail [[0], [0,1], [1,0,1], [1,2], [1,2,0], [2], [2,0,0]]
     [0,1,2,2,0,1::nat] =
   [([0], 0), ([0, 1], 1), ([1, 2], 2), ([2], 2), ([2], 3), ([0], 4), ([0, 1], 5)]"
  by eval

definition occurs_ending_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "occurs_ending_at pat text i \<longleftrightarrow>
     i < length text \<and> suffix pat (take (Suc i) text)"

lemma in_ac_search_from_iff:
  "(p, k) \<in> set (ac_search_from pats w i xs) \<longleftrightarrow>
     (\<exists>j < length xs.
        k = i + j \<and>
        p \<in> set pats \<and>
        suffix p (ac_state pats (w @ take (Suc j) xs)))"
proof (induction xs arbitrary: w i k)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?w' = "w @ [x]"
  show ?case (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then have mem:
      "(p, k) \<in>
        set (map (\<lambda>p. (p, i)) (ac_output pats (ac_state pats ?w')) @
          ac_search_from pats ?w' (Suc i) xs)"
      by (simp add: Let_def)
    have out_or_rec:
      "p \<in> set (ac_output pats (ac_state pats ?w')) \<and> k = i \<or>
       (p, k) \<in> set (ac_search_from pats ?w' (Suc i) xs)"
      using mem by auto
    then show ?rhs
    proof
      assume "p \<in> set (ac_output pats (ac_state pats ?w')) \<and> k = i"
      then have p: "p \<in> set pats"
        and k: "k = i"
        and s: "suffix p (ac_state pats ?w')"
        by (auto simp: ac_output_def)
      then show ?rhs
        using p k s by (intro exI[of _ 0]) simp
    next
      assume rec: "(p, k) \<in> set (ac_search_from pats ?w' (Suc i) xs)"
      then obtain j where j: "j < length xs"
        and k: "k = Suc i + j"
        and p: "p \<in> set pats"
        and s: "suffix p (ac_state pats (?w' @ take (Suc j) xs))"
        using Cons.IH[where w="?w'" and i="Suc i" and k=k] by auto
      have "?w' @ take (Suc j) xs = w @ take (Suc (Suc j)) (x # xs)"
        by simp
      moreover have "k = i + Suc j"
        using k by simp
      ultimately show ?rhs
        using j p s by (intro exI[of _ "Suc j"]) auto
    qed
  next
    assume ?rhs
    then obtain j where j: "j < length (x # xs)"
      and k: "k = i + j"
      and p: "p \<in> set pats"
      and s: "suffix p (ac_state pats (w @ take (Suc j) (x # xs)))"
      by auto
    show ?lhs
    proof (cases j)
      case 0
      then have "p \<in> set (ac_output pats (ac_state pats ?w'))"
        using p s by (simp add: ac_output_def)
      with 0 k show ?thesis by (simp add: Let_def)
    next
      case (Suc j')
      then have j': "j' < length xs"
        using j by simp
      have "?w' @ take (Suc j') xs = w @ take (Suc j) (x # xs)"
        using Suc by simp
      then have rec_suffix:
        "suffix p (ac_state pats (?w' @ take (Suc j') xs))"
        using s by simp
      have "(p, k) \<in> set (ac_search_from pats ?w' (Suc i) xs)"
        using Cons.IH[where w="?w'" and i="Suc i" and k=k] j' k p rec_suffix Suc by auto
      then show ?thesis by (simp add: Let_def)
    qed
  qed
qed

theorem ac_search_correct:
  "set (ac_search pats text) =
     {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
proof
  show "set (ac_search pats text) \<subseteq>
      {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
  proof
    fix x
    assume xin: "x \<in> set (ac_search pats text)"
    obtain p i where x: "x = (p, i)"
      by (cases x)
    have pin: "(p, i) \<in> set (ac_search pats text)"
      using xin by (simp add: x)
    then have pin': "(p, i) \<in> set (ac_search_from pats [] 0 text)"
      by (simp add: ac_search_def)
    then obtain j where j: "j < length text"
      and i: "i = j"
      and p: "p \<in> set pats"
      and s: "suffix p (ac_state pats (take (Suc j) text))"
      by (auto simp: in_ac_search_from_iff)
    have "suffix p (take (Suc j) text)"
      using pattern_suffix_ac_state_iff[OF p, of "take (Suc j) text"] s by simp
    then have "suffix p (take (Suc i) text)"
      using i by simp
    with j i p show "x \<in> {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
      by (auto simp: x occurs_ending_at_def)
  qed
next
  show "{(p, i). p \<in> set pats \<and> occurs_ending_at p text i} \<subseteq>
      set (ac_search pats text)"
  proof
    fix x
    assume xin: "x \<in> {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
    obtain p i where x: "x = (p, i)"
      by (cases x)
    from xin have p: "p \<in> set pats"
      and i: "i < length text"
      and s: "suffix p (take (Suc i) text)"
      by (auto simp: x occurs_ending_at_def)
    have "suffix p (ac_state pats (take (Suc i) text))"
      using pattern_suffix_ac_state_iff[OF p, of "take (Suc i) text"] s by simp
    with p i have "(p, i) \<in> set (ac_search_from pats [] 0 text)"
      by (auto simp: in_ac_search_from_iff)
    then show "x \<in> set (ac_search pats text)"
      by (simp add: x ac_search_def)
  qed
qed

theorem ac_search_states_correct:
  "set (ac_search_states pats text) =
     {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
  by (simp add: ac_search_states_eq ac_search_correct)

theorem ac_search_fail_correct:
  "set (ac_search_fail pats text) =
     {(p, i). p \<in> set pats \<and> occurs_ending_at p text i}"
  by (simp add: ac_search_fail_eq ac_search_correct)

end
