(* Authors: Tassilo Lemke, Tobias Nipkow *)

section\<open>LTS-based Automata\<close>

theory LTS_Automata
imports Labeled_Transition_System
begin

text\<open>An automaton \<open>M\<close> is a triple \<open>(T, S, F)\<close>, where \<open>T\<close> is the transition system,
  \<open>S\<close> is the start state and \<open>F\<close> are the final states.
  This is just a thin layer on top of \<open>lts\<close>.
  NB: \<open>T\<close> may be infinite (but we require to finiteness in crucial places).\<close>

record ('s, 't) auto =
  lts :: "('s, 't) lts"
  start :: 's
  finals :: "'s set"

text\<open>
  The language \<open>L(M)\<close> of an automaton \<open>M\<close> is defined as the set of words that
  reach at least one final state from the start state:
\<close>

abbreviation accepts_auto :: "('s, 't) auto \<Rightarrow> 't list \<Rightarrow> bool" where
  "accepts_auto M \<equiv> accepts_lts (lts M) (start M) (finals M)"

abbreviation Lang_auto :: "('s, 't) auto \<Rightarrow> 't list set" where
  "Lang_auto M \<equiv> Lang_lts (lts M) (start M) (finals M)"


subsection \<open>Sequential Composition of Automata\<close>

text \<open>We will later provide concrete example of automata accepting specific languages.
While proving that an automaton accepts a certain language often is straightforward,
proving that the automaton only accepts that language is a much more difficult task.
The lemma below provides a powerful tool to make these proofs manageable. It shows that
if two automata over disjoint state sets are connected via a single uni-directional bridge,
every word that reaches from the first set of states to a state within the second set of state must,
at some point, pass this bridge, and have a prefix within the first set of states
and a suffix within the second set.\<close>

lemma auto_merge:
  assumes "s\<^sub>A \<in> A" and "f\<^sub>A \<in> A" and "s\<^sub>B \<in> B" and "f\<^sub>B \<in> B" and "A \<inter> B = {}"
    and sideA: "\<forall>(q,c,q') \<in> T\<^sub>A. q \<in> A \<and> q' \<in> A"
    and sideB: "\<forall>(q,c,q') \<in> T\<^sub>B. q \<in> B \<and> q' \<in> B"
    and "f\<^sub>B \<in> steps_lts (T\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> T\<^sub>B) w s\<^sub>A"
  shows "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A@[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps_lts T\<^sub>A w\<^sub>A s\<^sub>A \<and> f\<^sub>B \<in> steps_lts T\<^sub>B w\<^sub>B s\<^sub>B"
using assms(1,8) proof (induction w arbitrary: s\<^sub>A)
  case Nil
  then have "steps_lts (T\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> T\<^sub>B) [] s\<^sub>A = {s\<^sub>A}"
    by (simp add: Steps_lts_def)
  then show ?case
    using Nil.prems assms(4,5) by fast
next
  case (Cons a w)
  define T where "T \<equiv> T\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> T\<^sub>B"

  \<comment> \<open>Obtain intermediate state after reading \<open>a\<close>:\<close>
  note \<open>f\<^sub>B \<in> steps_lts (T\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> T\<^sub>B) (a#w) s\<^sub>A\<close>
  then obtain q where a_step: "q \<in> steps_lts T [a] s\<^sub>A"
    and w_step: "f\<^sub>B \<in> steps_lts T w q"
    unfolding T_def using Steps_lts_split by force

  \<comment> \<open>There are now two options:\<close>
  \<comment> \<open>1. \<open>a\<close> directly traverses the bridge to \<open>B\<close>, so \<open>a = c\<close>.\<close>
  \<comment> \<open>2. \<open>a\<close> remains within \<open>A\<close> and we can use the IH.\<close>
  then show ?case
  proof (cases "(s\<^sub>A, a, q) \<notin> T\<^sub>A")
    case True
    moreover have "(s\<^sub>A, a, q) \<notin> T\<^sub>B"
      using Cons.prems(1) assms(5,7) by fast
    moreover have "(s\<^sub>A, a, q) \<in> T"
      using a_step by (auto simp: steps_lts_defs)
    ultimately have "s\<^sub>A = f\<^sub>A" and "a = c" and "q = s\<^sub>B"
      unfolding T_def by simp+

    have inB: "s\<^sub>B \<in> B \<Longrightarrow> f\<^sub>B \<in> steps_lts T w s\<^sub>B \<Longrightarrow> f\<^sub>B \<in> steps_lts T\<^sub>B w s\<^sub>B"
    proof (induction w arbitrary: s\<^sub>B)
      case Nil
      then show ?case
        by (simp add: Steps_lts_def)
    next
      case (Cons x xs)
      then obtain q where "f\<^sub>B \<in> steps_lts T xs q" and "q \<in> steps_lts T [x] s\<^sub>B"
        using Steps_lts_split by force
      then have "(s\<^sub>B, x, q) \<in> T"
        by (auto simp: steps_lts_defs)
      moreover have "s\<^sub>B \<in> B"
        using Cons by simp
      ultimately have "(s\<^sub>B, x, q) \<in> T\<^sub>B" and "q \<in> B"
        unfolding T_def using assms(2,5,6,7) by blast+
      then have "q \<in> steps_lts T\<^sub>B [x] s\<^sub>B"
        by (auto simp: steps_lts_defs) force
      moreover have "f\<^sub>B \<in> steps_lts T\<^sub>B xs q"
        using \<open>f\<^sub>B \<in> steps_lts T xs q\<close> \<open>q \<in> B\<close> Cons by simp
      ultimately show ?case
        using Steps_lts_join by force
    qed

    \<comment> \<open>The bridge is directly traversed, so \<open>A\<close> can be ignored:\<close>
    have "a#w = []@[c]@w"
      by (simp add: \<open>a = c\<close>)
    moreover have "f\<^sub>A \<in> steps_lts T\<^sub>A [] s\<^sub>A"
      by (simp add: \<open>s\<^sub>A = f\<^sub>A\<close> Steps_lts_def)
    moreover have "f\<^sub>B \<in> steps_lts T\<^sub>B w s\<^sub>B"
      using w_step assms(3) inB by (simp add: \<open>q = s\<^sub>B\<close>)
    ultimately show ?thesis
      by blast
  next
    case False
    then have a_step': "q \<in> steps_lts T\<^sub>A [a] s\<^sub>A"
      by (auto simp: steps_lts_defs) (force)
    then have "q \<in> A"
      using False Cons.prems(1) assms(6) by fast

    \<comment> \<open>Introduce the IH:\<close>
    then have "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A @[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps_lts T\<^sub>A w\<^sub>A q \<and> f\<^sub>B \<in> steps_lts T\<^sub>B w\<^sub>B s\<^sub>B"
      by (rule Cons.IH; use Cons.prems w_step[unfolded T_def] in simp)
    then obtain w\<^sub>A w\<^sub>B where "w = w\<^sub>A @[c]@w\<^sub>B" and "f\<^sub>A \<in> steps_lts T\<^sub>A w\<^sub>A q" and "f\<^sub>B \<in> steps_lts T\<^sub>B w\<^sub>B s\<^sub>B"
      by blast
    moreover then have "f\<^sub>A \<in> steps_lts T\<^sub>A (a#w\<^sub>A) s\<^sub>A"
      using a_step' Steps_lts_join by force
    ultimately have "a#w = a#w\<^sub>A@[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps_lts T\<^sub>A (a#w\<^sub>A) s\<^sub>A \<and> f\<^sub>B \<in> steps_lts T\<^sub>B w\<^sub>B s\<^sub>B"
      by simp
    then show ?thesis
      by (intro exI) auto
  qed
qed


subsection\<open>Concrete Automata\<close>

text \<open>We now present three concrete automata that accept certain languages.\<close>

subsubsection \<open>Universe over specific Alphabet\<close>

text\<open>This automaton accepts exactly the words that only contains letters from a given alphabet \<open>\<Sigma>\<close>.\<close>

definition loop_lts :: "'s \<Rightarrow> 'a set \<Rightarrow> ('s \<times> 'a \<times> 's) set" where
  "loop_lts q \<Sigma> \<equiv> {q} \<times> \<Sigma> \<times> {q}"

lemma loop_lts_fin: "finite \<Sigma> \<Longrightarrow> finite (loop_lts q \<Sigma>)"
  by (simp add: loop_lts_def)

lemma loop_lts_correct1: "set w \<subseteq> \<Sigma> \<Longrightarrow> steps_lts (loop_lts q \<Sigma>) w q = {q}"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: Steps_lts_def)
next
  case (Cons w ws)
  then have "steps_lts (loop_lts q \<Sigma>) [w] q = {q}"
    unfolding loop_lts_def steps_lts_defs by fastforce
  moreover have "steps_lts (loop_lts q \<Sigma>) ws q = {q}"
    using Cons by simp
  ultimately show ?case
    by (simp add: Steps_lts_def)
qed

lemma loop_lts_correct2: "\<not> set w \<subseteq> \<Sigma> \<Longrightarrow> steps_lts (loop_lts q \<Sigma>) w q = {}"
proof (induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons w ws)
  then consider "w \<notin> \<Sigma>" | "\<not> set ws \<subseteq> \<Sigma>"
    by auto
  then show ?case
  proof (cases)
    case 1
    then have "steps_lts (loop_lts q \<Sigma>) [w] q = {}"
      by (auto simp: loop_lts_def steps_lts_defs)
    moreover have "Steps_lts (loop_lts q \<Sigma>) ws {} = {}"
      by (meson Steps_lts_path ex_in_conv)
    ultimately show ?thesis
      by (metis Steps_lts_split all_not_in_conv append_Cons append_Nil)
  next
    case 2
    then have "steps_lts (loop_lts q \<Sigma>) ws q = {}"
      using Cons by simp
    moreover have "steps_lts (loop_lts q \<Sigma>) [w] q \<subseteq> {q}"
      by (auto simp: loop_lts_def steps_lts_defs)
    ultimately show ?thesis
      by (metis Steps_lts_def Steps_lts_mono Un_insert_right ex_in_conv fold_simps(1,2) insert_absorb insert_not_empty sup.absorb_iff1)
  qed
qed

lemmas loop_lts_correct = loop_lts_correct1 loop_lts_correct2

definition auto_univ :: "'a set \<Rightarrow> (unit, 'a) auto" where
  "auto_univ \<Sigma> \<equiv> \<lparr>
    lts = loop_lts () \<Sigma>,
    start = (),
    finals = {()}
  \<rparr>"

lemma auto_univ_lang[simp]: "Lang_auto (auto_univ \<Sigma>) = {w. set w \<subseteq> \<Sigma>}"
proof -
  define T where "T \<equiv> loop_lts () \<Sigma>"
  have "\<And>w. set w \<subseteq> \<Sigma> \<longleftrightarrow> () \<in> steps_lts T w ()"
    unfolding T_def using loop_lts_correct by fast
  then show ?thesis
    by (auto simp: T_def auto_univ_def)
qed


subsubsection\<open>Fixed Character with Arbitrary Prefix/Suffix\<close>

text\<open>
  This automaton accepts exactly those words that contain a specific letter \<open>c\<close> at some point,
  and whose prefix and suffix are contained within the alphabets \<open>\<Sigma>p\<close> and \<open>\<Sigma>s\<close>.
\<close>

definition pcs_lts :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> (nat \<times> 'a \<times> nat) set" where
  "pcs_lts \<Sigma>p c \<Sigma>s \<equiv> loop_lts 0 \<Sigma>p \<union> {(0, c, 1)} \<union> loop_lts 1 \<Sigma>s"

lemma pcs_lts_fin: "finite \<Sigma>p \<Longrightarrow> finite \<Sigma>s \<Longrightarrow> finite (pcs_lts \<Sigma>p c \<Sigma>s)"
  by (auto intro: loop_lts_fin simp: pcs_lts_def)

lemma pcs_lts_correct1:
  "(\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> \<Sigma>p \<and> set s \<subseteq> \<Sigma>s) \<Longrightarrow> 1 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) w 0"
proof -
  assume "\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> \<Sigma>p \<and> set s \<subseteq> \<Sigma>s"
  then obtain p s where "w = p@[c]@s" and "set p \<subseteq> \<Sigma>p" and "set s \<subseteq> \<Sigma>s"
    by blast
  moreover hence "0 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) p 0"
    by (metis pcs_lts_def steps_lts_union loop_lts_correct1 singletonI)
  moreover have "1 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) [c] 0"
    unfolding pcs_lts_def steps_lts_defs by force
  moreover have "1 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) s 1"
    by (metis calculation(3) inf_sup_ord(3) insertI1 pcs_lts_def steps_lts_mono' loop_lts_correct1 sup_commute)
  ultimately show "1 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) w 0"
    using Steps_lts_join by meson
qed

lemma pcs_lts_correct2:
  assumes "1 \<in> steps_lts (pcs_lts \<Sigma>p c \<Sigma>s) w 0"
  shows "\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> \<Sigma>p \<and> set s \<subseteq> \<Sigma>s"
proof -
  define T\<^sub>A where [simp]: "T\<^sub>A \<equiv> loop_lts (0::nat) \<Sigma>p"
  define T\<^sub>B where [simp]: "T\<^sub>B \<equiv> loop_lts (1::nat) \<Sigma>s"

  have "1 \<in> steps_lts (T\<^sub>A \<union> {(0, c, 1)} \<union> T\<^sub>B) w 0"
    using assms by (simp add: pcs_lts_def)
  then have "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A@[c]@w\<^sub>B \<and> 0 \<in> steps_lts T\<^sub>A w\<^sub>A 0 \<and> 1 \<in> steps_lts T\<^sub>B w\<^sub>B 1"
    by (intro auto_merge[where A="{0}" and B="{1}"]) (simp add: loop_lts_def)+
  then obtain w\<^sub>A w\<^sub>B where w_split: "w = w\<^sub>A@[c]@w\<^sub>B" and "0 \<in> steps_lts T\<^sub>A w\<^sub>A 0" and "1 \<in> steps_lts T\<^sub>B w\<^sub>B 1"
    by blast
  then have "set w\<^sub>A \<subseteq> \<Sigma>p" and "set w\<^sub>B \<subseteq> \<Sigma>s"
    using loop_lts_correct2 by fastforce+
  then show ?thesis
    using w_split by blast
qed

lemmas pcs_lts_correct = pcs_lts_correct1 pcs_lts_correct2

definition cps_auto :: "'a \<Rightarrow> 'a set \<Rightarrow> (nat, 'a) auto" where
  "cps_auto c \<Sigma> \<equiv> \<lparr>
    lts = pcs_lts \<Sigma> c \<Sigma>,
    start = 0,
    finals = {1}
  \<rparr>"

lemma cps_auto_lang: "Lang_auto (cps_auto c U) = { \<alpha>@[c]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> U \<and> set \<beta> \<subseteq> U }"
  using pcs_lts_correct unfolding cps_auto_def
  by (metis (lifting) disjoint_insert(2) inf_bot_right select_convs(1,2,3))


subsubsection\<open>Singleton Language\<close>

text\<open>
  Last but not least, the automaton accepting exactly a single word can be inductively defined.
\<close>

lemma steps_lts_empty_lts: "w \<noteq> [] \<Longrightarrow> steps_lts {} w q\<^sub>0 = {}"
proof (induction w)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  moreover have "Steps_lts {} [w] {q\<^sub>0} = {}"
    by (simp add: steps_lts_defs)
  moreover have "Steps_lts {} ws {} = {}"
    using Steps_lts_noState by fast
  ultimately show ?case
    by (simp add: Steps_lts_def)
qed

fun word_lts :: "'a list \<Rightarrow> (nat \<times> 'a \<times> nat) set" where
  "word_lts (w#ws) = word_lts ws \<union> {(Suc (length ws), w, length ws)}" |
  "word_lts [] = {}"

lemma word_lts_domain:
  "(q, c, q') \<in> word_lts ws \<Longrightarrow> q \<le> length ws \<and> q' \<le> length ws"
  by (induction ws) auto

definition word_auto :: "'a list \<Rightarrow> (nat, 'a) auto" where
  "word_auto ws \<equiv> \<lparr> lts = word_lts ws, start = length ws, finals = {0} \<rparr>"

lemma word_lts_correct1:
  "0 \<in> steps_lts (word_lts ws) ws (length ws)"
proof (induction ws)
  case Nil
  then show ?case
    by (simp add: Steps_lts_def)
next
  case (Cons w ws)
  have "0 \<in> steps_lts (word_lts ws) ws (length ws)"
    using Cons.IH(1) by blast
  then have "0 \<in> steps_lts (word_lts (w#ws)) ws (length ws)"
    using steps_lts_mono' by (metis word_lts.simps(1) sup_ge1)
  moreover have "length ws \<in> steps_lts (word_lts (w#ws)) [w] (Suc (length ws))"
  proof -
    have "(Suc (length ws), w, length ws) \<in> word_lts (w#ws)"
      by simp
    then show ?thesis
      unfolding steps_lts_defs by force
  qed
  ultimately show ?case
    using Steps_lts_join by force
qed

lemma word_lts_correct2:
  "0 \<in> steps_lts (word_lts ws) ws' (length ws) \<Longrightarrow> ws = ws'"
proof (induction ws arbitrary: ws')
  case Nil
  then show ?case
    by (simp, metis equals0D steps_lts_empty_lts)
next
  case (Cons w ws)

  \<comment> \<open>Preparation to use @{thm [source] auto_merge}:\<close>
  define T\<^sub>B where [simp]: "T\<^sub>B \<equiv> word_lts ws"
  define B where [simp]: "B \<equiv> {n. n \<le> length ws}"
  define T where [simp]: "T \<equiv> {} \<union> {(Suc (length ws), w, length ws)} \<union> T\<^sub>B"

  \<comment> \<open>Apply @{thm [source] auto_merge}:\<close>
  have "0 \<in> steps_lts T ws' (length (w#ws))"
    using Cons.prems by simp
  moreover have "\<forall>(q, c, q')\<in>T\<^sub>B. q \<in> B \<and> q' \<in> B"
    using word_lts_domain by force
  ultimately have "\<exists>w\<^sub>A w\<^sub>B. ws' = w\<^sub>A@[w]@w\<^sub>B \<and> (Suc (length ws)) \<in> steps_lts {} w\<^sub>A (Suc (length ws)) \<and> 0 \<in> steps_lts T\<^sub>B w\<^sub>B (length ws)"
    by (intro auto_merge[where A="{Suc (length ws)}" and B=B]) simp+
  then obtain w\<^sub>A w\<^sub>B where ws'_split: "ws' = w\<^sub>A@[w]@w\<^sub>B"
      and w\<^sub>A_step: "(length (w#ws)) \<in> steps_lts {} w\<^sub>A (length (w#ws))"
      and w\<^sub>B_step: "0 \<in> steps_lts T\<^sub>B w\<^sub>B (length ws)"
    by force

  have "w\<^sub>A = []"
    using w\<^sub>A_step steps_lts_empty_lts by fast

  \<comment> \<open>Use IH to show that \<open>w\<^sub>B = ws\<close>:\<close>
  have "ws = w\<^sub>B"
    by (intro Cons.IH, use w\<^sub>B_step in simp)

  then show ?case
    using ws'_split by (simp add: \<open>w\<^sub>A = []\<close> \<open>ws = w\<^sub>B\<close>)
qed

lemmas word_lts_correct = word_lts_correct1 word_lts_correct2

lemma word_auto_lang[simp]: "Lang_auto (word_auto w) = {w}"
  unfolding word_auto_def using word_lts_correct[of w] by auto

lemma word_auto_finite_lts: "finite (lts (word_auto w))"
proof -
  have "finite (word_lts w)"
    by (induction w) simp+
  then show ?thesis
    by (simp add: word_auto_def)
qed

hide_const (open) lts start finals (* hide common names *)
term auto.start (* qualified names still work *)

end
