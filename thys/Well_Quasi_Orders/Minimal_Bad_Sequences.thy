(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c-sterna@jaist.ac.jp>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

header {* Constructing Minimal Bad Sequences *}

theory Minimal_Bad_Sequences
imports
  "../Abstract-Rewriting/Seq"
  Restricted_Predicates
begin

definition good :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a seq \<Rightarrow> bool" where
  "good P f \<equiv> \<exists>i j. i < j \<and> P (f i) (f j)"

abbreviation bad where "bad P f \<equiv> \<not> good P f"

subsection {* Piecing Together Infinite Sequences *}

text {*Replace the elements of an infinite sequence, starting from a given
position, by those of another infinite sequence.*}
definition repl :: "nat \<Rightarrow> 'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
  "repl i f g \<equiv> \<lambda>j. if j \<ge> i then g j else f j"

lemma repl_0 [simp]:
  "repl 0 f g = g"
  by (simp add: repl_def)

lemma repl_simps [simp]:
  "j \<ge> i \<Longrightarrow> repl i f g j = g j"
  "j < i \<Longrightarrow> repl i f g j = f j"
  by (auto simp: repl_def)

lemma repl_ident [simp]:
   "repl i f f = f"
   by (auto simp: repl_def)

lemma repl_repl_ident [simp]:
  "repl n f (repl n g h) = repl n f h"
  by (auto simp: repl_def)

lemma repl_repl_ident' [simp]:
  "repl n (repl n f g) h = repl n f h"
  by (auto simp: repl_def)

lemma ex_repl_conv:
  "(\<exists>j\<ge>n. P (repl n f g j)) \<longleftrightarrow> (\<exists>j\<ge>n. P (g j))"
  by auto

lemma repl_1 [simp]:
  assumes "f 0 = g 0"
  shows "repl (Suc 0) f g = g"
proof
  fix i show "repl (Suc 0) f g i = g i"
    by (induct i) (simp_all add: assms)
qed

lemma bad_repl:
  assumes "\<forall>i. f i \<ge> f 0" and "\<forall>i j. i > j \<longrightarrow> f i > f j"
    and "bad P (repl (f 0) A B)" (is "bad P ?A")
  shows "bad P (B \<circ> f)"
proof
  assume "good P (B \<circ> f)"
  then obtain i j where "i < j" and "P (B (f i)) (B (f j))" by (auto simp: good_def)
  hence "P (?A (f i)) (?A (f j))" using assms by auto
  moreover from `i < j` have "f i < f j" using assms by auto
  ultimately show False using assms(3) by (auto simp: good_def)
qed

fun minimal_bad_seq :: "('a seq \<Rightarrow> nat \<Rightarrow> 'a seq) \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" where
  "minimal_bad_seq A f 0 = A f 0"
| "minimal_bad_seq A f (Suc n) = (
    let g = minimal_bad_seq A f n in
    repl (Suc n) g (A g n))"

lemma choice2:
  "\<forall>x y. P x y \<longrightarrow> (\<exists>z. Q x y z) \<Longrightarrow> \<exists>f. \<forall>x y. P x y \<longrightarrow> Q x y (f x y)"
  using bchoice [of "{(x, y). P x y}" "\<lambda>(x, y) z. Q x y z"] by force

text {*A locale capturing the construction of minimal bad sequences over
\emph{values} from @{term "vals A"}. Where @{term "strong P"} is the order
that is used to check whether an infinite sequence is bad (here @{term P}
is an order on elements on which @{term "strong"} may rely), and @{term weak}
is the order that is used for checking minimality. The required properties are:
\begin{itemize}
\item @{term "weak"} has to be right-compatible with @{term "strong P"}
\item @{term "weak"} has to be well-founded on @{term "vals A"}
\item @{term "weak"} has to be transitive
\item @{term "weak"} reflects the property of being in @{term "vals A"}
\end{itemize}*}
locale mbs =
  fixes strong :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
    and weak :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and vals :: "'a set \<Rightarrow> 'b set"
  assumes strong_weak: "strong P x y \<Longrightarrow> weak y z \<Longrightarrow> strong P x z"
    and wfp_on_weak: "wfp_on weak (vals A)"
    and weak_trans: "weak x y \<Longrightarrow> weak y  z \<Longrightarrow> weak x z"
    and weak_vals: "weak x y \<Longrightarrow> y \<in> vals A \<Longrightarrow> x \<in> vals A"
begin

abbreviation weakeq where "weakeq \<equiv> weak\<^sup>=\<^sup>="

lemma strong_weakeq: "strong P x y \<Longrightarrow> weakeq y z \<Longrightarrow> strong P x z"
  using strong_weak by auto

lemma weakeq_trans: "weakeq x y \<Longrightarrow> weakeq y z \<Longrightarrow> weakeq x z"
  using weak_trans by auto

lemma weakeq_vals: "weakeq x y \<Longrightarrow> y \<in> vals A \<Longrightarrow> x \<in> vals A"
  using weak_vals by auto

text {*The following lemma is the reason for the suffix condition that
is used throughout.*}
lemma bad_strong_repl:
  assumes "bad (strong P) f"
    and "bad (strong P) g"
    and "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (g i) (f j)"
  shows "bad (strong P) (repl n f g)" (is "bad ?P ?f")
proof (rule ccontr)
  presume "good ?P ?f"
  then obtain i j where "i < j"
    and good: "?P (?f i) (?f j)" by (auto simp: good_def)
  {
    assume "j < n"
    with `i < j` and good have "?P (f i) (f j)" by simp
    with assms(1) have False using `i < j` by (auto simp: good_def)
  } moreover {
    assume "n \<le> i"
    with `i < j` and good have "?P (g i) (g j)" by auto
    with assms(2) have False using `i < j` by (auto simp: good_def)
  } moreover {
    assume "i < n" and "n \<le> j"
    with assms(3) obtain k where "k \<ge> n" and weakeq: "weakeq (g j) (f k)" by blast
    from `i < j` and `i < n` and `n \<le> j` and good
      have "?P (f i) (g j)" by auto
    from strong_weakeq [OF this weakeq] have "?P (f i) (f k)" .
    with `i < n` and `n \<le> k` and assms(1) have False by (auto simp: good_def)
  } ultimately show False using `i < j` by arith
qed simp


text {*An infinite sequence, is minimal at position @{text n}, if
every subsequence that coincides on the first @{text "n - 1"} elements is good,
whenever the @{text n}-th element is replaced by a smaller one.*}
definition min_at :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b seq \<Rightarrow> nat \<Rightarrow> bool" where
  "min_at P f n \<equiv>
    \<forall>g. (\<forall>i<n. g i = f i) \<and> weak (g n) (f n) \<and> (\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (g i) (f j))
    \<longrightarrow> good (strong P) g"

lemma weak_induct [consumes 1, case_names IH]:
  assumes "x \<in> vals A"
    and "\<And>x. x \<in> vals A \<Longrightarrow> (\<And>y. y \<in> vals A \<Longrightarrow> weak y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_weak, of x A P] and assms by blast

lemma weak_imp_weakeq: "weak x y \<Longrightarrow> weakeq x y" by auto

lemma suffix_repl:
  assumes "m \<ge> n"
    and suffix: "\<forall>i\<ge>m. \<exists>j\<ge>m. weakeq (h i) (f j)"
    and *: "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (e i) (repl m f h j)"
    (is "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (e i) (?g j)")
  shows "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (e i) (f j)"
proof (intro allI impI)
  fix i assume "n \<le> i"
  with * obtain j where "j \<ge> n"
    and **: "weakeq (e i) (?g j)" by auto
  show "\<exists>j\<ge>n. weakeq (e i) (f j)"
  proof (cases "j < m")
    case True with ** show ?thesis
      using `j \<ge> n` and `m \<ge> n` by auto
  next
    case False
    with `j \<ge> n` and `m \<ge> n` have "j \<ge> m" by auto
    with ** have "weakeq (e i) (h j)" by auto
    with suffix obtain k where "k \<ge> m"
      and "weakeq (h j) (f k)" using `j \<ge> m` by auto
    with `weakeq (e i) (h j)` have "weakeq (e i) (f k)" using weakeq_trans by blast
    moreover from `k \<ge> m` and `m \<ge> n` have "k \<ge> n" by auto
    ultimately show ?thesis by blast
  qed
qed

text {*Constructing a bad sequence that is minimal at @{term "Suc n"}
from a bad sequence that is minimal at @{term n}. Moreover, the first
@{term n} elements coincide with the given sequence (hence minimality
at @{term n} is preserved) and the remaining elements are weakly
related to the remaining elements of the given sequence.*}
(*same proof as for minimal_bad_Suc, but with explicit structure
of induction (better suited for textual explanation)*)
lemma
  assumes "f (Suc n) \<in> vals A"
    and "min_at P f n"
    and "bad (strong P) f" (is "bad ?P f")
  shows "\<exists>g.
    (\<forall>i\<le>n. g i = f i) \<and>
    weakeq (g (Suc n)) (f (Suc n)) \<and>
    (\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (g i) (f j)) \<and>
    bad (strong P) (repl (Suc n) f g) \<and>
    min_at P (repl(Suc n) f g) (Suc n)"
  (is "?C f (f (Suc n))")
proof -
  let ?I = "\<lambda>x. \<forall>f.
    x = f (Suc n) \<and> x \<in> vals A \<and> min_at P f n \<and> bad ?P f \<longrightarrow> ?C f x"
  {
    fix x
    assume "x = f (Suc n)"
    hence "x \<in> vals A" using assms by simp
    hence "?I x"
    proof (induct x rule: weak_induct)
      fix x
      assume "x \<in> vals A" and IH: "\<And>y. \<lbrakk>y \<in> vals A; weak y x\<rbrakk> \<Longrightarrow> ?I y"
      show "?I x"
      proof (intro allI impI, elim conjE)
        fix f
        assume x: "x = f (Suc n)" and "x \<in> vals A"
          and "min_at P f n" and "bad ?P f"
        show "?C f x"
        proof (cases "min_at P f (Suc n)")
          case True
          hence "min_at P (repl (Suc n) f f) (Suc n)" by simp
          moreover have "weakeq x x" by simp
          moreover from `bad ?P f` have "bad ?P (repl (Suc n) f f)" by simp
          ultimately show ?thesis unfolding x by blast
        next
          case False
          then obtain h
            where weak: "weak (h (Suc n)) (f (Suc n))"
            and suffix: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (h i) (f j)"
            and "bad (strong P) h" by (auto simp: min_at_def)
          let ?g = "repl (Suc n) f h"
          from weak have weak': "weak (?g (Suc n)) (f (Suc n))" by simp
          have min_at: "min_at P ?g n"
            using suffix_repl [OF _ suffix, of n]
            and `min_at P f n` by (auto simp: min_at_def)
          have bad: "bad (strong P) ?g"
            using bad_strong_repl [OF `bad (strong P) f` `bad (strong P) h`, of "Suc n", OF suffix] .
          let ?g' = "repl (Suc n) ?g"
          have "?g (Suc n) \<in> vals A"
            using weak_vals [OF weak `x \<in> vals A` [unfolded x]] by simp
          from IH [unfolded x, OF this weak', THEN spec [of _ ?g]]
            and min_at and bad and this obtain M
            where "\<forall>i\<le>n. M i = ?g i"
            and "weakeq (M (Suc n)) (?g (Suc n))"
            and *: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (M i) (?g j)"
            and "bad (strong P) (?g' M)"
            and "min_at P (?g' M) (Suc n)" by blast
          moreover with weak_imp_weakeq [OF weak]
            have "weakeq (M (Suc n)) (f (Suc n))"
            using weakeq_trans [of "M (Suc n)" "?g (Suc n)"] by auto
          moreover have "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (M i) (f j)"
            by (rule suffix_repl [OF _ suffix *]) simp
          ultimately show ?thesis unfolding x by auto
        qed
      qed
    qed
  }
  hence "\<And>x. x = f (Suc n) \<Longrightarrow> ?I x" .
  from this [OF refl, THEN spec [of _ f]] and assms
    show ?thesis by blast
qed

lemma minimal_bad_Suc:
  assumes "f (Suc n) \<in> vals A"
    and "min_at P f n"
    and "bad (strong P) f"
  shows "\<exists>g.
    (\<forall>i\<le>n. g i = f i) \<and>
    weakeq (g (Suc n)) (f (Suc n)) \<and>
    (\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (g i) (f j)) \<and>
    bad (strong P) (repl (Suc n) f g) \<and>
    min_at P (repl (Suc n) f g) (Suc n)"
using assms
proof (induct x\<equiv>"f (Suc n)" arbitrary: f rule: weak_induct)
  case IH show ?case
  proof (cases "min_at P f (Suc n)")
    case True
    with `bad (strong P) f` show ?thesis
      by (metis (full_types) repl_ident sup2CI)
  next
    case False
    then obtain h
      where weak: "weak (h (Suc n)) (f (Suc n))"
      and suffix: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (h i) (f j)"
      and "bad (strong P) h" by (auto simp: min_at_def)
    let ?g = "repl (Suc n) f h"
    from weak have weak': "weak (?g (Suc n)) (f (Suc n))" by simp
    have min_at: "min_at P ?g n"
      using suffix_repl [OF _ suffix, of n]
      and `min_at P f n` by (auto simp: min_at_def)
    have bad: "bad (strong P) ?g"
      using bad_strong_repl [OF `bad (strong P) f` `bad (strong P) h`, of "Suc n", OF suffix] .
    let ?g' = "repl (Suc n) ?g"
    have "?g (Suc n) \<in> vals A" using weak_vals [OF weak IH(1)] by simp
    from IH(2) [of ?g, OF this, OF weak' min_at bad] obtain M
      where "\<forall>i\<le>n. M i = ?g i"
      and "weakeq (M (Suc n)) (?g (Suc n))"
      and *: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (M i) (?g j)"
      and "bad (strong P) (?g' M)"
      and "min_at P (?g' M) (Suc n)" by auto
    moreover with weak_imp_weakeq [OF weak]
      have "weakeq (M (Suc n)) (f (Suc n))"
      using weakeq_trans [of "M (Suc n)" "?g (Suc n)"] by auto
    moreover have "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (M i) (f j)"
      by (rule suffix_repl [OF _ suffix *]) simp
    ultimately show ?thesis by auto
  qed
qed

text {*If there is a bad sequence, then there is a bad sequence that is
minimal at its first element (used for the base case of constructing a
minimal bad sequence.*}
lemma minimal_bad_0:
  assumes "f 0 \<in> vals A"
    and "bad (strong P) f"
  shows "\<exists>g. (\<forall>i. \<exists>j. weakeq (g i) (f j)) \<and> min_at P g 0 \<and> bad (strong P) g"
using assms
proof (induct x\<equiv>"f 0" arbitrary: f rule: weak_induct)
  case IH show ?case
  proof (cases "min_at P f 0")
    case True with IH show ?thesis by blast
  next
    case False
    then obtain h
      where weak: "weak (h 0) (f 0)"
      and suffix: "\<forall>i\<ge>0. \<exists>j\<ge>0. weakeq (h i) (f j)"
      and bad: "bad (strong P) h"
      unfolding min_at_def by auto
    have "h 0 \<in> vals A"
      using weak_vals [OF weak IH(1)] .
    from IH(2) [of h, OF this weak bad] obtain e
      where "\<forall>i. \<exists>j. weakeq (e i) (h j)"
      and "min_at P e 0"
      and "bad (strong P) e" by auto
    moreover with suffix
      have "\<forall>i. \<exists>j. weakeq (e i) (f j)" using weakeq_trans by fast
    ultimately show ?thesis by blast
  qed
qed

lemma iterated_weakeq:
  assumes "\<forall>n>0::nat. \<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (g n i) (g (n - 1) j)"
    and "m \<le> n"
  shows "\<forall>i\<ge>n. \<exists>j\<ge>m. weakeq (g n i) (g m j)"
using assms(2)
proof (induct "n - m" arbitrary: n)
  case 0 thus ?case by auto
next
  case (Suc k)
  then obtain n' where n: "n = Suc n'" by (cases n) auto
  with Suc have "k = n' - m" and "m \<le> n'" by auto
  have "n > 0" by (auto simp: n)
  show ?case
  proof (intro allI impI)
    fix i assume "i \<ge> n"
    with assms(1) [rule_format, OF `n > 0`] obtain j where "j \<ge> n"
      and "weakeq (g (Suc n') i) (g n' j)" by (auto simp: n)
    with Suc(1) [OF `k = n' - m` `m \<le> n'`, THEN spec [of _ j]]
      obtain k where "k \<ge> m" and "weakeq (g n' j) (g m k)" by (auto simp: n)
    with `weakeq (g (Suc n') i) (g n' j)`
      have "weakeq (g n i) (g m k)" unfolding n using weakeq_trans by blast
    thus "\<exists>j\<ge>m. weakeq (g n i) (g m j)" using `k \<ge> m` by blast
  qed
qed

text {*If there is a bad sequence over elements of @{term "vals A"},
then there is a minimal (i.e., minimal at all positions) bad sequence
over elements of @{term "vals A"}.*}
lemma mbs:
  assumes "\<forall>i. f i \<in> vals A" and "bad (strong P) f" (is "bad ?P f")
  shows "\<exists>g.
    bad (strong P) g \<and>
    (\<forall>n. min_at P g n) \<and>
    (\<forall>i. g i \<in> vals A)"
proof -
  from assms have "f 0 \<in> vals A" by simp
  from minimal_bad_0 [of f, OF this `bad ?P f`] obtain g
    where "\<forall>i. \<exists>j. weakeq (g i) (f j)"
    and "min_at P g 0"
    and "bad ?P g"
    by blast
  with `\<forall>i. f i \<in> vals A`
    have "\<And>i. g i \<in> vals A"
    using weakeq_vals by blast
  from minimal_bad_Suc [of _ _ _ P]
    have "\<forall>f n.
    f (Suc n) \<in> vals A \<and>
    min_at P f n \<and>
    bad ?P f \<longrightarrow>
    (\<exists>M.
      (\<forall>i\<le>n. M i = f i) \<and>
      weakeq (M (Suc n)) (f (Suc n)) \<and>
      (\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (M i) (f j)) \<and>
      bad ?P (repl (Suc n) f M) \<and>
      min_at P (repl (Suc n) f M) (Suc n))"
    (is "\<forall>f n. ?Q f n \<longrightarrow> (\<exists>M. ?Q' f n M)")
    by blast
  from choice2 [OF this] obtain M
    where * [rule_format]: "\<forall>f n. ?Q f n \<longrightarrow> ?Q' f n (M f n)" by force
  let ?g = "minimal_bad_seq M g"
  let ?A = "\<lambda>i. ?g i i"
  have "\<forall>n. (\<forall>i\<ge>n. ?g n i \<in> vals A)
    \<and> (n = 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (?g n i) (g j)))
    \<and> (n > 0 \<longrightarrow> (\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (?g n i) (?g (n - 1) j)))
    \<and> (\<forall>i\<le>n. min_at P (?g n) i)
    \<and> (\<forall>i\<le>n. ?A i = ?g n i)
    \<and> bad ?P (?g n)" (is "\<forall>n. ?Q n")
  proof
    fix n
    show "?Q n"
    proof (induction n)
      case 0
      have "\<forall>i\<ge>0. g i \<in> vals A" using `\<And>i. g i \<in> vals A` by auto
      moreover have "min_at P g 0" by fact
      moreover have "bad ?P g" by fact
      ultimately
        have M [simp]: "M g 0 0 = g 0" and "weakeq (M g 0 (Suc 0)) (g (Suc 0))"
        and "bad ?P (M g 0)" and "min_at P (M g 0) (Suc 0)"
        and **: "\<forall>i\<ge>Suc 0. \<exists>j\<ge>Suc 0. weakeq (M g 0 i) (g j)"
        using * [of g 0] by auto
      moreover have "\<forall>i. ?g 0 i \<in> vals A"
          using ** and weakeq_vals and `\<And>i. g i \<in> vals A`
          by (auto) (metis M le_0_eq not_less_eq_eq)
      moreover have "min_at P (M g 0) 0"
      proof (unfold min_at_def, intro allI impI, elim conjE)
        fix e :: "'b seq"
        presume "weak (e 0) (g 0)" and *: "\<forall>i. \<exists>j\<ge>0. weakeq (e i) (M g 0 j)"
        have "\<forall>i. \<exists>j\<ge>0::nat. weakeq (e i) (g j)"
        proof (intro allI impI)
          fix i
          from * obtain j where "j \<ge> 0" and "weakeq (e i) (M g 0 j)" by auto
          show "\<exists>j\<ge>0. weakeq (e i) (g j)"
          proof (cases "j = 0")
            case True
            with `weakeq (e i) (M g 0 j)` have "weakeq (e i) (g 0)" by auto
            thus ?thesis by auto
          next
            case False
            hence "j \<ge> Suc 0" by auto
            with ** obtain k where "k \<ge> Suc 0" and "weakeq (M g 0 j) (g k)" by auto
            with `weakeq (e i) (M g 0 j)`
              have "weakeq (e i) (g k)" using weakeq_trans by blast
            moreover with `k \<ge> Suc 0` have "k \<ge> 0" by auto
            ultimately show ?thesis by blast
          qed
        qed
        with `min_at P g 0` [unfolded min_at_def]
        show "good ?P e" using `weak (e 0) (g 0)` by (simp add: min_at_def)
      qed auto
      moreover have "\<forall>i\<ge>0. \<exists>j\<ge>0. weakeq (?g 0 i) (g j)"
      proof (intro allI impI)
        fix i::nat
        assume "i \<ge> 0"
        hence "i = 0 \<or> i \<ge> Suc 0" by auto
        thus "\<exists>j\<ge>0. weakeq (?g 0 i) (g j)"
        proof
          assume "i \<ge> Suc 0"
          with ** obtain j where "j \<ge> Suc 0" and "weakeq (?g 0 i) (g j)" by auto
          moreover from this have "j \<ge> 0" by auto
          ultimately show "?thesis" by auto
        next
          assume "i = 0"
          hence "weakeq (?g 0 i) (g 0)" by auto
          thus ?thesis by blast
        qed
      qed
      ultimately show ?case by simp
    next
      case (Suc n)
      with * [of "?g n" n]
        have eq: "\<forall>i\<le>n. ?A i = ?g n i"
        and weak: "weakeq (?g (Suc n) (Suc n)) (?g n (Suc n))"
        and subseq: "\<forall>i\<ge>Suc n. \<exists>j\<ge>Suc n. weakeq (?g (Suc n) i) (?g n j)"
        and "bad ?P (?g (Suc n))"
        and min_at: "min_at P (?g (Suc n)) (Suc n)"
        by (simp_all add: Let_def)
      moreover have "\<forall>i\<ge>Suc n. ?g (Suc n) i \<in> vals A"
      proof (intro allI impI)
        fix i
        assume "i \<ge> Suc n"
        with subseq obtain j where "j \<ge> Suc n"
          and "weakeq (?g (Suc n) i) (?g n j)" by auto
        moreover with Suc have "?g n j \<in> vals A" by simp
        ultimately show "?g (Suc n) i \<in> vals A"
          using weakeq_vals by auto
      qed
      moreover have *: "\<forall>i\<le>Suc n. ?A i = ?g (Suc n) i"
      proof (intro allI impI)
        fix i assume "i \<le> Suc n"
        show "?A i = ?g (Suc n) i"
        proof (cases "i = Suc n")
          assume "i = Suc n"
          thus ?thesis by simp
        next
          assume "i \<noteq> Suc n"
          with `i \<le> Suc n` have "i < Suc n" by auto
          thus ?thesis by (simp add: Let_def eq)
        qed
      qed
      moreover have "\<forall>i\<le>Suc n. min_at P (?g (Suc n)) i"
      proof (intro allI impI)
        fix i assume "i \<le> Suc n"
        show "min_at P (?g (Suc n)) i"
        proof (cases "i = Suc n")
          case True with min_at show ?thesis by simp
        next
          case False with `i \<le> Suc n` have le: "i \<le> Suc n" "i \<le> n" by auto
          show ?thesis
          proof (unfold min_at_def, intro allI impI, elim conjE)
            fix e
            note * = * [rule_format, symmetric] eq [rule_format, symmetric]
            assume "\<forall>i'<i. e i' = ?g (Suc n) i'"
            hence 1: "\<forall>i'<i. e i' = ?g n i'" using * and le by auto
            assume "weak (e i) (?g (Suc n) i)"
            hence 2: "weak (e i) (?g n i)" using * and le by simp
            assume **: "\<forall>j\<ge>i. \<exists>k\<ge>i. weakeq (e j) (?g (Suc n) k)"
            have 3: "\<forall>j\<ge>i. \<exists>k\<ge>i. weakeq (e j) (?g n k)"
            proof (intro allI impI)
              fix j assume "i \<le> j"
              with ** obtain k where "k \<ge> i" and "weakeq (e j) (?g (Suc n) k)" by blast
              show "\<exists>k\<ge>i. weakeq (e j) (?g n k)"
              proof (cases "k \<le> n")
                case True with `weakeq (e j) (?g (Suc n) k)`
                  have "weakeq (e j) (?g n k)" using * by auto
                thus ?thesis using `k \<ge> i` by auto
              next
                case False hence "k \<ge> Suc n" by auto
                with subseq obtain l where "l \<ge> Suc n"
                  and "weakeq (?g (Suc n) k) (?g n l)" by blast
                with `weakeq (e j) (?g (Suc n) k)`
                  have "weakeq (e j) (?g n l)" using weakeq_trans by blast
                moreover from `i \<le> Suc n` and `l \<ge> Suc n` have "l \<ge> i" by auto
                ultimately show ?thesis by blast
              qed
            qed
            from 1 2 3 and Suc [THEN conjunct2, THEN conjunct2, THEN conjunct2] and `i \<le> n`
              show "good ?P e" unfolding min_at_def by blast
          qed
        qed
      qed
      ultimately show ?case by simp
    qed
  qed
  hence 1: "\<forall>n. \<forall>i\<le>n. min_at P (?g n) i"
    and 2: "\<forall>n. \<forall>i\<le>n. ?A i = ?g n i"
    and 3: "\<forall>n. bad ?P (?g n)"
    and 4: "\<forall>i. \<exists>j. weakeq (?g 0 i) (g j)"
    and 5: "\<forall>n>0. \<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (?g n i) (?g (n - 1) j)"
    by auto
  have ex_weakeq: "\<forall>n. \<forall>i. \<exists>j. weakeq (?g n i) (g j)"
  proof
    fix n show "\<forall>i. \<exists>j. weakeq (?g n i) (g j)"
    proof (induct n)
      case 0 with 4 show ?case by simp
    next
      case (Suc n)
      show ?case
      proof
        fix i
        have "i < Suc n \<or> i \<ge> Suc n" by auto
        thus "\<exists>j. weakeq (?g (Suc n) i) (g j)"
        proof
          assume "i < Suc n" hence "i \<le> Suc n" and "i \<le> n" by auto
          from `i \<le> Suc n` have "?g (Suc n) i = ?g i i" using 2 by auto
          moreover from `i \<le> n` have "?g n i = ?g i i" using 2 by auto
          ultimately have "?g (Suc n) i = ?g n i" by auto
          with Suc show ?thesis by auto
        next
          assume "i \<ge> Suc n"
          with 5 [THEN spec [of _ "Suc n"]]
            obtain j where "j \<ge> Suc n"
            and "weakeq (?g (Suc n) i) (?g n j)" by auto
          moreover from Suc obtain k where "weakeq (?g n j) (g k)" by blast
          ultimately show ?thesis using weakeq_trans by blast
        qed
      qed
    qed
  qed
  have bad: "bad ?P ?A"
  proof
    assume "good ?P ?A"
    then obtain i j :: nat where "i < j"
      and "?P (?g i i) (?g j j)" unfolding good_def by auto
    moreover with 2 [rule_format, of i j]
      have "?P (?g j i) (?g j j)" by auto
    ultimately have "good ?P (?g j)" unfolding good_def by blast
    with 3 show False by auto
  qed
  moreover have "\<forall>S n.
    (\<forall>i<n. S i = ?A i) \<and>
    weak (S n) (?A n) \<and>
    (\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (S i) (?A j)) \<longrightarrow> good ?P S"
  proof (intro allI impI, elim conjE)
    fix S n
    assume *: "\<forall>i<n. S i = ?A i"
      and "weak (S n) (?A n)"
      and **: "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (S i) (?A j)"
    from * have "\<forall>i<n. S i = ?g n i" using 2 by auto
    moreover have "weak (S n) (?A n)" by fact
    moreover have "\<forall>i\<ge>n. \<exists>j\<ge>n. weakeq (S i) (?g n j)"
      using iterated_weakeq [OF 5] and ** by (metis order_refl weakeq_trans)
    ultimately show "good ?P S"
      using 1 [rule_format, of n, OF le_refl, unfolded min_at_def] by auto
  qed
  moreover have "\<forall>i. ?A i \<in> vals A"
    using `\<And>i. g i \<in> vals A` and ex_weakeq and weakeq_vals by blast
  ultimately show ?thesis unfolding min_at_def by blast
qed

end

end
