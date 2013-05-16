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

lemma repl_1 [simp]:
  assumes "f 0 = g 0"
  shows "repl (Suc 0) f g = g"
proof
  fix i show "repl (Suc 0) f g i = g i"
    by (induct i) (simp_all add: assms)
qed

fun minimal_bad_seq :: "('a seq \<Rightarrow> nat \<Rightarrow> 'a seq) \<Rightarrow> 'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" where
  "minimal_bad_seq A f 0 = f"
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
  fixes strong :: "'a set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"
    and weak :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and vals :: "'a set \<Rightarrow> 'b set"
  assumes strong_weak: "z \<in> vals A \<Longrightarrow> strong A x y \<Longrightarrow> weak y z \<Longrightarrow> strong A x z"
    and wfp_on_weak: "wfp_on weak (vals A)"
    and weak_trans: "weak x y \<Longrightarrow> weak y z \<Longrightarrow> weak x z"
    and weak_vals: "weak x y \<Longrightarrow> y \<in> vals A \<Longrightarrow> x \<in> vals A"
begin

abbreviation weakeq where "weakeq \<equiv> weak\<^sup>=\<^sup>="

lemma strong_weakeq: "z \<in> vals A \<Longrightarrow> strong A x y \<Longrightarrow> weakeq y z \<Longrightarrow> strong A x z"
  using strong_weak by auto

lemma weakeq_trans: "weakeq x y \<Longrightarrow> weakeq y z \<Longrightarrow> weakeq x z"
  using weak_trans by auto

lemma weakeq_vals: "weakeq x y \<Longrightarrow> y \<in> vals A \<Longrightarrow> x \<in> vals A"
  using weak_vals by auto

lemma bad_strong_repl:
  assumes "\<forall>i. f i \<in> vals A"
    and "bad (strong A) f"
    and "bad (strong A) g"
    and "\<forall>i<n. f i = g i"
  shows "bad (strong A) (repl n f g)" (is "bad ?P ?f")
proof (rule ccontr)
  presume "good ?P ?f"
  then obtain i j where "i < j"
    and good: "?P (?f i) (?f j)" by (auto simp: good_def)
  {
    assume "j < n"
    with `i < j` and good have "?P (f i) (f j)" by simp
    with assms(2) have False using `i < j` by (auto simp: good_def)
  } moreover {
    assume "n \<le> i"
    with `i < j` and good have "?P (g i) (g j)" by auto
    with assms(3) have False using `i < j` by (auto simp: good_def)
  } moreover {
    assume "i < n" and "n \<le> j"
    with assms(4) have "f i = g i" by simp
    with `i < j` and `i < n` and `n \<le> j` and good
      have "?P (g i) (g j)" by simp
    with assms(3) and `i < j` have False by (auto simp: good_def)
  } ultimately show False using `i < j` by arith
qed simp

text {*An infinite sequence, is minimal at position @{text n}, if
every subsequence that coincides on the first @{text "n - 1"} elements is good,
whenever the @{text n}-th element is replaced by a smaller one.*}
definition min_at :: "'a set \<Rightarrow> 'b seq \<Rightarrow> nat \<Rightarrow> bool" where
  "min_at A f n \<equiv>
    \<forall>g. (\<forall>i. g i \<in> vals A) \<and> (\<forall>i<n. g i = f i) \<and> weak (g n) (f n) \<longrightarrow> good (strong A) g"

lemma weak_induct [consumes 1, case_names IH]:
  assumes "x \<in> vals A"
    and "\<And>x. x \<in> vals A \<Longrightarrow> (\<And>y. y \<in> vals A \<Longrightarrow> weak y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using wfp_on_induct [OF wfp_on_weak, of x A P] and assms by blast

lemma weak_imp_weakeq: "weak x y \<Longrightarrow> weakeq x y" by auto

text {*Constructing a bad sequence that is minimal at @{term "Suc n"}
from a bad sequence that is minimal at @{term n}. Moreover, the first
@{term n} elements coincide with the given sequence (hence minimality
at @{term n} is preserved) and the remaining elements are weakly
related to the remaining elements of the given sequence.*}
(*same proof as for minimal_bad_Suc, but with explicit structure
of induction (better suited for textual explanation)*)
lemma
  assumes "\<forall>i. f i \<in> vals A"
    and "min_at A f n"
    and "bad (strong A) f" (is "bad ?P f")
  shows "\<exists>g.
    (\<forall>i. g i \<in> vals A) \<and>
    (\<forall>i\<le>n. g i = f i) \<and>
    weakeq (g (Suc n)) (f (Suc n)) \<and>
    bad (strong A) (repl (Suc n) f g) \<and>
    min_at A (repl (Suc n) f g) (Suc n)"
  (is "\<exists>g. ?C g f (f (Suc n))")
proof -
  let ?I = "\<lambda>x. \<forall>f.
    x = f (Suc n) \<and> (\<forall>i. f i \<in> vals A) \<and> min_at A f n \<and> bad ?P f \<longrightarrow> (\<exists>g. ?C g f x)"
  {
    fix x
    assume "x = f (Suc n)"
    hence "x \<in> vals A" using assms by simp+
    hence "?I x"
    proof (induct x rule: weak_induct)
      fix x
      assume "x \<in> vals A" and IH: "\<And>y. \<lbrakk>y \<in> vals A; weak y x\<rbrakk> \<Longrightarrow> ?I y"
      show "?I x"
      proof (intro allI impI, elim conjE)
        fix f
        assume x: "x = f (Suc n)" and *: "\<forall>i. f i \<in> vals A"
          and "min_at A f n" and "bad ?P f"
        show "\<exists>g. ?C g f x"
        proof (cases "min_at A f (Suc n)")
          case True
          then have "min_at A (repl (Suc n) f f) (Suc n)" by simp
          moreover have "\<forall>i. f i \<in> vals A" by fact
          moreover have "weakeq x x" by simp
          moreover from `bad ?P f` have "bad ?P (repl (Suc n) f f)" by simp
          ultimately show ?thesis unfolding x by blast
        next
          case False
          then obtain h
            where weak: "weak (h (Suc n)) (f (Suc n))"
            and eq: "\<forall>i<Suc n. f i = h i"
            and vals: "\<forall>i. h i \<in> vals A"
            and "bad ?P h" by (auto simp: min_at_def)
          let ?g = "repl (Suc n) f h"
          have "?g (Suc n) \<in> vals A"
            using weak_vals [OF weak `x \<in> vals A` [unfolded x]] by simp
          moreover
          from weak have weak': "weak (?g (Suc n)) x" by (simp add: x)
          ultimately have "?I (?g (Suc n))" by (rule IH)
          moreover have vals: "\<forall>i. ?g i \<in> vals A"
          proof
            fix i show "?g i \<in> vals A" using vals and * by (cases "i < Suc n") simp+
          qed
          moreover have min_at: "min_at A ?g n"
            using `min_at A f n` by (auto simp: min_at_def)
          moreover have bad: "bad ?P ?g"
            using bad_strong_repl [OF * `bad ?P f` `bad ?P h`, of "Suc n", OF eq] .
          ultimately obtain M where C: "?C M ?g (?g (Suc n))" by blast
          moreover with weak_imp_weakeq [OF weak]
            have "weakeq (M (Suc n)) (f (Suc n))"
            using weakeq_trans [of "M (Suc n)" "?g (Suc n)"] by auto
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
  assumes "\<forall>i. f i \<in> vals A"
    and "min_at A f n"
    and "bad (strong A) f"
  shows "\<exists>g.
    (\<forall>i. g i \<in> vals A) \<and>
    (\<forall>i\<le>n. g i = f i) \<and>
    weakeq (g (Suc n)) (f (Suc n)) \<and>
    bad (strong A) (repl (Suc n) f g) \<and>
    min_at A (repl (Suc n) f g) (Suc n)"
  (is "\<exists>g. ?C g f (f (Suc n))")
using assms(1) [THEN spec, of "Suc n"] and assms
proof (induct x\<equiv>"f (Suc n)" arbitrary: f rule: weak_induct)
  let ?P = "strong A"
  case IH
  then have *: "\<forall>i. f i \<in> vals A" by simp
  show ?case
  proof (cases "min_at A f (Suc n)")
    case True
    with `bad ?P f` show ?thesis
      by (metis (full_types) repl_ident sup2CI *)
  next
    case False
    then obtain h
      where weak: "weak (h (Suc n)) (f (Suc n))"
      and eq: "\<forall>i<Suc n. f i = h i"
      and vals: "\<forall>i. h i \<in> vals A"
      and "bad ?P h" by (auto simp: min_at_def)
    let ?g = "repl (Suc n) f h"
    from weak have weak': "weak (?g (Suc n)) (f (Suc n))" by simp
    have min_at: "min_at A ?g n"
      using `min_at A f n` by (auto simp: min_at_def)
    have vals: "\<forall>i. ?g i \<in> vals A"
    proof
      fix i show "?g i \<in> vals A" using vals and * by (cases "i < Suc n") simp+
    qed
    have bad: "bad ?P ?g"
      using bad_strong_repl [OF * `bad ?P f` `bad ?P h`, of "Suc n", OF eq] .
    have "?g (Suc n) \<in> vals A" using weak_vals [OF weak IH(1)] by simp
    from IH(2) [of ?g, OF this weak' vals min_at bad] obtain M
      where C: "?C M ?g (?g (Suc n))" by blast
    moreover with weak_imp_weakeq [OF weak]
      have "weakeq (M (Suc n)) (f (Suc n))"
      using weakeq_trans [of "M (Suc n)" "?g (Suc n)"] by auto
    ultimately show ?thesis by auto
  qed
qed

text {*If there is a bad sequence, then there is a bad sequence that is
minimal at its first element (used for the base case of constructing a
minimal bad sequence.*}
lemma minimal_bad_0:
  assumes "\<forall>i. f i \<in> vals A"
    and "bad (strong A) f" (is "bad ?P f")
  shows "\<exists>g. (\<forall>i. g i \<in> vals A) \<and> min_at A g 0 \<and> bad ?P g"
using assms(1) [THEN spec, of "0"] and assms
proof (induct x\<equiv>"f 0" arbitrary: f rule: weak_induct)
  case IH show ?case
  proof (cases "min_at A f 0")
    case True with IH show ?thesis by blast
  next
    case False
    then obtain h
      where weak: "weak (h 0) (f 0)"
      and vals: "\<forall>i. h i \<in> vals A"
      and bad: "bad ?P h"
      unfolding min_at_def by auto
    have "h 0 \<in> vals A"
      using weak_vals [OF weak IH(1)] .
    from IH(2) [of h, OF this weak vals bad] obtain e
      where "\<forall>i. e i \<in> vals A"
      and "min_at A e 0"
      and "bad ?P e" by auto
    then show ?thesis by blast
  qed
qed

text {*If there is a bad sequence over elements of @{term "vals A"},
then there is a minimal (i.e., minimal at all positions) bad sequence
over elements of @{term "vals A"}.*}
lemma mbs:
  assumes "\<forall>i. f i \<in> vals A" and "bad (strong A) f" (is "bad ?P f")
  shows "\<exists>g.
    (\<forall>i. g i \<in> vals A) \<and>
    bad ?P g \<and>
    (\<forall>n. min_at A g n)"
proof -
  from minimal_bad_0 [of f, OF assms(1) `bad ?P f`] obtain g
    where "\<And>i. g i \<in> vals A"
    and "min_at A g 0"
    and "bad ?P g"
    by blast
  from minimal_bad_Suc
    have "\<forall>f n.
    (\<forall>i. f i \<in> vals A) \<and>
    min_at A f n \<and>
    bad ?P f \<longrightarrow>
    (\<exists>M.
      (\<forall>i. M i \<in> vals A) \<and>
      (\<forall>i\<le>n. M i = f i) \<and>
      weakeq (M (Suc n)) (f (Suc n)) \<and>
      bad ?P (repl (Suc n) f M) \<and>
      min_at A (repl (Suc n) f M) (Suc n))"
    (is "\<forall>f n. ?Q f n \<longrightarrow> (\<exists>M. ?Q' f n M)")
    by blast
  from choice2 [OF this] obtain M
    where * [rule_format]: "\<forall>f n. ?Q f n \<longrightarrow> ?Q' f n (M f n)" by force
  let ?g = "minimal_bad_seq M g"
  let ?A = "\<lambda>i. ?g i i"
  have "\<forall>n. (\<forall>i. ?g n i \<in> vals A)
    \<and> (\<forall>i\<le>n. min_at A (?g n) i)
    \<and> (\<forall>i\<le>n. ?A i = ?g n i)
    \<and> bad ?P (?g n)" (is "\<forall>n. ?Q n")
  proof
    fix n
    show "?Q n"
    proof (induction n)
      case 0
      with `\<And>i. g i \<in> vals A` and `min_at A g 0` and `bad ?P g`
        show ?case
        by auto
    next
      case (Suc n)
      from Suc and * [of "?g n" n]
        have eq: "\<forall>i\<le>n. ?A i = ?g n i"
        and vals: "\<forall>i. ?g n i \<in> vals A"
        and weak: "weakeq (?g (Suc n) (Suc n)) (?g n (Suc n))"
        and bad: "bad ?P (?g n)"
        and "bad ?P (?g (Suc n))"
        and min_at: "min_at A (?g n) n"
        and min_at_Suc: "min_at A (?g (Suc n)) (Suc n)"
        by (simp_all add: Let_def)
      moreover have vals': "\<forall>i\<ge>Suc n. ?g (Suc n) i \<in> vals A"
      proof (intro allI impI)
        fix i assume "Suc n \<le> i"
        moreover from * [of "?g n"] and vals and min_at and bad
          have "M (?g n) n i \<in> vals A" by simp
        ultimately show "?g (Suc n) i \<in> vals A" by (simp add: Let_def)
      qed
      moreover have *: "\<forall>i\<le>Suc n. ?A i = ?g (Suc n) i"
      proof (intro allI impI)
        fix i assume "i \<le> Suc n"
        thus "?A i = ?g (Suc n) i"
          by (cases "i = Suc n") (auto dest: neq_le_trans simp: Let_def eq)
      qed
      moreover have "\<forall>i. ?g (Suc n) i \<in> vals A"
      proof
        fix i
        from weak
        show "?g (Suc n) i \<in> vals A"
        proof (cases "i \<ge> Suc n")
          assume "i \<ge> Suc n" then show ?thesis using vals' by simp
        next
          assume "\<not> i \<ge> Suc n"
          then have "i \<le> n" by arith
          with eq and * and vals show ?thesis by simp
        qed
      qed
      moreover have "\<forall>i\<le>Suc n. min_at A (?g (Suc n)) i"
      proof (intro allI impI)
        fix i assume "i \<le> Suc n"
        show "min_at A (?g (Suc n)) i"
        proof (cases "i = Suc n")
          case True with min_at_Suc show ?thesis by simp
        next
          case False with `i \<le> Suc n` have le: "i \<le> Suc n" "i \<le> n" by auto
          show ?thesis
          proof (unfold min_at_def, intro allI impI, elim conjE)
            fix e
            note * = * [rule_format, symmetric] eq [rule_format, symmetric]
            assume 1: "\<forall>i::nat. e i \<in> vals A"
            assume "\<forall>i'<i. e i' = ?g (Suc n) i'"
            hence 2: "\<forall>i'<i. e i' = ?g n i'" using * and le by auto
            assume "weak (e i) (?g (Suc n) i)"
            hence 3: "weak (e i) (?g n i)" using * and le by simp
            from 1 2 3 and Suc [THEN conjunct2, THEN conjunct1] and `i \<le> n`
              show "good ?P e" unfolding min_at_def by blast
          qed
        qed
      qed
      ultimately show ?case by simp
    qed
  qed
  then have vals: "\<forall>i. ?A i \<in> vals A"
    and 1: "\<forall>n. \<forall>i\<le>n. min_at A (?g n) i"
    and 2: "\<forall>n. \<forall>i\<le>n. ?A i = ?g n i"
    and 3: "\<forall>n. bad ?P (?g n)"
    and 4: "\<forall>i. \<exists>j. weakeq (?g 0 i) (g j)"
    by auto
  have "\<forall>i. ?A i \<in> vals A" by fact
  moreover have bad: "bad ?P ?A"
  proof
    assume "good ?P ?A"
    then obtain i j :: nat where "i < j"
      and "?P (?g i i) (?g j j)" unfolding good_def by auto
    moreover with 2 [rule_format, of i j]
      have "?P (?g j i) (?g j j)" by auto
    ultimately have "good ?P (?g j)" unfolding good_def by blast
    with 3 show False by auto
  qed
  moreover have "\<forall>n S.
    (\<forall>i. S i \<in> vals A) \<and>
    (\<forall>i<n. S i = ?A i) \<and>
    weak (S n) (?A n) \<longrightarrow> good ?P S"
  proof (intro allI impI, elim conjE)
    fix S n
    assume "\<forall>i. S i \<in> vals A"
      and *: "\<forall>i<n. S i = ?A i"
      and "weak (S n) (?A n)"
    from * have "\<forall>i<n. S i = ?g n i" using 2 by auto
    moreover have "\<forall>i. S i \<in> vals A" by fact
    moreover have "weak (S n) (?A n)" by fact
    ultimately show "good ?P S"
      using 1 [rule_format, of n, OF le_refl, unfolded min_at_def] by auto
  qed
  ultimately show ?thesis unfolding min_at_def by auto
qed

end

end

