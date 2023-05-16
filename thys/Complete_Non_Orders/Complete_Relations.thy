(*
Author:  Akihisa Yamada (2018-2021)
License: LGPL (see file COPYING.LESSER)
*)
section \<open> Completeness of Relations \<close>

text \<open>Here we formalize various order-theoretic completeness conditions.\<close>

theory Complete_Relations
  imports Well_Relations Directedness
begin

subsection \<open>Completeness Conditions\<close>

text \<open>Order-theoretic completeness demands certain subsets of elements to admit suprema or infima.\<close>

definition complete ("_-complete"[999]1000) where
 "\<C>-complete A (\<sqsubseteq>) \<equiv> \<forall>X \<subseteq> A. \<C> X (\<sqsubseteq>) \<longrightarrow> (\<exists>s. extreme_bound A (\<sqsubseteq>) X s)" for less_eq (infix "\<sqsubseteq>" 50)

lemmas completeI = complete_def[unfolded atomize_eq, THEN iffD2, rule_format]
lemmas completeD = complete_def[unfolded atomize_eq, THEN iffD1, rule_format]
lemmas completeE = complete_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN exE]

lemma complete_cmono: "CC \<le> DD \<Longrightarrow> DD-complete \<le> CC-complete"
  by (force simp: complete_def)

lemma complete_subclass:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes "\<C>-complete A (\<sqsubseteq>)" and "\<forall>X \<subseteq> A. \<D> X (\<sqsubseteq>) \<longrightarrow> \<C> X (\<sqsubseteq>)"
  shows "\<D>-complete A (\<sqsubseteq>)"
  using assms by (auto simp: complete_def)


lemma complete_empty[simp]: "\<C>-complete {} r \<longleftrightarrow> \<not> \<C> {} r" by (auto simp: complete_def)

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

text\<open>Toppedness can be also seen as a completeness condition,
since it is equivalent to saying that the universe has a supremum.\<close>

lemma extremed_iff_UNIV_complete: "extremed A (\<sqsubseteq>) \<longleftrightarrow> (\<lambda>X r. X = A)-complete A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain e where "extreme A (\<sqsubseteq>) e" by (erule extremedE)
  then have "extreme_bound A (\<sqsubseteq>) A e" by auto
  then show ?r by (auto intro!: completeI)
next
  assume ?r
  from completeD[OF this] obtain s where "extreme_bound A (\<sqsubseteq>) A s" by auto
  then have "extreme A (\<sqsubseteq>) s" by auto
  then show ?l by (auto simp: extremed_def)
qed

text \<open>The dual notion of topped is called ``pointed'', equivalently ensuring a supremum
of the empty set.\<close>

lemma pointed_iff_empty_complete: "extremed A (\<sqsubseteq>) \<longleftrightarrow> (\<lambda>X r. X = {})-complete A (\<sqsubseteq>)\<^sup>-"
  by (auto simp: complete_def extremed_def)

text \<open>Downward closure is topped.\<close>
lemma dual_closure_is_extremed:
  assumes bA: "b \<in> A" and "b \<sqsubseteq> b"
  shows "extremed {a \<in> A. a \<sqsubseteq> b} (\<sqsubseteq>)"
  using assms by (auto intro!: extremedI[of _ _ b])

text \<open>Downward closure preserves completeness.\<close>
lemma dual_closure_is_complete:
  assumes A: "\<C>-complete A (\<sqsubseteq>)" and bA: "b \<in> A"
  shows "\<C>-complete {x\<in>A. x \<sqsubseteq> b} (\<sqsubseteq>)"
proof (intro completeI)
  fix X assume XAb:"X \<subseteq> {x \<in> A. x \<sqsubseteq> b}" and X: "\<C> X (\<sqsubseteq>)"
  with completeD[OF A] obtain x where x: "extreme_bound A (\<sqsubseteq>) X x" by auto
  then have xA: "x \<in> A" by auto
  from XAb have "x \<sqsubseteq> b" by (auto intro!: extreme_boundD[OF x] bA)
  with xA x show "\<exists>x. extreme_bound {x \<in> A. x \<sqsubseteq> b} (\<sqsubseteq>) X x" by (auto intro!: exI[of _ x])
qed

interpretation less_eq_dualize.

text \<open>Upward closure preserves completeness, under a condition.\<close>
lemma closure_is_complete:
  assumes A: "\<C>-complete A (\<sqsubseteq>)" and bA: "b \<in> A"
    and Cb: "\<forall>X \<subseteq> A. \<C> X (\<sqsubseteq>) \<longrightarrow> bound X (\<sqsupseteq>) b \<longrightarrow> \<C> (X \<union> {b}) (\<sqsubseteq>)"
  shows "\<C>-complete {x\<in>A. b \<sqsubseteq> x} (\<sqsubseteq>)"
proof (intro completeI)
  fix X assume XAb:"X \<subseteq> {x \<in> A. b \<sqsubseteq> x}" and X: "\<C> X (\<sqsubseteq>)"
  with Cb have XbC: "\<C> (X \<union> {b}) (\<sqsubseteq>)" by auto
  from XAb bA have XbA: "X \<union> {b} \<subseteq> A" by auto
  with completeD[OF A XbA] XbC
  obtain x where x: "extreme_bound A (\<sqsubseteq>) (X\<union>{b}) x" by auto
  then show "\<exists>x. extreme_bound {x \<in> A. b \<sqsubseteq> x} (\<sqsubseteq>) X x"
    by (auto intro!: exI[of _ x] extreme_boundI)
qed

lemma biclosure_is_complete:
  assumes A: "\<C>-complete A (\<sqsubseteq>)" and aA: "a \<in> A" and bA: "b \<in> A" and ab: "a \<sqsubseteq> b"
    and Ca: "\<forall>X \<subseteq> A. \<C> X (\<sqsubseteq>) \<longrightarrow> bound X (\<sqsupseteq>) a \<longrightarrow> \<C> (X \<union> {a}) (\<sqsubseteq>)"
  shows "\<C>-complete {x\<in>A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b} (\<sqsubseteq>)"
proof-
  note closure_is_complete[OF A aA Ca]
  from dual_closure_is_complete[OF this, of b] bA ab show ?thesis by auto
qed

end


text \<open>One of the most well-studied notion of completeness would be the semilattice condition:
every pair of elements $x$ and $y$ has a supremum $x \sqcup y$
(not necessarily unique if the underlying relation is not antisymmetric).\<close>

definition "pair_complete \<equiv> (\<lambda>X r. \<exists>x y. X = {x,y})-complete"

lemma pair_completeI:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<exists>s. extreme_bound A r {x,y} s"
  shows "pair_complete A r"
  using assms by (auto simp: pair_complete_def complete_def)

lemma pair_completeD:
  assumes "pair_complete A r"
  shows "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<exists>s. extreme_bound A r {x,y} s"
   by (intro completeD[OF assms[unfolded pair_complete_def]], auto)


context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma pair_complete_imp_directed:
  assumes comp: "pair_complete A (\<sqsubseteq>)" shows "directed A (\<sqsubseteq>)"
proof
  fix x y :: 'a
  assume "x \<in> A" "y \<in> A"
  with pair_completeD[OF comp this] show "\<exists>z \<in> A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
qed

end

lemma (in connex) pair_complete: "pair_complete A (\<sqsubseteq>)"
proof (safe intro!: pair_completeI)
  fix x y
  assume x: "x \<in> A" and y: "y \<in> A"
  then show "\<exists>s. extreme_bound A (\<sqsubseteq>) {x, y} s"
  proof (cases rule:comparable_cases)
    case le
    with x y show ?thesis by (auto intro!: exI[of _ y])
  next
    case ge
    with x y show ?thesis by (auto intro!: exI[of _ x])
  qed
qed

text \<open>The next one assumes that every nonempty finite set has a supremum.\<close>

abbreviation "finite_complete \<equiv> (\<lambda>X r. finite X \<and> X \<noteq> {})-complete"

lemma finite_complete_le_pair_complete: "finite_complete \<le> pair_complete"
  by (unfold pair_complete_def, rule complete_cmono, auto)

text \<open>The next one assumes that every nonempty bounded set has a supremum.
It is also called the Dedekind completeness.\<close>

abbreviation "conditionally_complete A \<equiv> (\<lambda>X r. \<exists>b \<in> A. bound X r b \<and> X \<noteq> {})-complete A"

lemma conditionally_complete_imp_nonempty_imp_ex_extreme_bound_iff_ex_bound:
  assumes comp: "conditionally_complete A r"
  assumes "X \<subseteq> A" and "X \<noteq> {}"
  shows "(\<exists>s. extreme_bound A r X s) \<longleftrightarrow> (\<exists>b\<in>A. bound X r b)"
  using assms by (auto 0 4 intro!:completeD[OF comp])

text \<open>The $\omega$-completeness condition demands a supremum for an $\omega$-chain.\<close>

text\<open>\emph{Directed completeness} is an important notion in domain theory~\cite{abramski94},
asserting that every nonempty directed set has a supremum.
Here, a set $X$ is \emph{directed} if any pair of two elements in $X$ has a bound in $X$.\<close>

definition "directed_complete \<equiv> (\<lambda>X r. directed X r \<and> X \<noteq> {})-complete"

lemma monotone_directed_complete:
  assumes comp: "directed_complete A r"
  assumes fI: "f ` I \<subseteq> A" and dir: "directed I ri" and I0: "I \<noteq> {}" and mono: "monotone_on I ri r f"
  shows "\<exists>s. extreme_bound A r (f ` I) s"
  apply (rule completeD[OF comp[unfolded directed_complete_def], OF fI])
  using monotone_directed_image[OF mono dir] I0 by auto

lemma (in reflexive) dual_closure_is_directed_complete:
  assumes comp: "directed-complete A (\<sqsubseteq>)" and bA: "b \<in> A"
  shows "directed-complete {X \<in> A. b \<sqsubseteq> X} (\<sqsubseteq>)"
  apply (rule closure_is_complete[OF comp bA])
proof (intro allI impI directedI CollectI)
  interpret less_eq_dualize.
  fix X x y assume Xdir: "directed X (\<sqsubseteq>)" and X: "X \<subseteq> A"
    and bX: "bound X (\<sqsupseteq>) b" and x: "x \<in> X \<union> {b}" and y: "y \<in> X \<union> {b}"
  from x y X bA have xA: "x \<in> A" and yA: "y \<in> A" by auto
  show "\<exists>z\<in>X \<union> {b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  proof (cases "x = b")
    case [simp]: True
    with y bX bA have "b \<sqsubseteq> y" by auto
    with y yA bA show ?thesis by (auto intro!: bexI[of _ y])
  next
    case False
    with x have x: "x \<in> X" by auto
    show ?thesis
    proof (cases "y = b")
      case [simp]: True
      with x bX have "b \<sqsubseteq> x" by auto
      with x xA bA show ?thesis by (auto intro!: bexI[of _ x])
    next
      case False
      with y have y: "y \<in> X" by auto
      from directedD[OF Xdir x y] show ?thesis by simp
    qed
  qed
qed


text \<open>The next one is quite complete, only the empty set may fail to have a supremum.
The terminology follows \cite{Bergman2015},
although there it is defined more generally depending on a cardinal $\alpha$
such that a nonempty set $X$ of cardinality below $\alpha$ has a supremum.\<close>

abbreviation "semicomplete \<equiv> (\<lambda>X r. X \<noteq> {})-complete"

lemma semicomplete_nonempty_imp_extremed:
  "semicomplete A r \<Longrightarrow> A \<noteq> {} \<Longrightarrow> extremed A r"
  unfolding extremed_iff_UNIV_complete
  using complete_cmono[of "\<lambda>X r. X = A" "\<lambda>X r. X \<noteq> {}"]
  by auto

lemma connex_dual_semicomplete: "semicomplete {C. connex C r} (\<supseteq>)"
proof (intro completeI)
  fix X
  assume "X \<subseteq> {C. connex C r}" and "X \<noteq> {}"
  then have "connex (\<Inter>X) r" by (auto simp: connex_def)
  then have "extreme_bound {C. connex C r} (\<supseteq>) X (\<Inter> X)" by auto
  then show "\<exists>S. extreme_bound {C. connex C r} (\<supseteq>) X S" by auto
qed

subsection \<open>Pointed Ones\<close>

text \<open>The term `pointed' refers to the dual notion of toppedness, i.e., there is a global least element.
  This serves as the supremum of the empty set.\<close>

lemma complete_sup: "(CC \<squnion> CC')-complete A r \<longleftrightarrow> CC-complete A r \<and> CC'-complete A r"
  by (auto simp: complete_def)

lemma pointed_directed_complete:
  "directed-complete A r \<longleftrightarrow> directed_complete A r \<and> extremed A r\<^sup>-"
proof-
  have [simp]: "(\<lambda>X r. directed X r \<and> X \<noteq> {} \<or> X = {}) = directed" by auto
  show ?thesis
    by (auto simp: directed_complete_def pointed_iff_empty_complete complete_sup[symmetric]
        sup_fun_def)
qed

text \<open>``Bounded complete'' refers to pointed conditional complete,
but this notion is just the dual of semicompleteness. We prove this later.\<close>

abbreviation "bounded_complete A \<equiv> (\<lambda>X r. \<exists>b\<in>A. bound X r b)-complete A"

subsection \<open>Relations between Completeness Conditions\<close>

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

text \<open>Pair-completeness implies that the universe is directed. Thus, with directed completeness
implies toppedness.\<close>

proposition directed_complete_pair_complete_imp_extremed:
  assumes dc: "directed_complete A (\<sqsubseteq>)" and pc: "pair_complete A (\<sqsubseteq>)" and A: "A \<noteq> {}"
  shows "extremed A (\<sqsubseteq>)"
proof-
  have "\<exists>s. extreme_bound A (\<sqsubseteq>) A s"
    apply (rule completeD[OF dc[unfolded directed_complete_def]])
    using pair_complete_imp_directed[OF pc] A by auto
  then obtain t where "extreme_bound A (\<sqsubseteq>) A t" by auto
  then have "\<forall>x \<in> A. x \<sqsubseteq> t" and "t \<in> A" by auto
  then show ?thesis by (auto simp: extremed_def)
qed

text \<open>Semicomplete is conditional complete and topped.\<close>

proposition semicomplete_iff_conditionally_complete_extremed:
  assumes A: "A \<noteq> {}"
  shows "semicomplete A (\<sqsubseteq>) \<longleftrightarrow> conditionally_complete A (\<sqsubseteq>) \<and> extremed A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume r: "?r"
  then have cc: "conditionally_complete A (\<sqsubseteq>)" and e: "extremed A (\<sqsubseteq>)" by auto
  show ?l
  proof (intro completeI)
    fix X
    assume X: "X \<subseteq> A" and "X \<noteq> {}"
    with extremed_imp_ex_bound[OF e X]
    show "\<exists>s. extreme_bound A (\<sqsubseteq>) X s" by (auto intro!: completeD[OF cc X])
  qed
next
  assume l: ?l
  with semicomplete_nonempty_imp_extremed[OF l] A
  show ?r by (auto intro!: completeI dest: completeD)
qed

proposition complete_iff_pointed_semicomplete:
  "\<top>-complete A (\<sqsubseteq>) \<longleftrightarrow> semicomplete A (\<sqsubseteq>) \<and> extremed A (\<sqsupseteq>)" (is "?l \<longleftrightarrow> ?r")
  by (unfold pointed_iff_empty_complete complete_sup[symmetric], auto simp: sup_fun_def top_fun_def)

text \<open>Conditional completeness only lacks top and bottom to be complete.\<close>

proposition complete_iff_conditionally_complete_extremed_pointed:
  "\<top>-complete A (\<sqsubseteq>) \<longleftrightarrow> conditionally_complete A (\<sqsubseteq>) \<and> extremed A (\<sqsubseteq>) \<and> extremed A (\<sqsupseteq>)"
  unfolding complete_iff_pointed_semicomplete
  apply (cases "A = {}")
   apply (auto intro!: completeI dest: extremed_imp_ex_bound)[1]
  unfolding semicomplete_iff_conditionally_complete_extremed
  apply (auto intro:completeI)
  done


text \<open>If the universe is directed, then every pair is bounded, and thus has a supremum.
  On the other hand, supremum gives an upper bound, witnessing directedness.\<close>

proposition conditionally_complete_imp_pair_complete_iff_directed:
  assumes comp: "conditionally_complete A (\<sqsubseteq>)"
  shows "pair_complete A (\<sqsubseteq>) \<longleftrightarrow> directed A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI)
  assume ?r
  then show ?l
    by (auto intro!: pair_completeI completeD[OF comp] elim: directedE)
next
  assume pc: ?l
  show ?r
  proof (intro directedI)
    fix x y assume "x \<in> A" and "y \<in> A"
    with pc obtain z where "extreme_bound A (\<sqsubseteq>) {x,y} z" by (auto dest: pair_completeD)
    then show "\<exists>z\<in>A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
  qed
qed

end

subsection \<open>Duality of Completeness Conditions\<close>

text \<open>Conditional completeness is symmetric.\<close>

context fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

lemma conditionally_complete_dual:
  assumes comp: "conditionally_complete A (\<sqsubseteq>)" shows "conditionally_complete A (\<sqsupseteq>)"
proof (intro completeI)
  fix X assume XA: "X \<subseteq> A"
  define B where [simp]: "B \<equiv> {b\<in>A. bound X (\<sqsupseteq>) b}"
  assume bound: "\<exists>b\<in>A. bound X (\<sqsupseteq>) b \<and> X \<noteq> {}"
  with in_mono[OF XA] have B: "B \<subseteq> A" and "\<exists>b \<in> A. bound B (\<sqsubseteq>) b" and "B \<noteq> {}" by auto
  from comp[THEN completeD, OF B] this
  obtain s where "s \<in> A" and "extreme_bound A (\<sqsubseteq>) B s" by auto
  with in_mono[OF XA] show "\<exists>s. extreme_bound A (\<sqsupseteq>) X s"
    by (intro exI[of _ s] extreme_boundI, auto)
qed

text \<open>Full completeness is symmetric.\<close>

lemma complete_dual:
  "\<top>-complete A (\<sqsubseteq>) \<Longrightarrow> \<top>-complete A (\<sqsupseteq>)"
  apply (unfold complete_iff_conditionally_complete_extremed_pointed)
  using conditionally_complete_dual by auto

text \<open>Now we show that bounded completeness is the dual of semicompleteness.\<close>

lemma bounded_complete_iff_pointed_conditionally_complete:
  assumes A: "A \<noteq> {}"
  shows "bounded_complete A (\<sqsubseteq>) \<longleftrightarrow> conditionally_complete A (\<sqsubseteq>) \<and> extremed A (\<sqsupseteq>)"
  apply (unfold pointed_iff_empty_complete)
  apply (fold complete_sup)
  apply (unfold sup_fun_def)
  apply (rule arg_cong[of _ _ "\<lambda>CC. CC-complete A (\<sqsubseteq>)"])
  using A by auto

proposition bounded_complete_iff_dual_semicomplete:
  "bounded_complete A (\<sqsubseteq>) \<longleftrightarrow> semicomplete A (\<sqsupseteq>)"
proof (cases "A = {}")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis
    apply (unfold bounded_complete_iff_pointed_conditionally_complete[OF False])
    apply (unfold semicomplete_iff_conditionally_complete_extremed)
    using Complete_Relations.conditionally_complete_dual by auto
qed

lemma bounded_complete_imp_conditionally_complete:
  assumes "bounded_complete A (\<sqsubseteq>)" shows "conditionally_complete A (\<sqsubseteq>)"
  using assms by (cases "A = {}", auto simp:bounded_complete_iff_pointed_conditionally_complete)

text \<open>Completeness in downward-closure:\<close>
lemma conditionally_complete_imp_semicomplete_in_dual_closure:
  assumes A: "conditionally_complete A (\<sqsubseteq>)" and bA: "b \<in> A"
  shows "semicomplete {a \<in> A. a \<sqsubseteq> b} (\<sqsubseteq>)"
proof (intro completeI)
  fix X assume X: "X \<subseteq> {a \<in> A. a \<sqsubseteq> b}" and X0: "X \<noteq> {}"
  then have "X \<subseteq> A" and Xb: "bound X (\<sqsubseteq>) b" by auto
  with bA completeD[OF A] X0 obtain s where Xs: "extreme_bound A (\<sqsubseteq>) X s" by auto
  with Xb bA have sb: "s \<sqsubseteq> b" by auto
  with Xs have "extreme_bound {a \<in> A. a \<sqsubseteq> b} (\<sqsubseteq>) X s"
    by (intro extreme_boundI, auto)
  then show "\<exists>s. extreme_bound {a \<in> A. a \<sqsubseteq> b} (\<sqsubseteq>) X s" by auto
qed

end

text \<open>Completeness in intervals:\<close>
lemma conditionally_complete_imp_complete_in_interval:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes comp: "conditionally_complete A (\<sqsubseteq>)" and aA: "a \<in> A" and bA: "b \<in> A"
    and aa: "a \<sqsubseteq> a" and ab: "a \<sqsubseteq> b"
  shows "\<top>-complete {x \<in> A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b} (\<sqsubseteq>)"
proof (intro completeI)
  fix X assume X: "X \<subseteq> {x \<in> A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b}"
  note conditionally_complete_imp_semicomplete_in_dual_closure[OF comp bA]
  from closure_is_complete[OF this, of a,simplified] aA ab
  have semi: "semicomplete {x \<in> A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b} (\<sqsubseteq>)" by (simp add: conj_commute cong: Collect_cong)
  show "Ex (extreme_bound {x \<in> A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b} (\<sqsubseteq>) X)"
  proof (cases "X = {}")
    case True
    with aA aa ab have "extreme_bound {x \<in> A. a \<sqsubseteq> x \<and> x \<sqsubseteq> b} (\<sqsubseteq>) X a" by (auto simp: bound_empty)
    then show ?thesis by auto
  next
    case False
    with completeD[OF semi X] show ?thesis by simp
  qed
qed

lemmas connex_bounded_complete = connex_dual_semicomplete[folded bounded_complete_iff_dual_semicomplete]

subsection \<open>Completeness Results Requiring Order-Like Properties\<close>

text \<open>Above results hold without any assumption on the relation.
This part demands some order-like properties.\<close>

text \<open>It is well known that in a semilattice, i.e., a pair-complete partial order,
every finite nonempty subset of elements has a supremum.
We prove the result assuming transitivity, but only that.\<close>

lemma (in transitive) pair_complete_iff_finite_complete:
  "pair_complete A (\<sqsubseteq>) \<longleftrightarrow> finite_complete A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI completeI, elim CollectE conjE)
  fix X
  assume pc: ?l
  show "finite X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Ex (extreme_bound A (\<sqsubseteq>) X)"
  proof (induct X rule: finite_induct)
  case empty
    then show ?case by auto
  next
    case (insert x X)
    then have x: "x \<in> A" and X: "X \<subseteq> A" by auto
    show ?case
    proof (cases "X = {}")
      case True
      obtain x' where "extreme_bound A (\<sqsubseteq>) {x,x} x'" using pc[THEN pair_completeD, OF x x] by auto
      with True show ?thesis by (auto intro!: exI[of _ x'])
    next
      case False
      with insert obtain b where b: "extreme_bound A (\<sqsubseteq>) X b" by auto
      with pc[THEN pair_completeD] x obtain c where c: "extreme_bound A (\<sqsubseteq>) {x,b} c" by auto
      from c have cA: "c \<in> A" and xc: "x \<sqsubseteq> c" and bc: "b \<sqsubseteq> c" by auto
      from b have bA: "b \<in> A" and bX: "bound X (\<sqsubseteq>) b" by auto
      show ?thesis
      proof (intro exI extreme_boundI)
        fix xb assume xb: "xb \<in> insert x X"
        from bound_trans[OF bX bc X bA cA] have "bound X (\<sqsubseteq>) c".
        with xb xc show "xb \<sqsubseteq> c" by auto
      next
        fix d assume "bound (insert x X) (\<sqsubseteq>) d" and dA: "d \<in> A"
        with b have "bound {x,b} (\<sqsubseteq>) d" by auto
        with c show "c \<sqsubseteq> d" using dA by auto
      qed (fact cA)
    qed
  qed
qed (insert finite_complete_le_pair_complete, auto)


text \<open>Gierz et al.~\cite{gierz03} showed that a directed complete partial order is semicomplete
if and only if it is also a semilattice.
We generalize the claim so that the underlying relation is only transitive.\<close>

proposition(in transitive) semicomplete_iff_directed_complete_pair_complete:
  "semicomplete A (\<sqsubseteq>) \<longleftrightarrow> directed_complete A (\<sqsubseteq>) \<and> pair_complete A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume l: ?l
  then show ?r by (auto simp: directed_complete_def intro!: completeI pair_completeI completeD[OF l])
next
  assume ?r
  then have dc: "directed_complete A (\<sqsubseteq>)" and pc: "pair_complete A (\<sqsubseteq>)" by auto
  with pair_complete_iff_finite_complete have fc: "finite_complete A (\<sqsubseteq>)" by auto
  show ?l
  proof (intro completeI)
    fix X assume XA: "X \<subseteq> A"
    have 1: "directed {x. \<exists>Y \<subseteq> X. finite Y \<and> Y \<noteq> {} \<and> extreme_bound A (\<sqsubseteq>) Y x} (\<sqsubseteq>)" (is "directed ?B _")
    proof (intro directedI)
      fix a b assume a: "a \<in> ?B" and b: "b \<in> ?B"
      from a obtain Y where Y: "extreme_bound A (\<sqsubseteq>) Y a" "finite Y" "Y \<noteq> {}" "Y \<subseteq> X" by auto
      from b obtain B where B: "extreme_bound A (\<sqsubseteq>) B b" "finite B" "B \<noteq> {}" "B \<subseteq> X" by auto
      from XA Y B have AB: "Y \<subseteq> A" "B \<subseteq> A" "finite (Y \<union> B)" "Y \<union> B \<noteq> {}" "Y \<union> B \<subseteq> X" by auto
      with fc[THEN completeD] have "Ex (extreme_bound A (\<sqsubseteq>) (Y \<union> B))" by auto
      then obtain c where c: "extreme_bound A (\<sqsubseteq>) (Y \<union> B) c" by auto
      show "\<exists>c \<in> ?B. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
      proof (intro bexI conjI)
        from Y B c show "a \<sqsubseteq> c" and "b \<sqsubseteq> c" by (auto simp: extreme_bound_iff)
        from AB c show "c \<in> ?B" by (auto intro!: exI[of _ "Y \<union> B"])
      qed
    qed
    have B: "?B \<subseteq> A" by auto
    assume "X \<noteq> {}"
    then obtain x where xX: "x \<in> X" by auto
    with fc[THEN completeD, of "{x}"] XA
    obtain x' where "extreme_bound A (\<sqsubseteq>) {x} x'" by auto
    with xX have x'B: "x' \<in> ?B" by (auto intro!: exI[of _ "{x}"] extreme_boundI)
    then have 2: "?B \<noteq> {}" by auto
    from dc[unfolded directed_complete_def, THEN completeD, of ?B] 1 2
    obtain b where b: "extreme_bound A (\<sqsubseteq>) ?B b" by auto
    then have bA: "b \<in> A" by auto
    show "Ex (extreme_bound A (\<sqsubseteq>) X)"
    proof (intro exI extreme_boundI UNIV_I)
      fix x
      assume xX: "x \<in> X"
      with XA fc[THEN completeD, of "{x}"]
      obtain c where c: "extreme_bound A (\<sqsubseteq>) {x} c" by auto
      then have cA: "c \<in> A" and xc: "x \<sqsubseteq> c" by auto
      from c xX have cB: "c \<in> ?B" by (auto intro!: exI[of _ "{x}"] extreme_boundI)
      with b have bA: "b \<in> A" and cb: "c \<sqsubseteq> b" by auto
      from xX XA cA bA trans[OF xc cb]
      show "x \<sqsubseteq> b" by auto text\<open> Here transitivity is needed. \<close>
    next
      fix x
      assume xA: "x \<in> A" and Xx: "bound X (\<sqsubseteq>) x"
      have "bound ?B (\<sqsubseteq>) x"
      proof (intro boundI UNIV_I, clarify)
        fix c Y
        assume "finite Y" and YX: "Y \<subseteq> X" and "Y \<noteq> {}" and c: "extreme_bound A (\<sqsubseteq>) Y c"
        from YX Xx have "bound Y (\<sqsubseteq>) x" by auto
        with c xA show "c \<sqsubseteq> x" by auto
      qed
      with b xA show "b \<sqsubseteq> x" by auto
    qed (fact bA)
  qed
qed

text\<open>The last argument in the above proof requires transitivity,
but if we had reflexivity then $x$ itself is a supremum of $\set{x}$
(see @{thm reflexive.extreme_bound_singleton}) and so $x \SLE s$ would be immediate.
Thus we can replace transitivity by reflexivity,
but then pair-completeness does not imply finite completeness.
We obtain the following result.\<close>

proposition (in reflexive) semicomplete_iff_directed_complete_finite_complete:
  "semicomplete A (\<sqsubseteq>) \<longleftrightarrow> directed_complete A (\<sqsubseteq>) \<and> finite_complete A (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume l: ?l
  then show ?r by (auto simp: directed_complete_def intro!: completeI pair_completeI completeD[OF l])
next
  assume ?r
  then have dc: "directed_complete A (\<sqsubseteq>)" and fc: "finite_complete A (\<sqsubseteq>)" by auto
  show ?l
  proof (intro completeI)
    fix X assume XA: "X \<subseteq> A"
    have 1: "directed {x. \<exists>Y \<subseteq> X. finite Y \<and> Y \<noteq> {} \<and> extreme_bound A (\<sqsubseteq>) Y x} (\<sqsubseteq>)" (is "directed ?B _")
    proof (intro directedI)
      fix a b assume a: "a \<in> ?B" and b: "b \<in> ?B"
      from a obtain Y where Y: "extreme_bound A (\<sqsubseteq>) Y a" "finite Y" "Y \<noteq> {}" "Y \<subseteq> X" by auto
      from b obtain B where B: "extreme_bound A (\<sqsubseteq>) B b" "finite B" "B \<noteq> {}" "B \<subseteq> X" by auto
      from XA Y B have AB: "Y \<subseteq> A" "B \<subseteq> A" "finite (Y \<union> B)" "Y \<union> B \<noteq> {}" "Y \<union> B \<subseteq> X" by auto
      with fc[THEN completeD] have "Ex (extreme_bound A (\<sqsubseteq>) (Y \<union> B))" by auto
      then obtain c where c: "extreme_bound A (\<sqsubseteq>) (Y \<union> B) c" by auto
      show "\<exists>c \<in> ?B. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
      proof (intro bexI conjI)
        from Y B c show "a \<sqsubseteq> c" and "b \<sqsubseteq> c" by (auto simp: extreme_bound_iff)
        from AB c show "c \<in> ?B" by (auto intro!: exI[of _ "Y \<union> B"])
      qed
    qed
    have B: "?B \<subseteq> A" by auto
    assume "X \<noteq> {}"
    then obtain x where xX: "x \<in> X" by auto
    with XA have "extreme_bound A (\<sqsubseteq>) {x} x"
      by (intro extreme_bound_singleton, auto)
    with xX have xB: "x \<in> ?B" by (auto intro!: exI[of _ "{x}"])
    then have 2: "?B \<noteq> {}" by auto
    from dc[unfolded directed_complete_def, THEN completeD, of ?B] B 1 2
    obtain b where b: "extreme_bound A (\<sqsubseteq>) ?B b" by auto
    then have bA: "b \<in> A" by auto
    show "Ex (extreme_bound A (\<sqsubseteq>) X)"
    proof (intro exI extreme_boundI UNIV_I)
      fix x
      assume xX: "x \<in> X"
      with XA have x: "extreme_bound A (\<sqsubseteq>) {x} x" by (intro extreme_bound_singleton, auto)
      from x xX have cB: "x \<in> ?B" by (auto intro!: exI[of _ "{x}"])
      with b show "x \<sqsubseteq> b" by auto
    next
      fix x
      assume Xx: "bound X (\<sqsubseteq>) x" and xA: "x \<in> A"
      have "bound ?B (\<sqsubseteq>) x"
      proof (intro boundI UNIV_I, clarify)
        fix c Y
        assume "finite Y" and YX: "Y \<subseteq> X" and "Y \<noteq> {}" and c: "extreme_bound A (\<sqsubseteq>) Y c"
        from YX Xx have "bound Y (\<sqsubseteq>) x" by auto
        with YX XA xA c show "c \<sqsubseteq> x" by auto
      qed
      with xA b show "b \<sqsubseteq> x" by auto
    qed (fact bA)
  qed
qed


subsection \<open>Relating to Classes\<close>

(* HOL.Conditionally_Complete_Lattices imports choice.

text \<open>Isabelle's class @{class conditionally_complete_lattice} satisfies @{const conditionally_complete}.
The other direction does not hold, since for the former,
@{term "Sup {}"} and @{term "Inf {}"} are arbitrary even if there are top or bottom elements.\<close>

lemma (in conditionally_complete_lattice) "conditionally_complete UNIV (\<le>)"
proof (intro completeI, elim CollectE)
  fix X :: "'a set"
  assume "\<exists>b\<in>UNIV. bound X (\<le>) b \<and> X \<noteq> {}"
  then have bdd:"bdd_above X" and X0: "X \<noteq> {}" by (auto 0 3)
  from cSup_upper[OF _ bdd] cSup_least[OF X0]
  have "supremum X (Sup X)" by (intro extremeI boundI, auto)
  then show "\<exists>s. least {b \<in> UNIV. bound X (\<le>) b} s" by auto
qed
*)
text \<open>Isabelle's class @{class complete_lattice} is @{term "\<top>-complete"}.\<close>

lemma (in complete_lattice) "\<top>-complete UNIV (\<le>)"
  by (auto intro!: completeI extreme_boundI Sup_upper Sup_least Inf_lower Inf_greatest)

subsection \<open>Set-wise Completeness\<close>

lemma Pow_extreme_bound: "X \<subseteq> Pow A \<Longrightarrow> extreme_bound (Pow A) (\<subseteq>) X (\<Union>X)"
  by (intro extreme_boundI, auto 2 3)

lemma Pow_complete: "\<C>-complete (Pow A) (\<subseteq>)"
  by (auto intro!: completeI dest: Pow_extreme_bound)

lemma directed_directed_Un:
assumes ch: "XX \<subseteq> {X. directed X r}" and dir: "directed XX (\<subseteq>)"
    shows "directed (\<Union>XX) r"
proof (intro directedI, elim UnionE)
  fix x y X Y assume xX: "x \<in> X" and X: "X \<in> XX" and yY: "y \<in> Y" and Y: "Y \<in> XX"
  from directedD[OF dir X Y]
  obtain Z where "X \<subseteq> Z" "Y \<subseteq> Z" and Z: "Z \<in> XX" by auto
  with ch xX yY have "directed Z r" "x \<in> Z" "y \<in> Z" by auto
  then obtain z where "z \<in> Z" "r x z \<and> r y z" by (auto elim:directedE)
  with Z show "\<exists>z\<in>\<Union> XX. r x z \<and> r y z" by auto
qed

lemmas directed_connex_Un = directed_directed_Un[OF _ connex.directed]

lemma directed_sets_directed_complete:
  assumes cl: "\<forall>DC. DC \<subseteq> AA \<longrightarrow> (\<forall>X\<in>DC. directed X r) \<longrightarrow> (\<Union>DC) \<in> AA"
  shows "directed-complete {X \<in> AA. directed X r} (\<subseteq>)"
proof (intro completeI)
  fix XX
  assume ch: "XX \<subseteq> {X \<in> AA. directed X r}" and dir: "directed XX (\<subseteq>)"
  with cl have "(\<Union>XX) \<in> AA" by auto
  moreover have "directed (\<Union>XX) r"
    apply (rule directed_directed_Un) using ch by (auto simp: dir)
  ultimately show "Ex (extreme_bound {X \<in> AA. directed X r} (\<subseteq>) XX)"
    by (auto intro!: exI[of _ "\<Union>XX"])
qed

lemma connex_directed_Un:
  assumes ch: "CC \<subseteq> {C. connex C r}" and dir: "directed CC (\<subseteq>)"
  shows "connex (\<Union>CC) r"
proof (intro connexI, elim UnionE)
  fix x y X Y assume xX: "x \<in> X" and X: "X \<in> CC" and yY: "y \<in> Y" and Y: "Y \<in> CC"
  from directedD[OF dir X Y]
  obtain Z where "X \<subseteq> Z" "Y \<subseteq> Z" "Z \<in> CC" by auto
  with xX yY ch have "x \<in> Z" "y \<in> Z" "connex Z r" by auto
  then show "r x y \<or> r y x" by (auto elim:connexE)
qed

lemma connex_is_directed_complete: "directed-complete {C. C \<subseteq> A \<and> connex C r} (\<subseteq>)"
proof (intro completeI)
  fix CC assume CC: "CC \<subseteq> {C. C \<subseteq> A \<and> connex C r}" and "directed CC (\<subseteq>)"
  with connex_directed_Un have Scon: "connex (\<Union>CC) r" by auto
  from CC have SA: "\<Union>CC \<subseteq> A" by auto
  from Scon SA show "\<exists>S. extreme_bound {C. C \<subseteq> A \<and> connex C r} (\<subseteq>) CC S"
    by (auto intro!: exI[of _ "\<Union>CC"] extreme_boundI)
qed

lemma (in well_ordered_set) well_ordered_set_insert:
  assumes aA: "total_ordered_set (insert a A) (\<sqsubseteq>)"
  shows "well_ordered_set (insert a A) (\<sqsubseteq>)"
proof-
  interpret less_eq_asymmetrize.
  interpret aA: total_ordered_set "insert a A" "(\<sqsubseteq>)" using aA.
  show ?thesis
  proof (intro well_ordered_set.intro aA.antisymmetric_axioms well_related_setI)
    fix X assume XaA: "X \<subseteq> insert a A" and X0: "X \<noteq> {}"
    show "\<exists>e. extreme X (\<sqsupseteq>) e"
    proof (cases "a \<in> X")
      case False
      with XaA have "X \<subseteq> A" by auto
      from nonempty_imp_ex_extreme[OF this X0] show ?thesis.
    next
      case aX: True
      show ?thesis
      proof (cases "X - {a} = {}")
        case True
        with aX XaA have Xa: "X = {a}" by auto
        from aA.refl[of a]
        have "a \<sqsubseteq> a" by auto
        then show ?thesis by (auto simp: Xa)
      next
        case False
        from nonempty_imp_ex_extreme[OF _ False] XaA
        obtain e where Xae: "extreme (X-{a}) (\<sqsupseteq>) e" by auto
        with Xae XaA have eaA: "e \<in> insert a A" by auto
        then have "e \<sqsubseteq> a \<or> a \<sqsubseteq> e" by (intro aA.comparable, auto)
        then show ?thesis
        proof (elim disjE)
          assume ea: "e \<sqsubseteq> a"
          with Xae show ?thesis by (auto intro!:exI[of _ e])
        next
          assume ae: "a \<sqsubseteq> e"
          show ?thesis
          proof (intro exI[of _ a] extremeI aX)
            fix x assume xX: "x \<in> X"
            show "a \<sqsubseteq> x"
            proof (cases "a = x")
              case True with aA.refl[of a] show ?thesis by auto
            next
              case False
              with xX have "x \<in> X - {a}" by auto
              with Xae have "e \<sqsubseteq> x" by auto
              from aA.trans[OF ae this _ eaA] xX XaA
              show ?thesis by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>The following should be true in general, but here we use antisymmetry to avoid
  the axiom of choice.\<close>

lemma (in antisymmetric) pointwise_connex_complete:
  assumes comp: "connex-complete A (\<sqsubseteq>)"
  shows "connex-complete {f. f ` X \<subseteq> A} (pointwise X (\<sqsubseteq>))"
proof (safe intro!: completeI exI)
  fix F
  assume FXA: "F \<subseteq> {f. f ` X \<subseteq> A}" and F: "connex F (pointwise X (\<sqsubseteq>))"
  show "extreme_bound {f. f ` X \<subseteq> A} (pointwise X (\<sqsubseteq>)) F (\<lambda>x. The (extreme_bound A (\<sqsubseteq>) {f x |. f \<in> F}))"
  proof (unfold pointwise_extreme_bound[OF FXA], safe)
    fix x assume xX: "x \<in> X"
    from FXA xX have FxA: "{f x |. f \<in> F} \<subseteq> A" by auto
    have "Ex (extreme_bound A (\<sqsubseteq>) {f x |. f \<in> F})"
    proof (intro completeD[OF comp] FxA CollectI connexI, elim imageE, fold atomize_eq)
      fix f g assume fF: "f \<in> F" and gF: "g \<in> F"
      from connex.comparable[OF F this] xX show "f x \<sqsubseteq> g x \<or> g x \<sqsubseteq> f x" by auto
    qed
    also note ex_extreme_bound_iff_the
    finally
    show "extreme_bound A (\<sqsubseteq>) {f x |. f \<in> F} (The (extreme_bound A (\<sqsubseteq>) {f x |. f \<in> F}))".
  qed
qed

text \<open>Our supremum/infimum coincides with those of Isabelle's @{class complete_lattice}.\<close>

lemma complete_UNIV: "\<top>-complete (UNIV::'a::complete_lattice set) (\<le>)"
proof-
  have "Ex (supremum X)" for X :: "'a set"
    by (auto intro!: exI[of _ "\<Squnion>X"] supremumI simp:Sup_upper Sup_least)
  then show ?thesis by (auto intro!: completeI )
qed

context
  fixes X :: "'a :: complete_lattice set"
begin

lemma supremum_Sup: "supremum X (\<Squnion>X)"
proof-
  define it where "it \<equiv> The (supremum X)"
  note completeD[OF complete_UNIV,simplified, of X]
  from this[unfolded order.dual.ex_extreme_iff_the]
  have 1: "supremum X it" by (simp add: it_def)
  then have "\<Squnion>X = it" by (intro Sup_eqI, auto)
  with 1 show ?thesis by auto
qed

lemmas Sup_eq_The_supremum = order.dual.eq_The_extreme[OF supremum_Sup]

lemma supremum_eq_Sup: "supremum X x \<longleftrightarrow> \<Squnion>X = x"
  using order.dual.eq_The_extreme supremum_Sup by auto

lemma infimum_Inf:
  shows "infimum X (\<Sqinter>X)"
proof-
  define it where "it \<equiv> The (infimum X)"
  note completeD[OF complete_dual[OF complete_UNIV],simplified, of X]
  from this[unfolded order.ex_extreme_iff_the]
  have 1: "infimum X it" by (simp add: it_def)
  then have "\<Sqinter>X = it" by (intro Inf_eqI, auto)
  with 1 show ?thesis by auto
qed

lemmas Inf_eq_The_infimum = order.eq_The_extreme[OF infimum_Inf]

lemma infimum_eq_Inf: "infimum X x \<longleftrightarrow> \<Sqinter>X = x"
  using order.eq_The_extreme infimum_Inf by auto

end

end