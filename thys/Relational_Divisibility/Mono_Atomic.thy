section \<open>Mono-Atomic Elements\<close>

theory Mono_Atomic

imports Stone_Relation_Algebras.Relation_Algebras

begin

text \<open>
This theory defines mono-atomic elements in a bounded semilattice and shows that they correspond to join-irreducible elements under the divisibility axioms A1--A17 of \cite{Cegielski1989}.
In the model of natural numbers both types of elements correspond to prime powers.
\<close>

subsection \<open>Mono-atomic\<close>

context order_bot
begin

text \<open>
Divisibility axioms A1 (reflexivity), A2 (antisymmetry), A3 (transitivity) and A6 (least element) are the axioms of class \<open>order_bot\<close>, so not mentioned explicitly.
\<close>

text \<open>
An \<open>atom\<close> in a partial order is an element that is strictly above only the least element \<open>bot\<close>.
\<close>

definition "atom a                       \<equiv> a \<noteq> bot \<and> (\<forall>x . x \<le> a \<longrightarrow> x = bot \<or> x = a)"
abbreviation "atom_below a x             \<equiv> atom a \<and> a \<le> x"

text \<open>
A mono-atomic element has exactly one atom below it.
\<close>

definition "mono_atomic x                \<equiv> (\<exists>!a . atom_below a x)"
definition "mono_atomic_with x a         \<equiv> atom_below a x \<and> (\<forall>b . atom_below b x \<longrightarrow> b = a)"
abbreviation "mono_atomic_below x y      \<equiv> mono_atomic x \<and> x \<le> y"
abbreviation "mono_atomic_above x y      \<equiv> mono_atomic x \<and> y \<le> x"
definition "mono_atomic_above_or_bot x y \<equiv> x = bot \<or> mono_atomic_above x y"

text \<open>
Divisibility axiom A11 (atomicity) states that every element except \<open>bot\<close> is above some atom.
\<close>

abbreviation A11_atomic            :: "'a \<Rightarrow> bool" where "A11_atomic _            \<equiv> (\<forall>x . x \<noteq> bot \<longrightarrow> (\<exists>a . atom_below a x))"

lemma mono_atomic_above:
  "mono_atomic x \<longleftrightarrow> (\<exists>a . mono_atomic_with x a)"
  by (metis mono_atomic_with_def mono_atomic_def)

text \<open>
Among others, the following divisibility axioms are considered in \cite{Cegielski1989}.
In the model of natural numbers,
\begin{itemize}
\item A7 (pre-f-decomposability) expresses that every number $x$ is the least upper bound of the prime powers below $x$;
\item A8 (fibered) expresses that the prime powers can be partitioned into chains;
\item A9 (f-decomposability) expresses that for every number $x$ above an atom $a$ there is a maximal prime power of $a$ below $x$;
\item A14 (truncability) express that the prime powers contained in a number $y$ can be restricted to those whose atoms are not below a number $x$.
\end{itemize}
Their definitions are based on join-irreducible elements and given in class \<open>bounded_semilattice_sup_bot\<close> below.
Here we introduce corresponding axioms B7, B8, B9 and B14 based on mono-atomic elements.
\<close>

abbreviation B7_pre_f_decomposable :: "'a \<Rightarrow> bool" where "B7_pre_f_decomposable _ \<equiv> (\<forall>x y . (\<forall>z . mono_atomic_below z x \<longrightarrow> z \<le> y) \<longrightarrow> x \<le> y)"
abbreviation B8_fibered            :: "'a \<Rightarrow> bool" where "B8_fibered _            \<equiv> (\<forall>x y z . mono_atomic x \<and> mono_atomic y \<and> mono_atomic z \<and> ((x \<le> z \<and> y \<le> z) \<or> (z \<le> x \<and> z \<le> y)) \<longrightarrow> x \<le> y \<or> y \<le> x)"
abbreviation B9_f_decomposable     :: "'a \<Rightarrow> bool" where "B9_f_decomposable _     \<equiv> (\<forall>x a . atom a \<longrightarrow> (\<exists>z . mono_atomic_above_or_bot z a \<and> z \<le> x \<and> (\<forall>w . mono_atomic_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> z)))"

text \<open>
Function \<open>mval\<close> returns the value whose existence is asserted by axiom B9.
\<close>

definition "mval a x \<equiv> SOME z . mono_atomic_above_or_bot z a \<and> z \<le> x \<and> (\<forall>w . mono_atomic_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> z)"

lemma mval_char:
  assumes "B9_f_decomposable _"
      and "atom a"
    shows "mono_atomic_above_or_bot (mval a x) a \<and> mval a x \<le> x \<and> (\<forall>w . mono_atomic_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> mval a x)"
proof -
  obtain z where "mono_atomic_above_or_bot z a \<and> z \<le> x \<and> (\<forall>w . mono_atomic_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> z)"
    using assms by blast
  thus ?thesis
    using mval_def someI by simp
qed

lemma mval_unique:
  assumes "B9_f_decomposable _"
      and "atom a"
      and "mono_atomic_above_or_bot z a \<and> z \<le> x \<and> (\<forall>w . mono_atomic_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> z)"
    shows "z = mval a x"
  by (simp add: assms dual_order.antisym mval_char)

lemma atom_below_mval:
  assumes "B9_f_decomposable _"
      and "atom a"
      and "a \<le> x"
    shows "a \<le> mval a x"
proof -
  have "mono_atomic_above_or_bot a a"
    using assms(2) atom_def mono_atomic_above_or_bot_def mono_atomic_def by auto
  thus ?thesis
    by (simp add: assms mval_char)
qed

abbreviation B14_truncability      :: "'a \<Rightarrow> bool" where "B14_truncability _      \<equiv> (\<forall>x y . \<exists> z . \<forall>a . atom a \<longrightarrow> (if a \<le> x then mval a z = bot else mval a z = mval a y))"

text \<open>
Function \<open>mtrunc\<close> returns the value whose existence is asserted by axiom B14.
\<close>

definition "mtrunc x y \<equiv> SOME z . \<forall>a . atom a \<longrightarrow> (if a \<le> x then mval a z = bot else mval a z = mval a y)"

lemma mtrunc_char:
  assumes "B14_truncability _"
    shows "\<forall>a . atom a \<longrightarrow> (if a \<le> x then mval a (mtrunc x y) = bot else mval a (mtrunc x y) = mval a y)"
proof -
  obtain z where "\<forall>a . atom a \<longrightarrow> (if a \<le> x then mval a z = bot else mval a z = mval a y)"
    using assms by blast
  thus ?thesis
    by (smt mtrunc_def someI)
qed

lemma mtrunc_char_1:
  assumes "B14_truncability _"
      and "atom a"
      and "a \<le> x"
    shows "mval a (mtrunc x y) = bot"
  by (simp add: assms mtrunc_char)

lemma mtrunc_char_2:
  assumes "B14_truncability _"
      and "atom a"
      and "\<not> a \<le> x"
    shows "mval a (mtrunc x y) = mval a y"
  by (simp add: assms mtrunc_char)

lemma mtrunc_unique:
  assumes "B14_truncability _"
      and "\<forall>a . atom a \<longrightarrow> (if a \<le> x then mval a z = bot else mval a z = mval a y)"
      and "atom a"
    shows "mval a z = mval a (mtrunc x y)"
  by (smt (z3) assms mtrunc_char)

lemma lesseq_iff_mval_below:
  assumes "B7_pre_f_decomposable _"
      and "B9_f_decomposable _"
      and "atom a"
    shows "x \<le> y \<longleftrightarrow> (\<forall>a . atom a \<longrightarrow> mval a x \<le> y)"
proof (rule iffI)
  assume 1: "x \<le> y"
  show "\<forall>a . atom a \<longrightarrow> mval a x \<le> y"
  proof (rule allI, rule impI)
    fix a
    assume "atom a"
    thus "mval a x \<le> y"
      using 1 assms(2) dual_order.trans mval_char by blast
  qed
next
  assume 2: "\<forall>a . atom a \<longrightarrow> mval a x \<le> y"
  have "\<forall>z . mono_atomic_below z x \<longrightarrow> z \<le> y"
  proof (rule allI, rule impI)
    fix z
    assume 3: "mono_atomic_below z x"
    from this obtain a where 4: "atom_below a z"
      using mono_atomic_def by blast
    hence "z \<le> mval a x"
      using 3 assms(2) mono_atomic_above_or_bot_def mval_char by auto
    thus "z \<le> y"
      using 2 4 by auto
  qed
  thus "x \<le> y"
    using assms(1) by blast
qed

end

subsection \<open>Join-irreducible\<close>

context bounded_semilattice_sup_bot
begin

text \<open>
Divisibility axioms A1 (reflexivity), A2 (antisymmetry), A3 (transitivity), A5 (least upper bound) and A6 (least element) are the axioms of class \<open>bounded_semilattice_sup_bot\<close>, so not mentioned explicitly.
\<close>

text \<open>
A join-irreducible element cannot be expressed as the join of two incomparable elements.
\<close>

definition "join_irreducible x                \<equiv> x \<noteq> bot \<and> (\<forall>y z . x = y \<squnion> z \<longrightarrow> x = y \<or> x = z)"
abbreviation "join_irreducible_below x y      \<equiv> join_irreducible x \<and> x \<le> y"
abbreviation "join_irreducible_above x y      \<equiv> join_irreducible x \<and> y \<le> x"
definition "join_irreducible_above_or_bot x y \<equiv> x = bot \<or> join_irreducible_above x y"

text \<open>
Divisibility axioms A7, A8 and A9 based on join-irreducible elements are introduced here; axiom A14 is not needed for this development.
\<close>

abbreviation A7_pre_f_decomposable :: "'a \<Rightarrow> bool" where "A7_pre_f_decomposable _ \<equiv> (\<forall>x y . (\<forall>z . join_irreducible_below z x \<longrightarrow> z \<le> y) \<longrightarrow> x \<le> y)"
abbreviation A8_fibered            :: "'a \<Rightarrow> bool" where "A8_fibered _            \<equiv> (\<forall>x y z . join_irreducible x \<and> join_irreducible y \<and> join_irreducible z \<and> ((x \<le> z \<and> y \<le> z) \<or> (z \<le> x \<and> z \<le> y)) \<longrightarrow> x \<le> y \<or> y \<le> x)"
abbreviation A9_f_decomposable     :: "'a \<Rightarrow> bool" where "A9_f_decomposable _     \<equiv> (\<forall>x a . atom a \<longrightarrow> (\<exists>z . join_irreducible_above_or_bot z a \<and> z \<le> x \<and> (\<forall>w . join_irreducible_above_or_bot w a \<and> w \<le> x \<longrightarrow> w \<le> z)))"

lemma atom_join_irreducible:
  assumes "atom a"
    shows "join_irreducible a"
  by (metis assms join_irreducible_def atom_def sup.cobounded1 sup_bot_left)

lemma mono_atomic_with_downclosed:
  assumes "A11_atomic _"
      and "mono_atomic_with x a"
      and "y \<noteq> bot"
      and "y \<le> x"
    shows "mono_atomic_with y a"
  using assms mono_atomic_with_def[of y a] mono_atomic_with_def[of x a] order_lesseq_imp[of y] by blast

subsection \<open>Equivalence\<close>

text \<open>
The following result shows that under divisibility axioms A1--A3, A5--A9 and A11, join-irreducible elements coincide with mono-atomic elements.
\<close>

lemma join_irreducible_iff_mono_atomic:
  assumes "A7_pre_f_decomposable _"
      and "A8_fibered _"
      and "A9_f_decomposable _"
      and "A11_atomic _"
    shows "join_irreducible x \<longleftrightarrow> mono_atomic x"
proof (rule iffI)
  assume 1: "join_irreducible x"
  from this obtain a where 2: "atom_below a x"
    using assms(4) join_irreducible_def by blast
  have "\<forall>b . atom_below b x \<longrightarrow> b = a"
  proof (rule allI, rule impI)
    fix b
    assume 3: "atom_below b x"
    hence "join_irreducible a \<and> join_irreducible b"
      using 2 atom_join_irreducible by auto
    hence "a \<le> b \<or> b \<le> a"
      using 1 2 3 assms(2) by blast
    thus "b = a"
      using 2 3 atom_def by auto
  qed
  thus "mono_atomic x"
    using 2 mono_atomic_def by auto
next
  assume "mono_atomic x"
  from this obtain a where 4: "mono_atomic_with x a"
    using mono_atomic_above by blast
  hence 5: "x \<noteq> bot"
    using atom_def le_bot mono_atomic_with_def by blast
  have "\<forall>y z . x = y \<squnion> z \<longrightarrow> x = y \<or> x = z"
  proof (intro allI, rule impI)
    fix y z
    assume 6: "x = y \<squnion> z"
    show "x = y \<or> x = z"
    proof (cases "y = bot \<or> z = bot")
      case True
      thus "x = y \<or> x = z"
        using 6 by auto
    next
      case False
      hence 7: "mono_atomic_with y a \<and> mono_atomic_with z a"
        using 4 6 assms(4) sup.cobounded1 sup.cobounded2 mono_atomic_with_downclosed by blast
      from this obtain u where 8: "join_irreducible_above_or_bot u a \<and> u \<le> y \<and> (\<forall>w . join_irreducible_above_or_bot w a \<and> w \<le> y \<longrightarrow> w \<le> u)"
        using assms(3) mono_atomic_with_def by blast
      from 7 obtain v where 9: "join_irreducible_above_or_bot v a \<and> v \<le> z \<and> (\<forall>w . join_irreducible_above_or_bot w a \<and> w \<le> z \<longrightarrow> w \<le> v)"
        using assms(3) mono_atomic_with_def by blast
      have "join_irreducible a"
        using 4 atom_join_irreducible mono_atomic_with_def by blast
      hence 10: "u \<le> v \<or> v \<le> u"
        using 8 9 assms(2) join_irreducible_above_or_bot_def by auto
      have 11: "u \<le> v \<Longrightarrow> y \<le> z"
      proof -
        assume 12: "u \<le> v"
        have "\<forall>w . join_irreducible_below w y \<longrightarrow> w \<le> z"
        proof (rule allI, rule impI)
          fix w
          assume 13: "join_irreducible_below w y"
          hence "mono_atomic_with w a"
            using 7 by (metis assms(4) join_irreducible_def mono_atomic_with_downclosed)
          hence "w \<le> u"
            using 8 13 by (simp add: join_irreducible_above_or_bot_def mono_atomic_with_def)
          thus "w \<le> z"
            using 9 12 by force
        qed
        thus "y \<le> z"
          using assms(1) by blast
      qed
      have "v \<le> u \<Longrightarrow> z \<le> y"
      proof -
        assume 14: "v \<le> u"
        have "\<forall>w . join_irreducible_below w z \<longrightarrow> w \<le> y"
        proof (rule allI, rule impI)
          fix w
          assume 15: "join_irreducible_below w z"
          hence "mono_atomic_with w a"
            using 7 by (metis assms(4) join_irreducible_def mono_atomic_with_downclosed)
          hence "w \<le> v"
            using 9 15 by (simp add: join_irreducible_above_or_bot_def mono_atomic_with_def)
          thus "w \<le> y"
            using 8 14 by force
        qed
        thus "z \<le> y"
          using assms(1) by blast
      qed
      thus ?thesis
        using 6 10 11 sup.order_iff sup_monoid.add_commute by force
    qed
  qed
  thus "join_irreducible x"
    using 5 join_irreducible_def by blast
qed

text \<open>
The following result shows that under divisibility axioms A1--A3, A5--A6, B7--B9, A11 and B14, join-irreducible elements coincide with mono-atomic elements.
\<close>

lemma mono_atomic_iff_join_irreducible:
  assumes "B7_pre_f_decomposable _"
      and "B8_fibered _"
      and "B9_f_decomposable _"
      and "A11_atomic _"
      and "B14_truncability _"
    shows "mono_atomic x \<longleftrightarrow> join_irreducible x"
proof (rule iffI)
  assume 1: "mono_atomic x"
  from this obtain a where "mono_atomic_below a x"
    by blast
  hence 2: "x \<noteq> bot"
    using atom_def bot_unique mono_atomic_def by force
  have "\<forall>y z . x = y \<squnion> z \<longrightarrow> x = y \<or> x = z"
  proof (intro allI, rule impI)
    fix y z
    assume 3: "x = y \<squnion> z"
    show "x = y \<or> x = z"
    proof (cases "y = bot \<or> z = bot")
      case True
      thus ?thesis
        using 3 by fastforce
    next
      case False
      hence "mono_atomic y \<and> mono_atomic z"
        using 1 3 by (metis assms(4) mono_atomic_above sup.cobounded1 sup_right_divisibility mono_atomic_with_downclosed)
      hence "y \<le> z \<or> z \<le> y"
        using 1 3 assms(2) by force
      thus ?thesis
        using 3 sup.order_iff sup_monoid.add_commute by force
    qed
  qed
  thus "join_irreducible x"
    using 2 join_irreducible_def by blast
next
  assume "join_irreducible x"
  from this obtain a where 4: "atom a \<and> join_irreducible_above x a"
    using assms(4) join_irreducible_def by blast
  let ?y = "mval a x"
  let ?z = "mtrunc ?y x"
  have 5: "mval a ?z = bot"
    using 4 by (smt (z3) assms(3,5) mono_atomic_above_or_bot_def mtrunc_char mval_char)
  have 6: "mono_atomic_above_or_bot ?y a"
    using 4 assms(3) mval_char by simp
  hence "\<forall>b . atom b \<and> b \<noteq> a \<longrightarrow> \<not> b \<le> ?y"
    using 4 by (metis atom_def bot_unique mono_atomic_above_or_bot_def mono_atomic_def)
  hence 7: "\<forall>b . atom b \<and> b \<noteq> a \<longrightarrow> mval b ?z = mval b x"
    by (simp add: assms(5) mtrunc_char)
  have 8: "?y \<le> x"
    using 4 assms(3) mval_char by blast
  have "\<forall>b . atom b \<longrightarrow> mval b ?z \<le> x"
  proof (rule allI, rule impI)
    fix b
    assume 9: "atom b"
    show "mval b ?z \<le> x"
    proof (cases "b = a")
      case True
      thus ?thesis
        using 5 by auto
    next
      case False
      thus ?thesis
        using 7 9 by (simp add:  assms(3) mval_char)
    qed
  qed
  hence 10: "?z \<le> x"
    using 4 assms(1,3) lesseq_iff_mval_below by blast
  have "\<forall>w . ?y \<le> w \<and> ?z \<le> w \<longrightarrow> x \<le> w"
  proof (rule allI, rule impI)
    fix w
    assume 11: "?y \<le> w \<and> ?z \<le> w"
    have "\<forall>c . atom c \<longrightarrow> mval c x \<le> w"
    proof (rule allI, rule impI)
      fix c
      assume 12: "atom c"
      show "mval c x \<le> w"
      proof (cases "c = a")
        case True
        thus ?thesis
          using 11 by blast
      next
        case False
        thus ?thesis
          using 7 11 12 by (smt (z3) assms(3) dual_order.trans mval_char)
      qed
    qed
    thus "x \<le> w"
      using 4 assms(1,3) lesseq_iff_mval_below by blast
  qed
  hence 13: "x = ?y \<squnion> ?z"
    using 8 10 order.ordering_axioms ordering.antisym by force
  have "x \<noteq> ?z"
  proof (rule notI)
    assume "x = ?z"
    hence "?y = bot"
      using 5 by force
    hence "a = bot"
      using 4 assms(3) atom_below_mval bot_unique by fastforce
    thus False
      using 4 atom_def by blast
  qed
  hence "x = ?y"
    using 4 13 join_irreducible_def by force
  thus "mono_atomic x"
    using 4 6 join_irreducible_def mono_atomic_above_or_bot_def by auto
qed

end

end
