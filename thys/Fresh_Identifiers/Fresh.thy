section \<open>The type class \<open>fresh\<close>\<close>

theory Fresh
  imports Main
begin

text \<open>A type in this class comes with a mechanism to generate fresh elements.
The \<open>fresh\<close> operator takes a set of items to be avoided, \<open>X\<close>, and
a preferred element to be generated, \<open>x\<close>.

It is required that implementations of fresh for specific types produce \<open>x\<close> if possible
(i.e., if not in \<open>X\<close>).

While not required, it is also expected that, if \<open>x\<close> is not possible,
then implementation produces an element that is as close to \<open>x\<close> as
possible, given a notion of distance.

A subclass \<open>fresh0\<close> provides function \<open>fresh0 :: 'a set \<Rightarrow> 'a\<close> that does not require
an initial item.
\<close>

class fresh =
  fixes fresh :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fresh_notIn: "finite F \<Longrightarrow> fresh F x \<notin> F"
  and fresh_eq: "x \<notin> A \<Longrightarrow> fresh A x = x"
begin

text \<open>Generate a list of fresh names \<open>[a', b', c', \<dots>]\<close> given the list \<open>[a, b, c, \<dots>]\<close>:\<close>

fun freshs :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"freshs X [] = []" |
"freshs X (a#as) = (let a' = fresh X a in a' # freshs (insert a' X) as)"

lemma length_freshs: "finite X \<Longrightarrow> length(freshs X as) = length as"
by(induction as arbitrary: X)(auto simp: fresh_notIn Let_def)

lemma freshs_disj: "finite X \<Longrightarrow> X \<inter> set(freshs X as) = {}"
proof(induction as arbitrary: X)
  case Cons
  then show ?case using fresh_notIn by(auto simp add: Let_def)
qed simp

lemma freshs_distinct: "finite X \<Longrightarrow> distinct (freshs X as)"
proof(induction as arbitrary: X)
  case (Cons a as)
  then show ?case
    using freshs_disj[of "insert (fresh X a) X" as] fresh_notIn by(auto simp add: Let_def)
qed simp

end

text \<open>The type class \<^class>\<open>fresh\<close> is essentially the same as
the type class \<open>infinite\<close> but with an emphasis on fresh item generation.\<close>

class infinite =
  assumes infinite_UNIV: "\<not> finite (UNIV :: 'a set)"

text \<open>We can subclass \<^class>\<open>fresh\<close> to \<^class>\<open>infinite\<close> since the latter
has no associated operators (in particular, no additional operators w.r.t.
the former).\<close>

subclass (in fresh) infinite
  apply (standard)
  using local.fresh_notIn by auto

class fresh0 = fresh +
fixes fresh0_default :: "'a"
begin

definition fresh0 :: "'a set \<Rightarrow> 'a" where
"fresh0 X = fresh X fresh0_default"

lemma fresh0_notIn: "finite F \<Longrightarrow> fresh0 F \<notin> F"
unfolding fresh0_def by(rule fresh_notIn)

end

end
