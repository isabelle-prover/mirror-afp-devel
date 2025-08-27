section \<open>The type class \<open>fresh\<close>\<close>

theory Fresh
  imports Main
begin

text \<open>A type in this class comes with a mechanism to generate fresh elements.
The \<open>fresh\<close> operator takes a set of items to be avoided, \<open>xs\<close>, and
a preferred element to be generated, \<open>x\<close>.

It is required that implementations of fresh for specific types produce \<open>x\<close> if possible
(i.e., if not in \<open>xs\<close>).

While not required, it is also expected that, if \<open>x\<close> is not possible,
then implementation produces an element that is as close to \<open>x\<close> as
possible, given a notion of distance.
\<close>

class fresh =
  fixes fresh :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes fresh_notIn: "finite F \<Longrightarrow> fresh F x \<notin> F"
  and fresh_eq: "x \<notin> A \<Longrightarrow> fresh A x = x"
begin

text \<open>Generate a list of fresh names \<open>[a', b', c', \<dots>]\<close> given a list \<open>[a, b, c, \<dots>]\<close>:\<close>

fun freshs :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"freshs X [] = []" |
"freshs X (a#as) = (let a' = fresh X a in a' # freshs (insert a' X) as)"

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

end
