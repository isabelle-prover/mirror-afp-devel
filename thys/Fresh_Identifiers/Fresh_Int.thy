section \<open>Fresh identifier generation for integers\<close>

theory Fresh_Int
  imports Fresh
begin

text \<open>Function \<open>fresh\<close> does not follow the "find element closest to \<open>x\<close> outside of \<open>X\<close> requirement.
If \<open>x < 0\<close>, a fresh negative value is produced by repeated \<open>-1\<close>.
Similarly if \<open>x \<ge> 0\<close> with \<open>+1\<close>.
\<close>

function fresh_pos :: "int set \<Rightarrow> int \<Rightarrow> int" where
"fresh_pos X x = (if x \<notin> X \<or> infinite X then x else fresh_pos X (x+1))"
by auto
termination
  by(relation "measure (\<lambda>(X,x). nat(Max X + 1 - x))") (simp_all)

function fresh_neg :: "int set \<Rightarrow> int \<Rightarrow> int" where
"fresh_neg X x = (if x \<notin> X \<or> infinite X then x else fresh_neg X (x-1))"
by auto
termination
  by(relation "measure (\<lambda>(X,x). nat(- Min X + x + 1))") (simp_all)

lemma fresh_pos_notIn: "finite X \<Longrightarrow> fresh_pos X x \<notin> X"
  by (induct X x rule: fresh_pos.induct) auto

lemma fresh_neg_notIn: "finite X \<Longrightarrow> fresh_neg X x \<notin> X"
  by (induct X x rule: fresh_neg.induct) auto

instantiation int :: fresh
begin

text \<open>\<open>fresh xs x y\<close> returns an element
that is fresh for \<open>xs\<close> and closest to \<open>x\<close>, favoring smaller elements: \<close>

definition fresh_int :: "int set \<Rightarrow> int \<Rightarrow> int" where
"fresh_int X x \<equiv> if x < 0 then fresh_neg X x else fresh_pos X x"

instance
proof (standard, goal_cases)
  case (1 F x)
  then show ?case unfolding fresh_int_def
    by (metis fresh_pos_notIn fresh_neg_notIn)
next
  case (2 x A)
  then show ?case unfolding fresh_int_def by simp
qed

end (* instantiation *)

instantiation int :: fresh0
begin

definition fresh0_default_int :: nat where
"fresh0_default_int \<equiv> 0"

instance ..

end (* instantiation *)

text \<open>Code generation\<close>

lemma fresh_pos_list[code]:
  "fresh_pos (set xs) x =
     (if x \<notin> set xs then x else fresh_pos (set xs) (x+1))"
  by (simp)

lemma fresh_neg_list[code]:
  "fresh_neg (set xs) x =
     (if x \<notin> set xs then x else fresh_neg (set xs) (x-1))"
  by (simp)

text \<open>Some tests: \<close>

value "[fresh {} 1, fresh {3,5,2,4} 3, fresh {-2,-3} (-2)] :: int list"

end
