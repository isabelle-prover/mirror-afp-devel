section \<open>Words over the terminals \<open>{A,B,C}\<close>\<close>

theory ABC_Words
imports Main
begin

text \<open>This theory is convenient for examples involving exactly the letters A, B, C.
These examples often involve families \<open>A^i B^j C^k\<close>. Hence \<open>sorted\<close> is relevant.
\<close>

datatype letter = A | B | C

definition abcword :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> letter list" where
"abcword i j k = replicate i A @ replicate j B @ replicate k C"

text \<open>Letter counts of an \<open>abcword\<close> recover its three exponents.\<close>

lemma count_abcword:
  "count_list (abcword i j k) A = i"
  "count_list (abcword i j k) B = j"
  "count_list (abcword i j k) C = k"
  by (auto simp: abcword_def)

lemma abcword_inj: "abcword i j k = abcword i' j' k' \<Longrightarrow> i = i' \<and> j = j' \<and> k = k'"
  by (metis count_abcword)

text \<open>Order the alphabet \<open>A < B < C\<close>.\<close>

fun rank :: "letter \<Rightarrow> nat" where
"rank A = 0" | "rank B = Suc 0" | "rank C = Suc (Suc 0)"

lemma rank_inj: "rank x = rank y \<Longrightarrow> x = y"
  by (cases x; cases y) simp_all

instantiation letter :: linorder
begin

definition less_eq_letter :: "letter \<Rightarrow> letter \<Rightarrow> bool" where
"less_eq_letter x y \<longleftrightarrow> rank x \<le> rank y"

definition less_letter :: "letter \<Rightarrow> letter \<Rightarrow> bool" where
"less_letter x y \<longleftrightarrow> rank x < rank y"

instance
  by intro_classes (auto simp: less_eq_letter_def less_letter_def dest: rank_inj)

end

lemma abcword_sorted: "sorted (abcword i j k)"
  by (auto simp: abcword_def sorted_append less_eq_letter_def)

text \<open>A factor that occurs squared inside a sorted word is uniform (all one letter).\<close>

lemma sorted_square_uniform:
  assumes "sorted (ys @ ys)" "a \<in> set ys" "b \<in> set ys"
  shows "a = b"
proof -
  from assms(1) have "\<forall>p\<in>set ys. \<forall>q\<in>set ys. p \<le> q" by (auto simp: sorted_append)
  thus ?thesis using assms(2,3) by (meson antisym)
qed

lemma sorted_factor_uniform:
  assumes "sorted (u @ ys @ ys @ v)" "a \<in> set ys" "b \<in> set ys"
  shows "a = b"
proof -
  have "sorted (ys @ ys)" using assms(1) by (auto simp: sorted_append)
  thus ?thesis using sorted_square_uniform assms(2,3) by blast
qed

end
