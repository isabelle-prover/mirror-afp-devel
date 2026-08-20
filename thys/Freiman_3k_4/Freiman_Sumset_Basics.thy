theory Freiman_Sumset_Basics
  imports Main
begin

definition sumset :: "('a::comm_monoid_add) set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "sumset A B = {x. \<exists>a\<in>A. \<exists>b\<in>B. x = a + b}"

lemma sumset_iff:
  "x \<in> sumset A B \<longleftrightarrow> (\<exists>a\<in>A. \<exists>b\<in>B. x = a + b)"
  by (auto simp: sumset_def)

lemma sumsetI [intro]:
  assumes "a \<in> A" "b \<in> B"
  shows "a + b \<in> sumset A B"
  using assms by (auto simp: sumset_def)

lemma sumsetE [elim]:
  assumes "x \<in> sumset A B"
  obtains a b where "a \<in> A" "b \<in> B" "x = a + b"
  using assms by (auto simp: sumset_def)

lemma sumset_as_image:
  "sumset A B = case_prod (+) ` (A \<times> B)"
  by (auto simp: sumset_def)

lemma sumset_commute:
  "sumset A B = sumset B A"
proof
  show "sumset A B \<subseteq> sumset B A"
  proof
    fix x
    assume "x \<in> sumset A B"
    then obtain a b where "a \<in> A" "b \<in> B" "x = a + b"
      by (auto simp: sumset_def)
    then show "x \<in> sumset B A"
    proof -
      have "b + a \<in> sumset B A"
        using \<open>b \<in> B\<close> \<open>a \<in> A\<close> by auto
      then show ?thesis
        using \<open>x = a + b\<close> by (simp add: add.commute)
    qed
  qed
next
  show "sumset B A \<subseteq> sumset A B"
  proof
    fix x
    assume "x \<in> sumset B A"
    then obtain b a where "b \<in> B" "a \<in> A" "x = b + a"
      by (auto simp: sumset_def)
    then show "x \<in> sumset A B"
    proof -
      have "a + b \<in> sumset A B"
        using \<open>a \<in> A\<close> \<open>b \<in> B\<close> by auto
      then show ?thesis
        using \<open>x = b + a\<close> by (simp add: add.commute)
    qed
  qed
qed

lemma empty_sumset_left [simp]:
  "sumset {} B = {}"
  by (auto simp: sumset_def)

lemma empty_sumset_right [simp]:
  "sumset A {} = {}"
  by (auto simp: sumset_def)

lemma sumset_assoc:
  fixes A B C :: "('a::comm_monoid_add) set"
  shows "sumset (sumset A B) C = sumset A (sumset B C)"
proof
  show "sumset (sumset A B) C \<subseteq> sumset A (sumset B C)"
  proof
    fix x
    assume "x \<in> sumset (sumset A B) C"
    then obtain ab c where ab: "ab \<in> sumset A B" and c: "c \<in> C" and x: "x = ab + c"
      by blast
    from ab obtain a b where a: "a \<in> A" and b: "b \<in> B" and ab_eq: "ab = a + b"
      by blast
    have "b + c \<in> sumset B C"
      using b c by auto
    then show "x \<in> sumset A (sumset B C)"
    proof -
      have "a + (b + c) \<in> sumset A (sumset B C)"
        using a \<open>b + c \<in> sumset B C\<close> by auto
      then show ?thesis
        using x ab_eq by (simp add: add.assoc)
    qed
  qed
next
  show "sumset A (sumset B C) \<subseteq> sumset (sumset A B) C"
  proof
    fix x
    assume "x \<in> sumset A (sumset B C)"
    then obtain a bc where a: "a \<in> A" and bc: "bc \<in> sumset B C" and x: "x = a + bc"
      by blast
    from bc obtain b c where b: "b \<in> B" and c: "c \<in> C" and bc_eq: "bc = b + c"
      by blast
    have "a + b \<in> sumset A B"
      using a b by auto
    then show "x \<in> sumset (sumset A B) C"
    proof -
      have "(a + b) + c \<in> sumset (sumset A B) C"
      proof (rule sumsetI)
        show "a + b \<in> sumset A B"
          using \<open>a + b \<in> sumset A B\<close> .
        show "c \<in> C"
          using c .
      qed
      then show ?thesis
        using x bc_eq by (simp add: add.assoc)
    qed
  qed
qed

lemma finite_sumset [intro]:
  assumes "finite A" "finite B"
  shows "finite (sumset A B)"
  unfolding sumset_as_image
  using assms by (intro finite_imageI finite_cartesian_product)

end
