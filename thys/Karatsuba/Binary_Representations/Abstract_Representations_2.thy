subsection "Abstract Representations 2"

theory Abstract_Representations_2
  imports Main
begin

text "Idea: a subset @{term represented_set} of some type @{text 'a} is represented non-uniquely by
some type @{text 'b}."

locale abstract_representation_2 =
  fixes from_type :: "'a \<Rightarrow> 'b"
  fixes to_type :: "'b \<Rightarrow> 'a"
  fixes represented_set :: "'a set"
  assumes to_from: "\<And>x. x \<in> represented_set \<Longrightarrow> to_type (from_type x) = x"
  assumes to_type_in_represented_set: "\<And>y. to_type y \<in> represented_set"
begin

definition reduce where
"reduce x \<equiv> from_type (to_type x)"

abbreviation reduced where
"reduced x \<equiv> reduce x = x"

lemma reduce_reduce[simp]: "reduced (reduce x)"
  unfolding reduce_def
  by (simp add: to_from to_type_in_represented_set)

definition representations where
"representations \<equiv> from_type ` represented_set"

lemma range_reduce: "representations = range reduce"
  unfolding representations_def reduce_def
  image_def 
  apply (intro equalityI subsetI)
  subgoal for x
  proof -
    assume "x \<in> {y. \<exists>x\<in>represented_set. y = from_type x}"
    then have "\<exists>y\<in>represented_set. x = from_type y" by simp
    then obtain y where "x = from_type y" "y \<in> represented_set" by blast
    then have "to_type x = y" using to_from by simp
    then have "x = from_type (to_type x)" using \<open>x = from_type y\<close> by simp
    then show ?thesis by blast
  qed
  subgoal for x
    using to_type_in_represented_set by blast
  done

corollary reduced_from_type[simp]: "x \<in> represented_set \<Longrightarrow> reduced (from_type x)"
  using range_reduce representations_def reduce_reduce by force

lemma to_type_reduce: "to_type (reduce x) = to_type x"
  unfolding reduce_def
  by (simp add: to_from to_type_in_represented_set)

lemma reduced_iff: "reduced x \<longleftrightarrow> (\<exists>y\<in>represented_set. x = from_type y)"
  apply standard
  subgoal
    using reduce_def to_type_in_represented_set by metis
  subgoal
    by fastforce
  done

lemma to_eq_iff_f_eq: "to_type x = to_type y \<longleftrightarrow> reduce x = reduce y"
proof
  show "to_type x = to_type y \<Longrightarrow> reduce x = reduce y" unfolding reduce_def by simp
next
  show "reduce x = reduce y \<Longrightarrow> to_type x = to_type y" using to_type_reduce by metis
qed

lemma from_inj: "inj_on from_type represented_set"
  unfolding inj_on_def
  apply standard+
  subgoal for x y
    using to_from[of x, symmetric] to_from[of y] by simp
  done

corollary from_bij_betw: "bij_betw from_type represented_set representations"
  unfolding representations_def
  using from_inj
  by (simp add: inj_on_imp_bij_betw)

lemma correctness_to_from:
  fixes h :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes g :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes "\<And>x y. to_type (g x y) = h (to_type x) (to_type y)"
  shows "\<And>x y. x \<in> represented_set \<Longrightarrow> y \<in> represented_set \<Longrightarrow> reduce (g (from_type x) (from_type y)) = from_type (h x y)"
proof -
  fix x y
  assume "x \<in> represented_set" "y \<in> represented_set"
  have "reduce (g (from_type x) (from_type y)) = from_type (to_type (g (from_type x) (from_type y)))"
    unfolding reduce_def by simp
  also have "... = from_type (h (to_type (from_type x)) (to_type (from_type y)))"
    using assms by simp
  also have "... = from_type (h x y)"
    using to_from \<open>x \<in> represented_set\<close> \<open>y \<in> represented_set\<close> by simp
  finally show "reduce (g (from_type x) (from_type y)) = from_type (h x y)" .
qed

end

lemma from_to_f_criterion:
  assumes "\<And>x. x \<in> represented_set \<Longrightarrow> to_type (from_type x) = x"
  assumes "\<And>x. x \<in> represented_set \<Longrightarrow> f (from_type x) = from_type x"
  assumes "\<And>x y. to_type x = to_type y \<Longrightarrow> f x = f y"
  assumes "\<And>y. to_type y \<in> represented_set"
  shows "\<And>x. from_type (to_type x) = f x"
proof -
  fix x
  have "to_type (from_type (to_type x)) = to_type x"
    using assms(1) assms(4) by simp
  hence "f (from_type (to_type x)) = f x"
    using assms(3) by metis
  thus "from_type (to_type x) = f x"
    using assms(2) assms(4) by simp
qed

end