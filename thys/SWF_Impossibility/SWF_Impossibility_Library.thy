section \<open>Auxiliary Material\<close>
subsection \<open>Miscellaneous\<close>
theory SWF_Impossibility_Library
imports
  "Randomised_Social_Choice.Preference_Profiles"
  "HOL-Combinatorics.Multiset_Permutations"
begin

lemma wfp_on_iff_wfp: "wfp_on A R \<longleftrightarrow> wfp (\<lambda>x y. R x y \<and> x \<in> A \<and> y \<in> A)"
proof -
  have "wfp_on A R \<longleftrightarrow> wf_on A {(x,y). R x y}"
    by (simp add: wfp_on_def wf_on_def)
  also have "\<dots> = wf {(x,y). R x y \<and> x \<in> A \<and> y \<in> A}"
    by (subst wf_on_iff_wf) simp_all
  also have "\<dots> \<longleftrightarrow> wfp (\<lambda>x y. R x y \<and> x \<in> A \<and> y \<in> A)"
    by (simp add: wfp_def)
  finally show ?thesis .
qed

lemma permutations_of_set_conv_mset:
  "finite A \<Longrightarrow> permutations_of_set A = {xs. mset xs = mset_set A}"
  by (metis permutations_of_multiset_def permutations_of_set_altdef)

lemma Set_filter_insert_if:
  "Set.filter P (insert x A) = (if P x then insert x (Set.filter P A) else Set.filter P A)"
  by auto

lemma Set_filter_insert:
  "P x \<Longrightarrow> Set.filter P (insert x A) = insert x (Set.filter P A)"
  "\<not>P x \<Longrightarrow> Set.filter P (insert x A) = Set.filter P A"
  by auto

lemma Set_filter_empty [simp]: "Set.filter P {} = {}"
  by auto

(* facts about multisets *)
lemma filter_mset_empty_conv: "filter_mset P A = {#} \<longleftrightarrow> (\<forall>x\<in>#A. \<not>P x)"
  by (induction A) auto

lemma image_mset_repeat_mset: "image_mset f (repeat_mset n A) = repeat_mset n (image_mset f A)"
  by (induction A) auto

lemma filter_mset_repeat_mset: "filter_mset P (repeat_mset n A) = repeat_mset n (filter_mset P A)"
  by (induction n) auto

lemma mset_eq_mset_set_iff:
  assumes "finite A"
  shows   "mset xs = mset_set A \<longleftrightarrow> xs \<in> permutations_of_set A"
  using assms unfolding permutations_of_set_def mem_Collect_eq
  by (metis mset_set_set permutations_of_multisetI permutations_of_setD(1,2) permutations_of_set_altdef)

lemma size_Diff_mset_same_size:
  fixes A B :: "'a multiset"
  assumes "size (A - B) = n" "size A = size B"
  shows   "size (B - A) = n"
proof -
  define E where "E = A - B"
  define C where "C = B \<inter># A"
  define D where "D = B - A"
  have "B = C + D"
    unfolding C_def D_def by (simp add: inter_mset_def)
  have "A - B + B = E + B"
    by (simp add: E_def)
  also have "A - B + B = A + D" unfolding D_def
    by (metis add.commute subset_mset.inf.commute union_diff_inter_eq_sup union_mset_def)
  finally have "size (A + D) = size (E + B)"
    by (rule arg_cong)
  hence "size A + size D = size B + size E"
    by simp
  also have "size A = size B"
    by fact
  finally have "size D = size E"
    by simp
  thus ?thesis using assms
    by (simp add: D_def E_def)
qed

lemma image_mset_diff_if_inj_on:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "inj_on f (set_mset (A+B))"
  shows "image_mset f (A - B) = image_mset f A - image_mset f B"
  using assms
proof (induction B arbitrary: A)
  case (add x B A)
  show ?case
  proof (cases "x \<in># A")
    case False
    hence "f x \<notin># image_mset f A"
      using add.prems by auto
    have "image_mset f (A - add_mset x B) = image_mset f (A - B)"
      using False by simp
    also have "\<dots> = image_mset f A - image_mset f B"
      by (rule add.IH) (use add.prems in auto)
    also have "\<dots> = image_mset f A - image_mset f (add_mset x B)"
      using \<open>f x \<notin># image_mset f A\<close> by simp
    finally show ?thesis .
  next
    case True
    define A' where "A' = A - {#x#}"
    have A_eq: "A = A' + {#x#}"
      using True by (simp add: A'_def)
    have "image_mset f (A - add_mset x B) = image_mset f (A' - B)"
      by (simp add: A_eq)
    also have "\<dots> = image_mset f A' - image_mset f B"
      by (rule add.IH) (use add.prems in \<open>auto simp: A_eq\<close>)
    also have "\<dots> = image_mset f A - image_mset f (add_mset x B)"
      by (simp add: A_eq)
    finally show ?thesis .
  qed
qed auto


(* material about orders *)

context preorder_on
begin

sublocale dual: preorder_on carrier "\<lambda>x y. le y x"
  by standard (use not_outside refl in \<open>auto intro: trans\<close>)

end


context order_on
begin

sublocale dual: order_on carrier "\<lambda>x y. le y x"
  by standard (use antisymmetric in auto)

end


context total_preorder_on
begin

sublocale dual: total_preorder_on carrier "\<lambda>x y. le y x"
  by standard (use total in auto)

end


context linorder_on
begin

sublocale dual: linorder_on carrier "\<lambda>x y. le y x"
  by standard (use total in auto)

end


context finite_linorder_on
begin

sublocale dual: finite_linorder_on carrier "\<lambda>x y. le y x"
  by standard auto

end


locale linorder_family = preorder_family dom carrier R for dom carrier R +
  assumes linorder_in_dom [simp]: "i \<in> dom \<Longrightarrow> linorder_on carrier (R i)"

lemma preorder_familyI [intro?]:
  fixes dom
  assumes "dom \<noteq> {}"
  assumes "\<And>i. i \<in> dom \<Longrightarrow> preorder_on carrier (R i)"
  assumes "\<And>i x y. i \<notin> dom \<Longrightarrow> \<not> R i x y"
  shows  "preorder_family dom carrier R"
  using assms unfolding preorder_family_def by auto

lemma linorder_familyI [intro?]:
  fixes dom
  assumes "dom \<noteq> {}"
  assumes "\<And>i. i \<in> dom \<Longrightarrow> linorder_on carrier (R i)"
  assumes "\<And>i x y. i \<notin> dom \<Longrightarrow> \<not> R i x y"
  shows   "linorder_family dom carrier R"
proof -
  have "preorder_family dom carrier R"
    by rule (use assms in \<open>auto simp: linorder_on_def total_preorder_on_def\<close>)
  thus ?thesis
    unfolding linorder_family_def linorder_family_axioms_def
    using assms by auto
qed


context order_on
begin

lemma order_on_restrict:
  "order_on (carrier \<inter> A) (restrict_relation A le)"
proof -
  interpret restrict: preorder_on "carrier \<inter> A" "restrict_relation A le"
    by (rule preorder_on_restrict)
  show ?thesis
    by standard (use antisymmetric in \<open>auto simp: restrict_relation_def\<close>)
qed

lemma order_on_restrict_subset:
  "A \<subseteq> carrier \<Longrightarrow> order_on A (restrict_relation A le)"
  using order_on_restrict[of A] by (simp add: Int_absorb1)

end


context linorder_on
begin

lemma linorder_on_restrict:
  "linorder_on (carrier \<inter> A) (restrict_relation A le)"
proof -
  interpret restrict: order_on "carrier \<inter> A" "restrict_relation A le"
    by (rule order_on_restrict)
  show ?thesis
    by standard (use total in \<open>auto simp: restrict_relation_def\<close>)
qed

lemma linorder_on_restrict_subset:
  "A \<subseteq> carrier \<Longrightarrow> linorder_on A (restrict_relation A le)"
  using linorder_on_restrict[of A] by (simp add: Int_absorb1)

end

lemma linorder_on_concat:
  assumes "linorder_on A R" "linorder_on B S" "A \<inter> B = {}"
  shows   "linorder_on (A \<union> B) (\<lambda>x y. if x \<in> A then R x y \<or> y \<in> B else S x y)"
proof -
  interpret R: linorder_on A R
    by fact
  interpret S: linorder_on B S
    by fact
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 x y)
    thus ?case
      using R.not_outside S.not_outside by (auto split: if_splits)
  next
    case (2 x y)
    thus ?case
      using R.not_outside S.not_outside by (auto split: if_splits)
  next
    case (3 x)
    thus ?case
      by (auto simp: R.refl S.refl)
  next
    case (4 x y z)
    thus ?case using assms(3) R.not_outside S.not_outside
      by (auto split: if_splits intro: R.trans S.trans)
  next
    case (5 x y)
    thus ?case using assms(3) R.not_outside S.not_outside
      by (auto split: if_splits intro: R.antisymmetric S.antisymmetric)
  next
    case (6 x y)
    thus ?case using R.total S.total
      by auto
  qed
qed

lemma linorder_on_prepend:
  assumes "linorder_on A R" "z \<notin> A"
  shows   "linorder_on (insert z A) (\<lambda>x y. if x = z then y \<in> insert z A else R x y)"
proof -
  have *: "linorder_on {z} (\<lambda>x y. x = z \<and> y = z)"
    by standard auto
  have "linorder_on ({z} \<union> A) (\<lambda>x y. if x \<in> {z} then x = z \<and> y = z \<or> y \<in> A else R x y)"
    by (rule linorder_on_concat) (use assms * in auto)
  also have "\<dots> = (\<lambda>x y. if x = z then y \<in> insert z A else R x y)"
    by auto
  finally show ?thesis
    by simp
qed

lemma finite_linorder_on_exists:
  assumes "finite A"
  shows   "\<exists>R. linorder_on A R"
  using assms
proof (induction rule: finite_induct)
  case empty
  have "linorder_on ({} :: 'a set) (\<lambda>_ _. False)"
    by standard auto
  thus ?case by blast
next
  case (insert x A)
  from insert.IH obtain R where R: "linorder_on A R"
    by blast
  have "linorder_on (insert x A) (\<lambda>y z. if y = x then z \<in> insert x A else R y z)"
    by (rule linorder_on_prepend) fact+
  thus ?case
    by blast
qed



context order_on
begin

lemma order_on_map:
  assumes "bij_betw f A carrier"
  shows   "order_on A (restrict_relation A (map_relation f le))"
proof -
  have "preorder_on (f -` carrier) (map_relation f le)"
    by (rule preorder_on_map)
  hence "preorder_on (f -` carrier \<inter> A) (restrict_relation A (map_relation f le))"
    by (rule preorder_on.preorder_on_restrict)
  also have "f -` carrier \<inter> A = A"
    using assms by (auto simp: bij_betw_def)
  finally interpret f: preorder_on A "restrict_relation A (map_relation f le)" .

  show ?thesis
  proof
    fix x y
    assume "restrict_relation A (map_relation f le) x y" "restrict_relation A (map_relation f le) y x"
    hence "f x = f y" "x \<in> A" "y \<in> A" using antisymmetric
      by (auto simp: restrict_relation_def map_relation_def)
    thus "x = y"
      using assms by (auto simp: bij_betw_def inj_on_def)
  qed
qed

end



context linorder_on
begin

lemma linorder_on_map:
  assumes "bij_betw f A carrier"
  shows   "linorder_on A (restrict_relation A (map_relation f le))"
proof -
  interpret order_on A "restrict_relation A (map_relation f le)"
    by (rule order_on_map) fact

  have "total_preorder_on (f -` carrier) (map_relation f le)"
    by (rule total_preorder_on_map)
  hence "total_preorder_on (f -` carrier \<inter> A) (restrict_relation A (map_relation f le))"
    by (rule total_preorder_on.total_preorder_on_restrict)
  also have "f -` carrier \<inter> A = A"
    using assms by (auto simp: bij_betw_def)
  finally interpret f: total_preorder_on A "restrict_relation A (map_relation f le)" .
  show ?thesis ..
qed

end


context finite_linorder_on
begin

lemma finite_linorder_on_map:
  assumes "bij_betw f A carrier"
  shows   "finite_linorder_on A (restrict_relation A (map_relation f le))"
proof -
  interpret linorder_on A "restrict_relation A (map_relation f le)"
    by (rule linorder_on_map) fact
  have [simp]: "finite A"
    using finite_carrier bij_betw_finite[OF assms] by simp
  show ?thesis
    by standard auto
qed

end



subsection \<open>The Majority Relation\<close>

text \<open>
  Given a family of preorders, the majority relation induced by it is the one where $x$ and $y$
  are related iff $x \preceq y$ holds in at least half of the relations in the family.

  Note that the majority relation is in general neither antisymmetric
  (due to the possibility of ties) nor transitive (due to Condorcet cycles).
\<close>

definition majority :: "('a \<Rightarrow> 'b relation) \<Rightarrow> 'b relation" where
  "majority R x y \<longleftrightarrow> (\<exists>i. R i x x) \<and> (\<exists>i. R i y y) \<and> card {i. R i x y} \<ge> card {i. R i y x}"

text \<open>
  The same notion can easily be defined for multisets of relations as well.
\<close>
definition majority_mset :: "'a relation multiset \<Rightarrow> 'a relation" where
  "majority_mset Rs x y \<longleftrightarrow>
     (\<exists>R\<in>#Rs. R x x) \<and> (\<exists>R\<in>#Rs. R y y) \<and> 
     size (filter_mset (\<lambda>R. R x y) Rs) \<ge> size (filter_mset (\<lambda>R. R y x) Rs)"

lemma majority_mset_not_outside:
  assumes "majority_mset Rs x y" "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R"
  shows   "x \<in> A" "y \<in> A"
proof -
  from assms(1) obtain R1 R2 where "R1 \<in># Rs" "R2 \<in># Rs" "R1 x x" "R2 y y"
    unfolding majority_mset_def by blast
  thus "x \<in> A" "y \<in> A"
    using assms(2) by (meson preorder_on.not_outside(1))+
qed

lemma majority_mset_refl_iff': "majority_mset Rs x x \<longleftrightarrow> (\<exists>R\<in>#Rs. R x x)"
  unfolding majority_mset_def by simp

lemma majority_mset_refl_iff:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R" "Rs \<noteq> {#}"
  shows   "majority_mset Rs x x \<longleftrightarrow> x \<in> A"
  unfolding majority_mset_refl_iff' using assms
  by (metis multiset_nonemptyE preorder_on.not_outside(1) preorder_on.refl)

lemma majority_mset_refl: 
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R" "Rs \<noteq> {#}" "x \<in> A"
  shows   "majority_mset Rs x x"
  using majority_mset_refl_iff[OF assms(1,2)] assms(3) by simp

lemma majority_mset_iff':
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R" "Rs \<noteq> {#}"
  shows   "majority_mset Rs x y \<longleftrightarrow>
             x \<in> A \<and> y \<in> A \<and> 
             size (filter_mset (\<lambda>R. R x y) Rs) \<ge> size (filter_mset (\<lambda>R. R y x) Rs)"
proof -
  obtain R where R: "R \<in># Rs"
    using \<open>Rs \<noteq> {#}\<close> by auto
  interpret R: preorder_on A R
    using assms(1) R by auto
  have *: "R x x \<longleftrightarrow> x \<in> A" if "R \<in># Rs" for R x
    using assms(1)[OF that] preorder_on.refl preorder_on.not_outside(1) by metis
  show ?thesis using R
    unfolding majority_mset_def by (auto simp: *)
qed

lemma majority_mset_iff:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R" "Rs \<noteq> {#}" "x \<in> A" "y \<in> A"
  shows   "majority_mset Rs x y \<longleftrightarrow>
             size (filter_mset (\<lambda>R. R x y) Rs) \<ge> size (filter_mset (\<lambda>R. R y x) Rs)"
  by (subst majority_mset_iff'[of Rs A]) (use assms in auto)

lemma majority_mset_iff_ge:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on A R" "Rs \<noteq> {#}" "x \<in> A" "y \<in> A"
  shows   "majority_mset Rs x y \<longleftrightarrow>
             2 * size (filter_mset (\<lambda>R. R x y) Rs) \<ge> size Rs"
proof (cases "x = y")
  case True
  have [simp]: "R y y" if "R \<in># Rs" for R
    using assms(1) \<open>y \<in> A\<close> by (metis linorder_on_def that total_preorder_on.total)
  have "majority_mset Rs y y"
    using assms by (metis linorder_on_def majority_mset_refl order_on_def)
  moreover have "{#R \<in># Rs. R y y#} = filter_mset (\<lambda>_. True) Rs"
    by (intro filter_mset_cong) auto
  ultimately show ?thesis using True
    by simp
next
  case False
  have "Rs = filter_mset (\<lambda>R. R x y) Rs + filter_mset (\<lambda>R. \<not>R x y) Rs"
    by (rule multiset_partition)
  also have "size \<dots> = size (filter_mset (\<lambda>R. R x y) Rs) + size (filter_mset (\<lambda>R. \<not>R x y) Rs)"
    by (rule size_union)
  also have "filter_mset (\<lambda>R. \<not>R x y) Rs = filter_mset (\<lambda>R. R y x) Rs"
  proof (rule filter_mset_cong)
    fix R assume "R \<in># Rs"
    then interpret R: linorder_on A R using assms(1) by auto
    show "\<not>R x y \<longleftrightarrow> R y x"
      using \<open>x \<noteq> y\<close> R.antisymmetric R.total assms(3-4) by blast
  qed auto
  finally have eq: "size Rs = size {#R \<in># Rs. R x y#} + size {#R \<in># Rs. R y x#}" .
  show ?thesis
  proof (subst majority_mset_iff[of Rs A])
    fix R assume "R \<in># Rs"
    then interpret linorder_on A R using assms(1) by blast
    show "preorder_on A R" ..
  qed (use assms eq in auto)
qed

lemma majority_mset_iff_le:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on A R" "Rs \<noteq> {#}" "x \<in> A" "y \<in> A" "x \<noteq> y"
  shows   "majority_mset Rs x y \<longleftrightarrow>
             2 * size (filter_mset (\<lambda>R. R y x) Rs) \<le> size Rs"
proof -
  have "Rs = filter_mset (\<lambda>R. R x y) Rs + filter_mset (\<lambda>R. \<not>R x y) Rs"
    by (rule multiset_partition)
  also have "size \<dots> = size (filter_mset (\<lambda>R. R x y) Rs) + size (filter_mset (\<lambda>R. \<not>R x y) Rs)"
    by (rule size_union)
  also have "filter_mset (\<lambda>R. \<not>R x y) Rs = filter_mset (\<lambda>R. R y x) Rs"
  proof (rule filter_mset_cong)
    fix R assume "R \<in># Rs"
    then interpret R: linorder_on A R using assms(1) by auto
    show "\<not>R x y \<longleftrightarrow> R y x"
      using \<open>x \<noteq> y\<close> R.antisymmetric R.total assms(3-4) by blast
  qed auto
  finally have eq: "size Rs = size {#R \<in># Rs. R x y#} + size {#R \<in># Rs. R y x#}" .
  show ?thesis
  proof (subst majority_mset_iff[of Rs A])
    fix R assume "R \<in># Rs"
    then interpret linorder_on A R using assms(1) by blast
    show "preorder_on A R" ..
  qed (use assms eq in auto)
qed

lemma strongly_preferred_majority_mset_iff_gt:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on A R" "Rs \<noteq> {#}" "x \<in> A" "y \<in> A"
  shows   "x \<prec>[majority_mset Rs] y \<longleftrightarrow> x \<noteq> y \<and>
             2 * size (filter_mset (\<lambda>R. R x y) Rs) > size Rs"
proof (cases "x = y")
  case True
  show ?thesis using True
    by (auto simp: strongly_preferred_def)
next
  case False
  have "Rs = filter_mset (\<lambda>R. R x y) Rs + filter_mset (\<lambda>R. \<not>R x y) Rs"
    by (rule multiset_partition)
  also have "size \<dots> = size (filter_mset (\<lambda>R. R x y) Rs) + size (filter_mset (\<lambda>R. \<not>R x y) Rs)"
    by (rule size_union)
  also have "filter_mset (\<lambda>R. \<not>R x y) Rs = filter_mset (\<lambda>R. R y x) Rs"
  proof (rule filter_mset_cong)
    fix R assume "R \<in># Rs"
    then interpret R: linorder_on A R using assms(1) by auto
    show "\<not>R x y \<longleftrightarrow> R y x"
      using \<open>x \<noteq> y\<close> R.antisymmetric R.total assms(3-4) by blast
  qed auto
  finally have eq: "size Rs = size {#R \<in># Rs. R x y#} + size {#R \<in># Rs. R y x#}" .
  show ?thesis unfolding strongly_preferred_def
  proof (subst (1 2) majority_mset_iff[of Rs A])
    fix R assume "R \<in># Rs"
    then interpret linorder_on A R using assms(1) by blast
    show "preorder_on A R" ..
  qed (use assms eq in auto)
qed

lemma strongly_preferred_majority_mset_iff_lt:
  assumes "\<And>R. R \<in># Rs \<Longrightarrow> linorder_on A R" "Rs \<noteq> {#}" "x \<in> A" "y \<in> A"
  shows   "x \<prec>[majority_mset Rs] y \<longleftrightarrow>
             2 * size (filter_mset (\<lambda>R. R y x) Rs) < size Rs"
proof (cases "x = y")
  case True
  have [simp]: "R y y" if "R \<in># Rs" for R
    using assms(1) \<open>y \<in> A\<close> by (metis linorder_on_def that total_preorder_on.total)
  have "{#R \<in># Rs. R y y#} = filter_mset (\<lambda>_. True) Rs"
    by (intro filter_mset_cong) auto
  thus ?thesis using True
    by (auto simp: strongly_preferred_def)
next
  case False
  have *: "\<And>R. R \<in># Rs \<Longrightarrow> preorder_on A R"
    using assms(1) by (simp add: linorder_on_def order_on_def)
  have "x \<prec>[majority_mset Rs] y \<longleftrightarrow> \<not>(y \<preceq>[majority_mset Rs] x)"
    using False majority_mset_iff[OF * assms(2)] assms(3,4)
    by (auto simp: strongly_preferred_def)
  also have "\<dots> \<longleftrightarrow> size Rs > 2 * size {#R \<in># Rs. R y x#}"
    by (subst majority_mset_iff_ge[of Rs A]) (use assms in auto)
  finally show ?thesis .
qed

context preorder_family
begin

lemma majority_iff':
  "majority R x y \<longleftrightarrow> x \<in> carrier \<and> y \<in> carrier \<and> card {i\<in>dom. R i x y} \<ge> card {i\<in>dom. R i y x}"
proof -
  have *: "{i. R i x y} = {i\<in>dom. R i x y}" for x y
    using not_in_dom by blast
  from nonempty_dom obtain i where "i \<in> dom"
    by blast
  then interpret Ri: preorder_on carrier "R i"
    by simp
  show ?thesis
    using Ri.refl unfolding majority_def *
    by (meson in_dom not_in_dom preorder_on.not_outside(1))
qed

lemma majority_iff:
  assumes "x \<in> carrier" "y \<in> carrier"
  shows   "majority R x y \<longleftrightarrow> card {i\<in>dom. R i x y} \<ge> card {i\<in>dom. R i y x}"
  using assms by (simp add: majority_iff')

lemma majority_refl [simp]: "x \<in> carrier \<Longrightarrow> majority R x x"
  by (auto simp: majority_iff)

lemma majority_refl_iff: "majority R x x \<longleftrightarrow> x \<in> carrier"
  by (auto simp: majority_iff')

lemma majority_total: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> majority R x y \<or> majority R y x"
  by (auto simp: majority_iff)

lemma strongly_preferred_majority_iff:
  assumes "x \<in> carrier" "y \<in> carrier"
  shows   "x \<prec>[majority R] y \<longleftrightarrow> card {i\<in>dom. R i x y} > card {i\<in>dom. R i y x}"
  unfolding strongly_preferred_def by (auto simp: majority_iff assms)

lemma majority_not_outside:
  assumes "majority R x y"
  shows   "x \<in> carrier" "y \<in> carrier"
  using assms in_dom not_in_dom preorder_on.not_outside unfolding majority_def by meson+

text \<open>
  The majority relation chains with the unanimity relation.
\<close>
lemma majority_Pareto1:
  assumes "Pareto R x y" "majority R y z" "finite dom"
  shows   "majority R x z"
proof -
  have xyz: "x \<in> carrier" "y \<in> carrier" "z \<in> carrier"
    using Pareto.not_outside assms majority_not_outside by auto
   have "card {i \<in> dom. R i z x} \<le> card {i \<in> dom. R i z y}"
    by (rule card_mono)
       (use assms(1,3) in_dom in \<open>auto simp: Pareto_iff intro: preorder_on.trans[OF in_dom]\<close>)
  also have "card {i \<in> dom. R i z y} \<le> card {i \<in> dom. R i y z}"
    using assms(2) xyz by (simp add: majority_iff)
  also have "\<dots> \<le> card {i \<in> dom. R i x z}"
    by (rule card_mono)
       (use assms(1,3) in_dom in \<open>auto simp: Pareto_iff intro: preorder_on.trans[OF in_dom]\<close>)
  finally show ?thesis
    using assms(2) xyz by (simp add: majority_iff)
qed

lemma majority_Pareto2:
  assumes "majority R x y" "Pareto R y z" "finite dom"
  shows   "majority R x z"
proof -
  have xyz: "x \<in> carrier" "y \<in> carrier" "z \<in> carrier"
    using Pareto.not_outside assms majority_not_outside by auto
   have "card {i \<in> dom. R i z x} \<le> card {i \<in> dom. R i y x}"
    by (rule card_mono)
       (use assms in_dom in \<open>auto simp: Pareto_iff intro: preorder_on.trans[OF in_dom]\<close>)
  also have "card {i \<in> dom. R i y x} \<le> card {i \<in> dom. R i x y}"
    using assms(1) xyz by (simp add: majority_iff)
  also have "\<dots> \<le> card {i \<in> dom. R i x z}"
    by (rule card_mono)
       (use assms in_dom in \<open>auto simp: Pareto_iff intro: preorder_on.trans[OF in_dom]\<close>)
  finally show ?thesis
    using assms(2) xyz by (simp add: majority_iff)
qed

lemma majority_conv_majority_mset:
  assumes "finite dom"
  shows   "majority R = majority_mset (image_mset R (mset_set dom))" (is "?lhs = ?rhs")
proof (intro ext)
  fix x y
  show "?lhs x y \<longleftrightarrow> ?rhs x y"
    unfolding majority_iff'
    by (subst majority_mset_iff'[where A = carrier])
       (use in_dom nonempty_dom
        in  \<open>auto simp del: in_dom simp: assms mset_set_empty_iff filter_mset_image_mset\<close>)
qed

end


context linorder_family
begin

lemma majority_iff_ge_half: 
  assumes "x \<in> carrier" "y \<in> carrier" "finite dom"
  shows   "majority R x y \<longleftrightarrow> 2 * card {i\<in>dom. R i x y} \<ge> card dom"
proof (cases "x = y")
  case [simp]: True
  have "{i\<in>dom. R i x y} = dom"
    using assms preorder_on.refl[OF in_dom] by auto
  with assms show ?thesis
    by (simp add: majority_iff)
next
  case False
  have "dom = {i \<in> dom. R i x y} \<union> {i \<in> dom. \<not>R i x y}"
    by auto
  also have "card \<dots> = card {i \<in> dom. R i x y} + card {i \<in> dom. \<not>R i x y}"
    by (rule card_Un_disjoint) (use \<open>finite dom\<close> in auto)
  also have "{i \<in> dom. \<not>R i x y} = {i \<in> dom. R i y x}"
  proof (rule set_eqI, unfold mem_Collect_eq, intro conj_cong refl)
    fix i assume i: "i \<in> dom"
    interpret Ri: linorder_on carrier "R i"
      using i by simp
    show "\<not>R i x y \<longleftrightarrow> R i y x"
      using Ri.total[of x y] Ri.antisymmetric[of x y] assms \<open>x \<noteq> y\<close> by blast
  qed
  finally show ?thesis
    using assms by (auto simp: majority_iff)
qed

lemma majority_iff_le_half: 
  assumes "x \<in> carrier" "y \<in> carrier" "x \<noteq> y" "finite dom"
  shows   "majority R x y \<longleftrightarrow> 2 * card {i\<in>dom. R i y x} \<le> card dom"
proof -
  have "dom = {i \<in> dom. R i x y} \<union> {i \<in> dom. \<not>R i x y}"
    by auto
  also have "card \<dots> = card {i \<in> dom. R i x y} + card {i \<in> dom. \<not>R i x y}"
    by (rule card_Un_disjoint) (use \<open>finite dom\<close> in auto)
  also have "{i \<in> dom. \<not>R i x y} = {i \<in> dom. R i y x}"
  proof (rule set_eqI, unfold mem_Collect_eq, intro conj_cong refl)
    fix i assume i: "i \<in> dom"
    interpret Ri: linorder_on carrier "R i"
      using i by simp
    show "\<not>R i x y \<longleftrightarrow> R i y x"
      using Ri.total[of x y] Ri.antisymmetric[of x y] assms \<open>x \<noteq> y\<close> by blast
  qed
  finally show ?thesis
    using assms by (auto simp: majority_iff)
qed

text \<open>
  For families of odd cardinality, the majority rule is always antisymmetric.
\<close>
lemma odd_imp_majority_antisymmetric:
  assumes "odd (card dom)" "majority R x y" "majority R y x"
  shows   "x = y"
proof (rule ccontr)
  assume "x \<noteq> y"
  have [simp]: "finite dom"
    using assms(1) card_ge_0_finite odd_pos by blast
  have xy: "x \<in> carrier" "y \<in> carrier" "card {i \<in> dom. R i y x} = card {i \<in> dom. R i x y}"
    using assms unfolding majority_iff' by auto
  have "dom = {i \<in> dom. R i x y} \<union> {i \<in> dom. \<not>R i x y}"
    by auto
  also have "card \<dots> = card {i \<in> dom. R i x y} + card {i \<in> dom. \<not>R i x y}"
    by (rule card_Un_disjoint) auto
  also have "{i \<in> dom. \<not>R i x y} = {i \<in> dom. R i y x}"
  proof (rule set_eqI, unfold mem_Collect_eq, intro conj_cong refl)
    fix i assume i: "i \<in> dom"
    interpret Ri: linorder_on carrier "R i"
      using i by simp
    show "\<not>R i x y \<longleftrightarrow> R i y x"
      using Ri.total[of x y] Ri.antisymmetric[of x y] xy(1,2) \<open>x \<noteq> y\<close> by blast
  qed
  also have "card \<dots> = card {i \<in> dom. R i x y}"
    using xy(3) by simp
  finally have "even (card dom)"
    by simp
  with \<open>odd (card dom)\<close> show False
    by simp
qed

end



subsection \<open>The lexicographic order on lists\<close>

fun lexprod_list_aux :: "'a relation \<Rightarrow> 'a list relation" where
  "lexprod_list_aux R [] ys \<longleftrightarrow> True"
| "lexprod_list_aux R (x # xs) [] \<longleftrightarrow> False"
| "lexprod_list_aux R (x # xs) (y # ys) \<longleftrightarrow> x \<preceq>[R] y \<and> (x \<prec>[R] y \<or> lexprod_list_aux R xs ys)"

lemma lexprod_list_aux_Nil_right_iff [simp]: "lexprod_list_aux R xs [] \<longleftrightarrow> xs = []"
  by (cases xs) auto

lemma lexprod_list_aux_refl: "(\<forall>x\<in>set xs. R x x) \<Longrightarrow> lexprod_list_aux R xs xs"
  by (induction xs) auto

definition lexprod_list :: "'a relation \<Rightarrow> 'a list relation" where
  "lexprod_list R = restrict_relation {xs. \<forall>x\<in>set xs. R x x} (lexprod_list_aux R)"

definition lexprod_length_list :: "nat \<Rightarrow> 'a relation \<Rightarrow> 'a list relation" where
  "lexprod_length_list n R = restrict_relation {xs. length xs = n} (lexprod_list R)"


context preorder_on
begin

lemma lexprod_list_aux_trans:
  assumes "lexprod_list_aux le xs ys" "lexprod_list_aux le ys zs"
  shows "lexprod_list_aux le xs zs"
  using assms
proof (induction xs arbitrary: ys zs)
  case (Cons x xs ys zs)
  obtain y ys' where [simp]: "ys = y # ys'"
    using Cons.prems by (cases ys) auto
  obtain z zs' where [simp]: "zs = z # zs'"
    using Cons.prems by (cases zs) auto
  show ?case
    using Cons.prems Cons.IH[of ys' zs'] trans by (auto simp: strongly_preferred_def)
qed auto

lemma preorder_lexprod_list: "preorder_on (lists carrier) (lexprod_list le)"
proof
  show "lexprod_list le xs xs" if "xs \<in> lists carrier" for xs
  proof -
    have "lexprod_list_aux le xs xs"
      using that by (induction xs) (auto intro: refl)
    thus ?thesis
      using that by (auto simp: lexprod_list_def restrict_relation_def refl)
  qed
next
  show "lexprod_list le xs zs" if "lexprod_list le xs ys" "lexprod_list le ys zs" for xs ys zs
    using lexprod_list_aux_trans[of xs ys zs] that
    by (auto simp: lexprod_list_def restrict_relation_def)
next
  show "xs \<in> lists carrier" "ys \<in> lists carrier"
    if "lexprod_list le xs ys" for xs ys
  proof -
    have "{xs, ys} \<subseteq> {xs. \<forall>x\<in>set xs. le x x}"
      using that by (auto simp: lexprod_list_def restrict_relation_def)
    also have "\<dots> \<subseteq> lists carrier"
      using not_outside by blast
    finally show "xs \<in> lists carrier" "ys \<in> lists carrier"
      by blast+
  qed
qed


lemma preorder_lexprod_length_list:
  "preorder_on {xs. set xs \<subseteq> carrier \<and> length xs = n} (lexprod_length_list n le)"
proof -
  interpret lex: preorder_on "lists carrier" "lexprod_list le"
    by (rule preorder_lexprod_list)
  have "preorder_on (lists carrier \<inter> {xs. length xs = n}) (lexprod_length_list n le)"
    unfolding lexprod_length_list_def by (rule lex.preorder_on_restrict)
  also have "lists carrier \<inter> {xs. length xs = n} = {xs. set xs \<subseteq> carrier \<and> length xs = n}"
    by auto
  finally show ?thesis .
qed

end



context total_preorder_on
begin

lemma total_preorder_lexprod_list: "total_preorder_on (lists carrier) (lexprod_list le)"
proof -
  interpret lex: preorder_on "lists carrier" "lexprod_list le"
    by (rule preorder_lexprod_list)
  show ?thesis
  proof
    show "lexprod_list le xs ys \<or> lexprod_list le ys xs" 
      if "xs \<in> lists carrier" "ys \<in> lists carrier" for xs ys
    proof -
      have "lexprod_list_aux le xs ys \<or> lexprod_list_aux le ys xs" using that total
        by (induction le xs ys rule: lexprod_list_aux.induct)
           (auto simp: strongly_preferred_def)
      thus ?thesis
        using that not_outside refl unfolding lexprod_list_def restrict_relation_def
        by blast
    qed
  qed
qed

lemma total_preorder_lexprod_length_list:
  "total_preorder_on {xs. set xs \<subseteq> carrier \<and> length xs = n} (lexprod_length_list n le)"
proof -
  interpret lex: total_preorder_on "lists carrier" "lexprod_list le"
    by (rule total_preorder_lexprod_list)
  have "total_preorder_on (lists carrier \<inter> {xs. length xs = n}) (lexprod_length_list n le)"
    unfolding lexprod_length_list_def by (rule lex.total_preorder_on_restrict)
  also have "lists carrier \<inter> {xs. length xs = n} = {xs. set xs \<subseteq> carrier \<and> length xs = n}"
    by auto
  finally show ?thesis .
qed

end


context order_on
begin

lemma order_lexprod_list: "order_on (lists carrier) (lexprod_list le)"
proof -
  interpret lex: preorder_on "lists carrier" "lexprod_list le"
    by (rule preorder_lexprod_list)
  show ?thesis
  proof
    show "xs = ys" if "lexprod_list le xs ys" "lexprod_list le ys xs"  for xs ys
    proof -
      have "lexprod_list_aux le xs ys" "lexprod_list_aux le ys xs"
           "set xs \<subseteq> carrier" "set ys \<subseteq> carrier"
        using that not_outside by (auto simp: lexprod_list_def restrict_relation_def)
      thus "xs = ys" using antisymmetric
        by (induction le xs ys rule: lexprod_list_aux.induct)
           (auto simp: strongly_preferred_def)
    qed
  qed
qed

lemma order_lexprod_length_list:
  "order_on {xs. set xs \<subseteq> carrier \<and> length xs = n} (lexprod_length_list n le)"
proof -
  interpret lex: order_on "lists carrier" "lexprod_list le"
    by (rule order_lexprod_list)
  have "order_on (lists carrier \<inter> {xs. length xs = n}) (lexprod_length_list n le)"
    unfolding lexprod_length_list_def by (rule lex.order_on_restrict)
  also have "lists carrier \<inter> {xs. length xs = n} = {xs. set xs \<subseteq> carrier \<and> length xs = n}"
    by auto
  finally show ?thesis .
qed

end



context linorder_on
begin

lemma order_lexprod_list: "linorder_on (lists carrier) (lexprod_list le)"
proof -
  interpret lex: order_on "lists carrier" "lexprod_list le"
    by (rule order_lexprod_list)
  interpret lex: total_preorder_on "lists carrier" "lexprod_list le"
    by (rule total_preorder_lexprod_list)
  show ?thesis ..
qed

lemma linorder_lexprod_length_list:
  "linorder_on {xs. set xs \<subseteq> carrier \<and> length xs = n} (lexprod_length_list n le)"
proof -
  interpret lex: linorder_on "lists carrier" "lexprod_list le"
    by (rule order_lexprod_list)
  have "linorder_on (lists carrier \<inter> {xs. length xs = n}) (lexprod_length_list n le)"
    unfolding lexprod_length_list_def by (rule lex.linorder_on_restrict)
  also have "lists carrier \<inter> {xs. length xs = n} = {xs. set xs \<subseteq> carrier \<and> length xs = n}"
    by auto
  finally show ?thesis .
qed

end



subsection \<open>Maximal and minimal elements\<close>

definition Min_wrt_among :: "'a relation \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "Min_wrt_among R A = {x\<in>A. R x x \<and> (\<forall>y\<in>A. R y x \<longrightarrow> R x y)}"

lemma Min_wrt_among_cong:
  assumes "restrict_relation A R = restrict_relation A R'"
  shows   "Min_wrt_among R A = Min_wrt_among R' A"
proof -
  from assms have "R x y \<longleftrightarrow> R' x y" if "x \<in> A" "y \<in> A" for x y
    using that by (auto simp: restrict_relation_def fun_eq_iff)
  thus ?thesis unfolding Min_wrt_among_def by blast
qed

definition Min_wrt :: "'a relation \<Rightarrow> 'a set" where
  "Min_wrt R = Min_wrt_among R UNIV"
  
lemma Min_wrt_altdef: "Min_wrt R = {x. R x x \<and> (\<forall>y. R y x \<longrightarrow> R x y)}"
  unfolding Min_wrt_def Min_wrt_among_def by simp

lemma Min_wrt_among_conv_Max_wrt_among: "Min_wrt_among R A = Max_wrt_among (\<lambda>x y. R y x) A"
  by (simp add: Min_wrt_among_def Max_wrt_among_def)


context preorder_on
begin

lemma Min_wrt_among_preorder:
  "Min_wrt_among le A = {x\<in>carrier \<inter> A. \<forall>y\<in>carrier \<inter> A. le y x \<longrightarrow> le x y}"
  unfolding Min_wrt_among_def using not_outside refl by blast

lemma Min_wrt_preorder:
  "Min_wrt le = {x\<in>carrier. \<forall>y\<in>carrier. le y x \<longrightarrow> le x y}"
  unfolding Min_wrt_altdef using not_outside refl by blast

lemma Min_wrt_among_subset:
  "Min_wrt_among le A \<subseteq> carrier" "Min_wrt_among le A \<subseteq> A"
  unfolding Min_wrt_among_preorder by auto
  
lemma Min_wrt_subset:
  "Min_wrt le \<subseteq> carrier"
  unfolding Min_wrt_preorder by auto

lemma Min_wrt_among_nonempty:
  assumes "B \<inter> carrier \<noteq> {}" "finite (B \<inter> carrier)"
  shows   "Min_wrt_among le B \<noteq> {}"
  by (simp add: Min_wrt_among_conv_Max_wrt_among assms(1,2) dual.Max_wrt_among_nonempty)
  
lemma Min_wrt_nonempty:
  "carrier \<noteq> {} \<Longrightarrow> finite carrier \<Longrightarrow> Min_wrt le \<noteq> {}"
  using Min_wrt_among_nonempty[of UNIV] by (simp add: Min_wrt_def)

lemma Min_wrt_among_map_relation_vimage:
  "f -` Min_wrt_among le A \<subseteq> Min_wrt_among (map_relation f le) (f -` A)"
  by (auto simp: Min_wrt_among_def map_relation_def)

lemma Min_wrt_map_relation_vimage:
  "f -` Min_wrt le \<subseteq> Min_wrt (map_relation f le)"
  by (auto simp: Min_wrt_altdef map_relation_def)

lemma Min_wrt_among_map_relation_bij_subset:
  assumes "bij (f :: 'a \<Rightarrow> 'b)"
  shows   "f ` Min_wrt_among le A \<subseteq> 
             Min_wrt_among (map_relation (inv f) le) (f ` A)"
  using assms Min_wrt_among_map_relation_vimage[of "inv f" A]
  by (simp add: bij_imp_bij_inv inv_inv_eq bij_vimage_eq_inv_image)
  
lemma Min_wrt_among_map_relation_bij:
  assumes "bij f"
  shows   "f ` Min_wrt_among le A = Min_wrt_among (map_relation (inv f) le) (f ` A)"
proof (intro equalityI Min_wrt_among_map_relation_bij_subset assms)
  interpret R: preorder_on "f ` carrier" "map_relation (inv f) le"
    using preorder_on_map[of "inv f"] assms 
      by (simp add: bij_imp_bij_inv bij_vimage_eq_inv_image inv_inv_eq)
  show "Min_wrt_among (map_relation (inv f) le) (f ` A) \<subseteq> f ` Min_wrt_among le A"
    unfolding Min_wrt_among_preorder R.Min_wrt_among_preorder 
    using assms bij_is_inj[OF assms]
    by (auto simp: map_relation_def inv_f_f image_Int [symmetric])
qed

lemma Min_wrt_map_relation_bij:
  "bij f \<Longrightarrow> f ` Min_wrt le = Min_wrt (map_relation (inv f) le)"
proof -
  assume bij: "bij f"
  interpret R: preorder_on "f ` carrier" "map_relation (inv f) le"
    using preorder_on_map[of "inv f"] bij
      by (simp add: bij_imp_bij_inv bij_vimage_eq_inv_image inv_inv_eq)
  from bij show ?thesis
    unfolding R.Min_wrt_preorder Min_wrt_preorder
    by (auto simp: map_relation_def inv_f_f bij_is_inj)
qed

lemma Min_wrt_among_mono:
  "le y x \<Longrightarrow> x \<in> Min_wrt_among le A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<in> Min_wrt_among le A"
  using not_outside by (auto simp: Min_wrt_among_preorder intro: trans)

lemma Min_wrt_mono:
  "le y x \<Longrightarrow> x \<in> Min_wrt le \<Longrightarrow> y \<in> Min_wrt le"
  unfolding Min_wrt_def using Min_wrt_among_mono[of y x UNIV] by blast

end


context total_preorder_on
begin

lemma Min_wrt_among_total_preorder:
  "Min_wrt_among le A = {x\<in>carrier \<inter> A. \<forall>y\<in>carrier \<inter> A. le x y}"
  unfolding Min_wrt_among_preorder using total by blast

lemma Min_wrt_total_preorder:
  "Min_wrt le = {x\<in>carrier. \<forall>y\<in>carrier. le x y}"
  unfolding Min_wrt_preorder using total by blast

lemma decompose_Min:
  assumes A: "A \<subseteq> carrier"
  defines "M \<equiv> Min_wrt_among le A"
  shows   "restrict_relation A le = (\<lambda>x y. x \<in> M \<and> y \<in> A \<or> (y \<notin> M \<and> restrict_relation (A - M) le x y))"
  using A by (intro ext) (auto simp: M_def Min_wrt_among_total_preorder 
                            restrict_relation_def Int_absorb1 intro: trans)
  
end



definition min_wrt_among :: "'a relation \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "min_wrt_among R A = the_elem (Min_wrt_among R A)"

definition min_wrt :: "'a relation \<Rightarrow> 'a" where
  "min_wrt R = min_wrt_among R UNIV"

definition max_wrt_among :: "'a relation \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "max_wrt_among R A = the_elem (Max_wrt_among R A)"

definition max_wrt :: "'a relation \<Rightarrow> 'a" where
  "max_wrt R = max_wrt_among R UNIV"


context finite_linorder_on
begin

lemma Max_wrt_among_singleton:
  assumes "A \<noteq> {}" "A \<subseteq> carrier"
  shows   "is_singleton (Max_wrt_among le A)"
proof -
  have "x = y" if "x \<in> Max_wrt_among le A" "y \<in> Max_wrt_among le A" for x y
    using antisymmetric[of x y] total[of x y] that assms
    unfolding Max_wrt_among_def by blast
  moreover have "Max_wrt_among le A \<noteq> {}"
    by (rule Max_wrt_among_nonempty) (use assms in auto)
  ultimately show ?thesis
    unfolding is_singleton_def by blast
qed

lemma max_wrt_among_inside:
  assumes "A \<noteq> {}" "A \<subseteq> carrier"
  shows   "max_wrt_among le A \<in> A"
proof -
  have "max_wrt_among le A \<in> Max_wrt_among le A"
    using Max_wrt_among_singleton[OF assms]
    unfolding is_singleton_def max_wrt_among_def by force
  also have "\<dots> \<subseteq> A"
    by (auto simp: Max_wrt_among_def)
  finally show ?thesis .
qed

lemma le_max_wrt_among:
  assumes "y \<in> A" "A \<subseteq> carrier"
  shows   "le y (max_wrt_among le A)"
proof -
  have "A \<noteq> {}"
    using assms by auto
  have "max_wrt_among le A \<in> Max_wrt_among le A"
    using Max_wrt_among_singleton[OF \<open>A \<noteq> {}\<close> assms(2)]
    unfolding is_singleton_def max_wrt_among_def by force
  thus ?thesis using \<open>y \<in> A\<close>
    by (metis assms(2) decompose_Max restrict_relation_def)
qed

end


context finite_linorder_on
begin

lemma Min_wrt_among_singleton:
  assumes "A \<noteq> {}" "A \<subseteq> carrier"
  shows   "is_singleton (Min_wrt_among le A)"
  using assms by (metis Min_wrt_among_conv_Max_wrt_among dual.Max_wrt_among_singleton)

lemma min_wrt_among_inside:
  assumes "A \<noteq> {}" "A \<subseteq> carrier"
  shows   "min_wrt_among le A \<in> A"
  using dual.max_wrt_among_inside[OF assms]
  by (simp add: max_wrt_among_def min_wrt_among_def Min_wrt_among_conv_Max_wrt_among)

lemma le_min_wrt_among:
  assumes "y \<in> A" "A \<subseteq> carrier"
  shows   "le (min_wrt_among le A) y"
  using dual.le_max_wrt_among[OF assms]
  by (simp add: max_wrt_among_def min_wrt_among_def Min_wrt_among_conv_Max_wrt_among)

end

end