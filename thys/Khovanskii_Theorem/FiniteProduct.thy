section \<open>Product Operator for Commutative Monoids\<close>

(*
  Finite products in group theory. This theory is largely based on HOL/Algebra/FiniteProduct.thy. 
  --L C Paulson
*)

theory FiniteProduct
  imports 
    "Jacobson_Basic_Algebra.Group_Theory"

begin

subsection \<open>Products over Finite Sets\<close>

context commutative_monoid begin

definition "M_ify x \<equiv> if x \<in> M then x else \<one>"

definition "fincomp f A \<equiv> if finite A then Finite_Set.fold (\<lambda>x y. f x \<cdot> M_ify y) \<one> A else \<one>"

lemma fincomp_empty [simp]: "fincomp f {} = \<one>"
  by (simp add: fincomp_def)

lemma fincomp_infinite[simp]: "infinite A \<Longrightarrow> fincomp f A = \<one>"
  by (simp add: fincomp_def)

lemma left_commute: "\<lbrakk> a \<in> M; b \<in> M; c \<in> M \<rbrakk> \<Longrightarrow> b \<cdot> (a \<cdot> c) = a \<cdot> (b \<cdot> c)"
  using commutative by force


lemma comp_fun_commute_onI:
  assumes "f \<in> F \<rightarrow> M"
  shows "comp_fun_commute_on F (\<lambda>x y. f x \<cdot> M_ify y)"
  using assms
  by (auto simp add: comp_fun_commute_on_def Pi_iff M_ify_def left_commute)

lemma fincomp_closed [simp]:
  assumes "f \<in> F \<rightarrow> M" 
  shows "fincomp f F \<in> M"
proof -
  interpret comp_fun_commute_on F "\<lambda>x y. f x \<cdot> M_ify y"
    by (simp add: assms comp_fun_commute_onI)
  show ?thesis
    unfolding fincomp_def
    by (smt (verit, ccfv_threshold) M_ify_def Pi_iff fold_graph_fold assms composition_closed equalityE fold_graph_closed_lemma unit_closed)
qed

lemma fincomp_insert [simp]:
  assumes F: "finite F" "a \<notin> F" and f: "f \<in> F \<rightarrow> M" "f a \<in> M"
  shows "fincomp f (insert a F) = f a \<cdot> fincomp f F"
proof -
  interpret comp_fun_commute_on "insert a F" "\<lambda>x y. f x \<cdot> M_ify y"
    by (simp add: comp_fun_commute_onI f)
  show ?thesis
    using assms fincomp_closed commutative_monoid.M_ify_def commutative_monoid_axioms
    by (fastforce simp add: fincomp_def)
qed

lemma fincomp_unit_eqI: "(\<And>x. x \<in> A \<Longrightarrow> f x = \<one>) \<Longrightarrow> fincomp f A = \<one>"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  have "(\<lambda>i. \<one>) \<in> A \<rightarrow> M" by auto
  with insert show ?case by simp
qed simp

lemma fincomp_unit [simp]: "fincomp (\<lambda>i. \<one>) A = \<one>"
  by (simp add: fincomp_unit_eqI)

lemma funcset_Int_left [simp, intro]:
  "\<lbrakk>f \<in> A \<rightarrow> C; f \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> f \<in> A Int B \<rightarrow> C"
  by fast

lemma funcset_Un_left [iff]:
  "(f \<in> A Un B \<rightarrow> C) = (f \<in> A \<rightarrow> C \<and> f \<in> B \<rightarrow> C)"
  by fast

lemma fincomp_Un_Int:
  "\<lbrakk>finite A; finite B; g \<in> A \<rightarrow> M; g \<in> B \<rightarrow> M\<rbrakk> \<Longrightarrow>
     fincomp g (A \<union> B) \<cdot> fincomp g (A \<inter> B) =
     fincomp g A \<cdot> fincomp g B"
  \<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert a A)
  then have "g a \<in> M" "g \<in> A \<rightarrow> M" by blast+
  with insert show ?case
    by (simp add: Int_insert_left associative insert_absorb left_commute)
qed

lemma fincomp_Un_disjoint:
  "\<lbrakk>finite A; finite B; A \<inter> B = {}; g \<in> A \<rightarrow> M; g \<in> B \<rightarrow> M\<rbrakk>
   \<Longrightarrow> fincomp g (A \<union> B) = fincomp g A \<cdot> fincomp g B"
  by (metis Pi_split_domain fincomp_Un_Int fincomp_closed fincomp_empty right_unit)

lemma fincomp_comp:
  "\<lbrakk>f \<in> A \<rightarrow> M; g \<in> A \<rightarrow> M\<rbrakk> \<Longrightarrow> fincomp (\<lambda>x. f x \<cdot> g x) A = (fincomp f A \<cdot> fincomp g A)"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A) 
  then have "f a \<in> M" "g \<in> A \<rightarrow> M" "g a \<in> M" "f \<in> A \<rightarrow> M" "(\<lambda>x. f x \<cdot> g x) \<in> A \<rightarrow> M"
    by blast+
  then show ?case
    by (simp add: insert associative left_commute)
qed simp

lemma fincomp_cong':
  assumes "A = B" "g \<in> B \<rightarrow> M" "\<And>i. i \<in> B \<Longrightarrow> f i = g i"
  shows "fincomp f A = fincomp g B"
proof (cases "finite B")
  case True
  then have ?thesis
    using assms
  proof (induct arbitrary: A)
    case empty thus ?case by simp
  next
    case (insert x B)
    then have "fincomp f A = fincomp f (insert x B)" by simp
    also from insert have "... = f x \<cdot> fincomp f B"
      by (simp add: Pi_iff)
    also from insert have "... = g x \<cdot> fincomp g B" by fastforce
    also from insert have "... = fincomp g (insert x B)"
      by (intro fincomp_insert [THEN sym]) auto
    finally show ?case .
  qed
  with assms show ?thesis by simp
next
  case False with assms show ?thesis by simp
qed

lemma fincomp_cong:
  assumes "A = B" "g \<in> B \<rightarrow> M" "\<And>i. i \<in> B =simp=> f i = g i"
  shows "fincomp f A = fincomp g B"
  using assms unfolding simp_implies_def by (blast intro: fincomp_cong')

text \<open>Usually, if this rule causes a failed congruence proof error,
  the reason is that the premise \<open>g \<in> B \<rightarrow> M\<close> cannot be shown.
  Adding @{thm [source] Pi_def} to the simpset is often useful.
  For this reason, @{thm [source] fincomp_cong}
  is not added to the simpset by default.
\<close>

lemma fincomp_0 [simp]:
  "f \<in> {0::nat} \<rightarrow> M \<Longrightarrow> fincomp f {..0} = f 0"
  by (simp add: Pi_def)

lemma fincomp_0': "f \<in> {..n} \<rightarrow> M \<Longrightarrow> (f 0) \<cdot> fincomp f {Suc 0..n} = fincomp f {..n}"
  by (metis Pi_split_insert_domain Suc_n_not_le_n atLeastAtMost_iff atLeastAtMost_insertL atMost_atLeast0 finite_atLeastAtMost fincomp_insert le0)

lemma fincomp_Suc [simp]:
  "f \<in> {..Suc n} \<rightarrow> M \<Longrightarrow> fincomp f {..Suc n} = (f (Suc n) \<cdot> fincomp f {..n})"
  by (simp add: Pi_def atMost_Suc)

lemma fincomp_Suc2:
  "f \<in> {..Suc n} \<rightarrow> M \<Longrightarrow> fincomp f {..Suc n} = (fincomp (%i. f (Suc i)) {..n} \<cdot> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case 
    by (simp add: associative Pi_def)
qed

lemma fincomp_Suc3:
  assumes "f \<in> {..n :: nat} \<rightarrow> M"
  shows "fincomp f {.. n} = (f n) \<cdot> fincomp f {..< n}"
proof (cases "n = 0")
  case True thus ?thesis
    using assms atMost_Suc by simp
next
  case False
  then obtain k where "n = Suc k"
    using not0_implies_Suc by blast
  thus ?thesis
    using fincomp_Suc[of f k] assms atMost_Suc lessThan_Suc_atMost by simp
qed

lemma fincomp_reindex: \<^marker>\<open>contributor \<open>Jeremy Avigad\<close>\<close>
  "f \<in> (h ` A) \<rightarrow> M \<Longrightarrow>
        inj_on h A \<Longrightarrow> fincomp f (h ` A) = fincomp (\<lambda>x. f (h x)) A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  hence "\<not> finite (h ` A)"
    using finite_imageD by blast
  with \<open>\<not> finite A\<close> show ?case by simp
qed (auto simp add: Pi_def)

lemma fincomp_const: \<^marker>\<open>contributor \<open>Jeremy Avigad\<close>\<close>
  assumes a [simp]: "a \<in> M"
  shows "fincomp (\<lambda>x. a) A = rec_nat \<one> (\<lambda>u. (\<cdot>) a) (card A)"
  by (induct A rule: infinite_finite_induct) auto

lemma fincomp_singleton: \<^marker>\<open>contributor \<open>Jesus Aransay\<close>\<close>
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> M"
  shows "fincomp (\<lambda>j. if i = j then f j else \<one>) A = f i"
  using i_in_A fincomp_insert [of "A - {i}" i "(\<lambda>j. if i = j then f j else \<one>)"]
    fin_A f_Pi fincomp_unit [of "A - {i}"]
    fincomp_cong [of "A - {i}" "A - {i}" "(\<lambda>j. if i = j then f j else \<one>)" "(\<lambda>i. \<one>)"]
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

lemma fincomp_singleton_swap:
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> M"
  shows "fincomp (\<lambda>j. if j = i then f j else \<one>) A = f i"
  using fincomp_singleton [OF assms] by (simp add: eq_commute)

lemma fincomp_mono_neutral_cong_left:
  assumes "finite B"
    and "A \<subseteq> B"
    and 1: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>"
    and gh: "\<And>x. x \<in> A \<Longrightarrow> g x = h x"
    and h: "h \<in> B \<rightarrow> M"
  shows "fincomp g A = fincomp h B"
proof-
  have eq: "A \<union> (B - A) = B" using \<open>A \<subseteq> B\<close> by blast
  have d: "A \<inter> (B - A) = {}" using \<open>A \<subseteq> B\<close> by blast
  from \<open>finite B\<close> \<open>A \<subseteq> B\<close> have f: "finite A" "finite (B - A)"
    by (auto intro: finite_subset)
  have "h \<in> A \<rightarrow> M" "h \<in> B - A \<rightarrow> M"
    using assms by (auto simp: image_subset_iff_funcset)
  moreover have "fincomp g A = fincomp h A \<cdot> fincomp h (B - A)"
  proof -
    have "fincomp h (B - A) = \<one>"
      using "1" fincomp_unit_eqI by blast
    moreover have "fincomp g A = fincomp h A"
      using \<open>h \<in> A \<rightarrow> M\<close> fincomp_cong' gh by blast
    ultimately show ?thesis
      by (simp add: \<open>h \<in> A \<rightarrow> M\<close>)
  qed
  ultimately show ?thesis
    by (simp add: fincomp_Un_disjoint [OF f d, unfolded eq])
qed

lemma fincomp_mono_neutral_cong_right:
  assumes "finite B"
    and "A \<subseteq> B" "\<And>i. i \<in> B - A \<Longrightarrow> g i = \<one>" "\<And>x. x \<in> A \<Longrightarrow> g x = h x" "g \<in> B \<rightarrow> M"
  shows "fincomp g B = fincomp h A"
  using assms  by (auto intro!: fincomp_mono_neutral_cong_left [symmetric])

lemma fincomp_mono_neutral_cong:
  assumes [simp]: "finite B" "finite A"
    and *: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>" "\<And>i. i \<in> A - B \<Longrightarrow> g i = \<one>"
    and gh: "\<And>x. x \<in> A \<inter> B \<Longrightarrow> g x = h x"
    and g: "g \<in> A \<rightarrow> M"
    and h: "h \<in> B \<rightarrow> M"
  shows "fincomp g A = fincomp h B"
proof-
  have "fincomp g A = fincomp g (A \<inter> B)"
    by (rule fincomp_mono_neutral_cong_right) (use assms in auto)
  also have "\<dots> = fincomp h (A \<inter> B)"
    by (rule fincomp_cong) (use assms in auto)
  also have "\<dots> = fincomp h B"
    by (rule fincomp_mono_neutral_cong_left) (use assms in auto)
  finally show ?thesis .
qed


lemma fincomp_UN_disjoint:
  assumes
    "finite I" "\<And>i. i \<in> I \<Longrightarrow> finite (A i)" "pairwise (\<lambda>i j. disjnt (A i) (A j)) I"
    "\<And>i x. i \<in> I \<Longrightarrow> x \<in> A i \<Longrightarrow> g x \<in> M"
  shows "fincomp g (\<Union>(A ` I)) = fincomp (\<lambda>i. fincomp g (A i)) I"
  using assms
proof (induction set: finite)
  case empty
  then show ?case
    by force
next
  case (insert i I)
  then show ?case
    unfolding pairwise_def disjnt_def
    apply clarsimp
    apply (subst fincomp_Un_disjoint)
         apply (fastforce intro!: funcsetI fincomp_closed)+
    done
qed

lemma fincomp_Union_disjoint:
  "\<lbrakk>finite C; \<And>A. A \<in> C \<Longrightarrow> finite A \<and> (\<forall>x\<in>A. f x \<in> M); pairwise disjnt C\<rbrakk> \<Longrightarrow>
    fincomp f (\<Union>C) = fincomp (fincomp f) C"
  by (frule fincomp_UN_disjoint [of C id f]) auto

end

subsection \<open>Results for Abelian Groups\<close>

context abelian_group begin

lemma fincomp_inverse:
  "f \<in> A \<rightarrow> G \<Longrightarrow> fincomp (\<lambda>x. inverse (f x)) A = inverse (fincomp f A)"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A) 
  then have "f a \<in> G" "f \<in> A \<rightarrow> G" "(\<lambda>x. inverse (f x)) \<in> A \<rightarrow> G"
    by blast+
  with insert show ?case
    by (simp add: commutative inverse_composition_commute)
qed simp

text \<open> Jeremy Avigad. This should be generalized to arbitrary groups, not just Abelian
   ones, using Lagrange's theorem.\<close>
lemma power_order_eq_one:
  assumes fin [simp]: "finite G"
    and a [simp]: "a \<in> G"
  shows "rec_nat \<one> (\<lambda>u. (\<cdot>) a) (card G) = \<one>"
proof -
  have rec_G: "rec_nat \<one> (\<lambda>u. (\<cdot>) a) (card G) \<in> G"
    by (metis Pi_I' a fincomp_closed fincomp_const)
  have "\<And>x. x \<in> G \<Longrightarrow> x \<in> (\<cdot>) a ` G"
    by (metis a composition_closed imageI invertible invertible_inverse_closed invertible_right_inverse2)
  with a have "(\<cdot>) a ` G = G" by blast
  then have "\<one> \<cdot> fincomp (\<lambda>x. x) G = fincomp (\<lambda>x. x) ((\<cdot>) a ` G)"
    by simp
  also have "\<dots> = fincomp (\<lambda>x. a \<cdot> x) G"
    using fincomp_reindex
    by (subst (2) fincomp_reindex [symmetric]) (auto simp: inj_on_def)
  also have "\<dots> = fincomp (\<lambda>x. a) G \<cdot> fincomp (\<lambda>x. x) G"
    by (simp add: fincomp_comp)
  also have "fincomp (\<lambda>x. a) G = rec_nat \<one> (\<lambda>u. (\<cdot>) a) (card G)"
    by (simp add: fincomp_const)
  finally show ?thesis
    by (metis commutative fincomp_closed funcset_id invertible invertible_left_cancel rec_G unit_closed)
qed

end

end
