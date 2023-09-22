section \<open>Inclusion-exclusion principle\<close>

text \<open>Inclusion-exclusion principle, the usual and generalized forms.\<close>

theory Inclusion_Exclusion
  imports Main
begin

lemma subset_insert_lemma:
  "{T. T \<subseteq> (insert a S) \<and> P T} = {T. T \<subseteq> S \<and> P T} \<union> {insert a T |T. T \<subseteq> S \<and> P(insert a T)}" (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
    by (smt (verit) UnI1 UnI2 insert_Diff mem_Collect_eq subsetI subset_insert_iff)
qed blast

locale Incl_Excl =
  fixes P :: "'a set \<Rightarrow> bool" and f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes disj_add: "\<lbrakk>P S; P T; disjnt S T\<rbrakk> \<Longrightarrow> f(S \<union> T) = f S + f T"
    and empty: "P{}"
    and Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)"
    and Un: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<union> T)"
    and Diff: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S - T)"

begin

lemma f_empty [simp]: "f{} = 0"
  using disj_add empty by fastforce

lemma f_Un_Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> f(S \<union> T) + f(S \<inter> T) = f S + f T"
  by (smt (verit, ccfv_threshold) Groups.add_ac(2) Incl_Excl.Diff Incl_Excl.Int Incl_Excl_axioms Int_Diff_Un Int_Diff_disjoint Int_absorb Un_Diff Un_Int_eq(2) disj_add disjnt_def group_cancel.add2 sup_bot.right_neutral)

lemma restricted_indexed:
  assumes "finite A" and X: "\<And>a. a \<in> A \<Longrightarrow> P(X a)"
  shows "f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
proof -
  have "\<lbrakk>finite A; card A = n; \<forall>a \<in> A. P (X a)\<rbrakk>
              \<Longrightarrow> f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))" for n X and A :: "'c set"
  proof (induction n arbitrary: A X rule: less_induct)
    case (less n0 A0 X)
    show ?case
    proof (cases "n0=0")
      case True
      with less show ?thesis
       by fastforce
    next
      case False
      with less.prems obtain A n a where *: "n0 = Suc n" "A0 = insert a A" "a \<notin> A" "card A = n" "finite A"
        by (metis card_Suc_eq_finite not0_implies_Suc)
      with less have "P (X a)" by blast
      have APX: "\<forall>a \<in> A. P (X a)"
        by (simp add: "*" less.prems)
      have PUXA: "P (\<Union> (X ` A))"
        using \<open>finite A\<close> APX
        by (induction) (auto simp: empty Un)
      have "f (\<Union> (X ` A0)) = f (X a \<union> \<Union> (X ` A))"
        by (simp add: *)
      also have "... = f (X a) + f (\<Union> (X ` A)) - f (X a \<inter> \<Union> (X ` A))"
        using f_Un_Int add_diff_cancel PUXA \<open>P (X a)\<close> by metis
      also have "... = f (X a) - (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (\<Inter> (X ` B))) +
                       (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
      proof -
        have 1: "f (\<Union>i\<in>A. X a \<inter> X i) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter>b\<in>B. X a \<inter> X b))"
          using less.IH [of n A "\<lambda>i. X a \<inter> X i"] APX Int \<open>P (X a)\<close>  by (simp add: *)
        have 2: "X a \<inter> \<Union> (X ` A) = (\<Union>i\<in>A. X a \<inter> X i)"
          by auto
        have 3: "f (\<Union> (X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
          using less.IH [of n A X] APX Int \<open>P (X a)\<close>  by (simp add: *)
        show ?thesis
          unfolding 3 2 1
          by (simp add: sum_negf)
      qed
      also have "... = (\<Sum>B | B \<subseteq> A0 \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
      proof -
         have F: "{insert a B |B. B \<subseteq> A} = insert a ` Pow A \<and> {B. B \<subseteq> A \<and> B \<noteq> {}} = Pow A - {{}}"
          by auto
        have G: "(\<Sum>B\<in>Pow A. (- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B))) = (\<Sum>B\<in>Pow A. - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B))))"
        proof (rule sum.cong [OF refl])
          fix B
          assume B: "B \<in> Pow A"
          then have "finite B"
            using \<open>finite A\<close> finite_subset by auto
          show "(- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B)) = - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
            using B * by (auto simp add: card_insert_if \<open>finite B\<close>)
        qed
        have disj: "{B. B \<subseteq> A \<and> B \<noteq> {}} \<inter> {insert a B |B. B \<subseteq> A} = {}"
          using * by blast
        have inj: "inj_on (insert a) (Pow A)"
          using "*" inj_on_def by fastforce
        show ?thesis
          apply (simp add: * subset_insert_lemma sum.union_disjoint disj sum_negf)
          apply (simp add: F G sum_negf sum.reindex [OF inj] o_def sum_diff *)
          done
      qed
      finally show ?thesis .
    qed   
  qed
  then show ?thesis
    by (meson assms)
qed

lemma restricted:
  assumes "finite A" "\<And>a. a \<in> A \<Longrightarrow> P a"
  shows  "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using restricted_indexed [of A "\<lambda>x. x"] assms by auto

end

subsection\<open>Versions for unrestrictedly additive functions\<close>

lemma Incl_Excl_UN:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union>(G ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (-1) ^ (card B + 1) * f (\<Inter> (G ` B)))"
proof -
  interpret Incl_Excl "\<lambda>x. True" f
    by (simp add: Incl_Excl.intro assms(1))
  show ?thesis
    using restricted_indexed assms by blast
qed

lemma Incl_Excl_Union:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using Incl_Excl_UN[of f A "\<lambda>X. X"] assms by simp

text \<open>The famous inclusion-exclusion formula for the cardinality of a union\<close>
lemma int_card_UNION:
  assumes "finite A" "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "int (card (\<Union>A)) = (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
proof -
  interpret Incl_Excl finite "int o card"
  proof qed (auto simp add: card_Un_disjnt)
  show ?thesis
    using restricted assms by auto
qed

text\<open>A more conventional form\<close>
lemma inclusion_exclusion:
  assumes "finite A" "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "int(card(\<Union> A)) =
         (\<Sum>n=1..card A. (-1) ^ (Suc n) * (\<Sum>B | B \<subseteq> A \<and> card B = n. int (card (\<Inter> B))))" (is "_=?R")
proof -
  have fin: "finite {I. I \<subseteq> A \<and> I \<noteq> {}}"
    by (simp add: assms)
  have "\<And>k. \<lbrakk>Suc 0 \<le> k; k \<le> card A\<rbrakk> \<Longrightarrow> \<exists>B\<subseteq>A. B \<noteq> {} \<and> k = card B"
    by (metis (mono_tags, lifting) Suc_le_D Zero_neq_Suc card_eq_0_iff obtain_subset_with_card_n)
  with \<open>finite A\<close> finite_subset
  have card_eq: "card ` {I. I \<subseteq> A \<and> I \<noteq> {}} = {1..card A}"
    using not_less_eq_eq card_mono by (fastforce simp: image_iff)
  have "int(card(\<Union> A)) 
      = (\<Sum>y = 1..card A. \<Sum>I\<in>{x. x \<subseteq> A \<and> x \<noteq> {} \<and> card x = y}. - ((- 1) ^ y * int (card (\<Inter> I))))"
    by (simp add: int_card_UNION assms sum.image_gen [OF fin, where g=card] card_eq)
  also have "... = ?R"
  proof -
    have "{B. B \<subseteq> A \<and> B \<noteq> {} \<and> card B = k} = {B. B \<subseteq> A \<and> card B = k}"
      if "Suc 0 \<le> k" and "k \<le> card A" for k
      using that by auto
    then show ?thesis
      by (clarsimp simp add: sum_negf simp flip: sum_distrib_left)
  qed
  finally show ?thesis .
qed

lemma card_UNION:
  assumes "finite A" and "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "card (\<Union>A) = nat (\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I)))"
  by (simp only: flip: int_card_UNION [OF assms])

lemma card_UNION_nonneg:
  assumes "finite A" and "\<And>K. K \<in> A \<Longrightarrow> finite K"
  shows "(\<Sum>I | I \<subseteq> A \<and> I \<noteq> {}. (- 1) ^ (card I + 1) * int (card (\<Inter>I))) \<ge> 0"
  using int_card_UNION [OF assms] by presburger

subsection \<open>a general "Moebius inversion" inclusion-exclusion principle. 
This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" \<close>

lemma sum_Un_eq:
   "\<lbrakk>S \<inter> T = {}; S \<union> T = U; finite U\<rbrakk>
           \<Longrightarrow> (sum f S + sum f T = sum f U)"
  by (metis finite_Un sum.union_disjoint)

lemma card_adjust_lemma: "\<lbrakk>inj_on f S; x = y + card (f ` S)\<rbrakk> \<Longrightarrow> x = y + card S"
  by (simp add: card_image)

lemma card_subsets_step:
  assumes "finite S" "x \<notin> S" "U \<subseteq> S"
  shows "card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> odd(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)} + card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} \<and>
         card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> even(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} + card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)}"
proof -
  have inj: "inj_on (insert x) {T. T \<subseteq> S \<and> P T}" for P
    using assms by (auto simp: inj_on_def)
  have [simp]: "finite {T. T \<subseteq> S \<and> P T}"  "finite (insert x ` {T. T \<subseteq> S \<and> P T})" for P
    using \<open>finite S\<close> by auto
  have [simp]: "disjnt {T. T \<subseteq> S \<and> P T} (insert x ` {T. T \<subseteq> S \<and> Q T})" for P Q
    using assms by (auto simp: disjnt_iff)
  have eq: "{T. T \<subseteq> S \<and> U \<subseteq> T \<and> P T} \<union> insert x ` {T. T \<subseteq> S \<and> U \<subseteq> T \<and> Q T}
          = {T. T \<subseteq> insert x S \<and> U \<subseteq> T \<and> P T}"  (is "?L = ?R")
    if "\<And>A. A \<subseteq> S \<Longrightarrow> Q (insert x A) \<longleftrightarrow> P A" "\<And>A. \<not> Q A \<longleftrightarrow> P A" for P Q
  proof
    show "?L \<subseteq> ?R"
      by (clarsimp simp: image_iff subset_iff) (meson subsetI that)
    show "?R \<subseteq> ?L"
      using \<open>U \<subseteq> S\<close>
      by (clarsimp simp: image_iff) (smt (verit) insert_iff mk_disjoint_insert subset_iff that)
  qed
  have [simp]: "\<And>A. A \<subseteq> S \<Longrightarrow> even (card (insert x A)) \<longleftrightarrow> odd (card A)"
    by (metis \<open>finite S\<close> \<open>x \<notin> S\<close> card_insert_disjoint even_Suc finite_subset subsetD)
  show ?thesis
    by (intro conjI card_adjust_lemma [OF inj]; simp add: eq flip: card_Un_disjnt)
qed

lemma card_subsupersets_even_odd:
  assumes "finite S" "U \<subset> S"
  shows "card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} 
       = card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)}"
  using assms
proof (induction "card S" arbitrary: S rule: less_induct)
  case (less S)
  then obtain x where "x \<notin> U" "x \<in> S"
    by blast
  then have U: "U \<subseteq> S - {x}"
    using less.prems(2) by blast
  let ?V = "S - {x}"
  show ?case
    using card_subsets_step [of ?V x U] less.prems U
    by (simp add: insert_absorb \<open>x \<in> S\<close>)
qed

lemma sum_alternating_cancels:
  assumes "finite S" "card {x. x \<in> S \<and> even(f x)} = card {x. x \<in> S \<and> odd(f x)}"
  shows "(\<Sum>x\<in>S. (-1) ^ f x) = (0::'b::ring_1)"
proof -
  have "(\<Sum>x\<in>S. (-1) ^ f x)
      = (\<Sum>x | x \<in> S \<and> even (f x). (-1) ^ f x) + (\<Sum>x | x \<in> S \<and> odd (f x). (-1) ^ f x)"
    by (rule sum_Un_eq [symmetric]; force simp: \<open>finite S\<close>)
  also have "... = (0::'b::ring_1)"
    by (simp add: minus_one_power_iff assms cong: conj_cong)
  finally show ?thesis .
qed

lemma inclusion_exclusion_symmetric:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes \<section>: "\<And>S. finite S \<Longrightarrow> g S = (\<Sum>T \<in> Pow S. (-1) ^ card T * f T)"
    and "finite S"
  shows "f S = (\<Sum>T \<in> Pow S. (-1) ^ card T * g T)"
proof -
  have "(-1) ^ card T * g T = (-1) ^ card T * (\<Sum>U | U \<subseteq> S \<and> U \<subseteq> T. (-1) ^ card U * f U)" 
    if "T \<subseteq> S" for T
  proof -
    have [simp]: "{U. U \<subseteq> S \<and> U \<subseteq> T} = Pow T"
      using that by auto
    show ?thesis
      using that by (simp add: \<open>finite S\<close> finite_subset \<section>)
  qed
  then have "(\<Sum>T \<in> Pow S. (-1) ^ card T * g T)
      = (\<Sum>T\<in>Pow S. (-1) ^ card T * (\<Sum>U | U \<in> {U. U \<subseteq> S} \<and> U \<subseteq> T. (-1) ^ card U * f U))"
    by simp
  also have "... = (\<Sum>U\<in>Pow S. (\<Sum>T | T \<subseteq> S \<and> U \<subseteq> T. (-1) ^ card T) * (-1) ^ card U * f U)"
    unfolding sum_distrib_left
    by (subst sum.swap_restrict; simp add: \<open>finite S\<close> algebra_simps sum_distrib_right Pow_def)
  also have "... = (\<Sum>U\<in>Pow S. if U=S then f S else 0)"
  proof -
    have [simp]: "{T. T \<subseteq> S \<and> S \<subseteq> T} = {S}"
      by auto
    show ?thesis
      apply (rule sum.cong [OF refl])
      by (simp add: sum_alternating_cancels card_subsupersets_even_odd \<open>finite S\<close> flip: power_add)
  qed
  also have "... = f S"
    by (simp add: \<open>finite S\<close>)
  finally show ?thesis
    by presburger
qed

text\<open> The more typical non-symmetric version.                                   \<close>
lemma inclusion_exclusion_mobius:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes \<section>: "\<And>S. finite S \<Longrightarrow> g S = sum f (Pow S)" and "finite S"
  shows "f S = (\<Sum>T \<in> Pow S. (-1) ^ (card S - card T) * g T)" (is "_ = ?rhs")
proof -
  have "(- 1) ^ card S * f S = (\<Sum>T\<in>Pow S. (- 1) ^ card T * g T)"
    by (rule inclusion_exclusion_symmetric; simp add: assms flip: power_add mult.assoc)
  then have "((- 1) ^ card S * (- 1) ^ card S) * f S = ((- 1) ^ card S) * (\<Sum>T\<in>Pow S. (- 1) ^ card T * g T)"
    by (simp add: mult_ac)
  then have "f S = (\<Sum>T\<in>Pow S. (- 1) ^ (card S + card T) * g T)"
    by (simp add: sum_distrib_left flip: power_add mult.assoc)
  also have "... = ?rhs"
    by (simp add: \<open>finite S\<close> card_mono neg_one_power_add_eq_neg_one_power_diff)
  finally show ?thesis .
qed

end