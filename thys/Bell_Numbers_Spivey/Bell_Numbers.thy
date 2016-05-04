(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section {* Bell Numbers and Spivey's Generalized Recurrence *}

theory Bell_Numbers
imports
  Binomial
  "~~/src/HOL/Eisbach/Eisbach"
  "~~/src/HOL/Library/FuncSet"
  "~~/src/HOL/Library/Monad_Syntax"
  "../Discrete_Summation/Stirling"
  "../Card_Number_Partitions/Additions_to_Main"
  "Set_Partition"
begin

subsection {* Preliminaries *}

subsubsection {* Additions to FuncSet *}

(* this is clearly to be added to FuncSet *)
lemma extensional_funcset_ext:
  assumes "f \<in> A \<rightarrow>\<^sub>E B" "g \<in> A \<rightarrow>\<^sub>E B"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "f = g"
using assms by (metis PiE_iff extensionalityI)

subsubsection {* Additions for Injectivity Proofs *}

lemma inj_on_impl_inj_on_image:
  assumes "inj_on f A"
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<subseteq> A"
  shows "inj_on (op ` f) X"
using assms by (meson inj_onI inj_on_image_eq_iff)

lemma injectivity_union:
  assumes "A \<union> B = C \<union> D"
  assumes "P A" "P C"
  assumes "Q B" "Q D"
    "\<And>S T. P S \<Longrightarrow> Q T \<Longrightarrow> S \<inter> T = {}"
  shows "A = C \<and> B = D"
using assms Int_Un_distrib Int_commute inf_sup_absorb by blast+

lemma injectivity_image:
  assumes "f ` A = g ` A"
  assumes "\<forall>x\<in>A. invert (f x) = x \<and> invert (g x) = x"
  shows "\<forall>x\<in>A. f x = g x"
using assms by (metis (no_types, lifting) image_iff)

lemma injectivity_image_union:
  assumes "(\<lambda>X. X \<union> F X) ` P = (\<lambda>X. X \<union> G X) ` P'"
  assumes "\<forall>X \<in> P. X \<subseteq> A" "\<forall>X \<in> P'. X \<subseteq> A"
  assumes "\<forall>X \<in> P. \<forall>y\<in>F X. y \<notin> A" "\<forall>X \<in> P'. \<forall>y\<in>G X. y \<notin> A"
  shows "P = P'"
proof
  show "P \<subseteq> P'"
  proof
    fix X
    assume "X \<in> P"
    from assms(1) this obtain X' where "X' \<in> P'" and "X \<union> F X = X' \<union> G X'"
      by (metis imageE image_eqI)
    moreover from assms(2,4) \<open>X \<in> P\<close> have X: "(X \<union> F X) \<inter> A = X" by auto
    moreover from assms(3,5) \<open>X' \<in> P'\<close> have X': "(X' \<union> G X') \<inter> A = X'" by auto
    ultimately have "X = X'" by simp
    from this \<open>X' \<in> P'\<close> show "X \<in> P'" by auto
  qed
next
  show "P' \<subseteq> P"
  proof
    fix X'
    assume "X' \<in> P'"
    from assms(1) this obtain X where "X \<in> P" and "X \<union> F X = X' \<union> G X'"
      by (metis imageE image_eqI)
    moreover from assms(2,4) \<open>X \<in> P\<close> have X: "(X \<union> F X) \<inter> A = X" by auto
    moreover from assms(3,5) \<open>X' \<in> P'\<close> have X': "(X' \<union> G X') \<inter> A = X'" by auto
    ultimately have "X = X'" by simp
    from this \<open>X \<in> P\<close> show "X' \<in> P" by auto
  qed
qed

subsubsection {* Disjointness under Function Application *}

definition disjoint_under :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "disjoint_under f S = (\<forall>s\<in>S. \<forall>t\<in>S. s \<noteq> t \<longrightarrow> (f s) \<inter> (f t) = {})"

lemma disjoint_underI:
  assumes "\<And>s t. s \<in> S \<and> t \<in> S \<Longrightarrow> s \<noteq> t \<Longrightarrow> (f s) \<inter> (f t) = {}"
  shows "disjoint_under f S"
using assms unfolding disjoint_under_def by auto

lemma disjoint_singleton: "\<And>s t X Y. s \<noteq> t \<Longrightarrow> (X = Y \<Longrightarrow> s = t) \<Longrightarrow> {X} \<inter> {Y} = {}"
by auto

lemma disjoint_bind: "\<And>S T f g. (\<And>s t. S s \<and> T t \<Longrightarrow> f s \<inter> g t = {}) \<Longrightarrow> ({s. S s} \<bind> f) \<inter> ({t. T t} \<bind> g)  = {}"
by fastforce

lemma disjoint_bind': "\<And>S T f g. (\<And>s t. s \<in> S \<and> t \<in> T \<Longrightarrow> f s \<inter> g t = {}) \<Longrightarrow> (S \<bind> f) \<inter> (T \<bind> g)  = {}"
by fastforce

lemma injectivity_solver_CollectE:
  assumes "a \<in> {x. P x} \<and> a' \<in> {x. P' x}"
  assumes "(P a \<and> P' a') \<Longrightarrow> W"
  shows "W"
using assms by auto

lemma injectivity_solver_prep_assms:
  assumes "x \<in> {x. P x}"
  shows "P x \<and> P x"
using assms by simp

method injectivity_solver uses rule =
  ((drule injectivity_solver_prep_assms)+)?;
  rule disjoint_underI;
  (rule disjoint_bind | rule disjoint_bind')+; erule disjoint_singleton;
  (elim injectivity_solver_CollectE)?;
  rule rule;
  assumption+

subsubsection {* Cardinality Theorems for Set.bind *}

lemma finite_bind:
  assumes "finite S"
  assumes "\<forall>x \<in> S. finite (f x)"
  shows "finite (S \<bind> f)"
using assms by (simp add: bind_UNION)

lemma card_bind:
  assumes "finite S"
  assumes "\<forall>X \<in> S. finite (f X)"
  assumes "disjoint_under f S"
  shows "card (S \<bind> f) = (\<Sum>x\<in>S. card (f x))"
proof -
  have "card (S \<bind> f) = card (\<Union>(f ` S))"
    by (simp add: bind_UNION)
  also have "card (\<Union>(f ` S)) = (\<Sum>x\<in>S. card (f x))"
    using assms unfolding disjoint_under_def
    by (subst card_Union_image) simp+
  finally show ?thesis .
qed

lemma card_bind_constant:
  assumes "finite S"
  assumes "\<forall>X \<in> S. finite (f X)"
  assumes "disjoint_under f S"
  assumes "\<And>x. x \<in> S \<Longrightarrow> card (f x) = k"
  shows "card (S \<bind> f) = card S * k"
using assms by (simp add: card_bind)

subsection {* Definition of Bell Numbers *}

definition Bell :: "nat \<Rightarrow> nat"
where
  "Bell n = card {P. partitions P {0..<n}}"

text {* Show that definition holds for any set A with cardinality n *}

lemma Bell_altdef:
  assumes "finite A"
  shows "Bell (card A) = card {P. partitions P A}"
proof -
  from \<open>finite A\<close> obtain f where bij: "bij_betw f {0..<card A} A"
    using ex_bij_betw_nat_finite by blast
  from this have inj: "inj_on f {0..<card A}"
    using bij_betw_imp_inj_on by blast
  from bij have image_f_eq: "A = f ` {0..<card A}"
    using bij_betw_imageE by blast
  have "\<forall>x \<in> {P. partitions P {0..<card A}}. x \<subseteq> Pow {0..<card A}"
    by (auto elim: partitionsE)
  from this inj have "inj_on (op ` (op ` f)) {P. partitions P {0..<card A}}"
    by (intro inj_on_impl_inj_on_image[of _ "Pow {0..<card A}"]
     inj_on_impl_inj_on_image[of _ "{0..<card A}"]) blast+
  moreover from inj have "op ` (op ` f) ` {P. partitions P {0..<card A}} = {P. partitions P A}"
    by (subst image_f_eq, auto elim!: set_of_partitions_map)
  ultimately have "bij_betw (op ` (op ` f)) {P. partitions P {0..<card A}} {P. partitions P A}"
    by (auto intro: bij_betw_imageI)
  from this \<open>finite A\<close> show ?thesis
    unfolding Bell_def by (subst BIJ[symmetric]) (auto intro: finitely_many_partitions)
qed

lemma Bell_0:
  "Bell 0 = 1"
by (auto simp add: Bell_def partitions_empty)

subsection {* Construction of the Partitions *}

definition construct_partitions :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set set"
where
  "construct_partitions B C =
    do {
       k  \<leftarrow> {0..card B};
       j  \<leftarrow> {0..card C};
       P  \<leftarrow> {P. partitions P C \<and> card P = j};
       B' \<leftarrow> {B'. B' \<subseteq> B \<and> card B' = k};
       Q  \<leftarrow> {Q. partitions Q B'};
       f  \<leftarrow> (B - B') \<rightarrow>\<^sub>E P;
       P'  \<leftarrow> {(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P};
       {P' \<union> Q}
    }"

lemma construct_partitions:
  assumes "finite B" "finite C"
  assumes "B \<inter> C = {}"
  shows "construct_partitions B C = {P. partitions P (B \<union> C)}"
proof (rule set_eqI')
  fix Q'
  assume "Q' \<in> construct_partitions B C"
  from this obtain j k P P' Q B' f
    where "j \<le> card C"
    and "k \<le> card B"
    and P: "partitions P C \<and> card P = j"
    and B': "B' \<subseteq> B \<and> card B' = k"
    and Q: "partitions Q B'"
    and f: "f \<in> B - B' \<rightarrow>\<^sub>E P"
    and P': "P' = (\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P"
    and Q': "Q' = P' \<union> Q"
    unfolding construct_partitions_def by auto
  from P f have "partitions P' (B - B' \<union> C)"
    unfolding P' using \<open>B \<inter> C = {}\<close>
    by (intro partitions_insert_elements) auto
  from this Q have "partitions Q' ((B - B' \<union> C) \<union> B')"
    unfolding Q' using B' \<open>B \<inter> C = {}\<close> by (auto intro: partitions_union)
  from this have "partitions Q' (B \<union> C)"
    using B' by (metis Diff_partition sup.assoc sup.commute)
  from this show "Q' \<in> {P. partitions P (B \<union> C)}" by auto
next
  fix Q'
  assume Q': "Q' \<in> {Q'. partitions Q' (B \<union> C)}"
  from Q' have "{} \<notin> Q'" by (auto elim!: partitionsE)
  obtain Q where Q: "Q = ((\<lambda>X. if X \<subseteq> B then X else {}) ` Q') - {{}}" by blast
  obtain P' where P': "P' = ((\<lambda>X. if X \<subseteq> B then {} else X) ` Q') - {{}}" by blast
  from P' Q \<open>{} \<notin> Q'\<close> have Q'_prop: "Q' = P' \<union> Q" by auto
  have P'_nosubset: "\<forall>X \<in> P'. \<not> X \<subseteq> B"
    unfolding P' by auto
  moreover have "\<forall>X \<in> P'. X \<subseteq> B \<union> C"
    using Q' P' by (auto elim: partitionsE)
  ultimately have P'_witness: "\<forall>X \<in> P'. \<exists>x. x \<in> X \<inter> C"
    using \<open>B \<inter> C = {}\<close> by fastforce
  obtain B' where B': "B' = \<Union>Q" by blast
  have Q_prop: "partitions Q B'"
    using B' Q' Q'_prop partitions_split2 mem_Collect_eq by blast
  have "\<Union>P' = B - B' \<union> C"
  proof
    have "\<Union>Q' = B \<union> C" "\<forall>X\<in>Q'. \<forall>X'\<in>Q'. X \<noteq> X' \<longrightarrow> X \<inter> X' = {}"
      using Q' unfolding partitions_def by auto
    from this show "\<Union>P' \<subseteq> B - B' \<union> C"
      unfolding P' B' Q by auto blast
  next
    show "B - B' \<union> C \<subseteq> \<Union>P'"
    proof
      fix x
      assume "x \<in> B - B' \<union> C"
      from this obtain X where X: "x \<in> X" "X \<in> Q'"
        using Q' by (metis Diff_iff Un_iff mem_Collect_eq partitions_partitions_unique)
      have "\<forall>X \<in> Q'. X \<subseteq> B \<longrightarrow> X \<subseteq> B'"
        unfolding B' Q by auto
      from this X \<open>x \<in> B - B' \<union> C\<close> have "\<not> X \<subseteq> B"
        using \<open>B \<inter> C = {}\<close> by auto
      from this \<open>X \<in> Q'\<close> have "X \<in> P'" using P' by auto
      from this \<open>x \<in> X\<close> show "x \<in> \<Union>P'" by auto
    qed
  qed
  from this have partitions_P': "partitions P' (B - B' \<union> C)"
    using partitions_split1 Q'_prop Q' mem_Collect_eq by fastforce
  obtain P where P: "P = (\<lambda>X. X \<inter> C) ` P'" by blast
  from P partitions_P' P'_witness have "partitions P C"
    using partitions_intersect_on_elements by auto
  obtain f where f: "f = (\<lambda>x. if x \<in> B - B' then (THE X. x \<in> X \<and> X \<in> P') \<inter> C else undefined)" by blast
  have P'_prop: "P' = (\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P"
  proof
    {
      fix X
      assume "X \<in> P'"
      have X_subset: "X \<subseteq> (B - B') \<union> C"
        using partitions_P' \<open>X \<in> P'\<close> by (auto elim: partitionsE)
      have "X = X \<inter> C \<union> {x \<in> B - B'. f x = X \<inter> C}"
      proof
        {
          fix x
          assume  "x \<in> X"
          from this X_subset have "x \<in> (B - B') \<union> C" by auto
          from this have "x \<in> X \<inter> C \<union> {xa \<in> B - B'. f xa = X \<inter> C}"
          proof
            assume "x \<in> C"
            from this \<open>x \<in> X\<close> show ?thesis by simp
          next
            assume "x \<in> B - B'"
            from partitions_P' \<open>x \<in> X\<close> \<open>X \<in> P'\<close> have "(THE X. x \<in> X \<and> X \<in> P') = X"
              by (simp add: partitions_the_part_eq)
            from \<open>x \<in> B - B'\<close> this show ?thesis unfolding f by auto
          qed
        }
        from this show "X \<subseteq> X \<inter> C \<union> {x \<in> B - B'. f x = X \<inter> C}" by auto
      next
        show "X \<inter> C \<union> {xa \<in> B - B'. f xa = X \<inter> C} \<subseteq> X"
        proof
          fix x
          assume "x \<in> X \<inter> C \<union> {x \<in> B - B'. f x = X \<inter> C}"
          from this show "x \<in> X"
          proof
            assume "x \<in> X \<inter> C"
            from this show ?thesis by simp
          next
            assume x_in: "x \<in> {x \<in> B - B'. f x = X \<inter> C}"
            from this have ex1: "\<exists>!X. x \<in> X \<and> X \<in> P'"
              using partitions_P' by (auto intro!: partitions_partitions_unique)
            from x_in X_subset have eq: "(THE X. x \<in> X \<and> X \<in> P') \<inter> C = X \<inter> C"
              unfolding f by auto
           from P'_nosubset \<open>X \<in> P'\<close> have "\<not> X \<subseteq> B" by simp
           from this have "X \<inter> C \<noteq> {}"
             using X_subset assms(3) by blast
           from this obtain y where y: "y \<in> X \<inter> C" by auto
           from this eq have y_in: "y \<in> (THE X. x \<in> X \<and> X \<in> P') \<inter> C" by simp
           from y y_in have "y \<in> X" "y \<in> (THE X. x \<in> X \<and> X \<in> P')" by auto
           moreover from y have "\<exists>!X. y \<in> X \<and> X \<in> P'"
             using partitions_P' by (simp add: partitions_partitions_unique)
           moreover have "(THE X. x \<in> X \<and> X \<in> P') \<in> P'"
             using ex1 by (rule the1I2) auto
           ultimately have "(THE X. x \<in> X \<and> X \<in> P') = X" using \<open>X \<in> P'\<close> by auto
           from this ex1 show ?thesis by (auto intro: the1I2)
          qed
        qed
      qed
      from \<open>X \<in> P'\<close> this have "X \<in> (\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P"
        unfolding P by simp
    }
    from this show "P' \<subseteq> (\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P" ..
  next
    {
      fix x
      assume x_in_image: "x \<in> (\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P"
      {
        fix X
        assume "X \<in> P'"
        have "{x \<in> B - B'. f x = X \<inter> C} =  {x \<in> B - B'. x \<in> X}"
        proof -
          {
            fix x
            assume "x \<in> B - B'"
            from this have ex1: "\<exists>!X. x \<in> X \<and> X \<in> P'"
              using partitions_P' by (auto intro!: partitions_partitions_unique)
            from this have in_p: "(THE X. x \<in> X \<and> X \<in> P') \<in> P'"
              and x_in: "x \<in> (THE X. x \<in> X \<and> X \<in> P')"
              by (metis (mono_tags, lifting) theI)+
            have "f x = X \<inter> C \<longleftrightarrow> (THE X. x \<in> X \<and> X \<in> P') \<inter> C = X \<inter> C"
              using \<open>x \<in> B - B'\<close> unfolding f by auto
            also have "... \<longleftrightarrow> (THE X. x \<in> X \<and> X \<in> P') = X"
            proof
              assume "(THE X. x \<in> X \<and> X \<in> P') = X"
              from this show "(THE X. x \<in> X \<and> X \<in> P') \<inter> C = X \<inter> C" by auto
            next
              assume "(THE X. x \<in> X \<and> X \<in> P') \<inter> C = X \<inter> C"
              have "(THE X. x \<in> X \<and> X \<in> P') \<inter> X \<noteq> {}"
                using P'_witness \<open>(THE X. x \<in> X \<and> X \<in> P') \<inter> C = X \<inter> C\<close> \<open>X \<in> P'\<close> by fastforce
              from this show "(THE X. x \<in> X \<and> X \<in> P') = X"
                using partitions_P'[unfolded partitions_def] in_p \<open>X \<in> P'\<close> by metis
            qed
            also have "... \<longleftrightarrow> x \<in> X"
              using ex1 \<open>X \<in> P'\<close> x_in by (auto; metis (no_types, lifting) the_equality)
            finally have "f x = X \<inter> C \<longleftrightarrow> x \<in> X" .
          }
          from this show ?thesis by auto
        qed
        moreover have  "X \<subseteq> B - B' \<union> C"
          using partitions_P' \<open>X \<in> P'\<close> by (blast elim: partitionsE)
        ultimately have "X \<inter> C \<union> {x \<in> B. x \<notin> B' \<and> f x = X \<inter> C} = X" by auto
      }
      from this x_in_image have "x \<in> P'" unfolding P by auto
    }
    from this show "(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P \<subseteq> P'" ..
  qed
  from partitions_P' have f_prop: "f \<in> (B - B') \<rightarrow>\<^sub>E P"
    unfolding f P by (auto simp add: partitions_the_part_mem)
  from Q B' have "B' \<subseteq> B" by auto
  obtain k where k: "k = card B'" by blast
  from \<open>finite B\<close> \<open>B' \<subseteq> B\<close> k have k_prop: "k \<in> {0..card B}" by (simp add: card_mono)
  obtain j where j: "j = card P" by blast
  from j \<open>partitions P C\<close> have j_prop: "j \<in> {0..card C}"
    by (simp add: assms(2) partitions_le_set_elements)
  from \<open>partitions P C\<close> j have P_prop: "partitions P C \<and> card P = j" by auto
  from k \<open>B' \<subseteq> B\<close> have B'_prop: "B' \<subseteq> B \<and> card B' = k" by auto
  show "Q' \<in> construct_partitions B C"
    using j_prop k_prop P_prop B'_prop Q_prop P'_prop f_prop Q'_prop
    unfolding construct_partitions_def
    by (auto simp del: atLeastAtMost_iff) blast
qed

subsection {* Injectivity of the Set Construction *}

lemma injectivity:
  assumes "B \<inter> C = {}"
  assumes P: "(partitions P C \<and> card P = j) \<and> (partitions P' C \<and> card P' = j')"
  assumes B': "(B' \<subseteq> B \<and> card B' = k) \<and> (B'' \<subseteq> B \<and> card B'' = k')"
  assumes Q: "partitions Q B' \<and> partitions Q' B''"
  assumes f: "f \<in> B - B' \<rightarrow>\<^sub>E P \<and> g \<in> B - B'' \<rightarrow>\<^sub>E P'"
  assumes P': "P'' \<in> {(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P} \<and>
    P''' \<in> {(\<lambda>X. X \<union> {x \<in> B - B''. g x = X}) ` P'}"
  assumes eq_result: "P'' \<union> Q = P''' \<union> Q'"
  shows "f = g" and "Q = Q'" and "B' = B''"
    and "P = P'" and "j = j'" and "k = k'"
proof -
  have P_nonempty_sets: "\<forall>X\<in>P. \<exists>c\<in>C. c \<in> X" "\<forall>X\<in>P'. \<exists>c\<in>C. c \<in> X"
    using P by (force elim: partitionsE)+
  have 1: "\<forall>X\<in>P''. \<exists>c\<in>C. c \<in> X" "\<forall>X\<in>P'''. \<exists>c\<in>C. c \<in> X"
    using P' P_nonempty_sets by fastforce+
  have 2: "\<forall>X\<in>Q. \<forall>x\<in>X. x \<notin> C" "\<forall>X\<in>Q'. \<forall>x\<in>X. x \<notin> C"
    using \<open>B \<inter> C = {}\<close> Q B' by (auto elim: partitionsE)
  from eq_result have "P'' = P'''" and "Q = Q'"
    by (auto dest: injectivity_union[OF _ 1 2])
  from this Q show "Q = Q'" and "B' = B''"
    by (auto intro!: partitions_eq_implies_eq_carrier)
  have subset_C: "\<forall>X\<in>P. X \<subseteq> C" "\<forall>X\<in>P'. X \<subseteq> C"
    using P by (auto elim: partitionsE)
  have eq_image: "(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P = (\<lambda>X. X \<union> {x \<in> B - B''. g x = X}) ` P'"
    using P' \<open>P'' = P'''\<close> by auto
  from this \<open>B \<inter> C = {}\<close>  show "P = P'"
    by (auto dest: injectivity_image_union[OF _ subset_C])
  have eq2: "(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P = (\<lambda>X. X \<union> {x \<in> B - B'. g x = X}) ` P"
    using \<open>P = P'\<close> \<open>B' = B''\<close> eq_image by simp
  from P have P_props: "\<forall>X \<in> P. X \<subseteq> C" "\<forall>X \<in> P. X \<noteq> {}" by (auto elim: partitionsE)
  have invert: "\<forall>X\<in>P. (X \<union> {x \<in> B - B'. f x = X}) \<inter> C = X \<and> (X \<union> {x \<in> B - B'. g x = X}) \<inter> C = X"
    using \<open>B \<inter> C = {}\<close> P_props by auto
  have eq3: "\<forall>X \<in> P. (X \<union> {x \<in> B - B'. f x = X}) = (X \<union> {x \<in> B - B'. g x = X})"
    using injectivity_image[OF eq2 invert] by blast
  have eq4: "\<forall>X \<in> P. {x \<in> B - B'. f x = X} = {x \<in> B - B'. g x = X}"
  proof
    fix X
    assume "X \<in> P"
    from this P have "X \<subseteq> C" by (auto elim: partitionsE)
    have disjoint: "X \<inter> {x \<in> B - B'. f x = X} = {}" "X \<inter> {x \<in> B - B'. g x = X} = {}"
      using \<open>B \<inter> C = {}\<close> \<open>X \<subseteq> C\<close> by auto
    from eq3 \<open>X \<in> P\<close> have "X \<union> {x \<in> B - B'. f x = X} = X \<union> {x \<in> B - B'. g x = X}" by auto
    from this disjoint show "{x \<in> B - B'. f x = X} = {x \<in> B - B'. g x = X}"
      by (auto intro: injectivity_union)
  qed
  from eq4 f have eq5: "\<forall>b\<in>B - B'. f b = g b" by blast
  from eq5 f \<open>B' = B''\<close> \<open>P = P'\<close> show eq6: "f = g" by (auto intro: extensional_funcset_ext)
  from P \<open>P = P'\<close> show "j = j'" by simp
  from B' \<open>B' = B''\<close> show "k = k'" by simp
qed

subsection {* The Generalized Bell Recurrence Relation *}

theorem Bell_eq:
  "Bell (n + m) = (\<Sum>k\<le>n. \<Sum>j\<le>m. j ^ (n - k) * Stirling m j * (n choose k) * Bell k)"
proof -
  def A == "{0..<n + m}"
  def B == "{0..<n}"
  def C == "{n..<n + m}"
  have "A = B \<union> C" "B \<inter> C = {}" "finite B" "card B = n" "finite C" "card C = m"
    unfolding A_def B_def C_def by auto
  have step1: "Bell (n + m) = card {P. partitions P A}"
    unfolding Bell_def A_def ..
  from \<open>A = B \<union> C\<close> \<open>B \<inter> C = {}\<close> \<open>finite B\<close> \<open>finite C\<close> have step2: "card {P. partitions P A} = card (construct_partitions B C)"
    by (simp add: construct_partitions)
  note injectivity = injectivity[OF \<open>B \<inter> C = {}\<close>]
  let ?expr = "do {
    k  \<leftarrow> {0..card B};
    j  \<leftarrow> {0..card C};
    P  \<leftarrow> {P. partitions P C \<and> card P = j};
    B' \<leftarrow> {B'. B' \<subseteq> B \<and> card B' = k};
    Q  \<leftarrow> {Q. partitions Q B'};
    f  \<leftarrow> (B - B') \<rightarrow>\<^sub>E P;
    P'  \<leftarrow> {(\<lambda>X. X \<union> {x \<in> B - B'. f x = X}) ` P};
    {P' \<union> Q}
  }"
  let "?S \<bind> ?comp" = ?expr
  {
    fix k
    assume k: "k \<in> {..card B}"
    let ?expr = "?comp k"
    let "?S \<bind> ?comp" = ?expr
    {
      fix j
      assume "j \<in> {.. card C}"
      let ?expr = "?comp j"
      let "?S \<bind> ?comp" = ?expr
      from \<open>finite C\<close> have "finite ?S"
        by (intro finite_Collect_conjI disjI1 finitely_many_partitions)
      {
        fix P
        assume P: "P \<in> {P. partitions P C \<and> card P = j}"
        from this have "partitions P C" by simp
        let ?expr = "?comp P"
        let "?S \<bind> ?comp" = ?expr
        have "finite P"
         using P \<open>finite C\<close> by (auto intro: finite_elements)
        from \<open>finite B\<close> have "finite ?S" by (auto simp add: finite_subset)
        moreover
        {
          fix B'
          assume B': "B' \<in> {B'. B' \<subseteq> B \<and> card B' = k}"
          from this have "B' \<subseteq> B" by simp
          let ?expr = "?comp B'"
          let "?S \<bind> ?comp" = ?expr
          from \<open>finite B\<close> have "finite B'"
            using B' by (auto simp add: finite_subset)
          from \<open>finite B'\<close> have "finite {Q. partitions Q B'}"
            by (rule finitely_many_partitions)
          moreover
          {
            fix Q
            assume Q: "Q \<in> {Q. partitions Q B'}"
            let ?expr = "?comp Q"
            let "?S \<bind> ?comp" = ?expr
            {
              fix f
              assume "f \<in> B - B' \<rightarrow>\<^sub>E P"
              let ?expr = "?comp f"
              let "?S \<bind> ?comp" = ?expr
              have "disjoint_under ?comp ?S"
                unfolding disjoint_under_def by auto
              from this have "card ?expr = 1"
                by (simp add: card_bind_constant)
              moreover have "finite ?expr"
                by (simp add: finite_bind)
              ultimately have "finite ?expr \<and> card ?expr = 1" by blast
            }
            moreover have "finite ?S"
              using \<open>finite B\<close> \<open>finite P\<close> by (auto intro: finite_PiE)
            moreover have "disjoint_under ?comp ?S"
              using P B' Q
              by - (injectivity_solver rule: local.injectivity(1))
            moreover have "card ?S = j ^ (n - k)"
            proof -
              have "card (B - B') = n - k"
                using B' \<open>finite B'\<close> \<open>card B = n\<close>
                by (subst card_Diff_subset) auto
              from this show ?thesis
                using \<open>finite B\<close> P
                by (subst card_PiE) (simp add: setprod_constant)+
            qed
            ultimately have "card ?expr = j ^ (n - k)"
              by (simp add: card_bind_constant)
            moreover have "finite ?expr"
              using \<open>finite ?S\<close> \<open>finite {P. partitions P C \<and> card P = j}\<close>
              by (auto intro!: finite_bind)
            ultimately have "finite ?expr \<and> card ?expr = j ^ (n - k)" by blast
          } note inner = this
          moreover have "card ?S = Bell k"
            using B' \<open>finite B'\<close> by (auto simp add: Bell_altdef[symmetric])
          moreover have "disjoint_under ?comp ?S"
            using P B'
            by - (injectivity_solver rule: local.injectivity(2))
          ultimately have "card ?expr = j ^ (n - k) * Bell k"
            by (subst card_bind_constant) auto
          moreover have "finite ?expr"
            using inner \<open>finite ?S\<close> by (auto intro: finite_bind)
          ultimately have "finite ?expr \<and> card ?expr = j ^ (n - k) * Bell k" by blast
        } note inner = this
        moreover have "card ?S = n choose k"
          using \<open>card B = n\<close> \<open>finite B\<close> by (simp add: n_subsets)
        moreover have "disjoint_under ?comp ?S"
          using P
          by - (injectivity_solver rule: local.injectivity(3))
        ultimately have "card ?expr = j ^ (n - k) * (n choose k) * Bell k"
          by (subst card_bind_constant) auto
        moreover have "finite ?expr"
          using inner \<open>finite ?S\<close> by (auto intro: finite_bind)
        ultimately have "finite ?expr \<and> card ?expr = j ^ (n - k) * (n choose k) * Bell k" by blast
      } note inner = this
      moreover note \<open>finite ?S\<close>
      moreover have "card ?S = Stirling m j"
        using \<open>finite C\<close> \<open>card C = m\<close> by (simp add: card_partitions)
      moreover have "disjoint_under ?comp ?S"
        by (injectivity_solver rule: local.injectivity(4))
      ultimately have "card ?expr = j ^ (n - k) * Stirling m j * (n choose k) * Bell k"
        by (subst card_bind_constant) auto
      moreover have "finite ?expr"
        using inner \<open>finite ?S\<close> by (auto intro: finite_bind)
      ultimately have "finite ?expr \<and> card ?expr = j ^ (n - k) * Stirling m j * (n choose k) * Bell k" by blast
    } note inner = this
    moreover have "finite ?S" by simp
    moreover have "disjoint_under ?comp ?S"
      by (injectivity_solver rule: local.injectivity(5))
    ultimately have "card ?expr = (\<Sum>j\<le>m. j ^ (n - k) * Stirling m j * (n choose k) * Bell k)" (is "_ = ?formula")
      using \<open>card C = m\<close> by (subst card_bind) (auto intro: setsum.cong)
    moreover have "finite ?expr"
      using inner \<open>finite ?S\<close> by (auto intro: finite_bind)
    ultimately have "finite ?expr \<and> card ?expr = ?formula" by blast
  }
  moreover have "finite ?S" by simp
  moreover have "disjoint_under ?comp ?S"
    by (injectivity_solver rule: local.injectivity(6))
  ultimately have step3: "card (construct_partitions B C) = (\<Sum>k\<le>n. \<Sum>j\<le>m. j ^ (n - k) * Stirling m j * (n choose k) * Bell k)"
    unfolding construct_partitions_def
    using \<open>card B = n\<close> by (subst card_bind) (auto intro: setsum.cong)
  from step1 step2 step3 show ?thesis by auto
qed

subsection {* Corollaries of the Generalized Bell Recurrence *}

corollary Bell_Stirling_eq:
  "Bell m = (\<Sum>j\<le>m. Stirling m j)"
proof -
  have "Bell m = Bell (0 + m)" by simp
  also have "... = (\<Sum>j\<le>m. Stirling m j)"
    unfolding Bell_eq[of 0] by (simp add: Bell_0)
  finally show ?thesis .
qed

corollary Bell_recursive_eq:
  "Bell (n + 1) = (\<Sum>k\<le>n. (n choose k) * Bell k)"
unfolding Bell_eq[of _ 1] by simp

end
