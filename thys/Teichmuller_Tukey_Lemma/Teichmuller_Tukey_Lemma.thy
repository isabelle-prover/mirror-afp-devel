(*  Title:      Teichmuller_Tukey_Lemma.thy
    Author:     Vithor Lindermann Kraisch, Federal University of Santa Catarina
    Author:     Luiz Gustavo Cordeiro, Federal University of Santa Catarina
    Maintainer: Vithor Lindermann Kraisch <vithorkr at gmail.com>
*)

section \<open>The Teichmüller--Tukey Lemma\<close>

theory Teichmuller_Tukey_Lemma
  imports Main
begin

text \<open>
  The Teichmüller--Tukey lemma states that every nonempty family of sets of
  finite character has a member that is maximal under inclusion.  Although the
  result follows from Zorn's lemma, the development below formalizes the direct
  choice-function construction presented by Sun and Yu
  \<^cite>\<open>"SunYu2019"\<close>.  Their proof is formulated in Morse--Kelley set
  theory and checked in Coq; here it is adapted to polymorphic HOL sets.

  This result was developed as infrastructure for a separate formalization of
  first-order logic following Shoenfield \<^cite>\<open>"Shoenfield1967"\<close>.
\<close>

subsection \<open>Families of finite character\<close>

definition Maximal :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "Maximal A J \<equiv> A \<in> J \<and> (\<forall>B\<in>J. \<not> A \<subset> B)"

definition Nest :: "'a set set \<Rightarrow> bool" where
  "Nest A \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. x \<subseteq> y \<or> y \<subseteq> x"

definition Finite_character :: "'a set set \<Rightarrow> bool" where
  "Finite_character J \<equiv> \<forall>\<Delta>. \<Delta> \<in> J \<longleftrightarrow> (\<forall>\<delta>\<subseteq>\<Delta>. finite \<delta> \<longrightarrow> \<delta> \<in> J)"

text \<open>
  A family of finite character is downward closed.  It is also closed under the
  union of a nest.  Nonemptiness is needed for the empty nest: it ensures that
  the empty set belongs to the family.
\<close>

proposition property_fin_char:
  assumes "Finite_character J" and "J \<noteq> {}"
  shows "\<forall>A\<in>J. \<forall>B\<subseteq>A. B \<in> J"
    and "\<forall>G. Nest G \<and> G \<subseteq> J \<longrightarrow> \<Union>G \<in> J"
proof -
  show "\<forall>A\<in>J. \<forall>B\<subseteq>A. B \<in> J"
    using Finite_character_def assms(1) by (meson subset_trans)
next
  show "\<forall>G. Nest G \<and> G \<subseteq> J \<longrightarrow> \<Union>G \<in> J"
  proof (rule allI, rule impI)
    fix G
    assume B: "Nest G \<and> G \<subseteq> J"
    have C: "\<And>g. set g \<subseteq> \<Union>G \<Longrightarrow> g \<noteq> [] \<Longrightarrow> \<exists>X\<in>G. set g \<subseteq> X"
    proof -
      fix g
      show "set g \<subseteq> \<Union>G \<Longrightarrow> g \<noteq> [] \<Longrightarrow> \<exists>X\<in>G. set g \<subseteq> X"
      proof (induction g rule: measure_induct[of length])
        case (1 g)
        then show ?case
        proof cases
          assume "g = [] \<or> (\<exists>a. g = [a])"
          then show ?case using "1.prems"(1,2) by fastforce
        next
          assume "\<not> (g = [] \<or> (\<exists>a. g = [a]))"
          then obtain a and xs where axs: "g = a # xs \<and> xs \<noteq> []"
            by (metis list.exhaust)
          from this 1(1-2) have
            "(\<exists>X\<in>G. {a} \<subseteq> X) \<and> (\<exists>X\<in>G. set xs \<subseteq> X)"
            by auto
          thus ?case
            using B Nest_def axs
            by (metis dual_order.trans insert_subset list.simps(15))
        qed
      qed
    qed
    thus "\<Union>G \<in> J"
      using assms(1-2) B C Finite_character_def
      by (smt (z3) ex_in_conv finite_list set_empty subset_eq list.set(1,1,1,1)
          subsetI subset_antisym)
  qed
qed

subsection \<open>The choice extension\<close>

fun enlarge :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "enlarge F J = {x. x \<in> \<Union>J \<and> F\<union>{x} \<in> J}"

proposition enlarge_subset: "F \<in> J \<Longrightarrow> F \<subseteq> enlarge F J"
  using UnionI insert_absorb by force

fun \<X>_choice :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set" where
  "\<X>_choice F J c =
    (if enlarge F J - F = {} then F else F\<union>{c (enlarge F J - F)})"

text \<open>
  For a member @{term F} of @{term J}, @{term "enlarge F J"} contains the
  elements that can be adjoined to @{term F} while staying in @{term J}.  The
  operation @{term "\<X>_choice F J c"} adjoins an element chosen outside
  @{term F}, unless no such element exists.
\<close>

text \<open>
  The fixed-point argument below makes explicit a detail that is only implicit
  in Proof 4.7 of the source article.  From
  @{term "\<X>_choice F J c = F"} one may conclude
  @{term "enlarge F J = F"} only by using the choice property of @{term c}:
  if @{term "enlarge F J - F"} were nonempty, its chosen element would lie
  both outside and inside @{term F}.  This is the step that turns a fixed point
  of the choice extension into a maximal member.
\<close>

lemma \<X>_implies_TTL:
  assumes "Finite_character J"
    and "\<exists>F\<in>J. \<exists>c. ((\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y) \<and> \<X>_choice F J c = F)"
  shows "\<exists>\<Delta>\<in>J. Maximal \<Delta> J"
proof -
  from assms(2) obtain \<Delta> and c where
    \<Delta>c: "\<Delta> \<in> J \<and> (\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y) \<and> \<X>_choice \<Delta> J c = \<Delta>"
    by blast
  hence ig: "enlarge \<Delta> J = \<Delta>"
    by (metis DiffD2 Un_upper2 \<X>_choice.elims diff_shunt enlarge_subset
        insert_subset order_antisym_conv)
  have "Maximal \<Delta> J"
  proof (rule ccontr)
    assume "\<not> Maximal \<Delta> J"
    from this \<Delta>c obtain B where B: "B \<in> J \<and> \<Delta> \<subset> B"
      using Maximal_def by meson
    then obtain d where d: "d \<in> B \<and> d \<notin> \<Delta>" by blast
    hence "d \<in> enlarge \<Delta> J"
      using assms(1) Finite_character_def B property_fin_char(1) by fastforce
    thus False using ig d by blast
  qed
  thus "\<exists>\<Delta>\<in>J. Maximal \<Delta> J" using \<Delta>c by blast
qed

subsection \<open>The least closed subclass\<close>

text \<open>
  Following the notation of the source proof, a @{emph \<open>t-subclass\<close>}
  contains the empty set and is closed under both choice extensions and unions
  of nests.  Intersecting all t-subclasses gives the least such subclass.
\<close>

definition tSubclass :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> bool" where
  "tSubclass G J c \<equiv>
    G \<subseteq> J \<and> {} \<in> G \<and> (\<forall>F\<in>G. \<X>_choice F J c \<in> G) \<and>
    (\<forall>L\<subseteq>G. Nest L \<longrightarrow> \<Union>L \<in> G)"

definition inter_subclass :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set set" where
  "inter_subclass J c \<equiv> \<Inter>{G. tSubclass G J c}"

definition \<mu>_function :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set set" where
  "\<mu>_function C J c \<equiv>
    {A\<in>inter_subclass J c. A \<subseteq> C \<or> C \<subseteq> A}"

definition total_subclass :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set set" where
  "total_subclass J c \<equiv>
    {C\<in>inter_subclass J c. \<mu>_function C J c = inter_subclass J c}"

definition \<nu>_function :: "'a set \<Rightarrow> 'a set set \<Rightarrow> ('a set \<Rightarrow> 'a) \<Rightarrow> 'a set set" where
  "\<nu>_function D J c \<equiv>
    {A\<in>inter_subclass J c. A \<subseteq> D \<or> \<X>_choice D J c \<subseteq> A}"

proposition property_\<X>: "F \<in> J \<Longrightarrow> F \<subseteq> \<X>_choice F J c"
  by auto

proposition property_inter_subclass:
  assumes "Finite_character J" and "J \<noteq> {}"
    and "\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y"
  shows "tSubclass (inter_subclass J c) J c"
    and "\<forall>G. tSubclass G J c \<longrightarrow> inter_subclass J c \<subseteq> G"
proof -
  have JSubJ: "tSubclass J J c"
    using tSubclass_def Nest_def assms(1-3) property_fin_char(2)
    by (smt (verit, ccfv_threshold) Diff_iff Sup_empty \<X>_choice.simps
        dual_order.refl empty_iff empty_subsetI enlarge.simps mem_Collect_eq)
  show "tSubclass (inter_subclass J c) J c"
  proof (auto simp only: tSubclass_def[of "inter_subclass J c" J c])
    show "{} \<in> inter_subclass J c"
      using inter_subclass_def tSubclass_def
      by (metis (no_types, lifting) Inter_iff mem_Collect_eq)
  next
    have "\<forall>G F. tSubclass G J c \<longrightarrow> F \<in> G \<longrightarrow> \<X>_choice F J c \<in> G"
      using tSubclass_def by blast
    thus "\<And>F. F \<in> inter_subclass J c \<Longrightarrow> \<X>_choice F J c \<in> inter_subclass J c"
      using inter_subclass_def by blast
  next
    have "\<forall>G L. tSubclass G J c \<longrightarrow> L \<subseteq> G \<longrightarrow> Nest L \<longrightarrow> \<Union>L \<in> G"
      using tSubclass_def by metis
    thus "\<And>L. L \<subseteq> inter_subclass J c \<Longrightarrow> Nest L \<Longrightarrow> \<Union>L \<in> inter_subclass J c"
      using inter_subclass_def[of J c] by blast
  qed (auto simp add: JSubJ inter_subclass_def)
qed (auto simp add: inter_subclass_def)

subsection \<open>The least t-subclass is a Nest\<close>

text \<open>
  The next three lemmas correspond to Steps I--III of Section 4.1 in the
  source.  The auxiliary subclasses @{term "\<mu>_function C J c"} and
  @{term "\<nu>_function D J c"} isolate the members comparable with a given
  set and allow comparability to be propagated through the choice extension.
\<close>

lemma step1:
  assumes "Finite_character J" and "J \<noteq> {}"
    and "\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y"
    and "D \<in> total_subclass J c"
  shows "tSubclass (\<nu>_function D J c) J c"
proof -
  show ?thesis
  proof (auto simp only: tSubclass_def[of "\<nu>_function D J c" J c])
    have "\<nu>_function D J c \<subseteq> inter_subclass J c"
      using \<nu>_function_def by blast
    thus "\<And>x. x \<in> \<nu>_function D J c \<Longrightarrow> x \<in> J"
      using tSubclass_def property_inter_subclass(1) assms by (metis in_mono)
  next
    fix F
    assume "F \<in> \<nu>_function D J c"
    then have F: "F \<in> inter_subclass J c \<and>
        (F \<subseteq> D \<or> \<X>_choice D J c \<subseteq> F)"
      using \<nu>_function_def by blast
    show "\<X>_choice F J c \<in> \<nu>_function D J c"
    proof cases
      assume c1: "\<X>_choice D J c \<subseteq> F"
      then show ?thesis
        using F \<nu>_function_def assms(1-3) property_\<X>
          property_inter_subclass(1) tSubclass_def
        by (smt (verit) in_mono mem_Collect_eq subset_trans)
    next
      assume "\<not> \<X>_choice D J c \<subseteq> F"
      hence b: "\<X>_choice F J c \<subseteq> D \<or> D \<subseteq> \<X>_choice F J c"
        using assms F \<mu>_function_def tSubclass_def property_inter_subclass(1)
          total_subclass_def
        by (smt (verit, del_insts) mem_Collect_eq)
      show ?thesis
      proof (rule ccontr)
        assume hyp: "\<X>_choice F J c \<notin> \<nu>_function D J c"
        then have "\<not> \<X>_choice F J c \<subseteq> D"
          using assms(1-3) \<nu>_function_def F tSubclass_def
            property_inter_subclass(1)
          by (metis (no_types, lifting) mem_Collect_eq)
        from this b have "D \<subset> \<X>_choice F J c" by blast
        hence "D \<subset> F \<or> D \<subset> F\<union>{c (enlarge F J - F)}"
          by (metis \<X>_choice.simps)
        hence "\<X>_choice D J c \<subseteq> \<X>_choice F J c"
          using F \<open>\<not> \<X>_choice D J c \<subseteq> F\<close>
          by (metis Un_insert_right insert_subsetI leD order_class.order_eq_iff
              psubset_insert_iff sup_bot_right)
        thus False
          using hyp \<nu>_function_def F assms(1-3) property_inter_subclass(1)
            tSubclass_def
          by (metis (no_types, lifting) mem_Collect_eq)
      qed
    qed
  next
    fix L
    assume hyp1: "L \<subseteq> \<nu>_function D J c" and hyp2: "Nest L"
    then have UL: "\<Union>L \<in> inter_subclass J c"
      using \<nu>_function_def[of D J c] property_inter_subclass(1) assms(1-3)
        tSubclass_def
      by (smt (verit) mem_Collect_eq subset_eq)
    have "\<Union>L \<subseteq> D \<or> \<X>_choice D J c \<subseteq> \<Union>L"
    proof cases
      assume "\<forall>l\<in>L. l \<subseteq> D"
      then show ?thesis using UL \<nu>_function_def by blast
    next
      assume "\<not> (\<forall>l\<in>L. l \<subseteq> D)"
      from this hyp1 show ?thesis using \<nu>_function_def[of D J c] by blast
    qed
    thus "\<Union>L \<in> \<nu>_function D J c"
      using \<nu>_function_def[of D J c] UL by blast
  qed (simp add: \<nu>_function_def inter_subclass_def tSubclass_def)
qed

lemma step2:
  assumes "Finite_character J" and "J \<noteq> {}"
    and "\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y"
    and "D \<in> total_subclass J c"
  shows "\<X>_choice D J c \<in> total_subclass J c"
proof -
  from assms have "inter_subclass J c \<subseteq> \<nu>_function D J c"
    using step1 property_inter_subclass(2) by metis
  moreover have "\<nu>_function D J c \<subseteq> \<mu>_function (\<X>_choice D J c) J c"
    using \<mu>_function_def \<nu>_function_def
    by (smt (verit, best) Un_upper1 \<X>_choice.simps mem_Collect_eq subsetD subsetI)
  moreover have "... \<subseteq> inter_subclass J c" using \<mu>_function_def by blast
  ultimately have
    "\<mu>_function (\<X>_choice D J c) J c = inter_subclass J c"
    by order
  thus ?thesis
    using assms total_subclass_def[of J c] property_inter_subclass[of J c]
      tSubclass_def[of "inter_subclass J c" J c] by simp
qed

lemma step3:
  assumes "Finite_character J" and "J \<noteq> {}"
    and "\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y"
  shows "Nest (inter_subclass J c)"
proof -
  have "Nest (total_subclass J c)"
    using Nest_def[of "total_subclass J c"] total_subclass_def[of J c]
      \<mu>_function_def[of _ J c] by blast
  moreover have a: "total_subclass J c \<subseteq> inter_subclass J c"
    using total_subclass_def by auto
  moreover have "tSubclass (total_subclass J c) J c"
  proof (auto simp only: tSubclass_def[of "total_subclass J c" J c])
    show "\<And>x. x \<in> total_subclass J c \<Longrightarrow> x \<in> J"
      using a assms property_inter_subclass[of J c] tSubclass_def by (meson subsetD)
    show "{} \<in> total_subclass J c"
      using assms property_inter_subclass[of J c] \<mu>_function_def
        tSubclass_def[of "inter_subclass J c"] total_subclass_def[of J c]
      by fastforce
    show "\<And>F. F \<in> total_subclass J c \<Longrightarrow>
        \<X>_choice F J c \<in> total_subclass J c"
      using assms step2 by blast
    show "\<And>L. L \<subseteq> total_subclass J c \<Longrightarrow> Nest L \<Longrightarrow>
        \<Union>L \<in> total_subclass J c"
    proof -
      fix L
      assume hyp1: "L \<subseteq> total_subclass J c" and "Nest L"
      then have "\<Union>L \<in> inter_subclass J c"
        using property_inter_subclass(1) assms tSubclass_def a
        by (metis subset_trans)
      moreover from hyp1 have
        "\<forall>A\<in>inter_subclass J c. A \<subseteq> \<Union>L \<or> \<Union>L \<subseteq> A"
        using total_subclass_def[of J c] \<mu>_function_def[of _ J c] by blast
      ultimately show "\<Union>L \<in> total_subclass J c"
        using total_subclass_def[of J c] \<mu>_function_def[of "\<Union>L" J c]
        by auto
    qed
  qed
  hence "inter_subclass J c \<subseteq> total_subclass J c"
    using inter_subclass_def by blast
  ultimately show ?thesis by simp
qed

subsection \<open>The fixed point and the main theorem\<close>

text \<open>
  Since the least t-subclass is a nest, its union belongs to it.  Closure under
  the choice extension then places the extension in the same nest, while the
  definition of union bounds it from above.  Hence the union is a fixed point.
\<close>

lemma step4:
  assumes "Finite_character J" and "J \<noteq> {}"
    and "\<forall>Y. Y \<noteq> {} \<longrightarrow> c Y \<in> Y"
  shows "\<X>_choice (\<Union>(inter_subclass J c)) J c = \<Union>(inter_subclass J c)"
  using assms property_\<X> property_fin_char(2) property_inter_subclass step3
    tSubclass_def
  by (metis Union_upper subset_antisym)

theorem teichmueller_tuckey_lemma:
  fixes J :: "'a set set"
  assumes "Finite_character J" and "J \<noteq> {}"
  shows "\<exists>\<Delta>\<in>J. Maximal \<Delta> J"
proof -
  let ?c = "\<lambda>Y :: 'a set. SOME y. y \<in> Y"
  have choice: "\<forall>Y :: 'a set. Y \<noteq> {} \<longrightarrow> ?c Y \<in> Y"
    by (simp add: some_in_eq)
  have fixed:
    "\<X>_choice (\<Union>(inter_subclass J ?c)) J ?c =
      \<Union>(inter_subclass J ?c)"
    using assms choice step4 by metis
  have member: "\<Union>(inter_subclass J ?c) \<in> J"
    using assms choice property_fin_char(2) property_inter_subclass(1)
      step3 tSubclass_def by metis
  show ?thesis
    using assms(1) choice fixed member \<X>_implies_TTL[of J]
    by metis
qed

end
