(*
 Title: Source_and_Sink_Algebras_Constructions.thy
 Author: Tetsuya Sato
*)

theory Source_and_Sink_Algebras_Constructions
  imports
    "HOL-Analysis.Finite_Product_Measure"
    "Source_and_Sink_Algebras"
    "Measurable_Isomorphism"
begin

section \<open> Basic measurable sapces defined with initial and final lifts \<close>

subsection \<open> Another form of product \<open>\<sigma>\<close>-algebra \<close>

text \<open> We here introduce another form of product \<open>\<sigma>\<close>-algebra. The initial lift induced by projections has the same \<open>\<sigma>\<close>-algebra as @{term PiM} in the standard library, but ours are more suitable for categorical semantics of probabilistic programs. \<close>

definition prod_initial_source\<^marker>\<open>tag important\<close> :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<Rightarrow> 'a) measure"where
  "prod_initial_source I M = initial_source (\<Pi>\<^sub>E i\<in>I. space (M i)) ({((\<lambda> f. f i),M i) |i. i \<in> I})"

syntax
  "_prod_initial_source":: "pttrn \<Rightarrow>'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<times> 'a) set"("(3\<Pi>\<^sub>S _\<in>_./ _)"10)
translations
  "\<Pi>\<^sub>S x\<in>A. B"\<rightleftharpoons>"CONST prod_initial_source A (\<lambda>x. B)"

lemma space_prod_initial_source:
  "space (\<Pi>\<^sub>S i\<in>I. (M i)) = (\<Pi>\<^sub>E i\<in>I. space (M i))"
  by (auto simp: prod_initial_source_def)

lemma PiM_is_initial_source_nonempty_sets:
  assumes "I \<noteq> {}"
  shows "sets (PiM I M) = sets(prod_initial_source I M)"
  unfolding prod_initial_source_def initial_source_def
proof(subst sets_PiM_eq_proj, unfold vimage_algebra_def)
  show "sets (SUP i\<in>I. sigma (\<Pi>\<^sub>E i\<in>I. space (M i)) {(\<lambda>x. x i) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) |A. A \<in> sets (M i)}) =
 sets
 (sigma (\<Pi>\<^sub>E i\<in>I. space (M i))
 {B. \<exists>A f N. B = f -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) \<and> (f, N) \<in> {(\<lambda>f. f i, M i) |i. i \<in> I} \<and> A \<in> sets N})"
  proof(subst SUP_sigma_sigma)
    show "sets (sigma (\<Pi>\<^sub>E i\<in>I. space (M i)) (\<Union>m\<in>I. {(\<lambda>x. x m) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) |A. A \<in> sets (M m)}))
 = sets (sigma (\<Pi>\<^sub>E i\<in>I. space (M i)) {B. \<exists>A f N. B = f -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) \<and> (f, N) \<in> {(\<lambda>f. f i, M i) |i. i \<in> I} \<and> A \<in> sets N})"
    proof(subst sets_measure_of)
      show "sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) (\<Union>m\<in>I. {(\<lambda>x. x m) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) |A. A \<in> sets (M m)})
 = sets (sigma (\<Pi>\<^sub>E i\<in>I. space (M i)) {B. \<exists>A f N. B = f -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) \<and> (f, N) \<in> {(\<lambda>f. f i, M i) |i. i \<in> I} \<and> A \<in> sets N})"
      proof(subst sets_measure_of)
        show "sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) (\<Union>m\<in>I. {(\<lambda>x. x m) -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) |A. A \<in> sets (M m)})
 = sigma_sets (\<Pi>\<^sub>E i\<in>I. space (M i)) {B. \<exists>A f N. B = f -` A \<inter> (\<Pi>\<^sub>E i\<in>I. space (M i)) \<and> (f, N) \<in> {(\<lambda>f. f i, M i) |i. i \<in> I} \<and> A \<in> sets N}"
          by(rule sigma_sets_eqI,blast,blast)
      qed(auto)
    qed(auto)
  qed(auto simp add: assms)
qed(auto simp add: assms)

lemma PiM_is_initial_source_nonempty_space:
  assumes "I \<noteq> {}"
  shows "space (PiM I M) = space(prod_initial_source I M)"
  by (meson assms PiM_is_initial_source_nonempty_sets sets_eq_imp_space_eq)

lemma
  shows PiM_is_initial_source_empty_space: "space(prod_initial_source {} M) = {\<lambda>k. undefined}"
    and PiM_is_initial_source_empty_sets: "sets(prod_initial_source {} M) = {{}, {\<lambda>k. undefined}}"
proof
  show s1: "space (prod_initial_source {} M) \<subseteq> {\<lambda>k. undefined}"
    by (auto simp add: prod_initial_source_def)
  show s2: "{\<lambda>k. undefined} \<subseteq> space (prod_initial_source {} M)"
    by (auto simp add: prod_initial_source_def)
  show "sets (prod_initial_source {} M) = {{}, {\<lambda>k. undefined}}"
  proof
    show "sets (prod_initial_source {} M) \<subseteq> {{}, {\<lambda>k. undefined}}"
      by (metis s1 s2 insertCI sets.sets_into_space subsetI subset_antisym subset_singletonD)
    show "sets (prod_initial_source {} M) \<supseteq> {{}, {\<lambda>k. undefined}}"
      by (metis empty_subsetI insert_subsetI s1 s2 sets.empty_sets sets.top subset_antisym)
  qed
qed

proposition\<^marker>\<open>tag important\<close> PiM_is_initial_source:
  shows "space (PiM I M) = space (prod_initial_source I M)"
    and "sets (PiM I M) = sets (prod_initial_source I M)"
proof-
  show "sets (PiM I M) = sets (prod_initial_source I M)"
  proof(cases"I={}")
    case True
    thus ?thesis using PiM_is_initial_source_empty_sets sets_PiM_empty by metis
  next
    case False
    thus ?thesis using PiM_is_initial_source_nonempty_sets by metis
  qed
  thus "space (PiM I M) = space (prod_initial_source I M)"
    using sets_eq_imp_space_eq by auto
qed

lemma measurable_prod_initial_sourceI:
  assumes space: "f \<in> space N \<rightarrow> (\<Pi>\<^sub>E i\<in>I. space (M i))"
    and measurability: "\<And> i. i \<in> I \<Longrightarrow> (\<lambda> x . f x i) \<in> N \<rightarrow>\<^sub>M M i"
  shows "f \<in> N \<rightarrow>\<^sub>M prod_initial_source I M"
  by(unfold prod_initial_source_def, rule measurable_initial_source2, auto simp add: space intro: measurability)

lemma measurable_prod_initial_source_projections [measurable(raw)]:
  assumes "i \<in> I"
  shows "(\<lambda>f. f i) \<in> (\<Pi>\<^sub>S i\<in>I. (M i)) \<rightarrow>\<^sub>M (M i)"
  by(unfold prod_initial_source_def PiE_def, intro measurable_initial_source1,auto intro: assms)

subsubsection\<open>decomposition of countable product\<close>

lemma measurable_projection_shift:
  shows "(\<lambda>x n. x (Suc n)) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<n}. M)"
  by(induction n)(rule measurable_prod_initial_sourceI,auto simp:space_prod_initial_source)+

lemma measurable_decompose_prod_initial_source_Suc_n:
  shows "(\<lambda> f. (f 0, (\<lambda> n. f (Suc n)))) \<in> (\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M))"
  by(rule measurable_Pair,auto simp: measurable_projection_shift)

lemma measurable_integrate_prod_initial_source_Suc_n:
  shows "(\<lambda>p. (\<lambda> n. if n = 0 then (fst p) else (snd p)(n - 1))) \<in> (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M)) \<rightarrow>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<Suc n}. M)"
proof(rule measurable_prod_initial_sourceI)
  show "(\<lambda>p n. if n = 0 then fst p else snd p (n - 1)) \<in> space (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<n}. M)) \<rightarrow> {..<Suc n} \<rightarrow>\<^sub>E space M"
    unfolding space_pair_measure space_prod_initial_source PiE_def extensional_def Pi_def by auto
  fix i assume i: "i \<in> {..<Suc n}"
  show "(\<lambda>x. if i = 0 then fst x else snd x (i - 1)) \<in> M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M M"
  proof(cases"i = 0")
    case True
    thus ?thesis by auto
  next
    case False
    from i False have 1: "(i - 1) \<in> {..<n}"
      by auto
    from False have "(\<lambda>x. if i = 0 then fst x else snd x (i - 1)) = (\<lambda>f. f(i - 1)) o snd"
      by auto
    also have "... \<in> M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<n}. M) \<rightarrow>\<^sub>M M"
      using 1 by measurable
    finally show ?thesis .
  qed
qed

proposition measurable_iff_prod_initial_source:
  shows integrate_prod_initial_source_iff:
    "\<And> f . (f \<in> (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M)) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda> f. (f 0, (\<lambda> n. f (Suc n))))) \<in> ((\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M N)"
    and decompose_prod_initial_source_iff:
    "\<And> f . (f \<in> (\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda>p. (\<lambda> n. if n = 0 then (fst p) else (snd p)(n - 1))) \<in> (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M)) \<rightarrow>\<^sub>M N)"
proof-
  have A: "\<forall>x\<in>space (\<Pi>\<^sub>S i\<in>{..<Suc n}. M). (\<lambda>n. if n = 0 then fst (x 0, \<lambda>n. x (Suc n)) else snd (x 0, \<lambda>n. x (Suc n)) (n - 1)) = x"
    and B: "\<forall>y\<in>space (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..<n}. M)). (if 0 = 0 then fst y else snd y (0 - 1), \<lambda>n. if Suc n = 0 then fst y else snd y (Suc n - 1)) = y"
    by auto
  show "\<And> f . (f \<in> (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M)) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda> f. (f 0, (\<lambda> n. f (Suc n))))) \<in> ((\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M N)"
    and "\<And> f . (f \<in> (\<Pi>\<^sub>S i\<in>{..<Suc n}. M) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (f o (\<lambda>p. (\<lambda> n. if n = 0 then (fst p) else (snd p)(n - 1))) \<in> (M \<Otimes>\<^sub>M (\<Pi>\<^sub>S i\<in>{..< n}. M)) \<rightarrow>\<^sub>M N)"
    using
      measurable_isomorphism_iff(1,2)[of"(\<lambda> f. (f 0, (\<lambda> n. f (Suc n))))"_ _"(\<lambda>p. (\<lambda> n. if n = 0 then (fst p) else (snd p)(n - 1)))"_ N , OF measurable_decompose_prod_initial_source_Suc_n measurable_integrate_prod_initial_source_Suc_n A B]
    by auto
qed

subsection \<open> (Infinite) coproduct (disjoint union, direct sum) space \<close>

text \<open> We here introduce coproduct \<open>\<sigma>\<close>-algebra as the final lift induced by coprojections. We first recall coprojections and copairs, and then we define coproduct space. \<close>

subsubsection \<open> Coprojections and Cotuples \<close>

text \<open> We want to distinguish the usage of @{term "Pair"} for the coprojections from the pairing for binary product. \<close>

definition
  "coProj \<equiv> Pair"

lemma coProj_function:
  assumes "i \<in> I"
  shows "coProj i \<in> A i \<rightarrow> (SIGMA i:I. A i)"
  by (auto simp: assms Sigma_def coProj_def)

definition\<^marker>\<open>tag important\<close> coTuple :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a set) \<Rightarrow> ('i \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> ('i \<times> 'a \<Rightarrow> 'b)"where
  "coTuple I A F = (\<lambda> (i,a). F i a)"

lemma coTuple_function:
  assumes "\<forall> i \<in> I. F i \<in> A i \<rightarrow> B"
  shows "coTuple I A F \<in> (SIGMA i:I. A i) \<rightarrow> B"
  unfolding coTuple_def Sigma_def using assms by auto

lemma coTuple_eqI:
  assumes "\<forall> i \<in> I. F i \<in> A i \<rightarrow> C"
    and "\<forall> i \<in> I. (\<forall>a \<in> (A i). F i a = G i a)"
  shows "\<forall>(i,a) \<in> (SIGMA i:I. A i). coTuple I A F (i,a) = coTuple I A G (i,a)"
  unfolding coTuple_def Sigma_def using assms by auto

lemma coProj_coTuple:
  assumes "i \<in> I"
  shows "coTuple I A F o coProj i = F i"
  unfolding coTuple_def coProj_def by auto

lemma coTuple_unique:
  assumes "g \<in> (SIGMA i:I. A i) \<rightarrow> B"
  shows "\<forall> (i,a) \<in> (SIGMA i:I. A i). g(i,a) = (coTuple I A (\<lambda> j \<in> I. (g o coProj j)))(i,a)"
  by (auto simp: coTuple_def coProj_def Sigma_def)

subsubsection \<open> Coproduct \<open>\<sigma>\<close>-algebra defined as the final lift \<close>

definition\<^marker>\<open>tag important\<close> coprod_final_sink\<^marker>\<open>tag important\<close> :: "'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<times> 'a) measure"where
  "coprod_final_sink I M = final_sink (SIGMA i:I. space (M i)) ({(coProj i,M i) |i. i \<in> I})"

syntax
  "_coprod_final_sink":: "pttrn \<Rightarrow>'i set \<Rightarrow> ('i \<Rightarrow> 'a measure) \<Rightarrow> ('i \<times> 'a) measure"("(3\<amalg>\<^sub>M _\<in>_./ _)"10)
translations
  "\<amalg>\<^sub>M i\<in>I. M"\<rightleftharpoons>"CONST coprod_final_sink I (\<lambda>i. M)"

lemma coProj_measurable[measurable]:
  assumes "i \<in> I"
  shows "coProj i \<in> M i \<rightarrow>\<^sub>M (\<amalg>\<^sub>M i\<in>I. M i)"
  unfolding coprod_final_sink_def
proof(rule measurable_final_sink1)
  show "\<forall>(g, N)\<in>{(coProj i, M i) |i. i \<in> I}. g \<in> space N \<rightarrow> (SIGMA i:I. space (M i))"
    using coProj_function by force
  show "(coProj i, M i) \<in> {(coProj i, M i) |i. i \<in> I}"
    using assms by auto
qed

lemma coTuple_measurable [measurable(raw)]:
  assumes "\<forall> i \<in> I. F i \<in> (M i)  \<rightarrow>\<^sub>M N"
  shows "coTuple I (\<lambda> i. space (M i)) F \<in> (\<amalg>\<^sub>M i\<in>I. M i) \<rightarrow>\<^sub>M N"
  unfolding coprod_final_sink_def
proof(rule measurable_final_sink2)
  show "coTuple I (\<lambda>i. space (M i)) F \<in> (SIGMA i:I. space (M i)) \<rightarrow> space N"
    using assms by(auto simp: coTuple_function measurable_iff_sets)
  show "\<forall>(g, N)\<in>{(coProj i, M i) |i. i \<in> I}. g \<in> space N \<rightarrow> (SIGMA i:I. space (M i))"
    using coProj_function by (auto simp add: Sigma_def coProj_def)
  show "\<forall>(g, K)\<in>{(coProj i, M i) |i. i \<in> I}. (\<lambda>x. coTuple I (\<lambda>i. space (M i)) F (g x)) \<in> K \<rightarrow>\<^sub>M N"
    using assms by (auto simp add: coTuple_def coProj_def)
qed

proposition coprod_measurable_iff:
  shows "\<And> f. (f \<in> (\<amalg>\<^sub>M i\<in>I. M i) \<rightarrow>\<^sub>M N) \<longleftrightarrow> (\<forall> i\<in> I. (f o coProj i) \<in> M i \<rightarrow>\<^sub>M N)"
proof
  fix f assume f1: "f \<in> coprod_final_sink I M \<rightarrow>\<^sub>M N"
  thus"\<forall>i\<in>I. f \<circ> coProj i \<in> M i \<rightarrow>\<^sub>M N"
    using f1 coProj_measurable by auto
next fix f assume f2: "\<forall>i\<in>I. f \<circ> coProj i \<in> M i \<rightarrow>\<^sub>M N"
  hence *: "(coTuple I (\<lambda> i. space (M i)) (\<lambda> i \<in> I. (f \<circ> coProj i))) \<in> coprod_final_sink I M \<rightarrow>\<^sub>M N"
    by auto
  have "\<forall> (n,h) \<in> space (\<amalg>\<^sub>M i\<in>I. M i). f (n,h) = coTuple I (\<lambda> i. space (M i)) (\<lambda> i \<in> I. (f \<circ> coProj i)) (n,h)"
    unfolding coprod_final_sink_def space_final_sink
    by(rule coTuple_unique, auto)
  with * show "f \<in> coprod_final_sink I M \<rightarrow>\<^sub>M N"
    using measurable_cong_simp by fastforce
qed

lemma space_coprod_final_sink:
  shows "space (coprod_final_sink I M) = (SIGMA i:I. space (M i))"
  by(auto simp: coprod_final_sink_def)

lemma sets_coprod_final_sink_gen:
  shows "i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow> j \<in> I \<Longrightarrow>coProj j -` ({i} \<times> A) \<inter> space (M j) \<in> sets (M j)"
  by(cases"j = i",auto simp:  coProj_def)

lemma sets_coprod_final_sink_section[measurable(raw)]:
  shows "i \<in> I \<Longrightarrow> A \<in> sets (M i) \<Longrightarrow>({i} \<times> A) \<in> sets (coprod_final_sink I M)"
proof
  fix i A assume i: "i \<in> I"and Ai: "A \<in> sets (M i)"
  hence "A \<subseteq> space (M i)"
    by (auto simp: sets.sets_into_space)
  hence cond1: "{i} \<times> A \<in> Pow (SIGMA i:I. space (M i))"
    unfolding Sigma_def using i by auto
  from sets_coprod_final_sink_gen[of i I A M,OF i,OF Ai] have
    cond2: "(\<forall>(g, N)\<in>{(coProj i, M i) |i. i \<in> I}. g -` ({i} \<times> A) \<inter> space N \<in> sets N)"
    by blast
  from cond1 cond2 show "{i} \<times> A \<in> sets (coprod_final_sink I M)"
    unfolding coprod_final_sink_def sets_final_sink by auto
qed(auto)

lemma sets_coprod_final_sink_partition:
  assumes A: "A \<in> sets (coprod_final_sink I M)"
  shows "(\<forall> i \<in> I. {c | c. (i,c) \<in> A \<and> c \<in> space (M i)} \<in> sets (M i))"
    and "A = \<Union> ((\<lambda> i. {i} \<times> {c | c. (i,c) \<in> A \<and> c \<in> space (M i)}) ` I)"
proof
  fix i assume i: "i \<in> I"
  have "{c |c. (i, c) \<in> A \<and> c \<in> space (M i)} = coProj i -` A \<inter> space (M i)"
    by (auto simp: Collect_conj_eq vimage_def coProj_def)
  also have "...\<in> sets (M i)"
    by (meson assms coProj_measurable i measurable_sets)
  finally show "{c |c. (i, c) \<in> A \<and> c \<in> space (M i)} \<in> sets (M i)".
next
  have "A \<subseteq> space (coprod_final_sink I M)"
    using A sets.sets_into_space by blast
  also have "... = {(i,c) |i c. i \<in> I \<and> c \<in> space (M i)}"
    unfolding coprod_final_sink_def space_final_sink
    by (auto simp add: Sigma_def)
  finally have "A \<subseteq> {(i,c) |i c. i \<in> I \<and> c \<in> space (M i)}".
  thus"A = \<Union> ((\<lambda> i. {i} \<times> {c | c. (i,c) \<in> A \<and> c \<in> space (M i)}) ` I)"
    by auto
qed

proposition sets_coprod_final_sink:
  assumes I: "countable I"
  shows "sets (coprod_final_sink I M) = sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
proof
  show "sets (coprod_final_sink I M) \<subseteq> sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
  proof
    fix A assume "A \<in> sets (coprod_final_sink I M)"
    hence measAi: "(\<forall> i \<in> I. {c | c. (i,c) \<in> A \<and> c \<in> space (M i)} \<in> sets (M i))"
      and UnionAi: "A = \<Union> ((\<lambda> i. {i} \<times> {c | c. (i,c) \<in> A \<and> c \<in> space (M i)}) ` I)"
      using sets_coprod_final_sink_partition [of A I M] by auto
    have measUnionAi: "\<Union> ((\<lambda> i. {i} \<times> {c | c. (i,c) \<in> A \<and> c \<in> space (M i)}) ` I) \<in> sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
    proof(intro sigma_sets_UNION)
      show "countable ((\<lambda>i. {i} \<times> {c |c. (i, c) \<in> A \<and> c \<in> space (M i)}) ` I)"
        using I by blast
      fix B assume "B \<in> (\<lambda>i. {i} \<times> {c |c. (i, c) \<in> A \<and> c \<in> space (M i)}) ` I"
      then obtain i where Bi: "i \<in> I \<and> B = {i} \<times> {c |c. (i, c) \<in> A \<and> c \<in> space (M i)}"
        by auto
      with measAi have "{i} \<times> {c |c. (i, c) \<in> A \<and> c \<in> space (M i)} \<in> {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
        by auto
      with Bi have "B \<in> {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
        by auto
      thus"B \<in> sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
        by (meson sigma_sets.Basic)
    qed
    with UnionAi show "A \<in> sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)}"
      by auto
  qed
  show "sigma_sets (SIGMA i:I. space (M i)) {{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)} \<subseteq> sets (coprod_final_sink I M)"
  proof(intro sigma_algebra.sigma_sets_subset)
    show "sigma_algebra (SIGMA i:I. space (M i)) (sets (coprod_final_sink I M))"
      unfolding coprod_final_sink_def sets_final_sink
      by (auto simp: sigma_algebra_sigma_sets subset_iff)
    {
      fix i A assume i: "i \<in> I"and Ai: "A \<in> sets(M i)"
      note sets_coprod_final_sink_section[of i I A M, OF i Ai]
    }
    thus"{{i} \<times> A |i A. i \<in> I \<and> A \<in> sets (M i)} \<subseteq> sets (coprod_final_sink I M)"
      by auto
  qed
qed

subsubsection \<open> Distributive laws between binary products and countable coproducts\<close>

text\<open> We here formalize the distributive laws between binary products and countable coproducts, that is, the measurable isomorphisms between @{term"(\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i))"} and @{term"M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)"}\<close>

definition dist_law_A  :: "'i set \<Rightarrow> ('i \<Rightarrow> 'b measure) \<Rightarrow> 'a measure \<Rightarrow> 'i \<times> 'a \<times> 'b \<Rightarrow> 'a \<times> 'i \<times> 'b"where
  "dist_law_A I N M =
  (coTuple I (\<lambda>i. space M \<times> space (N i)) (\<lambda>i. \<lambda> p. ((fst p), coProj i (snd p))))"

proposition dist_law_A_measurable[measurable]:
  shows "dist_law_A I N M \<in> (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) \<rightarrow>\<^sub>M (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))"
  unfolding dist_law_A_def space_pair_measure[THEN sym]
  by auto

lemma dist_law_A_def2:
  shows "dist_law_A I N M = (\<lambda> p. ((fst (snd p)), ((fst p) ,(snd (snd p)))))"
  unfolding coTuple_def dist_law_A_def coProj_def
  by auto

lemma dist_law_A_vimage:
  shows "dist_law_A I N M -` space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) = (space (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)))"
  unfolding dist_law_A_def2 coprod_final_sink_def space_pair_measure space_final_sink Sigma_def
  by auto

definition dist_law_B  :: "'i set \<Rightarrow> ('i \<Rightarrow> 'b measure) \<Rightarrow> 'a measure \<Rightarrow> 'a \<times> 'i \<times> 'b \<Rightarrow> 'i \<times> 'a \<times> 'b"where
  "dist_law_B I N M = (\<lambda> p. ((fst (snd p)), ((fst p) ,(snd (snd p)))))"

lemma dist_law_B_function:
  shows "dist_law_B I N M \<in> space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow> space (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i))"
  unfolding space_pair_measure coprod_final_sink_def space_final_sink Sigma_def dist_law_B_def
  by auto

lemma dist_law_B_vimage:
  shows "dist_law_B I N M -` (space (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i))) = space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))"
  unfolding space_pair_measure coprod_final_sink_def space_final_sink Sigma_def dist_law_B_def
  by auto

lemma dist_laws_mutually_inverse:
  shows "\<And>x. (dist_law_A I N M o dist_law_B I N M) x = x"
    and "\<And>y. (dist_law_B I N M o dist_law_A I N M) y = y"
  unfolding dist_law_B_def
  by(auto simp add:dist_law_A_def2)

lemma sets_generator_product_of_M_and_coprodNi:
  assumes I: "countable I"
  shows "sets (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) = sigma_sets (space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))) {A \<times> ({i} \<times> B) | A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)}"
proof
  have "{A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)} \<subseteq> sets (M \<Otimes>\<^sub>M coprod_final_sink I N)"
  proof(clarify)
    fix A i B assume "A \<in> sets M""i \<in> I""B \<in> sets (N i)"
    hence "A \<in> sets M""{i} \<times> B \<in> sets (coprod_final_sink I N)"
      using sets_coprod_final_sink_section by auto
    thus"A \<times> {i} \<times> B \<in> sets (M \<Otimes>\<^sub>M coprod_final_sink I N)"
      by auto
  qed
  thus"sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)} \<subseteq> sets (M \<Otimes>\<^sub>M coprod_final_sink I N)"
    by (auto simp: sets.sigma_sets_subset)
  show "sets (M \<Otimes>\<^sub>M coprod_final_sink I N) \<subseteq> sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
  proof
    {
      fix C assume "C \<in> sigma_sets (space M \<times> space (coprod_final_sink I N)){A \<times> D | A D . A \<in> sets M \<and> D \<in> sets (coprod_final_sink I N)}"
      hence "C \<in> sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      proof(induction C)
        case (Basic a)
        then obtain A D where *: "a = A \<times> D \<and> A \<in> sets M \<and> D \<in> sets (coprod_final_sink I N)"
          by auto
        hence measDi: "(\<forall> i \<in> I. {c | c. (i,c) \<in> D \<and> c \<in> space (N i)} \<in> sets (N i))"
          using sets_coprod_final_sink_partition(1) by force
        from * have unionDi: "D = \<Union> ((\<lambda> i. {i} \<times> {c | c. (i,c) \<in> D \<and> c \<in> space (N i)}) ` I)"
          using sets_coprod_final_sink_partition(2) by force
        with * have "a = \<Union> ((\<lambda> i. A \<times> ({i} \<times> {c | c. (i,c) \<in> D \<and> c \<in> space (N i)}))` I)"
          by(auto intro: set_eqI)
        also have "... \<in> sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
        proof(intro sigma_sets_UNION)
          show "countable ((\<lambda>i. A \<times> {i} \<times> {c |c. (i, c) \<in> D \<and> c \<in> space (N i)}) ` I)"
            using I by blast
          show "\<And>C. C \<in> (\<lambda>i. A \<times> {i} \<times> {c |c. (i, c) \<in> D \<and> c \<in> space (N i)}) ` I \<Longrightarrow> C \<in> sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
            using measDi * by blast
        qed
        finally show ?case.
      next
        case Empty
        thus ?case
          using sigma_sets.Empty by auto
      next
        case (Compl a)
        thus ?case
          unfolding space_pair_measure
          using sigma_sets.Compl by blast
      next
        case (Union a)
        thus ?case
          unfolding space_pair_measure
          using sigma_sets.Union by blast
      qed
    }
    thus "\<And>x. x \<in> sets (M \<Otimes>\<^sub>M coprod_final_sink I N) \<Longrightarrow> x \<in> sigma_sets (space (M \<Otimes>\<^sub>M coprod_final_sink I N)) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      unfolding sets_pair_measure by auto
  qed
qed

lemma sets_generator_coproduct_of_prod_M_Ni:
  assumes I: "countable I"
  shows "sets (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)) = sigma_sets (space (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i))) {{i} \<times> (A \<times> B) | A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)}"
proof
  have "{{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)} \<subseteq> sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)"
  proof(clarify)
    fix A i B assume "A \<in> sets M""i \<in> I""B \<in> sets (N i)"
    thus"{i} \<times> A \<times> B \<in> sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)"
      by (auto simp: sets_coprod_final_sink_section)
  qed
  thus"sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)} \<subseteq> sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)"
    by (meson sets.sigma_sets_subset)
  {
    fix i assume i: "i \<in> I"
    fix D assume Di: "D \<in> sigma_sets (space (M \<Otimes>\<^sub>M N i)) {A \<times> B | A B. A \<in> sets M \<and> B \<in> sets (N i)}"
    hence "{i} \<times> D \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    proof(induction D)
      case (Basic a)
      thus ?case
        using i by auto
    next
      case Empty
      thus ?case
        using sigma_sets.Empty by auto
    next
      case (Compl a)
      hence "{i} \<times> (space (M \<Otimes>\<^sub>M N i) - a) = ({i} \<times> (space (M \<Otimes>\<^sub>M N i))) - ({i} \<times> a)"
        by blast
      also have "... \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      proof(intro ring_of_sets.Diff)
        have "sigma_algebra (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) (sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)})"
          unfolding space_pair_measure coprod_final_sink_def space_final_sink
        proof(intro sigma_algebra_sigma_sets subsetI)
          fix W assume "W \<in> {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
          then obtain A i B where *: "W = {i} \<times> A \<times> B \<and>A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)"
            by blast
          hence "W \<subseteq> {(i, a) |i a. i \<in> I \<and> a \<in> space M \<times> space (N i)}"
          proof(intro subsetI)
            {
              fix i a b assume W: "(i,a,b) \<in> W"
              hence "(a \<in> A) \<and> (i \<in> I) \<and> (b \<in> B)"
                using * by auto
              hence "(a \<in> space M) \<and> (i \<in> I) \<and> (b \<in> space (N i))"
                using * by (metis SigmaD1 W sets.sets_into_space singletonD subsetD)
              hence "(i,a,b) \<in>{(i, a) |i a. i \<in> I \<and> a \<in> space M \<times> space (N i)}"
                by auto
            }
            thus"\<And>x. x \<in> W \<Longrightarrow> x \<in> {(i, a) |i a. i \<in> I \<and> a \<in> space M \<times> space (N i)}"
              by auto
          qed
          thus"W \<in> Pow (SIGMA i:I. space M \<times> space (N i))"
            by auto
        qed
        thus"ring_of_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) (sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)})"
          using algebra.axioms(1) sigma_algebra_def by blast
        show "{i} \<times> space (M \<Otimes>\<^sub>M N i) \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
          unfolding space_pair_measure using i by blast
        show "{i} \<times> a \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
          using local.Compl by blast
      qed
      finally show ?case.
    next
      case (Union a)
      have "{i} \<times> \<Union> (range a) = \<Union> (range (\<lambda> n :: nat. {i} \<times> (a n)))"
        by auto
      also have "... \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
        using sigma_sets.Union local.Union
        by (auto simp: sigma_sets.Union local.Union)
      finally show ?case .
    qed
  }
  hence "\<forall> i \<in> I. \<forall> D \<in> sigma_sets (space (M \<Otimes>\<^sub>M N i)) {A \<times> B |A B. A \<in> sets M \<and> B \<in> sets (N i)}. {i} \<times> D
 \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    by auto
  hence "{{i} \<times> D |i D. i \<in> I \<and> D \<in> sets (M \<Otimes>\<^sub>M N i)} \<subseteq> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    unfolding sets_pair_measure space_pair_measure by auto
  hence eq: "sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> D |i D. i \<in> I \<and> D \<in> sets (M \<Otimes>\<^sub>M N i)} \<subseteq> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    by (auto simp: sigma_sets_mono)
  have eq2: "sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) = sigma_sets (SIGMA i:I. space (M \<Otimes>\<^sub>M N i)) {{i} \<times> D |i D. i \<in> I \<and> D \<in> sets (M \<Otimes>\<^sub>M N i)}"
    by(intro sets_coprod_final_sink I)
  from eq eq2 show "sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) \<subseteq> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    unfolding coprod_final_sink_def space_final_sink by auto
qed

proposition dist_law_B_measurable [measurable(raw)]:
  assumes I: "countable I"
  shows "dist_law_B I N M \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow>\<^sub>M (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i))"
proof(rule measurableI)
  show "\<And>x. x \<in> space (M \<Otimes>\<^sub>M coprod_final_sink I N) \<Longrightarrow> dist_law_B I N M x \<in> space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)"
    unfolding space_pair_measure coprod_final_sink_def space_final_sink Sigma_def dist_law_B_def
    by auto
  show "\<And>A. A \<in> sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) \<Longrightarrow> dist_law_B I N M -` A \<inter> space (M \<Otimes>\<^sub>M coprod_final_sink I N) \<in> sets (M \<Otimes>\<^sub>M coprod_final_sink I N)"
  proof
    have "\<And> A i B. (A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)) \<Longrightarrow> dist_law_B I N M -` ({i} \<times> (A \<times> B)) = A \<times> {i} \<times> B"
      unfolding dist_law_B_def by auto
    hence "\<And>D. D \<in> {{i} \<times> (A \<times> B) | A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)} \<Longrightarrow> dist_law_B I N M -` D \<in> {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      by blast
    hence baseD: "\<And>D. D \<in> {{i} \<times> (A \<times> B) | A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)} \<Longrightarrow> dist_law_B I N M -` D \<in> sigma_sets (space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      by auto
    have Dgen: "\<And>D. D \<in> sigma_sets (space ((\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i))) {{i} \<times> (A \<times> B) | A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets(N i)} \<Longrightarrow> (dist_law_B I N M -` D) \<in> sigma_sets (space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
    proof-
      fix D assume D: "D \<in> sigma_sets (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i)) {{i} \<times> A \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      thus"dist_law_B I N M -` D \<in> sigma_sets (space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i))) {A \<times> {i} \<times> B |A i B. A \<in> sets M \<and> i \<in> I \<and> B \<in> sets (N i)}"
      proof(induct)
        case (Basic a)
        thus ?case using baseD by auto
      next
        case Empty
        thus ?case using sigma_sets.Empty by auto
      next
        case (Compl a)
        have "dist_law_B I N M -` (space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) - a) = (space (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)))- (dist_law_B I N M -` a)"
          using dist_law_B_vimage by blast
        thus ?case
          by (metis (mono_tags, lifting) Compl.hyps(2) sigma_sets.Compl)
      next
        case (Union a)
        have "(dist_law_B I N M -` \<Union> (range a)) = (\<Union> i :: nat. (dist_law_B I N M -` (a i)))"
          by auto
        thus ?case
          by (metis (mono_tags, lifting) sigma_sets.Union local.Union(2))
      qed
    qed
    show "\<And>A. A \<in> sets (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i) \<Longrightarrow> dist_law_B I N M -` A \<in> sets (M \<Otimes>\<^sub>M coprod_final_sink I N)"
      using sets_generator_product_of_M_and_coprodNi[of I M N, OF I] sets_generator_coproduct_of_prod_M_Ni[of I M N, OF I] Dgen
      by blast
  qed(auto)
qed

proposition measurable_iff_dist_laws:
  assumes I: "countable I"
  shows measurable_iff_dist_law_A: "\<And>f. (f \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow>\<^sub>M K) \<longleftrightarrow> ((f o dist_law_A I N M) \<in> (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)) \<rightarrow>\<^sub>M K)"
    and measurable_iff_dist_law_B: "\<And>f. (f \<in> (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)) \<rightarrow>\<^sub>M K) \<longleftrightarrow> ((f o dist_law_B I N M) \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow>\<^sub>M K)"
proof-
  have A: "\<forall>x\<in>space (\<amalg>\<^sub>M i\<in>I. M \<Otimes>\<^sub>M N i). dist_law_B I N M (dist_law_A I N M x) = x"
    and B: "\<forall>y\<in>space (M \<Otimes>\<^sub>M coprod_final_sink I N). dist_law_A I N M (dist_law_B I N M y) = y"
    using dist_laws_mutually_inverse by auto
  show "\<And>f. (f \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow>\<^sub>M K) \<longleftrightarrow> ((f o dist_law_A I N M) \<in> (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)) \<rightarrow>\<^sub>M K)"
    and "\<And>f. (f \<in> (\<amalg>\<^sub>M i\<in>I. (M \<Otimes>\<^sub>M N i)) \<rightarrow>\<^sub>M K) \<longleftrightarrow> ((f o dist_law_B I N M) \<in> (M \<Otimes>\<^sub>M (\<amalg>\<^sub>M i\<in>I. N i)) \<rightarrow>\<^sub>M K)"
    using measurable_isomorphism_iff(1,2)[OF dist_law_A_measurable dist_law_B_measurable[OF I] A B ]
    by auto
qed

subsection \<open> Binary coproduct (disjoint union, direct sum) space defined with final lifts \<close>

text \<open>We can define binary coproduct of measurable space, but it is rather ugly. It might be better to formalize them directly.\<close>

subsubsection \<open> The "union"of two \<open>\<sigma>\<close>-algebras \<close>

definition union_final_sink :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure"where
  "union_final_sink M1 M2 = final_sink ((space M1) \<union> (space M2)) {(id,M1),(id,M2)}"

lemma space_union_final_sink[simp]:
  shows "space(union_final_sink M1 M2) = (space M1) \<union> (space M2)"
  unfolding union_final_sink_def by auto

lemma union_final_sink_sym:
  shows "union_final_sink M1 M2 = union_final_sink M2 M1"
  unfolding union_final_sink_def by(intro final_sink_cong,auto)

paragraph \<open> The "union"of two disjoint \<open>\<sigma>\<close>-algebras \<close>

lemma restrict_space_sets_cong2:
  shows "(A \<inter> space M) = (B \<inter> space N) \<Longrightarrow> sets M = sets N \<Longrightarrow> sets (restrict_space M A) = sets (restrict_space N B)"
proof-
  have eq1: "sets (restrict_space M A) = sets (restrict_space M (A \<inter> space M))"
    by (metis image_cong inf_assoc sets.Int_space_eq1 sets_restrict_space)
  have eq2: "sets (restrict_space N B) = sets (restrict_space N (B \<inter> space N))"
    by (metis image_cong inf_assoc sets.Int_space_eq1 sets_restrict_space)
  show "(A \<inter> space M) = (B \<inter> space N) \<Longrightarrow> sets M = sets N \<Longrightarrow> sets (restrict_space M A) = sets (restrict_space N B)"
    unfolding eq1 eq2 by (rule restrict_space_sets_cong)
qed

context
  fixes M1 M2::"'a measure"
  assumes disj: "(space M1) \<inter> (space M2) = {}"
begin

lemma sets_union_final_sink_disjoint:
  shows "sets (union_final_sink M1 M2) = {A \<union> B | A B. A \<in> sets M1 \<and> B \<in> sets M2}"
  unfolding union_final_sink_def
proof(subst sets_final_sink')
  show "\<forall>(g, N)\<in>{(id, M1), (id, M2)}. g \<in> space N \<rightarrow> space M1 \<union> space M2"by auto
  show "{A |A. A \<in> Pow (space M1 \<union> space M2) \<and> (\<forall>(g, N)\<in>{(id, M1), (id, M2)}. g -` A \<inter> space N \<in> sets N)} = {A \<union> B |A B. A \<in> sets M1 \<and> B \<in> sets M2}"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> {A |A. A \<in> Pow (space M1 \<union> space M2) \<and> (\<forall>(g, N)\<in>{(id, M1), (id, M2)}. g -` A \<inter> space N \<in> sets N)}"
    then have "x \<inter> space M1 \<in> sets M1" and "x \<inter> space M2 \<in> sets M2"and "x = (x \<inter> space M1) \<union> (x \<inter> space M2)"by auto
    thus  "x \<in> {A \<union> B |A B. A \<in> sets M1 \<and> B \<in> sets M2}"by auto
  next fix x assume "x \<in> {A \<union> B |A B. A \<in> sets M1 \<and> B \<in> sets M2}"
    then obtain A B where x: "x = A \<union> B"and A: "A \<in> sets M1"and B: "B \<in> sets M2"by auto
    hence x2: "x \<in> Pow (space M1 \<union> space M2)"
      by (metis PowI sets.sets_into_space sup_mono)
    from x A B disj have "(x \<inter> space M1) = A"
      by (metis (full_types) inf_assoc inf_bot_right inf_commute inf_sup_distrib2 sets.Int_space_eq2 sup_bot_right)
    with A have A2: "x \<inter> space M1 \<in> sets M1"by auto
    from x A B disj have "(x \<inter> space M2) = B"
      by (metis Int_assoc Un_empty_left boolean_algebra.conj_disj_distrib2 boolean_algebra.conj_zero_right sets.Int_space_eq2)
    with B have B2: "x \<inter> space M2 \<in> sets M2"by auto
    from x2 A2 B2
    show "x \<in> {A |A. A \<in> Pow (space M1 \<union> space M2) \<and> (\<forall>(g, N)\<in>{(id, M1), (id, M2)}. g -` A \<inter> space N \<in> sets N)}"
      by auto
  qed
qed

lemma union_final_sink_restricted_space_disjoint:
  shows "sets(restrict_space (union_final_sink M1 M2)  {x. x \<in> space M1} ) = (sets M1)"
proof(subst sets_restrict_space,subst sets_union_final_sink_disjoint )
  have "(\<inter>)  {x. x \<in> space M1} ` {A \<union> B |A B. A \<in> sets M1 \<and> B \<in> sets M2} = {(space M1) \<inter> (A \<union> B) |A B. A \<in> sets M1 \<and> B \<in> sets M2}"by auto
  also have "... = (sets M1)"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> {space M1 \<inter> (A \<union> B) |A B. A \<in> sets M1 \<and> B \<in> sets M2}"
    then obtain A B where x: "x = space M1 \<inter> (A \<union> B)"and A: "A \<in> sets M1" and "B \<in> sets M2"
      by auto
    with disj have B2: "(space M1) \<inter> B = {}"
      by (metis Int_empty_right Int_left_commute sets.Int_space_eq2)
    with x A have "x = A"
      by (auto simp: Int_Un_distrib)
    with A show "x \<in> (sets M1)"by auto
  next show "\<And>x. x \<in> (sets M1) \<Longrightarrow> x \<in> {space M1 \<inter> (A \<union> B) |A B. A \<in> sets M1 \<and> B \<in> sets M2}"
      by (metis (mono_tags, lifting) Un_empty_right mem_Collect_eq sets.Int_space_eq1 sets.empty_sets)
  qed
  finally show "(\<inter>)  {x. x \<in> space M1} ` {A \<union> B |A B. A \<in> sets M1 \<and> B \<in> sets M2} = sets M1".
qed

lemma union_final_sink_restricted_space_disjoint':
  shows "sets(restrict_space (union_final_sink M1 M2) {x. x \<in> space M2}) = (sets M2)"
  using union_final_sink_sym[of"M1""M2"] union_final_sink_restricted_space_disjoint
  by (metis Int_commute Source_and_Sink_Algebras_Constructions.union_final_sink_restricted_space_disjoint disj)

lemma measurable_inclusion_union_final_sink_restricted_space_disjoint:
  shows "id \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M1} \<rightarrow>\<^sub>M M1"
  using union_final_sink_restricted_space_disjoint measurable_cong_sets measurable_ident
  by blast

lemma measurable_inclusion_union_final_sink_restricted_space_disjoint2:
  shows "id \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M2} \<rightarrow>\<^sub>M M2"
  using union_final_sink_restricted_space_disjoint' measurable_cong_sets measurable_ident
  by blast

lemma measurable_if_union_final_sink_disjoint:
  assumes "f \<in> M1 \<rightarrow>\<^sub>M N"
    and "g \<in> M2 \<rightarrow>\<^sub>M N"
  shows "(\<lambda>x. if (x \<in> space M1) then f x else g x) \<in> (union_final_sink M1 M2) \<rightarrow>\<^sub>M N"
  using assms
proof(subst measurable_If_restrict_space_iff)
  have eq1: "{x \<in> space (union_final_sink M1 M2). x \<in> space M1} = space M1"
    unfolding space_union_final_sink by auto
  have in1: "{x. (x \<in> space M1 \<or> x \<in> space M2) \<and> x \<in> space M1} \<inter> space M1 \<in> sets M1"
    using eq1 by auto
  have in2: "{x. (x \<in> space M1 \<or> x \<in> space M2) \<and> x \<in> space M1} \<inter> space M2 \<in> sets M2"
    using disj eq1 by auto
  show "{x \<in> space (union_final_sink M1 M2). x \<in> space M1} \<in> sets (union_final_sink M1 M2)"
    unfolding union_final_sink_def
    by(subst sets_final_sink',auto simp add: in1 in2)
  show "f \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M1} \<rightarrow>\<^sub>M N \<and> g \<in> restrict_space (union_final_sink M1 M2) {x. x \<notin> space M1} \<rightarrow>\<^sub>M N"
  proof(rule conjI)
    show "f \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M1} \<rightarrow>\<^sub>M N"
    proof(subst measurable_cong')
      show "f o id \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M1} \<rightarrow>\<^sub>M N"
        by(rule measurable_comp[OF measurable_inclusion_union_final_sink_restricted_space_disjoint assms(1)])
    qed(auto)
    show "g \<in> restrict_space (union_final_sink M1 M2) {x. x \<notin> space M1} \<rightarrow>\<^sub>M N"
    proof(subst measurable_cong_simp)
      have eq1: "sets (restrict_space (union_final_sink M1 M2) {x. x \<notin> space M1}) = sets (restrict_space (union_final_sink M1 M2) {x. x \<in> space M2})"
        using disj by(intro restrict_space_sets_cong2,auto)
      thus"restrict_space (union_final_sink M1 M2) {x. x \<notin> space M1} = (restrict_space (union_final_sink M1 M2) {x. x \<in> space M2})"
        unfolding restrict_space_def using eq1 by (metis sets_eq_imp_space_eq sets_restrict_space space_restrict_space)
      show "g \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M2} \<rightarrow>\<^sub>M N"
      proof(subst measurable_cong')
        show "g o id \<in> restrict_space (union_final_sink M1 M2) {x. x \<in> space M2} \<rightarrow>\<^sub>M N"
          by(rule measurable_comp[OF measurable_inclusion_union_final_sink_restricted_space_disjoint2 assms(2)])
      qed(auto)
    qed(auto)
  qed
qed

end (*end of context*)

subsubsection \<open> Binary coproduct space \<close>

text \<open> To construct the coproduct of @{term M} and @{term N}. We first embed them to the common @{typ"('a + 'b) measure"} \<close>

lemma
  shows Plus_inter: "(A <+> B) \<inter> (C <+> D) = ((A \<inter> C) <+> (B \<inter> D))"
    and Plus_union: "(A <+> B) \<union> (C <+> D) = ((A \<union> C) <+> (B \<union> D))"
  unfolding Plus_def by auto

lemma
  shows Plus_mono: "\<And>A B C D. A \<subseteq> B \<Longrightarrow> C \<subseteq> D \<Longrightarrow> A <+> C \<subseteq> B <+> D"
    and Plus_decompose: "\<And>A. A = Inl -` A <+> Inr -` A"
    and Plus_subset_decompose: "\<And>A C D. A \<subseteq> C <+> D \<Longrightarrow> (Inl -` A) \<subseteq> C \<and> (Inr -` A) \<subseteq> D"
    and vimage_inl: "\<And>A B. Inl -` (A <+> B) = A"
    and vimage_inr: "\<And>A B. Inr -` (A <+> B) = B"
  unfolding Plus_def using UNIV_sum by auto (*takes long time*)

definition Inl_final_sink :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a + 'b) measure"where
  "Inl_final_sink M N = final_sink ((space M) <+> ({} :: 'b set)) {(Inl,M)}"

lemma space_Inl_final_sink:
  "space (Inl_final_sink M N) = (space M) <+> {}"
  by(auto simp: Inl_final_sink_def)

lemma sets_Inl_final_sink:
  fixes M :: "'a measure"and N :: "'b measure"
  shows "sets (Inl_final_sink M N) = {A <+> ({} :: 'b set) | A. A \<in> sets M}"
  unfolding Inl_final_sink_def
proof(subst sets_final_sink')
  have imp: "\<And>A x. A \<in> sets M \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> space M"
    using sets.sets_into_space by auto
  show "{A |A. A \<in> Pow (space M <+> {}) \<and> (\<forall>(g, N)\<in>{(Inl, M)}. g -` A \<inter> space N \<in> sets N)} = {A <+> {} |A. A \<in> sets M}"
    by(intro set_eqI iffI)(clarify,intro exI conjI sets.sets_into_space,auto simp:imp vimage_inl vimage_inr)
qed(auto)

definition Inr_final_sink :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a + 'b) measure"where
  "Inr_final_sink M N = final_sink (({} :: 'a set) <+> (space N)) {(Inr,N)}"

lemma space_Inr_final_sink:
  shows "space (Inr_final_sink M N) = {} <+> (space N)"
  by(auto simp: Inr_final_sink_def)

lemma sets_Inr_final_sink:
  fixes M :: "'a measure"and N :: "'b measure"
  shows "sets (Inr_final_sink M N) = {({} :: 'a set) <+> A | A. A \<in> sets N}"
  unfolding Inr_final_sink_def
proof(subst sets_final_sink')
  have imp: "\<And>A y. A \<in> sets N \<Longrightarrow> y \<in> A \<Longrightarrow> y \<in> space N"
    using sets.sets_into_space by auto
  show "{A |A. A \<in> Pow ({} <+> space N) \<and> (\<forall>(g, N)\<in>{(Inr, N)}. g -` A \<inter> space N \<in> sets N)} = {{} <+> A |A. A \<in> sets N}"
    by(intro set_eqI iffI)(clarify,intro exI conjI sets.sets_into_space,auto simp:imp vimage_inl vimage_inr)
qed(auto)

definition\<^marker>\<open>tag important\<close> Plus_algebra :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a + 'b) measure"where
  "Plus_algebra M N = union_final_sink (Inl_final_sink M N) (Inr_final_sink M N)"

lemma space_Plus_algebra[simp]:
  shows "space (Plus_algebra M N) = ((space M) <+> (space N))"
  unfolding Plus_algebra_def union_final_sink_def space_final_sink Inl_final_sink_def Inr_final_sink_def by auto

lemma measurable_Inl': "Inl \<in> M \<rightarrow>\<^sub>M (Inl_final_sink M N)"
  unfolding Inl_final_sink_def
  by(rule measurable_final_sink1,auto)

lemma measurable_projl':
  shows "projl \<in> (Inl_final_sink M N) \<rightarrow>\<^sub>M M"
  unfolding Inl_final_sink_def
  by(auto intro!: measurable_final_sink2)

lemma measurable_Inr': "Inr \<in> N \<rightarrow>\<^sub>M (Inr_final_sink M N)"
  unfolding Inr_final_sink_def
  by(rule measurable_final_sink1,auto)

lemma measurable_projr':
  shows "projr \<in> (Inr_final_sink M N) \<rightarrow>\<^sub>M N"
  unfolding Inr_final_sink_def
  by(auto intro!: measurable_final_sink2)

lemma measurable_Inl[measurable]:
  shows "Inl \<in> M \<rightarrow>\<^sub>M (Plus_algebra M N)"
proof-
  have "Inl = id o Inl"
    by auto
  also have "... \<in> M \<rightarrow>\<^sub>M (Plus_algebra M N)"
    by(rule measurable_comp,auto intro: measurable_Inl' measurable_final_sink1 simp: Plus_algebra_def union_final_sink_def)
  finally show "Inl \<in> M \<rightarrow>\<^sub>M Plus_algebra M N".
qed

lemma measurable_Inr[measurable]:
  shows "Inr \<in> N \<rightarrow>\<^sub>M (Plus_algebra M N)"
proof-
  have "Inr = id o Inr"
    by auto
  also have "... \<in> N \<rightarrow>\<^sub>M (Plus_algebra M N)"
    by(rule measurable_comp,auto intro: measurable_Inr' measurable_final_sink1 simp: Plus_algebra_def union_final_sink_def)
  finally show "Inr \<in> N \<rightarrow>\<^sub>M Plus_algebra M N".
qed

lemma measurable_case_sum [measurable(raw)]:
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M K"
    and [measurable]: "g \<in> N \<rightarrow>\<^sub>M K"
  shows "case_sum f g \<in> (Plus_algebra M N) \<rightarrow>\<^sub>M K"
proof-
  note [measurable] = measurable_Inl' measurable_Inr' measurable_projl' measurable_projr'
  {
    fix w assume "w \<in> space (Plus_algebra M N)"
    then consider"(\<exists> x. x \<in> space M \<and> w = Inl x)"|"(\<exists> y. y \<in> space N \<and> w = Inr y)"
      by auto
    hence "case_sum f g w = (\<lambda>x. if (x \<in> space (Inl_final_sink M N)) then (f o projl) x else (g o projr) x) w"
      by(cases,auto simp: space_Inl_final_sink)
  }note eq1 = this
  show ?thesis
  proof(subst measurable_cong[OF eq1],clarify)
    show "(\<lambda>w. if w \<in> space (Inl_final_sink M N) then (f \<circ> projl) w else (g \<circ> projr) w) \<in> Plus_algebra M N \<rightarrow>\<^sub>M K"
      unfolding Plus_algebra_def
      by(rule measurable_if_union_final_sink_disjoint,auto simp: space_Inl_final_sink space_Inr_final_sink)
  qed
qed

lemma measurable_from_plus_algebra_iff:
  shows "(h o Inl \<in> M \<rightarrow>\<^sub>M K) \<and> (h o Inr \<in> N \<rightarrow>\<^sub>M K) \<longleftrightarrow> h \<in> (Plus_algebra M N) \<rightarrow>\<^sub>M K"
proof(rule iffI)
  assume A: "(h o Inl \<in> M \<rightarrow>\<^sub>M K) \<and> (h o Inr \<in> N \<rightarrow>\<^sub>M K)"
  have "h = case_sum (h o Inl) (h o Inr)"
    by (auto simp: case_sum_expand_Inr_pointfree)
  also have "... \<in> (Plus_algebra M N) \<rightarrow>\<^sub>M K"
    by (auto simp: A measurable_case_sum)
  finally show "h \<in> Plus_algebra M N \<rightarrow>\<^sub>M K".
next
  note [measurable] = measurable_Inl measurable_Inr
  assume A2: "h \<in> Plus_algebra M N \<rightarrow>\<^sub>M K"
  thus"h \<circ> Inl \<in> M \<rightarrow>\<^sub>M K \<and> h \<circ> Inr \<in> N \<rightarrow>\<^sub>M K"
    by(intro conjI, measurable)
qed

text \<open> It might be better to use the following \<open>\<sigma>\<close>-algebra directly. \<close>

lemma \<^marker>\<open>tag important\<close>sets_Plus_algebra:
  fixes M :: "'a measure"and N :: "'b measure"
  shows "sets (Plus_algebra M N) = {A <+> B | A B. A \<in> sets M \<and> B \<in> sets N}"
  unfolding Plus_algebra_def space_Inl_final_sink space_Inr_final_sink
proof(subst sets_union_final_sink_disjoint)
  show "space (Inl_final_sink M N) \<inter> space (Inr_final_sink M N) = {}"
    by(auto simp: space_Inl_final_sink space_Inr_final_sink)
  show "{A \<union> B |A B. A \<in> sets (Inl_final_sink M N) \<and> B \<in> sets (Inr_final_sink M N)} = {A <+> B |A B. A \<in> sets M \<and> B \<in> sets N}"
    by(rule equalityI subsetI)(auto simp: sets_Inl_final_sink sets_Inr_final_sink Plus_def)
qed

paragraph \<open> Distributive laws between binary products and binary coproducts  \<close>

lemma measurable_Plus_pair_pair_to_pair_Plus:
  shows "case_sum (\<lambda>(a,b). (Inl a,b)) (\<lambda>(a,b). (Inr a,b)) \<in> (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)) \<rightarrow>\<^sub>M ((Plus_algebra M N) \<Otimes>\<^sub>M L)  "
  by measurable

lemma sets_Plus_pair_basis:
  "sets (Plus_algebra M N \<Otimes>\<^sub>M L) = sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E | C D E. C \<in> sets M \<and> D \<in> sets N  \<and> E \<in> sets L}"
  unfolding sets_pair_measure sets_Plus_algebra space_Plus_algebra space_pair_measure
  by(rule subset_antisym)(intro sigma_sets_mono,clarify,blast)+

lemma sets_pair_Plus_basis:
  "sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)) = sigma_sets (space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))) {(C \<times> E) <+> (D \<times> F) | C D E F. C \<in> sets M \<and> D \<in> sets N  \<and> E \<in> sets L \<and> F \<in> sets L} "
  unfolding space_Plus_algebra space_pair_measure
proof(rule subset_antisym)
  let ?\<Omega> = "sigma_sets  (space M \<times> space L <+> space N \<times> space L) {(C \<times> E) <+> (D \<times> F) | C D E F. C \<in> sets M \<and> D \<in> sets N  \<and> E \<in> sets L \<and> F \<in> sets L} "
  have 1: "ring_of_sets (space M \<times> space L <+> space N \<times> space L) ?\<Omega>"
  proof(intro algebra.axioms(1) sigma_algebra.axioms(1) sigma_algebra_sigma_sets subsetI)
    fix x assume "x \<in> {C \<times> E <+> D \<times> F |C D E F. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L \<and> F \<in> sets L}"
    then obtain C D E F where "C \<in> sets M""D \<in> sets N""E \<in> sets L""F \<in> sets L "and x :"x = C \<times> E <+> D \<times> F"
      by auto
    hence "C \<subseteq> space M" "D \<subseteq> space N" "E \<subseteq> space L" "F \<subseteq> space L"
      using sets.sets_into_space by blast+
    thus "x \<in> Pow (space M \<times> space L <+> space N \<times> space L)"unfolding x by auto
  qed

  show "sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)) \<subseteq> ?\<Omega>"
    unfolding sets_Plus_algebra space_Plus_algebra space_pair_measure  sets_pair_measure
  proof(intro subsetI,clarify)
    fix A B assume A: "A \<in> sigma_sets (space M \<times> space L) {C \<times> D |C D. C \<in> sets M \<and> D \<in> sets L}"and B: "B \<in> sigma_sets (space N \<times> space L) {C \<times> D |C D. C \<in> sets N \<and> D \<in> sets L}"
    from A have A2: "A <+> {}  \<in> ?\<Omega>"
    proof(induct A rule: sigma_sets.induct)
      case (Basic a)
      then show ?case
        by (blast intro: Sigma_empty1)
    next
      case Empty
      then show ?case
        by (auto simp: Plus_def sigma_sets.Empty)
    next
      case (Compl a)
      have "(space M \<times> space L - a) <+> {} =  ((space M \<times> space L ) <+> {}) -(a <+> {}) "
        by auto
      also have "... \<in> ?\<Omega>"
      proof(intro ring_of_sets.Diff)
        show "space M \<times> space L <+> {} \<in>  ?\<Omega>"
          by blast
      qed(fact+)
      finally show ?case .
    next
      case (Union a)
      have "\<Union> (range a) <+> {}  = \<Union> { a i <+> {} | i::nat. i \<in> UNIV} "by auto
      also have "...  \<in> ?\<Omega>"
      proof(rule sigma_sets_UNION)
        show "countable {a i <+> {} |i. i \<in> UNIV}"
          by (metis Setcompr_eq_image uncountable_def)
      qed(auto simp: Union)
      finally show ?case .
    qed

    from B have B2: "{} <+> B \<in> ?\<Omega>"
    proof(induct B rule: sigma_sets.induct)
      case (Basic a)
      then show ?case
        by (blast intro: Sigma_empty1)
    next
      case Empty
      then show ?case unfolding Plus_def
        by (auto simp: sigma_sets.Empty)
    next
      case (Compl a)
      have "{} <+> (space N \<times> space L - a) =  ({} <+> (space N \<times> space L )) -({} <+> a) "
        by auto
      also have "... \<in>  ?\<Omega>"
      proof(rule ring_of_sets.Diff)
        show "{} <+> space N \<times> space L \<in>  ?\<Omega>"
          by blast
      qed(fact+)
      finally show ?case .
    next
      case (Union a)
      have "{} <+> \<Union> (range a)  = \<Union> {{} <+> a i | i::nat. i \<in> UNIV} "by auto
      also have "...  \<in>  ?\<Omega>"
      proof(rule sigma_sets_UNION)
        show "countable {{} <+> a i |i. i \<in> UNIV}"
          by (metis Setcompr_eq_image uncountable_def)
      qed (auto simp: Union)
      finally show ?case .
    qed
    from A2 B2
    have "A <+> B = (A <+> {}) \<union> ({} <+> B)"by auto
    also have "... \<in>  ?\<Omega>"
      by(rule sigma_sets_Un, auto simp: A2 B2)
    finally show "A <+> B \<in> ?\<Omega>".
  qed

  show "?\<Omega> \<subseteq> sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
  proof(intro subsetI)
    fix x assume "x \<in> ?\<Omega>"
    then show "x \<in>  sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
    proof (induct x rule: sigma_sets.induct)
      case (Basic a)
      then obtain C E D F where a: "a = C \<times> E <+> D \<times> F"and "C \<in> sets M""D \<in> sets N""E \<in> sets L""F \<in> sets L"
        by auto
      hence "C \<times> E \<in> sigma_sets (space M \<times> space L) {a \<times> b |a b. a \<in> sets M \<and> b \<in> sets L}""D \<times> F\<in> sigma_sets (space N \<times> space L) {a \<times> b |a b. a \<in> sets N \<and> b \<in> sets L}"
        by auto
      then show ?case unfolding a sets_Plus_algebra sets_pair_measure space_Plus_algebra space_pair_measure by auto
    next
      case Empty
      then show ?case by blast
    next
      case (Compl a)
      then show ?case
      proof(intro ring_of_sets.Diff)
        show "space M \<times> space L <+> space N \<times> space L \<in> sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
          unfolding sets_Plus_algebra sets_pair_measure space_Plus_algebra space_pair_measure by blast
        show "ring_of_sets (space M \<times> space L <+> space N \<times> space L) (sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)))"
          by(intro algebra.axioms(1) sigma_algebra.axioms(1)) (metis sets.sigma_algebra_axioms space_Plus_algebra space_pair_measure)
      qed(auto)
    next
      case (Union a)
      then show ?case by auto
    qed
  qed
qed

lemma vimage_map_sum:
  shows "(map_sum f g) -` (A <+> B) = (f -` A) <+> (g -` B)"
proof
  let ?f = "(map_sum f g)"
  show "?f -` (A <+> B) \<subseteq> f -` A <+> g -` B"
  proof(rule subsetI,unfold vimage_eq)
    fix x::"('a + 'b)"assume xin: "?f x \<in> A <+> B"
    then have P: "(\<exists> a::'a. x = (Inl a)) \<or> (\<exists> a::'b. x = (Inr a))"
      using sum.exhaust_sel by blast
    consider  "(\<exists> a::'a.  x = (Inl a))"| "(\<exists> a::'b. x = (Inr a))"
      using P by auto
    then show "x \<in> f -` A <+> g -` B"
      using xin by(cases, force+)
  qed
  show "f -` A <+> g -` B \<subseteq> map_sum f g -` (A <+> B)"
    by auto
qed

lemma measurable_pair_Plus_to_Plus_pair_pair:
  shows "(\<lambda>(a::'a +'b, b::'c).  case a of Inl x \<Rightarrow> Inl (x, b) | Inr x \<Rightarrow> Inr (x, b)) \<in> ((Plus_algebra M N) \<Otimes>\<^sub>M L) \<rightarrow>\<^sub>M (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
    (is "?f  \<in> ((Plus_algebra M N) \<Otimes>\<^sub>M L) \<rightarrow>\<^sub>M (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))")
proof(rule measurableI)
  have feq: "?f -` space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))  = space (Plus_algebra M N \<Otimes>\<^sub>M L)"
    unfolding  space_Plus_algebra space_pair_measure
  proof(intro set_eqI iffI;unfold vimage_eq)
    fix x::"('a + 'b) \<times> 'c"assume xin: "?f x \<in> space M \<times> space L <+> space N \<times> space L"
    then have P: "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b)) \<or> (\<exists> a::'b. \<exists> b::'c. x = (Inr a, b)) "
      by (metis prod.exhaust_sel sum.exhaust_sel)
    consider  "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b))"| "(\<exists> a::'b. \<exists> b::'c. x = (Inr a, b))"
      using P by auto
    then show "x \<in> (space M <+> space N) \<times> space L"
      using xin by(cases,force+)
  next fix x assume xin: "x \<in> (space M <+> space N) \<times> space L"
    then have P: "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b)) \<or> (\<exists> a::'b. \<exists> b::'c. x = (Inr a, b)) "
      by (metis prod.exhaust_sel sum.exhaust_sel)
    consider  "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b))"| "(\<exists> a::'b. \<exists> b::'c. x = (Inr a, b))"
      using P by auto
    then show "?f x  \<in> space M \<times> space L <+> space N \<times> space L"
      using xin by(cases,force+)
  qed
  show "\<And>x. x \<in> space (Plus_algebra M N \<Otimes>\<^sub>M L) \<Longrightarrow> ?f x \<in> space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
    by (auto simp: space_pair_measure)
  fix A assume A: "A \<in> sets (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
  have "?f -` A \<inter> space (Plus_algebra M N \<Otimes>\<^sub>M L) = ?f -` A"
  proof
    show "?f -` A \<inter> space (Plus_algebra M N \<Otimes>\<^sub>M L)  \<subseteq> ?f -` A"
      by auto
    have "?f -` A \<subseteq>  space (Plus_algebra M N \<Otimes>\<^sub>M L) "
      using A sets.sets_into_space feq by blast
    thus "?f -` A \<subseteq> ?f -` A \<inter> space (Plus_algebra M N \<Otimes>\<^sub>M L)"
      by auto
  qed
  also have "... \<in> sets (Plus_algebra M N \<Otimes>\<^sub>M L)"
    using A
    unfolding sets_Plus_pair_basis sets_pair_Plus_basis comp_def
  proof(induct rule: sigma_sets.induct)
    case (Basic a)
    then obtain C D E F where C: "C \<in> sets M"and D: "D \<in> sets N"and E: "E \<in> sets L"and F: "F \<in> sets L "and a :"a = C \<times> E <+> D \<times> F"
      by auto
    have finva: "?f -` a = ((C <+> {}) \<times> E) \<union> (({} <+> D) \<times> F) "
      unfolding a
    proof(intro set_eqI iffI; unfold vimage_eq)
      fix x::"('a + 'b) \<times> 'c"assume xin: "?f x \<in> C \<times> E <+> D \<times> F"
      then have P: "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b)) \<or> (\<exists> a::'b. \<exists> b::'c. x = (Inr a, b)) "
        by (metis old.sum.exhaust surj_pair)
      consider  "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b))"| "(\<exists> a::'b. \<exists> b::'c. x = (Inr a, b))"
        using P by auto
      then show "x \<in> (C <+> {}) \<times> E \<union> ({} <+> D) \<times> F"
        using xin by(cases,force+)
    next
      fix x::"('a + 'b) \<times> 'c"assume xin: "x \<in> (C <+> {}) \<times> E \<union> ({} <+> D) \<times> F"
      then have P: "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b)) \<or> (\<exists> a::'b. \<exists> b::'c. x = (Inr a, b)) "
        by (metis old.sum.exhaust surj_pair)
      consider  "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b))"| "(\<exists> a::'b. \<exists> b::'c. x = (Inr a, b))"
        using P by auto
      then show "?f x \<in>  C \<times> E <+> D \<times> F"
        using xin by(cases,force+)
    qed
    show ?case unfolding finva
      by(intro sigma_sets_Un sigma_sets.Basic, auto intro!: C D E F)
  next
    case Empty
    then show ?case
      by (auto simp: sigma_sets.Empty)
  next
    case (Compl a)
    have "?f -` (space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)) - a) = ?f -` (space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))) - ?f -` a"
      by auto
    also have "... \<in> sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L}"
    proof(rule ring_of_sets.Diff)
      show "?f -` (space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))) \<in> sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L}"
        using feq unfolding space_Plus_algebra space_pair_measure by auto
      show "?f -` a \<in> sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L}"
        by fact
      show "ring_of_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) (sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L})"
        by(intro algebra.axioms(1) sigma_algebra.axioms(1) sigma_algebra_sigma_sets, auto simp: space_pair_measure dest!: sets.sets_into_space)
    qed
    finally show ?case .
  next
    case (Union a)
    {fix i
      have incl: "a i \<subseteq> space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L))"
      proof(rule sigma_sets_into_sp)
        show "{C \<times> E <+> D \<times> F |C D E F. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L \<and> F \<in> sets L} \<subseteq> Pow (space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)))"
          unfolding space_pair_measure space_Plus_algebra using sets.sets_into_space[of _ M] sets.sets_into_space[of _ N] sets.sets_into_space[of _ L]
          by fastforce
      qed (fact)
      hence "(\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -` a i \<subseteq> (\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -`( space (Plus_algebra (M \<Otimes>\<^sub>M L) (N \<Otimes>\<^sub>M L)))"
        by blast
      also have "... \<subseteq>  space (Plus_algebra M N \<Otimes>\<^sub>M L)"
        unfolding space_pair_measure space_Plus_algebra
      proof(rule subsetI,unfold vimage_eq)
        fix x::"('a + 'b) \<times> 'c"assume A: "(case x of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) \<in> space M \<times> space L <+> space N \<times> space L "
        then have P: "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b)) \<or> (\<exists> a::'b. \<exists> b::'c. x = (Inr a, b)) "
          by (metis prod.exhaust_sel sum.exhaust_sel)
        consider  "(\<exists> a::'a. \<exists> b::'c. x = (Inl a, b))"| "(\<exists> a::'b. \<exists> b::'c. x = (Inr a, b))"
          using P by auto
        then show "x \<in> (space M <+> space N) \<times> space L"
        proof(cases)
          case 1
          then obtain a b where x: "x = (Inl a, b)"
            by auto
          then have "(case x of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b))  = Inl (a,b)"
            by auto
          then have "a \<in> space M"and "b \<in> space L"
            using A by auto
          then show ?thesis using x by auto
        next
          case 2
          then obtain a b where x: "x = (Inr a, b)"
            by auto
          then have "(case x of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b))  = Inr (a,b)"
            by auto
          then have "a \<in> space N"and "b \<in> space L"
            using A by auto
          then show ?thesis using x by auto
        qed
      qed
      finally have incl: "(\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -` a i \<subseteq> space (Plus_algebra M N \<Otimes>\<^sub>M L)".
      hence meas:"(\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -` a i \<in> sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L}"using Union(2) by auto
      note * = incl meas
    }note * = this
    then have "(\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -` \<Union> (range a)  = \<Union> (range (\<lambda> i. (\<lambda>a. case a of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b)) -` a i))"
      by blast
    also have "... \<in> sigma_sets (space (Plus_algebra M N \<Otimes>\<^sub>M L)) {(C <+> D) \<times> E |C D E. C \<in> sets M \<and> D \<in> sets N \<and> E \<in> sets L}"
      using sigma_sets.Union *(2)
      by (metis (no_types, lifting))
    finally show ?case by blast
  qed
  finally show "?f -` A \<inter> space (Plus_algebra M N \<Otimes>\<^sub>M L)  \<in> sets (Plus_algebra M N \<Otimes>\<^sub>M L)".
qed

lemma pair_Plus_o_Plus_pair_pair_id:
  "( (\<lambda>(a::'a +'b, b::'c). case a of Inl x \<Rightarrow> Inl (x, b) | Inr x \<Rightarrow> Inr (x, b)) o case_sum (\<lambda>(a,b). (Inl a,b)) (\<lambda>(a,b). (Inr a,b)) ) = id"
  unfolding comp_def
proof
  fix x::"('a \<times>'c) + ('b \<times>'c)"
  consider "(\<exists> a c. x = Inl(a,c)) "|"(\<exists> b c. x = Inr(b,c))"
    by (metis obj_sumE surj_pair)
  thus "(case case x of Inl (a, xa) \<Rightarrow> (Inl a, xa) | Inr (a, xa) \<Rightarrow> (Inr a, xa) of (Inl x, b) \<Rightarrow> Inl (x, b) | (Inr x, b) \<Rightarrow> Inr (x, b))= id x"
    by (cases,auto)
qed

lemma Plus_pair_pair_o_pair_Plus_id:
  "(case_sum (\<lambda>(a,b). (Inl a,b)) (\<lambda>(a,b). (Inr a,b)) o  (\<lambda>(a::'a +'b, b::'c). case a of Inl x \<Rightarrow> Inl (x, b) | Inr x \<Rightarrow> Inr (x, b))) = id"
proof
  fix x::"('a +'b)  \<times>'c"
  consider "(\<exists> a c. x = (Inl a,c)) "|"(\<exists> b c. x = (Inr b,c))"
    by (metis obj_sumE surj_pair)
  thus "(case_sum (\<lambda>(a, b). (Inl a, b)) (\<lambda>(a, b). (Inr a, b)) \<circ> (\<lambda>(a, b). case a of Inl x \<Rightarrow> Inl (x, b) | Inr x \<Rightarrow> Inr (x, b))) x = id x"
    by (cases,auto)
qed

subsection \<open> Option spaces \<close>

definition None_algebra :: "('a  option) measure"where
  "None_algebra = sigma {None} {{None}}"

definition Some_final_sink :: "'a measure \<Rightarrow> ('a  option) measure"where
  "Some_final_sink M = final_sink (Some` (space M)) {(Some,M)}"

lemma sets_Some_final_sink:
  shows "sets (Some_final_sink M) = {Some `A | A. A \<in> (sets M)}"
  unfolding Some_final_sink_def
proof(subst sets_final_sink')
  show "\<forall>(g, N)\<in>{(Some, M)}. g \<in> space N \<rightarrow> Some ` space M"by auto
  show "{A |A. A \<in> Pow (Some ` space M) \<and> (\<forall>(g, N)\<in>{(Some, M)}. g -` A \<inter> space N \<in> sets N)} = {Some ` A |A. A \<in> sets M}"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> {A |A. A \<in> Pow (Some ` space M) \<and> (\<forall>(g, N)\<in>{(Some, M)}. g -` A \<inter> space N \<in> sets N)}"
    then have "x = Some ` (Some -` x)"and "Some -` x = Some -` x \<inter> space M"and 2: "Some -` x \<inter> space M \<in> sets M"
      by auto
    thus "x \<in> {Some ` A |A. A \<in> sets M}"
      by (metis (mono_tags, lifting) mem_Collect_eq)
  next fix x assume "x \<in> {Some ` A |A. A \<in> sets M}"
    then obtain A where "A \<subseteq> space M"and A: "A \<in> sets M"and "x = Some ` A"
      using sets.sets_into_space by force
    hence "x \<in> Pow (Some ` space M)"and "Some -` x  \<inter> space M  = A"
      by blast+
    with A show "x \<in> {A |A. A \<in> Pow (Some ` space M) \<and> (\<forall>(g, N)\<in>{(Some, M)}. g -` A \<inter> space N \<in> sets N)}"
      by blast
  qed
qed

definition option_final_sink:: "'a measure \<Rightarrow> ('a  option) measure"where
  "option_final_sink M =  union_final_sink (Some_final_sink M) (None_algebra)"

lemma space_option_final_sink[simp]:
  shows "space (option_final_sink M) = (Some` (space M)) \<union> {None}"
  by(auto simp:option_final_sink_def Some_final_sink_def  None_algebra_def union_final_sink_def)

lemma measurable_Some[measurable]:
  shows "Some \<in> M \<rightarrow>\<^sub>M option_final_sink M"
proof-
  have "Some = id o Some"
    by auto
  also have "... \<in> M \<rightarrow>\<^sub>M option_final_sink M"
    by(rule measurable_comp[of _ _  "Some_final_sink M"],auto simp:Some_final_sink_def option_final_sink_def union_final_sink_def)
  finally show ?thesis .
qed

lemma sets_option_final_sink:
  shows "sets (option_final_sink M) = { (Some `A ) \<union> {None} | A. A \<in> sets M} \<union> { (Some `A ) | A. A \<in> sets M}"
  unfolding option_final_sink_def
proof(subst sets_union_final_sink_disjoint)
  show "space (Some_final_sink M) \<inter> space None_algebra = {}"
    unfolding Some_final_sink_def None_algebra_def
    by auto
  show "{A \<union> B |A B. A \<in> sets (Some_final_sink M) \<and> B \<in> sets None_algebra} = {Some ` A \<union> {None} |A. A \<in> sets M} \<union> {Some ` A |A. A \<in> sets M}"
  proof(intro equalityI subsetI)
    fix x assume "x \<in> {A \<union> B |A B. A \<in> sets (Some_final_sink M) \<and> B \<in> sets None_algebra}"
    then obtain A B where x: "x = A \<union> B"and "A \<in> sets (Some_final_sink M)"and  B: "B \<in> sets None_algebra"by auto
    then obtain C where A: "A = Some `C "and C: "C \<in> (sets M)"
      by (auto simp:sets_Some_final_sink)
    from B have B: "B = {} \<or> B = {None}"
      unfolding None_algebra_def by auto
    from x A C B show "x \<in> {Some ` A \<union> {None} |A. A \<in> sets M} \<union> {Some ` A |A. A \<in> sets M}"by auto
  next fix x assume "x \<in> {Some ` A \<union> {None} |A. A \<in> sets M} \<union> {Some ` A |A. A \<in> sets M}"
    then have "x \<in>  {Some ` A \<union> {None} |A. A \<in> sets M} \<or> x \<in> {Some ` A |A. A \<in> sets M}"by auto
    thus "x \<in> {A \<union> B |A B. A \<in> sets (Some_final_sink M) \<and> B \<in> sets None_algebra} "
      by (auto simp:sets_Some_final_sink None_algebra_def)
  qed
qed

end