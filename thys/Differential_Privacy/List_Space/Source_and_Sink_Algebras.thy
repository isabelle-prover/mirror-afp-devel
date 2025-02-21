(*
 Title: Source_and_Sink_Algebras.thy
 Author: Tetsuya Sato
*)

theory Source_and_Sink_Algebras
  imports
    "HOL-Analysis.Sigma_Algebra"
    "HOL-Analysis.Measure_Space"
begin

section \<open>Meausrable Spaces form a Topological Concrete Category\<close>

text \<open> This entry is based on the fact that the category Meas of measurable spaces and measurable functions forms a topological concrete category (see also, [Brümmer, Topology Appl. 1983], [Adamek, Herrlich and Strecker,1990]), where (i) for any family of functions from a set X to measurable spaces Y(i), the coarsest \<open>\<sigma>\<close>-algebra over X retracted from the ones Y(i) (initial lift) exists and (ii) for any family of functions from measurable spaces X(i) to Y, the finest \<open>\<sigma>\<close>-algebra over Y pushed out from the one of X(i) (called final lift) exists. All limits and colimits are given by initial and final lifts respectively. Due to the type system of Isabelle/HOL, the type of family in the construction of initial and final lifts are restricted. \<close>

subsection \<open>Initial lift: the coarsest \<open>\<sigma>\<close>-algebra retracted from a family of functions \<close>

definition\<^marker>\<open>tag important\<close> initial_source :: "'a set \<Rightarrow> (('a \<Rightarrow> 'b) \<times> 'b measure) set \<Rightarrow> 'a measure" where
  "initial_source X F = sigma X {f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M}"

text \<open> Roughly speaking, @{term F} is a structured source @{term"{(f,M) | f M. (f,M) \<in> F}"} having the common domain @{term X}. @{term"initial_source X F"} is the initial lift with respect to the source @{term"{(f,M) | f M. (f,M) \<in> F}"}\<close>

text \<open> It is an extension of @{term vimage_algebra} that accepts a family of functions. \<close>

lemma vimage_algebra_to_initial_source:
  shows "vimage_algebra X f M = initial_source X {(f, M)}"
  unfolding vimage_algebra_def initial_source_def by auto

lemma space_initial_source [simp]:
  shows "space (initial_source X F) = X"
  unfolding initial_source_def by (rule space_measure_of) auto

lemma sets_initial_source:
  shows "sets (initial_source X F) = sigma_sets X {f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M}"
  unfolding initial_source_def
  by (rule sets_measure_of) auto

lemma sets_initial_source_mono:
  assumes "\<forall> (f, M) \<in> F. \<forall> A \<in> sets M. f -` A \<inter> X \<in> (sigma_sets X {g -` A \<inter> X | A g N. (g,N) \<in> G \<and> A \<in> sets N})"
  shows "sets (initial_source X F) \<subseteq> sets (initial_source X G)"
proof-
  have "{f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M} \<subseteq> (sigma_sets X {g -` A \<inter> X | A g N. (g,N) \<in> G \<and> A \<in> sets N})"
    using assms by auto
  hence "sigma_sets X {f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M} \<subseteq> sigma_sets X {g -` A \<inter> X | A g N. (g,N) \<in> G \<and> A \<in> sets N}"
    by (auto simp: sigma_sets_mono sigma_sets_subseteq sigma_sets_sigma_sets_eq)
  thus ?thesis
    by (auto simp: sets_initial_source)
qed

lemma sets_initial_source_cong:
  assumes "\<forall> (f, M) \<in> F. \<forall> A \<in> sets M. f -` A \<inter> X \<in> (sigma_sets X {g -` A \<inter> X | A g N. (g,N) \<in> G \<and> A \<in> sets N})"
    and "\<forall> (g, N) \<in> G. \<forall> B \<in> sets N. g -` B \<inter> X \<in> (sigma_sets X {f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M})"
  shows "sets (initial_source X F) = sets (initial_source X G)"
proof
  show "sets (initial_source X F) \<subseteq> sets (initial_source X G)"
    by (auto simp: sets_initial_source_mono[where X ="X", OF assms(1)])
  show "sets (initial_source X G) \<subseteq> sets (initial_source X F)"
    by (auto simp: sets_initial_source_mono[where X ="X", OF assms(2)])
qed

lemma initial_source_cong:
  assumes "X = Y"
    and "\<forall> (f, M) \<in> F. \<forall> A \<in> sets M. f -` A \<inter> X \<in> (sigma_sets X {g -` A \<inter> X | A g N. (g,N) \<in> G \<and> A \<in> sets N})"
    and "\<forall> (g, N) \<in> G. \<forall> B \<in> sets N. g -` B \<inter> X \<in> (sigma_sets X {f -` A \<inter> X | A f M. (f,M) \<in> F \<and> A \<in> sets M})"
  shows "(initial_source X F) = (initial_source Y G)"
proof(rule measure_eqI)
  show "sets (initial_source X F) = sets (initial_source Y G)"
    using sets_initial_source_cong assms by auto
  fix A assume "A \<in> sets (initial_source X F)"
  show "emeasure (initial_source X F) A = emeasure (initial_source Y G) A"
    unfolding initial_source_def by (auto simp: emeasure_sigma)
qed

proposition in_initial_source:
  shows "(f,M) \<in> F \<Longrightarrow> A \<in> sets M \<Longrightarrow> f -` A \<inter> X \<in> sets (initial_source X F)"
  by (auto simp: initial_source_def)

text\<open> Axiom of initial lift I: it makes the family measurable \<close>

proposition measurable_initial_source1[measurable(raw)]:
  shows "(f,M) \<in> F \<Longrightarrow> f \<in> X \<rightarrow> space M \<Longrightarrow> f \<in> measurable (initial_source X F) M"
  unfolding measurable_def by (auto intro: in_initial_source)

text\<open> Axiom of initial lift II: factorization \<close>

proposition measurable_initial_source2:
  assumes "g \<in> space N \<rightarrow> X"
    and "\<forall>(f,M) \<in> F. f \<in> X \<rightarrow> space M"
    and "\<forall>(f,M) \<in> F. (\<lambda>x. f (g x)) \<in> measurable N M"
  shows "g \<in> measurable N (initial_source X F)"
  unfolding initial_source_def
proof (rule measurableI)
  fix x assume xinN: "x \<in> space N"
  show "g x \<in> space (sigma X {B. \<exists>A f M. B = f -` A \<inter> X \<and> (f, M) \<in> F \<and> A \<in> sets M})"
    using assms(1) xinN space_measure_of_conv by fastforce
next fix B assume "B \<in> sets (sigma X {C. \<exists>A f M. C = f -` A \<inter> X \<and> (f, M) \<in> F \<and> A \<in> sets M})"
  hence "B \<in> sigma_sets X {C. \<exists>A f M. C = f -` A \<inter> X \<and> (f, M) \<in> F \<and> A \<in> sets M}"
    by (metis sets_initial_source initial_source_def)
  thus "g -` B \<inter> space N \<in> sets N"
  proof(induction B rule: sigma_sets.induct)
    case (Basic a)
    then obtain A f M where"a = f -` A \<inter> X \<and> (f, M) \<in> F \<and> A \<in> sets M"
      by auto
    hence prop1: "a = f -` A \<inter> X" "f \<in> X \<rightarrow> space M" "(\<lambda>x. f (g x)) \<in> measurable N M" "A \<in> sets M"
      using assms by auto
    hence "g -` a \<inter> space N = (\<lambda>x. f (g x)) -` A \<inter> space N"
      using assms(1) by auto
    also have "... \<in> sets N"
      using prop1 by (auto simp: measurable_sets)
    finally show ?case .
  next
    case Empty
    thus ?case by auto
  next
    case (Compl a)
    have "g -` (X - a) \<inter> space N = (g -` X \<inter> space N) - (g -` a \<inter> space N)"
      by (auto simp: Diff_Int_distrib inf_commute vimage_Diff)
    also have "... = (space N) - (g -` a \<inter> space N)"
      using assms(1) by auto
    also have "... \<in> sets N"
      by (auto simp: Compl.IH sets.compl_sets)
    finally show ?case .
  next
    case (Union a)
    have "g -` \<Union> (range a) \<inter> space N =\<Union> (range (\<lambda> i. ((g -` a i) \<inter> space N)))"
      by auto
    also have "... \<in> sets N"
      using Union.IH by blast
    finally show ?case .
  qed
qed

text\<open> The \<open>\<sigma>\<close>-algebra of a initial lift is the coarsest one that makes the family measurable. \<close>

lemma sets_image_in_sets_family:
  assumes N: "space N = X"
    and f: "\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M"
  shows "sets (initial_source X F) \<subseteq> sets N"
  unfolding sets_initial_source N[symmetric]
proof
  fix A assume A: "A \<in> sigma_sets (space N) {f -` A \<inter> (space N) | A f M. (f,M) \<in> F \<and> A \<in> sets M}"
  {
    fix A f M assume a0: "(f,M) \<in> F \<and> A \<in> sets M"
    hence "f \<in> measurable N M"using f by auto
    hence "f -` A \<inter> (space N) \<in> sets N"using a0
      by (auto simp: measurable_sets)
  }
  hence "{f -` A \<inter> (space N) | A f M. (f,M) \<in> F \<and> A \<in> sets M} \<subseteq> (sets N)"
    by auto
  with A have "A \<in> sigma_sets (space N) (sets N)"
    by (meson in_mono sigma_sets_subseteq)
  also have "... = (sets N)"
    by (auto simp: sets.sigma_sets_eq)
  finally show "A \<in> (sets N)".
qed

proposition initial_source_coarsest:
  assumes "\<forall>(f, M)\<in>F. f \<in> X \<rightarrow> space M"
  shows "sets (initial_source X F) = Inf{ sets N | N. space N = X  \<and> (\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M) } "
proof(subst Inf_eqI)
  show "\<And>i. i \<in> { sets N | N. space N = X  \<and> (\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M) } \<Longrightarrow> sets (initial_source X F) \<subseteq> i "
  proof-
    fix i assume " i \<in> { sets N | N. space N = X  \<and> (\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M) }"
    then obtain N where i: "i = sets N" and N: "space N = X" and  f: " \<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M"
      by auto
    show "sets (initial_source X F) \<subseteq> i"
      by(auto simp: i sets_image_in_sets_family[OF N f])
  qed
  have "\<And> f M. (f, M)\<in>F \<Longrightarrow> f \<in> initial_source X F \<rightarrow>\<^sub>M M"
    using assms measurable_initial_source1 by blast
  hence "sets (initial_source X F) \<in> {sets N |N. space N = X \<and> (\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M)}"
    by(auto intro!: CollectI exI[of _ "(initial_source X F)" ])
  thus "\<And>y. (\<And>i. i \<in> {sets N |N. space N = X \<and> (\<forall>(f, M)\<in>F. f \<in> N \<rightarrow>\<^sub>M M)} \<Longrightarrow> y \<subseteq> i) \<Longrightarrow> y \<subseteq> sets (initial_source X F)" by auto
qed(auto)

text\<open> An initial lift of a bundle of initial lifts is flatten to an initial lift. \<close>

lemma initial_source_initial_source_eq:
  assumes "\<forall> i \<in> I. G i \<in> Z \<rightarrow> (Y i)"
    and "\<forall> i \<in> I. \<forall> j \<in> J i. F i j \<in> Y i \<rightarrow> space (M i j)"
  shows "initial_source Z {((G i), (initial_source (Y i) {((F i j),(M i j)) | j. j \<in> (J i)})) | i. i \<in> I} = initial_source Z {(((F i j) o (G i)),(M i j)) | i j. i \<in> I \<and> j \<in> (J i)}"
proof (rule measure_eqI)
  show "\<And>A. A \<in> sets (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) \<Longrightarrow> emeasure (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) A = emeasure (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}) A"
    by (auto simp: emeasure_sigma initial_source_def)
  show "sets (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) =
 sets (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i})"
  proof
    show "sets (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) \<subseteq> sets (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i})"
    proof(rule sets_image_in_sets_family)
      show "space (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}) = Z"
        by auto
      {
        fix i assume i: "i \<in> I"
        hence "G i \<in> initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i} \<rightarrow>\<^sub>M initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}"
        proof(intro measurable_initial_source2)
          show "G i \<in> space (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}) \<rightarrow> Y i"
            using i assms(1) by auto
          show "\<forall>(f, M)\<in>{(F i j, M i j) |j. j \<in> J i}. f \<in> Y i \<rightarrow> space M"
            using assms(2) i by auto
          show "\<forall>(f, N)\<in>{(F i j, M i j) |j. j \<in> J i}. (\<lambda>x. f (G i x)) \<in> initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i} \<rightarrow>\<^sub>M N"
          proof
            {
              fix j assume j: "j \<in> J i"
              hence "(\<lambda>x. F i j(G i x)) \<in> initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i} \<rightarrow>\<^sub>M M i j"
              proof(intro measurable_initial_source1)
                have "(F i j \<circ> G i, M i j) \<in> {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}"
                  using i j by blast
                thus "(\<lambda>x. F i j (G i x), M i j) \<in> {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}"
                  by(auto simp: comp_def)
                show "(\<lambda>x. F i j (G i x)) \<in> Z \<rightarrow> space (M i j)"
                  using assms by (auto simp: Pi_iff i j)
              qed
            }
            thus "\<And>x. x \<in> {(F i j, M i j) |j. j \<in> J i} \<Longrightarrow> case x of (f, N) \<Rightarrow> (\<lambda>x. f (G i x)) \<in> initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i} \<rightarrow>\<^sub>M N"
              by auto
          qed
        qed
      }
      thus "\<forall>(f, N)\<in>{(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}. f \<in> initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i} \<rightarrow>\<^sub>M N"
        by force
    qed
    show "sets (initial_source Z {(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}) \<subseteq> sets (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I})"
    proof(rule sets_image_in_sets_family)
      show "space (initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) = Z"
        by auto
      {
        fix i j assume ij: "i \<in> I \<and> j \<in> J i"
        have measFij: "(F i j) \<in> initial_source (Y i) {(F i j, M i j) |j. j \<in> J i} \<rightarrow>\<^sub>M M i j"
        proof(intro measurable_initial_source1)
          show "(F i j, M i j) \<in> {(F i j, M i j) |j. j \<in> J i}"
            using ij by auto
          show "F i j \<in> Y i \<rightarrow> space (M i j)"
            using ij assms(2) by auto
        qed
        have measGi: "G i \<in> initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I} \<rightarrow>\<^sub>M initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}"
        proof(intro measurable_initial_source1)
          show "(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) \<in> {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}"
            using ij by auto
          show "G i \<in> Z \<rightarrow> space (initial_source (Y i) {(F i j, M i j) |j. j \<in> J i})"
            using ij assms(1) by auto
        qed
        from measFij measGi
        have "F i j \<circ> G i \<in> initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I} \<rightarrow>\<^sub>M M i j"
          by(auto simp: measurable_comp)
      }
      thus "\<forall>(f, N)\<in>{(F i j \<circ> G i, M i j) |i j. i \<in> I \<and> j \<in> J i}. f \<in> initial_source Z {(G i, initial_source (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I} \<rightarrow>\<^sub>M N"
        by blast
    qed
  qed
qed

subsection \<open>Final lift: the finest \<open>\<sigma>\<close>-algebra pushed out from a family of functions\<close>

definition\<^marker>\<open>tag important\<close> final_sink :: "'b set \<Rightarrow> (('a \<Rightarrow> 'b) \<times> 'a measure) set \<Rightarrow> 'b measure" where
  "final_sink Y G = sigma Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N) \<in> sets N))}"

text \<open> Roughly speaking, @{term G} is a structured sink @{term"{(g,N) | g N. (g,N) \<in> G}"} having the common codomain @{term Y}. @{term"final_sink Y G"} is the final lift with respect to the sink @{term"{(g,N) | g N. (g,N) \<in> G}"}.\<close>

lemma space_final_sink [simp]:
  shows "space (final_sink Y G) = Y"
  unfolding final_sink_def by (auto simp: space_measure_of_conv)

lemma sets_final_sink:
  shows "sets (final_sink Y G) = sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
  unfolding final_sink_def by (auto simp: subset_eq)

lemma sets_final_sink2:
  assumes g: "\<forall>(g,N) \<in> G . g \<in> space N \<rightarrow> Y"
  shows "sigma_sets Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)} = {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
proof-
  have "sigma_algebra Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
  proof
    show inclfam: "{A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)} \<subseteq> Pow Y"
      by auto
    show empty: "{} \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      by auto
    {
      fix g N assume "(g, N)\<in>G"
      hence "g \<in> space N \<rightarrow> Y"using g
        by auto
      hence "g -` Y \<inter> space N = space N"
        by auto
      hence "g -` Y \<inter> space N \<in> sets N"
        by auto
    }
    thus "Y \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      by auto
    fix A B assume ABgN: "A \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      "B \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
    hence AB: "A \<in> Pow Y" "B \<in> Pow Y" "\<And>g N .(g, N)\<in>G \<Longrightarrow> g -` A \<inter> space N \<in> sets N \<and> g -` B \<inter> space N \<in> sets N"
      by auto
    {
      fix g N assume G: "(g, N)\<in>G"
      from AB G have IntinN: "g -` (A \<inter> B) \<inter> space N \<in> sets N"
        by (metis Int_assoc imageI sets_restrict_space sets_restrict_space_iff vimage_Int)
      from AB G have UnioninN: "g -` (A \<union> B) \<inter> space N \<in> sets N"
        by (auto simp: boolean_algebra.conj_disj_distrib2 sets.Un)
      from AB G have MinusinN: "g -` (A - B) \<inter> space N \<in> sets N"
        by (auto simp: Diff_Int_distrib2 sets.Diff vimage_Diff)
      note IntinN UnioninN MinusinN
    } note ABbinary = this
    show "A \<inter> B \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      using AB(1,2) ABbinary(1) by auto
    show "A \<union> B \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      using AB(1,2) ABbinary(2) by auto
    have "A - B \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      using AB(1,2) ABbinary(3) by auto
    hence "{A - B,{}}\<subseteq> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)} \<and> finite {A - B,{}} \<and> disjoint {A - B,{}} \<and> A - B = \<Union> {A - B,{}}"
      by (auto simp: inclfam empty pairwise_insert)
    thus "\<exists>C \<subseteq> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}. finite C \<and> disjoint C \<and> A - B = \<Union> C"
      by(intro exI)
  next fix W :: "nat \<Rightarrow> _" assume W: "range W \<subseteq> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
    {
      fix g N assume G: "(g, N)\<in>G"
      have Wi: "\<forall> i. W i \<in> Pow Y \<and> W i \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
        using W by blast
      hence UWPow: "(\<Union> (range W)) \<in> Pow Y"by auto
      from Wi have Wimeas: "\<forall> i. W i \<in> Pow Y \<and> g -` (W i) \<inter> space N \<in> sets N"
        using G by blast
      have "g -` (\<Union> (range W)) \<inter> space N = \<Union>(range (\<lambda> i. g -` (W i) \<inter> space N))"
        by auto
      hence "g -` (\<Union> (range W)) \<inter> space N = \<Union>(range (\<lambda> i. g -` (W i) \<inter> space N))"
        by auto
      also have "... \<in> sets N"
        using Wimeas by blast
      finally have UWg: "g -` (\<Union> (range W)) \<inter> space N \<in> sets N".
      note * = UWPow UWg
    } note WiUnion = this
    thus "\<Union> (range W) \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
      using Collect_mono_iff Pow_def W by auto
  qed
  thus "sigma_sets Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)} = {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
    by (auto simp: sigma_algebra.sigma_sets_eq)
qed

lemma \<^marker>\<open>tag important\<close> sets_final_sink':
  assumes g: "\<forall>(g,N) \<in> G . g \<in> space N \<rightarrow> Y"
  shows "sets (final_sink Y G) = {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
  using sets_final_sink sets_final_sink2[OF assms] by auto

lemma set_final_sink_mono:
  assumes "\<And>A. A \<in> Pow Y \<Longrightarrow> (\<forall> (f, M) \<in> F. (f -` A \<inter> (space M)\<in> sets M)) \<Longrightarrow> A \<in> sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
  shows "sets (final_sink Y F) \<subseteq> sets (final_sink Y G)"
proof-
  have "{A | A. A \<in> Pow Y \<and> (\<forall> (f,M) \<in> F. (f -` A \<inter> (space M)\<in> sets M))} \<subseteq> sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
    using assms by auto
  hence "sigma_sets Y{A | A. A \<in> Pow Y \<and> (\<forall> (f,M) \<in> F. (f -` A \<inter> (space M)\<in> sets M))} \<subseteq> sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
    by (meson sigma_sets_mono)
  thus "sets (final_sink Y F) \<subseteq> sets (final_sink Y G)"
    unfolding final_sink_def
    by (metis sets_final_sink final_sink_def)
qed

lemma set_final_sink_cong:
  assumes "\<And>A. A \<in> Pow Y \<Longrightarrow> (\<forall> (g, N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))\<Longrightarrow> A \<in> sigma_sets Y{A | A. A \<in> Pow Y \<and> (\<forall> (f,M) \<in> F. (f -` A \<inter> (space M)\<in> sets M))}"
    and "\<And>A. A \<in> Pow Y \<Longrightarrow> (\<forall> (f, M) \<in> F. (f -` A \<inter> (space M)\<in> sets M)) \<Longrightarrow> A \<in> sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
  shows "sets (final_sink Y G) = sets (final_sink Y F)"
proof
  show "sets (final_sink Y G) \<subseteq> sets (final_sink Y F)"
    using set_final_sink_mono assms(1) by auto
  show "sets (final_sink Y F) \<subseteq> sets (final_sink Y G)"
    using set_final_sink_mono assms(2) by auto
qed

lemma final_sink_cong:
  assumes "X = Y"
    and "\<And>A. A \<in> Pow Y \<Longrightarrow> (\<forall> (g, N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))\<Longrightarrow> A \<in> sigma_sets Y{A | A. A \<in> Pow Y \<and> (\<forall> (f,M) \<in> F. (f -` A \<inter> (space M)\<in> sets M))}"
    and "\<And>A. A \<in> Pow Y \<Longrightarrow> (\<forall> (f, M) \<in> F. (f -` A \<inter> (space M)\<in> sets M)) \<Longrightarrow> A \<in> sigma_sets Y {A | A. A \<in> Pow Y \<and> (\<forall> (g,N) \<in> G. (g -` A \<inter> (space N)\<in> sets N))}"
  shows "(final_sink Y G) = (final_sink X F)"
proof(rule measure_eqI)
  show "sets (final_sink Y G) = sets (final_sink X F)"
    unfolding assms(1) by(subst set_final_sink_cong[OF assms(2,3)],auto)
  fix A assume "A \<in> sets (final_sink Y G)"
  show "emeasure (final_sink Y G) A = emeasure (final_sink X F) A"
    unfolding final_sink_def
    by (auto simp: emeasure_sigma)
qed

lemma in_final_sink:
  shows "\<forall>(g,N) \<in> G . g \<in> space N \<rightarrow> Y \<Longrightarrow> (g,N) \<in> G \<Longrightarrow> A \<in> sets (final_sink Y G) \<Longrightarrow> ((g -` A \<inter> (space N))\<in> sets N)"
  by (metis (mono_tags, lifting) case_prodD mem_Collect_eq sets_final_sink sets_final_sink2)

text \<open> Axiom of final lift I: it makes the family measurable \<close>

lemma measurable_final_sink1[measurable(raw)]:
  shows "\<forall>(g,N) \<in> G . g \<in> space N \<rightarrow> Y \<Longrightarrow> (g,N) \<in> G \<Longrightarrow> g \<in> N \<rightarrow>\<^sub>M (final_sink Y G)"
  unfolding measurable_def by (auto intro: in_final_sink)

text \<open> Axiom of final lift II: factorization \<close>

lemma measurable_final_sink2:
  assumes "f \<in> Y \<rightarrow> space M"
    and "\<forall>(g,N) \<in> G . g \<in> space N \<rightarrow> Y"
    and "\<forall>(g,N) \<in> G . (\<lambda>x. f (g x)) \<in> N \<rightarrow>\<^sub>M M"
  shows "f \<in> (final_sink Y G) \<rightarrow>\<^sub>M M"
  unfolding final_sink_def
proof (rule measurableI)
  have Ysp: "space (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}) = Y"
    by (auto simp: space_measure_of_conv)
  show "\<And>x. x \<in> space (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}) \<Longrightarrow> f x \<in> space M"
    using assms Ysp by auto
  fix A assume A: "A \<in> sets M"
  {
    fix g N assume gN: "(g,N) \<in> G"
    hence *: "g \<in> space N \<rightarrow> Y" "(\<lambda>x. f (g x)) \<in> N \<rightarrow>\<^sub>M M"
      using assms(2,3) by auto
    hence eq1: "g -` Y \<inter> space N = space N"
      by auto
    from * A have "g -`(f -` A \<inter> Y) = (\<lambda>x. f (g x))-` A \<inter>g -`Y"
      by auto
    with eq1 have "g -`(f -` A \<inter> Y) \<inter> space N = (\<lambda>x. f (g x))-` A \<inter> space N"
      by (auto simp: inf_assoc)
  }note ** = this

  hence "f -` A \<inter> Y \<in> {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
    using A assms(3) measurable_sets by fastforce
  also have "... \<subseteq> sets (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)})"
    by auto
  finally have eq2: "f -` A \<inter> Y \<in> sets (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)})".

  have eq3: "f -` A \<inter> space (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}) = f -` A \<inter> Y"
    using Ysp by auto
  from eq2 eq3 show "f -` A \<inter> space (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}) \<in> sets (sigma Y {A |A. A \<in> Pow Y \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)})"
    by auto
qed

text\<open> The \<open>\<sigma>\<close>-algebra of a final lift is finest one that it makes the family measurable. \<close>

lemma sets_vimage_in_set_family:
  assumes M: "space M = Y"
    and g: "\<forall>(g,N) \<in> G . g \<in> N \<rightarrow>\<^sub>M M"
  shows "sets M \<subseteq> sets (final_sink Y G)"
  unfolding sets_final_sink M[symmetric]
proof
  fix B assume "B \<in> sets M"
  with g M have "B \<in> Pow (space M) \<and> (\<forall>(g, N)\<in>G. g -` B \<inter> space N \<in> sets N)"
    by (metis (no_types, lifting) Pow_iff case_prodD case_prodI2 measurable_sets sets.sets_into_space)
  thus "B \<in> sigma_sets (space M) {A |A. A \<in> Pow (space M) \<and> (\<forall>(g, N)\<in>G. g -` A \<inter> space N \<in> sets N)}"
    by auto
qed

proposition final_sink_finest:
  assumes "\<forall>(g, N)\<in>G. g \<in> space N \<rightarrow> Y"
  shows "sets (final_sink Y G) = Sup{ sets M | M. space M = Y \<and> (\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M ) } "
proof(subst Sup_eqI)
  show " \<And>y. y \<in> {sets M |M. space M = Y \<and> (\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M)} \<Longrightarrow> y \<subseteq>  sets  (final_sink Y G)"
  proof-
    fix y assume " y \<in> {sets M |M. space M = Y \<and> (\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M)}"
    then obtain M where y: "y = sets M" and M: "space M = Y" and g: "\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M"
      by auto
    show "y \<subseteq>  sets  (final_sink Y G)"
      by(auto simp: y sets_vimage_in_set_family[OF M g])
  qed
  have "\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M (final_sink Y G)"
    using measurable_final_sink1 assms by blast
  hence "(sets (final_sink Y G)) \<in> {sets M |M. space M = Y \<and> (\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M)}"
    by(intro CollectI exI[of _ "(final_sink Y G)"],auto)
  thus "\<And>y. (\<And>z. z \<in> {sets M |M. space M = Y \<and> (\<forall>(g, N)\<in>G. g \<in> N \<rightarrow>\<^sub>M M)} \<Longrightarrow> z \<subseteq> y) \<Longrightarrow> sets (final_sink Y G) \<subseteq> y"
    by auto
qed(auto)

text\<open> A final lift of a bundle of final lifts is flatten to a final lift. \<close>

lemma final_sink_final_sink_eq:
  assumes "\<forall> i \<in> I. G i \<in> (Y i) \<rightarrow> Z"
    and "\<forall> i \<in> I. \<forall> j \<in> J i. F i j \<in> space (M i j) \<rightarrow> (Y i)"
  shows "final_sink Z {((G i), (final_sink (Y i) {((F i j),(M i j)) | j. j \<in> (J i)})) | i. i \<in> I} = final_sink Z {((G i) o (F i j), (M i j)) | i j. i \<in> I \<and> j \<in> (J i)}"
proof (rule measure_eqI)
  show "\<And>A. A \<in> sets (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) \<Longrightarrow> emeasure (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) A = emeasure (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}) A"
    unfolding final_sink_def by (auto simp: emeasure_sigma)
  show "sets (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) = sets (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i})"
  proof
    show "sets (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) \<subseteq> sets (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i})"
    proof(rule sets_vimage_in_set_family)
      show "space (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}) = Z"
        by auto
      {
        fix i j assume i: "i \<in> I" and j: "j \<in> J i"
        hence measFij: "F i j \<in> M i j \<rightarrow>\<^sub>M final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}"
        proof(intro measurable_final_sink1)
          show "\<forall>(g, N)\<in>{(F i j, M i j) |j. j \<in> J i}. g \<in> space N \<rightarrow> Y i"
            using assms(2) i by blast
          show "(F i j, M i j) \<in> {(F i j, M i j) |j. j \<in> J i}"
            using j by auto
        qed
        from i j have measGi: "G i \<in> final_sink (Y i) {(F i j, M i j) |j. j \<in> J i} \<rightarrow>\<^sub>M final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}"
        proof(intro measurable_final_sink1)
          show "\<forall>(g, N)\<in>{(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}. g \<in> space N \<rightarrow> Z"
          proof
            show "\<And>x. x \<in> {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I} \<Longrightarrow> case x of (g, N) \<Rightarrow> g \<in> space N \<rightarrow> Z"
              using assms(1) by fastforce
          qed
          show "(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) \<in> {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}"
            using i by auto
        qed
        from measFij measGi
        have "G i \<circ> F i j \<in> M i j \<rightarrow>\<^sub>M final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}"
          by (auto simp: measurable_comp)
      }
      thus "\<forall>(g, N)\<in>{(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}. g \<in> N \<rightarrow>\<^sub>M final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}"
        by blast
    qed
    show "sets (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}) \<subseteq> sets (final_sink Z {(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I})"
    proof(rule sets_vimage_in_set_family)
      show "space (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}) = Z"
        by auto
      {
        fix i assume i: "i \<in> I"
        have "G i \<in> final_sink (Y i) {(F i j, M i j) |j. j \<in> J i} \<rightarrow>\<^sub>M final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}"
        proof(rule measurable_final_sink2)
          show "G i \<in> Y i \<rightarrow> space (final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i})"
            using i assms(1) by auto
          show "\<forall>(g, N)\<in>{(F i j, M i j) |j. j \<in> J i}. g \<in> space N \<rightarrow> Y i"
            using assms(2) i by blast
          show "\<forall>(g, N)\<in>{(F i j, M i j) |j. j \<in> J i}. (\<lambda>x. G i (g x)) \<in> N \<rightarrow>\<^sub>M final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}"
          proof(clarify)
            fix j assume j: "j \<in> J i"
            thus "(\<lambda>x. G i (F i j x)) \<in> M i j \<rightarrow>\<^sub>M final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}"
            proof(intro measurable_final_sink1)
              show "\<forall>(g, N)\<in>{(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}. g \<in> space N \<rightarrow> Z"
                using assms by fastforce
              show "(\<lambda>x. G i (F i j x), M i j) \<in> {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}"
                using i j comp_def[THEN sym] by blast
            qed
          qed
        qed
      }
      thus "\<forall>(g, N)\<in>{(G i, final_sink (Y i) {(F i j, M i j) |j. j \<in> J i}) |i. i \<in> I}. g \<in> N \<rightarrow>\<^sub>M final_sink Z {(G i \<circ> F i j, M i j) |i j. i \<in> I \<and> j \<in> J i}"
        by blast
    qed
  qed
qed

end