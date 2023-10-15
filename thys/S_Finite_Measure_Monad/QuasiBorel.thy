(*  Title:   QuasiBorel.thy
    Author:  Michikazu Hirata, Yasuhiko Minamide Tokyo Institute of Technology
*)

section \<open>Quasi-Borel Spaces\<close>
theory QuasiBorel
imports "HOL-Probability.Probability"
begin

subsection \<open> Definitions \<close>

subsubsection \<open> Quasi-Borel Spaces\<close>
definition qbs_closed1 :: "(real \<Rightarrow> 'a) set \<Rightarrow> bool"
  where "qbs_closed1 Mx \<equiv> (\<forall>a \<in> Mx. \<forall>f \<in> (borel :: real measure) \<rightarrow>\<^sub>M (borel :: real measure). a \<circ> f \<in> Mx)"

definition qbs_closed2 :: "['a set, (real \<Rightarrow> 'a) set] \<Rightarrow> bool"
 where "qbs_closed2 X Mx \<equiv> (\<forall>x \<in> X. (\<lambda>r. x) \<in> Mx)"

definition qbs_closed3 :: "(real \<Rightarrow> 'a) set \<Rightarrow> bool"
 where "qbs_closed3 Mx \<equiv> (\<forall>P::real \<Rightarrow> nat. \<forall>Fi::nat \<Rightarrow> real \<Rightarrow> 'a.
                          (P \<in> borel \<rightarrow>\<^sub>M count_space UNIV) \<longrightarrow> (\<forall>i. Fi i \<in> Mx) \<longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx)"

lemma separate_measurable:
  fixes P :: "real \<Rightarrow> nat"
  assumes "\<And>i. P -` {i} \<in> sets borel"
  shows "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
  by (auto simp add: assms measurable_count_space_eq_countable)

lemma measurable_separate:
  fixes P :: "real \<Rightarrow> nat"
  assumes "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
  shows "P -` {i} \<in> sets borel"
  by (metis assms borel_singleton measurable_sets_borel sets.empty_sets sets_borel_eq_count_space)

definition "is_quasi_borel X Mx \<longleftrightarrow> Mx \<subseteq> UNIV \<rightarrow> X \<and> qbs_closed1 Mx \<and> qbs_closed2 X Mx \<and> qbs_closed3 Mx"

lemma is_quasi_borel_intro[simp]:
  assumes "Mx \<subseteq> UNIV \<rightarrow> X"
      and "qbs_closed1 Mx" "qbs_closed2 X Mx" "qbs_closed3 Mx"
    shows "is_quasi_borel X Mx"
  using assms by(simp add: is_quasi_borel_def)

typedef 'a quasi_borel = "{(X::'a set, Mx). is_quasi_borel X Mx}"
proof
  show "(UNIV, UNIV) \<in> {(X::'a set, Mx). is_quasi_borel X Mx}"
    by (simp add: is_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def)
qed

definition qbs_space :: "'a quasi_borel \<Rightarrow> 'a set" where
  "qbs_space X \<equiv> fst (Rep_quasi_borel X)"

definition qbs_Mx :: "'a quasi_borel \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "qbs_Mx X \<equiv> snd (Rep_quasi_borel X)"

declare [[coercion qbs_space]]

lemma qbs_decomp : "(qbs_space X,qbs_Mx X) \<in> {(X::'a set, Mx). is_quasi_borel X Mx}"
  by (simp add: qbs_space_def qbs_Mx_def Rep_quasi_borel[simplified])

lemma qbs_Mx_to_X:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "\<alpha> r \<in> qbs_space X"
  using qbs_decomp assms by(auto simp: is_quasi_borel_def)

lemma qbs_closed1I:
  assumes "\<And>\<alpha> f. \<alpha> \<in> Mx \<Longrightarrow> f \<in> borel \<rightarrow>\<^sub>M borel \<Longrightarrow> \<alpha> \<circ> f \<in> Mx"
  shows "qbs_closed1 Mx"
  using assms by(simp add: qbs_closed1_def)

lemma qbs_closed1_dest[simp]:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "f \<in> borel \<rightarrow>\<^sub>M borel"
    shows "\<alpha> \<circ> f \<in> qbs_Mx X"
  using assms qbs_decomp by (auto simp add: is_quasi_borel_def qbs_closed1_def)

lemma qbs_closed1_dest'[simp]:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "f \<in> borel \<rightarrow>\<^sub>M borel"
    shows "(\<lambda>r. \<alpha> (f r)) \<in> qbs_Mx X"
  using qbs_closed1_dest[OF assms] by (simp add: comp_def)

lemma qbs_closed2I:
  assumes "\<And>x. x \<in> X \<Longrightarrow> (\<lambda>r. x) \<in> Mx"
  shows "qbs_closed2 X Mx"
  using assms by(simp add: qbs_closed2_def)

lemma qbs_closed2_dest[simp]:
  assumes "x \<in> qbs_space X"
  shows "(\<lambda>r. x) \<in> qbs_Mx X"
  using assms qbs_decomp[of X] by (auto simp add: is_quasi_borel_def qbs_closed2_def)

lemma qbs_closed3I:
  assumes "\<And>(P :: real \<Rightarrow> nat) Fi. P \<in> borel \<rightarrow>\<^sub>M count_space UNIV \<Longrightarrow> (\<And>i. Fi i \<in> Mx)
                  \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx"
  shows "qbs_closed3 Mx"
  using assms by(auto simp: qbs_closed3_def)

lemma qbs_closed3I':
  assumes "\<And>(P :: real \<Rightarrow> nat) Fi. (\<And>i. P -` {i} \<in> sets borel) \<Longrightarrow> (\<And>i. Fi i \<in> Mx)
                  \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx"
  shows "qbs_closed3 Mx"
  using assms by(auto intro!: qbs_closed3I dest: measurable_separate)

lemma qbs_closed3_dest[simp]:
  fixes P::"real \<Rightarrow> nat" and Fi :: "nat \<Rightarrow> real \<Rightarrow> _"
  assumes "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
      and "\<And>i. Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
  using assms qbs_decomp[of X] by (auto simp add: is_quasi_borel_def qbs_closed3_def)

lemma qbs_closed3_dest':
  fixes P::"real \<Rightarrow> nat" and Fi :: "nat \<Rightarrow> real \<Rightarrow> _"
  assumes "\<And>i. P -` {i} \<in> sets borel"
      and "\<And>i. Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
  using qbs_closed3_dest[OF separate_measurable[OF assms(1)] assms(2)] .

lemma qbs_closed3_dest2:
  assumes "countable I"
 and [measurable]: "P \<in> borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> I \<Longrightarrow> Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
proof -
  have 0:"I \<noteq> {}"
    using measurable_empty_iff[of "count_space I" P borel] assms(2)
    by fastforce
  define P' where "P' \<equiv> to_nat_on I \<circ> P"
  define Fi' where "Fi' \<equiv> Fi \<circ> (from_nat_into I)"
  have 1:"P' \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
    by(simp add: P'_def)
  have 2:"\<And>i. Fi' i \<in> qbs_Mx X"
    using assms(3) from_nat_into[OF 0] by(simp add: Fi'_def)
  have "(\<lambda>r. Fi' (P' r) r) \<in> qbs_Mx X"
    using 1 2 measurable_separate by auto
  thus ?thesis
    using from_nat_into_to_nat_on[OF assms(1)] measurable_space[OF assms(2)]
    by(auto simp: Fi'_def P'_def)
qed

lemma qbs_closed3_dest2':
  assumes "countable I"
 and [measurable]: "P \<in> borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> range P \<Longrightarrow> Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
proof -
  have 0:"range P \<inter> I = range P"
    using measurable_space[OF assms(2)] by auto
  have 1:"P \<in> borel \<rightarrow>\<^sub>M count_space (range P)"
    using restrict_count_space[of I "range P"] measurable_restrict_space2[OF _ assms(2),of "range P"]
    by(simp add: 0)
  have 2:"countable (range P)"
    using countable_Int2[OF assms(1),of "range P"]
    by(simp add: 0)
  show ?thesis
    by(auto intro!: qbs_closed3_dest2[OF 2 1 assms(3)])
qed

lemma qbs_Mx_indicat:
  assumes "S \<in> sets borel" "\<alpha> \<in> qbs_Mx X" "\<beta> \<in> qbs_Mx X"
  shows "(\<lambda>r. if r \<in> S then \<alpha> r else \<beta> r) \<in> qbs_Mx X"
proof -
  have "(\<lambda>r::real. if r \<in> S then \<alpha> r else \<beta> r) = (\<lambda>r. (\<lambda>b. if b then \<alpha> else \<beta>) (r \<in> S) r)"
    by(auto simp: indicator_def)
  also have "... \<in> qbs_Mx X"
    by(rule qbs_closed3_dest2[where I=UNIV and Fi="\<lambda>b. if b then \<alpha> else \<beta>"]) (use assms in auto)
  finally show ?thesis .
qed

lemma qbs_space_Mx: "qbs_space X = {\<alpha> x |x \<alpha>. \<alpha> \<in> qbs_Mx X}"
proof safe
  fix x
  assume 1:"x \<in> qbs_space X"
  show "\<exists>xa \<alpha>. x = \<alpha> xa \<and> \<alpha> \<in> qbs_Mx X"
    by(auto intro!: exI[where x=0] exI[where x="(\<lambda>r. x)"] simp: 1)
qed(simp add: qbs_Mx_to_X)

lemma qbs_space_eq_Mx:
  assumes "qbs_Mx X = qbs_Mx Y"
  shows "qbs_space X = qbs_space Y"
  by(simp add: qbs_space_Mx assms)

lemma qbs_eqI:
  assumes "qbs_Mx X = qbs_Mx Y"
  shows "X = Y"
  by (metis Rep_quasi_borel_inverse prod.exhaust_sel qbs_Mx_def qbs_space_def assms qbs_space_eq_Mx[OF assms])

subsubsection \<open> Empty Space \<close>
definition empty_quasi_borel  :: "'a quasi_borel" where
"empty_quasi_borel \<equiv> Abs_quasi_borel ({},{})"

lemma
  shows eqb_space[simp]: "qbs_space empty_quasi_borel = ({} :: 'a set)"
    and eqb_Mx[simp]: "qbs_Mx empty_quasi_borel = ({} :: (real \<Rightarrow> 'a) set)"
proof -
  have "Rep_quasi_borel empty_quasi_borel = ({} :: 'a set, {})"
    using Abs_quasi_borel_inverse by(auto simp add: Abs_quasi_borel_inverse empty_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)
  thus "qbs_space empty_quasi_borel = ({} :: 'a set)" "qbs_Mx empty_quasi_borel = ({} :: (real \<Rightarrow> 'a) set)"
    by(auto simp add: qbs_space_def qbs_Mx_def)
qed

lemma qbs_empty_equiv :"qbs_space X = {} \<longleftrightarrow> qbs_Mx X = {}"
proof safe
  fix x
  assume "qbs_Mx X = {}"
     and h:"x \<in> qbs_space X"
  have "(\<lambda>r. x) \<in> qbs_Mx X"
    using h by simp
  thus "x \<in> {}" using \<open>qbs_Mx X = {}\<close> by simp
qed(use qbs_Mx_to_X in blast)

lemma empty_quasi_borel_iff:
  "qbs_space X = {} \<longleftrightarrow> X = empty_quasi_borel"
  by(auto intro!: qbs_eqI simp: qbs_empty_equiv)

subsubsection \<open> Unit Space \<close>
definition unit_quasi_borel :: "unit quasi_borel" ("1\<^sub>Q") where
"unit_quasi_borel \<equiv> Abs_quasi_borel (UNIV,UNIV)"

lemma
  shows unit_qbs_space[simp]: "qbs_space unit_quasi_borel = {()}"
    and unit_qbs_Mx[simp]: "qbs_Mx unit_quasi_borel = {\<lambda>r. ()}"
proof -
  have "Rep_quasi_borel unit_quasi_borel = (UNIV,UNIV)"
    using Abs_quasi_borel_inverse by(auto simp add: unit_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)
  thus "qbs_space unit_quasi_borel = {()}" "qbs_Mx unit_quasi_borel = {\<lambda>r. ()}"
    by(auto simp add: qbs_space_def qbs_Mx_def UNIV_unit)
qed

subsubsection \<open> Sub-Spaces \<close>
definition sub_qbs :: "['a quasi_borel, 'a set] \<Rightarrow> 'a quasi_borel" where
"sub_qbs X U \<equiv> Abs_quasi_borel (qbs_space X \<inter> U,{\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)})"

lemma
  shows sub_qbs_space: "qbs_space (sub_qbs X U) = qbs_space X \<inter> U"
    and sub_qbs_Mx: "qbs_Mx (sub_qbs X U) = {\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)}"
proof -
  have "qbs_closed1 {\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)}" "qbs_closed2 (qbs_space X \<inter> U) {\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)}"
       "qbs_closed3 {\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)}"
    unfolding qbs_closed1_def qbs_closed2_def qbs_closed3_def by auto
  hence "Rep_quasi_borel (sub_qbs X U) = (qbs_space X \<inter> U,{\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)})"
    by(auto simp: sub_qbs_def is_quasi_borel_def qbs_Mx_to_X intro!: Abs_quasi_borel_inverse)
  thus "qbs_space (sub_qbs X U) = qbs_space X \<inter> U" "qbs_Mx (sub_qbs X U) = {\<alpha>. \<alpha> \<in> qbs_Mx X \<and> (\<forall>r. \<alpha> r \<in> U)}"
    by(simp_all add: qbs_Mx_def qbs_space_def)
qed

lemma sub_qbs:
  assumes "U \<subseteq> qbs_space X"
  shows "(qbs_space (sub_qbs X U), qbs_Mx (sub_qbs X U)) = (U, {f \<in> UNIV \<rightarrow> U. f \<in> qbs_Mx X})"
  using assms by (auto simp: sub_qbs_space sub_qbs_Mx)

lemma sub_qbs_ident: "sub_qbs X (qbs_space X) = X"
  by(auto intro!: qbs_eqI simp: sub_qbs_Mx qbs_Mx_to_X)

lemma sub_qbs_sub_qbs: "sub_qbs (sub_qbs X A) B = sub_qbs X (A \<inter> B)"
  by(auto intro!: qbs_eqI simp: sub_qbs_Mx sub_qbs_space)

subsubsection \<open> Image Spaces \<close>
definition map_qbs :: "['a \<Rightarrow> 'b] \<Rightarrow> 'a quasi_borel \<Rightarrow> 'b quasi_borel" where
"map_qbs f X = Abs_quasi_borel (f ` (qbs_space X),{f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X})"

lemma
  shows map_qbs_space: "qbs_space (map_qbs f X) = f ` (qbs_space X)"
    and map_qbs_Mx: "qbs_Mx (map_qbs f X) = {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
proof -
  have  "{f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X} \<subseteq> UNIV \<rightarrow> f ` (qbs_space X)"
    using qbs_Mx_to_X by fastforce
  moreover have "qbs_closed1 {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
    unfolding qbs_closed1_def using qbs_closed1_dest by(fastforce simp: comp_def)
  moreover have  "qbs_closed2 (f ` (qbs_space X)) {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
    unfolding qbs_closed2_def by fastforce
  moreover have  "qbs_closed3 {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
  proof(rule qbs_closed3I')
    fix P :: "real \<Rightarrow> nat" and Fi
    assume h:"\<And>i::nat. P -` {i} \<in> sets borel"
             "\<And>i::nat. Fi i \<in> {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
    then obtain \<alpha>i where ha: "\<And>i::nat. \<alpha>i i \<in> qbs_Mx X" "\<And>i. Fi i = f \<circ> (\<alpha>i i)"
      by auto metis
    hence 1:"(\<lambda>r. \<alpha>i (P r) r) \<in> qbs_Mx X"
      using h(1) qbs_closed3_dest' by blast
    show "(\<lambda>r. Fi (P r) r)  \<in> {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
      by(auto intro!: bexI[where x="(\<lambda>r. \<alpha>i (P r) r)"] simp add: 1 ha comp_def)
  qed
  ultimately have "Rep_quasi_borel (map_qbs f X) = (f ` (qbs_space X),{f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X})"
    unfolding map_qbs_def by(auto intro!: Abs_quasi_borel_inverse)
  thus "qbs_space (map_qbs f X) = f ` (qbs_space X)" "qbs_Mx (map_qbs f X) = {f \<circ> \<alpha> |\<alpha>. \<alpha>\<in> qbs_Mx X}"
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

subsubsection \<open> Binary Product Spaces \<close>
definition pair_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<times> 'b) quasi_borel" (infixr "\<Otimes>\<^sub>Q" 80) where
"pair_qbs X Y = Abs_quasi_borel (qbs_space X \<times> qbs_space Y, {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y})"

lemma
  shows pair_qbs_space: "qbs_space (X \<Otimes>\<^sub>Q Y) = qbs_space X \<times> qbs_space Y"
    and pair_qbs_Mx: "qbs_Mx (X \<Otimes>\<^sub>Q Y) = {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
proof -
  have "{f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y} \<subseteq> UNIV \<rightarrow> qbs_space X \<times> qbs_space Y"
    by (auto simp: mem_Times_iff[of _ "qbs_space X" "qbs_space Y"]; use qbs_Mx_to_X in fastforce)
  moreover have "qbs_closed1 {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
    unfolding qbs_closed1_def by (metis (no_types, lifting) comp_assoc mem_Collect_eq qbs_closed1_dest)
  moreover have "qbs_closed2 (qbs_space X \<times> qbs_space Y) {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
    unfolding qbs_closed2_def by auto
  moreover have "qbs_closed3 {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
  proof(safe intro!: qbs_closed3I)
    fix P :: "real \<Rightarrow> nat"
    fix Fi :: "nat \<Rightarrow> real \<Rightarrow> 'a \<times> 'b"
    define Fj :: "nat \<Rightarrow> real \<Rightarrow> 'a" where "Fj \<equiv> \<lambda>j.(fst \<circ> Fi j)"
    assume "\<forall>i. Fi i \<in> {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
    then have "\<And>i. Fj i \<in> qbs_Mx X" by (simp add: Fj_def)
    moreover assume "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
    ultimately have "(\<lambda>r. Fj (P r) r) \<in> qbs_Mx X"
      by auto
    moreover have "fst \<circ> (\<lambda>r. Fi (P r) r) = (\<lambda>r. Fj (P r) r)" by (auto simp add: Fj_def)
    ultimately show "fst \<circ> (\<lambda>r. Fi (P r) r) \<in> qbs_Mx X" by simp
  next
    fix P :: "real \<Rightarrow> nat"
    fix Fi :: "nat \<Rightarrow> real \<Rightarrow> 'a \<times> 'b"
    define Fj :: "nat \<Rightarrow> real \<Rightarrow> 'b" where "Fj \<equiv> \<lambda>j.(snd \<circ> Fi j)"
    assume "\<forall>i. Fi i \<in> {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
    then have "\<And>i. Fj i \<in> qbs_Mx Y" by (simp add: Fj_def)
    moreover assume "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
    ultimately have "(\<lambda>r. Fj (P r) r) \<in> qbs_Mx Y"
      by auto
    moreover have "snd \<circ> (\<lambda>r. Fi (P r) r) = (\<lambda>r. Fj (P r) r)" by (auto simp add: Fj_def)
    ultimately show "snd \<circ> (\<lambda>r. Fi (P r) r) \<in> qbs_Mx Y" by simp
  qed
  ultimately have "Rep_quasi_borel (X \<Otimes>\<^sub>Q Y) = (qbs_space X \<times> qbs_space Y, {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y})"
    unfolding pair_qbs_def by(auto intro!: Abs_quasi_borel_inverse is_quasi_borel_intro)
  thus "qbs_space (X \<Otimes>\<^sub>Q Y) = qbs_space X \<times> qbs_space Y" "qbs_Mx (X \<Otimes>\<^sub>Q Y) = {f. fst \<circ> f \<in> qbs_Mx X \<and> snd \<circ> f \<in> qbs_Mx Y}"
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

lemma pair_qbs_fst:
  assumes "qbs_space Y \<noteq> {}"
  shows "map_qbs fst (X \<Otimes>\<^sub>Q Y) = X"
proof(rule qbs_eqI)
  obtain \<alpha>y where hy:"\<alpha>y \<in> qbs_Mx Y"
    using qbs_empty_equiv[of Y] assms by auto
  show "qbs_Mx (map_qbs fst (X \<Otimes>\<^sub>Q Y)) = qbs_Mx X"
    by(auto simp: map_qbs_Mx pair_qbs_Mx hy comp_def intro!: exI[where x="\<lambda>r. (_ r, \<alpha>y r)"])
qed

lemma pair_qbs_snd:
  assumes "qbs_space X \<noteq> {}"
  shows "map_qbs snd (X \<Otimes>\<^sub>Q Y) = Y"
proof(rule qbs_eqI)
  obtain \<alpha>x where hx:"\<alpha>x \<in> qbs_Mx X"
    using qbs_empty_equiv[of X] assms by auto
  show "qbs_Mx (map_qbs snd (X \<Otimes>\<^sub>Q Y)) = qbs_Mx Y"
    by(auto simp: map_qbs_Mx pair_qbs_Mx hx comp_def intro!: exI[where x="\<lambda>r. (\<alpha>x r, _ r)"])
qed

subsubsection \<open> Binary Coproduct Spaces  \<close>
definition copair_qbs_Mx :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real => 'a + 'b) set" where
"copair_qbs_Mx X Y \<equiv> 
  {g. \<exists> S \<in> sets borel.
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X. \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))}"


definition copair_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a + 'b) quasi_borel" (infixr "\<Oplus>\<^sub>Q" 65) where
"copair_qbs X Y \<equiv> Abs_quasi_borel (qbs_space X <+> qbs_space Y, copair_qbs_Mx X Y)"


text \<open> The following is an equivalent definition of @{term copair_qbs_Mx}. \<close>
definition copair_qbs_Mx2 :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real => 'a + 'b) set" where
"copair_qbs_Mx2 X Y \<equiv> 
  {g. (if qbs_space X = {} \<and> qbs_space Y = {} then False
       else if qbs_space X \<noteq> {} \<and> qbs_space Y = {} then 
                  (\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))
       else if qbs_space X = {} \<and> qbs_space Y \<noteq> {} then 
                  (\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))
       else 
         (\<exists>S \<in> sets borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))) }"

lemma copair_qbs_Mx_equiv :"copair_qbs_Mx (X :: 'a quasi_borel) (Y :: 'b quasi_borel) = copair_qbs_Mx2 X Y"
proof safe
(* \<subseteq> *)
  fix g :: "real \<Rightarrow> 'a + 'b"
  assume "g \<in> copair_qbs_Mx X Y"
  then obtain S where hs:"S\<in> sets borel \<and> 
  (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
  (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
  ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
     (\<exists> \<alpha>1\<in> qbs_Mx X.
      \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
    by (auto simp add: copair_qbs_Mx_def)
  consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
  then show "g \<in> copair_qbs_Mx2 X Y"
  proof cases
    assume "S = {}"
    from hs this have "\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))" by simp
    then obtain \<alpha>1 where h1:"\<alpha>1\<in> qbs_Mx X \<and> g = (\<lambda>r. Inl (\<alpha>1 r))" by auto
    have "qbs_space X \<noteq> {}"
      using qbs_empty_equiv h1
      by auto
    then have "(qbs_space X \<noteq> {} \<and> qbs_space Y = {}) \<or> (qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})"
      by simp
    then show "g \<in> copair_qbs_Mx2 X Y"
    proof
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
      then show "g \<in> copair_qbs_Mx2 X Y" 
        by(simp add: copair_qbs_Mx2_def \<open>\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))\<close>)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then obtain \<alpha>2 where "\<alpha>2 \<in> qbs_Mx Y" using qbs_empty_equiv by force
      define S' :: "real set" 
        where "S' \<equiv> UNIV"
      define g' :: "real \<Rightarrow> 'a + 'b"
        where "g' \<equiv> (\<lambda>r::real. (if (r \<in> S') then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      from \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> h1 \<open>\<alpha>2 \<in> qbs_Mx Y\<close>
      have "g' \<in> copair_qbs_Mx2 X Y" 
        by(force simp add: S'_def g'_def copair_qbs_Mx2_def)
      moreover have "g = g'"
        using h1 by(simp add: g'_def S'_def)
      ultimately show ?thesis
        by simp
    qed
  next
    assume "S = UNIV"
    from hs this have "\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))" by simp
    then obtain \<alpha>2 where h2:"\<alpha>2\<in> qbs_Mx Y \<and> g = (\<lambda>r. Inr (\<alpha>2 r))" by auto
    have "qbs_space Y \<noteq> {}"
      using qbs_empty_equiv h2
      by auto
    then have "(qbs_space X = {} \<and> qbs_space Y \<noteq> {}) \<or> (qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})"
      by simp
    then show "g \<in> copair_qbs_Mx2 X Y"
    proof
      assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
      then show ?thesis
        by(simp add: copair_qbs_Mx2_def \<open>\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))\<close>)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then obtain \<alpha>1 where "\<alpha>1 \<in> qbs_Mx X" using qbs_empty_equiv by force
      define S' :: "real set"
        where "S' \<equiv> {}"
      define g' :: "real \<Rightarrow> 'a + 'b"
        where "g' \<equiv> (\<lambda>r::real. (if (r \<in> S') then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      from \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> h2 \<open>\<alpha>1 \<in> qbs_Mx X\<close>
      have "g' \<in> copair_qbs_Mx2 X Y" 
        by(force simp add: S'_def g'_def copair_qbs_Mx2_def)
      moreover have "g = g'"
        using h2 by(simp add: g'_def S'_def)
      ultimately show ?thesis
        by simp
    qed
  next
    assume "S \<noteq> {} \<and> S \<noteq> UNIV"
    then have 
    h: "\<exists> \<alpha>1\<in> qbs_Mx X.
        \<exists> \<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
      using hs by simp
    then have "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      by (metis empty_iff qbs_empty_equiv)
    thus ?thesis
      using hs h by(auto simp add: copair_qbs_Mx2_def)
  qed

(* \<supseteq> *)
next
  fix g :: "real \<Rightarrow> 'a + 'b"
  assume "g \<in> copair_qbs_Mx2 X Y"
  then have
  h: "if qbs_space X = {} \<and> qbs_space Y = {} then False
      else if qbs_space X \<noteq> {} \<and> qbs_space Y = {} then 
                  (\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))
      else if qbs_space X = {} \<and> qbs_space Y \<noteq> {} then 
                  (\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))
      else 
          (\<exists>S \<in> sets borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
           g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))"
    by(simp add: copair_qbs_Mx2_def)
  consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
           "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
           "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
  then show "g \<in> copair_qbs_Mx X Y"
  proof cases
    assume "qbs_space X = {} \<and> qbs_space Y = {}"
    then show ?thesis
      using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(simp add: copair_qbs_Mx2_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
    from h this have "\<exists>\<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r))" by simp
    thus ?thesis
      by(auto simp add: copair_qbs_Mx_def)
  next
    assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
    from h this have "\<exists>\<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r))" by simp
    thus ?thesis
      unfolding copair_qbs_Mx_def 
      by(force simp add: copair_qbs_Mx_def)
  next
    assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
    from h this obtain S \<alpha>1 \<alpha>2 where Sag:
     "S \<in> sets borel" "\<alpha>1 \<in> qbs_Mx X" "\<alpha>2 \<in> qbs_Mx Y" "g = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))"
      by auto
    consider "S = {}" | "S = UNIV" | "S \<noteq> {}" "S \<noteq> UNIV" by auto
    then show "g \<in> copair_qbs_Mx X Y"
    proof cases
      assume "S = {}"
      then have [simp]: "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) = (\<lambda>r. Inr (\<alpha>2 r))"
        by simp
      show ?thesis
        using \<open>\<alpha>2 \<in> qbs_Mx Y\<close> unfolding copair_qbs_Mx_def
        by(auto intro! : bexI[where x=UNIV] simp: Sag)
    next
      assume "S = UNIV"
      then have "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) = (\<lambda>r. Inl (\<alpha>1 r))"
        by simp
      then show ?thesis
        using Sag by(auto simp add: copair_qbs_Mx_def)
    next
      assume "S \<noteq> {}" "S \<noteq> UNIV"
      then show ?thesis
        using Sag by(auto simp add: copair_qbs_Mx_def)
    qed
  qed
qed

lemma
  shows copair_qbs_space: "qbs_space (X \<Oplus>\<^sub>Q Y) = qbs_space X <+> qbs_space Y" (is ?goal1)
    and copair_qbs_Mx: "qbs_Mx (X \<Oplus>\<^sub>Q Y) = copair_qbs_Mx X Y" (is ?goal2)
proof -
  have "copair_qbs_Mx X Y \<subseteq> UNIV \<rightarrow> qbs_space X <+> qbs_space Y"
  proof
    fix g
    assume "g \<in> copair_qbs_Mx X Y"
    then obtain S where hs:"S\<in> sets borel \<and> 
     (S = {}   \<longrightarrow> (\<exists> \<alpha>1\<in> qbs_Mx X. g = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
     (S = UNIV \<longrightarrow> (\<exists> \<alpha>2\<in> qbs_Mx Y. g = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
     ((S \<noteq> {} \<and> S \<noteq> UNIV) \<longrightarrow>
        (\<exists> \<alpha>1\<in> qbs_Mx X.
         \<exists> \<alpha>2\<in> qbs_Mx Y.
             g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))))"
      by (auto simp add: copair_qbs_Mx_def)
    consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
    then show "g \<in> UNIV \<rightarrow> qbs_space X <+> qbs_space Y"
    proof cases
      assume "S = {}"
      then show ?thesis
        using hs qbs_Mx_to_X by auto
    next
      assume "S = UNIV"
      then show ?thesis
        using hs qbs_Mx_to_X by auto
    next
      assume "S \<noteq> {} \<and> S \<noteq> UNIV"
      then have "\<exists> \<alpha>1\<in> qbs_Mx X. \<exists> \<alpha>2\<in> qbs_Mx Y.
            g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))" using hs by simp
      then show ?thesis
        by(auto dest: qbs_Mx_to_X)
    qed
  qed
  moreover have "qbs_closed1 (copair_qbs_Mx X Y)"
  proof(rule qbs_closed1I)
    fix g and f :: "real \<Rightarrow> real"
    assume "g \<in> copair_qbs_Mx X Y" and [measurable]: "f \<in> borel \<rightarrow>\<^sub>M borel"
    then have "g \<in> copair_qbs_Mx2 X Y" using copair_qbs_Mx_equiv by auto
    consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
             "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
             "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
             "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
    then have "g \<circ> f \<in> copair_qbs_Mx2 X Y"
    proof cases
      assume "qbs_space X = {} \<and> qbs_space Y = {}"
      then show ?thesis
        using \<open>g \<in> copair_qbs_Mx2 X Y\<close> qbs_empty_equiv by(simp add: copair_qbs_Mx2_def)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
      then obtain \<alpha>1 where h1:"\<alpha>1\<in> qbs_Mx X \<and> g = (\<lambda>r. Inl (\<alpha>1 r))"
        using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
      then have "\<alpha>1 \<circ> f \<in> qbs_Mx X"
        by auto
      moreover have "g \<circ> f = (\<lambda>r. Inl ((\<alpha>1 \<circ> f) r))"
        using h1 by auto
      ultimately show ?thesis
        using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y = {}\<close> by(force simp add: copair_qbs_Mx2_def)
    next
      assume "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})"
      then obtain \<alpha>2 where h2:"\<alpha>2\<in> qbs_Mx Y \<and> g = (\<lambda>r. Inr (\<alpha>2 r))"
        using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
      then have "\<alpha>2 \<circ> f \<in> qbs_Mx Y"
        by auto
      moreover have "g \<circ> f = (\<lambda>r. Inr ((\<alpha>2 \<circ> f) r))"
        using h2 by auto
      ultimately show ?thesis
        using \<open>(qbs_space X = {} \<and> qbs_space Y \<noteq> {})\<close> by(force simp add: copair_qbs_Mx2_def)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then have "\<exists>S \<in> sets borel. \<exists>\<alpha>1\<in> qbs_Mx X. \<exists>\<alpha>2\<in> qbs_Mx Y.
          g = (\<lambda>r::real. (if (r \<in> S) then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)))"
        using \<open>g \<in> copair_qbs_Mx2 X Y\<close> by(simp add: copair_qbs_Mx2_def)
      then show ?thesis
      proof safe
        fix S \<alpha>1 \<alpha>2
        assume [measurable]:"S \<in> sets borel" and "\<alpha>1\<in> qbs_Mx X" "\<alpha>2 \<in> qbs_Mx Y"
             "g = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))"
        have "f -` S \<in> sets borel"
          using \<open>S \<in> sets borel\<close> \<open>f \<in> borel_measurable borel\<close> measurable_sets_borel by blast
        moreover have "\<alpha>1 \<circ> f \<in> qbs_Mx X" 
          using \<open>\<alpha>1\<in> qbs_Mx X\<close> by(auto simp add: qbs_closed1_def)
        moreover have "\<alpha>2 \<circ> f \<in> qbs_Mx Y"
          using \<open>\<alpha>2\<in> qbs_Mx Y\<close> by(auto simp add: qbs_closed1_def)
        moreover have "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r)) \<circ> f = (\<lambda>r. if r \<in> f -` S then Inl ((\<alpha>1 \<circ> f) r) else Inr ((\<alpha>2 \<circ> f) r))"
          by auto
        ultimately show "(\<lambda>r. if r \<in> S then Inl (\<alpha>1 r)  else Inr (\<alpha>2 r)) \<circ> f \<in> copair_qbs_Mx2 X Y"
          using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> by(force simp add: copair_qbs_Mx2_def)
      qed
    qed
    thus "g \<circ> f \<in> copair_qbs_Mx X Y"
      using copair_qbs_Mx_equiv by auto
  qed
  moreover have "qbs_closed2 (qbs_space X <+> qbs_space Y) (copair_qbs_Mx X Y)"
  proof(rule qbs_closed2I)
    fix y
    assume "y \<in> qbs_space X <+> qbs_space Y"
    then consider "y \<in> Inl ` (qbs_space X)" | "y \<in> Inr ` (qbs_space Y)"
      by auto
    thus "(\<lambda>r. y) \<in> copair_qbs_Mx X Y"
    proof cases
      case 1
      then obtain x where x: "y = Inl x" "x \<in> qbs_space X"
        by auto
      define \<alpha>1 :: "real \<Rightarrow> _" where "\<alpha>1 \<equiv> (\<lambda>r. x)"
      have "\<alpha>1 \<in> qbs_Mx X" using \<open>x \<in> qbs_space X\<close> qbs_decomp 
        by(force simp add: qbs_closed2_def \<alpha>1_def)
      moreover have "(\<lambda>r. Inl x) = (\<lambda>l. Inl (\<alpha>1 l))" by (simp add: \<alpha>1_def)
      moreover have "{} \<in> sets borel" by auto
      ultimately show "(\<lambda>r. y) \<in> copair_qbs_Mx X Y"
        by(auto simp add: copair_qbs_Mx_def x)
    next
      case 2
      then obtain x where x: "y = Inr x" "x \<in> qbs_space Y"
        by auto
      define \<alpha>2 :: "real \<Rightarrow> _" where "\<alpha>2 \<equiv> (\<lambda>r. x)"
      have "\<alpha>2 \<in> qbs_Mx Y" using \<open>x \<in> qbs_space Y\<close> qbs_decomp 
        by(force simp add: qbs_closed2_def \<alpha>2_def)
      moreover have "(\<lambda>r. Inr x) = (\<lambda>l. Inr (\<alpha>2 l))" by (simp add: \<alpha>2_def)
      moreover have "UNIV \<in> sets borel" by auto
      ultimately show "(\<lambda>r. y) \<in> copair_qbs_Mx X Y"
        unfolding copair_qbs_Mx_def
        by(auto intro!: bexI[where x=UNIV] simp: x)
    qed
  qed
  moreover have "qbs_closed3 (copair_qbs_Mx X Y)"
  proof(safe intro!: qbs_closed3I)
    fix P :: "real \<Rightarrow> nat"
    fix Fi :: "nat \<Rightarrow> real \<Rightarrow>_ + _"
    assume "P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
         "\<forall>i. Fi i \<in> copair_qbs_Mx X Y"
    then have "\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y" using copair_qbs_Mx_equiv by blast
    consider "(qbs_space X = {} \<and> qbs_space Y = {})" |
             "(qbs_space X \<noteq> {} \<and> qbs_space Y = {})" |
             "(qbs_space X = {} \<and> qbs_space Y \<noteq> {})" |
             "(qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {})" by auto
    then have "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx2 X Y"
    proof cases
      assume "qbs_space X = {} \<and> qbs_space Y = {}"
      then show ?thesis
        using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> qbs_empty_equiv
        by(simp add: copair_qbs_Mx2_def)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y = {}"
      then have "\<forall>i. \<exists>\<alpha>i. \<alpha>i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>i r))"
        using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
      then have "\<exists>\<alpha>1. \<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>1 i r))"
        by(rule choice)
      then obtain \<alpha>1 :: "nat \<Rightarrow> real \<Rightarrow> _" 
        where h1: "\<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> Fi i = (\<lambda>r. Inl (\<alpha>1 i r))" by auto
      define \<beta> :: "real \<Rightarrow> _"  where "\<beta> \<equiv> (\<lambda>r. \<alpha>1 (P r) r)"
      from \<open>P \<in> borel \<rightarrow>\<^sub>M count_space UNIV\<close> h1
      have "\<beta> \<in> qbs_Mx X" by (simp add: \<beta>_def)
      moreover have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. Inl (\<beta> r))"
        using h1 by(simp add: \<beta>_def)
      ultimately show ?thesis
        using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y = {}\<close> by (auto simp add: copair_qbs_Mx2_def)
    next
      assume "qbs_space X = {} \<and> qbs_space Y \<noteq> {}"
      then have "\<forall>i. \<exists>\<alpha>i. \<alpha>i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>i r))"
        using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by(auto simp add: copair_qbs_Mx2_def)
      then have "\<exists>\<alpha>2. \<forall>i. \<alpha>2 i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>2 i r))"
        by(rule choice)
      then obtain \<alpha>2 :: "nat \<Rightarrow> real \<Rightarrow> _" 
        where h2: "\<forall>i. \<alpha>2 i \<in> qbs_Mx Y \<and> Fi i = (\<lambda>r. Inr (\<alpha>2 i r))" by auto
      define \<beta> :: "real \<Rightarrow> _" where "\<beta> \<equiv> (\<lambda>r. \<alpha>2 (P r) r)"
      from \<open>P \<in> borel \<rightarrow>\<^sub>M count_space UNIV\<close> h2
      have "\<beta> \<in> qbs_Mx Y" by(simp add: \<beta>_def)
      moreover have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. Inr (\<beta> r))"
        using h2 by(simp add: \<beta>_def)
      ultimately show ?thesis
        using \<open>qbs_space X = {} \<and> qbs_space Y \<noteq> {}\<close> by (auto simp add: copair_qbs_Mx2_def)
    next
      assume "qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}"
      then have "\<forall>i. \<exists>Si. Si \<in> sets borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> Si) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
        using \<open>\<forall>i. Fi i \<in> copair_qbs_Mx2 X Y\<close> by (auto simp add: copair_qbs_Mx2_def)
      then have "\<exists>S. \<forall>i. S i \<in> sets borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
        by(rule choice)
      then obtain S :: "nat \<Rightarrow> real set" 
        where hs :"\<forall>i. S i \<in> sets borel \<and> (\<exists>\<alpha>1i\<in> qbs_Mx X. \<exists>\<alpha>2i\<in> qbs_Mx Y.
                   Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
        by auto
      then have "\<forall>i. \<exists>\<alpha>1i. \<alpha>1i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1i r) else Inr (\<alpha>2i r))))"
        by blast
      then have "\<exists>\<alpha>1. \<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r))))"
        by(rule choice)
      then obtain \<alpha>1 where h1: "\<forall>i. \<alpha>1 i \<in> qbs_Mx X \<and> (\<exists>\<alpha>2i\<in> qbs_Mx Y.
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r))))"
        by auto
      define \<beta>1 :: "real \<Rightarrow> _" where "\<beta>1 \<equiv> (\<lambda>r. \<alpha>1 (P r) r)"
      from \<open>P \<in> borel \<rightarrow>\<^sub>M count_space UNIV\<close> h1
      have "\<beta>1 \<in> qbs_Mx X" by(simp add: \<beta>1_def)
      from h1 have "\<forall>i. \<exists>\<alpha>2i. \<alpha>2i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2i r)))"
        by auto
      then have "\<exists>\<alpha>2. \<forall>i. \<alpha>2 i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2 i r)))"
        by(rule choice)
      then obtain \<alpha>2
        where h2: "\<forall>i. \<alpha>2 i\<in> qbs_Mx Y \<and>
               Fi i = (\<lambda>r::real. (if (r \<in> S i) then Inl (\<alpha>1 i r) else Inr (\<alpha>2 i r)))"
        by auto
      define \<beta>2 :: "real \<Rightarrow> _" where "\<beta>2 \<equiv> (\<lambda>r. \<alpha>2 (P r) r)"
      from \<open>P \<in> borel \<rightarrow>\<^sub>M count_space UNIV\<close> h2
      have "\<beta>2 \<in> qbs_Mx Y" by(simp add: \<beta>2_def)
      define A :: "nat \<Rightarrow> real set" where "A \<equiv> (\<lambda>i. S i \<inter> P -` {i})"
      have [measurable]:"\<And>i. A i \<in> sets borel"
        using A_def hs measurable_separate[OF \<open>P \<in> borel \<rightarrow>\<^sub>M count_space UNIV\<close>] by blast
      define S' :: "real set" where "S' \<equiv> {r. r \<in> S (P r)}"
      have "S' = (\<Union>i::nat. A i)"
        by(auto simp add: S'_def A_def)
      hence "S' \<in> sets borel" by auto
      from h2 have "(\<lambda>r. Fi (P r) r) = (\<lambda>r. (if r \<in> S' then Inl (\<beta>1  r)
                                                        else Inr (\<beta>2 r)))"
        by(auto simp add: \<beta>1_def \<beta>2_def S'_def)
      thus "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx2 X Y"
        using \<open>qbs_space X \<noteq> {} \<and> qbs_space Y \<noteq> {}\<close> \<open>S' \<in> sets borel\<close> \<open>\<beta>1 \<in> qbs_Mx X\<close> \<open>\<beta>2 \<in> qbs_Mx Y\<close>
        by(auto simp add: copair_qbs_Mx2_def)
    qed
    thus "(\<lambda>r. Fi (P r) r) \<in> copair_qbs_Mx X Y"
      using copair_qbs_Mx_equiv by auto
  qed
  ultimately have "Rep_quasi_borel (copair_qbs X Y) = (qbs_space X <+> qbs_space Y, copair_qbs_Mx X Y)"
    unfolding copair_qbs_def by(auto intro!: Abs_quasi_borel_inverse)
  thus ?goal1 ?goal2
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

lemma copair_qbs_MxD:
  assumes "g \<in> qbs_Mx (X \<Oplus>\<^sub>Q Y)"
      and "\<And>\<alpha>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> g = (\<lambda>r. Inl (\<alpha> r)) \<Longrightarrow> P g"
      and "\<And>\<beta>. \<beta> \<in> qbs_Mx Y \<Longrightarrow> g = (\<lambda>r. Inr (\<beta> r)) \<Longrightarrow> P g"
      and "\<And>S \<alpha> \<beta>. (S :: real set) \<in> sets borel \<Longrightarrow> S \<noteq> {} \<Longrightarrow> S \<noteq> UNIV \<Longrightarrow> \<alpha> \<in> qbs_Mx X \<Longrightarrow> \<beta> \<in> qbs_Mx Y \<Longrightarrow> g = (\<lambda>r. if r \<in> S then Inl (\<alpha> r) else Inr (\<beta> r)) \<Longrightarrow> P g"
    shows "P g"
  using assms by(fastforce simp: copair_qbs_Mx copair_qbs_Mx_def)

subsubsection \<open> Product Spaces \<close>
definition PiQ :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b quasi_borel) \<Rightarrow> ('a \<Rightarrow> 'b) quasi_borel" where
"PiQ I X \<equiv> Abs_quasi_borel (\<Pi>\<^sub>E i\<in>I. qbs_space (X i), {\<alpha>. \<forall>i. (i \<in> I \<longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (X i)) \<and> (i \<notin> I \<longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined))})"

syntax
  "_PiQ" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a quasi_borel \<Rightarrow> ('i => 'a) quasi_borel"  ("(3\<Pi>\<^sub>Q _\<in>_./ _)"  10)
translations
  "\<Pi>\<^sub>Q x\<in>I. X" == "CONST PiQ I (\<lambda>x. X)"

lemma
  shows PiQ_space: "qbs_space (PiQ I X) = (\<Pi>\<^sub>E i\<in>I. qbs_space (X i))" (is ?goal1)
    and PiQ_Mx: "qbs_Mx (PiQ I X) = {\<alpha>. \<forall>i. (i \<in> I \<longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (X i)) \<and> (i \<notin> I \<longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined))}" (is "_ = ?Mx")
proof -
  have "?Mx \<subseteq> UNIV \<rightarrow> (\<Pi>\<^sub>E i\<in>I. qbs_space (X i))"
    using qbs_Mx_to_X[of _ "X _"] by auto metis
  moreover have "qbs_closed1 ?Mx"
  proof(safe intro!: qbs_closed1I)
    fix \<alpha> i and f :: "real \<Rightarrow> real"
    assume h[measurable]:"\<forall>i. (i \<in> I \<longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (X i)) \<and> (i \<notin> I \<longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined))"
                         "f \<in> borel \<rightarrow>\<^sub>M borel"
    show "(\<lambda>r. (\<alpha> \<circ> f) r i) \<in> qbs_Mx (X i)" if i:"i \<in> I"
    proof -
      have "(\<lambda>r. \<alpha> r i) \<circ> f \<in> qbs_Mx (X i)"
        using h i by auto
      thus "(\<lambda>r. (\<alpha> \<circ> f) r i) \<in> qbs_Mx (X i)"
        by(simp add: comp_def)
    qed
    show "i \<notin> I \<Longrightarrow> (\<lambda>r. (\<alpha> \<circ> f) r i) = (\<lambda>r. undefined)"
      by (metis comp_apply h(1))
  qed
  moreover have "qbs_closed2 (\<Pi>\<^sub>E i\<in>I. qbs_space (X i)) ?Mx"
    by(rule qbs_closed2I) (auto simp: PiE_def extensional_def Pi_def)
  moreover have "qbs_closed3 ?Mx"
  proof(rule qbs_closed3I)
    fix P :: "real \<Rightarrow> nat" and Fi
    assume h:"P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
             "\<And>i::nat. Fi i \<in> ?Mx"
    show "(\<lambda>r. Fi (P r) r) \<in> ?Mx"
    proof safe
      fix i
      assume hi:"i \<in> I"
      then show "(\<lambda>r. Fi (P r) r i) \<in> qbs_Mx (X i)"
        using h qbs_closed3_dest[OF h(1),of "\<lambda>j r. Fi j r i"]
        by auto
    next
      show "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. Fi (P r) r i) = (\<lambda>r. undefined)"
        using h by auto meson
    qed
  qed
  ultimately have "Rep_quasi_borel (PiQ I X) = (\<Pi>\<^sub>E i\<in>I. qbs_space (X i), ?Mx)"
    by(auto intro!: Abs_quasi_borel_inverse is_quasi_borel_intro simp: PiQ_def)
  thus ?goal1 "qbs_Mx (PiQ I X) = ?Mx"
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

lemma prod_qbs_MxI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (X i)"
      and "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined)"
    shows "\<alpha> \<in> qbs_Mx (PiQ I X)"
  using assms by(auto simp: PiQ_Mx)

lemma prod_qbs_MxD:
  assumes "\<alpha> \<in> qbs_Mx (PiQ I X)"
  shows "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (X i)"
    and "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined)"
    and "\<And>i r. i \<notin> I \<Longrightarrow> \<alpha> r i = undefined"
  using assms by(auto simp: PiQ_Mx dest: fun_cong[where g="(\<lambda>r. undefined)"])

lemma PiQ_eqI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> X i = Y i"
  shows "PiQ I X = PiQ I Y"
  by(auto intro!: qbs_eqI simp: PiQ_Mx assms)

lemma PiQ_empty: "qbs_space (PiQ {} X) = {\<lambda>i. undefined}"
  by(auto simp: PiQ_space)

lemma PiQ_empty_Mx: "qbs_Mx (PiQ {} X) = {\<lambda>r i. undefined}"
  by(auto simp: PiQ_Mx) meson

subsubsection \<open> Coproduct Spaces \<close>
definition coprod_qbs_Mx :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) set" where
"coprod_qbs_Mx I X \<equiv> { \<lambda>r. (f r, \<alpha> (f r) r) |f \<alpha>. f \<in> borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>i\<in>range f. \<alpha> i \<in> qbs_Mx (X i))}"

definition coprod_qbs_Mx' :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a \<times> 'b) set" where
"coprod_qbs_Mx' I X \<equiv> { \<lambda>r. (f r, \<alpha> (f r) r) |f \<alpha>. f \<in> borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>i. (i \<in> range f \<or> qbs_space (X i) \<noteq> {}) \<longrightarrow> \<alpha> i \<in> qbs_Mx (X i))}"

lemma coproduct_qbs_Mx_eq:
 "coprod_qbs_Mx I X = coprod_qbs_Mx' I X"
proof safe
  fix \<alpha>
  assume "\<alpha>  \<in> coprod_qbs_Mx I X"
  then obtain f \<beta> where hfb:
    "f \<in> borel \<rightarrow>\<^sub>M count_space I" "\<And>i. i \<in> range f \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (f r, \<beta> (f r) r))"
    unfolding coprod_qbs_Mx_def by blast
  define \<beta>' where "\<beta>' \<equiv> (\<lambda>i. if i \<in> range f then \<beta> i
                              else if qbs_space (X i) \<noteq> {} then (SOME \<gamma>. \<gamma> \<in> qbs_Mx (X i))
                              else \<beta> i)"
  have 1:"\<alpha> = (\<lambda>r. (f r, \<beta>' (f r) r))"
    by(simp add: hfb(3) \<beta>'_def)
  have 2:"\<And>i. qbs_space (X i) \<noteq> {} \<Longrightarrow> \<beta>' i \<in> qbs_Mx (X i)"
  proof -
    fix i
    assume hne:"qbs_space (X i) \<noteq> {}"
    then obtain x where "x \<in> qbs_space (X i)" by auto
    hence "(\<lambda>r. x) \<in> qbs_Mx (X i)" by auto
    thus "\<beta>' i \<in> qbs_Mx (X i)"
      by(cases "i \<in> range f") (auto simp: \<beta>'_def hfb(2) hne intro!: someI2[where a="\<lambda>r. x"])
  qed
  show "\<alpha> \<in> coprod_qbs_Mx' I X"
    using hfb(1,2) 1 2 \<beta>'_def by(auto simp: coprod_qbs_Mx'_def intro!: exI[where x=f] exI[where x=\<beta>'])
next
  fix \<alpha>
  assume "\<alpha> \<in> coprod_qbs_Mx' I X"
  then obtain f \<beta> where hfb:
    "f \<in> borel \<rightarrow>\<^sub>M count_space I"  "\<And>i. qbs_space (X i) \<noteq> {} \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)"
    "\<And>i. i \<in> range f \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)"  "\<alpha> = (\<lambda>r. (f r, \<beta> (f r) r))"
    unfolding coprod_qbs_Mx'_def by blast
  show "\<alpha> \<in> coprod_qbs_Mx I X"
    by(auto simp: hfb(4) coprod_qbs_Mx_def intro!: hfb(1) hfb(3))
qed

definition coprod_qbs :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> ('a \<times> 'b) quasi_borel" where
"coprod_qbs I X \<equiv> Abs_quasi_borel (SIGMA i:I. qbs_space (X i), coprod_qbs_Mx I X)"

syntax
 "_coprod_qbs" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a quasi_borel \<Rightarrow> ('i \<times> 'a) quasi_borel" ("(3\<amalg>\<^sub>Q _\<in>_./ _)"  10)
translations
 "\<amalg>\<^sub>Q x\<in>I. X" \<rightleftharpoons> "CONST coprod_qbs I (\<lambda>x. X)"

lemma
  shows coprod_qbs_space: "qbs_space (coprod_qbs I X) = (SIGMA i:I. qbs_space (X i))" (is ?goal1)
    and coprod_qbs_Mx: "qbs_Mx (coprod_qbs I X) = coprod_qbs_Mx I X" (is ?goal2)
proof -
  have "coprod_qbs_Mx I X \<subseteq> UNIV \<rightarrow> (SIGMA i:I. qbs_space (X i))"
    by(fastforce simp: coprod_qbs_Mx_def dest: measurable_space qbs_Mx_to_X)
  moreover have "qbs_closed1 (coprod_qbs_Mx I X)"
  proof(rule qbs_closed1I)
    fix \<alpha> and f :: "real \<Rightarrow> real"
    assume "\<alpha> \<in> coprod_qbs_Mx I X"
       and 1[measurable]: "f \<in> borel \<rightarrow>\<^sub>M borel"
    then obtain \<beta> g where ha:
      "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<in> qbs_Mx (X i)" "\<alpha> = (\<lambda>r. (g r, \<beta> (g r) r))" and [measurable]:"g \<in> borel \<rightarrow>\<^sub>M count_space I"
      by(fastforce simp: coprod_qbs_Mx_def)
    then have "\<And>i. i \<in> range g \<Longrightarrow> \<beta> i \<circ> f \<in> qbs_Mx (X i)"
      by simp
    thus "\<alpha> \<circ> f \<in> coprod_qbs_Mx I X"
      unfolding coprod_qbs_Mx_def by (auto intro!: exI[where x="g \<circ> f"] exI[where x="\<lambda>i. \<beta> i \<circ> f"] simp: ha(2))
  qed
  moreover have "qbs_closed2 (SIGMA i:I. qbs_space (X i)) (coprod_qbs_Mx I X)"
  proof(safe intro!: qbs_closed2I)
    fix i x
    assume "i \<in> I" "x \<in> qbs_space (X i)"
    then show "(\<lambda>r. (i,x)) \<in> coprod_qbs_Mx I X"
      by(auto simp: coprod_qbs_Mx_def intro!: exI[where x="\<lambda>r. i"])
  qed
  moreover have "qbs_closed3 (coprod_qbs_Mx I X)"
  proof(rule qbs_closed3I)
    fix P :: "real \<Rightarrow> nat" and Fi
    assume h[measurable]:"P \<in> borel \<rightarrow>\<^sub>M count_space UNIV"
             "\<And>i :: nat. Fi i \<in> coprod_qbs_Mx I X"
    then have "\<forall>i. \<exists>fi \<alpha>i. Fi i = (\<lambda>r. (fi r, \<alpha>i (fi r) r)) \<and> fi \<in> borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range fi \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i j \<in> qbs_Mx (X j))"
      by(auto simp: coproduct_qbs_Mx_eq coprod_qbs_Mx'_def)
    then obtain fi where
   "\<forall>i. \<exists>\<alpha>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i (fi i r) r)) \<and> fi i \<in> borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range (fi i) \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i j \<in> qbs_Mx (X j))"
      by(fastforce intro!: choice)
    then obtain \<alpha>i where
     "\<forall>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i i (fi i r) r)) \<and> fi i \<in> borel \<rightarrow>\<^sub>M count_space I \<and> (\<forall>j. (j \<in> range (fi i) \<or> qbs_space (X j) \<noteq> {}) \<longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j))"
      by(fastforce intro!: choice)
    then have hf[measurable]:
     "\<And>i. Fi i = (\<lambda>r. (fi i r, \<alpha>i i (fi i r) r))" "\<And>i. fi i \<in> borel \<rightarrow>\<^sub>M count_space I" "\<And>i j. j \<in> range (fi i) \<Longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j)" "\<And>i j. qbs_space (X j) \<noteq> {} \<Longrightarrow> \<alpha>i i j \<in> qbs_Mx (X j)"
      by auto

    define f' where "f' \<equiv> (\<lambda>r. fi (P r) r)"
    define \<alpha>' where "\<alpha>' \<equiv> (\<lambda>i r. \<alpha>i (P r) i r)"
    have 1:"(\<lambda>r. Fi (P r) r) = (\<lambda>r. (f' r, \<alpha>' (f' r) r))"
      by(simp add: \<alpha>'_def f'_def hf)
    have "f' \<in> borel \<rightarrow>\<^sub>M count_space I"
      by(simp add: f'_def)
    moreover have "\<And>i. i \<in> range f' \<Longrightarrow> \<alpha>' i \<in> qbs_Mx (X i)"
    proof -
      fix i
      assume hi:"i \<in> range f'"
      then obtain r where hr: "i = fi (P r) r" by(auto simp: f'_def)
      hence "i \<in> range (fi (P r))" by simp
      hence "\<alpha>i (P r) i \<in> qbs_Mx (X i)" by(simp add: hf)
      hence "qbs_space (X i) \<noteq> {}"
        by(auto simp: qbs_empty_equiv)
      hence "\<And>j. \<alpha>i j i \<in> qbs_Mx (X i)"
        by(simp add: hf(4))
      then show "\<alpha>' i \<in> qbs_Mx (X i)"
        by(auto simp: \<alpha>'_def h(1) intro!: qbs_closed3_dest[of P "\<lambda>j. \<alpha>i j i"])
    qed
    ultimately show "(\<lambda>r. Fi (P r) r) \<in> coprod_qbs_Mx I X"
      by(auto simp: 1 coprod_qbs_Mx_def intro!: exI[where x=f'])
  qed
  ultimately have "Rep_quasi_borel (coprod_qbs I X) = (SIGMA i:I. qbs_space (X i), coprod_qbs_Mx I X)"
    unfolding coprod_qbs_def by(fastforce intro!: Abs_quasi_borel_inverse)
  thus ?goal1 ?goal2
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

lemma coprod_qbs_MxI:
  assumes "f \<in> borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> range f \<Longrightarrow> \<alpha> i \<in> qbs_Mx (X i)"
    shows "(\<lambda>r. (f r, \<alpha> (f r) r)) \<in> qbs_Mx (coprod_qbs I X)"
  using assms unfolding coprod_qbs_Mx_def coprod_qbs_Mx by blast

lemma coprod_qbs_eqI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> X i = Y i"
  shows "coprod_qbs I X = coprod_qbs I Y"
  using assms by(auto intro!: qbs_eqI simp: coprod_qbs_Mx coprod_qbs_Mx_def) (metis UNIV_I measurable_space space_borel space_count_space)+

subsubsection \<open> List Spaces \<close>
text \<open> We define the quasi-Borel spaces on list using the following isomorphism.
       \begin{align*}
         List(X) \cong \coprod_{n\in \mathbb{N}} \prod_{0\leq i < n} X
       \end{align*}\<close>
definition "list_of X \<equiv> \<amalg>\<^sub>Q n\<in>(UNIV :: nat set).\<Pi>\<^sub>Q i\<in>{..<n}. X"
definition list_nil :: "nat \<times> (nat \<Rightarrow> 'a)" where
"list_nil \<equiv> (0, \<lambda>n. undefined)"
definition list_cons :: "['a, nat \<times> (nat \<Rightarrow> 'a)] \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
"list_cons x l \<equiv> (Suc (fst l), (\<lambda>n. if n = 0 then x else (snd l) (n - 1)))"

fun from_list :: "'a list \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
 "from_list [] = list_nil" |
 "from_list (a#l) = list_cons a (from_list l)"

fun to_list' ::  "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
 "to_list' 0 _ = []" |
 "to_list' (Suc n) f = f 0 # to_list' n (\<lambda>n. f (Suc n))"

definition to_list :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
"to_list \<equiv> case_prod to_list'"

text \<open> Definition \<close>
definition list_qbs :: "'a quasi_borel \<Rightarrow> 'a list quasi_borel" where
"list_qbs X \<equiv> map_qbs to_list (list_of X)"

definition list_head :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> 'a" where
"list_head l = snd l 0"
definition list_tail :: "nat \<times> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> (nat \<Rightarrow> 'a)" where
"list_tail l = (fst l - 1, \<lambda>m. (snd l) (Suc m))"

lemma list_simp1: "list_nil \<noteq> list_cons x l"
  by (simp add: list_nil_def list_cons_def)

lemma list_simp2:
  assumes "list_cons a al = list_cons b bl"
  shows "a = b" "al = bl"
proof -
  have "a = snd (list_cons a al) 0" "b = snd (list_cons b bl) 0"
    by (auto simp: list_cons_def)
  thus "a = b"
    by(simp add: assms)
next
  have "fst al = fst bl"
    using assms by (simp add: list_cons_def)
  moreover have "snd al = snd bl"
  proof
    fix n
    have "snd al n = snd (list_cons a al) (Suc n)"
      by (simp add: list_cons_def)
    also have "... = snd (list_cons b bl) (Suc n)"
      by (simp add: assms)
    also have "... = snd bl n"
      by (simp add: list_cons_def)
    finally show "snd al n = snd bl n" .
  qed
  ultimately show "al = bl"
    by (simp add: prod.expand)
qed

lemma
  shows list_simp3:"list_head (list_cons a l) = a"
    and list_simp4:"list_tail (list_cons a l) = l"
  by(simp_all add: list_head_def list_cons_def list_tail_def)

lemma list_decomp1:
  assumes "l \<in> qbs_space (list_of X)"
  shows "l = list_nil \<or>
         (\<exists>a l'. a \<in> qbs_space X \<and> l' \<in> qbs_space (list_of X) \<and> l = list_cons a l')"
proof(cases l)
  case hl:(Pair n f)
  show ?thesis
  proof(cases n)
    case 0
    then show ?thesis
      using assms hl by (simp add: list_of_def list_nil_def coprod_qbs_space PiQ_space)
  next
    case hn:(Suc n')
    define f' where "f' \<equiv> \<lambda>m. f (Suc m)"
    have "l = list_cons (f 0) (n',f')"
      unfolding hl hn list_cons_def
    proof safe
      fix m
      show "f = (\<lambda>m. if m = 0 then f 0 else snd (n', f') (m - 1))"
      proof
        fix m
        show "f m = (if m = 0 then f 0 else snd (n', f') (m - 1))"
          using assms hl by(cases m; fastforce simp: f'_def) 
      qed
    qed simp
    moreover have "(n', f') \<in> qbs_space (list_of X)"
    proof -
      have "\<And>x. x \<in> {..<n'} \<Longrightarrow> f' x \<in> qbs_space X"
        using assms hl hn by(fastforce simp: f'_def list_of_def coprod_qbs_space PiQ_space)
      moreover {
        fix x
        assume 1:"x \<notin> {..<n'}"
        hence " f' x = undefined"
          using hl assms hn by(auto simp: f'_def list_of_def coprod_qbs_space PiQ_space)
      }
      ultimately show ?thesis
        by(auto simp add: list_of_def coprod_qbs_space PiQ_space)
    qed
    ultimately show ?thesis
      using hl assms by(auto intro!: exI[where x="f 0"] exI[where x="(n',\<lambda>m. if m = 0 then undefined else f (Suc m))"] simp: list_cons_def list_of_def coprod_qbs_space PiQ_space)
  qed
qed

lemma list_simp5:
  assumes "l \<in> qbs_space (list_of X)"
      and "l \<noteq> list_nil"
    shows "l = list_cons (list_head l) (list_tail l)"
proof -
  obtain a l' where hl:
  "a \<in> qbs_space X" "l' \<in> qbs_space (list_of X)" "l = list_cons a l'"
    using list_decomp1[OF assms(1)] assms(2) by blast
  hence "list_head l = a" "list_tail l = l'"
    by(simp_all add: list_simp3 list_simp4)
  thus ?thesis
    using hl(3) list_simp2 by auto
qed

lemma list_simp6:
 "list_nil \<in> qbs_space (list_of X)"
  by (simp add: list_nil_def list_of_def coprod_qbs_space PiQ_space)

lemma list_simp7:
  assumes "a \<in> qbs_space X"
      and "l \<in> qbs_space (list_of X)"
    shows "list_cons a l \<in> qbs_space (list_of X)"
  using assms by(fastforce simp: PiE_def extensional_def list_cons_def list_of_def coprod_qbs_space PiQ_space)

lemma list_destruct_rule:
  assumes "l \<in> qbs_space (list_of X)"
          "P list_nil"
      and "\<And>a l'. a \<in> qbs_space X \<Longrightarrow> l' \<in> qbs_space (list_of X) \<Longrightarrow> P (list_cons a l')"
    shows "P l"
  by(rule disjE[OF list_decomp1[OF assms(1)]]) (use assms in auto)

lemma list_induct_rule:
  assumes "l \<in> qbs_space (list_of X)"
          "P list_nil"
      and "\<And>a l'. a \<in> qbs_space X \<Longrightarrow> l' \<in> qbs_space (list_of X) \<Longrightarrow> P l' \<Longrightarrow> P (list_cons a l')"
    shows "P l"
proof(cases l)
  case hl:(Pair n f)
  then show ?thesis
    using assms(1)
  proof(induction n arbitrary: f l)
    case 0
    then show ?case
      using assms(2) by (simp add: list_of_def coprod_qbs_space PiQ_space list_nil_def)
  next
    case ih:(Suc n)
    then obtain a l' where hl:
    "a \<in> qbs_space X" "l' \<in> qbs_space (list_of X)" "l = list_cons a l'"
      using list_decomp1 by(simp add: list_nil_def) blast
    have "P l'"
      using ih hl(3)
      by(auto intro!: ih(1)[OF _ hl(2),of "snd l'"] simp: list_of_def coprod_qbs_space PiQ_space list_cons_def)
    from assms(3)[OF hl(1,2) this]
    show ?case
      by(simp add: hl(3))
  qed
qed

lemma to_list_simp1: "to_list list_nil = []"
  by(simp add: to_list_def list_nil_def)

lemma to_list_simp2:
  assumes "l \<in> qbs_space (list_of X)"
  shows "to_list (list_cons a l) = a # to_list l"
  using assms by(auto simp:PiE_def to_list_def list_cons_def list_of_def coprod_qbs_space PiQ_space)

lemma to_list_set:
  assumes "l \<in> qbs_space (list_of X)"
  shows "set (to_list l) \<subseteq> qbs_space X"
  by(rule list_induct_rule[OF assms]) (auto simp: to_list_simp1 to_list_simp2)

lemma from_list_length: "fst (from_list l) = length l"
  by(induction l, simp_all add: list_cons_def list_nil_def)

lemma from_list_in_list_of:
  assumes "set l \<subseteq> qbs_space X"
  shows "from_list l \<in> qbs_space (list_of X)"
  using assms by(induction l) (auto simp: PiE_def extensional_def Pi_def list_of_def coprod_qbs_space PiQ_space list_nil_def list_cons_def)

lemma from_list_in_list_of': "from_list l \<in> qbs_space (list_of (Abs_quasi_borel (UNIV,UNIV)))"
proof -
  have "set l \<subseteq> qbs_space (Abs_quasi_borel (UNIV,UNIV))"
    by(simp add: qbs_space_def Abs_quasi_borel_inverse[of "(UNIV,UNIV)",simplified is_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def,simplified])
  thus ?thesis
    using from_list_in_list_of by blast
qed

lemma list_cons_in_list_of:
  assumes "set (a#l) \<subseteq> qbs_space X"
  shows "list_cons a (from_list l) \<in> qbs_space (list_of X)"
  using from_list_in_list_of[OF assms] by simp

lemma from_list_to_list_ident:
 "to_list (from_list l) = l"
  by(induction l) (simp add: to_list_def list_nil_def,simp add: to_list_simp2[OF from_list_in_list_of'])

lemma to_list_from_list_ident:
  assumes "l \<in> qbs_space (list_of X)"
  shows "from_list (to_list l) = l"
proof(rule list_induct_rule[OF assms])
  fix a l'
  assume h: "l' \<in> qbs_space (list_of X)"
     and ih:"from_list (to_list l') = l'"
  show "from_list (to_list (list_cons a l')) = list_cons a l'"
    by(auto simp add: to_list_simp2[OF h] ih[simplified])
qed (simp add: to_list_simp1)

definition rec_list' :: "'b \<Rightarrow> ('a \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'a)) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (nat \<times> (nat \<Rightarrow> 'a)) \<Rightarrow> 'b" where
"rec_list' t0 f l \<equiv> (rec_list t0 (\<lambda>x l'. f x (from_list l')) (to_list l))"

lemma rec_list'_simp1:
 "rec_list' t f list_nil = t"
  by(simp add: rec_list'_def to_list_simp1)

lemma rec_list'_simp2:
  assumes "l \<in> qbs_space (list_of X)"
  shows "rec_list' t f (list_cons x l) = f x l (rec_list' t f l)"
  by(simp add: rec_list'_def to_list_simp2[OF assms] to_list_from_list_ident[OF assms,simplified])

lemma list_qbs_space: "qbs_space (list_qbs X) = {l. set l \<subseteq> qbs_space X}"
  using to_list_set by(auto simp: list_qbs_def map_qbs_space image_def from_list_to_list_ident from_list_in_list_of intro!: bexI[where x="from_list _"])

subsubsection \<open> Option Spaces \<close>
text \<open> The option spaces is defined using the following isomorphism.
       \begin{align*}
         Option(X) \cong X + 1
       \end{align*}\<close>
definition option_qbs :: "'a quasi_borel \<Rightarrow> 'a option quasi_borel" where
"option_qbs X = map_qbs (\<lambda>x. case x of Inl y \<Rightarrow> Some y | Inr y \<Rightarrow> None) (X \<Oplus>\<^sub>Q 1\<^sub>Q)"

lemma option_qbs_space: "qbs_space (option_qbs X) = {Some x|x. x \<in> qbs_space X} \<union> {None}"
  by(auto simp: option_qbs_def map_qbs_space copair_qbs_space) (metis InrI image_eqI insert_iff old.sum.simps(6), metis InlI image_iff sum.case(1))

subsubsection \<open> Function Spaces \<close>
definition exp_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<Rightarrow> 'b) quasi_borel" (infixr "\<Rightarrow>\<^sub>Q" 61) where
"X \<Rightarrow>\<^sub>Q Y \<equiv> Abs_quasi_borel ({f. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}, {g. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y})"

lemma
  shows exp_qbs_space: "qbs_space (exp_qbs X Y) = {f. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}"
    and exp_qbs_Mx: "qbs_Mx (exp_qbs X Y) = {g. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y}"
proof -
  have "{g:: real \<Rightarrow> _. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y} \<subseteq> UNIV \<rightarrow> {f. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}"
  proof safe
    fix g :: "real \<Rightarrow> _" and r :: real and \<alpha>
    assume h:"\<forall>\<alpha>\<in>borel_measurable borel. \<forall>\<beta>\<in>qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y" "\<alpha> \<in> qbs_Mx X"
    have [simp]: "g r \<circ> \<alpha> = (\<lambda>l. g r (\<alpha> l))" by (auto simp: comp_def)
    thus "g r \<circ> \<alpha> \<in> qbs_Mx Y"
      using h by auto
  qed
  moreover have "qbs_closed3 {g. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y}"
    by(rule qbs_closed3I, auto) (rule qbs_closed3_dest,auto)
  ultimately have "Rep_quasi_borel (exp_qbs X Y) = ({f. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}, {g. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y})"
    unfolding exp_qbs_def by(auto intro!: Abs_quasi_borel_inverse is_quasi_borel_intro qbs_closed1I qbs_closed2I simp: comp_def)
  thus "qbs_space (exp_qbs X Y) = {f. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}"
       "qbs_Mx (exp_qbs X Y) = {g. \<forall>\<alpha>\<in> borel_measurable borel. \<forall>\<beta>\<in> qbs_Mx X. (\<lambda>r. g (\<alpha> r) (\<beta> r)) \<in> qbs_Mx Y}"
    by(simp_all add: qbs_space_def qbs_Mx_def)
qed

subsubsection \<open> Ordering on Quasi-Borel Spaces \<close>

inductive_set generating_Mx :: "'a set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set"
  for X :: "'a set" and Mx :: "(real \<Rightarrow> 'a) set"
  where
    Basic: "\<alpha> \<in> Mx \<Longrightarrow> \<alpha> \<in> generating_Mx X Mx"
  | Const: "x \<in> X \<Longrightarrow> (\<lambda>r. x) \<in> generating_Mx X Mx"
  | Comp : "f \<in> (borel :: real measure) \<rightarrow>\<^sub>M (borel :: real measure) \<Longrightarrow> \<alpha> \<in> generating_Mx X Mx \<Longrightarrow> \<alpha> \<circ> f \<in> generating_Mx X Mx"
  | Part : "(\<And>i. Fi i \<in> generating_Mx X Mx) \<Longrightarrow> P \<in> borel \<rightarrow>\<^sub>M count_space (UNIV :: nat set) \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> generating_Mx X Mx"

lemma generating_Mx_to_space:
  assumes "Mx \<subseteq> UNIV \<rightarrow> X"
  shows "generating_Mx X Mx \<subseteq> UNIV \<rightarrow> X"
proof
  fix \<alpha>
  assume "\<alpha> \<in> generating_Mx X Mx"
  then show "\<alpha> \<in> UNIV \<rightarrow> X"
   by(induct rule: generating_Mx.induct) (use assms in auto)
qed

lemma generating_Mx_closed1:
 "qbs_closed1 (generating_Mx X Mx)"
  by (simp add: generating_Mx.Comp qbs_closed1I)

lemma generating_Mx_closed2:
 "qbs_closed2 X (generating_Mx X Mx)"
  by (simp add: generating_Mx.Const qbs_closed2I)

lemma generating_Mx_closed3:
 "qbs_closed3 (generating_Mx X Mx)"
  by(simp add: qbs_closed3I generating_Mx.Part)

lemma generating_Mx_Mx:
 "generating_Mx (qbs_space X) (qbs_Mx X) = qbs_Mx X"
proof safe
  fix \<alpha>
  assume "\<alpha> \<in> generating_Mx (qbs_space X) (qbs_Mx X)"
  then show "\<alpha> \<in> qbs_Mx X"
    by(rule generating_Mx.induct) (auto intro!: qbs_closed1_dest[simplified comp_def] simp: qbs_closed3_dest')
next
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  then show "\<alpha> \<in> generating_Mx (qbs_space X) (qbs_Mx X)" ..
qed

instantiation quasi_borel :: (type) order_bot
begin

inductive less_eq_quasi_borel :: "'a quasi_borel \<Rightarrow> 'a quasi_borel \<Rightarrow> bool" where
  "qbs_space X \<subset> qbs_space Y \<Longrightarrow> less_eq_quasi_borel X Y"
| "qbs_space X = qbs_space Y \<Longrightarrow> qbs_Mx Y \<subseteq> qbs_Mx X \<Longrightarrow> less_eq_quasi_borel X Y"

lemma le_quasi_borel_iff:
 "X \<le> Y \<longleftrightarrow> (if qbs_space X = qbs_space Y then qbs_Mx Y \<subseteq> qbs_Mx X else qbs_space X \<subset> qbs_space Y)"
  by(auto elim: less_eq_quasi_borel.cases intro: less_eq_quasi_borel.intros)

definition less_quasi_borel :: "'a quasi_borel \<Rightarrow> 'a quasi_borel \<Rightarrow> bool" where
 "less_quasi_borel X Y \<longleftrightarrow> (X \<le> Y \<and> \<not> Y \<le> X)"

definition bot_quasi_borel :: "'a quasi_borel" where
 "bot_quasi_borel = empty_quasi_borel"

instance
proof
  show "bot \<le> a" for a :: "'a quasi_borel"
    using qbs_empty_equiv
    by(auto simp add: le_quasi_borel_iff bot_quasi_borel_def)
qed (auto simp: le_quasi_borel_iff less_quasi_borel_def split: if_split_asm intro: qbs_eqI)
end

definition inf_quasi_borel :: "['a quasi_borel, 'a quasi_borel] \<Rightarrow> 'a quasi_borel" where
"inf_quasi_borel X X' = Abs_quasi_borel (qbs_space X \<inter> qbs_space X', qbs_Mx X \<inter> qbs_Mx X')"

lemma inf_quasi_borel_correct: "Rep_quasi_borel (inf_quasi_borel X X') = (qbs_space X \<inter> qbs_space X', qbs_Mx X \<inter> qbs_Mx X')"
  by(auto intro!: Abs_quasi_borel_inverse  simp: inf_quasi_borel_def is_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def dest: qbs_Mx_to_X)

lemma inf_qbs_space[simp]: "qbs_space (inf_quasi_borel X X') = qbs_space X \<inter> qbs_space X'"
  by (simp add: qbs_space_def inf_quasi_borel_correct)

lemma inf_qbs_Mx[simp]: "qbs_Mx (inf_quasi_borel X X') = qbs_Mx X \<inter> qbs_Mx X'"
  by(simp add: qbs_Mx_def inf_quasi_borel_correct)

definition max_quasi_borel :: "'a set \<Rightarrow> 'a quasi_borel" where
"max_quasi_borel X = Abs_quasi_borel (X, UNIV \<rightarrow> X)"

lemma max_quasi_borel_correct: "Rep_quasi_borel (max_quasi_borel X) = (X, UNIV \<rightarrow> X)"
  by(fastforce intro!: Abs_quasi_borel_inverse
   simp: max_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)

lemma max_qbs_space[simp]: "qbs_space (max_quasi_borel X) = X"
  by(simp add: qbs_space_def max_quasi_borel_correct)

lemma max_qbs_Mx[simp]: "qbs_Mx (max_quasi_borel X) = UNIV \<rightarrow> X"
  by(simp add: qbs_Mx_def max_quasi_borel_correct)

instantiation quasi_borel :: (type) semilattice_sup
begin

definition sup_quasi_borel :: "'a quasi_borel \<Rightarrow> 'a quasi_borel \<Rightarrow> 'a quasi_borel" where
"sup_quasi_borel X Y \<equiv> (if qbs_space X = qbs_space Y      then inf_quasi_borel X Y
                        else if qbs_space X \<subset> qbs_space Y then Y
                        else if qbs_space Y \<subset> qbs_space X then X
                        else max_quasi_borel (qbs_space X \<union> qbs_space Y))"


instance
proof
  fix X Y :: "'a quasi_borel"
  let ?X = "qbs_space X"
  let ?Y = "qbs_space Y"
  consider "?X = ?Y" | "?X \<subset> ?Y" | "?Y \<subset> ?X" | "?X \<subset> ?X \<union> ?Y \<and> ?Y \<subset> ?X \<union> ?Y"
    by auto
  then show "X \<le> X \<squnion> Y"
  proof(cases)
    case 1
    show ?thesis
      unfolding sup_quasi_borel_def
      by(rule less_eq_quasi_borel.intros(2),simp_all add: 1)
  next
    case 2
    then show ?thesis
      unfolding sup_quasi_borel_def
      by (simp add: less_eq_quasi_borel.intros(1))
  next
    case 3
    then show ?thesis
      unfolding sup_quasi_borel_def
      by auto
  next
    case 4
    then show ?thesis
      unfolding sup_quasi_borel_def
      by(auto simp: less_eq_quasi_borel.intros(1))
  qed
next
  fix X Y :: "'a quasi_borel"
  let ?X = "qbs_space X"
  let ?Y = "qbs_space Y"
  consider "?X = ?Y" | "?X \<subset> ?Y" | "?Y \<subset> ?X" | "?X \<subset> ?X \<union> ?Y \<and> ?Y \<subset> ?X \<union> ?Y"
    by auto
  then show "Y \<le> X \<squnion> Y"
  proof(cases)
    case 1
    show ?thesis
      unfolding sup_quasi_borel_def
      by(rule less_eq_quasi_borel.intros(2)) (simp_all add: 1)
  next
    case 2
    then show ?thesis
      unfolding sup_quasi_borel_def
      by auto
  next
    case 3
    then show ?thesis
      unfolding sup_quasi_borel_def
      by (auto simp add: less_eq_quasi_borel.intros(1))
  next
    case 4
    then show ?thesis
      unfolding sup_quasi_borel_def
      by(auto simp: less_eq_quasi_borel.intros(1))
  qed
next
  fix X Y Z :: "'a quasi_borel"
  assume h:"X \<le> Z" "Y \<le> Z"
  let ?X = "qbs_space X"
  let ?Y = "qbs_space Y"
  let ?Z = "qbs_space Z"
  consider "?X = ?Y" | "?X \<subset> ?Y" | "?Y \<subset> ?X" | "?X \<subset> ?X \<union> ?Y \<and> ?Y \<subset> ?X \<union> ?Y"
    by auto
  then show "sup X Y \<le> Z"
  proof cases
    case 1
    show ?thesis
      unfolding sup_quasi_borel_def
      apply(simp add: 1,rule less_eq_quasi_borel.cases[OF h(1)])
       apply(rule less_eq_quasi_borel.intros(1))
       apply auto[1]
      apply simp
      apply(rule less_eq_quasi_borel.intros(2))
       apply(simp add: 1)
      apply(rule less_eq_quasi_borel.cases[OF h(2)])
      using 1
        apply fastforce
       apply simp
      by (metis "1" h(2) inf_qbs_Mx le_inf_iff le_quasi_borel_iff)
      
  next
    case 2
    then show ?thesis
      unfolding sup_quasi_borel_def
      using h(2) by auto
  next
    case 3
    then show ?thesis
      unfolding sup_quasi_borel_def
      using h(1) by auto
  next
    case 4
    then have [simp]:"?X \<noteq> ?Y" "~ (?X \<subset> ?Y)" "~ (?Y \<subset> ?X)"
      by auto
    have [simp]:"?X \<subseteq> ?Z" "?Y \<subseteq> ?Z"
      by (metis h(1) dual_order.order_iff_strict less_eq_quasi_borel.cases)
         (metis h(2) dual_order.order_iff_strict less_eq_quasi_borel.cases)
    then consider "?X \<union> ?Y = ?Z" | "?X \<union> ?Y \<subset> ?Z"
      by blast
    then show ?thesis
      unfolding sup_quasi_borel_def
      apply cases
       apply simp
       apply(rule less_eq_quasi_borel.intros(2))
        apply simp
      using qbs_Mx_to_X apply auto[1]
      by(simp add: less_eq_quasi_borel.intros(1))
  qed
qed

end

end