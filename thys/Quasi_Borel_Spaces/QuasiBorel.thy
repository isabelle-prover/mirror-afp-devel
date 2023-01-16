(*  Title:   QuasiBorel.thy
    Author:  Yasuhiko Minamide, Michikazu Hirata, Tokyo Institute of Technology
*)

section \<open>Quasi-Borel Spaces\<close>
theory QuasiBorel
imports "StandardBorel"
begin

subsection \<open> Definitions \<close>

text \<open> We formalize quasi-Borel spaces introduced by Heunen et al.~\<^cite>\<open>"Heunen_2017"\<close>.\<close>

subsubsection \<open> Quasi-Borel Spaces\<close>
definition qbs_closed1 :: "(real \<Rightarrow> 'a) set \<Rightarrow> bool"
  where "qbs_closed1 Mx \<equiv> (\<forall>a \<in> Mx. \<forall>f \<in> real_borel \<rightarrow>\<^sub>M real_borel. a \<circ> f \<in> Mx)"

definition qbs_closed2 :: "['a set, (real \<Rightarrow> 'a) set] \<Rightarrow> bool"
 where "qbs_closed2 X Mx \<equiv> (\<forall>x \<in> X. (\<lambda>r. x) \<in> Mx)"

definition qbs_closed3 :: "(real \<Rightarrow> 'a) set \<Rightarrow> bool"
 where "qbs_closed3 Mx \<equiv> (\<forall>P::real \<Rightarrow> nat. \<forall>Fi::nat \<Rightarrow> real \<Rightarrow> 'a.
                          (\<forall>i. P -` {i} \<in> sets real_borel)
                           \<longrightarrow> (\<forall>i. Fi i \<in> Mx)
                           \<longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx)"

lemma separate_measurable:
  fixes P :: "real \<Rightarrow> nat"
  assumes "\<And>i. P -` {i} \<in> sets real_borel"
  shows "P \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
proof -
  have "P \<in> real_borel \<rightarrow>\<^sub>M count_space UNIV"
    by (auto simp add: assms measurable_count_space_eq_countable)
  thus ?thesis
    using measurable_cong_sets sets_borel_eq_count_space by blast
qed

lemma measurable_separate:
  fixes P :: "real \<Rightarrow> nat"
  assumes "P \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
  shows "P -` {i} \<in> sets real_borel"
  by(rule measurable_sets_borel[OF assms borel_singleton[OF sets.empty_sets,of i]])

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

lemma qbs_decomp : 
"(qbs_space X,qbs_Mx X) \<in> {(X::'a set, Mx). is_quasi_borel X Mx}"
  by (simp add: qbs_space_def qbs_Mx_def Rep_quasi_borel[simplified])

lemma qbs_Mx_to_X[dest]:
  assumes "\<alpha> \<in> qbs_Mx X"
  shows "\<alpha> \<in> UNIV \<rightarrow> qbs_space X"
        "\<alpha> r \<in> qbs_space X"
  using qbs_decomp assms by(auto simp: is_quasi_borel_def)


lemma qbs_closed1I:
  assumes "\<And>\<alpha> f. \<alpha> \<in> Mx \<Longrightarrow> f \<in> real_borel \<rightarrow>\<^sub>M real_borel \<Longrightarrow> \<alpha> \<circ> f \<in> Mx"
  shows "qbs_closed1 Mx"
  using assms by(simp add: qbs_closed1_def)

lemma qbs_closed1_dest[simp]:
  assumes "\<alpha> \<in> qbs_Mx X"
      and "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
    shows "\<alpha> \<circ> f \<in> qbs_Mx X"
  using assms qbs_decomp by (auto simp add: is_quasi_borel_def qbs_closed1_def)

lemma qbs_closed2I:
  assumes "\<And>x. x \<in> X \<Longrightarrow> (\<lambda>r. x) \<in> Mx"
  shows "qbs_closed2 X Mx"
  using assms by(simp add: qbs_closed2_def)

lemma qbs_closed2_dest[simp]:
  assumes "x \<in> qbs_space X"
  shows "(\<lambda>r. x) \<in> qbs_Mx X"
  using assms qbs_decomp[of X] by (auto simp add: is_quasi_borel_def qbs_closed2_def)

lemma qbs_closed3I:
  assumes "\<And>(P :: real \<Rightarrow> nat) Fi. (\<And>i. P -` {i} \<in> sets real_borel) \<Longrightarrow> (\<And>i. Fi i \<in> Mx)
                  \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx"
  shows "qbs_closed3 Mx"
  using assms by(auto simp: qbs_closed3_def)

lemma qbs_closed3I':
  assumes "\<And>(P :: real \<Rightarrow> nat) Fi. P \<in> real_borel \<rightarrow>\<^sub>M nat_borel \<Longrightarrow> (\<And>i. Fi i \<in> Mx)
                  \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> Mx"
  shows "qbs_closed3 Mx"
  using assms by(auto intro!: qbs_closed3I simp: separate_measurable)

lemma qbs_closed3_dest[simp]:
  fixes P::"real \<Rightarrow> nat" and Fi :: "nat \<Rightarrow> real \<Rightarrow> _"
  assumes "\<And>i. P -` {i} \<in> sets real_borel"
      and "\<And>i. Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
  using assms qbs_decomp[of X] by (auto simp add: is_quasi_borel_def qbs_closed3_def)

lemma qbs_closed3_dest':
  fixes P::"real \<Rightarrow> nat" and Fi :: "nat \<Rightarrow> real \<Rightarrow> _"
  assumes "P \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
      and "\<And>i. Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
  using qbs_closed3_dest[OF measurable_separate[OF assms(1)] assms(2)] .

lemma qbs_closed3_dest2:
  assumes "countable I"
 and [measurable]: "P \<in> real_borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> I \<Longrightarrow> Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
proof -
  have 0:"I \<noteq> {}"
    using measurable_empty_iff[of "count_space I" P real_borel] assms(2)
    by fastforce
  define P' where "P' \<equiv> to_nat_on I \<circ> P"
  define Fi' where "Fi' \<equiv> Fi \<circ> (from_nat_into I)"
  have 1:"P' \<in> real_borel \<rightarrow>\<^sub>M nat_borel"
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
 and [measurable]: "P \<in> real_borel \<rightarrow>\<^sub>M count_space I"
      and "\<And>i. i \<in> range P \<Longrightarrow> Fi i \<in> qbs_Mx X"
    shows "(\<lambda>r. Fi (P r) r) \<in> qbs_Mx X"
proof -
  have 0:"range P \<inter> I = range P"
    using measurable_space[OF assms(2)] by auto
  have 1:"P \<in> real_borel \<rightarrow>\<^sub>M count_space (range P)"
    using restrict_count_space[of I "range P"] measurable_restrict_space2[OF _ assms(2),of "range P"]
    by(simp add: 0)
  have 2:"countable (range P)"
    using countable_Int2[OF assms(1),of "range P"]
    by(simp add: 0)
  show ?thesis
    by(auto intro!: qbs_closed3_dest2[OF 2 1 assms(3)])
qed

lemma qbs_space_Mx:
 "qbs_space X = {\<alpha> x |x \<alpha>. \<alpha> \<in> qbs_Mx X}"
proof auto
  fix x
  assume 1:"x \<in> qbs_space X"
  show "\<exists>xa \<alpha>. x = \<alpha> xa \<and> \<alpha> \<in> qbs_Mx X"
    by(auto intro!: exI[where x=0] exI[where x="(\<lambda>r. x)"] simp: 1)
qed

lemma qbs_space_eq_Mx:
  assumes "qbs_Mx X = qbs_Mx Y"
  shows "qbs_space X = qbs_space Y"
  by(simp add: qbs_space_Mx assms)

lemma qbs_eqI:
  assumes "qbs_Mx X = qbs_Mx Y"
  shows "X = Y"
  by (metis Rep_quasi_borel_inverse prod.exhaust_sel qbs_Mx_def qbs_space_def assms qbs_space_eq_Mx[OF assms])


subsubsection \<open> Morphism of Quasi-Borel Spaces \<close>
definition qbs_morphism :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>Q" 60) where 
  "X \<rightarrow>\<^sub>Q Y \<equiv> {f \<in> qbs_space X \<rightarrow> qbs_space Y. \<forall>\<alpha> \<in> qbs_Mx X. f \<circ> \<alpha> \<in> qbs_Mx Y}"

lemma qbs_morphismI:
  assumes "\<And>\<alpha>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> f \<circ> \<alpha> \<in> qbs_Mx Y"
  shows "f \<in> X \<rightarrow>\<^sub>Q Y"
proof -
  have "f \<in> qbs_space X \<rightarrow> qbs_space Y"
  proof
    fix x
    assume "x \<in> qbs_space X "
    then have "(\<lambda>r. x) \<in> qbs_Mx X"
      by simp
    hence "f \<circ> (\<lambda>r. x) \<in> qbs_Mx Y"
      using assms by blast
    thus "f x \<in> qbs_space Y"
      by auto
  qed
  thus ?thesis
    using assms by(simp add: qbs_morphism_def)
qed

lemma qbs_morphismE[dest]:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y"
  shows "f \<in> qbs_space X \<rightarrow> qbs_space Y"
        "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x \<in> qbs_space Y"
        "\<And>\<alpha>. \<alpha> \<in> qbs_Mx X \<Longrightarrow> f \<circ> \<alpha> \<in> qbs_Mx Y"
  using assms by(auto simp add: qbs_morphism_def)

lemma qbs_morphism_ident[simp]:
   "id \<in> X \<rightarrow>\<^sub>Q X"
  by(auto intro: qbs_morphismI)

lemma qbs_morphism_ident'[simp]:
   "(\<lambda>x. x) \<in> X \<rightarrow>\<^sub>Q X"
  using qbs_morphism_ident by(simp add: id_def)


lemma qbs_morphism_comp:
  assumes "f \<in> X \<rightarrow>\<^sub>Q Y" "g \<in> Y \<rightarrow>\<^sub>Q Z"
  shows "g \<circ> f \<in> X \<rightarrow>\<^sub>Q Z"
  using assms by (simp add: comp_assoc Pi_def qbs_morphism_def)

lemma qbs_morphism_cong:
  assumes "\<And>x. x \<in> qbs_space X \<Longrightarrow> f x = g x"
      and "f \<in> X \<rightarrow>\<^sub>Q Y"
    shows "g \<in> X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume 1:"\<alpha> \<in> qbs_Mx X"
  have "g \<circ> \<alpha> = f \<circ> \<alpha>"
  proof
    fix x
    have "\<alpha> x \<in> qbs_space X"
      using 1 qbs_decomp[of X] by auto
    thus "(g \<circ> \<alpha>) x = (f \<circ> \<alpha>) x"
      using assms(1) by simp
  qed
  thus "g \<circ> \<alpha> \<in> qbs_Mx Y"
    using 1 assms(2) by(simp add: qbs_morphism_def)
qed

lemma qbs_morphism_const:
  assumes "y \<in> qbs_space Y"
  shows "(\<lambda>_. y) \<in> X \<rightarrow>\<^sub>Q Y"
  using assms by (auto intro: qbs_morphismI)


subsubsection \<open> Empty Space \<close>
definition empty_quasi_borel  :: "'a quasi_borel" where
"empty_quasi_borel \<equiv> Abs_quasi_borel ({},{})"

lemma eqb_correct: "Rep_quasi_borel empty_quasi_borel = ({}, {})"
  using Abs_quasi_borel_inverse
  by(auto simp add: Abs_quasi_borel_inverse empty_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)

lemma eqb_space[simp]: "qbs_space empty_quasi_borel = {}"
  by(simp add: qbs_space_def eqb_correct)

lemma eqb_Mx[simp]: "qbs_Mx empty_quasi_borel = {}"
  by(simp add: qbs_Mx_def eqb_correct)

lemma qbs_empty_equiv :"qbs_space X = {} \<longleftrightarrow> qbs_Mx X = {}"
proof(auto)
  fix x
  assume "qbs_Mx X = {}"
     and h:"x \<in> qbs_space X"
  have "(\<lambda>r. x) \<in> qbs_Mx X"
    using h by simp
  thus "False" using \<open>qbs_Mx X = {}\<close> by simp
qed

lemma empty_quasi_borel_iff:
  "qbs_space X = {} \<longleftrightarrow> X = empty_quasi_borel"
  by(auto intro!: qbs_eqI)

subsubsection \<open> Unit Space \<close>
definition unit_quasi_borel :: "unit quasi_borel" ("1\<^sub>Q") where
"unit_quasi_borel \<equiv> Abs_quasi_borel (UNIV,UNIV)"

lemma uqb_correct: "Rep_quasi_borel unit_quasi_borel = (UNIV,UNIV)"
  using Abs_quasi_borel_inverse
  by(auto simp add: unit_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def is_quasi_borel_def)

lemma uqb_space[simp]: "qbs_space unit_quasi_borel = {()}"
  by(simp add: qbs_space_def UNIV_unit uqb_correct)

lemma uqb_Mx[simp]: "qbs_Mx unit_quasi_borel = {\<lambda>r. ()}"
  by(auto simp add: qbs_Mx_def uqb_correct)

lemma unit_quasi_borel_terminal:
 "\<exists>! f. f \<in> X \<rightarrow>\<^sub>Q unit_quasi_borel"
  by(fastforce simp: qbs_morphism_def)

definition to_unit_quasi_borel :: "'a \<Rightarrow> unit" ("!\<^sub>Q") where
"to_unit_quasi_borel \<equiv> (\<lambda>_.())"

lemma to_unit_quasi_borel_morphism :
 "!\<^sub>Q \<in> X \<rightarrow>\<^sub>Q unit_quasi_borel"
  by(auto simp add: to_unit_quasi_borel_def qbs_morphism_def)

subsubsection \<open> Subspaces \<close>
definition sub_qbs :: "['a quasi_borel, 'a set] \<Rightarrow> 'a quasi_borel" where
"sub_qbs X U \<equiv> Abs_quasi_borel (qbs_space X \<inter> U,{f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X})"

lemma sub_qbs_closed:
  "qbs_closed1 {f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X}"
  "qbs_closed2 (qbs_space X \<inter> U) {f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X}"
  "qbs_closed3 {f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X}"
  unfolding qbs_closed1_def qbs_closed2_def qbs_closed3_def by auto

lemma sub_qbs_correct[simp]: "Rep_quasi_borel (sub_qbs X U) = (qbs_space X \<inter> U,{f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X})"
  by(simp add: Abs_quasi_borel_inverse sub_qbs_def sub_qbs_closed)

lemma sub_qbs_space[simp]: "qbs_space (sub_qbs X U) = qbs_space X \<inter> U"
  by(simp add: qbs_space_def)

lemma sub_qbs_Mx[simp]: "qbs_Mx (sub_qbs X U) = {f \<in> UNIV \<rightarrow> qbs_space X \<inter> U. f \<in> qbs_Mx X}"
  by(simp add: qbs_Mx_def)

lemma sub_qbs:
  assumes "U \<subseteq> qbs_space X"
  shows "(qbs_space (sub_qbs X U), qbs_Mx (sub_qbs X U)) = (U, {f \<in> UNIV \<rightarrow> U. f \<in> qbs_Mx X})"
  using assms by auto


subsubsection \<open> Image Spaces \<close>
definition map_qbs :: "['a \<Rightarrow> 'b] \<Rightarrow> 'a quasi_borel \<Rightarrow> 'b quasi_borel" where
"map_qbs f X = Abs_quasi_borel (f ` (qbs_space X),{\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>})"

lemma map_qbs_f:
 "{\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>} \<subseteq> UNIV \<rightarrow> f ` (qbs_space X)"
  by fastforce

lemma map_qbs_closed1:
 "qbs_closed1 {\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>}"
  unfolding qbs_closed1_def
  using qbs_closed1_dest by(fastforce simp: comp_def)

lemma map_qbs_closed2:
 "qbs_closed2 (f ` (qbs_space X)) {\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>}"
  unfolding qbs_closed2_def by fastforce

lemma map_qbs_closed3:
 "qbs_closed3 {\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>}"
proof(auto simp add: qbs_closed3_def)
  fix P Fi
  assume h:"\<forall>i::nat. P -` {i} \<in> sets real_borel"
           "\<forall>i::nat. \<exists>\<alpha>\<in>qbs_Mx X. Fi i = f \<circ> \<alpha>"
  then obtain \<alpha>i
    where ha: "\<forall>i::nat. \<alpha>i i \<in> qbs_Mx X \<and>  Fi i = f \<circ> (\<alpha>i i)"
    by metis
  hence 1:"(\<lambda>r. \<alpha>i (P r) r) \<in> qbs_Mx X"
    using h(1) by fastforce
  show "\<exists>\<alpha>\<in>qbs_Mx X. (\<lambda>r. Fi (P r) r) = f \<circ> \<alpha>"
    by(auto intro!: bexI[where x="(\<lambda>r. \<alpha>i (P r) r)"] simp add: 1 ha comp_def)
qed

lemma map_qbs_correct[simp]:
 "Rep_quasi_borel (map_qbs f X) = (f ` (qbs_space X),{\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>})"
  unfolding map_qbs_def
  by(simp add: Abs_quasi_borel_inverse map_qbs_f map_qbs_closed1 map_qbs_closed2 map_qbs_closed3)

lemma map_qbs_space[simp]:
 "qbs_space (map_qbs f X) = f ` (qbs_space X)"
  by(simp add: qbs_space_def)

lemma map_qbs_Mx[simp]:
 "qbs_Mx (map_qbs f X) = {\<beta>. \<exists>\<alpha>\<in> qbs_Mx X. \<beta> = f \<circ> \<alpha>}"
  by(simp add: qbs_Mx_def)


inductive_set generating_Mx :: "'a set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set"
  for X :: "'a set" and Mx :: "(real \<Rightarrow> 'a) set"
  where
    Basic: "\<alpha> \<in> Mx \<Longrightarrow> \<alpha> \<in> generating_Mx X Mx"
  | Const: "x \<in> X \<Longrightarrow> (\<lambda>r. x) \<in> generating_Mx X Mx"
  | Comp : "f \<in> real_borel \<rightarrow>\<^sub>M real_borel \<Longrightarrow> \<alpha> \<in> generating_Mx X Mx \<Longrightarrow> \<alpha> \<circ> f \<in> generating_Mx X Mx"
  | Part : "(\<And>i. Fi i \<in> generating_Mx X Mx) \<Longrightarrow> P \<in> real_borel \<rightarrow>\<^sub>M nat_borel \<Longrightarrow> (\<lambda>r. Fi (P r) r) \<in> generating_Mx X Mx"

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
  by(simp add: qbs_closed3I' generating_Mx.Part)

lemma generating_Mx_Mx:
 "generating_Mx (qbs_space X) (qbs_Mx X) = qbs_Mx X"
proof auto
  fix \<alpha>
  assume "\<alpha> \<in> generating_Mx (qbs_space X) (qbs_Mx X)"
  then show "\<alpha> \<in> qbs_Mx X"
    by(rule generating_Mx.induct) (auto intro!: qbs_closed1_dest[simplified comp_def] simp: qbs_closed3_dest')
next
  fix \<alpha>
  assume "\<alpha> \<in> qbs_Mx X"
  then show "\<alpha> \<in> generating_Mx (qbs_space X) (qbs_Mx X)" ..
qed


subsubsection \<open> Ordering of Quasi-Borel Spaces \<close>

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
  by(fastforce intro!: Abs_quasi_borel_inverse
     simp: inf_quasi_borel_def is_quasi_borel_def qbs_closed1_def qbs_closed2_def qbs_closed3_def)

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
      apply auto
      apply(rule less_eq_quasi_borel.intros(2))
       apply(simp add: 1)
      by(rule less_eq_quasi_borel.cases[OF h(2)]) (auto simp: 1)
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
       apply auto[1]
      by(simp add: less_eq_quasi_borel.intros(1))
  qed
qed
end

end