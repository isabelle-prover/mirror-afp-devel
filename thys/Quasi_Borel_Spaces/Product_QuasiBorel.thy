(*  Title:   Product_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsubsection \<open> Product Spaces\<close>
theory Product_QuasiBorel

imports "Binary_Product_QuasiBorel"

begin

definition prod_qbs_Mx :: "['a set, 'a \<Rightarrow> 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'b) set" where
"prod_qbs_Mx I M \<equiv> { \<alpha> | \<alpha>. \<forall>i. (i \<in> I \<longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (M i)) \<and> (i \<notin> I \<longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined))}"

lemma prod_qbs_MxI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (M i)"
      and "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined)"
    shows "\<alpha> \<in> prod_qbs_Mx I M"
  using assms by(auto simp: prod_qbs_Mx_def)

lemma prod_qbs_MxE:
  assumes "\<alpha> \<in> prod_qbs_Mx I M"
  shows "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) \<in> qbs_Mx (M i)"
    and "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. \<alpha> r i) = (\<lambda>r. undefined)"
    and "\<And>i r. i \<notin> I \<Longrightarrow> \<alpha> r i = undefined"
  using assms by(auto simp: prod_qbs_Mx_def dest: fun_cong[where g="(\<lambda>r. undefined)"])

definition PiQ :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b quasi_borel) \<Rightarrow> ('a \<Rightarrow> 'b) quasi_borel" where
"PiQ I M \<equiv> Abs_quasi_borel (\<Pi>\<^sub>E i\<in>I. qbs_space (M i), prod_qbs_Mx I M)"

syntax
  "_PiQ" :: "pttrn \<Rightarrow> 'i set \<Rightarrow> 'a quasi_borel \<Rightarrow> ('i => 'a) quasi_borel"  ("(3\<Pi>\<^sub>Q _\<in>_./ _)"  10)
translations
  "\<Pi>\<^sub>Q x\<in>I. M" == "CONST PiQ I (\<lambda>x. M)"


lemma PiQ_f: "prod_qbs_Mx I M \<subseteq> UNIV \<rightarrow> (\<Pi>\<^sub>E i\<in>I. qbs_space (M i))"
  using prod_qbs_MxE by fastforce

lemma PiQ_closed1: "qbs_closed1 (prod_qbs_Mx I M)"
proof(rule qbs_closed1I)
  fix \<alpha> f
  assume h:"\<alpha> \<in> prod_qbs_Mx I M "
           "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
  show "\<alpha> \<circ> f \<in> prod_qbs_Mx I M"
  proof(rule prod_qbs_MxI)
    fix i
    assume "i \<in> I"
    from prod_qbs_MxE(1)[OF h(1) this]
    have "(\<lambda>r. \<alpha> r i) \<circ> f \<in> qbs_Mx (M i)"
      using h(2) by auto
    thus "(\<lambda>r. (\<alpha> \<circ> f) r i) \<in> qbs_Mx (M i)"
      by(simp add: comp_def)
  next
    fix i
    assume "i \<notin> I"
    from prod_qbs_MxE(3)[OF h(1) this]
    show "(\<lambda>r. (\<alpha> \<circ> f) r i) = (\<lambda>r. undefined)"
      by simp
  qed
qed

lemma PiQ_closed2: "qbs_closed2 (\<Pi>\<^sub>E i\<in>I. qbs_space (M i)) (prod_qbs_Mx I M)"
proof(rule qbs_closed2I)
  fix x
  assume h:"x \<in> (\<Pi>\<^sub>E i\<in>I. qbs_space (M i))"
  show "(\<lambda>r. x) \<in> prod_qbs_Mx I M"
  proof(rule prod_qbs_MxI)
    fix i
    assume hi:"i \<in> I"
    then have "x i \<in> qbs_space (M i)"
      using h by auto
    thus "(\<lambda>r. x i) \<in> qbs_Mx (M i)"
      by auto
  next
    show "\<And>i. i \<notin> I \<Longrightarrow> (\<lambda>r. x i) = (\<lambda>r. undefined)"
      using h by auto
  qed
qed

lemma PiQ_closed3: "qbs_closed3 (prod_qbs_Mx I M)"
proof(rule qbs_closed3I)
  fix P Fi
  assume h:"\<And>i::nat. P -` {i} \<in> sets real_borel"
           "\<And>i::nat. Fi i \<in> prod_qbs_Mx I M"
  show "(\<lambda>r. Fi (P r) r) \<in> prod_qbs_Mx I M"
  proof(rule prod_qbs_MxI)
    fix i
    assume hi:"i \<in> I"
    show "(\<lambda>r. Fi (P r) r i) \<in> qbs_Mx (M i)"
      using prod_qbs_MxE(1)[OF h(2) hi] qbs_closed3_dest[OF h(1),of "\<lambda>j r. Fi j r i"]
      by auto
  next
    show "\<And>i. i \<notin> I \<Longrightarrow>
         (\<lambda>r. Fi (P r) r i) = (\<lambda>r. undefined)"
      using prod_qbs_MxE[OF h(2)] by auto
  qed
qed

lemma PiQ_correct: "Rep_quasi_borel (PiQ I M) = (\<Pi>\<^sub>E i\<in>I. qbs_space (M i), prod_qbs_Mx I M)"
  by(auto intro!: Abs_quasi_borel_inverse PiQ_f is_quasi_borel_intro simp: PiQ_def PiQ_closed1 PiQ_closed2 PiQ_closed3)

lemma PiQ_space[simp]: "qbs_space (PiQ I M) = (\<Pi>\<^sub>E i\<in>I. qbs_space (M i))"
  by(simp add: qbs_space_def PiQ_correct)

lemma PiQ_Mx[simp]: "qbs_Mx (PiQ I M) = prod_qbs_Mx I M"
  by(simp add: qbs_Mx_def PiQ_correct)


lemma qbs_morphism_component_singleton:
  assumes "i \<in> I"
  shows "(\<lambda>x. x i) \<in> (\<Pi>\<^sub>Q i\<in>I. (M i)) \<rightarrow>\<^sub>Q M i"
  by(auto intro!: qbs_morphismI simp: prod_qbs_Mx_def comp_def assms)

lemma product_qbs_canonical1:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> Y \<rightarrow>\<^sub>Q X i"
      and "\<And>i. i \<notin> I \<Longrightarrow> f i = (\<lambda>y. undefined)"
    shows "(\<lambda>y i. f i y) \<in> Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. X i)"
  using qbs_morphismE(3)[simplified comp_def,OF assms(1)] assms(2)
  by(auto intro!: qbs_morphismI prod_qbs_MxI)

lemma product_qbs_canonical2:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> Y \<rightarrow>\<^sub>Q X i"
          "\<And>i. i \<notin> I \<Longrightarrow> f i = (\<lambda>y. undefined)"
          "g \<in> Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I. X i)"
          "\<And>i. i \<in> I \<Longrightarrow> f i = (\<lambda>x. x i) \<circ> g"
      and "y \<in> qbs_space Y"
    shows "g y = (\<lambda>i. f i y)"
proof(rule ext)+
  fix i
  show "g y i = f i y"
  proof(cases "i \<in> I")
    case True
    then show ?thesis
      using assms(4)[of i] by simp
  next
    case False
    moreover have "(\<lambda>r. y) \<in> qbs_Mx Y"
      using assms(5) by simp
    ultimately show ?thesis
      using assms(2,3) qbs_morphismE(3)[OF assms(3) _]
      by(fastforce simp: prod_qbs_Mx_def)
  qed
qed

lemma merge_qbs_morphism:
 "merge I J \<in> (\<Pi>\<^sub>Q i\<in>I. (M i)) \<Otimes>\<^sub>Q (\<Pi>\<^sub>Q j\<in>J. (M j)) \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>I\<union>J. (M i))"
proof(rule qbs_morphismI)
  fix \<alpha>
  assume h:"\<alpha> \<in> qbs_Mx ((\<Pi>\<^sub>Q i\<in>I. (M i)) \<Otimes>\<^sub>Q (\<Pi>\<^sub>Q j\<in>J. (M j)))"
  show "merge I J \<circ> \<alpha> \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>I\<union>J. (M i))"
  proof(simp, rule prod_qbs_MxI)
    fix i
    assume "i \<in> I \<union> J"
    then consider "i \<in> I" | "i \<in> I \<and> i \<in> J" | "i \<notin> I \<and> i \<in> J"
      by auto
    then show "(\<lambda>r. (merge I J \<circ> \<alpha>) r i) \<in> qbs_Mx (M i)"
      apply cases
      using h
      by(auto simp: merge_def pair_qbs_Mx_def split_beta' dest: prod_qbs_MxE)
  next
    fix i
    assume "i \<notin> I \<union> J"
    then show "(\<lambda>r. (merge I J \<circ> \<alpha>) r i) = (\<lambda>r. undefined)"
      using h
      by(auto simp: merge_def pair_qbs_Mx_def split_beta' dest: prod_qbs_MxE )
  qed
qed

text \<open> The following lemma corresponds to \<^cite>\<open>"Heunen_2017"\<close> Proposition 19(1). \<close>
lemma r_preserves_product':
  "measure_to_qbs (\<Pi>\<^sub>M i\<in>I. M i) = (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
proof(rule qbs_eqI)
  show "qbs_Mx (measure_to_qbs (Pi\<^sub>M I M)) = qbs_Mx (\<Pi>\<^sub>Q i\<in>I. measure_to_qbs (M i))"
  proof auto
    fix f
    assume h:"f \<in> real_borel \<rightarrow>\<^sub>M Pi\<^sub>M I M"
    show "f \<in> prod_qbs_Mx I (\<lambda>i. measure_to_qbs (M i))"
    proof(rule prod_qbs_MxI)
      fix i
      assume 1:"i \<in> I"
      show "(\<lambda>r. f r i) \<in> qbs_Mx (measure_to_qbs (M i))"
        using measurable_comp[OF h measurable_component_singleton[OF 1,of M]]
        by (simp add: comp_def)
    next
      fix i
      assume 1:"i \<notin> I"
      then show "(\<lambda>r. f r i) = (\<lambda>r. undefined)"
        using measurable_space[OF h] 1
        by(auto simp: space_PiM PiE_def extensional_def)
    qed
  next
    fix f
    assume h:"f \<in> prod_qbs_Mx I (\<lambda>i. measure_to_qbs (M i))"
    show "f \<in> real_borel \<rightarrow>\<^sub>M Pi\<^sub>M I M"
      apply(rule measurable_PiM_single')
      using prod_qbs_MxE(1)[OF h] apply auto[1]
      using PiQ_f[of I M] h by auto
  qed
qed

text \<open> $\prod_{i = 0,1} X_i \cong X_1 \times X_2$. \<close>
lemma product_binary_product:
 "\<exists>f g. f \<in> (\<Pi>\<^sub>Q i\<in>UNIV. if i then X else Y) \<rightarrow>\<^sub>Q X \<Otimes>\<^sub>Q Y \<and> g \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q (\<Pi>\<^sub>Q i\<in>UNIV. if i then X else Y) \<and>
        g \<circ> f = id \<and> f \<circ> g = id"
  by(auto intro!: exI[where x="\<lambda>f. (f True, f False)"] exI[where x="\<lambda>xy b. if b then fst xy else snd xy"] qbs_morphismI
            simp: prod_qbs_Mx_def pair_qbs_Mx_def comp_def all_bool_eq ext)

end