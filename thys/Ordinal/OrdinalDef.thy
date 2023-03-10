(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Definition of Ordinals\<close>

theory OrdinalDef
  imports Main
begin

subsection \<open>Preliminary datatype for ordinals\<close>

datatype ord0 = ord0_Zero | ord0_Lim "nat \<Rightarrow> ord0"

text \<open>subterm ordering on ord0\<close>

definition
  ord0_prec :: "(ord0 \<times> ord0) set" where
  "ord0_prec = (\<Union>f i. {(f i, ord0_Lim f)})"

lemma wf_ord0_prec: "wf ord0_prec"
proof -
  have "\<forall>x. (\<forall>y. (y, x) \<in> ord0_prec \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> P a" for P a
    unfolding ord0_prec_def by (induction a) blast+
  then show ?thesis
    by (metis wfUNIVI)
qed

lemmas ord0_prec_induct = wf_induct[OF wf_trancl[OF wf_ord0_prec]]

text \<open>less-than-or-equal ordering on ord0\<close>

inductive_set ord0_leq :: "(ord0 \<times> ord0) set" where
  "\<lbrakk>\<forall>a. (a,x) \<in> ord0_prec\<^sup>+ \<longrightarrow> (\<exists>b. (b,y) \<in> ord0_prec\<^sup>+ \<and> (a,b) \<in> ord0_leq)\<rbrakk>
  \<Longrightarrow> (x,y) \<in> ord0_leq"

lemma ord0_leqI:
  "\<lbrakk>\<forall>a. (a,x) \<in> ord0_prec\<^sup>+ \<longrightarrow> (a,y) \<in> ord0_leq O ord0_prec\<^sup>+\<rbrakk>
 \<Longrightarrow> (x,y) \<in> ord0_leq"
  by (meson ord0_leq.intros relcomp.cases)

lemma ord0_leqD:
  "\<lbrakk>(x,y) \<in> ord0_leq; (a,x) \<in> ord0_prec\<^sup>+\<rbrakk> \<Longrightarrow> (a,y) \<in> ord0_leq O ord0_prec\<^sup>+"
  by (ind_cases "(x,y) \<in> ord0_leq", auto)

lemma ord0_leq_refl: "(x, x) \<in> ord0_leq"
  by (rule ord0_prec_induct, rule ord0_leqI, auto)

lemma ord0_leq_trans:
  "(x,y) \<in> ord0_leq \<Longrightarrow> (y,z) \<in> ord0_leq \<Longrightarrow> (x,z) \<in> ord0_leq"
proof (induction x arbitrary: y z rule: ord0_prec_induct)
  case (1 x)
  then show ?case
    by (meson ord0_leq.cases ord0_leq.intros)
qed

lemma wf_ord0_leq: "wf (ord0_leq O ord0_prec\<^sup>+)"
  unfolding wf_def
proof clarify
  fix P x
  assume *: "\<forall>x. (\<forall>y. (y, x) \<in> ord0_leq O ord0_prec\<^sup>+ \<longrightarrow> P y) \<longrightarrow> P x"
  have "\<forall>z. (z, x) \<in> ord0_leq \<longrightarrow> P z" 
    by (rule ord0_prec_induct) (meson * ord0_leq.cases ord0_leq_trans relcomp.cases)
  then show "P x"
    by (simp add: ord0_leq_refl)
qed


text \<open>ordering on ord0\<close>

instantiation ord0 :: ord
begin

definition
  ord0_less_def: "x < y \<longleftrightarrow> (x,y) \<in> ord0_leq O ord0_prec\<^sup>+"

definition
  ord0_le_def:   "x \<le> y \<longleftrightarrow> (x,y) \<in> ord0_leq"

instance ..

end

lemma ord0_order_refl[simp]: "(x::ord0) \<le> x"
  by (simp add: ord0_le_def ord0_leq_refl)

lemma ord0_order_trans: "\<lbrakk>(x::ord0) \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
  using ord0_le_def ord0_leq_trans by blast

lemma ord0_wf: "wf {(x,y::ord0). x < y}"
  using ord0_less_def wf_ord0_leq by auto

lemmas ord0_less_induct = wf_induct[OF ord0_wf]

lemma ord0_leI: "\<lbrakk>\<forall>a::ord0. a < x \<longrightarrow> a < y\<rbrakk> \<Longrightarrow> x \<le> y"
  by (meson ord0_le_def ord0_leqD ord0_leqI ord0_leq_refl ord0_less_def)

lemma ord0_less_le_trans: "\<lbrakk>(x::ord0) < y; y \<le> z\<rbrakk> \<Longrightarrow> x < z"
  by (meson ord0_le_def ord0_leq.cases ord0_leq_trans ord0_less_def relcomp.intros relcompEpair)

lemma ord0_le_less_trans:
  "\<lbrakk>(x::ord0) \<le> y; y < z\<rbrakk> \<Longrightarrow> x < z"
  by (meson ord0_le_def ord0_leq_trans ord0_less_def relcomp.cases relcomp.intros)

lemma rev_ord0_le_less_trans:
  "\<lbrakk>(y::ord0) < z; x \<le> y\<rbrakk> \<Longrightarrow> x < z"
  by (rule ord0_le_less_trans)

lemma ord0_less_trans: "\<lbrakk>(x::ord0) < y; y < z\<rbrakk> \<Longrightarrow> x < z"
  unfolding ord0_less_def 
  by (meson ord0_leq.cases relcomp.cases relcompI[OF ord0_leq_trans trancl_trans])

lemma ord0_less_imp_le: "(x::ord0) < y \<Longrightarrow> x \<le> y"
  using ord0_leI ord0_less_trans by blast

lemma ord0_linear_lemma:
  fixes m :: ord0 and n :: ord0
  shows "m < n \<or> n < m \<or> (m \<le> n \<and> n \<le> m)"
proof -
  have "m < n \<or> n < m \<or> m \<le> n \<and> n \<le> m" for m
  proof (induction n arbitrary: m rule: ord0_less_induct)
    case (1 n)
    have "\<forall>y. (y, n) \<in> {(x, y). x < y} \<longrightarrow> (\<forall>x. x < y \<or> y < x \<or> x \<le> y \<and> y \<le> x) \<Longrightarrow> 
           m < n \<or> n < m \<or> m \<le> n \<and> n \<le> m"
    proof (induction m rule: ord0_less_induct)
      case (1 x)
      then show ?case
        by (smt (verit, best) mem_Collect_eq old.prod.case ord0_leI ord0_le_less_trans ord0_less_imp_le)
    qed
    then show ?case
      using "1" by blast
  qed
  then show ?thesis
    by simp
qed

lemma ord0_linear: "(x::ord0) \<le> y \<or> y \<le> x"
  using ord0_less_imp_le ord0_linear_lemma by blast

lemma ord0_order_less_le: "(x::ord0) < y \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)" (is "?L=?R")
proof
  show "?L \<Longrightarrow> ?R"
    by (metis ord0_less_def ord0_less_imp_le ord0_less_le_trans wf_not_refl wf_ord0_leq)
  show "?R \<Longrightarrow> ?L"
  using ord0_less_imp_le ord0_linear_lemma by blast
qed

subsection \<open>Ordinal type\<close>

definition
  ord0rel :: "(ord0 \<times> ord0) set" where
  "ord0rel = {(x,y). x \<le> y \<and> y \<le> x}"

typedef ordinal = "(UNIV::ord0 set) // ord0rel"
  by (unfold quotient_def, auto)

theorem Abs_ordinal_cases2 [case_names Abs_ordinal, cases type: ordinal]:
  "(\<And>z. x = Abs_ordinal (ord0rel `` {z}) \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases x, auto simp add: quotient_def)


instantiation ordinal :: ord
begin

definition
  ordinal_less_def: "x < y \<longleftrightarrow> (\<forall>a\<in>Rep_ordinal x. \<forall>b\<in>Rep_ordinal y. a < b)"

definition
  ordinal_le_def: "x \<le> y \<longleftrightarrow> (\<forall>a\<in>Rep_ordinal x. \<forall>b\<in>Rep_ordinal y. a \<le> b)"

instance ..

end

lemma Rep_Abs_ord0rel [simp]:
  "Rep_ordinal (Abs_ordinal (ord0rel `` {x})) = (ord0rel `` {x})"
  by (simp add: Abs_ordinal_inverse quotientI)

lemma mem_ord0rel_Image [simp, intro!]: "x \<in> ord0rel `` {x}"
  by (simp add: ord0rel_def)

lemma equiv_ord0rel: "equiv UNIV ord0rel"
  unfolding equiv_def refl_on_def sym_def trans_def ord0rel_def
  by (auto elim: ord0_order_trans)

lemma Abs_ordinal_eq[simp]:
  "(Abs_ordinal (ord0rel `` {x}) = Abs_ordinal (ord0rel `` {y})) = (x \<le> y \<and> y \<le> x)"
  apply (simp add: Abs_ordinal_inject quotientI eq_equiv_class_iff[OF equiv_ord0rel])
  apply (simp add: ord0rel_def)
  done

lemma Abs_ordinal_le[simp]:
  "Abs_ordinal (ord0rel `` {x}) \<le> Abs_ordinal (ord0rel `` {y}) \<longleftrightarrow> (x \<le> y)" (is "?L=?R")
proof
  show "?L \<Longrightarrow> ?R"
    using Rep_Abs_ord0rel ordinal_le_def by blast
next
  assume ?R
  then have "\<And>a b. \<lbrakk>(x, a) \<in> ord0rel; (y, b) \<in> ord0rel\<rbrakk> \<Longrightarrow> a \<le> b"
    unfolding ord0rel_def by (blast intro: ord0_order_trans)
  then show ?L
    by (auto simp add: ordinal_le_def)
qed

lemma Abs_ordinal_less[simp]:
  "Abs_ordinal (ord0rel `` {x}) < Abs_ordinal (ord0rel `` {y}) \<longleftrightarrow> (x < y)" (is "?L=?R")
proof
  show "?L \<Longrightarrow> ?R"
    using Rep_Abs_ord0rel ordinal_less_def by blast
next
  assume ?R
  then have "\<And>a b. \<lbrakk>(x, a) \<in> ord0rel; (y, b) \<in> ord0rel\<rbrakk> \<Longrightarrow> a < b"
    unfolding ord0rel_def
    by (blast intro: ord0_le_less_trans ord0_less_le_trans)
  then show ?L
    by (auto simp add: ordinal_less_def)
qed

instance ordinal :: linorder
proof
  show "(x::ordinal) \<le> x" for x
    by (cases x, simp)
  show "((x::ordinal) < y) = (x \<le> y \<and> \<not> y \<le> x)" for x y
    by (cases x, cases y, auto simp add: ord0_order_less_le)
  show "(x::ordinal) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" for x y z
    by (cases x, cases y, cases z, auto elim: ord0_order_trans)
  show "(x::ordinal) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" for x y
    by (cases x, cases y, simp)
  show "(x::ordinal) \<le> y \<or> y \<le> x" for x y
    by (cases x, cases y, simp add: ord0_linear)
qed

instance ordinal :: wellorder
proof
  show "P a" if "(\<And>x::ordinal. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x)" for P a
  proof (rule Abs_ordinal_cases2)
    fix z
    assume a: "a = Abs_ordinal (ord0rel `` {z})"
    have "P (Abs_ordinal (ord0rel `` {z}))"
      using that
      apply (rule ord0_less_induct)
      by (metis Abs_ordinal_cases2 Abs_ordinal_less CollectI case_prodI)
    with a show "P a" by simp
  qed
qed

lemma ordinal_linear: "(x::ordinal) \<le> y \<or> y \<le> x"
  by auto

lemma ordinal_wf: "wf {(x,y::ordinal). x < y}"
  by (simp add: wf)


subsection \<open>Induction over ordinals\<close>

text "zero and strict limits"

definition
  oZero :: "ordinal" where
  "oZero = Abs_ordinal (ord0rel `` {ord0_Zero})"

definition
  oStrictLimit :: "(nat \<Rightarrow> ordinal) \<Rightarrow> ordinal" where
  "oStrictLimit f = Abs_ordinal
      (ord0rel `` {ord0_Lim (\<lambda>n. SOME x. x \<in> Rep_ordinal (f n))})"

text "induction over ordinals"

lemma ord0relD: "(x,y) \<in> ord0rel \<Longrightarrow> x \<le> y \<and> y \<le> x"
  by (simp add: ord0rel_def)

lemma ord0_precD: "(x,y) \<in> ord0_prec \<Longrightarrow> \<exists>f n. x = f n \<and> y = ord0_Lim f"
  by (simp add: ord0_prec_def)

lemma less_ord0_LimI: "f n < ord0_Lim f"
  using ord0_leq_refl ord0_less_def ord0_prec_def by fastforce

lemma less_ord0_LimD: 
  assumes "x < ord0_Lim f" shows "\<exists>n. x \<le> f n"
proof -
  obtain y where "x\<le>y" "y < ord0_Lim f"
    using assms ord0_linear by auto
  then consider "(y, ord0_Lim f) \<in> ord0_prec" | z where "y \<le> z" "(z, ord0_Lim f) \<in> ord0_prec"
    apply (clarsimp simp add: ord0_less_def ord0_le_def)
    by (metis ord0_less_def ord0_less_imp_le relcomp.relcompI that(2) tranclE)
  then show ?thesis
    by (metis \<open>x \<le> y\<close> ord0.inject ord0_order_trans ord0_precD)
qed
  
lemma some_ord0rel: "(x, SOME y. (x,y) \<in> ord0rel) \<in> ord0rel"
  by (rule_tac x=x in someI, simp add: ord0rel_def)

lemma ord0_Lim_le: "\<forall>n. f n \<le> g n \<Longrightarrow> ord0_Lim f \<le> ord0_Lim g"
  by (metis less_ord0_LimD less_ord0_LimI ord0_le_less_trans ord0_linear ord0_order_less_le)

lemma ord0_Lim_ord0rel:
  "\<forall>n. (f n, g n) \<in> ord0rel \<Longrightarrow> (ord0_Lim f, ord0_Lim g) \<in> ord0rel"
  by (simp add: ord0rel_def ord0_Lim_le)

lemma Abs_ordinal_oStrictLimit:
  "Abs_ordinal (ord0rel `` {ord0_Lim f})
  = oStrictLimit (\<lambda>n. Abs_ordinal (ord0rel `` {f n}))"
  apply (simp add: oStrictLimit_def)
  using ord0_Lim_le ord0relD some_ord0rel by presburger

lemma oStrictLimit_induct:
  assumes base: "P oZero"
  assumes step: "\<And>f. \<forall>n. P (f n) \<Longrightarrow> P (oStrictLimit f)"
  shows "P a"
proof -
  obtain z where z: "a = Abs_ordinal (ord0rel `` {z})"
    using Abs_ordinal_cases2 by auto
  have "P (Abs_ordinal (ord0rel `` {z}))"
  proof (induction z)
    case ord0_Zero
    with base oZero_def show ?case by auto
  next
    case (ord0_Lim x)
    then show ?case
      by (simp add: Abs_ordinal_oStrictLimit local.step)
  qed
  then show ?thesis
    by (simp add: z)
qed

text "order properties of 0 and strict limits"

lemma oZero_least: "oZero \<le> x"
proof -
  have "x = Abs_ordinal (ord0rel `` {z}) \<Longrightarrow> ord0_Zero \<le> z" for z
  proof (induction z arbitrary: x)
    case (ord0_Lim u)
    then show ?case
      by (meson less_ord0_LimI ord0_le_less_trans ord0_less_imp_le rangeI) 
  qed auto
  then show ?thesis
    by (metis Abs_ordinal_cases2 Abs_ordinal_le oZero_def)
qed

lemma oStrictLimit_ub: "f n < oStrictLimit f"
  apply (cases "f n", simp add: oStrictLimit_def)
  apply (rule_tac y="SOME x. x \<in> Rep_ordinal (f n)" in ord0_le_less_trans)
  apply (metis (no_types) Image_singleton_iff Rep_Abs_ord0rel empty_iff mem_ord0rel_Image ord0relD some_in_eq)
  by (meson less_ord0_LimI)

lemma oStrictLimit_lub: 
  assumes "\<forall>n. f n < x" shows "oStrictLimit f \<le> x"
proof -
  have "\<exists>n. x \<le> f n" if x: "x < oStrictLimit f"
  proof -
    obtain z where z: "x = Abs_ordinal (ord0rel `` {z})" 
                      "z < ord0_Lim (\<lambda>n. SOME x. x \<in> Rep_ordinal (f n))"
      using less_ord0_LimI x unfolding oStrictLimit_def
      by (metis Abs_ordinal_cases2 Abs_ordinal_less)
    then obtain n where "z \<le> (SOME x. x \<in> Rep_ordinal (f n))"
      using less_ord0_LimD by blast
    then have "Abs_ordinal (ord0rel `` {z}) \<le> f n"
      apply (rule_tac x="f n" in Abs_ordinal_cases2)
      using ord0_order_trans ord0relD some_ord0rel by auto
    then show ?thesis
      using \<open>x = Abs_ordinal (ord0rel `` {z})\<close> by auto
  qed
  then show ?thesis
    using assms linorder_not_le by blast
qed

lemma less_oStrictLimitD: "x < oStrictLimit f \<Longrightarrow> \<exists>n. x \<le> f n"
  by (metis leD leI oStrictLimit_lub)

end
