(*
Title: Groupoids
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Groupoids\<close>

theory Groupoid
  imports Catoid

begin

subsection \<open>st-Multigroupoids\<close>

text \<open>I define multigroupoids, extending the standard definition. I equip catoids with an operation
of inversion.\<close>

class inv_op = fixes inv :: "'a \<Rightarrow> 'a"

class st_multigroupoid = catoid + inv_op +
  assumes invl: "\<sigma> x \<in> x \<odot> inv x"
  and invr: "\<tau> x \<in> inv x \<odot> x"

sublocale st_multigroupoid \<subseteq> st_mgpd: st_multigroupoid  "\<lambda>x y. y \<odot> x" tgt src inv
  by unfold_locales (simp_all add: local.invr local.invl)

text \<open>Every multigroupoid is local.\<close>

lemma (in st_multigroupoid) st_mgpd_local:
  assumes "\<tau> x = \<sigma> y"
  shows "\<Delta> x y"
proof-
  have "x \<in> x \<odot> \<sigma> y"
    by (metis assms local.t_absorb singletonI)
  hence "x \<in> {x} \<star> (y \<odot> inv y)"
    using local.conv_exp2 local.invl by auto
  hence "x \<in> (x \<odot> y) \<star> {inv y}"
    using local.assoc_var by force
  hence "\<exists>u v. x \<in> u \<odot> v \<and> u \<in> x \<odot> y \<and> v = inv y"
    by (metis multimagma.conv_exp2 singletonD)
  hence "\<exists>u. x \<in> u \<odot> inv y \<and> u \<in> x \<odot> y"
    by presburger
  hence "\<exists>u. u \<in> x \<odot> y"
    by fastforce
  thus ?thesis
    by force
qed

sublocale st_multigroupoid \<subseteq> stmgpd: local_catoid "(\<odot>)" src tgt
  apply unfold_locales
   apply (metis local.Dst local.st_locality_locality local.st_mgpd_local set_eq_subset)
  by (metis local.Dst local.st_locality_locality local.st_mgpd_local subset_refl)

lemma (in st_multigroupoid) tgt_inv [simp]: "\<tau> (inv x) = \<sigma> x"
  using local.Dst local.invr by fastforce

lemma (in st_multigroupoid) src_inv: "\<sigma> (inv x) = \<tau> x"
  by simp

text \<open>The following lemma is from Theorem 5.2  of Jónsson and Tarski's Boolean Algebras with Operators II article.\<close>

lemma (in st_multigroupoid) bao3:
  assumes "x \<odot> y = {\<sigma> x}"
  shows "inv x = y"
proof -
  have "\<tau> x = \<sigma> y"
    using assms local.Dst by force
  hence "{y} = \<tau> x \<odot> y"
    by simp
  hence "y \<in> {inv x} \<star> {x} \<star> {y}"
    using local.conv_exp2 local.invr by fastforce
  hence "y \<in> inv x \<odot> \<sigma> x"
    by (metis assms local.assoc_var local.conv_atom)
  hence "y \<in> inv x \<odot> \<tau> (inv x)"
    by simp
  thus ?thesis
    by (metis local.t_absorb singletonD)
qed

lemma (in st_multigroupoid) inv_s [simp]: "inv (\<sigma> x) = \<sigma> x"
proof-
  have "\<sigma> x \<odot> \<sigma> x = {\<sigma> x}"
    by simp
  thus "inv (\<sigma> x) = \<sigma> x"
    by (simp add: local.st_mgpd.bao3)
qed

lemma (in st_multigroupoid) srcfunct_inv:
   "\<sigma> x \<in> x \<odot> inv x \<Longrightarrow> \<sigma> y \<in> x \<odot> inv x \<Longrightarrow> \<sigma> x = \<sigma> y"
  using local.ts_msg.src_funct by fastforce

lemma (in st_multigroupoid) tgtfunct_inv:
   "\<tau> x \<in> inv x \<odot> x \<Longrightarrow> \<tau> y \<in> inv x \<odot> x \<Longrightarrow> \<tau> x = \<tau> y"
  by (metis local.ts_msg.src_comp_aux local.tt_idem)

text \<open>As for catoids, I prove quantalic properties, lifting to powersets.\<close>

abbreviation (in st_multigroupoid) Inv :: "'a set \<Rightarrow> 'a set" where
  "Inv \<equiv> image inv"

lemma (in st_multigroupoid) Inv_exp: "Inv X = {inv x |x. x \<in> X}"
  by blast

lemma (in st_multigroupoid) Inv_un: "Inv (X \<union> Y) = Inv X \<union> Inv Y"
  by (simp add: image_Un)

lemma (in st_multigroupoid) Inv_Un: "Inv (\<Union>\<X>) = (\<Union>X \<in> \<X>. Inv X)"
  unfolding Inv_exp by auto

lemma (in st_multigroupoid) Invl: "Src X \<subseteq> X \<star> Inv X"
  unfolding Inv_exp conv_exp using local.invl by fastforce

lemma (in st_multigroupoid) Invr: "Tgt X \<subseteq> Inv X \<star> X"
  by (meson imageI image_subsetI local.invr local.stopp.conv_exp2)

lemma (in st_multigroupoid) Inv_strong_gelfand: "X \<subseteq> X \<star> Inv X \<star> X"
proof-
  have "X = Src X \<star> X"
    by simp
  also have "\<dots> \<subseteq> X \<star> Inv X \<star> X"
    using local.Invl local.conv_isor by presburger
  finally show ?thesis.
qed

text \<open>At powerset level, one can define domain and codomain operations explicitly as in
relation algebras.\<close>

lemma (in st_multigroupoid) dom_def: "Src X = sfix \<inter> (X \<star> Inv X)"
proof-
  {fix a
  have "(a \<in> sfix \<inter> (X \<star> Inv X)) = (\<sigma> a = a \<and> \<sigma> a \<in> X \<star> Inv X)"
    by fastforce
  also have "\<dots> = (\<sigma> a = a \<and> (\<exists>b \<in> X.\<exists>c \<in> Inv X. \<sigma> a \<in> b \<odot> c))"
    using local.conv_exp2 by auto
  also have "\<dots> = (\<sigma> a = a \<and> (\<exists>b \<in> X. \<sigma> a = \<sigma> b))"
    by (metis imageI local.invl local.ts_msg.tgt_comp_aux)
  also have "\<dots> = (a \<in> Src X)"
    by auto
  finally have "(a \<in> sfix \<inter> (X \<star> Inv X)) = (a \<in> Src X)".}
  thus ?thesis
    by blast
qed

lemma (in st_multigroupoid) cod_def: "Tgt X = sfix \<inter> (Inv X \<star> X)"
  by (metis local.st_mgpd.dom_def local.stfix_set local.stopp.conv_def multimagma.conv_def)

lemma (in st_multigroupoid) dom_def_var: "Src X = sfix \<inter> (X \<star> UNIV)"
proof-
  {fix a
  have "(a \<in> sfix \<inter> (X \<star> UNIV)) = (\<sigma> a = a \<and> \<sigma> a \<in> X \<star> UNIV)"
    by fastforce
  also have "\<dots> = (\<sigma> a = a \<and> (\<exists>b \<in> X.\<exists>c. \<sigma> a \<in> b \<odot> c))"
    using local.conv_exp2 by auto
  also have "\<dots> = (\<sigma> a = a \<and> (\<exists>b \<in> X. \<sigma> a = \<sigma> b))"
    by (metis local.invl local.ts_msg.tgt_comp_aux)
  also have "\<dots> = (a \<in> Src X)"
    by auto
  finally have "(a \<in> sfix \<inter> (X \<star> UNIV)) = (a \<in> Src X)".}
  thus ?thesis
    by blast
qed

lemma (in st_multigroupoid) cod_def_var: "Tgt X = sfix \<inter> (UNIV \<star> X)"
  by (metis local.ST_im local.sfix_im local.st_mgpd.dom_def_var local.stopp.conv_def local.tfix_im multimagma.conv_def)

lemma (in st_multigroupoid) dom_univ: "X \<star> UNIV = Src X \<star> UNIV"
proof-
  have "X \<star> UNIV = Src X \<star> X \<star> UNIV"
    using local.Src_absorp by presburger
  also have "\<dots> \<subseteq> Src X \<star> UNIV \<star> UNIV"
    by (meson local.conv_isol local.conv_isor subset_UNIV)
  finally have a: "X \<star> UNIV \<subseteq> Src X \<star> UNIV"
    using local.conv_assoc local.conv_isol subset_UNIV by blast
  have "Src X \<star> UNIV \<subseteq> X \<star> Inv X \<star> UNIV"
    using local.Invl local.conv_isor by presburger
  also have "\<dots> \<subseteq> X \<star> UNIV \<star> UNIV"
    by (simp add: local.conv_isol local.conv_isor)
  finally have "Src X \<star> UNIV \<subseteq> X \<star> UNIV"
    by (metis dual_order.trans local.conv_assoc local.conv_isol subset_UNIV)
  thus ?thesis
    using a by force
qed

lemma (in st_multigroupoid) cod_univ: "UNIV \<star> X = UNIV \<star> Tgt X"
  by (metis local.st_mgpd.dom_univ local.stopp.conv_def multimagma.conv_def)


subsection \<open>Groupoids\<close>

text \<open>Groupoids are simply functional multigroupoids. I start with a somewhat indirect axiomatisaion.\<close>

class groupoid_var = st_multigroupoid + functional_catoid

begin

lemma invl [simp]: "x \<odot> inv x = {\<sigma> x}"
  using local.fun_in_sgl local.invl by force

lemma invr [simp]: "inv x \<odot> x = {\<tau> x}"
  using local.fun_in_sgl local.invr by force

end

text \<open>Next, I provide a more direct axiomatisation.\<close>

class groupoid = catoid + inv_op +
  assumes invs [simp]: "x \<odot> inv x = {\<sigma> x}"
  and invt [simp]: "inv x \<odot> x = {\<tau> x}"

subclass (in groupoid) st_multigroupoid
  by unfold_locales simp_all

sublocale groupoid \<subseteq> lrgpd: groupoid "\<lambda>x y. y \<odot> x"  tgt src inv
  by unfold_locales simp_all

lemma (in groupoid) bao4 [simp]: "inv (inv x) = x"
proof-
  have "inv x \<odot> x = {\<sigma> (inv x)}"
    by simp
  thus ?thesis
    using local.bao3 by blast
qed

lemma (in groupoid) rev1:
  "x \<in> y \<odot> z \<Longrightarrow> y \<in> x \<odot> inv z"
proof-
  assume h: "x \<in> y \<odot> z"
  hence "x \<odot> inv z \<subseteq> y \<odot> z \<star> {inv z}"
    using multimagma.conv_exp2 by fastforce
  hence "x \<odot> inv z \<subseteq> {y} \<star> (z \<odot> inv z)"
    using local.assoc_var by presburger
  hence "x \<odot> inv z \<subseteq> y \<odot> \<sigma> z"
    by simp
  hence "x \<odot> inv z \<subseteq> y \<odot> \<tau> y"
    using h local.src_comp_aux local.src_twisted_aux by auto
  hence a: "x \<odot> inv z \<subseteq> {y}"
    by simp
  have "\<tau> x = \<tau> z"
    using h local.tgt_comp_aux by auto
  hence  "x \<odot> inv z \<noteq> {}"
    by (simp add: local.st_mgpd_local)
  hence "x \<odot> inv z = {y}"
    using a by auto
  thus ?thesis
    by force
qed

lemma (in groupoid) rev2:
  "x \<in> y \<odot> z \<Longrightarrow> z \<in> inv y \<odot> x"
  by (simp add: local.lrgpd.rev1)

lemma (in groupoid) rev1_eq: "(y \<in> x \<odot> (inv z)) = (x \<in> y \<odot> z)"
  using local.lrgpd.rev2 by force

lemma (in groupoid) rev2_eq: "(z \<in> (inv y) \<odot> x) = (x \<in> y \<odot> z)"
  by (simp add: local.lrgpd.rev1_eq)

text \<open>The following fact show that the axiomatisation above captures indeed  groupoids.\<close>

lemma (in groupoid) lr_mgpd_partial:
  assumes "x \<in> y \<odot> z"
  and "x' \<in> y \<odot> z"
  shows "x = x'"
proof-
  have "z \<in> inv y \<odot> x"
    by (simp add: assms(1) rev2)
  hence "x' \<in> {y} \<star> (inv y \<odot> x)"
    using assms(2) local.conv_exp2 by auto
  hence "x'\<in> (y \<odot> inv y) \<star> {x}"
    by (simp add: local.assoc_var)
  hence "x' \<in> \<sigma> y \<odot> x"
    by (simp add: multimagma.conv_atom)
  hence "x' \<in> \<sigma> x \<odot> x"
    using assms(1) local.ts_msg.tgt_comp_aux by auto
  thus ?thesis
    by simp
qed

subclass (in groupoid) single_set_category
  by unfold_locales (simp add: local.lr_mgpd_partial)

text \<open>Hence st-groupoids are indeed single-set categories in which all arrows
are isomorphisms.\<close>

lemma (in groupoid) src_canc1:
  assumes "\<tau> z = \<sigma> x"
  and "\<tau> z = \<sigma> y"
  and "z \<otimes> x = z \<otimes> y"
shows "x = y"
proof-
  have "inv z \<otimes> (z \<otimes> x) = inv z \<otimes> (z \<otimes> y)"
    by (simp add: assms(3))
  hence "(inv z \<otimes> z) \<otimes> x = (inv z \<otimes> z) \<otimes> y"
    using assms(1) assms(2) local.sscatml.comp0_assoc by auto
  hence "\<tau> z \<otimes> x  = \<tau> z \<otimes> y"
    by (simp add: local.pcomp_def)
  thus ?thesis
    by (metis assms(1) assms(2) local.sscatml.l0_absorb)
qed

lemma (in groupoid) tgt_canc1:
  assumes "\<tau> x = \<sigma> z"
  and "\<tau> y = \<sigma> z"
  and "x \<otimes> z = y \<otimes> z"
  shows "x = y"
  by (metis assms local.lrgpd.pcomp_def_var local.lrgpd.src_canc1 local.pcomp_def_var local.st_mgpd.st_mgpd_local)

text \<open>The following lemmas are from Theorem 5.2  of Jónsson and Tarski's BAO II article.\<close>

lemma (in groupoid) bao1 [simp]: "x \<otimes> (inv x \<otimes> x) = x"
  by (simp add: local.pcomp_def)

lemma (in groupoid) bao2 [simp]: "(x \<otimes> inv x) \<otimes> x = x"
  by (simp add: local.st_assoc)

lemma (in groupoid) bao5:
  "\<tau> x = \<sigma> y \<Longrightarrow> inv x \<otimes> x = y \<otimes> inv y"
  using local.invs local.invt local.pcomp_def by auto

lemma (in groupoid) bao6: "Inv (x \<odot> y) = inv y \<odot> inv x"
  apply (rule antisym)
  using rev1_eq rev2_eq apply force
  by (clarsimp, metis imageI local.bao4 local.rev1_eq local.rev2_eq)


subsection \<open>Axioms of relation algebra\<close>

text \<open>I formalise a special case of a famous theorem of Jónsson and Tarski, showing that groupoids lift
to relation algebras at powerset level. All axioms not related to converse have already been considered
previously.\<close>

lemma (in groupoid) Inv_invol [simp]: "Inv (Inv X) = X"
proof-
  have "Inv (Inv X) = {inv (inv x) |x. x \<in> X}"
    by (simp add: image_image)
  also have "\<dots> = X"
    by simp
  finally show ?thesis.
qed

lemma (in groupoid) Inv_contrav: "Inv (X \<star> Y) = Inv Y \<star> Inv X"
proof-
  have "Inv (X \<star> Y) = (\<Union>x \<in> X. \<Union>y \<in> Y. Inv (x \<odot> y))"
    unfolding conv_def image_def by blast
  also have "\<dots> = (\<Union>x \<in> X. \<Union>y \<in> Y. inv y \<odot> inv x)"
    by (simp add: local.bao6)
  also have "\<dots> = Inv Y \<star> Inv X"
    unfolding conv_def image_def by blast
  finally show ?thesis.
qed

lemma (in groupoid) residuation: "Inv X \<star> -(X \<star> Y) \<subseteq> -Y"
  using local.lrgpd.rev1 local.stopp.conv_exp2 by fastforce

lemma (in groupoid) modular_law: "(X \<star> Y) \<inter> Z \<subseteq> (X \<inter> (Z \<star> Inv Y)) \<star> Y"
  using local.lrgpd.rev2 local.stopp.conv_exp2 by fastforce

lemma (in groupoid) dedekind: "(X \<star> Y) \<inter> Z \<subseteq> (X \<inter> (Z \<star> Inv Y)) \<star> (Y \<inter> (Inv X \<star> Z))"
  unfolding Inv_exp conv_exp
  apply clarsimp
  using local.rev1 local.rev2 by blast

text \<open>In sum, this shows that the powerset lifting of a groupoid is a relation algebra. I link this formally with relations
in an interpretation statement in another component.\<close>

text \<open>Jónsson and Tarski's axioms of relation algebra are slightly different. It is routine to related them formally with those used here.
It might also be interested to use their partiality-by-closure approach to defining groupoids in a setting with explicit carrier sets
in another Isabelle formalisation.\<close>

lemma (in groupoid) Inv_compl: "Inv (-X) = -(Inv X)"
  by (metis UNIV_I bij_def bij_image_Compl_eq equalityI image_eqI inj_def local.bao4 subsetI)

lemma (in groupoid) Inv_inter: "Inv (X \<inter> Y) = Inv X \<inter> Inv Y"
  using local.Inv_compl by auto

lemma (in groupoid) Inv_Un: "Inv (\<Inter>\<X>) = (\<Inter>X \<in> \<X>. Inv X)"
proof-
  have "Inv (\<Inter>\<X>) = Inv (-(\<Union>X \<in> \<X>. -X))"
    by (simp add: Setcompr_eq_image)
  also have "\<dots> = - (Inv (\<Union>X \<in> \<X>. -X))"
    using local.Inv_compl by presburger
  also have "\<dots> = -(\<Union> X \<in> \<X>. Inv (-X))"
    by blast
  also have "\<dots> = -(\<Union>X \<in> \<X>. -(Inv X))"
    using local.Inv_compl by presburger
  also have "\<dots> = (\<Inter>X \<in> \<X>. Inv X)"
    by blast
  finally show "Inv (\<Inter>\<X>) = (\<Inter>X \<in> \<X>. Inv X)".
qed

end

