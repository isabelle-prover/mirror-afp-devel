(*
Title: Catoids
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Catoids\<close>

theory Catoid
  imports Main

begin

subsection \<open>Multimagmas\<close>

text \<open>Multimagmas are sets equipped with multioperations. Multioperations are isomorphic to ternary relations.\<close>

class multimagma =
  fixes mcomp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set" (infixl "\<odot>" 70)

begin

text \<open>I introduce notation for the domain of definition of the multioperation.\<close>

abbreviation "\<Delta> x y \<equiv> (x \<odot> y \<noteq> {})"

text \<open>I extend the multioperation to powersets\<close>

definition conv :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<star>" 70) where
  "X \<star> Y = (\<Union>x \<in> X. \<Union>y \<in> Y. x \<odot> y)"

lemma conv_exp: "X \<star> Y = {z. \<exists>x y. z \<in> x \<odot> y \<and> x \<in> X \<and> y \<in> Y}"
  unfolding conv_def by fastforce

lemma conv_exp2: "(z \<in> X \<star> Y) = (\<exists>x y. z \<in> x \<odot> y \<and> x \<in> X \<and> y \<in> Y)"
  by (simp add: multimagma.conv_exp)

lemma conv_distl: "X \<star> \<Union>\<Y> = (\<Union>Y \<in> \<Y>. X \<star> Y)"
  unfolding conv_def by blast

lemma conv_distr: "\<Union>\<X> \<star> Y = (\<Union>X \<in> \<X>. X \<star> Y)"
  unfolding conv_def by blast

lemma conv_distl_small: "X \<star> (Y \<union> Z) = X \<star> Y \<union> X \<star> Z"
  unfolding conv_def by blast

lemma conv_distr_small: "(X \<union> Y) \<star> Z  = X \<star> Z \<union> Y \<star> Z"
  unfolding conv_def by blast

lemma conv_isol: "X \<subseteq> Y \<Longrightarrow> Z \<star> X \<subseteq> Z \<star> Y"
  using conv_exp2 by fastforce

lemma conv_isor: "X \<subseteq> Y \<Longrightarrow> X \<star> Z \<subseteq> Y \<star> Z"
  using conv_exp2 by fastforce

lemma conv_atom [simp]: "{x} \<star> {y} = x \<odot> y"
  by (simp add: conv_def)

end


subsection \<open>Multisemigroups\<close>

text \<open>Sultisemigroups are associative multimagmas.\<close>

class multisemigroup = multimagma +
  assumes assoc: "(\<Union>v \<in> y \<odot> z. x \<odot> v) = (\<Union>v \<in> x \<odot> y. v \<odot> z)"

begin

lemma assoc_exp: "(\<exists>v. w \<in> x \<odot> v \<and> v \<in> y \<odot> z) = (\<exists>v. v \<in> x \<odot> y \<and> w \<in> v \<odot> z)"
  using assoc by blast

lemma assoc_var: "{x} \<star> (y \<odot> z) = (x \<odot> y) \<star> {z}"
  unfolding conv_def assoc_exp using local.assoc by force

text \<open>Associativity extends to powersets.\<close>

lemma conv_assoc: "X \<star> (Y \<star> Z) = (X \<star> Y) \<star> Z"
  unfolding conv_exp using assoc_exp by fastforce

end


subsection \<open>st-Multimagmas\<close>

text \<open>I equip multimagmas with source and target maps.\<close>

class st_op =
  fixes src :: "'a \<Rightarrow> 'a" ("\<sigma>")
  and tgt :: "'a \<Rightarrow> 'a" ("\<tau>")

class st_multimagma = multimagma + st_op +
  assumes Dst: "x \<odot> y \<noteq> {} \<Longrightarrow> \<tau> x = \<sigma> y"
  and s_absorb [simp]: "\<sigma> x \<odot> x = {x}"
  and t_absorb [simp]: "x \<odot> \<tau> x = {x}"

text \<open>The following sublocale proof sets up opposition/duality.\<close>

sublocale st_multimagma \<subseteq> stopp: st_multimagma "\<lambda>x y. y \<odot> x" tgt src
  rewrites "stopp.conv X Y = Y \<star> X"
  by (unfold_locales, auto simp add: local.Dst multimagma.conv_def)

lemma (in st_multimagma) ts_compat [simp]: "\<tau> (\<sigma> x) = \<sigma> x"
  by (simp add: Dst)

lemma (in st_multimagma) ss_idem [simp]: "\<sigma> (\<sigma> x) = \<sigma> x"
  by (metis local.stopp.ts_compat local.ts_compat)

lemma (in st_multimagma) st_fix: "(\<tau> x = x) = (\<sigma> x = x)"
proof
  assume h1: "\<tau> x = x"
  hence "\<sigma> x = \<sigma> (\<tau> x)"
    by simp
  also have "\<dots> = x"
    by (metis h1 local.stopp.ts_compat)
  finally show "\<sigma> x = x".
next
  assume h2: "\<sigma> x = x"
  hence "\<tau> x = \<tau> (\<sigma> x)"
    by simp
  also have "\<dots> = x"
    by (metis h2 ts_compat)
  finally show "\<tau> x = x".
qed

lemma (in st_multimagma) st_eq1: "\<sigma> x = x \<Longrightarrow> \<sigma> x = \<tau> x"
  by (simp add: local.stopp.st_fix)

lemma (in st_multimagma) st_eq2: "\<tau> x = x \<Longrightarrow> \<sigma> x = \<tau> x"
  by (simp add: local.stopp.st_fix)

text \<open>I extend source and target operations to powersets by taking images.\<close>

abbreviation (in st_op) Src :: "'a set \<Rightarrow> 'a set" where
  "Src \<equiv> image \<sigma>"

abbreviation (in st_op) Tgt :: "'a set \<Rightarrow> 'a set" where
  "Tgt \<equiv> image \<tau>"

text \<open>Fixpoints of source and target maps model source and target elements.
These correspond to units.\<close>

abbreviation (in st_op) sfix :: "'a set" where
  "sfix \<equiv> {x. \<sigma> x = x}"

abbreviation (in st_op) tfix :: "'a set" where
  "tfix \<equiv> {x. \<tau> x = x}"

lemma (in st_multimagma) st_mm_rfix [simp]: "tfix = stopp.sfix"
  by simp

lemma (in st_multimagma) st_fix_set: "{x. \<sigma> x = x} = {x. \<tau> x = x}"
  using local.st_fix by presburger

lemma (in st_multimagma) stfix_set: "sfix = tfix"
  using local.st_fix_set by blast

lemma (in st_multimagma) sfix_im: "sfix = Src UNIV"
  by (smt (verit, best) Collect_cong full_SetCompr_eq local.ss_idem)

lemma (in st_multimagma) tfix_im: "tfix = Tgt UNIV"
  using local.stopp.sfix_im by blast

lemma (in st_multimagma) ST_im: "Src UNIV = Tgt UNIV"
  using local.sfix_im local.stfix_set local.tfix_im by presburger

text \<open>Source and target elements are "orthogonal" idempotents.\<close>

lemma (in st_multimagma) s_idem [simp]: "\<sigma> x \<odot> \<sigma> x = {\<sigma> x}"
proof-
  have "{\<sigma> x} = \<sigma> x \<odot> \<tau> (\<sigma> x)"
    using local.t_absorb by presburger
  also have "\<dots> = \<sigma> x \<odot> \<sigma> x"
    by simp
  finally show ?thesis..
qed

lemma (in st_multimagma) s_ortho:
  "\<Delta> (\<sigma> x) (\<sigma> y) \<Longrightarrow> \<sigma> x = \<sigma> y"
proof-
  assume "\<Delta> (\<sigma> x) (\<sigma> y)"
  hence "\<tau> (\<sigma> x) = \<sigma> (\<sigma> y)"
    using local.Dst by blast
  thus ?thesis
    by simp
qed

lemma (in st_multimagma) s_ortho_iff: "\<Delta> (\<sigma> x) (\<sigma> y) = (\<sigma> x = \<sigma> y)"
  using local.s_ortho by auto

lemma (in st_multimagma) st_ortho_iff: "\<Delta> (\<sigma> x) (\<tau> y) = (\<sigma> x = \<tau> y)"
  using local.Dst by fastforce

lemma (in st_multimagma) s_ortho_id: "(\<sigma> x) \<odot> (\<sigma> y) = (if (\<sigma> x = \<sigma> y) then {\<sigma> x} else {})"
  using local.s_ortho_iff by auto

lemma (in st_multimagma) s_absorb_var: "(\<sigma> y \<noteq> \<sigma> x) = (\<sigma> y \<odot> x = {})"
  using local.Dst by force

lemma (in st_multimagma) s_absorb_var2: "(\<sigma> y = \<sigma> x) = (\<sigma> y \<odot> x \<noteq> {})"
  using local.s_absorb_var by blast

lemma (in st_multimagma) s_absorb_var3: "(\<sigma> y = \<sigma> x) = \<Delta> (\<sigma> x) y"
  by (metis local.s_absorb_var)

lemma (in st_multimagma) s_assoc: "{\<sigma> x} \<star> (\<sigma> y \<odot> z) = (\<sigma> x \<odot> \<sigma> y) \<star> {z}"
proof-
  {fix a
    have "(a \<in> {\<sigma> x} \<star> (\<sigma> y \<odot> z)) = (\<exists>b. a \<in> \<sigma> x \<odot> b \<and> b \<in> \<sigma> y \<odot> z)"
      by (simp add: local.conv_exp2)
    also have "\<dots> = (\<exists>b. a \<in> \<sigma> x \<odot> b \<and> b \<in> \<sigma> y \<odot> z \<and> \<sigma> y = \<sigma> z)"
    using local.s_absorb_var by auto
  also have "\<dots> = (\<exists>b. a \<in> \<sigma> x \<odot> b \<and> b \<in> \<sigma> y \<odot> z \<and> \<sigma> y = \<sigma> z \<and> \<sigma> x = \<sigma> y)"
    using local.stopp.Dst by fastforce
  also have "\<dots> = (\<exists>b. b \<in> \<sigma> x \<odot> \<sigma> y \<and> a \<in> b \<odot> z \<and> \<sigma> y = \<sigma> z \<and> \<sigma> x = \<sigma> y)"
    by fastforce
  also have "\<dots> = (\<exists>b. b \<in> \<sigma> x \<odot> \<sigma> y \<and> a \<in> b \<odot> z)"
    by (metis equals0D local.s_absorb_var3 local.s_idem singleton_iff)
  also have "\<dots> = (a \<in> (\<sigma> x \<odot> \<sigma> y) \<star> {z})"
    using local.conv_exp2 by auto
  finally have "(a \<in> {\<sigma> x} \<star> (\<sigma> y \<odot> z)) = (a \<in> (\<sigma> x \<odot> \<sigma> y) \<star> {z})".}
  thus ?thesis
    by blast
qed

lemma (in st_multimagma) sfix_absorb_var [simp]: "(\<Union>e \<in> sfix. e \<odot> x) = {x}"
  apply safe
   apply (metis local.s_absorb local.s_absorb_var2 singletonD)
  by (smt (verit, del_insts) UNIV_I UN_iff imageI local.s_absorb local.sfix_im singletonI)

lemma (in st_multimagma) tfix_absorb_var: "(\<Union>e \<in> tfix. x \<odot> e) = {x}"
  using local.stopp.sfix_absorb_var by presburger

lemma (in st_multimagma) st_comm: "\<tau> x \<odot> \<sigma> y = \<sigma> y \<odot> \<tau> x"
  using local.Dst by fastforce

lemma (in st_multimagma) s_weak_twisted: "(\<Union>u \<in> x \<odot> y. \<sigma> u \<odot> x) \<subseteq> x \<odot> \<sigma> y"
  by (safe, metis empty_iff insertI1 local.Dst local.s_absorb local.t_absorb)

lemma (in st_multimagma) s_comm: "\<sigma> x \<odot> \<sigma> y = \<sigma> y \<odot> \<sigma> x"
  using local.Dst by force

lemma (in st_multimagma) s_export [simp]: "Src (\<sigma> x \<odot> y) = \<sigma> x \<odot> \<sigma> y"
  using local.Dst by force

lemma (in st_multimagma) st_prop: "(\<tau> x = \<sigma> y) = \<Delta> (\<tau> x) (\<sigma> y)"
  by (metis local.stopp.s_absorb_var2 local.stopp.st_comm local.ts_compat)

lemma (in st_multimagma) weak_local_var: "\<tau> x \<odot> \<sigma> y = {} \<Longrightarrow> x \<odot> y = {}"
  using local.Dst local.st_prop by auto

text \<open>The following facts hold by duality.\<close>

lemma (in st_multimagma) st_compat: "\<sigma> (\<tau> x) = \<tau> x"
  by simp

lemma (in st_multimagma) tt_idem: "\<tau> (\<tau> x) = \<tau> x"
  by simp

lemma (in st_multimagma) t_idem: "\<tau> x \<odot> \<tau> x = {\<tau> x}"
  by simp

lemma (in st_multimagma)t_weak_twisted: "(\<Union>u \<in> y \<odot> x. x \<odot> \<tau> u) \<subseteq> \<tau> y \<odot> x"
  using local.stopp.s_weak_twisted by auto

lemma (in st_multimagma) t_comm: "\<tau> x \<odot> \<tau> y = \<tau> y \<odot> \<tau> x"
  by (simp add: stopp.s_comm)

lemma (in st_multimagma) t_export: "image \<tau> (x \<odot> \<tau> y) = \<tau> x \<odot> \<tau> y"
  by simp

lemma (in st_multimagma) tt_comp_prop: "\<Delta> (\<tau> x) (\<tau> y) = (\<tau> x = \<tau> y)"
  using local.stopp.s_ortho_iff by force

text \<open>The set of all sources (and targets) are units at powerset level.\<close>

lemma (in st_multimagma) conv_uns [simp]: "sfix \<star> X = X"
proof-
  {fix a
    have "(a \<in> sfix \<star> X) = (\<exists>b \<in> sfix. \<exists>c \<in> X. a \<in> b \<odot> c)"
      by (meson local.conv_exp2)
    also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<sigma> b = b \<and> a \<in> b \<odot> c)"
      by blast
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. a \<in> \<sigma> b \<odot> c)"
    by (metis local.ss_idem)
  also have "\<dots> = (\<exists>c \<in> X. a \<in> \<sigma> c \<odot> c)"
    by (metis empty_iff local.s_absorb_var)
  also have "\<dots> = (a \<in> X)"
    by auto
  finally have "(a \<in> sfix \<star> X) = (a \<in> X)".}
  thus ?thesis
    by blast
qed

lemma (in st_multimagma) conv_unt: "X \<star> tfix = X"
  using stopp.conv_uns by blast

text \<open>I prove laws of modal powerset quantales.\<close>

lemma (in st_multimagma) Src_exp: "Src X = {\<sigma> x |x. x \<in> X}"
  by (simp add: Setcompr_eq_image)

lemma (in st_multimagma) ST_compat [simp]: "Src (Tgt X) = Tgt X"
  unfolding image_def by fastforce

lemma (in st_multimagma) TS_compat: "Tgt (Src X) = Src X"
  by (meson local.stopp.ST_compat)

lemma (in st_multimagma) Src_absorp [simp]: "Src X \<star> X = X"
proof-
  {fix a
  have "(a \<in> Src X \<star> X) = (\<exists>b \<in> Src X. \<exists>c \<in> X. a \<in> b \<odot> c)"
    using local.conv_exp2 by auto
  also have "\<dots> = (\<exists>b \<in> X. \<exists>c \<in> X. a \<in> \<sigma> b \<odot> c)"
    by blast
  also have "\<dots> = (\<exists>c \<in> X. a \<in> \<sigma> c \<odot> c)"
    by (metis empty_iff local.s_absorb_var)
 also have "\<dots> = (a \<in> X)"
   by simp
  finally have "(a \<in> Src X \<star> X) = (a \<in> X)".}
  thus ?thesis
    by force
qed

lemma (in st_multimagma) Tgt_absorp: "X \<star> Tgt X = X"
  by simp

lemma (in st_multimagma) Src_Sup_pres: "Src (\<Union>\<X>) = (\<Union>X \<in> \<X>. Src X)"
  unfolding Src_exp by auto

lemma (in st_multimagma) Tgt_Sup_pres: "Tgt (\<Union>\<X>) = (\<Union> X \<in> \<X>. Tgt X)"
  by blast

lemma (in st_multimagma) ST_comm: "Src X \<star> Tgt Y = Tgt Y \<star> Src X"
proof-
  {fix a
  have "(a \<in> Src X \<star> Tgt Y) = (\<exists>b \<in> Src X. \<exists>c \<in> Tgt Y. a \<in> b \<odot> c)"
    using local.conv_exp2 by auto
  also have "\<dots> = (\<exists>b \<in> X. \<exists>c \<in> Y. a \<in> \<sigma> b \<odot> \<tau> c)"
    by auto
  also have "\<dots> = (\<exists>b \<in> X. \<exists>c \<in> Y. a \<in> \<tau> c \<odot> \<sigma> b)"
    using local.st_comm by auto
  also have "\<dots> = (a \<in> Tgt Y \<star> Src X)"
    using multimagma.conv_exp2 by fastforce
  finally have "(a \<in> Src X \<star> Tgt Y) = (a \<in> Tgt Y \<star> Src X)".}
  thus ?thesis
    by force
qed

lemma (in st_multimagma) Src_comm: "Src X \<star> Src Y = Src Y \<star> Src X"
  by (metis local.ST_comm local.TS_compat)

lemma (in st_multimagma) Tgt_comm: "Tgt X \<star> Tgt Y = Tgt Y \<star> Tgt X"
  using local.stopp.Src_comm by presburger

lemma (in st_multimagma) Src_subid: "Src X \<subseteq> sfix"
  by force

lemma (in st_multimagma) Tgt_subid: "Tgt X \<subseteq> tfix"
  using local.stopp.Src_subid by presburger

lemma (in st_multimagma) Src_export [simp]: "Src (Src X \<star> Y) = Src X \<star> Src Y"
proof-
  {fix a
  have "(a \<in> Src (Src X \<star> Y)) = (\<exists>b \<in> Src X \<star> Y. a = \<sigma> b)"
    by (simp add: image_iff)
  also have "\<dots> = (\<exists>b. \<exists>c \<in> Src X. \<exists>d \<in> Y. a = \<sigma> b \<and> b \<in> c \<odot> d)"
    by (meson local.conv_exp2)
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. a = \<sigma> b \<and> b \<in> \<sigma> c \<odot> d)"
    by simp
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src (\<sigma> c \<odot> d))"
    by (metis (mono_tags, lifting) image_iff)
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> \<sigma> c \<odot> \<sigma> d)"
    by auto
  also have "\<dots> = (\<exists>c \<in> Src X. \<exists>d \<in> Src Y. a \<in> c \<odot> d)"
    by force
  also have "\<dots> = (a \<in> Src X \<star> Src Y)"
    using local.conv_exp2 by auto
  finally have "(a \<in> Src (Src X \<star> Y)) = (a \<in> Src X \<star> Src Y)".}
  thus ?thesis
    by force
qed

lemma (in st_multimagma) Tgt_export [simp]: "Tgt (X \<star> Tgt Y) = Tgt X \<star> Tgt Y"
  by simp

text \<open>Locality implies st-locality, which is the composition pattern of categories.\<close>

lemma (in st_multimagma) locality:
  assumes src_local: "Src (x \<odot> \<sigma> y) \<subseteq> Src (x \<odot> y)"
  and tgt_local: "Tgt (\<tau> x \<odot> y) \<subseteq> Tgt (x \<odot> y)"
  shows "\<Delta> x y  = (\<tau> x = \<sigma> y)"
  using local.Dst tgt_local by auto


subsection \<open>Catoids\<close>

class catoid = st_multimagma + multisemigroup

sublocale catoid \<subseteq> ts_msg: catoid "\<lambda>x y. y \<odot> x"  tgt src
  by (unfold_locales, simp add: local.assoc)

lemma (in catoid) src_comp_aux: "v \<in> x \<odot> y \<Longrightarrow> \<sigma> v = \<sigma> x"
  by (metis emptyE insert_iff local.assoc_exp local.s_absorb local.s_absorb_var3)

lemma (in catoid) src_comp: "Src (x \<odot> y) \<subseteq> {\<sigma> x}"
proof-
  {fix a
  assume "a \<in> Src (x \<odot> y)"
  hence "\<exists>b \<in> x \<odot> y. a = \<sigma> b"
    by auto
  hence "\<exists>b. \<sigma> b = \<sigma> x \<and> a = \<sigma> b"
    using local.src_comp_aux by blast
  hence "a = \<sigma> x"
    by blast}
  thus ?thesis
    by blast
qed

lemma (in catoid) src_comp_cond: "(\<Delta> x y) \<Longrightarrow> Src (x \<odot> y) = {\<sigma> x}"
  by (meson image_is_empty local.src_comp subset_singletonD)

lemma (in catoid) tgt_comp_aux: "v \<in> x \<odot> y \<Longrightarrow> \<tau> v = \<tau> y"
  using local.ts_msg.src_comp_aux by fastforce

lemma (in catoid) tgt_comp: "Tgt (x \<odot> y) \<subseteq> {\<tau> y}"
  by (simp add: local.ts_msg.src_comp)

lemma (in catoid) tgt_comp_cond: "\<Delta> x y \<Longrightarrow> Tgt (x \<odot> y) = {\<tau> y}"
  by (simp add: local.ts_msg.src_comp_cond)

lemma (in catoid) src_weak_local: "Src (x \<odot> y) \<subseteq> Src (x \<odot> \<sigma> y)"
proof-
  {fix a
  assume "a \<in> Src (x \<odot> y)"
  hence "\<exists>b \<in> x \<odot> y. a = \<sigma> b"
    by auto
  hence "\<exists>b \<in> x \<odot> y. a = \<sigma> b"
    by blast
  hence "\<exists>b \<in> x \<odot> y. a = \<sigma> b \<and> \<tau> x = \<sigma> y"
    using local.Dst by auto
  hence "\<exists>b \<in> x \<odot> \<sigma> y. a = \<sigma> b"
    by (metis insertI1 local.t_absorb local.ts_msg.tgt_comp_aux)
  hence "a \<in> Src (x \<odot> \<sigma> y)"
    by force}
  thus ?thesis
    by force
qed

lemma (in catoid) src_local_cond:
  "\<Delta> x y \<Longrightarrow> Src (x \<odot> y) = Src (x \<odot> \<sigma> y)"
  by (simp add: local.stopp.Dst local.ts_msg.tgt_comp_cond)

lemma (in catoid) tgt_weak_local: "Tgt (x \<odot> y) \<subseteq> Tgt (\<tau> x \<odot> y)"
  by (simp add: local.ts_msg.src_weak_local)

lemma (in catoid) tgt_local_cond:
  "\<Delta> x y \<Longrightarrow> Tgt (x \<odot> y) = Tgt (\<tau> x \<odot> y)"
  using local.ts_msg.src_local_cond by presburger

lemma (in catoid) src_twisted_aux:
  "u \<in> x \<odot> y \<Longrightarrow> (x \<odot> \<sigma> y = \<sigma> u \<odot> x)"
  by (metis local.Dst local.s_absorb local.src_comp_aux local.t_absorb)

lemma (in catoid) src_twisted_cond:
  "\<Delta> x y \<Longrightarrow> x \<odot> \<sigma> y = \<Union>{\<sigma> u \<odot> x |u. u \<in> x \<odot> y}"
   using local.stopp.Dst local.ts_msg.tgt_comp_aux by auto

lemma (in catoid) tgt_twisted_aux:
  "u \<in> x \<odot> y \<Longrightarrow> (\<tau> x \<odot> y = y \<odot> \<tau> u)"
  by (simp add: local.ts_msg.src_twisted_aux)

lemma (in catoid) tgt_twisted_cond:
  "\<Delta> x y  \<Longrightarrow> \<tau> x \<odot> y = \<Union>{y \<odot> \<tau> u |u. u \<in> x \<odot> y}"
  by (simp add: local.ts_msg.src_twisted_cond)

lemma (in catoid) src_funct:
  "x \<in> y \<odot> z \<Longrightarrow> x' \<in> y \<odot> z \<Longrightarrow> \<sigma> x = \<sigma> x'"
  using local.src_comp_aux by force

lemma (in catoid) st_local_iff:
  "(\<forall>x y. \<Delta> x y = (\<tau> x = \<sigma> y)) = (\<forall>v x y z. v \<in> x \<odot> y \<longrightarrow> \<Delta> y z \<longrightarrow> \<Delta> v z)"
  apply safe
    apply (metis local.ts_msg.src_comp_aux)
  using local.Dst apply blast
  by (metis local.s_absorb_var2 local.t_absorb singleton_iff)

text \<open>Again one can lift to properties of modal semirings and quantales.\<close>

lemma (in catoid) Src_weak_local: "Src (X \<star> Y) \<subseteq> Src (X \<star> Src Y)"
proof-
  {fix a
  assume "a \<in> Src (X \<star> Y)"
  hence "\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. a = \<sigma> b \<and> b \<in> c \<odot> d"
    by (smt (verit) image_iff local.conv_exp2)
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src (c \<odot> d)"
    by auto
  hence "\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src (c \<odot> \<sigma> d)"
    by (metis empty_iff image_empty local.src_local_cond)
  hence "\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Src Y. a = \<sigma> b \<and> b \<in> c \<odot> d"
    by auto
  hence "a \<in> Src (X \<star> Src Y)"
    by (metis image_iff local.conv_exp2)}
  thus ?thesis
    by blast
qed

lemma (in catoid) Tgt_weak_local: "Tgt (X \<star> Y) \<subseteq> Tgt (Tgt X \<star> Y)"
  by (metis local.stopp.conv_exp local.ts_msg.Src_weak_local multimagma.conv_exp)

text \<open>st-Locality implies locality.\<close>

lemma (in catoid) st_locality_l_locality:
  assumes "\<Delta> x y = (\<tau> x = \<sigma> y)"
  shows "Src (x \<odot> y) = Src (x \<odot> \<sigma> y)"
proof-
  {fix a
  have "(a \<in> Src (x \<odot> \<sigma> y)) = (\<exists>b \<in> x \<odot> \<sigma> y. a = \<sigma> b)"
    by auto
  also have "\<dots> = (\<exists>b \<in> x \<odot> \<sigma> y. a = \<sigma> b \<and> \<tau> x = \<sigma> y)"
    by (simp add: local.st_prop local.tgt_comp_aux local.tgt_twisted_aux)
  also have "\<dots> = (\<exists>b \<in> x \<odot> y. a = \<sigma> b)"
    by (metis assms ex_in_conv local.t_absorb local.ts_msg.tgt_comp_aux singletonI)
  also have "\<dots> = (a \<in> Src (x \<odot> y))"
    by auto
  finally have "(a \<in> Src (x \<odot> \<sigma> y)) = (a \<in> Src (x \<odot> y))".}
  thus ?thesis
    by force
qed

lemma (in catoid) st_locality_r_locality:
  assumes lr_locality: "\<Delta> x y = (\<tau> x = \<sigma> y)"
  shows  "Tgt (x \<odot> y) = Tgt (\<tau> x \<odot> y)"
  by (metis local.ts_msg.st_locality_l_locality lr_locality)

lemma (in catoid) st_locality_locality:
  "(Src (x \<odot> y) = Src (x \<odot> \<sigma> y) \<and> Tgt (x \<odot> y) = Tgt (\<tau> x \<odot> y)) = (\<Delta> x y = (\<tau> x = \<sigma> y))"
  apply standard
   apply (simp add: local.locality)
  by (metis local.st_locality_l_locality local.ts_msg.st_locality_l_locality)


subsection \<open>Locality\<close>

text \<open>For st-multimagmas there are different notions of locality. I do not develop this in detail.\<close>

class local_catoid = catoid +
  assumes src_local: "Src (x \<odot> \<sigma> y) \<subseteq> Src (x \<odot> y)"
  and tgt_local: "Tgt (\<tau> x \<odot> y) \<subseteq> Tgt (x \<odot> y)"

sublocale local_catoid \<subseteq> sts_msg: local_catoid "\<lambda>x y. y \<odot> x" tgt src
  apply unfold_locales using local.tgt_local local.src_local by auto

lemma (in local_catoid) src_local_eq [simp]: "Src (x \<odot> \<sigma> y) = Src (x \<odot> y)"
  by (simp add: local.src_local local.src_weak_local order_class.order_eq_iff)

lemma (in local_catoid) tgt_local_eq: "Tgt (\<tau> x \<odot> y) = Tgt (x \<odot> y)"
  by simp

lemma (in local_catoid) src_twisted: "x \<odot> \<sigma> y = (\<Union>u \<in> x \<odot> y. \<sigma> u \<odot> x)"
  by (metis Setcompr_eq_image Sup_empty empty_is_image local.src_twisted_cond local.sts_msg.tgt_local_eq)

lemma (in local_catoid) tgt_twisted: "\<tau> x \<odot> y = (\<Union>u \<in> x \<odot> y. y \<odot> \<tau> u)"
  using local.sts_msg.src_twisted by auto

lemma (in local_catoid) local_var: "\<Delta> x y \<Longrightarrow> \<Delta> (\<tau> x) (\<sigma> y)"
  by (simp add: local.stopp.Dst)

lemma (in local_catoid) local_var_eq [simp]: "\<Delta> (\<tau> x) (\<sigma> y) = \<Delta> x y"
  by (simp add: local.locality)

text \<open>I lift locality to powersets.\<close>

lemma (in local_catoid) Src_local [simp]: "Src (X \<star> Src Y) = Src (X \<star> Y)"
proof-
  {fix a
  have "(a \<in> Src (X \<star> Src Y)) = (\<exists>b \<in> X \<star> Src Y. a = \<sigma> b)"
    by (simp add: image_iff)
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Src Y. b \<in> c \<odot> d \<and> a = \<sigma> b)"
    by (meson local.conv_exp2)
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. b \<in> c \<odot> \<sigma> d \<and> a = \<sigma> b)"
    by simp
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src (c \<odot> \<sigma> d))"
    by blast
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Src (c \<odot> d))"
    by auto
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. b \<in> c \<odot> d \<and> a = \<sigma> b)"
    by auto
  also have "\<dots> = (\<exists>b \<in> X \<star> Y. a = \<sigma> b)"
    by (meson local.conv_exp2)
  also have "\<dots> = (a \<in> Src (X \<star> Y))"
    by (simp add: image_iff)
  finally have "(a \<in> Src (X \<star> Src Y)) = (a \<in> Src (X \<star> Y))".}
  thus ?thesis
    by force
qed

lemma (in local_catoid) Tgt_local [simp]: "Tgt (Tgt X \<star> Y) = Tgt (X \<star> Y)"
  by (metis local.stopp.conv_def local.sts_msg.Src_local multimagma.conv_def)

lemma (in local_catoid) st_local: "\<Delta> x y = (\<tau> x = \<sigma> y)"
  using local.stopp.locality by force


subsection \<open>From partial magmas to single-set categories.\<close>

class functional_magma = multimagma +
  assumes functionality: "x \<in> y \<odot> z \<Longrightarrow> x' \<in> y \<odot> z \<Longrightarrow> x = x'"

begin

text \<open>Functional magmas could also be called partial magmas. The multioperation corresponds to a partial operation.\<close>

lemma partial_card: "card (x \<odot> y) \<le> 1"
  by (metis One_nat_def card.infinite card_le_Suc0_iff_eq local.functionality zero_less_one_class.zero_le_one)

lemma fun_in_sgl: "(x \<in> y \<odot> z) = ({x} = y \<odot> z)"
  using local.functionality by fastforce

text \<open>I introduce a partial operation.\<close>

definition pcomp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70) where
  "x \<otimes> y = (THE z. z \<in> x \<odot> y)"

lemma functionality_var: "\<Delta> x y \<Longrightarrow> (\<exists>!z. z \<in> x \<odot> y)"
  using local.functionality by auto

lemma functionality_lem: "(\<exists>!z. z \<in> x \<odot> y) \<or> (x \<odot> y = {})"
  using functionality_var by blast

lemma functionality_lem_var: "\<Delta> x y = (\<exists>z. {z} = x \<odot> y)"
  using functionality_lem by blast

lemma pcomp_def_var: "(\<Delta> x y \<and> x \<otimes> y = z) = (z \<in> x \<odot> y)"
  unfolding pcomp_def by (smt (verit, del_insts) all_not_in_conv functionality_lem theI_unique)

lemma pcomp_def_var2: "\<Delta> x y \<Longrightarrow> ((x \<otimes> y = z) = (z \<in> x \<odot> y))"
  using pcomp_def_var by blast

lemma pcomp_def_var3: "\<Delta> x y \<Longrightarrow> ((x \<otimes> y = z) = ({z} = x \<odot> y))"
  by (simp add: fun_in_sgl pcomp_def_var2)

end

class functional_st_magma = functional_magma + st_multimagma

class functional_semigroup = functional_magma + multisemigroup

begin

lemma pcomp_assoc_defined: "(\<Delta> u v \<and> \<Delta> (u \<otimes> v) w) = (\<Delta> u (v \<otimes> w) \<and> \<Delta> v w)"
proof-
  have "(\<Delta> u v \<and> \<Delta> (u \<otimes> v) w) = (\<exists>x. \<Delta> u v \<and> \<Delta> x w  \<and> x = u \<otimes> v)"
    by simp
  also have "... = (\<exists>x. x \<in> u \<odot> v \<and> \<Delta> x w)"
    by (metis local.pcomp_def_var)
  also have "... = (\<exists>x. x \<in> v \<odot> w \<and> \<Delta> u x)"
    using local.assoc_exp by blast
  also have "... = (\<exists>x. \<Delta> v w \<and> x = v \<otimes> w \<and> \<Delta> u x)"
    by (metis local.pcomp_def_var)
  also have "... = (\<Delta> u (v \<otimes> w) \<and> \<Delta> v w)"
    by auto
  finally show ?thesis.
qed

lemma pcomp_assoc: "\<Delta> x y \<and> \<Delta> (x \<otimes> y) z \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  by (metis (full_types) local.assoc_var local.conv_atom local.fun_in_sgl local.pcomp_def_var2 pcomp_assoc_defined)

end

class functional_catoid = functional_semigroup + catoid

text \<open>Finally, here comes the definition of single-set categories as in Chapter 12 of Mac Lane's book,
but with partiality of arrow composition modelled using a multioperation, or a partial operation
based on it.\<close>

class single_set_category = functional_catoid + local_catoid

begin

lemma st_assoc: "\<tau> x = \<sigma> y \<Longrightarrow> \<tau> y = \<sigma> z \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
  by (metis local.st_local local.pcomp_assoc local.pcomp_def_var2 local.tgt_comp_aux)

end


subsection  \<open>Morphisms of multimagmas and lr-multimagmas\<close>

text \<open>In the context of single-set categories, these morphisms are functors. Bounded morphisms
are functional bisimulations. They are known as zig-zag morphisms or p-morphism in modal and
substructural logics.\<close>

definition mm_morphism :: "('a::multimagma \<Rightarrow> 'b::multimagma) \<Rightarrow> bool" where
  "mm_morphism f = (\<forall>x y. image f (x \<odot> y) \<subseteq> f x \<odot> f y)"

definition bounded_mm_morphism :: "('a::multimagma \<Rightarrow> 'b::multimagma) \<Rightarrow> bool" where
  "bounded_mm_morphism f = (mm_morphism f \<and> (\<forall>x u v. f x \<in> u \<odot> v \<longrightarrow> (\<exists>y z. u = f y \<and> v = f z \<and> x \<in> y \<odot> z)))"

definition st_mm_morphism :: "('a::st_multimagma \<Rightarrow> 'b::st_multimagma) \<Rightarrow> bool" where
  "st_mm_morphism f = (mm_morphism f \<and> f \<circ> \<sigma> = \<sigma> \<circ> f \<and> f \<circ> \<tau> = \<tau> \<circ> f)"

definition bounded_st_mm_morphism :: "('a::st_multimagma \<Rightarrow> 'b::st_multimagma) \<Rightarrow> bool" where
  "bounded_st_mm_morphism f = (bounded_mm_morphism f \<and> st_mm_morphism f)"


subsection \<open>Relationship with categories\<close>

text \<open>Next I add a standard definition of a category following Moerdijk and Mac Lane's book and,
for good measure, show that categories form single set categories and vice versa.\<close>

locale category =
  fixes id :: "'objects \<Rightarrow> 'arrows"
  and dom :: "'arrows \<Rightarrow> 'objects"
  and cod :: "'arrows \<Rightarrow> 'objects"
  and comp :: "'arrows \<Rightarrow> 'arrows \<Rightarrow> 'arrows" (infixl "\<bullet>" 70)
  assumes dom_id [simp]: "dom (id X) = X"
  and cod_id [simp]: "cod (id X) = X"
  and id_dom [simp]: "id (dom f) \<bullet> f = f"
  and id_cod [simp]: "f \<bullet> id (cod f) = f"
  and dom_loc [simp]: "cod f = dom g \<Longrightarrow> dom (f \<bullet> g) = dom f"
  and cod_loc [simp]: "cod f = dom g \<Longrightarrow> cod (f \<bullet> g) = cod g"
  and assoc: "cod f = dom g \<Longrightarrow> cod g = dom h \<Longrightarrow> (f \<bullet> g) \<bullet> h = f \<bullet> (g \<bullet> h)"

begin

lemma "cod f = dom g \<Longrightarrow> dom (f \<bullet> g) = dom (f \<bullet> id (dom g))"
  by simp

abbreviation "LL f \<equiv> id (dom f)"

abbreviation "RR f \<equiv> id (cod f)"

abbreviation "Comp \<equiv> \<lambda>f g. (if RR f = LL g then {f \<bullet> g} else {})"

end

typedef (overloaded) 'a::single_set_category st_objects = "{x::'a::single_set_category. \<sigma> x = x}"
  using stopp.tt_idem by blast

setup_lifting type_definition_st_objects

lemma Sfix_coerce [simp]: "Abs_st_objects (\<sigma> (Rep_st_objects X)) = X"
  by (smt (verit, best) Rep_st_objects Rep_st_objects_inverse mem_Collect_eq)

lemma Rfix_coerce [simp]: "Abs_st_objects (\<tau> (Rep_st_objects X)) = X"
  by (smt (verit, best) Rep_st_objects Rep_st_objects_inverse mem_Collect_eq stopp.st_fix)

sublocale single_set_category \<subseteq> sscatcat: category Rep_st_objects "Abs_st_objects \<circ> \<sigma>" "Abs_st_objects \<circ> \<tau>" "(\<otimes>)"
  apply unfold_locales
        apply simp_all
      apply (metis (mono_tags, lifting) Abs_st_objects_inverse empty_not_insert functional_magma_class.pcomp_def_var2 insertI1 mem_Collect_eq st_multimagma_class.s_absorb st_multimagma_class.ss_idem)
     apply (metis (mono_tags, lifting) Abs_st_objects_inverse functional_magma_class.pcomp_def_var insert_iff mem_Collect_eq st_multimagma_class.stopp.s_absorb st_multimagma_class.stopp.ts_compat)
    apply (metis (mono_tags, lifting) Abs_st_objects_inject catoid_class.ts_msg.tgt_comp_aux functional_magma_class.pcomp_def_var2 local_catoid_class.sts_msg.st_local mem_Collect_eq st_multimagma_class.stopp.ts_compat st_multimagma_class.stopp.tt_idem)
   apply (metis (mono_tags, lifting) Abs_st_objects_inject functional_semigroup_class.pcomp_assoc_defined local_catoid_class.sts_msg.st_local mem_Collect_eq st_multimagma_class.stopp.s_absorb_var st_multimagma_class.stopp.st_compat)
  by (metis (mono_tags, lifting) Abs_st_objects_inverse mem_Collect_eq single_set_category_class.st_assoc st_multimagma_class.stopp.st_compat st_multimagma_class.stopp.ts_compat)

sublocale category \<subseteq> catlrm: st_multimagma Comp  LL RR
  by unfold_locales auto

sublocale category \<subseteq> catsscat: single_set_category Comp LL RR
  apply unfold_locales
     apply (smt (verit, ccfv_threshold) Sup_empty category.assoc category_axioms ccpo_Sup_singleton cod_id cod_loc dom_loc image_empty image_insert)
    apply (metis empty_iff singletonD)
   apply (smt (verit, best) category.dom_id category_axioms dom_loc image_insert set_eq_subset)
  by (smt (z3) category.cod_id category_axioms cod_loc image_insert subsetI)

subsection \<open>A Mac Lane style variant\<close>

text \<open>Next I present an axiomatisation of single-set categories that follows Mac Lane's axioms
in Chapter I of his textbook more closely, but still uses a multioperation for arrow composition.\<close>

class mlss_cat = functional_magma +
  fixes l0 :: "'a \<Rightarrow>'a"
  fixes r0 :: "'a \<Rightarrow>'a"
  assumes comp0_def: "(x \<odot> y \<noteq> {}) = (r0 x = l0 y)"
  assumes r0l0 [simp]: "r0 (l0 x) = l0 x"
  assumes l0r0 [simp]: "l0 (r0 x) = r0 x"
  assumes l0_absorb [simp]: "l0 x \<otimes> x = x"
  assumes r0_absorb [simp] : "x \<otimes> r0 x = x"
  assumes assoc_defined: "(u \<odot> v \<noteq> {} \<and> (u \<otimes> v) \<odot> w \<noteq> {}) = (u \<odot> (v \<otimes> w) \<noteq> {} \<and> v \<odot> w \<noteq> {})"
  assumes comp0_assoc: "r0 x = l0 y \<Longrightarrow> r0 y = l0 z \<Longrightarrow> x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
  assumes locall_var: "r0 x = l0 y \<Longrightarrow> l0 (x \<otimes> y) = l0 x"
  assumes localr_var: "r0 x = l0 y \<Longrightarrow> r0 (x \<otimes> y) = r0 y"

begin

lemma ml_locall [simp]: "l0 (x \<otimes> l0 y) = l0 (x \<otimes> y)"
  by (metis local.comp0_def local.l0_absorb local.locall_var local.pcomp_def local.r0l0)

lemma ml_localr [simp]: "r0 (r0 x \<otimes> y) = r0 (x \<otimes> y)"
  by (metis local.comp0_def local.l0r0 local.localr_var local.pcomp_def local.r0l0)

lemma ml_locall_im [simp]: "image l0 (x \<odot> l0 y) = image l0 (x \<odot> y)"
  by (metis (no_types, lifting) image_insert image_is_empty local.comp0_def local.fun_in_sgl local.l0r0 local.pcomp_def_var local.r0_absorb local.r0l0 ml_locall)

lemma ml_localr_im [simp]: "image r0 (r0 x \<odot> y) = image r0 (x \<odot> y)"
  by (smt (verit, best) image_insert local.comp0_def local.fun_in_sgl local.functionality_lem local.l0_absorb local.l0r0 local.pcomp_def_var local.r0_absorb ml_localr)

end

sublocale single_set_category \<subseteq> sscatml: mlss_cat "(\<odot>)" "\<sigma>" "\<tau>"
  apply unfold_locales
          apply (simp_all add: st_local pcomp_def_var2)
  using local.pcomp_assoc_defined local.st_local apply force
  using pcomp_assoc_defined st_assoc local.pcomp_def_var2 local.st_local local.src_comp_aux tgt_comp_aux by fastforce+

sublocale mlss_cat \<subseteq> mlsscat: single_set_category "(\<odot>)" "l0" "r0"
  apply unfold_locales
       apply (simp_all add: comp0_def)
    apply standard
     apply (clarsimp, smt (verit, ccfv_SIG) local.assoc_defined local.comp0_assoc local.comp0_def local.fun_in_sgl local.pcomp_def_var)
    apply (clarsimp, metis local.assoc_defined local.comp0_assoc local.comp0_def local.pcomp_def_var)
   apply (metis local.comp0_def local.fun_in_sgl local.l0_absorb local.pcomp_def_var2 local.r0l0)
  using local.comp0_def local.fun_in_sgl local.l0r0 local.pcomp_def_var2 local.r0_absorb by presburger


subsection \<open>Product of catoids\<close>

text \<open>Finally I formalise products of categories as an exercise.\<close>

instantiation prod :: (catoid, catoid) catoid
begin

definition "src_prod x = (\<sigma> (fst x), \<sigma> (snd x))"
  for x :: "'a \<times> 'b"


definition "tgt_prod x = (\<tau> (fst x), \<tau> (snd x))"
  for x :: "'a \<times> 'b"

definition "mcomp_prod x y = {(u,v) |u v. u \<in> fst x \<odot> fst y \<and> v \<in> snd x \<odot> snd y}"
  for x y :: "'a \<times> 'b"

instance
proof
  fix x y z :: "'a \<times> 'b"
  show "(\<Union>v \<in> y \<odot> z. x \<odot> v) = (\<Union>v \<in> x \<odot> y. v \<odot> z)"
  proof-
    {fix a b
      have "((a,b) \<in> (\<Union> v \<in> y \<odot> z. x \<odot> v)) = (\<exists>v. (a,b) \<in> x \<odot> v \<and> v \<in> y \<odot> z)"
        by blast
      also have "\<dots> = (\<exists>v w. a \<in> fst x \<odot> v \<and> v \<in> fst y \<odot> fst z \<and> b \<in> snd x \<odot> w \<and> w \<in> snd y \<odot> snd z)"
        using mcomp_prod_def by auto
      also have "\<dots> = (\<exists>v w. a \<in> v \<odot> fst z \<and> v \<in> fst x \<odot> fst y \<and> b \<in> w \<odot> snd z \<and> w \<in> snd x \<odot> snd y)"
        by (meson ts_msg.assoc_exp)
      also have "\<dots> = (\<exists>v. (a,b) \<in> v \<odot> z \<and> v \<in> x \<odot> y)"
        using mcomp_prod_def by auto
      also have "\<dots> = ((a,b) \<in> (\<Union>v \<in> x \<odot> y. v \<odot> z))"
        by blast
      finally have "((a,b) \<in> (\<Union>v \<in> y \<odot> z. x \<odot> v)) = ((a,b) \<in> (\<Union>v \<in> x \<odot> y. v \<odot> z))".}
    thus ?thesis
      by (meson pred_equals_eq2)
  qed
  show "x \<odot> y \<noteq> {} \<Longrightarrow> \<tau> x = \<sigma> y"
    by (simp add: Catoid.mcomp_prod_def Dst src_prod_def tgt_prod_def)
  show "\<sigma> x \<odot> x = {x}"
    unfolding src_prod_def mcomp_prod_def by simp
  show "x \<odot> \<tau> x = {x}"
    unfolding tgt_prod_def mcomp_prod_def by simp
qed

end

instantiation prod :: (single_set_category, single_set_category) single_set_category
begin

instance
proof
  fix x y z x' :: "'a \<times> 'b"
  show "x \<in> y \<odot> z \<Longrightarrow> x' \<in> y \<odot> z \<Longrightarrow> x = x'"
    unfolding mcomp_prod_def by (smt (verit, best) functionality mem_Collect_eq)
  show a: "stopp.Tgt (x \<odot> \<sigma> y) \<subseteq> stopp.Tgt (x \<odot> y)"
  proof-
    {fix a b
      have "((a,b) \<in> stopp.Tgt (x \<odot> \<sigma> y)) = ((a,b) \<in> Src {(c,d) |c d. c \<in> fst x \<odot> \<sigma> (fst y) \<and> d \<in> snd x \<odot> \<sigma> (snd y)})"
        by (simp add: mcomp_prod_def src_prod_def)
      also have "\<dots> = (a \<in> Src (fst x \<odot> \<sigma> (fst y)) \<and> b \<in> Src (snd x \<odot> \<sigma> (snd y)))"
        by (smt (z3) Setcompr_eq_image fst_conv mem_Collect_eq snd_conv src_prod_def stopp.tt_idem)
      also have "\<dots> = (a \<in> Src (fst x \<odot> fst y) \<and> b \<in> Src (snd x \<odot> snd y))"
        by simp
      also have "\<dots> = ((a,b) \<in> Src {(c,d) |c d. c \<in> (fst x \<odot> fst y) \<and> d \<in> (snd x \<odot> snd y)})"
        by (smt (z3) Setcompr_eq_image fst_conv mem_Collect_eq snd_conv src_prod_def stopp.tt_idem)
      also have "\<dots> = ((a,b) \<in> stopp.Tgt (x \<odot> y))"
        by (simp add: mcomp_prod_def src_prod_def)
      finally have "((a,b) \<in> stopp.Tgt (x \<odot> \<sigma> y)) = ((a,b) \<in> stopp.Tgt (x \<odot> y))".}
    thus ?thesis
      by auto
  qed
  show "Tgt (\<tau> x \<odot> y) \<subseteq> Tgt (x \<odot> y)"
    by (metis (no_types, lifting) a bot.extremum_uniqueI empty_is_image stopp.s_absorb_var3 tgt_local_cond tgt_weak_local ts_msg.st_locality_l_locality)
qed

end

end


