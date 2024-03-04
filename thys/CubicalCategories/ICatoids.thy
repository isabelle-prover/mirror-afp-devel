(*
Title: Indexed Catoids
Authors: Tanguy Massacrier, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section\<open>Indexed Catoids\<close>

theory ICatoids
  imports Catoids.Catoid

begin

text \<open>All categories considered in this component are single-set categories.\<close>

no_notation src ("\<sigma>")

notation True ("tt") 
notation False ("ff")

abbreviation Fix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
  "Fix f \<equiv> {x. f x = x}"

text \<open>First we lift locality to powersets.\<close>

lemma (in local_catoid) locality_lifting: "(X \<star> Y \<noteq> {}) = (Tgt X \<inter> Src Y \<noteq> {})"
proof-
  have "(X \<star> Y \<noteq> {}) = (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> x \<odot> y \<noteq> {})"
    by (metis (mono_tags, lifting) all_not_in_conv conv_exp2)
  also have "\<dots> = (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> tgt x = src y)"
    using local.st_local by auto
  also have "\<dots> = (Tgt X \<inter> Src Y \<noteq> {})"
    by blast
  finally show ?thesis.
qed

text \<open>The following lemma about functional catoids is useful in proofs.\<close>

lemma (in functional_catoid) pcomp_def_var4: "\<Delta> x y \<Longrightarrow> x \<odot> y = {x \<otimes> y}"
  using local.pcomp_def_var3 by blast


subsection \<open>Indexed catoids and categories\<close>

class face_map_op = 
  fixes fmap :: "nat \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("\<partial>") 

begin

abbreviation Face :: "nat \<Rightarrow> bool \<Rightarrow> 'a set \<Rightarrow> 'a set" ("\<partial>\<partial>") where
  "\<partial>\<partial> i \<alpha> \<equiv> image (\<partial> i \<alpha>)"

abbreviation face_fix :: "nat \<Rightarrow> 'a set" where
  "face_fix i \<equiv> Fix (\<partial> i ff)"

abbreviation "fFx i x \<equiv> (\<partial> i ff x = x)"

abbreviation "FFx i X \<equiv> (\<forall>x \<in> X. fFx i x)"

end

class icomp_op =
  fixes icomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a set" ("_\<odot>\<^bsub>_\<^esub>_"[70,70,70]70)

class imultisemigroup = icomp_op +
  assumes iassoc: "(\<Union>v \<in> y \<odot>\<^bsub>i\<^esub> z. x \<odot>\<^bsub>i\<^esub> v) = (\<Union>v \<in> x \<odot>\<^bsub>i\<^esub> y. v \<odot>\<^bsub>i\<^esub> z)"

begin

sublocale ims: multisemigroup "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"
  by unfold_locales (simp add: local.iassoc)

abbreviation "DD \<equiv> ims.\<Delta>"

abbreviation iconv :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<star>\<^bsub>_\<^esub>_"[70,70,70]70) where
  "X \<star>\<^bsub>i\<^esub> Y \<equiv> ims.conv i X Y"

end

class icatoid = imultisemigroup + face_map_op +
  assumes iDst: "DD i x y \<Longrightarrow> \<partial> i tt x = \<partial> i ff y"
  and is_absorb [simp]: "(\<partial> i ff x) \<odot>\<^bsub>i\<^esub> x = {x}"
  and it_absorb [simp]: "x \<odot>\<^bsub>i\<^esub> (\<partial> i tt x) = {x}"

begin

text \<open>Every indexed catoid is a catoid. \<close>

sublocale icid: catoid "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "\<partial> i ff" "\<partial> i tt"
  by unfold_locales (simp_all add: iDst)

lemma lFace_Src: "\<partial>\<partial> i ff = icid.Src i"
  by simp

lemma uFace_Tgt: "\<partial>\<partial> i tt = icid.Tgt i"
  by simp

lemma face_fix_sfix: "face_fix = icid.sfix"
  by force

lemma face_fix_tfix: "face_fix = icid.tfix"
  using icid.stopp.stfix_set by presburger

lemma face_fix_prop [simp]: "x \<in> face_fix i = (\<partial> i \<alpha> x = x)"
  by (smt (verit, del_insts) icid.stopp.st_fix mem_Collect_eq)

lemma fFx_prop: "fFx i x = (\<partial> i \<alpha> x = x)"
  by (metis icid.st_eq1 icid.st_eq2)

end

class icategory = icatoid +
  assumes locality: "\<partial> i tt x = \<partial> i ff y \<Longrightarrow> DD i x y"
  and functionality: "z \<in> x \<odot>\<^bsub>i\<^esub> y \<Longrightarrow> z' \<in> x \<odot>\<^bsub>i\<^esub> y \<Longrightarrow> z = z'"

begin 

text \<open>Every indexed category is a (single-set) category.\<close>

sublocale icat: single_set_category "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "\<partial> i ff" "\<partial> i tt"
  apply unfold_locales
    apply (simp add: local.functionality)
   apply (metis dual_order.eq_iff icid.src_local_cond icid.st_locality_locality local.locality)
  by (metis icid.st_locality_locality local.iDst local.locality order_refl)

abbreviation ipcomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<otimes>\<^bsub>_\<^esub>_"[70,70,70]70) where
  "x \<otimes>\<^bsub>i\<^esub> y \<equiv> icat.pcomp i x y"

lemma iconv_prop: "X \<star>\<^bsub>i\<^esub> Y = {x \<otimes>\<^bsub>i\<^esub>y |x y. x \<in> X \<and> y \<in> Y \<and> DD i x y}"
  by (rule antisym) (clarsimp simp: ims.conv_def, metis local.icat.pcomp_def_var)+

abbreviation "dim_bound k x \<equiv> (\<forall>i. k \<le> i \<longrightarrow> fFx i x)"

abbreviation "fin_dim x \<equiv> (\<exists>k. dim_bound k x)"

end

end