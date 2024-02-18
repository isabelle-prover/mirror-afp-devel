(* 
Title: Omega-Catoids
Author: Cameron Calk, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>$\omega$-Catoids\<close>

theory Omega_Catoid
  imports "Two_Catoid"

begin

subsection \<open>Indexed catoids.\<close>

text \<open>We add an index to the operations of catoids.\<close>

class imultimagma = 
  fixes imcomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a set" ("_\<odot> \<^bsub>_\<^esub> _" [70,70,70]70) 

definition (in imultimagma) iconv  :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<star>\<^bsub>_\<^esub>_"[70,70,70]70) where
  "X \<star>\<^bsub>i\<^esub> Y = (\<Union>x \<in> X. \<Union>y \<in> Y. x \<odot>\<^bsub>i\<^esub> y)"

class imultisemigroup = imultimagma +
  assumes assoc: "(\<Union>v \<in> y \<odot>\<^bsub>i\<^esub> z. x \<odot>\<^bsub>i\<^esub> v) = (\<Union>v \<in> x \<odot>\<^bsub>i\<^esub> y. v \<odot>\<^bsub>i\<^esub> z)"

begin

sublocale ims: multisemigroup "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"
  by unfold_locales (simp add: local.assoc)

abbreviation "DD \<equiv> ims.\<Delta>"

lemma iconv_prop: "X \<star>\<^bsub>i\<^esub> Y \<equiv> ims.conv i X Y"
  by (simp add: local.iconv_def multimagma.conv_def)

end

class st_imultimagma = imultimagma + 
 fixes src :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
 and tgt :: "nat \<Rightarrow> 'a \<Rightarrow> 'a"
 assumes Dst: "x \<odot>\<^bsub>i\<^esub> y \<noteq> {} \<Longrightarrow> tgt i x = src i y"
 and src_absorb [simp]: "(src i x) \<odot>\<^bsub>i\<^esub> x = {x}" 
 and tgt_absorb [simp]: "x \<odot>\<^bsub>i\<^esub> (tgt i x) = {x}" 

begin

lemma inst: "(src 1 x) \<odot>\<^bsub>1\<^esub> x = {x}"
  by simp 

sublocale stimm: st_multimagma "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales (simp_all add: local.Dst)

sublocale stimm0: st_multimagma0 "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales (simp_all add: local.Dst)

sublocale stimm1: st_multimagma1 "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales (simp_all add: local.Dst)

abbreviation "srcfix \<equiv> stimm.sfix"

abbreviation "tgtfix \<equiv> stimm.tfix"

abbreviation "Srci \<equiv> stimm.Src"

abbreviation "Tgti \<equiv> stimm.Tgt"

end

class icatoid = st_imultimagma + imultisemigroup

sublocale icatoid \<subseteq> icat: catoid  "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales

class local_icatoid = icatoid +
  assumes src_local: "Srci i (x \<odot>\<^bsub>i\<^esub> src i y) \<subseteq> Srci i (x \<odot>\<^bsub>i\<^esub> y)"
  and tgt_local: "Tgti i (tgt i x \<odot>\<^bsub>i\<^esub> y) \<subseteq> Tgti i (x \<odot>\<^bsub>i\<^esub> y)"

sublocale local_icatoid \<subseteq> licat: local_catoid  "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales(simp_all add: local.src_local local.tgt_local)

class functional_imagma = imultimagma + 
  assumes functionality: "x \<in> y \<odot>\<^bsub>i\<^esub> z \<Longrightarrow> x' \<in> y \<odot>\<^bsub>i\<^esub> z \<Longrightarrow> x = x'"

sublocale functional_imagma \<subseteq> pmi: functional_magma "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"
  by unfold_locales(simp add: local.functionality)

class functional_isemigroup = functional_imagma + imultisemigroup

sublocale functional_isemigroup \<subseteq> psgi: functional_semigroup "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"..

class functional_icatoid = functional_isemigroup + icatoid

sublocale functional_icatoid \<subseteq> psgi: functional_catoid  "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales

class icategory = functional_icatoid + local_icatoid

sublocale icategory \<subseteq> icatt: single_set_category "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "src i" "tgt i"
  by unfold_locales

subsection \<open>$\omega$-Catoids\<close>

text \<open>Next we define $\omega$-catoids and $\omega$-categories.\<close>

class omega_st_multimagma = st_imultimagma +
  assumes comm_sisj: "i \<noteq> j \<Longrightarrow> src i (src j x) = src j (src i x)"
  and comm_sitj: "i \<noteq> j \<Longrightarrow> src i (tgt j x) = tgt j (src i x)"
  and comm_titj: "i \<noteq> j \<Longrightarrow> tgt i  (tgt j x) = tgt j (tgt i x)"
  and si_hom: "i \<noteq> j \<Longrightarrow> Srci i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> src i x \<odot>\<^bsub>j\<^esub> src i y"
  and ti_hom: "i \<noteq> j \<Longrightarrow> Tgti i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> tgt i x \<odot>\<^bsub>j\<^esub> tgt i y"
  and omega_interchange: "i < j \<Longrightarrow> (w \<odot>\<^bsub>j\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>j\<^esub> z) \<subseteq> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>j\<^esub> (x \<odot>\<^bsub>i\<^esub> z)"
  and sjsi [simp]: "i < j \<Longrightarrow> src j (src i x) = src i x"
  and sjti [simp]: "i < j \<Longrightarrow> src j (tgt i x) = tgt i x"
  and tjsi [simp]: "i < j \<Longrightarrow> tgt j (src i x) = src i x"
  and tjti [simp]: "i < j \<Longrightarrow> tgt j (tgt i x) = tgt i x"

class omega_catoid = omega_st_multimagma + icatoid

context omega_st_multimagma
begin

lemma omega_interchange_var: "(w \<odot>\<^bsub>(i + k + 1)\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>(i + k + 1)\<^esub> z) \<subseteq> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>(i + k + 1)\<^esub> (x \<odot>\<^bsub>i\<^esub> z)"
  using local.omega_interchange by auto

lemma all_sisj: "src i (src j x) = src j (src i x)"
  by (metis local.comm_sisj)

lemma all_titj: "tgt i (tgt j x) = tgt j (tgt i x)"
  by (metis local.comm_titj)

lemma sjsi_var [simp]: "src (i + k) (src i x) = src i x"
  by (metis le_add1 local.sjsi local.stimm.stopp.tt_idem nless_le)

lemma sjti_var [simp]: "src (i + k) (tgt i x) = tgt i x"
  by (metis local.stimm.stopp.ts_compat sjsi_var)

lemma tjsi_var [simp]: "tgt (i + k) (src i x) = src i x"
  by (simp add: stimm.st_fix)

lemma tjti_var [simp]: "tgt (i + k) (tgt i x) = tgt i x"
  by (simp add: stimm.st_fix)

text \<open>The following sublocale statement should help us to translate statements for 2-catoids to 
$\omega$-catoids. But it does not seem to work. Hence we duplicate the work done for 2-catoids, and
later also for semirings and quantales.\<close>

sublocale otmm: two_st_multimagma  
  "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"  
  "src i" 
  "tgt i" 
  "\<lambda>x y. x \<odot>\<^bsub>(i + k + 1)\<^esub> y"  
  "src (i + k + 1)" 
  "tgt (i + k + 1)"
  apply unfold_locales
              apply (simp_all add: comm_sisj comm_sitj comm_titj si_hom ti_hom)
  using less_add_Suc1 local.all_sisj local.sjsi apply simp
  apply (metis lessI less_add_Suc1 local.comm_sitj local.sjti not_add_less1)
  apply (metis less_add_Suc1 local.comm_titj local.tjti)
  using local.iconv_def local.omega_interchange local.stimm.conv_def by simp

end

class omega_st_multimagma_strong = omega_st_multimagma +
 assumes sj_hom_strong: "i < j \<Longrightarrow> Srci j (x \<odot>\<^bsub>i\<^esub> y) = src j x \<odot>\<^bsub>i\<^esub> src j y"
 and tj_hom_strong: "i < j \<Longrightarrow> Tgti j (x \<odot>\<^bsub>i\<^esub> y) = tgt j x \<odot>\<^bsub>i\<^esub> tgt j y"

begin

lemma sj_hom_strong_var: "Srci (i + k + 1) (x \<odot>\<^bsub>i\<^esub> y) = src (i + k + 1) x \<odot>\<^bsub>i\<^esub> src (i + k + 1) y"
  by (simp add: local.sj_hom_strong)

lemma tj_hom_strong_var: "Tgti (i + k + 1) (x \<odot>\<^bsub>i\<^esub> y) = tgt (i + k + 1) x \<odot>\<^bsub>i\<^esub> tgt (i + k + 1) y"
  by (simp add: local.tj_hom_strong)

end

sublocale omega_st_multimagma \<subseteq> olropp: omega_st_multimagma "\<lambda> x i y. y \<odot>\<^bsub>i\<^esub> x" "tgt" "src"
  apply unfold_locales
  apply (simp_all add: local.Dst)
  using local.comm_titj apply simp
  using local.comm_sitj apply simp
  using local.all_sisj apply simp
  apply (simp add: local.ti_hom)
  apply (simp add: local.si_hom)
  unfolding imultimagma.iconv_def
  using local.iconv_def local.omega_interchange local.stimm.conv_def local.stimm.stopp.conv_def by simp

context omega_st_multimagma
begin

lemma sisj: "i \<le> j \<Longrightarrow> src i (src j x) = src i x"
  using antisym_conv2 local.all_sisj local.sjsi by fastforce

lemma sisj_var [simp]: "src i (src (i + k) x) = src i x"
  by (simp add: sisj)

lemma sitj: "i < j \<Longrightarrow> src i (tgt j x) = src i x"
  by (simp add: local.comm_sitj)

lemma sitj_var [simp]: "src i (tgt (i + k + 1) x) = src i x"
  using local.otmm.twolropp.t0s1 by auto

lemma tisj: "i < j \<Longrightarrow> tgt i (src j x) = tgt i x"
  by (simp add: local.olropp.comm_sitj)

lemma tisj_var [simp]: "tgt i (src (i + k + 1) x) = tgt i x"
  using local.otmm.twolropp.s0t1 by auto

lemma titi: "i \<le> j \<Longrightarrow> tgt i (tgt j x) = tgt i x"
  using antisym_conv2 local.olropp.all_sisj local.tjti by fastforce

lemma titi_var [simp]: "tgt i (tgt (i + k) x) = tgt i x"
  by (simp add: titi)

end

context omega_catoid
begin

lemma src_icat1:
  assumes "i \<le> j"
  and "DD j x y"
  shows "Srci i (x \<odot>\<^bsub>j\<^esub> y) = {src i x}"
  by (smt (verit, ccfv_SIG) assms icat.src_comp_cond image_is_empty local.comm_sitj local.si_hom local.sisj local.stimm.stopp.Dst local.tgt_absorb subset_singletonD)

lemma src_icat2:
  assumes "i < j"
  and "DD j x y"
shows "Srci i (x \<odot>\<^bsub>j\<^esub> y) = {src i y}"
  by (metis assms less_or_eq_imp_le local.all_sisj local.sitj local.sjsi local.stimm.stopp.Dst src_icat1)

lemma tgt_icat1:
  assumes "i < j"
  and "DD j x y"
  shows "Tgti i (x \<odot>\<^bsub>j\<^esub> y) = {tgt i x}"
  by (smt (verit) assms image_is_empty local.olropp.all_sisj local.stimm.stopp.Dst local.ti_hom local.tisj local.tjti not_less_iff_gr_or_eq stimm.t_idem subset_singletonD)

lemma tgt_icat2:
  assumes "i \<le> j"
  and "DD j x y"
  shows "Tgti i (x \<odot>\<^bsub>j\<^esub> y) = {tgt i y}"
  by (smt (verit, best) assms(1) assms(2) icat.tgt_comp_cond local.all_titj local.stimm.stopp.Dst local.tisj local.tjti nat_less_le tgt_icat1)

end
text \<open>We lift the axioms to the powerset level.\<close>

context omega_st_multimagma
begin

lemma comm_SiSj: "Srci i (Srci j X) = Srci j (Srci i X)"
  by (metis (mono_tags, lifting) image_cong image_image local.comm_sisj)

lemma comm_TiTj: "Tgti i (Tgti j X) = Tgti j (Tgti i X)"
  by (simp add: image_image local.olropp.all_sisj)

lemma comm_SiTj: "i \<noteq> j \<Longrightarrow> Srci i (Tgti j x) = Tgti j (Srci i x)"
  by (metis (mono_tags, lifting) image_cong image_image local.comm_sitj)

lemma comm_TiSj: "i \<noteq> j \<Longrightarrow> Tgti i (Srci j x) = Srci j (Tgti i x)"
  using local.comm_SiTj by simp

lemma interchange_lift: 
  assumes "i < j"
  shows "(W \<star>\<^bsub>j\<^esub> X) \<star>\<^bsub>i\<^esub> (Y \<star>\<^bsub>j\<^esub> Z) \<subseteq> (W \<star>\<^bsub>i\<^esub> Y) \<star>\<^bsub>j\<^esub> (X \<star>\<^bsub>i\<^esub> Z)"
proof-
  {fix a
  assume "a \<in> (W \<star>\<^bsub>j\<^esub> X) \<star>\<^bsub>i\<^esub> (Y \<star>\<^bsub>j\<^esub> Z)"
  hence "\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. a \<in> (w \<odot>\<^bsub>j\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>j\<^esub> z)"
    unfolding iconv_def by force
  hence "\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. a \<in> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>j\<^esub> (x \<odot>\<^bsub>i\<^esub> z)"
    using assms local.omega_interchange by fastforce
  hence "a \<in> (W \<star>\<^bsub>i\<^esub> Y) \<star>\<^bsub>j\<^esub> (X \<star>\<^bsub>i\<^esub> Z)"
    unfolding iconv_def by force}
  thus ?thesis..
qed

lemma Srcj_hom: 
  assumes "i \<noteq> j"
  shows "Srci j (X \<star>\<^bsub>i\<^esub> Y) \<subseteq> Srci j X \<star>\<^bsub>i\<^esub> Srci j Y" 
  unfolding iconv_def by (clarsimp, metis assms image_subset_iff local.si_hom)

lemma Tgtj_hom:
  assumes "i \<noteq> j"
  shows "Tgti j (X \<star>\<^bsub>i\<^esub> Y) \<subseteq> Tgti j X \<star>\<^bsub>i\<^esub> Tgti j Y" 
  unfolding iconv_def by (clarsimp, metis assms image_subset_iff local.ti_hom)

lemma SjSi: "i \<le> j \<Longrightarrow> Srci j (Srci i X) = Srci i X"
  by (smt (verit, best) antisym_conv2 imageE image_cong local.sjsi local.stimm.stopp.ST_compat local.stimm.stopp.ts_compat stimm.ts_compat)

lemma SjSi_var [simp]: "Srci (i + k) (Srci i X) = Srci i X"
  by (simp add: image_image)

lemma SjTi: "i \<le> j \<Longrightarrow> Srci j (Tgti i X) = Tgti i X"
  by (metis SjSi_var less_eqE local.stimm.stopp.TS_compat)

lemma SjTi_var [simp]: "Srci (i + k) (Tgti i X) = Tgti i X"
  by (simp add: SjTi)

lemma TjSi: "i \<le> j \<Longrightarrow> Tgti j (Srci i X) = Srci i X"
  by (metis local.SjSi local.stimm.stopp.ST_compat)

lemma TjSi_var [simp]: "Tgti (i + k) (Srci i X) = Srci i X"
  using TjSi le_add1 by presburger

lemma TjTi: "i \<le> j \<Longrightarrow> Tgti j (Tgti i X) = Tgti i X"
  by (metis local.SjTi local.stimm.stopp.ST_compat)

lemma TjTi_var [simp]: "Tgti (i + k) (Tgti i X) = Tgti i X"
  by (simp add: TjTi)

lemma srcfixij: "i \<le> j \<Longrightarrow> srcfix i \<subseteq> srcfix i \<star>\<^bsub>j\<^esub> srcfix i"
  by (smt (verit, ccfv_SIG) UN_iff antisym_conv2 local.iconv_def local.tgt_absorb local.tjti mem_Collect_eq singletonI stimm.ts_compat subsetI)

lemma srcfixij_var: "srcfix i \<subseteq> srcfix i \<star>\<^bsub>(j + k)\<^esub> srcfix i"
  by (smt (verit, ccfv_SIG) UN_iff local.comm_sitj local.iconv_def local.stimm.stopp.ts_compat local.tgt_absorb mem_Collect_eq singletonI subsetI)

lemma srcfixij_var2: "i \<le> j \<Longrightarrow> srcfix i \<subseteq> srcfix j"
  by (metis local.SjSi local.stimm.stopp.Tgt_subid local.stimm.stopp.tfix_im)

lemma srcfixij_var3: "srcfix i \<subseteq> srcfix (i + k)"
  using le_add1 srcfixij_var2 by blast

end

context omega_st_multimagma_strong
begin

lemma Srcj_hom_strong: 
  assumes "i < j"
  shows "Srci j (X \<star>\<^bsub>i\<^esub> Y) = Srci j X \<star>\<^bsub>i\<^esub> Srci j Y"
proof-
  {fix a 
  have "(a \<in> Srci j (X \<star>\<^bsub>i\<^esub> Y)) = (\<exists>b \<in> X \<star>\<^bsub>i\<^esub> Y. a = src j b)"
    by force
  also have "\<dots> = (\<exists>b. \<exists>c \<in> X. \<exists>d \<in> Y. a = src j b \<and> b \<in> c \<odot>\<^bsub>i\<^esub> d)"
    using local.iconv_def by auto
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Srci j (c \<odot>\<^bsub>i\<^esub> d))"
    by force
  also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> src j c \<odot>\<^bsub>i\<^esub> src j d)"
    using assms local.sj_hom_strong by auto
  also have "\<dots> = (\<exists>c \<in> Srci j X. \<exists>d \<in> Srci j Y. a \<in> c \<odot>\<^bsub>i\<^esub> d)"
    by force
  also have "\<dots> = (a \<in> Srci j X \<star>\<^bsub>i\<^esub> Srci j Y)"
    by (simp add: local.iconv_def)
  finally have "(a \<in> Srci j (X \<star>\<^bsub>i\<^esub> Y)) = (a \<in> Srci j X \<star>\<^bsub>i\<^esub> Srci j Y)".}
  thus ?thesis
    by force
qed

lemma Srcj_hom_strong_var: "Srci (i + k + 1) (X \<star>\<^bsub>i\<^esub> Y) = Srci (i + k + 1) X \<star>\<^bsub>i\<^esub> Srci (i + k + 1) Y"
  by (simp add: Srcj_hom_strong)

lemma Tgtj_hom_strong: 
  assumes "i < j"
  shows "Tgti j (X \<star>\<^bsub>i\<^esub> Y) = Tgti j X \<star>\<^bsub>i\<^esub> Tgti j Y" 
proof-
  {fix a 
    have "(a \<in> Tgti j (X \<star>\<^bsub>i\<^esub> Y)) = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> Tgti j (c \<odot>\<^bsub>i\<^esub> d))"
      using local.iconv_def by force
    also have "\<dots> = (\<exists>c \<in> X. \<exists>d \<in> Y. a \<in> tgt j c \<odot>\<^bsub>i\<^esub> tgt j d)"
      using assms local.tj_hom_strong by force
    also have "\<dots> = (a \<in> Tgti j X \<star>\<^bsub>i\<^esub> Tgti j Y)"
      by (simp add: local.iconv_def)
  finally have "(a \<in> Tgti j (X \<star>\<^bsub>i\<^esub> Y)) = (a \<in> Tgti j X \<star>\<^bsub>i\<^esub> Tgti j Y)".}
  thus ?thesis
    by force
qed

lemma Tgtj_hom_strong_var: "Tgti (i + k + 1) (X \<star>\<^bsub>i\<^esub> Y) = Tgti (i + k + 1) X \<star>\<^bsub>i\<^esub> Tgti (i + k + 1) Y"
  using Tgtj_hom_strong by auto 

lemma srcfixij_var2: "i < j \<Longrightarrow> srcfix j \<star>\<^bsub>i\<^esub> srcfix j \<subseteq> srcfix j"
  by (metis local.Srcj_hom_strong local.stimm.stopp.Tgt_subid local.stimm.stopp.tfix_im)

lemma srcfixij_var22: "srcfix (i + k + 1) \<star>\<^bsub>i\<^esub> srcfix (i + k + 1) \<subseteq> srcfix (i + k + 1)"
  using Suc_eq_plus1 less_add_Suc1 local.srcfixij_var2 by presburger
 
lemma srcfixij_eq: "i < j \<Longrightarrow> srcfix j \<star>\<^bsub>i\<^esub> srcfix j = srcfix j"
  unfolding iconv_def
  apply safe
   apply (metis imageE local.sj_hom_strong local.stimm.stopp.tt_idem)
  by (smt (verit, ccfv_threshold) UN_iff local.sjsi local.stimm.stopp.ts_compat local.tgt_absorb mem_Collect_eq singletonI)

lemma srcfixij_eq_var [simp]: "srcfix (i + k + 1) \<star>\<^bsub>i\<^esub> srcfix (i + k + 1) = srcfix (i + k + 1)"
  using Suc_eq_plus1 less_add_Suc1 srcfixij_eq by presburger

end

subsection\<open>$\omega$-Catoids and single-set $\omega$-categories\<close>

class omega_catoid_strong = omega_st_multimagma_strong + omega_catoid

class local_omega_catoid = omega_st_multimagma + local_icatoid

class functional_omega_catoid = omega_st_multimagma  + functional_icatoid

class local_omega_catoid_strong = omega_st_multimagma_strong + local_icatoid

class omega_category = omega_st_multimagma + icategory

begin

lemma sj_hom_strong: 
  assumes "i < j"
  shows "Srci j (x \<odot>\<^bsub>i\<^esub> y) = src j x \<odot>\<^bsub>i\<^esub> src j y"
  by (smt (verit, best) assms image_is_empty less_or_eq_imp_le licat.src_local_eq local.pmi.functionality_lem_var local.si_hom local.sisj local.stimm.stopp.Dst local.tgt_absorb local.tisj nat_neq_iff subset_singletonD)

lemma sj_hom_strong_var: "Srci (i + k + 1) (x \<odot>\<^bsub>i\<^esub> y) = src (i + k + 1) x \<odot>\<^bsub>i\<^esub> src (i + k + 1) y"
  using local.sj_hom_strong by force

lemma sj_hom_strong_delta: "i < j \<Longrightarrow> DD i x y = DD i (src j x) (src j y)"
  using local.sisj local.tisj stimm.locality by simp

lemma tj_hom_strong: "i < j \<Longrightarrow> Tgti j (x \<odot>\<^bsub>i\<^esub> y) = tgt j x \<odot>\<^bsub>i\<^esub> tgt j y"
  by (smt (verit, best) empty_is_image licat.st_local local.olropp.si_hom local.pmi.functionality_lem_var local.sitj local.titi order.strict_iff_order subset_singleton_iff)

lemma tj_hom_strong_var: "Tgti (i + k + 1) (x \<odot>\<^bsub>i\<^esub> y) = tgt (i + k + 1) x \<odot>\<^bsub>i\<^esub> tgt (i + k + 1) y"
  by (simp add: local.tj_hom_strong)

lemma tj_hom_strong_delta: " i < j \<Longrightarrow> DD i x y = DD i (tgt j x) (tgt j y)"
  using less_or_eq_imp_le licat.st_local local.sitj local.titi by simp

lemma convi_sgl: "a \<in> x \<odot>\<^bsub>i\<^esub> y \<Longrightarrow> {a} = x \<odot>\<^bsub>i\<^esub> y"
  by (simp add: local.pmi.fun_in_sgl)

text \<open>Next we derive some simple globular properties.\<close>

lemma strong_interchange_STj: 
  assumes "i < j"
  and "a \<in> (w \<odot>\<^bsub>i\<^esub> x) \<star>\<^bsub>j\<^esub> (y \<odot>\<^bsub>i\<^esub> z)"
  shows "Tgti j (w \<odot>\<^bsub>i\<^esub> x) = Srci j (y \<odot>\<^bsub>i\<^esub> z)"
  by (smt (verit) assms(2) image_empty image_insert local.iconv_prop local.pmi.fun_in_sgl local.pmi.pcomp_def_var local.stimm.stopp.Dst multimagma.conv_exp2)

lemma strong_interchange_ssi: 
  assumes "i < j"
  and "a \<in> (w \<odot>\<^bsub>i\<^esub> x) \<star>\<^bsub>j\<^esub> (y \<odot>\<^bsub>i\<^esub> z)"
shows "src i w = src i y"
  by (smt (verit, ccfv_threshold) assms icat.src_comp_aux icat.tgt_comp_aux less_or_eq_imp_le local.iconv_prop local.sisj local.sitj multimagma.conv_exp2)

end


subsection \<open>Reduced axiomatisations\<close>

class omega_st_multimagma_red = st_imultimagma +
  assumes interchange: "i < j \<Longrightarrow> (w \<odot>\<^bsub>j\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>j\<^esub> z) \<subseteq> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>j\<^esub> (x \<odot>\<^bsub>i\<^esub> z)" (* irredundant *)
  assumes srcj_hom: "i < j \<Longrightarrow> Srci j (x \<odot>\<^bsub>i\<^esub> y) = src j x \<odot>\<^bsub>i\<^esub> srcj y"  (* irredundant *)
  and tgtj_hom: "i < j \<Longrightarrow> Tgti j (x \<odot>\<^bsub>i\<^esub> y) = tgt j x \<odot>\<^bsub>i\<^esub> tgt j y" (* irredundant *)
  and srci_weak_hom: "i < j \<Longrightarrow> Srci i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> src i x \<odot>\<^bsub>j\<^esub> src i y" (* no proof no counterexample *)
  and tgti_weak_hom: "i < j \<Longrightarrow> Tgti i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> src i x \<odot>\<^bsub>j\<^esub> src i y" (* no proof no counterexample *) 

begin

lemma sitjsi [simp]: "src i (tgt j (src i x)) = src i x"
  by (smt (z3) empty_iff image_empty image_insert insert_subset less_add_Suc1 local.srcj_hom local.stimm.stopp.t_idem stimm.s_absorb_var2 subset_empty)

lemma tisjsi [simp]: "tgt i (src j (src i x)) = src i x"
  by (smt (verit) local.srcj_hom local.stimm.stopp.s_absorb_var3 local.stimm.stopp.ts_compat not_less_iff_gr_or_eq sitjsi)

lemma sjsi: 
  assumes "i \<le> j"
  shows "src j (src i x) = src i x"
  by (smt (verit) antisym_conv2 assms insertE insert_absorb insert_subset local.Dst local.iconv_def local.interchange local.src_absorb local.stimm.conv_def local.stimm.stopp.conv_atom local.tgt_absorb local.tgtj_hom stimm.s_absorb_var2 stimm.t_export tisjsi)

lemma sjti: "i \<le> j \<Longrightarrow> src j (tgt i x) = tgt i x"
  by (metis local.sjsi local.stimm.stopp.ts_compat)

lemma tjsi: "i \<le> j \<Longrightarrow> tgt j (src i x) = src i x"
  by (metis antisym_conv2 local.sjsi stimm.ts_compat)

lemma tjti: "i \<le> j \<Longrightarrow> tgt j  (tgt i x) = tgt i x"
  by (simp add: local.sjti stimm.st_fix)

lemma comm_sisj: "i \<noteq> j \<Longrightarrow> src i (src j x) = src j (src i x)"
  by (smt (verit, ccfv_threshold) less_or_eq_imp_le local.sjsi local.srcj_hom not_less_iff_gr_or_eq stimm.s_ortho_iff tisjsi)

lemma comm_sitj: "i \<noteq> j \<Longrightarrow> src i (tgt j x) = tgt j (src i x)"
  by (smt (verit, best) local.srcj_hom local.stimm.stopp.ts_compat local.tjsi nat_less_le nle_le stimm.s_absorb_var)

lemma comm_titj: "i \<noteq> j \<Longrightarrow> tgt i (tgt j x) = tgt j (tgt i x)"
  by (smt (verit, ccfv_SIG) local.comm_sisj local.comm_sitj local.stimm.stopp.ts_compat tisjsi)

end

class omega_catoid_red = icatoid +
  assumes interchange: "i < j \<Longrightarrow> (w \<odot>\<^bsub>j\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>j\<^esub> z) \<subseteq> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>j\<^esub> (x \<odot>\<^bsub>i\<^esub> z)" (* irredundant *)
  and sj_hom: "i < j \<Longrightarrow> Srci j (x \<odot>\<^bsub>i\<^esub> y) \<subseteq> src j x \<odot>\<^bsub>i\<^esub> src j y"  (* irredundant *)
  and tj_hom: "i < j \<Longrightarrow> Tgti j (x \<odot>\<^bsub>i\<^esub> y) \<subseteq> tgt j x \<odot>\<^bsub>i\<^esub> tgt j y" (* irredundant *)

begin

lemma sitjsi: 
  assumes "i < j"
  shows "src i (tgt j (src i x)) = src i x"
  by (metis (no_types, lifting) SUP_empty assms local.iconv_prop local.interchange local.src_absorb local.stimm.stopp.conv_atom local.stimm.stopp.conv_def local.tgt_absorb order_less_imp_le stimm.s_absorb_var3 subset_empty)

lemma tisjsi: "i < j \<Longrightarrow> tgt i (src j (src i x)) = src i x"
  by (smt (verit, ccfv_SIG) image_is_empty local.sitjsi local.sj_hom local.stimm.stopp.Dst local.stimm.stopp.st_ortho_iff stimm.s_absorb_var subset_empty)

lemma sjsi: 
  assumes "i < j"
  shows "src j (src i x) = src i x"
  by (smt (verit, ccfv_SIG) assms empty_iff insert_iff insert_subset less_or_eq_imp_le local.iconv_prop local.interchange local.sitjsi local.src_absorb local.stimm.stopp.conv_atom local.stimm.stopp.s_absorb_var2 local.tgt_absorb local.tisjsi stimm.s_ortho_iff)
 
lemma sjti: "i < j \<Longrightarrow> src j (tgt i x) = tgt i x"
  by (metis local.sjsi local.stimm.stopp.ts_compat)

lemma tjsi: "i < j \<Longrightarrow> tgt j (src i x) = src i x"
  by (simp add: local.sjsi stimm.st_fix)

lemma tjti: "i < j \<Longrightarrow> tgt j  (tgt i x) = tgt i x"
  by (simp add: local.sjti stimm.st_fix)

lemma comm_sisj: "i < j \<Longrightarrow> src i (src j x) = src j (src i x)"
  by (metis (no_types, opaque_lifting) empty_iff image_insert insert_subset local.sj_hom local.sjsi local.src_absorb local.stimm.stopp.Dst stimm.ts_compat)

lemma comm_sitj: "i < j \<Longrightarrow> src i (tgt j x) = tgt j (src i x)"
  by (metis empty_iff image_insert insert_subset local.src_absorb local.tj_hom local.tjsi stimm.s_absorb_var2)

lemma comm_tisj: "i < j \<Longrightarrow> tgt i (src j x) = src j (tgt i x)"
  by (metis empty_iff image_insert insert_subset local.sj_hom local.sjti local.stimm.stopp.s_absorb_var3 local.tgt_absorb)

lemma comm_titj: "i < j \<Longrightarrow> tgt i (tgt j x) = tgt j (tgt i x)"
  by (smt (verit) bot.extremum_uniqueI local.sjti local.stimm.stopp.s_absorb_var local.stimm.stopp.s_export local.tgt_absorb local.tj_hom stimm.st_fix)

lemma si_hom: "i < j \<Longrightarrow> Srci i  (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> src i x \<odot>\<^bsub>j\<^esub> src i y"
  by (smt (verit, del_insts) icat.tgt_comp_aux image_subset_iff local.comm_sisj local.comm_sitj local.icat.ts_msg.src_twisted_aux local.src_absorb local.stimm.stopp.Dst local.tjsi singletonI)

lemma ti_hom: "i < j \<Longrightarrow> Tgti i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> tgt i x \<odot>\<^bsub>j\<^esub> tgt i y"
  by (smt (verit, ccfv_SIG) comm_tisj icat.tgt_comp_aux image_subset_iff local.comm_titj local.stimm.stopp.Dst local.tgt_absorb local.tjti singletonI)

end 

class omega_catoid_red_strong = icatoid +
  assumes interchange: "i < j \<Longrightarrow> (w \<odot>\<^bsub>j\<^esub> x) \<star>\<^bsub>i\<^esub> (y \<odot>\<^bsub>j\<^esub> z) \<subseteq> (w \<odot>\<^bsub>i\<^esub> y) \<star>\<^bsub>j\<^esub> (x \<odot>\<^bsub>i\<^esub> z)" (* irredundant *)
  and sj_hom_strong: "i \<le> j \<Longrightarrow> Srci j (x \<odot>\<^bsub>i\<^esub>y) = src j x \<odot>\<^bsub>i\<^esub> src j y"  (* irredundant *)
  and tj_hom_strong: "i \<le> j \<Longrightarrow> Tgti j (x \<odot>\<^bsub>i\<^esub> y) = tgt j x \<odot>\<^bsub>i\<^esub> tgt j y" (* irredundant *)

begin

lemma sitjsi: "i < j \<Longrightarrow> src i (tgt j (src i x)) = src i x"
  by (metis UN_empty Union_empty dual_order.strict_iff_not local.src_absorb local.stimm.stopp.s_ortho_id local.tj_hom_strong stimm.Tgt_Sup_pres stimm.s_absorb_var stimm.s_ortho_id stimm.t_export stimm.tt_idem)

lemma tisjsi: "i < j \<Longrightarrow> tgt i (src j (src i x)) = src i x"
  by (metis image_empty less_or_eq_imp_le local.sj_hom_strong local.stimm.stopp.Dst local.stimm.stopp.s_absorb_var2 stimm.ts_compat)

lemma sjsi: 
  assumes "i < j"
  shows "src j (src i x) = src i x"
proof-
  have "{src i x} = src i x \<odot>\<^bsub>i\<^esub> src i x"
    by simp
  also have "\<dots> = (src j (src i x) \<odot>\<^bsub>j\<^esub> src i x) \<star>\<^bsub>i\<^esub> (src i x \<odot>\<^bsub>j\<^esub> tgt j (src i x))"
    by (simp add: local.iconv_prop)
  also have "\<dots> \<subseteq> (src j (src i x) \<odot>\<^bsub>i\<^esub> src i x) \<star>\<^bsub>j\<^esub> (src i x \<odot>\<^bsub>i\<^esub> tgt j (src i x))"
    by (meson assms local.interchange)
  also have "\<dots> = (src j (src i x) \<odot>\<^bsub>i\<^esub> tgt i (src j (src i x))) \<star>\<^bsub>j\<^esub> (src i (tgt j (src i x)) \<odot>\<^bsub>i\<^esub> tgt j (src i x))"
    by (simp add: assms local.sitjsi local.tisjsi)
  also have "\<dots> = src j (src i x) \<odot>\<^bsub>j\<^esub> tgt j (src i x)"
    using local.iconv_prop by simp
  finally have "{src i x} \<subseteq> src j (src i x) \<odot>\<^bsub>j\<^esub> tgt j (src i x)".
  thus ?thesis
    using local.stimm.stopp.Dst by force
qed
 
lemma sjti: "i < j \<Longrightarrow> src j (tgt i x) = tgt i x"
  by (metis local.sjsi local.stimm.stopp.ts_compat)

lemma tjsi: "i < j \<Longrightarrow> tgt j (src i x) = src i x"
  using local.sjsi stimm.st_fix by blast

lemma tjti: "i < j \<Longrightarrow> tgt j (tgt i x) = tgt i x"
  by (simp add: local.sjti stimm.st_fix)

lemma comm_sisj: "i < j \<Longrightarrow> src i (src j x) = src j (src i x)"
  by (smt (verit) less_or_eq_imp_le local.sj_hom_strong local.sjsi local.src_absorb stimm.s_absorb_var3)

lemma comm_sitj: "i < j \<Longrightarrow> src i (tgt j x) = tgt j (src i x)"
  by (metis local.tj_hom_strong local.tjsi order.strict_iff_not stimm.s_absorb_var2)

lemma comm_tisj: "i < j \<Longrightarrow> tgt i (src j x) = src j (tgt i x)"
  by (metis dual_order.strict_implies_order local.sj_hom_strong local.sjti local.stimm.stopp.s_absorb_var)

lemma comm_titj: "i < j \<Longrightarrow> tgt i (tgt j x) = tgt j (tgt i x)"
  by (metis image_empty less_or_eq_imp_le local.comm_sitj local.sj_hom_strong local.stimm.stopp.Dst stimm.s_ortho_iff)

lemma s0_weak_hom: "i < j \<Longrightarrow> Srci i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> src i x \<odot>\<^bsub>j\<^esub> src i y"
  by (smt (verit, best) image_subsetI insertI1 local.comm_sisj local.comm_sitj local.icat.ts_msg.tgt_comp_aux local.sjsi local.src_absorb local.stimm.stopp.Dst local.tjsi)

lemma t0_weak_hom: "i < j \<Longrightarrow> Tgti i (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> tgt i x \<odot>\<^bsub>j\<^esub> tgt i y"
  by (smt (verit, ccfv_SIG) icat.tgt_comp_aux image_subset_iff local.comm_tisj local.comm_titj local.sjsi local.stimm.stopp.Dst local.stimm.stopp.ts_compat local.tgt_absorb singletonI stimm.ts_compat)

end

end






