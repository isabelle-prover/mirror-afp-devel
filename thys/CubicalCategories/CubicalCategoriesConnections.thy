(*
Title: Cubical Categories with Connections
Authors: Tanguy Massacrier, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section\<open>Cubical Categories with Connections\<close>

theory CubicalCategoriesConnections
  imports CubicalCategories

begin

text \<open>All categories considered in this component are single-set categories.\<close>

class connection_ops = 
  fixes connection :: "nat \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Gamma>")

abbreviation (in connection_ops) "\<Gamma>\<Gamma> i \<alpha> \<equiv> image (\<Gamma> i \<alpha>)"

text \<open>We define a class for cubical $\omega$-categories with connections.\<close>

class cubical_omega_category_connections = cubical_omega_category + connection_ops +
  assumes conn_face1: "fFx j x \<Longrightarrow> \<partial> j \<alpha> (\<Gamma> j \<alpha> x) = x"
  and conn_face2: "fFx j x \<Longrightarrow> \<partial> (j + 1) \<alpha> (\<Gamma> j \<alpha> x) = \<sigma> j x"
  and conn_face3: "i \<noteq> j \<Longrightarrow> i \<noteq> j + 1 \<Longrightarrow> fFx j x \<Longrightarrow> \<partial> i \<alpha> (\<Gamma> j \<beta> x) = \<Gamma> j \<beta> (\<partial> i \<alpha> x)"
  and conn_corner1: "fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD (i + 1) x y \<Longrightarrow> \<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)" 
  and conn_corner2: "fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD (i + 1) x y \<Longrightarrow> \<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) \<otimes>\<^bsub>i\<^esub> (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y)"
  and conn_corner3: "j \<noteq> i \<and> j \<noteq> i + 1 \<Longrightarrow> fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD j x y \<Longrightarrow> \<Gamma> i \<alpha> (x \<otimes>\<^bsub>j\<^esub> y) = \<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y"
  and conn_fix: "fFx i x \<Longrightarrow> fFx (i + 1) x \<Longrightarrow> \<Gamma> i \<alpha> x = x"
  and conn_zigzag1: "fFx i x \<Longrightarrow> \<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff x = x"
  and conn_zigzag2: "fFx i x \<Longrightarrow> \<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff x = \<sigma> i x"
  and conn_conn_braid: "diffSup i j 2 \<Longrightarrow> fFx j x \<Longrightarrow> fFx i x \<Longrightarrow> \<Gamma> i \<alpha> (\<Gamma> j \<beta> x) = \<Gamma> j \<beta> (\<Gamma> i \<alpha> x)"
  and conn_shift: "fFx i x \<Longrightarrow> fFx (i + 1) x \<Longrightarrow> \<sigma> (i + 1) (\<sigma> i (\<Gamma> (i + 1) \<alpha> x)) = \<Gamma> i \<alpha> (\<sigma> (i + 1) x)"

begin 

lemma conn_face4: "fFx j x \<Longrightarrow> \<partial> j \<alpha> (\<Gamma> j (\<not>\<alpha>) x) = \<partial> (j + 1) \<alpha> x"
  by (smt (z3) local.conn_face1 local.conn_zigzag2 local.face_comm_var local.locality local.pcomp_lface local.pcomp_uface local.sym_face1 local.sym_fix_var1)

lemma conn_face1_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> j \<alpha> (\<Gamma>\<Gamma> j \<alpha> X) = X"
  by (auto simp add: image_iff local.conn_face1)

lemma conn_face4_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> j \<alpha> (\<Gamma>\<Gamma> j (\<not>\<alpha>) X) = \<partial>\<partial> (j + 1) \<alpha> X"
  apply safe
  apply (simp add: local.conn_face4)
  by (metis image_eqI local.conn_face4)

lemma conn_face2_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> (j + 1) \<alpha> (\<Gamma>\<Gamma> j \<alpha> X) = \<sigma>\<sigma> j X"
  by (smt (z3) comp_apply image_comp image_cong local.conn_face2)

lemma conn_face3_lift: "i \<noteq> j \<Longrightarrow> i \<noteq> j + 1 \<Longrightarrow> FFx j X \<Longrightarrow> \<partial>\<partial> i \<alpha> (\<Gamma>\<Gamma> j \<beta> X) = \<Gamma>\<Gamma> j \<beta> (\<partial>\<partial> i \<alpha> X)"
  by (smt (z3) image_cong image_image local.conn_face3)

lemma conn_fix_lift: "FFx i X \<Longrightarrow> FFx (i + 1) X \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> X = X"
  by (simp add: local.conn_fix)

lemma conn_conn_braid_lift: 
  assumes "diffSup i j 2" 
  and "FFx j X" 
  and "FFx i X"
  shows "\<Gamma>\<Gamma> i \<alpha> (\<Gamma>\<Gamma> j \<beta> X) = \<Gamma>\<Gamma> j \<beta> (\<Gamma>\<Gamma> i \<alpha> X)"
  by (smt (z3) assms image_cong image_image local.conn_conn_braid)

lemma conn_sym_braid: 
  assumes "diffSup i j 2"
  and "fFx i x"
  and "fFx j x"
  shows "\<Gamma> i \<alpha> (\<sigma> j x) = \<sigma> j (\<Gamma> i \<alpha> x)"
  by (smt (z3) assms add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' icat.st_local le_add1 local.conn_conn_braid local.conn_corner3 local.conn_face1 local.conn_face3 local.conn_zigzag2 numeral_le_one_iff rel_simps(28) semiring_norm(69))

lemma conn_zigzag1_var [simp]: "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<partial> i \<alpha> x}"
proof (cases "DD (i + 1) (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<Gamma> i ff (\<partial> i \<alpha> x))")
  case True
  hence "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x)}"
    by (metis True local.icat.pcomp_def_var4)
  also have "\<dots> = {\<partial> i \<alpha> x}"
    using local.conn_zigzag1 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    using local.conn_face2 local.locality by simp 
qed

lemma conn_zigzag1_lift:
  assumes "FFx i X"
  shows "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff X = X"
proof-
  have "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff X = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> DD (i + 1) (\<Gamma> i tt x) (\<Gamma> i ff y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<partial> (i + 1) tt (\<Gamma> i tt x) = \<partial> (i + 1) ff (\<Gamma> i ff y)}"
    using icat.st_local by presburger
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<sigma> i x = \<sigma> i y}"
    by (metis (no_types, lifting) assms local.conn_face2)
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff x | x. x \<in> X}"
    using assms local.sym_inj_var by blast
  also have "\<dots> = {\<Gamma> i tt (\<partial> i tt x) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i tt x) | x. x \<in> X}"
    by (metis (full_types) assms icid.ts_compat)
  also have "\<dots> = {\<partial> i tt x | x. x \<in> X}"
    using local.conn_zigzag1 local.face_compat_var by presburger
  also have "\<dots> = X"
    by (smt (verit, del_insts) Collect_cong Collect_mem_eq assms local.icid.stopp.st_fix)
  finally show ?thesis.
qed

lemma conn_zigzag2_var: "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<sigma> i (\<partial> i \<alpha> x)}"
proof (cases "DD i (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<Gamma> i ff (\<partial> i \<alpha> x))")
  case True
  hence "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x)}"
    by (metis True local.icat.pcomp_def_var4)
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x)}"
    using local.conn_zigzag2 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (simp add: local.conn_face1 local.locality)
qed

lemma conn_zigzag2_lift:
  assumes "FFx i X"
  shows "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>i\<^esub> \<Gamma>\<Gamma> i ff X = \<sigma>\<sigma> i X"
proof-
  have "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>i\<^esub> \<Gamma>\<Gamma> i ff X = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> DD i (\<Gamma> i tt x) (\<Gamma> i ff y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<partial> i tt (\<Gamma> i tt x) = \<partial> i ff (\<Gamma> i ff y)}"
    using icat.st_local by presburger
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff x | x. x \<in> X}"
    by (metis (full_types) assms local.conn_face1)
  also have "\<dots> = {\<Gamma> i tt (\<partial> i tt x) \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i tt x) | x. x \<in> X}"
    by (metis (full_types) assms icid.ts_compat)
  also have "\<dots> = {\<sigma> i x | x. x \<in> X}"
    by (metis assms icid.ts_compat local.conn_zigzag2)
  also have "\<dots> = \<sigma>\<sigma> i X"
    by force
  finally show ?thesis.
qed

lemma conn_sym_braid_lift: "diffSup i j 2 \<Longrightarrow> FFx i X \<Longrightarrow> FFx j X \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> (\<sigma>\<sigma> j X) = \<sigma>\<sigma> j (\<Gamma>\<Gamma> i \<alpha> X)"
  by (smt (z3) image_cong image_image local.conn_sym_braid)

lemma conn_corner1_DD:
  assumes "fFx i x"
  and "fFx i y"
  and "DD (i + 1) x y"
  shows "DD i (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)"
proof-
  have h1: "DD (i + 1) (\<Gamma> i tt x) (\<sigma> i x)"
    using assms(1) local.conn_face2 local.locality local.sym_type_var by simp
  have h2: "DD (i + 1) x (\<Gamma> i tt y)"
    by (metis assms(2) assms(3) conn_zigzag1_var icat.st_local icid.src_comp_aux singleton_iff)
  have h3: "\<partial> i tt (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) = x"
    by (metis assms(1) local.conn_face1 local.conn_face2 local.icat.sscatml.r0_absorb)
  have "\<partial> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<partial> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)"
    using h2 local.face_func by simp
  hence h4: "\<partial> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y"
    by (metis (full_types) assms(1) assms(2) local.conn_face4)
  have "\<partial> i tt (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) = \<partial> i tt (\<Gamma> i tt x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i x)"
    using h1 local.face_func by simp
  also have "\<dots> = x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) tt x"
    using calculation h3 by simp
  thus ?thesis
    using assms(3) h3 h4 local.icat.sts_msg.st_local by simp
qed

lemma conn_corner1_var: "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<star>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "DD (i + 1) (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<sigma> i (\<partial> i \<alpha> x))"
    by (metis local.conn_face2 local.face_compat_var local.locality)
  have h2: "DD (i + 1) (\<partial> i \<alpha> x) (\<Gamma> i tt (\<partial> i \<beta> y))"
    by (metis True icid.src_comp_aux insertCI local.conn_zigzag1_var local.iDst local.locality)
  have h3: "DD i (\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
    using True local.conn_corner1_DD local.face_compat_var by simp
  have "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = \<Gamma>\<Gamma> i tt {\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y}"
    using True local.icat.pcomp_def_var4 by simp
  also have "\<dots> = {(\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<otimes>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))}"
    using True local.conn_corner1 local.face_compat_var by simp
  also have "\<dots> = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)} \<star>\<^bsub>i\<^esub> {\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)}"
    using h3 local.icat.pcomp_def_var4 local.icid.stopp.conv_atom by simp
  also have "\<dots> = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<star>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
    using h1 h2 local.icat.pcomp_def_var4 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (smt (z3) Union_empty empty_is_image icat.st_local icid.ts_compat local.conn_face4 local.face_comm_var local.icid.stopp.ts_compat multimagma.conv_distl)
qed

lemma conn_corner1_lift_aux: "fFx i x \<Longrightarrow> \<partial> (i + 1) ff (\<Gamma> i tt x) = \<partial> (i + 1) ff x"
  by (metis conn_zigzag1_var empty_not_insert equals0I icid.src_comp_aux singletonD)

lemma conn_corner1_lift:
  assumes "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i tt (X \<star>\<^bsub>(i + 1)\<^esub> Y) = (\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<sigma>\<sigma> i X) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i tt Y)"
proof-
  have h1: "\<forall>y \<in> Y. \<partial> (i + 1) ff (\<Gamma> i tt y) = \<partial> (i + 1) ff y"
    by (metis assms(2) conn_zigzag1_var local.icid.ts_msg.tgt_comp_aux singletonI)
  have h2 :"\<forall>xa \<in> X. DD (i + 1) (\<Gamma> i tt xa) (\<sigma> i xa) \<longrightarrow> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) = \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa)"
    by (simp add: local.face_func)
  have h3 :"\<forall>xc \<in> X. \<forall>y \<in> Y. DD (i + 1) xc (\<Gamma> i tt y) \<longrightarrow> \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)"
    by (simp add: local.face_func)
  have h4: "\<forall>xa \<in> X. \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa) = xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa)"
    by (smt (z3) assms(1) local.conn_face1 local.fFx_prop local.face_comm_var local.sym_face1_var1 local.sym_fix_var1)
  have h5: "\<forall>xc \<in> X. \<forall>y \<in> Y. \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y) = xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y"
    by (metis (full_types) assms(1) assms(2) local.conn_face4)
  have h6: "\<forall>xc \<in> X. \<forall>y \<in> Y. DD (i + 1) xc (\<partial> (i + 1) ff y) \<longrightarrow> xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y = xc"
    by (metis local.face_compat_var local.icat.sscatml.r0_absorb local.icid.stopp.Dst)
  have h7: "\<forall>xa \<in> X. xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa) = xa"
    by (metis assms(1) local.face_comm_var local.face_compat_var local.icat.sscatml.r0_absorb)
  have h8: "\<forall>x \<in> X. \<forall>y \<in> Y. DD (i + 1) x y \<longrightarrow> (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y)"
    using assms(1) assms(2) local.conn_corner1 by auto
  have "(\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<sigma>\<sigma> i X) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i tt Y) = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> DD (i + 1) (\<Gamma> i tt xa) (\<sigma> i xb) \<and> DD (i + 1) xc (\<Gamma> i tt y) \<and> DD i (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    unfolding local.iconv_prop by blast
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt (\<Gamma> i tt xa) = \<partial> (i + 1) ff (\<sigma> i xb) \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff (\<Gamma> i tt y) \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    using icat.st_local by presburger
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> xa = xb \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff (\<Gamma> i tt y) \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    by (smt (verit) Collect_cong assms(1) local.conn_face2 local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    by (smt (verit, best) Collect_cong assms(1) h1 local.conn_face3 local.locality local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa) = \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)}"
    by (smt (verit, del_insts) h2 h3 Collect_cong assms(1) h1 icat.st_local local.conn_face2 local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa) = xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y}"
    by (smt (verit, del_insts) h4 h5 Collect_cong)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> xa = xc}"
    by (smt (z3) h6 h7 Collect_cong assms(2) icid.st_eq1 local.face_comm_var)
  also have "\<dots> = {\<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD (i + 1) x y}"
    by (smt (verit, ccfv_threshold) h8 Collect_cong icat.st_local)
  also have "\<dots> = \<Gamma>\<Gamma> i tt (X \<star>\<^bsub>(i + 1)\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_corner2_DD:
  assumes "fFx i x"
  and "fFx i y"
  and "DD (i + 1) x y"
  shows "DD i (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y)"
proof-
  have h1: "DD (i + 1) (\<Gamma> i ff x) y"
    by (metis assms(1) assms(3) conn_zigzag1_var insertCI local.iDst local.icid.ts_msg.src_comp_aux local.locality)
  have h2: "\<partial> i ff (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y) = \<partial> i ff (\<sigma> i y) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff y)"
    using assms(2) local.conn_face2 local.face_func local.locality local.sym_face3_simp by auto
  have "\<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt y"
    using h1 local.face_func by simp
  hence h4: "\<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<partial> (i + 1) tt x \<otimes>\<^bsub>(i + 1)\<^esub> y"
    by (metis (full_types) assms(1) assms(2) icid.st_eq1 local.conn_face4)
  thus ?thesis
    by (metis h2 assms(2) assms(3) local.conn_face1 local.conn_face2 local.face_comm_var local.icid.stopp.Dst local.locality)
qed

lemma conn_corner2_var: "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) \<star>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "DD (i + 1) (\<Gamma> i ff (\<partial> i \<alpha> x)) (\<partial> i \<beta> y)"
    by (metis True insertCI local.conn_zigzag1_var local.iDst local.icid.ts_msg.src_comp_aux local.locality)
  have h2: "DD (i + 1) (\<sigma> i (\<partial> i \<beta> y)) (\<Gamma> i ff (\<partial> i \<beta> y))"
    by (metis local.conn_face2 local.face_compat_var local.locality)
  have h3: "DD i (\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) (\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
    using True local.conn_corner2_DD by simp
  have "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = {\<Gamma> i ff (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y)}"
    by (metis (full_types) True local.icat.pcomp_def_var4 image_empty image_insert) 
  also have "\<dots> = {(\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<otimes>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))}"
    using True conn_corner2 local.face_compat_var by simp
 also have "\<dots> = {\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)} \<star>\<^bsub>i\<^esub> {\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)}"
   using h3 local.icat.pcomp_def_var4 local.icid.stopp.conv_atom by simp
  also have "\<dots> = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<star>\<^bsub>i\<^esub> {\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)}"
    by (metis h1 local.icat.functionality_lem_var local.icat.pcomp_def local.icat.sscatml.r0_absorb local.it_absorb)
  also have "\<dots> = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<star>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
    using h2 local.icat.pcomp_def_var4 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (metis UN_empty add_eq_self_zero empty_is_image local.conn_face1 local.face_compat_var local.pcomp_face_func_DD multimagma.conv_def nat_neq_iff zero_less_one)
qed

lemma conn_corner2_lift:
  assumes "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i ff (X \<star>\<^bsub>(i + 1)\<^esub> Y) = (\<Gamma>\<Gamma> i ff X \<star>\<^bsub>(i + 1)\<^esub> Y) \<star>\<^bsub>i\<^esub> (\<sigma>\<sigma> i Y \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff Y)"
proof-
  have h1 :"\<forall>x \<in> X. \<forall>ya \<in> Y. \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<longrightarrow> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya"
    by (metis local.face_func add.commute add_diff_cancel_right' assms(1) bot_nat_0.extremum_unique cancel_comm_monoid_add_class.diff_cancel conn_zigzag1_var empty_not_insert ex_in_conv icat.st_local local.icid.ts_msg.src_comp_aux not_one_le_zero singletonD)
  have h2 :"\<forall>yb \<in> Y. DD (i + 1) (\<sigma> i yb) (\<Gamma> i ff yb) \<longrightarrow> \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb)"
    by (simp add: local.face_func)
  have h3: "\<forall>x \<in> X. \<forall>y \<in> Y. DD (i + 1) x y \<longrightarrow> (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) \<otimes>\<^bsub>i\<^esub> (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y) = \<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y)"
    using assms local.conn_corner2 by simp
  have h4: "\<forall>x \<in> X. \<forall>ya \<in> Y. (\<partial> (i + 1) tt (\<Gamma> i ff x) = \<partial> (i + 1) ff ya) = (\<partial> (i + 1) tt x = \<partial> (i + 1) ff ya)"
    by (metis assms(1) conn_zigzag1_var local.icid.ts_msg.src_comp_aux singletonI)
  have h5: "\<forall>yb \<in> Y. \<forall>yc \<in> Y. (\<partial> (i + 1) tt (\<sigma> i yb) = \<partial> (i + 1) ff (\<Gamma> i ff yc)) = (yb = yc)"
    by (metis assms(2) local.conn_face2 local.inv_sym_sym local.sym_face3_simp)
  have h6: "\<forall>x \<in> X. \<forall>ya \<in> Y. \<forall>yb \<in> Y. (x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb)) = (x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb))"
    using h1 h2 h5 icat.st_local by force
  have "(\<Gamma>\<Gamma> i ff X \<star>\<^bsub>(i + 1)\<^esub> Y) \<star>\<^bsub>i\<^esub> (\<sigma>\<sigma> i Y \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff Y) = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc) | x ya yb yc. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> yc \<in> Y \<and> DD (i + 1) (\<Gamma> i ff x) ya \<and> DD (i + 1) (\<sigma> i yb) (\<Gamma> i ff yc) \<and> DD i (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc)}"
    unfolding local.iconv_prop by fastforce
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc) | x ya yb yc. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> yc \<in> Y \<and> \<partial> (i + 1) tt (\<Gamma> i ff x) = \<partial> (i + 1) ff ya \<and> \<partial> (i + 1) tt (\<sigma> i yb) = \<partial> (i + 1) ff (\<Gamma> i ff yc) \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc)}"
    using icat.st_local by simp
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb)}"
    using h4 h5 by (smt (verit, del_insts) Collect_cong)
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb)}"
    using h6 by fastforce
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> (i + 1) tt x \<otimes>\<^bsub>(i + 1)\<^esub> ya = \<partial> (i + 1) ff yb \<otimes>\<^bsub>(i + 1)\<^esub> yb}"
    by (smt (z3) Collect_cong assms(1) assms(2) icid.st_eq1 local.conn_face1 local.conn_face4 local.conn_face2 local.face_comm_var)
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> ya = yb}"
    by force
  also have "\<dots> = {\<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD (i + 1) x y}"
    by (smt (verit, ccfv_threshold) h3 Collect_cong icat.st_local)
  also have "\<dots> = \<Gamma>\<Gamma> i ff (X \<star>\<^bsub>(i + 1)\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_corner3_var: 
  assumes "j \<noteq> i \<and> j \<noteq> i + 1"
  shows "\<Gamma>\<Gamma> i \<alpha> (\<partial> i \<beta> x \<odot>\<^bsub>j\<^esub> \<partial> i \<gamma> y) = \<Gamma> i \<alpha> (\<partial> i \<beta> x) \<odot>\<^bsub>j\<^esub> \<Gamma> i \<alpha> (\<partial> i \<gamma> y)"
  by (smt (z3) assms empty_is_image image_insert local.conn_corner3 local.conn_face1 local.conn_face3 local.face_compat_var local.iDst local.icat.pcomp_def_var4 local.locality local.pcomp_face_func_DD)

lemma conn_corner3_lift:
  assumes "j \<noteq> i"
  and "j \<noteq> i + 1"
  and "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i \<alpha> (X \<star>\<^bsub>j\<^esub> Y) = \<Gamma>\<Gamma> i \<alpha> X \<star>\<^bsub>j\<^esub> \<Gamma>\<Gamma> i \<alpha> Y"
proof-
  have h: "\<forall>x \<in> X. \<forall>y \<in> Y. DD j (\<Gamma> i \<alpha> x) (\<Gamma> i \<alpha> y) = DD j x y"
    by (metis assms icat.st_local local.conn_face1 local.conn_face3 local.face_comm_var)
  have "\<Gamma>\<Gamma> i \<alpha> X \<star>\<^bsub>j\<^esub> \<Gamma>\<Gamma> i \<alpha> Y = {\<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y | x y. x \<in> X \<and> y \<in> Y \<and> DD j (\<Gamma> i \<alpha> x) (\<Gamma> i \<alpha> y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y | x y. x \<in> X \<and> y \<in> Y \<and> DD j x y}"
    using h by force
  also have "\<dots> = {\<Gamma> i \<alpha> (x \<otimes>\<^bsub>j\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD j x y}"
    using conn_corner3 assms by fastforce
  also have "\<dots> = \<Gamma>\<Gamma> i \<alpha> (X \<star>\<^bsub>j\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_face5 [simp]: "\<partial> (j + 1) \<alpha> (\<Gamma> j (\<not>\<alpha>) (\<partial> j \<gamma> x)) = \<partial> (j + 1) \<alpha> (\<partial> j \<gamma> x)"
  by (smt (verit, ccfv_SIG) icid.s_absorb_var local.conn_corner1_lift_aux local.conn_zigzag1_var local.face_compat_var local.icid.ts_msg.src_comp_cond local.is_absorb singleton_insert_inj_eq')

lemma conn_inv_sym_braid:
  assumes "diffSup i j 2"
  shows "\<Gamma> i \<alpha> (\<theta> j (\<partial> i \<beta> (\<partial> (j + 1) \<gamma> x))) = \<theta> j (\<Gamma> i \<alpha> (\<partial> i \<beta> (\<partial> (j + 1) \<gamma> x)))"
  by (smt (z3) add_diff_cancel_left' assms diff_add_0 diff_is_0_eq' local.conn_face3 local.conn_sym_braid local.face_comm_var local.face_compat_var local.inv_sym_face2 local.inv_sym_sym_var1 local.inv_sym_type_var local.sym_inv_sym nat_1_add_1 nle_le rel_simps(28))

lemma conn_corner4: "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) \<star>\<^bsub>(i + 1)\<^esub> (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "\<partial>\<partial> (i+1) tt (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) = {\<sigma> i (\<partial> i \<alpha> x)}"
    by (metis image_empty image_insert local.conn_face1 local.conn_face2 local.face_compat_var local.it_absorb)
  have "\<partial> (i+1) tt (\<partial> i \<alpha> x) = \<partial> (i+1) ff (\<partial> i \<beta> y)"
    using True local.iDst by simp
  hence h2: "\<partial>\<partial> (i+1) ff (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<alpha> x)}"
    by (smt (z3) add_eq_self_zero conn_face4 conn_face5 icat.st_local image_is_empty local.comp_face_func local.conn_face2 local.face_comm_var local.face_compat_var local.it_absorb subset_singletonD zero_neq_one)
  hence "\<partial>\<partial> (i+1) tt (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) \<inter> \<partial>\<partial> (i+1) ff (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)) \<noteq> {}"
    using h1 by simp
  thus ?thesis
    by (smt (z3) True add_cancel_right_right dual_order.eq_iff empty_is_image h1 h2 icat.locality_lifting local.conn_corner1_var local.icat.pcomp_def_var4 local.interchange_var multimagma.conv_atom not_one_le_zero)
next
  case False
  thus ?thesis
    by (smt (z3) Union_empty add_eq_self_zero dual_order.eq_iff icat.st_local image_empty local.conn_face4 local.conn_face2 local.face_comm_var local.face_compat_var multimagma.conv_distl not_one_le_zero)
qed

lemma conn_corner5: "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) \<star>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "\<partial>\<partial> (i+1) ff (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<beta> y)}"
    by (metis image_empty image_insert local.conn_face1 local.conn_face2 local.face_compat_var local.is_absorb)
  have "\<partial> (i+1) tt (\<partial> i \<alpha> x) = \<partial> (i+1) ff (\<partial> i \<beta> y)"
    using True local.iDst by simp
  hence h2: "\<partial>\<partial> (i+1) tt (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<beta> y)}"
    by (smt (z3) conn_face4 conn_face5 h1 icat.st_local image_insert image_is_empty local.comp_face_func local.conn_face2 local.face_comm_var local.face_compat_var local.icat.functionality_lem_var local.it_absorb subset_singletonD)
  hence "\<partial>\<partial> (i+1) ff (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)) \<inter> \<partial>\<partial> (i+1) tt (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) \<noteq> {}"
    using h1 by simp
  thus ?thesis
    by (smt (z3) True add_cancel_right_right dual_order.eq_iff empty_is_image h1 h2 icat.locality_lifting local.conn_corner2_var local.icat.functionality_lem_var local.interchange_var multimagma.conv_atom not_one_le_zero)
next
  case False
  thus ?thesis
    by (smt (z3) UN_empty add_cancel_right_right dual_order.eq_iff image_empty local.conn_face2 local.face_compat_var local.pcomp_face_func_DD local.sym_func2_DD local.sym_type_var multimagma.conv_def not_one_le_zero)
qed

lemma conn_corner3_alt: "j \<noteq> i \<Longrightarrow>  j \<noteq> i + 1 \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> (\<partial> i \<beta> x \<odot>\<^bsub>j\<^esub> \<partial> i \<gamma> y) = \<Gamma> i \<alpha> (\<partial> i \<beta> x) \<odot>\<^bsub>j\<^esub> \<Gamma> i \<alpha> (\<partial> i \<gamma> y)"
  by (simp add: local.conn_corner3_var)

lemma conn_shift2:
  assumes "fFx i x"
  and "fFx (i + 2) x"
shows "\<theta> i (\<theta> (i + 1) (\<Gamma> i \<alpha> x)) = \<Gamma> (i + 1) \<alpha> (\<theta> (i + 1) x)"

proof-
  have "\<Gamma> i \<alpha> x = \<sigma> (i + 1) (\<sigma> i (\<Gamma> (i + 1) \<alpha> (\<theta> (i + 1) x)))"
    using assms local.conn_shift local.inv_sym_face2 local.inv_sym_face3_simp local.sym_inv_sym by simp
  thus ?thesis
    using assms local.conn_face3 local.inv_sym_face2 local.inv_sym_sym local.inv_sym_type_var local.sym_type_var by simp
qed

end

end