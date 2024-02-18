(* 
Title: Eckmann-Hilton Collapse for 2-Catoids
Author: Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>2-Catoids with (too) strong homomorphisms\<close>

theory Two_Catoid_Collapse
  imports Two_Catoid

begin

text \<open>Here we present  variants of 2-categories where the axioms are too strong. There is an Eckmann-Hilton
style collapse of the two structures.\<close>


subsection \<open>2-st-Multimagmas with strong homomorphism laws\<close>

class two_st_multimagma_collapse = st_multimagma0 + st_multimagma1 +
  assumes comm_s0s1: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and comm_t0t1: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  and comm_s0t1: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and commtr0s1: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
  assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) \<subseteq> (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)"
  and t0_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) = \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"  (* this is too strong *)
  and t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) = \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y"
  and s0_hom: "Src\<^sub>0 (x \<odot>\<^sub>1 y) = \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y" (* this is too strong *)
  and s1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) = \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y" 
  and s1_s0 [simp]: "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x" 
  and t1_s0 [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"  
  and s1_t0 [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x" 
  and t1_t0 [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x" 

begin

text \<open>The source and target structure collapses.\<close>

lemma s0s1: "\<sigma>\<^sub>0 x = \<sigma>\<^sub>1 x"
proof-
  have "Src\<^sub>0 (\<sigma>\<^sub>1 x \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)) = \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x))"
    by (simp add: local.s0_hom)
  also have "\<dots>  = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)) \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)"
    by simp
  also have "\<dots> = {\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)}"
    using local.src1_absorb by presburger
  also have "\<dots> \<noteq> {}" 
   by (metis insert_not_empty)
  finally have "Src\<^sub>0 (\<sigma>\<^sub>1 x \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x)) \<noteq> {}".
  hence "\<sigma>\<^sub>1 x \<odot>\<^sub>1 \<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) \<noteq> {}" 
    by (metis image_empty) 
  hence "\<tau>\<^sub>1 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x))"
    using local.Dst1 by presburger
  hence "\<sigma>\<^sub>1 x = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x))"
    by simp
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x))"
    by (simp add: local.comm_s0s1)
  also have "\<dots> = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<sigma>\<^sub>0 x"
    by simp
  finally show ?thesis..
qed

lemma t0t1: "\<tau>\<^sub>0 x = \<tau>\<^sub>1 x"
  using local.comm_s0t1 local.commtr0s1 local.s0s1 stmm0.ts_compat by force

lemma s0t0: "\<sigma>\<^sub>0 x = \<tau>\<^sub>0 x"
proof-
  have "\<sigma>\<^sub>0 x = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"
    by (simp add: local.comm_s0t1)
  also have "\<dots> = \<sigma>\<^sub>0 (\<tau>\<^sub>0 x)"
    by (simp add: t0t1)
  also have "\<dots> = \<tau>\<^sub>0 x "
    by simp
  finally show ?thesis.
qed

lemma "\<sigma>\<^sub>0 x = x"
  (*nitpick [expect = genuine]*)
  oops 

lemma s1t1: "\<sigma>\<^sub>1 x = \<tau>\<^sub>1 x"
  using local.s0s1 s0t0 t0t1 by force

lemma "x \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x = x'"
  (*nitpick [expect = genuine]*)
  oops 

lemma "x \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x = x'"
  (*nitpick [expect = genuine]*)
  oops 

text \<open>The two compositions are still different---but see below for 2-catoids.\<close>

end

subsection\<open>2-Catoids with (too) strong homomorphisms\<close>

class two_catoid_collapse = two_st_multimagma_collapse + catoid0 + catoid1

begin

text \<open>The two compositions are still different, and neither of them commutes.\<close>

lemma "x \<odot>\<^sub>0 y = x \<odot>\<^sub>1 y"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<odot>\<^sub>0 y = y \<odot>\<^sub>0 x"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<odot>\<^sub>1 y = y \<odot>\<^sub>1 x"
  (*nitpick [expect = genuine]*)
  oops

end

subsection\<open>Single-set 2-categories with (too) strong homomorphisms\<close>

class two_category_collapse = two_catoid_collapse + single_set_category0 + single_set_category1

begin

lemma comp_collapse: "x \<odot>\<^sub>0 y = x \<odot>\<^sub>1 y"
  by (smt (verit, del_insts) local.interchange local.mm0.conv_atom local.mm1.conv_atom local.pm1.functionality_lem_var local.s0s1 local.src0_absorb local.src1_absorb local.stmsg1.sts_msg.st_local local.t0t1 local.tgt0_absorb local.tgt1_absorb ssmsg0.st_local subset_singleton_iff)

lemma comp0_comm: "x \<odot>\<^sub>0 y = y \<odot>\<^sub>0 x"
  by (smt (verit, best) bot_set_def comp_collapse doubleton_eq_iff local.interchange local.mm0.conv_atom local.mm1.conv_atom local.pm0.functionality_lem_var local.s0t0 local.src0_absorb local.tgt0_absorb singleton_insert_inj_eq' ssmsg0.st_local)

lemma comp1_comm: "x \<odot>\<^sub>1 y = y \<odot>\<^sub>1 x"
  using comp0_comm comp_collapse by auto

lemma "\<sigma>\<^sub>0 x = x"
  (*nitpick [expect = genuine]*)
  oops 

lemma "\<sigma>\<^sub>0 x = \<sigma>\<^sub>0 y"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<odot>\<^sub>0 y \<noteq> {}"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<odot>\<^sub>1 y \<noteq> {}"
  (*nitpick [expect = genuine]*)
  oops

end

subsection \<open>2-lr-Multimagmas with strong interchange law\<close>

class two_lr_multimagma_bad = st_multimagma0 + st_multimagma1 +
  assumes comm_s0s1: "\<sigma>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and comm_t0t1: "\<tau>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<tau>\<^sub>0 x)"
  and comm_s0t1: "\<sigma>\<^sub>0 (\<tau>\<^sub>1 x) = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
  and comm_t0s1: "\<tau>\<^sub>0 (\<sigma>\<^sub>1 x) = \<sigma>\<^sub>1 (\<tau>\<^sub>0 x)"
  assumes interchange: "(w \<odot>\<^sub>1 x) *\<^sub>0 (y \<odot>\<^sub>1 z) = (w \<odot>\<^sub>0 y) *\<^sub>1 (x \<odot>\<^sub>0 z)" (* this is too strong *)
  and t0_hom: "Tgt\<^sub>0 (x \<odot>\<^sub>1 y) = \<tau>\<^sub>0 x \<odot>\<^sub>1 \<tau>\<^sub>0 y"
  and t1_hom: "Tgt\<^sub>1 (x \<odot>\<^sub>0 y) = \<tau>\<^sub>1 x \<odot>\<^sub>0 \<tau>\<^sub>1 y"
  and s0_hom: "Src\<^sub>0 (x \<odot>\<^sub>1 y) \<subseteq> \<sigma>\<^sub>0 x \<odot>\<^sub>1 \<sigma>\<^sub>0 y" 
  and s1_hom: "Src\<^sub>1 (x \<odot>\<^sub>0 y) \<subseteq> \<sigma>\<^sub>1 x \<odot>\<^sub>0 \<sigma>\<^sub>1 y" 
  and s1_s0 [simp]: "\<sigma>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x" 
  and t1_s0 [simp]: "\<tau>\<^sub>1 (\<sigma>\<^sub>0 x) = \<sigma>\<^sub>0 x"  
  and s1_t0 [simp]: "\<sigma>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x" 
  and t1_t0 [simp]: "\<tau>\<^sub>1 (\<tau>\<^sub>0 x) = \<tau>\<^sub>0 x" 

begin

text \<open>The source and target structure collapses.\<close>

lemma s0s1: "\<sigma>\<^sub>0 x = \<sigma>\<^sub>1 x"
  by (metis image_empty local.comm_s0s1 local.s1_s0 local.stmm0.stopp.st_fix local.stmm0.stopp.ts_compat local.t0_hom stmm1.s_absorb_var3)

lemma t0t1: "\<tau>\<^sub>0 x = \<tau>\<^sub>1 x"
  using local.comm_s0t1 local.comm_t0s1 local.s0s1 stmm0.ts_compat by auto

lemma s0t0: "\<sigma>\<^sub>0 x = \<tau>\<^sub>0 x"
proof-
  have "\<sigma>\<^sub>0 x = \<tau>\<^sub>1 (\<sigma>\<^sub>0 x)"
    by simp
  also have "\<dots> = \<sigma>\<^sub>0 (\<tau>\<^sub>1 x)"
    by (simp add: local.comm_s0t1)
  also have "\<dots> = \<sigma>\<^sub>0 (\<tau>\<^sub>0 x)"
    by (simp add: local.t0t1)
  also have "\<dots> = \<tau>\<^sub>0 x "
    by simp
  finally show ?thesis.
qed

lemma s1t1: "\<sigma>\<^sub>1 x = \<tau>\<^sub>1 x"
  using local.comm_t0s1 local.t0t1 by force

lemma comp_collapse: "x \<odot>\<^sub>0 y = x \<odot>\<^sub>1 y"
  by (metis (no_types, opaque_lifting) local.interchange local.s0s1 local.src0_absorb local.src1_absorb local.stmm0.stopp.Dst local.stmm1.stopp.Dst local.t0t1 local.tgt0_absorb local.tgt1_absorb multimagma.conv_atom)

lemma comp0_comm: "x \<odot>\<^sub>0 y = y \<odot>\<^sub>0 x"
  by (metis local.comp_collapse local.interchange local.mm0.conv_atom local.s0s1 local.s1t1 local.src0_absorb local.tgt1_absorb stmm1.t_comm)

lemma comp1_comm: "x \<odot>\<^sub>1 y = y \<odot>\<^sub>1 x"
  using local.comp0_comm local.comp_collapse by auto

lemma comp0_assoc: "{x} *\<^sub>0 (y \<odot>\<^sub>0 z) = (x \<odot>\<^sub>0 y) *\<^sub>0 {z}"
  by (smt (z3) local.comp_collapse local.interchange local.s1t1 local.src1_absorb local.stmm0.stopp.Dst local.stmm0.stopp.s_assoc local.stmm1.stopp.conv_atom local.t0t1 local.t1_t0 local.tgt1_absorb)

lemma comp1_assoc: "{x} *\<^sub>1 (y \<odot>\<^sub>1 z) = (x \<odot>\<^sub>1 y) *\<^sub>1 {z}"
  by (metis (full_types) local.comp0_assoc local.comp1_comm local.comp_collapse local.interchange local.tgt1_absorb)

lemma "\<sigma>\<^sub>0 x = x"
  (*nitpick [expect = genuine]*)
  oops 

lemma "\<sigma>\<^sub>0 x = \<sigma>\<^sub>0 y"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<odot>\<^sub>0 y \<noteq> {}"
  (*nitpick [expect = genuine]*) 
  oops

lemma "x \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>0 z \<Longrightarrow> x = x'"
  (*nitpick [expect = genuine]*)
  oops 

lemma "x \<odot>\<^sub>1 y \<noteq> {}"
  (*nitpick [expect = genuine]*)
  oops

lemma "x \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x' \<in> y \<odot>\<^sub>1 z \<Longrightarrow> x = x'"
  (*nitpick [expect = genuine]*)
  oops 

end

end

