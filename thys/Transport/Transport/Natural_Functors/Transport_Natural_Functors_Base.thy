\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Transport for Natural Functors\<close>
subsection \<open>Basic Setup\<close>
theory Transport_Natural_Functors_Base
  imports
    HOL.BNF_Def
    HOL_Alignment_Functions
    Transport_Base
begin

paragraph \<open>Summary\<close>
text \<open>Basic setup for closure proofs and simple lemmas.\<close>

text \<open>In the following, we willingly use granular apply-style proofs since,
in practice, these theorems have to be automatically generated whenever we
declare a new natural functor.

Note that "HOL-Library" provides a command \<open>bnf_axiomatization\<close> which allows
one to axiomatically declare a bounded natural functor. However, we only need a
subset of these axioms - the boundedness of the functor is irrelevant for our
purposes. For this reason - and the sake of completeness - we state all the
required axioms explicitly below.\<close>

lemma Grp_UNIV_eq_eq_comp: "BNF_Def.Grp UNIV f = (=) \<circ> f"
  by (intro ext) (auto elim: GrpE intro: GrpI)

lemma eq_comp_rel_comp_eq_comp: "(=) \<circ> f \<circ>\<circ> R = R \<circ> f"
  by (intro ext) auto

lemma Domain_Collect_case_prod_eq_Collect_in_dom:
  "Domain {(x, y). R x y} = {x. in_dom R x}"
  by blast

lemma ball_in_dom_iff_ball_ex:
  "(\<forall>x \<in> S. in_dom R x) \<longleftrightarrow> (\<forall>x \<in> S. \<exists>y. R x y)"
  by blast

lemma pair_mem_Collect_case_prod_iff: "(x, y) \<in> {(x, y). R x y} \<longleftrightarrow> R x y"
  by blast


paragraph \<open>Natural Functor Axiomatisation\<close>

typedecl ('d, 'a, 'b, 'c) F

consts Fmap :: "('a1 \<Rightarrow> 'a2) \<Rightarrow> ('b1 \<Rightarrow> 'b2) \<Rightarrow> ('c1 \<Rightarrow> 'c2) \<Rightarrow>
    ('d, 'a1, 'b1, 'c1) F \<Rightarrow> ('d, 'a2, 'b2, 'c2) F"
  Fset1 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'a set"
  Fset2 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'b set"
  Fset3 :: "('d, 'a, 'b, 'c) F \<Rightarrow> 'c set"

axiomatization
  where Fmap_id: "Fmap id id id = id"
  and Fmap_comp: "\<And>f1 f2 f3 g1 g2 g3.
    Fmap (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) = Fmap g1 g2 g3 \<circ> Fmap f1 f2 f3"
  and Fmap_cong: "\<And>f1 f2 f3 g1 g2 g3 x.
    (\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> f1 x1 = g1 x1) \<Longrightarrow>
    (\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> f2 x2 = g2 x2) \<Longrightarrow>
    (\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> f3 x3 = g3 x3) \<Longrightarrow>
    Fmap f1 f2 f3 x = Fmap g1 g2 g3 x"
  and Fset1_natural: "\<And>f1 f2 f3. Fset1 \<circ> Fmap f1 f2 f3 = image f1 \<circ> Fset1"
  and Fset2_natural: "\<And>f1 f2 f3. Fset2 \<circ> Fmap f1 f2 f3 = image f2 \<circ> Fset2"
  and Fset3_natural: "\<And>f1 f2 f3. Fset3 \<circ> Fmap f1 f2 f3 = image f3 \<circ> Fset3"

lemma Fmap_id_eq_self: "Fmap id id id x = x"
  by (subst Fmap_id, subst id_eq_self, rule refl)

lemma Fmap_comp_eq_Fmap_Fmap:
  "Fmap (g1 \<circ> f1) (g2 \<circ> f2) (g3 \<circ> f3) x = Fmap g1 g2 g3 (Fmap f1 f2 f3 x)"
  by (fact fun_cong[OF Fmap_comp, simplified comp_eq])

lemma Fset1_Fmap_eq_image_Fset1: "Fset1 (Fmap f1 f2 f3 x) = f1 ` Fset1 x"
  by (fact fun_cong[OF Fset1_natural, simplified comp_eq])

lemma Fset2_Fmap_eq_image_Fset2: "Fset2 (Fmap f1 f2 f3 x) = f2 ` Fset2 x"
  by (fact fun_cong[OF Fset2_natural, simplified comp_eq])

lemma Fset3_Fmap_eq_image_Fset3: "Fset3 (Fmap f1 f2 f3 x) = f3 ` Fset3 x"
  by (fact fun_cong[OF Fset3_natural, simplified comp_eq])

lemmas Fset_Fmap_eqs = Fset1_Fmap_eq_image_Fset1 Fset2_Fmap_eq_image_Fset2
  Fset3_Fmap_eq_image_Fset3

paragraph \<open>Relator\<close>

definition Frel :: "('a1 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow> ('b1 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow> ('c1 \<Rightarrow> 'c2 \<Rightarrow> bool) \<Rightarrow>
  ('d, 'a1, 'b1, 'c1) F \<Rightarrow> ('d, 'a2, 'b2, 'c2) F \<Rightarrow> bool"
  where "Frel R1 R2 R3 x y \<equiv> (\<exists>z.
    z \<in> {x. Fset1 x \<subseteq> {(x, y). R1 x y} \<and> Fset2 x \<subseteq> {(x, y). R2 x y}
      \<and> Fset3 x \<subseteq> {(x, y). R3 x y}}
    \<and> Fmap fst fst fst z = x
    \<and> Fmap snd snd snd z = y)"

lemma FrelI:
  assumes "Fset1 z \<subseteq> {(x, y). R1 x y}"
  and "Fset2 z \<subseteq> {(x, y). R2 x y}"
  and "Fset3 z \<subseteq> {(x, y). R3 x y}"
  and "Fmap fst fst fst z = x"
  and "Fmap snd snd snd z = y"
  shows "Frel R1 R2 R3 x y"
  apply (subst Frel_def)
  apply (intro exI conjI CollectI)
  apply (fact assms)+
  done

lemma FrelE:
  assumes "Frel R1 R2 R3 x y"
  obtains z where "Fset1 z \<subseteq> {(x, y). R1 x y}" "Fset2 z \<subseteq> {(x, y). R2 x y}"
    "Fset3 z \<subseteq> {(x, y). R3 x y}" "Fmap fst fst fst z = x" "Fmap snd snd snd z = y"
  apply (insert assms)
  apply (subst (asm) Frel_def)
  apply (elim exE CollectE conjE)
  apply assumption
  done

lemma Grp_UNIV_Fmap_eq_Frel_Grp: "BNF_Def.Grp UNIV (Fmap f1 f2 f3) =
  Frel (BNF_Def.Grp UNIV f1) (BNF_Def.Grp UNIV f2) (BNF_Def.Grp UNIV f3)"
  apply (intro ext iffI)
    apply (rule FrelI[where
      ?z="Fmap (BNF_Def.convol id f1) (BNF_Def.convol id f2) (BNF_Def.convol id f3) _"])
    apply (subst Fset_Fmap_eqs,
      rule image_subsetI,
      rule convol_mem_GrpI[simplified Fun_id_eq_id],
      rule UNIV_I)+
    apply (unfold Fmap_comp_eq_Fmap_Fmap[symmetric]
      fst_convol[simplified Fun_comp_eq_comp]
      snd_convol[simplified Fun_comp_eq_comp]
      Fmap_id id_eq_self)
    apply (rule refl)
    apply (subst (asm) Grp_UNIV_eq_eq_comp)
    apply (subst (asm) comp_eq)
    apply assumption
    apply (erule FrelE)
    apply hypsubst
    apply (subst Grp_UNIV_eq_eq_comp)
    apply (subst comp_eq)
    apply (subst Fmap_comp_eq_Fmap_Fmap[symmetric])
    apply (rule Fmap_cong;
      rule Collect_case_prod_Grp_eqD[simplified Fun_comp_eq_comp],
      drule rev_subsetD,
      assumption+)
  done

lemma Frel_Grp_UNIV_Fmap:
  "Frel (BNF_Def.Grp UNIV f1) (BNF_Def.Grp UNIV f2) (BNF_Def.Grp UNIV f3)
    x (Fmap f1 f2 f3 x)"
  apply (subst Grp_UNIV_Fmap_eq_Frel_Grp[symmetric])
  apply (subst Grp_UNIV_eq_eq_comp)
  apply (subst comp_eq)
  apply (rule refl)
  done

lemma Frel_Grp_UNIV_iff_eq_Fmap:
  "Frel (BNF_Def.Grp UNIV f1) (BNF_Def.Grp UNIV f2) (BNF_Def.Grp UNIV f3) x y \<longleftrightarrow>
    (y = Fmap f1 f2 f3 x)"
  by (subst eq_commute[of y])
  (fact fun_cong[OF fun_cong[OF Grp_UNIV_Fmap_eq_Frel_Grp],
    simplified Grp_UNIV_eq_eq_comp comp_eq, folded Grp_UNIV_eq_eq_comp, symmetric])

lemma Frel_eq: "Frel (=) (=) (=) = (=)"
  apply (unfold BNF_Def.eq_alt[simplified Fun_id_eq_id])
  apply (subst Grp_UNIV_Fmap_eq_Frel_Grp[symmetric])
  apply (subst Fmap_id)
  apply (fold BNF_Def.eq_alt[simplified Fun_id_eq_id])
  apply (rule refl)
  done

corollary Frel_eq_self: "Frel (=) (=) (=) x x"
  by (fact iffD2[OF fun_cong[OF fun_cong[OF Frel_eq]] refl])

lemma Frel_mono_strong:
  assumes "Frel R1 R2 R3 x y"
  and "\<And>x1 y1. x1 \<in> Fset1 x \<Longrightarrow> y1 \<in> Fset1 y \<Longrightarrow> R1 x1 y1 \<Longrightarrow> S1 x1 y1"
  and "\<And>x2 y2. x2 \<in> Fset2 x \<Longrightarrow> y2 \<in> Fset2 y \<Longrightarrow> R2 x2 y2 \<Longrightarrow> S2 x2 y2"
  and "\<And>x3 y3. x3 \<in> Fset3 x \<Longrightarrow> y3 \<in> Fset3 y \<Longrightarrow> R3 x3 y3 \<Longrightarrow> S3 x3 y3"
  shows "Frel S1 S2 S3 x y"
  apply (insert assms(1))
  apply (erule FrelE)
  apply (rule FrelI)
    apply (rule subsetI,
      frule rev_subsetD,
      assumption,
      frule imageI[of _ "Fset1 _" fst]
        imageI[of _ "Fset2 _" fst]
        imageI[of _ "Fset3 _" fst],
      drule imageI[of _ "Fset1 _" snd]
        imageI[of _ "Fset2 _" snd]
        imageI[of _ "Fset3 _" snd],
      (subst (asm) Fset_Fmap_eqs[symmetric])+,
      intro CollectI case_prodI2,
      rule assms;
      hypsubst,
      unfold fst_conv snd_conv,
      (elim CollectE case_prodE Pair_inject, hypsubst)?,
      assumption)+
    apply assumption+
  done

corollary Frel_mono:
  assumes "R1 \<le> S1" "R2 \<le> S2" "R3 \<le> S3"
  shows "Frel R1 R2 R3 \<le> Frel S1 S2 S3"
  apply (intro le_relI)
  apply (rule Frel_mono_strong)
    apply assumption
    apply (insert assms)
    apply (drule le_relD[OF assms(1)] le_relD[OF assms(2)] le_relD[OF assms(3)],
      assumption)+
  done

lemma Frel_refl_strong:
  assumes "\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> R1 x1 x1"
  and "\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> R2 x2 x2"
  and "\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> R3 x3 x3"
  shows "Frel R1 R2 R3 x x"
  by (rule Frel_mono_strong[OF Frel_eq_self[of x]];
    drule assms, hypsubst, assumption)

lemma Frel_cong:
  assumes "\<And>x1 y1. x1 \<in> Fset1 x \<Longrightarrow> y1 \<in> Fset1 y \<Longrightarrow> R1 x1 y1 \<longleftrightarrow> R1' x1 y1"
  and "\<And>x2 y2. x2 \<in> Fset2 x \<Longrightarrow> y2 \<in> Fset2 y \<Longrightarrow> R2 x2 y2 \<longleftrightarrow> R2' x2 y2"
  and "\<And>x3 y3. x3 \<in> Fset3 x \<Longrightarrow> y3 \<in> Fset3 y \<Longrightarrow> R3 x3 y3 \<longleftrightarrow> R3' x3 y3"
  shows "Frel R1 R2 R3 x y = Frel R1' R2' R3' x y"
  by (rule iffI;
    rule Frel_mono_strong,
    assumption;
    rule iffD1[OF assms(1)] iffD1[OF assms(2)] iffD1[OF assms(3)]
      iffD2[OF assms(1)] iffD2[OF assms(2)] iffD2[OF assms(3)];
    assumption)

lemma Frel_rel_inv_eq_rel_inv_Frel: "Frel R1\<inverse> R2\<inverse> R3\<inverse> = (Frel R1 R2 R3)\<inverse>"
  by (intro ext iffI;
    unfold rel_inv_iff_rel,
    erule FrelE,
    hypsubst,
    rule FrelI[where ?z="Fmap prod.swap prod.swap prod.swap _"];
      ((subst Fset_Fmap_eqs,
      rule image_subsetI,
      drule rev_subsetD,
      assumption,
      elim CollectE case_prodE,
      hypsubst,
      subst swap_simp,
      subst pair_mem_Collect_case_prod_iff,
      assumption) |
      (subst Fmap_comp_eq_Fmap_Fmap[symmetric],
        rule Fmap_cong;
        unfold comp_eq fst_swap snd_swap,
        rule refl)))

text \<open>Given the former axioms, the following axiom - subdistributivity of the
relator - is equivalent to the (F, Fmap) functor preserving weak pullbacks.\<close>

axiomatization
  where Frel_comp_le_Frel_rel_comp: "\<And>R1 R2 R3 S1 S2 S3.
    Frel R1 R2 R3 \<circ>\<circ> Frel S1 S2 S3 \<le> Frel (R1 \<circ>\<circ> S1) (R2 \<circ>\<circ> S2) (R3 \<circ>\<circ> S3)"

lemma fst_sndOp_eq_snd_fstOp: "fst \<circ> BNF_Def.sndOp P Q = snd \<circ> BNF_Def.fstOp P Q"
  unfolding fstOp_def sndOp_def by (intro ext) simp

lemma Frel_rel_comp_le_Frel_comp:
  "Frel (R1 \<circ>\<circ> S1) (R2 \<circ>\<circ> S2) (R3 \<circ>\<circ> S3) \<le> (Frel R1 R2 R3 \<circ>\<circ> Frel S1 S2 S3)"
  apply (rule le_relI)
  apply (erule FrelE)
  apply (rule rel_compI[where ?y="Fmap (snd \<circ> BNF_Def.fstOp R1 S1)
    (snd \<circ> BNF_Def.fstOp R2 S2) (snd \<circ> BNF_Def.fstOp R3 S3) _"])
  apply (rule FrelI[where ?z="Fmap (BNF_Def.fstOp R1 S1)
    (BNF_Def.fstOp R2 S2) (BNF_Def.fstOp R3 S3) _"])
    apply (subst Fset_Fmap_eqs,
      intro image_subsetI,
      rule fstOp_in[unfolded relcompp_eq_rel_comp],
      drule rev_subsetD,
      assumption+)+
    apply (subst Fmap_comp_eq_Fmap_Fmap[symmetric])
    apply (fold ext[of fst "fst \<circ> _", OF fst_fstOp[unfolded Fun_comp_eq_comp]])
    apply hypsubst
    apply (rule refl)
    apply (subst Fmap_comp_eq_Fmap_Fmap[symmetric])
    apply (rule refl)
    apply (rule FrelI[where ?z="Fmap (BNF_Def.sndOp R1 S1)
      (BNF_Def.sndOp R2 S2) (BNF_Def.sndOp R3 S3) _"])
    apply (subst Fset_Fmap_eqs,
      intro image_subsetI,
      rule sndOp_in[unfolded relcompp_eq_rel_comp],
      drule rev_subsetD,
      assumption+)+
    apply (subst Fmap_comp_eq_Fmap_Fmap[symmetric])
    apply (unfold fst_sndOp_eq_snd_fstOp)
    apply (rule refl)
    apply (subst Fmap_comp_eq_Fmap_Fmap[symmetric])
    apply (fold ext[of snd "snd \<circ> _", OF snd_sndOp[unfolded Fun_comp_eq_comp]])
    apply hypsubst
    apply (rule refl)
  done

corollary Frel_comp_eq_Frel_rel_comp:
  "Frel R1 R2 R3 \<circ>\<circ> Frel S1 S2 S3 = Frel (R1 \<circ>\<circ> S1) (R2 \<circ>\<circ> S2) (R3 \<circ>\<circ> S3)"
  by (rule antisym; rule Frel_comp_le_Frel_rel_comp Frel_rel_comp_le_Frel_comp)

lemma Frel_Fmap_eq1: "Frel R1 R2 R3 (Fmap f1 f2 f3 x) y =
  Frel (\<lambda>x. R1 (f1 x)) (\<lambda>x. R2 (f2 x)) (\<lambda>x. R3 (f3 x)) x y"
  apply (rule iffI)
    apply (fold comp_eq[of R1] comp_eq[of R2] comp_eq[of R3])
    apply (drule rel_compI[where ?R="Frel _ _ _" and ?S="Frel _ _ _",
      OF Frel_Grp_UNIV_Fmap])
    apply (unfold Grp_UNIV_eq_eq_comp)
    apply (drule le_relD[OF Frel_comp_le_Frel_rel_comp])
    apply (unfold eq_comp_rel_comp_eq_comp)
    apply assumption
    apply (fold eq_comp_rel_comp_eq_comp[where ?R=R1]
      eq_comp_rel_comp_eq_comp[where ?R=R2]
      eq_comp_rel_comp_eq_comp[where ?R=R3]
      Grp_UNIV_eq_eq_comp)
    apply (drule le_relD[OF Frel_rel_comp_le_Frel_comp])
    apply (erule rel_compE)
    apply (subst (asm) Frel_Grp_UNIV_iff_eq_Fmap)
    apply hypsubst
    apply assumption
  done

lemma Frel_Fmap_eq2: "Frel R1 R2 R3 x (Fmap g1 g2 g3 y) =
  Frel (\<lambda>x y. R1 x (g1 y)) (\<lambda>x y. R2 x (g2 y)) (\<lambda>x y. R3 x (g3 y)) x y"
  apply (subst rel_inv_iff_rel[of "Frel _ _ _", symmetric])
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (subst Frel_Fmap_eq1)
  apply (rule sym)
  apply (subst rel_inv_iff_rel[of "Frel _ _ _", symmetric])
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (unfold rel_inv_iff_rel)
  apply (rule refl)
  done

lemmas Frel_Fmap_eqs = Frel_Fmap_eq1 Frel_Fmap_eq2


paragraph \<open>Predicator\<close>

definition Fpred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow>
  ('d, 'a, 'b, 'c) F \<Rightarrow> bool"
  where "Fpred P1 P2 P3 x \<equiv> Frel ((=)\<restriction>\<^bsub>P1\<^esub>) ((=)\<restriction>\<^bsub>P2\<^esub>) ((=)\<restriction>\<^bsub>P3\<^esub>) x x"

lemma Fpred_mono_strong:
  assumes "Fpred P1 P2 P3 x"
  and "\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> P1 x1 \<Longrightarrow> Q1 x1"
  and "\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> P2 x2 \<Longrightarrow> Q2 x2"
  and "\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> P3 x3 \<Longrightarrow> Q3 x3"
  shows "Fpred Q1 Q2 Q3 x"
  apply (insert assms(1))
  apply (unfold Fpred_def)
  apply (rule Frel_mono_strong,
    assumption;
    erule restrict_leftE,
    rule restrict_leftI,
    assumption,
    rule assms,
    assumption+)
  done

lemma Fpred_top: "Fpred \<top> \<top> \<top> x"
  apply (subst Fpred_def)
  apply (rule Frel_refl_strong;
    subst restrict_left_top_eq,
    rule refl)
  done

lemma FpredI:
  assumes "\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> P1 x1"
  and "\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> P2 x2"
  and "\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> P3 x3"
  shows "Fpred P1 P2 P3 x"
  using assms by (rule Fpred_mono_strong[OF Fpred_top])

lemma FpredE:
  assumes "Fpred P1 P2 P3 x"
  obtains "\<And>x1. x1 \<in> Fset1 x \<Longrightarrow> P1 x1"
    "\<And>x2. x2 \<in> Fset2 x \<Longrightarrow> P2 x2"
    "\<And>x3. x3 \<in> Fset3 x \<Longrightarrow> P3 x3"
  by (elim meta_impE; (assumption |
    insert assms,
    subst (asm) Fpred_def,
    erule FrelE,
    hypsubst,
    subst (asm) Fset_Fmap_eqs,
    subst (asm) Domain_fst[symmetric],
    drule rev_subsetD,
    rule Domain_mono,
    assumption,
    unfold Domain_Collect_case_prod_eq_Collect_in_dom in_dom_restrict_left_eq,
    elim CollectE inf1E,
    assumption))

lemma Fpred_eq_ball: "Fpred P1 P2 P3 =
  (\<lambda>x. Ball (Fset1 x) P1 \<and> Ball (Fset2 x) P2 \<and> Ball (Fset3 x) P3)"
  by (intro ext iffI conjI ballI FpredI; elim FpredE conjE bspec)

lemma Fpred_Fmap_eq:
  "Fpred P1 P2 P3 (Fmap f1 f2 f3 x) = Fpred (P1 \<circ> f1) (P2 \<circ> f2) (P3 \<circ> f3) x"
  by (unfold Fpred_def Frel_Fmap_eqs)
  (rule iffI;
    erule FrelE,
    hypsubst,
    unfold Frel_Fmap_eqs,
    rule Frel_refl_strong;
    rule restrict_leftI,
    rule refl,
    drule rev_subsetD,
    assumption,
    elim CollectE case_prodE restrict_leftE,
    hypsubst,
    unfold comp_eq fst_conv,
    assumption)

lemma Fpred_in_dom_if_in_dom_Frel:
  assumes "in_dom (Frel R1 R2 R3) x"
  shows "Fpred (in_dom R1) (in_dom R2) (in_dom R3) x"
  apply (insert assms)
  apply (elim in_domE FrelE)
  apply hypsubst
  apply (subst Fpred_Fmap_eq)
  apply (rule FpredI;
    drule rev_subsetD,
    assumption,
    elim CollectE case_prodE,
    hypsubst,
    unfold comp_eq fst_conv,
    rule in_domI,
    assumption)
  done

lemma in_dom_Frel_if_Fpred_in_dom:
  assumes "Fpred (in_dom R1) (in_dom R2) (in_dom R3) x"
  shows "in_dom (Frel R1 R2 R3) x"
  apply (insert assms)
  apply (subst (asm) Fpred_eq_ball)
  apply (elim conjE)
  apply (subst (asm) ball_in_dom_iff_ball_ex,
    drule bchoice, \<comment>\<open>requires the axiom of choice.\<close>
    erule exE)+
  apply (rule in_domI[where ?x=x and ?y="Fmap _ _ _ x" for x])
  apply (subst Frel_Fmap_eq2)
  apply (rule Frel_refl_strong)
  apply (drule bspec[of "Fset1 _"])
  apply assumption+
  apply (drule bspec[of "Fset2 _"])
  apply assumption+
  apply (drule bspec[of "Fset3 _"])
  apply assumption+
  done

lemma in_dom_Frel_eq_Fpred_in_dom:
  "in_dom (Frel R1 R2 R3) = Fpred (in_dom R1) (in_dom R2) (in_dom R3)"
  by (intro ext iffI; rule Fpred_in_dom_if_in_dom_Frel in_dom_Frel_if_Fpred_in_dom)

lemma in_codom_Frel_eq_Fpred_in_codom:
  "in_codom (Frel R1 R2 R3) = Fpred (in_codom R1) (in_codom R2) (in_codom R3)"
  apply (subst in_dom_rel_inv_eq_in_codom[symmetric])
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (subst in_dom_Frel_eq_Fpred_in_dom)
  apply (subst in_dom_rel_inv_eq_in_codom)+
  apply (rule refl)
  done

lemma in_field_Frel_eq_Fpred_in_in_field:
  "in_field (Frel R1 R2 R3) =
    Fpred (in_dom R1) (in_dom R2) (in_dom R3) \<squnion>
    Fpred (in_codom R1) (in_codom R2) (in_codom R3)"
  apply (subst in_field_eq_in_dom_sup_in_codom)
  apply (subst in_dom_Frel_eq_Fpred_in_dom)
  apply (subst in_codom_Frel_eq_Fpred_in_codom)
  apply (rule refl)
  done

lemma Frel_restrict_left_Fpred_eq_Frel_restrict_left:
  fixes R1 :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and R2 :: "'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and R3 :: "'c1 \<Rightarrow> 'c2 \<Rightarrow> bool"
  and P1 :: "'a1 \<Rightarrow> bool"
  and P2 :: "'b1 \<Rightarrow> bool"
  and P3 :: "'c1 \<Rightarrow> bool"
  shows "(Frel R1 R2 R3 :: ('d, 'a1, 'b1, 'c1) F \<Rightarrow> _)\<restriction>\<^bsub>Fpred P1 P2 P3 :: ('d, 'a1, 'b1, 'c1) F \<Rightarrow> _\<^esub> =
    Frel (R1\<restriction>\<^bsub>P1\<^esub>) (R2\<restriction>\<^bsub>P2\<^esub>) (R3\<restriction>\<^bsub>P3\<^esub>)"
  apply (intro ext)
  apply (rule iffI)
    apply (erule restrict_leftE)
    apply (elim FpredE)
    apply (rule Frel_mono_strong,
      assumption;
      rule restrict_leftI,
      assumption+)
    apply (rule restrict_leftI)
      apply (rule Frel_mono_strong,
        assumption;
        erule restrict_leftE,
        assumption)
      apply (drule in_domI[of "Frel (R1\<restriction>\<^bsub>P1\<^esub>) (R2\<restriction>\<^bsub>P2\<^esub>) (R3\<restriction>\<^bsub>P3\<^esub>)"])
      apply (drule Fpred_in_dom_if_in_dom_Frel)
      apply (rule Fpred_mono_strong,
        assumption;
        unfold in_dom_restrict_left_eq inf_apply inf_bool_def;
        rule conjunct2,
        assumption)
  done

lemma Frel_restrict_right_Fpred_eq_Frel_restrict_right:
  fixes R1 :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and R2 :: "'b1 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and R3 :: "'c1 \<Rightarrow> 'c2 \<Rightarrow> bool"
  and P1 :: "'a2 \<Rightarrow> bool"
  and P2 :: "'b2 \<Rightarrow> bool"
  and P3 :: "'c2 \<Rightarrow> bool"
  shows "(Frel R1 R2 R3 :: _ \<Rightarrow> ('d, 'a2, 'b2, 'c2) F \<Rightarrow> _)\<upharpoonleft>\<^bsub>Fpred P1 P2 P3 :: ('d, 'a2, 'b2, 'c2) F \<Rightarrow> _\<^esub> =
    Frel (R1\<upharpoonleft>\<^bsub>P1\<^esub>) (R2\<upharpoonleft>\<^bsub>P2\<^esub>) (R3\<upharpoonleft>\<^bsub>P3\<^esub>)"
  apply (subst restrict_right_eq)
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (subst Frel_restrict_left_Fpred_eq_Frel_restrict_left)
  apply (subst Frel_rel_inv_eq_rel_inv_Frel[symmetric])
  apply (fold restrict_right_eq)
  apply (rule refl)
  done

locale transport_natural_functor =
  t1 : transport L1 R1 l1 r1 + t2 : transport L2 R2 l2 r2 +
  t3 : transport L3 R3 l3 r3
  for L1 :: "'a1 \<Rightarrow> 'a1 \<Rightarrow> bool"
  and R1 :: "'b1 \<Rightarrow> 'b1 \<Rightarrow> bool"
  and l1 :: "'a1 \<Rightarrow> 'b1"
  and r1 :: "'b1 \<Rightarrow> 'a1"
  and L2 :: "'a2 \<Rightarrow> 'a2 \<Rightarrow> bool"
  and R2 :: "'b2 \<Rightarrow> 'b2 \<Rightarrow> bool"
  and l2 :: "'a2 \<Rightarrow> 'b2"
  and r2 :: "'b2 \<Rightarrow> 'a2"
  and L3 :: "'a3 \<Rightarrow> 'a3 \<Rightarrow> bool"
  and R3 :: "'b3 \<Rightarrow> 'b3 \<Rightarrow> bool"
  and l3 :: "'a3 \<Rightarrow> 'b3"
  and r3 :: "'b3 \<Rightarrow> 'a3"
begin

notation L1 (infix "\<le>\<^bsub>L1\<^esub>" 50)
notation R1 (infix "\<le>\<^bsub>R1\<^esub>" 50)
notation L2 (infix "\<le>\<^bsub>L2\<^esub>" 50)
notation R2 (infix "\<le>\<^bsub>R2\<^esub>" 50)
notation L3 (infix "\<le>\<^bsub>L3\<^esub>" 50)
notation R3 (infix "\<le>\<^bsub>R3\<^esub>" 50)

notation t1.ge_left (infix "\<ge>\<^bsub>L1\<^esub>" 50)
notation t1.ge_right (infix "\<ge>\<^bsub>R1\<^esub>" 50)
notation t2.ge_left (infix "\<ge>\<^bsub>L2\<^esub>" 50)
notation t2.ge_right (infix "\<ge>\<^bsub>R2\<^esub>" 50)
notation t3.ge_left (infix "\<ge>\<^bsub>L3\<^esub>" 50)
notation t3.ge_right (infix "\<ge>\<^bsub>R3\<^esub>" 50)

notation t1.left_Galois (infix "\<^bsub>L1\<^esub>\<lessapprox>" 50)
notation t1.right_Galois (infix "\<^bsub>R1\<^esub>\<lessapprox>" 50)
notation t2.left_Galois (infix "\<^bsub>L2\<^esub>\<lessapprox>" 50)
notation t2.right_Galois (infix "\<^bsub>R2\<^esub>\<lessapprox>" 50)
notation t3.left_Galois (infix "\<^bsub>L3\<^esub>\<lessapprox>" 50)
notation t3.right_Galois (infix "\<^bsub>R3\<^esub>\<lessapprox>" 50)

notation t1.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L1\<^esub>" 50)
notation t1.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R1\<^esub>" 50)
notation t2.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L2\<^esub>" 50)
notation t2.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R2\<^esub>" 50)
notation t3.ge_Galois_left (infix "\<greaterapprox>\<^bsub>L3\<^esub>" 50)
notation t3.ge_Galois_right (infix "\<greaterapprox>\<^bsub>R3\<^esub>" 50)

notation t1.right_ge_Galois (infix "\<^bsub>R1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_right (infix "\<lessapprox>\<^bsub>R1\<^esub>" 50)
notation t2.right_ge_Galois (infix "\<^bsub>R2\<^esub>\<greaterapprox>" 50)
notation t2.Galois_right (infix "\<lessapprox>\<^bsub>R2\<^esub>" 50)
notation t3.right_ge_Galois (infix "\<^bsub>R3\<^esub>\<greaterapprox>" 50)
notation t3.Galois_right (infix "\<lessapprox>\<^bsub>R3\<^esub>" 50)

notation t1.left_ge_Galois (infix "\<^bsub>L1\<^esub>\<greaterapprox>" 50)
notation t1.Galois_left (infix "\<lessapprox>\<^bsub>L1\<^esub>" 50)
notation t2.left_ge_Galois (infix "\<^bsub>L2\<^esub>\<greaterapprox>" 50)
notation t2.Galois_left (infix "\<lessapprox>\<^bsub>L2\<^esub>" 50)
notation t3.left_ge_Galois (infix "\<^bsub>L3\<^esub>\<greaterapprox>" 50)
notation t3.Galois_left (infix "\<lessapprox>\<^bsub>L3\<^esub>" 50)

notation t1.unit ("\<eta>\<^sub>1")
notation t1.counit ("\<epsilon>\<^sub>1")
notation t2.unit ("\<eta>\<^sub>2")
notation t2.counit ("\<epsilon>\<^sub>2")
notation t3.unit ("\<eta>\<^sub>3")
notation t3.counit ("\<epsilon>\<^sub>3")

definition "L \<equiv> Frel (\<le>\<^bsub>L1\<^esub>) (\<le>\<^bsub>L2\<^esub>) (\<le>\<^bsub>L3\<^esub>)"

lemma left_rel_eq_Frel: "L = Frel (\<le>\<^bsub>L1\<^esub>) (\<le>\<^bsub>L2\<^esub>) (\<le>\<^bsub>L3\<^esub>)"
  unfolding L_def ..

definition "l \<equiv> Fmap l1 l2 l3"

lemma left_eq_Fmap: "l = Fmap l1 l2 l3"
  unfolding l_def ..

context
begin

interpretation flip :
  transport_natural_functor R1 L1 r1 l1 R2 L2 r2 l2 R3 L3 r3 l3 .

abbreviation "R \<equiv> flip.L"
abbreviation "r \<equiv> flip.l"

lemma right_rel_eq_Frel: "R = Frel (\<le>\<^bsub>R1\<^esub>) (\<le>\<^bsub>R2\<^esub>) (\<le>\<^bsub>R3\<^esub>)"
  unfolding flip.left_rel_eq_Frel ..

lemma right_eq_Fmap: "r = Fmap r1 r2 r3"
  unfolding flip.left_eq_Fmap ..

lemmas transport_defs = left_rel_eq_Frel left_eq_Fmap
  right_rel_eq_Frel right_eq_Fmap

end

sublocale transport L R l r .

(*FIXME: somehow the notation for the fixed parameters L and R, defined in
Order_Functions_Base.thy, is lost. We hence re-declare it here.*)
notation L (infix "\<le>\<^bsub>L\<^esub>" 50)
notation R (infix "\<le>\<^bsub>R\<^esub>" 50)

lemma unit_eq_Fmap: "\<eta> = Fmap \<eta>\<^sub>1 \<eta>\<^sub>2 \<eta>\<^sub>3"
  unfolding unit_eq_comp by (simp only: right_eq_Fmap left_eq_Fmap
    flip: Fmap_comp t1.unit_eq_comp t2.unit_eq_comp t3.unit_eq_comp)

interpretation flip_inv : transport_natural_functor "(\<ge>\<^bsub>R1\<^esub>)" "(\<ge>\<^bsub>L1\<^esub>)" r1 l1
  "(\<ge>\<^bsub>R2\<^esub>)" "(\<ge>\<^bsub>L2\<^esub>)" r2 l2 "(\<ge>\<^bsub>R3\<^esub>)" "(\<ge>\<^bsub>L3\<^esub>)" r3 l3
  rewrites "flip_inv.unit \<equiv> \<epsilon>" and "flip_inv.t1.unit \<equiv> \<epsilon>\<^sub>1"
  and "flip_inv.t2.unit \<equiv> \<epsilon>\<^sub>2" and "flip_inv.t3.unit \<equiv> \<epsilon>\<^sub>3"
  by (simp_all only: order_functors.flip_counit_eq_unit)

lemma counit_eq_Fmap: "\<epsilon> = Fmap \<epsilon>\<^sub>1 \<epsilon>\<^sub>2 \<epsilon>\<^sub>3"
  by (fact flip_inv.unit_eq_Fmap)

lemma flip_inv_right_eq_ge_left: "flip_inv.R = (\<ge>\<^bsub>L\<^esub>)"
  unfolding left_rel_eq_Frel flip_inv.right_rel_eq_Frel
  by (fact Frel_rel_inv_eq_rel_inv_Frel)

interpretation flip :
  transport_natural_functor R1 L1 r1 l1 R2 L2 r2 l2 R3 L3 r3 l3 .

lemma flip_inv_left_eq_ge_right: "flip_inv.L \<equiv> (\<ge>\<^bsub>R\<^esub>)"
  unfolding flip.flip_inv_right_eq_ge_left .

lemma mono_wrt_rel_leftI:
  assumes "((\<le>\<^bsub>L1\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R1\<^esub>)) l1"
  and "((\<le>\<^bsub>L2\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R2\<^esub>)) l2"
  and "((\<le>\<^bsub>L3\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R3\<^esub>)) l3"
  shows "((\<le>\<^bsub>L\<^esub>) \<Rrightarrow>\<^sub>m (\<le>\<^bsub>R\<^esub>)) l"
  apply (unfold left_rel_eq_Frel right_rel_eq_Frel left_eq_Fmap)
  apply (rule dep_mono_wrt_relI)
  apply (unfold Frel_Fmap_eqs)
  apply (fold rel_map_eq)
  apply (rule le_relD[OF Frel_mono])
    apply (subst mono_wrt_rel_iff_le_rel_map[symmetric], rule assms)+
    apply assumption
  done

end


end