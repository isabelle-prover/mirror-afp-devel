(*
Author:  Akihisa Yamada (2018-2021)
License: LGPL (see file COPYING.LESSER)
*)
section \<open>Binary Relations\<close>

text \<open>We start with basic properties of binary relations.\<close>

theory Binary_Relations
  imports
(* To verify that we don't use the axiom of choice, import
    HOL.Complete_Partial_Order HOL.Wellfounded
   instead of *)
    Main
begin

unbundle lattice_syntax

lemma conj_iff_conj_iff_imp_iff: "Trueprop (x \<and> y \<longleftrightarrow> x \<and> z) \<equiv> (x \<Longrightarrow> (y \<longleftrightarrow> z))"
  by (auto intro!: equal_intr_rule)

lemma conj_imp_eq_imp_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)"
  by standard simp_all

lemma tranclp_trancl: "r\<^sup>+\<^sup>+ = (\<lambda>x y. (x,y) \<in> {(a,b). r a b}\<^sup>+)"
  by (auto simp: tranclp_trancl_eq[symmetric])

lemma tranclp_id[simp]: "transp r \<Longrightarrow> tranclp r = r"
  using trancl_id[of "{(x,y). r x y}", folded transp_trans] by (auto simp:tranclp_trancl)

lemma transp_tranclp[simp]: "transp (tranclp r)" by (auto simp: tranclp_trancl transp_trans)

lemma funpow_dom: "f ` A \<subseteq> A \<Longrightarrow> (f^^n) ` A \<subseteq> A" by (induct n, auto)

lemma image_subsetD: "f ` A \<subseteq> B \<Longrightarrow> a \<in> A \<Longrightarrow> f a \<in> B" by auto

text \<open>Below we introduce an Isabelle-notation for $\{ \ldots x\ldots \mid x \in X \}$.\<close>

syntax
  "_range" :: "'a \<Rightarrow> idts \<Rightarrow> 'a set" ("(1{_ /|./ _})")
  "_image" :: "'a \<Rightarrow> pttrn \<Rightarrow> 'a set \<Rightarrow> 'a set"  ("(1{_ /|./ (_/ \<in> _)})")
translations
  "{e |. p}" \<rightleftharpoons> "{e | p. CONST True}"
  "{e |. p \<in> A}" \<rightleftharpoons> "CONST image (\<lambda>p. e) A"

lemma image_constant:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i = y"
  shows "f ` I = (if I = {} then {} else {y})"
  using assms by auto


subsection \<open>Various Definitions\<close>

text \<open>Here we introduce various definitions for binary relations.
The first one is our abbreviation for the dual of a relation.\<close>

abbreviation(input) dual ("(_\<^sup>-)" [1000] 1000) where "r\<^sup>- x y \<equiv> r y x"

lemma conversep_is_dual[simp]: "conversep = dual" by auto

lemma dual_inf: "(r \<sqinter> s)\<^sup>- = r\<^sup>- \<sqinter> s\<^sup>-" by (auto intro!: ext)

text \<open>Monotonicity is already defined in the library, but we want one restricted to a domain.\<close>

lemmas monotone_onE = monotone_on_def[unfolded atomize_eq, THEN iffD1, elim_format, rule_format]

lemma monotone_on_dual: "monotone_on X r s f \<Longrightarrow> monotone_on X r\<^sup>- s\<^sup>- f"
  by (auto simp: monotone_on_def)

lemma monotone_on_id: "monotone_on X r r id"
  by (auto simp: monotone_on_def)

lemma monotone_on_cmono: "A \<subseteq> B \<Longrightarrow> monotone_on B \<le> monotone_on A"
   by (intro le_funI, auto simp: monotone_on_def)

text \<open>Here we define the following notions in a standard manner\<close>

text \<open>The symmetric part of a relation:\<close>

definition sympartp where "sympartp r x y \<equiv> r x y \<and> r y x"

lemma sympartpI[intro]:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "x \<sqsubseteq> y" and "y \<sqsubseteq> x" shows "sympartp (\<sqsubseteq>) x y"
  using assms by (auto simp: sympartp_def)

lemma sympartpE[elim]:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "sympartp (\<sqsubseteq>) x y" and "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: sympartp_def)

lemma sympartp_dual: "sympartp r\<^sup>- = sympartp r"
  by (auto intro!:ext simp: sympartp_def)

lemma sympartp_eq[simp]: "sympartp (=) = (=)" by auto

lemma sympartp_sympartp[simp]: "sympartp (sympartp r) = sympartp r" by (auto intro!:ext)

lemma reflclp_sympartp[simp]: "(sympartp r)\<^sup>=\<^sup>= = sympartp r\<^sup>=\<^sup>=" by auto

definition "equivpartp r x y \<equiv> x = y \<or> r x y \<and> r y x"

lemma sympartp_reflclp_equivp[simp]: "sympartp r\<^sup>=\<^sup>= = equivpartp r" by (auto intro!:ext simp: equivpartp_def)

lemma equivpartI[simp]: "equivpartp r x x"
  and sympartp_equivpartpI: "sympartp r x y \<Longrightarrow> equivpartp r x y"
  and equivpartpCI[intro]: "(x \<noteq> y \<Longrightarrow> sympartp r x y) \<Longrightarrow> equivpartp r x y"
  by (auto simp:equivpartp_def)

lemma equivpartpE[elim]:
  assumes "equivpartp r x y"
    and "x = y \<Longrightarrow> thesis"
    and "r x y \<Longrightarrow> r y x \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: equivpartp_def)

lemma equivpartp_eq[simp]: "equivpartp (=) = (=)" by auto

lemma sympartp_equivpartp[simp]: "sympartp (equivpartp r) = (equivpartp r)"
  and equivpartp_equivpartp[simp]: "equivpartp (equivpartp r) = (equivpartp r)"
  and equivpartp_sympartp[simp]: "equivpartp (sympartp r) = (equivpartp r)"
  by (auto 0 5 intro!:ext)

lemma equivpartp_dual: "equivpartp r\<^sup>- = equivpartp r"
  by (auto intro!:ext simp: equivpartp_def)

text \<open>The asymmetric part:\<close>

definition "asympartp r x y \<equiv> r x y \<and> \<not> r y x"

lemma asympartpE[elim]:
  fixes r (infix "\<sqsubseteq>" 50)
  shows "asympartp (\<sqsubseteq>) x y \<Longrightarrow> (x \<sqsubseteq> y \<Longrightarrow> \<not>y \<sqsubseteq> x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: asympartp_def)

lemmas asympartpI[intro] = asympartp_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp, rule_format] 

lemma asympartp_eq[simp]: "asympartp (=) = bot" by auto

lemma asympartp_sympartp [simp]: "asympartp (sympartp r) = bot"
  and sympartp_asympartp [simp]: "sympartp (asympartp r) = bot"
  by (auto intro!: ext)

lemma asympartp_dual: "asympartp r\<^sup>- = (asympartp r)\<^sup>-" by auto

text \<open>Restriction to a set:\<close>

definition Restrp (infixl "\<restriction>" 60) where "(r \<restriction> A) a b \<equiv> a \<in> A \<and> b \<in> A \<and> r a b"

lemmas RestrpI[intro!] = Restrp_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp]
lemmas RestrpE[elim!] = Restrp_def[unfolded atomize_eq, THEN iffD1, elim_format, unfolded conj_imp_eq_imp_imp]

lemma Restrp_simp[simp]: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> (r \<restriction> A) a b \<longleftrightarrow> r a b" by auto

lemma Restrp_UNIV[simp]: "r \<restriction> UNIV \<equiv> r" by (auto simp: atomize_eq)

lemma Restrp_Restrp[simp]: "r \<restriction> A \<restriction> B \<equiv> r \<restriction> A \<inter> B" by (auto simp: atomize_eq Restrp_def)

lemma sympartp_Restrp[simp]: "sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
  by (auto simp: atomize_eq)

text \<open>Relational images:\<close>
definition Imagep (infixr "```" 59) where "r ``` A \<equiv> {b. \<exists>a \<in> A. r a b}"

lemma Imagep_Image: "r ``` A = {(a,b). r a b} `` A"
  by (auto simp: Imagep_def)

lemma in_Imagep: "b \<in> r ``` A \<longleftrightarrow> (\<exists>a \<in> A. r a b)" by (auto simp: Imagep_def)

lemma ImagepI: "a \<in> A \<Longrightarrow> r a b \<Longrightarrow> b \<in> r ``` A" by (auto simp: in_Imagep)

lemma subset_Imagep: "B \<subseteq> r ``` A \<longleftrightarrow> (\<forall>b\<in>B. \<exists>a\<in>A. r a b)"
  by (auto simp: Imagep_def)

text \<open>Bounds of a set:\<close>
definition "bound X (\<sqsubseteq>) b \<equiv> \<forall>x \<in> X. x \<sqsubseteq> b" for r (infix "\<sqsubseteq>" 50)

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows boundI[intro!]: "(\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> bound X (\<sqsubseteq>) b"
    and boundE[elim]: "bound X (\<sqsubseteq>) b \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    and boundD: "bound X (\<sqsubseteq>) b \<Longrightarrow> a \<in> X \<Longrightarrow> a \<sqsubseteq> b"
  by (auto simp: bound_def)

lemma bound_empty: "bound {} = (\<lambda>r x. True)" by auto

lemma bound_cmono: assumes "X \<subseteq> Y" shows "bound Y \<le> bound X"
  using assms by auto

lemmas bound_subset = bound_cmono[THEN le_funD, THEN le_funD, THEN le_boolD, folded atomize_imp]

lemma bound_un: "bound (A \<union> B) = bound A \<sqinter> bound B"
  by auto

lemma bound_insert[simp]:
  fixes r (infix "\<sqsubseteq>" 50)
  shows "bound (insert x X) (\<sqsubseteq>) b \<longleftrightarrow> x \<sqsubseteq> b \<and> bound X (\<sqsubseteq>) b" by auto

lemma bound_cong:
  assumes "A = A'"
    and "b = b'"
    and "\<And>a. a \<in> A' \<Longrightarrow> le a b' = le' a b'"
  shows "bound A le b = bound A' le' b'"
  by (auto simp: assms)

lemma bound_subsel: "le \<le> le' \<Longrightarrow> bound A le \<le> bound A le'"
  by (auto simp add: bound_def)

text \<open>Extreme (greatest) elements in a set:\<close>
definition "extreme X (\<sqsubseteq>) e \<equiv> e \<in> X \<and> (\<forall>x \<in> X. x \<sqsubseteq> e)" for r (infix "\<sqsubseteq>" 50)

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows extremeI[intro]: "e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> extreme X (\<sqsubseteq>) e"
    and extremeD: "extreme X (\<sqsubseteq>) e \<Longrightarrow> e \<in> X" "extreme X (\<sqsubseteq>) e \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e)"
    and extremeE[elim]: "extreme X (\<sqsubseteq>) e \<Longrightarrow> (e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: extreme_def)

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows extreme_UNIV[simp]: "extreme UNIV (\<sqsubseteq>) t \<longleftrightarrow> (\<forall>x. x \<sqsubseteq> t)" by auto

lemma extreme_iff_bound: "extreme X r e \<longleftrightarrow> bound X r e \<and> e \<in> X" by auto

lemma extreme_imp_bound: "extreme X r x \<Longrightarrow> bound X r x" by auto

lemma extreme_inf: "extreme X (r \<sqinter> s) x \<longleftrightarrow> extreme X r x \<and> extreme X s x" by auto

lemma extremes_equiv: "extreme X r b \<Longrightarrow> extreme X r c \<Longrightarrow> sympartp r b c" by blast

lemma extreme_cong:
  assumes "A = A'"
    and "b = b'"
    and "\<And>a. a \<in> A' \<Longrightarrow> b' \<in> A' \<Longrightarrow> le a b' = le' a b'"
  shows "extreme A le b = extreme A' le' b'"
  by (auto simp: assms extreme_def)

lemma extreme_subset: "X \<subseteq> Y \<Longrightarrow> extreme X r x \<Longrightarrow> extreme Y r y \<Longrightarrow> r x y" by blast

lemma extreme_subrel:
  "le \<le> le' \<Longrightarrow> extreme A le \<le> extreme A le'" by (auto simp: extreme_def)

text \<open>Now suprema and infima are given uniformly as follows.
  The definition is restricted to a given set.
\<close>

definition
  "extreme_bound A (\<sqsubseteq>) X \<equiv> extreme {b \<in> A. bound X (\<sqsubseteq>) b} (\<sqsubseteq>)\<^sup>-" for r (infix "\<sqsubseteq>" 50)

lemmas extreme_boundI_extreme = extreme_bound_def[unfolded atomize_eq, THEN fun_cong, THEN iffD2]

lemmas extreme_boundD_extreme = extreme_bound_def[unfolded atomize_eq, THEN fun_cong, THEN iffD1]

context
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma extreme_boundI[intro]:
  assumes "\<And>b. bound X (\<sqsubseteq>) b \<Longrightarrow> b \<in> A \<Longrightarrow> s \<sqsubseteq> b" and "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> s" and "s \<in> A"
  shows "extreme_bound A (\<sqsubseteq>) X s"
  using assms by (auto simp: extreme_bound_def)

lemma extreme_boundD:
  assumes "extreme_bound A (\<sqsubseteq>) X s"
  shows "x \<in> X \<Longrightarrow> x \<sqsubseteq> s"
    and "bound X (\<sqsubseteq>) b \<Longrightarrow> b \<in> A \<Longrightarrow> s \<sqsubseteq> b"
    and extreme_bound_in: "s \<in> A"
  using assms by (auto simp: extreme_bound_def)

lemma extreme_boundE[elim]:
  assumes "extreme_bound A (\<sqsubseteq>) X s"
    and "s \<in> A \<Longrightarrow> bound X (\<sqsubseteq>) s \<Longrightarrow> (\<And>b. bound X (\<sqsubseteq>) b \<Longrightarrow> b \<in> A \<Longrightarrow> s \<sqsubseteq> b) \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: extreme_bound_def)

lemma extreme_bound_imp_bound: "extreme_bound A (\<sqsubseteq>) X s \<Longrightarrow> bound X (\<sqsubseteq>) s" by auto

lemma extreme_imp_extreme_bound:
  assumes Xs: "extreme X (\<sqsubseteq>) s" and XA: "X \<subseteq> A" shows "extreme_bound A (\<sqsubseteq>) X s"
  using assms by force

lemma extreme_bound_subset_bound:
  assumes XY: "X \<subseteq> Y"
    and sX: "extreme_bound A (\<sqsubseteq>) X s"
    and b: "bound Y (\<sqsubseteq>) b" and bA: "b \<in> A"
  shows "s \<sqsubseteq> b"
  using bound_subset[OF XY b] sX bA by auto

lemma extreme_bound_subset:
  assumes XY: "X \<subseteq> Y"
    and sX: "extreme_bound A (\<sqsubseteq>) X sX"
    and sY: "extreme_bound A (\<sqsubseteq>) Y sY"
  shows "sX \<sqsubseteq> sY"
  using extreme_bound_subset_bound[OF XY sX] sY by auto

lemma extreme_bound_iff:
  "extreme_bound A (\<sqsubseteq>) X s \<longleftrightarrow> s \<in> A \<and> (\<forall>c \<in> A. (\<forall>x \<in> X. x \<sqsubseteq> c) \<longrightarrow> s \<sqsubseteq> c) \<and> (\<forall>x \<in> X. x \<sqsubseteq> s)"
  by (auto simp: extreme_bound_def extreme_def)

lemma extreme_bound_empty: "extreme_bound A (\<sqsubseteq>) {} x \<longleftrightarrow> extreme A (\<sqsubseteq>)\<^sup>- x"
  by auto

lemma extreme_bound_singleton_refl[simp]:
  "extreme_bound A (\<sqsubseteq>) {x} x \<longleftrightarrow> x \<in> A \<and> x \<sqsubseteq> x" by auto

lemma extreme_bound_image_const:
  "x \<sqsubseteq> x \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i = x) \<Longrightarrow> x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` I) x"
  by (auto simp: image_constant)

lemma extreme_bound_UN_const:
  "x \<sqsubseteq> x \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i y. i \<in> I \<Longrightarrow> P i y \<longleftrightarrow> x = y) \<Longrightarrow> x \<in> A \<Longrightarrow>
  extreme_bound A (\<sqsubseteq>) (\<Union>i\<in>I. {y. P i y}) x"
  by auto

lemma extreme_bounds_equiv:
  assumes s: "extreme_bound A (\<sqsubseteq>) X s" and s': "extreme_bound A (\<sqsubseteq>) X s'"
  shows "sympartp (\<sqsubseteq>) s s'"
  using s s'
  apply (unfold extreme_bound_def)
  apply (subst sympartp_dual)
  by (rule extremes_equiv)

lemma extreme_bound_sqweeze:
  assumes XY: "X \<subseteq> Y" and YZ: "Y \<subseteq> Z"
    and Xs: "extreme_bound A (\<sqsubseteq>) X s" and Zs: "extreme_bound A (\<sqsubseteq>) Z s"
  shows "extreme_bound A (\<sqsubseteq>) Y s"
proof
  from Xs show "s \<in> A" by auto
  fix b assume Yb: "bound Y (\<sqsubseteq>) b" and bA: "b \<in> A"
  from bound_subset[OF XY Yb] have "bound X (\<sqsubseteq>) b".
  with Xs bA
  show "s \<sqsubseteq> b" by auto
next
  fix y assume yY: "y \<in> Y"
  with YZ have "y \<in> Z" by auto
  with Zs show "y \<sqsubseteq> s" by auto
qed

lemma bound_closed_imp_extreme_bound_eq_extreme:
  assumes closed: "\<forall>b \<in> A. bound X (\<sqsubseteq>) b \<longrightarrow> b \<in> X" and XA: "X \<subseteq> A"
  shows "extreme_bound A (\<sqsubseteq>) X = extreme X (\<sqsubseteq>)"
proof (intro ext iffI extreme_boundI extremeI)
  fix e
  assume "extreme_bound A (\<sqsubseteq>) X e"
  then have Xe: "bound X (\<sqsubseteq>) e" and "e \<in> A" by auto
  with closed show "e \<in> X" by auto
  fix x assume "x \<in> X"
  with Xe show "x \<sqsubseteq> e" by auto
next
  fix e
  assume Xe: "extreme X (\<sqsubseteq>) e"
  then have eX: "e \<in> X" by auto
  with XA show "e \<in> A" by auto
  { fix b assume Xb: "bound X (\<sqsubseteq>) b" and "b \<in> A"
    from eX Xb show "e \<sqsubseteq> b" by auto
  }
  fix x assume xX: "x \<in> X" with Xe show "x \<sqsubseteq> e" by auto
qed

end

lemma extreme_bound_cong:
  assumes "A = A'"
    and "X = X'"
    and "\<And>a b. a \<in> A' \<Longrightarrow> b \<in> A' \<Longrightarrow> le a b \<longleftrightarrow> le' a b"
    and "\<And>a b. a \<in> X' \<Longrightarrow> b \<in> A' \<Longrightarrow> le a b \<longleftrightarrow> le' a b"
  shows "extreme_bound A le X s = extreme_bound A le' X s"
  apply (unfold extreme_bound_def)
  apply (rule extreme_cong)
  by (auto simp: assms)


text \<open>Maximal or Minimal\<close>

definition "extremal X (\<sqsubseteq>) x \<equiv> x \<in> X \<and> (\<forall>y \<in> X. x \<sqsubseteq> y \<longrightarrow> y \<sqsubseteq> x)" for r (infix "\<sqsubseteq>" 50)

context
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma extremalI:
  assumes "x \<in> X" "\<And>y. y \<in> X \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x"
  shows "extremal X (\<sqsubseteq>) x"
  using assms by (auto simp: extremal_def)

lemma extremalE:
  assumes "extremal X (\<sqsubseteq>) x"
    and "x \<in> X \<Longrightarrow> (\<And>y. y \<in> X \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x) \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: extremal_def)

lemma extremalD:
  assumes "extremal X (\<sqsubseteq>) x" shows "x \<in> X" "y \<in> X \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x"
  using assms by (auto elim!: extremalE)

end

context
  fixes ir (infix "\<preceq>" 50) and r (infix "\<sqsubseteq>" 50) and I f
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f"
begin

lemma monotone_image_bound:
  assumes "X \<subseteq> I" and "b \<in> I" and "bound X (\<preceq>) b"
  shows "bound (f ` X) (\<sqsubseteq>) (f b)"
  using assms monotone_onD[OF mono]
  by (auto simp: bound_def)

lemma monotone_image_extreme:
  assumes e: "extreme I (\<preceq>) e"
  shows "extreme (f ` I) (\<sqsubseteq>) (f e)"
  using e[unfolded extreme_iff_bound] monotone_image_bound[of I e] by auto

end

context
  fixes ir :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50)
    and r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
    and f and A and e and I
  assumes fIA: "f ` I \<subseteq> A"
    and mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f"
    and e: "extreme I (\<preceq>) e"
begin

lemma monotone_extreme_imp_extreme_bound:
  "extreme_bound A (\<sqsubseteq>) (f ` I) (f e)"
  using monotone_onD[OF mono] e fIA
  by (intro extreme_boundI, auto simp: image_def elim!: extremeE)

lemma monotone_extreme_extreme_boundI:
  "x = f e \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` I) x"
  using monotone_extreme_imp_extreme_bound by auto

end

subsection \<open>Locales for Binary Relations\<close>

text \<open>We now define basic properties of binary relations,
in form of \emph{locales}~\cite{Kammuller00,locale}.\<close>

subsubsection \<open>Syntactic Locales\<close>

text \<open>The following locales do not assume anything, but provide infix notations for
relations.\<close>

locale less_eq_syntax =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

locale less_syntax =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)

locale equivalence_syntax =
  fixes equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sim>" 50)
begin

abbreviation equiv_class ("[_]\<^sub>\<sim>") where "[x]\<^sub>\<sim> \<equiv> { y. x \<sim> y }"

end

text \<open>Next ones introduce abbreviations for dual etc.
To avoid needless constants, one should be careful when declaring them as sublocales.\<close>

locale less_eq_dualize = less_eq_syntax
begin

abbreviation (input) greater_eq (infix "\<sqsupseteq>" 50) where "x \<sqsupseteq> y \<equiv> y \<sqsubseteq> x"

end

locale less_eq_symmetrize = less_eq_dualize
begin

abbreviation sym (infix "\<sim>" 50) where "(\<sim>) \<equiv> sympartp (\<sqsubseteq>)"
abbreviation equiv (infix "(\<simeq>)" 50) where "(\<simeq>) \<equiv> equivpartp (\<sqsubseteq>)"

end

locale less_eq_asymmetrize = less_eq_symmetrize
begin

abbreviation less (infix "\<sqsubset>" 50) where "(\<sqsubset>) \<equiv> asympartp (\<sqsubseteq>)"
abbreviation greater (infix "\<sqsupset>" 50) where "(\<sqsupset>) \<equiv> (\<sqsubset>)\<^sup>-"

lemma asym_cases[consumes 1, case_names asym sym]:
  assumes "x \<sqsubseteq> y" and "x \<sqsubset> y \<Longrightarrow> thesis" and "x \<sim> y \<Longrightarrow> thesis"
  shows thesis
  using assms by auto

end

locale less_dualize = less_syntax
begin

abbreviation (input) greater (infix "\<sqsupset>" 50) where "x \<sqsupset> y \<equiv> y \<sqsubset> x"

end

locale related_set =
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

subsubsection \<open>Basic Properties of Relations\<close>

text \<open>In the following we define basic properties in form of locales.\<close>

text \<open>Reflexivity restricted on a set:\<close>
locale reflexive = related_set +
  assumes refl[intro]: "x \<in> A \<Longrightarrow> x \<sqsubseteq> x"
begin

lemma eq_implies: "x = y \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> y" by auto

lemma reflexive_subset: "B \<subseteq> A \<Longrightarrow> reflexive B (\<sqsubseteq>)" apply unfold_locales by auto

lemma extreme_singleton[simp]: "x \<in> A \<Longrightarrow> extreme {x} (\<sqsubseteq>) y \<longleftrightarrow> x = y" by auto

lemma extreme_bound_singleton: "x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) {x} x" by auto

lemma extreme_bound_cone: "x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) {a \<in> A. a \<sqsubseteq> x} x" by auto

end

lemmas reflexiveI[intro!] = reflexive.intro

lemma reflexiveE[elim]:
  assumes "reflexive A r" and "(\<And>x. x \<in> A \<Longrightarrow> r x x) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: reflexive.refl)

lemma reflexive_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> reflexive A r \<longleftrightarrow> reflexive A r'"
  by (simp add: reflexive_def)

locale irreflexive = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes irrefl: "x \<in> A \<Longrightarrow> \<not> x \<sqsubset> x"
begin

lemma irreflD[simp]: "x \<sqsubset> x \<Longrightarrow> \<not>x \<in> A" by (auto simp: irrefl)

lemma implies_not_eq: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> x \<noteq> y" by auto

lemma Restrp_irreflexive: "irreflexive UNIV ((\<sqsubset>)\<restriction>A)"
  apply unfold_locales by auto

lemma irreflexive_subset: "B \<subseteq> A \<Longrightarrow> irreflexive B (\<sqsubset>)" apply unfold_locales by auto

end

lemmas irreflexiveI[intro!] = irreflexive.intro

lemma irreflexive_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> irreflexive A r \<longleftrightarrow> irreflexive A r'"
  by (simp add: irreflexive_def)

context reflexive begin

interpretation less_eq_asymmetrize.

lemma asympartp_irreflexive: "irreflexive A (\<sqsubset>)" by auto

end

locale transitive = related_set +
  assumes trans[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubseteq> z"
begin

lemma Restrp_transitive: "transitive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  by (auto intro: trans)

lemma bound_trans[trans]: "bound X (\<sqsubseteq>) b \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> X \<subseteq> A \<Longrightarrow> b \<in> A \<Longrightarrow> c \<in> A \<Longrightarrow> bound X (\<sqsubseteq>) c"
  by (auto 0 4 dest: trans)

lemma extreme_bound_mono:
  assumes XY: "\<forall>x\<in>X. \<exists>y\<in>Y. x \<sqsubseteq> y" and XA: "X \<subseteq> A" and YA: "Y \<subseteq> A"
    and sX: "extreme_bound A (\<sqsubseteq>) X sX"
    and sY: "extreme_bound A (\<sqsubseteq>) Y sY"
  shows "sX \<sqsubseteq> sY"
proof (intro extreme_boundD(2)[OF sX] CollectI conjI boundI)
  from sY show sYA: "sY \<in> A" by auto
  from sY have "bound Y (\<sqsubseteq>) sY" by auto
  fix x assume xX: "x \<in> X" with XY obtain y where yY: "y \<in> Y" and xy: "x \<sqsubseteq> y" by auto
  from yY sY have "y \<sqsubseteq> sY" by auto
  from trans[OF xy this] xX XA yY YA sYA show "x \<sqsubseteq> sY" by auto
qed

lemma transitive_subset:
  assumes BA: "B \<subseteq> A" shows "transitive B (\<sqsubseteq>)"
  apply unfold_locales
  using trans BA by blast

lemma asympartp_transitive: "transitive A (asympartp (\<sqsubseteq>))"
  apply unfold_locales by (auto dest:trans)

lemma reflclp_transitive: "transitive A (\<sqsubseteq>)\<^sup>=\<^sup>="
  apply unfold_locales by (auto dest: trans)

text \<open>The symmetric part is also transitive, but this is done in the later semiattractive locale\<close>

end

lemmas transitiveI = transitive.intro

lemma transitive_ball[code]:
  "transitive A (\<sqsubseteq>) \<longleftrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. x \<sqsubseteq> y \<longrightarrow> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z)"
  for less_eq (infix "\<sqsubseteq>" 50)
  by (auto simp: transitive_def)

lemma transitive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b" shows "transitive A r \<longleftrightarrow> transitive A r'"
proof (intro iffI)
  show "transitive A r \<Longrightarrow> transitive A r'"
    apply (intro transitive.intro)
    apply (unfold r[symmetric])
    using transitive.trans.
  show "transitive A r' \<Longrightarrow> transitive A r"
    apply (intro transitive.intro)
    apply (unfold r)
    using transitive.trans.
qed

lemma transitive_empty[intro!]: "transitive {} r" by (auto intro!: transitive.intro)

lemma tranclp_transitive: "transitive A (tranclp r)"
  using tranclp_trans by unfold_locales

locale symmetric = related_set A "(\<sim>)" for A and equiv (infix "\<sim>" 50) +
  assumes sym[sym]: "x \<sim> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<sim> x"
begin

lemma sym_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> y \<sim> x"
  by (auto dest: sym)

lemma Restrp_symmetric: "symmetric UNIV ((\<sim>)\<restriction>A)"
  apply unfold_locales by (auto simp: sym_iff)

lemma symmetric_subset: "B \<subseteq> A \<Longrightarrow> symmetric B (\<sim>)"
  apply unfold_locales by (auto dest: sym)

end

lemmas symmetricI[intro] = symmetric.intro

lemma symmetric_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> symmetric A r \<longleftrightarrow> symmetric A r'"
  by (auto simp: symmetric_def)

lemma symmetric_empty[intro!]: "symmetric {} r" by auto

global_interpretation sympartp: symmetric UNIV "sympartp r"
  rewrites "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  by auto

lemma sympartp_symmetric: "symmetric A (sympartp r)" by auto

locale antisymmetric = related_set +
  assumes antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y"
begin

interpretation less_eq_symmetrize.

lemma sym_iff_eq_refl: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> x = y \<and> y \<sqsubseteq> y" by (auto dest: antisym)

lemma equiv_iff_eq[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<simeq> y \<longleftrightarrow> x = y" by (auto dest: antisym elim: equivpartpE)

lemma extreme_unique: "X \<subseteq> A \<Longrightarrow> extreme X (\<sqsubseteq>) x \<Longrightarrow> extreme X (\<sqsubseteq>) y \<longleftrightarrow> x = y"
  by (elim extremeE, auto dest!: antisym[OF _ _ subsetD])

lemma ex_extreme_iff_ex1:
  "X \<subseteq> A \<Longrightarrow> Ex (extreme X (\<sqsubseteq>)) \<longleftrightarrow> Ex1 (extreme X (\<sqsubseteq>))" by (auto simp: extreme_unique)

lemma ex_extreme_iff_the:
   "X \<subseteq> A \<Longrightarrow> Ex (extreme X (\<sqsubseteq>)) \<longleftrightarrow> extreme X (\<sqsubseteq>) (The (extreme X (\<sqsubseteq>)))"
  apply (rule iffI)
  apply (rule theI')
  using extreme_unique by auto

lemma eq_The_extreme: "X \<subseteq> A \<Longrightarrow> extreme X (\<sqsubseteq>) x \<Longrightarrow> x = The (extreme X (\<sqsubseteq>))"
  by (rule the1_equality[symmetric], auto simp: ex_extreme_iff_ex1[symmetric])

lemma Restrp_antisymmetric: "antisymmetric UNIV ((\<sqsubseteq>)\<restriction>A)"
   apply unfold_locales
  by (auto dest: antisym)

lemma antisymmetric_subset: "B \<subseteq> A \<Longrightarrow> antisymmetric B (\<sqsubseteq>)"
  apply unfold_locales using antisym by auto

end

lemmas antisymmetricI[intro] = antisymmetric.intro

lemma antisymmetric_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> antisymmetric A r \<longleftrightarrow> antisymmetric A r'"
  by (auto simp: antisymmetric_def)

lemma antisymmetric_empty[intro!]: "antisymmetric {} r" by auto

lemma antisymmetric_union:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes A: "antisymmetric A (\<sqsubseteq>)" and B: "antisymmetric B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<longrightarrow> b \<sqsubseteq> a \<longrightarrow> a = b"
  shows "antisymmetric (A \<union> B) (\<sqsubseteq>)"
proof-
  interpret A: antisymmetric A "(\<sqsubseteq>)" using A.
  interpret B: antisymmetric B "(\<sqsubseteq>)" using B.
  show ?thesis by (auto dest: AB[rule_format] A.antisym B.antisym)
qed

text \<open>The following notion is new, generalizing antisymmetry and transitivity.\<close>

locale semiattractive = related_set +
  assumes attract: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubseteq> z"
begin

interpretation less_eq_symmetrize.

lemma equiv_order_trans[trans]:
  assumes xy: "x \<simeq> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using attract[OF _ _ _ x y z] xy yz by (auto elim: equivpartpE)

lemma equiv_transitive: "transitive A (\<simeq>)"
proof unfold_locales
  fix x y z
  assume x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A" and xy: "x \<simeq> y" and yz: "y \<simeq> z"
  show "x \<simeq> z"
    using equiv_order_trans[OF xy _ x y z] attract[OF _ _ _ z y x] xy yz by (auto simp:equivpartp_def)
qed

lemma sym_order_trans[trans]:
  assumes xy: "x \<sim> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using attract[OF _ _ _ x y z] xy yz by auto

interpretation sym: transitive A "(\<sim>)"
proof unfold_locales
  fix x y z
  assume x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A" and xy: "x \<sim> y" and yz: "y \<sim> z"
  show "x \<sim> z"
    using sym_order_trans[OF xy _ x y z] attract[OF _ _ _ z y x] xy yz by auto
qed

lemmas sym_transitive = sym.transitive_axioms

lemma extreme_bound_quasi_const:
  assumes C: "C \<subseteq> A" and x: "x \<in> A" and C0: "C \<noteq> {}" and const: "\<forall>y \<in> C. y \<sim> x"
  shows "extreme_bound A (\<sqsubseteq>) C x"
proof (intro extreme_boundI x)
  from C0 obtain c where cC: "c \<in> C" by auto
  with C have c: "c \<in> A" by auto
  from cC const have cx: "c \<sim> x" by auto
  fix b assume b: "b \<in> A" and "bound C (\<sqsubseteq>) b"
  with cC have cb: "c \<sqsubseteq> b" by auto
  from attract[OF _ _ cb x c b] cx show "x \<sqsubseteq> b" by auto
next
  fix c assume "c \<in> C"
  with const show "c \<sqsubseteq> x" by auto
qed

lemma extreme_bound_quasi_const_iff:
  assumes C: "C \<subseteq> A" and x: "x \<in> A" and y: "y \<in> A" and C0: "C \<noteq> {}" and const: "\<forall>z \<in> C. z \<sim> x"
  shows "extreme_bound A (\<sqsubseteq>) C y \<longleftrightarrow> x \<sim> y"
proof (intro iffI)
  assume y: "extreme_bound A (\<sqsubseteq>) C y"
  note x = extreme_bound_quasi_const[OF C x C0 const]
  from extreme_bounds_equiv[OF y x]
  show "x \<sim> y" by auto
next
  assume xy: "x \<sim> y"
  with const C sym.trans[OF _ xy _ x y] have Cy: "\<forall>z \<in> C. z \<sim> y" by auto
  show "extreme_bound A (\<sqsubseteq>) C y"
    using extreme_bound_quasi_const[OF C y C0 Cy].
qed

lemma Restrp_semiattractive: "semiattractive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  by (auto dest: attract)

lemma semiattractive_subset: "B \<subseteq> A \<Longrightarrow> semiattractive B (\<sqsubseteq>)"
  apply unfold_locales using attract by blast

end

lemmas semiattractiveI = semiattractive.intro

lemma semiattractive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiattractive A r \<longleftrightarrow> semiattractive A r'" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (intro semiattractive.intro)
    apply (unfold r[symmetric])
    using semiattractive.attract.
  show "?r \<Longrightarrow> ?l"
    apply (intro semiattractive.intro)
    apply (unfold r)
    using semiattractive.attract.
qed

lemma semiattractive_empty[intro!]: "semiattractive {} r"
  by (auto intro!: semiattractiveI)

locale attractive = semiattractive +
  assumes "semiattractive A (\<sqsubseteq>)\<^sup>-"
begin

interpretation less_eq_symmetrize.

sublocale dual: semiattractive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "sympartp ((\<sqsubseteq>) \<restriction> A)\<^sup>- \<equiv> (\<sim>) \<restriction> A"
    and "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> (\<sim>)"
    and "equivpartp (\<sqsubseteq>)\<^sup>- \<equiv> (\<simeq>)"
  using attractive_axioms[unfolded attractive_def]
  by (auto intro!: ext simp: attractive_axioms_def atomize_eq equivpartp_def)

lemma order_equiv_trans[trans]:
  assumes xy: "x \<sqsubseteq> y" and yz: "y \<simeq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using dual.attract[OF _ _ _ z y x] xy yz by auto

lemma order_sym_trans[trans]:
  assumes xy: "x \<sqsubseteq> y" and yz: "y \<sim> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using dual.attract[OF _ _ _ z y x] xy yz by auto

lemma extreme_bound_sym_trans:
  assumes XA: "X \<subseteq> A" and Xx: "extreme_bound A (\<sqsubseteq>) X x"
    and xy: "x \<sim> y" and yA: "y \<in> A"
  shows "extreme_bound A (\<sqsubseteq>) X y"
proof (intro extreme_boundI yA)
  from Xx have xA: "x \<in> A" by auto
  {
    fix b assume Xb: "bound X (\<sqsubseteq>) b" and bA: "b \<in> A"
    with Xx have xb: "x \<sqsubseteq> b" by auto
    from sym_order_trans[OF _ xb yA xA bA] xy show "y \<sqsubseteq> b" by auto
  }
  fix a assume aX: "a \<in> X"
  with Xx have ax: "a \<sqsubseteq> x" by auto
  from aX XA have aA: "a \<in> A" by auto
  from order_sym_trans[OF ax xy aA xA yA] show "a \<sqsubseteq> y" by auto
qed

interpretation Restrp: semiattractive UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_semiattractive.
interpretation dual.Restrp: semiattractive UNIV "(\<sqsubseteq>)\<^sup>-\<restriction>A" using dual.Restrp_semiattractive.

lemma Restrp_attractive: "attractive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  using dual.Restrp.attract by auto

lemma attractive_subset: "B \<subseteq> A \<Longrightarrow> attractive B (\<sqsubseteq>)"
  apply (intro attractive.intro attractive_axioms.intro)
  using semiattractive_subset dual.semiattractive_subset by auto

end

lemmas attractiveI = attractive.intro[OF _ attractive_axioms.intro]

lemma attractive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "attractive A r \<longleftrightarrow> attractive A r'"
  by (simp add: attractive_def attractive_axioms_def r cong: semiattractive_cong)

lemma attractive_empty[intro!]: "attractive {} r"
  by (auto intro!: attractiveI)

context antisymmetric begin

sublocale attractive
  apply unfold_locales by (auto dest: antisym)

end

context transitive begin

sublocale attractive
  rewrites "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "(sympartp (\<sqsubseteq>))\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "(sympartp (\<sqsubseteq>) \<restriction> A)\<^sup>- \<equiv> sympartp (\<sqsubseteq>) \<restriction> A"
    and "asympartp (asympartp (\<sqsubseteq>)) = asympartp (\<sqsubseteq>)"
    and "asympartp (sympartp (\<sqsubseteq>)) = bot"
    and "asympartp (\<sqsubseteq>) \<restriction> A = asympartp ((\<sqsubseteq>) \<restriction> A)"
  apply unfold_locales
  by (auto intro!:ext dest: trans simp: atomize_eq)

end

subsection \<open>Combined Properties\<close>

text \<open>Some combinations of the above basic properties are given names.\<close>

locale asymmetric = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes asym: "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> False"
begin

sublocale irreflexive
  apply unfold_locales by (auto dest: asym)

lemma antisymmetric_axioms: "antisymmetric A (\<sqsubset>)"
  apply unfold_locales by (auto dest: asym)

lemma Restrp_asymmetric: "asymmetric UNIV ((\<sqsubset>)\<restriction>A)"
  apply unfold_locales
  by (auto dest:asym)

lemma asymmetric_subset: "B \<subseteq> A \<Longrightarrow> asymmetric B (\<sqsubset>)"
  apply unfold_locales using asym by auto

end

lemmas asymmetricI = asymmetric.intro

lemma asymmetric_iff_irreflexive_antisymmetric:
  fixes less (infix "\<sqsubset>" 50)
  shows "asymmetric A (\<sqsubset>) \<longleftrightarrow> irreflexive A (\<sqsubset>) \<and> antisymmetric A (\<sqsubset>)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then interpret asymmetric.
  show ?r by (auto dest: asym)
next
  assume ?r
  then interpret irreflexive + antisymmetric A "(\<sqsubset>)" by auto
  show ?l by (auto intro!:asymmetricI dest: antisym irrefl)
qed

lemma asymmetric_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "asymmetric A r \<longleftrightarrow> asymmetric A r'"
  by (simp add: asymmetric_iff_irreflexive_antisymmetric r cong: irreflexive_cong antisymmetric_cong)

lemma asymmetric_empty: "asymmetric {} r"
  by (auto simp: asymmetric_iff_irreflexive_antisymmetric)

locale quasi_ordered_set = reflexive + transitive
begin

lemma quasi_ordered_subset: "B \<subseteq> A \<Longrightarrow> quasi_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset transitive_subset by auto

end

lemmas quasi_ordered_setI = quasi_ordered_set.intro

lemma quasi_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "quasi_ordered_set A r \<longleftrightarrow> quasi_ordered_set A r'"
  by (simp add: quasi_ordered_set_def r cong: reflexive_cong transitive_cong)

lemma quasi_ordered_set_empty[intro!]: "quasi_ordered_set {} r"
  by (auto intro!: quasi_ordered_set.intro)

lemma rtranclp_quasi_ordered: "quasi_ordered_set A (rtranclp r)"
  by (unfold_locales, auto)

locale near_ordered_set = antisymmetric + transitive
begin

interpretation Restrp: antisymmetric UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_antisymmetric.
interpretation Restrp: transitive UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_transitive.

lemma Restrp_near_order: "near_ordered_set UNIV ((\<sqsubseteq>)\<restriction>A)"..

lemma near_ordered_subset: "B \<subseteq> A \<Longrightarrow> near_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using antisymmetric_subset transitive_subset by auto

end

lemmas near_ordered_setI = near_ordered_set.intro

lemma near_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "near_ordered_set A r \<longleftrightarrow> near_ordered_set A r'"
  by (simp add: near_ordered_set_def r cong: antisymmetric_cong transitive_cong)

lemma near_ordered_set_empty[intro!]: "near_ordered_set {} r"
  by (auto intro!: near_ordered_set.intro)

locale pseudo_ordered_set = reflexive + antisymmetric
begin

interpretation less_eq_symmetrize.

lemma sym_eq[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> x = y"
  by (auto simp: refl dest: antisym)

lemma extreme_bound_singleton_eq[simp]: "x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) {x} y \<longleftrightarrow> x = y"
  by (auto intro!: antisym)

lemma eq_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x" by (auto dest: antisym simp:refl)

lemma extreme_order_iff_eq: "e \<in> A \<Longrightarrow> extreme {x \<in> A. x \<sqsubseteq> e} (\<sqsubseteq>) s \<longleftrightarrow> e = s"
  by (auto intro!: antisym)

lemma pseudo_ordered_subset: "B \<subseteq> A \<Longrightarrow> pseudo_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset antisymmetric_subset by auto

end

lemmas pseudo_ordered_setI = pseudo_ordered_set.intro

lemma pseudo_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "pseudo_ordered_set A r \<longleftrightarrow> pseudo_ordered_set A r'"
  by (simp add: pseudo_ordered_set_def r cong: reflexive_cong antisymmetric_cong)

lemma pseudo_ordered_set_empty[intro!]: "pseudo_ordered_set {} r"
  by (auto intro!: pseudo_ordered_setI)

locale partially_ordered_set = reflexive + antisymmetric + transitive
begin

sublocale pseudo_ordered_set + quasi_ordered_set + near_ordered_set ..

lemma partially_ordered_subset: "B \<subseteq> A \<Longrightarrow> partially_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset transitive_subset antisymmetric_subset by auto

end

lemmas partially_ordered_setI = partially_ordered_set.intro

lemma partially_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "partially_ordered_set A r \<longleftrightarrow> partially_ordered_set A r'"
  by (simp add: partially_ordered_set_def r cong: reflexive_cong antisymmetric_cong transitive_cong)

lemma partially_ordered_set_empty[intro!]: "partially_ordered_set {} r"
  by (auto intro!: partially_ordered_setI)

locale strict_ordered_set = irreflexive + transitive A "(\<sqsubset>)"
begin

sublocale asymmetric
proof
  fix x y
  assume x: "x \<in> A" and y: "y \<in> A"
  assume xy: "x \<sqsubset> y"
  also assume yx: "y \<sqsubset> x"
  finally have "x \<sqsubset> x" using x y by auto
  with x show False by auto
qed

lemma near_ordered_set_axioms: "near_ordered_set A (\<sqsubset>)"
  using antisymmetric_axioms by intro_locales

interpretation Restrp: asymmetric UNIV "(\<sqsubset>)\<restriction>A" using Restrp_asymmetric.
interpretation Restrp: transitive UNIV "(\<sqsubset>)\<restriction>A" using Restrp_transitive.

lemma Restrp_strict_order: "strict_ordered_set UNIV ((\<sqsubset>)\<restriction>A)"..

lemma strict_ordered_subset: "B \<subseteq> A \<Longrightarrow> strict_ordered_set B (\<sqsubset>)"
  apply intro_locales
  using irreflexive_subset transitive_subset by auto

end

lemmas strict_ordered_setI = strict_ordered_set.intro

lemma strict_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "strict_ordered_set A r \<longleftrightarrow> strict_ordered_set A r'"
  by (simp add: strict_ordered_set_def r cong: irreflexive_cong transitive_cong)

lemma strict_ordered_set_empty[intro!]: "strict_ordered_set {} r"
  by (auto intro!: strict_ordered_set.intro)

locale tolerance = symmetric + reflexive A "(\<sim>)"
begin

lemma tolerance_subset: "B \<subseteq> A \<Longrightarrow> tolerance B (\<sim>)"
  apply intro_locales
  using symmetric_subset reflexive_subset by auto

end

lemmas toleranceI = tolerance.intro

lemma tolerance_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "tolerance A r \<longleftrightarrow> tolerance A r'"
  by (simp add: tolerance_def r cong: reflexive_cong symmetric_cong)

lemma tolerance_empty[intro!]: "tolerance {} r" by (auto intro!: toleranceI)

global_interpretation equiv: tolerance UNIV "equivpartp r"
  rewrites "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  by unfold_locales (auto simp:equivpartp_def)

locale partial_equivalence = symmetric +
  assumes "transitive A (\<sim>)"
begin

sublocale transitive A "(\<sim>)"
  rewrites "sympartp (\<sim>)\<restriction>A \<equiv> (\<sim>)\<restriction>A"
    and "sympartp ((\<sim>)\<restriction>A) \<equiv> (\<sim>)\<restriction>A"
  using partial_equivalence_axioms
  unfolding partial_equivalence_axioms_def partial_equivalence_def
  by (auto simp: atomize_eq sym intro!:ext)

lemma partial_equivalence_subset: "B \<subseteq> A \<Longrightarrow> partial_equivalence B (\<sim>)"
  apply (intro partial_equivalence.intro partial_equivalence_axioms.intro)
  using symmetric_subset transitive_subset by auto

end

lemmas partial_equivalenceI = partial_equivalence.intro[OF _ partial_equivalence_axioms.intro]

lemma partial_equivalence_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "partial_equivalence A r \<longleftrightarrow> partial_equivalence A r'"
  by (simp add: partial_equivalence_def partial_equivalence_axioms_def r
      cong: transitive_cong symmetric_cong)

lemma partial_equivalence_empty[intro!]: "partial_equivalence {} r"
  by (auto intro!: partial_equivalenceI)

locale equivalence = symmetric + reflexive A "(\<sim>)" + transitive A "(\<sim>)"
begin

sublocale tolerance + partial_equivalence + quasi_ordered_set A "(\<sim>)"..

lemma equivalence_subset: "B \<subseteq> A \<Longrightarrow> equivalence B (\<sim>)"
  apply (intro equivalence.intro)
  using symmetric_subset transitive_subset by auto

end

lemmas equivalenceI = equivalence.intro

lemma equivalence_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "equivalence A r \<longleftrightarrow> equivalence A r'"
  by (simp add: equivalence_def r cong: reflexive_cong transitive_cong symmetric_cong)

text \<open>Some combinations lead to uninteresting relations.\<close>

context
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bowtie>" 50)
begin

proposition reflexive_irreflexive_is_empty:
  assumes r: "reflexive A (\<bowtie>)" and ir: "irreflexive A (\<bowtie>)"
  shows "A = {}"
proof (rule ccontr)
  interpret irreflexive A "(\<bowtie>)" using ir.
  interpret reflexive A "(\<bowtie>)" using r.
  assume "A \<noteq> {}"
  then obtain a where a: "a \<in> A" by auto
  from a refl have "a \<bowtie> a" by auto
  with irrefl a show False by auto
qed

proposition symmetric_antisymmetric_imp_eq:
  assumes s: "symmetric A (\<bowtie>)" and as: "antisymmetric A (\<bowtie>)"
  shows "(\<bowtie>)\<restriction>A \<le> (=)"
proof-
  interpret symmetric A "(\<bowtie>)" + antisymmetric A "(\<bowtie>)" using assms by auto
  show "?thesis" using antisym by (auto dest: sym)
qed

proposition nontolerance:
  shows "irreflexive A (\<bowtie>) \<and> symmetric A (\<bowtie>) \<longleftrightarrow> tolerance A (\<lambda>x y. \<not> x \<bowtie> y)"
proof (intro iffI conjI, elim conjE)
  assume "irreflexive A (\<bowtie>)" and "symmetric A (\<bowtie>)"
  then interpret irreflexive A "(\<bowtie>)" + symmetric A "(\<bowtie>)".
  show "tolerance A (\<lambda>x y. \<not> x \<bowtie> y)" by (unfold_locales, auto dest: sym irrefl)
next
  assume "tolerance A (\<lambda>x y. \<not> x \<bowtie> y)"
  then interpret tolerance A "\<lambda>x y. \<not> x \<bowtie> y".
  show "irreflexive A (\<bowtie>)" by (auto simp: eq_implies)
  show "symmetric A (\<bowtie>)" using sym by auto
qed

proposition irreflexive_transitive_symmetric_is_empty:
  assumes irr: "irreflexive A (\<bowtie>)" and tr: "transitive A (\<bowtie>)" and sym: "symmetric A (\<bowtie>)"
  shows "(\<bowtie>)\<restriction>A = bot"
proof (intro ext, unfold bot_fun_def bot_bool_def eq_False, rule notI, erule RestrpE)
  interpret strict_ordered_set A "(\<bowtie>)" using assms by (unfold strict_ordered_set_def, auto)
  interpret symmetric A "(\<bowtie>)" using assms by auto
  fix x y assume x: "x \<in> A" and y: "y \<in> A"
  assume xy: "x \<bowtie> y"
  also note sym[OF xy x y]
  finally have "x \<bowtie> x" using x y by auto
  with x show False by auto
qed

end

subsection \<open>Totality\<close>

locale semiconnex = related_set _ "(\<sqsubset>)" + less_syntax +
  assumes semiconnex: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
begin

lemma cases[consumes 2, case_names less eq greater]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubset> y \<Longrightarrow> P" and "x = y \<Longrightarrow> P" and "y \<sqsubset> x \<Longrightarrow> P"
  shows "P" using semiconnex assms by auto

lemma neqE:
  assumes "x \<in> A" and "y \<in> A"
  shows "x \<noteq> y \<Longrightarrow> (x \<sqsubset> y \<Longrightarrow> P) \<Longrightarrow> (y \<sqsubset> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases rule: cases[OF assms], auto)

lemma semiconnex_subset: "B \<subseteq> A \<Longrightarrow> semiconnex B (\<sqsubset>)"
  apply (intro semiconnex.intro)
  using semiconnex by auto

end

lemmas semiconnexI[intro] = semiconnex.intro

text \<open>Totality is negated antisymmetry \cite[Proposition 2.2.4]{Schmidt1993}.\<close>
proposition semiconnex_iff_neg_antisymmetric:
  fixes less (infix "\<sqsubset>" 50)
  shows "semiconnex A (\<sqsubset>) \<longleftrightarrow> antisymmetric A (\<lambda>x y. \<not> x \<sqsubset> y)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI semiconnexI antisymmetricI)
  assume ?l
  then interpret semiconnex.
  fix x y
  assume "x \<in> A" "y \<in> A" "\<not> x \<sqsubset> y" and "\<not> y \<sqsubset> x"
  then show "x = y" by (cases rule: cases, auto)
next
  assume ?r
  then interpret neg: antisymmetric A "(\<lambda>x y. \<not> x \<sqsubset> y)".
  fix x y
  show "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" using neg.antisym by auto
qed

lemma semiconnex_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiconnex A r \<longleftrightarrow> semiconnex A r'"
  by (simp add: semiconnex_iff_neg_antisymmetric r cong: antisymmetric_cong)

locale semiconnex_irreflexive = semiconnex + irreflexive
begin

lemma neq_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<longleftrightarrow> x \<sqsubset> y \<or> y \<sqsubset> x" by (auto elim:neqE dest: irrefl)

lemma semiconnex_irreflexive_subset: "B \<subseteq> A \<Longrightarrow> semiconnex_irreflexive B (\<sqsubset>)"
  apply (intro semiconnex_irreflexive.intro)
  using semiconnex_subset irreflexive_subset by auto

end

lemmas semiconnex_irreflexiveI = semiconnex_irreflexive.intro

lemma semiconnex_irreflexive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiconnex_irreflexive A r \<longleftrightarrow> semiconnex_irreflexive A r'"
  by (simp add: semiconnex_irreflexive_def r cong: semiconnex_cong irreflexive_cong)

locale connex = related_set +
  assumes comparable: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
begin

interpretation less_eq_asymmetrize.

sublocale reflexive apply unfold_locales using comparable by auto

lemma comparable_cases[consumes 2, case_names le ge]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubseteq> y \<Longrightarrow> P" and "y \<sqsubseteq> x \<Longrightarrow> P" shows "P"
  using assms comparable by auto

lemma comparable_three_cases[consumes 2, case_names less eq greater]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubset> y \<Longrightarrow> P" and "x \<sim> y \<Longrightarrow> P" and "y \<sqsubset> x \<Longrightarrow> P" shows "P"
  using assms comparable by auto

lemma
  assumes x: "x \<in> A" and y: "y \<in> A"
  shows not_iff_asym: "\<not>x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
    and not_asym_iff: "\<not>x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  using comparable[OF x y] by auto

lemma connex_subset: "B \<subseteq> A \<Longrightarrow> connex B (\<sqsubseteq>)"
  by (intro connex.intro comparable, auto)

interpretation less_eq_asymmetrize.

end

lemmas connexI[intro] = connex.intro

lemmas connexE = connex.comparable_cases

lemma connex_empty: "connex {} A" by auto

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma connex_iff_semiconnex_reflexive: "connex A (\<sqsubseteq>) \<longleftrightarrow> semiconnex A (\<sqsubseteq>) \<and> reflexive A (\<sqsubseteq>)"
  (is "?c \<longleftrightarrow> ?t \<and> ?r")
proof (intro iffI conjI; (elim conjE)?)
  assume ?c then interpret connex.
  show ?t apply unfold_locales using comparable by auto
  show ?r by unfold_locales
next
  assume ?t then interpret semiconnex A "(\<sqsubseteq>)".
  assume ?r then interpret reflexive.
  from semiconnex show ?c by auto
qed

lemma chain_connect: "Complete_Partial_Order.chain r A \<equiv> connex A r"
  by (auto intro!: ext simp: atomize_eq connex_def Complete_Partial_Order.chain_def)

lemma connex_union:
  assumes "connex X (\<sqsubseteq>)" and "connex Y (\<sqsubseteq>)" and "\<forall>x \<in> X. \<forall>y \<in> Y. x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  shows "connex (X\<union>Y) (\<sqsubseteq>)"
  using assms by (auto simp: connex_def)

end

lemma connex_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "connex A r \<longleftrightarrow> connex A r'"
  by (simp add: connex_iff_semiconnex_reflexive r cong: semiconnex_cong reflexive_cong)

locale total_pseudo_ordered_set = connex + antisymmetric
begin

sublocale pseudo_ordered_set ..

lemma not_weak_iff:
  assumes x: "x \<in> A" and y: "y \<in> A" shows "\<not> y \<sqsubseteq> x \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
using x y by (cases rule: comparable_cases, auto intro:antisym)

lemma total_pseudo_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_pseudo_ordered_set B (\<sqsubseteq>)"
  apply (intro_locales)
  using antisymmetric_subset connex_subset by auto

interpretation less_eq_asymmetrize.

interpretation asympartp: semiconnex_irreflexive A "(\<sqsubset>)"
proof (intro semiconnex_irreflexive.intro asympartp_irreflexive semiconnexI)
  fix x y assume xA: "x \<in> A" and yA: "y \<in> A"
  with comparable antisym
  show "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" by (auto simp: asympartp_def)
qed

lemmas asympartp_semiconnex = asympartp.semiconnex_axioms
lemmas asympartp_semiconnex_irreflexive = asympartp.semiconnex_irreflexive_axioms

end

lemmas total_pseudo_ordered_setI = total_pseudo_ordered_set.intro

lemma total_pseudo_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_pseudo_ordered_set A r \<longleftrightarrow> total_pseudo_ordered_set A r'"
  by (simp add: total_pseudo_ordered_set_def r cong: connex_cong antisymmetric_cong)

locale total_quasi_ordered_set = connex + transitive
begin

sublocale quasi_ordered_set ..

lemma total_quasi_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_quasi_ordered_set B (\<sqsubseteq>)"
  using transitive_subset connex_subset by intro_locales

end

lemmas total_quasi_ordered_setI = total_quasi_ordered_set.intro

lemma total_quasi_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_quasi_ordered_set A r \<longleftrightarrow> total_quasi_ordered_set A r'"
  by (simp add: total_quasi_ordered_set_def r cong: connex_cong transitive_cong)

locale total_ordered_set = total_quasi_ordered_set + antisymmetric
begin

sublocale partially_ordered_set + total_pseudo_ordered_set ..

lemma total_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_ordered_set B (\<sqsubseteq>)"
  using total_quasi_ordered_subset antisymmetric_subset by (intro total_ordered_set.intro)

lemma weak_semiconnex: "semiconnex A (\<sqsubseteq>)"
  using connex_axioms by (simp add: connex_iff_semiconnex_reflexive)

interpretation less_eq_asymmetrize.

end

lemmas total_ordered_setI = total_ordered_set.intro[OF total_quasi_ordered_setI]

lemma total_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_ordered_set A r \<longleftrightarrow> total_ordered_set A r'"
  by (simp add: total_ordered_set_def r cong: total_quasi_ordered_set_cong antisymmetric_cong)


lemma monotone_connex_image:
  fixes ir (infix "\<preceq>" 50) and r (infix "\<sqsubseteq>" 50)
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f" and connex: "connex I (\<preceq>)"
  shows "connex (f ` I) (\<sqsubseteq>)"
proof (rule connexI)
  fix x y
  assume "x \<in> f ` I" and "y \<in> f ` I"
  then obtain i j where ij: "i \<in> I" "j \<in> I" and [simp]: "x = f i" "y = f j" by auto
  from connex ij have "i \<preceq> j \<or> j \<preceq> i" by (auto elim: connexE)
  with ij mono show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by (elim disjE, auto dest: monotone_onD) 
qed

subsection \<open>Order Pairs\<close>

text \<open>We pair a relation (weak part) with a well-behaving ``strict'' part. Here no assumption is
 put on the ``weak'' part.\<close>

locale compatible_ordering =
  related_set + irreflexive +
  assumes strict_implies_weak: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq> y"
  assumes weak_strict_trans[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
  assumes strict_weak_trans[trans]: "x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
begin

text \<open>The following sequence of declarations are in order to obtain fact names in a manner
similar to the Isabelle/HOL facts of orders.\<close>

text \<open>The strict part is necessarily transitive.\<close>

sublocale strict: transitive A "(\<sqsubset>)"
  using weak_strict_trans[OF strict_implies_weak] by unfold_locales

sublocale strict_ordered_set A "(\<sqsubset>)" ..

thm strict.trans asym irrefl

lemma Restrp_compatible_ordering: "compatible_ordering UNIV ((\<sqsubseteq>)\<restriction>A) ((\<sqsubset>)\<restriction>A)"
  apply (unfold_locales)
  by (auto dest: weak_strict_trans strict_weak_trans strict_implies_weak)

lemma strict_implies_not_weak: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> y \<sqsubseteq> x"
  using irrefl weak_strict_trans by blast

lemma weak_implies_not_strict:
  assumes xy: "x \<sqsubseteq> y" and [simp]: "x \<in> A" "y \<in> A"
  shows "\<not>y \<sqsubset> x"
proof 
  assume "y \<sqsubset> x"
  also note xy
  finally show False using irrefl by auto
qed

lemma compatible_ordering_subset: assumes "X \<subseteq> A" shows "compatible_ordering X (\<sqsubseteq>) (\<sqsubset>)"
  apply unfold_locales
  using assms strict_implies_weak by (auto intro: strict_weak_trans weak_strict_trans)

end

context transitive begin

interpretation less_eq_asymmetrize.

lemma asym_trans[trans]:
  shows "x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
    and "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
  by (auto 0 3 dest: trans)

lemma asympartp_compatible_ordering: "compatible_ordering A (\<sqsubseteq>) (\<sqsubset>)"
  apply unfold_locales
  by (auto dest: asym_trans)

end

locale reflexive_ordering = reflexive + compatible_ordering

locale reflexive_attractive_ordering = reflexive_ordering + attractive

locale pseudo_ordering = pseudo_ordered_set + compatible_ordering
begin

sublocale reflexive_attractive_ordering..

end

locale quasi_ordering = quasi_ordered_set + compatible_ordering
begin

sublocale reflexive_attractive_ordering..

lemma quasi_ordering_subset: assumes "X \<subseteq> A" shows "quasi_ordering X (\<sqsubseteq>) (\<sqsubset>)"
  by (intro quasi_ordering.intro quasi_ordered_subset compatible_ordering_subset assms)

end

context quasi_ordered_set begin

interpretation less_eq_asymmetrize.

lemma asympartp_quasi_ordering: "quasi_ordering A (\<sqsubseteq>) (\<sqsubset>)"
  by (intro quasi_ordering.intro quasi_ordered_set_axioms asympartp_compatible_ordering)

end

locale partial_ordering = partially_ordered_set + compatible_ordering
begin

sublocale quasi_ordering + pseudo_ordering..

lemma partial_ordering_subset: assumes "X \<subseteq> A" shows "partial_ordering X (\<sqsubseteq>) (\<sqsubset>)"
  by (intro partial_ordering.intro partially_ordered_subset compatible_ordering_subset assms)

end

context partially_ordered_set begin

interpretation less_eq_asymmetrize.

lemma asympartp_partial_ordering: "partial_ordering A (\<sqsubseteq>) (\<sqsubset>)"
  by (intro partial_ordering.intro partially_ordered_set_axioms asympartp_compatible_ordering)

end

locale total_quasi_ordering = total_quasi_ordered_set + compatible_ordering
begin

sublocale quasi_ordering..

lemma total_quasi_ordering_subset: assumes "X \<subseteq> A" shows "total_quasi_ordering X (\<sqsubseteq>) (\<sqsubset>)"
  by (intro total_quasi_ordering.intro total_quasi_ordered_subset compatible_ordering_subset assms)

end

context total_quasi_ordered_set begin

interpretation less_eq_asymmetrize.

lemma asympartp_total_quasi_ordering: "total_quasi_ordering A (\<sqsubseteq>) (\<sqsubset>)"
  by (intro total_quasi_ordering.intro total_quasi_ordered_set_axioms asympartp_compatible_ordering)

end


text \<open>Fixing the definition of the strict part is very common, though it looks restrictive
to the author.\<close>
locale strict_quasi_ordering = quasi_ordered_set + less_syntax +
  assumes strict_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> \<not>y \<sqsubseteq> x"
begin

sublocale compatible_ordering
proof unfold_locales
  fix x y z
  show "x \<in> A \<Longrightarrow> \<not> x \<sqsubset> x" by (auto simp: strict_iff)
  { assume xy: "x \<sqsubseteq> y" and yz: "y \<sqsubset> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
    from yz y z have ywz: "y \<sqsubseteq> z" and zy: "\<not>z \<sqsubseteq> y" by (auto simp: strict_iff)
    from trans[OF xy ywz]x y z have xz: "x \<sqsubseteq> z" by auto
    from trans[OF _ xy] x y z zy have zx: "\<not>z \<sqsubseteq> x" by auto 
    from xz zx x z show "x \<sqsubset> z" by (auto simp: strict_iff)
  }
  { assume xy: "x \<sqsubset> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
    from xy x y have xwy: "x \<sqsubseteq> y" and yx: "\<not>y \<sqsubseteq> x" by (auto simp: strict_iff)
    from trans[OF xwy yz]x y z have xz: "x \<sqsubseteq> z" by auto
    from trans[OF yz] x y z yx have zx: "\<not>z \<sqsubseteq> x" by auto 
    from xz zx x z show "x \<sqsubset> z" by (auto simp: strict_iff)
  }
  { show "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq> y" by (auto simp: strict_iff) }
qed

end

locale strict_partial_ordering = strict_quasi_ordering + antisymmetric
begin

sublocale partial_ordering..

lemma strict_iff_neq: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  by (auto simp: strict_iff antisym)

end

locale total_ordering = reflexive + compatible_ordering + semiconnex A "(\<sqsubset>)"
begin

sublocale semiconnex_irreflexive ..

sublocale connex
proof
  fix x y assume x: "x \<in> A" and y: "y \<in> A"
  then show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
    by (cases rule: cases, auto dest: strict_implies_weak)
qed

lemma not_weak:
  assumes "x \<in> A" and "y \<in> A" shows "\<not> x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
  using assms by (cases rule:cases, auto simp: strict_implies_not_weak dest: strict_implies_weak)

lemma not_strict: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  using not_weak by blast

sublocale strict_partial_ordering
proof
  fix a b
  assume a: "a \<in> A" and b: "b \<in> A"
  then show "a \<sqsubset> b \<longleftrightarrow> a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a" by (auto simp: not_strict[symmetric] dest: asym)
next
  fix x y z assume xy: "x \<sqsubseteq> y" and yz: "y \<sqsubseteq> z" and xA: "x \<in> A" and yA: "y \<in> A" and zA: "z \<in> A"
  with weak_strict_trans[OF yz] show "x \<sqsubseteq> z" by (auto simp: not_strict[symmetric])
next
  fix x y assume xy: "x \<sqsubseteq> y" and yx: "y \<sqsubseteq> x" and xA: "x \<in> A" and yA: "y \<in> A"
  with semiconnex show "x = y" by (auto dest: weak_implies_not_strict)
qed

sublocale total_ordered_set..

context
  fixes s
  assumes s: "\<forall>x \<in> A. x \<sqsubset> s \<longrightarrow> (\<exists>z \<in> A. x \<sqsubset> z \<and> z \<sqsubset> s)" and sA: "s \<in> A"
begin

lemma dense_weakI:
  assumes bound: "\<And>x. x \<sqsubset> s \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> y" and yA: "y \<in> A"
  shows "s \<sqsubseteq> y"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with yA sA have "y \<sqsubset> s" by (simp add: not_weak)
  from s[rule_format, OF yA this]
  obtain x where xA: "x \<in> A" and xs: "x \<sqsubset> s" and yx: "y \<sqsubset> x" by safe
  have xy: "x \<sqsubseteq> y" using bound[OF xs xA] .
  from yx xy xA yA
  show False by (simp add: weak_implies_not_strict)
qed

lemma dense_bound_iff:
  assumes bA: "b \<in> A" shows "bound {x\<in>A. x \<sqsubset> s} (\<sqsubseteq>) b \<longleftrightarrow> s \<sqsubseteq> b"
  using assms sA
  by (auto simp: bound_def intro: strict_implies_weak strict_weak_trans dense_weakI)

lemma dense_extreme_bound:
  "extreme_bound A (\<sqsubseteq>) {x \<in> A. x \<sqsubset> s} s"
  by (auto intro!: extreme_boundI intro: strict_implies_weak simp: dense_bound_iff sA)

end

lemma ordinal_cases[consumes 1, case_names suc lim]:
  assumes aA: "a \<in> A"
    and suc: "\<And>p. extreme {x \<in> A. x \<sqsubset> a} (\<sqsubseteq>) p \<Longrightarrow> thesis"
    and lim: "extreme_bound A (\<sqsubseteq>) {x \<in> A. x \<sqsubset> a} a \<Longrightarrow> thesis"
  shows "thesis"
proof (cases "\<exists>p. extreme {x \<in> A. x \<sqsubset> a} (\<sqsubseteq>) p")
  case True
  with suc show ?thesis by auto
next
  case False
  show ?thesis
  proof (rule lim, rule dense_extreme_bound, safe intro!: aA)
    fix x assume xA: "x \<in> A" and xa: "x \<sqsubset> a"
    show "\<exists>z\<in>A. x \<sqsubset> z \<and> z \<sqsubset> a"
    proof (rule ccontr)
      assume "\<not>?thesis"
      with xA xa have "extreme {x \<in> A. x \<sqsubset> a} (\<sqsubseteq>) x" by (auto simp: not_strict)
      with False show False by auto
    qed
  qed
qed

end

context total_ordered_set begin

interpretation less_eq_asymmetrize.

lemma asympartp_total_ordering: "total_ordering A (\<sqsubseteq>) (\<sqsubset>)"
  by (intro total_ordering.intro reflexive_axioms asympartp_compatible_ordering asympartp_semiconnex)

end

subsection \<open>Functions\<close>

definition "pointwise I r f g \<equiv> \<forall>i \<in> I. r (f i) (g i)"

lemmas pointwiseI = pointwise_def[unfolded atomize_eq, THEN iffD2, rule_format]

lemmas pointwiseD[simp] = pointwise_def[unfolded atomize_eq, THEN iffD1, rule_format]

lemma pointwise_cong:
  assumes "r = r'" "\<And>i. i \<in> I \<Longrightarrow> f i = f' i" "\<And>i. i \<in> I \<Longrightarrow> g i = g' i"
  shows "pointwise I r f g = pointwise I r' f' g'"
  using assms by (auto simp: pointwise_def)

lemma pointwise_empty[simp]: "pointwise {} = \<top>" by (auto intro!: ext pointwiseI)

lemma dual_pointwise[simp]: "(pointwise I r)\<^sup>- = pointwise I r\<^sup>-"
  by (auto intro!: ext pointwiseI dest: pointwiseD)

lemma pointwise_dual: "pointwise I r\<^sup>- f g \<Longrightarrow> pointwise I r g f" by (auto simp: pointwise_def)

lemma pointwise_un: "pointwise (I\<union>J) r = pointwise I r \<sqinter> pointwise J r"
  by (auto intro!: ext pointwiseI)

lemma pointwise_unI[intro!]: "pointwise I r f g \<Longrightarrow> pointwise J r f g \<Longrightarrow> pointwise (I \<union> J) r f g"
  by (auto simp: pointwise_un)

lemma pointwise_bound: "bound F (pointwise I r) f \<longleftrightarrow> (\<forall>i \<in> I. bound {f i |. f \<in> F} r (f i))"
  by (auto intro!:pointwiseI elim!: boundE)

lemma pointwise_extreme:
  shows "extreme F (pointwise X r) e \<longleftrightarrow> e \<in> F \<and> (\<forall>x \<in> X. extreme {f x |. f \<in> F} r (e x))"
  by (auto intro!: pointwiseI extremeI elim!: extremeE)

lemma pointwise_extreme_bound:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes F: "F \<subseteq> {f. f ` X \<subseteq> A}"
  shows "extreme_bound {f. f ` X \<subseteq> A} (pointwise X (\<sqsubseteq>)) F s \<longleftrightarrow>
    (\<forall>x \<in> X. extreme_bound A (\<sqsubseteq>) {f x |. f \<in> F} (s x))" (is "?p \<longleftrightarrow> ?a")
proof (safe intro!: extreme_boundI pointwiseI)
  fix x
  assume s: ?p and xX: "x \<in> X"
  { fix b
    assume b: "bound {f x |. f \<in> F} (\<sqsubseteq>) b" and bA: "b \<in> A"
    have "pointwise X (\<sqsubseteq>) s (s(x:=b))"
    proof (rule extreme_boundD(2)[OF s], safe intro!: pointwiseI)
      fix f y
      assume fF: "f \<in> F" and yX: "y \<in> X"
      show "f y \<sqsubseteq> (s(x:=b)) y"
      proof (cases "x = y")
        case True
        with b fF show "?thesis" by auto
      next
        case False
        with s[THEN extreme_bound_imp_bound] fF yX show ?thesis by (auto dest: boundD)
      qed
    next
      fix y assume "y \<in> X" with bA s show "(s(x := b)) y \<in> A" by auto
    qed
    with xX show "s x \<sqsubseteq> b" by (auto dest: pointwiseD)
  next
    fix f assume "f \<in> F"
    from extreme_boundD(1)[OF s this] F xX
    show "f x \<sqsubseteq> s x" by auto
  next
    show "s x \<in> A" using s xX by auto
  }
next
  fix x
  assume s: ?a and xX: "x \<in> X"
  { from s xX show "s x \<in> A" by auto
  next
    fix b assume b: "bound F (pointwise X (\<sqsubseteq>)) b" and bA: "b ` X \<subseteq> A"
    with xX have "bound {f x |. f \<in> F} (\<sqsubseteq>) (b x)" by (auto simp: pointwise_bound)
    with s[rule_format, OF xX] bA xX show "s x \<sqsubseteq> b x" by auto
  next
    fix f assume "f \<in> F"
    with s[rule_format, OF xX] show "f x \<sqsubseteq> s x" by auto
  }
qed

lemma dual_pointwise_extreme_bound:
  "extreme_bound FA (pointwise X r)\<^sup>- F = extreme_bound FA (pointwise X r\<^sup>-) F"
  by (simp)

lemma pointwise_monotone_on:
  fixes less_eq (infix "\<sqsubseteq>" 50) and prec_eq (infix "\<preceq>" 50)
  shows "monotone_on I (\<preceq>) (pointwise A (\<sqsubseteq>)) f \<longleftrightarrow>
   (\<forall>a \<in> A. monotone_on I (\<preceq>) (\<sqsubseteq>) (\<lambda>i. f i a))" (is "?l \<longleftrightarrow> ?r")
proof (safe intro!: monotone_onI pointwiseI)
  fix a i j assume aA: "a \<in> A" and *: ?l "i \<preceq> j" "i \<in> I" "j \<in> I"
  then
  show "f i a \<sqsubseteq> f j a" by (auto dest: monotone_onD)
next
  fix a i j assume ?r and "a \<in> A" and ij: "i \<preceq> j" "i \<in> I" "j \<in> I"
  then have "monotone_on I (\<preceq>) (\<sqsubseteq>) (\<lambda>i. f i a)" by auto
  from monotone_onD[OF this]ij
  show "f i a \<sqsubseteq> f j a" by auto
qed

lemmas pointwise_monotone = pointwise_monotone_on[of UNIV]

lemma (in reflexive) pointwise_reflexive: "reflexive {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
  apply unfold_locales by (auto intro!: pointwiseI simp: subsetD[OF _ imageI])

lemma (in irreflexive) pointwise_irreflexive:
  assumes I0: "I \<noteq> {}" shows "irreflexive {f. f ` I \<subseteq> A} (pointwise I (\<sqsubset>))"
proof (safe intro!: irreflexive.intro)
  fix f
  assume f: "f ` I \<subseteq> A" and ff: "pointwise I (\<sqsubset>) f f"
  from I0 obtain i where i: "i \<in> I" by auto
  with ff have "f i \<sqsubset> f i" by auto
  with f i show False by auto
qed

lemma (in semiattractive) pointwise_semiattractive: "semiattractive {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
proof (unfold_locales, safe intro!: pointwiseI)
  fix f g h i
  assume fg: "pointwise I (\<sqsubseteq>) f g" and gf: "pointwise I (\<sqsubseteq>) g f" and gh: "pointwise I (\<sqsubseteq>) g h"
    and [simp]: "i \<in> I" and f: "f ` I \<subseteq> A" and g: "g ` I \<subseteq> A" and h: "h ` I \<subseteq> A"
  show "f i \<sqsubseteq> h i"
  proof (rule attract)
    from fg show "f i \<sqsubseteq> g i" by auto
    from gf show "g i \<sqsubseteq> f i" by auto
    from gh show "g i \<sqsubseteq> h i" by auto
  qed (insert f g h, auto simp: subsetD[OF _ imageI])
qed

lemma (in attractive) pointwise_attractive: "attractive {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
  apply (intro attractive.intro attractive_axioms.intro)
  using pointwise_semiattractive dual.pointwise_semiattractive by auto

text \<open>Antisymmetry will not be preserved by pointwise extension over restricted domain.\<close>
lemma (in antisymmetric) pointwise_antisymmetric:
  "antisymmetric {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
  oops

lemma (in transitive) pointwise_transitive: "transitive {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
proof (unfold_locales, safe intro!: pointwiseI)
  fix f g h i
  assume fg: "pointwise I (\<sqsubseteq>) f g" and gh: "pointwise I (\<sqsubseteq>) g h"
    and [simp]: "i \<in> I" and f: "f ` I \<subseteq> A" and g: "g ` I \<subseteq> A" and h: "h ` I \<subseteq> A"
  from fg have "f i \<sqsubseteq> g i" by auto
  also from gh have "g i \<sqsubseteq> h i" by auto
  finally show "f i \<sqsubseteq> h i" using f g h by (auto simp: subsetD[OF _ imageI])
qed

lemma (in quasi_ordered_set) pointwise_quasi_order:
  "quasi_ordered_set {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>))"
  by (intro quasi_ordered_setI pointwise_transitive pointwise_reflexive)

lemma (in compatible_ordering) pointwise_compatible_ordering:
  assumes I0: "I \<noteq> {}"
  shows "compatible_ordering {f. f ` I \<subseteq> A} (pointwise I (\<sqsubseteq>)) (pointwise I (\<sqsubset>))"
proof (intro compatible_ordering.intro compatible_ordering_axioms.intro pointwise_irreflexive[OF I0], safe intro!: pointwiseI)
  fix f g h i
  assume fg: "pointwise I (\<sqsubseteq>) f g" and gh: "pointwise I (\<sqsubset>) g h"
    and [simp]: "i \<in> I" and f: "f ` I \<subseteq> A" and g: "g ` I \<subseteq> A" and h: "h ` I \<subseteq> A"
  from fg have "f i \<sqsubseteq> g i" by auto
  also from gh have "g i \<sqsubset> h i" by auto
  finally show "f i \<sqsubset> h i" using f g h by (auto simp: subsetD[OF _ imageI])
next
  fix f g h i
  assume fg: "pointwise I (\<sqsubset>) f g" and gh: "pointwise I (\<sqsubseteq>) g h"
    and [simp]: "i \<in> I" and f: "f ` I \<subseteq> A" and g: "g ` I \<subseteq> A" and h: "h ` I \<subseteq> A"
  from fg have "f i \<sqsubset> g i" by auto
  also from gh have "g i \<sqsubseteq> h i" by auto
  finally show "f i \<sqsubset> h i" using f g h by (auto simp: subsetD[OF _ imageI])
next
  fix f g i
  assume fg: "pointwise I (\<sqsubset>) f g"
    and [simp]: "i \<in> I"
    and f: "f ` I \<subseteq> A" and g: "g ` I \<subseteq> A"
  from fg have "f i \<sqsubset> g i" by auto
  with f g show "f i \<sqsubseteq> g i" by (auto simp: subsetD[OF _ imageI] strict_implies_weak)
qed

subsection \<open>Relating to Classes\<close>

text \<open>In Isabelle 2020, we should declare sublocales in class before declaring dual
sublocales, since otherwise facts would be prefixed by ``dual.dual.''\<close>

context ord begin

abbreviation least where "least X \<equiv> extreme X (\<lambda>x y. y \<le> x)"

abbreviation greatest where "greatest X \<equiv> extreme X (\<le>)"

abbreviation supremum where "supremum X \<equiv> least (Collect (bound X (\<le>)))"

abbreviation infimum where "infimum X \<equiv> greatest (Collect (bound X (\<lambda>x y. y \<le> x)))"

lemma supremumI: "bound X (\<le>) s \<Longrightarrow> (\<And>b. bound X (\<le>) b \<Longrightarrow> s \<le> b) \<Longrightarrow> supremum X s"
  and infimumI: "bound X (\<ge>) i \<Longrightarrow> (\<And>b. bound X (\<ge>) b \<Longrightarrow> b \<le> i) \<Longrightarrow> infimum X i"
  by (auto intro!: extremeI)

lemma supremumE: "supremum X s \<Longrightarrow>
    (bound X (\<le>) s \<Longrightarrow> (\<And>b. bound X (\<le>) b \<Longrightarrow> s \<le> b) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  and infimumE: "infimum X i \<Longrightarrow>
    (bound X (\<ge>) i \<Longrightarrow> (\<And>b. bound X (\<ge>) b \<Longrightarrow> b \<le> i) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto)

lemma extreme_bound_supremum[simp]: "extreme_bound UNIV (\<le>) = supremum" by (auto intro!: ext)
lemma extreme_bound_infimum[simp]: "extreme_bound UNIV (\<ge>) = infimum" by (auto intro!: ext)

lemma Least_eq_The_least: "Least P = The (least {x. P x})"
  by (auto simp: Least_def extreme_def[unfolded atomize_eq, THEN ext])

lemma Greatest_eq_The_greatest: "Greatest P = The (greatest {x. P x})"
  by (auto simp: Greatest_def extreme_def[unfolded atomize_eq, THEN ext])

end

lemma Ball_UNIV[simp]: "Ball UNIV = All" by auto
lemma Bex_UNIV[simp]: "Bex UNIV = Ex" by auto

lemma pointwise_UNIV_le[simp]: "pointwise UNIV (\<le>) = (\<le>)" by (intro ext, simp add: pointwise_def le_fun_def)
lemma pointwise_UNIV_ge[simp]: "pointwise UNIV (\<ge>) = (\<ge>)" by (intro ext, simp add: pointwise_def le_fun_def)

lemma fun_supremum_iff: "supremum F e \<longleftrightarrow> (\<forall>x. supremum {f x |. f \<in> F} (e x))"
  using pointwise_extreme_bound[of F UNIV UNIV "(\<le>)"] by simp

lemma fun_infimum_iff: "infimum F e \<longleftrightarrow> (\<forall>x. infimum {f x |. f \<in> F} (e x))"
  using pointwise_extreme_bound[of F UNIV UNIV "(\<ge>)"] by simp


class reflorder = ord + assumes "reflexive_ordering UNIV (\<le>) (<)"
begin

sublocale order: reflexive_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using reflorder_axioms unfolding class.reflorder_def by (auto 0 4 simp:atomize_eq)

end

text \<open>We should have imported locale-based facts in classes, e.g.:\<close>
thm order.trans order.strict.trans order.refl order.irrefl order.asym order.extreme_bound_singleton

class attrorder = ord +
  assumes "reflexive_attractive_ordering UNIV (\<le>) (<)"
begin

text \<open>We need to declare subclasses before sublocales in order to preserve facts for superclasses.\<close>

subclass reflorder
proof-
  interpret reflexive_attractive_ordering UNIV
    using attrorder_axioms unfolding class.attrorder_def by auto
  show "class.reflorder (\<le>) (<)"..
qed

sublocale order: reflexive_attractive_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using attrorder_axioms unfolding class.attrorder_def
  by (auto simp:atomize_eq)

end

thm order.extreme_bound_quasi_const

class psorder = ord + assumes "pseudo_ordering UNIV (\<le>) (<)"
begin

subclass attrorder
proof-
  interpret pseudo_ordering UNIV
    using psorder_axioms unfolding class.psorder_def by auto
  show "class.attrorder (\<le>) (<)"..
qed

sublocale order: pseudo_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using psorder_axioms unfolding class.psorder_def by (auto simp:atomize_eq)

end

class qorder = ord + assumes "quasi_ordering UNIV (\<le>) (<)"
begin

subclass attrorder
proof-
  interpret quasi_ordering UNIV
    using qorder_axioms unfolding class.qorder_def by auto
  show "class.attrorder (\<le>) (<)"..
qed

sublocale order: quasi_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using qorder_axioms unfolding class.qorder_def by (auto simp:atomize_eq)

lemmas [intro!] = order.quasi_ordered_subset

end

class porder = ord + assumes "partial_ordering UNIV (\<le>) (<)"
begin

interpretation partial_ordering UNIV
  using porder_axioms unfolding class.porder_def by auto

subclass psorder..

subclass qorder..

sublocale order: partial_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

class linqorder = ord + assumes "total_quasi_ordering UNIV (\<le>) (<)"
begin

interpretation total_quasi_ordering UNIV
  using linqorder_axioms unfolding class.linqorder_def by auto

subclass qorder..

sublocale order: total_quasi_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
    using linqorder_axioms unfolding class.linqorder_def
    by (auto simp:atomize_eq)

lemmas asympartp_le = order.not_iff_asym[symmetric, abs_def]

end


text \<open>Isabelle/HOL's @{class preorder} belongs to @{class qorder}, but not vice versa.\<close>

context preorder begin

text \<open>The relation @{term "(<)"} is defined as the antisymmetric part of @{term "(\<le>)"}.\<close>
lemma [simp]:
  shows asympartp_le: "asympartp (\<le>) = (<)"
    and asympartp_ge: "asympartp (\<ge>) = (>)"
  by (intro ext, auto simp: asympartp_def less_le_not_le)

interpretation strict_quasi_ordering UNIV "(\<le>)" "(<)"
  apply unfold_locales
  using order_refl apply assumption
  using order_trans apply assumption
  using less_le_not_le apply assumption
  done

subclass qorder..

sublocale order: strict_quasi_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales
    by (auto simp:atomize_eq)

end

context order begin

interpretation strict_partial_ordering UNIV "(\<le>)" "(<)"
  apply unfold_locales
  using order_antisym by assumption

subclass porder..

sublocale order: strict_partial_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales
    by (auto simp:atomize_eq)

end

text \<open>Isabelle/HOL's @{class linorder} is equivalent to our locale @{locale total_ordering}.\<close>

context linorder begin

subclass linqorder apply unfold_locales by auto

sublocale order: total_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

text \<open>Tests: facts should be available in the most general classes.\<close>

thm order.strict.trans[where 'a="'a::reflorder"]
thm order.extreme_bound_quasi_const[where 'a="'a::attrorder"]
thm order.extreme_bound_singleton_eq[where 'a="'a::psorder"]
thm order.trans[where 'a="'a::qorder"]
thm order.comparable_cases[where 'a="'a::linqorder"]
thm order.cases[where 'a="'a::linorder"]

subsection \<open>Declaring Duals\<close>

sublocale reflexive \<subseteq> sym: reflexive A "sympartp (\<sqsubseteq>)"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "\<And>r. sympartp r \<restriction> A \<equiv> sympartp (r \<restriction> A)"
  by (auto 0 4 simp:atomize_eq)

sublocale quasi_ordered_set \<subseteq> sym: quasi_ordered_set A "sympartp (\<sqsubseteq>)"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
    and "sympartp (sympartp (\<sqsubseteq>)) = sympartp (\<sqsubseteq>)"
   apply unfold_locales by (auto 0 4 dest: trans)
  
text \<open>At this point, we declare dual as sublocales.
In the following, ``rewrites'' eventually cleans up redundant facts.\<close>

sublocale reflexive \<subseteq> dual: reflexive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
  by (auto simp: atomize_eq)

context attractive begin

interpretation less_eq_symmetrize.

sublocale dual: attractive A "(\<sqsupseteq>)"
  rewrites "sympartp (\<sqsupseteq>) = (\<sim>)"
    and "equivpartp (\<sqsupseteq>) \<equiv> (\<simeq>)"
    and "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
  apply unfold_locales by (auto intro!: ext dest: attract dual.attract simp: atomize_eq)

end

context irreflexive begin

sublocale dual: irreflexive A "(\<sqsubset>)\<^sup>-"
  rewrites "(\<sqsubset>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubset>) \<restriction> A)\<^sup>-"
  apply unfold_locales by (auto dest: irrefl simp: atomize_eq)

end

sublocale transitive \<subseteq> dual: transitive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
    and "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
    and "asympartp (\<sqsubseteq>)\<^sup>- = (asympartp (\<sqsubseteq>))\<^sup>-"
  apply unfold_locales by (auto dest: trans simp: atomize_eq intro!:ext)

sublocale antisymmetric \<subseteq> dual: antisymmetric A "(\<sqsubseteq>)\<^sup>-"
  rewrites "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
    and "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by (auto dest: antisym simp: atomize_eq)

context antisymmetric begin

lemma extreme_bound_unique:
  "extreme_bound A (\<sqsubseteq>) X x \<Longrightarrow> extreme_bound A (\<sqsubseteq>) X y \<longleftrightarrow> x = y"
  apply (unfold extreme_bound_def)
  apply (rule dual.extreme_unique) by auto

lemma ex_extreme_bound_iff_ex1:
  "Ex (extreme_bound A (\<sqsubseteq>) X) \<longleftrightarrow> Ex1 (extreme_bound A (\<sqsubseteq>) X)"
  apply (unfold extreme_bound_def)
  apply (rule dual.ex_extreme_iff_ex1) by auto

lemma ex_extreme_bound_iff_the:
   "Ex (extreme_bound A (\<sqsubseteq>) X) \<longleftrightarrow> extreme_bound A (\<sqsubseteq>) X (The (extreme_bound A (\<sqsubseteq>) X))"
  apply (rule iffI)
  apply (rule theI')
  using extreme_bound_unique by auto

end

sublocale semiconnex \<subseteq> dual: semiconnex A "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubset>)\<^sup>- = sympartp (\<sqsubset>)"
  using semiconnex by auto

sublocale connex \<subseteq> dual: connex A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by (auto intro!: chainI dest:comparable)

sublocale semiconnex_irreflexive \<subseteq> dual: semiconnex_irreflexive A "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubset>)\<^sup>- = sympartp (\<sqsubset>)"
  by unfold_locales auto

sublocale pseudo_ordered_set \<subseteq> dual: pseudo_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale quasi_ordered_set \<subseteq> dual: quasi_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale partially_ordered_set \<subseteq> dual: partially_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale total_pseudo_ordered_set \<subseteq> dual: total_pseudo_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale total_quasi_ordered_set \<subseteq> dual: total_quasi_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale compatible_ordering \<subseteq> dual: compatible_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  apply unfold_locales
  by (auto dest: strict_implies_weak strict_weak_trans weak_strict_trans)

lemmas(in qorder) [intro!] = order.dual.quasi_ordered_subset

sublocale reflexive_ordering \<subseteq> dual: reflexive_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale reflexive_attractive_ordering \<subseteq> dual: reflexive_attractive_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale pseudo_ordering \<subseteq> dual: pseudo_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale quasi_ordering \<subseteq> dual: quasi_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale partial_ordering \<subseteq> dual: partial_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale total_quasi_ordering \<subseteq> dual: total_quasi_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale total_ordering \<subseteq> dual: total_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale strict_quasi_ordering \<subseteq> dual: strict_quasi_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto simp: strict_iff)

sublocale strict_partial_ordering \<subseteq> dual: strict_partial_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale total_ordering \<subseteq> dual: total_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

lemma(in antisymmetric) monotone_extreme_imp_extreme_bound_iff:
  fixes ir (infix "\<preceq>" 50)
  assumes "f ` C \<subseteq> A" and "monotone_on C (\<preceq>) (\<sqsubseteq>) f" and i: "extreme C (\<preceq>) i"
  shows "extreme_bound A (\<sqsubseteq>) (f ` C) x \<longleftrightarrow> f i = x"
  using dual.extreme_unique monotone_extreme_extreme_boundI[OF assms]
  by (auto simp: extreme_bound_def)

subsection \<open>Instantiations\<close>

text \<open>Finally, we instantiate our classes for sanity check.\<close>

instance nat :: linorder ..

text \<open>Pointwise ordering of functions are compatible only if the weak part is transitive.\<close>

instance "fun" :: (type,qorder) reflorder
proof (intro_classes, unfold_locales)
  note [simp] = le_fun_def less_fun_def
  fix f g h :: "'a \<Rightarrow> 'b"
  { assume fg: "f \<le> g" and gh: "g < h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally (order.trans) show "f x \<le> h x" for x.
      assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      also from fg have "f x \<le> g x" for x by auto
      finally have "h \<le> g" by auto
      with gh show False by auto
    qed
  }
  { assume fg: "f < g" and gh: "g \<le> h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally show "f x \<le> h x" for x.
      from gh have "g x \<le> h x" for x by auto
      also assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      finally have "g \<le> f" by auto
      with fg show False by auto
    qed
  }
  show "f < g \<Longrightarrow> f \<le> g" by auto
  show "\<not>f < f" by auto
  show "f \<le> f" by auto
qed

instance "fun" :: (type,qorder) qorder
  apply intro_classes
  apply unfold_locales
  by (auto simp: le_fun_def dest: order.trans)

instance "fun" :: (type,porder) porder
  apply intro_classes
  apply unfold_locales
proof (intro ext)
  fix f g :: "'a \<Rightarrow> 'b" and x :: 'a
  assume fg: "f \<le> g" and gf: "g \<le> f"
  then have "f x \<le> g x" and "g x \<le> f x" by (auto elim: le_funE)
  from order.antisym[OF this] show "f x = g x" by auto
qed

end
