theory Continuity
  imports Complete_Relations
begin

subsection \<open>Scott Continuity, $\omega$-Continuity\<close>

text \<open>In this Section, we formalize Scott continuity and $\omega$-continuity.
We then prove that a Scott continuous map is $\omega$-continuous and that an $\omega$-continuous 
map is ``nearly'' monotone.\<close>

definition continuous ("_-continuous" [1000]1000) where
  "\<C>-continuous A (\<sqsubseteq>) B (\<unlhd>) f \<equiv>
   f ` A \<subseteq> B \<and>
   (\<forall>X s. \<C> X (\<sqsubseteq>) \<longrightarrow> X \<noteq> {} \<longrightarrow> X \<subseteq> A \<longrightarrow> extreme_bound A (\<sqsubseteq>) X s \<longrightarrow> extreme_bound B (\<unlhd>) (f`X) (f s))"
  for leA (infix "\<sqsubseteq>" 50) and leB (infix "\<unlhd>" 50)

lemmas continuousI[intro?] =
  continuous_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp, rule_format]

lemmas continuousE =
  continuous_def[unfolded atomize_eq, THEN iffD1, elim_format, unfolded conj_imp_eq_imp_imp, rule_format]

lemma
  fixes prec_eq (infix "\<preceq>" 50) and less_eq (infix "\<sqsubseteq>" 50)
  assumes "\<C>-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  shows continuous_carrierD[dest]: "f ` I \<subseteq> A"
    and continuousD: "\<C> X (\<preceq>) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> X \<subseteq> I \<Longrightarrow> extreme_bound I (\<preceq>) X b \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` X) (f b)"
  using assms by (auto elim!: continuousE)

lemma continuous_comp:
  fixes leA (infix "\<sqsubseteq>\<^sub>A" 50) and leB (infix "\<sqsubseteq>\<^sub>B" 50) and leC (infix "\<sqsubseteq>\<^sub>C" 50)
  assumes KfL: "\<forall>X \<subseteq> A. \<K> X (\<sqsubseteq>\<^sub>A) \<longrightarrow> \<L> (f ` X) (\<sqsubseteq>\<^sub>B)"
  assumes f: "\<K>-continuous A (\<sqsubseteq>\<^sub>A) B (\<sqsubseteq>\<^sub>B) f" and g: "\<L>-continuous B (\<sqsubseteq>\<^sub>B) C (\<sqsubseteq>\<^sub>C) g"
  shows "\<K>-continuous A (\<sqsubseteq>\<^sub>A) C (\<sqsubseteq>\<^sub>C) (g \<circ> f)"
  apply (intro continuousI)
proof -
  from f g have fAB: "f ` A \<subseteq> B" and gBC: "g ` B \<subseteq> C" by auto
  then show "(g \<circ> f) ` A \<subseteq> C" by auto
  fix X s
  assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}" and XK: "\<K> X (\<sqsubseteq>\<^sub>A)" and Xs: "extreme_bound A (\<sqsubseteq>\<^sub>A) X s"
  from fAB XA have fXB: "f ` X \<subseteq> B" by auto
  from X0 have fX0: "f ` X \<noteq> {}" by auto
  from KfL XA XK have fXL: "\<L> (f ` X) (\<sqsubseteq>\<^sub>B)" by auto
  from continuousD[OF f XK X0 XA Xs]
  have "extreme_bound B (\<sqsubseteq>\<^sub>B) (f ` X) (f s)".
  from continuousD[OF g fXL fX0 fXB this]
  show "extreme_bound C (\<sqsubseteq>\<^sub>C) ((g\<circ>f)`X) ((g\<circ>f) s)" by (auto simp: image_comp)
qed

lemma continuous_comp_top:
  fixes leA (infix "\<sqsubseteq>\<^sub>A" 50) and leB (infix "\<sqsubseteq>\<^sub>B" 50) and leC (infix "\<sqsubseteq>\<^sub>C" 50)
  assumes f: "\<K>-continuous A (\<sqsubseteq>\<^sub>A) B (\<sqsubseteq>\<^sub>B) f" and g: "\<top>-continuous B (\<sqsubseteq>\<^sub>B) C (\<sqsubseteq>\<^sub>C) g"
  shows "\<K>-continuous A (\<sqsubseteq>\<^sub>A) C (\<sqsubseteq>\<^sub>C) (g \<circ> f)"
  by (rule continuous_comp[OF _ f g], auto)

lemma id_continuous:
  fixes leA (infix "\<sqsubseteq>\<^sub>A" 50)
  shows "\<K>-continuous A (\<sqsubseteq>\<^sub>A) A (\<sqsubseteq>\<^sub>A) (\<lambda>x. x)"
  by (auto intro: continuousI)

lemma cst_continuous:
  fixes leA (infix "\<sqsubseteq>\<^sub>A" 50) and leB (infix "\<sqsubseteq>\<^sub>B" 50)
  assumes "b \<in> B" and bb: "b \<sqsubseteq>\<^sub>B b"
  shows "\<K>-continuous A (\<sqsubseteq>\<^sub>A) B (\<sqsubseteq>\<^sub>B) (\<lambda>x. b)"
  apply (intro continuousI)
  using assms(1) apply auto
  using assms extreme_bound_singleton_refl[of B "(\<sqsubseteq>\<^sub>B)" b] by blast


lemma continuous_cmono:
  assumes CD: "\<C> \<le> \<D>" shows "\<D>-continuous \<le> \<C>-continuous"
proof (safe intro!: le_funI le_boolI)
  fix I A f and prec_eq (infix "\<preceq>" 50) and less_eq (infix "\<sqsubseteq>" 50)
  assume cont: "\<D>-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  show "\<C>-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  proof (rule continuousI)
    from cont show "f ` I \<subseteq> A" by auto
    fix X s assume X: "\<C> X (\<preceq>)" and X0: "X \<noteq> {}" and XI: "X \<subseteq> I" and Xs: "extreme_bound I (\<preceq>) X s"
    from CD X have "\<D> X (\<preceq>)" by auto
    from continuousD[OF cont, OF this X0 XI Xs]
    show "extreme_bound A (\<sqsubseteq>) (f ` X) (f s)".
  qed
qed

context
  fixes prec_eq :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50) and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma continuous_subclass:
  assumes CD: "\<forall>X\<subseteq>I. X \<noteq> {} \<longrightarrow> \<C> X (\<preceq>) \<longrightarrow> \<D> X (\<preceq>)" and cont: "\<D>-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  shows "\<C>-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  using cont by (auto simp: continuous_def CD[rule_format])

lemma chain_continuous_imp_well_continuous:
  assumes cont: "connex-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  shows "well_related_set-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  by (rule continuous_subclass[OF _ cont], auto simp: well_related_set.connex)

lemma well_continuous_imp_omega_continous:
  assumes cont: "well_related_set-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  shows "omega_chain-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  by (rule continuous_subclass[OF _ cont], auto simp: omega_chain_imp_well_related)

end

abbreviation "scott_continuous I (\<preceq>) \<equiv> directed_set-continuous I (\<preceq>)"
  for prec_eq (infix "\<preceq>" 50)

lemma scott_continuous_imp_well_continuous:
  fixes prec_eq :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50) and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
  assumes cont: "scott_continuous I (\<preceq>) A (\<sqsubseteq>) f"
  shows "well_related_set-continuous I (\<preceq>) A (\<sqsubseteq>) f"
  by (rule continuous_subclass[OF _ cont], auto simp: well_related_set.directed_set)

lemmas scott_continuous_imp_omega_continuous =
  scott_continuous_imp_well_continuous[THEN well_continuous_imp_omega_continous]


subsubsection \<open>Continuity implies monotonicity\<close>

lemma continuous_imp_mono_refl:
  fixes prec_eq (infix "\<preceq>" 50) and less_eq (infix "\<sqsubseteq>" 50)
  assumes cont: "\<C>-continuous I (\<preceq>) A (\<sqsubseteq>) f" and xyC: "\<C> {x,y} (\<preceq>)"
    and xy: "x \<preceq> y" and yy: "y \<preceq> y"
    and x: "x \<in> I" and y: "y \<in> I"
  shows "f x \<sqsubseteq> f y"
proof-
  have fboy: "extreme_bound A (\<sqsubseteq>) (f ` {x,y}) (f y)"
  proof (intro continuousD[OF cont] xyC)
    from x y show CI: "{x,y} \<subseteq> I" by auto
    show Cy: "extreme_bound I (\<preceq>) {x,y} y" using xy yy x y by auto
  qed auto
  then show ?thesis by auto
qed

lemma omega_continuous_imp_mono_refl:
  fixes prec_eq (infix "\<preceq>" 50) and less_eq (infix "\<sqsubseteq>" 50)
  assumes cont: "omega_chain-continuous I (\<preceq>) A (\<sqsubseteq>) f"
    and xx: "x \<preceq> x" and xy: "x \<preceq> y" and yy: "y \<preceq> y"
    and x: "x \<in> I" and y: "y \<in> I"
  shows "f x \<sqsubseteq> f y"
  apply (rule continuous_imp_mono_refl[OF cont, OF pair_omega_chain])
  using assms by auto

context reflexive begin

lemma continuous_imp_monotone_on:
  fixes leB (infix "\<unlhd>" 50)
  assumes cont: "\<C>-continuous A (\<sqsubseteq>) B (\<unlhd>) f"
    and II: "\<forall>i \<in> A. \<forall> j \<in> A. i \<sqsubseteq> j \<longrightarrow> \<C> {i,j} (\<sqsubseteq>)"
  shows "monotone_on A (\<sqsubseteq>) (\<unlhd>) f"
proof-
  show ?thesis
    apply (intro monotone_onI continuous_imp_mono_refl[OF cont])
    using II by auto
qed

lemma well_complete_imp_monotone_on:
  fixes leB (infix "\<unlhd>" 50)
  assumes cont: "well_related_set-continuous A (\<sqsubseteq>) B (\<unlhd>) f"
  shows "monotone_on A (\<sqsubseteq>) (\<unlhd>) f"                       
  by (auto intro!: continuous_imp_monotone_on cont pair_well_related)

end

end