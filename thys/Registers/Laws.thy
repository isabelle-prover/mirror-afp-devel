section \<open>Generic laws about registers\<close>

theory Laws
  imports Axioms
begin

text \<open>This notation is only used inside this file\<close>
notation comp_update (infixl "*\<^sub>u" 55)
notation tensor_update (infixr "\<otimes>\<^sub>u" 70)
notation register_pair ("'(_;_')")

subsection \<open>Elementary facts\<close>

declare id_preregister[simp]
declare id_update_left[simp]
declare id_update_right[simp]
declare register_preregister[simp]
declare register_comp[simp]
declare register_of_id[simp]
declare register_tensor_left[simp]
declare register_tensor_right[simp]
declare preregister_mult_right[simp]
declare preregister_mult_left[simp]
declare register_id[simp]

subsection \<open>Preregisters\<close>

lemma preregister_tensor_left[simp]: \<open>preregister (\<lambda>b::'b::domain update. tensor_update a b)\<close>
  for a :: \<open>'a::domain update\<close>
proof -
  have \<open>preregister ((\<lambda>b1::('a\<times>'b) update. (a \<otimes>\<^sub>u id_update) *\<^sub>u b1) o (\<lambda>b. tensor_update id_update b))\<close>
    by (rule comp_preregister; simp)
  then show ?thesis
    by (simp add: o_def tensor_update_mult)
qed

lemma preregister_tensor_right[simp]: \<open>preregister (\<lambda>a::'a::domain update. tensor_update a b)\<close>  
  for b :: \<open>'b::domain update\<close>
proof -
  have \<open>preregister ((\<lambda>a1::('a\<times>'b) update. (id_update \<otimes>\<^sub>u b) *\<^sub>u a1) o (\<lambda>a. tensor_update a id_update))\<close>
    by (rule comp_preregister, simp_all)
  then show ?thesis
    by (simp add: o_def tensor_update_mult)
qed

subsection \<open>Registers\<close>

lemma id_update_tensor_register[simp]:
  assumes \<open>register F\<close>
  shows \<open>register (\<lambda>a::'a::domain update. id_update \<otimes>\<^sub>u F a)\<close>
  using assms apply (rule register_comp[unfolded o_def])
  by simp

lemma register_tensor_id_update[simp]:
  assumes \<open>register F\<close>
  shows \<open>register (\<lambda>a::'a::domain update. F a \<otimes>\<^sub>u id_update)\<close>
  using assms apply (rule register_comp[unfolded o_def])
  by simp

subsection \<open>Tensor product of registers\<close>

definition register_tensor  (infixr "\<otimes>\<^sub>r" 70) where
  "register_tensor F G = register_pair (\<lambda>a. tensor_update (F a) id_update) (\<lambda>b. tensor_update id_update (G b))"

lemma register_tensor_is_register: 
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  shows "register F \<Longrightarrow> register G \<Longrightarrow> register (F \<otimes>\<^sub>r G)"
  unfolding register_tensor_def
  apply (rule register_pair_is_register)
  by (simp_all add: tensor_update_mult)

lemma register_tensor_apply[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'b::domain update" and G :: "'c::domain update \<Rightarrow> 'd::domain update"
  assumes \<open>register F\<close> and \<open>register G\<close>
  shows "(F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b) = F a \<otimes>\<^sub>u G b"
  unfolding register_tensor_def
  apply (subst register_pair_apply)
  unfolding register_tensor_def 
  by (simp_all add: assms tensor_update_mult)

definition "separating (_::'b::domain itself) A \<longleftrightarrow> 
  (\<forall>F G :: 'a::domain update \<Rightarrow> 'b update. preregister F \<longrightarrow> preregister G \<longrightarrow> (\<forall>x\<in>A. F x = G x) \<longrightarrow> F = G)"

lemma separating_UNIV[simp]: \<open>separating TYPE(_) UNIV\<close>
  unfolding separating_def by auto

lemma separating_mono: \<open>A \<subseteq> B \<Longrightarrow> separating TYPE('a::domain) A \<Longrightarrow> separating TYPE('a) B\<close>
  unfolding separating_def by (meson in_mono) 

lemma register_eqI: \<open>separating TYPE('b::domain) A \<Longrightarrow> preregister F \<Longrightarrow> preregister G \<Longrightarrow> (\<And>x. x\<in>A \<Longrightarrow> F x = G x) \<Longrightarrow> F = (G::_ \<Rightarrow> 'b update)\<close>
  unfolding separating_def by auto

lemma separating_tensor:
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes [simp]: \<open>separating TYPE('c::domain) A\<close>
  assumes [simp]: \<open>separating TYPE('c) B\<close>
  shows \<open>separating TYPE('c) {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
proof (unfold separating_def, intro allI impI)
  fix F G :: \<open>('a\<times>'b) update \<Rightarrow> 'c update\<close>
  assume [simp]: \<open>preregister F\<close> \<open>preregister G\<close>
  have [simp]: \<open>preregister (\<lambda>x. F (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>preregister F\<close> apply (rule comp_preregister[unfolded o_def])
    by simp
  have [simp]: \<open>preregister (\<lambda>x. G (a \<otimes>\<^sub>u x))\<close> for a
    using _ \<open>preregister G\<close> apply (rule comp_preregister[unfolded o_def])
    by simp
  have [simp]: \<open>preregister (\<lambda>x. F (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>preregister F\<close> apply (rule comp_preregister[unfolded o_def])
    by simp
  have [simp]: \<open>preregister (\<lambda>x. G (x \<otimes>\<^sub>u b))\<close> for b
    using _ \<open>preregister G\<close> apply (rule comp_preregister[unfolded o_def])
    by simp

  assume \<open>\<forall>x\<in>{a \<otimes>\<^sub>u b |a b. a\<in>A \<and> b\<in>B}. F x = G x\<close>
  then have EQ: \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> and \<open>b \<in> B\<close> for a b
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> if \<open>a \<in> A\<close> for a b
    apply (rule register_eqI[where A=B, THEN fun_cong, where x=b, rotated -1])
    using that by auto
  then have \<open>F (a \<otimes>\<^sub>u b) = G (a \<otimes>\<^sub>u b)\<close> for a b
    apply (rule register_eqI[where A=A, THEN fun_cong, where x=a, rotated -1])
    by auto
  then show "F = G"
    apply (rule tensor_extensionality[rotated -1])
    by auto
qed

lemma register_tensor_distrib:
  assumes [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register H\<close> \<open>register L\<close>
  shows \<open>(F \<otimes>\<^sub>r G) o (H \<otimes>\<^sub>r L) = (F o H) \<otimes>\<^sub>r (G o L)\<close>
  apply (rule tensor_extensionality)
  by (auto intro!: register_comp register_preregister register_tensor_is_register)

text \<open>The following is easier to apply using the @{method rule}-method than @{thm [source] separating_tensor}\<close>
lemma separating_tensor':
  fixes A :: \<open>'a::domain update set\<close> and B :: \<open>'b::domain update set\<close>
  assumes \<open>separating TYPE('c::domain) A\<close>
  assumes \<open>separating TYPE('c) B\<close>
  assumes \<open>C = {a \<otimes>\<^sub>u b | a b. a\<in>A \<and> b\<in>B}\<close>
  shows \<open>separating TYPE('c) C\<close>
  using assms
  by (simp add: separating_tensor)

lemma tensor_extensionality3: 
  fixes F G :: \<open>('a::domain\<times>'b::domain\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes "\<And>f g h. F (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = G (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule register_eqI[where A=\<open>{a\<otimes>\<^sub>ub\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>separating TYPE('d) {b \<otimes>\<^sub>u c |b c. True}\<close>
    apply (rule separating_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>separating TYPE('d) {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac separating_tensor'[where A=UNIV and B=\<open>{b\<otimes>\<^sub>uc| b c. True}\<close>])
    by auto
  show \<open>preregister F\<close> \<open>preregister G\<close> by auto
  show \<open>x \<in> {a \<otimes>\<^sub>u b \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed

lemma tensor_extensionality3': 
  fixes F G :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> 'd::domain update\<close>
  assumes [simp]: \<open>register F\<close> \<open>register G\<close>
  assumes "\<And>f g h. F ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = G ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)"
  shows "F = G"
proof (rule register_eqI[where A=\<open>{(a\<otimes>\<^sub>ub)\<otimes>\<^sub>uc| a b c. True}\<close>])
  have \<open>separating TYPE('d) {a \<otimes>\<^sub>u b | a b. True}\<close>
    apply (rule separating_tensor'[where A=UNIV and B=UNIV])
    by auto
  then show \<open>separating TYPE('d) {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True}\<close>
    apply (rule_tac separating_tensor'[where B=UNIV and A=\<open>{a\<otimes>\<^sub>ub| a b. True}\<close>])
    by auto
  show \<open>preregister F\<close> \<open>preregister G\<close> by auto
  show \<open>x \<in> {(a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c |a b c. True} \<Longrightarrow> F x = G x\<close> for x
    using assms(3) by auto
qed

lemma register_tensor_id[simp]: \<open>id \<otimes>\<^sub>r id = id\<close>
  apply (rule tensor_extensionality)
  by (auto simp add: register_tensor_is_register)

subsection \<open>Pairs and compatibility\<close>

definition compatible :: \<open>('a::domain update \<Rightarrow> 'c::domain update)
                       \<Rightarrow> ('b::domain update \<Rightarrow> 'c update) \<Rightarrow> bool\<close> where
  \<open>compatible F G \<longleftrightarrow> register F \<and> register G \<and> (\<forall>a b. F a *\<^sub>u G b = G b *\<^sub>u F a)\<close>

lemma compatibleI:
  assumes "register F" and "register G"
  assumes \<open>\<And>a b. (F a) *\<^sub>u (G b) = (G b) *\<^sub>u (F a)\<close>
  shows "compatible F G"
  using assms unfolding compatible_def by simp

lemma swap_registers:
  assumes "compatible R S"
  shows "R a *\<^sub>u S b = S b *\<^sub>u R a"
  using assms unfolding compatible_def by metis

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  by (simp add: compatible_def)

lemma pair_is_register[simp]:
  assumes "compatible F G"
  shows "register (F; G)"
  by (metis assms compatible_def register_pair_is_register)

lemma register_pair_apply:
  assumes \<open>compatible F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (F a) *\<^sub>u (G b)\<close>
  apply (rule register_pair_apply)
  using assms unfolding compatible_def by metis+

lemma register_pair_apply':
  assumes \<open>compatible F G\<close>
  shows \<open>(F; G) (a \<otimes>\<^sub>u b) = (G b) *\<^sub>u (F a)\<close>
  apply (subst register_pair_apply)
  using assms by (auto simp: compatible_def intro: register_preregister)



lemma compatible_comp_left[simp]: "compatible F G \<Longrightarrow> register H \<Longrightarrow> compatible (F \<circ> H) G"
  by (simp add: compatible_def)

lemma compatible_comp_right[simp]: "compatible F G \<Longrightarrow> register H \<Longrightarrow> compatible F (G \<circ> H)"
  by (simp add: compatible_def)

lemma compatible_comp_inner[simp]: 
  "compatible F G \<Longrightarrow> register H \<Longrightarrow> compatible (H \<circ> F) (H \<circ> G)"
  by (smt (verit, best) comp_apply compatible_def register_comp register_mult)

lemma compatible_register1: \<open>compatible F G \<Longrightarrow> register F\<close>
  by (simp add: compatible_def)
lemma compatible_register2: \<open>compatible F G \<Longrightarrow> register G\<close>
  by (simp add: compatible_def)

lemma pair_o_tensor:
  assumes "compatible A B" and [simp]: \<open>register C\<close> and [simp]: \<open>register D\<close>
  shows "(A; B) o (C \<otimes>\<^sub>r D) = (A o C; B o D)"
  apply (rule tensor_extensionality)
  using assms by (simp_all add: register_tensor_is_register register_pair_apply comp_preregister)

lemma compatible_tensor_id_update_left[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by simp

lemma compatible_tensor_id_update_right[simp]:
  fixes F :: "'a::domain update \<Rightarrow> 'c::domain update" and G :: "'b::domain update \<Rightarrow> 'c::domain update"
  assumes "compatible F G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  using assms apply (rule compatible_comp_inner[unfolded o_def])
  by simp

lemma compatible_tensor_id_update_rl[simp]:
  assumes "register F" and "register G"
  shows "compatible (\<lambda>a. F a \<otimes>\<^sub>u id_update) (\<lambda>a. id_update \<otimes>\<^sub>u G a)"
  apply (rule compatibleI)
  using assms by (auto simp: tensor_update_mult)

lemma compatible_tensor_id_update_lr[simp]:
  assumes "register F" and "register G"
  shows "compatible (\<lambda>a. id_update \<otimes>\<^sub>u F a) (\<lambda>a. G a \<otimes>\<^sub>u id_update)"
  apply (rule compatibleI)
  using assms by (auto simp: tensor_update_mult)

lemma register_comp_pair:
  assumes [simp]: \<open>register F\<close> and [simp]: \<open>compatible G H\<close>
  shows "(F o G; F o H) = F o (G; H)"
proof (rule tensor_extensionality)
  show \<open>preregister (F \<circ> G;F \<circ> H)\<close> and \<open>preregister (F \<circ> (G;H))\<close>
    by simp_all

  have [simp]: \<open>compatible (F o G) (F o H)\<close>
    apply (rule compatible_comp_inner, simp)
    by simp
  then have [simp]: \<open>register (F \<circ> G)\<close> \<open>register (F \<circ> H)\<close>
    unfolding compatible_def by auto
  from assms have [simp]: \<open>register G\<close> \<open>register H\<close>
    unfolding compatible_def by auto
  fix a b
  show \<open>(F \<circ> G;F \<circ> H) (a \<otimes>\<^sub>u b) = (F \<circ> (G;H)) (a \<otimes>\<^sub>u b)\<close>
    by (auto simp: register_pair_apply register_mult tensor_update_mult)
qed

lemma swap_registers_left:
  assumes "compatible R S"
  shows "R a *\<^sub>u S b *\<^sub>u c = S b *\<^sub>u R a *\<^sub>u c"
  using assms unfolding compatible_def by metis

lemma swap_registers_right:
  assumes "compatible R S"
  shows "c *\<^sub>u R a *\<^sub>u S b = c *\<^sub>u S b *\<^sub>u R a"
  by (metis assms comp_update_assoc compatible_def)

lemmas compatible_ac_rules = swap_registers comp_update_assoc[symmetric] swap_registers_right

subsection \<open>Fst and Snd\<close>

definition Fst where \<open>Fst a = a \<otimes>\<^sub>u id_update\<close>
definition Snd where \<open>Snd a = id_update \<otimes>\<^sub>u a\<close>

lemma register_Fst[simp]: \<open>register Fst\<close>
  unfolding Fst_def by (rule register_tensor_left)

lemma register_Snd[simp]: \<open>register Snd\<close>
  unfolding Snd_def by (rule register_tensor_right)

lemma compatible_Fst_Snd[simp]: \<open>compatible Fst Snd\<close>
  apply (rule compatibleI, simp, simp)
  by (simp add: Fst_def Snd_def tensor_update_mult)

lemmas compatible_Snd_Fst[simp] = compatible_Fst_Snd[THEN compatible_sym]

definition \<open>swap = (Snd; Fst)\<close>

lemma swap_apply[simp]: "swap (a \<otimes>\<^sub>u b) = (b \<otimes>\<^sub>u a)"
  unfolding swap_def
  by (simp add: Axioms.register_pair_apply Fst_def Snd_def tensor_update_mult) 

lemma swap_o_Fst: "swap o Fst = Snd"
  by (auto simp add: Fst_def Snd_def)
lemma swap_o_Snd: "swap o Snd = Fst"
  by (auto simp add: Fst_def Snd_def)

lemma register_swap[simp]: \<open>register swap\<close>
  by (simp add: swap_def)

lemma pair_Fst_Snd: \<open>(Fst; Snd) = id\<close>
  apply (rule tensor_extensionality)
  by (simp_all add: register_pair_apply Fst_def Snd_def tensor_update_mult)

lemma swap_o_swap[simp]: \<open>swap o swap = id\<close>
  by (metis swap_def compatible_Snd_Fst pair_Fst_Snd register_comp_pair register_swap swap_o_Fst swap_o_Snd)

lemma swap_swap[simp]: \<open>swap (swap x) = x\<close>
  by (simp add: pointfree_idE)

lemma inv_swap[simp]: \<open>inv swap = swap\<close>
  by (meson inv_unique_comp swap_o_swap)

lemma register_pair_Fst:
  assumes \<open>compatible F G\<close>
  shows \<open>(F;G) o Fst = F\<close>
  using assms by (auto intro!: ext simp: Fst_def register_pair_apply compatible_register2)

lemma register_pair_Snd:
  assumes \<open>compatible F G\<close>
  shows \<open>(F;G) o Snd = G\<close>
  using assms by (auto intro!: ext simp: Snd_def register_pair_apply compatible_register1)

lemma register_Fst_register_Snd[simp]:
  assumes \<open>register F\<close>
  shows \<open>(F o Fst; F o Snd) = F\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: register_pair_apply Fst_def Snd_def register_mult tensor_update_mult)

lemma register_Snd_register_Fst[simp]: 
  assumes \<open>register F\<close>
  shows \<open>(F o Snd; F o Fst) = F o swap\<close>
  apply (rule tensor_extensionality)
  using assms by (auto simp: register_pair_apply Fst_def Snd_def register_mult tensor_update_mult)


lemma compatible3[simp]:
  assumes [simp]: "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible (F; G) H"
proof (rule compatibleI)
  have [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register H\<close>
    using assms compatible_def by auto
  then have [simp]: \<open>preregister F\<close> \<open>preregister G\<close> \<open>preregister H\<close>
    using register_preregister by blast+
  have [simp]: \<open>preregister (\<lambda>a. (F;G) a *\<^sub>u z)\<close> for z
    apply (rule comp_preregister[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have [simp]: \<open>preregister (\<lambda>a. z *\<^sub>u (F;G) a)\<close> for z
    apply (rule comp_preregister[unfolded o_def, of \<open>(F;G)\<close>])
    by simp_all
  have "(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u H h = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)" for f g h
  proof -
    have FH: "F f *\<^sub>u H h = H h *\<^sub>u F f"
      using assms compatible_def by metis
    have GH: "G g *\<^sub>u H h = H h *\<^sub>u G g"
      using assms compatible_def by metis
    have \<open>(F; G) (f \<otimes>\<^sub>u g) *\<^sub>u (H h) = F f *\<^sub>u G g *\<^sub>u H h\<close>
      using \<open>compatible F G\<close> by (subst register_pair_apply, auto)
    also have \<open>\<dots> = H h *\<^sub>u F f *\<^sub>u G g\<close>
      using FH GH by (metis comp_update_assoc)
    also have \<open>\<dots> = H h *\<^sub>u (F; G) (f \<otimes>\<^sub>u g)\<close>
      using \<open>compatible F G\<close> by (subst register_pair_apply, auto simp: comp_update_assoc)
    finally show ?thesis
      by -
  qed
  then show "(F; G) fg *\<^sub>u (H h) = (H h) *\<^sub>u (F; G) fg" for fg h
    apply (rule_tac tensor_extensionality[THEN fun_cong])
    by auto
  show "register H" and  "register (F; G)"
    by simp_all
qed

lemma compatible3'[simp]:
  assumes "compatible F G" and "compatible G H" and "compatible F H"
  shows "compatible F (G; H)"
  apply (rule compatible_sym)
  apply (rule compatible3)
  using assms by (auto simp: compatible_sym)

lemma pair_o_swap[simp]:
  assumes [simp]: "compatible A B"
  shows "(A; B) o swap = (B; A)"
proof (rule tensor_extensionality)
  have [simp]: "preregister A" "preregister B"
     apply (metis (no_types, opaque_lifting) assms compatible_register1 register_preregister)
    by (metis (full_types) assms compatible_register2 register_preregister)
  then show \<open>preregister ((A; B) \<circ> swap)\<close>
    by simp
  show \<open>preregister (B; A)\<close>
    by (metis (no_types, lifting) assms compatible_sym register_preregister pair_is_register)
  show \<open>((A; B) \<circ> swap) (a \<otimes>\<^sub>u b) = (B; A) (a \<otimes>\<^sub>u b)\<close> for a b
    (* Without the "only:", we would not need the "apply subst",
       but that proof fails when instantiated in Classical.thy *)
    apply (simp only: o_def swap_apply)
    apply (subst register_pair_apply, simp)
    apply (subst register_pair_apply, simp add: compatible_sym)
    by (metis (no_types, lifting) assms compatible_def)
qed


subsection \<open>Compatibility of register tensor products\<close>

lemma compatible_register_tensor:
  fixes F :: \<open>'a::domain update \<Rightarrow> 'e::domain update\<close> and G :: \<open>'b::domain update \<Rightarrow> 'f::domain update\<close>
    and F' :: \<open>'c::domain update \<Rightarrow> 'e update\<close> and G' :: \<open>'d::domain update \<Rightarrow> 'f update\<close>
  assumes [simp]: \<open>compatible F F'\<close>
  assumes [simp]: \<open>compatible G G'\<close>
  shows \<open>compatible (F \<otimes>\<^sub>r G) (F' \<otimes>\<^sub>r G')\<close>
proof -
  note [intro!] = 
    comp_preregister[OF _ preregister_mult_right, unfolded o_def]
    comp_preregister[OF _ preregister_mult_left, unfolded o_def]
    comp_preregister
    register_tensor_is_register
  have [simp]: \<open>register F\<close> \<open>register G\<close> \<open>register F'\<close> \<open>register G'\<close>
    using assms compatible_def by blast+
  have [simp]: \<open>register (F \<otimes>\<^sub>r G)\<close> \<open>register (F' \<otimes>\<^sub>r G')\<close>
    by (auto simp add: register_tensor_def)
  have [simp]: \<open>register (F;F')\<close> \<open>register (G;G')\<close>
    by auto
  define reorder :: \<open>(('a\<times>'b) \<times> ('c\<times>'d)) update \<Rightarrow> (('a\<times>'c) \<times> ('b\<times>'d)) update\<close>
    where \<open>reorder = ((Fst o Fst; Snd o Fst); (Fst o Snd; Snd o Snd))\<close>
  have [simp]: \<open>preregister reorder\<close>
    by (auto simp: reorder_def)
  have [simp]: \<open>reorder ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u (c \<otimes>\<^sub>u d)) = ((a \<otimes>\<^sub>u c) \<otimes>\<^sub>u (b \<otimes>\<^sub>u d))\<close> for a b c d
    apply (simp add: reorder_def register_pair_apply)
    by (simp add: Fst_def Snd_def tensor_update_mult)
  define \<Phi> where \<open>\<Phi> c d = ((F;F') \<otimes>\<^sub>r (G;G')) o reorder o (\<lambda>\<sigma>. \<sigma> \<otimes>\<^sub>u (c \<otimes>\<^sub>u d))\<close> for c d
  have [simp]: \<open>preregister (\<Phi> c d)\<close> for c d
    unfolding \<Phi>_def 
    by (auto intro: register_preregister)
  have \<open>\<Phi> c d (a \<otimes>\<^sub>u b) = (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b) *\<^sub>u (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d)\<close> for a b c d
    unfolding \<Phi>_def by (auto simp: register_pair_apply tensor_update_mult)
  then have \<Phi>1: \<open>\<Phi> c d \<sigma> = (F \<otimes>\<^sub>r G) \<sigma> *\<^sub>u (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d)\<close> for c d \<sigma>
    apply (rule_tac fun_cong[of _ _ \<sigma>])
    apply (rule tensor_extensionality)
    by auto
  have \<open>\<Phi> c d (a \<otimes>\<^sub>u b) = (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d) *\<^sub>u (F \<otimes>\<^sub>r G) (a \<otimes>\<^sub>u b)\<close> for a b c d
    unfolding \<Phi>_def apply (auto simp: register_pair_apply)
    by (metis assms(1) assms(2) compatible_def tensor_update_mult)
  then have \<Phi>2: \<open>\<Phi> c d \<sigma> = (F' \<otimes>\<^sub>r G') (c \<otimes>\<^sub>u d) *\<^sub>u (F \<otimes>\<^sub>r G) \<sigma>\<close> for c d \<sigma>
    apply (rule_tac fun_cong[of _ _ \<sigma>])
    apply (rule tensor_extensionality)
    by auto
  from \<Phi>1 \<Phi>2 have \<open>(F \<otimes>\<^sub>r G) \<sigma> *\<^sub>u (F' \<otimes>\<^sub>r G') \<tau> = (F' \<otimes>\<^sub>r G') \<tau> *\<^sub>u (F \<otimes>\<^sub>r G) \<sigma>\<close> for \<tau> \<sigma>
    apply (rule_tac fun_cong[of _ _ \<tau>])
    apply (rule tensor_extensionality)
    by auto
  then show ?thesis
    apply (rule compatibleI[rotated -1])
    by auto
qed

subsection \<open>Associativity of the tensor product\<close>

definition assoc :: \<open>(('a::domain\<times>'b::domain)\<times>'c::domain) update \<Rightarrow> ('a\<times>('b\<times>'c)) update\<close> where 
  \<open>assoc = ((Fst; Snd o Fst); Snd o Snd)\<close>

lemma assoc_is_hom[simp]: \<open>preregister assoc\<close>
  by (auto simp: assoc_def)

lemma assoc_apply[simp]: \<open>assoc ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c) = (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c))\<close>
  by (auto simp: assoc_def register_pair_apply Fst_def Snd_def tensor_update_mult)

definition assoc' :: \<open>('a\<times>('b\<times>'c)) update \<Rightarrow> (('a::domain\<times>'b::domain)\<times>'c::domain) update\<close> where 
  \<open>assoc' = (Fst o Fst; (Fst o Snd; Snd))\<close>

lemma assoc'_is_hom[simp]: \<open>preregister assoc'\<close>
  by (auto simp: assoc'_def)

lemma assoc'_apply[simp]: \<open>assoc' (a \<otimes>\<^sub>u (b \<otimes>\<^sub>u c)) =  ((a \<otimes>\<^sub>u b) \<otimes>\<^sub>u c)\<close>
  by (auto simp: assoc'_def register_pair_apply Fst_def Snd_def tensor_update_mult)

lemma register_assoc[simp]: \<open>register assoc\<close>
  unfolding assoc_def
  by force

lemma register_assoc'[simp]: \<open>register assoc'\<close>
  unfolding assoc'_def 
  by force

lemma pair_o_assoc[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible G H\<close> \<open>compatible F H\<close>
  shows \<open>(F; (G; H)) \<circ> assoc = ((F; G); H)\<close>
proof (rule tensor_extensionality3')
  show \<open>register ((F; (G; H)) \<circ> assoc)\<close>
    by simp
  show \<open>register ((F; G); H)\<close>
    by simp
  show \<open>((F; (G; H)) \<circ> assoc) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h) = ((F; G); H) ((f \<otimes>\<^sub>u g) \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: register_pair_apply assoc_apply comp_update_assoc)
qed

lemma pair_o_assoc'[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible G H\<close> \<open>compatible F H\<close>
  shows \<open>((F; G); H) \<circ> assoc' = (F; (G; H))\<close>
proof (rule tensor_extensionality3)
  show \<open>register (((F; G); H) \<circ> assoc')\<close>
    by simp
  show \<open>register (F; (G; H))\<close>
    by simp
  show \<open>(((F; G); H) \<circ> assoc') (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h) = (F; (G; H)) (f \<otimes>\<^sub>u g \<otimes>\<^sub>u h)\<close> for f g h
    by (simp add: register_pair_apply assoc'_apply comp_update_assoc)
qed

lemma assoc'_o_assoc[simp]: \<open>assoc' o assoc = id\<close>
  apply (rule tensor_extensionality3')
  by auto

lemma assoc'_assoc[simp]: \<open>assoc' (assoc x) = x\<close>
  by (simp add: pointfree_idE)

lemma assoc_o_assoc'[simp]: \<open>assoc o assoc' = id\<close>
  apply (rule tensor_extensionality3)
  by auto

lemma assoc_assoc'[simp]: \<open>assoc (assoc' x) = x\<close>
  by (simp add: pointfree_idE)

lemma inv_assoc[simp]: \<open>inv assoc = assoc'\<close>
  using assoc'_o_assoc assoc_o_assoc' inv_unique_comp by blast

lemma inv_assoc'[simp]: \<open>inv assoc' = assoc\<close>
  by (simp add: inv_equality)

lemma [simp]: \<open>bij assoc\<close>
  using assoc'_o_assoc assoc_o_assoc' o_bij by blast

lemma [simp]: \<open>bij assoc'\<close>
  using assoc'_o_assoc assoc_o_assoc' o_bij by blast

subsection \<open>Iso-registers\<close>

definition \<open>iso_register F \<longleftrightarrow> register F \<and> (\<exists>G. register G \<and> F o G = id \<and> G o F = id)\<close>
  for F :: \<open>_::domain update \<Rightarrow> _::domain update\<close>

lemma iso_registerI:
  assumes \<open>register F\<close> \<open>register G\<close> \<open>F o G = id\<close> \<open>G o F = id\<close>
  shows \<open>iso_register F\<close>
  using assms(1) assms(2) assms(3) assms(4) iso_register_def by blast

lemma iso_register_inv: \<open>iso_register F \<Longrightarrow> iso_register (inv F)\<close>
  by (metis inv_unique_comp iso_register_def)

lemma iso_register_inv_comp1: \<open>iso_register F \<Longrightarrow> inv F o F = id\<close>
  using inv_unique_comp iso_register_def by blast

lemma iso_register_inv_comp2: \<open>iso_register F \<Longrightarrow> F o inv F = id\<close>
  using inv_unique_comp iso_register_def by blast


lemma iso_register_id[simp]: \<open>iso_register id\<close>
  by (simp add: iso_register_def)

lemma iso_register_is_register: \<open>iso_register F \<Longrightarrow> register F\<close>
  using iso_register_def by blast

lemma iso_register_comp[simp]:
  assumes [simp]: \<open>iso_register F\<close> \<open>iso_register G\<close>
  shows \<open>iso_register (F o G)\<close>
proof -
  from assms obtain F' G' where [simp]: \<open>register F'\<close> \<open>register G'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    by (meson iso_register_def)
  show ?thesis
    apply (rule iso_registerI[where G=\<open>G' o F'\<close>])
       apply (auto simp: register_tensor_is_register iso_register_is_register register_tensor_distrib)
     apply (metis \<open>F \<circ> F' = id\<close> \<open>G \<circ> G' = id\<close> fcomp_assoc fcomp_comp id_fcomp)
    by (metis (no_types, lifting) \<open>F \<circ> F' = id\<close> \<open>F' \<circ> F = id\<close> \<open>G' \<circ> G = id\<close> fun.map_comp inj_iff inv_unique_comp o_inv_o_cancel)
qed


lemma iso_register_tensor_is_iso_register[simp]:
  assumes [simp]: \<open>iso_register F\<close> \<open>iso_register G\<close>
  shows \<open>iso_register (F \<otimes>\<^sub>r G)\<close>
proof -
  from assms obtain F' G' where [simp]: \<open>register F'\<close> \<open>register G'\<close> \<open>F o F' = id\<close> \<open>F' o F = id\<close>
    \<open>G o G' = id\<close> \<open>G' o G = id\<close>
    by (meson iso_register_def)
  show ?thesis
    apply (rule iso_registerI[where G=\<open>F' \<otimes>\<^sub>r G'\<close>])
    by (auto simp: register_tensor_is_register iso_register_is_register register_tensor_distrib)
qed

lemma iso_register_bij: \<open>iso_register F \<Longrightarrow> bij F\<close>
  using iso_register_def o_bij by auto

lemma inv_register_tensor[simp]: 
  assumes [simp]: \<open>iso_register F\<close> \<open>iso_register G\<close>
  shows \<open>inv (F \<otimes>\<^sub>r G) = inv F \<otimes>\<^sub>r inv G\<close>
  apply (auto intro!: inj_imp_inv_eq bij_is_inj iso_register_bij 
              simp: register_tensor_distrib[unfolded o_def, THEN fun_cong] iso_register_is_register
                    iso_register_inv bij_is_surj iso_register_bij surj_f_inv_f)
  by (metis eq_id_iff register_tensor_id)

lemma iso_register_swap[simp]: \<open>iso_register swap\<close>
  apply (rule iso_registerI[of _ swap])
  by auto

lemma iso_register_assoc[simp]: \<open>iso_register assoc\<close>
  apply (rule iso_registerI[of _ assoc'])
  by auto

lemma iso_register_assoc'[simp]: \<open>iso_register assoc'\<close>
  apply (rule iso_registerI[of _ assoc])
  by auto

definition \<open>equivalent_registers F G \<longleftrightarrow> (register F \<and> (\<exists>I. iso_register I \<and> F o I = G))\<close>
  for F G :: \<open>_::domain update \<Rightarrow> _::domain update\<close>

lemma iso_register_equivalent_id[simp]: \<open>equivalent_registers id F \<longleftrightarrow> iso_register F\<close>
  by (simp add: equivalent_registers_def)

lemma equivalent_registersI:
  assumes \<open>register F\<close>
  assumes \<open>iso_register I\<close>
  assumes \<open>F o I = G\<close>
  shows \<open>equivalent_registers F G\<close>
  using assms unfolding equivalent_registers_def by blast

lemma equivalent_registers_register_left: \<open>equivalent_registers F G \<Longrightarrow> register F\<close>
  using equivalent_registers_def by auto

lemma equivalent_registers_register_right: \<open>register G\<close> if \<open>equivalent_registers F G\<close>
  by (metis equivalent_registers_def iso_register_def register_comp that)

lemma equivalent_registers_sym:
  assumes \<open>equivalent_registers F G\<close>
  shows \<open>equivalent_registers G F\<close>
  by (smt (verit) assms comp_id equivalent_registers_def equivalent_registers_register_right fun.map_comp iso_register_def)

lemma equivalent_registers_trans[trans]: 
  assumes \<open>equivalent_registers F G\<close> and \<open>equivalent_registers G H\<close>
  shows \<open>equivalent_registers F H\<close>
proof -
  from assms have [simp]: \<open>register F\<close> \<open>register G\<close>
    by (auto simp: equivalent_registers_def)
  from assms(1) obtain I where [simp]: \<open>iso_register I\<close> and \<open>F o I = G\<close>
    using equivalent_registers_def by blast
  from assms(2) obtain J where [simp]: \<open>iso_register J\<close> and \<open>G o J = H\<close>
    using equivalent_registers_def by blast
  have \<open>register F\<close>
    by (auto simp: equivalent_registers_def)
  moreover have \<open>iso_register (I o J)\<close>
    using \<open>iso_register I\<close> \<open>iso_register J\<close> iso_register_comp by blast
  moreover have \<open>F o (I o J) = H\<close>
    by (simp add: \<open>F \<circ> I = G\<close> \<open>G \<circ> J = H\<close> o_assoc)
  ultimately show ?thesis
    by (rule equivalent_registersI)
qed

lemma equivalent_registers_assoc[simp]:
  assumes [simp]: \<open>compatible F G\<close> \<open>compatible F H\<close> \<open>compatible G H\<close>
  shows \<open>equivalent_registers (F;(G;H)) ((F;G);H)\<close>
  apply (rule equivalent_registersI[where I=assoc])
  by auto

lemma equivalent_registers_pair_right:
  assumes [simp]: \<open>compatible F G\<close>
  assumes eq: \<open>equivalent_registers G H\<close>
  shows \<open>equivalent_registers (F;G) (F;H)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_register I\<close> and \<open>G o I = H\<close>
    by (metis equivalent_registers_def)
  then have *: \<open>(F;G) \<circ> (id \<otimes>\<^sub>r I) = (F;H)\<close>
    by (auto intro!: tensor_extensionality register_comp register_preregister register_tensor_is_register 
        simp:  register_pair_apply iso_register_is_register)
  show ?thesis
    apply (rule equivalent_registersI[where I=\<open>id \<otimes>\<^sub>r I\<close>])
    using * by (auto intro!: iso_register_tensor_is_iso_register)
qed

lemma equivalent_registers_pair_left:
  assumes [simp]: \<open>compatible F G\<close>
  assumes eq: \<open>equivalent_registers F H\<close>
  shows \<open>equivalent_registers (F;G) (H;G)\<close>
proof -
  from eq obtain I where [simp]: \<open>iso_register I\<close> and \<open>F o I = H\<close>
    by (metis equivalent_registers_def)
  then have *: \<open>(F;G) \<circ> (I \<otimes>\<^sub>r id) = (H;G)\<close>
    by (auto intro!: tensor_extensionality register_comp register_preregister register_tensor_is_register 
        simp:  register_pair_apply iso_register_is_register)
  show ?thesis
    apply (rule equivalent_registersI[where I=\<open>I \<otimes>\<^sub>r id\<close>])
    using * by (auto intro!: iso_register_tensor_is_iso_register)
qed

lemma equivalent_registers_comp:
  assumes \<open>register H\<close>
  assumes \<open>equivalent_registers F G\<close>
  shows \<open>equivalent_registers (H o F) (H o G)\<close>
  by (metis (no_types, lifting) assms(1) assms(2) comp_assoc equivalent_registers_def register_comp)

subsection \<open>Compatibility simplification\<close>

text \<open>The simproc \<open>compatibility_warn\<close> produces helpful warnings for subgoals of the form
   \<^term>\<open>compatible x y\<close> that are probably unsolvable due to missing declarations of 
   variable compatibility facts. Same for subgoals of the form \<^term>\<open>register x\<close>.\<close>
simproc_setup "compatibility_warn" ("compatible x y" | "register x") = \<open>
let val thy_string = Markup.markup (Theory.get_markup \<^theory>) (Context.theory_name \<^theory>)
in
fn m => fn ctxt => fn ct => let
  val (x,y) = case Thm.term_of ct of
                 Const(\<^const_name>\<open>compatible\<close>,_ ) $ x $ y => (x, SOME y)
               | Const(\<^const_name>\<open>register\<close>,_ ) $ x => (x, NONE)
  val str : string lazy = Lazy.lazy (fn () => Syntax.string_of_term ctxt (Thm.term_of ct))
  fun w msg = warning (msg ^ "\n(Disable these warnings with: using [[simproc del: "^thy_string^".compatibility_warn]])")
  val _ = case (x,y) of
        (Free(n,T), SOME (Free(n',T'))) => 
            if String.isPrefix ":" n orelse String.isPrefix ":" n' then 
                      w ("Simplification subgoal " ^ Lazy.force str ^ " contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else if n=n' then (if T=T' then () 
                          else w ("In simplification subgoal " ^ Lazy.force str ^ 
                               ", variables have same name and different types.\n" ^
                               "Probably something is wrong."))
                    else w ("Simplification subgoal " ^ Lazy.force str ^ 
                            " occurred but cannot be solved.\n" ^
                            "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ 
                            "\<close>  somewhere.")
      | (Free(n,T), NONE) => 
            if String.isPrefix ":" n then 
                      w ("Simplification subgoal '" ^ Lazy.force str ^ "' contains a bound variable.\n" ^
                      "Try to add some assumptions that makes this goal solvable by the simplifier")
            else w ("Simplification subgoal " ^ Lazy.force str ^ " occurred but cannot be solved.\n" ^
                    "Please add assumption/fact  [simp]: \<open>" ^ Lazy.force str ^ "\<close>  somewhere.")
      | _ => ()
  in NONE end
end\<close>


named_theorems register_attribute_rule_immediate
named_theorems register_attribute_rule

lemmas [register_attribute_rule] = conjunct1 conjunct2 iso_register_is_register iso_register_is_register[OF iso_register_inv]
lemmas [register_attribute_rule_immediate] = compatible_sym compatible_register1 compatible_register2
  asm_rl[of \<open>compatible _ _\<close>] asm_rl[of \<open>iso_register _\<close>] asm_rl[of \<open>register _\<close>] iso_register_inv

text \<open>The following declares an attribute \<open>[register]\<close>. When the attribute is applied to a fact
  of the form \<^term>\<open>register F\<close>, \<^term>\<open>iso_register F\<close>, \<^term>\<open>compatible F G\<close> or a conjunction of these,
  then those facts are added to the simplifier together with some derived theorems
  (e.g., \<^term>\<open>compatible F G\<close> also adds \<^term>\<open>register F\<close>).

  In theory \<open>Laws_Complement\<close>, support for \<^term>\<open>is_unit_register F\<close> and \<^term>\<open>complements F G\<close> is
  added to this attribute.\<close>

setup \<open>
let
fun add thm results = 
  Net.insert_term (K true) (Thm.concl_of thm, thm) results
  handle Net.INSERT => results
fun try_rule f thm rule state = case SOME (rule OF [thm]) handle THM _ => NONE  of
  NONE => state | SOME th => f th state
fun collect (rules,rules_immediate) thm results =
  results |> fold (try_rule add thm) rules_immediate |> fold (try_rule (collect (rules,rules_immediate)) thm) rules
fun declare thm context = let
  val ctxt = Context.proof_of context
  val rules = Named_Theorems.get ctxt @{named_theorems register_attribute_rule}
  val rules_immediate = Named_Theorems.get ctxt @{named_theorems register_attribute_rule_immediate}
  val thms = collect (rules,rules_immediate) thm Net.empty |> Net.entries
  (* val _ = \<^print> thms *)
  in Simplifier.map_ss (fn ctxt => ctxt addsimps thms) context end
in
Attrib.setup \<^binding>\<open>register\<close>
 (Scan.succeed (Thm.declaration_attribute declare))
  "Add register-related rules to the simplifier"
end
\<close>

subsection \<open>Notation\<close>

no_notation comp_update (infixl "*\<^sub>u" 55)
no_notation tensor_update (infixr "\<otimes>\<^sub>u" 70)

bundle register_notation begin
notation register_tensor (infixr "\<otimes>\<^sub>r" 70)
notation register_pair ("'(_;_')")
end

bundle no_register_notation begin
no_notation register_tensor (infixr "\<otimes>\<^sub>r" 70)
no_notation register_pair ("'(_;_')")
end

end
