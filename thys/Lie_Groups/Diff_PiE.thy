(*  Title:       Diff_PiE
    Author:      Richard Schmoetten <richard.schmoetten@ed.ac.uk>, 2024
    Maintainer:  Richard Schmoetten <richard.schmoetten@ed.ac.uk>
*)

theory Diff_PiE
imports
  More_Manifolds
  "HOL-Library.FuncSet"
begin

lemma Pi\<^sub>E_iff: "f \<in> A\<rightarrow>\<^sub>EB \<longleftrightarrow> (\<forall>a\<in>A. f a \<in> B) \<and> (\<forall>a. a\<notin>A \<longrightarrow> f a = undefined)" by auto
lemma "f x = None \<Longrightarrow> x \<notin> dom f" by (simp add: domIff)
lemma "f \<in> D\<rightarrow>\<^sub>EC \<Longrightarrow> f x = undefined \<Longrightarrow> x\<notin>D" oops
lemma "f \<in> D\<rightarrow>\<^sub>EC \<Longrightarrow> x\<notin>D \<Longrightarrow> f x \<notin> C" oops
lemma "f \<in> D\<rightarrow>\<^sub>EC \<Longrightarrow> f x \<notin> C \<Longrightarrow> x\<notin>D" by auto


section \<open>Automorphisms using the function set\<close>

locale automorphism_PiE = c_manifold begin

definition automorphism_PiE :: "('a\<Rightarrow>'a) \<Rightarrow> bool"
  where "automorphism_PiE f \<equiv> (\<exists>f'\<in>carrier\<rightarrow>\<^sub>Ecarrier. c_automorphism k charts f f') \<and> f\<in>carrier\<rightarrow>\<^sub>Ecarrier"

lemma automorphism_PiED [dest]:
  assumes "automorphism_PiE f"
  shows "\<exists>f'\<in>carrier\<rightarrow>\<^sub>Ecarrier. c_automorphism k charts f f'"
    and "f\<in>carrier\<rightarrow>\<^sub>Ecarrier" and "bij_betw f carrier carrier"
  using assms diffeomorphism.is_bij_betw[of k charts charts f] by (auto simp: automorphism_PiE_def c_automorphism_def)

lemma automorphism_PiED2:
  assumes "automorphism_PiE f"
  obtains f' where "f'\<in>carrier\<rightarrow>\<^sub>Ecarrier" "c_automorphism k charts f f'" "bij_betw f carrier carrier"
  using automorphism_PiED[OF assms] by blast

lemma automorphism_PiEI [intro]:
  assumes "\<exists>f'\<in>carrier\<rightarrow>\<^sub>Ecarrier. c_automorphism k charts f f'"
    and "f\<in>carrier\<rightarrow>\<^sub>Ecarrier" and "bij_betw f carrier carrier"
  shows "automorphism_PiE f"
  using assms by (auto simp: automorphism_PiE_def)

lemma automorphism_PiE_partial_id: "automorphism_PiE (restrict id carrier)"
  apply (intro automorphism_PiEI exI c_automorphism.intro)
  apply (smt (verit, best) c_automorphism.automorphism_cong' c_automorphism.c_automorphism_cong c_automorphism.intro id_apply id_diffeomorphism restrict_PiE_iff restrict_apply')
  by auto

lemma automorphism_PiE_openin:
  assumes "automorphism_PiE f" "openin (top_of_set carrier) S"
  shows "openin (top_of_set carrier) (f ` S)"
  using assms diffeomorphism.is_homeomorphism homeomorphism_imp_open_map
  unfolding automorphism_PiE_def c_automorphism_def
  by metis

lemma automorphism_surj_inj:
  assumes "automorphism_PiE f"
  shows "f ` carrier = carrier" "inj_on f carrier"
  using automorphism_PiED[OF assms] by (meson bij_betw_imp_surj_on bij_betw_imp_inj_on)+

lemma the_inverse_aut_PiE:
  fixes f g
  defines f' [simp]: "f' \<equiv> \<lambda>y::'a. if y\<in>carrier then g y else undefined"
  assumes f: "f\<in>carrier\<rightarrow>\<^sub>Ecarrier" "bij_betw f carrier carrier" and g: "g\<in>carrier\<rightarrow>\<^sub>Ecarrier" "c_automorphism k charts f g"
  shows "automorphism_PiE f'"
    and "\<And>x. x \<in> carrier \<Longrightarrow> (f' ((f x))) = x"
    and "\<And>x. x \<in> carrier \<Longrightarrow> (f ((f' x))) = x"
proof -

  have diff_f': "diff k charts charts f'"
    using c_automorphism.inverse_automorphism g diff.diff_cong
    unfolding c_automorphism_def diffeomorphism_def f'
    by fastforce

  text \<open>Finding an inverse diffeomorphism is the main part of this proof.\<close>
  have diffeo_f': "diffeomorphism k charts charts f' f"
    apply (intro diffeomorphism.intro diffeomorphism_axioms.intro conjI)
    subgoal using diff_f' .
    subgoal using assms unfolding automorphism_PiE_def c_automorphism_def diffeomorphism_def by simp
    subgoal by (simp, metis c_automorphism.axioms(1) diffeomorphism.f'_inv g(2))
    subgoal using c_automorphism.in_dest diffeomorphism.f_inv g by (simp add: c_automorphism_def, blast)
    done

  show "automorphism_PiE f'"
    apply (intro automorphism_PiEI exI[of _ f])
    using c_automorphism.intro diffeo_f' f(1) apply blast
    using c_automorphism.in_dest c_automorphism.intro diffeo_f' apply fastforce
    by (smt (verit, ccfv_SIG) bij_betwE bij_betwI' diff.defined diff_f' diffeo_f' diffeomorphism.f'_inv diffeomorphism.f_inv f(2) image_eqI subsetD)

  { fix x assume "x \<in> carrier"
    show "f' (f x) = x"
      using \<open>x \<in> carrier\<close> diffeo_f' diffeomorphism.f'_inv by blast
    show "f (f' x) = x"
      using \<open>x \<in> carrier\<close> diffeo_f' diffeomorphism.f_inv by blast }
qed

lemma obtain_inverse_aut_PiE:
  assumes "automorphism_PiE f"
  obtains f' where "automorphism_PiE f'"
    and "\<And>x. x \<in> carrier \<Longrightarrow> (f' ((f x))) = x"
    and "\<And>x. x \<in> carrier \<Longrightarrow> (f ((f' x))) = x"
  using the_inverse_aut_PiE automorphism_PiED[OF assms] by blast

abbreviation Diff_comp_PiE (infixl \<open>\<circ>\<^sub>c\<close> 80)
  where "Diff_comp_PiE \<equiv> compose carrier"

lemma aut_comp_simps [simp]: "(g \<circ>\<^sub>c f) x = g (f x)"
    "automorphism_PiE g \<Longrightarrow> \<exists>z\<in>carrier. z = (g \<circ>\<^sub>c f) x"
  if "x \<in> carrier" "automorphism_PiE f" for x
  subgoal by (simp add: compose_eq that(1))
  subgoal by (metis (no_types, lifting) automorphism_surj_inj(1) image_eqI surj_compose that)
  done

lemma aut_to [simp]: "f x \<in> carrier" if "automorphism_PiE f" "x \<in> carrier"
  using automorphism_surj_inj(1) that by auto

lemma automorphism_PiE_ran: "{f x | x. x \<in> carrier} = carrier" if aut_f: "automorphism_PiE f"
proof -
  have "\<exists>y. x = f y \<and> y \<in> carrier" if "x \<in> carrier" for x
    using aut_to obtain_inverse_aut_PiE that aut_f by metis
  thus ?thesis by (auto simp: that)
qed

lemma aut_comp:
  assumes "automorphism_PiE f" "automorphism_PiE g"
  shows "automorphism_PiE (g \<circ>\<^sub>c f)"
proof (intro automorphism_PiEI)

  obtain f' where f': "c_automorphism k charts (\<lambda>x. f x) f'" and f: "f\<in>carrier\<rightarrow>\<^sub>Ecarrier" "bij_betw f carrier carrier"
    using automorphism_PiED[OF assms(1)] by blast
  obtain g' where g': "c_automorphism k charts (\<lambda>x. g x) g'" and g: "g\<in>carrier\<rightarrow>\<^sub>Ecarrier" "bij_betw g carrier carrier"
    using automorphism_PiED[OF assms(2)] by blast

  have aut_comp: "c_automorphism k charts (\<lambda>x. g (f x)) (f' \<circ> g')"
    using c_automorphism.automorphism_compose[OF f' g'] c_automorphism.c_automorphism_cong
    by fastforce
  have aut_compc: "c_automorphism k charts (g \<circ>\<^sub>c f) (f' \<circ>\<^sub>c g')"
  proof -
    have "diff k charts charts (\<lambda>x\<in>carrier. g (f x))" "diff k charts charts (\<lambda>x\<in>carrier. f' (g' x))"
      using aut_comp[unfolded compose_def c_automorphism_def diffeomorphism_def] diff.diff_cong
      unfolding restrict_def by fastforce+
    moreover have "diffeomorphism_axioms charts charts (\<lambda>x\<in>carrier. g (f x)) (\<lambda>x\<in>carrier. f' (g' x))"
    proof
      fix x assume x: "x\<in>carrier"
      have "f' (g' (g (f x))) = x"
        using aut_comp x c_automorphism.axioms diffeomorphism.f_inv by fastforce
      moreover have "f' (g' x) \<in> carrier \<Longrightarrow> g (f (f' (g' x))) = x"
        using aut_comp x c_automorphism.axioms diffeomorphism.f'_inv by fastforce
      moreover have "f' (g' x) \<notin> carrier \<Longrightarrow> undefined = x"
        using x c_automorphism.in_dest c_automorphism.inverse_automorphism f' g' by meson
      ultimately show "(\<lambda>z\<in>carrier. f' (g' z)) ((\<lambda>z\<in>carrier. g (f z)) x) = x"
        and "(\<lambda>z\<in>carrier. g (f z)) ((\<lambda>z\<in>carrier. f' (g' z)) x) = x"
        by (metis assms aut_to restrict_apply)+
    qed
    ultimately show ?thesis
      unfolding compose_def c_automorphism_def diffeomorphism_def by simp
  qed
  show "\<exists>f'\<in>carrier \<rightarrow>\<^sub>E carrier. c_automorphism k charts (g \<circ>\<^sub>c f) f'"
    apply (intro bexI[of _ "f' \<circ>\<^sub>c g'"] PiE_I)
    using aut_compc c_automorphism.in_dest c_automorphism.inverse_automorphism
    by (simp, blast, simp add: compose_def)
  show "g \<circ>\<^sub>c f \<in> carrier \<rightarrow>\<^sub>E carrier"
    by (simp add: assms compose_def extensional_funcset_def)
  show "bij_betw (g \<circ>\<^sub>c f) carrier carrier"
    using automorphism_PiED(3) assms by (auto intro: bij_betw_compose)
qed

definition "Diff_PiE \<equiv> {f. automorphism_PiE f}"

lemma Diff_PiED [dest]: "f \<in> Diff_PiE \<Longrightarrow> automorphism_PiE f" by (simp add: Diff_PiE_def)
lemma Diff_PiEI [intro]: "automorphism_PiE f \<Longrightarrow> f \<in> Diff_PiE" by (simp add: Diff_PiE_def)

abbreviation (*input*) "Diff_id_PiE \<equiv> \<lambda>x\<in>carrier. x"

lemma Diff_grp: "grp_on Diff_PiE (\<circ>\<^sub>c) Diff_id_PiE"
proof (unfold_locales)

  show assoc: "Diff_comp_PiE (Diff_comp_PiE a b) c = Diff_comp_PiE a (Diff_comp_PiE b c)"
    if asms: "a \<in> Diff_PiE" "b \<in> Diff_PiE" "c \<in> Diff_PiE" for a b c
    unfolding compose_def using Diff_PiED that(3) by auto

  show id_comp: "Diff_comp_PiE Diff_id_PiE a = a \<and> Diff_comp_PiE a Diff_id_PiE = a" if "a \<in> Diff_PiE" for a
    using Id_compose compose_Id automorphism_PiED Diff_PiED that by (metis extensional_funcset_def Int_iff eq_id_iff)

  show id_mem: "Diff_id_PiE \<in> Diff_PiE"
    using automorphism_PiE_partial_id by (metis Diff_PiEI eq_id_iff)

  { fix x y assume x: "x\<in>Diff_PiE" and y: "y\<in>Diff_PiE"
    show "Diff_comp_PiE x y \<in> Diff_PiE"
      using aut_comp Diff_PiED x y by auto }

  show "\<forall>x\<in>Diff_PiE. \<exists>y\<in>Diff_PiE. x \<circ>\<^sub>c y = Diff_id_PiE \<and> y \<circ>\<^sub>c x = Diff_id_PiE"
  proof
    fix f assume f: "f\<in>Diff_PiE"
    then obtain f' where f': "f'\<in>Diff_PiE" "\<forall>x \<in> carrier. (f' ((f x))) = x" "\<forall>x \<in> carrier. (f ((f' x))) = x"
        using obtain_inverse_aut_PiE[OF Diff_PiED[OF f]] Diff_PiEI by metis
    then show "\<exists>y\<in>Diff_PiE. f \<circ>\<^sub>c y = Diff_id_PiE \<and> y \<circ>\<^sub>c f = Diff_id_PiE"
      apply (intro bexI[OF _ f'(1)]) unfolding compose_def id_def restrict_def by meson
  qed
qed

end

end
