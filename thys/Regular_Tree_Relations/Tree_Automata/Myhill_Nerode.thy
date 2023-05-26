theory Myhill_Nerode
  imports Tree_Automata Ground_Ctxt
begin

subsection \<open>Myhill Nerode characterization for regular tree languages\<close>

lemma ground_ctxt_apply_pres_der:
  assumes "ta_der \<A> (term_of_gterm s) = ta_der \<A> (term_of_gterm t)"
  shows "ta_der \<A> (term_of_gterm C\<langle>s\<rangle>\<^sub>G) = ta_der \<A> (term_of_gterm C\<langle>t\<rangle>\<^sub>G)" using assms
  by (induct C) (auto, (metis append_Cons_nth_not_middle nth_append_length)+)

locale myhill_nerode =
  fixes \<F> \<L> assumes term_subset: "\<L> \<subseteq> \<T>\<^sub>G \<F>"
begin

definition myhill ("_ \<equiv>\<^sub>\<L> _") where
  "myhill s t \<equiv> s \<in> \<T>\<^sub>G \<F> \<and> t \<in> \<T>\<^sub>G \<F> \<and> (\<forall> C. C\<langle>s\<rangle>\<^sub>G \<in> \<L> \<and> C\<langle>t\<rangle>\<^sub>G \<in> \<L> \<or> C\<langle>s\<rangle>\<^sub>G \<notin> \<L> \<and> C\<langle>t\<rangle>\<^sub>G \<notin> \<L>)"

lemma myhill_sound: "s \<equiv>\<^sub>\<L> t \<Longrightarrow> s \<in> \<T>\<^sub>G \<F>"  "s \<equiv>\<^sub>\<L> t \<Longrightarrow> t \<in> \<T>\<^sub>G \<F>"
  unfolding myhill_def by auto

lemma myhill_refl [simp]: "s \<in> \<T>\<^sub>G \<F> \<Longrightarrow> s \<equiv>\<^sub>\<L> s"
  unfolding myhill_def by auto

lemma myhill_symmetric: "s \<equiv>\<^sub>\<L> t \<Longrightarrow> t \<equiv>\<^sub>\<L> s"
  unfolding myhill_def by auto

lemma myhill_trans [trans]:
  "s \<equiv>\<^sub>\<L> t \<Longrightarrow> t \<equiv>\<^sub>\<L> u \<Longrightarrow> s \<equiv>\<^sub>\<L> u"
  unfolding myhill_def by auto

abbreviation myhill_r ("MN\<^sub>\<L>") where
  "myhill_r \<equiv> {(s, t) | s t. s \<equiv>\<^sub>\<L> t}"

lemma myhill_equiv:
  "equiv (\<T>\<^sub>G \<F>) MN\<^sub>\<L>"
  apply (intro equivI) apply (auto simp: myhill_sound myhill_symmetric sym_def trans_def refl_on_def)
  using myhill_trans by blast

lemma rtl_der_image_on_myhill_inj:
  assumes "gta_lang Q\<^sub>f \<A> = \<L>"
  shows "inj_on (\<lambda> X. gta_der \<A> ` X) (\<T>\<^sub>G \<F> // MN\<^sub>\<L>)" (is "inj_on ?D ?R")
proof -
  {fix S T assume eq_rel: "S \<in> ?R" "T \<in> ?R" "?D S = ?D T"
    have "\<And> s t. s \<in> S \<Longrightarrow> t \<in> T \<Longrightarrow> s \<equiv>\<^sub>\<L> t"
    proof -
      fix s t assume mem: "s \<in> S" "t \<in> T"
      then obtain t' where res: "t' \<in> T" "gta_der \<A> s = gta_der \<A> t'" using eq_rel(3)
        by (metis image_iff)
      from res(1) mem have "s \<in> \<T>\<^sub>G \<F>" "t \<in> \<T>\<^sub>G \<F>" "t' \<in> \<T>\<^sub>G \<F>" using eq_rel(1, 2)
        using in_quotient_imp_subset myhill_equiv by blast+
      then have "s \<equiv>\<^sub>\<L> t'" using assms res ground_ctxt_apply_pres_der[of \<A> s]
        by (auto simp: myhill_def gta_der_def simp flip: ctxt_of_gctxt_apply
         elim!: gta_langE intro: gta_langI)
      moreover have "t' \<equiv>\<^sub>\<L> t" using quotient_eq_iff[OF myhill_equiv eq_rel(2) eq_rel(2) res(1) mem(2)]
        by simp
      ultimately show "s \<equiv>\<^sub>\<L> t" using myhill_trans by blast
    qed
    then have "\<And> s t. s \<in> S \<Longrightarrow> t \<in> T \<Longrightarrow> (s, t) \<in> MN\<^sub>\<L>" by blast
    then have "S = T" using quotient_eq_iff[OF myhill_equiv eq_rel(1, 2)]
      using eq_rel(3) by fastforce}
  then show inj: "inj_on ?D ?R" by (meson inj_onI)
qed

lemma rtl_implies_finite_indexed_myhill_relation:
  assumes "gta_lang Q\<^sub>f \<A> = \<L>"
  shows "finite (\<T>\<^sub>G \<F> // MN\<^sub>\<L>)" (is "finite ?R")
proof -
  let ?D = "\<lambda> X. gta_der \<A> ` X"
  have image: "?D ` ?R \<subseteq> Pow (fset (fPow (\<Q> \<A>)))" unfolding gta_der_def
    by (meson PowI fPowI ground_ta_der_states ground_term_of_gterm image_subsetI)
  then have "finite (Pow (fset (fPow (\<Q> \<A>))))" by simp
  then have "finite (?D ` ?R)" using finite_subset[OF image] by fastforce
  then show ?thesis using finite_image_iff[OF rtl_der_image_on_myhill_inj[OF assms]]
    by blast
qed

end

end