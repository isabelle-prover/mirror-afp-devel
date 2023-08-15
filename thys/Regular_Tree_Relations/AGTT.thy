theory AGTT
  imports GTT GTT_Transitive_Closure Pair_Automaton
begin


definition AGTT_union where
  "AGTT_union \<G>\<^sub>1 \<G>\<^sub>2 \<equiv> (ta_union (fst \<G>\<^sub>1) (fst \<G>\<^sub>2),
                       ta_union (snd \<G>\<^sub>1) (snd \<G>\<^sub>2))"

abbreviation AGTT_union' where
  "AGTT_union' \<G>\<^sub>1 \<G>\<^sub>2 \<equiv> AGTT_union (fmap_states_gtt Inl \<G>\<^sub>1) (fmap_states_gtt Inr \<G>\<^sub>2)"

lemma disj_gtt_states_disj_fst_ta_states:
  assumes dist_st: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "\<Q> (fst \<G>\<^sub>1) |\<inter>| \<Q> (fst \<G>\<^sub>2) = {||}"
  using assms unfolding gtt_states_def by auto

lemma disj_gtt_states_disj_snd_ta_states:
  assumes dist_st: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "\<Q> (snd \<G>\<^sub>1) |\<inter>| \<Q> (snd \<G>\<^sub>2) = {||}"
  using assms unfolding gtt_states_def by auto

lemma ta_der_not_contains_undefined_state:
  assumes "q |\<notin>| \<Q> T" and "ground t"
  shows "q |\<notin>| ta_der T t"
  using ground_ta_der_states[OF assms(2)] assms(1)
  by blast

lemma AGTT_union_sound1:
  assumes dist_st: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "agtt_lang (AGTT_union \<G>\<^sub>1 \<G>\<^sub>2) \<subseteq> agtt_lang \<G>\<^sub>1 \<union> agtt_lang \<G>\<^sub>2"
proof -
  let ?TA_A = "ta_union (fst \<G>\<^sub>1) (fst \<G>\<^sub>2)"
  let ?TA_B = "ta_union (snd \<G>\<^sub>1) (snd \<G>\<^sub>2)"
  {fix s t assume ass: "(s, t) \<in> agtt_lang (AGTT_union \<G>\<^sub>1 \<G>\<^sub>2)"
    then obtain q where ls: "q |\<in>| ta_der ?TA_A (term_of_gterm s)" and
      rs: "q |\<in>| ta_der ?TA_B (term_of_gterm t)"
      by (auto simp add: AGTT_union_def agtt_lang_def gta_der_def)
    then have "(s, t) \<in> agtt_lang \<G>\<^sub>1 \<or> (s, t) \<in> agtt_lang \<G>\<^sub>2"
    proof (cases "q |\<in>| gtt_states \<G>\<^sub>1")
      case True
      then have "q |\<notin>| gtt_states \<G>\<^sub>2" using dist_st
        by blast
      then have nt_fst_st: "q |\<notin>| \<Q> (fst \<G>\<^sub>2)" and
        nt_snd_state: "q |\<notin>| \<Q> (snd \<G>\<^sub>2)" by (auto simp add: gtt_states_def)
      from True show ?thesis
        using ls rs
        using ta_der_not_contains_undefined_state[OF nt_fst_st]
        using ta_der_not_contains_undefined_state[OF nt_snd_state]
        unfolding gtt_states_def agtt_lang_def gta_der_def
        using ta_union_der_disj_states[OF disj_gtt_states_disj_fst_ta_states[OF dist_st]]
        using ta_union_der_disj_states[OF disj_gtt_states_disj_snd_ta_states[OF dist_st]]
        using ground_term_of_gterm by blast
    next
      case False
      then have "q |\<notin>| gtt_states \<G>\<^sub>1" by (metis IntI dist_st emptyE)
      then have nt_fst_st: "q |\<notin>| \<Q> (fst \<G>\<^sub>1)" and
        nt_snd_state: "q |\<notin>| \<Q> (snd \<G>\<^sub>1)" by (auto simp add: gtt_states_def)
      from False show ?thesis
        using ls rs
        using ta_der_not_contains_undefined_state[OF nt_fst_st]
        using ta_der_not_contains_undefined_state[OF nt_snd_state]
        unfolding gtt_states_def agtt_lang_def gta_der_def
        using ta_union_der_disj_states[OF disj_gtt_states_disj_fst_ta_states[OF dist_st]]
        using ta_union_der_disj_states[OF disj_gtt_states_disj_snd_ta_states[OF dist_st]]
        using ground_term_of_gterm by blast
    qed}
  then show ?thesis by auto
qed

lemma AGTT_union_sound2:
  shows "agtt_lang \<G>\<^sub>1 \<subseteq> agtt_lang (AGTT_union \<G>\<^sub>1 \<G>\<^sub>2)"
    "agtt_lang \<G>\<^sub>2 \<subseteq> agtt_lang (AGTT_union \<G>\<^sub>1 \<G>\<^sub>2)"
  unfolding agtt_lang_def gta_der_def AGTT_union_def
  by auto (meson fin_mono ta_der_mono' ta_union_ta_subset)+

lemma AGTT_union_sound:
  assumes dist_st: "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "agtt_lang (AGTT_union \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang \<G>\<^sub>1 \<union> agtt_lang \<G>\<^sub>2"
  using AGTT_union_sound1[OF assms] AGTT_union_sound2 by blast

lemma AGTT_union'_sound:
  fixes \<G>\<^sub>1 :: "('q, 'f) gtt" and \<G>\<^sub>2 :: "('q, 'f) gtt"
  shows "agtt_lang (AGTT_union' \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang \<G>\<^sub>1 \<union> agtt_lang \<G>\<^sub>2"
proof -
  have map: "agtt_lang (AGTT_union' \<G>\<^sub>1 \<G>\<^sub>2) =
    agtt_lang (fmap_states_gtt CInl \<G>\<^sub>1) \<union> agtt_lang (fmap_states_gtt CInr \<G>\<^sub>2)"
    by (intro  AGTT_union_sound) (auto simp add: agtt_lang_fmap_states_gtt)
  then show ?thesis by (simp add: agtt_lang_fmap_states_gtt finj_CInl_CInr)
qed

subsection \<open>Anchord gtt compositon\<close>

definition AGTT_comp :: "('q, 'f) gtt \<Rightarrow> ('q, 'f) gtt \<Rightarrow> ('q, 'f) gtt" where
  "AGTT_comp \<G>\<^sub>1 \<G>\<^sub>2 = (let (\<A>, \<B>) = (fst \<G>\<^sub>1, snd \<G>\<^sub>2) in
    (TA (rules \<A>) (eps \<A> |\<union>| (\<Delta>\<^sub>\<epsilon> (snd \<G>\<^sub>1) (fst \<G>\<^sub>2) |\<inter>| (gtt_interface \<G>\<^sub>1 |\<times>| gtt_interface \<G>\<^sub>2))),
     TA (rules \<B>) (eps \<B>)))"

abbreviation AGTT_comp' where
  "AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2 \<equiv> AGTT_comp (fmap_states_gtt Inl \<G>\<^sub>1) (fmap_states_gtt Inr \<G>\<^sub>2)"

lemma AGTT_comp_sound:
  assumes "gtt_states \<G>\<^sub>1 |\<inter>| gtt_states \<G>\<^sub>2 = {||}"
  shows "agtt_lang (AGTT_comp \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang \<G>\<^sub>1 O agtt_lang \<G>\<^sub>2"
proof -
  let ?Q\<^sub>1 = "fId_on (gtt_interface \<G>\<^sub>1)" let ?Q\<^sub>2 = "fId_on (gtt_interface \<G>\<^sub>2)" 
  have lan: "agtt_lang \<G>\<^sub>1 = pair_at_lang \<G>\<^sub>1 ?Q\<^sub>1" "agtt_lang \<G>\<^sub>2 = pair_at_lang \<G>\<^sub>2 ?Q\<^sub>2"
    using pair_at_agtt[of \<G>\<^sub>1] pair_at_agtt[of \<G>\<^sub>2]
    by auto
  have "agtt_lang \<G>\<^sub>1 O agtt_lang \<G>\<^sub>2 = pair_at_lang (fst \<G>\<^sub>1, snd \<G>\<^sub>2) (\<Delta>_eps_pair \<G>\<^sub>1 ?Q\<^sub>1 \<G>\<^sub>2 ?Q\<^sub>2)"
    using pair_comp_sound1 pair_comp_sound2
    by (auto simp add: lan pair_comp_sound1 pair_comp_sound2 relcomp.simps)
  moreover have "AGTT_comp \<G>\<^sub>1 \<G>\<^sub>2 = pair_at_to_agtt (fst \<G>\<^sub>1, snd \<G>\<^sub>2) (\<Delta>_eps_pair \<G>\<^sub>1 ?Q\<^sub>1 \<G>\<^sub>2 ?Q\<^sub>2)"
    by (auto simp: AGTT_comp_def pair_at_to_agtt_def gtt_interface_def \<Delta>\<^sub>\<epsilon>_def' \<Delta>_eps_pair_def)
  ultimately show ?thesis using pair_at_agtt_conv[of "\<Delta>_eps_pair \<G>\<^sub>1 ?Q\<^sub>1 \<G>\<^sub>2 ?Q\<^sub>2" "(fst \<G>\<^sub>1, snd \<G>\<^sub>2)"]
    using assms
    by (auto simp: \<Delta>_eps_pair_def gtt_states_def gtt_interface_def)
qed

lemma AGTT_comp'_sound:
  "agtt_lang (AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang \<G>\<^sub>1 O agtt_lang \<G>\<^sub>2"
  using AGTT_comp_sound[of "fmap_states_gtt (Inl :: 'b \<Rightarrow> 'b + 'c) \<G>\<^sub>1"
    "fmap_states_gtt (Inr :: 'c \<Rightarrow> 'b + 'c) \<G>\<^sub>2"]
  by (auto simp add: agtt_lang_fmap_states_gtt disjoint_iff_not_equal agtt_lang_Inl_Inr_states_agtt)

subsection \<open>Anchord gtt transitivity\<close>

definition AGTT_trancl :: "('q, 'f) gtt \<Rightarrow> ('q + 'q, 'f) gtt" where
  "AGTT_trancl \<G> = (let \<A> = fmap_states_ta Inl (fst \<G>) in
    (TA (rules \<A>) (eps \<A> |\<union>| map_prod CInl CInr |`| (\<Delta>_Atrans_gtt \<G> (fId_on (gtt_interface \<G>)))),
     TA (map_ta_rule CInr id |`| (rules (snd \<G>))) (map_both CInr |`| (eps (snd \<G>)))))"

lemma AGTT_trancl_sound:
  shows "agtt_lang (AGTT_trancl \<G>) = (agtt_lang \<G>)\<^sup>+"
proof -
  let ?P = "map_prod (fmap_states_ta CInl) (fmap_states_ta CInr) \<G>"
  let ?Q = "fId_on (gtt_interface \<G>)" let ?Q' = "map_prod CInl CInr |`| ?Q"
  have inv: "finj_on CInl (\<Q> (fst \<G>))" "finj_on CInr (\<Q> (snd \<G>))"
    "?Q |\<subseteq>| \<Q> (fst \<G>) |\<times>| \<Q> (snd \<G>)"
    by (auto simp: gtt_interface_def finj_CInl_CInr)
  have *: "fst |`| map_prod CInl CInr |`| \<Delta>_Atrans_gtt \<G> (fId_on (gtt_interface \<G>)) |\<subseteq>| CInl |`| \<Q> (fst \<G>)"
    using fsubsetD[OF \<Delta>_Atrans_states_stable[OF inv(3)]]
    by (auto simp add: gtt_interface_def)
  from pair_at_lang_fun_states[OF inv]
  have "agtt_lang \<G> = pair_at_lang ?P ?Q'" using pair_at_agtt[of \<G>] by auto
  moreover then have "(agtt_lang \<G>)\<^sup>+ = pair_at_lang ?P (\<Delta>_Atrans_gtt ?P ?Q')"
    by (simp add: pair_trancl_sound)
  moreover have "AGTT_trancl \<G> = pair_at_to_agtt ?P (\<Delta>_Atrans_gtt ?P ?Q')"
    using \<Delta>_Atrans_states_stable[OF inv(3)] \<Delta>_Atrans_map_prod[OF inv, symmetric]
    using fId_on_frelcomp_id[OF *]
    by (auto simp: AGTT_trancl_def pair_at_to_agtt_def gtt_interface_def Let_def fmap_states_ta_def)
       (metis fmap_prod_fimageI fmap_states fmap_states_ta_def)
  moreover have "gtt_interface (map_prod (fmap_states_ta CInl) (fmap_states_ta CInr) \<G>) = {||}"
    by (auto simp: gtt_interface_def)
  ultimately show ?thesis using pair_at_agtt_conv[of "\<Delta>_Atrans_gtt ?P ?Q'" ?P] \<Delta>_Atrans_states_stable[OF inv(3)]
    unfolding \<Delta>_Atrans_map_prod[OF inv, symmetric]
    by (simp add: fimage_mono gtt_interface_def map_prod_ftimes)
qed

subsection \<open>Anchord gtt intersection\<close>

definition AGTT_inter where
  "AGTT_inter \<G>\<^sub>1 \<G>\<^sub>2 \<equiv> (prod_ta (fst \<G>\<^sub>1) (fst \<G>\<^sub>2),
                       prod_ta (snd \<G>\<^sub>1) (snd \<G>\<^sub>2))"

lemma AGTT_inter_sound:
  "agtt_lang (AGTT_inter \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang \<G>\<^sub>1 \<inter> agtt_lang \<G>\<^sub>2" (is "?Ls = ?Rs")
proof -
  let ?TA_A = "prod_ta (fst \<G>\<^sub>1) (fst \<G>\<^sub>2)"
  let ?TA_B = "prod_ta (snd \<G>\<^sub>1) (snd \<G>\<^sub>2)"
  {fix s t assume ass: "(s, t) \<in> agtt_lang (AGTT_inter \<G>\<^sub>1 \<G>\<^sub>2)"
    then obtain q where ls: "q |\<in>| ta_der ?TA_A (term_of_gterm s)" and
      rs: "q |\<in>| ta_der ?TA_B (term_of_gterm t)"
      by (auto simp add: AGTT_inter_def agtt_lang_def gta_der_def)
    then have "(s, t) \<in> agtt_lang \<G>\<^sub>1 \<and> (s, t) \<in> agtt_lang \<G>\<^sub>2"
      using prod_ta_der_to_\<A>_\<B>_der1[of q] prod_ta_der_to_\<A>_\<B>_der2[of q]
      by (auto simp: agtt_lang_def gta_der_def) blast}
  then have f: "?Ls \<subseteq> ?Rs" by auto
  moreover have "?Rs \<subseteq> ?Ls" using \<A>_\<B>_der_to_prod_ta
    by (fastforce simp: agtt_lang_def AGTT_inter_def gta_der_def)
  ultimately show ?thesis by blast
qed

subsection \<open>Anchord gtt triming\<close>

abbreviation "trim_agtt \<equiv> trim_gtt"

lemma agtt_only_prod_lang:
  "agtt_lang (gtt_only_prod \<G>) = agtt_lang \<G>" (is "?Ls = ?Rs")
proof -
  let ?A = "fst \<G>" let ?B = "snd \<G>"
  have "?Ls \<subseteq> ?Rs" unfolding agtt_lang_def gtt_only_prod_def
    by (auto simp: Let_def gta_der_def dest: ta_der_ta_only_prod_ta_der)
  moreover
  {fix s t assume "(s, t) \<in> ?Rs"
    then obtain q where r: "q |\<in>| ta_der (fst \<G>) (term_of_gterm s)" "q |\<in>| ta_der (snd \<G>) (term_of_gterm t)"
      by (auto simp: agtt_lang_def gta_der_def)
    then have " q |\<in>| gtt_interface \<G>" by (auto simp: gtt_interface_def)
    then have "(s, t) \<in> ?Ls" using r
      by (auto simp: agtt_lang_def gta_der_def gtt_only_prod_def Let_def intro!: exI[of _ q] ta_der_only_prod ta_productive_setI)}
  ultimately show ?thesis by auto
qed

lemma agtt_only_reach_lang:
  "agtt_lang (gtt_only_reach \<G>) = agtt_lang \<G>"
  unfolding agtt_lang_def gtt_only_reach_def
  by (auto simp: gta_der_def simp flip: ta_der_gterm_only_reach)

lemma trim_agtt_lang [simp]:
  "agtt_lang (trim_agtt G) = agtt_lang G"
  unfolding trim_gtt_def comp_def agtt_only_prod_lang agtt_only_reach_lang ..


end