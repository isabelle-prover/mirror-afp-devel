theory GTT
  imports Tree_Automata Ground_Closure
begin

section \<open>Ground Tree Transducers (GTT)\<close>

(* A GTT \<G> consists of a set of interface states and
   a set of rules for automaton \<A> and one for \<B>. *)
type_synonym ('q, 'f) gtt = "('q, 'f) ta \<times> ('q, 'f) ta"

abbreviation gtt_rules where
  "gtt_rules \<G> \<equiv> rules (fst \<G>) |\<union>| rules (snd \<G>)"
abbreviation gtt_eps where
  "gtt_eps \<G> \<equiv> eps (fst \<G>) |\<union>| eps (snd \<G>)"
definition gtt_states where
  "gtt_states \<G> = \<Q> (fst \<G>) |\<union>| \<Q> (snd \<G>)"
abbreviation gtt_syms where
  "gtt_syms \<G> \<equiv> ta_sig (fst \<G>) |\<union>| ta_sig (snd \<G>)"
definition gtt_interface where
  "gtt_interface \<G> = \<Q> (fst \<G>) |\<inter>| \<Q> (snd \<G>)"
definition gtt_eps_free where
  "gtt_eps_free \<G> = (eps_free (fst \<G>), eps_free (snd \<G>))"

definition is_gtt_eps_free :: "('q, 'f) ta \<times> ('p, 'g) ta \<Rightarrow> bool" where
  "is_gtt_eps_free \<G> \<longleftrightarrow> eps (fst \<G>) = {||} \<and> eps (snd \<G>) = {||}"

text \<open>*anchored* language accepted by a GTT\<close>

definition agtt_lang :: "('q, 'f) gtt \<Rightarrow> 'f gterm rel" where
  "agtt_lang \<G> = {(t, u) |t u q. q |\<in>| gta_der (fst \<G>) t \<and> q |\<in>| gta_der (snd \<G>) u}"

lemma agtt_langI:
  "q |\<in>| gta_der (fst \<G>) s \<Longrightarrow> q |\<in>| gta_der (snd \<G>) t \<Longrightarrow> (s, t) \<in> agtt_lang \<G>"
  by (auto simp: agtt_lang_def)

lemma agtt_langE:
  assumes "(s, t) \<in> agtt_lang \<G>"
  obtains q where "q |\<in>| gta_der (fst \<G>) s" "q |\<in>| gta_der (snd \<G>) t"
  using assms by (auto simp: agtt_lang_def)

lemma converse_agtt_lang:
  "(agtt_lang \<G>)\<inverse> = agtt_lang (prod.swap \<G>)"
  by (auto simp: agtt_lang_def)

lemma agtt_lang_swap:
  "agtt_lang (prod.swap \<G>) = prod.swap ` agtt_lang \<G>"
  by (auto simp: agtt_lang_def)

text \<open>language accepted by a GTT\<close>

abbreviation gtt_lang :: "('q, 'f) gtt \<Rightarrow> 'f gterm rel" where
  "gtt_lang \<G> \<equiv> gmctxt_cl UNIV (agtt_lang \<G>)"  

lemma gtt_lang_join:
  "q |\<in>| gta_der (fst \<G>) s \<Longrightarrow> q |\<in>| gta_der (snd \<G>) t \<Longrightarrow> (s, t) \<in> gmctxt_cl UNIV (agtt_lang \<G>)"
  by (auto simp: agtt_lang_def)

definition gtt_accept where
  "gtt_accept \<G> s t \<equiv> (s, t) \<in> gmctxt_cl UNIV (agtt_lang \<G>)"

lemma gtt_accept_intros:
  "(s, t) \<in> agtt_lang \<G> \<Longrightarrow> gtt_accept \<G> s t"
  "length ss = length ts \<Longrightarrow> \<forall> i < length ts. gtt_accept \<G> (ss ! i) (ts ! i) \<Longrightarrow>
    (f, length ss) \<in> \<F> \<Longrightarrow> gtt_accept \<G> (GFun f ss) (GFun f ts)"
  by (auto simp: gtt_accept_def)

abbreviation gtt_lang_terms :: "('q, 'f) gtt \<Rightarrow> ('f, 'q) term rel" where
  "gtt_lang_terms \<G> \<equiv> (\<lambda> s. map_both term_of_gterm s) ` (gmctxt_cl UNIV (agtt_lang \<G>))"

lemma term_of_gterm_gtt_lang_gtt_lang_terms_conv:
  "map_both term_of_gterm ` gtt_lang \<G> = gtt_lang_terms \<G>"
  by auto

lemma gtt_accept_swap [simp]:
  "gtt_accept (prod.swap \<G>) s t \<longleftrightarrow> gtt_accept \<G> t s"
  by (auto simp: gmctxt_cl_swap agtt_lang_swap gtt_accept_def)

lemma gtt_lang_swap:
  "(gtt_lang (A, B))\<inverse> = gtt_lang (B, A)"
  using gtt_accept_swap[of "(A, B)"]
  by (auto simp: gtt_accept_def)

(* The following Lemmas are about ta_res' *)

lemma gtt_accept_exI:
  assumes "gtt_accept \<G> s t"
  shows "\<exists> u. u |\<in>| ta_der' (fst \<G>) (term_of_gterm s) \<and> u |\<in>| ta_der' (snd \<G>) (term_of_gterm t)"
  using assms unfolding gtt_accept_def
proof (induction)
  case (base s t)
  then show ?case unfolding agtt_lang_def
    by (auto simp: gta_der_def ta_der_to_ta_der')
next
  case (step ss ts f)
  then have inner: "\<exists> us. length us = length ss \<and>
    (\<forall>i < length ss. (us ! i) |\<in>| ta_der' (fst \<G>) (term_of_gterm (ss ! i)) \<and>
    (us ! i) |\<in>| ta_der' (snd \<G>) (term_of_gterm (ts ! i)))"
    using Ex_list_of_length_P[of "length ss" "\<lambda> u i. u |\<in>| ta_der' (fst \<G>) (term_of_gterm (ss ! i)) \<and>
      u |\<in>| ta_der' (snd \<G>) (term_of_gterm (ts ! i))"]
    by auto
  then obtain us where "length us = length ss \<and> (\<forall>i < length ss.
            (us ! i) |\<in>| ta_der' (fst \<G>) (term_of_gterm (ss ! i)) \<and> (us ! i) |\<in>| ta_der' (snd \<G>) (term_of_gterm (ts ! i)))"
    by blast
  then have "Fun f us |\<in>| ta_der' (fst \<G>) (Fun f (map term_of_gterm ss)) \<and>
         Fun f us |\<in>| ta_der' (snd \<G>) (Fun f (map term_of_gterm ts))" using step(1) by fastforce
  then show ?case by (metis term_of_gterm.simps) 
qed


lemma agtt_lang_mono:
  assumes "rules (fst \<G>) |\<subseteq>| rules (fst \<G>')" "eps (fst \<G>) |\<subseteq>| eps (fst \<G>')"
    "rules (snd \<G>) |\<subseteq>| rules (snd \<G>')" "eps (snd \<G>) |\<subseteq>| eps (snd \<G>')"
  shows "agtt_lang \<G> \<subseteq> agtt_lang \<G>'"
  using fsubsetD[OF ta_der_mono[OF assms(1, 2)]] ta_der_mono[OF assms(3, 4)]
  by (auto simp: agtt_lang_def gta_der_def dest!: fsubsetD[OF ta_der_mono[OF assms(1, 2)]] fsubsetD[OF ta_der_mono[OF assms(3, 4)]])

lemma gtt_lang_mono:
  assumes "rules (fst \<G>) |\<subseteq>| rules (fst \<G>')" "eps (fst \<G>) |\<subseteq>| eps (fst \<G>')" 
    "rules (snd \<G>) |\<subseteq>| rules (snd \<G>')" "eps (snd \<G>) |\<subseteq>| eps (snd \<G>')"
  shows "gtt_lang \<G> \<subseteq> gtt_lang \<G>'"
  using agtt_lang_mono[OF assms]
  by (intro gmctxt_cl_mono_rel) auto

definition fmap_states_gtt where
  "fmap_states_gtt f \<equiv> map_both (fmap_states_ta f)"

lemma ground_map_vars_term_simp:
  "ground t \<Longrightarrow> map_term f g t = map_term f (\<lambda>_. undefined) t"
  by (induct t) auto

lemma states_fmap_states_gtt [simp]:
  "gtt_states (fmap_states_gtt f \<G>) = f |`| gtt_states \<G>"
  by (simp add: fimage_funion gtt_states_def fmap_states_gtt_def)

lemma agtt_lang_fmap_states_gtt:
  assumes "finj_on f (gtt_states \<G>)"
  shows "agtt_lang (fmap_states_gtt f \<G>) = agtt_lang \<G>" (is "?Ls = ?Rs")
proof -
  from assms have inj: "finj_on f (\<Q> (fst \<G>) |\<union>| \<Q> (snd \<G>))" "finj_on f (\<Q> (fst \<G>))" "finj_on f (\<Q> (snd \<G>))"
    by (auto simp: gtt_states_def finj_on_fUn)
  then have "?Ls \<subseteq> ?Rs" using ta_der_fmap_states_inv_superset[OF _ inj(1)]
    by (auto simp: agtt_lang_def gta_der_def fmap_states_gtt_def)
  moreover have "?Rs \<subseteq> ?Ls"
    by (auto simp: agtt_lang_def gta_der_def fmap_states_gtt_def elim!: ta_der_to_fmap_states_der)
  ultimately show ?thesis by blast
qed

lemma agtt_lang_Inl_Inr_states_agtt:
  "agtt_lang (fmap_states_gtt Inl \<G>) = agtt_lang \<G>"
  "agtt_lang (fmap_states_gtt Inr \<G>) = agtt_lang \<G>"
  by (auto simp: finj_Inl_Inr intro!: agtt_lang_fmap_states_gtt)

lemma gtt_lang_fmap_states_gtt:
  assumes "finj_on f (gtt_states \<G>)"
  shows "gtt_lang (fmap_states_gtt f \<G>) = gtt_lang \<G>" (is "?Ls = ?Rs")
  unfolding fmap_states_gtt_def
  using agtt_lang_fmap_states_gtt[OF assms]
  by (simp add: fmap_states_gtt_def)

definition gtt_only_reach where
  "gtt_only_reach = map_both ta_only_reach"

subsection \<open>(A)GTT reachable states\<close>

lemma agtt_only_reach_lang:
  "agtt_lang (gtt_only_reach \<G>) = agtt_lang \<G>"
  unfolding agtt_lang_def gtt_only_reach_def
  by (auto simp: gta_der_def simp flip: ta_der_gterm_only_reach)

lemma gtt_only_reach_lang:
  "gtt_lang (gtt_only_reach \<G>) = gtt_lang \<G>"
  by (auto simp: agtt_only_reach_lang)

lemma gtt_only_reach_syms:
  "gtt_syms (gtt_only_reach \<G>) |\<subseteq>| gtt_syms \<G>"
  by (auto simp: gtt_only_reach_def ta_restrict_def ta_sig_def)

subsection \<open>(A)GTT productive states\<close>

definition gtt_only_prod where
  "gtt_only_prod \<G> = (let iface = gtt_interface \<G> in
     map_both (ta_only_prod iface) \<G>)"

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
                   
lemma gtt_only_prod_lang:
  "gtt_lang (gtt_only_prod \<G>) = gtt_lang \<G>"
  by (auto simp: agtt_only_prod_lang)

lemma gtt_only_prod_syms:
  "gtt_syms (gtt_only_prod \<G>) |\<subseteq>| gtt_syms \<G>"
  by (auto simp: gtt_only_prod_def ta_restrict_def ta_sig_def Let_def)

subsection \<open>(A)GTT trimming\<close>

definition trim_gtt where
  "trim_gtt = gtt_only_prod \<circ> gtt_only_reach"

lemma trim_agtt_lang:
  "agtt_lang (trim_gtt G) = agtt_lang G"
  unfolding trim_gtt_def comp_def agtt_only_prod_lang agtt_only_reach_lang ..

lemma trim_gtt_lang:
  "gtt_lang (trim_gtt G) = gtt_lang G"
  unfolding trim_gtt_def comp_def gtt_only_prod_lang gtt_only_reach_lang ..

lemma trim_gtt_prod_syms:
  "gtt_syms (trim_gtt G) |\<subseteq>| gtt_syms G"
  unfolding trim_gtt_def using fsubset_trans[OF gtt_only_prod_syms gtt_only_reach_syms] by simp

subsection \<open>root-cleanliness\<close>

text \<open>A GTT is root-clean if none of its interface states can occur in a non-root positions
  in the accepting derivations corresponding to its anchored GTT relation.\<close>

definition ta_nr_states :: "('q, 'f) ta \<Rightarrow> 'q fset" where
  "ta_nr_states A = |\<Union>| ((fset_of_list \<circ> r_lhs_states) |`| (rules A))"

definition gtt_nr_states where
  "gtt_nr_states G = ta_nr_states (fst G) |\<union>| ta_nr_states (snd G)"

definition gtt_root_clean where
  "gtt_root_clean G \<longleftrightarrow> gtt_nr_states G |\<inter>| gtt_interface G = {||}"


subsection \<open>Relabeling\<close>

definition relabel_gtt :: "('q :: linorder, 'f) gtt \<Rightarrow> (nat, 'f) gtt" where
  "relabel_gtt G = fmap_states_gtt (map_fset_to_nat (gtt_states G)) G"

lemma relabel_agtt_lang [simp]:
  "agtt_lang (relabel_gtt G) = agtt_lang G"
  by (simp add: agtt_lang_fmap_states_gtt map_fset_to_nat_inj relabel_gtt_def)

lemma agtt_lang_sig:
  "fset (gtt_syms G) \<subseteq> \<F> \<Longrightarrow> agtt_lang G \<subseteq> \<T>\<^sub>G \<F> \<times> \<T>\<^sub>G \<F>"
  by (auto simp: agtt_lang_def gta_der_def \<T>\<^sub>G_equivalent_def)
     (metis ffunas_gterm.rep_eq less_eq_fset.rep_eq subset_iff ta_der_gterm_sig)+

subsection \<open>epsilon free GTTs\<close>


lemma agtt_lang_gtt_eps_free [simp]:
  "agtt_lang (gtt_eps_free \<G>) = agtt_lang \<G>"
  by (auto simp: agtt_lang_def gta_der_def gtt_eps_free_def ta_res_eps_free)

lemma gtt_lang_gtt_eps_free [simp]:
  "gtt_lang (gtt_eps_free \<G>) = gtt_lang \<G>"
  by auto

end
