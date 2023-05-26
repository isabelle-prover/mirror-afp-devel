theory FOR_Check_Impl
  imports FOR_Check
   Regular_Tree_Relations.Regular_Relation_Impl
   NF_Impl
begin

section \<open>Inference checking implementation\<close>

(* we define epsilon free agtt/gtt constructions *)
definition "ftrancl_eps_free_closures \<A> = eps_free_automata (eps \<A>) \<A>"
abbreviation "ftrancl_eps_free_reg \<A> \<equiv> Reg (fin \<A>) (ftrancl_eps_free_closures (ta \<A>))"

lemma ftrancl_eps_free_ta_derI:
  "(eps \<A>)|\<^sup>+| = eps \<A> \<Longrightarrow> ta_der (ftrancl_eps_free_closures \<A>) (term_of_gterm t) = ta_der \<A> (term_of_gterm t)"
  using eps_free[of \<A>] ta_res_eps_free[of \<A>]
  by (auto simp add: ftrancl_eps_free_closures_def)

lemma \<L>_ftrancl_eps_free_closuresI:
  "(eps (ta \<A>))|\<^sup>+| = eps (ta \<A>) \<Longrightarrow> \<L> (ftrancl_eps_free_reg \<A>) = \<L> \<A>"
  using ftrancl_eps_free_ta_derI[of "ta \<A>"]
  unfolding \<L>_def by (auto simp: gta_lang_def gta_der_def)

definition "root_step R \<F> \<equiv> (let (TA1, TA2) = agtt_grrstep R \<F> in
  (ftrancl_eps_free_closures TA1, TA2))"

definition AGTT_trancl_eps_free :: "('q, 'f) gtt \<Rightarrow> ('q + 'q, 'f) gtt" where
  "AGTT_trancl_eps_free \<G> = (let (\<A>, \<B>) = AGTT_trancl \<G> in
    (ftrancl_eps_free_closures \<A>, \<B>))"

definition GTT_trancl_eps_free where
  "GTT_trancl_eps_free \<G> = (let (\<A>, \<B>) = GTT_trancl \<G> in
   (ftrancl_eps_free_closures \<A>,
    ftrancl_eps_free_closures \<B>))"

definition AGTT_comp_eps_free where
  "AGTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2 = (let (\<A>, \<B>) = AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2 in
    (ftrancl_eps_free_closures \<A>, \<B>))"

definition GTT_comp_eps_free where
  "GTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2 =(let (\<A>, \<B>) = GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2 in
    (ftrancl_eps_free_closures \<A>, ftrancl_eps_free_closures \<B>))"

(* epsilon free proves *)
lemma eps_free_relable [simp]:
  "is_gtt_eps_free (relabel_gtt \<G>) = is_gtt_eps_free \<G>"
  by (auto simp: is_gtt_eps_free_def relabel_gtt_def fmap_states_gtt_def fmap_states_ta_def)

lemma eps_free_prod_swap:
  "is_gtt_eps_free (\<A>, \<B>) \<Longrightarrow> is_gtt_eps_free (\<B>, \<A>)"
  by (auto simp: is_gtt_eps_free_def)

lemma eps_free_root_step:
  "is_gtt_eps_free (root_step R \<F>)"
  by (auto simp add: case_prod_beta is_gtt_eps_free_def root_step_def pair_at_to_agtt'_def ftrancl_eps_free_closures_def)

lemma eps_free_AGTT_trancl_eps_free:
  "is_gtt_eps_free \<G> \<Longrightarrow> is_gtt_eps_free (AGTT_trancl_eps_free \<G>)"
  by (auto simp: case_prod_beta is_gtt_eps_free_def AGTT_trancl_def Let_def
      AGTT_trancl_eps_free_def ftrancl_eps_free_closures_def)

lemma eps_free_GTT_trancl_eps_free:
  "is_gtt_eps_free \<G> \<Longrightarrow> is_gtt_eps_free (GTT_trancl_eps_free \<G>)"
  by (auto simp: case_prod_beta is_gtt_eps_free_def GTT_trancl_eps_free_def ftrancl_eps_free_closures_def)

lemma eps_free_AGTT_comp_eps_free:
  "is_gtt_eps_free \<G>\<^sub>2 \<Longrightarrow> is_gtt_eps_free (AGTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2)"
  by (auto simp: case_prod_beta is_gtt_eps_free_def AGTT_comp_eps_free_def
    ftrancl_eps_free_closures_def AGTT_comp_def fmap_states_gtt_def fmap_states_ta_def)

lemma eps_free_GTT_comp_eps_free:
  "is_gtt_eps_free (GTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2)"
  by (auto simp: case_prod_beta is_gtt_eps_free_def GTT_comp_eps_free_def ftrancl_eps_free_closures_def)

lemmas eps_free_const =
  eps_free_prod_swap
  eps_free_root_step
  eps_free_AGTT_trancl_eps_free
  eps_free_GTT_trancl_eps_free
  eps_free_AGTT_comp_eps_free
  eps_free_GTT_comp_eps_free

(* lang preserve proofs *)
lemma agtt_lang_derI:
  assumes "\<And> t. ta_der (fst \<A>) (term_of_gterm t) = ta_der (fst \<B>) (term_of_gterm t)"
    and "\<And> t. ta_der (snd \<A>) (term_of_gterm t) = ta_der (snd \<B>) (term_of_gterm t)"
  shows "agtt_lang \<A> = agtt_lang \<B>" using assms
  by (auto simp: agtt_lang_def gta_der_def)

lemma agtt_lang_root_step_conv:
  "agtt_lang (root_step R \<F>) = agtt_lang (agtt_grrstep R \<F>)"
  using ftrancl_eps_free_ta_derI[OF agtt_grrstep_eps_trancl(1), of R \<F>]
  by (auto simp: case_prod_beta root_step_def intro!: agtt_lang_derI)

lemma agtt_lang_AGTT_trancl_eps_free_conv:
  assumes "is_gtt_eps_free \<G>"
  shows "agtt_lang (AGTT_trancl_eps_free \<G>) = agtt_lang (AGTT_trancl \<G>)"
proof -
  let ?eps = "eps (fst (AGTT_trancl \<G>))"
  have "?eps |O| ?eps = {||}" using assms
    by (auto simp: AGTT_trancl_def is_gtt_eps_free_def Let_def fmap_states_ta_def)
  from ftrancl_eps_free_ta_derI[OF frelcomp_empty_ftrancl_simp[OF this]]
  show ?thesis
    by (auto simp: case_prod_beta AGTT_trancl_eps_free_def intro!: agtt_lang_derI)
qed

lemma agtt_lang_GTT_trancl_eps_free_conv:
  assumes "is_gtt_eps_free \<G>"
  shows "agtt_lang (GTT_trancl_eps_free \<G>) = agtt_lang (GTT_trancl \<G>)"
proof -
  have "(eps (fst (GTT_trancl \<G>)))|\<^sup>+| = eps (fst (GTT_trancl \<G>))"
    "(eps (snd (GTT_trancl \<G>)))|\<^sup>+| = eps (snd (GTT_trancl \<G>))" using assms
    by (auto simp: GTT_trancl_def Let_def is_gtt_eps_free_def \<Delta>_trancl_inv)
  from ftrancl_eps_free_ta_derI[OF this(1)] ftrancl_eps_free_ta_derI[OF this(2)]
  show ?thesis
    by (auto simp: case_prod_beta GTT_trancl_eps_free_def intro!: agtt_lang_derI)
qed

lemma agtt_lang_AGTT_comp_eps_free_conv:
  assumes "is_gtt_eps_free \<G>\<^sub>1" "is_gtt_eps_free \<G>\<^sub>2"
  shows "agtt_lang (AGTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang (AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2)"
proof -
  have "(eps (fst (AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+| = eps (fst (AGTT_comp' \<G>\<^sub>1 \<G>\<^sub>2))" using assms
    by (auto simp: is_gtt_eps_free_def fmap_states_gtt_def fmap_states_ta_def
      case_prod_beta AGTT_comp_def gtt_interface_def \<Q>_def intro!: frelcomp_empty_ftrancl_simp)
  from ftrancl_eps_free_ta_derI[OF this] show ?thesis
    by (auto simp: case_prod_beta AGTT_comp_eps_free_def intro!: agtt_lang_derI)
qed

lemma agtt_lang_GTT_comp_eps_free_conv:
  assumes "is_gtt_eps_free \<G>\<^sub>1" "is_gtt_eps_free \<G>\<^sub>2"
  shows "agtt_lang (GTT_comp_eps_free \<G>\<^sub>1 \<G>\<^sub>2) = agtt_lang (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2)"
proof -
  have "(eps (fst (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+| = eps (fst (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2))"
    "(eps (snd (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2)))|\<^sup>+| = eps (snd (GTT_comp' \<G>\<^sub>1 \<G>\<^sub>2))" using assms
    by (auto simp: is_gtt_eps_free_def fmap_states_gtt_def fmap_states_ta_def \<Delta>\<^sub>\<epsilon>_fmember
      case_prod_beta GTT_comp_def gtt_interface_def \<Q>_def dest!: ground_ta_der_statesD
      intro!: frelcomp_empty_ftrancl_simp)
  from ftrancl_eps_free_ta_derI[OF this(1)] ftrancl_eps_free_ta_derI[OF this(2)]
  show ?thesis
    by (auto simp: case_prod_beta GTT_comp_eps_free_def intro!: agtt_lang_derI)
qed

fun gtt_of_gtt_rel_impl :: "('f \<times> nat) fset \<Rightarrow> ('f :: linorder, 'v) fin_trs list \<Rightarrow> ftrs gtt_rel \<Rightarrow> (nat, 'f) gtt option" where
  "gtt_of_gtt_rel_impl \<F> Rs (ARoot is) = liftO1 (\<lambda>R. relabel_gtt (root_step R \<F>)) (is_to_trs' Rs is)"
| "gtt_of_gtt_rel_impl \<F> Rs (GInv g) = liftO1 prod.swap (gtt_of_gtt_rel_impl \<F> Rs g)"
| "gtt_of_gtt_rel_impl \<F> Rs (AUnion g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (AGTT_union' g1 g2)) (gtt_of_gtt_rel_impl \<F> Rs g1) (gtt_of_gtt_rel_impl \<F> Rs g2)"
| "gtt_of_gtt_rel_impl \<F> Rs (ATrancl g) = liftO1 (relabel_gtt \<circ> AGTT_trancl_eps_free) (gtt_of_gtt_rel_impl \<F> Rs g)"
| "gtt_of_gtt_rel_impl \<F> Rs (GTrancl g) = liftO1 GTT_trancl_eps_free (gtt_of_gtt_rel_impl \<F> Rs g)"
| "gtt_of_gtt_rel_impl \<F> Rs (AComp g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (AGTT_comp_eps_free g1 g2)) (gtt_of_gtt_rel_impl \<F> Rs g1) (gtt_of_gtt_rel_impl \<F> Rs g2)"
| "gtt_of_gtt_rel_impl \<F> Rs (GComp g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (GTT_comp_eps_free g1 g2)) (gtt_of_gtt_rel_impl \<F> Rs g1) (gtt_of_gtt_rel_impl \<F> Rs g2)"

lemma gtt_of_gtt_rel_impl_is_gtt_eps_free:
  "gtt_of_gtt_rel_impl \<F> Rs g = Some g' \<Longrightarrow> is_gtt_eps_free g'"
proof (induct g arbitrary: g')
  case (AUnion g1 g2)
  then show ?case
    by (auto simp: is_gtt_eps_free_def AGTT_union_def fmap_states_gtt_def fmap_states_ta_def ta_union_def relabel_gtt_def)
qed (auto simp: eps_free_const)

lemma gtt_of_gtt_rel_impl_gtt_of_gtt_rel:
  "gtt_of_gtt_rel_impl \<F> Rs g \<noteq> None \<longleftrightarrow> gtt_of_gtt_rel \<F> Rs g \<noteq> None" (is "?Ls \<longleftrightarrow> ?Rs")
proof -
  have "?Ls \<Longrightarrow> ?Rs" by (induct g) auto
  moreover have "?Rs \<Longrightarrow> ?Ls" by (induct g) auto
  ultimately show ?thesis by blast
qed

lemma gtt_of_gtt_rel_impl_sound:
  "gtt_of_gtt_rel_impl \<F> Rs g = Some g' \<Longrightarrow> gtt_of_gtt_rel \<F> Rs g = Some g'' \<Longrightarrow> agtt_lang g' = agtt_lang g''"
proof (induct g arbitrary: g' g'')
  case (ARoot x)
  then show ?case by (simp add: agtt_lang_root_step_conv)
next
  case (GInv g)
  then have "agtt_lang (prod.swap g') = agtt_lang (prod.swap g'')" by auto
  then show ?case
    by (metis converse_agtt_lang converse_converse)
next
  case (AUnion g1 g2)
  then show ?case
    by simp (metis AGTT_union'_sound option.sel)
next
  case (ATrancl g)
  then show ?case
    using agtt_lang_AGTT_trancl_eps_free_conv[OF gtt_of_gtt_rel_impl_is_gtt_eps_free, of \<F> Rs g]
    by simp (metis AGTT_trancl_sound option.sel)
next
  case (GTrancl g)
  then show ?case
    using agtt_lang_GTT_trancl_eps_free_conv[OF gtt_of_gtt_rel_impl_is_gtt_eps_free, of \<F> Rs g]
    by simp (metis GTT_trancl_alang option.sel) 
next
  case (AComp g1 g2)
  then show ?case
    using agtt_lang_AGTT_comp_eps_free_conv[OF gtt_of_gtt_rel_impl_is_gtt_eps_free, of \<F> Rs g
      "the (gtt_of_gtt_rel_impl \<F> Rs g1)" "the (gtt_of_gtt_rel_impl \<F> Rs g2)"]
    by simp (metis AGTT_comp'_sound agtt_lang_AGTT_comp_eps_free_conv gtt_of_gtt_rel_impl_is_gtt_eps_free option.sel) 
next
  case (GComp g1 g2)
  then show ?case
    using agtt_lang_GTT_comp_eps_free_conv[OF gtt_of_gtt_rel_impl_is_gtt_eps_free, of \<F> Rs g
      "the (gtt_of_gtt_rel_impl \<F> Rs g1)" "the (gtt_of_gtt_rel_impl \<F> Rs g2)"]
    by simp (metis agtt_lang_GTT_comp_eps_free_conv gtt_comp'_alang gtt_of_gtt_rel_impl_is_gtt_eps_free option.sel) 
qed

(* eps free closure constructions *)
lemma \<L>_eps_free_nhole_ctxt_closure_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (ftrancl_eps_free_reg (nhole_ctxt_closure_reg \<F> \<A>)) = \<L> (nhole_ctxt_closure_reg \<F> \<A>)"
proof -
  have "eps (ta (nhole_ctxt_closure_reg \<F> \<A>)) |O| eps (ta (nhole_ctxt_closure_reg \<F> \<A>)) = {||}" using assms
    by (auto simp: nhole_ctxt_closure_reg_def gen_nhole_ctxt_closure_reg_def
      gen_nhole_ctxt_closure_automaton_def ta_union_def reflcl_over_nhole_ctxt_ta_def
      fmap_states_reg_def is_ta_eps_free_def fmap_states_ta_def reg_Restr_Q\<^sub>f_def)
  from frelcomp_empty_ftrancl_simp[OF this] show ?thesis
    by (intro \<L>_ftrancl_eps_free_closuresI) simp
qed

lemma \<L>_eps_free_ctxt_closure_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (ftrancl_eps_free_reg (ctxt_closure_reg \<F> \<A>)) = \<L> (ctxt_closure_reg \<F> \<A>)"
proof -
  have "eps (ta (ctxt_closure_reg \<F> \<A>)) |O| eps (ta (ctxt_closure_reg \<F> \<A>)) = {||}" using assms
    by (auto simp: ctxt_closure_reg_def gen_ctxt_closure_reg_def Let_def
      gen_ctxt_closure_automaton_def ta_union_def reflcl_over_single_ta_def
      fmap_states_reg_def is_ta_eps_free_def fmap_states_ta_def reg_Restr_Q\<^sub>f_def)
  from frelcomp_empty_ftrancl_simp[OF this] show ?thesis
    by (intro \<L>_ftrancl_eps_free_closuresI) simp
qed

lemma \<L>_eps_free_parallel_closure_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (ftrancl_eps_free_reg (parallel_closure_reg \<F> \<A>)) = \<L> (parallel_closure_reg \<F> \<A>)"
proof -
  have "eps (ta (parallel_closure_reg \<F> \<A>)) |O| eps (ta (parallel_closure_reg \<F> \<A>)) = {||}" using assms
    by (auto simp: parallel_closure_reg_def gen_parallel_closure_automaton_def Let_def ta_union_def
      refl_over_states_ta_def fmap_states_reg_def is_ta_eps_free_def fmap_states_ta_def reg_Restr_Q\<^sub>f_def)
  from frelcomp_empty_ftrancl_simp[OF this] show ?thesis
    by (intro \<L>_ftrancl_eps_free_closuresI) simp
qed

abbreviation "eps_free_reg' S R \<equiv> Reg (fin R) (eps_free_automata S (ta R))"

definition "eps_free_mctxt_closure_reg \<F> \<A> =
  (let \<B> = mctxt_closure_reg \<F> \<A> in
  eps_free_reg' ((\<lambda> p. (fst p, Inr cl_state)) |`| (eps (ta \<B>)) |\<union>| eps (ta \<B>)) \<B>)"

definition "eps_free_nhole_mctxt_reflcl_reg \<F> \<A> =
  (let \<B> = nhole_mctxt_reflcl_reg \<F> \<A> in
  eps_free_reg' ((\<lambda> p. (fst p, Inl (Inr cl_state))) |`| (eps (ta \<B>)) |\<union>| eps (ta \<B>)) \<B>)"

definition "eps_free_nhole_mctxt_closure_reg \<F> \<A> =
  (let \<B> = nhole_mctxt_closure_reg \<F> \<A> in
  eps_free_reg' ((\<lambda> p. (fst p, (Inr cl_state))) |`| (eps (ta \<B>)) |\<union>| eps (ta \<B>)) \<B>)"

lemma \<L>_eps_free_reg'I:
  "(eps (ta \<A>))|\<^sup>+| = S \<Longrightarrow> \<L> (eps_free_reg' S \<A>) = \<L> \<A>"
  by (auto simp:  \<L>_def gta_lang_def gta_der_def ta_res_eps_free simp flip: eps_free) 

lemma \<L>_eps_free_mctxt_closure_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (eps_free_mctxt_closure_reg \<F> \<A>) = \<L> (mctxt_closure_reg \<F> \<A>)" using assms
  unfolding eps_free_mctxt_closure_reg_def Let_def
  apply (intro \<L>_eps_free_reg'I)
  apply (auto simp: comp_def mctxt_closure_reg_def is_ta_eps_free_def Let_def
    gen_nhole_mctxt_closure_automaton_def reflcl_over_nhole_mctxt_ta_def ta_union_def
    reflcl_over_nhole_ctxt_ta_def  gen_mctxt_closure_reg_def reg_Restr_Q\<^sub>f_def
    fmap_states_reg_def fmap_states_ta_def dest: ftranclD ftranclD2)
  by (meson fimageI finsert_iff finterI fr_into_trancl ftrancl_into_trancl)

lemma \<L>_eps_free_nhole_mctxt_reflcl_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (eps_free_nhole_mctxt_reflcl_reg \<F> \<A>) = \<L> (nhole_mctxt_reflcl_reg \<F> \<A>)" using assms
  unfolding eps_free_nhole_mctxt_reflcl_reg_def Let_def
  apply (intro \<L>_eps_free_reg'I)
  apply (auto simp: comp_def nhole_mctxt_reflcl_reg_def is_ta_eps_free_def Let_def
    nhole_mctxt_closure_reg_def gen_nhole_mctxt_closure_reg_def reg_union_def ta_union_def
    gen_nhole_mctxt_closure_automaton_def reflcl_over_nhole_mctxt_ta_def
    reflcl_over_nhole_ctxt_ta_def reg_Restr_Q\<^sub>f_def fmap_states_reg_def fmap_states_ta_def dest: ftranclD ftranclD2)
  by (meson fimageI finsert_iff finterI fr_into_trancl ftrancl_into_trancl)

lemma \<L>_eps_free_nhole_mctxt_closure_reg:
  assumes "is_ta_eps_free (ta \<A>)"
  shows "\<L> (eps_free_nhole_mctxt_closure_reg \<F> \<A>) = \<L> (nhole_mctxt_closure_reg \<F> \<A>)" using assms
  unfolding eps_free_nhole_mctxt_closure_reg_def Let_def
  apply (intro \<L>_eps_free_reg'I)
  apply (auto simp: comp_def nhole_mctxt_closure_reg_def is_ta_eps_free_def Let_def
    gen_nhole_mctxt_closure_reg_def reg_Restr_Q\<^sub>f_def fmap_states_reg_def fmap_states_ta_def
    gen_nhole_mctxt_closure_automaton_def reflcl_over_nhole_mctxt_ta_def ta_union_def
    reflcl_over_nhole_ctxt_ta_def dest: ftranclD ftranclD2)
  by (meson fimageI finsert_iff finterI fr_into_trancl ftrancl_into_trancl)

fun rr1_of_rr1_rel_impl :: "('f \<times> nat) fset \<Rightarrow> ('f :: linorder, 'v) fin_trs list \<Rightarrow> ftrs rr1_rel \<Rightarrow> (nat, 'f) reg option"
and rr2_of_rr2_rel_impl :: "('f \<times> nat) fset \<Rightarrow> ('f, 'v) fin_trs list \<Rightarrow> ftrs rr2_rel \<Rightarrow> (nat, 'f option \<times> 'f option) reg option" where
  "rr1_of_rr1_rel_impl \<F> Rs R1Terms = Some (relabel_reg (term_reg \<F>))"
| "rr1_of_rr1_rel_impl \<F> Rs (R1NF is) = liftO1 (\<lambda>R. (simplify_reg (nf_reg (fst |`| R) \<F>))) (is_to_trs' Rs is)"
| "rr1_of_rr1_rel_impl \<F> Rs (R1Inf r) = liftO1 (\<lambda>R.
    let \<A> = trim_reg R in
    simplify_reg (proj_1_reg (Inf_reg_impl \<A>))
  ) (rr2_of_rr2_rel_impl \<F> Rs r)"
| "rr1_of_rr1_rel_impl \<F> Rs (R1Proj i r) = (case i of 0 \<Rightarrow>
      liftO1 (trim_reg \<circ> proj_1_reg) (rr2_of_rr2_rel_impl \<F> Rs r)
    | _ \<Rightarrow> liftO1 (trim_reg \<circ> proj_2_reg) (rr2_of_rr2_rel_impl \<F> Rs r))"
| "rr1_of_rr1_rel_impl \<F> Rs (R1Union s1 s2) =
    liftO2 (\<lambda> x y. relabel_reg (reg_union x y)) (rr1_of_rr1_rel_impl \<F> Rs s1) (rr1_of_rr1_rel_impl \<F> Rs s2)"
| "rr1_of_rr1_rel_impl \<F> Rs (R1Inter s1 s2) =
    liftO2 (\<lambda> x y. simplify_reg (reg_intersect x y)) (rr1_of_rr1_rel_impl \<F> Rs s1) (rr1_of_rr1_rel_impl \<F> Rs s2)"
| "rr1_of_rr1_rel_impl \<F> Rs (R1Diff s1 s2) = liftO2 (\<lambda> x y. relabel_reg (trim_reg (difference_reg x y))) (rr1_of_rr1_rel_impl \<F> Rs s1) (rr1_of_rr1_rel_impl \<F> Rs s2)"

| "rr2_of_rr2_rel_impl \<F> Rs (R2GTT_Rel g w x) =
    (case w of PRoot \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> reflcl_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g))
      | PNonRoot \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> ftrancl_eps_free_reg \<circ> nhole_ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_nhole_mctxt_reflcl_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_nhole_mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g))
      | PAny \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> ftrancl_eps_free_reg \<circ> ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> ftrancl_eps_free_reg \<circ> parallel_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel_impl \<F> Rs g)))"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Diag s) =
    liftO1 (\<lambda> x. fmap_funs_reg (\<lambda>f. (Some f, Some f)) x) (rr1_of_rr1_rel_impl \<F> Rs s)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Prod s1 s2) =
    liftO2 (\<lambda> x y. simplify_reg (pair_automaton_reg x y)) (rr1_of_rr1_rel_impl \<F> Rs s1) (rr1_of_rr1_rel_impl \<F> Rs s2)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Inv r) = liftO1 (fmap_funs_reg prod.swap) (rr2_of_rr2_rel_impl \<F> Rs r)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Union r1 r2) =
    liftO2 (\<lambda> x y. relabel_reg (reg_union x y)) (rr2_of_rr2_rel_impl \<F> Rs r1) (rr2_of_rr2_rel_impl \<F> Rs r2)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Inter r1 r2) =
    liftO2 (\<lambda> x y. simplify_reg (reg_intersect x y)) (rr2_of_rr2_rel_impl \<F> Rs r1) (rr2_of_rr2_rel_impl \<F> Rs r2)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Diff r1 r2) = liftO2 (\<lambda> x y. simplify_reg (difference_reg x y)) (rr2_of_rr2_rel_impl \<F> Rs r1) (rr2_of_rr2_rel_impl \<F> Rs r2)"
| "rr2_of_rr2_rel_impl \<F> Rs (R2Comp r1 r2) = liftO2 (\<lambda> x y. simplify_reg (rr2_compositon \<F> x y))
     (rr2_of_rr2_rel_impl \<F> Rs r1) (rr2_of_rr2_rel_impl \<F> Rs r2)"

lemmas ta_simp_unfold = simplify_reg_def relabel_reg_def trim_reg_def relabel_ta_def term_reg_def
lemma is_ta_eps_free_trim_reg [intro!]:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta (trim_reg R))"
  by (simp add: is_ta_eps_free_def trim_reg_def trim_ta_def ta_restrict_def)

lemma is_ta_eps_free_relabel_reg [intro!]:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta (relabel_reg R))"
  by (simp add: is_ta_eps_free_def relabel_reg_def relabel_ta_def fmap_states_ta_def)

lemma is_ta_eps_free_simplify_reg [intro!]:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta (simplify_reg R))"
  by (simp add: is_ta_eps_free_def ta_simp_unfold fmap_states_ta_def trim_ta_def ta_restrict_def)

lemma is_ta_emptyI [simp]:
 "is_ta_eps_free (TA R {||}) \<longleftrightarrow> True"
  by (simp add: is_ta_eps_free_def)

lemma is_ta_empty_trim_reg:
  "is_ta_eps_free (ta A) \<Longrightarrow> eps (ta (trim_reg A)) = {||}"
  by (auto simp: is_ta_eps_free_def trim_reg_def trim_ta_def ta_restrict_def)

lemma is_proj_ta_eps_empty:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta (proj_1_reg R))"
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta (proj_2_reg R))"
  by (auto simp: is_ta_eps_free_def proj_1_reg_def proj_2_reg_def collapse_automaton_reg_def collapse_automaton_def
    fmap_funs_reg_def fmap_funs_ta_def trim_reg_def trim_ta_def ta_restrict_def)

lemma is_pod_ta_eps_empty:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta L) \<Longrightarrow> is_ta_eps_free (ta (reg_intersect R L))"
  by (auto simp: reg_intersect_def prod_ta_def prod_epsRp_def prod_epsLp_def is_ta_eps_free_def)

lemma is_fmap_funs_reg_eps_empty:
  "is_ta_eps_free (ta R) \<Longrightarrow>  is_ta_eps_free (ta (fmap_funs_reg f R))"
  by (auto simp: fmap_funs_reg_def fmap_funs_ta_def is_ta_eps_free_def)

lemma is_collapse_automaton_reg_eps_empty:
  "is_ta_eps_free (ta R) \<Longrightarrow>  is_ta_eps_free (ta (collapse_automaton_reg R))"
  by (auto simp: collapse_automaton_reg_def collapse_automaton_def is_ta_eps_free_def)

lemma is_pair_automaton_reg_eps_empty:
  "is_ta_eps_free (ta R) \<Longrightarrow> is_ta_eps_free (ta L) \<Longrightarrow> is_ta_eps_free (ta (pair_automaton_reg R L))"
  by (auto simp: pair_automaton_reg_def pair_automaton_def is_ta_eps_free_def)

lemma is_reflcl_automaton_eps_free:
  "is_ta_eps_free A \<Longrightarrow> is_ta_eps_free (reflcl_automaton (lift_sig_RR2 |`| \<F>) A)"
  by (auto simp: is_ta_eps_free_def reflcl_automaton_def ta_union_def gen_reflcl_automaton_def Let_def fmap_states_ta_def)

lemma is_GTT_to_RR2_root_eps_empty:
  "is_gtt_eps_free \<G> \<Longrightarrow> is_ta_eps_free (GTT_to_RR2_root \<G>)"
  by (auto simp: is_gtt_eps_free_def GTT_to_RR2_root_def pair_automaton_def is_ta_eps_free_def)

lemma is_term_automata_eps_empty:
  "is_ta_eps_free (ta (term_reg \<F>)) \<longleftrightarrow> True"
  by (auto simp: is_ta_eps_free_def term_reg_def term_automaton_def)

lemma is_ta_eps_free_eps_free_automata [simp]:
  " is_ta_eps_free (eps_free_automata S R) \<longleftrightarrow> True"
  by (auto simp: eps_free_automata_def is_ta_eps_free_def)

lemma rr2_of_rr2_rel_impl_eps_free:
  shows "\<forall> A. rr1_of_rr1_rel_impl \<F> Rs r1 = Some A \<longrightarrow> is_ta_eps_free (ta A)"
   "\<forall> A. rr2_of_rr2_rel_impl \<F> Rs r2 = Some A \<longrightarrow> is_ta_eps_free (ta A)"
proof (induct r1 and r2)
case R1Terms
  then show ?case
    by (auto simp: is_ta_eps_free_def term_automaton_def fmap_states_ta_def ta_simp_unfold)
next
  case (R1NF x)
  then show ?case
    by (auto simp: nf_reg_def nf_ta_def)
next
  case (R1Inf x)
  then show ?case
    by (auto simp: Inf_reg_impl_def Let_def Inf_reg_def Inf_automata_def is_ta_empty_trim_reg intro!: is_proj_ta_eps_empty)
next
  case (R1Proj n x2)
  then show ?case
    by (cases n) (auto  intro!: is_proj_ta_eps_empty)
next
  case (R1Union x1 x2)
  then show ?case
    by (simp add: reg_union_def ta_union_def fmap_states_ta_def is_ta_eps_free_def relabel_reg_def relabel_ta_def)
next
  case (R1Inter x1 x2)
  then show ?case
    by (auto intro: is_pod_ta_eps_empty)
next
  case (R1Diff x1 x2)
  then show ?case
    by (auto simp: difference_reg_def Let_def complement_reg_def ps_reg_def ps_ta_def intro!: is_pod_ta_eps_empty)
next
  case (R2GTT_Rel x1 x2 x3)
  then show ?case 
    by (cases x2; cases x3) (auto simp: GTT_to_RR2_root_reg_def ftrancl_eps_free_closures_def
      eps_free_nhole_mctxt_closure_reg_def eps_free_nhole_mctxt_reflcl_reg_def Let_def
      eps_free_mctxt_closure_reg_def reflcl_reg_def
      dest: gtt_of_gtt_rel_impl_is_gtt_eps_free
      intro!: is_GTT_to_RR2_root_eps_empty is_reflcl_automaton_eps_free)
next
  case (R2Diag x)
  then show ?case by (auto simp: fmap_funs_reg_def fmap_funs_ta_def is_ta_eps_free_def)
next
  case (R2Prod x1 x2)
  then show ?case by (auto intro: is_pair_automaton_reg_eps_empty)
next
  case (R2Inv x)
  then show ?case by (auto simp: fmap_funs_reg_def fmap_funs_ta_def is_ta_eps_free_def)
next
  case (R2Union x1 x2)
  then show ?case by (simp add: reg_union_def ta_union_def fmap_states_ta_def is_ta_eps_free_def relabel_reg_def relabel_ta_def)
next
  case (R2Inter x1 x2)
  then show ?case by (auto intro: is_pod_ta_eps_empty)
next
  case (R2Diff x1 x2)
  then show ?case by (auto simp: difference_reg_def Let_def complement_reg_def ps_reg_def ps_ta_def intro!: is_pod_ta_eps_empty)
next
  case (R2Comp x1 x2)
  then show ?case by (auto simp: is_term_automata_eps_empty rr2_compositon_def Let_def
     intro!: is_pod_ta_eps_empty is_fmap_funs_reg_eps_empty is_collapse_automaton_reg_eps_empty is_pair_automaton_reg_eps_empty)
qed

lemma rr_of_rr_rel_impl_complete:
  "rr1_of_rr1_rel_impl \<F> Rs r1 \<noteq> None \<longleftrightarrow> rr1_of_rr1_rel \<F> Rs r1 \<noteq> None"
  "rr2_of_rr2_rel_impl \<F> Rs r2 \<noteq> None \<longleftrightarrow> rr2_of_rr2_rel \<F> Rs r2 \<noteq> None"
proof (induct r1 and r2)
  case (R1Proj n x2)
  then show ?case by (cases n) auto
next
  case (R2GTT_Rel x1 n p)
  then show ?case using gtt_of_gtt_rel_impl_gtt_of_gtt_rel[of \<F> Rs]
    by (cases p; cases n) auto
qed auto

lemma \<Q>_fmap_funs_reg [simp]:
  "\<Q>\<^sub>r (fmap_funs_reg f \<A>) = \<Q>\<^sub>r \<A>"
  by (auto simp: fmap_funs_reg_def)

lemma ta_reachable_fmap_funs_reg [simp]:
  "ta_reachable (ta (fmap_funs_reg f \<A>)) = ta_reachable (ta \<A>)"
  by (auto simp: fmap_funs_reg_def)

lemma collapse_reg_cong:
  "\<Q>\<^sub>r \<A> |\<subseteq>| ta_reachable (ta \<A>) \<Longrightarrow> \<Q>\<^sub>r \<B> |\<subseteq>| ta_reachable (ta \<B>) \<Longrightarrow> \<L> \<A> = \<L> \<B> \<Longrightarrow> \<L> (collapse_automaton_reg \<A>) = \<L> (collapse_automaton_reg \<B>)"
  by (auto simp: collapse_automaton_reg_def \<L>_def collapse_automaton')

lemma \<L>_fmap_funs_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<L> (fmap_funs_reg h \<A>) = \<L> (fmap_funs_reg h \<B>)"
  by (auto simp: fmap_funs_\<L>)

lemma \<L>_pair_automaton_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<L> \<C> = \<L> \<D> \<Longrightarrow> \<L> (pair_automaton_reg \<A> \<C>) = \<L> (pair_automaton_reg \<B> \<D>)"
  by (auto simp: pair_automaton')

lemma \<L>_nhole_ctxt_closure_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (nhole_ctxt_closure_reg \<F> \<A>) = \<L> (nhole_ctxt_closure_reg \<G> \<B>)"
  by (auto simp: nhole_ctxtcl_lang)

lemma \<L>_nhole_mctxt_closure_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (nhole_mctxt_closure_reg \<F> \<A>) = \<L> (nhole_mctxt_closure_reg \<G> \<B>)"
  by (auto simp: nhole_gmctxt_closure_lang)

lemma \<L>_ctxt_closure_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (ctxt_closure_reg \<F> \<A>) = \<L> (ctxt_closure_reg \<G> \<B>)"
  by (auto simp: gctxt_closure_lang)

lemma \<L>_parallel_closure_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (parallel_closure_reg \<F> \<A>) = \<L> (parallel_closure_reg \<G> \<B>)"
  by (auto simp: parallelcl_gmctxt_lang)

lemma \<L>_mctxt_closure_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (mctxt_closure_reg \<F> \<A>) = \<L> (mctxt_closure_reg \<G> \<B>)"
  by (auto simp: gmctxt_closure_lang)

lemma \<L>_nhole_mctxt_reflcl_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<F> = \<G> \<Longrightarrow> \<L> (nhole_mctxt_reflcl_reg \<F> \<A>) = \<L> (nhole_mctxt_reflcl_reg \<G> \<B>)"
  unfolding nhole_mctxt_reflcl_lang
  by (intro arg_cong2[where ?f = "(\<union>)"] \<L>_nhole_mctxt_closure_reg_cong) auto

declare equalityI[rule del]
declare fsubsetI[rule del]
lemma \<L>_proj_1_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<L> (proj_1_reg \<A>) = \<L> (proj_1_reg \<B>)"
  by (auto simp: proj_1_reg_def \<L>_trim intro!: collapse_reg_cong \<L>_fmap_funs_reg_cong)

lemma \<L>_proj_2_reg_cong:
  "\<L> \<A> = \<L> \<B> \<Longrightarrow> \<L> (proj_2_reg \<A>) = \<L> (proj_2_reg \<B>)"
  by (auto simp: proj_2_reg_def \<L>_trim intro!: collapse_reg_cong \<L>_fmap_funs_reg_cong)

lemma rr2_of_rr2_rel_impl_sound:
  assumes  "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  shows "\<And> A B. rr1_of_rr1_rel_impl \<F> Rs r1 = Some A \<Longrightarrow> rr1_of_rr1_rel \<F> Rs r1 = Some B \<Longrightarrow> \<L> A = \<L> B"
  "\<And> A B. rr2_of_rr2_rel_impl \<F> Rs r2 = Some A \<Longrightarrow> rr2_of_rr2_rel \<F> Rs r2 = Some B \<Longrightarrow> \<L> A = \<L> B"
proof (induct r1 and r2)
  case (R1Inf r)
  then obtain C D where inf: "rr2_of_rr2_rel_impl \<F> Rs r = Some C" "rr2_of_rr2_rel \<F> Rs r = Some D"
     "\<L> C = \<L> D" by auto
  have spec: "RR2_spec C (eval_rr2_rel (fset \<F>) (map fset Rs) r)" "RR2_spec D (eval_rr2_rel (fset \<F>) (map fset Rs) r)"
    using rr12_of_rr12_rel_correct(2)[OF assms, rule_format, OF inf(2)] inf(3)
    by (auto simp: RR2_spec_def)
  then have trim_spec: "RR2_spec (trim_reg C) (eval_rr2_rel (fset \<F>) (map fset Rs) r)"
    "RR2_spec (trim_reg D) (eval_rr2_rel (fset \<F>) (map fset Rs) r)"
    by (auto simp: RR2_spec_def \<L>_trim)
  let ?C = "Inf_reg (trim_reg C) (Q_infty (ta (trim_reg C)) \<F>)" let ?D = "Inf_reg (trim_reg D) (Q_infty (ta (trim_reg D)) \<F>)" 
  from spec have *: "\<L> (Inf_reg_impl (trim_reg C)) = \<L> ?C"
    using eval_rr12_rel_sig(2)[of "fset \<F>" "map fset Rs" r]
    by (intro Inf_reg_impl_sound) (auto simp: RR2_spec_def \<L>_trim \<T>\<^sub>G_equivalent_def)
  from spec have **: "\<L> (Inf_reg_impl (trim_reg D)) = \<L> ?D"
    using eval_rr12_rel_sig(2)[of "fset \<F>" "map fset Rs" r]
    by (intro Inf_reg_impl_sound) (auto simp: RR2_spec_def \<L>_trim \<T>\<^sub>G_equivalent_def)
  then have C: "RR2_spec ?C {(s, t) | s t. gpair s t \<in> \<L> ?C}" and
    D: "RR2_spec ?D {(s, t) | s t. gpair s t \<in> \<L> ?D}"
    using subset_trans[OF Inf_automata_subseteq[of "trim_reg C" \<F>], of "\<L> C"] spec
    using subset_trans[OF Inf_automata_subseteq[of "trim_reg D" \<F>], of "\<L> D"]
    using eval_rr12_rel_sig(2)[of "fset \<F>" "map fset Rs" r]
    by (auto simp: RR2_spec_def \<L>_trim \<T>\<^sub>G_equivalent_def intro!: equalityI fsubsetI)
  from * ** have r: "\<L> (proj_1_reg (Inf_reg_impl (trim_reg C))) = \<L> (proj_1_reg ?C)"
    "\<L> (proj_1_reg (Inf_reg_impl (trim_reg D))) = \<L> (proj_1_reg ?D)"
    by (auto intro: \<L>_proj_1_reg_cong)
  from \<L>_Inf_reg[OF trim_spec(1), of \<F>] \<L>_Inf_reg[OF trim_spec(2), of \<F>]
  show ?case using R1Inf eval_rr12_rel_sig(2)[of "fset \<F>" "map fset Rs" r]
    by (auto simp: liftO1_def r inf \<T>\<^sub>G_equivalent_def \<L>_proj(1)[OF C] \<L>_proj(1)[OF D])
next
  case (R1Proj n x2)
  then show ?case by (cases n)
    (auto simp: liftO1_def \<L>_trim proj_1_reg_def proj_2_reg_def intro!: fsubsetI \<L>_fmap_funs_reg_cong collapse_reg_cong, (meson fin_mono trim_reg_reach)+)
next
  case (R2GTT_Rel g p n) note IH = this
  note ass = R2GTT_Rel
  consider (a) "\<exists> A. gtt_of_gtt_rel_impl \<F> Rs g = Some A" | (b) "gtt_of_gtt_rel_impl \<F> Rs g = None" by blast
  then show ?case
  proof cases
    case a then obtain C D where gtt [simp]: "gtt_of_gtt_rel_impl \<F> Rs g = Some C"
      "gtt_of_gtt_rel \<F> Rs g = Some D" using gtt_of_gtt_rel_impl_gtt_of_gtt_rel by blast
    from gtt_of_gtt_rel_impl_sound[OF this]
    have spec [simp]: "agtt_lang C = agtt_lang D" by auto
    have eps [simp]: "is_ta_eps_free (ta (GTT_to_RR2_root_reg C))"
      using gtt_of_gtt_rel_impl_is_gtt_eps_free[OF gtt(1)]
      by (auto simp: GTT_to_RR2_root_reg_def GTT_to_RR2_root_def pair_automaton_def is_ta_eps_free_def is_gtt_eps_free_def)
    have lang: "\<L> (GTT_to_RR2_root_reg C) = \<L> (GTT_to_RR2_root_reg D)"
      by (metis (no_types, lifting) GTT_to_RR2_root RR2_spec_def spec)
    show ?thesis
    proof (cases p)
      case PRoot
      then show ?thesis using IH spec lang
        by (cases n) (auto simp: \<L>_eps_free \<L>_reflcl_reg)
    next
      case PNonRoot
      then show ?thesis using IH
        by (cases n) (auto simp: \<L>_eps_free \<L>_eps_free_nhole_ctxt_closure_reg[OF eps]
        \<L>_eps_free_nhole_mctxt_reflcl_reg[OF eps] \<L>_eps_free_nhole_mctxt_closure_reg[OF eps]
        lang intro: \<L>_nhole_ctxt_closure_reg_cong \<L>_nhole_mctxt_reflcl_reg_cong \<L>_nhole_mctxt_closure_reg_cong)
    next
      case PAny
      then show ?thesis using IH
        by (cases n) (auto simp: \<L>_eps_free \<L>_eps_free_ctxt_closure_reg[OF eps]
          \<L>_eps_free_parallel_closure_reg[OF eps] \<L>_eps_free_mctxt_closure_reg[OF eps] lang
          intro!: \<L>_ctxt_closure_reg_cong \<L>_parallel_closure_reg_cong \<L>_mctxt_closure_reg_cong)
    qed
  next
    case b then show ?thesis using IH
      by (cases p; cases n) auto
  qed
next
  case (R2Comp x1 x2)
  then show ?case
    by (auto simp: liftO1_def rr2_compositon_def \<L>_trim \<L>_intersect Let_def
        intro!: \<L>_pair_automaton_reg_cong \<L>_fmap_funs_reg_cong collapse_reg_cong arg_cong2[where ?f = "(\<inter>)"])
qed (auto simp: liftO1_def \<L>_intersect \<L>_union \<L>_trim \<L>_difference_reg intro!: \<L>_fmap_funs_reg_cong \<L>_pair_automaton_reg_cong)
declare equalityI[intro!]
declare fsubsetI[intro!]

lemma rr12_of_rr12_rel_impl_correct:
  assumes  "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  shows "\<forall>ta1. rr1_of_rr1_rel_impl \<F> Rs r1 = Some ta1 \<longrightarrow> RR1_spec ta1 (eval_rr1_rel (fset \<F>) (map fset Rs) r1)"
    "\<forall>ta2. rr2_of_rr2_rel_impl \<F> Rs r2 = Some ta2 \<longrightarrow> RR2_spec ta2 (eval_rr2_rel (fset \<F>) (map fset Rs) r2)"
  using rr12_of_rr12_rel_correct(1)[OF assms, of r1]
  using rr12_of_rr12_rel_correct(2)[OF assms, of r2]
  using rr2_of_rr2_rel_impl_sound(1)[OF assms, of r1]
  using rr2_of_rr2_rel_impl_sound(2)[OF assms, of r2]
  using rr_of_rr_rel_impl_complete(1)[of \<F> Rs r1]
  using rr_of_rr_rel_impl_complete(2)[of \<F> Rs r2]
  by (force simp: RR1_spec_def RR2_spec_def)+

lemma check_inference_rrn_impl_correct:
  assumes sig: "\<T>\<^sub>G (fset \<F>) \<noteq> {}" and Rs: "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  assumes infs: "\<And>fvA. fvA \<in> set infs \<Longrightarrow> formula_spec (fset \<F>) (map fset Rs) (fst (snd fvA)) (snd (snd fvA)) (fst fvA)"
  assumes inf: "check_inference rr1_of_rr1_rel_impl rr2_of_rr2_rel_impl \<F> Rs infs (l, step, fm, is) = Some (fm', vs, A')"
  shows "l = length infs \<and> fm = fm' \<and> formula_spec (fset \<F>) (map fset Rs) vs A' fm'"
  using check_inference_correct[where ?rr1c = rr1_of_rr1_rel_impl and ?rr2c = rr2_of_rr2_rel_impl, OF assms]
  using rr12_of_rr12_rel_impl_correct[OF Rs]
  by auto

definition check_sig_nempty where
  "check_sig_nempty \<F> = (0 |\<in>| snd |`| \<F>)"

definition check_trss where
  "check_trss \<R> \<F> = list_all (\<lambda> R. lv_trs (fset R) \<and> funas_trs (fset R) \<subseteq> fset \<F>) \<R>"

lemma check_sig_nempty:
  "check_sig_nempty \<F> \<longleftrightarrow> \<T>\<^sub>G (fset \<F>) \<noteq> {}" (is "?Ls \<longleftrightarrow> ?Rs")
proof -
  {assume ?Ls then obtain a where "(a, 0) |\<in>| \<F>" by (auto simp: check_sig_nempty_def)
    then have "GFun a [] \<in> \<T>\<^sub>G (fset \<F>)"
      by (intro const) simp
    then have ?Rs by blast}
  moreover
  {assume ?Rs then obtain s where "s \<in> \<T>\<^sub>G (fset \<F>)" by blast
    then obtain a where "(a, 0) |\<in>| \<F>"
      by (induct s) (auto, force)
    then have ?Ls unfolding check_sig_nempty_def
      by (auto simp: image_iff Bex_def)}
  ultimately show ?thesis by blast
qed

lemma check_trss:
  "check_trss \<R> \<F> \<longleftrightarrow> (\<forall> R \<in> set \<R>. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>)"
  unfolding check_trss_def list_all_iff
  by (auto simp: ffunas_trs.rep_eq less_eq_fset.rep_eq)

fun check_inference_list :: "('f \<times> nat) fset \<Rightarrow> ('f ::  {compare,linorder}, 'v) fin_trs list
  \<Rightarrow> (nat \<times> ftrs inference \<times> ftrs formula \<times> info list) list
  \<Rightarrow> (ftrs formula \<times> nat list \<times> (nat, 'f option list) reg) list option" where
  "check_inference_list \<F> Rs infs = do {
     guard (check_sig_nempty \<F>);
     guard (check_trss Rs \<F>);
     foldl (\<lambda> tas inf. do {
        tas' \<leftarrow> tas;
        r \<leftarrow> check_inference rr1_of_rr1_rel_impl rr2_of_rr2_rel_impl \<F> Rs tas' inf;
        Some (tas' @ [r])
      })
      (Some []) infs
  }"

lemma check_inference_list_correct:
  assumes "check_inference_list \<F> Rs infs = Some fvAs"
  shows "length infs = length fvAs \<and> (\<forall> i < length fvAs. fst (snd (snd (infs ! i))) = fst (fvAs ! i)) \<and>
   (\<forall> i < length fvAs. formula_spec (fset \<F>) (map fset Rs) (fst (snd (fvAs ! i))) (snd (snd (fvAs ! i))) (fst (fvAs ! i)))"
  using assms
proof (induct infs arbitrary: fvAs rule: rev_induct)
  note [simp] = bind_eq_Some_conv guard_simps
  {case Nil
    then show ?case by auto
  next
    case (snoc a infs)
    have inv: "\<T>\<^sub>G (fset \<F>) \<noteq> {}" "\<forall>R\<in>set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
      using snoc(2) by (auto simp: check_sig_nempty check_trss)
    from snoc(2) obtain fvAs' l steps fm fm' is' vs A' where
      ch: "check_inference_list \<F> Rs infs = Some fvAs'" "a = (l, steps, fm, is')"
      "check_inference rr1_of_rr1_rel_impl rr2_of_rr2_rel_impl \<F> Rs fvAs' (l, steps, fm, is') = Some (fm', vs, A')" "fvAs = fvAs' @ [(fm', vs, A')]"
      by (auto simp del: check_inference.simps) (metis prod_cases4)
    from snoc(1)[OF ch(1)] have "fvA \<in> set fvAs' \<Longrightarrow> formula_spec (fset \<F>) (map fset Rs) (fst (snd fvA)) (snd (snd fvA)) (fst fvA)" for fvA
      by (auto dest: in_set_idx)
    from check_inference_rrn_impl_correct[OF inv this, of fvAs'] this
    show ?case using snoc(1)[OF ch(1)] ch
      by (auto simp del: check_inference.simps simp: nth_append)
  }
qed

fun check_certificate where
  "check_certificate \<F> Rs A fm (Certificate infs claim n) = do {
    guard (n < length infs);
    guard (A \<longleftrightarrow> claim = Nonempty);
    guard (fm = fst (snd (snd (infs ! n))));
    fvA \<leftarrow> check_inference_list \<F> Rs (take (Suc n) infs);
    (let E = reg_empty (snd (snd (last fvA))) in
     case claim of Empty \<Rightarrow> Some E
       | _ \<Rightarrow> Some (\<not> E))
  }"

definition formula_unsatisfiable where
  "formula_unsatisfiable \<F> Rs fm \<longleftrightarrow> (formula_satisfiable \<F> Rs fm = False)"

definition correct_certificate where
  "correct_certificate \<F> Rs claim infs n \<equiv>
    (claim = Empty \<longleftrightarrow> (formula_unsatisfiable (fset \<F>) (map fset Rs) (fst (snd (snd (infs ! n))))) \<and>
     claim = Nonempty \<longleftrightarrow> formula_satisfiable (fset \<F>) (map fset Rs) (fst (snd (snd (infs ! n)))))"

lemma check_certificate_sound:
  assumes "check_certificate \<F> Rs A fm (Certificate infs claim n) = Some B"
  shows "fm = fst (snd (snd (infs ! n)))" "A \<longleftrightarrow> claim = Nonempty"
  using assms by (auto simp: bind_eq_Some_conv guard_simps)

lemma check_certificate_correct:
  assumes "check_certificate \<F> Rs A fm (Certificate infs claim n) = Some B"
  shows "(B = True \<longrightarrow> correct_certificate \<F> Rs claim infs n) \<and>
    (B = False \<longrightarrow> correct_certificate \<F> Rs (case_claim Nonempty Empty claim) infs n)"
proof -
  note [simp] = bind_eq_Some_conv guard_simps
  from assms obtain fvAs where inf: "check_inference_list \<F> Rs (take (Suc n) infs) = Some fvAs"
    by auto
  from assms have len: "n < length infs" by auto
  from check_inference_list_correct[OF inf] have
    inv: "length fvAs = n + 1"
    "fst (snd (snd (infs ! n))) = fst (fvAs ! n)"
    "formula_spec (fset \<F>) (map fset Rs) (fst (snd (last fvAs))) (snd (snd (last fvAs))) (fst (last fvAs))"
    using len last_conv_nth[of fvAs] by force+
  have nth: "fst (last fvAs) = fst (fvAs ! n)" using inv(1)
    using len last_conv_nth[of fvAs] by force
  note spec = formula_spec_empty[OF _ inv(3)] formula_spec_nt_empty_form_sat[OF _ inv(3)]
  consider (a) "claim = Empty" | (b) "claim = Nonempty" using claim.exhaust by blast
  then show ?thesis
  proof cases
    case a
    then have *: "B = reg_empty (snd (snd (last fvAs)))" using inv
      using assms len last_conv_nth[of fvAs]
      by (auto simp: inf simp del: check_inference_list.simps)
    show ?thesis using a inv spec unfolding *
      by (auto simp: formula_satisfiable_def nth correct_certificate_def formula_unsatisfiable_def simp del: reg_empty)
  next
    case b
    then have *: "B \<longleftrightarrow> \<not> (reg_empty (snd (snd (last fvAs))))" using inv
      using assms len last_conv_nth[of fvAs]
      by (auto simp: inf simp del: check_inference_list.simps)
    show ?thesis using b inv spec unfolding *
      by (auto simp: formula_satisfiable_def nth formula_unsatisfiable_def correct_certificate_def simp del: reg_empty)
  qed
qed


definition check_certificate_string ::
  "(integer list \<times> fvar) fset \<Rightarrow>
   ((integer list, integer list) Term.term \<times> (integer list, integer list) Term.term) fset list \<Rightarrow>
   bool \<Rightarrow> ftrs formula \<Rightarrow> ftrs certificate \<Rightarrow> bool option"
  where "check_certificate_string = check_certificate"


(***********************************)
export_code check_certificate_string Var Fun fset_of_list nat_of_integer Certificate
  R2GTT_Rel R2Eq R2Reflc R2Step R2StepEq R2Steps R2StepsEq R2StepsNF R2ParStep R2RootStep
  R2RootStepEq R2RootSteps R2RootStepsEq R2NonRootStep R2NonRootStepEq R2NonRootSteps
  R2NonRootStepsEq R2Meet R2Join
  ARoot GSteps PRoot ESingle Empty Size EDistribAndOr
  R1Terms R1Fin
  FRR1 FRestrict FTrue FFalse
  IRR1 Fwd in Haskell module_name FOR

end