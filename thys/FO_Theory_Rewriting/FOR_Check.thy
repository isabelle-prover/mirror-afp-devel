theory FOR_Check
  imports
    FOR_Semantics
    FOL_Extra
    GTT_RRn
    First_Order_Terms.Option_Monad
    LV_to_GTT
    NF
    Regular_Tree_Relations.GTT_Transitive_Closure
    Regular_Tree_Relations.AGTT
    Regular_Tree_Relations.RR2_Infinite_Q_infinity
    Regular_Tree_Relations.RRn_Automata
begin

section \<open>Check inference steps\<close>

type_synonym ('f, 'v) fin_trs  = "('f, 'v) rule fset"

lemma tl_drop_conv:
  "tl xs = drop 1 xs"
  by (induct xs) auto

definition rrn_drop_fst where
  "rrn_drop_fst \<A> = relabel_reg (trim_reg (collapse_automaton_reg (fmap_funs_reg (drop_none_rule 1) (trim_reg \<A>))))"

lemma rrn_drop_fst_lang:
  assumes "RRn_spec n A T" "1 < n"
  shows "RRn_spec (n - 1) (rrn_drop_fst A) (drop 1 ` T)"
  using drop_automaton_reg[OF _ assms(2), of "trim_reg A" T] assms(1)
  unfolding rrn_drop_fst_def
  by (auto simp: trim_ta_reach)


definition liftO1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "liftO1 = map_option"

definition liftO2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option" where
  "liftO2 f a b = case_option None (\<lambda>a'. liftO1 (f a') b) a"

lemma liftO1_Some [simp]:
  "liftO1 f x = Some y \<longleftrightarrow> (\<exists>x'. x = Some x') \<and> y = f (the x)"
  by (cases x) (auto simp: liftO1_def)

lemma liftO2_Some [simp]:
  "liftO2 f x y = Some z \<longleftrightarrow> (\<exists>x' y'. x = Some x' \<and> y = Some y') \<and> z = f (the x) (the y)"
  by (cases x; cases y) (auto simp: liftO2_def)

subsection \<open>Computing TRSs\<close>

lemma is_to_trs_props:
  assumes "\<forall> R \<in> set Rs. finite R \<and> lv_trs R \<and> funas_trs R \<subseteq> \<F>" "\<forall>i \<in> set is. case_ftrs id id i < length Rs"
  shows "funas_trs (is_to_trs Rs is) \<subseteq> \<F>" "lv_trs (is_to_trs Rs is)" "finite (is_to_trs Rs is)"
proof (goal_cases \<F> lv fin)
  case \<F> show ?case using assms nth_mem
    apply (auto simp: is_to_trs_def funas_trs_def case_prod_beta split: ftrs.splits)
     apply fastforce
    apply (metis (no_types, lifting) assms(1) in_mono rhs_wf)
    apply (metis (no_types, lifting) assms(1) in_mono rhs_wf)
    by (smt (z3) UN_subset_iff fst_conv in_mono le_sup_iff)
qed (insert assms, (fastforce simp: is_to_trs_def funas_trs_def lv_trs_def split: ftrs.splits)+)


definition is_to_fin_trs :: "('f, 'v) fin_trs list \<Rightarrow> ftrs list \<Rightarrow> ('f, 'v) fin_trs" where
  "is_to_fin_trs Rs is = |\<Union>|  (fset_of_list (map (case_ftrs ((!) Rs) ((|`|) prod.swap \<circ> (!) Rs)) is))"


lemma is_to_fin_trs_conv:
  assumes "\<forall>i \<in> set is. case_ftrs id id i < length Rs"
  shows "is_to_trs (map fset Rs) is = fset (is_to_fin_trs Rs is)"
  using assms unfolding is_to_trs_def is_to_fin_trs_def
  by (auto simp: ffUnion.rep_eq fset_of_list.rep_eq split: ftrs.splits)

definition is_to_trs' :: "('f, 'v) fin_trs list \<Rightarrow> ftrs list \<Rightarrow> ('f, 'v) fin_trs option" where
  "is_to_trs' Rs is = do {
    guard (\<forall>i \<in> set is. case_ftrs id id i < length Rs);
    Some (is_to_fin_trs Rs is)
  }"

lemma is_to_trs_conv:
  "is_to_trs' Rs is = Some S \<Longrightarrow> is_to_trs (map fset Rs) is = fset S"
  using is_to_fin_trs_conv unfolding is_to_trs'_def
  by (auto simp add: guard_simps split: bind_splits)

lemma is_to_trs'_props:
  assumes "\<forall> R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>" and "is_to_trs' Rs is = Some S"
  shows "ffunas_trs S |\<subseteq>| \<F>" "lv_trs (fset S)"
proof -
  from assms(2) have well: "\<forall>i \<in> set is. case_ftrs id id i < length Rs" "is_to_fin_trs Rs is = S"
    unfolding is_to_trs'_def
    by (auto simp add: guard_simps split: bind_splits)
  have "\<forall> R \<in> set Rs. finite (fset R) \<and> lv_trs (fset R) \<and> funas_trs (fset R) \<subseteq> (fset \<F>)"
    using assms(1) by (auto simp: ffunas_trs.rep_eq less_eq_fset.rep_eq)
  from is_to_trs_props[of "map fset Rs" "fset \<F>" "is"] this well(1)
  have "lv_trs (is_to_trs (map fset Rs) is)" "funas_trs (is_to_trs (map fset Rs) is) \<subseteq> fset \<F>"
    by auto
  then show "lv_trs (fset S)" "ffunas_trs S |\<subseteq>| \<F>"
    using is_to_fin_trs_conv[OF well(1)] unfolding well(2)
    by (auto simp: ffunas_trs.rep_eq less_eq_fset.rep_eq)
qed

subsection \<open>Computing GTTs\<close>

fun gtt_of_gtt_rel :: "('f \<times> nat) fset \<Rightarrow> ('f :: linorder, 'v) fin_trs list \<Rightarrow> ftrs gtt_rel \<Rightarrow> (nat, 'f) gtt option" where
  "gtt_of_gtt_rel \<F> Rs (ARoot is) = liftO1 (\<lambda>R. relabel_gtt (agtt_grrstep R \<F>)) (is_to_trs' Rs is)"
| "gtt_of_gtt_rel \<F> Rs (GInv g) = liftO1 prod.swap (gtt_of_gtt_rel \<F> Rs g)"
| "gtt_of_gtt_rel \<F> Rs (AUnion g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (AGTT_union' g1 g2)) (gtt_of_gtt_rel \<F> Rs g1) (gtt_of_gtt_rel \<F> Rs g2)"
| "gtt_of_gtt_rel \<F> Rs (ATrancl g) = liftO1 (relabel_gtt \<circ> AGTT_trancl) (gtt_of_gtt_rel \<F> Rs g)"
| "gtt_of_gtt_rel \<F> Rs (GTrancl g) = liftO1 GTT_trancl (gtt_of_gtt_rel \<F> Rs g)"
| "gtt_of_gtt_rel \<F> Rs (AComp g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (AGTT_comp' g1 g2)) (gtt_of_gtt_rel \<F> Rs g1) (gtt_of_gtt_rel \<F> Rs g2)"
| "gtt_of_gtt_rel \<F> Rs (GComp g1 g2) = liftO2 (\<lambda>g1 g2. relabel_gtt (GTT_comp' g1 g2)) (gtt_of_gtt_rel \<F> Rs g1) (gtt_of_gtt_rel \<F> Rs g2)"


lemma gtt_of_gtt_rel_correct:
  assumes "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  shows "gtt_of_gtt_rel \<F> Rs g = Some g' \<Longrightarrow> agtt_lang g' = eval_gtt_rel (fset \<F>) (map fset Rs) g"
proof (induct g arbitrary: g')
  note [simp] = bind_eq_Some_conv guard_simps
  have proj_sq: "fst ` (X \<times> X) = X" "snd ` (X \<times> X) = X" for X by auto
{
  case (ARoot "is")
  then obtain w where w:"is_to_trs' Rs is = Some w" by auto
  then show ?case using ARoot is_to_trs'_props[OF assms w] is_to_trs_conv[OF w]
    using agtt_grrstep 
    by auto
next
  case (GInv g) then show ?case by (simp add: agtt_lang_swap gtt_states_def)
next
  case (AUnion g1 g2)
  from AUnion(3)[simplified, THEN conjunct1] AUnion(3)[simplified, THEN conjunct2, THEN conjunct1]
  obtain w1 w2 where
    [simp]: "gtt_of_gtt_rel \<F> Rs g1 = Some w1" "gtt_of_gtt_rel \<F> Rs g2 = Some w2"
    by blast
  then show ?case using AUnion(3)
    by (simp add: AGTT_union'_sound AUnion)
next
  case (ATrancl g)
  from ATrancl[simplified] obtain w1 where
    [simp]: "gtt_of_gtt_rel \<F> Rs g = Some w1" "g' = relabel_gtt (AGTT_trancl w1)" by auto
  then have fin_lang: "eval_gtt_rel (fset \<F>) (map fset Rs) g = agtt_lang w1"
    using ATrancl by auto
  from fin_lang show ?case using AGTT_trancl_sound[of w1]
    by auto
next
  case (GTrancl g) note * = GTrancl(2)[simplified, THEN conjunct2]
  show ?case unfolding gtt_of_gtt_rel.simps GTT_trancl_alang * gtrancl_rel_def eval_gtt_rel.simps gmctxt_cl_gmctxtex_onp_conv
  proof ((intro conjI equalityI subrelI; (elim relcompE)?), goal_cases LR RL)
    case (LR _ _ s _ z s' t' t)
    show ?case using lift_root_steps_sig_transfer'[OF LR(2)[folded lift_root_step.simps], of "fset \<F>"]
      lift_root_steps_sig_transfer[OF LR(5)[folded lift_root_step.simps], of "fset \<F>"]
      image_mono[OF eval_gtt_rel_sig[of "fset \<F>" "map fset Rs" g], of fst, unfolded proj_sq]
      image_mono[OF eval_gtt_rel_sig[of "fset \<F>" "map fset Rs" g], of snd, unfolded proj_sq]
      subsetD[OF eval_gtt_rel_sig[of "fset \<F>" "map fset Rs" g]] LR(1, 3, 4) GTrancl
      by (intro relcompI[OF _ relcompI, of _ s' _ t' _])
         (auto simp: \<T>\<^sub>G_funas_gterm_conv lift_root_step.simps)
  next
    case (RL _ _ s _ z s' t' t)
    then show ?case using GTrancl
      lift_root_step_mono[of "fset \<F>" UNIV PAny ESingle "eval_gtt_rel (fset \<F>) (map fset Rs) g", THEN rtrancl_mono]
      unfolding lift_root_step.simps[symmetric]
      by (intro relcompI[OF _ relcompI, of _ s' _ t' _])
         (auto simp: \<T>\<^sub>G_funas_gterm_conv lift_root_step_mono trancl_mono)
  qed
next
  case (AComp g1 g2)
  from AComp[simplified] obtain w1 w2 where
    [simp]: "gtt_of_gtt_rel \<F> Rs g1 = Some w1" "gtt_of_gtt_rel \<F> Rs g2 = Some w2"
            "g' = relabel_gtt (AGTT_comp' w1 w2)" by auto
  then have fin_lang: "eval_gtt_rel (fset \<F>) (map fset Rs) g1 = agtt_lang w1"
    "eval_gtt_rel (fset \<F>) (map fset Rs) g2 = agtt_lang w2"
    using AComp by auto
  from fin_lang AGTT_comp'_sound[of w1 w2]
  show ?case by simp
next
  case (GComp g1 g2)
  let ?r = "\<lambda> g. eval_gtt_rel (fset \<F>) (map fset Rs) g"
  have *: "gmctxtex_onp (\<lambda>C. True) (?r g1) = lift_root_step UNIV PAny EParallel (?r g1)"
    "gmctxtex_onp (\<lambda>C. True) (?r g2) = lift_root_step UNIV PAny EParallel (?r g2)"
    by (auto simp: lift_root_step.simps)
  show ?case using GComp(3)
    apply (intro conjI equalityI subrelI; simp add: gmctxt_cl_gmctxtex_onp_conv GComp(1,2) gtt_comp'_alang gcomp_rel_def * flip: lift_root_step.simps; elim conjE disjE exE relcompE)
    subgoal for s t _ _ _ _ _ u
      using image_mono[OF eval_gtt_rel_sig, of snd "fset \<F>" "map fset Rs", unfolded proj_sq]
      apply (subst relcompI[of _ u "eval_gtt_rel _ _ g1", OF _ lift_root_step_sig_transfer[of _ UNIV PAny EParallel "_ g2" "fset \<F>"]])
      apply (force simp add: subsetI \<T>\<^sub>G_equivalent_def)+
      done
    subgoal for s t _ _ _ _ _ u
      using image_mono[OF eval_gtt_rel_sig, of fst "fset \<F>" "map fset Rs", unfolded proj_sq]
      apply (subst relcompI[of _ u _ _ "eval_gtt_rel _ _ g2", OF lift_root_step_sig_transfer'[of _ UNIV PAny EParallel "_ g1" "fset \<F>"]])
      apply (force simp add: subsetI \<T>\<^sub>G_equivalent_def)+
      done
    by (auto intro: subsetD[OF lift_root_step_mono[of "fset \<F>" UNIV]])
}
qed


subsection \<open>Computing RR1 and RR2 relations\<close>

definition "simplify_reg \<A> = (relabel_reg (trim_reg \<A>))"

lemma \<L>_simplify_reg [simp]: "\<L> (simplify_reg \<A>) = \<L> \<A>"
  by (simp add: simplify_reg_def \<L>_trim)

lemma RR1_spec_simplify_reg[simp]:
  "RR1_spec (simplify_reg \<A>) R = RR1_spec \<A> R"
  by (auto simp: RR1_spec_def)
lemma RR2_spec_simplify_reg[simp]:
  "RR2_spec (simplify_reg \<A>) R = RR2_spec \<A> R"
  by (auto simp: RR2_spec_def)
lemma RRn_spec_simplify_reg[simp]:
  "RRn_spec n (simplify_reg \<A>) R = RRn_spec n \<A> R"
  by (auto simp: RRn_spec_def)

lemma RR1_spec_eps_free_reg[simp]:
  "RR1_spec (eps_free_reg \<A>) R = RR1_spec \<A> R"
  by (auto simp: RR1_spec_def \<L>_eps_free)
lemma RR2_spec_eps_free_reg[simp]:
  "RR2_spec (eps_free_reg \<A>) R = RR2_spec \<A> R"
  by (auto simp: RR2_spec_def \<L>_eps_free)
lemma RRn_spec_eps_free_reg[simp]:
  "RRn_spec n (eps_free_reg \<A>) R = RRn_spec n \<A> R"
  by (auto simp: RRn_spec_def \<L>_eps_free)

fun rr1_of_rr1_rel :: "('f \<times> nat) fset \<Rightarrow> ('f :: linorder, 'v) fin_trs list \<Rightarrow> ftrs rr1_rel \<Rightarrow> (nat, 'f) reg option"
and rr2_of_rr2_rel :: "('f \<times> nat) fset \<Rightarrow> ('f, 'v) fin_trs list \<Rightarrow> ftrs rr2_rel \<Rightarrow> (nat, 'f option \<times> 'f option) reg option" where
  "rr1_of_rr1_rel \<F> Rs R1Terms = Some (relabel_reg (term_reg \<F>))"
| "rr1_of_rr1_rel \<F> Rs (R1NF is) = liftO1 (\<lambda>R. (simplify_reg (nf_reg (fst |`| R) \<F>))) (is_to_trs' Rs is)"
| "rr1_of_rr1_rel \<F> Rs (R1Inf r) = liftO1 (\<lambda>R.
    let \<A> = trim_reg R in
    simplify_reg (proj_1_reg (Inf_reg_impl \<A>))
  ) (rr2_of_rr2_rel \<F> Rs r)"
| "rr1_of_rr1_rel \<F> Rs (R1Proj i r) = (case i of 0 \<Rightarrow>
      liftO1 (trim_reg \<circ> proj_1_reg) (rr2_of_rr2_rel \<F> Rs r)
    | _ \<Rightarrow> liftO1 (trim_reg \<circ> proj_2_reg) (rr2_of_rr2_rel \<F> Rs r))"
| "rr1_of_rr1_rel \<F> Rs (R1Union s1 s2) =
    liftO2 (\<lambda> x y. relabel_reg (reg_union x y)) (rr1_of_rr1_rel \<F> Rs s1) (rr1_of_rr1_rel \<F> Rs s2)"
| "rr1_of_rr1_rel \<F> Rs (R1Inter s1 s2) =
    liftO2 (\<lambda> x y. simplify_reg (reg_intersect x y)) (rr1_of_rr1_rel \<F> Rs s1) (rr1_of_rr1_rel \<F> Rs s2)"
| "rr1_of_rr1_rel \<F> Rs (R1Diff s1 s2) = liftO2 (\<lambda> x y. relabel_reg (trim_reg (difference_reg x y))) (rr1_of_rr1_rel \<F> Rs s1) (rr1_of_rr1_rel \<F> Rs s2)"

| "rr2_of_rr2_rel \<F> Rs (R2GTT_Rel g w x) =
    (case w of PRoot \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> reflcl_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g))
      | PNonRoot \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> nhole_ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> nhole_mctxt_reflcl_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> nhole_mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g))
      | PAny \<Rightarrow>
      (case x of ESingle \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> ctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> parallel_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)
        | EStrictParallel \<Rightarrow> liftO1 (simplify_reg \<circ> eps_free_reg \<circ> mctxt_closure_reg (lift_sig_RR2 |`| \<F>) \<circ> GTT_to_RR2_root_reg) (gtt_of_gtt_rel \<F> Rs g)))"
| "rr2_of_rr2_rel \<F> Rs (R2Diag s) =
    liftO1 (\<lambda> x. fmap_funs_reg (\<lambda>f. (Some f, Some f)) x) (rr1_of_rr1_rel \<F> Rs s)"
| "rr2_of_rr2_rel \<F> Rs (R2Prod s1 s2) =
    liftO2 (\<lambda> x y. simplify_reg (pair_automaton_reg x y)) (rr1_of_rr1_rel \<F> Rs s1) (rr1_of_rr1_rel \<F> Rs s2)"
| "rr2_of_rr2_rel \<F> Rs (R2Inv r) = liftO1 (fmap_funs_reg prod.swap) (rr2_of_rr2_rel \<F> Rs r)"
| "rr2_of_rr2_rel \<F> Rs (R2Union r1 r2) =
    liftO2 (\<lambda> x y. relabel_reg (reg_union x y)) (rr2_of_rr2_rel \<F> Rs r1) (rr2_of_rr2_rel \<F> Rs r2)"
| "rr2_of_rr2_rel \<F> Rs (R2Inter r1 r2) =
    liftO2 (\<lambda> x y. simplify_reg (reg_intersect x y)) (rr2_of_rr2_rel \<F> Rs r1) (rr2_of_rr2_rel \<F> Rs r2)"
| "rr2_of_rr2_rel \<F> Rs (R2Diff r1 r2) = liftO2 (\<lambda> x y. simplify_reg (difference_reg x y)) (rr2_of_rr2_rel \<F> Rs r1) (rr2_of_rr2_rel \<F> Rs r2)"
| "rr2_of_rr2_rel \<F> Rs (R2Comp r1 r2) = liftO2 (\<lambda> x y. simplify_reg (rr2_compositon \<F> x y))
     (rr2_of_rr2_rel \<F> Rs r1) (rr2_of_rr2_rel \<F> Rs r2)"


abbreviation lhss where
  "lhss R \<equiv> fst |`| R"

lemma rr12_of_rr12_rel_correct:
  fixes Rs :: "(('f :: linorder, 'v) Term.term \<times> ('f, 'v) Term.term) fset list"
  assumes  "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  shows "\<forall>ta1. rr1_of_rr1_rel \<F> Rs r1 = Some ta1 \<longrightarrow> RR1_spec ta1 (eval_rr1_rel (fset \<F>) (map fset Rs) r1)"
    "\<forall>ta2. rr2_of_rr2_rel \<F> Rs r2 = Some ta2 \<longrightarrow> RR2_spec ta2 (eval_rr2_rel (fset \<F>) (map fset Rs) r2)"
proof (induct r1 and r2)
  note [simp] = bind_eq_Some_conv guard_simps
  let ?F = "fset \<F>" let ?Rs = "map fset Rs"
{
  case R1Terms
  then show ?case using term_automaton[of \<F>]
    by (simp add: \<T>\<^sub>G_equivalent_def)
next
  case (R1NF r)
  consider (a) "\<exists> R. is_to_trs' Rs r = Some R" | (b) "is_to_trs' Rs r = None" by auto
  then show ?case
  proof (cases)
    case a
    from a obtain R where [simp]: "is_to_trs' Rs r = Some R" "is_to_fin_trs Rs r = R"
      by (auto simp: is_to_trs'_def)
    from is_to_trs'_props[OF assms this(1)] have inv: "ffunas_trs R |\<subseteq>| \<F>" "lv_trs (fset R)" .
    from inv have fl: "\<forall> l |\<in>| lhss R. linear_term l"
      by (auto simp: lv_trs_def split!: prod.splits)
    {fix s t assume ass: "(s, t) \<in> grstep (fset R)"
      then obtain C l r \<sigma> where step: "(l, r) |\<in>| R" "term_of_gterm s = (C :: ('f, 'v) ctxt) \<langle>l \<cdot> \<sigma>\<rangle>" "term_of_gterm t = C\<langle>r \<cdot> \<sigma>\<rangle>"
        unfolding grstep_def by (auto simp: dest!: rstep_imp_C_s_r)
      from step ta_nf_lang_sound[of l "lhss R" C \<sigma> \<F>]
      have "s \<notin> \<L> (nf_reg (lhss R) \<F>)" unfolding \<L>_def
        by (metis fimage_eqI fst_conv nf_reg_def reg.sel(1, 2) term_of_gterm_in_ta_lang_conv)}
    note mem = this
    have funas: "funas_trs (fset R) \<subseteq> ?F" using inv(1)
      by (simp add: ffunas_trs.rep_eq less_eq_fset.rep_eq subsetD)
    {fix s assume "s \<in> \<L> (nf_reg (lhss R) \<F>)"
      then have "s \<in> NF (Restr (grstep (fset R)) (\<T>\<^sub>G (fset \<F>))) \<inter> \<T>\<^sub>G (fset \<F>)"
        by (meson IntI NF_I \<T>\<^sub>G_funas_gterm_conv gta_lang_nf_ta_funas inf.cobounded1 mem subset_iff)}
    moreover
    {fix s assume ass: "s \<in> NF (Restr (grstep (fset R)) (\<T>\<^sub>G (fset \<F>))) \<inter> \<T>\<^sub>G (fset \<F>)"
      then have *: "(term_of_gterm s, term_of_gterm t) \<notin> rstep (fset R)" for t using funas
        by (auto simp: funas_trs_def grstep_def NF_iff_no_step \<T>\<^sub>G_funas_gterm_conv)
           (meson R1NF_reps funas rstep.cases)
      then have "s \<in> \<L> (nf_reg (lhss R) \<F>)" using fl ass
        using ta_nf_\<L>_complete[OF fl, of _ \<F>] gta_lang_nf_ta_funas[of _ "lhss R" \<F>]
        by (smt (verit, ccfv_SIG) IntE R1NF_reps \<T>\<^sub>G_sound fimageE funas surjective_pairing)}
    ultimately have "\<L> (nf_reg (lhss R) \<F>) = NF (Restr (grstep (fset R)) (\<T>\<^sub>G (fset \<F>))) \<inter> \<T>\<^sub>G (fset \<F>)"
      by blast
    then show ?thesis using fl(1)
      by (simp add: RR1_spec_def is_to_trs_conv)
  qed auto
next
  case (R1Inf r)
  consider (a) "\<exists> A. rr2_of_rr2_rel \<F> Rs r = Some A" | (b) " rr2_of_rr2_rel \<F> Rs r = None" by auto
  then show ?case
  proof cases
    case a
    have [simp]: "{u. (t, u) \<in> eval_rr2_rel ?F ?Rs r \<and> funas_gterm u \<subseteq> ?F} =
     {u. (t, u) \<in> eval_rr2_rel ?F ?Rs r}" for t
      using eval_rr12_rel_sig(2)[of ?F ?Rs r] by (auto simp: \<T>\<^sub>G_equivalent_def)
    have [simp]: "infinite {u. (t, u) \<in> eval_rr2_rel ?F ?Rs r} \<Longrightarrow> funas_gterm t \<subseteq> ?F" for t
      using eval_rr12_rel_sig(2)[of ?F ?Rs r] not_finite_existsD by (fastforce simp: \<T>\<^sub>G_equivalent_def)
    from a obtain A where [simp]: "rr2_of_rr2_rel \<F> Rs r = Some A" by blast
    from R1Inf this have spec: "RR2_spec A (eval_rr2_rel ?F ?Rs r)" by auto
    then have spec_trim: "RR2_spec (trim_reg A) (eval_rr2_rel ?F ?Rs r)" by auto
    let ?B = "(Inf_reg (trim_reg A) (Q_infty (ta (trim_reg A)) \<F>))"
    have B: "RR2_spec ?B {(s, t) | s t. gpair s t \<in> \<L> ?B}"
      using subset_trans[OF Inf_automata_subseteq[of "trim_reg A" \<F>], of "\<L> A"] spec
      by (auto simp: RR2_spec_def \<L>_trim)
    have *: "\<L> (Inf_reg_impl (trim_reg A)) = \<L> ?B" using spec
      using eval_rr12_rel_sig(2)[of ?F ?Rs r]
      by (intro Inf_reg_impl_sound) (auto simp: \<L>_trim RR2_spec_def \<T>\<^sub>G_equivalent_def)
    then have **: "RR2_spec (Inf_reg_impl (trim_reg A)) {(s, t) | s t. gpair s t \<in> \<L> ?B}" using B
      by (auto simp: RR2_spec_def)
    show ?thesis
      using spec eval_rr12_rel_sig(2)[of ?F ?Rs r]
      using \<L>_Inf_reg[OF spec_trim, of \<F>]
      by (auto simp: \<T>\<^sub>G_equivalent_def * RR1_spec_def \<L>_trim \<L>_proj(1)[OF **]
                     Inf_branching_terms_def fImage_singleton)
         (metis (no_types, lifting) SigmaD1 in_mono mem_Collect_eq not_finite_existsD)
  qed auto
next
  case (R1Proj i r)
  then show ?case
  proof (cases i)
    case [simp]:0 show ?thesis using R1Proj
      using proj_automaton_gta_lang(1)[of "the (rr2_of_rr2_rel \<F> Rs r)" "eval_rr2_rel ?F ?Rs r"]
      by simp
  next
    case (Suc nat) then show ?thesis using R1Proj
      using proj_automaton_gta_lang(2)[of "the (rr2_of_rr2_rel \<F> Rs r)" "eval_rr2_rel ?F ?Rs r"]
      by simp
  qed
next
  case (R1Union s1 s2)
  then show ?case
    by (auto simp: RR1_spec_def \<L>_union)
next
  case (R1Inter s1 s2)
  from R1Inter show ?case
    by (auto simp: \<L>_intersect RR1_spec_def)
next
  case (R1Diff s1 s2)
  then show ?case
    by (auto intro: RR1_difference)
next
  case (R2GTT_Rel g w x)
  note ass = R2GTT_Rel
  consider (a) "\<exists> A. gtt_of_gtt_rel \<F> Rs g = Some A" | (b) "gtt_of_gtt_rel \<F> Rs g = None" by blast
  then show ?case
  proof cases
    case a then obtain A where [simp]: "gtt_of_gtt_rel \<F> Rs g = Some A" by blast
    from gtt_of_gtt_rel_correct[OF assms this]
    have spec [simp]: "eval_gtt_rel ?F ?Rs g = agtt_lang A" by auto
    let ?B = "GTT_to_RR2_root_reg A" note [simp] = GTT_to_RR2_root[of A]
    show ?thesis
    proof (cases w)
      case [simp]: PRoot show ?thesis
      proof (cases x)
        case EParallel
        then show ?thesis using reflcl_automaton[of ?B "agtt_lang A" \<F>]
          by auto
      qed (auto simp: GTT_to_RR2_root)
    next
      case PNonRoot
      then show ?thesis
        using nhole_ctxt_closure_automaton[of ?B "agtt_lang A" \<F>]
        using nhole_mctxt_reflcl_automaton[of ?B "agtt_lang A" \<F>]
        using nhole_mctxt_closure_automaton[of ?B "agtt_lang A" \<F>]
        by (cases x) auto
    next
      case PAny
      then show ?thesis
        using ctxt_closure_automaton[of ?B "agtt_lang A" \<F>]
        using parallel_closure_automaton[of ?B "agtt_lang A" \<F>]
        using mctxt_closure_automaton[of ?B "agtt_lang A" \<F>]
        by (cases x) auto
    qed
  qed (cases w; cases x, auto)
next
  case (R2Diag s)
  then show ?case
    by (auto simp: RR2_spec_def RR1_spec_def fmap_funs_\<L> Id_on_iff
                   fmap_funs_gta_lang map_funs_term_some_gpair)
next
  case (R2Prod s1 s2)
  then show ?case using pair_automaton[of "the (rr1_of_rr1_rel \<F> Rs s1)" _ "the (rr1_of_rr1_rel \<F> Rs s2)"]
    by auto
next
  case (R2Inv r)
  show ?case using R2Inv by (auto simp: swap_RR2_spec)
next
  case (R2Union r1 r2)
  then show ?case using union_automaton
    by (auto simp: RR2_spec_def \<L>_union)
next
  case (R2Inter r1 r2)
  then show ?case
    by (auto simp: \<L>_intersect RR2_spec_def)
next
  case (R2Diff r1 r2)
  then show ?case by (auto intro: RR2_difference)
next
  case (R2Comp r1 r2)
  then show ?case using eval_rr12_rel_sig
    by (auto intro!: rr2_compositon) blast+
}
qed


subsection \<open>Misc\<close>

lemma eval_formula_arity_cong:
  assumes "\<And>i. i < formula_arity f \<Longrightarrow> \<alpha>' i = \<alpha> i"
  shows "eval_formula \<F> Rs \<alpha>' f = eval_formula \<F> Rs \<alpha> f"
proof -
  have [simp]: "j < length fs \<Longrightarrow> i < formula_arity (fs ! j) \<Longrightarrow> i < max_list (map formula_arity fs)" for i j fs
    by (simp add: less_le_trans max_list)
  show ?thesis using assms
  proof (induct f arbitrary: \<alpha> \<alpha>')
    case (FAnd fs)
    show ?case using FAnd(1)[OF nth_mem, of _ \<alpha>' \<alpha>] FAnd(2) by (auto simp: all_set_conv_all_nth)
  next
    case (FOr fs)
    show ?case using FOr(1)[OF nth_mem, of _ \<alpha>' \<alpha>] FOr(2) by (auto simp: ex_set_conv_ex_nth)
  next
    case (FNot f)
    show ?case using FNot(1)[of \<alpha>' \<alpha>] FNot(2) by simp
  next
    case (FExists f)
    show ?case using FExists(1)[of "\<alpha>'\<langle>0 : z\<rangle>" "\<alpha>\<langle>0 : z\<rangle>" for z] FExists(2) by (auto simp: shift_def)
  next
    case (FForall f)
    show ?case using FForall(1)[of "\<alpha>'\<langle>0 : z\<rangle>" "\<alpha>\<langle>0 : z\<rangle>" for z] FForall(2) by (auto simp: shift_def)
  qed simp_all
qed


subsection \<open>Connect semantics to FOL-Fitting\<close>

primrec form_of_formula :: "'trs formula \<Rightarrow> (unit, 'trs rr1_rel + 'trs rr2_rel) form" where
  "form_of_formula (FRR1 r1 x) = Pred (Inl r1) [Var x]"
| "form_of_formula (FRR2 r2 x y) = Pred (Inr r2) [Var x, Var y]"
| "form_of_formula (FAnd fs) = foldr And (map form_of_formula fs) TT"
| "form_of_formula (FOr fs) = foldr Or (map form_of_formula fs) FF"
| "form_of_formula (FNot f) = Neg (form_of_formula f)"
| "form_of_formula (FExists f) = Exists (And (Pred (Inl R1Terms) [Var 0]) (form_of_formula f))"
| "form_of_formula (FForall f) = Forall (Impl (Pred (Inl R1Terms) [Var 0]) (form_of_formula f))"


fun for_eval_rel :: "('f \<times> nat) set \<Rightarrow> ('f, 'v) trs list \<Rightarrow> ftrs rr1_rel + ftrs rr2_rel \<Rightarrow> 'f gterm list \<Rightarrow> bool" where
  "for_eval_rel \<F> Rs (Inl r1) [t] \<longleftrightarrow> t \<in> eval_rr1_rel \<F> Rs r1"
| "for_eval_rel \<F> Rs (Inr r2) [t, u] \<longleftrightarrow> (t, u) \<in> eval_rr2_rel \<F> Rs r2"

lemma eval_formula_conv:
  "eval_formula \<F> Rs \<alpha> f = eval \<alpha> undefined (for_eval_rel \<F> Rs) (form_of_formula f)"
proof (induct f arbitrary: \<alpha>)
  case (FAnd fs) then show ?case
    unfolding eval_formula.simps by (induct fs) auto
next
  case (FOr fs) then show ?case
    unfolding eval_formula.simps by (induct fs) auto
qed auto


subsection \<open>RRn relations and formulas\<close>

lemma shift_rangeI [intro!]:
  "range \<alpha> \<subseteq> T \<Longrightarrow> x \<in> T \<Longrightarrow> range (shift \<alpha> i x) \<subseteq> T"
  by (auto simp: shift_def)

definition formula_relevant where
  "formula_relevant \<F> Rs vs fm \<longleftrightarrow>
     (\<forall>\<alpha> \<alpha>'. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<longrightarrow> range \<alpha>' \<subseteq> \<T>\<^sub>G \<F> \<longrightarrow> map \<alpha> vs = map \<alpha>' vs \<longrightarrow> eval_formula \<F> Rs \<alpha> fm \<longrightarrow> eval_formula \<F> Rs \<alpha>' fm)"

lemma formula_relevant_mono:
  "set vs \<subseteq> set ws \<Longrightarrow> formula_relevant \<F> Rs vs fm \<Longrightarrow> formula_relevant \<F> Rs ws fm"
  unfolding formula_relevant_def
  by (meson map_eq_conv subset_code(1))

lemma formula_relevantD:
  "formula_relevant \<F> Rs vs fm \<Longrightarrow>
   range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<Longrightarrow> range \<alpha>' \<subseteq> \<T>\<^sub>G \<F> \<Longrightarrow> map \<alpha> vs = map \<alpha>' vs \<Longrightarrow>
   eval_formula \<F> Rs \<alpha> fm \<Longrightarrow> eval_formula \<F> Rs \<alpha>' fm"
  unfolding formula_relevant_def
  by blast

lemma trivial_formula_relevant:
  assumes "\<And>\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<Longrightarrow> \<not> eval_formula \<F> Rs \<alpha> fm"
  shows "formula_relevant \<F> Rs vs fm"
  using assms unfolding formula_relevant_def
  by auto

lemma formula_relevant_0_FExists:
  assumes "formula_relevant \<F> Rs [0] fm"
  shows "formula_relevant \<F> Rs [] (FExists fm)"
  unfolding formula_relevant_def
proof (intro allI, intro impI)
  fix \<alpha> \<alpha>' assume ass: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "range (\<alpha>' :: fvar \<Rightarrow> 'a gterm) \<subseteq> \<T>\<^sub>G \<F>"
    "eval_formula \<F> Rs \<alpha> (FExists fm)"
  from ass(3) obtain z where "z \<in> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs (\<alpha>\<langle>0 : z\<rangle>) fm"
    by auto
  then show "eval_formula \<F> Rs \<alpha>' (FExists fm)"
    using ass(1, 2) formula_relevantD[OF assms, of "\<alpha>\<langle>0:z\<rangle>" "\<alpha>'\<langle>0:z\<rangle>"]
    by (auto simp: shift_rangeI intro!: exI[of _ z])
qed

definition formula_spec where
  "formula_spec \<F> Rs vs A fm \<longleftrightarrow> sorted vs \<and> distinct vs \<and>
     formula_relevant \<F> Rs vs fm \<and>
     RRn_spec (length vs) A {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> fm}"

lemma formula_spec_RRn_spec:
  "formula_spec \<F> Rs vs A fm \<Longrightarrow> RRn_spec (length vs) A {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> fm}"
  by (simp add: formula_spec_def)

lemma formula_spec_nt_empty_form_sat:
  "\<not> reg_empty A \<Longrightarrow> formula_spec \<F> Rs vs A fm \<Longrightarrow> \<exists> \<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> fm"
  unfolding formula_spec_def
  by (auto simp: RRn_spec_def \<L>_def)

lemma formula_spec_empty:
  "reg_empty A \<Longrightarrow> formula_spec \<F> Rs vs A fm \<Longrightarrow> range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<Longrightarrow> eval_formula \<F> Rs \<alpha> fm \<longleftrightarrow> False"
  unfolding formula_spec_def
  by (auto simp: RRn_spec_def \<L>_def)

text \<open>In each inference step, we obtain a triple consisting of a formula @{term "fm"}, a list of
  relevant variables @{term "vs"} (typically a sublist of @{term "[0..<formula_arity fm]"}), and
  an RRn automaton @{term "A"}, such that the property @{term "formula_spec \<F> Rs vs A fm"} holds.\<close>

lemma false_formula_spec:
  "sorted vs \<Longrightarrow> distinct vs \<Longrightarrow> formula_spec \<F> Rs vs empty_reg FFalse"
  by (auto simp: formula_spec_def false_RRn_spec FFalse_def formula_relevant_def)

lemma true_formula_spec:
  assumes "vs \<noteq> [] \<or> \<T>\<^sub>G (fset \<F>) \<noteq> {}" "sorted vs" "distinct vs"
  shows "formula_spec (fset \<F>) Rs vs (true_RRn \<F> (length vs)) FTrue"
proof -
  have "{ts. length ts = length vs \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>)} = {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>)}"
  proof (intro equalityI subsetI CollectI, goal_cases LR RL)
    case (LR ts)
    moreover obtain t0 where "funas_gterm t0 \<subseteq> fset \<F>" using LR assms(1) unfolding \<T>\<^sub>G_equivalent_def
      by (cases vs) fastforce+
    ultimately show ?case using `distinct vs`
      apply (intro exI[of _ "\<lambda>t. if t \<in> set vs then ts ! inv_into {0..<length vs} ((!) vs) t else t0"])
      apply (auto intro!: nth_equalityI dest!: inj_on_nth[of vs "{0..<length vs}"] simp: in_set_conv_nth \<T>\<^sub>G_equivalent_def)
      by (metis inv_to_set mem_Collect_eq subsetD) 
  qed fastforce
  then show ?thesis using assms true_RRn_spec[of "length vs" \<F>]
    by (auto simp: formula_spec_def FTrue_def formula_relevant_def \<T>\<^sub>G_equivalent_def)
qed

lemma relabel_formula_spec:
  "formula_spec \<F> Rs vs A fm \<Longrightarrow> formula_spec \<F> Rs vs (relabel_reg A) fm"
  by (simp add: formula_spec_def)

lemma trim_formula_spec:
  "formula_spec \<F> Rs vs A fm \<Longrightarrow> formula_spec \<F> Rs vs (trim_reg A) fm"
  by (simp add: formula_spec_def)

definition fit_permute :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "fit_permute vs vs' vs'' = map (\<lambda>v. if v \<in> set vs then the (mem_idx v vs) else length vs + the (mem_idx v vs'')) vs'"

definition fit_rrn :: "('f \<times> nat) fset \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat, 'f option list) reg \<Rightarrow> (_, 'f option list) reg" where
  "fit_rrn \<F> vs vs' A = (let vs'' = subtract_list_sorted vs' vs in
    fmap_funs_reg (\<lambda>fs. map ((!) fs) (fit_permute vs vs' vs''))
      (fmap_funs_reg (pad_with_Nones (length vs) (length vs'')) (pair_automaton_reg A (true_RRn \<F> (length vs'')))))"

lemma the_mem_idx_simp [simp]:
  "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> the (mem_idx (xs ! i) xs) = i"
  using mem_idx_sound[THEN iffD1, OF nth_mem, of i xs] mem_idx_sound_output[of "xs ! i" xs] distinct_conv_nth
  by fastforce

lemma fit_rrn:
  assumes spec: "formula_spec (fset \<F>) Rs vs A fm" and vs: "sorted vs'" "distinct vs'" "set vs \<subseteq> set vs'"
  shows "formula_spec (fset \<F>) Rs vs' (fit_rrn \<F> vs vs' A) fm"
  using spec unfolding formula_spec_def formula_relevant_def
  apply (elim conjE)
proof (intro conjI vs(1,2) allI, goal_cases rel spec)
  case (rel \<alpha> \<alpha>') show ?case using vs(3)
    by (fastforce intro!: rel(3)[rule_format, of \<alpha> \<alpha>'])
next
  case spec
  define vs'' where "vs'' = subtract_list_sorted vs' vs"
  have evalI: "range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<Longrightarrow> range \<alpha>' \<subseteq> \<T>\<^sub>G (fset \<F>) \<Longrightarrow> map \<alpha> vs = map \<alpha>' vs
   \<Longrightarrow> eval_formula (fset \<F>) Rs \<alpha> fm \<Longrightarrow> eval_formula (fset \<F>) Rs \<alpha>' fm" for \<alpha> \<alpha>'
    using spec(3) by blast
  have [simp]: "set vs' = set vs \<union> set vs''" "set vs'' \<inter> set vs = {}" "set vs \<inter> set vs'' = {}" and d: "distinct vs''"
    using vs spec(1,2) by (auto simp: vs''_def)
  then have [dest]: "v \<in> set vs'' \<Longrightarrow> v \<in> set vs \<Longrightarrow> False" for v by blast
  note * = permute_automaton[OF append_automaton[OF spec(4) true_RRn_spec, of "length vs''"]]
  have [simp]: "distinct vs \<Longrightarrow> i \<in> set vs \<Longrightarrow> vs ! the (mem_idx i vs) = (i :: nat)" for vs i
    by (simp add: mem_idx_sound mem_idx_sound_output)
  have [dest]: "distinct vs \<Longrightarrow> i \<in> set vs \<Longrightarrow> \<not> the (mem_idx i vs) < length vs \<Longrightarrow> False" for i
    by (meson mem_idx_sound2 mem_idx_sound_output option.exhaust_sel)
  show ?case unfolding fit_rrn_def Let_def vs''_def[symmetric] \<T>\<^sub>G_equivalent_def
    apply (rule subst[where P = "\<lambda>l. RRn_spec l _ _", OF _ subst[where P = "\<lambda>ta. RRn_spec _ _ ta", OF _ *]])
    subgoal by (simp add: fit_permute_def)
    subgoal
      apply (intro equalityI subsetI CollectI imageI; elim imageE CollectE exE conjE; unfold \<T>\<^sub>G_equivalent_def)
      subgoal for x fs ts us \<alpha>
        using spec(1, 2) d
        apply (intro exI[of _ "\<lambda>v. if v \<in> set vs'' then us ! the (mem_idx v vs'') else \<alpha> v"])
        apply (auto simp: fit_permute_def nth_append \<T>\<^sub>G_equivalent_def
                    intro!: nth_equalityI evalI[of \<alpha> "\<lambda>v. if v \<in> set vs'' then us ! the (mem_idx v vs'') else \<alpha> v"])
        apply (metis distinct_Ex1 in_mono mem_Collect_eq nth_mem the_mem_idx_simp)
        apply (metis distinct_Ex1 in_mono mem_Collect_eq nth_mem the_mem_idx_simp)
        apply blast
        by (meson \<open>\<And>va. \<lbrakk>va \<in> set vs''; va \<in> set vs\<rbrakk> \<Longrightarrow> False\<close> nth_mem)
      subgoal premises p for xs \<alpha>
        apply (intro rev_image_eqI[of "map \<alpha> (vs @ vs'')"])
        subgoal using p by (force intro!: exI[of _ "map \<alpha> vs", OF exI[of _ "map \<alpha> vs''"]])
        subgoal using p(1)
          by (force intro!: nth_equalityI simp: fit_permute_def comp_def nth_append dest: iffD1[OF mem_idx_sound] mem_idx_sound_output)
        done
      done
    subgoal using vs spec(1,2) unfolding fit_permute_def
      apply (intro equalityI subsetI)
      subgoal by (auto 0 3 dest: iffD1[OF mem_idx_sound] mem_idx_sound_output)
      subgoal for x
        apply (simp add: Compl_eq[symmetric] Diff_eq[symmetric] Un_Diff Diff_triv Int_absorb1)
        apply (simp add: nth_image[symmetric, of "length xs" xs for xs, simplified] image_iff comp_def)
        using image_cong[OF refl arg_cong[OF the_mem_idx_simp]] \<open>distinct vs''\<close>
        by (smt (z3) add_diff_inverse_nat add_less_cancel_left atLeast0LessThan lessThan_iff the_mem_idx_simp)
      done
  done
qed

definition fit_rrns :: "('f \<times> nat) fset \<Rightarrow> (ftrs formula \<times> nat list \<times> (nat, 'f option list) reg) list \<Rightarrow>
  nat list \<times> ((nat, 'f option list) reg) list" where
  "fit_rrns \<F> rrns = (let vs' = fold union_list_sorted (map (fst \<circ> snd) rrns) [] in
    (vs', map (\<lambda>(fm, vs, ta). relabel_reg (trim_reg (fit_rrn \<F> vs vs' ta))) rrns))"

lemma sorted_union_list_sortedI [simp]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (union_list_sorted xs ys)"
  by (induct xs ys rule: union_list_sorted.induct) auto

lemma distinct_union_list_sortedI [simp]:
  "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> distinct (union_list_sorted xs ys)"
  by (induct xs ys rule: union_list_sorted.induct) auto

lemma fit_rrns:
  assumes infs: "\<And>fvA. fvA \<in> set rrns \<Longrightarrow> formula_spec (fset \<F>) Rs (fst (snd fvA)) (snd (snd fvA)) (fst fvA)"
  assumes "(vs', tas') = fit_rrns \<F> rrns"
  shows "length tas' = length rrns" "\<And>i. i < length rrns \<Longrightarrow> formula_spec (fset \<F>) Rs vs' (tas' ! i) (fst (rrns ! i))"
    "distinct vs'" "sorted vs'"
proof (goal_cases)
  have vs': "vs' = fold union_list_sorted (map (fst \<circ> snd) rrns) []" using assms(2) by (simp add: fit_rrns_def Let_def)
  have *: "sorted vs'" "distinct vs'" "\<And>fvA. fvA \<in> set rrns \<Longrightarrow> set (fst (snd fvA)) \<subseteq> set vs'"
    using infs[unfolded formula_spec_def, THEN conjunct2, THEN conjunct1]
      infs[unfolded formula_spec_def, THEN conjunct1]
    unfolding vs' by (induct rrns rule: rev_induct) auto
{
  case 1 then show ?case using assms(2) by (simp add: fit_rrns_def Let_def)
next
  case (2 i)
  have tas': "tas' ! i = relabel_reg (trim_reg (fit_rrn \<F> (fst (snd (rrns ! i))) vs' (snd (snd (rrns ! i)))))"
    using 2 assms(2) by (simp add: fit_rrns_def Let_def split: prod.splits)
  from *(1,2) *(3)[OF nth_mem] show ?case using 2 unfolding tas'
    by (auto intro!: relabel_formula_spec trim_formula_spec fit_rrn 2 assms(1,2))
next
  case 3 show ?case by (rule *)
next
  case 4 show ?case by (rule *)
}
qed


subsection \<open>Building blocks\<close>

definition for_rrn where
  "for_rrn tas = fold (\<lambda>A B. relabel_reg (reg_union A B)) tas (Reg {||} (TA {||} {||}))"

lemma for_rrn:
  assumes "length tas = length fs" "\<And>i. i < length fs \<Longrightarrow> formula_spec \<F> Rs vs (tas ! i) (fs ! i)"
    and vs: "sorted vs" "distinct vs"
  shows "formula_spec \<F> Rs vs (for_rrn tas) (FOr fs)"
  using assms(1,2) unfolding for_rrn_def
proof (induct fs arbitrary: tas rule: rev_induct)
  case Nil then show ?case using vs false_formula_spec[of vs \<F> Rs] by (auto simp: FFalse_def)
next
  case (snoc fm fs)
  have *: "Bex (set [x]) P = P x" for P x by auto
  have [intro!]: "formula_spec \<F> Rs vs (reg_union A B) (FOr (fs @ [fm]))" if
    "formula_spec \<F> Rs vs A fm" "formula_spec \<F> Rs vs B (FOr fs)" for A B using that
    unfolding formula_spec_def
    apply (intro conjI, blast, blast)
    subgoal unfolding formula_relevant_def eval_formula.simps set_append bex_Un * by blast
    apply (elim conjE)
    subgoal premises p by (rule subst[of _ _ "RRn_spec _ _", OF _ union_automaton[OF p(6,8)]]) auto
    done
  show ?case using snoc(1)[of "take (length fs) tas"] snoc(2) snoc(3)[simplified, OF less_SucI] snoc(3)[of "length fs"] vs
    by (cases tas rule: rev_exhaust) (auto simp: min_def nth_append intro!: relabel_formula_spec)
qed

fun fand_rrn where
  "fand_rrn \<F> n [] = true_RRn \<F> n"
| "fand_rrn \<F> n (A # tas) = fold (\<lambda>A B. simplify_reg (reg_intersect A B)) tas A"

lemma fand_rrn:
  assumes "\<T>\<^sub>G (fset \<F>) \<noteq> {}" "length tas = length fs" "\<And>i. i < length fs \<Longrightarrow> formula_spec (fset \<F>) Rs vs (tas ! i) (fs ! i)"
    and vs: "sorted vs" "distinct vs"
  shows "formula_spec (fset \<F>) Rs vs (fand_rrn \<F> (length vs) tas) (FAnd fs)"
proof (cases fs)
  case Nil
  have "tas = []" using assms(2) by (auto simp: Nil)
  then show ?thesis using true_formula_spec[OF _ vs, of \<F> Rs] assms(1) Nil
    by (simp add: FTrue_def)
next
  case (Cons fm fs)
  obtain ta tas' where tas: "tas = ta # tas'" using assms(2) Cons by (cases tas) auto
  show ?thesis using assms(2) assms(3)[of "Suc _"] unfolding tas Cons
    unfolding list.size add_Suc_right add_0_right nat.inject Suc_less_eq nth_Cons_Suc fand_rrn.simps
  proof (induct fs arbitrary: tas' rule: rev_induct)
    case Nil
    have "formula_relevant (fset \<F>) Rs vs (FAnd [fm])" using assms(3)[of 0]
      apply (simp add: tas Cons formula_spec_def)
      unfolding formula_relevant_def eval_formula.simps in_set_simps by blast
    then show ?case using assms(3)[of 0, unfolded tas Cons, simplified] Nil by (simp add: formula_spec_def)
  next
    case (snoc fm' fs)
    have *: "Ball (insert x X) P \<longleftrightarrow> P x \<and> Ball X P" for P x X by auto
    have [intro!]: "formula_spec (fset \<F>) Rs vs (reg_intersect A B) (FAnd (fm # fs @ [fm']))" if
      "formula_spec (fset \<F>) Rs vs A fm'" "formula_spec (fset \<F>) Rs vs B (FAnd (fm # fs))" for A B using that
      unfolding formula_spec_def
      apply (intro conjI, blast, blast)
      subgoal unfolding formula_relevant_def eval_formula.simps set_append set_simps ball_simps ball_Un in_set_simps *
        by blast
      apply (elim conjE)
      subgoal premises p
        by (rule subst[of _ _ "RRn_spec _ _", OF _ intersect_automaton[OF p(6,8)]])
          (auto dest:  p(5)[unfolded formula_relevant_def, rule_format])
      done
    show ?case using snoc(1)[of "take (length fs) tas'"] snoc(2) snoc(3)[simplified, OF less_SucI] snoc(3)[of "length fs"] vs
      by (cases tas' rule: rev_exhaust) (auto simp: min_def nth_append simplify_reg_def intro!: relabel_formula_spec trim_formula_spec)
  qed
qed

subsubsection \<open>IExists inference rule\<close>

lemma lift_fun_gpairD:
  "map_gterm lift_fun s = gpair t u \<Longrightarrow> t = s"
  "map_gterm lift_fun s = gpair t u \<Longrightarrow> u = s"
  by (metis gfst_gpair gsnd_gpair map_funs_term_some_gpair)+

definition upd_bruijn :: "nat list \<Rightarrow> nat list" where
  "upd_bruijn vs = tl (map (\<lambda> x. x - 1) vs)"

lemma upd_bruijn_length[simp]:
  "length (upd_bruijn vs) = length vs - 1"
  by (induct vs) (auto simp: upd_bruijn_def)

lemma pres_sorted_dec:
  "sorted xs \<Longrightarrow> sorted (map (\<lambda>x. x - Suc 0) xs)"
  by (induct xs) auto

lemma upd_bruijn_pres_sorted:
  "sorted xs \<Longrightarrow> sorted (upd_bruijn xs)"
  unfolding upd_bruijn_def
  by (intro sorted_tl) (auto simp: pres_sorted_dec)

lemma pres_distinct_not_0_list_dec:
  "distinct xs \<Longrightarrow> 0 \<notin> set xs \<Longrightarrow> distinct (map (\<lambda>x. x - Suc 0) xs)"
  by (induct xs) (auto, metis Suc_pred neq0_conv)

lemma upd_bruijn_pres_distinct:
  assumes "sorted xs" "distinct xs"
  shows "distinct (upd_bruijn xs)"
proof -
  have "sorted (ys :: nat list) \<Longrightarrow> distinct ys \<Longrightarrow> 0 \<notin> set (tl ys)" for ys
    by (induct ys) auto
  from this[OF assms] show ?thesis using assms(2)
    using pres_distinct_not_0_list_dec[OF distinct_tl, OF assms(2)]
    unfolding upd_bruijn_def
    by (simp add: map_tl)
qed

lemma upd_bruijn_relevant_inv:
  assumes "sorted vs" "distinct vs" "0 \<in> set vs"
    and "\<And> x. x \<in> set (upd_bruijn vs) \<Longrightarrow> \<alpha> x = \<alpha>' x"
  shows "\<And> x. x \<in> set vs \<Longrightarrow> (shift \<alpha> 0 z) x = (shift \<alpha>' 0 z) x"
  using assms unfolding upd_bruijn_def
  by (induct vs) (auto simp add: FOL_Fitting.shift_def)

lemma ExistsI_upd_brujin_0:
  assumes "sorted vs" "distinct vs" "0 \<in> set vs" "formula_relevant \<F> Rs vs fm"
  shows "formula_relevant \<F> Rs (upd_bruijn vs) (FExists fm)"
  unfolding formula_relevant_def
proof (intro allI, intro impI)
  fix \<alpha> \<alpha>' assume ass: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "range (\<alpha>' :: fvar \<Rightarrow> 'a gterm) \<subseteq> \<T>\<^sub>G \<F>"
    "map \<alpha> (upd_bruijn vs) = map \<alpha>' (upd_bruijn vs)" "eval_formula \<F> Rs \<alpha> (FExists fm)"
  from ass(4) obtain z where "z \<in> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs (\<alpha>\<langle>0 : z\<rangle>) fm"
    by auto
  then show "eval_formula \<F> Rs \<alpha>' (FExists fm)"
    using ass(1 - 3) formula_relevantD[OF assms(4), of "\<alpha>\<langle>0:z\<rangle>" "\<alpha>'\<langle>0:z\<rangle>"]
    using upd_bruijn_relevant_inv[OF assms(1 - 3), of "\<alpha>" "\<alpha>'"]
    by (auto simp: shift_rangeI intro!: exI[of _ z])
qed

declare subsetI[rule del]
lemma ExistsI_upd_brujin_no_0:
  assumes "0 \<notin> set vs" and "formula_relevant \<F> Rs vs fm"
  shows "formula_relevant \<F> Rs (map (\<lambda>x. x - Suc 0) vs) (FExists fm)"
  unfolding formula_relevant_def
proof ((intro allI)+ , (intro impI)+, unfold eval_formula.simps)
  fix \<alpha> \<alpha>' assume st: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "range \<alpha>' \<subseteq> \<T>\<^sub>G \<F>"
  "map \<alpha> (map (\<lambda>x. x - Suc 0) vs) = map \<alpha>' (map (\<lambda>x. x - Suc 0) vs)"
  "\<exists> z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (shift \<alpha> 0 z) fm"
  then obtain z where w: "z \<in> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs (shift \<alpha> 0 z) fm" by auto
  from this(1) have "eval_formula \<F> Rs (shift \<alpha>' 0 z) fm"
    using st(1 - 3) assms(1) FOL_Fitting.shift_def
    apply (intro formula_relevantD[OF assms(2) _ _ _ w(2), of "shift \<alpha>' 0 z"])
    by auto (simp add: FOL_Fitting.shift_def)
  then show "\<exists> z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (shift \<alpha>' 0 z) fm" using w(1)
    by blast
qed

definition shift_right where
  "shift_right \<alpha> \<equiv> \<lambda> i. \<alpha> (i + 1)"

lemma shift_right_nt_0:
  "i \<noteq> 0 \<Longrightarrow> \<alpha> i = shift_right \<alpha> (i - Suc 0)"
  unfolding shift_right_def
  by auto

lemma shift_shift_right_id [simp]:
  "shift (shift_right \<alpha>) 0 (\<alpha> 0) = \<alpha>"
  by (auto simp: shift_def shift_right_def)

lemma shift_right_rangeI [intro]:
  "range \<alpha> \<subseteq> T \<Longrightarrow> range (shift_right \<alpha>) \<subseteq> T"
  by (auto simp: shift_right_def intro: subsetI)

lemma eval_formula_shift_right_eval:
  "eval_formula \<F> Rs \<alpha> fm \<Longrightarrow> eval_formula \<F> Rs (shift (shift_right \<alpha>) 0 (\<alpha> 0)) fm"
  "eval_formula \<F> Rs (shift (shift_right \<alpha>) 0 (\<alpha> 0)) fm \<Longrightarrow> eval_formula \<F> Rs \<alpha> fm"
  by (auto)
declare subsetI[intro!]

lemma nt_rel_0_trivial_shift:
  assumes "0 \<notin> set vs"
  shows "{map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> fm} =
         {map (\<lambda>x. \<alpha> (x - Suc 0)) vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> (\<exists>z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (\<alpha>\<langle>0:z\<rangle>) fm)}"
    (is "?Ls = ?Rs")
proof
  {fix \<alpha> assume ass: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs \<alpha> fm" 
    then have "map \<alpha> vs = map (\<lambda>x. (shift_right \<alpha>) (x - Suc 0)) vs"
      "range (shift_right \<alpha>) \<subseteq> \<T>\<^sub>G \<F>" "\<alpha> 0 \<in>\<T>\<^sub>G \<F>" "eval_formula \<F> Rs (shift (shift_right \<alpha>) 0 (\<alpha> 0)) fm"
      using shift_right_rangeI[OF ass(1)] assms
      by (auto intro: eval_formula_shift_right_eval(1), metis shift_right_nt_0)}
  then show "?Ls \<subseteq> ?Rs"
    by blast
next
  show "?Rs \<subseteq> ?Ls"
    by auto (metis FOL_Fitting.shift_def One_nat_def assms not_less0 shift_rangeI)
qed

lemma relevant_vars_upd_bruijn_tl:
  assumes "sorted vs" "distinct vs"
  shows "map (shift_right \<alpha>) (upd_bruijn vs) = tl (map \<alpha> vs)" using assms
proof (induct vs)
  case (Cons a vs) then show ?case
    using le_antisym
    by (auto simp: upd_bruijn_def shift_right_def)
       (metis One_nat_def Suc_eq_plus1 le_0_eq shift_right_def shift_right_nt_0)
qed (auto simp: upd_bruijn_def)

lemma drop_upd_bruijn_set:
  assumes "sorted vs" "distinct vs"
  shows "drop 1 ` {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> eval_formula \<F> Rs \<alpha> fm} =
         {map \<alpha> (upd_bruijn vs) |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> (\<exists>z\<in>\<T>\<^sub>G \<F>. eval_formula \<F> Rs (\<alpha>\<langle>0:z\<rangle>) fm)}"
    (is "?Ls = ?Rs")
proof
  {fix \<alpha> assume ass: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs \<alpha> fm" 
    then have "drop 1 (map \<alpha> vs) = map (shift_right \<alpha>) (upd_bruijn vs)"
      "range (shift_right \<alpha>) \<subseteq> \<T>\<^sub>G \<F>" "\<alpha> 0 \<in>\<T>\<^sub>G \<F>" "eval_formula \<F> Rs (shift (shift_right \<alpha>) 0 (\<alpha> 0)) fm"
      using shift_right_rangeI[OF ass(1)]
      by (auto simp: tl_drop_conv relevant_vars_upd_bruijn_tl[OF assms(1, 2)])}
  then show "?Ls \<subseteq> ?Rs"
    by blast
next
  have [dest]: "0 \<in> set (tl vs) \<Longrightarrow> False" using assms(1, 2)
    by (cases vs) auto
  {fix \<alpha> z assume ass: "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "z \<in> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs (\<alpha>\<langle>0:z\<rangle>) fm"
    then have "map \<alpha> (upd_bruijn vs) = tl (map (\<alpha>\<langle>0:z\<rangle>) vs)"
      "range (\<alpha>\<langle>0:z\<rangle>) \<subseteq> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs (\<alpha>\<langle>0:z\<rangle>) fm"
      using shift_rangeI[OF ass(1)]
      by (auto simp: upd_bruijn_def shift_def simp flip: map_tl)}
  then show "?Rs \<subseteq> ?Ls"
    by (auto simp: tl_drop_conv image_def) blast
qed


lemma closed_sat_form_env_dom:
  assumes "formula_relevant \<F> Rs [] (FExists fm)" "range \<alpha> \<subseteq> \<T>\<^sub>G \<F>" "eval_formula \<F> Rs \<alpha> fm"
  shows "{[\<alpha> 0] |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G \<F> \<and> (\<exists> z \<in> \<T>\<^sub>G \<F>. eval_formula \<F> Rs (\<alpha>\<langle>0:z\<rangle>) fm)} = {[t] | t. t \<in> \<T>\<^sub>G \<F>}"
  using formula_relevantD[OF assms(1)] assms(2-)
  apply auto
  apply blast
  by (smt rangeI shift_eq shift_rangeI shift_right_rangeI shift_shift_right_id subsetD)

(* MOVE *)
lemma find_append:
  "find P (xs @ ys) = (if find P xs \<noteq> None then find P xs else find P ys)"
  by (induct xs arbitrary: ys) (auto split!: if_splits)

subsection \<open>Checking inferences\<close>

derive linorder ext_step pos_step gtt_rel rr1_rel rr2_rel ftrs
derive compare ext_step pos_step gtt_rel rr1_rel rr2_rel ftrs

fun check_inference :: "(('f \<times> nat) fset \<Rightarrow> ('f, 'v) fin_trs list \<Rightarrow> ftrs rr1_rel \<Rightarrow> (nat, 'f) reg option)
  \<Rightarrow> (('f \<times> nat) fset \<Rightarrow> ('f, 'v) fin_trs list \<Rightarrow> ftrs rr2_rel \<Rightarrow> (nat, 'f option \<times> 'f option) reg option)
  \<Rightarrow> ('f \<times> nat) fset \<Rightarrow> ('f :: compare, 'v) fin_trs list
  \<Rightarrow> (ftrs formula \<times> nat list \<times> (nat, 'f option list) reg) list
  \<Rightarrow> (nat \<times> ftrs inference \<times> ftrs formula \<times> info list)
  \<Rightarrow> (ftrs formula \<times> nat list \<times> (nat, 'f option list) reg) option" where
  "check_inference rr1c rr2c \<F> Rs infs (l, step, fm, is) = do {
    guard (l = length infs);
    case step of
      IRR1 s x \<Rightarrow> do {
        guard (fm = FRR1 s x);
        liftO1 (\<lambda>ta. (FRR1 s x, [x], fmap_funs_reg (\<lambda>f. [Some f]) ta)) (rr1c \<F> Rs s)
    }
    | IRR2 r x y \<Rightarrow> do {
        guard (fm = FRR2 r x y);
        case compare x y of
          Lt \<Rightarrow> liftO1 (\<lambda>ta. (FRR2 r x y, [x, y], fmap_funs_reg (\<lambda>(f, g). [f, g]) ta)) (rr2c \<F> Rs r)
        | Eq \<Rightarrow> liftO1 (\<lambda>ta. (FRR2 r x y, [x], fmap_funs_reg (\<lambda>f. [Some f]) ta))
          (liftO1 (simplify_reg \<circ> proj_1_reg)
          (liftO2 (\<lambda> t1 t2. simplify_reg (reg_intersect t1 t2)) (rr2c \<F> Rs r) (rr2c \<F> Rs (R2Diag R1Terms))))
        | Gt \<Rightarrow> liftO1 (\<lambda>ta. (FRR2 r x y, [y, x], fmap_funs_reg (\<lambda>(f, g). [g, f]) ta)) (rr2c \<F> Rs r)
    }
    | IAnd ls \<Rightarrow> do {
        guard (\<forall>l' \<in> set ls. l' < l);
        guard (fm = FAnd (map (\<lambda>l'. fst (infs ! l')) ls));
        let (vs', tas') = fit_rrns \<F> (map ((!) infs) ls) in
        Some (fm, vs', fand_rrn \<F> (length vs') tas')
    }
    | IOr ls \<Rightarrow> do {
        guard (\<forall>l' \<in> set ls. l' < l);
        guard (fm = FOr (map (\<lambda>l'. fst (infs ! l')) ls));
        let (vs', tas') = fit_rrns \<F> (map ((!) infs) ls) in
        Some (fm, vs', for_rrn tas')
    }
    | INot l' \<Rightarrow> do {
        guard (l' < l);
        guard (fm = FNot (fst (infs ! l')));
        let (vs', tas') = snd (infs ! l');
        Some (fm, vs', simplify_reg (difference_reg (true_RRn \<F> (length vs')) tas'))
    }
    | IExists l' \<Rightarrow> do {
        guard (l' < l);
        guard (fm = FExists (fst (infs ! l')));
        let (vs', tas') = snd (infs ! l');
        if length vs' = 0 then Some (fm, [], tas') else
          if reg_empty tas' then Some (fm, [], empty_reg)
          else if 0 \<notin> set vs' then Some (fm, map (\<lambda> x. x - 1) vs', tas')
          else if 1 = length vs' then Some (fm, [], true_RRn \<F> 0)
          else Some (fm, upd_bruijn vs', rrn_drop_fst tas')
    }
    | IRename l' vs \<Rightarrow> guard (l' < l) \<then> None
    | INNFPlus l' \<Rightarrow> do {
        guard (l' < l);
        let fm' = fst (infs ! l');
        guard (ord_form_list_aci (nnf_to_list_aci (nnf (form_of_formula fm'))) = ord_form_list_aci (nnf_to_list_aci (nnf (form_of_formula fm))));
        Some (fm, snd (infs ! l'))
    }
    | IRepl eq pos l' \<Rightarrow> guard (l' < l) \<then> None
    }"

lemma RRn_spec_true_RRn:
  "RRn_spec (Suc 0) (true_RRn \<F> (Suc 0)) {[t] |t. t \<in> \<T>\<^sub>G (fset \<F>)}"
  apply (auto simp: RRn_spec_def \<T>\<^sub>G_equivalent_def fmap_funs_\<L>
      image_def term_automaton[of \<F>, unfolded RR1_spec_def])
   apply (metis gencode_singleton)+
  done

lemma check_inference_correct:
  assumes sig: "\<T>\<^sub>G (fset \<F>) \<noteq> {}" and Rs: "\<forall>R \<in> set Rs. lv_trs (fset R) \<and> ffunas_trs R |\<subseteq>| \<F>"
  assumes infs: "\<And>fvA. fvA \<in> set infs \<Longrightarrow> formula_spec (fset \<F>) (map fset Rs) (fst (snd fvA)) (snd (snd fvA)) (fst fvA)"
  assumes inf: "check_inference rr1c rr2c \<F> Rs infs (l, step, fm, is) = Some (fm', vs, A')"
  assumes rr1: "\<And>r1. \<forall>ta1. rr1c \<F> Rs r1 = Some ta1 \<longrightarrow> RR1_spec ta1 (eval_rr1_rel (fset \<F>) (map fset Rs) r1)"
  assumes rr2: "\<And>r2. \<forall>ta2. rr2c \<F> Rs r2 = Some ta2 \<longrightarrow> RR2_spec ta2 (eval_rr2_rel (fset \<F>) (map fset Rs) r2)"
  shows "l = length infs \<and> fm = fm' \<and> formula_spec (fset \<F>) (map fset Rs) vs A' fm'"
  using inf
proof (induct step)
  note [simp] = bind_eq_Some_conv guard_simps
  let ?F = "fset \<F>" let ?Rs = "map fset Rs"
{
  case (IRR1 s x)
  then show ?case
    using rr1[rule_format, of s]
    subsetD[OF eval_rr12_rel_sig(1), of _ ?F ?Rs s]
    by (force simp: formula_spec_def formula_relevant_def RR1_spec_def \<T>\<^sub>G_equivalent_def
      intro!: RR1_to_RRn_spec[of _ "(\<lambda>\<alpha>. \<alpha> x) ` Collect P" for P, unfolded image_comp, unfolded image_Collect comp_def One_nat_def])
next
  case (IRR2 r x y)
  then show ?case using rr2[rule_format, of r]
    subsetD[OF eval_rr12_rel_sig(2), of _ ?F ?Rs r]
    two_comparisons_into_compare(1)[of x y "x = y" "x < y" "x > y"]
  proof (induct "compare x y")
    note [intro!] = RR1_to_RRn_spec[of _ "(\<lambda>\<alpha>. \<alpha> y) ` Collect P" for P, unfolded image_comp,
      unfolded image_Collect comp_def One_nat_def prod.simps]
    case Eq
    then obtain A where w[simp]: "rr2c \<F> Rs r = Some A" by auto
    from Eq obtain B where [simp]:"rr2c \<F> Rs (R2Diag R1Terms) = Some B" by auto
    let ?B = "reg_intersect A B"
    from Eq(3)[OF w] have "RR2_spec ?B (eval_rr2_rel ?F ?Rs r \<inter> Restr Id (\<T>\<^sub>G ?F))"
      using rr2[rule_format, of "R2Diag R1Terms" B]
      by (auto simp add: \<L>_intersect RR2_spec_def dest: lift_fun_gpairD)
    then have "RR2_spec (relabel_reg (trim_reg ?B)) (eval_rr2_rel ?F ?Rs r \<inter> Restr Id (\<T>\<^sub>G ?F))" by simp
    from proj_1(1)[OF this]
    have "RR1_spec (proj_1_reg (relabel_reg (trim_reg ?B))) {\<alpha> y |\<alpha>. range \<alpha> \<subseteq> gterms ?F \<and> (\<alpha> y, \<alpha> y) \<in> eval_rr2_rel ?F ?Rs r}"
      apply (auto simp: RR1_spec_def \<T>\<^sub>G_equivalent_def image_iff)
      by (metis Eq.prems(3) IdI IntI \<T>\<^sub>G_equivalent_def fst_conv) 
    then show ?thesis using Eq
      by (auto simp: formula_spec_def formula_relevant_def liftO1_def \<T>\<^sub>G_equivalent_def simplify_reg_def RR2_spec_def
      split: if_splits intro!: exI[of _ "\<lambda>z. if z = x then _ else _"])
  next
    note [intro!] = RR2_to_RRn_spec[of _ "(\<lambda>\<alpha>. (\<alpha> x, \<alpha> y)) ` Collect P" for P, unfolded image_comp,
      unfolded image_Collect comp_def numeral_2_eq_2 prod.simps]
    case Lt then show ?thesis by (fastforce simp: formula_spec_def formula_relevant_def RR2_spec_def \<T>\<^sub>G_equivalent_def
      split: if_splits intro!: exI[of _ "\<lambda>z. if z = x then _ else _"])
  next
    note [intro!] = RR2_to_RRn_spec[of _ "prod.swap ` (\<lambda>\<alpha>. (\<alpha> x, \<alpha> y)) ` Collect P" for P, OF swap_RR2_spec,
      unfolded image_comp, unfolded image_Collect comp_def numeral_2_eq_2 prod.simps fmap_funs_reg_comp case_swap]
    case Gt then show ?thesis
      by (fastforce simp: formula_spec_def formula_relevant_def RR2_spec_def \<T>\<^sub>G_equivalent_def
        split: if_splits intro!: exI[of _ "\<lambda>z. if z = x then _ else _"])
  qed
next
  case (IAnd ls)
  have [simp]: "(fm, vs, ta) \<in> (!) infs ` set ls \<Longrightarrow> formula_spec ?F ?Rs vs ta fm" for fm vs ta
    using infs IAnd by auto
  show ?case using IAnd fit_rrns[OF assms(3), of "map ((!) infs) ls", OF _ prod.collapse]
    by (force split: prod.splits intro!: fand_rrn[OF assms(1)])
next
  case (IOr ls)
  have [simp]: "(fm, vs, ta) \<in> (!) infs ` set ls \<Longrightarrow> formula_spec ?F ?Rs vs ta fm" for fm vs ta
    using infs IOr by auto
  show ?case using IOr fit_rrns[OF assms(3), of "map ((!) infs) ls", OF _ prod.collapse]
    by (force split: prod.splits intro!: for_rrn)
next
  case (INot l')
  obtain fm vs' ta where [simp]: "infs ! l' = (fm, vs', ta)" by (cases "infs ! l'") auto
  then have spec: "formula_spec ?F ?Rs vs ta fm" using infs[OF nth_mem, of l'] INot
    by auto
  have rel: "formula_relevant (fset \<F>) (map fset Rs) vs (FNot fm)" using spec
    unfolding formula_spec_def formula_relevant_def
    by (metis (no_types, lifting) eval_formula.simps(5))
  have vs: "sorted vs" "distinct vs" using spec by (auto simp: formula_spec_def)
  {fix xs assume ass: "\<forall>\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<longrightarrow> xs = map \<alpha> vs \<longrightarrow> \<not> eval_formula (fset \<F>) (map fset Rs) \<alpha> fm"
    "length xs = length vs" "set xs \<subseteq> \<T>\<^sub>G (fset \<F>)"
    from sig obtain s where mem: "s \<in> \<T>\<^sub>G (fset \<F>)" by blast
    let ?g = "\<lambda> i. find (\<lambda> p. fst p = i) (zip vs [0 ..< length vs])"
    let ?f = "\<lambda> i. if ?g i = None then s else xs ! snd (the (?g i))"
    from vs(1) have *: "sorted (zip vs [0 ..< length vs])"
      by (induct vs rule: rev_induct) (auto simp: sorted_append elim!: in_set_zipE intro!: sorted_append_bigger)
    have "i < length vs \<Longrightarrow> ?g (vs ! i) = Some (vs ! i, i)" for i using vs(2)
      by (induct vs rule: rev_induct) (auto simp: nth_append find_append find_Some_iff nth_eq_iff_index_eq split!: if_splits)
    then have "map ?f vs = xs" using vs(2) ass(2)
      by (intro nth_equalityI) (auto simp: find_None_iff set_zip)
    moreover have "range ?f \<subseteq> \<T>\<^sub>G (fset \<F>)" using ass(2, 3) mem
      using find_SomeD(2) set_zip_rightD by auto fastforce
    ultimately have "\<exists>\<alpha>. xs = map \<alpha> vs \<and> range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<and> \<not> eval_formula (fset \<F>) (map fset Rs) \<alpha> fm" using ass(1)
      by (intro exI[of _ ?f]) auto}
  then have *: "{ts. length ts = length vs \<and> set ts \<subseteq> \<T>\<^sub>G (fset \<F>)} -
    {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<and> eval_formula (fset \<F>) (map fset Rs) \<alpha> fm} =
    {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<and> \<not> eval_formula (fset \<F>) (map fset Rs) \<alpha> fm}"
    apply auto
    apply force
    using formula_relevantD[OF rel] unfolding eval_formula.simps
    by (meson map_ext)
  have "RRn_spec (length vs) (difference_reg (true_RRn \<F> (length vs)) ta)
     {map \<alpha> vs |\<alpha>. range \<alpha> \<subseteq> \<T>\<^sub>G (fset \<F>) \<and> \<not> eval_formula (fset \<F>) (map fset Rs) \<alpha> fm}"
    using RRn_difference[OF true_RRn_spec[of "length vs" \<F>] formula_spec_RRn_spec[OF spec]]
    unfolding * by simp
  then show ?case using INot spec rel
    by (auto split: prod.splits simp: formula_spec_def)
next
  case (IExists l')
  obtain fm vs ta where [simp]: "infs ! l' = (fm, vs, ta)" by (cases "infs ! l'") auto
  then have spec: "formula_spec ?F ?Rs vs ta fm" using infs[OF nth_mem, of l'] IExists
    by auto
  show ?case
  proof (cases "length vs = 0")
    case True
    then show ?thesis using IExists spec
      apply (auto simp: formula_spec_def)
      subgoal apply (auto simp: formula_relevant_def)
        apply (meson shift_rangeI)
        done
      subgoal apply (auto simp: RRn_spec_def image_iff)
        apply (meson eval_formula_shift_right_eval(1) rangeI shift_right_rangeI subsetD)
        apply (meson shift_rangeI)
        done
      done
  next
    case False note len = this
    then have *[simp]: "vs \<noteq> []" by (cases vs) auto 
    show ?thesis
    proof (cases "reg_empty ta")
      case True
      then show ?thesis using IExists spec formula_spec_empty[OF _ spec]
        by (auto simp: \<T>\<^sub>G_equivalent_def comp_def formula_spec_def
                        shift_rangeI RRn_spec_def image_iff \<L>_epmty
               intro!: trivial_formula_relevant)
    next
      case False
      then have nt_empty [simp]: "\<L> ta \<noteq> {}" by auto
      show ?thesis
      proof (cases "0 \<notin> set vs")
        case True
        then have ta: "ta = A'" using spec IExists
          by (auto simp: formula_spec_def)
        from True have relv: "formula_relevant ?F ?Rs (map (\<lambda>x. x - Suc 0) vs) (FExists fm)"
          using spec IExists
          by (intro ExistsI_upd_brujin_no_0) (auto simp: formula_spec_def)
        then show ?thesis using True spec IExists nt_rel_0_trivial_shift[OF True, of ?F ?Rs ]
          by (auto simp: formula_spec_def \<T>\<^sub>G_equivalent_def comp_def
                   elim!: formula_relevantD
                   intro!: pres_distinct_not_0_list_dec pres_sorted_dec)
      next
        case False
        then have rel_0: "0 \<in> set vs" by simp
        show ?thesis
        proof (cases "1 = length vs")
          case True
          then have [simp]: "vs = [0]" using rel_0 by (induct vs) auto
          {fix t assume "0 |\<in>| ta_der (TA {|[] [] \<rightarrow> 0|} {||}) (term_of_gterm t)"
            then have "t = GFun [] []" by (cases t) auto}
          then have [simp]: "\<L> (Reg {|0|} (TA {|TA_rule [] [] 0|} {||})) = {GFun [] []}"
            by (auto simp: \<L>_def gta_der_def gta_lang_def)
          have [simp]: "GFun [] [] = gencode []"
            by (auto simp: gencode_def gunions_def)
          show ?thesis using IExists spec nt_empty
            by (auto simp: formula_spec_def RRn_spec_true_RRn RRn_spec_def formula_relevant_0_FExists image_iff)
               (meson eval_formula_shift_right_eval(1) in_mono rangeI shift_right_rangeI)
        next
          case False
          from False show ?thesis using spec IExists rel_0 nt_empty
            using rrn_drop_fst_lang[OF formula_spec_RRn_spec[OF spec]]
            by (auto simp: formula_spec_def Suc_lessI simp flip: drop_upd_bruijn_set
                     split: prod.splits
                     intro: upd_bruijn_pres_sorted upd_bruijn_pres_distinct ExistsI_upd_brujin_0)
        qed
      qed
    qed
  qed
next
  case (IRename l' vs)
  then show ?case by simp
next
  case (INNFPlus l')
  show ?case using infs[OF nth_mem, of l'] INNFPlus
    apply (auto simp: formula_spec_def formula_relevant_def eval_formula_conv)
    apply (simp_all only: check_equivalence_by_nnf_sortedlist_aci[of "form_of_formula (fst (infs ! l'))" "form_of_formula fm"])
    done
next
  case (IRepl eq pos l')
  then show ?case by simp
}
qed


end