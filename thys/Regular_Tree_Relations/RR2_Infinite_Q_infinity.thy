theory RR2_Infinite_Q_infinity
  imports RR2_Infinite
begin

(* This section constructs an executable membership check for Q infinity,
  since Inf_automata is already executable (for all sets Q where checking membership is executable)
*)

lemma if_cong':
  "b = c \<Longrightarrow> x = u \<Longrightarrow> y = v \<Longrightarrow> (if b then x else y) = (if c then u else v)"
  by auto

(* The reachable terms where eps transitions can only occur after the rule *)
fun ta_der_strict :: "('q,'f) ta \<Rightarrow> ('f,'q) term \<Rightarrow> 'q fset" where
  "ta_der_strict \<A> (Var q) = {|q|}"
| "ta_der_strict \<A> (Fun f ts) = {| q' | q' q qs. TA_rule f qs q |\<in>| rules \<A> \<and> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|) \<and> 
    length qs = length ts \<and> (\<forall> i < length ts. qs ! i |\<in>| ta_der_strict \<A> (ts ! i))|}"

lemma ta_der_strict_Var:
  "q |\<in>| ta_der_strict \<A> (Var x) \<longleftrightarrow> x = q"
  unfolding ta_der.simps by auto

lemma ta_der_strict_Fun:
  "q |\<in>| ta_der_strict \<A> (Fun f ts) \<longleftrightarrow> (\<exists> ps p. TA_rule f ps p |\<in>| (rules \<A>) \<and>
      (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|) \<and> length ps = length ts \<and> 
      (\<forall> i < length ts. ps ! i |\<in>| ta_der_strict \<A> (ts ! i)))" (is "?Ls \<longleftrightarrow> ?Rs")
  unfolding ta_der_strict.simps
  by (intro iffI fCollect_memberI finite_Collect_less_eq[OF _ finite_eps[of \<A>]]) auto

declare ta_der_strict.simps[simp del]
lemmas ta_der_strict_simps [simp] = ta_der_strict_Var ta_der_strict_Fun

lemma ta_der_strict_sub_ta_der:
  "ta_der_strict \<A> t |\<subseteq>| ta_der \<A> t"
proof (induct t)
  case (Fun f ts)
  then show ?case
    by auto (metis fsubsetD nth_mem)+
qed auto
  
lemma ta_der_strict_ta_der_eq_on_ground:
  assumes"ground t"
  shows "ta_der \<A> t = ta_der_strict \<A> t"
proof
  {fix q assume "q |\<in>| ta_der \<A> t" then have "q |\<in>| ta_der_strict \<A> t" using assms
    proof (induct t arbitrary: q)
      case (Fun f ts)
      then show ?case apply auto
        using nth_mem by blast+
    qed auto}
  then show "ta_der \<A> t |\<subseteq>| ta_der_strict \<A> t"
    by auto
next
  show "ta_der_strict \<A> t |\<subseteq>| ta_der \<A> t" using ta_der_strict_sub_ta_der .
qed

lemma ta_der_to_ta_strict:
  assumes "q |\<in>| ta_der A C\<langle>Var p\<rangle>" and "ground_ctxt C"
  shows "\<exists> q'. (p = q' \<or> (p, q') |\<in>| (eps A)|\<^sup>+|) \<and> q |\<in>| ta_der_strict A C\<langle>Var q'\<rangle>"
  using assms
proof (induct C arbitrary: q p)
  case (More f ss C ts)
  from More(2) obtain qs q' where
    r: "TA_rule f qs q' |\<in>| rules A" "length qs = Suc (length ss + length ts)" "q' = q \<or> (q', q) |\<in>| (eps A)|\<^sup>+|" and
    rec: "\<forall> i < length qs. qs ! i |\<in>| ta_der A ((ss @ C\<langle>Var p\<rangle> # ts) ! i)"
    by auto
  from More(1)[of "qs ! length ss" p] More(3) rec r(2) obtain q'' where
    mid: "(p = q'' \<or> (p, q'') |\<in>| (eps A)|\<^sup>+|) \<and> qs ! length ss |\<in>| ta_der_strict A C\<langle>Var q''\<rangle>"
    by auto (metis length_map less_add_Suc1 nth_append_length)
  then have "\<forall> i < length qs. qs ! i |\<in>| ta_der_strict A ((ss @ C\<langle>Var q''\<rangle> # ts) ! i)"
    using rec r(2) More(3)
    using ta_der_strict_ta_der_eq_on_ground[of _ A]
    by (auto simp: nth_append_Cons all_Suc_conv split:if_splits cong: if_cong')
  then show ?case using rec r conjunct1[OF mid]
    by (rule_tac x = q'' in exI, auto intro!: exI[of _ q'] exI[of _ qs])
qed auto

fun root_ctxt where
  "root_ctxt (More f ss C ts) = f"
| "root_ctxt \<box> = undefined"

lemma root_to_root_ctxt [simp]:
  assumes "C \<noteq> \<box>"
  shows "fst (the (root C\<langle>t\<rangle>)) \<longleftrightarrow> root_ctxt C"
  using assms by (cases C) auto


(* Q_inf section *)

inductive_set Q_inf for \<A> where
  trans: "(p, q) \<in> Q_inf \<A> \<Longrightarrow> (q, r) \<in> Q_inf \<A> \<Longrightarrow> (p, r) \<in> Q_inf \<A>"
| rule: "(None, Some f) qs \<rightarrow> q |\<in>| rules \<A> \<Longrightarrow> i < length qs \<Longrightarrow> (qs ! i, q) \<in> Q_inf \<A>"
| eps: "(p, q) \<in> Q_inf \<A> \<Longrightarrow> (q, r) |\<in>| eps \<A> \<Longrightarrow> (p, r) \<in> Q_inf \<A>"

abbreviation "Q_inf_e \<A> \<equiv> {q | p q. (p, p) \<in> Q_inf \<A> \<and> (p, q) \<in> Q_inf \<A>}"

lemma Q_inf_states_ta_states:
  assumes "(p, q) \<in> Q_inf \<A>"
  shows "p |\<in>| \<Q> \<A>" "q |\<in>| \<Q> \<A>"
  using assms by (induct) (auto simp: rule_statesD eps_statesD)

lemma Q_inf_finite:
  "finite (Q_inf \<A>)" "finite (Q_inf_e \<A>)"
proof -
  have *: "Q_inf \<A> \<subseteq> fset (\<Q> \<A> |\<times>| \<Q> \<A>)" "Q_inf_e \<A> \<subseteq> fset (\<Q> \<A>)"
    by (auto simp add: Q_inf_states_ta_states(1, 2) subrelI)
  show "finite (Q_inf \<A>)"
    by (intro finite_subset[OF *(1)]) simp
  show "finite (Q_inf_e \<A>)"
    by (intro finite_subset[OF *(2)]) simp
qed

context
includes fset.lifting
begin
lift_definition fQ_inf :: "('a, 'b option \<times> 'c option) ta \<Rightarrow> ('a \<times> 'a) fset" is Q_inf
  by (simp add: Q_inf_finite(1))
lift_definition fQ_inf_e :: "('a, 'b option \<times> 'c option) ta \<Rightarrow> 'a fset" is Q_inf_e
  using Q_inf_finite(2) .
end


lemma Q_inf_ta_eps_Q_inf:
  assumes "(p, q) \<in> Q_inf \<A>" and "(q, q') |\<in>| (eps \<A>)|\<^sup>+|"
  shows "(p, q') \<in> Q_inf \<A>" using assms(2, 1)
  by (induct rule: ftrancl_induct) (auto simp add: Q_inf.eps)

lemma lhs_state_rule:
  assumes "(p, q) \<in> Q_inf \<A>"
  shows "\<exists> f qs r. (None, Some f) qs \<rightarrow> r |\<in>| rules \<A> \<and> p |\<in>| fset_of_list qs"
  using assms by induct (force intro: nth_mem)+

lemma Q_inf_reach_state_rule:
  assumes "(p, q) \<in> Q_inf \<A>" and "\<Q> \<A> |\<subseteq>| ta_reachable \<A>"
  shows "\<exists> ss ts f C. q |\<in>| ta_der \<A> (More (None, Some f) ss C ts)\<langle>Var p\<rangle> \<and> ground_ctxt (More (None, Some f) ss C ts)"
    (is "\<exists> ss ts f C. ?P ss ts f C q p")
  using assms
proof (induct)
  case (trans p q r)
  then obtain f1 f2 ss1 ts1 ss2 ts2 C1 C2 where
    C: "?P ss1 ts1 f1 C1 q p" "?P ss2 ts2 f2 C2 r q" by blast
  then show ?case
    apply (rule_tac x = "ss2" in exI, rule_tac x = "ts2" in exI, rule_tac x = "f2" in exI,
        rule_tac x = "C2 \<circ>\<^sub>c (More (None, Some f1) ss1 C1 ts1)" in exI)
    apply (auto simp del: ctxt_apply_term.simps)
    apply (metis Subterm_and_Context.ctxt_ctxt_compose ctxt_compose.simps(2) ta_der_ctxt)
    done
next
  case (rule f qs q i)
  have "\<forall> i < length qs. \<exists> t. qs ! i |\<in>| ta_der \<A> t \<and> ground t"
    using rule(1, 2) fset_mp[OF rule(3), of "qs ! i" for i]
    by auto (meson fnth_mem rule_statesD(4) ta_reachableE) 
  then obtain ts where wit: "length ts = length qs"
    "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (ts ! i) \<and> ground (ts ! i)"
    using Ex_list_of_length_P[of "length qs" "\<lambda> x i. qs ! i |\<in>| ta_der \<A> x \<and> ground x"] by blast
  {fix j assume "j < length qs"
    then have "qs ! j |\<in>| ta_der \<A> ((take i ts @ Var (qs ! i) # drop (Suc i) ts) ! j)"
      using wit by (cases "j < i") (auto simp: min_def nth_append_Cons)}
  then have "\<forall> i < length qs. qs ! i |\<in>| (map (ta_der \<A>) (take i ts @ Var (qs ! i) # drop (Suc i) ts)) ! i"
    using wit rule(2) by (auto simp: nth_append_Cons)
  then have res: "q |\<in>| ta_der \<A> (Fun (None, Some f) (take i ts @ Var (qs ! i) # drop (Suc i) ts))"
    using rule(1, 2) wit by (auto simp: min_def nth_append_Cons intro!: exI[of _ q] exI[of _ qs])
  then show ?case using rule(1, 2) wit
    apply (rule_tac x = "take i ts" in exI, rule_tac x = "drop (Suc i) ts" in exI)
    apply (auto simp: take_map drop_map  dest!: in_set_takeD in_set_dropD simp del: ta_der_simps intro!: exI[of _ f] exI[of _ Hole])
    apply (metis all_nth_imp_all_set)+
    done
next
  case (eps p q r)
  then show ?case by (meson r_into_rtrancl ta_der_eps)
qed

lemma rule_target_Q_inf:
  assumes "(None, Some f) qs \<rightarrow> q' |\<in>| rules \<A>" and "i < length qs"
   shows "(qs ! i, q') \<in> Q_inf \<A>" using assms  
  by (intro rule) auto

lemma rule_target_eps_Q_inf:
  assumes "(None, Some f) qs \<rightarrow> q' |\<in>| rules \<A>" "(q', q) |\<in>| (eps \<A>)|\<^sup>+|"
     and "i < length qs"
   shows "(qs ! i, q) \<in> Q_inf \<A>"
  using assms(2, 1, 3) by (induct rule: ftrancl_induct) (auto intro: rule eps)


lemma step_in_Q_inf:
  assumes "q |\<in>| ta_der_strict \<A> (map_funs_term (\<lambda>f. (None, Some f)) (Fun f (ss @ Var p # ts)))"
    shows "(p, q) \<in> Q_inf \<A>"
  using assms rule_target_eps_Q_inf[of f _ _ \<A> q] rule_target_Q_inf[of f _ q \<A>]
  by (auto simp: comp_def nth_append_Cons split!: if_splits) 


lemma ta_der_Q_inf:
  assumes "q |\<in>| ta_der_strict \<A> (map_funs_term (\<lambda>f. (None, Some f)) (C\<langle>Var p\<rangle>))" and "C \<noteq> Hole"
  shows "(p, q) \<in> Q_inf \<A>" using assms
proof (induct C arbitrary: q)
  case (More f ss C ts)
  then show ?case
  proof (cases "C = Hole")
    case True
    then show ?thesis using More(2) by (auto simp: step_in_Q_inf)
  next
    case False
    then obtain q' where q: "q' |\<in>| ta_der_strict \<A> (map_funs_term (\<lambda>f. (None, Some f)) C\<langle>Var p\<rangle>)"
     "q |\<in>| ta_der_strict \<A> (map_funs_term (\<lambda>f. (None, Some f)) (Fun f (ss @ Var q' # ts)))"
      using More(2) length_map
     (* SLOW *)
      by (auto simp: comp_def nth_append_Cons split: if_splits cong: if_cong')
         (smt nat_neq_iff nth_map ta_der_strict_simps)+
    have "(p, q') \<in> Q_inf \<A>" using More(1)[OF q(1) False] .
    then show ?thesis using step_in_Q_inf[OF q(2)] by (auto intro: trans)
  qed
qed auto

lemma Q_inf_e_infinite_terms_res:
  assumes "q \<in> Q_inf_e \<A>" and "\<Q> \<A> |\<subseteq>| ta_reachable \<A>"
  shows "infinite {t. q |\<in>| ta_der \<A> (term_of_gterm t) \<and> fst (groot_sym t) = None}"
proof -
  let ?P ="\<lambda> u. ground u \<and> q |\<in>| ta_der \<A> u \<and> fst (fst (the (root u))) = None"
  have groot[simp]: "fst (fst (the (root (term_of_gterm t)))) = fst (groot_sym t)" for t by (cases t) auto
  have [simp]: "C \<noteq> \<box> \<Longrightarrow> fst (fst (the (root C\<langle>t\<rangle>))) = fst (root_ctxt C)" for C t by (cases C) auto
  from assms(1) obtain p where cycle: "(p, p) \<in> Q_inf \<A>" "(p, q) \<in> Q_inf \<A>" by auto
  from Q_inf_reach_state_rule[OF cycle(1) assms(2)] obtain C where
    ctxt: "C \<noteq> \<box>" "ground_ctxt C" and reach: "p |\<in>| ta_der \<A> C\<langle>Var p\<rangle>"
    by blast
  obtain C2 where
    closing_ctxt: "C2 \<noteq> \<box>" "ground_ctxt C2" "fst (root_ctxt C2) = None" and cl_reach: "q |\<in>| ta_der \<A> C2\<langle>Var p\<rangle>"
    by (metis (full_types) Q_inf_reach_state_rule[OF cycle(2) assms(2)] ctxt.distinct(1) fst_conv root_ctxt.simps(1))
  from assms(2) obtain t where t: "p |\<in>| ta_der \<A> t" and gr_t: "ground t"
    by (meson Q_inf_states_ta_states(1) cycle(1) fsubsetD ta_reachableE)
  let ?terms = "\<lambda> n. (C ^ Suc n)\<langle>t\<rangle>" let ?S = "{?terms n | n. p |\<in>| ta_der \<A> (?terms n) \<and> ground (?terms n)}"
  have "ground (?terms n)" for n using ctxt(2) gr_t by auto
  moreover have "p |\<in>| ta_der \<A> (?terms n)" for n using reach t(1)
    by (auto simp: ta_der_ctxt) (meson ta_der_ctxt ta_der_ctxt_n_loop)
  ultimately have inf: "infinite ?S" using ctxt_comp_n_lower_bound[OF ctxt(1)]
    using no_upper_bound_infinite[of _ depth, of ?S] by blast
  from infinite_inj_image_infinite[OF this] have inf:"infinite (ctxt_apply_term C2 ` ?S)"
    by (smt ctxt_eq inj_on_def)
  {fix u assume "u \<in> (ctxt_apply_term C2 ` ?S)"
    then have "?P u" unfolding image_Collect using closing_ctxt cl_reach
      by (auto simp: ta_der_ctxt)}
  from this have inf: "infinite {u. ground u \<and> q |\<in>| ta_der \<A> u \<and> fst (fst (the (root u))) = None}"
    by (intro infinite_super[OF _ inf] subsetI) fast
  have inf: "infinite (gterm_of_term ` {u. ground u \<and> q |\<in>| ta_der \<A> u \<and> fst (fst (the (root u))) = None})"
    by (intro infinite_inj_image_infinite[OF inf] gterm_of_term_inj) auto
  show ?thesis
    by (intro infinite_super[OF _ inf]) (auto dest: groot_sym_gterm_of_term)
qed













lemma gfun_at_after_hole_pos:
  assumes "ghole_pos C \<le>\<^sub>p p"
  shows "gfun_at C\<langle>t\<rangle>\<^sub>G p = gfun_at t (p -\<^sub>p ghole_pos C)" using assms
proof (induct C arbitrary: p)
  case (GMore f ss C ts) then show ?case
    by (cases p) auto
qed auto

lemma pos_diff_0 [simp]: "p -\<^sub>p p = []"
  by (auto simp: pos_diff_def)

lemma Max_suffI: "finite A \<Longrightarrow> A = B \<Longrightarrow> Max A = Max B"
  by (intro Max_eq_if) auto

lemma nth_args_depth_eqI:
  assumes "length ss = length ts"
    and "\<And> i. i < length ts \<Longrightarrow> depth (ss ! i) = depth (ts ! i)"
  shows "depth (Fun f ss) = depth (Fun g ts)"
proof -
  from assms(1, 2) have "depth ` set ss = depth ` set ts"
    using nth_map_conv[OF assms(1), of depth depth]
    by (simp flip: set_map)
  from Max_suffI[OF _ this] show ?thesis using assms(1)
    by (cases ss; cases ts) auto
qed

lemma subt_at_ctxt_apply_hole_pos [simp]: "C\<langle>s\<rangle> |_ hole_pos C = s"
  by (induct C) auto

lemma ctxt_at_pos_ctxt_apply_hole_poss [simp]: "ctxt_at_pos C\<langle>s\<rangle> (hole_pos C) = C"
  by (induct C) auto

abbreviation "map_funs_ctxt f \<equiv> map_ctxt f (\<lambda> x. x)"
lemma map_funs_term_ctxt_apply [simp]:
  "map_funs_term f C\<langle>s\<rangle> = (map_funs_ctxt f C)\<langle>map_funs_term f s\<rangle>"
  by (induct C) auto

lemma map_funs_term_ctxt_decomp:
  assumes "map_funs_term fg t = C\<langle>s\<rangle>"
  shows "\<exists> D u. C = map_funs_ctxt fg D \<and> s = map_funs_term fg u \<and> t = D\<langle>u\<rangle>"
using assms
proof (induct C arbitrary: t)
  case Hole
  show ?case
    by (rule exI[of _ Hole], rule exI[of _ t], insert Hole, auto)
next
  case (More g bef C aft)
  from More(2) obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from More(2)[unfolded t] have f: "fg f = g" and ts: "map (map_funs_term fg) ts = bef @ C\<langle>s\<rangle> # aft" (is "?ts = ?bca") by auto
  from ts have "length ?ts = length ?bca" by auto
  then have len: "length ts = length ?bca" by auto
  note id = ts[unfolded map_nth_eq_conv[OF len], THEN spec, THEN mp]
  let ?i = "length bef"
  from len have i: "?i < length ts" by auto
  from id[of ?i] have "map_funs_term fg (ts ! ?i) = C\<langle>s\<rangle>" by auto
  from More(1)[OF this] obtain D u where D: "C = map_funs_ctxt fg D" and
    u: "s = map_funs_term fg u" and id: "ts ! ?i = D\<langle>u\<rangle>" by auto
  from ts have "take ?i ?ts = take ?i ?bca" by simp
  also have "... = bef" by simp
  finally have bef: "map (map_funs_term fg) (take ?i ts) = bef" by (simp add: take_map)
  from ts have "drop (Suc ?i) ?ts = drop (Suc ?i) ?bca" by simp
  also have "... = aft" by simp
  finally have aft: "map (map_funs_term fg) (drop (Suc ?i) ts) = aft" by (simp add:drop_map)
  let ?bda = "take ?i ts @ D\<langle>u\<rangle> # drop (Suc ?i) ts"
  show ?case
  proof (rule exI[of _ "More f (take ?i ts) D (drop (Suc ?i) ts)"],
      rule exI[of _ u], simp add: u f D bef aft t)
    have "ts = take ?i ts @ ts ! ?i # drop (Suc ?i) ts"
      by (rule id_take_nth_drop[OF i])
    also have "... = ?bda" by (simp add: id)
    finally show "ts = ?bda" .
  qed
qed





lemma prod_automata_from_none_root_dec:
  assumes "gta_lang Q \<A> \<subseteq> {gpair s t| s t. funas_gterm s \<subseteq> \<F> \<and> funas_gterm t \<subseteq> \<F>}"
    and "q |\<in>| ta_der \<A> (term_of_gterm t)" and "fst (groot_sym t) = None"
    and "\<Q> \<A> |\<subseteq>| ta_reachable \<A>" and "q |\<in>| ta_productive Q \<A>"
  shows "\<exists> u. t = gterm_to_None_Some u \<and> funas_gterm u \<subseteq> \<F>"
proof -
  have *: "gfun_at t [] = Some (groot_sym t)" by (cases t) auto
  from assms(4, 5) obtain C q\<^sub>f where ctxt: "ground_ctxt C" and
    fin: "q\<^sub>f |\<in>| ta_der \<A> C\<langle>Var q\<rangle>" "q\<^sub>f |\<in>| Q"
    by (auto simp: ta_productive_def'[OF assms(4)])
  then obtain s v where gp: "gpair s v = (gctxt_of_ctxt C)\<langle>t\<rangle>\<^sub>G" and
   funas: "funas_gterm v \<subseteq> \<F>"
    using assms(1, 2) gta_langI[OF fin(2), of \<A> "(gctxt_of_ctxt C)\<langle>t\<rangle>\<^sub>G"]
    by (auto simp: ta_der_ctxt ground_gctxt_of_ctxt_apply_gterm)
  from gp have mem: "hole_pos C \<in> gposs s \<union> gposs v"
    by auto (metis Un_iff ctxt ghole_pos_in_apply gposs_of_gpair ground_hole_pos_to_ghole)
  from this have "hole_pos C \<notin> gposs s" using assms(3)
    using arg_cong[OF gp, of "\<lambda> t. gfun_at t (hole_pos C)"]
    using ground_hole_pos_to_ghole[OF ctxt]
    using gfun_at_after_hole_pos[OF position_less_refl, of "gctxt_of_ctxt C"]
    by (auto simp: gfun_at_gpair * split: if_splits)
       (metis fstI gfun_at_None_ngposs_iff)+
  from subst_at_gpair_nt_poss_None_Some[OF _ this, of v] this
  have "t = gterm_to_None_Some (gsubt_at v (hole_pos C)) \<and> funas_gterm (gsubt_at v (hole_pos C)) \<subseteq> \<F>"
    using funas mem funas_gterm_gsubt_at_subseteq
    by (auto simp: gp intro!: exI[of _ "gsubt_at v (hole_pos C)"])
       (metis ctxt ground_hole_pos_to_ghole gsubt_at_gctxt_apply_ghole)
  then show ?thesis by blast
qed

lemma infinite_set_dec_infinite:
  assumes "infinite S" and "\<And> s. s \<in> S \<Longrightarrow> \<exists> t. f t = s \<and> P t"
  shows "infinite {t | t s. s \<in> S \<and> f t = s \<and> P t}" (is "infinite ?T")
proof (rule ccontr)
  assume ass: "\<not> infinite ?T"
  have "S \<subseteq> f ` {x . P x}" using assms(2) by auto 
  then show False using ass assms(1)
    by (auto simp: subset_image_iff)
      (smt Ball_Collect finite_imageI image_subset_iff infinite_iff_countable_subset subset_eq) 
qed

lemma Q_inf_exec_impl_Q_inf:
  assumes "gta_lang Q \<A> \<subseteq> {gpair s t| s t. funas_gterm s \<subseteq> fset \<F> \<and> funas_gterm t \<subseteq> fset \<F>}"
   and "\<Q> \<A> |\<subseteq>| ta_reachable \<A>" and "\<Q> \<A> |\<subseteq>| ta_productive Q \<A>"
   and "q \<in> Q_inf_e \<A>"
  shows "q |\<in>| Q_infty \<A> \<F>"
proof -
  let ?S = "{t. q |\<in>| ta_der \<A> (term_of_gterm t) \<and> fst (groot_sym t) = None}"
  let ?P = "\<lambda> t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (term_of_gterm (gterm_to_None_Some t))"
  let ?F = "(\<lambda>(f, n). ((None, Some f), n)) |`| \<F>"
  from Q_inf_e_infinite_terms_res[OF assms(4, 2)] have inf: "infinite ?S" by auto
  {fix t assume "t \<in> ?S"
    then have "\<exists> u. t = gterm_to_None_Some u \<and> funas_gterm u \<subseteq> fset \<F>"
      using prod_automata_from_none_root_dec[OF assms(1)] assms(2, 3)
      using fin_mono by fastforce}
  then show ?thesis using infinite_set_dec_infinite[OF inf, of gterm_to_None_Some ?P]
    by (auto simp: Q_infty_fmember) blast
qed


lemma Q_inf_impl_Q_inf_exec:
  assumes "q |\<in>| Q_infty \<A> \<F>"
    shows "q \<in> Q_inf_e \<A>"
proof -
  let ?t_of_g = "\<lambda> t. term_of_gterm t :: ('b option \<times> 'b option, 'a) term"
  let ?t_og_g2 = "\<lambda> t. term_of_gterm t :: ('b, 'a) term"
  let ?inf = "(?t_og_g2 :: 'b gterm \<Rightarrow> ('b, 'a) term) ` {t |t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (?t_of_g (gterm_to_None_Some t))}"
  obtain n where card_st: "fcard (\<Q> \<A>) < n" by blast
  from assms(1) have "infinite {t |t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (?t_of_g (gterm_to_None_Some t))}"
    unfolding Q_infty_def by blast
  from infinite_inj_image_infinite[OF this, of "?t_og_g2"] have inf: "infinite ?inf" using inj_term_of_gterm by blast
  {fix s assume "s \<in> ?inf" then have "ground s" "funas_term s \<subseteq> fset \<F>" by (auto simp: funas_term_of_gterm_conv subsetD)}
  from infinte_no_depth_limit[OF inf, of "fset \<F>"] this obtain u where
    funas: "funas_gterm u \<subseteq> fset \<F>" and card_d: "n < depth (?t_og_g2 u)" and reach: "q |\<in>| ta_der \<A> (?t_of_g (gterm_to_None_Some u))"
    by auto blast
  have "depth (?t_og_g2 u) = depth (?t_of_g (gterm_to_None_Some u))"
  proof (induct u)
    case (GFun f ts) then show ?case
      by (auto simp: comp_def intro: nth_args_depth_eqI)
  qed 
  from this pigeonhole_tree_automata[OF _ reach] card_st card_d obtain C2 C s v p where
    ctxt: "C2 \<noteq> \<box>" "C\<langle>s\<rangle> = term_of_gterm (gterm_to_None_Some u)" "C2\<langle>v\<rangle> = s" and
    loop: "p |\<in>| ta_der \<A> v \<and> p |\<in>| ta_der \<A> C2\<langle>Var p\<rangle> \<and> q |\<in>| ta_der \<A> C\<langle>Var p\<rangle>"
    by auto
  from ctxt have gr: "ground_ctxt C2" "ground_ctxt C" by auto (metis ground_ctxt_apply ground_term_of_gterm)+ 
  from ta_der_to_ta_strict[OF _ gr(1)] loop obtain q' where
    to_strict: "(p = q' \<or> (p, q') |\<in>| (eps \<A>)|\<^sup>+|) \<and> p |\<in>| ta_der_strict \<A> C2\<langle>Var q'\<rangle>" by fastforce
  have *: "\<exists> C. C2 = map_funs_ctxt lift_None_Some C \<and> C \<noteq> \<box>" using ctxt(1, 2)
    by (auto simp flip: ctxt(3)) (smt ctxt.simps(8) map_funs_term_ctxt_decomp map_term_of_gterm)
  then have q_p: "(q', p) \<in> Q_inf \<A>" using to_strict ta_der_Q_inf[of p \<A> _  q'] ctxt
    by auto
  then have cycle: "(q', q') \<in> Q_inf \<A>" using to_strict by (auto intro: Q_inf_ta_eps_Q_inf)
  show ?thesis
  proof (cases "C = \<box>")
    case True then show ?thesis
      using cycle q_p loop by (auto intro: Q_inf_ta_eps_Q_inf)
  next
    case False
    obtain q'' where r: "p = q'' \<or> (p, q'') |\<in>| (eps \<A>)|\<^sup>+|" "q |\<in>| ta_der_strict \<A> C\<langle>Var q''\<rangle>"
      using ta_der_to_ta_strict[OF conjunct2[OF conjunct2[OF loop]] gr(2)] by auto
    then have "(q'', q) \<in>  Q_inf \<A>" using ta_der_Q_inf[of q \<A> _  q''] ctxt False
      by auto (smt (z3) ctxt.simps(8) map_funs_term_ctxt_decomp map_term_of_gterm)+
    then show ?thesis using r(1) cycle q_p
      by (auto simp: Q_inf_ta_eps_Q_inf intro!: exI[of _ q'])
         (meson Q_inf.trans Q_inf_ta_eps_Q_inf)+   
  qed
qed

lemma Q_infty_fQ_inf_e_conv:
  assumes "gta_lang Q \<A> \<subseteq> {gpair s t| s t. funas_gterm s \<subseteq> fset \<F> \<and> funas_gterm t \<subseteq> fset \<F>}"
   and "\<Q> \<A> |\<subseteq>| ta_reachable \<A>" and "\<Q> \<A> |\<subseteq>| ta_productive Q \<A>"
  shows "Q_infty \<A> \<F> = fQ_inf_e \<A>"
  using Q_inf_impl_Q_inf_exec Q_inf_exec_impl_Q_inf[OF assms]
  by (auto simp: fQ_inf_e.rep_eq) fastforce

definition Inf_reg_impl where
  "Inf_reg_impl R = Inf_reg R (fQ_inf_e (ta R))"

lemma Inf_reg_impl_sound:
  assumes "\<L> \<A> \<subseteq> {gpair s t| s t. funas_gterm s \<subseteq> fset \<F> \<and> funas_gterm t \<subseteq> fset \<F>}"
   and "\<Q>\<^sub>r \<A> |\<subseteq>| ta_reachable (ta \<A>)" and "\<Q>\<^sub>r \<A> |\<subseteq>| ta_productive (fin \<A>) (ta \<A>)"
  shows "\<L> (Inf_reg_impl \<A>) = \<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>))"
  using Q_infty_fQ_inf_e_conv[of "fin \<A>" "ta \<A>" \<F>] assms[unfolded \<L>_def]
  by (simp add: Inf_reg_impl_def)

end
