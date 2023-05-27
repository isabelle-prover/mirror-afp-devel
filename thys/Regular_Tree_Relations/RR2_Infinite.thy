theory RR2_Infinite
  imports RRn_Automata Tree_Automata_Pumping
begin


lemma map_ta_rule_id [simp]: "map_ta_rule f id r = (r_root r) (map f (r_lhs_states r)) \<rightarrow> (f (r_rhs r))" for f r
  by (simp add: ta_rule.expand ta_rule.map_sel(1 - 3))

(* Finitness/Infinitness facts *)

lemma no_upper_bound_infinite:
  assumes "\<forall>(n::nat). \<exists>t \<in> S. n < f t"
  shows "infinite S"
proof (rule ccontr, simp)
  assume "finite S"
  then obtain n where "n = Max (f ` S)" "\<forall> t \<in> S. f t \<le> n" by auto
  then show False using assms linorder_not_le by blast
qed

lemma set_constr_finite:
  assumes "finite F"
  shows "finite {h x | x. x \<in> F \<and> P x}" using assms
  by (induct) auto

lemma bounded_depth_finite:
  assumes fin_F: "finite \<F>" and "\<Union> (funas_term ` S) \<subseteq> \<F>"
    and "\<forall>t \<in> S. depth t \<le> n" and "\<forall>t \<in> S. ground t"
  shows "finite S" using assms(2-)
proof (induction n arbitrary: S)
  case 0
  {fix t assume elem: "t \<in> S"
    from 0 have "depth t = 0" "ground t" "funas_term t \<subseteq> \<F>" using elem by auto
    then have "\<exists> f. (f, 0) \<in> \<F> \<and> t = Fun f []" by (cases t rule: depth.cases) auto}
  then have "S \<subseteq> {Fun f [] |f . (f, 0) \<in> \<F>}" by (auto simp add: image_iff)
  from finite_subset[OF this] show ?case
    using set_constr_finite[OF fin_F, of "\<lambda> (f, n). Fun f []" "\<lambda> x. snd x = 0"]
    by auto
next
  case (Suc n)
  from Suc obtain S' where
    S: "S' = {t :: ('a, 'b) term . ground t \<and> funas_term t \<subseteq> \<F> \<and> depth t \<le> n}" "finite S'"
    by (auto simp add: SUP_le_iff)
  then obtain L F where L: "set L = S'" "set F = \<F>" using fin_F by (meson finite_list)
  let ?Sn = "{Fun f ts | f ts. (f, length ts) \<in> \<F> \<and> set ts \<subseteq> S'}"
  let ?Ln = "concat (map (\<lambda> (f, n). map (\<lambda> ts. Fun f ts) (List.n_lists n L)) F)"
  {fix t assume elem: "t \<in> S"
    from Suc have "depth t \<le> Suc n" "ground t" "funas_term t \<subseteq> \<F>" using elem by auto
    then have "funas_term t \<subseteq> \<F> \<and> (\<forall> x \<in> set (args t). depth x \<le> n) \<and> ground t"
      by (cases t rule: depth.cases) auto
    then have "t \<in> ?Sn \<union> S'"
      using S by (cases t) auto} note sub = this
  {fix t assume elem: "t \<in> ?Sn"
    then obtain f ts where [simp]: "t = Fun f ts" and invar: "(f, length ts) \<in> \<F>" "set ts \<subseteq> S'"
      by blast
    then have "Fun f ts \<in> set (map (\<lambda> ts. Fun f ts) (List.n_lists (length ts) L))" using L(1)
      by (auto simp: image_iff set_n_lists)
    then have "t \<in> set ?Ln" using invar(1) L(2) by auto}
  from this sub have sub: "?Sn \<subseteq> set ?Ln" "S \<subseteq> ?Sn \<union> S'" by blast+
  from finite_subset[OF sub(1)] finite_subset[OF sub(2)] finite_UnI[of ?Sn, OF _ S(2)]
  show ?case by blast
qed

lemma infinite_imageD:
  "infinite (f ` S) \<Longrightarrow> inj_on f S \<Longrightarrow> infinite S"
  by blast

lemma infinite_imageD2:
  "infinite (f ` S) \<Longrightarrow> inj f \<Longrightarrow> infinite S"
  by blast

lemma infinite_inj_image_infinite:
  assumes "infinite S" and "inj_on f S"
  shows "infinite (f ` S)"
  using assms finite_image_iff by blast

(*The following lemma tells us that number of terms greater than a certain depth are infinite*)
lemma infinte_no_depth_limit:
  assumes "infinite S" and "finite \<F>"
    and "\<forall>t \<in> S. funas_term t \<subseteq> \<F>" and "\<forall>t \<in> S. ground t"
  shows "\<forall>(n::nat). \<exists>t \<in> S. n < (depth t)"
proof(rule allI, rule ccontr)
  fix n::nat
  assume "\<not> (\<exists>t \<in> S. (depth t) >  n)"
  hence "\<forall>t \<in> S. depth t \<le> n" by auto
  from bounded_depth_finite[OF assms(2) _ this] show False using assms
    by auto
qed

lemma depth_gterm_conv:
  "depth (term_of_gterm t) = depth (term_of_gterm t)"
  by (metis leD nat_neq_iff poss_gposs_conv poss_length_bounded_by_depth poss_length_depth)

lemma funs_term_ctxt [simp]:
  "funs_term C\<langle>s\<rangle> = funs_ctxt C \<union> funs_term s"
  by (induct C) auto

lemma pigeonhole_ta_infinit_terms:
  fixes t ::"'f gterm" and \<A> :: "('q, 'f) ta"
  defines "t' \<equiv> term_of_gterm t :: ('f, 'q) term"
  assumes "fcard (\<Q> \<A>) < depth t'" and "q |\<in>| gta_der \<A> t" and "P (funas_gterm t)"
  shows "infinite {t . q |\<in>| gta_der \<A> t \<and> P (funas_gterm t)}"
proof -
  from pigeonhole_tree_automata[OF _ assms(3)[unfolded gta_der_def]] assms(2,4)
  obtain C C2 s v p where ctxt: "C2 \<noteq> \<box>" "C\<langle>s\<rangle> = t'" "C2\<langle>v\<rangle> = s" and
    loop: "p |\<in>| ta_der \<A> v" "p |\<in>| ta_der \<A> C2\<langle>Var p\<rangle>" "q |\<in>| ta_der \<A> C\<langle>Var p\<rangle>"
    unfolding assms(1) by auto
  let ?terms = "\<lambda> n. C\<langle>(C2 ^n)\<langle>v\<rangle>\<rangle>" let ?inner = "\<lambda> n. (C2 ^n)\<langle>v\<rangle>"
  have gr: "ground_ctxt C2" "ground_ctxt C" "ground v"
    using arg_cong[OF ctxt(2), of ground] unfolding ctxt(3)[symmetric] assms(1)
    by fastforce+
  moreover have funas: "funas_term (?terms (Suc n)) = funas_term t'" for n
    unfolding ctxt(2, 3)[symmetric] using ctxt_comp_n_pres_funas by auto
  moreover have der: "q |\<in>| ta_der \<A> (?terms (Suc n))" for n using loop
    by (meson ta_der_ctxt ta_der_ctxt_n_loop)
  moreover have "n < depth (?terms (Suc n))" for n
    by (meson ctxt(1) ctxt_comp_n_lower_bound depth_ctxt_less_eq less_le_trans)
  ultimately have "q |\<in>| ta_der \<A> (?terms (Suc n)) \<and> ground (?terms (Suc n)) \<and>
    P (funas_term (?terms (Suc n))) \<and> n < depth (?terms (Suc n))" for n using assms(4)
    by (auto simp: assms(1) funas_term_of_gterm_conv)
  then have inf: "infinite {t. q |\<in>| ta_der \<A> t \<and> ground t \<and> P (funas_term t)}"
    by (intro no_upper_bound_infinite[of _ depth]) blast
  have inj: "inj_on gterm_of_term {t. q |\<in>| ta_der \<A> t \<and> ground t \<and> P (funas_term t)}"
    by (intro gterm_of_term_inj) simp
  show ?thesis
    by (intro infinite_super[OF _ infinite_inj_image_infinite[OF inf inj]])
       (auto simp: image_def gta_der_def funas_gterm_gterm_of_term)
qed


lemma gterm_to_None_Some_funas [simp]:
  "funas_gterm (gterm_to_None_Some t) \<subseteq> (\<lambda> (f, n). ((None, Some f), n)) ` \<F> \<longleftrightarrow> funas_gterm t \<subseteq> \<F>"
  by (induct t) (auto simp: funas_gterm_def, blast)

lemma funas_gterm_bot_some_decomp:
  assumes "funas_gterm s \<subseteq> (\<lambda> (f, n). ((None, Some f), n)) ` \<F>"
  shows "\<exists> t. gterm_to_None_Some t = s \<and> funas_gterm t \<subseteq> \<F>" using assms
proof (induct s)
  case (GFun f ts)
  from GFun(1)[OF nth_mem] obtain ss where l: "length ss = length ts \<and> (\<forall>i<length ts. gterm_to_None_Some (ss ! i) = ts ! i)"
    using Ex_list_of_length_P[of "length ts" "\<lambda> s i. gterm_to_None_Some s = ts ! i"] GFun(2-)
    by (auto simp: funas_gterm_def) (meson UN_subset_iff nth_mem)
  then have "i < length ss \<Longrightarrow> funas_gterm (ss ! i) \<subseteq> \<F>" for i using GFun(2)
    by (auto simp: UN_subset_iff) (smt (z3) gterm_to_None_Some_funas nth_mem subsetD)
  then show ?case using GFun(2-) l
    by (cases f) (force simp: map_nth_eq_conv UN_subset_iff dest!: in_set_idx intro!: exI[of _ "GFun (the (snd f)) ss"])
qed

(* Definition INF, Q_infinity and automata construction *)

definition "Inf_branching_terms \<R> \<F> = {t . infinite {u. (t, u) \<in> \<R> \<and> funas_gterm u \<subseteq> fset \<F>} \<and> funas_gterm t \<subseteq> fset \<F>}"

definition "Q_infty \<A> \<F> = {|q | q. infinite {t | t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (term_of_gterm (gterm_to_None_Some t))}|}"

lemma Q_infty_fmember:
  "q |\<in>| Q_infty \<A> \<F> \<longleftrightarrow> infinite {t | t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (term_of_gterm (gterm_to_None_Some t))}"
proof -
  have "{q | q. infinite {t | t. funas_gterm t \<subseteq> fset \<F> \<and> q |\<in>| ta_der \<A> (term_of_gterm (gterm_to_None_Some t))}} \<subseteq> fset (\<Q> \<A>)"
    using not_finite_existsD by fastforce
  from finite_subset[OF this] show ?thesis
    by (auto simp: Q_infty_def)
qed

abbreviation q_inf_dash_intro_rules where
  "q_inf_dash_intro_rules Q r \<equiv> if (r_rhs r) |\<in>| Q \<and> fst (r_root r) = None then {|(r_root r) (map CInl (r_lhs_states r)) \<rightarrow> CInr (r_rhs r)|} else {||}"

abbreviation args :: "'a list \<Rightarrow> nat \<Rightarrow> ('a + 'a) list" where
  "args \<equiv> \<lambda> qs i. map CInl (take i qs) @ CInr (qs ! i) # map CInl (drop (Suc i) qs)"

abbreviation q_inf_dash_closure_rules :: "('q, 'f) ta_rule \<Rightarrow> ('q + 'q, 'f) ta_rule list" where
  "q_inf_dash_closure_rules r \<equiv> (let (f, qs, q) = (r_root r, r_lhs_states r, r_rhs r) in
   (map (\<lambda> i. f (args qs i) \<rightarrow> CInr q) [0 ..< length qs]))"

definition Inf_automata :: "('q, 'f option \<times> 'f option) ta \<Rightarrow> 'q fset \<Rightarrow> ('q + 'q, 'f option \<times> 'f option) ta" where
  "Inf_automata \<A> Q = TA
  (( |\<Union>| (q_inf_dash_intro_rules Q |`| rules \<A>)) |\<union>| ( |\<Union>| ((fset_of_list \<circ> q_inf_dash_closure_rules) |`| rules \<A>)) |\<union>|
   map_ta_rule CInl id |`| rules \<A>) (map_both Inl |`| eps \<A> |\<union>| map_both CInr |`| eps \<A>)"

definition Inf_reg where
  "Inf_reg \<A> Q = Reg (CInr |`| fin \<A>) (Inf_automata (ta \<A>) Q)"

lemma Inr_Inl_rel_comp:
  "map_both CInr |`| S |O| map_both CInl |`| S = {||}" by auto

lemmas eps_split = ftrancl_Un2_separatorE[OF Inr_Inl_rel_comp]

lemma Inf_automata_eps_simp [simp]:
  shows "(map_both Inl |`| eps \<A> |\<union>| map_both CInr |`| eps \<A>)|\<^sup>+| =
      (map_both CInl |`| eps \<A>)|\<^sup>+| |\<union>| (map_both CInr |`| eps \<A>)|\<^sup>+|"
proof -
  {fix x y z assume "(x, y) |\<in>| (map_both CInl |`| eps \<A>)|\<^sup>+|"
    "(y, z) |\<in>| (map_both CInr |`| eps \<A>)|\<^sup>+|"
    then have False
      by (metis Inl_Inr_False eps_statesI(1, 2) eps_states_image fimageE ftranclD ftranclD2)}
  then show ?thesis by (auto simp: Inf_automata_def eps_split)
qed

lemma map_both_CInl_ftrancl_conv:
  "(map_both CInl |`| eps \<A>)|\<^sup>+| = map_both CInl |`| (eps \<A>)|\<^sup>+|"
  by (intro ftrancl_map_both_fsubset) (auto simp: finj_CInl_CInr)

lemma map_both_CInr_ftrancl_conv:
  "(map_both CInr |`| eps \<A>)|\<^sup>+| = map_both CInr |`| (eps \<A>)|\<^sup>+|"
  by (intro ftrancl_map_both_fsubset) (auto simp: finj_CInl_CInr)

lemmas map_both_ftrancl_conv = map_both_CInl_ftrancl_conv map_both_CInr_ftrancl_conv 

lemma Inf_automata_Inl_to_eps [simp]:
  "(CInl p, CInl q) |\<in>| (map_both CInl |`| eps \<A>)|\<^sup>+| \<longleftrightarrow> (p, q) |\<in>| (eps \<A>)|\<^sup>+|"
  "(CInr p, CInr q) |\<in>| (map_both CInr |`| eps \<A>)|\<^sup>+| \<longleftrightarrow> (p, q) |\<in>| (eps \<A>)|\<^sup>+|"
  "(CInl q, CInl p) |\<in>| (map_both CInr |`| eps \<A>)|\<^sup>+| \<longleftrightarrow> False"
  "(CInr q, CInr p) |\<in>| (map_both CInl |`| eps \<A>)|\<^sup>+| \<longleftrightarrow> False"
  by (auto simp: map_both_ftrancl_conv dest: fmap_prod_fimageI)

lemma Inl_eps_Inr:
  "(CInl q, CInl p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+| \<longleftrightarrow> (CInr q, CInr p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+|"
  by (auto simp: Inf_automata_def)

lemma Inr_rhs_eps_Inr_lhs:
  assumes "(q, CInr p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+|"
  obtains q' where "q = CInr q'" using assms ftrancl_map_both_fsubset[OF finj_CInl_CInr(1)]
  by (cases q) (auto simp: Inf_automata_def map_both_ftrancl_conv)

lemma Inl_rhs_eps_Inl_lhs:
  assumes "(q, CInl p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+|"
  obtains q' where "q = CInl q'" using assms
  by (cases q) (auto simp: Inf_automata_def map_both_ftrancl_conv)

lemma Inf_automata_eps [simp]:
  "(CInl q, CInr p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+| \<longleftrightarrow> False"
  "(CInr q, CInl p) |\<in>| (eps (Inf_automata \<A> Q))|\<^sup>+| \<longleftrightarrow> False"
  by (auto elim: Inr_rhs_eps_Inr_lhs Inl_rhs_eps_Inl_lhs)

lemma Inl_A_res_Inf_automata:
  "ta_der (fmap_states_ta CInl \<A>) t |\<subseteq>| ta_der (Inf_automata \<A> Q) t"
proof (rule ta_der_mono)
  show "rules (fmap_states_ta CInl \<A>) |\<subseteq>| rules (Inf_automata \<A> Q)"
    apply (rule fsubsetI)
    by (auto simp: Inf_automata_def fmap_states_ta_def' image_iff Bex_def)
next
  show "eps (fmap_states_ta CInl \<A>) |\<subseteq>| eps (Inf_automata \<A> Q)"
    by (rule fsubsetI) (simp add: Inf_automata_def fmap_states_ta_def')
qed

lemma Inl_res_A_res_Inf_automata:
  "CInl |`| ta_der \<A> (term_of_gterm t) |\<subseteq>| ta_der (Inf_automata \<A> Q) (term_of_gterm t)"
  by (intro fsubset_trans[OF ta_der_fmap_states_ta_mono[of CInl \<A> t]]) (auto simp: Inl_A_res_Inf_automata)

lemma r_rhs_CInl_args_A_rule:
  assumes "f qs \<rightarrow> CInl q |\<in>| rules (Inf_automata \<A> Q)"
  obtains qs' where "qs = map CInl qs'" "f qs' \<rightarrow> q |\<in>| rules \<A>" using assms
  by (auto simp: Inf_automata_def split!: if_splits)

lemma A_rule_to_dash_closure:
  assumes "f qs \<rightarrow> q |\<in>| rules \<A>" and "i < length qs"
  shows "f (args qs i) \<rightarrow> CInr q |\<in>| rules (Inf_automata \<A> Q)"
  using assms by (auto simp add: Inf_automata_def fimage_iff fBall_def upt_fset intro!: fBexI[OF _ assms(1)])

lemma Inf_automata_reach_to_dash_reach:
  assumes "CInl p |\<in>| ta_der (Inf_automata \<A> Q) C\<langle>Var (CInl q)\<rangle>"
  shows "CInr p |\<in>| ta_der (Inf_automata \<A> Q) C\<langle>Var (CInr q)\<rangle>" (is "_ |\<in>| ta_der ?A _")
  using assms
proof (induct C arbitrary: p)
  case (More f ss C ts)
  from More(2) obtain qs q' where
    rule: "f qs \<rightarrow> q' |\<in>| rules ?A" "length qs = Suc (length ss + length ts)" and
    eps: "q' = CInl p \<or> (q', CInl p) |\<in>| (eps ?A)|\<^sup>+|" and
    reach: "\<forall> i <  Suc (length ss + length ts). qs ! i |\<in>| ta_der ?A ((ss @ C\<langle>Var (CInl q)\<rangle> # ts) ! i)"
    by auto
  from eps obtain q'' where [simp]: "q' = CInl q''"
    by (cases q') (auto simp add: Inf_automata_def eps_split elim: ftranclE converse_ftranclE)
  from rule obtain qs' where args: "qs = map CInl qs'" "f qs' \<rightarrow> q'' |\<in>| rules \<A>"
    using r_rhs_CInl_args_A_rule by (metis \<open>q' = CInl q''\<close>)
  then have "CInl (qs' ! length ss) |\<in>| ta_der (Inf_automata \<A> Q) C\<langle>Var (CInl q)\<rangle>" using reach
    by (auto simp: all_Suc_conv nth_append_Cons) (metis length_map less_add_Suc1 local.rule(2) nth_append_length nth_map reach) 
  from More(1)[OF this] More(2) show ?case
    using rule args eps reach A_rule_to_dash_closure[OF args(2), of "length ss" Q]
    by (auto simp: Inl_eps_Inr id_take_nth_drop all_Suc_conv
        intro!: exI[of _ "CInr q''"] exI[of _ "map CInl (take (length ss) qs') @ CInr (qs' ! length ss) # map CInl (drop (Suc (length ss)) qs')"])
      (auto simp: nth_append_Cons min_def)
qed (auto simp: Inf_automata_def)

lemma Inf_automata_dashI:
  assumes "run \<A> r (gterm_to_None_Some t)" and "ex_rule_state r |\<in>| Q"
  shows "CInr (ex_rule_state r) |\<in>| gta_der (Inf_automata \<A> Q) (gterm_to_None_Some t)"
proof (cases t)
  case [simp]: (GFun f ts)
  from run_root_rule[OF assms(1)] run_argsD[OF assms(1)] have
    rule: "TA_rule (None, Some f) (map ex_comp_state (gargs r)) (ex_rule_state r) |\<in>| rules \<A>" "length (gargs r) = length ts" and
    reach: "\<forall> i < length ts. ex_comp_state (gargs r ! i) |\<in>| ta_der \<A> (term_of_gterm (gterm_to_None_Some (ts  ! i)))"
    by (auto intro!: run_to_comp_st_gta_der[unfolded gta_der_def comp_def])
  from rule assms(2) have "(None, Some f) (map (CInl \<circ> ex_comp_state) (gargs r)) \<rightarrow> CInr (ex_rule_state r) |\<in>| rules  (Inf_automata \<A> Q)"
    apply (simp add: Inf_automata_def image_iff bex_Un)
    apply (rule disjI1)
    by force
  then show ?thesis using reach rule Inl_res_A_res_Inf_automata[of \<A> "gterm_to_None_Some (ts ! i)" Q for i]
    by (auto simp: gta_der_def intro!: exI[of _ "CInr (ex_rule_state r)"]  exI[of _ "map (CInl \<circ> ex_comp_state) (gargs r)"])
        blast
qed

lemma Inf_automata_dash_reach_to_reach:
  assumes "p |\<in>| ta_der (Inf_automata \<A> Q) t" (is "_ |\<in>| ta_der ?A _")
  shows "remove_sum p |\<in>| ta_der \<A> (map_vars_term remove_sum t)" using assms
proof (induct t arbitrary: p)
  case (Var x) then show ?case
    by (cases p; cases x) (auto simp: Inf_automata_def ftrancl_map_both map_both_ftrancl_conv)
next
  case (Fun f ss)
  from Fun(2) obtain qs q' where
    rule: "f qs \<rightarrow> q' |\<in>| rules ?A" "length qs = length ss" and
    eps: "q' = p \<or> (q', p) |\<in>| (eps ?A)|\<^sup>+|" and
    reach: "\<forall> i <  length ss. qs ! i |\<in>| ta_der ?A (ss ! i)" by auto
  from rule have r: "f (map (remove_sum) qs) \<rightarrow> (remove_sum q') |\<in>| rules \<A>"
    by (auto simp: comp_def Inf_automata_def min_def id_take_nth_drop[symmetric] upt_fset
             simp flip: drop_map take_map split!: if_splits)
  moreover have "remove_sum q' = remove_sum p \<or> (remove_sum q', remove_sum p) |\<in>| (eps \<A>)|\<^sup>+|" using eps
    by (cases "is_Inl q'"; cases "is_Inl p") (auto elim!: is_InlE is_InrE, auto simp: Inf_automata_def)
  ultimately show ?case using reach rule(2) Fun(1)[OF nth_mem, of i "qs ! i" for i]
    by auto (metis (mono_tags, lifting) length_map map_nth_eq_conv)+
qed

lemma depth_poss_split:
  assumes "Suc (depth (term_of_gterm t) + n) < depth (term_of_gterm u)"
  shows "\<exists> p q. p @ q \<in> gposs u \<and> n < length q \<and> p \<notin> gposs t"
proof -
  from poss_length_depth obtain p m where p: "p \<in> gposs u" "length p = m" "depth (term_of_gterm u) = m"
    using poss_gposs_conv by blast
  then obtain m' where dt: "depth (term_of_gterm t) = m'" by blast
  from assms dt p(2, 3) have "length (take (Suc m') p) = Suc m'"
    by (metis Suc_leI depth_gterm_conv length_take less_add_Suc1 less_imp_le_nat less_le_trans min.absorb2)
  then have nt: "take (Suc m') p \<notin> gposs t" using poss_length_bounded_by_depth dt depth_gterm_conv
    by (metis Suc_n_not_le_n gposs_to_poss)
  moreover have "n < length (drop (Suc m') p)" using assms depth_gterm_conv dt p(2-)
    by (metis add_Suc diff_diff_left length_drop zero_less_diff) 
  ultimately show ?thesis by (metis append_take_drop_id p(1))
qed

lemma Inf_to_automata:
  assumes "RR2_spec \<A> \<R>" and "t \<in> Inf_branching_terms \<R> \<F>"
  shows "\<exists> u. gpair t u \<in> \<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>))" (is "\<exists> u. gpair t u \<in> \<L> ?B")
proof -
  let ?A = "Inf_automata (ta \<A>) (Q_infty (ta \<A>) \<F>)"
  let ?t_of_g = "\<lambda> t. term_of_gterm t :: ('b, 'a) term"
  obtain n where depth_card: "depth (?t_of_g t) + fcard (\<Q> (ta \<A>)) < n" by auto
  from assms(1, 2) have fin: "infinite {u. gpair t u \<in> \<L> \<A> \<and> funas_gterm u \<subseteq> fset \<F>}"
    by (auto simp: RR2_spec_def Inf_branching_terms_def)
  from infinte_no_depth_limit[of "?t_of_g ` {u. gpair t u \<in> \<L> \<A> \<and> funas_gterm u \<subseteq> fset \<F>}" "fset \<F>"] this
  have "\<forall> n. \<exists>t \<in> ?t_of_g ` {u. gpair t u \<in> \<L> \<A> \<and> funas_gterm u \<subseteq> fset \<F>}. n < depth t"
    by (simp add: infinite_inj_image_infinite[OF fin] funas_term_of_gterm_conv inj_term_of_gterm)
  from this depth_card obtain u where funas: "funas_gterm u \<subseteq> fset \<F>" and
    depth: "Suc n < depth (?t_of_g u)" and lang: "gpair t u \<in> \<L> \<A>" by auto
  have "Suc (depth (term_of_gterm t) + fcard (\<Q> (ta \<A>))) < depth (term_of_gterm u)"
    using depth depth_card by (metis Suc_less_eq2 depth_gterm_conv less_trans)
  from depth_poss_split[OF this] obtain p q where
    pos: "p @ q \<in> gposs u" "p \<notin> gposs t" and card: "fcard (\<Q> (ta \<A>)) < length q" by auto
  then have gp: "gsubt_at (gpair t u) p = gterm_to_None_Some (gsubt_at u p)"
    using subst_at_gpair_nt_poss_None_Some[of p] by force
  from lang obtain r where r: "run (ta \<A>) r (gpair t u)" "ex_comp_state r |\<in>| fin \<A>"
    unfolding \<L>_def gta_lang_def by (fastforce dest: gta_der_to_run)
  from pos have p_gtu: "p \<in> gposs (gpair t u)" and pu: "p \<in> gposs u"
    using not_gposs_append by auto
  have qinf: "ex_rule_state (gsubt_at r p) |\<in>| Q_infty (ta \<A>) \<F>"
    using funas_gterm_gsubt_at_subseteq[OF pu] funas card
    unfolding Q_infty_fmember gta_der_def[symmetric]
    by (intro infinite_super[THEN infinite_imageD2[OF _ inj_gterm_to_None_Some],
     OF _ pigeonhole_ta_infinit_terms[of "ta \<A>" "gsubt_at (gpair t u) p" _
     "\<lambda> t. t \<subseteq> (\<lambda>(f, n). ((None, Some f), n)) ` fset \<F>",
     OF _ run_to_gta_der_gsubt_at(1)[OF r(1) p_gtu]]])
        (auto simp: poss_length_bounded_by_depth[of q] image_iff gp less_le_trans
                   pos(1) poss_gposs_conv pu dest!: funas_gterm_bot_some_decomp)
  from Inf_automata_dashI[OF run_gsubt_cl[OF r(1) p_gtu, unfolded gp] qinf]
  have dashI: "CInr (ex_rule_state (gsubt_at r p)) |\<in>| gta_der (Inf_automata (ta \<A>) (Q_infty (ta \<A>) \<F>)) (gsubt_at (gpair t u) p)"
    unfolding gp[symmetric] .
  have "CInl (ex_comp_state r) |\<in>| ta_der ?A (ctxt_at_pos (term_of_gterm (gpair t u)) p)\<langle>Var (CInl (ex_rule_state (gsubt_at r p)))\<rangle>"
    using ta_der_fmap_states_ta[OF run_ta_der_ctxt_split2[OF r(1) p_gtu], of CInl, THEN fsubsetD[OF Inl_A_res_Inf_automata]]
    unfolding replace_term_at_replace_at_conv[OF gposs_to_poss[OF p_gtu]]
    by (auto simp: gterm.map_ident simp flip: map_term_replace_at_dist[OF gposs_to_poss[OF p_gtu]])
  from ta_der_ctxt[OF dashI[unfolded gta_der_def] Inf_automata_reach_to_dash_reach[OF this]]
  have "CInr (ex_comp_state r) |\<in>| gta_der (Inf_automata (ta \<A>) (Q_infty (ta \<A>) \<F>)) (gpair t u)"
    unfolding replace_term_at_replace_at_conv[OF gposs_to_poss[OF p_gtu]]
    unfolding replace_gterm_conv[OF p_gtu]
    by (auto simp: gta_der_def)
  moreover from r(2) have "CInr (ex_comp_state r) |\<in>| fin (Inf_reg \<A> (Q_infty (ta \<A>) \<F>))"
    by (auto simp: Inf_reg_def)
  ultimately show ?thesis using r(2)
    by (auto simp: \<L>_def gta_der_def Inf_reg_def intro: exI[of _ u])
qed

lemma CInr_Inf_automata_to_q_state:
  assumes "CInr p |\<in>| ta_der (Inf_automata \<A> Q) t" and "ground t"
  shows "\<exists> C s q. C\<langle>s\<rangle> = t \<and> CInr q |\<in>| ta_der (Inf_automata \<A> Q) s \<and> q |\<in>| Q \<and>
    CInr p |\<in>| ta_der (Inf_automata \<A> Q) C\<langle>Var (CInr q)\<rangle> \<and>
    (fst \<circ> fst \<circ> the \<circ> root) s = None" using assms
proof (induct t arbitrary: p)
  case (Fun f ts)
  let ?A = "(Inf_automata \<A> Q)"
  from Fun(2) obtain qs q' where
    rule: "f qs \<rightarrow> CInr q' |\<in>| rules ?A" "length qs = length ts" and
    eps: "q' = p \<or> (CInr q', CInr p) |\<in>| (eps ?A)|\<^sup>+|" and
    reach: "\<forall> i < length ts. qs ! i |\<in>| ta_der ?A (ts ! i)"
    by auto (metis Inr_rhs_eps_Inr_lhs)
  consider (a) "\<And> i. i < length qs \<Longrightarrow> \<exists> q''. qs ! i = CInl q''" | (b) "\<exists> i < length qs. \<exists> q''. qs ! i = CInr q''"
    by (meson remove_sum.cases)
  then show ?case
  proof cases
    case a
    then have "f qs \<rightarrow> CInr q' |\<in>| |\<Union>| (q_inf_dash_intro_rules Q |`| rules \<A>)" using rule
      by (auto simp: Inf_automata_def min_def upt_fset split!: if_splits)
         (metis (no_types, lifting) Inl_Inr_False Suc_pred append_eq_append_conv id_take_nth_drop
               length_Cons length_drop length_greater_0_conv length_map
               less_nat_zero_code list.size(3) nth_append_length rule(2))
   then show ?thesis using reach eps rule
     by (intro exI[of _ Hole] exI[of _ "Fun f ts"] exI[of _ q'])
         (auto split!: if_splits)
  next
    case b
    then obtain i q'' where b: "i < length ts" "qs ! i = CInr q''" using rule(2) by auto
    then have "CInr q'' |\<in>| ta_der ?A (ts ! i)" using rule(2) reach by auto 
    from Fun(3) Fun(1)[OF nth_mem, OF b(1) this] b rule(2) obtain C s q''' where
      ctxt: "C\<langle>s\<rangle> = ts ! i" and
      qinf: "CInr q''' |\<in>| ta_der (Inf_automata \<A> Q) s \<and> q''' |\<in>| Q" and
      reach2: "CInr q'' |\<in>| ta_der (Inf_automata \<A> Q) C\<langle>Var (CInr q''')\<rangle>" and
      "(fst \<circ> fst \<circ> the \<circ> root) s = None"
      by auto
    then show ?thesis using rule eps reach ctxt qinf reach2 b(1) b(2)[symmetric]
      by (auto simp: min_def nth_append_Cons simp flip: map_append id_take_nth_drop[OF b(1)]
        intro!: exI[of _ "More f (take i ts) C (drop (Suc i) ts)"] exI[of _ "s"] exI[of _ "q'''"] exI[of _ "CInr q'"] exI[of _ "qs"])
  qed
qed auto

lemma aux_lemma:
  assumes "RR2_spec \<A> \<R>" and "\<R> \<subseteq> \<T>\<^sub>G (fset \<F>) \<times> \<T>\<^sub>G (fset \<F>)"
    and "infinite {u | u. gpair t u \<in> \<L> \<A>}"
  shows "t \<in> Inf_branching_terms \<R> \<F>"
proof -
  from assms have [simp]: "gpair t u \<in> \<L> \<A> \<longleftrightarrow> (t, u) \<in> \<R> \<and> u \<in> \<T>\<^sub>G (fset \<F>)"
    for u by (auto simp: RR2_spec_def)
  from assms have "t \<in> \<T>\<^sub>G (fset \<F>)" unfolding RR2_spec_def
    by (auto dest: not_finite_existsD)
  then show ?thesis using assms unfolding Inf_branching_terms_def
    by (auto simp: \<T>\<^sub>G_equivalent_def)
qed

lemma Inf_automata_to_Inf:
  assumes "RR2_spec \<A> \<R>" and "\<R> \<subseteq> \<T>\<^sub>G (fset \<F>) \<times> \<T>\<^sub>G (fset \<F>)"
    and "gpair t u \<in> \<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>))"
  shows "t \<in> Inf_branching_terms \<R> \<F>"
proof -
  let ?con = "\<lambda> t. term_of_gterm (gterm_to_None_Some t)"
  let ?A = "Inf_automata (ta \<A>) (Q_infty (ta \<A>) \<F>)"
  from assms(3) obtain q where fin: "q |\<in>| fin \<A>" and
    reach_fin: "CInr q |\<in>| ta_der ?A (term_of_gterm (gpair t u))"
    by (auto simp: Inf_reg_def \<L>_def Inf_automata_def elim!: gta_langE)
  from CInr_Inf_automata_to_q_state[OF reach_fin] obtain C s p where
    ctxt: "C\<langle>s\<rangle> = term_of_gterm (gpair t u)" and
    q_inf_st: "CInr p |\<in>| ta_der ?A s" "p |\<in>| Q_infty (ta \<A>) \<F>" and
    reach: "CInr q |\<in>| ta_der ?A C\<langle>Var (CInr p)\<rangle>" and
    none: "(fst \<circ> fst \<circ> the \<circ> root) s = None" by auto
  have gr: "ground s" "ground_ctxt C" using arg_cong[OF ctxt, of ground]
    by auto
  have reach: "q |\<in>| ta_der (ta \<A>) (adapt_vars_ctxt C)\<langle>Var p\<rangle>"
    using gr Inf_automata_dash_reach_to_reach[OF reach]
    by (auto simp: map_vars_term_ctxt_apply)
  from q_inf_st(2) have inf: "infinite {v. funas_gterm v \<subseteq> fset \<F> \<and> p |\<in>| ta_der (ta \<A>) (?con v)}"
    by (simp add: Q_infty_fmember)
  have inf: "infinite {v. funas_gterm v \<subseteq> fset \<F> \<and> q |\<in>| gta_der (ta \<A>) (gctxt_of_ctxt C)\<langle>gterm_to_None_Some v\<rangle>\<^sub>G}"
    using reach ground_ctxt_adapt_ground[OF gr(2)] gr
    by (intro infinite_super[OF _ inf], auto simp: gta_der_def)
       (smt (z3) adapt_vars_ctxt adapt_vars_term_of_gterm ground_gctxt_of_ctxt_apply_gterm ta_der_ctxt)
  have *: "gfun_at (gterm_of_term C\<langle>s\<rangle>) (hole_pos C) = gfun_at (gterm_of_term s) []"
    by (induct C) (auto simp: nth_append_Cons)
  from arg_cong[OF ctxt, of "\<lambda> t. gfun_at (gterm_of_term t) (hole_pos C)"] none
  have hp_nt: "ghole_pos (gctxt_of_ctxt C) \<notin> gposs t" unfolding ground_hole_pos_to_ghole[OF gr(2)]
    using gfun_at_gpair[of t u "hole_pos C"] gr *
    by (cases s) (auto simp flip: poss_gposs_mem_conv split: if_splits elim: gfun_at_possE)
  from gpair_ctxt_decomposition[OF hp_nt, of u "gsubt_at u (hole_pos C)"]
  have to_gpair: "gpair t (gctxt_at_pos u (hole_pos C))\<langle>v\<rangle>\<^sub>G = (gctxt_of_ctxt C)\<langle>gterm_to_None_Some v\<rangle>\<^sub>G" for v
    unfolding ground_hole_pos_to_ghole[OF gr(2)] using ctxt gr
    using subst_at_gpair_nt_poss_None_Some[OF _ hp_nt, of u]
    by (metis (no_types, lifting) UnE \<open>ghole_pos (gctxt_of_ctxt C) = hole_pos C\<close>
        gposs_of_gpair gsubt_at_gctxt_apply_ghole hole_pos_in_ctxt_apply hp_nt poss_gposs_conv term_of_gterm_ctxt_apply)
  have inf: "infinite {v. gpair t ((gctxt_at_pos u (hole_pos C))\<langle>v\<rangle>\<^sub>G) \<in> \<L> \<A>}" using fin
    by (intro infinite_super[OF _ inf]) (auto simp: \<L>_def gta_der_def simp flip: to_gpair)
  have "infinite {u |u. gpair t u \<in> \<L> \<A>}"
    by (intro infinite_super[OF _ infinite_inj_image_infinite[OF inf gctxt_apply_inj_on_term[of "gctxt_at_pos u (hole_pos C)"]]])
       (auto simp: image_def intro: infinite_super)
  then show ?thesis using assms(1, 2)
    by (intro aux_lemma[of \<A>]) simp
qed

lemma Inf_automata_subseteq:
  "\<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>)) \<subseteq> \<L> \<A>" (is "\<L> ?IA \<subseteq> _")
proof
  fix s assume l: "s \<in> \<L> ?IA"
  then obtain q where w: "q |\<in>| fin ?IA" "q |\<in>| ta_der (ta ?IA) (term_of_gterm s)"
    by (auto simp: \<L>_def elim!: gta_langE)
  from w(1) have "remove_sum q |\<in>| fin \<A>"
    by (auto simp: Inf_reg_def Inf_automata_def)
  then show "s \<in> \<L> \<A>" using Inf_automata_dash_reach_to_reach[of q "ta \<A>"] w(2)
    by (auto simp: gterm.map_ident \<L>_def Inf_reg_def)
       (metis gta_langI map_vars_term_term_of_gterm)
qed

lemma \<L>_Inf_reg:
  assumes "RR2_spec \<A> \<R>" and "\<R> \<subseteq> \<T>\<^sub>G (fset \<F>) \<times> \<T>\<^sub>G (fset \<F>)"
  shows "gfst ` \<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>)) = Inf_branching_terms \<R> \<F>"
proof -
  {fix s assume ass: "s \<in> \<L> (Inf_reg \<A> (Q_infty (ta \<A>) \<F>))"
    then have "\<exists> t u. s = gpair t u" using Inf_automata_subseteq[of \<A> \<F>] assms(1)
      by (auto simp: RR2_spec_def)
    then have "gfst s \<in> Inf_branching_terms \<R> \<F>"
      using ass Inf_automata_to_Inf[OF assms]
      by (force simp: gfst_gpair)}
  then show ?thesis using Inf_to_automata[OF assms(1), of _ \<F>]
    by (auto simp: gfst_gpair) (metis gfst_gpair image_iff)
qed
end