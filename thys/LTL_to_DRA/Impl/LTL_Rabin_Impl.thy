(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Executable Translation from LTL to Rabin Automata\<close>

theory LTL_Rabin_Impl
  imports Main "../Aux/Map2" "../Aux/AList_Mapping2" "../LTL_Rabin" LTL_Impl Mojmir_Rabin_Impl
begin

subsection \<open>Simple FG-case\<close>

fun ltl_FG_to_rabin_exec (* Not exported *)
where
  "ltl_FG_to_rabin_exec \<Sigma> \<phi> \<G> = mojmir_to_rabin_exec \<Sigma> \<up>af\<^sub>G (Abs \<phi>) (\<lambda>\<psi>. \<G> \<up>\<Turnstile>\<^sub>P \<psi>)"

subsection \<open>General Case\<close>

subsubsection \<open>Automaton Definition\<close>

fun initial
where
  "initial \<phi> = (Abs \<phi>, Mapping.tabulate (G_list \<phi>) (init o Abs o theG))"

fun delta
where
  "delta \<Sigma> = \<up>af \<times> \<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<up>af\<^sub>G o Abs o theG)"

fun reachable_transitions
where
  "reachable_transitions \<Sigma> \<phi> = DTS.reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)"

definition max_rank_of
where
  "max_rank_of \<Sigma> \<psi> \<equiv> semi_mojmir_def.max_rank (set \<Sigma>) \<up>af\<^sub>G (Abs \<psi>)"

definition mappings :: "'a set list \<Rightarrow> 'a ltl \<Rightarrow> ('a ltl, nat) mapping set"
where
  "mappings \<Sigma> \<phi> \<equiv> {\<pi>. Mapping.keys \<pi> \<subseteq> \<^bold>G \<phi> \<and> (\<forall>\<chi> \<in> (Mapping.keys \<pi>). the (Mapping.lookup \<pi> \<chi>) < max_rank_of \<Sigma> (theG \<chi>))}"

fun M_fin_filter_exec :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl\<^sub>P \<times> (('a ltl, ('a ltl\<^sub>P list)) mapping), 'a set) transition \<Rightarrow> bool"
where
  "M_fin_filter_exec \<phi> \<pi> ((\<phi>', m'), _) = (
    let
      m = Mapping.lookup m';
      \<G> = Mapping.keys \<pi>;
      \<G>\<^sub>L = filter (\<lambda>x. x \<in> \<G>) (G_list \<phi>)
    in
      Not ((\<up>And ((map Abs \<G>\<^sub>L) @ (map (\<up>eval\<^sub>G \<G>) (foldl (op @) [] (map (\<lambda>\<chi>. drop (the (Mapping.lookup \<pi> \<chi>)) (the (m \<chi>))) \<G>\<^sub>L))))) \<up>\<longrightarrow>\<^sub>P  \<phi>'))"

fun Acc_fin_filter_exec
where
  "Acc_fin_filter_exec \<Sigma> \<pi> \<chi> ((_, m'), \<nu>, _) = (
    let 
      t = (the (Mapping.lookup m' \<chi>), \<nu>, []); (* Third element is unused. Hence it is safe to pass dummy value. *)
      \<G> = Mapping.keys \<pi>
    in 
      fail_filt \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs \<G>) t 
    \<or> merge_filt \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs \<G>) (the (Mapping.lookup \<pi> \<chi>)) t)"

fun Acc_inf_filter_exec
where
  "Acc_inf_filter_exec \<pi> \<chi> ((_, m'), \<nu>, _) = (
    let 
      t = (the (Mapping.lookup m' \<chi>), \<nu>, []); (* Third element is unused. Hence it is safe to pass dummy value. *)
      \<G> = Mapping.keys \<pi>
    in 
      succeed_filt \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs \<G>) (the (Mapping.lookup \<pi> \<chi>)) t)"

fun ltl_to_rabin_exec
where
  "ltl_to_rabin_exec \<Sigma> \<phi> = (
    let
      \<delta>_LTS = reachable_transitions \<Sigma> \<phi>; 
      \<alpha>_fin_filter = \<lambda>\<pi> t. M_fin_filter_exec \<phi> \<pi> t \<or> (\<exists>\<chi> \<in> Mapping.keys \<pi>. Acc_fin_filter_exec (set \<Sigma>) \<pi> \<chi> t);
      to_pair = \<lambda>\<pi>. (Set.filter (\<alpha>_fin_filter \<pi>) \<delta>_LTS, (\<lambda>\<chi>. Set.filter (Acc_inf_filter_exec \<pi> \<chi>) \<delta>_LTS) ` Mapping.keys \<pi>);
      \<alpha> = to_pair ` (mappings \<Sigma> \<phi>) (* Multi-thread here! *)
    in
      (\<delta>_LTS, initial \<phi>, \<alpha>))"

subsubsection \<open>Correctness Proof\<close>

fun abstract_state :: "'a \<times> ('b, 'c list) mapping \<Rightarrow> 'a \<times> ('b \<rightharpoonup> 'c \<rightharpoonup> nat)" 
where
  "abstract_state (a, b) = (a, (map_option rk) o (Mapping.lookup b))"

fun abstract_transition
where
  "abstract_transition (q, \<nu>, q') = (abstract_state q, \<nu>, abstract_state q')"

lemma finite_\<Delta>:
  "finite (reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>))"
proof (cases "\<Sigma> \<noteq> []")
  case True
    have "finite (reach (set \<Sigma>) \<up>af (Abs \<phi>))"
      by (simp add: finite_reach_af)
    moreover
    have R: "range (\<lambda>_. hd \<Sigma>) \<subseteq> set \<Sigma>"
      using True by auto
    have "(\<And>x. x \<in> \<^bold>G \<phi> \<Longrightarrow> finite (reach (set \<Sigma>) ((nxt (set \<Sigma>) \<up>af\<^sub>G o Abs o theG) x) ((init o Abs o theG) x)))"
      using semi_mojmir.finite_Q[OF ltl_semi_mojmir[OF finite_set], OF R] unfolding G_eq_G_list semi_mojmir_def.Q\<^sub>E_def by simp 
    hence "finite (reach (set \<Sigma>) (\<up>\<Delta>\<^sub>\<times> (nxt (set \<Sigma>) \<up>af\<^sub>G o Abs o theG)) (Mapping.tabulate (G_list \<phi>) (init o Abs o theG)))"
      by (metis (no_types) finite_reach_product_abs[OF finite_keys_tabulate] G_eq_G_list  keys_tabulate lookup_tabulate_Some)
    ultimately
    have "finite (reach (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>))"
      using finite_reach_simple_product semi_mojmir.finite_Q ltl_semi_mojmir[OF finite_set] by fastforce 
    thus ?thesis
      by (simp add: finite_reach\<^sub>t) 
qed (simp add: reach\<^sub>t_def) 

lemma reach_delta_initial:
  assumes "(x, y) \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
  assumes "\<chi> \<in> \<^bold>G \<phi>"
  shows "Mapping.lookup y \<chi> \<noteq> None" (is ?t1)
    and "distinct (the (Mapping.lookup y \<chi>))" (is ?t2)
proof -
  from assms(1) obtain w i where y_def: "y = run (\<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<up>af\<^sub>G o Abs o theG)) (Mapping.tabulate (G_list \<phi>) (init o Abs o theG)) w i"
    unfolding reach_def delta.simps initial.simps simple_product_run by fast
  from assms(2) nxt_run_distinct show ?t1 
    unfolding y_def using product_abs_run_Some[of "(Mapping.tabulate (G_list \<phi>) (init o Abs o theG))" \<chi>] unfolding G_eq_G_list 
    unfolding lookup_tabulate by fastforce
  with nxt_run_distinct show ?t2
    unfolding y_def using lookup_tabulate  
    by (metis (no_types) G_eq_G_list assms(2) comp_eq_dest_lhs option.sel product_abs_run_Some) 
qed

lemma run_abstraction_correct:
  assumes "range w \<subseteq> \<Sigma>"
  assumes "finite \<Sigma>"
  fixes \<phi>
  defines "\<delta> \<equiv> \<delta>\<^sub>\<A> \<Sigma>"
  defines "q\<^sub>0 \<equiv> \<iota>\<^sub>\<A> \<phi>"
  shows "run \<delta> q\<^sub>0 w = abstract_state o (run (delta \<Sigma>) (initial \<phi>) w)"
proof -
  {
    fix i
 
    let ?\<delta>\<^sub>2 = "\<Delta>\<^sub>\<times> (\<lambda>\<chi>. ltl_FG_to_rabin_def.\<delta>\<^sub>R \<Sigma> (theG \<chi>))"    
    let ?q\<^sub>2 = "\<iota>\<^sub>\<times> (\<^bold>G \<phi>) (\<lambda>\<chi>. ltl_FG_to_rabin_def.q\<^sub>R (theG \<chi>))"
 
    let ?\<delta>\<^sub>2' = "\<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<up>af\<^sub>G o Abs o theG)"    
    let ?q\<^sub>2' = "Mapping.tabulate (G_list \<phi>) (init o Abs o theG)"
    
    have sm: "\<And>\<psi>. semi_mojmir \<Sigma> \<up>af\<^sub>G (Abs \<psi>) w"
    proof 
      fix \<psi>
      have nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
        using assms by auto
      show "finite (reach \<Sigma> \<up>af\<^sub>G (Abs \<psi>))" (is "finite ?A")
        using af_G_abs.finite_abs_reach finite_subset[where A = ?A, where B = "lift_ltl_transformer.abs_reach af_G_letter (Abs \<psi>)"]
        unfolding af_G_abs.abs_reach_def af_G_letter_abs_def reach_foldl_def[OF nonempty_\<Sigma>] by blast
    qed (insert assms, auto)

    {
      fix q
      assume "q \<notin> \<^bold>G \<phi>"
      hence "?q\<^sub>2 q = None" and "Mapping.lookup (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q = None"
        using G_eq_G_list product_abs_run_None by (simp, metis domIff keys_dom_lookup keys_tabulate)
      hence "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i q = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q"
        using product_run_None by (simp del: nxt.simps rk.simps)
    }

    moreover 

    {
      fix q j
      assume "q \<in> \<^bold>G \<phi>"
      hence init: "?q\<^sub>2 q = Some (semi_mojmir_def.initial (Abs (theG q)))" 
        and "Mapping.lookup (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q = Some (run ((nxt \<Sigma> \<up>af\<^sub>G \<circ> Abs \<circ> theG) q) ((init \<circ> Abs \<circ> theG) q) w i)"
        unfolding G_eq_G_list by (simp, metis (no_types, lifting) G_eq_G_list `q \<in> \<^bold>G \<phi>` lookup_tabulate product_abs_run_Some)
      hence "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i q = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q"
        unfolding product_run_Some[of "\<iota>\<^sub>\<times> (\<^bold>G \<phi>) (\<lambda>\<chi>. semi_mojmir_def.initial (Abs (theG \<chi>)))" q, OF init] 
        by (simp del: product.simps nxt.simps rk.simps; unfold map_of_map semi_mojmir.nxt_run_step_run[OF sm]; simp) 
    }

    ultimately

    have "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i)"
      by blast
  }
  hence "\<And>i. run \<delta> q\<^sub>0 w i = abstract_state (run (delta \<Sigma>) (initial \<phi>) w i)"
    by (simp add: simple_product_run assms del: simple_product.simps)
  thus ?thesis
    by auto
qed

lemma Acc_fin_filter_correct:
  assumes "((x, y), \<nu>, (z, z')) \<in> reach\<^sub>t \<Sigma> (delta \<Sigma>) (initial \<phi>)"
  assumes "\<chi> \<in> \<^bold>G \<phi>"
  shows "(abstract_state (x, y), \<nu>, abstract_state (z, z')) \<in> fst (Acc \<Sigma> (Mapping.lookup \<pi>) \<chi>) = Acc_fin_filter_exec \<Sigma> \<pi> \<chi> ((x, y), \<nu>, (z, z'))"
proof -
  have "(x, y) \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    and "(z, z') \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    using assms(1) unfolding reach\<^sub>t_def reach_def run\<^sub>t.simps by blast+
  hence "Mapping.lookup y \<chi> \<noteq> None"
    and "Mapping.lookup z' \<chi> \<noteq> None"
    using assms(2) by (blast dest: reach_delta_initial)+

  have FF: "fail_filt \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs (Mapping.keys \<pi>)) (the (Mapping.lookup y \<chi>), \<nu>, []) 
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.fail\<^sub>R \<Sigma> \<up>af\<^sub>G (Abs (theG \<chi>)) {q. Mapping.keys \<pi> \<Turnstile>\<^sub>P Rep q})"
    unfolding option.map_sel[OF `Mapping.lookup y \<chi> \<noteq> None`] fail_filt_eq[where y = "[]", symmetric] by (simp add: ltl_prop_entails_abs.rep_eq)  

  have MF: "\<And>i. merge_filt \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs (Mapping.keys \<pi>)) i (the (Mapping.lookup y \<chi>), \<nu>, [])
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.merge\<^sub>R \<up>af\<^sub>G (Abs (theG \<chi>)) {q. Mapping.keys \<pi> \<Turnstile>\<^sub>P Rep q} i)"
    unfolding option.map_sel[OF `Mapping.lookup y \<chi> \<noteq> None`] merge_filt_eq[where y = "[]", symmetric] by (simp add: ltl_prop_entails_abs.rep_eq)  

  show ?thesis
    apply (unfold Acc_fin_filter_exec.simps Let_def FF MF)
    apply (simp add: mojmir_to_rabin_def.fail\<^sub>R_def mojmir_to_rabin_def.merge\<^sub>R_def map_of_map del: rk.simps) 
    apply (insert `Mapping.lookup z' \<chi> \<noteq> None` `Mapping.lookup y \<chi> \<noteq> None`)
    unfolding keys_dom_lookup[symmetric] by force
qed

lemma Acc_inf_filter_correct:
  assumes "((x, y), \<nu>, (z, z')) \<in> reach\<^sub>t \<Sigma> (delta \<Sigma>) (initial \<phi>)"
  assumes "\<chi> \<in> \<^bold>G \<phi>"
  shows "(abstract_state (x, y), \<nu>, abstract_state (z, z')) \<in> snd (Acc \<Sigma> (Mapping.lookup \<pi>) \<chi>) = Acc_inf_filter_exec \<pi> \<chi> ((x, y), \<nu>, (z, z'))"
proof -
  have "(x, y) \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    and "(z, z') \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    using assms(1) unfolding reach\<^sub>t_def reach_def run\<^sub>t.simps by blast+
  hence "Mapping.lookup y \<chi> \<noteq> None"
    and "Mapping.lookup z' \<chi> \<noteq> None"
    using assms(2) by (blast dest: reach_delta_initial)+

  have SF: "\<And>i. succeed_filt \<up>af\<^sub>G (Abs (theG \<chi>)) (ltl_prop_entails_abs (Mapping.keys \<pi>)) i (the (Mapping.lookup y \<chi>), \<nu>, [])
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.succeed\<^sub>R \<up>af\<^sub>G (Abs (theG \<chi>)) {q. Mapping.keys \<pi> \<Turnstile>\<^sub>P Rep q} i)"
    unfolding option.map_sel[OF `Mapping.lookup y \<chi> \<noteq> None`] succeed_filt_eq[where y = "[]", symmetric] by (simp add: ltl_prop_entails_abs.rep_eq)  

  show ?thesis
    apply (unfold Acc_inf_filter_exec.simps Let_def SF)
    apply (simp add: mojmir_to_rabin_def.succeed\<^sub>R_def map_of_map del: rk.simps) 
    apply (insert `Mapping.lookup z' \<chi> \<noteq> None` `Mapping.lookup y \<chi> \<noteq> None`)
    unfolding keys_dom_lookup[symmetric] by force
qed
  
lemma M_filter_correct:
  assumes "((x, y), \<nu>, (z, z')) \<in> reach\<^sub>t \<Sigma> (delta \<Sigma>) (initial \<phi>)"
  assumes "dom \<pi> \<subseteq> \<^bold>G \<phi>"
  assumes "\<And>\<chi>. \<chi> \<in> (dom \<pi>) \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R \<Sigma> (theG \<chi>)"
  shows "(abstract_state (x, y), \<nu>, abstract_state (z, z')) \<in> M_fin \<pi> = M_fin_filter_exec \<phi> (Mapping.Mapping \<pi>) ((x, y), \<nu>, (z, z'))"
proof -
  have "(x, y) \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    and "(z, z') \<in> reach \<Sigma> (delta \<Sigma>) (initial \<phi>)"
    using assms(1) unfolding reach\<^sub>t_def reach_def run\<^sub>t.simps by blast+
  hence N1: "\<And>\<chi>. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> Mapping.lookup y \<chi> \<noteq> None"
    and D1: "\<And>\<chi>. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> distinct (the (Mapping.lookup y \<chi>))"
    and N2: "\<And>\<chi>. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> Mapping.lookup z' \<chi> \<noteq> None"
    and D2: "\<And>\<chi>. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> distinct (the (Mapping.lookup z' \<chi>))"
    by (blast dest: reach_delta_initial)+

  {
    fix x P S
    assume "x \<in> dom \<pi>"
    hence "x \<in> \<^bold>G \<phi>"
      using assms(2) by blast
     
    have "(\<forall>q. (\<exists>j\<ge>the (\<pi> x). the (map_option rk (Mapping.lookup y x)) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)
        = (\<forall>q \<in> set (drop (the (\<pi> x)) (the (Mapping.lookup y x))). S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)"
      using D1[THEN drop_rk, symmetric, of x "the (\<pi> x)", OF `x \<in> \<^bold>G \<phi>`] unfolding option.map_sel[OF N1, OF `x \<in> \<^bold>G \<phi>`] by auto
  }
  hence FOLDER: "\<And>x P S. (x \<in> (dom \<pi>) \<longrightarrow> P \<and> (\<forall>q. (\<exists>j\<ge>the (\<pi> x). the (map_option rk (Mapping.lookup y x)) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)) 
     = (x \<in> (dom \<pi>) \<longrightarrow> P \<and> (\<forall>q \<in> (set (drop (the (\<pi> x)) (the (Mapping.lookup y x)))). S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q))"
    by presburger

  have rewrite: "\<And>xs y. ((\<up>And xs) \<up>\<longrightarrow>\<^sub>P y) = (\<forall>S. (\<forall>x \<in> set xs. (S \<up>\<Turnstile>\<^sub>P x)) \<longrightarrow> (S \<up>\<Turnstile>\<^sub>P y))" 
    unfolding And_prop_entailment_abs[symmetric] unfolding ltl_prop_entails_abs.rep_eq ltl_prop_implies_def[symmetric] ltl_prop_implies_abs.rep_eq by simp

  have G_dom_simp: "\<And>x P. (x \<in> \<^bold>G \<phi> \<and> x \<in> dom \<pi> \<and> P) = (x \<in> dom \<pi> \<and> P)"
      using assms by auto

  {
    fix S
    have "((\<forall>x. (\<exists>y. \<pi> x = Some y) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P Abs x \<and> (\<forall>q\<in>set (drop (the (\<pi> x)) (the (Mapping.lookup y x))). S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)) \<and> \<not> S \<up>\<Turnstile>\<^sub>P x) 
      = ((\<forall>x. ((\<exists>xa. xa \<in> dom \<pi> \<and> x = Abs xa) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P x) \<and> ((\<exists>ya. (\<exists>x. ya = set x \<and>
                          (\<exists>xa. xa \<in> dom \<pi> \<and> x = drop (the (\<pi> xa)) (the (Mapping.lookup y xa)))) \<and>
                     (\<exists>xa\<in>ya. x = \<up>eval\<^sub>G (dom \<pi>) xa)) \<longrightarrow>
               S \<up>\<Turnstile>\<^sub>P x)) \<and>
         \<not> S \<up>\<Turnstile>\<^sub>P x)" (is "?s1 = _") by blast
      
    also
    have "\<dots> = ((\<forall>x. ((\<exists>xa. xa \<in> \<^bold>G \<phi> \<and> xa \<in> dom \<pi> \<and> x = Abs xa) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P x) \<and> ((\<exists>ya. (\<exists>x. ya = set x \<and>
                          (\<exists>xa. xa \<in> \<^bold>G \<phi> \<and> xa \<in> dom \<pi> \<and> x = drop (the (\<pi> xa)) (the (Mapping.lookup y xa)))) \<and>
                     (\<exists>xa\<in>ya. x = \<up>eval\<^sub>G (dom \<pi>) xa)) \<longrightarrow>
               S \<up>\<Turnstile>\<^sub>P x)) \<and>
         \<not> S \<up>\<Turnstile>\<^sub>P x)" (is "_ = ?sn")
         unfolding G_dom_simp by simp
     finally
     have "?s1 = ?sn"
       by blast
  }
  note lastStep = this

  show ?thesis
    apply (simp add: image_def ltl_prop_implies_def G_eq_G_list[symmetric] del: rk.simps not_all And_abs.simps) 
    unfolding rewrite Ball_def set_append set_map set_foldl_append G_eq_G_list[symmetric]
    apply (simp del: rk.simps)  
    unfolding case_prod_beta option.case_eq_if G_eq_G_list[symmetric]
    unfolding map_of_map comp_def FOLDER G_eq_G_list[symmetric]
    unfolding image_def G_eq_G_list[symmetric] keys_dom_lookup domIff Mapping.lookup.abs_eq
    apply (simp add: Let_def)
    using lastStep by simp  
qed 

theorem ltl_to_rabin_exec_correct:
  assumes "range w \<subseteq> set \<Sigma>"
  shows "w \<Turnstile> \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltl_to_rabin_exec \<Sigma> \<phi>) w" 
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have ERSTER: "?lhs \<longleftrightarrow> accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin (set \<Sigma>) \<phi>) w" (is "_ \<longleftrightarrow> ?l1")
    by (meson assms List.finite_set ltl_to_generalised_rabin_correct)
 
  let ?q\<^sub>0' = "initial \<phi>"
  let ?\<delta>' = "delta (set \<Sigma>)"

  {
    fix \<pi>
    assume \<pi>_wellformed: "dom \<pi> \<subseteq> \<^bold>G \<phi>"
      "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R (set \<Sigma>) (theG \<chi>)"
       
    let ?q\<^sub>0 = "\<iota>\<^sub>\<A> \<phi>"
    let ?\<delta> = "ltl_to_generalised_rabin_transition_function (set \<Sigma>)"
    let ?F = "(M_fin \<pi> \<union> \<Union>{Acc_fin (set \<Sigma>) \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf (set \<Sigma>) \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>})"

    let ?fin = "{t. M_fin_filter_exec \<phi> (Mapping.Mapping \<pi>) t} \<union> {t. \<exists>\<chi> \<in> dom \<pi>. Acc_fin_filter_exec (set \<Sigma>) (Mapping.Mapping \<pi>) \<chi> t}"
    let ?inf = "{{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} | \<chi>. \<chi> \<in> dom \<pi>}"
    let ?F' = "(?fin, ?inf)"

    let ?reach' = "reach\<^sub>t (set \<Sigma>) ?\<delta>' ?q\<^sub>0'"

    have F1: "finite (reach\<^sub>t (set \<Sigma>) ?\<delta> ?q\<^sub>0)"
      by (meson List.finite_set finite_reach\<^sub>t ltl_to_generalised_rabin_wellformed)
 
    have R: "run ?\<delta> ?q\<^sub>0 w = abstract_state o (run ?\<delta>' ?q\<^sub>0' w)"
      using run_abstraction_correct[OF assms] by simp

    {
      fix q \<nu> p
      assume "(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)"
      hence 1: "((fst q, snd q), \<nu>, (fst p, snd p)) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)"
        by simp
      have "((abstract_state q, \<nu>, abstract_state p) \<in> (M_fin \<pi> \<union> \<Union>{Acc_fin (set \<Sigma>) \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>})) =
     ((q, \<nu>, p) \<in> fst ({t. M_fin_filter_exec \<phi> (Mapping.Mapping \<pi>) t} \<union> {t. \<exists>\<chi>\<in> dom \<pi>. Acc_fin_filter_exec (set \<Sigma>) (Mapping.Mapping \<pi>) \<chi> t},
              {{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} |\<chi>. \<chi> \<in> dom \<pi>}))"
      using M_filter_correct[OF 1 \<pi>_wellformed] Acc_fin_filter_correct[OF 1, of _ "Mapping.Mapping \<pi>"] 1 `dom \<pi> \<subseteq> \<^bold>G \<phi>` 
      unfolding fst_conv snd_conv unfolding pair_collapse Mapping.lookup.abs_eq by blast
    }
    note FIN = this

    {
      fix I :: "('a ltl\<^sub>P \<times> ('a ltl \<Rightarrow> ('a ltl\<^sub>P \<Rightarrow> nat option) option), 'a set) transition set"
      assume "I \<in> {Acc_inf (set \<Sigma>) \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}"
      then obtain \<chi> where I'_def: "I = Acc_inf (set \<Sigma>) \<pi> \<chi>" and "\<chi> \<in> dom \<pi>"
        by auto
      
      have "\<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> I) = ((q, \<nu>, p) \<in> Collect (Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi>))"
        using Acc_inf_filter_correct[OF _ subsetD[OF `dom \<pi> \<subseteq> \<^bold>G \<phi>`], of _ _ _ _ _ "set \<Sigma>" _ "Mapping.Mapping \<pi>", OF _ `\<chi> \<in> dom \<pi>`]  
        unfolding combine_pairs.simps fst_conv snd_conv image_Un 
        unfolding pair_collapse Mapping.lookup.abs_eq  I'_def by fast
      hence "\<exists>I'\<in>{Collect (Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi>) |\<chi>. \<chi> \<in> dom \<pi>}.
        \<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> I) = ((q, \<nu>, p) \<in> I')"
          using  `\<chi> \<in> dom \<pi>` by blast    
    }
    hence INF1: "\<forall>I\<in> {Acc_inf (set \<Sigma>) \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}. \<exists>I'\<in>{Collect (Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi>) |\<chi>. \<chi> \<in> dom \<pi>}.
      \<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> I) = ((q, \<nu>, p) \<in> I')"
      by simp

    {
      fix I' :: "('a ltl\<^sub>P \<times> (('a ltl, ('a ltl\<^sub>P list)) mapping), 'a set) transition set"
      assume "I' \<in> {{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} | \<chi>. \<chi> \<in> dom \<pi>}"
      then obtain \<chi> where I'_def: "I' = {t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t}" and "\<chi> \<in> dom \<pi>"
        by auto
      
      have "\<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> (Acc_inf (set \<Sigma>) \<pi> \<chi>)) = ((q, \<nu>, p) \<in> I')"
          using Acc_inf_filter_correct[OF _ subsetD[OF `dom \<pi> \<subseteq> \<^bold>G \<phi>`], of _ _ _ _ _ "set \<Sigma>" \<chi> "Mapping.Mapping \<pi>", OF _ `\<chi> \<in> dom \<pi>`]  
      unfolding combine_pairs.simps fst_conv snd_conv image_Un 
      unfolding pair_collapse Mapping.lookup.abs_eq I'_def by fast   
       hence INF2: "
            \<exists>I \<in> {Acc_inf (set \<Sigma>) \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}.
            \<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> I) = ((q, \<nu>, p) \<in> I')"
          using  `\<chi> \<in> dom \<pi>` by blast
    }
    hence INF2: "\<forall>I' \<in> {{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} | \<chi>. \<chi> \<in> dom \<pi>}.
            \<exists>I \<in> {Acc_inf (set \<Sigma>) \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}.
            \<forall>(q, \<nu>, p) \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>). ((abstract_state q, \<nu>, abstract_state p) \<in> I) = ((q, \<nu>, p) \<in> I')"
      by simp
 
    have "accepting_pair\<^sub>G\<^sub>R ?\<delta> ?q\<^sub>0 ?F w \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R ?\<delta>' ?q\<^sub>0' ?F' w" (is "?l \<longleftrightarrow> _")
      using accepting_pair\<^sub>G\<^sub>R_abstract'[OF F1 finite_\<Delta> assms R, of "fst ?F" "fst ?F'" "snd ?F" "snd ?F'", unfolded fst_conv snd_conv, OF _ INF1 INF2]  FIN 
      unfolding fst_conv snd_conv pair_collapse by blast
  
    also 

    have "\<dots> \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R ?\<delta>' ?q\<^sub>0' (?fin \<inter> ?reach', (\<lambda>I. I \<inter> ?reach') ` ?inf) w"
      unfolding accepting_pair\<^sub>G\<^sub>R_restrict[OF assms, symmetric] by simp

    also 

    have "\<dots> \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R_LTS (reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)) ?q\<^sub>0' (?fin \<inter> ?reach', (\<lambda>I. I \<inter> ?reach') ` ?inf) w" (is "_ \<longleftrightarrow> ?r")
      unfolding accepting_pair\<^sub>G\<^sub>R_LTS[OF assms] by simp

    finally
    have "?l \<longleftrightarrow> ?r" .
  }
 
  note X = this

  {
    assume ?lhs
    then obtain \<pi> where 1: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
      and 2: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < ltl_FG_to_rabin_def.max_rank\<^sub>R (set \<Sigma>) (theG \<chi>)"
      and 3: "accepting_pair\<^sub>G\<^sub>R (\<delta>\<^sub>\<A> (set \<Sigma>)) (\<iota>\<^sub>\<A> \<phi>) (M_fin \<pi> \<union> \<Union>{Acc_fin (set \<Sigma>) \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf (set \<Sigma>) \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}) w"
      unfolding ltl_to_generalised_rabin_correct[OF finite_set assms] by auto
    
    hence 31: "accept\<^sub>G\<^sub>R_LTS (reach\<^sub>t (set \<Sigma>) ?\<delta>' ?q\<^sub>0', ?q\<^sub>0', {(({t. M_fin_filter_exec \<phi> (Mapping.Mapping \<pi>) t} \<union> {t. \<exists>\<chi>\<in>dom \<pi>. Acc_fin_filter_exec (set \<Sigma>) (Mapping.Mapping \<pi>) \<chi> t}) \<inter> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>),
        (\<lambda>I. I \<inter> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)) ` {{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} |\<chi>. \<chi> \<in> dom \<pi>})}) w"
      using X by simp
    def \<pi>' \<equiv> "Mapping.Mapping \<pi>"
    hence "\<pi> = Mapping.rep \<pi>'" and "dom \<pi> = Mapping.keys \<pi>'" 
      by (simp add: Mapping_inverse keys.abs_eq)+
    hence "finite (dom \<pi>)"
      using \<G>_properties[OF 1] by blast
    have FOO: "(({t. M_fin_filter_exec \<phi> (Mapping.Mapping \<pi>) t} \<union>
      {t. \<exists>\<chi>\<in>dom \<pi>.
             Acc_fin_filter_exec (set \<Sigma>) (Mapping.Mapping \<pi>) \<chi>
              t}) \<inter>
     reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>),
     (\<lambda>I. I \<inter> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)) `
     {{t. Acc_inf_filter_exec (Mapping.Mapping \<pi>) \<chi> t} |\<chi>.
      \<chi> \<in> dom \<pi>}) \<in> (\<lambda>\<pi>. ({a \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>).
             M_fin_filter_exec \<phi> \<pi> a \<or>
             (\<exists>\<chi>\<in>dom (Mapping.rep \<pi>).
                 Acc_fin_filter_exec (set \<Sigma>) \<pi> \<chi> a)},
            (\<lambda>\<chi>. {a \<in>
                   reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>))
                    (initial \<phi>).
                   Acc_inf_filter_exec \<pi> \<chi> a}) `
            dom (Mapping.rep \<pi>))) `
      {\<pi>. dom (Mapping.rep \<pi>) \<subseteq> \<^bold>G \<phi> \<and> (\<forall>\<chi>\<in>dom (Mapping.rep \<pi>). the (Mapping.rep \<pi> \<chi>) < semi_mojmir_def.max_rank (set \<Sigma>) \<up>af\<^sub>G (Abs (theG \<chi>)))}" 
      using 1 2 unfolding `\<pi> = Mapping.rep \<pi>'` apply (simp del: Acc_fin_filter_exec.simps Acc_inf_filter_exec.simps M_fin_filter_exec.simps delta.simps initial.simps add:  Set.filter_def image_def)
      unfolding Mapping.mapping.rep_inverse  by auto  
    hence "?rhs"
      using accept\<^sub>G\<^sub>R_LTS_push[OF 31 FOO]
      unfolding ltl_to_rabin_exec.simps Let_def fst_conv snd_conv max_rank_of_def mappings_def 
      unfolding keys_dom_lookup Set.filter_def Mapping.lookup.rep_eq by simp
  }
  
  moreover 

  {
    assume ?rhs (is "accept\<^sub>G\<^sub>R_LTS ?A w")
    then obtain Fin Inf where "(Fin, Inf) \<in> snd (snd ?A)"
      and 4: "accepting_pair\<^sub>G\<^sub>R_LTS (fst ?A) (fst (snd ?A)) (Fin, Inf) w"
      using accept\<^sub>G\<^sub>R_LTS_E by blast
    then obtain \<pi> where Y: "(Fin, Inf) = (Set.filter (\<lambda>t. M_fin_filter_exec \<phi> \<pi> t \<or> (\<exists>\<chi> \<in> Mapping.keys \<pi>. Acc_fin_filter_exec (set \<Sigma>) \<pi> \<chi> t)) (reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)),
                  (\<lambda>\<chi>. Set.filter (Acc_inf_filter_exec \<pi> \<chi>) (reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>))) ` (Mapping.keys \<pi>))"
        and 1: "Mapping.keys \<pi> \<subseteq> \<^bold>G \<phi>" and 2: "\<And>\<chi>. \<chi> \<in> Mapping.keys \<pi> \<Longrightarrow> the (Mapping.lookup \<pi> \<chi>) < semi_mojmir_def.max_rank (set \<Sigma>) \<up>af\<^sub>G (Abs (theG \<chi>))"
     unfolding ltl_to_rabin_exec.simps Let_def fst_conv snd_conv max_rank_of_def mappings_def reach\<^sub>t_def reachable_transitions.simps by auto
    def \<pi>' \<equiv> "Mapping.rep \<pi>"
    have 1: "dom \<pi>' \<subseteq> \<^bold>G \<phi>" and 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>' \<Longrightarrow> the (\<pi>' \<chi>) < semi_mojmir_def.max_rank (set \<Sigma>) \<up>af\<^sub>G (Abs (theG \<chi>))"
      using 1 2 unfolding  \<pi>'_def Mapping.keys.rep_eq Mapping.mapping.rep_inverse by (simp add: lookup.rep_eq)+
    hence "(M_fin \<pi>' \<union> \<Union>{Acc_fin (set \<Sigma>) \<pi>' \<chi> | \<chi>. \<chi> \<in> dom \<pi>'}, {Acc_inf (set \<Sigma>) \<pi>' \<chi> | \<chi>. \<chi> \<in> dom \<pi>'}) \<in> ltl_to_generalised_rabin_acceptance_condition (set \<Sigma>) \<phi>"
      (is "?Acc \<in> _") by auto
    moreover
    have "(({t. M_fin_filter_exec \<phi> \<pi> t} \<union>
       {t. \<exists>\<chi>\<in>dom (Mapping.rep \<pi>).
              Acc_fin_filter_exec (set \<Sigma>) \<pi> \<chi> t}) \<inter>
      reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>),
      (\<lambda>I. I \<inter> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>)) `
      {{t. Acc_inf_filter_exec \<pi> \<chi> t} |\<chi>.
       \<chi> \<in> dom (Mapping.rep \<pi>)}) = ({a \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>).
       M_fin_filter_exec \<phi> \<pi> a \<or>
       (\<exists>\<chi>\<in>dom (Mapping.rep \<pi>).
           Acc_fin_filter_exec (set \<Sigma>) \<pi> \<chi> a)},
      (\<lambda>\<chi>. {a \<in> reach\<^sub>t (set \<Sigma>) (delta (set \<Sigma>)) (initial \<phi>).
             Acc_inf_filter_exec \<pi> \<chi> a}) `
      dom (Mapping.rep \<pi>))" unfolding image_def by auto
    hence "accepting_pair\<^sub>G\<^sub>R (\<delta>\<^sub>\<A> (set \<Sigma>)) (\<iota>\<^sub>\<A> \<phi>) ?Acc w"
      using X[OF 1 2] 4 unfolding ltl_to_rabin_exec.simps Let_def fst_conv snd_conv Y Set.filter_def \<pi>'_def Mapping.keys.rep_eq Mapping.mapping.rep_inverse by simp      
    ultimately
    have ?lhs  
      unfolding ERSTER ltl_to_generalized_rabin.simps accept\<^sub>G\<^sub>R_def fst_conv snd_conv by blast
   }

  ultimately
    
  show ?thesis
    ..
qed

subsubsection \<open>Code Equations\<close>

lemma [code]: 
  "\<up>af (Abs \<phi>) \<nu> = Abs (remove_constants\<^sub>P (af_letter \<phi> \<nu>))"
  using LTL_Rabin.af_abs.f_abs.abs_eq af_letter_abs_def remove_constants_correct 
  using Quotient3_ltl_prop_equiv_quotient Quotient3_rel ltl_prop_equiv_def by metis

lemma [code]:
  "\<up>af\<^sub>G (Abs \<phi>) \<nu> = Abs (remove_constants\<^sub>P (af_G_letter \<phi> \<nu>))"
  using LTL_Rabin.af_G_abs.f_abs.abs_eq af_G_letter_abs_def remove_constants_correct 
  using Quotient3_ltl_prop_equiv_quotient Quotient3_rel ltl_prop_equiv_def by metis

lemma [code]:
  "\<up>\<Delta>\<^sub>\<times> f (AList_Mapping.Mapping xs) c = AList_Mapping.Mapping (map_ran (\<lambda>a b. f a b c) xs)"
proof -
  have "\<And>x. (\<Delta>\<^sub>\<times> f (map_of xs) c) x = (map_of (map (\<lambda>(k, v). (k, f k v c)) xs)) x"
    by (induction xs) auto
  thus ?thesis
    by (transfer; simp add: map_ran_def)
qed

lemma [code]:
  "max_rank_of \<Sigma> \<psi> = card (Set.filter (Not o semi_mojmir_def.sink (set \<Sigma>) \<up>af\<^sub>G (Abs \<psi>)) (Q\<^sub>L \<Sigma> \<up>af\<^sub>G (Abs \<psi>)))"
proof (cases "\<Sigma> \<noteq> []")
  case True
    then interpret semi_mojmir "set \<Sigma>" "\<up>af\<^sub>G" "Abs \<psi>" "\<lambda>_. hd \<Sigma>"
      using ltl_semi_mojmir[of "set \<Sigma>"] by force
    show ?thesis
      unfolding max_rank_of_def max_rank_def Q\<^sub>L_reach[OF finite_reach] 
      by (simp add: Set.filter_def set_diff_eq)
qed (simp add: max_rank_of_def semi_mojmir_def.max_rank_def reach_def Set.filter_def) 

lemma [code]:
  "reachable_transitions \<Sigma> \<phi> = \<delta>\<^sub>L \<Sigma> (delta (set \<Sigma>)) (initial \<phi>)"
  using finite_\<Delta> reachable_transitions.simps \<delta>\<^sub>L_reach by metis
  
lemma [code]:
  "mappings \<Sigma> \<phi> = (
    let 
      Gs = G_list \<phi>; 
      max_rank = Mapping.lookup (Mapping.tabulate Gs ((max_rank_of \<Sigma>) o theG))
    in 
      \<Union>(set (map (\<lambda>xs. mapping_generator xs (\<lambda>x. [0 ..< the (max_rank x)])) (sublists Gs))))"
  (is "?lhs = ?rhs")
proof -
  {
    fix xs :: "'a ltl list"
    have subset_G: "\<And>x. x \<in> set (sublists (xs)) \<Longrightarrow> set x \<subseteq> set xs"
      apply (induction xs)
      apply (simp)
      by (insert sublists_powset; blast)
  }
  hence subset_G: "\<And>x. x \<in> set (sublists (G_list \<phi>)) \<Longrightarrow> set x \<subseteq> \<^bold>G \<phi>"
    unfolding G_eq_G_list by auto

  have "?lhs = \<Union>{{\<pi>. Mapping.keys \<pi> = xs \<and> (\<forall>\<chi>\<in>Mapping.keys \<pi>. the (Mapping.lookup \<pi> \<chi>) < max_rank_of \<Sigma> (theG \<chi>))} | xs. xs \<in> set ` (set (sublists (G_list \<phi>)))}"
    unfolding mappings_def G_eq_G_list sublists_powset
    unfolding G_eq_G_list[symmetric] by auto
  also
  have "\<dots> = \<Union>{{\<pi>. Mapping.keys \<pi> = set xs \<and> (\<forall>\<chi> \<in> set xs. the (Mapping.lookup \<pi> \<chi>) < max_rank_of \<Sigma> (theG \<chi>))} |
       xs. xs \<in> set (sublists (G_list \<phi>))}"
    by auto
  also
  have "\<dots> = ?rhs"
    unfolding Let_def set_map mapping_generator_set_eq lookup_tabulate G_eq_G_list set_upt image_def apply simp 
    using subset_G unfolding G_eq_G_list[symmetric] by blast
  finally
  show ?thesis
    by simp
qed

subsubsection \<open>Simplified Interface\<close>

fun ltl_to_rabin_exec_simp 
where 
  "ltl_to_rabin_exec_simp \<phi> = ltl_to_rabin_exec (map set (sublists (vars_list \<phi>))) \<phi>"

theorem ltl_to_rabin_exec_simp_correct:
  "range w \<subseteq> Pow (vars \<phi>) \<Longrightarrow> w \<Turnstile> \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltl_to_rabin_exec_simp \<phi>) w"
  by (metis ltl_to_rabin_exec_simp.simps list.set_map ltl_to_rabin_exec_correct sublists_powset vars_eq_vars_list)  

end