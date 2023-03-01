theory GS_Code
  imports 
    "Code_Setup"
    "../Splitting_Methods_Fin" 
    "HOL-Library.Code_Target_Numeral"
    "HOL-Data_Structures.Array_Braun"
begin

context MDP_nat_disc begin

lemma \<L>\<^sub>b_split_zero:
  assumes "\<And>s. s \<ge> states \<Longrightarrow> apply_bfun v s = 0"
  shows "GS.\<L>\<^sub>b_split v s = GS_rec_upto states v 0 s"
proof (cases "s < states")
  case True
  then show ?thesis using GS_rec_upto_correct by auto
next
  case False
  have aux: "s \<ge> states \<Longrightarrow> apply_bfun (GS.\<L>\<^sub>b_split v) s = 0" for s
  proof (induction s rule: less_induct)
    case (less x)
    have "r (x, a) = 0" if "a \<in> A x" for a
      by (simp add: less.prems reward_zero_outside)
    moreover have "measure_pmf.expectation (K (x, a)) ((bfun_if (\<lambda>s'. s' < x) (GS.\<L>\<^sub>b_split v) v)) = 0" for a
      using K_closed_compl assms less
      by (fastforce simp: bfun_if.rep_eq intro!: AE_pmfI integral_eq_zero_AE)
    ultimately show ?case
      by (auto simp: A_ne \<L>\<^sub>b_split_GS)
  qed
  then show ?thesis
    by (metis False GS_rec_upto_ge assms not_less)
qed
end

context MDP_Code begin

function GS_iter_aux :: "nat \<Rightarrow> 'tv \<Rightarrow> real \<Rightarrow> ('tv \<times> real)" where
  "GS_iter_aux s v md = ( 
  if s \<ge> states 
  then (v, md)
  else (
    let vs_old = v_lookup v s;
        vs_new = \<L>_GS_code (s_lookup mdp s) v;
        vs_diff = abs (vs_old - vs_new);
        v' = v_update s vs_new v
    in
        GS_iter_aux (Suc s) v' (max md vs_diff)))"
  by auto
termination
  by (relation "Wellfounded.measure (\<lambda>(n, _). states - n)") auto

definition "GS_iter v = GS_iter_aux 0 v 0"

lemmas GS_iter_aux.simps[simp del]

lemma GS_iter_aux_fst_correct:
  assumes "v_len v = states" "v_invar v"
  shows "s < states \<longrightarrow> v_lookup (fst (GS_iter_aux n v md)) s = MDP.GS_rec_upto states (V_Map.map_to_bfun v) n s \<and> v_invar (fst (GS_iter_aux n v md))"
  using assms unfolding GS_iter_def
proof (induction n v md rule: GS_iter_aux.induct)
  case (1 s v md)
  show ?case
    unfolding GS_iter_aux.simps[of s] MDP.GS_rec_upto.simps[of _ _ s]
    apply (auto simp add: "1.prems" assms(1) intro!: v_lookup_map_to_bfun)
     apply (simp add: 1 \<L>_GS_code_correct)
    using "1.IH"
     apply (smt (verit) "1.IH" "1.prems"(1) "1.prems"(2) Sup.SUP_cong V_Map.invar_update V_Map.map_to_bfun_update \<L>_GS_code_correct linorder_le_less_linear v_len_update)
    by (auto simp add: "1.IH" \<L>_GS_code_correct 1 V_Map.map_to_bfun_update v_lookup_map_to_bfun v_len_update V_Map.invar_update)
qed

lemma snd_GS_iter_aux_correct:
  assumes "v_len v = states" "v_invar v"
  shows "snd (GS_iter_aux n v md) = Max (Set.insert md ((\<lambda>s. abs (MDP.GS_rec_upto states (V_Map.map_to_bfun v) n s - (V_Map.map_to_bfun v) s)) `  {n..<states}))"
  using assms unfolding GS_iter_def
proof (induction n v md rule: GS_iter_aux.induct)
  case (1 s' v md)
  {
    assume s'_le: "s' < states"
    have "snd (GS_iter_aux s' v md) = (snd (GS_iter_aux (Suc s') (v_update s' (\<L>_GS_code (s_lookup mdp s') v) v) (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)))"
      unfolding GS_iter_aux.simps[of s'] 
      using s'_le
      by auto
    also have "\<dots> = Max (Set.insert (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun (v_update s' (\<L>_GS_code (s_lookup mdp s') v) v)))  (Suc s') s - apply_bfun (V_Map.map_to_bfun (v_update s' (\<L>_GS_code (s_lookup mdp s') v) v)) s\<bar>) ` {Suc s'..<states}))"
      apply (subst "1.IH")
      subgoal using s'_le by auto
      using s'_le v_len_update
      by (auto simp add: "1.prems" V_Map.invar_update s'_le)
    also have "\<dots> = Max (Set.insert (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states ((V_Map.map_to_bfun v)(s' := (\<L>_GS_code (s_lookup mdp s') v))) (Suc s') s - apply_bfun (V_Map.map_to_bfun (v_update s' (\<L>_GS_code (s_lookup mdp s') v) v)) s\<bar>) ` {Suc s'..<states}))"
      using "1.prems"(1) "1.prems"(2) V_Map.map_to_bfun_update s'_le by presburger
    also have "\<dots> = Max (Set.insert (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states ((V_Map.map_to_bfun v)(s' := \<Squnion>a\<in>MDP_A s'. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s')) (Suc s') s - ((V_Map.map_to_bfun v) (s' := \<Squnion>a\<in>MDP_A s'. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s')) s \<bar>) ` {Suc s'..<states}))"
      using "1.prems"(1) "1.prems"(2) MDP.SUP_L\<^sub>a_eq_det MDP.\<L>\<^sub>b_eq_SUP_L\<^sub>a V_Map.map_to_fun_update \<L>_code_correct \<L>_code_lookup map_to_bfun_eq_fun by auto

    also have "\<dots> = Max (Set.insert (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states ((V_Map.map_to_bfun v)(s' := \<Squnion>a\<in>MDP_A s'. MDP.L\<^sub>a a (V_Map.map_to_bfun v) s')) (Suc s') s - V_Map.map_to_bfun v s \<bar>) ` {Suc s'..<states}))"
      using "1.prems"(1) "1.prems"(2) MDP.SUP_L\<^sub>a_eq_det MDP.\<L>\<^sub>b_eq_SUP_L\<^sub>a V_Map.map_to_fun_update \<L>_code_correct \<L>_code_lookup map_to_bfun_eq_fun by auto
    also have "\<dots> = Max (Set.insert (max md \<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` {Suc s'..<states}))"
      using s'_le MDP.GS_rec_upto.simps[symmetric, of states "s'" "(apply_bfun (V_Map.map_to_bfun v))"]
      by presburger
    also have "\<dots> = max md (Max (Set.insert (\<bar>v_lookup v s' - \<L>_GS_code (s_lookup mdp s') v\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` {Suc s'..<states})))"
    proof -
      have *: "Max (Set.insert (max x y) X) = max x (Max (Set.insert y X))" if "finite X" for X x y
        by (metis Max_insert Max_singleton max.assoc that)
      thus ?thesis
        by blast
    qed
    also have "\<dots> = max md (Max (Set.insert (\<bar>\<L>_GS_code (s_lookup mdp s') v - V_Map.map_to_bfun v s'\<bar>)
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` {Suc s'..<states})))"
      by (smt (verit, best) "1.prems"(1) "1.prems"(2) v_lookup_map_to_bfun s'_le)
    also have "\<dots> = max md (Max ((\<lambda>s. (\<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>)) ` {s'} \<union>
          ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` {Suc s'..<states})))"
    proof -
      have * :"\<L>_GS_code (s_lookup mdp s') v = MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s'"
        apply (subst MDP.GS_rec_upto_eq)
        using s'_le 
         apply blast
        using \<L>_GS_code_correct 1 s'_le
        by presburger
      show ?thesis
        by (auto simp: *)
    qed
    also have "\<dots> = max md (Max ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` ({s'} \<union> {Suc s'..<states})))"
      unfolding atLeastLessThan_def lessThan_def
      by auto
    also have "\<dots> = max md (Max ((\<lambda>s. \<bar>MDP.GS_rec_upto states (apply_bfun (V_Map.map_to_bfun v))  s' s - V_Map.map_to_bfun v s\<bar>) ` ({s'..<states})))"
    proof -
      have "({s'} \<union> {Suc s'..<states}) = {s'..<states}"
        using s'_le
        by auto
      thus ?thesis by auto
    qed
    finally have "snd (GS_iter_aux s' v md) = max md (MAX s\<in>{s'..<states}. \<bar>MDP.GS_rec_upto states ((V_Map.map_to_bfun v)) s' s - (V_Map.map_to_bfun v) s\<bar>)".
  }
  thus ?case
    apply (cases "s' < states")
     apply auto
    using "1.prems"(1) "1.prems"(2) GS_iter_aux_fst_correct assms(1) 
    apply (simp add: "1.prems"(1) "1.prems"(2) GS_iter_aux_fst_correct assms(1))
    by (simp add: GS_iter_aux.simps)
qed


lemma invar_GS_iter_aux: "v_len v = states \<Longrightarrow> v_invar v \<Longrightarrow> v_invar (fst (GS_iter_aux n v md))"
  by (metis GS_iter_aux.simps GS_iter_aux_fst_correct fst_conv linorder_not_le)

lemma invar_GS_iter: "v_len v = states \<Longrightarrow> v_invar v \<Longrightarrow> v_invar (fst (GS_iter v))"
  using invar_GS_iter_aux GS_iter_def by auto

lemma len_GS_iter_aux[simp]: "v_invar v \<Longrightarrow> v_len v = states \<Longrightarrow> v_len (fst (GS_iter_aux n v md)) = states"
proof (induction n v md   rule: GS_iter_aux.induct)
  case (1 s v md)
  have 2: " v_len (v_update s (\<L>_GS_code (s_lookup mdp s) v) v) = v_len v" if "s < states"
    using 1 that v_len_update by blast
  have "v_len (fst (GS_iter_aux (Suc s) (v_update s (\<L>_GS_code (s_lookup mdp s) v) v) (max md \<bar>v_lookup v s - \<L>_GS_code (s_lookup mdp s) v\<bar>))) = v_len v" if "s < states"
    unfolding 2[OF that, symmetric]
    using 1(2,3) that
    apply (subst "1.IH"[OF _ ])
           apply auto
    using V_Map.invar_update 2 by force+
  thus ?case
    by (metis "1.prems"(2) GS_iter_aux.elims fst_conv less_eq_Suc_le not_less_eq_eq)
qed

lemma len_GS_iter[simp]: "v_invar v \<Longrightarrow> v_len v = states \<Longrightarrow> v_len (fst (GS_iter v)) = v_len v"
  using len_GS_iter_aux GS_iter_def by auto

lemma GS_iter_aux_correct':
  assumes "v_len v = states" "v_invar v"
  shows "apply_bfun (V_Map.map_to_bfun (fst (GS_iter_aux 0 v md))) s = MDP.GS_rec_upto states (V_Map.map_to_bfun v) 0 s"
proof (cases "s < states")
  case True
  then show ?thesis
    using assms
    by (metis GS_iter_aux_fst_correct len_GS_iter_aux v_lookup_map_to_bfun)
next
  case False
  then show ?thesis
    by (simp add: MDP.GS_rec_upto_ge V_Map.map_to_bfun.rep_eq assms(1) assms(2))
qed


lemma GS_iter_aux_correct'':
  assumes "v_len v = states" "v_invar v"
  shows "V_Map.map_to_bfun (fst (GS_iter v)) = MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)"
  apply (rule bfun_eqI)
  unfolding V_Map.map_to_bfun.rep_eq
  apply auto
    apply (simp add: GS_iter_aux_fst_correct GS_iter_def MDP.GS_rec_upto_correct assms(1) assms(2))
   apply (simp add: GS_iter_def assms(1) assms(2) invar_GS_iter_aux)
  by (metis GS_iter_aux_correct' GS_iter_def MDP.\<L>\<^sub>b_split_zero V_Map.map_to_bfun.rep_eq assms(1) assms(2) linorder_not_less)


lemma snd_GS_iter_correct':
  assumes "v_len v = states" "v_invar v"
  shows "snd (GS_iter v) = dist (V_Map.map_to_bfun (fst (GS_iter v))) (V_Map.map_to_bfun v)"
proof -
  have "dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x) = 0" if "x \<ge> states" for x
    by (metis GS_iter_aux_correct'' V_Map.map_to_bfun.rep_eq assms(1) assms(2) dist_eq_0_iff leD len_GS_iter that)
  hence "(\<Squnion>x. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x)) =
    (\<Squnion>x\<in>{0..<Suc states}. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x)) \<squnion> (\<Squnion>x\<in>{Suc states..}. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x))"
    apply (subst cSUP_union[symmetric])
        apply auto
    by (simp add: ivl_disj_un_one(8))
  also have "\<dots> = max 0 (\<Squnion>(Set.insert 0 ((\<lambda>x. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x)) ` {0..< states})))"
  proof -
    have "dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x) = 0" if "x \<in> {Suc states..}" for x
      apply auto
      using MDP.\<L>\<^sub>b_split_zero
      by (meson Suc_leD \<open>\<And>x. states \<le> x \<Longrightarrow> dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x) = 0\<close> atLeast_iff dist_eq_0_iff that)
    thus ?thesis 
      using sup_real_def
      by (simp add: \<open>\<And>x. states \<le> x \<Longrightarrow> dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x) = 0\<close> atLeast0_lessThan_Suc)
  qed
  also have "\<dots> = max 0 (Max (Set.insert 0 ((\<lambda>x. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x)) ` {0..< states})))"  
    by (auto simp: cSup_eq_Max)
  also have "\<dots> = (Max (Set.insert 0 ((\<lambda>x. dist (apply_bfun (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) x) (apply_bfun (V_Map.map_to_bfun v) x)) ` {0..< states})))"  
    by auto
  also have "\<dots> = snd (GS_iter v)"
    unfolding GS_iter_def
    apply (subst snd_GS_iter_aux_correct)
      apply (simp add: assms)
     apply (simp add: assms)
    apply (auto simp: dist_real_def)
    apply (subst MDP.\<L>\<^sub>b_split_zero)
     apply (simp add: V_Map.map_to_bfun.rep_eq assms(1))
    by (auto simp: dist_real_def)
  finally show ?thesis
    by (simp add: GS_iter_aux_correct'' assms(1) assms(2) dist_bfun.rep_eq)
qed

lemma GS_iter_aux_correct:
  assumes "s < states" "v_len v = states" "v_invar v"
  shows "v_lookup (fst (GS_iter_aux n v eps)) s = MDP.GS_rec_upto states (V_Map.map_to_bfun v) n s"
  using GS_iter_aux_fst_correct assms(1) assms(2) assms(3) by blast


definition "find_policy_code_aux_upt (v::'tv) n = (
  fold (\<lambda>s (d,v). let (d', v') = find_policy_state_code_aux' v s in
      (d_update s d' d, v_update s v' v)) [0..<n] (d_empty, v))"

lemma find_policy_code_aux_upt_Suc:
  "find_policy_code_aux_upt v (Suc s) = (
  let (d, v) = (find_policy_code_aux_upt v s) in
    (d_update s ((fst (find_policy_state_code_aux' v s))) d, v_update s (snd (find_policy_state_code_aux' v s)) v))"
  unfolding find_policy_code_aux_upt_def
  by (auto simp: case_prod_beta)

definition "find_policy_code_aux v = find_policy_code_aux_upt v states"
definition "find_policy_code v = fst (find_policy_code_aux v)"


lemma d_invar_find_policy_code_aux_upt: "D_Map.invar (fst (find_policy_code_aux_upt v n))"
  by (induction n) (auto simp: D_Map.map_specs case_prod_beta find_policy_code_aux_upt_def)

lemma v_len_invar_find_policy_code_aux_upt: "n \<le> j \<Longrightarrow> v_len v = j \<Longrightarrow> v_invar v \<Longrightarrow> v_len (snd (find_policy_code_aux_upt v n)) = j \<and> v_invar (snd (find_policy_code_aux_upt v n))"
  apply (induction n arbitrary: v) 
   apply (simp add: find_policy_code_aux_upt_def)
  apply (simp add: case_prod_beta find_policy_code_aux_upt_def)
  apply (subst V_Map.invar_update)
    apply blast
   apply simp
  using Suc_le_lessD v_len_update by presburger

lemma assumes "s < states" "v_invar v" "v_len v \<ge> states"
  shows 
    "d_lookup (fst (find_policy_code_aux v)) s = d_lookup (fst (find_policy_code_aux_upt v (Suc s))) s"
    "v_lookup (snd (find_policy_code_aux v)) s = v_lookup (snd (find_policy_code_aux_upt v (Suc s))) s"
  unfolding find_policy_code_aux_def
  using assms
proof (induction states arbitrary: v)
  case (Suc states)
  {
    case 1
    show ?case
    proof (cases "s = states")
    next
      case False
      then show ?thesis 
        using 1 less_Suc_eq
        apply (subst find_policy_code_aux_upt_Suc)
        by (auto simp: case_prod_beta D_Map.map_update[OF d_invar_find_policy_code_aux_upt] Suc(1)[symmetric])
    qed auto
  next
    case 2
    then show ?case
    proof (cases "s = states")
    next
      case False
      then show ?thesis 
        using 2 less_Suc_eq
        apply (subst find_policy_code_aux_upt_Suc)
        apply (auto simp: case_prod_beta Suc(2)[symmetric])
        by (metis False Suc_leD dec_induct v_len_invar_find_policy_code_aux_upt v_lookup_update)
    qed auto
  }
qed auto

lemma find_policy_code_invar: "D_Map.invar (find_policy_code v)"
  unfolding find_policy_code_def find_policy_code_aux_def
  by (induction states) (auto simp: find_policy_code_aux_upt_def D_Map.map_specs case_prod_unfold)

lemma find_policy_code_notin: 
  assumes "s \<ge> states" shows "d_lookup (find_policy_code v) s = None"
  using assms d_invar_find_policy_code_aux_upt
  unfolding find_policy_code_def find_policy_code_aux_def
  by (induction states) (auto simp: find_policy_code_aux_upt_def case_prod_beta D_Map.map_specs)

lemma find_policy_code_in: 
  assumes "s < states" shows "\<exists>x. d_lookup (find_policy_code v) s = Some x"
  using assms
  unfolding find_policy_code_def find_policy_code_aux_def
proof (induction states)
  case 0
  then show ?case
    by simp
next
  case (Suc states)
  then show ?case
    using d_invar_find_policy_code_aux_upt
    by (auto simp: find_policy_code_aux_upt_Suc case_prod_beta D_Map.map_specs)
qed

lemma GS_iter_aux_fold: "fst (GS_iter_aux s v md) = fold (\<lambda>s v. v_update s (\<L>_GS_code (s_lookup mdp s) v) v) [s..<states] v"
proof (induction s v md arbitrary: rule: GS_iter_aux.induct)
  case (1 s v)
  have aux: "s < states \<Longrightarrow> [s..<states] = s#[Suc s..<states]"
    using upt_conv_Cons by presburger
  show ?case
    by (subst GS_iter_aux.simps) (auto simp: 1 aux)
qed

lemma find_policy_state_code_aux'_eq_\<L>_GS_code:
  assumes "v_len v = states" "v_invar v" "s < states"
  shows "snd (find_policy_state_code_aux' v s) = \<L>_GS_code (s_lookup mdp s) v"
  using assms
  by (auto simp: \<L>_GS_code_correct cSup_eq_Max find_policy_state_code_aux'_eq')


lemma snd_find_policy_code_aux_upt:
  assumes "v_len v = states" "v_invar v"
  shows "(snd (find_policy_code_aux_upt v states)) = fst (GS_iter_aux 0 v md)"
proof -
  have "fst (GS_iter_aux 0 v md) = fold (\<lambda>s v. v_update s (\<L>_GS_code (s_lookup mdp s) v) v) [0..<states] v"
    unfolding GS_iter_aux_fold ..
  also have "\<dots> = fold (\<lambda>s v. v_update s (snd (find_policy_state_code_aux' v s)) v) [0..<states] v"
    using find_policy_state_code_aux'_eq_\<L>_GS_code assms
    by (auto simp:V_Map.invar_update v_len_update intro!: fold_cong'[where P = "\<lambda>v. v_len v = states \<and> v_invar v"])
  also have "\<dots> = (snd (find_policy_code_aux_upt v states))"
    unfolding find_policy_code_aux_upt_def
    by (induction states) (auto simp add: split_def)
  finally show ?thesis..
qed

lemma GS_rec_upto_Suc: "MDP.GS_rec_upto (Suc n) v 0 = (MDP.GS_rec_upto n v 0)(n := (\<Squnion>a\<in>MDP_A n. MDP.L\<^sub>a a (MDP.GS_rec_upto n v 0) n))"
proof -
  have "s \<noteq> n \<Longrightarrow> MDP.GS_rec_upto (Suc n) v 0 s = MDP.GS_rec_upto n v 0 s" for s
    using MDP.GS_rec_upto_Suc MDP.GS_rec_upto_ge
    by (metis Suc_leI le_neq_implies_less not_less)
  moreover have "s = n \<Longrightarrow> MDP.GS_rec_upto (Suc n) v 0 s = (\<Squnion>a\<in>MDP_A n. MDP.L\<^sub>a a (MDP.GS_rec_upto n v 0) n)" for s
    using MDP.GS_rec_upto_Suc' by auto
  ultimately show ?thesis
    by auto
qed

lemma keys_fst_find_policy_code_aux_upt: "s \<le> states \<Longrightarrow> D_Map.keys (fst (find_policy_code_aux_upt v s)) = {0..<s}"
  using d_invar_find_policy_code_aux_upt find_policy_code_aux_upt_def
  by (induction s arbitrary: v) (auto simp: find_policy_code_aux_upt_Suc case_prod_beta)

lemma keys_fst_find_policy_code_aux: "D_Map.keys (fst (find_policy_code_aux v)) = {0..<states}"
  using keys_fst_find_policy_code_aux_upt find_policy_code_aux_def 
  by force

lemma find_policy_code_ge: "s \<ge> states \<Longrightarrow> D_Map.map_to_fun (find_policy_code v) s = 0"
  using find_policy_code_notin find_policy_code_def 
  by (auto simp: D_Map.map_to_fun_def)

lemma find_policy_code_aux_upt_zero[simp]: "find_policy_code_aux_upt v 0 = (d_empty, v)"
  unfolding find_policy_code_aux_upt_def
  by auto

lemma GS_rec_upto_zero[simp]: "MDP.GS_rec_upto 0 v n = v"
  by (auto simp: MDP.GS_rec_upto.simps)

lemma keys_find_policy_code_aux_upt:"n < states \<Longrightarrow> v_invar v \<Longrightarrow> v_len v = states \<Longrightarrow> v_len (snd (find_policy_code_aux_upt v n)) = states"
  apply (induction n arbitrary: v) 
   apply (auto simp: case_prod_beta find_policy_code_aux_upt_Suc)
  by (metis Suc_lessD less_or_eq_imp_le v_len_invar_find_policy_code_aux_upt v_len_update)

lemma split_eq_GS_rec_upto_Sup:
  "MDP.GS.\<L>\<^sub>b_split v s = (\<Squnion>a\<in>MDP_A s. MDP.L\<^sub>a a (MDP.GS_rec_upto s (apply_bfun v) 0) s)"
  using MDP.GS_rec_upto_correct MDP.GS_rec_upto_ge MDP.\<L>\<^sub>b_split_GS_iter[symmetric, of _ _ v] by auto

lemma split_eq_GS_rec_upto_is_arg_max:
  assumes "is_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto s (apply_bfun v) 0) s) (\<lambda>a. a \<in> MDP_A s) a"  
  shows "MDP.GS.\<L>\<^sub>b_split v s = MDP.L\<^sub>a a (MDP.GS_rec_upto s (apply_bfun v) 0) s"
  using arg_max_SUP[OF assms] split_eq_GS_rec_upto_Sup
  by auto

lemma "MDP.GS_rec_upto n (apply_bfun v) 0 s = (if s < n then MDP.GS.\<L>\<^sub>b_split v s else v s)"
  using MDP.GS_rec_upto_correct MDP.GS_rec_upto_ge
  by auto

lemma GS_rec_upto_eq_\<L>\<^sub>b_split': "MDP.GS_rec_upto n (apply_bfun v) 0 = (\<lambda>s. if s < n then MDP.GS.\<L>\<^sub>b_split v s else v s)"
  using MDP.GS_rec_upto_correct MDP.GS_rec_upto_ge not_le
  by auto

lemma snd_find_policy_code_aux_upt_correct:
  assumes "v_len v = states" "v_invar v" "n \<le> states"
  shows "V_Map.map_to_fun (snd (find_policy_code_aux_upt v n)) = MDP.GS_rec_upto n (V_Map.map_to_fun v) 0"
  using assms
proof (induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  have "V_Map.map_to_fun (snd (find_policy_code_aux_upt v (Suc n))) n = snd (find_policy_state_code_aux' (snd (find_policy_code_aux_upt v n)) n)"
    unfolding find_policy_code_aux_upt_Suc
    using  Suc(3)  Suc(2)
    apply (auto simp: case_prod_unfold V_Map.map_to_fun_update)
    apply (subst V_Map.map_to_fun_update)
    using v_len_invar_find_policy_code_aux_upt 
      apply auto
    by (metis Suc.prems(3) Suc_leD Suc_le_lessD assms(1))+
  also have "\<dots> = (MAX a\<in>MDP_A n. MDP.L\<^sub>a a (apply_bfun (V_Map.map_to_bfun (snd (find_policy_code_aux_upt v n)))) n)"
    using keys_find_policy_code_aux_upt Suc v_len_invar_find_policy_code_aux_upt
    by (smt (verit, ccfv_SIG) Suc_leD Suc_le_lessD Sup.SUP_cong find_policy_state_code_aux'_eq' snd_conv)
  also have "\<dots> = (\<Squnion>a\<in>MDP_A n. MDP.L\<^sub>a a (apply_bfun (V_Map.map_to_bfun (snd (find_policy_code_aux_upt v n)))) n)"
    using Suc
    by (auto simp: cSup_eq_Max[symmetric] V_Map.map_to_fun_def V_Map.map_to_bfun.rep_eq)
  also have "\<dots> = (\<Squnion>a\<in>MDP_A n. MDP.L\<^sub>a a ((V_Map.map_to_fun (snd (find_policy_code_aux_upt v n)))) n)"
    using Suc.prems
    by (auto simp: map_to_bfun_eq_fun)
  also have "\<dots> = MDP.GS_rec_upto (Suc n) (V_Map.map_to_fun v) 0 n"
    using MDP.GS_rec_upto_Suc' Suc
    by auto
  finally have "V_Map.map_to_fun (snd (find_policy_code_aux_upt v (Suc n))) n = MDP.GS_rec_upto (Suc n) (V_Map.map_to_fun v) 0 n".
  moreover have "V_Map.map_to_fun (snd (find_policy_code_aux_upt v (Suc n))) s = MDP.GS_rec_upto (Suc n) (V_Map.map_to_fun v) 0 s" if "s \<noteq> n" for s
    unfolding find_policy_code_aux_upt_Suc
    using Suc Suc_lessD that
    apply (auto simp: case_prod_beta V_Map.map_to_fun_update GS_rec_upto_Suc)
    by (metis Suc_leD Suc_le_lessD V_Map.invar_update V_Map.map_to_fun_def v_len_invar_find_policy_code_aux_upt v_len_update v_lookup_update)
  ultimately show ?case
    by fastforce
qed

lemma GS_inv_eq_L: "apply_bfun (MDP.GS_inv d v) s = MDP.L (MDP.mk_dec_det d) ((bfun_if ((\<le>) s) v (MDP.GS_inv d v))) s"
  using MDP.GS_inv_elem_eq MDP.L_def by presburger

lemma GS_inv_eq_L\<^sub>a: "MDP.GS_inv d v s = MDP.L\<^sub>a (d s) (bfun_if ((\<le>) s) v (MDP.GS_inv d v)) s"
  using GS_inv_eq_L MDP.L_eq_L\<^sub>a_det by presburger

lemma is_arg_max_L\<^sub>a_GS_inv:
  "is_arg_max (\<lambda>a. MDP.L\<^sub>a a (bfun_if ((\<le>) s) v (MDP.GS_inv d v)) s) (\<lambda>a. a \<in> MDP_A s) a 
  \<longleftrightarrow> is_arg_max (\<lambda>a. (MDP.GS_inv (d(s := a)) v s)) (\<lambda>a. a \<in> MDP_A s) a"
proof -
  have *: "s' < s \<Longrightarrow> MDP.GS_inv (d(s := a)) v s' =  MDP.GS_inv d v s'" for s' a
    using MDP.GS_indep_high_states by fastforce
  show ?thesis
    unfolding GS_inv_eq_L\<^sub>a by (fastforce simp: bfun_if.rep_eq * cong: if_cong)
qed

lemma GS_rec_upto_eq_\<L>\<^sub>b_split'': "MDP.GS_rec_upto s (apply_bfun v) 0 = bfun_if ((\<le>) s) v (MDP.GS.\<L>\<^sub>b_split v)"
  by (fastforce simp: MDP.GS_rec_upto_ge bfun_if.rep_eq MDP.GS_rec_upto_correct not_le)

lemma GS_inv_GS_least_eq_split: "MDP.GS_inv (MDP.d_GS_least v) v = MDP.GS.\<L>\<^sub>b_split v"
  using arg_max_SUP[OF MDP.d_GS_least_is_arg_max]
  by (auto simp: MDP.GS.\<L>\<^sub>b_split.rep_eq MDP.GS.\<L>_split_def MDP.GS_inv_def[symmetric])

lemma is_arg_max_L\<^sub>a_GS_inv_d_GS_least:
  "is_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto s (apply_bfun v) 0) s) (\<lambda>a. a \<in> MDP_A s) a 
  \<longleftrightarrow> is_arg_max (\<lambda>a. (MDP.GS_inv ((MDP.d_GS_least v)(s := a)) v s)) (\<lambda>a. a \<in> MDP_A s) a"
  by (auto simp: GS_inv_GS_least_eq_split GS_rec_upto_eq_\<L>\<^sub>b_split'' is_arg_max_L\<^sub>a_GS_inv[symmetric])

lemma d_GS_least_ge: "s \<ge> states \<Longrightarrow> MDP.d_GS_least (V_Map.map_to_bfun v) s = 0"
  by (subst MDP.d_GS_least_eq) (auto intro!: Least_equality simp: is_arg_max_linorder MDP_A_def)

lemma fst_find_policy_code_aux_upt_correct:
  assumes "v_len v = states" "v_invar v" "n \<le> states" "s < n"
  shows "D_Map.map_to_fun (fst (find_policy_code_aux_upt v n)) s = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto s (V_Map.map_to_fun v) 0) s) (\<lambda>a. a \<in> MDP_A s)"
  using assms
proof (induction n arbitrary: s)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  have "D_Map.map_to_fun (fst (find_policy_code_aux_upt v (Suc n))) n = fst (find_policy_state_code_aux' (snd (find_policy_code_aux_upt v n)) n)"
    using d_invar_find_policy_code_aux_upt Suc
    by (auto simp: find_policy_code_aux_upt_Suc case_prod_unfold D_Map.map_to_fun_update)
  also have "\<dots> = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (apply_bfun (V_Map.map_to_bfun (snd (find_policy_code_aux_upt v n)))) n) (\<lambda>a. a \<in> MDP_A n)"
    using Suc keys_find_policy_code_aux_upt  
    apply (auto simp: find_policy_state_code_aux'_eq')
    apply (subst find_policy_state_code_aux'_eq')
    using Suc_le_lessD apply presburger+
     apply (meson Suc_leD v_len_invar_find_policy_code_aux_upt)
    by force
  also have "\<dots> = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto n (V_Map.map_to_fun v) 0) n) (\<lambda>a. a \<in> MDP_A n)"
    using Suc map_to_bfun_eq_fun
    by (auto simp: snd_find_policy_code_aux_upt_correct)
  finally have "D_Map.map_to_fun (fst (find_policy_code_aux_upt v (Suc n))) n = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto n (V_Map.map_to_fun v) 0) n) (\<lambda>a. a \<in> MDP_A n)".
  moreover have "D_Map.map_to_fun (fst (find_policy_code_aux_upt v (Suc n))) s = least_arg_max (\<lambda>a. MDP.L\<^sub>a a (MDP.GS_rec_upto s (V_Map.map_to_fun v) 0) s) (\<lambda>a. a \<in> MDP_A s)" if "s < n" for s
    using that d_invar_find_policy_code_aux_upt Suc
    by (auto simp: find_policy_code_aux_upt_Suc case_prod_unfold D_Map.map_to_fun_update)
  ultimately show ?case
    using Suc by (cases "s = n") auto
qed

lemma GS_iter'_correct:
  assumes "v_len v = states" "v_invar v"
  shows "D_Map.map_to_fun (find_policy_code v) = (MDP.d_GS_least (V_Map.map_to_bfun v))"
proof -
  have "D_Map.map_to_fun (find_policy_code v) s = (MDP.d_GS_least (V_Map.map_to_bfun v)) s" if "s \<ge> states" for s
    using find_policy_code_ge d_GS_least_ge that
    by auto
  moreover have "D_Map.map_to_fun (find_policy_code v) s = (MDP.d_GS_least (V_Map.map_to_bfun v)) s" if "s < states" for s
    using that assms
  proof (induction s rule: less_induct)
    case (less x)
    show ?case
      unfolding find_policy_code_def find_policy_code_aux_def
      using less assms
      by (auto intro!: least_arg_max_cong' simp: MDP.d_GS_least_eq fst_find_policy_code_aux_upt_correct map_to_bfun_eq_fun is_arg_max_L\<^sub>a_GS_inv_d_GS_least[symmetric] least_arg_max_def[symmetric])
  qed
  ultimately show ?thesis
    using not_le by blast
qed

partial_function (tailrec) GS_code_aux where
  "GS_code_aux v eps = (
  let (v', md) = GS_iter v in
    if (2 * l) * md < eps * (1 - l)
    then v'
    else GS_code_aux v' eps)"

lemmas GS_code_aux.simps[code]

definition "GS_code v eps = (if l = 0 \<or> eps \<le> 0 then fst (GS_iter v) else GS_code_aux v eps)"


lemma GS_code_aux_correct_aux:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "V_Map.map_to_fun (GS_code_aux v eps) = MDP.gs_iteration eps (V_Map.map_to_bfun v) 
  \<and> v_len (GS_code_aux v eps) = states \<and> v_invar (GS_code_aux v eps)"
  using assms
proof (induction eps "(V_Map.map_to_bfun v)" arbitrary: v rule: MDP.gs_iteration.induct)
  case (1 eps)
  have *:"2 * l * snd (GS_iter v) < eps * (1 - l) \<longleftrightarrow> 2 * l * dist (MDP.GS.\<L>\<^sub>b_split (V_Map.map_to_bfun v)) (V_Map.map_to_bfun v) < eps * (1 - l)"      
    using GS_iter_aux_correct''
    by (auto simp: snd_GS_iter_correct' 1)

  thus ?case
  proof (cases "2 * l * snd (GS_iter v) < eps * (1 - l)")
    case True
    then show ?thesis 
      unfolding GS_code_aux.simps[of v]
      apply (simp add: case_prod_beta)
      apply (subst MDP.gs_iteration.simps)
      apply (auto simp: case_prod_beta *)
              apply (metis "1.prems"(2) "1.prems"(3) GS_iter_aux_correct'' map_to_bfun_eq_fun)
      using "1.prems"(1) apply (auto simp: dist_commute)
       apply (simp add: "1.prems"(2) "1.prems"(3))
      using "1.prems"(2) "1.prems"(3) invar_GS_iter by blast
  next
    case False
    then show ?thesis 
      unfolding GS_code_aux.simps[of v]
      apply (simp add: case_prod_beta)
      apply (subst MDP.gs_iteration.simps)
      apply (auto simp: case_prod_beta *)
      using "1.prems"(1) apply (auto simp: dist_commute)
      by (auto simp add: "1.hyps" "1.prems"(2) "1.prems"(3) GS_iter_aux_correct'' assms(4) invar_GS_iter)
  qed
qed

lemma GS_code_aux_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "V_Map.map_to_fun (GS_code_aux v eps) = MDP.gs_iteration eps (V_Map.map_to_bfun v)"
  using assms GS_code_aux_correct_aux by auto

lemma GS_code_aux_keys:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "v_len (GS_code_aux v eps) = states"
  using assms GS_code_aux_correct_aux by auto

lemma GS_code_aux_invar:
  assumes "eps > 0" "v_invar v" "v_len v = states" "l \<noteq> 0"
  shows "v_invar (GS_code_aux v eps)"
  using assms GS_code_aux_correct_aux by auto

lemma GS_code_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states"
  shows "V_Map.map_to_fun (GS_code v eps) = MDP.gs_iteration eps (V_Map.map_to_bfun v)"
proof (cases "l = 0")
  case True
  then show ?thesis  
    using assms invar_GS_iter GS_iter_aux_correct''
    unfolding GS_code_def MDP.gs_iteration.simps[of _ "V_Map.map_to_bfun v"]
    by (fastforce simp: map_to_bfun_eq_fun)
next
  case False
  then show ?thesis
    using assms
    by (auto simp add: GS_code_def GS_code_aux_correct  MDP.gs_iteration.simps )
qed

definition "GS_policy_code v eps = find_policy_code (GS_code v eps)"

lemma GS_policy_code_correct:
  assumes "eps > 0" "v_invar v" "v_len v = states"
  shows "D_Map.map_to_fun (GS_policy_code v eps) = MDP.vi_gs_policy eps (V_Map.map_to_bfun v)"
proof -
  have aux: "V_Map.map_to_bfun (GS_code v eps) = (MDP.gs_iteration eps (V_Map.map_to_bfun v))"
    using GS_code_correct[OF assms] assms(2) map_to_bfun_eq_fun by auto
  have "D_Map.map_to_fun (GS_policy_code v eps) = MDP.d_GS_least (V_Map.map_to_bfun (GS_code v eps))"
    unfolding GS_code_def GS_policy_code_def MDP.vi_gs_policy_def
  proof (subst GS_iter'_correct)
    show "v_len (if l = 0 \<or> eps \<le> 0 then fst (GS_iter v) else GS_code_aux v eps) = states" 
      using assms len_GS_iter GS_code_aux_keys assms by presburger
  qed (auto simp: assms GS_code_aux_invar invar_GS_iter)
  also have "\<dots> = MDP.d_GS_least (MDP.gs_iteration eps (V_Map.map_to_bfun v))"
    using GS_code_correct[of eps v] assms by (auto simp: aux)
  finally show ?thesis unfolding MDP.vi_gs_policy_def by auto
qed

end

lemma inorder_empty: "Tree2.inorder am = [] \<Longrightarrow> am = \<langle>\<rangle>"
  using Tree2.inorder.elims by blast



context MDP_nat_disc
begin


lemma dist_opt_bound_\<L>\<^sub>b_split: "dist v \<nu>\<^sub>b_opt \<le> dist v (GS.\<L>\<^sub>b_split v) / (1 - l)"
  using contraction_\<L>_split_dist
  by (simp add: mult.commute mult_imp_le_div_pos)

lemma cert_\<L>\<^sub>b_split: 
  assumes "\<epsilon> \<ge> 0" "dist v (GS.\<L>\<^sub>b_split v) / (1 - l) \<le> \<epsilon>"
  shows "dist v \<nu>\<^sub>b_opt \<le> \<epsilon>"
  using assms dist_opt_bound_\<L>\<^sub>b_split order_trans by auto

definition "check_value_GS eps v \<longleftrightarrow> dist v (GS.\<L>\<^sub>b_split v) / (1 - l) \<le> eps"

definition "gs_policy_bound_error v = (
  let v' = (GS.\<L>\<^sub>b_split v); err = (2 * l) * dist v v' / (1 - l) in
  (err, d_GS_least v'))"

lemma \<L>\<^sub>b_split_eq_L_opt: "GS.\<L>\<^sub>b_split v = GS.L_split (d_GS_least v) v"
  by (simp add: GS_inv_def \<L>\<^sub>b_split_eq_GS_inv)

lemma L_split_fix_\<nu>:
  assumes "d \<in> D\<^sub>D"
  assumes "GS.L_split d v = v"
  shows "v = \<nu>\<^sub>b (mk_stationary_det d)"
proof -
  have "r_dec\<^sub>b (mk_dec_det d) = (id_blinfun - l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d)) v"
    using GS_inv_rec[of d v]
    unfolding GS_inv_def assms(2)  \<P>\<^sub>1_sum_lower_upper
    by (auto simp: blinfun.bilinear_simps algebra_simps)
  hence "v = (\<Sum>t. (l *\<^sub>R \<P>\<^sub>1 (mk_dec_det d))^^t) (r_dec\<^sub>b (mk_dec_det d))"
    using inv_norm_le'(2)[OF norm_\<P>\<^sub>1_l_less] by auto
  thus "v = \<nu>\<^sub>b (mk_stationary (mk_dec_det d))"
    by (auto simp: \<nu>_stationary blincomp_scaleR_right)
qed


lemma 
  assumes "gs_policy_bound_error v = (err, d)"
  shows "dist (\<nu>\<^sub>b (mk_stationary_det d)) \<nu>\<^sub>b_opt \<le> err"
proof (cases "l = 0")
  case True
  hence "gs_policy_bound_error v = (0, d_GS_least (GS.\<L>\<^sub>b_split v))"
    unfolding gs_policy_bound_error_def by auto
  have "GS.\<L>\<^sub>b_split v = GS.\<L>\<^sub>b_split \<nu>\<^sub>b_opt"
    by (auto simp: GS.\<L>\<^sub>b_split.rep_eq R_GS_def GS.\<L>_split_def simp del: GS.\<L>\<^sub>b_split_fix intro!: bfun_eqI) 
      (simp add: True)
  hence "GS.\<L>\<^sub>b_split v = \<nu>\<^sub>b_opt"
    by auto
  hence "\<nu>\<^sub>b (mk_stationary_det (d_GS_least (GS.\<L>\<^sub>b_split v))) = \<nu>\<^sub>b_opt"
    using GS.\<L>\<^sub>b_split_fix GS_inv_def Q_GS_def R_GS_def True \<L>\<^sub>b_split_eq_GS_inv \<nu>_stationary_inv 
    by force
  then show ?thesis
    using assms unfolding gs_policy_bound_error_def 
    by (auto simp: True)
next
  case False
  then show ?thesis
  proof (cases "GS.\<L>\<^sub>b_split v = v")
    case True
    have v_opt: "v = \<nu>\<^sub>b_opt"
      using GS.\<L>\<^sub>b_lim(1) GS.\<L>\<^sub>b_split_fix True by blast
    have *: "(\<nu>\<^sub>b (mk_stationary_det d) = v) = (GS.L_split d v = v)" if "d \<in> D\<^sub>D" for d v
      using that L_split_fix_\<nu> GS.L_split_fix by auto

    have "GS.L_split (d_GS_least \<nu>\<^sub>b_opt) \<nu>\<^sub>b_opt = \<nu>\<^sub>b_opt"
      using GS.\<L>\<^sub>b_split_fix \<L>\<^sub>b_split_eq_L_opt by auto
    hence "\<nu>\<^sub>b (mk_stationary_det (d_GS_least (GS.\<L>\<^sub>b_split v))) = \<nu>\<^sub>b_opt"
      using d_GS_least_is_dec by (auto simp: v_opt *)
    then show ?thesis
      using assms unfolding gs_policy_bound_error_def 
      by (auto simp: True)
  next
    case False
    hence 1: "dist v (GS.\<L>\<^sub>b_split v) > 0"
      by fastforce
    hence "2 * l * dist v (GS.\<L>\<^sub>b_split v) > 0"
      using \<open>l \<noteq> 0\<close> zero_le_disc by (simp add: less_le)
    hence "err > 0"
      using assms unfolding gs_policy_bound_error_def by auto
    hence "dist (\<nu>\<^sub>b (mk_stationary_det (d_GS_least (GS.\<L>\<^sub>b_split v)))) \<nu>\<^sub>b_opt < err'" if "err < err'" for err'
      using that assms
      unfolding gs_policy_bound_error_def
      by (auto simp: pos_divide_less_eq[symmetric] intro: find_policy_error_bound_gs)
    then show ?thesis
      using assms unfolding gs_policy_bound_error_def by force
  qed
qed

end

context MDP_Code
begin
definition "gs_policy_bound_error_code v = (
  let v' = fst (GS_iter v);
    d = if states = 0 then 0 else (MAX s \<in> {..< states}. dist (v_lookup v s) (v_lookup v' s));
   err = (2 * l) * d / (1 - l) in
  (err, find_policy_code v'))"


lemma 
  assumes "v_len v = states" "v_invar v"
  shows "D_Map.map_to_fun (snd (gs_policy_bound_error_code v)) = snd (MDP.gs_policy_bound_error (V_Map.map_to_bfun v))"
  unfolding MDP.gs_policy_bound_error_def  gs_policy_bound_error_code_def
  by (simp add: GS_iter'_correct GS_iter_aux_correct'' assms invar_GS_iter)

lemma
  assumes "v_len v = states" "v_invar v"
  shows "(fst (gs_policy_bound_error_code v)) = fst (MDP.gs_policy_bound_error (V_Map.map_to_bfun v))"
proof-
  have dist_zero_ge: "dist ((V_Map.map_to_bfun v) x) ((V_Map.map_to_bfun (fst (GS_iter v))) x) = 0" if "x \<ge> states" for x
    using assms that 
    by (auto simp: V_Map.map_to_bfun.rep_eq split: option.splits)
  have univ: "UNIV = {0..<states} \<union> {states..}" by auto
  let ?d = "\<lambda>x. dist ((V_Map.map_to_bfun v) x) ((V_Map.map_to_bfun (fst (GS_iter v))) x)"

  have fin: "finite (range (\<lambda>x. ?d x))"
    by (auto simp: dist_zero_ge univ Set.image_Un Set.image_constant[of states])
  have r: "range (\<lambda>x. ?d x) = ?d ` {..<states} \<union> ?d ` {states..}"
    by force
  hence "Sup (range ?d) = Max (range ?d)"
    using fin cSup_eq_Max by blast
  also have "\<dots> = (if states = 0 then (Max (?d ` {states..})) else max (Max (?d ` {..<states})) (Max (?d ` {states..})))"
    using r fin by (auto intro: Max_Un)
  also have "\<dots> = (if states = 0 then 0 else max (Max (?d ` {..<states})) 0)"
    using dist_zero_ge
    by (auto simp: Set.image_constant[of states] cSup_eq_Max[symmetric, of "(\<lambda>_. 0) ` {states..}"])
  also have "\<dots> = (if states = 0 then 0 else (Max (?d ` {..<states})))"
    by (auto intro!: max_absorb1 max_geI)
  finally have 1: "Sup (range ?d) = (if states = 0 then 0 else (Max (?d ` {..<states})))".
  thus ?thesis
    unfolding MDP.gs_policy_bound_error_def gs_policy_bound_error_code_def dist_bfun_def
    using assms GS_iter'_correct GS_iter_aux_correct'' invar_GS_iter
    apply auto
    using GS_iter_aux_correct GS_iter_def MDP.GS_rec_upto_correct V_Map.map_to_fun_def map_to_bfun_eq_fun by auto
qed

end


global_interpretation GS_Code: MDP_Code
  (* state map (transition system) *)
  "IArray.sub" "\<lambda>n x arr. IArray ((IArray.list_of arr)[n:= x])" "IArray.length" "IArray" "IArray.list_of" "\<lambda>_. True"

(* action map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.transitions (Rep_Valid_MDP mdp)" "MDP.states (Rep_Valid_MDP mdp)"

(* value map *)
starray_get "\<lambda>i x arr. starray_set arr i x"  starray_length starray_of_list  "\<lambda>arr. starray_foldr (\<lambda>x xs. x # xs) arr []" "\<lambda>_. True"

(* decision rule map *)
RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup Tree2.inorder rbt

"MDP.disc (Rep_Valid_MDP mdp)"

for mdp states l
defines GS_code = GS_Code.GS_code  
  and find_policy_code = GS_Code.find_policy_code
  and GS_policy_code = GS_Code.GS_policy_code
  and GS_code_aux = GS_Code.GS_code_aux
  and check_dist = GS_Code.check_dist
  and GS_iter = GS_Code.GS_iter
  and GS_iter_aux = GS_Code.GS_iter_aux  
  and \<L>_GS_code = GS_Code.\<L>_GS_code
  and L\<^sub>a_code = GS_Code.L\<^sub>a_code
  and a_lookup' = GS_Code.a_lookup'
  and d_lookup' = GS_Code.d_lookup'
  and v0 = GS_Code.v0
  and find_policy_code_aux = GS_Code.find_policy_code_aux
  and find_policy_code_aux_upt = GS_Code.find_policy_code_aux_upt
  and find_policy_state_code_aux' = GS_Code.find_policy_state_code_aux'
  and find_policy_state_code_aux = GS_Code.find_policy_state_code_aux
  and entries = M.entries
  and from_list = M.from_list
  and arr_tabulate = starray_Array.arr_tabulate

and v_map_from_list = GS_Code.v_map_from_list
and gs_policy_bound_error_code = GS_Code.gs_policy_bound_error_code
  using Rep_Valid_MDP 
  by unfold_locales 
    (fastforce simp: pmf_of_list_wf_def Ball_set_list_all[symmetric] case_prod_beta is_MDP_def M.invar_def M.entries_def M.is_empty_def RBT_Set.empty_def  length_0_conv[symmetric])+

lemmas entries_def[unfolded M.entries_def, code]
lemmas from_list_def[unfolded M.from_list_def, code]
lemmas arr_tabulate_def[unfolded starray_Array.arr_tabulate_def, code]

end