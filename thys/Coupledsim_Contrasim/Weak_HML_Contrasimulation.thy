section \<open>Weak HML and the Contrasimulation Set Game\<close>

theory Weak_HML_Contrasimulation
  imports
    Contrasim_Set_Game
    HM_Logic_Infinitary
begin

subsection \<open> Distinguishing Formulas at Winning Attacker Positions\<close>

locale c_game_with_attacker_strategy  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> +
fixes
  strat :: \<open>('s, 'a) c_set_game_node posstrategy\<close> and
  attacker_winning_region :: \<open>('s, 'a) c_set_game_node set\<close> and
  attacker_order
defines
  \<open>attacker_order \<equiv> {(g', g). c_set_game_moves g g' \<and>
      g \<in> attacker_winning_region \<and> g' \<in> attacker_winning_region \<and>
      (player1_position g \<longrightarrow> g' = strat g)}\<^sup>+\<close>
assumes
  finite_win:
    \<open>wf attacker_order\<close> and
  strat_stays_winning:
    \<open>g \<in> attacker_winning_region \<Longrightarrow> player1_position g \<Longrightarrow>
      strat g \<in> attacker_winning_region \<and> c_set_game_moves g (strat g)\<close> and
  defender_keeps_losing:
    \<open>g \<in> attacker_winning_region \<Longrightarrow> c_set_game_defender_node g \<Longrightarrow> c_set_game_moves g g'
    \<Longrightarrow> g' \<in> attacker_winning_region\<close>
begin

text \<open>This construction of attacker formulas from a game only works if \<open>strat\<close> is a well-founded
  attacker strategy. (If it's winning and sound, the constructed formula should be distinguishing.)\<close>

function attack_formula :: \<open>('s, 'a) c_set_game_node \<Rightarrow> ('a,'s) HML_formula\<close> where
  \<open>attack_formula (AttackerNode p Q) =
    (if (AttackerNode p Q) \<in> attacker_winning_region
      then attack_formula (strat (AttackerNode p Q))
      else HML_true)\<close>
| \<open>attack_formula (DefenderSimNode a p Q) =
    (if (DefenderSimNode a p Q) \<in> attacker_winning_region
      then \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p (dsuccs a Q)))
      else HML_true)\<close>
| \<open>attack_formula (DefenderSwapNode p Q) =
    (if Q = {} \<or> DefenderSwapNode p Q \<notin> attacker_winning_region
      then HML_true
      else (HML_weaknor (weak_tau_succs Q)
        (\<lambda>q. if q \<in> (weak_tau_succs Q)
              then (attack_formula (AttackerNode q {p}))
              else HML_true )))\<close>
  using c_set_game_defender_node.cases
  by (auto, blast)

termination attack_formula
  using finite_win
proof (standard, safe)
  fix p Q
  assume \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
  thus \<open>(strat (AttackerNode p Q), AttackerNode p Q) \<in> attacker_order\<close>
    unfolding attacker_order_def
    using strat_stays_winning
    by auto
next
  fix a p Q
  assume attacker_wins: \<open>DefenderSimNode a p Q \<in> attacker_winning_region\<close>
  hence \<open>AttackerNode p (dsuccs a Q) \<in> attacker_winning_region\<close>
    using defender_keeps_losing simulation_answer by force
  with attacker_wins show
    \<open>(AttackerNode p (dsuccs a Q), DefenderSimNode a p Q) \<in> attacker_order\<close>
    unfolding attacker_order_def
    by (simp add: r_into_trancl')
next
  fix p Q q' q
  assume case_assms:
    \<open>q' \<in> weak_tau_succs Q\<close>
    \<open>(AttackerNode q' {p}, DefenderSwapNode p Q) \<notin> attacker_order\<close>
    \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close>
    \<open>q \<in> Q\<close>
  hence \<open>AttackerNode q' {p} \<notin> attacker_winning_region\<close>
    unfolding attacker_order_def by auto
  moreover from case_assms have \<open>AttackerNode q' {p} \<in> attacker_winning_region\<close>
    using swap_answer defender_keeps_losing by force
  ultimately show \<open>q \<in> {}\<close> by blast
qed

lemma attacker_defender_switch:
  assumes
    \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
  shows
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or>(\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p' )\<close>
  using strat_stays_winning[OF assms] by (cases \<open>strat (AttackerNode p Q)\<close>, auto)

lemma attack_options: 
  assumes
    \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
  shows
    \<open>(\<exists>a p'. p =\<rhd>a p' \<and> \<not>tau a \<and> strat (AttackerNode p Q) = (DefenderSimNode a p' Q) \<and>
      attack_formula (AttackerNode p Q)
      = \<langle>\<tau>\<rangle>\<langle>a\<rangle>(attack_formula (AttackerNode p' (dsuccs a Q))))
    \<or> (\<exists>p'. p \<longmapsto>* tau p' \<and> strat (AttackerNode p Q) = (DefenderSwapNode p' Q) \<and>
      attack_formula (AttackerNode p Q) =
      (HML_weaknor (weak_tau_succs Q) (\<lambda>q. 
        if q \<in> (weak_tau_succs Q)
          then (attack_formula (AttackerNode q {p'}))
          else HML_true )))
    \<or> (Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true)\<close>
proof -
  from assms have
    \<open>attack_formula (AttackerNode p Q) = attack_formula (strat (AttackerNode p Q))\<close>
    by simp
  moreover from attacker_defender_switch assms have
    \<open>(\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or> (\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p')\<close>
    by blast
  ultimately have 
    \<open> (\<exists>a p'. (strat (AttackerNode p Q)) = (DefenderSimNode a p' Q) \<and>
      (attack_formula (AttackerNode p Q))
       = attack_formula (DefenderSimNode a p' Q) \<and> p  =\<rhd>a p' \<and> \<not>tau a)
    \<or> (\<exists>p'. (strat (AttackerNode p Q)) = (DefenderSwapNode p' Q) \<and>
      (attack_formula (AttackerNode p Q))
       = attack_formula (DefenderSwapNode p' Q) \<and> p \<longmapsto>* tau p')\<close>
    by metis
  moreover from assms have \<open>strat (AttackerNode p Q) \<in> attacker_winning_region\<close>
    by (simp add: strat_stays_winning)
  ultimately show ?thesis using assms empty_iff 
    by fastforce
qed

lemma distinction_soundness:
  fixes p Q p0 Q0
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>pQ \<in> attacker_winning_region\<close>
  shows
    \<open>p \<Turnstile> \<phi> \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> \<phi>)\<close>
  using finite_win assms
proof (induct arbitrary: p Q \<phi>)
  case (less p Q)
  from attack_options[OF this(2)] show ?case
  proof
    assume \<open>\<exists>a p'. p =\<rhd> a  p' \<and> \<not> tau a \<and>
      strat (AttackerNode p Q) = DefenderSimNode a p' Q \<and>
      attack_formula (AttackerNode p Q) = \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
    then obtain a p' where case_assms:
      \<open>p =\<rhd> a  p' \<and> \<not> tau a\<close>
      \<open>strat (AttackerNode p Q) = DefenderSimNode a p' Q\<close>
      \<open>attack_formula (AttackerNode p Q)
      = \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close> by blast
    hence moves:
      \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
      \<open>c_set_game_moves (DefenderSimNode a p' Q) (AttackerNode p' (dsuccs a Q))\<close> by auto
    with case_assms less(2) defender_keeps_losing strat_stays_winning have all_winning:
      \<open>(AttackerNode p' (dsuccs a Q)) \<in> attacker_winning_region\<close>
      \<open>(DefenderSimNode a p' Q) \<in> attacker_winning_region\<close>
        by (metis c_set_game_defender_node.simps(2), force)
    with case_assms moves less(2) have
      \<open>(AttackerNode p' (dsuccs a Q), DefenderSimNode a p' Q) \<in> attacker_order\<close>
      \<open>(DefenderSimNode a p' Q, AttackerNode p Q) \<in> attacker_order\<close>
      unfolding attacker_order_def by (simp add: r_into_trancl')+
    hence \<open>(AttackerNode p' (dsuccs a Q), AttackerNode p Q) \<in> attacker_order\<close>
      unfolding attacker_order_def by auto
    with less.hyps all_winning(1) have
      \<open>p' \<Turnstile> attack_formula (AttackerNode p' (dsuccs a Q)) \<and>
      (\<forall>q\<in>(dsuccs a Q). \<not> q \<Turnstile> attack_formula (AttackerNode p' (dsuccs a Q)))\<close>
      by blast
    with case_assms have
      \<open>p \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
      \<open>\<forall>q\<in>Q. \<not>q \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>attack_formula (AttackerNode p' (dsuccs a Q))\<close>
      unfolding dsuccs_def by (auto, blast+)
    thus ?case unfolding case_assms by blast
  next
    assume \<open>(\<exists>p'. p \<longmapsto>* tau  p' \<and> strat (AttackerNode p Q) = DefenderSwapNode p' Q \<and>
        attack_formula (AttackerNode p Q)
        = HML_weaknor (weak_tau_succs Q) (\<lambda>q.
          if q \<in> (weak_tau_succs Q)
            then attack_formula (AttackerNode q {p'})
            else HML_true)) \<or>
      Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true\<close>
    thus ?case
    proof
      assume \<open>\<exists>p'. p \<longmapsto>* tau  p' \<and> strat (AttackerNode p Q) = DefenderSwapNode p' Q \<and>
        attack_formula (AttackerNode p Q)
        = HML_weaknor (weak_tau_succs Q) (\<lambda>q.
          if q \<in> (weak_tau_succs Q)
            then attack_formula (AttackerNode q {p'})
            else HML_true)\<close>
      then obtain p' where case_assms:
        \<open>p \<longmapsto>* tau  p'\<close>
        \<open>strat (AttackerNode p Q) = DefenderSwapNode p' Q\<close>
        \<open>attack_formula (AttackerNode p Q)
        = HML_weaknor (weak_tau_succs Q) (\<lambda>q.
          if q \<in> (weak_tau_succs Q)
          then attack_formula (AttackerNode q {p'})
          else HML_true)\<close>
        by blast
      from case_assms have moves:
        \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p' Q)\<close>
        \<open>\<forall>q'\<in>(weak_tau_succs Q).
          c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q' {p'})\<close>
        by auto
      with case_assms less(2) defender_keeps_losing strat_stays_winning
        have all_winning:
          \<open>(DefenderSwapNode p' Q) \<in> attacker_winning_region\<close>
          \<open>\<forall>q'\<in>(weak_tau_succs Q). (AttackerNode q' {p'}) \<in> attacker_winning_region\<close>
        by (metis, metis c_set_game_defender_node.simps(1,3))
      with case_assms moves less(2) have
        \<open>\<forall>q'\<in> weak_tau_succs Q. (AttackerNode q' {p'}, DefenderSwapNode p' Q) \<in> attacker_order\<close>
        \<open>(DefenderSwapNode p' Q, AttackerNode p Q) \<in> attacker_order\<close>
        unfolding attacker_order_def by (simp add: r_into_trancl')+
      hence \<open>\<forall>q'\<in> weak_tau_succs Q. (AttackerNode q' {p'}, AttackerNode p Q) \<in> attacker_order\<close>
        unfolding attacker_order_def by auto
      with less.hyps all_winning have
        \<open>\<forall>q'\<in> weak_tau_succs Q.
          q' \<Turnstile> attack_formula (AttackerNode q' {p'}) \<and>
          \<not> p' \<Turnstile> attack_formula (AttackerNode q' {p'})\<close>
        by blast
      with case_assms have
        \<open>p' \<Turnstile> HML_conj (weak_tau_succs Q)
          (\<lambda>q'. HML_neg (attack_formula (AttackerNode q' {p'})))\<close>
        \<open>\<forall>q'\<in> weak_tau_succs Q.
          \<not> q' \<Turnstile> HML_conj (weak_tau_succs Q)
          (\<lambda>qq'. HML_neg (attack_formula (AttackerNode qq' {p'})))\<close>
        by (simp, fastforce)
      with case_assms have
        \<open>p \<Turnstile> HML_weaknor (weak_tau_succs Q)
          (\<lambda>q. if q \<in> (weak_tau_succs Q)
            then attack_formula (AttackerNode q {p'})
            else HML_true)\<close>
        \<open>\<forall>q\<in>Q. \<not>q \<Turnstile>  HML_weaknor (weak_tau_succs Q)
          (\<lambda>q. if q \<in> (weak_tau_succs Q)
            then attack_formula (AttackerNode q {p'})
            else HML_true)\<close>
        unfolding weak_tau_succs_def HML_weaknor_def
        using conj_only_depends_on_indexset by (auto, force, fastforce)
      thus ?case unfolding case_assms by blast
    next
      assume \<open>Q = {} \<and> attack_formula (AttackerNode p Q) = HML_true\<close>
      thus ?case by auto
    qed
  qed
qed

lemma distinction_in_language:
  fixes p Q
  defines
    \<open>pQ == AttackerNode p Q\<close>
  defines
    \<open>\<phi> == attack_formula pQ\<close>
  assumes
    \<open>pQ \<in> attacker_winning_region\<close>
  shows
    \<open>\<phi> \<in> HML_weak_formulas\<close>
  using assms(2,3) unfolding assms(1)
proof (induct arbitrary: \<phi> rule: attack_formula.induct)
  case (1 p Q)
  then show ?case using strat_stays_winning by auto
next
  case (2 a p Q)
  then show ?case
    by (simp add: HML_weak_formulas.Base HML_weak_formulas.Obs)
next
  case (3 p Q)
  hence \<open>\<forall>q' \<in> weak_tau_succs Q. attack_formula (AttackerNode q' {p}) \<in> HML_weak_formulas\<close>
    using weak_tau_succs_def HML_weak_formulas.Base by fastforce
  then show ?case
    using HML_weak_formulas.Base \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close>
    by (auto simp add: HML_weak_formulas.Conj)
qed

end

subsection \<open>Attacker Wins on Pairs with Distinguishing Formulas\<close>

locale c_game_with_attacker_formula  =
  c_set_game trans \<tau>
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> 
begin

inductive_set attacker_winning_region :: \<open>('s, 'a) c_set_game_node set\<close> where
  Base: \<open>DefenderSwapNode _ {} \<in> attacker_winning_region\<close> |
  Atk: \<open>(c_set_game_moves (AttackerNode p Q) g' \<and> g' \<in> attacker_winning_region)
    \<Longrightarrow> (AttackerNode p Q) \<in> attacker_winning_region\<close> |
  Def: \<open>c_set_game_defender_node g \<Longrightarrow>
    (\<And>g'. c_set_game_moves g g' \<Longrightarrow> g' \<in> attacker_winning_region)
    \<Longrightarrow> g \<in> attacker_winning_region\<close>

lemma attacker_wins_if_defender_set_empty: 
  assumes
    \<open>Q = {}\<close>
  shows
    \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
proof - 
  have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p Q)\<close> 
    by (simp add: steps.refl)
  have \<open>DefenderSwapNode p Q \<in> attacker_winning_region\<close>
    using assms attacker_winning_region.Base by simp
  thus ?thesis using atk_move attacker_winning_region.Atk by blast
qed

lemma attacker_wr_propagation: 
  assumes 
    \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close>
    \<open>p =\<rhd>a p'\<close>
    \<open>\<not>tau a\<close>
  shows
    \<open>AttackerNode p Q \<in> attacker_winning_region\<close>
proof - 
  have AtkToSim: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSimNode a p' Q)\<close>
    using assms(2, 3) by simp
  have \<open>\<forall>g. c_set_game_moves 
        (DefenderSimNode a p' Q) g 
        \<longrightarrow> (g = AttackerNode p' (dsuccs a Q))\<close>
    by (simp add: csg_move_defsimnode_to_atknode)
  hence \<open>(DefenderSimNode a p' Q) \<in> attacker_winning_region\<close> 
    using assms(1) attacker_winning_region.Def
    by (metis c_set_game_defender_node.simps(2))
  thus ?thesis using AtkToSim attacker_winning_region.Atk by blast
qed

lemma distinction_completeness: 
  assumes 
    \<open>\<phi> \<in> HML_weak_formulas\<close>
    \<open>distinguishes_from_set \<phi> p Q\<close>
  shows
    \<open>(AttackerNode p Q) \<in> attacker_winning_region\<close>
proof (cases \<open>Q = {}\<close>)
  case True
  then show ?thesis using attacker_wins_if_defender_set_empty by auto
next
  case False
  then show ?thesis using assms
  proof (induct arbitrary: p Q rule: HML_weak_formulas.induct[OF assms(1)])
    case Base: 1
    have \<open>\<forall>q. q \<Turnstile> HML_true\<close> by simp
    hence \<open>False\<close> 
      using Base.prems(1, 3) by simp
    then show ?case by auto
  next
    case Obs: (2 \<phi> a)
    then obtain p' where p'_def: \<open>p =\<rhd>a p' \<and> p' \<Turnstile> \<phi> \<close> 
      using tau_a_obs_implies_delay_step[of p a \<phi>] by auto
    have \<open>\<forall>q. q \<in> Q \<longrightarrow> \<not> q \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>\<close> using Obs by auto
    hence \<open>\<forall>q. q \<in> Q \<longrightarrow> (\<forall>q'.  \<not>q  =\<rhd>a  q' \<or> \<not>q' \<Turnstile> \<phi>)\<close>
      using delay_step_implies_tau_a_obs by blast
    hence \<open>\<forall>q'. q' \<in> dsuccs a Q \<longrightarrow> \<not> q' \<Turnstile> \<phi>\<close> 
      unfolding dsuccs_def by blast
    hence phi_distinguishing: \<open>distinguishes_from_set \<phi> p' (dsuccs a Q)\<close> 
      using p'_def by simp
    thus ?case
    proof (cases \<open>dsuccs a Q = {}\<close>)
      case dsuccs_empty: True
      then show ?thesis
      proof (cases \<open>tau a\<close>)
        case True
        hence \<open>{q1. \<exists>q\<in> Q. q \<longmapsto>* tau q1} = {}\<close> using dsuccs_def dsuccs_empty by auto
        hence \<open>Q = {}\<close> using steps.refl by blast
        then show ?thesis using attacker_wins_if_defender_set_empty by auto
      next
        case False
        hence \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close> 
          using attacker_wins_if_defender_set_empty dsuccs_empty by auto
        thus ?thesis using attacker_wr_propagation False p'_def by blast
      qed
    next
      case False
      hence wr_pred_atk_node: 
        \<open>AttackerNode p' (dsuccs a Q) \<in> attacker_winning_region\<close> 
        using Obs.hyps phi_distinguishing 
        by auto
      thus ?thesis 
      proof(cases \<open>tau a\<close>)
        case True
        hence \<open>\<forall>p. (p \<Turnstile> \<langle>\<tau>\<rangle>\<langle>a\<rangle>\<phi>) = (p  \<Turnstile> \<phi>)\<close>
          using delay_step_implies_tau_a_obs p'_def satisfies.simps(4) tau_tau 
            Obs.hyps(1) weak_backwards_truth
          by (meson lts.refl)
        hence \<open>distinguishes_from_set \<phi> p Q\<close> using Obs.prems by auto
        thus ?thesis using Obs.hyps Obs.prems by blast
      next
        case False
        then show ?thesis 
          using wr_pred_atk_node attacker_wr_propagation p'_def 
          by blast
      qed
    qed
  next
    case Conj: (3 I F)
    then obtain p' where \<open>p \<Rightarrow>^\<tau> p'\<close> and p_sat:  \<open>p' \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      unfolding HML_weaknor_def by auto
    have \<open>\<And>q . q \<in> Q  \<Longrightarrow> \<not>q  \<Turnstile>  HML_poss \<tau> (HML_conj I (\<lambda>f. HML_neg (F f)))\<close>
      by (metis Conj.prems(3) HML_weaknor_def distinguishes_from_set.elims(2))
    hence \<open>\<And>q q'. q \<in> Q \<Longrightarrow> \<not>q \<Rightarrow>^\<tau> q' \<or> \<not>q'  \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      using satisfies.simps(4) tau_tau by blast
    hence \<open>\<And>q'. \<not>q' \<in> (weak_tau_succs Q) \<or> \<not>q'  \<Turnstile> HML_conj I (\<lambda>f. HML_neg (F f))\<close>
      using weak_tau_succs_def by auto
    hence Ex: \<open>\<And>q'.  q' \<in> (weak_tau_succs Q) \<Longrightarrow> (\<exists>i. i \<in> I \<and> q'  \<Turnstile>  (F i))\<close>
      by auto
    have atk_move: \<open>c_set_game_moves (AttackerNode p Q) (DefenderSwapNode p' Q)\<close>
      using \<open>p \<Rightarrow>^\<tau> p'\<close> by auto
    have Ex_i:
      \<open>\<forall>q1 P1. c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1) \<longrightarrow>
        (\<exists>i. i \<in> I \<and> q1  \<Turnstile>  (F i)) \<and> P1 = {p'}\<close>
      using Ex by auto
    hence \<open>\<forall>q1 P1.
      c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1)
      \<longrightarrow> (\<exists>i. i \<in> I \<and> q1  \<Turnstile>  (F i) \<and> (\<forall>p'. p' \<in> P1 \<longrightarrow> \<not> p' \<Turnstile> (F i)))\<close>
      using p_sat by auto
    hence  \<open>\<forall>q1 P1. 
      c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1)
      \<longrightarrow> (\<exists>i. i \<in> I \<and> distinguishes_from_set (F i) q1 P1)\<close> 
      unfolding distinguishes_from_set.simps using p_sat by blast
    hence all_atk_succs_in_wr: 
      \<open>\<forall>q1 P1. c_set_game_moves (DefenderSwapNode p' Q) (AttackerNode q1 P1)
        \<longrightarrow> (AttackerNode q1 P1 \<in> attacker_winning_region)\<close> 
      using Conj.hyps Ex_i by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g
        \<longrightarrow> (\<exists> q1 P1. g = (AttackerNode q1 P1))\<close> 
      using csg_move_defswapnode_to_atknode by blast
    hence \<open>\<forall>g. c_set_game_moves (DefenderSwapNode p' Q) g
        \<longrightarrow> g \<in> attacker_winning_region\<close> 
      using all_atk_succs_in_wr by auto
    hence \<open>DefenderSwapNode p' Q \<in> attacker_winning_region\<close> 
      using attacker_winning_region.Def
      by (meson c_set_game_defender_node.simps(3)) 
    then show ?case using atk_move attacker_winning_region.Atk by blast
  qed
qed

end
end
