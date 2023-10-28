section \<open>Game for Coupled Similarity with Delay Formulation\<close>

theory Coupledsim_Game_Delay
imports
  Coupled_Simulation
  Simple_Game
begin

subsection \<open>The Coupled Simulation Preorder Game Using Delay Steps\<close>

datatype ('s, 'a) cs_game_node =
  AttackerNode 's 's |
  DefenderStepNode 'a 's 's |
  DefenderCouplingNode 's 's

fun (in lts_tau) cs_game_moves ::
  \<open>('s, 'a) cs_game_node \<Rightarrow> ('s, 'a) cs_game_node \<Rightarrow> bool\<close> where
  simulation_visible_challenge:
    \<open>cs_game_moves (AttackerNode p q) (DefenderStepNode a p1 q0) =
      (\<not>tau a \<and> p \<longmapsto>a p1 \<and> q = q0)\<close> |
  simulation_internal_attacker_move:
    \<open>cs_game_moves (AttackerNode p q) (AttackerNode p1 q0) =
      (\<exists>a. tau a \<and> p \<longmapsto>a p1 \<and> q = q0)\<close> |
  simulation_answer:
    \<open>cs_game_moves (DefenderStepNode a p1 q0) (AttackerNode p11 q1) =    
      (q0 =\<rhd>a q1 \<and> p1 = p11)\<close> |
  coupling_challenge:
    \<open>cs_game_moves (AttackerNode p q) (DefenderCouplingNode p0 q0) =
      (p = p0 \<and> q = q0)\<close> |
  coupling_answer:
    \<open>cs_game_moves (DefenderCouplingNode p0 q0) (AttackerNode q1 p00) =
      (p0 = p00 \<and> q0 \<longmapsto>* tau q1)\<close> |
  cs_game_moves_no_step:
    \<open>cs_game_moves _ _ = False\<close>

fun cs_game_defender_node :: \<open>('s, 'a) cs_game_node \<Rightarrow> bool\<close> where
  \<open>cs_game_defender_node (AttackerNode _ _) = False\<close> |
  \<open>cs_game_defender_node (DefenderStepNode _ _ _) = True\<close> |
  \<open>cs_game_defender_node (DefenderCouplingNode _ _) = True\<close>

locale cs_game =
  lts_tau trans \<tau> +
  simple_game cs_game_moves cs_game_defender_node
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>_  _" [70, 70, 70] 80) and
  \<tau> :: \<open>'a\<close>
begin

subsection \<open>Coupled Simulation Implies Winning Strategy\<close>

fun strategy_from_coupleddsim :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s, 'a) cs_game_node strategy\<close> where
  \<open>strategy_from_coupleddsim R ((DefenderStepNode a p1 q0)#play) =
    (AttackerNode p1 (SOME q1 . R p1 q1 \<and> q0 =\<rhd>a q1))\<close> |
  \<open>strategy_from_coupleddsim R ((DefenderCouplingNode p0 q0)#play) =
    (AttackerNode (SOME q1 . R q1 p0 \<and> q0 \<longmapsto>* tau q1) p0)\<close> |
  \<open>strategy_from_coupleddsim _ _ = undefined\<close>

lemma defender_preceded_by_attacker:
  assumes
    \<open>n0 # play \<in> plays (AttackerNode p0 q0)\<close>
    \<open>cs_game_defender_node n0\<close>
  shows
    \<open>\<exists> p q . hd play = AttackerNode p q \<and> cs_game_moves (AttackerNode p q) n0\<close>
    \<open>play \<noteq> []\<close>
proof -
  have n0_not_init: \<open>n0 \<noteq> (AttackerNode p0 q0)\<close> using assms(2) by auto
  hence \<open>cs_game_moves (hd play) n0\<close> using assms(1)
    by (metis list.sel(1) list.sel(3) plays.cases)
  thus \<open>\<exists>p q. hd play = AttackerNode p q \<and> cs_game_moves (AttackerNode p q) n0\<close> using assms(2)
    by (metis cs_game_defender_node.elims(2,3) local.cs_game_moves_no_step(1,2,3,6))
  show \<open>play \<noteq> []\<close> using n0_not_init assms(1) plays.cases by auto
qed

lemma defender_only_challenged_by_visible_actions:
  assumes
    \<open>(DefenderStepNode a p q) # play \<in> plays (AttackerNode p0 q0)\<close>
  shows
    \<open>\<not>tau a\<close>
  using assms defender_preceded_by_attacker
  by fastforce

lemma strategy_from_coupleddsim_retains_coupledsim:
  assumes
    \<open>R p0 q0\<close>
    \<open>coupled_delay_simulation R\<close>
    \<open>initial = AttackerNode p0 q0\<close>
    \<open>play \<in> plays_for_0strategy (strategy_from_coupleddsim R) initial\<close>
  shows
    \<open>hd play = AttackerNode p q \<Longrightarrow> R p q\<close>
    \<open>length play > 1 \<Longrightarrow> hd (tl play) = AttackerNode p q \<Longrightarrow> R p q\<close>
  using assms(4)
proof (induct arbitrary: p q rule: plays_for_0strategy.induct[OF assms(4)])
  case 1
  fix p q
  assume \<open>hd [initial] = AttackerNode p q\<close>
  hence \<open>p = p0\<close> \<open>q = q0\<close> using assms(3) by auto
  thus \<open>R p q\<close> using assms(1) by simp
next
  case 1
  fix p q
  assume \<open>1 < length [initial]\<close>
  hence False by auto
  thus \<open>R p q\<close>  ..
next
  case (2 n0 play)
  hence n0play_is_play: \<open>n0 # play \<in> plays initial\<close> using strategy0_plays_subset by blast
  fix p q
  assume subassms:
    \<open>hd (strategy_from_coupleddsim R (n0 # play) # n0 # play) = AttackerNode p q\<close>
    \<open>strategy_from_coupleddsim R (n0 # play) # n0 # play
      \<in> plays_for_0strategy (strategy_from_coupleddsim R) initial\<close>
  then obtain pi qi where 
      piqi_def: \<open>hd (play) = AttackerNode pi qi\<close>
        \<open>cs_game_moves (AttackerNode pi qi) n0\<close> \<open>play \<noteq> []\<close>
    using defender_preceded_by_attacker n0play_is_play `cs_game_defender_node n0` assms(3) by blast
  hence \<open>R pi qi\<close> using 2(1,3) by simp
  have \<open>(\<exists> a . n0 = (DefenderStepNode a p qi) \<and> \<not> tau a \<and> pi \<longmapsto>a p)
    \<or> (n0 = (DefenderCouplingNode pi qi))\<close>
    using piqi_def(2) 2(4,5) subassms(1)
    using cs_game_defender_node.elims(2) cs_game_moves.simps(1,3)
      cs_game_moves.simps(4) list.sel(1)
    by metis
  thus \<open>R p q\<close>
  proof safe
    fix a
    assume n0_def: \<open>n0 = DefenderStepNode a p qi\<close> \<open>\<not> tau a\<close> \<open>pi \<longmapsto>a p\<close>
    have \<open>strategy_from_coupleddsim R (n0 # play) =
        (AttackerNode p (SOME q1 . R p q1 \<and> qi =\<rhd>a q1))\<close>
      unfolding n0_def(1) by auto
    with subassms(1) have q_def: \<open>q = (SOME q1. R p q1 \<and> qi =\<rhd>a  q1)\<close> by auto
    have \<open>\<exists> qii . R p qii \<and> qi =\<rhd>a qii\<close>
      using n0_def(2,3) `R pi qi` `coupled_delay_simulation R`
      unfolding coupled_delay_simulation_def delay_simulation_def by blast
    from someI_ex[OF this] show \<open>R p q\<close> unfolding q_def by blast
  next
    assume n0_def: \<open>n0 = DefenderCouplingNode pi qi\<close>
    have \<open>strategy_from_coupleddsim R (n0 # play) =
        (AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi)\<close>
      unfolding n0_def(1) by auto
    with subassms(1) have qp_def:
      \<open>p = (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1)\<close> \<open>q = pi\<close> by auto
    have \<open>\<exists> q1 . R q1 pi \<and> qi \<longmapsto>* tau q1\<close>
      using n0_def `R pi qi` `coupled_delay_simulation R`
      unfolding coupled_delay_simulation_def by blast
    from someI_ex[OF this] show \<open>R p q\<close> unfolding qp_def by blast
  qed
next
  case (2 n0 play)
  fix p q
  assume \<open>hd (tl (strategy_from_coupleddsim R (n0 # play) # n0 # play)) = AttackerNode p q\<close>
  hence False using 2(4) by auto
  thus \<open>R p q\<close> ..
next
  case (3 n1 play n1')
  fix p q
  assume \<open>hd (n1' # n1 # play) = AttackerNode p q\<close>
  then obtain p1 a where n1_spec: \<open>n1 = AttackerNode p1 q\<close> \<open>p1 \<longmapsto>a p\<close> \<open>tau a\<close>
   using 3 list.sel(1) 
   by (metis cs_game_defender_node.elims(3) simulation_internal_attacker_move)
  then have \<open>R p1 q\<close> using 3 by auto
  thus \<open>R p q\<close> 
    using  n1_spec(2,3) \<open>coupled_delay_simulation R\<close>
    unfolding coupled_delay_simulation_def delay_simulation_def by auto
next
  case (3 n1 play n1')
  fix p q
  assume \<open>hd (tl (n1' # n1 # play)) = AttackerNode p q\<close>
  thus \<open>R p q\<close> using 3(1,2) by auto
qed

lemma strategy_from_coupleddsim_sound:
  assumes
    \<open>R p0 q0\<close>
    \<open>coupled_delay_simulation R\<close>
    \<open>initial = AttackerNode p0 q0\<close>
  shows
    \<open>sound_0strategy (strategy_from_coupleddsim R) initial\<close>
  unfolding sound_0strategy_def
proof clarify
  fix n0 play
  assume subassms:
    \<open>n0 # play \<in> plays_for_0strategy(strategy_from_coupleddsim R) initial\<close>
    \<open>cs_game_defender_node n0\<close>
  then obtain pi qi where
      piqi_def: \<open>hd (play) = AttackerNode pi qi\<close>
        \<open>cs_game_moves (AttackerNode pi qi) n0\<close> \<open>play \<noteq> []\<close>
    using defender_preceded_by_attacker `cs_game_defender_node n0` assms(3)
      strategy0_plays_subset by blast
  hence \<open>R pi qi\<close>
    using strategy_from_coupleddsim_retains_coupledsim[OF assms] list.sel subassms by auto
  have \<open>(\<exists> a p . n0 = (DefenderStepNode a p qi) \<and> pi \<longmapsto>a p)
    \<or> (n0 = (DefenderCouplingNode pi qi))\<close>
    by (metis cs_game_defender_node.elims(2)
        coupling_challenge simulation_visible_challenge piqi_def(2) subassms(2))
  thus \<open>cs_game_moves n0 (strategy_from_coupleddsim R (n0 # play))\<close>
  proof safe
    fix a p
    assume dsn:
      \<open>pi \<longmapsto>a  p\<close>
      \<open>n0 = DefenderStepNode a p qi\<close>
    hence qi_spec:
      \<open>(strategy_from_coupleddsim R (n0 # play)) =
        AttackerNode p (SOME q1 . R p q1 \<and> qi =\<rhd>a q1)\<close>
      by simp
    then obtain qii where qii_spec:
      \<open>AttackerNode p (SOME q1 . R p q1 \<and> qi =\<rhd>a q1) = AttackerNode p qii\<close> by blast
    have \<open>\<exists> qii . R p qii \<and> qi =\<rhd>a qii\<close>
      using dsn `R pi qi` `coupled_delay_simulation R` steps.refl 
      unfolding coupled_delay_simulation_def delay_simulation_def by blast
    from someI_ex[OF this] have \<open>R p qii \<and> qi =\<rhd>a qii\<close> using qii_spec by blast
    thus \<open>cs_game_moves (DefenderStepNode a p qi)
          (strategy_from_coupleddsim R (DefenderStepNode a p qi # play))\<close>
      using qi_spec qii_spec unfolding dsn(2) by auto
  next \<comment>\<open>coupling quite analogous.\<close>
    assume dcn:
      \<open>n0 = DefenderCouplingNode pi qi\<close>
    hence qi_spec:
      \<open>(strategy_from_coupleddsim R (n0 # play)) =
      AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi\<close>
      by simp
    then obtain qii where qii_spec:
      \<open>AttackerNode (SOME q1 . R q1 pi \<and> qi \<longmapsto>* tau q1) pi = AttackerNode qii pi\<close> by blast
    have \<open>\<exists> qii . R qii pi \<and> qi \<longmapsto>* tau qii\<close>
      using dcn `R pi qi` `coupled_delay_simulation R`
      unfolding coupled_delay_simulation_def by blast
    from someI_ex[OF this] have \<open>R qii pi \<and> qi \<longmapsto>* tau qii\<close> using qii_spec by blast
    thus \<open>cs_game_moves (DefenderCouplingNode pi qi)
        (strategy_from_coupleddsim R (DefenderCouplingNode pi qi # play))\<close>
      using qi_spec qii_spec unfolding dcn by auto
  qed
qed

lemma coupleddsim_implies_winning_strategy:
  assumes
    \<open>R p q\<close>
    \<open>coupled_delay_simulation R\<close>
    \<open>initial = AttackerNode p q\<close>
  shows
    \<open>player0_winning_strategy (strategy_from_coupleddsim R) initial\<close>
  unfolding player0_winning_strategy_def
proof (clarify)
  fix play
  assume subassms:
    \<open>play \<in> plays_for_0strategy (strategy_from_coupleddsim R) initial\<close>
    \<open>player1_wins_immediately play\<close>
  show \<open>False\<close> using subassms
  proof (induct rule: simple_game.plays_for_0strategy.induct[OF subassms(1)])
    case 1
    then show ?case unfolding player1_wins_immediately_def using assms(3) by auto
  next
    case (2 n0 play)
    hence \<open>\<not> cs_game_defender_node (strategy_from_coupleddsim R (n0 # play))\<close>
      using cs_game_moves_no_step cs_game_defender_node.elims(2) by metis
    hence \<open>\<not>  player1_wins_immediately (strategy_from_coupleddsim R (n0 # play) # n0 # play)\<close>
      unfolding player1_wins_immediately_def by auto
    thus ?case using 2(6) by auto
  next
    case (3 n1 play n1')
    then obtain p q where n1_def: \<open>n1 = AttackerNode p q\<close>
      using cs_game_defender_node.elims(3) by blast
    hence \<open>R p q\<close>
      using strategy_from_coupleddsim_retains_coupledsim[OF assms, of \<open>n1 # play\<close>] 3(1)
      by auto
    have \<open>(\<exists> p1 a . n1' = (DefenderStepNode a p1 q) \<and> (p \<longmapsto>a p1))
        \<or> n1' = (DefenderCouplingNode p q)\<close>
      using n1_def `cs_game_moves n1 n1'` coupling_challenge cs_game_moves_no_step(5)
        simulation_visible_challenge "3.prems"(2) cs_game_defender_node.elims(1) list.sel(1)
      unfolding player1_wins_immediately_def
      by metis
    then show ?case
    proof 
      assume \<open>(\<exists> p1 a . n1' = (DefenderStepNode a p1 q) \<and> (p \<longmapsto>a p1))\<close>
      then obtain p1 a where 
        n1'_def: \<open>n1' = (DefenderStepNode a p1 q)\<close> \<open>p \<longmapsto>a p1\<close>
        by blast
      hence \<open>\<exists> q1 . q =\<rhd>a q1\<close> 
        using `R p q` `coupled_delay_simulation R`
        unfolding coupled_delay_simulation_def delay_simulation_def by blast
      hence \<open>\<exists> q1 . cs_game_moves (DefenderStepNode a p1 q) (AttackerNode p1 q1)\<close>
        by auto
      with `player1_wins_immediately (n1' # n1 # play)` show False
        unfolding player1_wins_immediately_def n1'_def
        by (metis list.sel(1))
    next
      assume n1'_def: \<open>n1' = DefenderCouplingNode p q\<close>
      have \<open>\<exists> q1 . q \<longmapsto>*tau q1\<close> 
        using `coupled_delay_simulation R` `R p q`
        unfolding coupled_delay_simulation_def by blast
      hence \<open>\<exists> q1 . cs_game_moves (DefenderCouplingNode p q) (AttackerNode q1 p)\<close>
        by auto
      with `player1_wins_immediately (n1' # n1 # play)` show False
        unfolding player1_wins_immediately_def n1'_def
        by (metis list.sel(1))
    qed
  qed
qed

subsection \<open>Winning Strategy Induces Coupled Simulation\<close>

lemma winning_strategy_implies_coupleddsim:
  assumes
    \<open>player0_winning_strategy f initial\<close>
    \<open>sound_0strategy f initial\<close>
  defines
    \<open>R == \<lambda> p q . (\<exists> play \<in> plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
  shows
    \<open>coupled_delay_simulation R\<close>
  unfolding coupled_delay_simulation_def delay_simulation_def
proof safe
  fix p q p' a
  assume challenge:
    \<open>R p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
    \<open>tau a \<close>
  hence game_move: \<open>cs_game_moves (AttackerNode p q) (AttackerNode p' q)\<close> by auto
  have \<open>(\<exists> play \<in> plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
    using challenge(1) assms by blast
  then obtain play where
      play_spec: \<open>AttackerNode p q # play \<in> plays_for_0strategy f initial\<close>
    by (metis list.sel(1) simple_game.plays.cases strategy0_plays_subset)
  hence interplay:
      \<open>(AttackerNode p' q) # AttackerNode p q # play \<in> plays_for_0strategy f initial\<close>
    using game_move by (simp add: simple_game.plays_for_0strategy.p1move)
  then show \<open>R p' q\<close>
    unfolding R_def list.sel by force
next
  fix p q p' a
  assume challenge:
    \<open>R p q\<close>
    \<open>p \<longmapsto>a  p'\<close>
    \<open>\<not> tau a \<close>
  hence game_move: \<open>cs_game_moves (AttackerNode p q) (DefenderStepNode a p' q)\<close> by auto
  have \<open>(\<exists> play \<in> plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
    using challenge(1) assms by blast
  then obtain play where
      play_spec: \<open>AttackerNode p q # play \<in> plays_for_0strategy f initial\<close>
    by (metis list.sel(1) simple_game.plays.cases strategy0_plays_subset)
  hence interplay:
      \<open>(DefenderStepNode a p' q) # AttackerNode p q # play \<in> plays_for_0strategy f initial\<close>
    using game_move by (simp add: simple_game.plays_for_0strategy.p1move)
  hence \<open>\<not> player1_wins_immediately ((DefenderStepNode a p' q) # AttackerNode p q # play)\<close>
    using assms(1) unfolding player0_winning_strategy_def by blast
  then obtain n1 where n1_def:
      \<open>n1 = f (DefenderStepNode a p' q # AttackerNode p q # play)\<close>
      \<open>cs_game_moves (DefenderStepNode a p' q) n1\<close>
    using interplay assms(2) unfolding player0_winning_strategy_def sound_0strategy_def by simp
  obtain q' where q'_spec:
      \<open>(AttackerNode p' q') = n1\<close> \<open>q =\<rhd>a q'\<close>
    using n1_def(2) by (cases n1, auto)
  hence \<open>(AttackerNode p' q') # (DefenderStepNode a p' q) # AttackerNode p q # play
      \<in> plays_for_0strategy f initial\<close>
    using interplay n1_def by (simp add: simple_game.plays_for_0strategy.p0move)
  hence \<open>R p' q'\<close> unfolding R_def by (meson list.sel(1))
  thus \<open>\<exists>q'. R p' q' \<and> q =\<rhd>a  q'\<close> using q'_spec(2) by blast
next
  fix p q 
  assume challenge:
    \<open>R p q\<close>
  hence game_move: \<open>cs_game_moves (AttackerNode p q) (DefenderCouplingNode p q)\<close> by auto
  have \<open>(\<exists> play \<in> plays_for_0strategy f initial . hd play = AttackerNode p q)\<close>
    using challenge assms by blast
  then obtain play where
      play_spec: \<open>AttackerNode p q # play \<in> plays_for_0strategy f initial\<close>
    by (metis list.sel(1) simple_game.plays.cases strategy0_plays_subset)
  hence interplay: \<open>(DefenderCouplingNode p q) # AttackerNode p q # play
      \<in> plays_for_0strategy f initial\<close>
    using game_move by (simp add: simple_game.plays_for_0strategy.p1move)
  hence \<open>\<not> player1_wins_immediately ((DefenderCouplingNode p q) # AttackerNode p q # play)\<close>
    using assms(1) unfolding player0_winning_strategy_def by blast
  then obtain n1 where n1_def:
      \<open>n1 = f (DefenderCouplingNode p q # AttackerNode p q # play)\<close>
      \<open>cs_game_moves (DefenderCouplingNode p q) n1\<close>
    using interplay assms(2)
    unfolding player0_winning_strategy_def sound_0strategy_def by simp
  obtain q' where q'_spec:
      \<open>(AttackerNode q' p) = n1\<close> \<open>q \<longmapsto>* tau q'\<close>
    using n1_def(2) by (cases n1, auto)
  hence \<open>(AttackerNode q' p) # (DefenderCouplingNode p q) # AttackerNode p q # play
      \<in> plays_for_0strategy f initial\<close>
    using interplay n1_def by (simp add: simple_game.plays_for_0strategy.p0move)
  hence \<open>R q' p\<close> unfolding R_def by (meson list.sel(1))
  thus \<open>\<exists>q'. q \<longmapsto>* tau  q' \<and> R q' p\<close> using q'_spec(2) by blast
qed

theorem winning_strategy_iff_coupledsim:
  assumes
    \<open>initial = AttackerNode p q\<close>
  shows 
    \<open>(\<exists> f . player0_winning_strategy f initial \<and> sound_0strategy f initial)
    = p \<sqsubseteq>cs q\<close>
proof (rule)
  assume
    \<open>(\<exists>f. player0_winning_strategy f initial \<and> sound_0strategy f initial)\<close>
  then obtain f where
    \<open>coupled_delay_simulation (\<lambda>p q. \<exists>play\<in>plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
    using winning_strategy_implies_coupleddsim by blast
  moreover have \<open>(\<lambda>p q. \<exists>play\<in>plays_for_0strategy f initial. hd play = AttackerNode p q) p q\<close>
    using assms plays_for_0strategy.init by force
  ultimately show \<open>p \<sqsubseteq>cs q\<close>
    unfolding coupled_sim_by_eq_coupled_delay_simulation
    by (metis (mono_tags, lifting))
next
  assume
    \<open>p \<sqsubseteq>cs  q\<close>
  thus \<open>(\<exists>f. player0_winning_strategy f initial \<and> sound_0strategy f initial)\<close>
    unfolding coupled_sim_by_eq_coupled_delay_simulation
    using coupleddsim_implies_winning_strategy[OF _ _ assms]
          strategy_from_coupleddsim_sound[OF _ _ assms] by blast
qed

end
end
