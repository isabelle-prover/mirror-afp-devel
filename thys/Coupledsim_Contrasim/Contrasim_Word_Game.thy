section \<open>The Contrasimulation Preorder Word Game\<close>

theory Contrasim_Word_Game
imports
  Simple_Game
  Contrasimulation
begin

datatype ('s, 'a) c_word_game_node =
  AttackerNode 's 's |
  DefenderNode "'a list" 's 's

fun (in lts_tau) c_word_game_moves ::
  \<open>('s, 'a) c_word_game_node \<Rightarrow> ('s, 'a) c_word_game_node \<Rightarrow> bool\<close> where
                             
  simulation_challenge:
   \<open>c_word_game_moves (AttackerNode p q) (DefenderNode A p1 q0) =
     (p \<Rightarrow>$A p1 \<and> q = q0 \<and> (\<forall>a\<in>set A. a \<noteq> \<tau>))\<close> |     

  simulation_answer:                        
    \<open>c_word_game_moves (DefenderNode A p1 q0) (AttackerNode q1 p10) =
      (q0 \<Rightarrow>$A q1 \<and> p1 = p10)\<close> |                                             
                                             
  c_word_game_moves_no_step:               
    \<open>c_word_game_moves _ _ = False\<close>

fun c_word_game_defender_node :: \<open>('s, 'a) c_word_game_node \<Rightarrow> bool\<close> where
  \<open>c_word_game_defender_node (AttackerNode _ _) = False\<close> |
  \<open>c_word_game_defender_node (DefenderNode _ _ _) = True\<close>


subsection \<open>Contrasimulation Implies Winning Strategy in Word Game (Completeness)\<close>

locale c_word_game =
  lts_tau trans \<tau> +
  simple_game c_word_game_moves c_word_game_defender_node
for
  trans :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> and
  \<tau> :: \<open>'a\<close> and 
  initial :: \<open>('s, 'a) c_word_game_node\<close> 
begin

fun strategy_from_contrasim:: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s, 'a) c_word_game_node strategy\<close> where
  \<open>strategy_from_contrasim R ((DefenderNode A p1 q0)#play) =
    (AttackerNode (SOME q1 . R q1 p1 \<and> q0 \<Rightarrow>$A q1) p1)\<close> |
  \<open>strategy_from_contrasim _ _ = undefined\<close>

lemma cwg_atknodes_precede_defnodes_in_plays: 
  assumes 
    \<open>c_word_game_defender_node n0\<close>
    \<open>n0 = DefenderNode A p' q\<close>
    \<open>(n0#play) \<in> plays initial\<close>
    \<open>initial = AttackerNode p0 q0\<close>
  shows \<open>\<exists>p. (hd play) = AttackerNode p q \<and> c_word_game_moves (hd play) n0\<close>
proof -
  have \<open>n0 \<noteq> initial\<close> using assms (2, 4) by auto
  hence mov: \<open>c_word_game_moves (hd play) n0\<close> using assms(3)
    by (metis list.inject list.sel(1) plays.cases)     
  hence \<open>\<exists>p. (hd play) = AttackerNode p q\<close> using assms(1 - 3)
    by (metis c_word_game_node.inject(2) c_word_game_defender_node.simps(1) c_word_game_moves.elims(2))
  thus ?thesis using mov by auto
qed

lemma cwg_second_play_elem_in_play_set : 
  assumes 
    \<open>(n0#play) \<in> plays initial\<close>
    \<open>initial = AttackerNode p0 q0\<close>
    \<open>n0 = DefenderNode A p q\<close>
  shows \<open>hd play \<in> set (n0 # play)\<close>
proof - 
  from assms(2, 3) have \<open>n0 \<noteq> initial\<close> by auto
  hence \<open>play \<in> plays initial\<close> using assms(1) plays.cases no_empty_plays by blast
  hence play_split: \<open>\<exists>x xs. play = x#xs\<close> using no_empty_plays
    using plays.cases by blast 
  then obtain x where x_def: \<open>\<exists>xs. play = x#xs\<close> ..
  have x_in_set: \<open>x \<in> set (n0#play)\<close> using x_def by auto
  have \<open>x = hd play\<close> using x_def by auto
  with x_in_set show \<open>hd play \<in> set (n0 # play)\<close> by auto
qed

lemma cwg_contrasim_contains_all_strat_consistent_atknodes:
  assumes 
    \<open>contrasimulation R\<close>
    \<open>R p0 q0\<close>
    \<open>initial = AttackerNode p0 q0\<close>
    \<open>play \<in> plays_for_0strategy (strategy_from_contrasim R) initial\<close>
shows \<open>((AttackerNode p q) \<in> set play) \<Longrightarrow> R p q\<close> 
  using assms(4)
proof (induct arbitrary: p q rule: plays_for_0strategy.induct[OF assms(4)])
  case 1 
  fix p q
  assume  \<open>(AttackerNode p q) \<in> (set [initial])\<close>
  thus \<open>R p q\<close> using assms(3, 2) by simp
next 
  case p0moved: (2 n0 play)
  hence IH:\<open>AttackerNode p q \<in> set (n0#play) \<Longrightarrow> R p q\<close> by simp
  from p0moved.prems have
    \<open>(AttackerNode p q) \<in> set ((strategy_from_contrasim R (n0 # play))#n0#play)\<close>
    by simp
  hence \<open>(AttackerNode p q =
      (strategy_from_contrasim R (n0 # play))) \<or> (AttackerNode p q \<in> set (n0#play))\<close>
    by simp
  thus \<open>R p q\<close>
  proof (rule disjE)
    assume \<open>AttackerNode p q \<in> set (n0#play)\<close>
    thus \<open>R p q\<close> using IH by simp
  next
    assume A: \<open>AttackerNode p q = (strategy_from_contrasim R (n0 # play))\<close>
    have \<open>\<exists>A ppred. n0 = (DefenderNode A q ppred)\<close> 
      using p0moved.hyps(3) strategy_from_contrasim.simps(1)[of \<open>R\<close>]
      by (metis (no_types, lifting) A c_word_game_node.inject(1) 
          c_word_game_defender_node.elims(2))
    then obtain A ppred where 
      n0_def: \<open>n0 = (DefenderNode A q ppred)\<close> \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
      by (metis assms(3) c_word_game.cwg_atknodes_precede_defnodes_in_plays
          simulation_challenge p0moved.hyps(1, 3) strategy0_plays_subset)
    hence \<open>strategy_from_contrasim R (n0#play) =
        AttackerNode (SOME q1. R q1 q \<and> ppred \<Rightarrow>$ A  q1) q\<close> 
      using n0_def strategy_from_contrasim.simps(1)[of \<open>R\<close> \<open>A\<close> \<open>q\<close> \<open>ppred\<close> \<open>play\<close>] by auto
    hence p_def: \<open>p = (SOME p1. R p1 q \<and> ppred \<Rightarrow>$ A p1)\<close> using A by auto
    have \<open>\<exists>qpred. hd play = (AttackerNode qpred ppred) \<and> c_word_game_moves (hd play) n0\<close> 
      using cwg_atknodes_precede_defnodes_in_plays strategy0_plays_subset[OF p0moved.hyps(1)]
      by (simp add: assms(3) n0_def  p0moved.hyps(3)) 
    then obtain qpred where qpred_def: \<open>hd play = (AttackerNode qpred ppred)\<close> 
      and qpred_move: \<open>c_word_game_moves (hd play) n0\<close> by auto
    have qpred_q_move: \<open>qpred \<Rightarrow>$A q\<close> using qpred_def qpred_move n0_def by simp
    have \<open>hd play \<in> set (n0 # play)\<close> 
      using cwg_second_play_elem_in_play_set strategy0_plays_subset[OF p0moved.hyps(1)] assms(3)
      by (auto simp add: n0_def)
    hence pred_R: \<open>R qpred ppred\<close> 
      by (simp add: qpred_def p0moved.hyps(1) p0moved.hyps(2))
    have  \<open>\<exists> p1 . R p1 q \<and> ppred \<Rightarrow>$ A p1\<close>
     using qpred_q_move pred_R assms(1) \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
     unfolding contrasimulation_def by blast
   from someI_ex[OF this] show \<open>R p q\<close> unfolding p_def by blast
  qed
next
  case p1moved: (3 n1 play n1')
  from p1moved.hyps have IH:\<open>AttackerNode p q \<in> set (n1#play) \<Longrightarrow> R p q\<close> by simp
  assume  \<open>(AttackerNode p q) \<in> (set (n1'#n1#play))\<close>
  hence \<open>(AttackerNode p q = n1') \<or> (AttackerNode p q \<in> set (n1#play))\<close> by auto
  thus \<open>R p q\<close>
  proof (rule disjE)
    assume \<open>(AttackerNode p q \<in> set (n1#play))\<close>
    thus \<open>R p q\<close> using p1moved.hyps by auto
  next
   assume A: \<open>AttackerNode p q = n1'\<close>
   from p1moved.hyps have \<open>player1_position n1\<close> by simp
   hence \<open>c_word_game_defender_node n1'\<close>
     by (metis c_word_game_defender_node.simps(2) c_word_game_moves.elims(2) p1moved.hyps(4))
   hence \<open>False\<close> using A by auto
   thus \<open>R p q\<close> ..
 qed
qed

lemma contrasim_word_game_complete:
  assumes 
    \<open>contrasimulation R\<close>
    \<open>R p q\<close> 
    \<open>initial = AttackerNode p q\<close>
  shows \<open>player0_winning_strategy (strategy_from_contrasim R) initial\<close>
    unfolding player0_winning_strategy_def 
proof (safe)
  fix play
  assume A1: \<open>play \<in> plays_for_0strategy (strategy_from_contrasim R) initial\<close>
  thus \<open>player1_wins_immediately play \<Longrightarrow> False\<close>
    unfolding player1_wins_immediately_def
  proof - 
    assume A: \<open>c_word_game_defender_node (hd play) \<and> (\<nexists>p'. c_word_game_moves (hd play) p')\<close>
    have player0_has_succ_node: \<open>c_word_game_defender_node (hd play) \<Longrightarrow>
      \<exists>p'. c_word_game_moves (hd play) p'\<close>
    proof (induct rule: simple_game.plays_for_0strategy.induct[OF A1])
      case init: 1 
      from assms(3) have \<open>\<not>c_word_game_defender_node (hd [initial])\<close> by simp
      hence \<open>False\<close> using init.prems by simp
      then show ?case ..
    next
      case p0moved: (2 n0 play)
      from p0moved.hyps have \<open>c_word_game_defender_node n0\<close> by simp
      hence \<open>\<exists>A p1 q. n0 = (DefenderNode A p1 q)\<close>
        by (meson c_word_game_defender_node.elims(2)) 
      hence \<open>\<not>c_word_game_defender_node (strategy_from_contrasim R (n0#play))\<close>
        using p0moved.hyps(4) c_word_game_moves.elims(2)
          [of \<open>n0\<close> \<open>strategy_from_contrasim R (n0#play)\<close>]
        by force 
      hence \<open>False\<close> using p0moved.prems by simp
      then show ?case ..
    next
      case p1moved: (3 n1 play n1')
      hence \<open>\<not>c_word_game_defender_node n1\<close> using p1moved.hyps by simp
      then obtain p q where n1_def: \<open>n1 = AttackerNode p q\<close>
        using c_word_game_defender_node.elims(3) by auto
      hence pq_in_R: \<open>R p q\<close> 
        using cwg_contrasim_contains_all_strat_consistent_atknodes[OF assms,
                of \<open>n1#play\<close>, OF p1moved.hyps(1)] 
        by auto
      have is_def: \<open>c_word_game_defender_node n1'\<close> using p1moved.prems by auto
      then obtain A p1 q0 where n1'_def: \<open>n1' = DefenderNode A p1 q0\<close>
        using c_word_game_defender_node.elims(2)[OF is_def] by auto
      hence \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> using p1moved.hyps(4) n1_def by simp
      have Move_n1_n1': \<open>c_word_game_moves (AttackerNode p q) (DefenderNode A p1 q0)\<close> 
        using p1moved.hyps n1_def n1'_def by auto
      hence same_q: \<open>q0 = q\<close> by auto
      from Move_n1_n1' have p_succ: \<open>p \<Rightarrow>$A p1\<close> by auto
      from assms(1) have Contra:
          \<open>\<And>p q p' A. (\<forall>a\<in>set A. a \<noteq> \<tau>) \<Longrightarrow> R p q \<Longrightarrow> p \<Rightarrow>$ A  p'
          \<Longrightarrow> (\<exists>q'. q \<Rightarrow>$ A  q' \<and> R q' p')\<close> 
        unfolding contrasimulation_def by auto
      hence \<open>\<exists> q'. (q \<Rightarrow>$ A q')\<and> R q' p1\<close>
        using Contra[OF \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> pq_in_R p_succ] by auto
      hence \<open>\<exists> p1 q1. c_word_game_moves n1' (AttackerNode p1 q1)\<close>
        using same_q n1'_def by auto
      then show ?case by auto
    qed
    thus \<open>False\<close> using A by auto
  qed
qed

subsection \<open>Winning Strategy Implies Contrasimulation in Word Game (Soundness)\<close>

lemma cwg_strategy_from_contrasim_sound: 
  assumes
    \<open>R p0 q0\<close>
    \<open>contrasimulation R\<close>
    \<open>initial = AttackerNode p0 q0\<close>
  shows
    \<open>sound_0strategy (strategy_from_contrasim R) initial\<close>
  unfolding sound_0strategy_def
proof (safe)
  fix n0 play
  assume A:
    \<open>n0 # play \<in> plays_for_0strategy (strategy_from_contrasim R) initial\<close>
    \<open>c_word_game_defender_node n0\<close>
  then obtain A p1 q where n0_def: \<open>n0 = DefenderNode A p1 q\<close>
    using c_word_game_defender_node.elims(2) by blast 
  then obtain p where p_def: \<open>hd play = AttackerNode p q\<close>
    using n0_def A cwg_atknodes_precede_defnodes_in_plays assms(3) strategy0_plays_subset 
    by blast
  hence \<open>c_word_game_moves (AttackerNode p q) (DefenderNode A p1 q)\<close> 
    using A n0_def 
    by (metis assms(3) cwg_atknodes_precede_defnodes_in_plays strategy0_plays_subset)
  hence mov_p_p1: \<open>p \<Rightarrow>$A p1\<close> \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> by auto  
  from p_def have \<open>R p q\<close> 
    using cwg_contrasim_contains_all_strat_consistent_atknodes A assms
      cwg_second_play_elem_in_play_set n0_def strategy0_plays_subset
    by fastforce
  with mov_p_p1 have q1_def: \<open>\<exists>q1. R q1 p1 \<and> q \<Rightarrow>$A q1\<close> 
    using assms(2) unfolding contrasimulation_def by blast
  from n0_def have
    \<open>strategy_from_contrasim R (n0 # play)
    = (AttackerNode (SOME q1 . R q1 p1 \<and> q \<Rightarrow>$A q1) p1)\<close>
    by auto
  then obtain q' where
    \<open>AttackerNode (SOME q1 . R q1 p1 \<and> q \<Rightarrow>$A q1) p1 = AttackerNode q' p1\<close> by blast
  hence q'_def: \<open>q' = (SOME q1 . R q1 p1 \<and> q \<Rightarrow>$A q1)\<close> by auto
  with someI_ex[OF q1_def] have \<open>R q' p1 \<and> q \<Rightarrow>$A q'\<close> by blast
  thus \<open>c_word_game_moves n0 (strategy_from_contrasim R (n0 # play))\<close>
    using q'_def by (simp add: n0_def) 
qed

lemma contrasim_word_game_sound: 
  assumes
    \<open>player0_winning_strategy f initial\<close>
    \<open>sound_0strategy f initial\<close>
  defines
    \<open>R == \<lambda> p q . (\<exists> play \<in> plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
  shows
    \<open>contrasimulation R\<close>  unfolding contrasimulation_def
proof (safe) 
  fix p q p1 A
  assume A1: \<open>p \<Rightarrow>$A p1\<close>
  assume A2: \<open>R p q\<close> \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close>
  hence \<open>\<exists> play . play \<in> plays_for_0strategy f initial \<and> hd play = AttackerNode p q\<close>
    using R_def by auto
  from this obtain play where play_def:
    \<open>play \<in> plays_for_0strategy f initial \<and> hd play = AttackerNode p q\<close> ..
  from assms(1) have \<open>\<not>player1_wins_immediately play\<close>
    using player0_winning_strategy_def play_def by auto
  hence \<open>(c_word_game_defender_node (hd play) \<and> (\<nexists>p'. c_word_game_moves (hd play) p')) 
    \<Longrightarrow> False\<close> 
    using player1_wins_immediately_def by auto
  hence Def_not_stuck: 
    \<open>c_word_game_defender_node (hd play) \<Longrightarrow> (\<nexists>p'. c_word_game_moves (hd play) p')
    \<Longrightarrow> False\<close> 
    by auto
  have \<open>(p \<Rightarrow>$A p1) \<Longrightarrow> (((DefenderNode A p1 q)#play) \<in> plays_for_0strategy f initial)\<close>
  proof -
    have \<open>\<exists>n0. n0 = DefenderNode A p1 q\<close> by auto
    from this obtain n0 where n0_def: \<open>n0 = DefenderNode A p1 q\<close> ..
    have play_split: \<open>play = (hd play)#(tl play)\<close>
      by (metis hd_Cons_tl play_def strategy0_plays_subset no_empty_plays) 
    hence inF:\<open>(hd play)#(tl play) \<in> plays_for_0strategy f initial\<close> by (simp add: play_def)
    have pl1: \<open>player1_position (hd play)\<close> by (simp add: play_def)
    have mov0:\<open>c_word_game_moves (hd play) (DefenderNode A p1 q)\<close> 
      using  \<open>\<forall>a\<in>set A. a \<noteq> \<tau>\<close> by (auto simp add: play_def A1)
    have \<open>(DefenderNode A p1 q)#(hd play)#(tl play) \<in> plays_for_0strategy f initial\<close> 
      using plays_for_0strategy.p1move[OF inF pl1 mov0] .
    thus \<open>DefenderNode A p1 q#play \<in> plays_for_0strategy f initial\<close>
      by (simp add: sym[OF play_split])
  qed
  hence def_in_f: \<open>(DefenderNode A p1 q)#play \<in> plays_for_0strategy f initial\<close>
    by (simp add: A1)
  hence \<open>\<not>(player1_wins_immediately (DefenderNode A p1 q#play))\<close> 
    using assms(1) player0_winning_strategy_def by auto
  hence \<open>\<exists>n1. c_word_game_moves (DefenderNode A p1 q) n1\<close>
    using player1_wins_immediately_def by auto
  have move_ex: \<open>c_word_game_moves (DefenderNode A p1 q) (f (DefenderNode A p1 q # play))\<close>
    using assms(2) def_in_f sound_0strategy_def by auto
  hence in_f: \<open>f ((DefenderNode A p1 q) # play) # (DefenderNode A p1 q) # play
      \<in> plays_for_0strategy f initial\<close> 
    using plays_for_0strategy.p0move[OF def_in_f] by auto
  obtain n1 where
    n1_def: \<open>n1 = f (DefenderNode A p1 q # play)\<close> and
    n1_move: \<open>c_word_game_moves (DefenderNode A p1 q) n1\<close>
    using move_ex by auto
  hence \<open>\<exists>q1. n1 = (AttackerNode q1 p1)\<close>
    using c_word_game_moves.elims(2)[of \<open>DefenderNode A p1 q\<close> n1] by auto
  from this obtain q1 where
    q1_def: \<open>n1 = (AttackerNode q1 p1)\<close> ..
  have \<open>c_word_game_moves (DefenderNode A p1 q) (AttackerNode q1 p1)\<close>
    using q1_def move_ex n1_def by auto
  hence q1_succ: \<open>q \<Rightarrow>$A q1\<close> using c_word_game_moves.simps(2) by auto
  have def: \<open>c_word_game_defender_node (DefenderNode A p1 q)\<close> by simp
  hence \<open>(AttackerNode q1 p1)#(DefenderNode A p1 q)#play \<in> plays_for_0strategy f initial\<close>
    using q1_def n1_def in_f by auto
  then obtain R_play where
    R_play_def: \<open>R_play = (AttackerNode q1 p1)#(DefenderNode A p1 q)#play\<close> and
    R_play_in_f: \<open>R_play \<in> plays_for_0strategy f initial\<close> by simp
  hence \<open>(hd R_play) = AttackerNode q1 p1\<close> by (simp add: R_play_def)
  hence \<open>R q1 p1\<close> unfolding R_def using R_play_in_f by auto
  thus \<open>R p q \<Longrightarrow> p \<Rightarrow>$ A  p1 \<Longrightarrow> \<exists>q1. q \<Rightarrow>$ A  q1 \<and> R q1 p1\<close> using q1_succ by auto
qed

theorem winning_strategy_in_c_word_game_iff_contrasim:
  assumes
    \<open>initial = AttackerNode p q\<close>
  shows 
    \<open>(\<exists> f . player0_winning_strategy f initial \<and> sound_0strategy f initial)
    = (\<exists> C. contrasimulation C \<and> C p q)\<close>
proof
  assume
    \<open>(\<exists>f. player0_winning_strategy f initial \<and> sound_0strategy f initial)\<close>
  then obtain f where
    \<open>contrasimulation (\<lambda>p q.
      \<exists>play\<in>plays_for_0strategy f initial. hd play = AttackerNode p q)\<close>
    using contrasim_word_game_sound by blast
  moreover have
    \<open>(\<lambda>p q. \<exists>play\<in>plays_for_0strategy f initial. hd play = AttackerNode p q) p q\<close>
    using assms plays_for_0strategy.init[of _ f] by (meson list.sel(1))
  ultimately show \<open>\<exists> C. contrasimulation C \<and> C p q\<close> by blast
next
  assume
    \<open>\<exists> C. contrasimulation C \<and> C p q\<close>
  thus \<open>(\<exists>f. player0_winning_strategy f initial \<and> sound_0strategy f initial)\<close>
    using contrasim_word_game_complete[OF _ _ assms]
         cwg_strategy_from_contrasim_sound[OF _ _ assms] by blast
qed

end                         
end