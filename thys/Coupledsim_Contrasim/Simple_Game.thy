subsection \<open>Simple Games\<close>

theory Simple_Game
imports
  Main
begin

text \<open>Simple games are games where player0 wins all infinite plays.\<close>
locale simple_game =
fixes
  game_move :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> ("_ \<longmapsto>\<heartsuit> _" [70, 70] 80) and
  player0_position :: \<open>'s \<Rightarrow> bool\<close>
begin

abbreviation player1_position :: \<open>'s \<Rightarrow> bool\<close>
  where \<open>player1_position s \<equiv> \<not> player0_position s\<close>

\<comment>\<open>Plays (to be precise: play prefixes) are lists.
  We model them with the most recent move at the beginning.
  (For our purpose it's enough to consider finite plays.)\<close>
type_synonym ('s2) play = \<open>'s2 list\<close>
type_synonym ('s2) strategy = \<open>'s2 play \<Rightarrow> 's2\<close>
type_synonym ('s2) posstrategy = \<open>'s2 \<Rightarrow> 's2\<close>

definition strategy_from_positional :: \<open>'s posstrategy \<Rightarrow> 's strategy\<close> where
  \<open>strategy_from_positional pf = (\<lambda> play. pf (hd play))\<close>

inductive_set plays :: \<open>'s \<Rightarrow> 's play set\<close> 
  for initial :: 's where
  \<open>[initial] \<in> plays initial\<close> |
  \<open>p#play \<in> plays initial \<Longrightarrow> p \<longmapsto>\<heartsuit> p' \<Longrightarrow> p'#p#play \<in> plays initial\<close>

definition play_continuation :: \<open>'s play \<Rightarrow> 's play \<Rightarrow> bool\<close>
  where \<open>play_continuation p1 p2 \<equiv> (drop (length p2 - length p1) p2) = p1\<close>

\<comment>\<open>Plays for a given player 0 strategy\<close>
inductive_set plays_for_0strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> 's play set\<close>
  for f initial where
  init: \<open>[initial] \<in> plays_for_0strategy f initial\<close> |
  p0move:
    \<open>n0#play \<in> plays_for_0strategy f initial \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)
    \<Longrightarrow> (f (n0#play))#n0#play \<in> plays_for_0strategy f initial\<close> |
  p1move:
    \<open>n1#play \<in> plays_for_0strategy f initial \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> n1'
    \<Longrightarrow> n1'#n1#play \<in> plays_for_0strategy f initial\<close>

lemma strategy0_step:
  assumes
    \<open>n0 # n1 # rest \<in> plays_for_0strategy f initial\<close>
    \<open>player0_position n1\<close>
  shows
    \<open>f (n1 # rest) = n0\<close>
  using assms
  by (induct rule: plays_for_0strategy.cases, auto)

\<comment>\<open>Plays for a given player 1 strategy\<close>
inductive_set plays_for_1strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> 's play set\<close>
  for f initial where
  init: \<open>[initial] \<in> plays_for_1strategy f initial\<close> |
  p0move:
    \<open>n0#play \<in> plays_for_1strategy f initial \<Longrightarrow> player0_position n0 \<Longrightarrow> n0 \<longmapsto>\<heartsuit> n0'
    \<Longrightarrow> n0'#n0#play \<in> plays_for_1strategy f initial\<close> |
  p1move:
    \<open>n1#play \<in> plays_for_1strategy f initial \<Longrightarrow> player1_position n1 \<Longrightarrow> n1 \<longmapsto>\<heartsuit> f (n1#play)
    \<Longrightarrow> (f (n1#play))#n1#play \<in> plays_for_1strategy f initial\<close>

definition positional_strategy :: \<open>'s strategy \<Rightarrow> bool\<close> where
  \<open>positional_strategy f \<equiv> \<forall>r1 r2 n. f (n # r1) = f (n # r2)\<close>

text \<open>A strategy is sound if it only decides on enabled transitions.\<close>
definition sound_0strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>sound_0strategy f initial \<equiv>
    \<forall> n0 play .
      n0#play \<in> plays_for_0strategy f initial \<and>
      player0_position n0 \<longrightarrow> n0 \<longmapsto>\<heartsuit> f (n0#play)\<close>

definition sound_1strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>sound_1strategy f initial \<equiv>
    \<forall> n1 play .
      n1#play \<in> plays_for_1strategy f initial \<and>
      player1_position n1 \<longrightarrow> n1 \<longmapsto>\<heartsuit> f (n1#play)\<close>

lemma strategy0_plays_subset:
  assumes \<open>play \<in> plays_for_0strategy f initial\<close>
  shows \<open>play \<in> plays initial\<close>
  using assms by (induct rule: plays_for_0strategy.induct, auto simp add: plays.intros)
lemma strategy1_plays_subset:
  assumes \<open>play \<in> plays_for_1strategy f initial\<close>
  shows \<open>play \<in> plays initial\<close>
  using assms by (induct rule: plays_for_1strategy.induct, auto simp add: plays.intros)

lemma no_empty_plays:
  assumes \<open>[] \<in> plays initial\<close>
  shows \<open>False\<close> 
  using assms plays.cases by blast

text \<open>Player1 wins a play if the play has reached a deadlock where it's player0's turn\<close>

definition player1_wins_immediately :: \<open>'s play \<Rightarrow> bool\<close> where
  \<open>player1_wins_immediately play \<equiv> player0_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')\<close>

definition player0_winning_strategy :: \<open>'s strategy \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>player0_winning_strategy f initial \<equiv> (\<forall> play \<in> plays_for_0strategy f initial.
    \<not> player1_wins_immediately play)\<close>

definition player0_wins :: \<open>'s \<Rightarrow> bool\<close> where
  \<open>player0_wins s \<equiv> (\<exists> f . player0_winning_strategy f s \<and> sound_0strategy f s)\<close>

lemma stuck_player0_win:
  assumes \<open>player1_position initial\<close> \<open>(\<nexists> p' . initial \<longmapsto>\<heartsuit> p')\<close>
  shows \<open>player0_wins initial\<close>
proof -
  have \<open>\<And>pl. pl \<in> plays initial \<Longrightarrow> pl = [initial]\<close>
  proof -
    fix pl
    assume \<open>pl \<in> plays initial\<close>
    thus \<open>pl = [initial]\<close> using assms(2) by (induct, auto)
  qed
  thus ?thesis using assms(1)
    by (metis list.sel(1) player0_winning_strategy_def player0_wins_def player1_wins_immediately_def
        sound_0strategy_def strategy0_plays_subset)
qed

definition player0_wins_immediately :: \<open>'s play \<Rightarrow> bool\<close> where
  \<open>player0_wins_immediately play \<equiv> player1_position (hd play) \<and> (\<nexists> p' . (hd play) \<longmapsto>\<heartsuit> p')\<close>

end
end
