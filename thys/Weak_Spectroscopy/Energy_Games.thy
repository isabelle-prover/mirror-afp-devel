(* License: LGPL *)

section \<open>Energy Games\<close>

theory Energy_Games
  imports Main
begin

text \<open>
  Energy games are the foundation for the weak spectroscopy game.
  We introduce them through a recursive definition of attacker's winning budgets in energy reachability games.
\<close>

subsection \<open>Fundamentals\<close>

type_synonym 'energy update = \<open>'energy \<Rightarrow> 'energy option\<close>

text \<open>An energy game is played by two players on a directed graph labeled by energy updates.
These updates represent the costs of choosing a certain move, in our case, for the attacker.\<close>
locale energy_game =
fixes
  weight_opt :: \<open>'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option\<close> and
  defender :: \<open>'gstate \<Rightarrow> bool\<close> and
  ord:: \<open>'energy \<Rightarrow> 'energy \<Rightarrow> bool\<close>
assumes
  antisim: \<open>\<And>e e'. (ord e e') \<Longrightarrow> (ord e' e) \<Longrightarrow> e = e'\<close> and
  monotonicity: \<open>\<And>g g' e e' eu eu'.
    weight_opt g g' \<noteq> None \<Longrightarrow> the (weight_opt g g') e = Some eu
    \<Longrightarrow> the (weight_opt g g') e' = Some eu' \<Longrightarrow> ord e e' \<Longrightarrow> ord eu eu'\<close> and
  defender_win_min: \<open>\<And>g g' e e'. ord e e' \<Longrightarrow> weight_opt g g' \<noteq> None
    \<Longrightarrow> the (weight_opt g g') e' = None \<Longrightarrow> the (weight_opt g g') e = None\<close>
begin

abbreviation attacker :: \<open>'gstate \<Rightarrow> bool\<close> where
  \<open>attacker p \<equiv> \<not> defender p\<close>

abbreviation moves :: \<open>'gstate \<Rightarrow> 'gstate \<Rightarrow> bool\<close> (infix \<open>\<Zinj>\<close> 70) where
  \<open>g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None\<close>

abbreviation weighted_move
  :: \<open>'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool\<close> (\<open>_ \<Zinj>wgt _ _\<close> [60,60,60] 70) where
  \<open>weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)\<close>

abbreviation \<open>weight g1 g2 \<equiv> the (weight_opt g1 g2)\<close>

abbreviation \<open>updated g g' e \<equiv> the (weight g g' e)\<close>

subsection \<open>Winning Budgets\<close>

text \<open>The attacker wins a game if and only if they manage to force the defender to get stuck before
running out of energy.\<close>

inductive attacker_wins:: \<open>'energy \<Rightarrow> 'gstate \<Rightarrow> bool\<close> where
  Attack: \<open>attacker_wins e g\<close> if
    \<open>attacker g\<close> \<open>g \<Zinj> g'\<close> \<open>weight g g' e = Some e'\<close> \<open>attacker_wins e' g'\<close> |
  Defense: \<open>attacker_wins e g\<close> if
    \<open>defender g\<close> \<open>\<forall>g'. (g \<Zinj> g') \<longrightarrow> (\<exists>e'. weight g g' e = Some e' \<and> attacker_wins e' g')\<close>

lemma attacker_wins_Ga_with_id_step:
  assumes \<open>attacker_wins e g'\<close> \<open>g \<Zinj>wgt Some g'\<close> \<open>attacker g\<close>
  shows \<open>attacker_wins e g\<close>
  using assms by (metis attacker_wins.simps)

text \<open>If from a certain starting position \<open>g\<close> a game is won by the attacker with some energy \<open>e\<close> (i.e. \<open>e\<close> is in the winning budget of \<open>g\<close>), then the game is also won by the attacker with more energy.\<close>

lemma win_a_upwards_closure:
  assumes
    \<open>attacker_wins e g\<close>
    \<open>ord e e'\<close>
  shows
    \<open>attacker_wins e' g\<close>
using assms proof (induct arbitrary: e' rule: attacker_wins.induct)
  case (Attack g g' e eu e')
  with defender_win_min obtain eu' where \<open>weight g g' e' = Some eu'\<close> by fastforce
  then show ?case
    using Attack monotonicity attacker_wins.simps by blast
next
  case (Defense g e)
  with defender_win_min have \<open>\<forall>g'. g \<Zinj> g' \<longrightarrow> (\<exists>eu'. weight g g' e' = Some eu')\<close> by fastforce
  then show ?case
    using Defense attacker_wins.Defense monotonicity by meson
qed

end \<comment> \<open>context \<open>energy_game\<close>\<close>

end
