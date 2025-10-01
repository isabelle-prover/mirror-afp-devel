section \<open>Minimizers in Topological and Metric Spaces\<close>

theory Minimizers_Definition
  imports Auxilary_Facts
begin

subsection \<open>Abstract Topological Definitions\<close>

\<comment> \<open>We first define a highly abstract set of definitions for general topological spaces.  
      In practice, we will assume we are working on a metric space to employ the geometry  
      to optimize functions.\<close>

definition global_minimizer :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "global_minimizer f x_star \<longleftrightarrow> (\<forall>x. f x_star \<le> f x)"

definition local_minimizer_on :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "local_minimizer_on f x_star U \<longleftrightarrow> (open U \<and> x_star \<in> U \<and> (\<forall>x \<in> U. f x_star \<le> f x))"

definition local_minimizer :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "local_minimizer f x_star \<longleftrightarrow> (\<exists>U. open U \<and> x_star \<in> U \<and> (\<forall>x \<in> U. f x_star \<le> f x))"

definition isolated_local_minimizer_on :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "isolated_local_minimizer_on f x_star U \<longleftrightarrow> 
     (local_minimizer_on f x_star U \<and> ({x \<in> U. local_minimizer f x} = {x_star}))"

definition isolated_local_minimizer :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "isolated_local_minimizer f x_star \<longleftrightarrow> 
     (\<exists>U. local_minimizer_on f x_star U \<and> ({x \<in> U. local_minimizer f x} = {x_star}))"

definition strict_local_minimizer_on :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strict_local_minimizer_on f x_star U \<longleftrightarrow> 
     (open U \<and> x_star \<in> U \<and> (\<forall>x \<in> U - {x_star}. f x_star < f x))"

definition strict_local_minimizer :: "('a::topological_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "strict_local_minimizer f x_star \<longleftrightarrow> (\<exists>U. strict_local_minimizer_on f x_star U)"

subsection \<open>Metric Space Reformulations\<close>

\<comment> \<open>Here are simplified definitions of the above restricted to metric spaces.  
      These definitions yield sets which are easier to work with.\<close>

lemma local_minimizer_on_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "local_minimizer f x_star"
  shows "\<exists>N > 0. \<forall>x \<in> ball x_star N. f x_star \<le> f x"
proof -
  from assms obtain U where
    "open U" "x_star \<in> U" and local_min: "\<forall>x \<in> U. f x_star \<le> f x"
    unfolding local_minimizer_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by blast 
  hence "\<forall>x \<in> ball x_star N. f x_star \<le> f x"
    using ball_in_U local_min by auto
  thus ?thesis
    using N_pos by auto
qed

lemma local_minimizer_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "local_minimizer f x_star"
  shows "\<exists>N > 0. \<forall>x. dist x x_star < N \<longrightarrow> f x_star \<le> f x"
proof -
  from assms obtain U where
    "open U" "x_star \<in> U" and local_min: "\<forall>x \<in> U. f x_star \<le> f x"
    unfolding local_minimizer_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by blast 
  hence "\<forall>x. dist x x_star < N \<longrightarrow> x \<in> ball x_star N"
    by (subst mem_ball, simp add: dist_commute)
  hence "\<forall>x. dist x x_star < N \<longrightarrow> f x_star \<le> f x"
    using ball_in_U local_min by blast
  thus ?thesis
    using N_pos by auto
qed

lemma isolated_local_minimizer_on_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "isolated_local_minimizer_on f x_star U"
  shows "\<exists>N > 0. \<forall>x \<in> ball x_star N. (local_minimizer f x \<longrightarrow> x = x_star)"
proof -
  from assms have
    "local_minimizer_on f x_star U"
    and unique_min: "{x \<in> U. local_minimizer f x} = {x_star}"
    unfolding isolated_local_minimizer_on_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by (metis local_minimizer_on_def)
  have "\<forall>x \<in> ball x_star N. local_minimizer f x \<longrightarrow> x = x_star"
  proof(clarify)
    fix x
    assume "x \<in> ball x_star N"
    then have "x \<in> U" using ball_in_U by auto
    moreover assume "local_minimizer f x"
    hence "x \<in> {x \<in> U. local_minimizer f x}" using \<open>x \<in> U\<close> by auto
    hence "x \<in> {x_star}" using unique_min by auto
    ultimately show "x = x_star"
      by simp 
  qed
  thus ?thesis using N_pos by auto
qed

lemma isolated_local_minimizer_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "isolated_local_minimizer f x_star"
  shows "\<exists>N > 0. \<forall>x \<in> ball x_star N. (local_minimizer f x \<longrightarrow> x = x_star)"
proof -
  from assms obtain U where
    "local_minimizer_on f x_star U"
    and unique_min: "{x \<in> U. local_minimizer f x} = {x_star}"
    unfolding isolated_local_minimizer_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by (metis local_minimizer_on_def)
  have "\<forall>x \<in> ball x_star N. local_minimizer f x \<longrightarrow> x = x_star"
  proof(clarify)
    fix x
    assume "x \<in> ball x_star N"
    then have "x \<in> U" using ball_in_U by auto
    moreover assume "local_minimizer f x"
    hence "x \<in> {x \<in> U. local_minimizer f x}" using \<open>x \<in> U\<close> by auto
    hence "x \<in> {x_star}" using unique_min by auto
    ultimately show "x = x_star" by simp
  qed
  thus ?thesis using N_pos by auto
qed

lemma strict_local_minimizer_on_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "strict_local_minimizer_on f x_star U"
  shows "\<exists>N > 0. \<forall>x \<in> ball x_star N - {x_star}. f x_star < f x"
proof -
  from assms have
    "open U" "x_star \<in> U" and strict_min: "\<forall>x \<in> U - {x_star}. f x_star < f x"
    unfolding strict_local_minimizer_on_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by metis
  have "\<forall>x \<in> ball x_star N - {x_star}. f x_star < f x"
  proof
    fix x
    assume "x \<in> ball x_star N - {x_star}"
    hence "x \<in> U - {x_star}" using ball_in_U by auto
    thus "f x_star < f x"
      using strict_min by auto
  qed
  thus ?thesis using N_pos by auto
qed

lemma strict_local_minimizer_def2:
  fixes f :: "'a::metric_space \<Rightarrow> real"
  assumes "strict_local_minimizer f x_star"
  shows "\<exists>N > 0. \<forall>x \<in> ball x_star N - {x_star}. f x_star < f x"
proof -
  from assms obtain U where
    "strict_local_minimizer_on f x_star U"
    unfolding strict_local_minimizer_def by auto
  then have
    "open U" "x_star \<in> U" and strict_min: "\<forall>x \<in> U - {x_star}. f x_star < f x"
    unfolding strict_local_minimizer_on_def by auto
  then obtain N where N_pos: "N > 0" and ball_in_U: "ball x_star N \<subseteq> U"
    using open_contains_ball by metis
  have "\<forall>x \<in> ball x_star N - {x_star}. f x_star < f x"
  proof
    fix x
    assume "x \<in> ball x_star N - {x_star}"
    hence "x \<in> U - {x_star}" using ball_in_U by auto
    thus "f x_star < f x"
      using strict_min by auto
  qed
  thus ?thesis using N_pos by auto
qed

lemma local_minimizer_neighborhood:
  fixes f :: "real \<Rightarrow> real"
  assumes loc_min: "local_minimizer f x_min"
  shows "\<exists>\<delta> > 0. \<forall>h. \<bar>h\<bar> < \<delta> \<longrightarrow> f (x_min + h) \<ge> f x_min"
proof -
  obtain N where N_pos: "N > 0" and N_prop: "\<forall>x. dist x x_min < N \<longrightarrow> f x_min \<le> f x"
    using local_minimizer_def2[OF loc_min] by auto
  then have "\<forall>h. abs h < N \<longrightarrow> f (x_min + h) \<ge> f x_min"
    by (simp add: dist_real_def)
  then show ?thesis
    using N_pos by blast 
qed

lemma local_minimizer_from_neighborhood:
  fixes f :: "real \<Rightarrow> real" and x_min :: real
  assumes "\<exists>\<delta> > 0. \<forall>x. \<bar>x - x_min\<bar> < \<delta> \<longrightarrow> f x_min \<le> f x"
  shows "local_minimizer f x_min"
proof -
  from assms obtain \<delta> where \<delta>_pos: "\<delta> > 0" and H: "\<forall>x. \<bar>x - x_min\<bar> < \<delta> \<longrightarrow> f x_min \<le> f x"
    by auto
  obtain U where U_def: "U = {x. \<bar>x - x_min\<bar> < \<delta>}"
    by simp
  then have "open U"
    by (smt (verit) dist_commute dist_real_def mem_Collect_eq metric_space_class.open_ball subsetI topological_space_class.openI) 
  moreover have "x_min \<in> U"
    using U_def \<delta>_pos by force 
  moreover have "\<forall>x \<in> U. f x_min \<le> f x"
    using H U_def by blast
  ultimately show ?thesis
    unfolding local_minimizer_def by auto
qed

end