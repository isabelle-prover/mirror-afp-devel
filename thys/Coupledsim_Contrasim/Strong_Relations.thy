section \<open>Notions of Equivalence\<close>

subsection \<open>Strong Simulation and Bisimulation\<close>

theory Strong_Relations
  imports Transition_Systems
begin

context lts
begin
  
definition simulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>simulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<longmapsto>a q')))\<close>
  
definition bisimulation :: 
  \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close>
where
  \<open>bisimulation R \<equiv> \<forall> p q. R p q \<longrightarrow> 
    (\<forall> p' a. p \<longmapsto>a p' \<longrightarrow> 
      (\<exists> q'. R p' q' \<and> (q \<longmapsto>a q'))) \<and>
    (\<forall> q' a. q \<longmapsto>a q' \<longrightarrow> 
      (\<exists> p'. R p' q' \<and> (p \<longmapsto>a p')))\<close>

lemma bisim_ruleformat:
  assumes \<open>bisimulation R\<close>
    and \<open>R p q\<close>
  shows
    \<open>p \<longmapsto>a p' \<Longrightarrow> (\<exists> q'. R p' q' \<and> (q \<longmapsto>a q'))\<close>
    \<open>q \<longmapsto>a q' \<Longrightarrow> (\<exists> p'. R p' q' \<and> (p \<longmapsto>a p'))\<close>
  using assms unfolding bisimulation_def by auto

end \<comment>\<open>context lts\<close>

end
  