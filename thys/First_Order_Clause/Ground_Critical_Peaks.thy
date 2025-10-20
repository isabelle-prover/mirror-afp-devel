theory Ground_Critical_Peaks
  imports Ground_Critical_Pairs
begin

context ground_term_rewrite_system
begin

definition ground_critical_peaks ::"'t rel \<Rightarrow> ('t \<times> 't \<times> 't) set" where
  "ground_critical_peaks R = { (c\<langle>r'\<rangle>, c\<langle>l\<rangle>, r) | l r r' c. (c\<langle>l\<rangle>, r) \<in> R \<and> (l, r') \<in> R }"

lemma ground_critical_peak_to_pair: 
  assumes "(l, m, r) \<in> ground_critical_peaks R" 
  shows "(l, r) \<in> ground_critical_pairs R" 
  using assms 
  unfolding ground_critical_peaks_def ground_critical_pairs_def 
  by blast

end

locale ground_critical_peaks = ground_term_rewrite_system +
  assumes ground_critical_peaks_main: 
    "\<And>R t u s.
      (t, u) \<in> rewrite_in_context R \<Longrightarrow>
      (t, s) \<in> rewrite_in_context R \<Longrightarrow>
      (s, u) \<in> join (rewrite_in_context R) \<or>
      (\<exists>c l m r. s = c\<langle>l\<rangle> \<and> t = c\<langle>m\<rangle> \<and> u = c\<langle>r\<rangle> \<and>
        ((l, m, r) \<in> ground_critical_peaks R \<or> (r, m, l) \<in> ground_critical_peaks R))"
begin

sublocale ground_critical_pairs
  using ground_critical_peaks_main ground_critical_peak_to_pair
  by unfold_locales metis

end

end
