theory Ground_Critical_Pairs
  imports Ground_Term_Rewrite_System
begin

context ground_term_rewrite_system
begin

definition ground_critical_pairs :: "'t rel \<Rightarrow> 't rel" where
  "ground_critical_pairs R = {(c\<langle>r\<^sub>2\<rangle>, r\<^sub>1) | c l r\<^sub>1 r\<^sub>2. (c\<langle>l\<rangle>, r\<^sub>1) \<in> R \<and> (l, r\<^sub>2) \<in> R}"

abbreviation ground_critical_pair_theorem where
  "ground_critical_pair_theorem R \<equiv> 
    WCR (rewrite_in_context R) \<longleftrightarrow> ground_critical_pairs R \<subseteq> (rewrite_in_context R)\<^sup>\<down>"

lemma ground_critical_pairs_fork:
  fixes R :: "'t rel"
  assumes ground_critical_pairs: "(l, r) \<in> ground_critical_pairs R"
  shows "(r, l) \<in> (rewrite_in_context R)\<inverse> O rewrite_in_context R"
proof -

  obtain c t t' where "l = c\<langle>t'\<rangle>" and "(c\<langle>t\<rangle>, r) \<in> R" and "(t, t') \<in> R" 
    using ground_critical_pairs
    unfolding ground_critical_pairs_def
    by auto

  have "(r, c\<langle>t\<rangle>) \<in> (rewrite_in_context R)\<inverse>"
    using \<open>(c\<langle>t\<rangle>, r) \<in> R\<close> subset_rewrite_in_context 
    by blast

  moreover have "(c\<langle>t\<rangle>, l) \<in> rewrite_in_context R"
    using \<open>(t, t') \<in> R\<close> \<open>l = c\<langle>t'\<rangle>\<close> rewrite_in_context_def
    by fast

  ultimately show ?thesis
    by auto
qed

lemma ground_critical_pairs_complete:
  fixes R :: "'t rel"
  assumes 
    ground_critical_pairs: "(l, r) \<in> ground_critical_pairs R" and
    no_join: "(l, r) \<notin> (rewrite_in_context R)\<^sup>\<down>"
  shows "\<not> WCR (rewrite_in_context R)"
  using ground_critical_pairs_fork[OF ground_critical_pairs] no_join
  by auto

end

locale ground_critical_pairs = ground_term_rewrite_system +
  assumes ground_critical_pairs_main: 
    "\<And>R s t\<^sub>1 t\<^sub>2.
      (s, t\<^sub>1) \<in> rewrite_in_context R \<Longrightarrow>
      (s, t\<^sub>2) \<in> rewrite_in_context R \<Longrightarrow>
      (t\<^sub>1, t\<^sub>2) \<in> (rewrite_in_context R)\<^sup>\<down> \<or>
       (\<exists>c l r. t\<^sub>1 = c\<langle>l\<rangle> \<and> t\<^sub>2 = c\<langle>r\<rangle> \<and>
         ((l, r) \<in> ground_critical_pairs R \<or> (r, l) \<in> ground_critical_pairs R))"
begin

lemma ground_critical_pairs:
  assumes ground_critical_pairs:
    "\<And>l r. (l, r) \<in> ground_critical_pairs R \<Longrightarrow> l \<noteq> r \<Longrightarrow>
      \<exists>s. (l, s) \<in> (rewrite_in_context R)\<^sup>* \<and> (r, s) \<in> (rewrite_in_context R)\<^sup>*"
  shows "WCR (rewrite_in_context R)"
proof (intro WCR_onI)

  let ?R = "rewrite_in_context R"
  let ?CP = "ground_critical_pairs R"

  fix s t\<^sub>1 t\<^sub>2

  assume steps: "(s, t\<^sub>1) \<in> ?R" "(s, t\<^sub>2) \<in> ?R"

  let ?p = "\<lambda>s'. (t\<^sub>1, s') \<in> ?R\<^sup>* \<and> (t\<^sub>2, s') \<in> ?R\<^sup>*"

  from ground_critical_pairs_main [OF steps]
  have "\<exists>s'. ?p s'"
    using ground_critical_pairs rewrite_in_context_trancl_add_context
    by (metis joinE rtrancl.rtrancl_refl)
 
  then show "(t\<^sub>1, t\<^sub>2) \<in> ?R\<^sup>\<down>"
    by auto
qed

theorem ground_critical_pair_theorem: "ground_critical_pair_theorem R" (is "?l = ?r")
proof (rule iffI)
  assume ?l

  with ground_critical_pairs_complete show ?r 
    by auto
next
  assume ?r

  with ground_critical_pairs show ?l
    by auto
qed

end

end
