section \<open>Traversal Set\<close>

text \<open>This theory defines the calculation of m-traversal paths.
      These are paths extended from some state until they visit pairwise r-distinguishable states
      a number of times dependent on m.\<close>  

theory Traversal_Set
imports Helper_Algorithms 
begin


definition m_traversal_paths_with_witness_up_to_length :: 
  "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('a\<times>'b\<times>'c\<times>'a) list \<times> ('a set \<times> 'a set)) set" 
  where
  "m_traversal_paths_with_witness_up_to_length M q D m k 
    = paths_up_to_length_or_condition_with_witness M (\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D) k q"

definition m_traversal_paths_with_witness :: 
  "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> nat \<Rightarrow> (('a\<times>'b\<times>'c\<times>'a) list \<times> ('a set \<times> 'a set)) set" 
  where
  "m_traversal_paths_with_witness M q D m = m_traversal_paths_with_witness_up_to_length M q D m (Suc (size M * m))"


lemma m_traversal_paths_with_witness_finite : "finite (m_traversal_paths_with_witness M q D m)"
  unfolding m_traversal_paths_with_witness_def m_traversal_paths_with_witness_up_to_length_def
  by (simp add: paths_up_to_length_or_condition_with_witness_finite) 
  

lemma m_traversal_paths_with_witness_up_to_length_max_length :
  assumes "\<And> q . q \<in> states M \<Longrightarrow> \<exists> d \<in> set D . q \<in> fst d"
  and     "\<And> d . d \<in> set D \<Longrightarrow> snd d \<subseteq> fst d"
  and     "q \<in> states M"
  and     "(p,d) \<in> (m_traversal_paths_with_witness_up_to_length M q D m k)"
shows "length p \<le> Suc ((size M) * m)"
proof (rule ccontr)
  assume "\<not> length p \<le> Suc (FSM.size M * m)"

  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"

  have "path M q []" using assms(3) by auto
  
  have "path M q p"
        and "length p \<le> k"
        and "?f p = Some d"
        and "\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> ?f p' = None"
    using assms(4) 
    unfolding m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def 
    by auto

  let ?p = "take (Suc (m * size M)) p"
  let ?p' = "drop (Suc (m * size M)) p"
  have "path M q ?p"
    using \<open>path M q p\<close> using path_prefix[of M q ?p "drop (Suc (m * size M)) p"]
    by simp
  have "?p' \<noteq> []"
    using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
    by (simp add: mult.commute) 

  have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) ?p) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) ?p))"
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) < Suc m"
      by auto
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) ?p)) \<le> (\<Sum>q\<in>states M . m)"
      using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m\<close> by (meson sum_mono) 
    then have "length ?p \<le> m * (size M)"
      using path_length_sum[OF \<open>path M q ?p\<close>] 
      using fsm_states_finite[of M] 
      by (simp add: mult.commute)

    then show "False"
      using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
      by (simp add: mult.commute) 
  qed

  then obtain q where "q \<in> states M"
                  and "length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> set D"
                  and "q \<in> fst d"
    using assms(1) by blast
  then have "\<And> t . t_target t = q \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q) ?p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) ?p)"
    using filter_length_weakening[of "\<lambda> t . t_target t = q" "\<lambda> t . t_target t \<in> fst d"] by auto
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
    using \<open>length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m\<close> by auto
  then have "?f ?p \<noteq> None"
    using assms(2)
  proof -
    have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
      by (metis \<open>d \<in> set D\<close> find_from)
    then show ?thesis
      using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take (Suc (m * FSM.size M)) p))\<close> 
            diff_le_self le_trans not_less_eq_eq 
      by blast
  qed 
  then obtain d' where "?f ?p = Some d'"
    by blast

  then have "p = ?p@?p' \<and> ?p' \<noteq> [] \<and> ?f ?p = Some d'"
    using \<open>?p' \<noteq> []\<close> by auto

  then show "False"
    using \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> (?f p') = None\<close>
    by (metis (no_types) option.distinct(1))
qed


lemma m_traversal_paths_with_witness_set :
  assumes "\<And> q . q \<in> states M \<Longrightarrow> \<exists> d \<in> set D . q \<in> fst d"
  and     "\<And> d .  d \<in> set D \<Longrightarrow> snd d \<subseteq> fst d"
  and     "q \<in> states M"
shows "(m_traversal_paths_with_witness M q D m) 
          = {(p,d) | p d . path M q p 
                            \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) D = Some d
                            \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)}"
        (is "?MTP = ?P")
proof -
  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"

  have "path M q []"
    using assms(3) by auto

  have "\<And> p . p \<in> ?MTP \<Longrightarrow> p \<in> ?P"
    unfolding m_traversal_paths_with_witness_def m_traversal_paths_with_witness_up_to_length_def 
              paths_up_to_length_or_condition_with_witness_def
    by force
  moreover have "\<And> p . p \<in> ?P \<Longrightarrow> p \<in> ?MTP"
  proof -
    fix px assume "px \<in> ?P"
    then obtain p x where "px = (p,x)"
          and p1: "path M q p"
          and **: "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) D = Some x"
          and ***:"(\<forall>p' p''.
                     p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow>
                     find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)"
      using prod.collapse by force

    
    then have "(p,x) \<in> (m_traversal_paths_with_witness_up_to_length M q D m (length p))"
      unfolding m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def
      by force
    then have "length p \<le> Suc (size M * m)"
      using m_traversal_paths_with_witness_up_to_length_max_length[OF assms] by blast
    
    have "(p,x) \<in> ?MTP"
      using \<open>path M q p\<close> \<open>length p \<le> Suc (size M * m)\<close> \<open>?f p = Some x\<close> 
            \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> (?f p') = None\<close>
      unfolding m_traversal_paths_with_witness_def m_traversal_paths_with_witness_up_to_length_def 
                paths_up_to_length_or_condition_with_witness_def
      by force 
    then show "px \<in> ?MTP"
      using \<open>px = (p,x)\<close> by simp
  qed
  ultimately show ?thesis
    by (meson subsetI subset_antisym) 
qed


lemma maximal_repetition_sets_from_separators_cover :
  assumes "q \<in> states M"
  shows "\<exists> d \<in> (maximal_repetition_sets_from_separators M) . q \<in> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  using maximal_pairwise_r_distinguishable_state_sets_from_separators_cover[OF assms] by auto


lemma maximal_repetition_sets_from_separators_d_reachable_subset :
  shows "\<And> d . d \<in> (maximal_repetition_sets_from_separators M) \<Longrightarrow> snd d \<subseteq> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  by auto



(* Sufficient conditions for a path to be contained in the m-traversal paths *)
lemma m_traversal_paths_with_witness_set_containment :
  assumes "q \<in> states M"
  and     "path M q p"
  and     "d \<in> set repSets"
  and     "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)"
  and     "\<And> p' p''.
                  p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow>
                  \<not> (\<exists>d\<in>set repSets.
                         Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'))"
  and     "\<And> q . q\<in>states M \<Longrightarrow> \<exists>d\<in>set repSets. q \<in> fst d"
  and     "\<And> d . d\<in>set repSets \<Longrightarrow> snd d \<subseteq> fst d"
shows "\<exists> d' . (p,d') \<in> (m_traversal_paths_with_witness M q repSets m)"
proof -
  obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) repSets = Some d'"
    using assms(3,4) find_None_iff[of "(\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))" repSets] 
    by auto
  moreover have "(\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] 
                  \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repSets = None)"
    using assms(5) find_None_iff[of _ repSets] by force  
  ultimately show ?thesis
    using m_traversal_paths_with_witness_set[of M repSets q m, OF  assms(6,7,1)] 
    using assms(2) by blast
qed


lemma m_traversal_path_exist :
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "inputs M \<noteq> {}"
  and     "\<And> q . q\<in>states M \<Longrightarrow> \<exists>d\<in>set D. q \<in> fst d"
  and     "\<And> d . d \<in> set D \<Longrightarrow> snd d \<subseteq> fst d"
shows "\<exists> p' d' . (p',d') \<in> (m_traversal_paths_with_witness M q D m)"
proof -

  obtain p where "path M q p" and "length p = Suc ((size M) * m)"
    using path_of_length_ex[OF assms(1-3)] by blast

  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"

  have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) p) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) p))"
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) p) < Suc m"
      by auto
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) p) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) p)) \<le> (\<Sum>q\<in>states M . m)"
      using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) p) \<le> m\<close> by (meson sum_mono) 
    then have "length p \<le> m * (size M)"
      using path_length_sum[OF \<open>path M q p\<close>] 
      using fsm_states_finite[of M] 
      by (simp add: mult.commute)

    then show "False"
      using \<open>length p = Suc ((size M) * m)\<close>
      by (simp add: mult.commute) 
  qed

  then obtain q' where "q' \<in> states M"
                   and "length (filter (\<lambda> t . t_target t = q') p) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> set D"
                  and "q' \<in> fst d"
    using assms(4) by blast
  then have "\<And> t . t_target t = q' \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q') p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) p)"
    using filter_length_weakening[of "\<lambda> t . t_target t = q'" "\<lambda> t . t_target t \<in> fst d"] by auto
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)"
    using \<open>length (filter (\<lambda> t . t_target t = q') p) \<ge> Suc m\<close> by auto
  then have "?f p \<noteq> None"
    using assms(2)
  proof -
    have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
      by (metis \<open>d \<in> set D\<close> find_from)
    have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>p. t_target p \<in> fst d) p)"
      using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)\<close> by linarith
    then show ?thesis
      using \<open>\<forall>p. find p D \<noteq> None \<or> \<not> p d\<close> by blast    
  qed 
  then obtain d' where "?f p = Some d'"
    by blast


  show ?thesis proof (cases "(\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)")
    case True
    then show ?thesis 
      using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] \<open>path M q p\<close> \<open>?f p = Some d'\<close> 
      by blast
  next
    case False

    define ps where ps_def: "ps = {p' . \<exists> p''. p = p' @ p'' \<and> p'' \<noteq> [] 
                                              \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None}"
    have "ps \<noteq> {}" 
      using False ps_def 
      by blast
    moreover have "finite ps" 
    proof -
      have "ps \<subseteq> set (prefixes p)"
        unfolding prefixes_set ps_def
        by blast 
      then show ?thesis
        by (meson List.finite_set rev_finite_subset) 
    qed
    ultimately obtain p' where "p' \<in> ps" and "\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''"
      by (meson leI min_length_elem) 
    then have "\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] 
                \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
    proof -
      fix p'' p''' assume "p' = p'' @ p'''" and "p''' \<noteq> []"
      show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
      proof (rule ccontr) 
        assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D \<noteq> None"
        moreover have "\<exists>p'''. p = p'' @ p''' \<and> p''' \<noteq> []"
          using \<open>p' \<in> ps\<close> \<open>p' = p'' @ p'''\<close> unfolding ps_def by auto
        ultimately have "p'' \<in> ps"
          unfolding ps_def by auto
        moreover have "length p'' < length p'" 
          using \<open>p''' \<noteq> []\<close> \<open>p' = p'' @ p'''\<close> by auto
        ultimately show "False"
          using \<open>\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''\<close>
          using leD by auto 
      qed
    qed 

    have "path M q p'" and "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None"
      using \<open>path M q p\<close> \<open>p' \<in> ps\<close> unfolding ps_def by auto
    then obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d'"
      by auto


    then have "path M q p' \<and>
               find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d' \<and>
               (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None)"
      using \<open>\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None\<close> 
            \<open>path M q p'\<close>
      by blast
    then have "(p',d') \<in> (m_traversal_paths_with_witness M q D m)"
      using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] by blast
    then show ?thesis by blast
  qed 
qed



lemma m_traversal_path_extension_exist :
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "inputs M \<noteq> {}"
  and     "\<And> q . q\<in>states M \<Longrightarrow> \<exists>d\<in>set D. q \<in> fst d"
  and     "\<And> d . d \<in> set D \<Longrightarrow> snd d \<subseteq> fst d"
  and     "path M q p1"
  and     "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)) D = None"
shows "\<exists> p2 d' . (p1@p2,d') \<in> (m_traversal_paths_with_witness M q D m)"
proof -
  obtain p2 where "path M (target q p1) p2" and "length p2 = (Suc ((size M) * m)) - length p1"
    using path_of_length_ex[OF assms(1) path_target_is_state[OF assms(6)] assms(3)] 
    by blast

  have "path M q (p1@p2)"
    using assms(6) \<open>path M (target q p1) p2\<close> by auto

  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"
  
  have "length p1 < Suc ((size M) * m)"
  proof (rule ccontr)
    assume "\<not> length p1 < Suc (FSM.size M * m)"
    then have "length (take (Suc (FSM.size M * m)) p1) = Suc (FSM.size M * m)"
      by auto
    let ?p = "(take (Suc (FSM.size M * m)) p1)"

    have "path M q ?p"
      using \<open>path M q p1\<close>
      by (metis append_take_drop_id path_append_elim) 

    have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) ?p) \<ge> Suc m"
    proof (rule ccontr)
      assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) ?p))"
      then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) < Suc m"
        by auto
      then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m"
        by auto
      
      have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) ?p)) \<le> (\<Sum>q\<in>states M . m)"
        using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m\<close> by (meson sum_mono) 
      then have "length ?p \<le> m * (size M)"
        using path_length_sum[OF \<open>path M q ?p\<close>] 
        using fsm_states_finite[of M] 
        by (simp add: mult.commute)
  
      then show "False"
        using \<open>length ?p = Suc ((size M) * m)\<close>
        by (simp add: mult.commute) 
    qed
    then obtain q' where "q' \<in> states M"
                   and "length (filter (\<lambda> t . t_target t = q') ?p) \<ge> Suc m" 
      by blast
    then obtain d where "d \<in> set D"
                    and "q' \<in> fst d"
      using assms(4) by blast
    then have "\<And> t . t_target t = q' \<Longrightarrow> t_target t \<in> fst d" by auto
    then have "length (filter (\<lambda> t . t_target t = q') ?p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) ?p)"
      using filter_length_weakening[of "\<lambda> t . t_target t = q'" "\<lambda> t . t_target t \<in> fst d"] by auto
    then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
      using \<open>length (filter (\<lambda> t . t_target t = q') ?p) \<ge> Suc m\<close> by auto
    moreover have "length (filter (\<lambda>t. t_target t \<in> fst d) ?p) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)" 
    proof -
      have "\<And> xs P n . length (filter P (take n xs)) \<le> length (filter P xs)"
        by (metis append_take_drop_id filter_append le0 le_add_same_cancel1 length_append)
      then show ?thesis by auto
    qed
    ultimately have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)"
      by auto
    then have "?f p1 \<noteq> None"
      using assms(2)
    proof -
      have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
        by (metis \<open>d \<in> set D\<close> find_from)
      have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>p. t_target p \<in> fst d) p1)"
        using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)\<close> by linarith
      then show ?thesis
        using \<open>\<forall>p. find p D \<noteq> None \<or> \<not> p d\<close> by blast    
    qed 
    then obtain d' where "?f p1 = Some d'"
      by blast
    then show "False"
      using assms(7) by simp
  qed

  have "length (p1@p2) = (Suc ((size M) * m))"
    using \<open>length p2 = (Suc ((size M) * m)) - length p1\<close>
          \<open>length p1 < Suc ((size M) * m)\<close> 
    by simp

  have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) (p1@p2)) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) (p1@p2)))"
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (p1@p2)) < Suc m"
      by auto
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (p1@p2)) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) (p1@p2))) \<le> (\<Sum>q\<in>states M . m)"
      using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (p1@p2)) \<le> m\<close> by (meson sum_mono) 
    then have "length (p1@p2) \<le> m * (size M)"
      using path_length_sum[OF \<open>path M q (p1@p2)\<close>] 
      using fsm_states_finite[of M] 
      by (simp add: mult.commute)

    then show "False"
      using \<open>length (p1@p2) = Suc ((size M) * m)\<close>
      by (simp add: mult.commute) 
  qed
  then obtain q' where "q' \<in> states M"
                   and "length (filter (\<lambda> t . t_target t = q') (p1@p2)) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> set D"
                  and "q' \<in> fst d"
    using assms(4) by blast
  then have "\<And> t . t_target t = q' \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q') (p1@p2)) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) (p1@p2))"
    using filter_length_weakening[of "\<lambda> t . t_target t = q'" "\<lambda> t . t_target t \<in> fst d"]
    by blast 
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (p1@p2))"
    using \<open>length (filter (\<lambda> t . t_target t = q') (p1@p2)) \<ge> Suc m\<close> by auto
  then have "?f (p1@p2) \<noteq> None"
    using assms(2)
  proof -
    have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
      by (metis \<open>d \<in> set D\<close> find_from)
    have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>p. t_target p \<in> fst d) (p1@p2))"
      using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (p1@p2))\<close> by linarith
    then show ?thesis
      using \<open>\<forall>p. find p D \<noteq> None \<or> \<not> p d\<close> by blast    
  qed 
  then obtain d' where "?f (p1@p2) = Some d'"
    by blast


  show ?thesis proof (cases "(\<forall>p' p''. (p1@p2) = p' @ p'' \<and> p'' \<noteq> [] 
                                 \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)")
    case True
    then show ?thesis 
      using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] \<open>path M q (p1@p2)\<close> \<open>?f (p1@p2) = Some d'\<close> 
      by blast
  next
    case False

    define ps where ps_def: "ps = {p' . \<exists> p''. (p1@p2) = p' @ p'' \<and> p'' \<noteq> [] 
                                                \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None}"
    have "ps \<noteq> {}" using False ps_def by blast
    moreover have "finite ps" 
    proof -
      have "ps \<subseteq> set (prefixes (p1@p2))"
        unfolding prefixes_set ps_def
        by auto
      then show ?thesis
        by (meson List.finite_set rev_finite_subset) 
    qed
    ultimately obtain p' where "p' \<in> ps" and "\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''"
      by (meson leI min_length_elem) 
    then have "\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] 
                            \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
    proof -
      fix p'' p''' assume "p' = p'' @ p'''" and "p''' \<noteq> []"
      show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
      proof (rule ccontr) 
        assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D \<noteq> None"
        moreover have "\<exists>p'''. (p1@p2) = p'' @ p''' \<and> p''' \<noteq> []"
          using \<open>p' \<in> ps\<close> \<open>p' = p'' @ p'''\<close> unfolding ps_def by auto
        ultimately have "p'' \<in> ps"
          unfolding ps_def by auto
        moreover have "length p'' < length p'" 
          using \<open>p''' \<noteq> []\<close> \<open>p' = p'' @ p'''\<close> by auto
        ultimately show "False"
          using \<open>\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''\<close>
          using leD by auto 
      qed
    qed 

    obtain p'' where "(p1@p2) = p' @ p''" 
               and   "p'' \<noteq> []" 
               and   "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None"
      using \<open>p' \<in> ps\<close> unfolding ps_def by blast
    then obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d'"
      by auto

    have "path M q p'" 
      using \<open>path M q (p1@p2)\<close>  unfolding \<open>(p1@p2) = p' @ p''\<close> by auto

    have "length p' > length p1"
    proof (rule ccontr)
      assume "\<not> length p1 < length p'"
      then obtain i where "p' = take i p1"
        by (metis \<open>p1 @ p2 = p' @ p''\<close> append_eq_append_conv_if less_le)

      have "\<And> i . find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1))) D = None"
      proof - 
        fix i
        show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1))) D = None"
        proof (rule ccontr)
          assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1))) D \<noteq> None"
          then obtain d where "d \<in> set D" 
                        and   "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1))"
            using find_None_iff[of "(\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1)))" D] 
            by meson
          
          moreover have "length (filter (\<lambda>t. t_target t \<in> fst d) (take i p1)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)"
            using filter_take_length by metis
          ultimately have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)"
            using le_trans by blast
          then show "False"
            using \<open>d \<in> set D\<close> assms(7) unfolding find_None_iff
            by blast 
        qed
      qed
      
      then have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None"      
        unfolding \<open>p' = take i p1\<close> by blast
      then show "False"
        using \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None\<close>          
        by auto
    qed
    
    moreover have "p' = take (length p') (p1@p2)"
      using \<open>(p1@p2) = p' @ p''\<close> by auto

    ultimately obtain p where "p' = p1 @ p"
      by auto        

    have "path M q p' \<and>
           find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d' \<and>
           (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None)"
      using \<open>\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None\<close> 
            \<open>path M q p'\<close> \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d'\<close>
      by blast
    then have "(p',d') \<in> (m_traversal_paths_with_witness M q D m)"
      using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] by blast
    then show ?thesis unfolding \<open>p' = p1 @ p\<close> by blast
  qed 
qed



lemma m_traversal_path_extension_exist_for_transition :
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "inputs M \<noteq> {}"
  and     "\<And> q . q\<in>states M \<Longrightarrow> \<exists>d\<in>set D. q \<in> fst d"
  and     "\<And> d . d \<in> set D \<Longrightarrow> snd d \<subseteq> fst d"
  and     "path M q p1"
  and     "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)) D = None"
  and     "t \<in> transitions M" 
  and     "t_source t = target q p1"
shows "\<exists> p2 d' . (p1@[t]@p2,d') \<in> (m_traversal_paths_with_witness M q D m)"
proof -
  let ?q = "(target q (p1 @ [t]))"
  let ?p = "p1 @ [t]"

  have "path M q ?p"
    using \<open>path M q p1\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = target q p1\<close> path_append_transition by simp
  

  obtain p2 where "path M ?q p2" and "length p2 = (Suc ((size M) * m)) - (length ?p)"
    using path_of_length_ex[OF assms(1) path_target_is_state[OF \<open>path M q (p1@[t])\<close>] assms(3)] 
    by blast

  have "path M q (?p@p2)"
    using \<open>path M q ?p\<close> \<open>path M ?q p2\<close> by auto

  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"
  
  have "length p1 < Suc ((size M) * m)"
  proof (rule ccontr)
    assume "\<not> length p1 < Suc (FSM.size M * m)"
    then have "length (take (Suc (FSM.size M * m)) p1) = Suc (FSM.size M * m)"
      by auto
    let ?p = "(take (Suc (FSM.size M * m)) p1)"

    have "path M q ?p"
      using \<open>path M q p1\<close>
      by (metis append_take_drop_id path_append_elim) 

    have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) ?p) \<ge> Suc m"
    proof (rule ccontr)
      assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) ?p))"
      then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) < Suc m"
        by auto
      then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m"
        by auto
      
      have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) ?p)) \<le> (\<Sum>q\<in>states M . m)"
        using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m\<close> by (meson sum_mono) 
      then have "length ?p \<le> m * (size M)"
        using path_length_sum[OF \<open>path M q ?p\<close>] 
        using fsm_states_finite[of M] 
        by (simp add: mult.commute)
  
      then show "False"
        using \<open>length ?p = Suc ((size M) * m)\<close>
        by (simp add: mult.commute) 
    qed
    then obtain q' where "q' \<in> states M"
                   and "length (filter (\<lambda> t . t_target t = q') ?p) \<ge> Suc m" 
      by blast
    then obtain d where "d \<in> set D"
                    and "q' \<in> fst d"
      using assms(4) by blast
    then have "\<And> t . t_target t = q' \<Longrightarrow> t_target t \<in> fst d" by auto
    then have "length (filter (\<lambda> t . t_target t = q') ?p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) ?p)"
      using filter_length_weakening[of "\<lambda> t . t_target t = q'" "\<lambda> t . t_target t \<in> fst d"] by auto
    then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
      using \<open>length (filter (\<lambda> t . t_target t = q') ?p) \<ge> Suc m\<close> by auto
    moreover have "length (filter (\<lambda>t. t_target t \<in> fst d) ?p) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)" 
    proof -
      have "\<And> xs P n . length (filter P (take n xs)) \<le> length (filter P xs)"
        by (metis append_take_drop_id filter_append le0 le_add_same_cancel1 length_append)
      then show ?thesis by auto
    qed
    ultimately have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)"
      by auto
    then have "?f p1 \<noteq> None"
      using assms(2)
    proof -
      have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
        by (metis \<open>d \<in> set D\<close> find_from)
      have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>p. t_target p \<in> fst d) p1)"
        using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)\<close> by linarith
      then show ?thesis
        using \<open>\<forall>p. find p D \<noteq> None \<or> \<not> p d\<close> by blast    
    qed 
    then obtain d' where "?f p1 = Some d'"
      by blast
    then show "False"
      using assms(7) by simp
  qed


  have "length (?p@p2) = (Suc ((size M) * m))"
    using \<open>length p2 = (Suc ((size M) * m)) - length ?p\<close>
          \<open>length p1 < Suc ((size M) * m)\<close> 
    by simp


  have "\<exists> q \<in> states M . length (filter (\<lambda>t . t_target t = q) (?p@p2)) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>states M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) (?p@p2)))"
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (?p@p2)) < Suc m"
      by auto
    then have "\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (?p@p2)) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) (?p@p2))) \<le> (\<Sum>q\<in>states M . m)"
      using \<open>\<forall> q \<in> states M . length (filter (\<lambda>t. t_target t = q) (?p@p2)) \<le> m\<close> by (meson sum_mono) 
    then have "length (?p@p2) \<le> m * (size M)"
      using path_length_sum[OF \<open>path M q (?p@p2)\<close>] 
      using fsm_states_finite[of M] 
      by (simp add: mult.commute)

    then show "False"
      using \<open>length (?p@p2) = Suc ((size M) * m)\<close>
      by (simp add: mult.commute) 
  qed

  then obtain q' where "q' \<in> states M"
                   and "length (filter (\<lambda> t . t_target t = q') (?p@p2)) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> set D"
                  and "q' \<in> fst d"
    using assms(4) by blast
  then have "\<And> t . t_target t = q' \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q') (?p@p2)) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) (?p@p2))"
    using filter_length_weakening[of "\<lambda> t . t_target t = q'" "\<lambda> t . t_target t \<in> fst d"]
    by blast 
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?p@p2))"
    using \<open>length (filter (\<lambda> t . t_target t = q') (?p@p2)) \<ge> Suc m\<close> by auto
  then have "?f (?p@p2) \<noteq> None"
    using assms(2)
  proof -
    have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
      by (metis \<open>d \<in> set D\<close> find_from)
    have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>p. t_target p \<in> fst d) (?p@p2))"
      using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?p@p2))\<close> by linarith
    then show ?thesis
      using \<open>\<forall>p. find p D \<noteq> None \<or> \<not> p d\<close> by blast    
  qed 
  then obtain d' where "?f (?p@p2) = Some d'"
    by blast



  


  show ?thesis proof (cases "(\<forall>p' p''. (?p@p2) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)")
    case True
    obtain d' where "((?p@p2), d') \<in> m_traversal_paths_with_witness M q D m"
      using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] \<open>path M q (?p@p2)\<close> \<open>?f (?p@p2) = Some d'\<close> True by force
    then show ?thesis 
      unfolding append.assoc[symmetric] by blast
  next
    case False

    show ?thesis proof (cases "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) D")
      case (Some a)

      have *: "(\<forall>p' p''. ?p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)"
      proof -
        have "\<And> p' p''. ?p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None"
        proof -
          fix p' p'' assume "?p = p' @ p''" and "p'' \<noteq> []"
          then have "length p' \<le> length p1" by (induction p'' rule: rev_induct; auto)
          moreover have "p' = take (length p') ?p"
            unfolding \<open>?p = p' @ p''\<close> by auto
          ultimately have "p' = take (length p') p1" 
            by auto

          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None"
          proof (rule ccontr)
            assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None"
            moreover have "\<And> x . length (filter (\<lambda>t. t_target t \<in> fst x) p') \<le> length (filter (\<lambda>t. t_target t \<in> fst x) p1)"
              using \<open>p' = take (length p') p1\<close>
              by (metis filter_take_length) 
            ultimately have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)) D \<noteq> None"
              unfolding find_None_iff
              using le_trans by blast 
            then show "False"
              using assms(7) by simp
          qed
        qed
        then show ?thesis by blast
      qed

      obtain d' where "(?p, d') \<in> m_traversal_paths_with_witness M q D m"
        using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] \<open>path M q ?p\<close> Some * by force
      then show ?thesis
        by fastforce
    next
      case None

      define ps where ps_def: "ps = {p' . \<exists> p''. (?p@p2) = p' @ p'' 
                                                  \<and> p'' \<noteq> [] 
                                                  \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None}"
      have "ps \<noteq> {}" using False ps_def by blast
      moreover have "finite ps" 
      proof -
        have "ps \<subseteq> set (prefixes (?p@p2))"
          unfolding prefixes_set ps_def
          by auto
        then show ?thesis
          by (meson List.finite_set rev_finite_subset) 
      qed
      ultimately obtain p' where "p' \<in> ps" and "\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''"
        by (meson leI min_length_elem) 
      then have "\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
      proof -
        fix p'' p''' assume "p' = p'' @ p'''" and "p''' \<noteq> []"
        show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None"
        proof (rule ccontr) 
          assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D \<noteq> None"
          moreover have "\<exists>p'''. (?p@p2) = p'' @ p''' \<and> p''' \<noteq> []"
            using \<open>p' \<in> ps\<close> \<open>p' = p'' @ p'''\<close> unfolding ps_def by auto
          ultimately have "p'' \<in> ps"
            unfolding ps_def by auto
          moreover have "length p'' < length p'" 
            using \<open>p''' \<noteq> []\<close> \<open>p' = p'' @ p'''\<close> by auto
          ultimately show "False"
            using \<open>\<And> p'' . p'' \<in> ps \<Longrightarrow> length p' \<le> length p''\<close>
            using leD by auto 
        qed
      qed 
  
      obtain p'' where "(?p@p2) = p' @ p''" 
                 and   "p'' \<noteq> []" 
                 and   "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None"
        using \<open>p' \<in> ps\<close> unfolding ps_def by blast
      then obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d'"
        by auto
  
      have "path M q p'" 
        using \<open>path M q (?p@p2)\<close>  unfolding \<open>(?p@p2) = p' @ p''\<close> by auto
  
      have "length p' > length ?p"
      proof (rule ccontr)
  
        assume "\<not> length ?p < length p'"
        then obtain i where "p' = take i ?p"
          by (metis \<open>?p @ p2 = p' @ p''\<close> append_eq_append_conv_if less_le)

        have "\<And> i . find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p))) D = None"
        proof - 
          fix i
          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p))) D = None"
          proof (rule ccontr)
            assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p))) D \<noteq> None"
            then obtain d where "d \<in> set D" 
                          and   "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p))"
              using find_None_iff[of "(\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p)))" D] 
              by meson
            
            moreover have "length (filter (\<lambda>t. t_target t \<in> fst d) (take i ?p)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
              using filter_take_length by metis
            ultimately have "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
              using le_trans by blast
            then show "False"
              using \<open>d \<in> set D\<close> None unfolding find_None_iff
              by blast
          qed
        qed
        
        then have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None"      
          unfolding \<open>p' = take i ?p\<close> by blast
        then show "False"
          using \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D \<noteq> None\<close>          
          by auto
      qed
      
      moreover have "p' = take (length p') (?p@p2)"
        using \<open>(?p@p2) = p' @ p''\<close> by auto
  
      ultimately obtain p where "p' = ?p @ p"
        by (metis dual_order.strict_implies_order take_all take_append) 

      have "path M q p' \<and>
             find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d' \<and>
             (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None)"
        using \<open>\<And>p'' p''' . p' = p'' @ p''' \<Longrightarrow> p''' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'')) D = None\<close> \<open>path M q p'\<close> \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = Some d'\<close>
        by blast
      then have "(p',d') \<in> (m_traversal_paths_with_witness M q D m)"
        using m_traversal_paths_with_witness_set[OF assms(4,5,2), of m] by blast
      then show ?thesis unfolding \<open>p' = ?p @ p\<close> by fastforce
    qed 
  qed
qed

end