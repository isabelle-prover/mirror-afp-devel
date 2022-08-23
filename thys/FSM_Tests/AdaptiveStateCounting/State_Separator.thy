section \<open>State Separators\<close>

text \<open>This theory defined state separators.
      A state separator @{text "S"} of some pair of states @{text "q1"}, @{text "q2"} of some FSM @{text "M"} 
      is an acyclic single-input FSM based on the product machine @{text "P"} of @{text "M"} with initial state
      @{text "q1"} and @{text "M"} with initial state @{text "q2"} such that every maximal length
      sequence in the language of @{text "S"} is either in the language of @{text "q1"} or the
      language of @{text "q2"}, but not both.
      That is, @{text "C"} represents a strategy of distinguishing @{text "q1"} and @{text "q2"} in 
      every complete submachine of @{text "P"}.
      In testing, separators are used to distinguish states reached in the SUT to establish a lower
      bound on the number of distinct states in the SUT.\<close>


theory State_Separator
imports "../Product_FSM" Backwards_Reachability_Analysis 
begin

subsection \<open>Canonical Separators\<close>

subsubsection \<open>Construction\<close>

fun canonical_separator :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm"  where
  "canonical_separator M q1 q2 = (canonical_separator' M ((product (from_FSM M q1) (from_FSM M q2))) q1 q2)"


lemma canonical_separator_simps :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "initial (canonical_separator M q1 q2) = Inl (q1,q2)"
        "states (canonical_separator M q1 q2) 
            = (image Inl (states (product (from_FSM M q1) (from_FSM M q2)))) \<union> {Inr q1, Inr q2}"
        "inputs (canonical_separator M q1 q2) = inputs M"
        "outputs (canonical_separator M q1 q2) = outputs M"
        "transitions (canonical_separator M q1 q2) 
            = shifted_transitions (transitions ((product (from_FSM M q1) (from_FSM M q2)))) 
                  \<union> distinguishing_transitions (h_out M) q1 q2 (states ((product (from_FSM M q1) (from_FSM M q2)))) (inputs ((product (from_FSM M q1) (from_FSM M q2))))"
proof -
  have *: "initial ((product (from_FSM M q1) (from_FSM M q2))) = (q1,q2)"
    unfolding restrict_to_reachable_states_simps product_simps using assms by auto
  have ***: "inputs ((product (from_FSM M q1) (from_FSM M q2))) = inputs M"
    unfolding restrict_to_reachable_states_simps product_simps using assms by auto
  have ****: "outputs ((product (from_FSM M q1) (from_FSM M q2))) = outputs M"
    unfolding restrict_to_reachable_states_simps product_simps using assms by auto
  
  show "initial (canonical_separator M q1 q2) = Inl (q1,q2)"
        "states (canonical_separator M q1 q2) = (image Inl (states (product (from_FSM M q1) (from_FSM M q2)))) \<union> {Inr q1, Inr q2}"
        "inputs (canonical_separator M q1 q2) = inputs M"
        "outputs (canonical_separator M q1 q2) = outputs M"
        "transitions (canonical_separator M q1 q2) = shifted_transitions (transitions ((product (from_FSM M q1) (from_FSM M q2)))) \<union> distinguishing_transitions (h_out M) q1 q2 (states ((product (from_FSM M q1) (from_FSM M q2)))) (inputs ((product (from_FSM M q1) (from_FSM M q2))))"
    unfolding canonical_separator.simps canonical_separator'_simps[OF *, of M] *** **** by blast+
qed


lemma distinguishing_transitions_alt_def :
  "distinguishing_transitions (h_out M) q1 q2 PS (inputs M) = 
    {(Inl (q1',q2'),x,y,Inr q1) | q1' q2' x y . (q1',q2') \<in> PS \<and> (\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> \<not>(\<exists> q' . (q2',x,y,q') \<in> transitions M)}
    \<union> {(Inl (q1',q2'),x,y,Inr q2) | q1' q2' x y . (q1',q2') \<in> PS \<and> \<not>(\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> (\<exists> q' . (q2',x,y,q') \<in> transitions M)}"
   (is "?dts = ?dl \<union> ?dr")
proof -
  have "\<And> t . t \<in> ?dts \<Longrightarrow> t \<in> ?dl \<or> t \<in> ?dr" 
    unfolding distinguishing_transitions_def h_out.simps by fastforce
  moreover have "\<And> t . t \<in> ?dl \<or> t \<in> ?dr \<Longrightarrow> t \<in> ?dts"  
  proof -
    fix t assume "t \<in> ?dl \<or> t \<in> ?dr"
    then obtain q1' q2' where "t_source t = Inl (q1',q2')" and "(q1',q2') \<in> PS"
      by auto
    
    consider (a) "t \<in> ?dl" |
             (b) "t \<in> ?dr" 
      using \<open>t \<in> ?dl \<or> t \<in> ?dr\<close> by blast
    then show "t \<in> ?dts" proof cases
      case a
      then have "t_target t = Inr q1" and "(\<exists> q' . (q1',t_input t,t_output t,q') \<in> transitions M)" 
            and "\<not>(\<exists> q' . (q2',t_input t,t_output t,q') \<in> transitions M)"
        using \<open>t_source t = Inl (q1',q2')\<close> by force+
      then have "t_output t \<in> h_out M (q1',t_input t) - h_out M (q2',t_input t)"
        unfolding h_out.simps by blast
      then have "t \<in> (\<lambda>y. (Inl (q1', q2'), t_input t, y, Inr q1)) ` (h_out M (q1', t_input t) - h_out M (q2', t_input t))"
        using \<open>t_source t = Inl (q1',q2')\<close> \<open>t_target t = Inr q1\<close>
        by (metis (mono_tags, lifting) imageI surjective_pairing) 
      moreover have "((q1',q2'),t_input t) \<in> PS \<times> inputs M"
        using fsm_transition_input \<open>(\<exists> q' . (q1',t_input t,t_output t,q') \<in> transitions M)\<close> 
              \<open>(q1',q2') \<in> PS\<close> 
        by auto 
      ultimately show ?thesis 
        unfolding distinguishing_transitions_def by fastforce
    next
      case b
      then have "t_target t = Inr q2" and "\<not>(\<exists> q' . (q1',t_input t,t_output t,q') \<in> transitions M)" 
            and "(\<exists> q' . (q2',t_input t,t_output t,q') \<in> transitions M)"
        using \<open>t_source t = Inl (q1',q2')\<close> by force+
      then have "t_output t \<in> h_out M (q2',t_input t) - h_out M (q1',t_input t)"
        unfolding h_out.simps by blast
      then have "t \<in> (\<lambda>y. (Inl (q1', q2'), t_input t, y, Inr q2)) ` (h_out M (q2', t_input t) - h_out M (q1', t_input t))"
        using \<open>t_source t = Inl (q1',q2')\<close> \<open>t_target t = Inr q2\<close>
        by (metis (mono_tags, lifting) imageI surjective_pairing) 
      moreover have "((q1',q2'),t_input t) \<in> PS \<times> inputs M"
        using fsm_transition_input \<open>(\<exists> q' . (q2',t_input t,t_output t,q') \<in> transitions M)\<close> \<open>(q1',q2') \<in> PS\<close> 
        by auto 
      ultimately show ?thesis 
        unfolding distinguishing_transitions_def by fastforce
    qed
  qed
  ultimately show ?thesis by blast
qed


lemma distinguishing_transitions_alt_alt_def :
  "distinguishing_transitions (h_out M) q1 q2 PS (inputs M) = 
    { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> PS \<and> t_target t = Inr q1 \<and> (\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}
  \<union> { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> PS \<and> t_target t = Inr q2 \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> (\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"
  
proof -
  have "{(Inl (q1',q2'),x,y,Inr q1) | q1' q2' x y . (q1',q2') \<in> PS \<and> (\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> \<not>(\<exists> q' . (q2',x,y,q') \<in> transitions M)}
        = { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> PS \<and> t_target t = Inr q1 \<and> (\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"
    by force
  moreover have "{(Inl (q1',q2'),x,y,Inr q2) | q1' q2' x y . (q1',q2') \<in> PS \<and> \<not>(\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> (\<exists> q' . (q2',x,y,q') \<in> transitions M)}
        = { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> PS \<and> t_target t = Inr q2 \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> (\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"
    by force
  ultimately show ?thesis  
    unfolding distinguishing_transitions_alt_def by force
qed
   

lemma shifted_transitions_alt_def :
  "shifted_transitions ts = {(Inl (q1',q2'), x, y, (Inl (q1'',q2''))) | q1' q2' x y q1'' q2'' . ((q1',q2'), x, y, (q1'',q2'')) \<in> ts}"   
  unfolding shifted_transitions_def by force


lemma canonical_separator_transitions_helper :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "transitions (canonical_separator M q1 q2) = 
          (shifted_transitions  (transitions (product (from_FSM M q1) (from_FSM M q2))))
          \<union> {(Inl (q1',q2'),x,y,Inr q1) | q1' q2' x y . (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> (\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> \<not>(\<exists> q' . (q2',x,y,q') \<in> transitions M)}
          \<union> {(Inl (q1',q2'),x,y,Inr q2) | q1' q2' x y . (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> \<not>(\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> (\<exists> q' . (q2',x,y,q') \<in> transitions M)}"
  unfolding canonical_separator_simps[OF assms]
            restrict_to_reachable_states_simps
            product_simps from_FSM_simps[OF assms(1)] from_FSM_simps[OF assms(2)]
            sup.idem
            distinguishing_transitions_alt_def 
  by blast


definition distinguishing_transitions_left :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) set" where
  "distinguishing_transitions_left M q1 q2  \<equiv> {(Inl (q1',q2'),x,y,Inr q1) | q1' q2' x y . (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> (\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> \<not>(\<exists> q' . (q2',x,y,q') \<in> transitions M)}"
definition distinguishing_transitions_right :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) set" where
  "distinguishing_transitions_right M q1 q2 \<equiv> {(Inl (q1',q2'),x,y,Inr q2) | q1' q2' x y . (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> \<not>(\<exists> q' . (q1',x,y,q') \<in> transitions M) \<and> (\<exists> q' . (q2',x,y,q') \<in> transitions M)}"

definition distinguishing_transitions_left_alt :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) set" where
  "distinguishing_transitions_left_alt M q1 q2  \<equiv> { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> t_target t = Inr q1 \<and> (\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"
definition distinguishing_transitions_right_alt :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) set" where
  "distinguishing_transitions_right_alt M q1 q2 \<equiv> { t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> t_target t = Inr q2 \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> (\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"


definition shifted_transitions_for :: "('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) set" where
"shifted_transitions_for M q1 q2 \<equiv> {(Inl (t_source t),t_input t, t_output t, Inl (t_target t)) | t . t \<in> transitions (product (from_FSM M q1) (from_FSM M q2))}"


lemma shifted_transitions_for_alt_def :
  "shifted_transitions_for M q1 q2 = {(Inl (q1',q2'), x, y, (Inl (q1'',q2''))) | q1' q2' x y q1'' q2'' . ((q1',q2'), x, y, (q1'',q2'')) \<in> transitions (product (from_FSM M q1) (from_FSM M q2))}"
  unfolding shifted_transitions_for_def by auto


lemma distinguishing_transitions_left_alt_alt_def :
  "distinguishing_transitions_left M q1 q2 = distinguishing_transitions_left_alt M q1 q2" 
proof -
  have "\<And> t . t \<in> distinguishing_transitions_left M q1 q2 \<Longrightarrow> t \<in> distinguishing_transitions_left_alt M q1 q2" 
  proof -
    fix t assume "t \<in> distinguishing_transitions_left M q1 q2"
    then obtain q1' q2' x y where "t = (Inl (q1', q2'), x, y, Inr q1)"
                                  "(q1', q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
                                  "(\<exists>q'. (q1', x, y, q') \<in> FSM.transitions M)" 
                                  "(\<nexists>q'. (q2', x, y, q') \<in> FSM.transitions M)"
      unfolding distinguishing_transitions_left_def by blast

    have "t_source t = Inl (q1', q2')"
      using \<open>t = (Inl (q1', q2'), x, y, Inr q1)\<close> by auto
    moreover note \<open>(q1', q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close>
    moreover have "t_target t = Inr q1"
      using \<open>t = (Inl (q1', q2'), x, y, Inr q1)\<close> by auto
    moreover have "(\<exists>t'\<in>FSM.transitions M. t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)" 
      using \<open>(\<exists>q'. (q1', x, y, q') \<in> FSM.transitions M)\<close> unfolding \<open>t = (Inl (q1', q2'), x, y, Inr q1)\<close> by force
    moreover have "\<not>(\<exists>t'\<in>FSM.transitions M. t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)" 
      using \<open>(\<nexists>q'. (q2', x, y, q') \<in> FSM.transitions M)\<close> unfolding \<open>t = (Inl (q1', q2'), x, y, Inr q1)\<close> by force
    ultimately show "t \<in> distinguishing_transitions_left_alt M q1 q2"
      unfolding distinguishing_transitions_left_alt_def by simp
  qed
  moreover have "\<And> t . t \<in> distinguishing_transitions_left_alt M q1 q2 \<Longrightarrow> t \<in> distinguishing_transitions_left M q1 q2"
    unfolding distinguishing_transitions_left_alt_def distinguishing_transitions_left_def 
    by fastforce
  ultimately show ?thesis by blast 
qed


lemma distinguishing_transitions_right_alt_alt_def :
  "distinguishing_transitions_right M q1 q2 = distinguishing_transitions_right_alt M q1 q2" 
proof -
  have "\<And> t . t \<in> distinguishing_transitions_right M q1 q2 \<Longrightarrow> t \<in> distinguishing_transitions_right_alt M q1 q2" 
  proof -
    fix t assume "t \<in> distinguishing_transitions_right M q1 q2"
    then obtain q1' q2' x y where "t = (Inl (q1', q2'), x, y, Inr q2)"
                                  "(q1', q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
                                  "(\<nexists>q'. (q1', x, y, q') \<in> FSM.transitions M)" 
                                  "(\<exists>q'. (q2', x, y, q') \<in> FSM.transitions M)"
      unfolding distinguishing_transitions_right_def by blast

    have "t_source t = Inl (q1', q2')"
      using \<open>t = (Inl (q1', q2'), x, y, Inr q2)\<close> by auto
    moreover note \<open>(q1', q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close>
    moreover have "t_target t = Inr q2"
      using \<open>t = (Inl (q1', q2'), x, y, Inr q2)\<close> by auto
    moreover have "\<not>(\<exists>t'\<in>FSM.transitions M. t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)" 
      using \<open>(\<nexists>q'. (q1', x, y, q') \<in> FSM.transitions M)\<close> unfolding \<open>t = (Inl (q1', q2'), x, y, Inr q2)\<close> by force
    moreover have "(\<exists>t'\<in>FSM.transitions M. t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)" 
      using \<open>(\<exists>q'. (q2', x, y, q') \<in> FSM.transitions M)\<close> unfolding \<open>t = (Inl (q1', q2'), x, y, Inr q2)\<close> by force
    ultimately show "t \<in> distinguishing_transitions_right_alt M q1 q2"
      unfolding distinguishing_transitions_right_def distinguishing_transitions_right_alt_def by simp
  qed
  moreover have "\<And> t . t \<in> distinguishing_transitions_right_alt M q1 q2 \<Longrightarrow> t \<in> distinguishing_transitions_right M q1 q2"
    unfolding distinguishing_transitions_right_def distinguishing_transitions_right_alt_def by fastforce
  ultimately show ?thesis
    by blast
qed

    
lemma canonical_separator_transitions_def :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "transitions (canonical_separator M q1 q2) = 
        {(Inl (q1',q2'), x, y, (Inl (q1'',q2''))) | q1' q2' x y q1'' q2'' . ((q1',q2'), x, y, (q1'',q2'')) \<in> transitions (product (from_FSM M q1) (from_FSM M q2))}
        \<union> (distinguishing_transitions_left M q1 q2)       
        \<union> (distinguishing_transitions_right M q1 q2)"
  unfolding canonical_separator_transitions_helper[OF assms]
            shifted_transitions_alt_def 
            distinguishing_transitions_left_def
            distinguishing_transitions_right_def by simp 

lemma canonical_separator_transitions_alt_def :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "transitions (canonical_separator M q1 q2) = 
        (shifted_transitions_for M q1 q2)
        \<union> (distinguishing_transitions_left_alt M q1 q2)
        \<union> (distinguishing_transitions_right_alt M q1 q2)"
proof -
  have *: "(shift_Inl `
            {t \<in> FSM.transitions (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)).
             t_source t \<in> reachable_states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))})
          = {(Inl (t_source t), t_input t, t_output t, Inl (t_target t)) |t.
             t \<in> FSM.transitions (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)) \<and>
             t_source t \<in> reachable_states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))}" 
    by blast
  
  show ?thesis
  unfolding canonical_separator_simps[OF assms]
            shifted_transitions_def
            restrict_to_reachable_states_simps
            product_simps from_FSM_simps[OF assms(1)] from_FSM_simps[OF assms(2)]
            sup.idem
  
            distinguishing_transitions_alt_alt_def
            shifted_transitions_for_def 
            * 
            
            distinguishing_transitions_left_alt_def
            distinguishing_transitions_right_alt_def
  by blast
qed




subsubsection \<open>State Separators as Submachines of Canonical Separators\<close>

definition is_state_separator_from_canonical_separator :: "(('a \<times> 'a) + 'a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a, 'b, 'c) fsm \<Rightarrow> bool" where
  "is_state_separator_from_canonical_separator CSep q1 q2 S = (
    is_submachine S CSep 
    \<and> single_input S
    \<and> acyclic S
    \<and> deadlock_state S (Inr q1)
    \<and> deadlock_state S (Inr q2)
    \<and> ((Inr q1) \<in> reachable_states S)
    \<and> ((Inr q2) \<in> reachable_states S)
    \<and> (\<forall> q \<in> reachable_states S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (isl q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> q \<in> reachable_states S . \<forall> x \<in> (inputs CSep) . (\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions CSep . t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S))
)"


subsubsection \<open>Canonical Separator Properties\<close>

lemma is_state_separator_from_canonical_separator_simps :
  assumes "is_state_separator_from_canonical_separator CSep q1 q2 S"
  shows "is_submachine S CSep" 
  and   "single_input S"
  and   "acyclic S"
  and   "deadlock_state S (Inr q1)"
  and   "deadlock_state S (Inr q2)"
  and   "((Inr q1) \<in> reachable_states S)"
  and   "((Inr q2) \<in> reachable_states S)"
  and   "\<And> q . q \<in> reachable_states S \<Longrightarrow> q \<noteq> Inr q1 \<Longrightarrow> q \<noteq> Inr q2 \<Longrightarrow> (isl q \<and> \<not> deadlock_state S q)"
  and   "\<And> q x t . q \<in> reachable_states S \<Longrightarrow> x \<in> (inputs CSep) \<Longrightarrow> (\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x) \<Longrightarrow> t \<in> transitions CSep \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow> t \<in> transitions S"
  using assms unfolding is_state_separator_from_canonical_separator_def by blast+


lemma is_state_separator_from_canonical_separator_initial :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
  shows "initial A = Inl (q1,q2)"
  using is_state_separator_from_canonical_separator_simps(1)[OF assms(1)] 
  using canonical_separator_simps(1)[OF assms(2,3)] by auto


lemma path_shift_Inl :
  assumes "(image shift_Inl (transitions M)) \<subseteq> (transitions C)"
      and "\<And> t . t \<in> (transitions C) \<Longrightarrow> isl (t_target t) \<Longrightarrow> \<exists> t' \<in> transitions M . t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
      and "initial C = Inl (initial M)"
      and "(inputs C) = (inputs M)"
      and "(outputs C) = (outputs M)"
    shows "path M (initial M) p = path C (initial C) (map shift_Inl p)"
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t p)

  have "path M (initial M) (p@[t]) \<Longrightarrow> path C (initial C) (map shift_Inl (p@[t]))"
  proof -
    assume "path M (initial M) (p@[t])"
    then have "path M (initial M) p" by auto
    then have "path C (initial C) (map shift_Inl p)" using snoc.IH
      by auto 

    have "t_source t = target (initial M) p"
      using \<open>path M (initial M) (p@[t])\<close> by auto
    then have "t_source (shift_Inl t) = target (Inl (initial M)) (map shift_Inl p)"
      by (cases p rule: rev_cases; auto)
    then have "t_source (shift_Inl t) = target (initial C) (map shift_Inl p)"
      using assms(3) by auto
    moreover have "target (initial C) (map shift_Inl p) \<in> states C"
      using path_target_is_state[OF \<open>path C (initial C) (map shift_Inl p)\<close>] by assumption
    ultimately have "t_source (shift_Inl t) \<in> states C"
      by auto
    moreover have "t \<in> transitions M"
      using \<open>path M (initial M) (p@[t])\<close> by auto
    ultimately have "(shift_Inl t) \<in> transitions C"
      using assms by auto

    show "path C (initial C) (map shift_Inl (p@[t]))"
      using path_append [OF \<open>path C (initial C) (map shift_Inl p)\<close>, of "[shift_Inl t]"]
      using \<open>(shift_Inl t) \<in> transitions C\<close> \<open>t_source (shift_Inl t) = target (initial C) (map shift_Inl p)\<close>
      using single_transition_path by force 
  qed

  moreover have "path C (initial C) (map shift_Inl (p@[t])) \<Longrightarrow> path M (initial M) (p@[t])" 
  proof -
    assume "path C (initial C) (map shift_Inl (p@[t]))"
    then have "path C (initial C) (map shift_Inl p)" by auto
    then have "path M (initial M) p" using snoc.IH
      by blast 

    have "t_source (shift_Inl t) = target (initial C) (map shift_Inl p)"
      using \<open>path C (initial C) (map shift_Inl (p@[t]))\<close> by auto
    then have "t_source (shift_Inl t) = target (Inl (initial M)) (map shift_Inl p)"
      using assms(3) by (cases p rule: rev_cases; auto)
    then have "t_source t = target (initial M) p"
      by (cases p rule: rev_cases; auto)
    moreover have "target (initial M) p \<in> states M"
      using path_target_is_state[OF \<open>path M (initial M) p\<close>] by assumption
    ultimately have "t_source t \<in> states M"
      by auto
    moreover have "shift_Inl t \<in> transitions C"
      using \<open>path C (initial C) (map shift_Inl (p@[t]))\<close> by auto
    moreover have "isl (t_target (shift_Inl t))"
      by auto
    ultimately have "t \<in> transitions M" using assms by fastforce

    show "path M (initial M) (p@[t])"
      using path_append [OF \<open>path M (initial M) p\<close>, of "[t]"]
            single_transition_path[OF \<open>t \<in> transitions M\<close>]
            \<open>t_source t = target (initial M) p\<close> by auto
  qed

  ultimately show ?case
    by linarith 
qed


lemma canonical_separator_product_transitions_subset : 
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "image shift_Inl (transitions (product (from_FSM M q1) (from_FSM M q2))) \<subseteq> (transitions (canonical_separator M q1 q2))"
  unfolding canonical_separator_simps[OF assms] shifted_transitions_def restrict_to_reachable_states_simps 
  by blast


lemma canonical_separator_transition_targets :
  assumes "t \<in> (transitions (canonical_separator M q1 q2))" 
  and "q1 \<in> states M" 
  and "q2 \<in> states M"
shows "isl (t_target t) \<Longrightarrow> t \<in> {(Inl (t_source t),t_input t, t_output t, Inl (t_target t)) | t . t \<in> transitions (product (from_FSM M q1) (from_FSM M q2))}" 
and   "t_target t = Inr q1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> t \<in> (distinguishing_transitions_left_alt M q1 q2)"
and   "t_target t = Inr q2 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> t \<in> (distinguishing_transitions_right_alt M q1 q2)"
and   "isl (t_target t) \<or> t_target t = Inr q1 \<or> t_target t = Inr q2"
unfolding shifted_transitions_for_def
          distinguishing_transitions_left_alt_def
          distinguishing_transitions_right_alt_def
proof -
  let ?shftd = "{(Inl (t_source t),t_input t, t_output t, Inl (t_target t)) | t . t \<in> transitions (product (from_FSM M q1) (from_FSM M q2))}"
  let ?dl    = "{ t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> t_target t = Inr q1 \<and> (\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"
  let ?dr    = "{ t . \<exists> q1' q2' . t_source t = Inl (q1',q2') \<and> (q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2)) \<and> t_target t = Inr q2 \<and> \<not>(\<exists> t'  \<in> transitions M . t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t) \<and> (\<exists> t'  \<in> transitions M . t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)}"

  have "t \<in> ?shftd \<union> ?dl \<union> ?dr"
    using assms(1) 
    unfolding canonical_separator_transitions_alt_def[OF assms(2,3)]
              shifted_transitions_for_def
              distinguishing_transitions_left_alt_def
              distinguishing_transitions_right_alt_def
    by force

  moreover have p1: "\<And> t' . t' \<in> ?shftd \<Longrightarrow> isl (t_target t')" 
  and  p2: "\<And> t' . t' \<in> ?dl \<Longrightarrow> t_target t' = Inr q1" 
  and  p3: "\<And> t' . t' \<in> ?dr \<Longrightarrow> t_target t' = Inr q2" 
    by auto
  ultimately show "isl (t_target t) \<or> t_target t = Inr q1 \<or> t_target t = Inr q2" 
    by fast

  show "isl (t_target t) \<Longrightarrow> t \<in> ?shftd" 
  proof -
    assume "isl (t_target t)"
    then have "t_target t \<noteq> Inr q1" and "t_target t \<noteq> Inr q2" by auto
    then have "t \<notin> ?dl" and "t \<notin> ?dr" by force+
    then show ?thesis using \<open>t \<in> ?shftd \<union> ?dl \<union> ?dr\<close> by fastforce
  qed

  show "t_target t = Inr q1 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> t \<in> ?dl" 
  proof -
    assume "t_target t = Inr q1" and "q1 \<noteq> q2"
    then have "\<not> isl (t_target t)" and "t_target t \<noteq> Inr q2" by auto
    then have "t \<notin> ?shftd" and "t \<notin> ?dr" by force+
    then show ?thesis using \<open>t \<in> ?shftd \<union> ?dl \<union> ?dr\<close> by fastforce
  qed

  show "t_target t = Inr q2 \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> t \<in> ?dr" 
  proof -
    assume "t_target t = Inr q2" and "q1 \<noteq> q2"
    then have "\<not> isl (t_target t)" and "t_target t \<noteq> Inr q1"  by auto
    then have "t \<notin> ?shftd" and "t \<notin> ?dl" by force+
    then show ?thesis using \<open>t \<in> ?shftd \<union> ?dl \<union> ?dr\<close> by fastforce
  qed
qed


lemma canonical_separator_path_shift :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) p 
    = path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (map shift_Inl p)"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?PR = "(product (from_FSM M q1) (from_FSM M q2))"
  
  have "(inputs ?C) = (inputs ?P)" 
  and  "(outputs ?C) = (outputs ?P)"
    unfolding canonical_separator_simps(3,4)[OF assms] using assms by auto

  have p1: "shift_Inl `
    FSM.transitions
     ((Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)))
    \<subseteq> FSM.transitions (canonical_separator M q1 q2)"
    using canonical_separator_product_transitions_subset[OF assms]
    unfolding restrict_to_reachable_states_simps by assumption

  have p2: "(\<And>t. t \<in> FSM.transitions (canonical_separator M q1 q2) \<Longrightarrow>
          isl (t_target t) \<Longrightarrow>
          \<exists>t'\<in>FSM.transitions
                ((Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))).
             t = shift_Inl t')"
    using canonical_separator_transition_targets(1)[OF _ assms] unfolding restrict_to_reachable_states_simps by fastforce

  have "path ?PR (initial ?PR) p = path ?C (initial ?C) (map shift_Inl p)"
    using path_shift_Inl[of ?PR ?C, OF p1 p2]  
    unfolding restrict_to_reachable_states_simps canonical_separator_simps(1,2,3,4)[OF assms] using assms by auto
  moreover have "path ?P (initial ?P) p = path ?PR (initial ?PR) p"
    unfolding restrict_to_reachable_states_simps
              restrict_to_reachable_states_path[OF reachable_states_initial] 
    by simp  
  ultimately show ?thesis 
    by simp
qed


lemma canonical_separator_t_source_isl :
  assumes "t \<in> (transitions (canonical_separator M q1 q2))"
  and "q1 \<in> states M" and "q2 \<in> states M"
  shows "isl (t_source t)"
  using assms(1) 
  unfolding canonical_separator_transitions_alt_def[OF assms(2,3)] 
            shifted_transitions_for_def
            distinguishing_transitions_left_alt_def
            distinguishing_transitions_right_alt_def
  by force


lemma canonical_separator_path_from_shift :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p"
      and "isl (target (initial (canonical_separator M q1 q2)) p)"
      and "q1 \<in> states M" and "q2 \<in> states M"
    shows "\<exists> p' . path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) p' 
                  \<and> p = (map shift_Inl p')"
using assms(1,2) proof (induction p rule: rev_induct)
  case Nil
  show ?case using canonical_separator_path_shift[OF assms(3,4), of "[]"] by fast
next
  case (snoc t p)
  then have "isl (t_target t)" by auto

  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  have "t \<in> transitions ?C" and "t_source t = target (initial ?C) p" 
    using snoc.prems by auto
  then have "isl (t_source t)"
    using canonical_separator_t_source_isl[of t M q1 q2, OF _ assms(3,4)] by blast  
  then have "isl (target (initial (canonical_separator M q1 q2)) p)"
    using \<open>t_source t = target (initial ?C) p\<close> by auto

  have "path ?C (initial ?C) p" using snoc.prems by auto
  then obtain p' where "path ?P (initial ?P) p'"
                   and "p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
    using snoc.IH[OF _ \<open>isl (target (initial (canonical_separator M q1 q2)) p)\<close>] by blast
  then have "target (initial ?C) p = Inl (target (initial ?P) p')"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis 
      unfolding target.simps visited_states.simps using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> canonical_separator_simps(1)[OF assms(3,4)]
      by (simp add: assms(3) assms(4)) 
  next
    case (snoc ys y)
    then show ?thesis 
      unfolding target.simps visited_states.simps using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> by (cases p' rule: rev_cases; auto)
  qed
  
  obtain t' where "t' \<in> transitions ?P" 
              and "t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
    using canonical_separator_transition_targets(1)[OF \<open>t \<in> transitions ?C\<close> assms(3,4) \<open>isl (t_target t)\<close>]
    by blast 
  
  have "path ?P (initial ?P) (p'@[t'])"
    by (metis \<open>path (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)) (FSM.initial (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))) p'\<close> 
          \<open>t = shift_Inl t'\<close> \<open>t' \<in> FSM.transitions (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close> 
          \<open>t_source t = target (FSM.initial (canonical_separator M q1 q2)) p\<close> 
          \<open>target (FSM.initial (canonical_separator M q1 q2)) p = Inl (target (FSM.initial (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))) p')\<close> 
          fst_conv path_append_transition sum.inject(1))
  moreover have "p@[t] = map shift_Inl (p'@[t'])"
    using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> 
          \<open>t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))\<close> 
    by auto
  ultimately show ?case 
    by meson
qed
    

lemma shifted_transitions_targets :
  assumes "t \<in> (shifted_transitions ts)"
  shows "isl (t_target t)"
  using assms unfolding shifted_transitions_def by force


lemma distinguishing_transitions_left_sources_targets :
  assumes "t \<in> (distinguishing_transitions_left_alt M q1 q2)"
      and "q2 \<in> states M"  
    obtains q1' q2' t' where "t_source t = Inl (q1',q2')" 
                            "q1' \<in> states M" 
                            "q2' \<in> states M" 
                            "t' \<in> transitions M" 
                            "t_source t' = q1'" 
                            "t_input t' = t_input t" 
                            "t_output t' = t_output t" 
                            "\<not> (\<exists>t''\<in> transitions M. t_source t'' = q2' \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t)" 
                            "t_target t = Inr q1"
  using assms(1) assms(2) fsm_transition_source path_target_is_state 
  unfolding distinguishing_transitions_left_alt_def
  by fastforce


lemma distinguishing_transitions_right_sources_targets :
  assumes "t \<in> (distinguishing_transitions_right_alt M q1 q2)"
      and "q1 \<in> states M"  
    obtains q1' q2' t' where "t_source t = Inl (q1',q2')" 
                            "q1' \<in> states M" 
                            "q2' \<in> states M" 
                            "t' \<in> transitions M" 
                            "t_source t' = q2'" 
                            "t_input t' = t_input t" 
                            "t_output t' = t_output t" 
                            "\<not> (\<exists>t''\<in> transitions M. t_source t'' = q1' \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t)" 
                            "t_target t = Inr q2"
  using assms(1) assms(2) fsm_transition_source path_target_is_state 
  unfolding distinguishing_transitions_right_alt_def
  by fastforce


lemma product_from_transition_split :
  assumes "t \<in> transitions (product (from_FSM M q1) (from_FSM M q2))"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows   "(\<exists>t'\<in> transitions M. t_source t' = fst (t_source t) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
and     "(\<exists>t'\<in> transitions M. t_source t' = snd (t_source t) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
  using product_transition_split_ob[OF assms(1)]
  unfolding product_transitions_alt_def from_FSM_simps[OF assms(2)] from_FSM_simps[OF assms(3)] by blast+


lemma shifted_transitions_underlying_transition :
  assumes "tS \<in> shifted_transitions_for M q1 q2"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  obtains t where "tS = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))"
            and   "t \<in> (transitions ((product (from_FSM M q1) (from_FSM M q2))))"
            and   "(\<exists>t'\<in>(transitions M).
                            t_source t' = fst (t_source t) \<and>
                            t_input t' = t_input t \<and> t_output t' = t_output t)"
            and   "(\<exists>t'\<in>(transitions M).
                            t_source t' = snd (t_source t) \<and>
                            t_input t' = t_input t \<and> t_output t' = t_output t)"
proof -
  obtain t where "tS = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))"
           and   *: "t \<in> (transitions ((product (from_FSM M q1) (from_FSM M q2))))"
    using assms unfolding shifted_transitions_for_def shifted_transitions_def restrict_to_reachable_states_simps by blast
  moreover have "(\<exists>t'\<in>(transitions M).
                            t_source t' = fst (t_source t) \<and>
                            t_input t' = t_input t \<and> t_output t' = t_output t)"
    using product_from_transition_split(1)[OF _ assms(2,3)]
          *
    unfolding restrict_to_reachable_states_simps by blast
  moreover have "(\<exists>t'\<in>(transitions M).
                            t_source t' = snd (t_source t) \<and>
                            t_input t' = t_input t \<and> t_output t' = t_output t)"
    using product_from_transition_split(2)[OF _ assms(2,3)]
          *
    unfolding restrict_to_reachable_states_simps by blast
  ultimately show ?thesis
    using that by blast 
qed
     

lemma shifted_transitions_observable_against_distinguishing_transitions_left :
  assumes "t1 \<in> (shifted_transitions_for M q1 q2)"
  and     "t2 \<in> (distinguishing_transitions_left M q1 q2)"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
  using assms(1,2)
  unfolding product_transitions_def from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)]
            shifted_transitions_for_def distinguishing_transitions_left_def
  by force

lemma shifted_transitions_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> (shifted_transitions_for M q1 q2)"
  and     "t2 \<in> (distinguishing_transitions_right M q1 q2)"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
  using assms
  unfolding product_transitions_def from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)] 
            shifted_transitions_for_def distinguishing_transitions_right_def
  by force


lemma distinguishing_transitions_left_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> (distinguishing_transitions_left M q1 q2)"
  and     "t2 \<in> (distinguishing_transitions_right M q1 q2)"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
  using assms 
  unfolding distinguishing_transitions_left_def distinguishing_transitions_right_def by force


lemma distinguishing_transitions_left_observable_against_distinguishing_transitions_left :
  assumes "t1 \<in> (distinguishing_transitions_left M q1 q2)"
  and     "t2 \<in> (distinguishing_transitions_left M q1 q2)"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2"
  using assms unfolding distinguishing_transitions_left_def by force


lemma distinguishing_transitions_right_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> (distinguishing_transitions_right M q1 q2)"
  and     "t2 \<in> (distinguishing_transitions_right M q1 q2)"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2"
  using assms unfolding distinguishing_transitions_right_def by force


lemma shifted_transitions_observable_against_shifted_transitions :
  assumes "t1 \<in> (shifted_transitions_for M q1 q2)"
  and     "t2 \<in> (shifted_transitions_for M q1 q2)"
  and     "observable M"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2" 
proof -
  obtain t1' where d1: "t1 = (Inl (t_source t1'), t_input t1', t_output t1', Inl (t_target t1'))"
             and   h1: "t1' \<in> (transitions (product (from_FSM M q1) (from_FSM M q2)))"
    using assms(1) unfolding shifted_transitions_for_def by auto

  obtain t2' where d2: "t2 = (Inl (t_source t2'), t_input t2', t_output t2', Inl (t_target t2'))"
             and   h2: "t2' \<in> (transitions (product (from_FSM M q1) (from_FSM M q2)))"
    using assms(2) unfolding shifted_transitions_for_def by auto

  have "observable (product (from_FSM M q1) (from_FSM M q2))"
    using from_FSM_observable[OF assms(3)] 
          product_observable 
    by metis
  
  then have "t1' = t2'"
    using d1 d2 h1 h2 \<open>t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close>
    by (metis fst_conv observable.elims(2) prod.expand snd_conv sum.inject(1)) 
  then show ?thesis using d1 d2 by auto
qed
  

lemma canonical_separator_observable :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "observable (canonical_separator M q1 q2)" (is "observable ?CSep")
proof -

  have  "\<And> t1 t2 . t1 \<in> (transitions ?CSep) \<Longrightarrow> 
                             t2 \<in> (transitions ?CSep) \<Longrightarrow> 
                    t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<Longrightarrow> t_target t1 = t_target t2" 
  proof -
    fix t1 t2 assume "t1 \<in> (transitions ?CSep)" 
              and    "t2 \<in> (transitions ?CSep)"
              and    *: "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
    
    moreover have "transitions ?CSep = shifted_transitions_for M q1 q2 \<union>
                                       distinguishing_transitions_left M q1 q2 \<union>
                                       distinguishing_transitions_right M q1 q2"
      using canonical_separator_transitions_alt_def[OF assms(2,3)] 
      unfolding distinguishing_transitions_left_alt_alt_def distinguishing_transitions_right_alt_alt_def by assumption

    ultimately consider "t1 \<in> shifted_transitions_for M q1 q2 \<and> t2 \<in> shifted_transitions_for M q1 q2"
                      | "t1 \<in> shifted_transitions_for M q1 q2 \<and> t2 \<in> distinguishing_transitions_left M q1 q2"
                      | "t1 \<in> shifted_transitions_for M q1 q2 \<and> t2 \<in> distinguishing_transitions_right M q1 q2"
                      | "t1 \<in> distinguishing_transitions_left M q1 q2 \<and> t2 \<in> shifted_transitions_for M q1 q2"
                      | "t1 \<in> distinguishing_transitions_left M q1 q2 \<and> t2 \<in> distinguishing_transitions_left M q1 q2"
                      | "t1 \<in> distinguishing_transitions_left M q1 q2 \<and> t2 \<in> distinguishing_transitions_right M q1 q2"
                      | "t1 \<in> distinguishing_transitions_right M q1 q2 \<and> t2 \<in> shifted_transitions_for M q1 q2"
                      | "t1 \<in> distinguishing_transitions_right M q1 q2 \<and> t2 \<in> distinguishing_transitions_left M q1 q2"
                      | "t1 \<in> distinguishing_transitions_right M q1 q2 \<and> t2 \<in> distinguishing_transitions_right M q1 q2"
      by force
    then show "t_target t1 = t_target t2" proof cases
      case 1
      then show ?thesis using shifted_transitions_observable_against_shifted_transitions[of t1 M q1 q2 t2, OF _ _ assms(1) *] by fastforce
    next
      case 2
      then show ?thesis using shifted_transitions_observable_against_distinguishing_transitions_left[OF _ _ assms(2,3), of t1 t2] * by fastforce
    next
      case 3
      then show ?thesis using shifted_transitions_observable_against_distinguishing_transitions_right[OF _ _ assms(2,3), of t1 t2] * by fastforce
    next
      case 4
      then show ?thesis using shifted_transitions_observable_against_distinguishing_transitions_left[OF _ _ assms(2,3), of t2 t1] * by fastforce
    next
      case 5
      then show ?thesis using * unfolding distinguishing_transitions_left_def by fastforce
    next
      case 6
      then show ?thesis using * unfolding distinguishing_transitions_left_def distinguishing_transitions_right_def by fastforce
    next
      case 7
      then show ?thesis using shifted_transitions_observable_against_distinguishing_transitions_right[OF _ _ assms(2,3), of t2 t1] * by fastforce
    next
      case 8
      then show ?thesis using * unfolding distinguishing_transitions_left_def distinguishing_transitions_right_def by fastforce
    next
      case 9
      then show ?thesis using * unfolding distinguishing_transitions_right_def by fastforce
    qed 
  qed
  then show ?thesis unfolding observable.simps by blast
qed


lemma canonical_separator_targets_ineq :
  assumes "t \<in> transitions (canonical_separator M q1 q2)" 
      and "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
  shows "isl (t_target t) \<Longrightarrow> t \<in> (shifted_transitions_for M q1 q2)"
    and "t_target t = Inr q1 \<Longrightarrow> t \<in> (distinguishing_transitions_left M q1 q2)"
    and "t_target t = Inr q2 \<Longrightarrow> t \<in> (distinguishing_transitions_right M q1 q2)"
proof -
  show "isl (t_target t) \<Longrightarrow> t \<in> (shifted_transitions_for M q1 q2)"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) canonical_separator_transition_targets(1) shifted_transitions_for_def)
  show "t_target t = Inr q1 \<Longrightarrow> t \<in> (distinguishing_transitions_left M q1 q2)"
    by (metis assms(1) assms(2) assms(3) assms(4) canonical_separator_transition_targets(2) distinguishing_transitions_left_alt_alt_def)
  show "t_target t = Inr q2 \<Longrightarrow> t \<in> (distinguishing_transitions_right M q1 q2)"
    by (metis assms(1) assms(2) assms(3) assms(4) canonical_separator_transition_targets(3) distinguishing_transitions_right_alt_alt_def)
qed


lemma canonical_separator_targets_observable :
  assumes "t \<in> transitions (canonical_separator M q1 q2)" 
      and "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
  shows "isl (t_target t) \<Longrightarrow> t \<in> (shifted_transitions_for M q1 q2)"
    and "t_target t = Inr q1 \<Longrightarrow> t \<in> (distinguishing_transitions_left M q1 q2)"
    and "t_target t = Inr q2 \<Longrightarrow> t \<in> (distinguishing_transitions_right M q1 q2)"
proof -
  show "isl (t_target t) \<Longrightarrow> t \<in> (shifted_transitions_for M q1 q2)"
    by (metis assms canonical_separator_targets_ineq(1))
  show "t_target t = Inr q1 \<Longrightarrow> t \<in> (distinguishing_transitions_left M q1 q2)"
    by (metis assms canonical_separator_targets_ineq(2))
  show "t_target t = Inr q2 \<Longrightarrow> t \<in> (distinguishing_transitions_right M q1 q2)"
    by (metis assms canonical_separator_targets_ineq(3))
qed


lemma canonical_separator_maximal_path_distinguishes_left :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S" (is "is_state_separator_from_canonical_separator ?C q1 q2 S")
      and "path S (initial S) p"
      and "target (initial S) p = Inr q1"  
      and "observable M"
      and "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
shows "p_io p \<in> LS M q1 - LS M q2"
proof (cases p rule: rev_cases)
  case Nil
  then have "initial S = Inr q1" using assms(3) by auto
  then have "initial ?C = Inr q1"
    using assms(1) assms(5) assms(6) is_state_separator_from_canonical_separator_initial by fastforce
  then show ?thesis using canonical_separator_simps(1) Inr_Inl_False
    using assms(5) assms(6) by fastforce 
next
  case (snoc p' t) 
  then have "path S (initial S) (p'@[t])"
    using assms(2) by auto
  then have "t \<in> transitions S" and "t_source t = target (initial S) p'" by auto


  have "path ?C (initial ?C) (p'@[t])"
    using \<open>path S (initial S) (p'@[t])\<close> assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S] by (meson submachine_path_initial)
  then have "path ?C (initial ?C) (p')" and "t \<in> transitions ?C"
    by auto

  have "isl (target (initial S) p')"
  proof (rule ccontr)
    assume "\<not> isl (target (initial S) p')"
    moreover have "target (initial S) p' \<in> states S"
      using \<open>path S (initial S) (p'@[t])\<close> by auto
    ultimately have "target (initial S) p' = Inr q1 \<or> target (initial S) p' = Inr q2"
      using \<open>t \<in> FSM.transitions (canonical_separator M q1 q2)\<close> \<open>t_source t = target (FSM.initial S) p'\<close> assms(5) assms(6) canonical_separator_t_source_isl by fastforce            
    moreover have "deadlock_state S (Inr q1)" and "deadlock_state S (Inr q2)"
      using assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S] by presburger+
    ultimately show "False" 
      using \<open>t \<in> transitions S\<close> \<open>t_source t = target (initial S) p'\<close> unfolding deadlock_state.simps
      by metis 
  qed
  then obtain q1' q2' where "target (initial S) p' = Inl (q1',q2')" using isl_def prod.collapse by metis
  then have "isl (target (initial ?C) p')"
     using assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S]
     by (metis (no_types, lifting) Nil_is_append_conv assms(2) isl_def list.distinct(1) list.sel(1) path.cases snoc submachine_path_initial) 


  obtain pC where "path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) pC"
              and "p' = map shift_Inl pC"
    by (metis (mono_tags, lifting) \<open>isl (target (FSM.initial (canonical_separator M q1 q2)) p')\<close> 
          \<open>path (canonical_separator M q1 q2) (FSM.initial (canonical_separator M q1 q2)) p'\<close> 
          assms(5) assms(6) canonical_separator_path_from_shift)
  then have "path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) pC"
    by (simp add: assms(5) assms(6))
  then have "path (from_FSM M q1) q1 (left_path pC)" and "path (from_FSM M q2) q2 (right_path pC)"
    using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 pC] by presburger+

  have "path M q1 (left_path pC)"
    using from_FSM_path[OF assms(5) \<open>path (from_FSM M q1) q1 (left_path pC)\<close>] by assumption
  have "path M q2 (right_path pC)"
    using from_FSM_path[OF assms(6) \<open>path (from_FSM M q2) q2 (right_path pC)\<close>] by assumption
  
  have "t_target t = Inr q1"
    using \<open>path S (initial S) (p'@[t])\<close> snoc assms(3) by auto
  then have "t \<in> (distinguishing_transitions_left M q1 q2)"
    using canonical_separator_targets_ineq(2)[OF \<open>t \<in> transitions ?C\<close> assms(5,6,7)] by auto
  then have "t \<in> (distinguishing_transitions_left_alt M q1 q2)"
    using distinguishing_transitions_left_alt_alt_def by force

  have "t_source t = Inl (q1',q2')"
    using \<open>target (initial S) p' = Inl (q1',q2')\<close> \<open>t_source t = target (initial S) p'\<close> by auto

  then obtain t' where "q1' \<in> states M"
                        and "q2' \<in> states M"
                        and "t' \<in> transitions M"
                        and "t_source t' = q1'"
                        and "t_input t' = t_input t"
                        and "t_output t' = t_output t"
                        and "\<not> (\<exists>t''\<in> transitions M. t_source t'' = q2' \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t)"
    using \<open>t \<in> (distinguishing_transitions_left_alt M q1 q2)\<close> assms(5,6) fsm_transition_source path_target_is_state 
    unfolding distinguishing_transitions_left_alt_def reachable_states_def by fastforce


  have "initial S = Inl (q1,q2)"
    by (meson assms(1) assms(5) assms(6) is_state_separator_from_canonical_separator_initial)
  have "length p' = length pC"
    using \<open>p' = map shift_Inl pC\<close> by auto
  then have "target (initial S) p' = Inl (target (q1,q2) pC)"
    using \<open>p' = map shift_Inl pC\<close> \<open>initial S = Inl (q1,q2)\<close> by (induction p' pC rule: list_induct2; auto)
  then have "target (q1,q2) pC = (q1',q2')"
     using \<open>target (initial S) p' = Inl (q1',q2')\<close> by auto 
  then have "target q2 (right_path pC) = q2'"
    using product_target_split(2) by fastforce
  then have "\<not> (\<exists>t'\<in> transitions M. t_source t' = target q2 (right_path pC) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
    using \<open>\<not> (\<exists>t'\<in> transitions M. t_source t' = q2' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close> by blast

  have "target q1 (left_path pC) = q1'"
    using \<open>target (q1,q2) pC = (q1',q2')\<close> product_target_split(1) by fastforce
  then have "path M q1 ((left_path pC)@[t'])"
    using \<open>path M q1 (left_path pC)\<close> \<open>t' \<in> transitions M\<close> \<open>t_source t' = q1'\<close>
    by (simp add: path_append_transition)
  then have "p_io ((left_path pC)@[t']) \<in> LS M q1" 
    unfolding LS.simps by force 
  moreover have "p_io p' = p_io (left_path pC)"
    using \<open>p' = map shift_Inl pC\<close> by auto
  ultimately have "p_io (p'@[t]) \<in> LS M q1"
    using \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> by auto
    
  have "p_io (right_path pC) @  [(t_input t, t_output t)] \<notin> LS M q2"
    using observable_path_language_step[OF assms(4) \<open>path M q2 (right_path pC)\<close> \<open>\<not> (\<exists>t'\<in> transitions M. t_source t' = target q2 (right_path pC) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close>] by assumption
  moreover have "p_io p' = p_io (right_path pC)"
    using \<open>p' = map shift_Inl pC\<close> by auto
  ultimately have "p_io (p'@[t]) \<notin> LS M q2"
    by auto

  show ?thesis 
    using \<open>p_io (p'@[t]) \<in> LS M q1\<close> \<open>p_io (p'@[t]) \<notin> LS M q2\<close> snoc by blast
qed


lemma canonical_separator_maximal_path_distinguishes_right :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S" 
          (is "is_state_separator_from_canonical_separator ?C q1 q2 S")
      and "path S (initial S) p"
      and "target (initial S) p = Inr q2"  
      and "observable M"
      and "q1 \<in> states M" and "q2 \<in> states M" and "q1 \<noteq> q2"
shows "p_io p \<in> LS M q2 - LS M q1"
proof (cases p rule: rev_cases)
  case Nil
  then have "initial S = Inr q2" using assms(3) by auto
  then have "initial ?C = Inr q2"
    using assms(1) assms(5) assms(6) is_state_separator_from_canonical_separator_initial by fastforce
  then show ?thesis using canonical_separator_simps(1) Inr_Inl_False
    using assms(5) assms(6) by fastforce  
next
  case (snoc p' t) 
  then have "path S (initial S) (p'@[t])"
    using assms(2) by auto
  then have "t \<in> transitions S" and "t_source t = target (initial S) p'" 
    by auto

  have "path ?C (initial ?C) (p'@[t])"
    using \<open>path S (initial S) (p'@[t])\<close> assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S] 
    by (meson submachine_path_initial)
  then have "path ?C (initial ?C) (p')" and "t \<in> transitions ?C"
    by auto

  have "isl (target (initial S) p')"
  proof (rule ccontr)
    assume "\<not> isl (target (initial S) p')"
    moreover have "target (initial S) p' \<in> states S"
      using \<open>path S (initial S) (p'@[t])\<close> by auto
    ultimately have "target (initial S) p' = Inr q1 \<or> target (initial S) p' = Inr q2"
      
      using assms(1) unfolding is_state_separator_from_canonical_separator_def
      by (metis \<open>t \<in> FSM.transitions (canonical_separator M q1 q2)\<close> \<open>t_source t = target (FSM.initial S) p'\<close> 
            assms(5) assms(6) canonical_separator_t_source_isl)   
    moreover have "deadlock_state S (Inr q1)" and "deadlock_state S (Inr q2)"
      using assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S] by presburger+
    ultimately show "False" 
      using \<open>t \<in> transitions S\<close> \<open>t_source t = target (initial S) p'\<close> unfolding deadlock_state.simps
      by metis 
  qed
  then obtain q1' q2' where "target (initial S) p' = Inl (q1',q2')" 
    using isl_def prod.collapse by metis
  then have "isl (target (initial ?C) p')"
     using assms(1) is_state_separator_from_canonical_separator_def[of ?C q1 q2 S]
     by (metis (no_types, lifting) Nil_is_append_conv assms(2) isl_def list.distinct(1) list.sel(1) 
         path.cases snoc submachine_path_initial) 

  obtain pC where "path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) pC"
              and "p' = map shift_Inl pC"
    using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) (p')\<close> \<open>isl (target (initial ?C) p')\<close>]
    using assms(5) assms(6) by blast 
  then have "path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) pC"
    by (simp add: assms(5) assms(6))

  then have "path (from_FSM M q1) q1 (left_path pC)" and "path (from_FSM M q2) q2 (right_path pC)"
    using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 pC] by presburger+

  have "path M q1 (left_path pC)"
    using from_FSM_path[OF assms(5) \<open>path (from_FSM M q1) q1 (left_path pC)\<close>] by assumption
  have "path M q2 (right_path pC)"
    using from_FSM_path[OF assms(6) \<open>path (from_FSM M q2) q2 (right_path pC)\<close>] by assumption
  
  have "t_target t = Inr q2"
    using \<open>path S (initial S) (p'@[t])\<close> snoc assms(3) by auto
  then have "t \<in> (distinguishing_transitions_right M q1 q2)"
    using canonical_separator_targets_ineq(3)[OF \<open>t \<in> transitions ?C\<close> assms(5,6,7)] by auto
  then have "t \<in> (distinguishing_transitions_right_alt M q1 q2)"
    unfolding distinguishing_transitions_right_alt_alt_def by assumption

  have "t_source t = Inl (q1',q2')"
    using \<open>target (initial S) p' = Inl (q1',q2')\<close> \<open>t_source t = target (initial S) p'\<close> by auto

  then obtain t' where "q1' \<in> states M"
                        and "q2' \<in> states M"
                        and "t' \<in> transitions M"
                        and "t_source t' = q2'"                        
                        and "t_input t' = t_input t"
                        and "t_output t' = t_output t"
                        and "\<not> (\<exists>t''\<in> transitions M. t_source t'' = q1' \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t)"
    using \<open>t \<in> (distinguishing_transitions_right_alt M q1 q2)\<close> assms(5,6) fsm_transition_source path_target_is_state 
    unfolding distinguishing_transitions_right_alt_def reachable_states_def by fastforce

  
  have "initial S = Inl (q1,q2)"
    by (meson assms(1) assms(5) assms(6) is_state_separator_from_canonical_separator_initial)
  have "length p' = length pC"
    using \<open>p' = map shift_Inl pC\<close> by auto
  then have "target (initial S) p' = Inl (target (q1,q2) pC)"
    using \<open>p' = map shift_Inl pC\<close> \<open>initial S = Inl (q1,q2)\<close> by (induction p' pC rule: list_induct2; auto)
  then have "target (q1,q2) pC = (q1',q2')"
     using \<open>target (initial S) p' = Inl (q1',q2')\<close> by auto 
  then have "target q1 (left_path pC) = q1'"
    using product_target_split(1) by fastforce
  then have "\<not> (\<exists>t'\<in> transitions M. t_source t' = target q1 (left_path pC) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
    using \<open>\<not> (\<exists>t'\<in> transitions M. t_source t' = q1' \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close> by blast

  have "target q2 (right_path pC) = q2'"
    using \<open>target (q1,q2) pC = (q1',q2')\<close> product_target_split(2) by fastforce
  then have "path M q2 ((right_path pC)@[t'])"
    using \<open>path M q2 (right_path pC)\<close> \<open>t' \<in> transitions M\<close> \<open>t_source t' = q2'\<close>
    by (simp add: path_append_transition)
  then have "p_io ((right_path pC)@[t']) \<in> LS M q2" 
    unfolding LS.simps by force 
  moreover have "p_io p' = p_io (right_path pC)"
    using \<open>p' = map shift_Inl pC\<close> by auto
  ultimately have "p_io (p'@[t]) \<in> LS M q2"
    using \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> by auto
    

  have "p_io (left_path pC) @  [(t_input t, t_output t)] \<notin> LS M q1"
    using observable_path_language_step[OF assms(4) \<open>path M q1 (left_path pC)\<close> \<open>\<not> (\<exists>t'\<in> transitions M. t_source t' = target q1 (left_path pC) \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close>] by assumption
  moreover have "p_io p' = p_io (left_path pC)"
    using \<open>p' = map shift_Inl pC\<close> by auto
  ultimately have "p_io (p'@[t]) \<notin> LS M q1"
    by auto
  
  show ?thesis 
    using \<open>p_io (p'@[t]) \<in> LS M q2\<close> \<open>p_io (p'@[t]) \<notin> LS M q1\<close> snoc 
    by blast   
qed


lemma state_separator_from_canonical_separator_observable :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "observable A"
  using submachine_observable[OF _ canonical_separator_observable[OF assms(2,3,4)]]
  using assms(1) unfolding is_state_separator_from_canonical_separator_def 
  by metis


lemma canonical_separator_initial :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
  shows "initial (canonical_separator M q1 q2) = Inl (q1,q2)" 
    unfolding canonical_separator_simps[OF assms] by simp


lemma canonical_separator_states :
  assumes "Inl (s1,s2) \<in> states (canonical_separator M q1 q2)"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "(s1,s2) \<in> states (product (from_FSM M q1) (from_FSM M q2))"
  using assms(1) reachable_state_is_state
  unfolding canonical_separator_simps[OF assms(2,3)] by fastforce


lemma canonical_separator_transition :
  assumes "t \<in> transitions (canonical_separator M q1 q2)" (is "t \<in> transitions ?C")
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "t_source t = Inl (s1,s2)"
  and     "observable M"
  and     "q1 \<noteq> q2"
shows "\<And> s1' s2' . t_target t = Inl (s1',s2') \<Longrightarrow> (s1, t_input t, t_output t, s1') \<in> transitions M \<and> (s2, t_input t, t_output t, s2') \<in> transitions M "
and   "t_target t = Inr q1 \<Longrightarrow> (\<exists> t'\<in> transitions M . t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t) 
                                \<and> (\<not>(\<exists> t'\<in> transitions M . t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t))"
and   "t_target t = Inr q2 \<Longrightarrow> (\<exists> t'\<in> transitions M . t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t) 
                                \<and> (\<not>(\<exists> t'\<in> transitions M . t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t))"
and   "(\<exists> s1' s2' . t_target t = Inl (s1',s2')) \<or> t_target t = Inr q1 \<or> t_target t = Inr q2"
proof -
  show "\<And> s1' s2' . t_target t = Inl (s1',s2') \<Longrightarrow> (s1, t_input t, t_output t, s1') \<in> transitions M \<and> (s2, t_input t, t_output t, s2') \<in> transitions M"
    using canonical_separator_transition_targets(1)[OF assms(1,2,3)] assms(4)
    unfolding shifted_transitions_for_def[symmetric] 
    unfolding shifted_transitions_for_alt_def 
    unfolding product_transitions_def from_FSM_simps[OF assms(2)] from_FSM_simps[OF assms(3)] by fastforce

  show "t_target t = Inr q1 \<Longrightarrow> (\<exists> t'\<in> transitions M . t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t) 
                                \<and> (\<not>(\<exists> t'\<in> transitions M . t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t))"
    using canonical_separator_targets_observable(2)[OF assms(1,2,3,6)] assms(4)
    unfolding distinguishing_transitions_left_def by fastforce

  show "t_target t = Inr q2 \<Longrightarrow> (\<exists> t'\<in> transitions M . t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t) 
                                \<and> (\<not>(\<exists> t'\<in> transitions M . t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t))"
    using canonical_separator_targets_observable(3)[OF assms(1,2,3,6)] assms(4)
    unfolding distinguishing_transitions_right_def by fastforce

  show "(\<exists> s1' s2' . t_target t = Inl (s1',s2')) \<or> t_target t = Inr q1 \<or> t_target t = Inr q2"
    using canonical_separator_transition_targets(4)[OF assms(1,2,3)]
    by (simp add: isl_def) 
qed


lemma canonical_separator_transition_source :
  assumes "t \<in> transitions (canonical_separator M q1 q2)" (is "t \<in> transitions ?C")
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
obtains q1' q2' where "t_source t = Inl (q1',q2')"
                      "(q1',q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
proof -
  consider "t \<in> shifted_transitions_for M q1 q2" | "t \<in> distinguishing_transitions_left_alt M q1 q2" |
       "t \<in> distinguishing_transitions_right_alt M q1 q2"
    using assms(1)
    unfolding canonical_separator_transitions_alt_def[OF assms(2,3)] by blast
  then show ?thesis proof cases
    case 1
    then show ?thesis unfolding shifted_transitions_for_def using that
      using fsm_transition_source by fastforce
  next
    case 2
    then show ?thesis unfolding distinguishing_transitions_left_alt_def using that by fastforce
  next
    case 3
    then show ?thesis unfolding distinguishing_transitions_right_alt_def using that by fastforce
  qed 
qed


lemma canonical_separator_transition_ex :
  assumes "t \<in> transitions (canonical_separator M q1 q2)" (is "t \<in> transitions ?C")
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "t_source t = Inl (s1,s2)"
shows "(\<exists> t1 \<in> transitions M . t_source t1 = s1 \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t) \<or>
       (\<exists> t2 \<in> transitions M . t_source t2 = s2 \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t)"
proof -
  consider "t \<in> shifted_transitions_for M q1 q2" | "t \<in> distinguishing_transitions_left_alt M q1 q2" |
       "t \<in> distinguishing_transitions_right_alt M q1 q2"
    using assms(1)
    unfolding canonical_separator_transitions_alt_def[OF assms(2,3)] by blast
  then show ?thesis proof cases
    case 1
    then show ?thesis unfolding shifted_transitions_for_def 
      using product_from_transition_split[OF _ assms(2,3)]
      using assms(4) by force
  next
    case 2
    then show ?thesis unfolding distinguishing_transitions_left_alt_def
      using assms(4) by auto 
      
  next
    case 3
    then show ?thesis unfolding distinguishing_transitions_right_alt_def 
      using assms(4) by auto 
  qed 
qed


lemma canonical_separator_path_split_target_isl :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (p@[t])"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  shows "isl (target (initial (canonical_separator M q1 q2)) p)"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  have "t \<in> transitions ?C"
    using assms by auto
  moreover have "\<not> deadlock_state ?C (t_source t)"
    using assms unfolding deadlock_state.simps by blast
  ultimately show ?thesis 
    using canonical_separator_t_source_isl assms
    by fastforce
qed


lemma canonical_separator_path_initial :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p" (is "path ?C (initial ?C) p")
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "observable M"
  and     "q1 \<noteq> q2"
shows "\<And> s1' s2' . target (initial (canonical_separator M q1 q2)) p = Inl (s1',s2') \<Longrightarrow> (\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = p_io p2 \<and> p_io p1 = p_io p \<and> target q1 p1 = s1' \<and> target q2 p2 = s2')"
and   "target (initial (canonical_separator M q1 q2)) p = Inr q1 \<Longrightarrow> (\<exists> p1 p2 t . path M q1 (p1@[t]) \<and> path M q2 p2 \<and> p_io (p1@[t]) = p_io p \<and> p_io p2 = butlast (p_io p)) \<and> (\<not>(\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p))"
and   "target (initial (canonical_separator M q1 q2)) p = Inr q2 \<Longrightarrow> (\<exists> p1 p2 t . path M q1 p1 \<and> path M q2 (p2@[t]) \<and> p_io p1 = butlast (p_io p) \<and> p_io (p2@[t]) = p_io p) \<and> (\<not>(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p))"
and   "(\<exists> s1' s2' . target (initial (canonical_separator M q1 q2)) p = Inl (s1',s2')) \<or> target (initial (canonical_separator M q1 q2)) p = Inr q1 \<or> target (initial (canonical_separator M q1 q2)) p = Inr q2"
proof -

  let ?P1 = "\<forall> s1' s2' . target (initial (canonical_separator M q1 q2)) p = Inl (s1',s2') \<longrightarrow> (\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = p_io p2 \<and> p_io p1 = p_io p \<and> target q1 p1 = s1' \<and> target q2 p2 = s2')"
  let ?P2 = "target (initial (canonical_separator M q1 q2)) p = Inr q1 \<longrightarrow> (\<exists> p1 p2 t . path M q1 (p1@[t]) \<and> path M q2 p2 \<and> p_io (p1@[t]) = p_io p \<and> p_io p2 = butlast (p_io p)) \<and> (\<not>(\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p))"
  let ?P3 = "target (initial (canonical_separator M q1 q2)) p = Inr q2 \<longrightarrow> (\<exists> p1 p2 t . path M q1 p1 \<and> path M q2 (p2@[t]) \<and> p_io p1 = butlast (p_io p) \<and> p_io (p2@[t]) = p_io p) \<and> (\<not>(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p))"

  have "?P1 \<and> ?P2 \<and> ?P3"
  using assms(1) proof (induction p rule: rev_induct) 
    case Nil 
    then have "target (FSM.initial (canonical_separator M q1 q2)) [] = Inl (q1, q2)"
      unfolding canonical_separator_simps[OF assms(2,3)] by auto
    then show ?case using assms(2,3,4) by fastforce
  next
    case (snoc t p)
    
    have "path ?C (initial ?C) p" and "t \<in> transitions ?C" and "t_source t = target (initial ?C) p"
      using snoc.prems(1) by auto

    let ?P1' = "(\<forall>s1' s2'. target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inl (s1', s2') \<longrightarrow> (\<exists>p1 p2. path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = p_io p2 \<and> p_io p1 = p_io (p @ [t]) \<and> target q1 p1 = s1' \<and> target q2 p2 = s2'))"
    let ?P2' = "(target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q1 \<longrightarrow> (\<exists>p1 p2 ta. path M q1 (p1 @ [ta]) \<and> path M q2 p2 \<and> p_io (p1 @ [ta]) = p_io (p @ [t]) \<and> p_io p2 = butlast (p_io (p @ [t]))) \<and> (\<nexists>p2. path M q2 p2 \<and> p_io p2 = p_io (p @ [t])))"
    let ?P3' = "(target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q2 \<longrightarrow> (\<exists>p1 p2 ta. path M q1 p1 \<and> path M q2 (p2 @ [ta]) \<and> p_io p1 = butlast (p_io (p @ [t])) \<and> p_io (p2 @ [ta]) = p_io (p @ [t])) \<and> (\<nexists>p1. path M q1 p1 \<and> p_io p1 = p_io (p @ [t])))"

    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    
    obtain p' where "path ?P (initial ?P) p'"
              and   *:"p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
      using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) p\<close> canonical_separator_path_split_target_isl[OF snoc.prems assms(2,3)] assms(2,3)]
      by blast
      
  
    let ?pL = "(map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p')"
    let ?pR = "(map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p')"
  
    have "path ?P (q1,q2) p'"
      using \<open>path ?P (initial ?P) p'\<close> assms(2,3) unfolding product_simps(1) from_FSM_simps(1) by simp  
    then have pL: "path (from_FSM M q1) q1 ?pL"
         and  pR: "path (from_FSM M q2) q2 ?pR"
      using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p'] by simp+

    have "p_io ?pL = p_io p" and "p_io ?pR = p_io p"
      using * by auto

    have pf1: "path (from_FSM M q1) (initial (from_FSM M q1)) ?pL"
      using pL assms(2) unfolding from_FSM_simps(1) by auto
    have pf2: "path (from_FSM M q2) (initial (from_FSM M q2)) ?pR"
      using pR assms(3) unfolding from_FSM_simps(1) by auto
    have pio: "p_io ?pL = p_io ?pR"
      by auto
    
    have "p_io (zip_path ?pL ?pR) = p_io ?pL"
      by (induction p'; auto)

    have zip1: "path ?P (initial ?P) (zip_path ?pL ?pR)"
    and  "target (initial ?P) (zip_path ?pL ?pR) = (target q1 ?pL, target q2 ?pR)"
      using product_path_from_paths[OF pf1 pf2 pio] assms(2,3)
      unfolding from_FSM_simps(1) by simp+
      
    have "p_io (zip_path ?pL ?pR) = p_io p"
      using \<open>p_io ?pL = p_io p\<close> \<open>p_io (zip_path ?pL ?pR) = p_io ?pL\<close> by auto 
    have "observable ?P"
      using product_observable[OF from_FSM_observable[OF assms(4)] from_FSM_observable[OF assms(4)]] by assumption
    
    have "p_io p' = p_io p"
      using * by auto
    
    obtain s1 s2 where "t_source t = Inl (s1,s2)"
      using canonical_separator_path_split_target_isl[OF snoc.prems(1) assms(2,3)] 
      by (metis \<open>t_source t = target (initial (canonical_separator M q1 q2)) p\<close> isl_def old.prod.exhaust)
  
    have "map t_target p = map (Inl o t_target) p'"
      using * by auto
    have "target (initial ?C) p = Inl (target (q1,q2) p')"
      unfolding target.simps visited_states.simps canonical_separator_simps[OF assms(2,3)] 
      unfolding \<open>map t_target p = map (Inl o t_target) p'\<close>
      by (simp add: last_map)
    then have "target (q1,q2) p'= (s1,s2)"
      using \<open>t_source t = target (initial ?C) p\<close> \<open>t_source t = Inl (s1,s2)\<close>
      by auto 
      
    have "target q1 ?pL = s1" and "target q2 ?pR = s2"  
      using product_target_split[OF \<open>target (q1,q2) p'= (s1,s2)\<close>] by auto

    consider (a) "(\<exists>s1' s2'. t_target t = Inl (s1', s2'))" |
             (b) "t_target t = Inr q1" |
             (c) "t_target t = Inr q2"
      using canonical_separator_transition(4)[OF \<open>t \<in> transitions ?C\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>t_source t = Inl (s1,s2)\<close> \<open>observable M\<close> \<open>q1 \<noteq> q2\<close>]
      by blast
    then show "?P1' \<and> ?P2' \<and> ?P3'" proof cases
      case a
      then obtain s1' s2' where "t_target t = Inl (s1',s2')"
        by blast

      let ?t1 = "(s1, t_input t, t_output t, s1')"
      let ?t2 = "(s2, t_input t, t_output t, s2')"

      have "?t1 \<in> transitions M" 
      and  "?t2 \<in> transitions M"
        using canonical_separator_transition(1)[OF \<open>t \<in> transitions ?C\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>t_source t = Inl (s1,s2)\<close> \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close> \<open>t_target t = Inl (s1',s2')\<close>] 
        by auto

      have "target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inl (s1', s2')"
        using \<open>t_target t = Inl (s1',s2')\<close> by auto

      have "path M q1 (?pL@[?t1])"
        using path_append_transition[OF from_FSM_path[OF \<open>q1 \<in> states M\<close> pL] \<open>?t1 \<in> transitions M\<close>] \<open>target q1 ?pL = s1\<close> by auto
      moreover have "path M q2 (?pR@[?t2])"
        using path_append_transition[OF from_FSM_path[OF \<open>q2 \<in> states M\<close> pR] \<open>?t2 \<in> transitions M\<close>] \<open>target q2 ?pR = s2\<close> by auto
      moreover have "p_io (?pL@[?t1]) = p_io (?pR@[?t2])"
        by auto
      moreover have "p_io (?pL@[?t1]) = p_io (p@[t])"
        using \<open>p_io ?pL = p_io p\<close> by auto
      moreover have "target q1 (?pL@[?t1]) = s1'" and "target q2 (?pR@[?t2]) = s2'"
        by auto 
      ultimately have "path M q1 (?pL@[?t1]) \<and> path M q2 (?pR@[?t2]) \<and> p_io (?pL@[?t1]) = p_io (?pR@[?t2]) \<and> p_io (?pL@[?t1]) = p_io (p@[t]) \<and> target q1 (?pL@[?t1]) = s1' \<and> target q2 (?pR@[?t2]) = s2'"
        by presburger
      then have "(\<exists>p1 p2. path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = p_io p2 \<and> p_io p1 = p_io (p @ [t]) \<and> target q1 p1 = s1' \<and> target q2 p2 = s2')"
        by meson
      then have ?P1'
        using \<open>target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inl (s1', s2')\<close> by auto
      then show ?thesis using \<open>target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inl (s1', s2')\<close> 
        by auto
    next
      case b
      then have "target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q1"
        by auto

      have "(\<exists>t'\<in>(transitions M). t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
      and  "\<not> (\<exists>t'\<in>(transitions M). t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
        using canonical_separator_transition(2)[OF \<open>t \<in> transitions ?C\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>t_source t = Inl (s1,s2)\<close> \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close> b] by blast+

      then obtain t' where "t' \<in> transitions M" and "t_source t' = s1" and "t_input t' = t_input t" and "t_output t' = t_output t"
        by blast

      have "path M q1 (?pL@[t'])"
        using path_append_transition[OF from_FSM_path[OF \<open>q1 \<in> states M\<close> pL] \<open>t' \<in> transitions M\<close>] \<open>target q1 ?pL = s1\<close> \<open>t_source t' = s1\<close> by auto
      moreover have "p_io (?pL@[t']) = p_io (p@[t])"
        using \<open>p_io ?pL = p_io p\<close> \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> by auto
      moreover have "p_io ?pR = butlast (p_io (p @ [t]))"
        using \<open>p_io ?pR = p_io p\<close> by auto
      ultimately have "path M q1 (?pL@[t']) \<and> path M q2 ?pR \<and> p_io (?pL@[t']) = p_io (p @ [t]) \<and> p_io ?pR = butlast (p_io (p @ [t]))"
        using from_FSM_path[OF \<open>q2 \<in> states M\<close> pR] by linarith
      then have "(\<exists>p1 p2 ta. path M q1 (p1 @ [ta]) \<and> path M q2 p2 \<and> p_io (p1 @ [ta]) = p_io (p @ [t]) \<and> p_io p2 = butlast (p_io (p @ [t])))"
        by meson
            
      moreover have "(\<nexists>p2. path M q2 p2 \<and> p_io p2 = p_io (p @ [t]))"
      proof 
        assume "\<exists>p2. path M q2 p2 \<and> p_io p2 = p_io (p @ [t])"
        then obtain p'' where "path M q2 p'' \<and> p_io p'' = p_io (p @ [t])"
          by blast
        then have "p'' \<noteq> []" by auto
        then obtain p2 t2 where "p'' = p2@[t2]"
          using rev_exhaust by blast
        then have "path M q2 (p2@[t2])" and "p_io (p2@[t2]) = p_io (p @ [t])"
          using \<open>path M q2 p'' \<and> p_io p'' = p_io (p @ [t])\<close> by auto
        then have "path M q2 p2" by auto


        then have pf2': "path (from_FSM M q2) (initial (from_FSM M q2)) p2"
          using from_FSM_path_initial[OF \<open>q2 \<in> states M\<close>, of p2] by simp
        have pio': "p_io ?pL = p_io p2"
          using \<open>p_io (?pL@[t']) = p_io (p@[t])\<close> \<open>p_io (p2@[t2]) = p_io (p @ [t])\<close> by auto

        have zip2: "path ?P (initial ?P) (zip_path ?pL p2)"
        and  "target (initial ?P) (zip_path ?pL p2) = (target q1 ?pL, target q2 p2)"
          using product_path_from_paths[OF pf1 pf2' pio'] assms(2,3)
          unfolding from_FSM_simps(1) by simp+

        have "length p' = length p2"
          using \<open>p_io (p2@[t2]) = p_io (p @ [t])\<close> 
          by (metis (no_types, lifting) length_map pio') 
        then have "p_io (zip_path ?pL p2) = p_io p'"
          by (induction p' p2 rule: list_induct2; auto)
        then have "p_io (zip_path ?pL p2) = p_io p"
          using * by auto
        then have "p_io (zip_path ?pL ?pR) = p_io (zip_path ?pL p2)" 
          using \<open>p_io (zip_path ?pL ?pR) = p_io p\<close> by simp

        have "p_io ?pR = p_io p2"
          using \<open>p_io ?pL = p_io p2\<close> pio by auto 


        have l1: "length ?pL = length ?pR" by auto
        have l2: "length ?pR = length ?pL" by auto 
        have l3: "length ?pL = length p2" using \<open>length p' = length p2\<close> by auto
        
        have "p2 = ?pR"
          using zip_path_eq_right[OF l1 l2 l3 \<open>p_io ?pR = p_io p2\<close> observable_path_unique[OF \<open>observable ?P\<close> zip1 zip2 \<open>p_io (zip_path ?pL ?pR) = p_io (zip_path ?pL p2)\<close>]] by simp
        then have "target q2 p2 = s2"
          using \<open>target q2 ?pR = s2\<close> by auto
        then have "t2 \<in> transitions M" and "t_source t2 = s2"
          using \<open>path M q2 (p2@[t2])\<close> by auto
        moreover have "t_input t2 = t_input t \<and> t_output t2 = t_output t"
          using \<open>p_io (p2@[t2]) = p_io (p @ [t])\<close> by auto
        ultimately show "False"
          using \<open>\<not> (\<exists>t'\<in>(transitions M). t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close> by blast
      qed

      ultimately have ?P2' 
        by blast
      moreover have ?P3' 
        using  \<open>q1 \<noteq> q2\<close> \<open>t_target t = Inr q1\<close> by auto
      moreover have ?P1'
       using \<open>target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q1\<close> by auto
     ultimately show ?thesis
       by blast
    next
      case c
      then have "target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q2"
        by auto

      have "(\<exists>t'\<in>(transitions M). t_source t' = s2 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
      and  "\<not> (\<exists>t'\<in>(transitions M). t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
        using canonical_separator_transition(3)[OF \<open>t \<in> transitions ?C\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>t_source t = Inl (s1,s2)\<close> \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close> c] by blast+

      then obtain t' where "t' \<in> transitions M" and "t_source t' = s2" and "t_input t' = t_input t" and "t_output t' = t_output t"
        by blast

      have "path M q2 (?pR@[t'])"
        using path_append_transition[OF from_FSM_path[OF \<open>q2 \<in> states M\<close> pR] \<open>t' \<in> transitions M\<close>] \<open>target q2 ?pR = s2\<close> \<open>t_source t' = s2\<close> by auto
      moreover have "p_io (?pR@[t']) = p_io (p@[t])"
        using \<open>p_io ?pR = p_io p\<close> \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> by auto
      moreover have "p_io ?pL = butlast (p_io (p @ [t]))"
        using \<open>p_io ?pL = p_io p\<close> by auto
      ultimately have "path M q2 (?pR@[t']) \<and> path M q1 ?pL \<and> p_io (?pR@[t']) = p_io (p @ [t]) \<and> p_io ?pL = butlast (p_io (p @ [t]))"
        using from_FSM_path[OF \<open>q1 \<in> states M\<close> pL] by linarith
      then have "(\<exists>p1 p2 ta. path M q1 p1 \<and> path M q2 (p2 @ [ta]) \<and> p_io p1 = butlast (p_io (p @ [t])) \<and> p_io (p2 @ [ta]) = p_io (p @ [t]))"
        by meson
            
      moreover have "(\<nexists>p1. path M q1 p1 \<and> p_io p1 = p_io (p @ [t]))"
      proof 
        assume "\<exists>p1. path M q1 p1 \<and> p_io p1 = p_io (p @ [t])"
        then obtain p'' where "path M q1 p'' \<and> p_io p'' = p_io (p @ [t])"
          by blast
        then have "p'' \<noteq> []" by auto
        then obtain p1 t1 where "p'' = p1@[t1]"
          using rev_exhaust by blast
        then have "path M q1 (p1@[t1])" and "p_io (p1@[t1]) = p_io (p @ [t])"
          using \<open>path M q1 p'' \<and> p_io p'' = p_io (p @ [t])\<close> by auto
        then have "path M q1 p1" 
          by auto
        then have pf1': "path (from_FSM M q1) (initial (from_FSM M q1)) p1"
          using from_FSM_path_initial[OF \<open>q1 \<in> states M\<close>, of p1] by simp
        have pio': "p_io p1 = p_io ?pR"
          using \<open>p_io (?pR@[t']) = p_io (p@[t])\<close> \<open>p_io (p1@[t1]) = p_io (p @ [t])\<close> by auto

        have zip2: "path ?P (initial ?P) (zip_path p1 ?pR)"
          using product_path_from_paths[OF pf1' pf2 pio']
          unfolding from_FSM_simps(1) by simp

        have "length p' = length p1"
          using \<open>p_io (p1@[t1]) = p_io (p @ [t])\<close> 
          by (metis (no_types, lifting) length_map pio') 
        then have "p_io (zip_path p1 ?pR) = p_io p'"
          using \<open>p_io p1 = p_io ?pR\<close> by (induction p' p1 rule: list_induct2; auto)
        then have "p_io (zip_path p1 ?pR) = p_io p"
          using * by auto
        then have "p_io (zip_path ?pL ?pR) = p_io (zip_path p1 ?pR)" 
          using \<open>p_io (zip_path ?pL ?pR) = p_io p\<close> by simp
        
        have l1: "length ?pL = length ?pR" by auto
        have l2: "length ?pR = length p1" using \<open>length p' = length p1\<close> by auto
        have l3: "length p1 = length ?pR" using l2 by auto
        
        have "?pL = p1"
          using zip_path_eq_left[OF l1 l2 l3 observable_path_unique[OF \<open>observable ?P\<close> zip1 zip2 \<open>p_io (zip_path ?pL ?pR) = p_io (zip_path p1 ?pR)\<close>]] by simp
        then have "target q1 p1 = s1"
          using \<open>target q1 ?pL = s1\<close> by auto
        then have "t1 \<in> transitions M" and "t_source t1 = s1"
          using \<open>path M q1 (p1@[t1])\<close> by auto
        moreover have "t_input t1 = t_input t \<and> t_output t1 = t_output t"
          using \<open>p_io (p1@[t1]) = p_io (p @ [t])\<close> by auto
        ultimately show "False"
          using \<open>\<not> (\<exists>t'\<in>(transitions M). t_source t' = s1 \<and> t_input t' = t_input t \<and> t_output t' = t_output t)\<close> by blast
      qed

      ultimately have ?P3' 
        by blast
      moreover have ?P2' 
        using \<open>q1 \<noteq> q2\<close> \<open>t_target t = Inr q2\<close> by auto
      moreover have ?P1'
        using \<open>target (initial (canonical_separator M q1 q2)) (p @ [t]) = Inr q2\<close> by auto
      ultimately show ?thesis
        by blast
    qed 
  qed

  then show  "\<And> s1' s2' . target (initial (canonical_separator M q1 q2)) p = Inl (s1',s2') \<Longrightarrow> (\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = p_io p2 \<and> p_io p1 = p_io p \<and> target q1 p1 = s1' \<and> target q2 p2 = s2')"
       and   "target (initial (canonical_separator M q1 q2)) p = Inr q1 \<Longrightarrow> (\<exists> p1 p2 t . path M q1 (p1@[t]) \<and> path M q2 p2 \<and> p_io (p1@[t]) = p_io p \<and> p_io p2 = butlast (p_io p)) \<and> (\<not>(\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p))"
       and   "target (initial (canonical_separator M q1 q2)) p = Inr q2 \<Longrightarrow> (\<exists> p1 p2 t . path M q1 p1 \<and> path M q2 (p2@[t]) \<and> p_io p1 = butlast (p_io p) \<and> p_io (p2@[t]) = p_io p) \<and> (\<not>(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p))"
    by blast+

  
  show   "(\<exists> s1' s2' . target (initial (canonical_separator M q1 q2)) p = Inl (s1',s2')) \<or> target (initial (canonical_separator M q1 q2)) p = Inr q1 \<or> target (initial (canonical_separator M q1 q2)) p = Inr q2"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis unfolding canonical_separator_simps(1)[OF assms(2,3)] by auto
  next
    case (snoc p' t)
    then have "t \<in> transitions ?C" and "target (initial (canonical_separator M q1 q2)) p = t_target t"
      using assms(1) by auto
    then have "t \<in> (transitions ?C)"
      by auto
    obtain s1 s2 where "t_source t = Inl (s1,s2)"
      using canonical_separator_t_source_isl[OF \<open>t \<in> (transitions ?C)\<close> assms(2,3)]
      by (metis sum.collapse(1) surjective_pairing)
    show ?thesis
      using canonical_separator_transition(4)[OF \<open>t \<in> transitions ?C\<close> assms(2,3) \<open>t_source t = Inl (s1,s2)\<close> assms(4) \<open>q1 \<noteq> q2\<close>] 
            \<open>target (initial (canonical_separator M q1 q2)) p = t_target t\<close>
      by simp 
  qed 
qed


(* does not assume observability of M (in contrast to the much stronger canonical_separator_path_initial) *)
lemma canonical_separator_path_initial_ex :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p" (is "path ?C (initial ?C) p")
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p) \<or> (\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p)"
and   "(\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io p) \<and> p_io p2 = butlast (p_io p))"
proof -
  have "((\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p) \<or> (\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p))
         \<and> (\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io p) \<and> p_io p2 = butlast (p_io p))"
  using assms proof (induction p rule: rev_induct) 
    case Nil
    then show ?case by auto
  next
    case (snoc t p)
    then have "path ?C (initial ?C) p" and "t \<in> transitions ?C" and "t_source t = target (initial ?C) p"
      by auto
  
    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    
    obtain p' where "path ?P (initial ?P) p'"
              and   *:"p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
      using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) p\<close> canonical_separator_path_split_target_isl[OF snoc.prems(1) assms(2,3)] assms(2,3)]
      by blast
  
    let ?pL = "(map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p')"
    let ?pR = "(map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p')"
  
    have "path ?P (q1,q2) p'"
      using \<open>path ?P (initial ?P) p'\<close> assms(2,3) by simp
  
    then have pL: "path (from_FSM M q1) q1 ?pL"
         and  pR: "path (from_FSM M q2) q2 ?pR"
      using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p'] by auto

    have "p_io ?pL = butlast (p_io (p@[t]))" and "p_io ?pR = butlast (p_io (p@[t]))"
      using * by auto
    then have "path M q1 ?pL \<and> path M q2 ?pR \<and> p_io ?pL = butlast (p_io (p@[t])) \<and> p_io ?pR = butlast (p_io (p@[t]))"
      using from_FSM_path[OF \<open>q1 \<in> states M\<close> pL] from_FSM_path[OF \<open>q2 \<in> states M\<close> pR] by auto
    then have "(\<exists>p1 p2. path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io (p @ [t])) \<and> p_io p2 = butlast (p_io (p @ [t])))"
      by blast
    
    obtain s1 s2 where "t_source t = Inl (s1,s2)"
      using canonical_separator_path_split_target_isl[OF snoc.prems(1) assms(2,3)] 
      by (metis \<open>t_source t = target (initial (canonical_separator M q1 q2)) p\<close> isl_def old.prod.exhaust)
  
    have "map t_target p = map (Inl o t_target) p'"
      using * by auto
    then have "target (initial ?C) p = Inl (target (q1,q2) p')"
      unfolding target.simps visited_states.simps canonical_separator_simps(1)[OF assms(2,3)] 
      by (simp add: last_map) 
    then have "target (q1,q2) p'= (s1,s2)"
      using \<open>t_source t = target (initial ?C) p\<close> \<open>t_source t = Inl (s1,s2)\<close>
      by auto 
      
    have "target q1 ?pL = s1" and "target q2 ?pR = s2"  
      using product_target_split[OF \<open>target (q1,q2) p'= (s1,s2)\<close>] by auto
  
    consider (a) "(\<exists>t1\<in>(transitions M). t_source t1 = s1 \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t)" |
             (b) "(\<exists>t2\<in>(transitions M). t_source t2 = s2 \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t)"
      using canonical_separator_transition_ex[OF \<open>t \<in> transitions ?C\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>t_source t = Inl (s1,s2)\<close>] by blast
    then show ?case proof cases
      case a
      then obtain t1 where "t1 \<in> transitions M" and "t_source t1 = s1" and "t_input t1 = t_input t" and "t_output t1 = t_output t" 
        by blast
  
      have "t_source t1 = target q1 ?pL"
        using \<open>target q1 ?pL = s1\<close> \<open>t_source t1 = s1\<close> by auto
      then have "path M q1 (?pL@[t1])"
        using pL \<open>t1 \<in> transitions M\<close>
        by (meson from_FSM_path path_append_transition snoc.prems(2))
      moreover have "p_io (?pL@[t1]) = p_io (p@[t])"
        using * \<open>t_input t1 = t_input t\<close> \<open>t_output t1 = t_output t\<close> by auto
      ultimately show ?thesis
        using \<open>(\<exists>p1 p2. path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io (p @ [t])) \<and> p_io p2 = butlast (p_io (p @ [t])))\<close>
        by meson
    next
      case b
      then obtain t2 where "t2 \<in> transitions M" and "t_source t2 = s2" and "t_input t2 = t_input t" and "t_output t2 = t_output t" 
        by blast
  
      have "t_source t2 = target q2 ?pR"
        using \<open>target q2 ?pR = s2\<close> \<open>t_source t2 = s2\<close> by auto
      then have "path M q2 (?pR@[t2])"
        using pR \<open>t2 \<in> transitions M\<close>
        by (meson from_FSM_path path_append_transition snoc.prems(3))
      moreover have "p_io (?pR@[t2]) = p_io (p@[t])"
        using * \<open>t_input t2 = t_input t\<close> \<open>t_output t2 = t_output t\<close> by auto
      ultimately show ?thesis
        using \<open>(\<exists>p1 p2. path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io (p @ [t])) \<and> p_io p2 = butlast (p_io (p @ [t])))\<close>
        by meson
    qed
  qed
  then show "(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p) \<or> (\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p)"
       and  "(\<exists> p1 p2 . path M q1 p1 \<and> path M q2 p2 \<and> p_io p1 = butlast (p_io p) \<and> p_io p2 = butlast (p_io p))"
    by blast+
qed


lemma canonical_separator_language :
  assumes "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "L (canonical_separator M q1 q2) \<subseteq> L (from_FSM M q1) \<union> L (from_FSM M q2)" (is "L ?C \<subseteq> L ?M1 \<union> L ?M2")
proof 
  fix io assume "io \<in> L (canonical_separator M q1 q2)"
  then obtain p where *: "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p" and **: "p_io p = io"
    by auto
  
  show "io \<in> L (from_FSM M q1) \<union> L (from_FSM M q2)"
    using canonical_separator_path_initial_ex[OF * assms] unfolding ** 
    using from_FSM_path_initial[OF assms(1)] from_FSM_path_initial[OF assms(2)]  
    unfolding LS.simps by blast
qed


lemma canonical_separator_language_prefix :
  assumes "io@[xy] \<in> L (canonical_separator M q1 q2)"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "observable M"
  and     "q1 \<noteq> q2"
shows "io \<in> LS M q1"
and   "io \<in> LS M q2"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  obtain p where "path ?C (initial ?C) p" and "p_io p = io@[xy]"
    using assms(1) by auto

  consider (a) "(\<exists>s1' s2'. target (initial (canonical_separator M q1 q2)) p = Inl (s1', s2'))" |
           (b) "target (initial (canonical_separator M q1 q2)) p = Inr q1" | 
           (c) "target (initial (canonical_separator M q1 q2)) p = Inr q2"
    using canonical_separator_path_initial(4)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5)] by blast
  then have "io \<in> LS M q1 \<and> io \<in> LS M q2"
  proof cases
    case a
    then obtain s1 s2 where *: "target (initial (canonical_separator M q1 q2)) p = Inl (s1, s2)"
      by blast
    show ?thesis using canonical_separator_path_initial(1)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5) *] language_prefix
      by (metis (mono_tags, lifting) LS.simps \<open>p_io p = io @ [xy]\<close> mem_Collect_eq )
  next
    case b
    show ?thesis using canonical_separator_path_initial(2)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5) b]
      using \<open>p_io p = io @ [xy]\<close> by fastforce      
  next
    case c
    show ?thesis using canonical_separator_path_initial(3)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5) c]
      using \<open>p_io p = io @ [xy]\<close> by fastforce
  qed
  then show "io \<in> LS M q1" and   "io \<in> LS M q2"
    by auto
qed


lemma canonical_separator_distinguishing_transitions_left_containment :
  assumes "t \<in> (distinguishing_transitions_left M q1 q2)"
      and "q1 \<in> states M" and "q2 \<in> states M"
    shows "t \<in> transitions (canonical_separator M q1 q2)" 
  using assms(1) unfolding canonical_separator_transitions_def[OF assms(2,3)] by blast


lemma canonical_separator_distinguishing_transitions_right_containment :
  assumes "t \<in> (distinguishing_transitions_right M q1 q2)"
      and "q1 \<in> states M" and "q2 \<in> states M"
  shows "t \<in> transitions (canonical_separator M q1 q2)" (is "t \<in> transitions ?C")
   using assms(1) unfolding canonical_separator_transitions_def[OF assms(2,3)] by blast


lemma distinguishing_transitions_left_alt_intro :
  assumes "(s1,s2) \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
  and "(\<exists>t \<in> transitions M. t_source t = s1 \<and> t_input t = x \<and> t_output t = y)" 
  and "\<not>(\<exists>t \<in> transitions M. t_source t = s2 \<and> t_input t = x \<and> t_output t = y)" 
shows "(Inl (s1,s2), x, y, Inr q1) \<in> distinguishing_transitions_left_alt M q1 q2"
  using assms unfolding distinguishing_transitions_left_alt_def
  by auto 


lemma distinguishing_transitions_left_right_intro :
  assumes "(s1,s2) \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
  and "\<not>(\<exists>t \<in> transitions M. t_source t = s1 \<and> t_input t = x \<and> t_output t = y)" 
  and "(\<exists>t \<in> transitions M. t_source t = s2 \<and> t_input t = x \<and> t_output t = y)" 
shows "(Inl (s1,s2), x, y, Inr q2) \<in> distinguishing_transitions_right_alt M q1 q2"
  using assms unfolding distinguishing_transitions_right_alt_def
  by auto 


lemma canonical_separator_io_from_prefix_left :
  assumes "io @ [io1] \<in> LS M q1"
  and     "io \<in> LS M q2"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "observable M"
  and     "q1 \<noteq> q2"
shows "io @ [io1] \<in> L (canonical_separator M q1 q2)"
proof -
  let ?C = "canonical_separator M q1 q2"

  obtain p1 where "path M q1 p1" and "p_io p1 = io @ [io1]"
    using \<open>io @ [io1] \<in> LS M q1\<close> by auto
  then have "p1 \<noteq> []"
    by auto
  then obtain pL tL where "p1 = pL @ [tL]"
    using rev_exhaust by blast
  then have "path M q1 (pL@[tL])" and "path M q1 pL" and "p_io pL = io" and "tL \<in> transitions M" 
        and "t_input tL = fst io1" and "t_output tL = snd io1" and "p_io (pL@[tL]) = io @ [io1]"
    using \<open>path M q1 p1\<close> \<open>p_io p1 = io @ [io1]\<close> by auto
  then have pLf: "path (from_FSM M q1) (initial (from_FSM M q1)) pL" 
        and pLf': "path (from_FSM M q1) (initial (from_FSM M q1)) (pL@[tL])"
    using from_FSM_path_initial[OF \<open>q1 \<in> states M\<close>] by auto

  obtain pR where "path M q2 pR" and "p_io pR = io"
    using \<open>io \<in> LS M q2\<close> by auto
  then have pRf: "path (from_FSM M q2) (initial (from_FSM M q2)) pR"
    using from_FSM_path_initial[OF \<open>q2 \<in> states M\<close>] by auto

  have "p_io pL = p_io pR"
    using \<open>p_io pL = io\<close> \<open>p_io pR = io\<close> by auto

  let ?pLR = "zip_path pL pR"
  let ?pCLR = "map shift_Inl ?pLR"
  let ?P = "product (from_FSM M q1) (from_FSM M q2)"

  have "path ?P (initial ?P) ?pLR"
  and  "target (initial ?P) ?pLR = (target q1 pL, target q2 pR)"
    using product_path_from_paths[OF pLf pRf \<open>p_io pL = p_io pR\<close>]
    unfolding from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)] by linarith+

  have "path ?C (initial ?C) ?pCLR"
    using canonical_separator_path_shift[OF assms(3,4)] \<open>path ?P (initial ?P) ?pLR\<close> 
    by simp 

  have "isl (target (initial ?C) ?pCLR)" 
    unfolding canonical_separator_simps(1)[OF assms(3,4)] by (cases ?pLR rule: rev_cases; auto)
  then obtain s1 s2 where "target (initial ?C) ?pCLR = Inl (s1,s2)"
    by (metis (no_types, lifting) \<open>path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) (map (\<lambda>t. ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), t_target (fst t), t_target (snd t))) (zip pL pR)))\<close> 
          assms(3) assms(4) assms(5) assms(6) canonical_separator_path_initial(4) sum.discI(2))
  then have "Inl (s1,s2) \<in> states ?C"
    using path_target_is_state[OF \<open>path ?C (initial ?C) ?pCLR\<close>] by simp
  then have "(s1,s2) \<in> states ?P"
    using canonical_separator_states[OF _ assms(3,4)] by force

  have "target (initial ?P) ?pLR = (s1,s2)"
    using \<open>target (initial ?C) ?pCLR = Inl (s1,s2)\<close> assms(3,4) 
    unfolding canonical_separator_simps(1)[OF assms(3,4)] product_simps(1) from_FSM_simps target.simps visited_states.simps 
    by (cases ?pLR rule: rev_cases; auto)
  then have "target q1 pL = s1" and "target q2 pR = s2"
    using \<open>target (initial ?P) ?pLR = (target q1 pL, target q2 pR)\<close> by auto
  then have "t_source tL = s1"
    using \<open>path M q1 (pL@[tL])\<close> by auto

  show ?thesis proof (cases "\<exists> tR \<in> (transitions M) . t_source tR = target q2 pR \<and> t_input tR = t_input tL \<and> t_output tR = t_output tL")
    case True
    then obtain tR where "tR \<in> (transitions M)" and "t_source tR = target q2 pR" and "t_input tR = t_input tL" and "t_output tR = t_output tL"
      by blast
    
    have "t_source tR \<in> states M"
      unfolding \<open>t_source tR = target q2 pR\<close> \<open>target q2 pR = s2\<close> 
      using \<open>(s1,s2) \<in> states ?P\<close> product_simps(2) from_FSM_simps(2) assms(3,4) by simp

    then have "tR \<in> transitions M"
      using \<open>tR \<in> (transitions M)\<close> \<open>t_input tR = t_input tL\<close> \<open>t_output tR = t_output tL\<close> \<open>tL \<in> transitions M\<close> by auto

    then have "path M q2 (pR@[tR])" 
      using \<open>path M q2 pR\<close> \<open>t_source tR = target q2 pR\<close> path_append_transition by metis
    then have pRf': "path (from_FSM M q2) (initial (from_FSM M q2)) (pR@[tR])"
      using from_FSM_path_initial[OF \<open>q2 \<in> states M\<close>] by auto
    
    let ?PP = "(zip_path (pL@[tL]) (pR@[tR]))"
    let ?PC = "map shift_Inl ?PP"

    have "length pL = length pR"
      using \<open>p_io pL = p_io pR\<close> map_eq_imp_length_eq by blast
    moreover have "p_io (pL@[tL]) = p_io (pR@[tR])"
      using \<open>p_io pR = io\<close> \<open>t_input tL = fst io1\<close> \<open>t_output tL = snd io1\<close> \<open>t_input tR = t_input tL\<close> \<open>t_output tR = t_output tL\<close> \<open>p_io (pL@[tL]) = io@[io1]\<close> by auto
    ultimately have "p_io ?PP = p_io (pL@[tL])"
      by (induction pL pR rule: list_induct2; auto)

    have "p_io ?PC = p_io ?PP"
      by auto
           
    have "path ?P (initial ?P) ?PP"
      using product_path_from_paths(1)[OF pLf' pRf' \<open>p_io (pL@[tL]) = p_io (pR@[tR])\<close>] by assumption
    then have "path ?C (initial ?C) ?PC"
      using canonical_separator_path_shift[OF assms(3,4)] by simp    
    moreover have "p_io ?PC = io@[io1]"
      using \<open>p_io (pL@[tL]) = io@[io1]\<close>  \<open>p_io ?PP = p_io (pL@[tL])\<close>  \<open>p_io ?PC = p_io ?PP\<close> by simp
    ultimately have "\<exists> p . path ?C (initial ?C) p \<and> p_io p = io@[io1]"
      by blast
    then show ?thesis unfolding LS.simps by force
  next
    case False

    let ?t = "(Inl (s1,s2), t_input tL, t_output tL, Inr q1)"

    have "(s1,s2) \<in> reachable_states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
      by (metis (no_types, lifting) \<open>path (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2)) (FSM.initial (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))) (zip_path pL pR)\<close> \<open>target (FSM.initial (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))) (zip_path pL pR) = (s1, s2)\<close> reachable_states_intro)
    moreover have "(\<exists>tR\<in>FSM.transitions M.
           t_source tR = target q1 pL \<and> t_input tR = t_input tL \<and> t_output tR = t_output tL)"
      using \<open>tL \<in> transitions M\<close> \<open>path M q1 (pL@[tL])\<close>
      by auto     
    ultimately have "?t \<in> (distinguishing_transitions_left_alt M q1 q2)"
      using distinguishing_transitions_left_alt_intro[OF _ _ False ]  \<open>q1 \<noteq> q2\<close>
      unfolding \<open>target q1 pL = s1\<close> \<open>target q2 pR = s2\<close>
      using \<open>(s1, s2) \<in> FSM.states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))\<close> by blast
    then have "?t \<in> transitions ?C" 
      using canonical_separator_distinguishing_transitions_left_containment[OF _ assms(3,4)] unfolding distinguishing_transitions_left_alt_alt_def by blast 
    then have "path ?C (initial ?C) (?pCLR@[?t])"
      using \<open>path ?C (initial ?C) ?pCLR\<close> \<open>target (initial ?C) ?pCLR = Inl (s1,s2)\<close> 
      by (simp add: path_append_transition)

    have "length pL = length pR"
      using \<open>p_io pL = p_io pR\<close> 
      using map_eq_imp_length_eq by blast
    then have "p_io ?pCLR = p_io pL" 
      by (induction pL pR rule: list_induct2; auto)
    then have "p_io (?pCLR@[?t]) = io @ [io1]"
      using \<open>p_io pL = io\<close> \<open>t_input tL = fst io1\<close> \<open>t_output tL = snd io1\<close>
      by auto
    then have "\<exists> p . path ?C (initial ?C) p \<and> p_io p = io@[io1]"
      using \<open>path ?C (initial ?C) (?pCLR@[?t])\<close> by meson
    then show ?thesis 
      unfolding LS.simps by force
  qed
qed





lemma canonical_separator_path_targets_language :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p"
  and     "observable M" 
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "isl (target (initial (canonical_separator M q1 q2)) p) \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2"
and   "(target (initial (canonical_separator M q1 q2)) p) = Inr q1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
and   "(target (initial (canonical_separator M q1 q2)) p) = Inr q2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
and   "p_io p \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> isl (target (initial (canonical_separator M q1 q2)) p)"
and   "p_io p \<in> LS M q1 - LS M q2 \<Longrightarrow> target (initial (canonical_separator M q1 q2)) p = Inr q1"
and   "p_io p \<in> LS M q2 - LS M q1 \<Longrightarrow> target (initial (canonical_separator M q1 q2)) p = Inr q2"
proof -
  let ?C = "canonical_separator M q1 q2"
  let ?tgt = "target (initial ?C) p"

  show "isl ?tgt \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2"
  proof -
    assume "isl ?tgt"
    then obtain s1 s2 where "?tgt = Inl (s1,s2)"
      by (metis isl_def old.prod.exhaust)
    then obtain p1 p2 where "path M q1 p1" and "path M q2 p2" and "p_io p1 = p_io p" and "p_io p2 = p_io p" 
      using canonical_separator_path_initial(1)[OF assms(1) \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close> \<open>?tgt = Inl (s1,s2)\<close> ] by force
    then show "p_io p \<in> LS M q1 \<inter> LS M q2"
      unfolding LS.simps by force
  qed
  moreover show "?tgt = Inr q1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
  proof -
    assume "?tgt = Inr q1"
    obtain p1 p2 t where "path M q1 (p1 @ [t])" and "path M q2 p2" and "p_io (p1 @ [t]) = p_io p" 
                     and "p_io p2 = butlast (p_io p)" and "(\<nexists>p2. path M q2 p2 \<and> p_io p2 = p_io p)" 
      using canonical_separator_path_initial(2)[OF assms(1) \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> 
            \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close> \<open>?tgt = Inr q1\<close>] 
      by meson

    have "path M q1 p1"
      using \<open>path M q1 (p1@[t])\<close> by auto
    have "p_io p1 = butlast (p_io p)"
      using \<open>p_io (p1 @ [t]) = p_io p\<close> 
      by (metis (no_types, lifting) butlast_snoc map_butlast)

    have "p_io p \<in> LS M q1" 
      using \<open>path M q1 (p1@[t])\<close> \<open>p_io (p1 @ [t]) = p_io p\<close> unfolding LS.simps by force
    moreover have "p_io p \<notin> LS M q2"
      using \<open>(\<nexists>p2. path M q2 p2 \<and> p_io p2 = p_io p)\<close> unfolding LS.simps by force
    moreover have "butlast (p_io p) \<in> LS M q1"
      using \<open>path M q1 p1\<close> \<open>p_io p1 = butlast (p_io p)\<close> unfolding LS.simps by force
    moreover have "butlast (p_io p) \<in> LS M q2"
      using \<open>path M q2 p2\<close> \<open>p_io p2 = butlast (p_io p)\<close> unfolding LS.simps by force
    ultimately show "p_io p \<in> LS M q1 - LS M q2 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
      by (simp add: map_butlast)
  qed 
  moreover show "?tgt = Inr q2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
  proof -
    assume "?tgt = Inr q2"
    obtain p1 p2 t where "path M q2 (p2 @ [t])" and "path M q1 p1" and "p_io (p2 @ [t]) = p_io p" 
                     and "p_io p1 = butlast (p_io p)" and "(\<nexists>p2. path M q1 p2 \<and> p_io p2 = p_io p)" 
      using canonical_separator_path_initial(3)[OF assms(1) \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> 
            \<open>observable M\<close> \<open>q1 \<noteq> q2\<close> \<open>?tgt = Inr q2\<close>] 
      by meson

    have "path M q2 p2"
      using \<open>path M q2 (p2@[t])\<close> by auto
    have "p_io p2 = butlast (p_io p)"
      using \<open>p_io (p2 @ [t]) = p_io p\<close> 
      by (metis (no_types, lifting) butlast_snoc map_butlast)

    have "p_io p \<in> LS M q2" 
      using \<open>path M q2 (p2@[t])\<close> \<open>p_io (p2 @ [t]) = p_io p\<close> unfolding LS.simps by force
    moreover have "p_io p \<notin> LS M q1"
      using \<open>(\<nexists>p2. path M q1 p2 \<and> p_io p2 = p_io p)\<close> unfolding LS.simps by force
    moreover have "butlast (p_io p) \<in> LS M q1"
      using \<open>path M q1 p1\<close> \<open>p_io p1 = butlast (p_io p)\<close> unfolding LS.simps by force
    moreover have "butlast (p_io p) \<in> LS M q2"
      using \<open>path M q2 p2\<close> \<open>p_io p2 = butlast (p_io p)\<close> unfolding LS.simps by force
    ultimately show "p_io p \<in> LS M q2 - LS M q1 \<and> p_io (butlast p) \<in> LS M q1 \<inter> LS M q2"
      by (simp add: map_butlast)
  qed 
  moreover have "isl ?tgt \<or> ?tgt = Inr q1 \<or> ?tgt = Inr q2"
    using canonical_separator_path_initial(4)[OF assms(1) \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>observable M\<close>  \<open>q1 \<noteq> q2\<close>] by force
  ultimately show "p_io p \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> isl (target (initial (canonical_separator M q1 q2)) p)"
             and  "p_io p \<in> LS M q1 - LS M q2 \<Longrightarrow> target (initial (canonical_separator M q1 q2)) p = Inr q1"
             and  "p_io p \<in> LS M q2 - LS M q1 \<Longrightarrow> target (initial (canonical_separator M q1 q2)) p = Inr q2"
    by blast+
qed
  

lemma canonical_separator_language_target :
  assumes "io \<in> L (canonical_separator M q1 q2)"
  and     "observable M" 
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets (canonical_separator M q1 q2) io (initial (canonical_separator M q1 q2)) = {Inr q1}"
and   "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets (canonical_separator M q1 q2) io (initial (canonical_separator M q1 q2)) = {Inr q2}"
proof -
  let ?C = "canonical_separator M q1 q2"
  obtain p where "path ?C (initial ?C) p" and "p_io p = io"
    using assms(1) by force

  show "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets (canonical_separator M q1 q2) io (initial (canonical_separator M q1 q2)) = {Inr q1}"
  proof -
    assume "io \<in> LS M q1 - LS M q2"
    then have "p_io p \<in> LS M q1 - LS M q2"
      using \<open>p_io p = io\<close> by auto
    have "Inr q1 \<in> io_targets ?C io (initial ?C)"
      using canonical_separator_path_targets_language(5)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5) \<open>p_io p \<in> LS M q1 - LS M q2\<close>]
      using \<open>path ?C (initial ?C) p\<close> unfolding io_targets.simps 
      by (metis (mono_tags, lifting) \<open>p_io p = io\<close> mem_Collect_eq)
    then show ?thesis
      by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) canonical_separator_observable observable_io_targets singletonD)
  qed

  show "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets (canonical_separator M q1 q2) io (initial (canonical_separator M q1 q2)) = {Inr q2}"
  proof -
    assume "io \<in> LS M q2 - LS M q1"
    then have "p_io p \<in> LS M q2 - LS M q1"
      using \<open>p_io p = io\<close> by auto
    have "Inr q2 \<in> io_targets ?C io (initial ?C)"
      using canonical_separator_path_targets_language(6)[OF \<open>path ?C (initial ?C) p\<close> assms(2,3,4,5) \<open>p_io p \<in> LS M q2 - LS M q1\<close>]
      using \<open>path ?C (initial ?C) p\<close> unfolding io_targets.simps 
      by (metis (mono_tags, lifting) \<open>p_io p = io\<close> mem_Collect_eq)
    then show ?thesis
      by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) canonical_separator_observable observable_io_targets singletonD)
  qed
qed


lemma canonical_separator_language_intersection :
  assumes "io \<in> LS M q1"
  and     "io \<in> LS M q2"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "io \<in> L (canonical_separator M q1 q2)" (is "io \<in> L ?C")
proof -
  let ?P = "product (from_FSM M q1) (from_FSM M q2)"

  have "io \<in> L ?P"
    using \<open>io \<in> LS M q1\<close> \<open>io \<in> LS M q2\<close> product_language[of "from_FSM M q1" "from_FSM M q2"] 
    unfolding from_FSM_language[OF \<open>q1 \<in> states M\<close>] from_FSM_language[OF \<open>q2 \<in> states M\<close>]
    by blast
  then obtain p where "path ?P (initial ?P) p" and "p_io p = io"
    by auto
  then have *: "path ?C (initial ?C) (map shift_Inl p)"
    using canonical_separator_path_shift[OF assms(3,4)] by auto
  have **: "p_io (map shift_Inl p) = io"
    using \<open>p_io p = io\<close> by (induction p; auto)
  show "io \<in> L ?C" 
    using language_state_containment[OF * **] by assumption
qed


lemma canonical_separator_deadlock :
  assumes "q1 \<in> states M"
      and "q2 \<in> states M"
    shows "deadlock_state (canonical_separator M q1 q2) (Inr q1)"
      and "deadlock_state (canonical_separator M q1 q2) (Inr q2)"
  unfolding deadlock_state.simps 
  by (metis assms(1) assms(2) canonical_separator_t_source_isl sum.disc(2))+


lemma canonical_separator_isl_deadlock :
  assumes "Inl (q1',q2') \<in> states (canonical_separator M q1 q2)"
      and "x \<in> inputs M"
      and "completely_specified M"
      and "\<not>(\<exists> t \<in> transitions (canonical_separator M q1 q2) . t_source t = Inl (q1',q2') \<and> t_input t = x \<and> isl (t_target t))"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
obtains y1 y2 where "(Inl (q1',q2'),x,y1,Inr q1) \<in> transitions (canonical_separator M q1 q2)"
                    "(Inl (q1',q2'),x,y2,Inr q2) \<in> transitions (canonical_separator M q1 q2)"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  have "(q1',q2') \<in> states ?P"
    using assms(1) unfolding canonical_separator_simps[OF assms(5,6)] by fastforce
  then have "(q1',q2') \<in> states ?P"
    using reachable_state_is_state by force
  then have "q1' \<in> states M" and "q2' \<in> states M"
    using assms(5,6) by auto
  then obtain y1 y2 where "y1 \<in> h_out M (q1',x)" and "y2 \<in> h_out M (q2',x)"
    by (metis (no_types, lifting) assms(2,3) h_out.simps completely_specified_alt_def mem_Collect_eq) 
  moreover have "h_out M (q1',x) \<inter> h_out M (q2',x) = {}"
  proof (rule ccontr)
    assume "h_out M (q1', x) \<inter> h_out M (q2', x) \<noteq> {}"
    then obtain y where "y \<in> h_out M (q1', x) \<inter> h_out M (q2', x)" by blast
    then obtain q1'' q2'' where "((q1',q2'),x,y,(q1'',q2'')) \<in> transitions ?P"
      unfolding product_transitions_def h_out.simps using assms(5,6) by auto
    then have "(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> transitions ?C"
      using \<open>(q1',q2') \<in> states ?P\<close> unfolding canonical_separator_transitions_def[OF assms(5,6)] h_out.simps by blast
    then show "False"
      using assms(4) by auto
  qed
  ultimately have "y1 \<in> h_out M (q1',x) - h_out M (q2',x)"
             and  "y2 \<in> h_out M (q2',x) - h_out M (q1',x)"
    by blast+

  let ?t1 = "(Inl (q1',q2'),x,y1,Inr q1)"
  let ?t2 = "(Inl (q1',q2'),x,y2,Inr q2)"

  have "?t1 \<in> distinguishing_transitions_left M q1 q2"
    using \<open>(q1',q2') \<in> states ?P\<close> \<open>y1 \<in> h_out M (q1',x) - h_out M (q2',x)\<close>
    unfolding distinguishing_transitions_left_def by auto
  then have "?t1 \<in> transitions (canonical_separator M q1 q2)"
    unfolding canonical_separator_transitions_def[OF assms(5,6)] by blast

  have "?t2 \<in> distinguishing_transitions_right M q1 q2"
    using \<open>(q1',q2') \<in> states ?P\<close> \<open>y2 \<in> h_out M (q2',x) - h_out M (q1',x)\<close>
    unfolding distinguishing_transitions_right_def by auto
  then have "?t2 \<in> transitions (canonical_separator M q1 q2)"
    unfolding canonical_separator_transitions_def[OF assms(5,6)] by blast

  show ?thesis 
    using that \<open>?t1 \<in> transitions (canonical_separator M q1 q2)\<close> \<open>?t2 \<in> transitions (canonical_separator M q1 q2)\<close> by blast
qed


lemma canonical_separator_deadlocks :
  assumes "q1 \<in> states M" and "q2 \<in> states M"
shows "deadlock_state (canonical_separator M q1 q2) (Inr q1)"
and   "deadlock_state (canonical_separator M q1 q2) (Inr q2)"
  using canonical_separator_t_source_isl[OF _ assms]
  unfolding deadlock_state.simps by force+


lemma state_separator_from_canonical_separator_language_target :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "io \<in> L A"
  and     "observable M" 
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets A io (initial A) = {Inr q1}"
and   "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets A io (initial A) = {Inr q2}"
and   "io \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}"
proof -
  have "observable A"
    using state_separator_from_canonical_separator_observable[OF assms(1,3,4,5)] by assumption

  let ?C = "canonical_separator M q1 q2"

  obtain p where "path A (initial A) p" and "p_io p = io"
    using assms(2) by force
  then have "path ?C (initial ?C) p"
    using submachine_path_initial[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)]] by auto
  then have "io \<in> L ?C"
    using \<open>p_io p = io\<close> by auto

  show "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets A io (initial A) = {Inr q1}"
  proof -
    assume "io \<in> LS M q1 - LS M q2"

    have "target (initial A) p = Inr q1"
      using submachine_path_initial[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)] \<open>path A (initial A) p\<close>] 
            canonical_separator_language_target(1)[OF \<open>io \<in> L ?C\<close> assms(3,4,5,6) \<open>io \<in> LS M q1 - LS M q2\<close>] 
            \<open>p_io p = io\<close>
      unfolding io_targets.simps is_state_separator_from_canonical_separator_initial[OF assms(1,4,5)] 
                canonical_separator_simps product_simps from_FSM_simps[OF assms(4)] from_FSM_simps[OF assms(5)]
      using assms(4) assms(5) canonical_separator_initial by fastforce
    then have "Inr q1 \<in> io_targets A io (initial A)"
      using \<open>path A (initial A) p\<close> \<open>p_io p = io\<close> unfolding io_targets.simps
      by (metis (mono_tags, lifting) mem_Collect_eq)  
    then show "io_targets A io (initial A) = {Inr q1}"
      using observable_io_targets[OF \<open>observable A\<close> \<open>io \<in> L A\<close>]
      by (metis singletonD)   
  qed

  show "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets A io (initial A) = {Inr q2}"
  proof -
    assume "io \<in> LS M q2 - LS M q1"

    have "target (initial A) p = Inr q2"
      using submachine_path_initial[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)] \<open>path A (initial A) p\<close>] 
            canonical_separator_language_target(2)[OF \<open>io \<in> L ?C\<close> assms(3,4,5,6) \<open>io \<in> LS M q2 - LS M q1\<close>] 
            \<open>p_io p = io\<close>
      unfolding io_targets.simps is_state_separator_from_canonical_separator_initial[OF assms(1,4,5)] 
                canonical_separator_simps product_simps from_FSM_simps[OF assms(4)] from_FSM_simps[OF assms(5)]
      using assms(4) assms(5) canonical_separator_initial by fastforce
    then have "Inr q2 \<in> io_targets A io (initial A)"
      using \<open>path A (initial A) p\<close> \<open>p_io p = io\<close> unfolding io_targets.simps
      by (metis (mono_tags, lifting) mem_Collect_eq)  
    then show "io_targets A io (initial A) = {Inr q2}"
      using observable_io_targets[OF \<open>observable A\<close> \<open>io \<in> L A\<close>]
      by (metis singletonD)   
  qed

  show "io \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}"
  proof -
    let ?P = "product (from_FSM M q1) (from_FSM M q2)"

    assume "io \<in> LS M q1 \<inter> LS M q2"

    have"\<And> q . q \<in> io_targets A io (initial A) \<Longrightarrow> q \<notin> {Inr q1, Inr q2}"
    proof -
      fix q assume "q \<in> io_targets A io (initial A)"
      then obtain p where "q = target (initial A) p" and "path A (initial A) p" and "p_io p = io"
        by auto
      then have "path ?C (initial ?C) p"
        using submachine_path_initial[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)]] by auto
      then have "isl (target (initial ?C) p)"
        using canonical_separator_path_targets_language(4)[OF _ \<open>observable M\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close>  \<open>q1 \<noteq> q2\<close>]
        using \<open>p_io p = io\<close> \<open>io \<in> LS M q1 \<inter> LS M q2\<close> by auto
      then show "q \<notin> {Inr q1, Inr q2}"
        using \<open>q = target (initial A) p\<close> 
        unfolding is_state_separator_from_canonical_separator_initial[OF assms(1,4,5)]
        unfolding canonical_separator_simps product_simps from_FSM_simps by auto
    qed

    then show "io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}"
      by blast
  qed
qed


lemma state_separator_language_intersections_nonempty :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "\<exists> io . io \<in> (L A \<inter> LS M q1) - LS M q2" and "\<exists> io . io \<in> (L A \<inter> LS M q2) - LS M q1"
proof -
  have "Inr q1 \<in> reachable_states A"
    using is_state_separator_from_canonical_separator_simps(6)[OF assms(1)] by assumption
  then obtain p where "path A (initial A) p" and "target (initial A) p = Inr q1"
    unfolding reachable_states_def by auto 
  then have "p_io p \<in> LS M q1 - LS M q2"
    using canonical_separator_maximal_path_distinguishes_left[OF assms(1) _ _ assms(2,3,4,5)] by blast
  moreover have "p_io p \<in> L A"
    using \<open>path A (initial A) p\<close> by auto
  ultimately show "\<exists> io . io \<in> (L A \<inter> LS M q1) - LS M q2" by blast

  have "Inr q2 \<in> reachable_states A"
    using is_state_separator_from_canonical_separator_simps(7)[OF assms(1)] by assumption
  then obtain p' where "path A (initial A) p'" and "target (initial A) p' = Inr q2"
    unfolding reachable_states_def by auto 
  then have "p_io p' \<in> LS M q2 - LS M q1"
    using canonical_separator_maximal_path_distinguishes_right[OF assms(1) _ _ assms(2,3,4,5)] by blast
  moreover have "p_io p' \<in> L A"
    using \<open>path A (initial A) p'\<close> by auto
  ultimately show "\<exists> io . io \<in> (L A \<inter> LS M q2) - LS M q1" by blast
qed


lemma state_separator_language_inclusion :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "L A \<subseteq> LS M q1 \<union> LS M q2"
  using canonical_separator_language[OF assms(2,3)]
  using submachine_language[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)]] 
  unfolding from_FSM_language[OF assms(2)] from_FSM_language[OF assms(3)] by blast


lemma state_separator_from_canonical_separator_targets_left_inclusion :
  assumes "observable T" 
  and     "observable M"
  and     "t1 \<in> states T"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "(inputs T) = (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS M q1"
  and     "q1 \<noteq> q2"
shows "target (initial A) p \<noteq> Inr q2"
and   "target (initial A) p = Inr q1 \<or> isl (target (initial A) p)"
proof -
  let ?C = "canonical_separator M q1 q2"
  have c_path: "\<And> p . path A (initial A) p \<Longrightarrow> path ?C (initial ?C) p"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] submachine_path_initial by metis
  have "path ?C (initial ?C) p"
    using assms(8) c_path by auto

  show "target (initial A) p \<noteq> Inr q2"
  proof 
    assume "target (initial A) p = Inr q2"
    then have "target (initial ?C) p = Inr q2"
      using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] by auto

    have "(\<nexists>p1. path M q1 p1 \<and> p_io p1 = p_io p)"
      using canonical_separator_path_initial(3)[OF \<open>path ?C (initial ?C) p\<close> assms(4,5,2,10) \<open>target (initial ?C) p = Inr q2\<close>] by blast
    then have "p_io p \<notin> LS M q1"
      unfolding LS.simps by force
    then show "False"
      using \<open>p_io p \<in> LS M q1\<close> by blast
  qed
  then have "target (initial ?C) p \<noteq> Inr q2"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] unfolding is_submachine.simps by simp
  then have "target (initial ?C) p = Inr q1 \<or> isl (target (initial ?C) p)"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis unfolding canonical_separator_simps[OF assms(4,5)] by simp
  next
    case (snoc ys y)
    then show ?thesis
      by (metis \<open>path (canonical_separator M q1 q2) (FSM.initial (canonical_separator M q1 q2)) p\<close> \<open>target (FSM.initial (canonical_separator M q1 q2)) p \<noteq> Inr q2\<close> assms(10) assms(2) assms(4) assms(5) canonical_separator_path_initial(4) isl_def)        
  qed
  then show "target (initial A) p = Inr q1 \<or> isl (target (initial A) p)"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] unfolding is_submachine.simps by simp
qed


lemma state_separator_from_canonical_separator_targets_right_inclusion :
  assumes "observable T" 
  and     "observable M"
  and     "t1 \<in> states T"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "(inputs T) = (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS M q2"
  and     "q1 \<noteq> q2"
shows "target (initial A) p \<noteq> Inr q1"
and   "target (initial A) p = Inr q2 \<or> isl (target (initial A) p)"
proof -
  let ?C = "canonical_separator M q1 q2"
  have c_path: "\<And> p . path A (initial A) p \<Longrightarrow> path ?C (initial ?C) p"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] submachine_path_initial by metis
  have "path ?C (initial ?C) p"
    using assms(8) c_path by auto

  show "target (initial A) p \<noteq> Inr q1"
  proof 
    assume "target (initial A) p = Inr q1"
    then have "target (initial ?C) p = Inr q1"
      using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] by auto

    have "(\<nexists>p1. path M q2 p1 \<and> p_io p1 = p_io p)"
      using canonical_separator_path_initial(2)[OF \<open>path ?C (initial ?C) p\<close> assms(4,5,2,10) \<open>target (initial ?C) p = Inr q1\<close> ] by blast
    then have "p_io p \<notin> LS M q2"
      unfolding LS.simps by force
    then show "False"
      using \<open>p_io p \<in> LS M q2\<close> by blast
  qed

  then have "target (initial ?C) p \<noteq> Inr q1"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] unfolding is_submachine.simps by simp
  then have "target (initial ?C) p = Inr q2 \<or> isl (target (initial ?C) p)"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis unfolding canonical_separator_simps[OF assms(4,5)] by simp
  next
    case (snoc ys y)
    then show ?thesis
      by (metis \<open>path (canonical_separator M q1 q2) (FSM.initial (canonical_separator M q1 q2)) p\<close> \<open>target (FSM.initial (canonical_separator M q1 q2)) p \<noteq> Inr q1\<close> assms(10) assms(2) assms(4) assms(5) canonical_separator_path_initial(4) isl_def)
  qed
  then show "target (initial A) p = Inr q2 \<or> isl (target (initial A) p)"
    using is_state_separator_from_canonical_separator_simps(1)[OF assms(6)] unfolding is_submachine.simps by simp
qed




subsection \<open>Calculating State Separators\<close>

subsubsection \<open>Sufficient Condition to Induce a State Separator\<close>

definition state_separator_from_input_choices :: "('a,'b,'c) fsm \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> 'b) list \<Rightarrow> (('a \<times> 'a) + 'a, 'b, 'c) fsm" where
  "state_separator_from_input_choices M CSep q1 q2 cs = 
    (let css  = set cs;
         cssQ = (set (map fst cs)) \<union> {Inr q1, Inr q2};
         S0   = filter_states CSep (\<lambda> q . q \<in> cssQ);
         S1   = filter_transitions S0 (\<lambda> t . (t_source t, t_input t) \<in> css)          
    in S1)"




lemma state_separator_from_input_choices_simps :      
  assumes "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
shows
  "initial (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = Inl (q1,q2)"
  "states (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = (set (map fst cs)) \<union> {Inr q1, Inr q2}"
  "inputs (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = inputs M"
  "outputs (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = outputs M"
  "transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = 
    {t \<in> (transitions (canonical_separator M q1 q2)) . \<exists> q1' q2' x . (Inl (q1',q2'),x) \<in> set cs \<and> t_source t = Inl (q1',q2') \<and> t_input t = x \<and> t_target t \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}}"
proof -
  let ?SS = "(state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
  let ?S0 = "filter_states (canonical_separator M q1 q2) (\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})"

  have "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))"
    unfolding canonical_separator_simps[OF assms(1,2)]
    using assms(4) by simp

  have "states ?S0 = (set (map fst cs)) \<union> {Inr q1, Inr q2}"
  proof -
    have "\<And> qq . qq \<in> states ?S0 \<Longrightarrow> qq \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}"
      unfolding filter_states_simps[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", 
                                   OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close> ]
      by fastforce
    moreover have "\<And> qq . qq \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2} \<Longrightarrow> qq \<in> states ?S0"
    proof -
      fix qq assume "qq \<in> set (map fst cs) \<union> {Inr q1, Inr q2}"
      then consider (a) "qq \<in> set (map fst cs)" | (b) "qq \<in> {Inr q1, Inr q2}"
        by blast
      then show "qq \<in> states ?S0" proof cases
        case a
        then obtain q1' q2' where "qq = Inl (q1',q2')"
          using assms(5) by (metis old.prod.exhaust) 
        then show ?thesis 
          using a assms(3)[of qq]  
          unfolding filter_states_simps[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close> ]
                canonical_separator_simps[OF assms(1,2)] by force
      next
        case b
        then show ?thesis using assms(3)  
          unfolding filter_states_simps[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close> ]
                canonical_separator_simps[OF assms(1,2)] by force
      qed 
    qed
      
    ultimately show ?thesis by blast
  qed
    

  show "initial (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = Inl (q1,q2)"
       "states (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = (set (map fst cs)) \<union> {Inr q1, Inr q2}"
       "inputs (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = inputs M"
       "outputs (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = outputs M"
    unfolding canonical_separator_simps[OF assms(1,2)] 
              filter_transitions_simps 
              state_separator_from_input_choices_def 
              Let_def 
              filter_states_simps(1,3,4,5)[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close> ] 
              \<open>states ?S0 = (set (map fst cs)) \<union> {Inr q1, Inr q2}\<close> 
    by simp+

  have alt_def_shared: "{t \<in> {t \<in> FSM.transitions (canonical_separator M q1 q2). t_source t \<in> set (map fst cs) \<union> {Inr q1, Inr q2} \<and> t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}}. (t_source t, t_input t) \<in> set cs}
                        = {t \<in> FSM.transitions (canonical_separator M q1 q2). \<exists> q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and> t_source t = Inl (q1', q2') \<and> t_input t = x \<and> t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}}" 
      (is "?ts1 = ?ts2")
  proof -
    have "\<And> t . t \<in> ?ts1 \<Longrightarrow> t \<in> ?ts2"
    proof -
      fix t assume "t \<in> ?ts1"
      then have "t \<in> FSM.transitions (canonical_separator M q1 q2)" and "t_source t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}" and "t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}" and "(t_source t, t_input t) \<in> set cs"
        by blast+
      
      have "t_source t \<in> set (map fst cs)"
        using \<open>t \<in> FSM.transitions (canonical_separator M q1 q2)\<close> \<open>t_source t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}\<close>
        using canonical_separator_deadlocks[OF assms(1,2)]
        by fastforce
      then obtain q1' q2' where "t_source t = Inl (q1',q2')"
        using assms(5) by (metis old.prod.exhaust) 
      then have "\<exists>q1' q2' x. (Inl (q1', q2'), x) \<in> set cs \<and> t_source t = Inl (q1', q2') \<and> t_input t = x"
        using \<open>(t_source t, t_input t) \<in> set cs\<close> by auto
        
      then show "t \<in> ?ts2"
        using \<open>t \<in> FSM.transitions (canonical_separator M q1 q2)\<close> \<open>t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}\<close>
        by simp
    qed
    moreover have "\<And> t . t \<in> ?ts2 \<Longrightarrow> t \<in> ?ts1"
      by force
    ultimately show ?thesis by blast
  qed

  show "transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = 
    {t \<in> (transitions (canonical_separator M q1 q2)) . \<exists> q1' q2' x . (Inl (q1',q2'),x) \<in> set cs \<and> t_source t = Inl (q1',q2') \<and> t_input t = x \<and> t_target t \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}}"
    unfolding canonical_separator_simps(1,2,3,4)[OF assms(1,2)] 
    unfolding state_separator_from_input_choices_def Let_def
    unfolding filter_transitions_simps
    unfolding filter_states_simps[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close> ]
    unfolding alt_def_shared by blast
qed


lemma state_separator_from_input_choices_submachine :
  assumes "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
    shows "is_submachine (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) (canonical_separator M q1 q2)"
proof -
  have "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))"
    unfolding canonical_separator_simps[OF assms(1,2)]
    using assms(4) by simp

  show ?thesis
    unfolding state_separator_from_input_choices_def Let_def
    using submachine_transitive[OF filter_states_submachine[of "(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2})", OF \<open>(\<lambda> q . q \<in> (set (map fst cs)) \<union> {Inr q1, Inr q2}) (initial (canonical_separator M q1 q2))\<close>]
                                   filter_transitions_submachine[of "filter_states (canonical_separator M q1 q2) (\<lambda>q. q \<in> set (map fst cs) \<union> {Inr q1, Inr q2})" "(\<lambda>t. (t_source t, t_input t) \<in> set cs)"]]
    by assumption
qed


lemma state_separator_from_input_choices_single_input :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
    shows "single_input (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
proof -
  have "\<And> t1 t2 . t1 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) \<Longrightarrow>
          t2 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) \<Longrightarrow>
             t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2"
  proof -
    fix t1 t2
    assume "t1 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
       and "t2 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
       and "t_source t1 = t_source t2"

    obtain q1' q2' where "(Inl (q1',q2'),t_input t1) \<in> set cs"
                     and "t_source t1 = Inl (q1',q2')"
      using \<open>t1 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)\<close>
      using state_separator_from_input_choices_simps(5)[OF assms(2,3,4,5,6)] by fastforce

    obtain q1'' q2'' where "(Inl (q1'',q2''),t_input t2) \<in> set cs"
                     and "t_source t2 = Inl (q1'',q2'')"
      using \<open>t2 \<in> FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)\<close>
      using state_separator_from_input_choices_simps(5)[OF assms(2,3,4,5,6)] by fastforce

    have "(Inl (q1',q2'),t_input t2) \<in> set cs"
      using \<open>(Inl (q1'',q2''),t_input t2) \<in> set cs\<close> \<open>t_source t1 = Inl (q1',q2')\<close> \<open>t_source t2 = Inl (q1'',q2'')\<close> \<open>t_source t1 = t_source t2\<close> 
      by simp
    then show "t_input t1 = t_input t2"
      using \<open>(Inl (q1',q2'),t_input t1) \<in> set cs\<close> \<open>distinct (map fst cs)\<close>
      by (meson eq_key_imp_eq_value) 
  qed
  then show ?thesis
    by fastforce
qed


lemma state_separator_from_input_choices_transition_list : 
  assumes "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "t \<in> transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
    shows "(t_source t, t_input t) \<in> set cs"
using state_separator_from_input_choices_simps(5)[OF assms(1,2,3,4,5)] assms(6) by auto


lemma state_separator_from_input_choices_transition_target :
  assumes "t \<in> transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
    shows "t \<in> transitions (canonical_separator M q1 q2) \<or> t_target t \<in> {Inr q1, Inr q2}"
  using state_separator_from_input_choices_simps(5)[OF assms(2-6)] assms(1) by fastforce


lemma state_separator_from_input_choices_acyclic_paths' :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs 
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
      and "path (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) q' p"
      and "target q' p = q'"
      and "p \<noteq> []"
shows "False"
proof -

  let ?S = "(state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"

  from \<open>p \<noteq> []\<close> obtain p' t' where "p = t'#p'"
    using list.exhaust by blast
  then have "path ?S q' (p@[t'])" 
    using assms(8,9) by fastforce

  define f :: "(('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a)) \<Rightarrow> nat"
    where f_def: "f = (\<lambda> t . the (find_index (\<lambda> qx . (fst qx) = t_source t \<and> snd qx = t_input t) cs))"
  
  have f_prop: "\<And> t . t \<in> set (p@[t']) \<Longrightarrow> (f t < length cs) 
                                      \<and> (\<lambda>(q, x). (q, x)) (cs ! (f t)) = (t_source t,t_input t)
                                      \<and> (\<forall> j < f t . (fst (cs ! j)) \<noteq> t_source t)"
  proof -
    fix t assume "t \<in> set (p@[t'])"
    then have "t \<in> set p" using \<open>p = t'#p'\<close> by auto
    then have "t \<in> transitions ?S" 
      using assms(8)
      by (meson path_transitions subsetD) 
    then have "(t_source t, t_input t) \<in> set cs"
      using state_separator_from_input_choices_transition_list[OF assms(2,3,4,5,6)]
      by blast 
    then have "\<exists> qx \<in> set cs . (\<lambda> qx . (fst qx) = t_source t \<and> snd qx = t_input t) qx"
      by force
    then have "find_index (\<lambda> qx . (fst qx) = t_source t \<and> snd qx = t_input t) cs \<noteq> None"
      by (simp add: find_index_exhaustive) 
    then obtain i where *: "find_index (\<lambda> qx . (fst qx) = t_source t \<and> snd qx = t_input t) cs = Some i"
      by auto

    have **: "\<And> j . j < i \<Longrightarrow> (fst (cs ! j)) = t_source t \<Longrightarrow> cs ! i = cs ! j"
      using assms(1)
      using nth_eq_iff_index_eq  find_index_index[OF *]
      by (metis (mono_tags, lifting) Suc_lessD length_map less_trans_Suc nth_map)

    have "f t < length cs"
      unfolding f_def using find_index_index(1)[OF *] unfolding * by simp
    moreover have "(\<lambda>(q, x). (q, x)) (cs ! (f t)) = (t_source t, t_input t)"
      unfolding f_def using find_index_index(2)[OF *]
      by (metis "*" case_prod_Pair_iden option.sel prod.collapse)
    moreover have "\<forall> j < f t . (fst (cs ! j)) \<noteq> t_source t"
      unfolding f_def using find_index_index(3)[OF *] unfolding *  
      using assms(1) **
      by (metis (no_types, lifting) "*" \<open>\<exists>qx\<in>set cs. fst qx = t_source t \<and> snd qx = t_input t\<close> eq_key_imp_eq_value find_index_index(1) nth_mem option.sel prod.collapse)
    
    ultimately show "(f t < length cs)
                      \<and> (\<lambda>(q, x). (q, x)) (cs ! (f t)) = (t_source t,t_input t)
                      \<and> (\<forall> j < f t . (fst (cs ! j)) \<noteq> t_source t)" by simp
  qed

  have *: "\<And> i . Suc i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
  proof -
    fix i assume "Suc i < length (p@[t'])"
    then have "(p@[t']) ! i \<in> set (p@[t'])" and "(p@[t']) ! (Suc i) \<in> set (p@[t'])"
      using Suc_lessD nth_mem by blast+
    then have "(p@[t']) ! i \<in> transitions ?S" and "(p@[t']) ! Suc i \<in> transitions ?S" 
      using \<open>path ?S q' (p@[t'])\<close>
      by (meson path_transitions subsetD)+
    then have "(p @ [t']) ! i \<in> FSM.transitions (canonical_separator M q1 q2) \<or> t_target ((p @ [t']) ! i) \<in> {Inr q1, Inr q2}" 
      using state_separator_from_input_choices_transition_target[OF _ assms(2-6)] by blast
    
    have "f ((p@[t']) ! i) < length cs"
    and  "(\<lambda>(q, x). (q, x)) (cs ! (f ((p@[t']) ! i))) = (t_source ((p@[t']) ! i), t_input ((p@[t']) ! i))"
    and  "(\<forall>j<f ((p@[t']) ! i). (fst (cs ! j)) \<noteq> t_source ((p@[t']) ! i))"
      using f_prop[OF \<open>(p@[t']) ! i \<in> set (p@[t'])\<close>] by auto

    have "f ((p@[t']) ! Suc i) < length cs"
    and  "(\<lambda>(q, x). (q, x)) (cs ! (f ((p@[t']) ! Suc i))) = (t_source ((p@[t']) ! Suc i), t_input ((p@[t']) ! Suc i))"
    and  "(\<forall>j<f ((p@[t']) ! Suc i). (fst (cs ! j)) \<noteq> t_source ((p@[t']) ! Suc i))"
      using f_prop[OF \<open>(p@[t']) ! Suc i \<in> set (p@[t'])\<close>] by auto

    have "t_source ((p @ [t']) ! i) = (fst (cs ! f ((p @ [t']) ! i)))" and "t_input ((p @ [t']) ! i) = snd (cs ! f ((p @ [t']) ! i))"
       using f_prop[OF \<open>(p@[t']) ! i \<in> set (p@[t'])\<close>]
       by (simp add: prod.case_eq_if)+ 

    have "t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)"
      using \<open>Suc i < length (p@[t'])\<close> \<open>path ?S q' (p@[t'])\<close>
      by (simp add: path_source_target_index) 
    then have "t_target ((p@[t']) ! i) \<notin> {Inr q1, Inr q2}"
      using state_separator_from_input_choices_transition_list[OF assms(2,3,4,5,6) \<open>(p@[t']) ! Suc i \<in> transitions ?S\<close>] assms(6) by force
    then have "t_target ((p @ [t']) ! i) \<in> set (map fst (take (f ((p @ [t']) ! i)) cs))"
      using assms(7)[OF \<open>f ((p@[t']) ! i) < length cs\<close> _ \<open>t_source ((p @ [t']) ! i) = (fst (cs ! f ((p @ [t']) ! i)))\<close> \<open>t_input ((p @ [t']) ! i) = snd (cs ! f ((p @ [t']) ! i))\<close>] 
      using \<open>(p @ [t']) ! i \<in> FSM.transitions (canonical_separator M q1 q2) \<or> t_target ((p @ [t']) ! i) \<in> {Inr q1, Inr q2}\<close> by blast
    then have "(\<exists>qx'\<in>set (take (f ((p@[t']) ! i)) cs). (fst qx') = t_target ((p@[t']) ! i))" 
      by force 
    then obtain j where "(fst (cs ! j)) = t_source ((p@[t']) ! Suc i)" and "j < f ((p@[t']) ! i)" 
      unfolding \<open>t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)\<close>
      by (metis (no_types, lifting) \<open>f ((p@[t']) ! i) < length cs\<close> in_set_conv_nth leD length_take min_def_raw nth_take)     
    then show "f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
      using \<open>(\<forall>j<f ((p@[t']) ! Suc i). (fst (cs ! j)) \<noteq> t_source ((p@[t']) ! Suc i))\<close>
      using leI le_less_trans by blast 
  qed

  have "\<And> i j . j < i \<Longrightarrow> i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! j) > f ((p@[t']) ! i)"
    using list_index_fun_gt[of "p@[t']" f] * by blast
  then have "f t' < f t'"
    unfolding \<open>p = t'#p'\<close> by fastforce 
  then show "False"
    by auto
qed


lemma state_separator_from_input_choices_acyclic_paths :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs 
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
      and "path (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) q' p"
shows "distinct (visited_states q' p)"
proof (rule ccontr)
  assume "\<not> distinct (visited_states q' p)"
  
  obtain i j where p1:"take j (drop i p) \<noteq> []"
               and p2:"target (target q' (take i p)) (take j (drop i p)) = (target q' (take i p))"
               and p3:"path (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) (target q' (take i p)) (take j (drop i p))"
    using cycle_from_cyclic_path[OF assms(8) \<open>\<not> distinct (visited_states q' p)\<close>] by blast
  
  show "False"
    using state_separator_from_input_choices_acyclic_paths'[OF assms(1-7) p3 p2 p1] by blast
qed


lemma state_separator_from_input_choices_acyclic :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs 
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2)
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
    shows "acyclic (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
  unfolding acyclic.simps using state_separator_from_input_choices_acyclic_paths[OF assms] by blast


lemma state_separator_from_input_choices_target :
  assumes "\<And> i t . i < length cs
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
      and "t \<in> FSM.transitions (canonical_separator M q1 q2)"
      and "\<exists> q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and> t_source t = Inl (q1', q2') \<and> t_input t = x" 
    shows "t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}" 
proof -
  from assms(3) obtain q1' q2' x where "(Inl (q1', q2'), x)\<in>set cs" and "t_source t = Inl (q1', q2')" and "t_input t = x"
    by auto
  then obtain i where "i < length cs" and "t_source t = (fst (cs ! i))" and "t_input  t = snd (cs ! i)"
    by (metis fst_conv in_set_conv_nth snd_conv)
  then have "t_target t \<in> set (map fst (take i cs)) \<union> {Inr q1, Inr q2}" using assms(1)[OF _ assms(2)] by blast
  then consider "t_target t \<in> set (map fst (take i cs))" | "t_target t \<in> {Inr q1, Inr q2}" by blast
  then show ?thesis proof cases
    case 1 
    then have "t_target t \<in> set (map fst cs)" 
      by (metis in_set_takeD take_map)
    then show ?thesis by blast
  next
    case 2
    then show ?thesis by auto
  qed 
qed


lemma state_separator_from_input_choices_transitions_alt_def :
  assumes "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
  shows "transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) = 
    {t \<in> (transitions (canonical_separator M q1 q2)) . \<exists> q1' q2' x . (Inl (q1',q2'),x) \<in> set cs \<and> t_source t = Inl (q1',q2') \<and> t_input t = x}"
proof -
  have "FSM.transitions (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) =
    {t \<in> FSM.transitions (canonical_separator M q1 q2).
     \<exists> q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and>
        t_source t = Inl (q1', q2') \<and>
        t_input t = x \<and> t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}}"
    using state_separator_from_input_choices_simps(5)[OF assms(1,2,3,4,5)] by blast

  moreover have "\<And> t . t \<in> FSM.transitions (canonical_separator M q1 q2) \<Longrightarrow>  \<exists> q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and> t_source t = Inl (q1', q2') \<and> t_input t = x \<Longrightarrow> t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}"
    using state_separator_from_input_choices_target[OF assms(6)] by blast

  ultimately show ?thesis 
    by fast
qed


lemma state_separator_from_input_choices_deadlock :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
      
    shows "\<And> qq . qq \<in> states (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) \<Longrightarrow> deadlock_state (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs) qq \<Longrightarrow> qq \<in> {Inr q1, Inr q2} \<or> (\<exists> q1' q2' x . qq = Inl (q1',q2') \<and> x \<in> inputs M \<and> (h_out M (q1',x) = {} \<and> h_out M (q2',x) = {}))"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?S = "(state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
 
  fix qq assume "qq \<in> states ?S" and "deadlock_state ?S qq"

  then consider (a) "qq \<in> (set (map fst cs))" | (b) "qq \<in> {Inr q1, Inr q2}"
    using state_separator_from_input_choices_simps(2)[OF assms(2,3,4,5,6)] by blast
  then show "qq \<in> {Inr q1, Inr q2} \<or> (\<exists> q1' q2' x . qq = Inl (q1',q2') \<and> x \<in> inputs M \<and> (h_out M (q1',x) = {} \<and> h_out M (q2',x) = {}))"
  proof cases
    case a
    then obtain q1' q2' x where "(Inl (q1',q2'),x) \<in> set cs" and  "qq = Inl (q1',q2')" using assms(6) by fastforce
    then have "Inl (q1',q2') \<in> states (canonical_separator M q1 q2)" and "x \<in> inputs M" using assms(4) by blast+
    then have "(q1', q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))"
      using canonical_separator_simps(2)[OF assms(2,3)] by fastforce

    have "h_out M (q1',x) = {} \<and> h_out M (q2',x) = {}"
    proof (rule ccontr)
      assume "\<not> (h_out M (q1', x) = {} \<and> h_out M (q2', x) = {})"
      then consider (a1) "\<exists> y \<in> (h_out M (q1', x) \<inter> h_out M (q2', x)) . True" | 
                    (a2) "\<exists> y \<in> (h_out M (q1', x) - h_out M (q2', x)) . True" |
                    (a3) "\<exists> y \<in> (h_out M (q2', x) - h_out M (q1', x)) . True"
        by blast
      then show "False" proof cases
        case a1
        then obtain y q1'' q2''  where "(y,q1'') \<in> h M (q1',x)" and "(y,q2'') \<in> h M (q2',x)" by auto
        then have "((q1',q2'),x,y,(q1'',q2'')) \<in> transitions (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
          unfolding product_transitions_def h.simps using assms(2,3) by auto
        then have "(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> transitions ?C"  
          using \<open>(q1', q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))\<close>
                canonical_separator_transitions_def[OF assms(2,3)]  by fast
        
        then have "(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> {t \<in> FSM.transitions (canonical_separator M q1 q2).
                                                             \<exists>q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and>
                                                                t_source t = Inl (q1', q2') \<and>
                                                                t_input t = x \<and> t_target t \<in> set (map fst cs) \<union> {Inr q1, Inr q2}}"
          using state_separator_from_input_choices_target[OF assms(7) \<open>(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> transitions ?C\<close>]
          using \<open>(Inl (q1', q2'), x) \<in> set cs\<close> by force 

        then have "(Inl (q1',q2'), x, y, Inl (q1'',q2'')) \<in> transitions ?S" 
          using state_separator_from_input_choices_simps(5)[OF assms(2,3,4,5,6)] by fastforce
        then show "False" 
          using \<open>deadlock_state ?S qq\<close> unfolding \<open>qq = Inl (q1',q2')\<close> by auto
      next
        case a2
        then obtain y where "y \<in> (h_out M (q1', x) - h_out M (q2', x))" unfolding h_out.simps by blast
        then have "(\<exists>q'. (q1', x, y, q') \<in> FSM.transitions M) \<and> (\<nexists>q'. (q2', x, y, q') \<in> FSM.transitions M)" unfolding h_out.simps by blast
        then have "(Inl (q1',q2'), x, y, Inr q1) \<in> distinguishing_transitions_left M q1 q2"
          unfolding distinguishing_transitions_left_def h.simps
          using \<open>(q1', q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))\<close> by blast
        then have "(Inl (q1',q2'), x, y, Inr q1) \<in> transitions ?C"
          unfolding canonical_separator_transitions_def[OF assms(2,3)] by blast
        moreover have "\<exists>q1'' q2'' x' . (Inl (q1'', q2''), x')\<in>set cs \<and> t_source (Inl (q1',q2'), x, y, Inr q1) = Inl (q1'', q2'') \<and> t_input (Inl (q1',q2'), x, y, Inr q1) = x'"
          using \<open>(Inl (q1', q2'), x) \<in> set cs\<close> by auto
        ultimately have "(Inl (q1',q2'), x, y, Inr q1) \<in> transitions ?S" 
          using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] by blast
        then show "False" 
          using \<open>deadlock_state ?S qq\<close> unfolding \<open>qq = Inl (q1',q2')\<close> by auto
      next
        case a3
        then obtain y where "y \<in> (h_out M (q2', x) - h_out M (q1', x))" unfolding h_out.simps by blast
        then have "\<not>(\<exists>q'. (q1', x, y, q') \<in> FSM.transitions M) \<and> (\<exists>q'. (q2', x, y, q') \<in> FSM.transitions M)" unfolding h_out.simps by blast
        then have "(Inl (q1',q2'), x, y, Inr q2) \<in> distinguishing_transitions_right M q1 q2"
          unfolding distinguishing_transitions_right_def h.simps
          using \<open>(q1', q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))\<close> by blast
        then have "(Inl (q1',q2'), x, y, Inr q2) \<in> transitions ?C"
          unfolding canonical_separator_transitions_def[OF assms(2,3)] by blast
        moreover have "\<exists>q1'' q2'' x' . (Inl (q1'', q2''), x')\<in>set cs \<and> t_source (Inl (q1',q2'), x, y, Inr q2) = Inl (q1'', q2'') \<and> t_input (Inl (q1',q2'), x, y, Inr q2) = x'"
          using \<open>(Inl (q1', q2'), x) \<in> set cs\<close> by auto
        ultimately have "(Inl (q1',q2'), x, y, Inr q2) \<in> transitions ?S" 
          using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] by blast
        then show "False" 
          using \<open>deadlock_state ?S qq\<close> unfolding \<open>qq = Inl (q1',q2')\<close> by auto
      qed 
    qed
    then show ?thesis 
      using \<open>qq = Inl (q1', q2')\<close> \<open>x \<in> FSM.inputs M\<close> by blast
  next
    case b
    then show ?thesis by simp
  qed
qed


lemma state_separator_from_input_choices_retains_io :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
    shows "retains_outputs_for_states_and_inputs (canonical_separator M q1 q2) (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
  unfolding retains_outputs_for_states_and_inputs_def
  using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] by fastforce


lemma state_separator_from_input_choices_is_state_separator :
  assumes "distinct (map fst cs)"
      and "q1 \<in> states M" 
      and "q2 \<in> states M"
      and "\<And> qq x . (qq,x) \<in> set cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      and "Inl (q1,q2) \<in> set (map fst cs)"
      and "\<And> qq . qq \<in> set (map fst cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
      and "\<And> i t . i < length cs
                    \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                    \<Longrightarrow> t_source t = (fst (cs ! i))
                    \<Longrightarrow> t_input  t = snd (cs ! i)
                    \<Longrightarrow> t_target t \<in> ((set (map fst (take i cs))) \<union> {Inr q1, Inr q2})"
      and "completely_specified M"
  shows "is_state_separator_from_canonical_separator
            (canonical_separator M q1 q2)
            q1
            q2
            (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?S = "(state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"

  have submachine_prop:   "is_submachine ?S ?C"
    using state_separator_from_input_choices_submachine[OF assms(2,3,4,5,6)] by blast

  have single_input_prop: "single_input ?S"
    using state_separator_from_input_choices_single_input[OF assms(1,2,3,4,5,6)] by blast

  have acyclic_prop :     "acyclic ?S"
    using state_separator_from_input_choices_acyclic[OF assms(1,2,3,4,5,6,7)] by blast

  have i3:                "\<And> qq . qq \<in> states ?S 
                                  \<Longrightarrow> deadlock_state ?S qq 
                                  \<Longrightarrow> qq \<in> {Inr q1, Inr q2} 
                                        \<or> (\<exists> q1' q2' x . qq = Inl (q1',q2') 
                                            \<and> x \<in> inputs M 
                                            \<and> h_out M (q1',x) = {} 
                                            \<and> h_out M (q2',x) = {})"
    using state_separator_from_input_choices_deadlock[OF assms(1,2,3,4,5,6,7)] by blast

  have i4:                "retains_outputs_for_states_and_inputs (canonical_separator M q1 q2) (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)"
    using state_separator_from_input_choices_retains_io[OF assms(1,2,3,4,5,6,7)] by blast



  have deadlock_prop_1: "deadlock_state ?S (Inr q1)"
    using submachine_deadlock[OF \<open>is_submachine ?S ?C\<close> canonical_separator_deadlock(1)[OF assms(2,3)]] by assumption

  have deadlock_prop_2: "deadlock_state ?S (Inr q2)"
    using submachine_deadlock[OF \<open>is_submachine ?S ?C\<close> canonical_separator_deadlock(2)[OF assms(2,3)]] by assumption

  have non_deadlock_prop': "\<And> qq . qq \<in> states ?S \<Longrightarrow> qq \<noteq> Inr q1 \<Longrightarrow> qq \<noteq> Inr q2 \<Longrightarrow> (isl qq \<and> \<not> deadlock_state ?S qq)"
  proof -
    fix qq assume "qq \<in> states ?S" and "qq \<noteq> Inr q1" and "qq \<noteq> Inr q2"
    then have "qq \<in> set (map fst cs)"
      using state_separator_from_input_choices_simps(2)[OF assms(2,3,4,5,6)] by blast
    then obtain q1' q2' x where "qq = Inl (q1',q2')" and "(Inl (q1',q2'),x) \<in> set cs"
      using assms(6) by fastforce
    then have "(Inl (q1',q2')) \<in> states (canonical_separator M q1 q2)" and "x \<in> inputs M"
      using assms(4) by blast+
    then have "(q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))"
      using canonical_separator_simps(2)[OF assms(2,3)] by fastforce
    then have "(q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))"
      using reachable_state_is_state by fastforce
    then have "q1' \<in> states M" and "q2' \<in> states M"
      using assms(2,3) by auto

    obtain y q1'' where "(y,q1'') \<in> h M (q1',x)"
      using \<open>completely_specified M\<close> \<open>q1' \<in> states M\<close> \<open>x \<in> inputs M\<close>
      unfolding completely_specified.simps h.simps by fastforce 

    consider (a) "y \<in> h_out M (q2',x)" | (b) "y \<notin> h_out M (q2',x)" by blast
    then have "\<not> deadlock_state ?S (Inl (q1',q2'))"
    proof cases
      case a 
      then obtain q2'' where "(y,q2'') \<in> h M (q2',x)" by auto
      then have "((q1',q2'),x,y,(q1'',q2'')) \<in> transitions (product (from_FSM M q1) (from_FSM M q2))"
        using assms(2,3) \<open>(y,q1'') \<in> h M (q1',x)\<close>
        unfolding h.simps product_transitions_def by fastforce
      then have "(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> transitions ?C"
        using canonical_separator_transitions_def[OF assms(2,3)]
        using \<open>(q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))\<close> by fast
      then have "(Inl (q1',q2'),x,y,Inl (q1'',q2'')) \<in> transitions ?S"
        using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] 
              \<open>(Inl (q1',q2'),x) \<in> set cs\<close> by fastforce
      then show ?thesis 
        unfolding deadlock_state.simps by fastforce
    next
      case b
      then have "(Inl (q1',q2'),x,y,Inr q1) \<in> distinguishing_transitions_left M q1 q2"
        using \<open>(y,q1'') \<in> h M (q1',x)\<close> \<open>(q1',q2') \<in> states (product (from_FSM M q1) (from_FSM M q2))\<close> 
        unfolding h_simps h_out.simps distinguishing_transitions_left_def 
        by blast        
      then have "(Inl (q1',q2'),x,y,Inr q1) \<in> transitions ?C"
        unfolding canonical_separator_transitions_def[OF assms(2,3)] by blast
      then have "(Inl (q1',q2'),x,y,Inr q1) \<in> transitions ?S"
        using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] 
              \<open>(Inl (q1',q2'),x) \<in> set cs\<close> by fastforce
      then show ?thesis 
        unfolding deadlock_state.simps by fastforce
    qed
    then show "(isl qq \<and> \<not> deadlock_state ?S qq)"
      unfolding \<open>qq = Inl (q1',q2')\<close> by simp
  qed
  then have non_deadlock_prop: "(\<forall> q \<in> reachable_states ?S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (isl q \<and> \<not> deadlock_state ?S q))"
    using reachable_state_is_state by force
    

  (* Idea for reachable-deadlock proofs:
      - get longest path from initial to some non-deadlock state
      - that state can only target deadlock states
      - by assm, both Inr q1 and Inr q2 must be reached from that state
  *)
  define ndlps where ndlps_def: "ndlps = {p . path ?S (initial ?S) p \<and> isl (target (initial ?S) p)}"
  

  obtain qdl where "qdl \<in> reachable_states ?S" and "deadlock_state ?S qdl"
    using acyclic_deadlock_reachable[OF \<open>acyclic ?S\<close>] by blast
  
  have "qdl = Inr q1 \<or> qdl = Inr q2"
    using non_deadlock_prop'[OF reachable_state_is_state[OF \<open>qdl \<in> reachable_states ?S\<close>]] \<open>deadlock_state ?S qdl\<close> by fastforce
  then have "Inr q1 \<in> reachable_states ?S \<or> Inr q2 \<in> reachable_states ?S"
    using \<open>qdl \<in> reachable_states ?S\<close> by blast

  have "isl (target (initial ?S) [])"
    using state_separator_from_input_choices_simps(1)[OF assms(2,3,4,5,6)] by auto
  then have "[] \<in> ndlps"
    unfolding ndlps_def by auto
  then have "ndlps \<noteq> {}"
    by blast
  moreover have "finite ndlps"
    using acyclic_finite_paths_from_reachable_state[OF \<open>acyclic ?S\<close>, of "[]"] unfolding ndlps_def by fastforce
  ultimately have "\<exists> p \<in> ndlps . \<forall> p' \<in> ndlps . length p' \<le> length p"
    by (meson max_length_elem not_le_imp_less) 
  then obtain mndlp where "path ?S (initial ?S) mndlp"
                      and "isl (target (initial ?S) mndlp)"
                      and "\<And> p . path ?S (initial ?S) p \<Longrightarrow> isl (target (initial ?S) p) \<Longrightarrow> length p \<le> length mndlp"
    unfolding ndlps_def by blast
  then have "(target (initial ?S) mndlp) \<in> reachable_states ?S"
    unfolding reachable_states_def by auto
  then have "(target (initial ?S) mndlp) \<in> states ?S"
    using reachable_state_is_state by auto
  then have "(target (initial ?S) mndlp) \<in> (set (map fst cs))"
    using \<open>isl (target (initial ?S) mndlp)\<close> state_separator_from_input_choices_simps(2)[OF assms(2,3,4,5,6)] by force
  then obtain q1' q2' x where "(Inl (q1',q2'),x) \<in> set cs"
                          and "target (initial ?S) mndlp = Inl (q1',q2')"
    using assms(6) by fastforce
  then obtain i where "i < length cs" and "(cs ! i) = (Inl (q1',q2'),x)"
    by (metis in_set_conv_nth)

  have "Inl (q1', q2') \<in> FSM.states (canonical_separator M q1 q2)" and "x \<in> FSM.inputs M"
    using assms(4)[OF \<open>(Inl (q1',q2'),x) \<in> set cs\<close>] by blast+
  then have "(q1',q2') \<in> states (Product_FSM.product (FSM.from_FSM M q1) (FSM.from_FSM M q2))"
    using canonical_separator_simps(2)[OF assms(2,3)] by blast

  have "q1' \<in> states M" and "q2' \<in> states M"
    using canonical_separator_states[OF \<open>Inl (q1', q2') \<in> FSM.states (canonical_separator M q1 q2)\<close> assms(2,3)]
    unfolding product_simps using assms(2,3) by simp+

  have "\<not>(\<exists>t'\<in>FSM.transitions (canonical_separator M q1 q2). t_source t' = target (initial ?S) mndlp \<and> t_input t' = x \<and> isl (t_target t'))"
  proof 
    assume "\<exists>t'\<in>FSM.transitions (canonical_separator M q1 q2). t_source t' = target (initial ?S) mndlp \<and> t_input t' = x \<and> isl (t_target t')"
    then obtain t' where "t'\<in>FSM.transitions (canonical_separator M q1 q2)"
                     and "t_source t' = target (initial ?S) mndlp"
                     and "t_input t' = x"
                     and "isl (t_target t')" 
      by blast
    then have "\<exists>q1' q2' x . (Inl (q1', q2'), x)\<in>set cs \<and> t_source t' = Inl (q1', q2') \<and> t_input t' = x"
      using \<open>(Inl (q1',q2'),x) \<in> set cs\<close> unfolding \<open>target (initial ?S) mndlp = Inl (q1',q2')\<close> by fast
    then have "t' \<in> transitions ?S"
      using \<open>t'\<in>FSM.transitions (canonical_separator M q1 q2)\<close> \<open>(Inl (q1',q2'),x) \<in> set cs\<close>
      using state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] by blast

    then have "path ?S (initial ?S) (mndlp @ [t'])"
      using \<open>path ?S (initial ?S) mndlp\<close> \<open>t_source t' = target (initial ?S) mndlp\<close> by (metis path_append_transition)
    moreover have "isl (target (initial ?S) (mndlp @[t']))"
      using \<open>isl (t_target t')\<close> by auto
    ultimately show "False"
      using \<open>\<And> p . path ?S (initial ?S) p \<Longrightarrow> isl (target (initial ?S) p) \<Longrightarrow> length p \<le> length mndlp\<close>[of "mndlp@[t']"] by auto
  qed

  then obtain y1 y2 where "(Inl (q1',q2'),x,y1,Inr q1) \<in> transitions (canonical_separator M q1 q2)"
                      and "(Inl (q1',q2'),x,y2,Inr q2) \<in> transitions (canonical_separator M q1 q2)"
    using canonical_separator_isl_deadlock[OF \<open>Inl (q1', q2') \<in> FSM.states (canonical_separator M q1 q2)\<close> \<open>x \<in> FSM.inputs M\<close> \<open>completely_specified M\<close> _ assms(2,3)]
    unfolding \<open>target (initial ?S) mndlp = Inl (q1',q2')\<close> by blast


  have "(Inl (q1',q2'), x, y1, Inr q1) \<in> transitions ?S"
    using \<open>(Inl (q1',q2'),x) \<in> set cs\<close> state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] \<open>(Inl (q1',q2'),x,y1,Inr q1) \<in> transitions (canonical_separator M q1 q2)\<close> by force

  have "(Inl (q1',q2'), x, y2, Inr q2) \<in> transitions ?S"
    using \<open>(Inl (q1',q2'),x) \<in> set cs\<close> state_separator_from_input_choices_transitions_alt_def[OF assms(2,3,4,5,6,7)] \<open>(Inl (q1',q2'),x,y2,Inr q2) \<in> transitions (canonical_separator M q1 q2)\<close> by force

  have "path ?S (initial ?S) (mndlp@[(Inl (q1',q2'), x, y1, Inr q1)])"
    using \<open>target (initial ?S) mndlp = Inl (q1',q2')\<close> 
    using path_append_transition[OF \<open>path ?S (initial ?S) mndlp\<close> \<open>(Inl (q1',q2'), x, y1, Inr q1) \<in> transitions ?S\<close>] by force
  moreover have "target (initial ?S) (mndlp@[(Inl (q1',q2'), x, y1, Inr q1)]) = Inr q1"
    by auto
  ultimately have reachable_prop_1: "Inr q1 \<in> reachable_states ?S"
    using reachable_states_intro by metis

   have "path ?S (initial ?S) (mndlp@[(Inl (q1',q2'), x, y2, Inr q2)])"
    using \<open>target (initial ?S) mndlp = Inl (q1',q2')\<close> 
    using path_append_transition[OF \<open>path ?S (initial ?S) mndlp\<close> \<open>(Inl (q1',q2'), x, y2, Inr q2) \<in> transitions ?S\<close>] by force
  moreover have "target (initial ?S) (mndlp@[(Inl (q1',q2'), x, y2, Inr q2)]) = Inr q2"
    by auto
  ultimately have reachable_prop_2: "Inr q2 \<in> reachable_states ?S"
    using reachable_states_intro by metis


  have retainment_prop : "\<And> q x t' . q \<in> reachable_states ?S
        \<Longrightarrow> x \<in> FSM.inputs ?C 
        \<Longrightarrow> (\<exists>t\<in>FSM.transitions ?S. t_source t = q \<and> t_input t = x) 
        \<Longrightarrow> t' \<in> FSM.transitions ?C
        \<Longrightarrow> t_source t' = q 
        \<Longrightarrow> t_input t' = x 
        \<Longrightarrow> t' \<in> FSM.transitions ?S"
  proof -
    fix q x t' assume "q \<in> reachable_states ?S"
                  and "x \<in> FSM.inputs ?C"
                  and "(\<exists>t\<in>FSM.transitions ?S. t_source t = q \<and> t_input t = x)"
                  and "t' \<in> FSM.transitions ?C"
                  and "t_source t' = q" 
                  and "t_input t' = x" 

    obtain t where "t \<in> FSM.transitions ?S" and "t_source t = q" and "t_input t = x"
      using \<open>(\<exists>t\<in>FSM.transitions ?S. t_source t = q \<and> t_input t = x)\<close> by blast
    then have "t_source t = t_source t' \<and> t_input t = t_input t'"
      using \<open>t_source t' = q\<close> \<open>t_input t' = x\<close> by auto

    
    show "t' \<in> FSM.transitions ?S"
      using i4 unfolding retains_outputs_for_states_and_inputs_def
      using \<open>t \<in> FSM.transitions ?S\<close> \<open>t' \<in> FSM.transitions ?C\<close> \<open>t_source t = t_source t' \<and> t_input t = t_input t'\<close> 
      by blast
  qed
    
  show ?thesis unfolding is_state_separator_from_canonical_separator_def
    using submachine_prop
          single_input_prop
          acyclic_prop
          deadlock_prop_1
          deadlock_prop_2
          reachable_prop_1
          reachable_prop_2
          non_deadlock_prop
          retainment_prop by blast 
qed
    
    

subsubsection \<open>Calculating a State Separator by Backwards Reachability Analysis\<close>

text \<open>A state separator for states @{text "q1"} and @{text "q2"} can be calculated using backwards 
      reachability analysis starting from the two deadlock states of their canonical separator until
      @{text "Inl (q1.q2)"} is reached or it is not possible to reach @{text "(q1,q2)"}.\<close>

definition s_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> 'b) list" where
  "s_states M q1 q2 = (let C = canonical_separator M q1 q2
   in select_inputs (h C) (initial C) (inputs_as_list C) (remove1 (Inl (q1,q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list C)))) {Inr q1, Inr q2} [])"


definition state_separator_from_s_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a, 'b, 'c) fsm option" 
  where
  "state_separator_from_s_states M q1 q2 = 
    (let cs = s_states M q1 q2 
      in (case length cs of
            0 \<Rightarrow> None |
            _ \<Rightarrow> if fst (last cs) = Inl (q1,q2)
                  then Some (state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 cs)
                  else None))"


lemma state_separator_from_s_states_code[code] :
  "state_separator_from_s_states M q1 q2 =
    (let C = canonical_separator M q1 q2;
         cs = select_inputs (h C) (initial C) (inputs_as_list C) (remove1 (Inl (q1,q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list C)))) {Inr q1, Inr q2} []
      in (case length cs of
            0 \<Rightarrow> None |
            _ \<Rightarrow> if fst (last cs) = Inl (q1,q2)
                  then Some (state_separator_from_input_choices M C q1 q2 cs) 
                  else None))"
  unfolding s_states_def state_separator_from_s_states_def Let_def by simp


lemma s_states_properties : 
  assumes "q1 \<in> states M" and "q2 \<in> states M" 
  shows "distinct (map fst (s_states M q1 q2))"
    and "\<And> qq x . (qq,x) \<in> set (s_states M q1 q2) \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
    and "\<And> qq . qq \<in> set (map fst (s_states M q1 q2)) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
    and "\<And> i t . i < length (s_states M q1 q2)
                  \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                  \<Longrightarrow> t_source t = (fst ((s_states M q1 q2) ! i))
                  \<Longrightarrow> t_input  t = snd ((s_states M q1 q2) ! i)
                  \<Longrightarrow> t_target t \<in> ((set (map fst (take i (s_states M q1 q2)))) \<union> {Inr q1, Inr q2})"
proof -
  let ?C = "canonical_separator M q1 q2"
  let ?nS = "{Inr q1, Inr q2}"
  let ?nL = "(remove1 (Inl (q1,q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list ?C))))"
  let ?iL = "(inputs_as_list ?C)"
  let ?q0 = "(initial ?C)"
  let ?f  = "(h ?C)"
  let ?k  = "(size (canonical_separator M q1 q2))"

  let ?cs = "(s_states M q1 q2)"
  
  (* parameter properties required by lemmata for select_inputs *)
  have pp1: "distinct (map fst [])" by auto
  have pp2: "set (map fst []) \<subseteq> ?nS" by auto
  have pp3: "?nS = ?nS \<union> set (map fst [])" by auto
  have pp4: "?q0 \<notin> ?nS" unfolding canonical_separator_simps[OF assms] by auto
  have pp5 :"distinct ?nL" using states_as_list_distinct by simp 
  have pp6: "?q0 \<notin> set ?nL" unfolding canonical_separator_simps[OF assms] by auto
  have pp7: "set ?nL \<inter> ?nS = {}" by auto

  (* index based properties *)

  have "\<And> i . length [] \<le> i" by auto

  have ip1: "\<And> i . i < length ?cs \<Longrightarrow> fst (?cs ! i) \<in> (insert ?q0 (set ?nL))" 
  and  ip2: "\<And> i . i < length ?cs \<Longrightarrow> fst (?cs ! i) \<notin> ?nS0"
  and  ip3: "\<And> i . i < length ?cs \<Longrightarrow> snd (?cs ! i) \<in> set ?iL"
  and  ip4: "\<And> i . i < length ?cs \<Longrightarrow> (\<forall> qx' \<in> set (take i ?cs) . fst (?cs ! i) \<noteq> fst qx')"
    using select_inputs_index_properties[OF _ \<open>\<And> i . length [] \<le> i\<close> pp1 pp3 pp4 pp5 pp6 pp7]
    unfolding s_states_def Let_def by blast+
  have ip5: "\<And> i . i < length ?cs \<Longrightarrow> (\<exists> t \<in> transitions ?C . t_source t = fst (?cs ! i) \<and> t_input t = snd (?cs ! i))"
    using select_inputs_index_properties(5)[OF _ \<open>\<And> i . length [] \<le> i\<close> pp1 pp3 pp4 pp5 pp6 pp7]
    unfolding s_states_def Let_def by blast
  have ip6: "\<And> i t . i < length ?cs \<Longrightarrow> t \<in> transitions ?C \<Longrightarrow> t_source t = fst (?cs ! i) \<Longrightarrow> t_input t = snd (?cs ! i) \<Longrightarrow> (t_target t \<in> ?nS0 \<or> (\<exists> qx' \<in> set (take i ?cs) . fst qx' = (t_target t)))"
    using select_inputs_index_properties(6)[OF _ \<open>\<And> i . length [] \<le> i\<close> pp1 pp3 pp4 pp5 pp6 pp7]
    unfolding s_states_def Let_def by blast


  show "distinct (map fst ?cs)" 
    using select_inputs_distinct[OF pp1 pp2 pp4 pp5 pp6 pp7]
    unfolding s_states_def Let_def by blast

  show "\<And> qq x . (qq,x) \<in> set ?cs \<Longrightarrow> qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
  proof -
    fix qq x assume "(qq,x) \<in> set ?cs"
    then obtain i where "i < length ?cs" and "?cs ! i = (qq,x)"
      by (meson in_set_conv_nth) 
    show "qq \<in> states (canonical_separator M q1 q2) \<and> x \<in> inputs M"
      using ip1[OF \<open>i < length ?cs\<close>] ip3[OF \<open>i < length ?cs\<close>] 
            states_as_list_set[of ?C] inputs_as_list_set[of ?C]
      unfolding \<open>?cs ! i = (qq,x)\<close> fst_conv snd_conv canonical_separator_simps(3)[OF assms]
      by auto 
  qed

  show "\<And> qq . qq \<in> set (map fst ?cs) \<Longrightarrow> \<exists> q1' q2' . qq = Inl (q1',q2')"
  proof -
    fix qq assume "qq \<in> set (map fst ?cs)"
    then obtain i where "i < length ?cs" and "fst (?cs ! i) = qq"
      by (metis (no_types, lifting) in_set_conv_nth length_map nth_map)
    show "\<exists> q1' q2' . qq = Inl (q1',q2')"
      using ip1[OF \<open>i < length ?cs\<close>] states_as_list_set[of ?C]
      unfolding \<open>fst (?cs ! i) = qq\<close> canonical_separator_simps[OF assms]
      by auto 
  qed

  show "\<And> i t . i < length ?cs
                  \<Longrightarrow> t \<in> transitions (canonical_separator M q1 q2) 
                  \<Longrightarrow> t_source t = (fst (?cs ! i))
                  \<Longrightarrow> t_input  t = snd (?cs ! i)
                  \<Longrightarrow> t_target t \<in> ((set (map fst (take i ?cs))) \<union> {Inr q1, Inr q2})"
  proof -
    fix i t assume "i < length ?cs"
               and "t \<in> transitions ?C"
               and "t_source t = (fst (?cs ! i))"
               and "t_input  t = snd (?cs ! i)"

    show "t_target t \<in> ((set (map fst (take i ?cs))) \<union> {Inr q1, Inr q2})"
      using ip6[OF \<open>i < length ?cs\<close> \<open>t \<in> transitions ?C\<close> \<open>t_source t = (fst (?cs ! i))\<close> \<open>t_input  t = snd (?cs ! i)\<close>] 
      by (metis Un_iff in_set_conv_nth length_map nth_map)
  qed
qed

     
lemma state_separator_from_s_states_soundness :
  assumes "state_separator_from_s_states M q1 q2 = Some A"
      and "q1 \<in> states M" and "q2 \<in> states M" and "completely_specified M"
  shows "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
proof -
  let ?cs = "s_states M q1 q2"

  have "length (s_states M q1 q2) \<noteq> 0 \<and> fst (last (s_states M q1 q2)) = Inl (q1,q2)"
  and  "A = state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 ?cs"
    using assms(1) unfolding state_separator_from_s_states_def Let_def
    by (cases "length (s_states M q1 q2)"; cases "fst (last (s_states M q1 q2)) = Inl (q1,q2)"; auto)+
  then have "Inl (q1,q2) \<in> set (map fst ?cs)"
    by (metis last_in_set length_0_conv map_set)
     

  show ?thesis 
    using state_separator_from_input_choices_is_state_separator[
        OF _ assms(2,3) _ \<open>Inl (q1,q2) \<in> set (map fst ?cs)\<close>,
        OF s_states_properties[OF assms(2,3)] assms(4)] 
    unfolding \<open>A = state_separator_from_input_choices M (canonical_separator M q1 q2) q1 q2 ?cs\<close>[symmetric] by blast
qed
  

lemma state_separator_from_s_states_exhaustiveness :
  assumes "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
      and "q1 \<in> states M" and "q2 \<in> states M" and "completely_specified M" and "observable M"
  shows "state_separator_from_s_states M q1 q2 \<noteq> None"
proof -
  let ?CSep = "(canonical_separator M q1 q2)"

  obtain S where S_def: "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
    using assms(1) by blast

  then have "is_submachine S ?CSep" 
       and  "single_input S"
       and  "acyclic S"
        and  *:"\<And> q . q \<in> reachable_states S \<Longrightarrow> q \<noteq> Inr q1 \<Longrightarrow> q \<noteq> Inr q2 \<Longrightarrow> (isl q \<and> \<not> deadlock_state S q)"
       and  **:"\<And> q x t . q \<in> reachable_states S \<Longrightarrow> x \<in> (inputs ?CSep) \<Longrightarrow> (\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x) \<Longrightarrow> t \<in> transitions ?CSep \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow> t \<in> transitions S"
    using assms unfolding is_state_separator_from_canonical_separator_def by blast+

  have p1: "(\<And>q x. q \<in> reachable_states S \<Longrightarrow> h S (q, x) \<noteq> {} \<Longrightarrow> h S (q, x) = h ?CSep (q, x))"
  proof - 
    fix q x assume "q \<in> reachable_states S" and "h S (q, x) \<noteq> {}"

    then have "x \<in> inputs ?CSep"
      using \<open>is_submachine S ?CSep\<close> fsm_transition_input by force
    have "(\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x)"
      using \<open>h S (q, x) \<noteq> {}\<close> by fastforce

    have "\<And> y q'' . (y,q'') \<in> h S (q,x) \<Longrightarrow> (y,q'') \<in> h ?CSep (q,x)" 
      using \<open>is_submachine S ?CSep\<close> by force 
    moreover have "\<And> y q'' . (y,q'') \<in> h ?CSep (q,x) \<Longrightarrow> (y,q'') \<in> h S (q,x)" 
      using **[OF \<open>q \<in> reachable_states S\<close> \<open>x \<in> inputs ?CSep\<close> \<open>(\<exists> t \<in> transitions S . t_source t = q \<and> t_input t = x)\<close>]
      unfolding h.simps by force
    ultimately show "h S (q, x) = h ?CSep (q, x)" 
      by force
  qed 

  have p2: "\<And>q'. q' \<in> reachable_states S \<Longrightarrow> deadlock_state S q' \<Longrightarrow> q' \<in> {Inr q1, Inr q2} \<union> set (map fst [])"
    using * by fast

  have "initial S = Inl (q1,q2)"
    using is_state_separator_from_canonical_separator_initial[OF S_def assms(2,3)] by assumption
 
  have ***: "(set (remove1 (Inl (q1, q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list ?CSep)))) \<union> {Inr q1, Inr q2} \<union> set (map fst [])) = (states ?CSep - {Inl (q1,q2)})"
    using states_as_list_set[of ?CSep] states_as_list_distinct[of ?CSep] 
    unfolding 
              \<open>initial S = Inl (q1,q2)\<close> 
              canonical_separator_simps(2)[OF assms(2,3)]
    by auto 

  have "Inl (q1,q2) \<in> reachable_states ?CSep"
    using reachable_states_initial[of S] unfolding \<open>initial S = Inl (q1,q2)\<close>
    using  submachine_reachable_subset[OF \<open>is_submachine S ?CSep\<close>] by blast
  then have p3: "states ?CSep = insert (FSM.initial S) (set (remove1 (Inl (q1,q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list ?CSep)))) \<union> {Inr q1, Inr q2} \<union> set (map fst []))"
    unfolding *** \<open>initial S = Inl (q1,q2)\<close>
    using reachable_state_is_state by fastforce
   
  have p4: "initial S \<notin> (set (remove1 (Inl (q1,q2)) (remove1 (Inr q1) (remove1 (Inr q2) (states_as_list ?CSep)))) \<union> {Inr q1, Inr q2} \<union> set (map fst []))"
    using \<open>FSM.initial S = Inl (q1, q2)\<close> by auto 

  have "fst (last (s_states M q1 q2)) = Inl (q1,q2)" and "length (s_states M q1 q2) > 0"
    using select_inputs_from_submachine[OF \<open>single_input S\<close> \<open>acyclic S\<close> \<open>is_submachine S ?CSep\<close> p1 p2 p3 p4]
    unfolding s_states_def submachine_simps[OF \<open>is_submachine S ?CSep\<close>] Let_def canonical_separator_simps(1)[OF assms(2,3)]
    by auto 

  obtain k where"length (s_states M q1 q2) = Suc k" 
    using \<open>length (s_states M q1 q2) > 0\<close> gr0_conv_Suc by blast 
  have "(fst (last (s_states M q1 q2)) = Inl (q1,q2)) = True"
    using \<open>fst (last (s_states M q1 q2)) = Inl (q1,q2)\<close> by simp

  show ?thesis                            
    unfolding state_separator_from_s_states_def Let_def \<open>length (s_states M q1 q2) = Suc k\<close> \<open>fst (last (s_states M q1 q2)) = Inl (q1,q2)\<close>
    by auto
qed



subsection \<open>Generalizing State Separators\<close>

text \<open>State separators can be defined without reverence to the canonical separator:\<close>

definition is_separator :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> bool" where
  "is_separator M q1 q2 A t1 t2 = 
    (single_input A
     \<and> acyclic A
     \<and> observable A
     \<and> deadlock_state A t1 
     \<and> deadlock_state A t2
     \<and> t1 \<in> reachable_states A
     \<and> t2 \<in> reachable_states A
     \<and> (\<forall> t \<in> reachable_states A . (t \<noteq> t1 \<and> t \<noteq> t2) \<longrightarrow> \<not> deadlock_state A t)
     \<and> (\<forall> io \<in> L A . (\<forall> x yq yt . (io@[(x,yq)] \<in> LS M q1 \<and> io@[(x,yt)] \<in> L A) \<longrightarrow> (io@[(x,yq)] \<in> L A))
                   \<and> (\<forall> x yq2 yt . (io@[(x,yq2)] \<in> LS M q2 \<and> io@[(x,yt)] \<in> L A) \<longrightarrow> (io@[(x,yq2)] \<in> L A)))
     \<and> (\<forall> p . (path A (initial A) p \<and> target (initial A) p = t1) \<longrightarrow> p_io p \<in> LS M q1 - LS M q2)
     \<and> (\<forall> p . (path A (initial A) p \<and> target (initial A) p = t2) \<longrightarrow> p_io p \<in> LS M q2 - LS M q1)
     \<and> (\<forall> p . (path A (initial A) p \<and> target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2) \<longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2)
     \<and> q1 \<noteq> q2
     \<and> t1 \<noteq> t2
     \<and> (inputs A) \<subseteq> (inputs M))"


lemma is_separator_simps :
  assumes "is_separator M q1 q2 A t1 t2"
shows "single_input A"
  and "acyclic A"
  and "observable A"
  and "deadlock_state A t1"
  and "deadlock_state A t2"
  and "t1 \<in> reachable_states A"
  and "t2 \<in> reachable_states A"
  and "\<And> t . t \<in> reachable_states A \<Longrightarrow> t \<noteq> t1 \<Longrightarrow> t \<noteq> t2 \<Longrightarrow> \<not> deadlock_state A t"
  and "\<And> io x yq yt . io@[(x,yq)] \<in> LS M q1 \<Longrightarrow> io@[(x,yt)] \<in> L A \<Longrightarrow> (io@[(x,yq)] \<in> L A)"
  and "\<And> io x yq yt . io@[(x,yq)] \<in> LS M q2 \<Longrightarrow> io@[(x,yt)] \<in> L A \<Longrightarrow> (io@[(x,yq)] \<in> L A)"
  and "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2"
  and "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1"
  and "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p \<noteq> t1 \<Longrightarrow> target (initial A) p \<noteq> t2 \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2"
  and "q1 \<noteq> q2"
  and "t1 \<noteq> t2"
  and "(inputs A) \<subseteq> (inputs M)"
proof -
  have p01: "single_input A"
  and  p02: "acyclic A"
  and  p03: "observable A"
  and  p04: "deadlock_state A t1" 
  and  p05: "deadlock_state A t2"
  and  p06: "t1 \<in> reachable_states A"
  and  p07: "t2 \<in> reachable_states A"
  and  p08: "(\<forall> t \<in> reachable_states A . (t \<noteq> t1 \<and> t \<noteq> t2) \<longrightarrow> \<not> deadlock_state A t)"
  and  p09: "(\<forall> io \<in> L A . (\<forall> x yq yt . (io@[(x,yq)] \<in> LS M q1 \<and> io@[(x,yt)] \<in> L A) \<longrightarrow> (io@[(x,yq)] \<in> L A))
                         \<and> (\<forall> x yq2 yt . (io@[(x,yq2)] \<in> LS M q2 \<and> io@[(x,yt)] \<in> L A) \<longrightarrow> (io@[(x,yq2)] \<in> L A)))"
  and  p10: "(\<forall> p . (path A (initial A) p \<and> target (initial A) p = t1) \<longrightarrow> p_io p \<in> LS M q1 - LS M q2)"
  and  p11: "(\<forall> p . (path A (initial A) p \<and> target (initial A) p = t2) \<longrightarrow> p_io p \<in> LS M q2 - LS M q1)"
  and  p12: "(\<forall> p . (path A (initial A) p \<and> target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2) \<longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2)"
  and  p13: "q1 \<noteq> q2"
  and  p14: "t1 \<noteq> t2"
  and  p15: "(inputs A) \<subseteq> (inputs M)"
    using assms unfolding is_separator_def by presburger+

  show "single_input A" using p01 by assumption
  show "acyclic A" using p02 by assumption
  show "observable A" using p03 by assumption
  show "deadlock_state A t1" using p04 by assumption
  show "deadlock_state A t2" using p05 by assumption
  show "t1 \<in> reachable_states A" using p06 by assumption
  show "t2 \<in> reachable_states A" using p07 by assumption
  show "\<And> io x yq yt . io@[(x,yq)] \<in> LS M q1 \<Longrightarrow> io@[(x,yt)] \<in> L A \<Longrightarrow> (io@[(x,yq)] \<in> L A)" using p09 language_prefix[of _ _ A "initial A"] by blast
  show "\<And> io x yq yt . io@[(x,yq)] \<in> LS M q2 \<Longrightarrow> io@[(x,yt)] \<in> L A \<Longrightarrow> (io@[(x,yq)] \<in> L A)" using p09 language_prefix[of _ _ A "initial A"] by blast
  show "\<And> t . t \<in> reachable_states A \<Longrightarrow> t \<noteq> t1 \<Longrightarrow> t \<noteq> t2 \<Longrightarrow> \<not> deadlock_state A t" using p08 by blast
  show "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2" using p10 by blast
  show "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1" using p11 by blast
  show "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p \<noteq> t1 \<Longrightarrow> target (initial A) p \<noteq> t2 \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2" using p12 by blast
  show "q1 \<noteq> q2" using p13 by assumption
  show "t1 \<noteq> t2" using p14 by assumption
  show "(inputs A) \<subseteq> (inputs M)" using p15 by assumption
qed


lemma separator_initial :
  assumes "is_separator M q1 q2 A t1 t2"
shows "initial A \<noteq> t1"
and   "initial A \<noteq> t2"
proof -
  show "initial A \<noteq> t1"
  proof 
    assume "initial A = t1"
    then have "deadlock_state A (initial A)"
      using is_separator_simps(4)[OF assms] by auto
    then have "reachable_states A = {initial A}" 
      using states_initial_deadlock by blast
    then show "False"
      using is_separator_simps(7,15)[OF assms] \<open>initial A = t1\<close> by auto
  qed

  show "initial A \<noteq> t2"
  proof 
    assume "initial A = t2"
    then have "deadlock_state A (initial A)"
      using is_separator_simps(5)[OF assms] by auto
    then have "reachable_states A = {initial A}" 
      using states_initial_deadlock by blast
    then show "False"
      using is_separator_simps(6,15)[OF assms] \<open>initial A = t2\<close> by auto
  qed
qed


lemma separator_path_targets :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "path A (initial A) p"
shows "p_io p \<in> LS M q1 - LS M q2 \<Longrightarrow> target (initial A) p = t1"
and   "p_io p \<in> LS M q2 - LS M q1 \<Longrightarrow> target (initial A) p = t2"
and   "p_io p \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> (target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2)"
and   "p_io p \<in> LS M q1 \<union> LS M q2"
proof -
  have pt1: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2" 
  and  pt2: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1" 
  and  pt3: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p \<noteq> t1 \<Longrightarrow> target (initial A) p \<noteq> t2 \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2" 
  and  "t1 \<noteq> t2"
  and  "observable A"
    using is_separator_simps[OF assms(1)] by blast+

  show "p_io p \<in> LS M q1 - LS M q2 \<Longrightarrow> target (initial A) p = t1"
    using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close> by blast
  show "p_io p \<in> LS M q2 - LS M q1 \<Longrightarrow> target (initial A) p = t2"
    using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close> by blast
  show "p_io p \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> (target (initial A) p \<noteq> t1 \<and> target (initial A) p \<noteq> t2)"
    using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close> by blast
  show "p_io p \<in> LS M q1 \<union> LS M q2"
    using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close> by blast
qed


lemma separator_language :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "io \<in> L A"
shows "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets A io (initial A) = {t1}"
and   "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets A io (initial A) = {t2}"
and   "io \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> io_targets A io (initial A) \<inter> {t1,t2} = {}"
and   "io \<in> LS M q1 \<union> LS M q2"
proof -

  obtain p where "path A (initial A) p" and "p_io p = io"
    using \<open>io \<in> L A\<close>  by auto

  have pt1: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2" 
  and  pt2: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1" 
  and  pt3: "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p \<noteq> t1 \<Longrightarrow> target (initial A) p \<noteq> t2 \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2" 
  and  "t1 \<noteq> t2"
  and  "observable A"
    using is_separator_simps[OF assms(1)] by blast+


  show "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets A io (initial A) = {t1}"
  proof -
    assume "io \<in> LS M q1 - LS M q2"
    
    then have "p_io p \<in> LS M q1 - LS M q2"
      using \<open>p_io p = io\<close> by auto
    then have "target (initial A) p = t1"
      using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close>
      by blast 
    then have "t1 \<in> io_targets A io (initial A)"
      using \<open>path A (initial A) p\<close> \<open>p_io p = io\<close> unfolding io_targets.simps by force
    then show "io_targets A io (initial A) = {t1}"
      using observable_io_targets[OF \<open>observable A\<close>]
      by (metis \<open>io \<in> L A\<close> singletonD) 
  qed

  show "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets A io (initial A) = {t2}"
  proof -
    assume "io \<in> LS M q2 - LS M q1"
    
    then have "p_io p \<in> LS M q2 - LS M q1"
      using \<open>p_io p = io\<close> by auto
    then have "target (initial A) p = t2"
      using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close>
      by blast 
    then have "t2 \<in> io_targets A io (initial A)"
      using \<open>path A (initial A) p\<close> \<open>p_io p = io\<close> unfolding io_targets.simps by force
    then show "io_targets A io (initial A) = {t2}"
      using observable_io_targets[OF \<open>observable A\<close>]
      by (metis \<open>io \<in> L A\<close> singletonD) 
  qed

  show "io \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> io_targets A io (initial A) \<inter> {t1,t2} = {}"
  proof -
    assume "io \<in> LS M q1 \<inter> LS M q2"
    
    then have "p_io p \<in> LS M q1 \<inter> LS M q2"
      using \<open>p_io p = io\<close> by auto
    then have "target (initial A) p \<noteq> t1" and "target (initial A) p \<noteq> t2"
      using pt1[OF \<open>path A (initial A) p\<close>] pt2[OF \<open>path A (initial A) p\<close>] pt3[OF \<open>path A (initial A) p\<close>] \<open>t1 \<noteq> t2\<close>
      by blast+ 
    moreover have "target (initial A) p \<in> io_targets A io (initial A)"
      using \<open>path A (initial A) p\<close> \<open>p_io p = io\<close> unfolding io_targets.simps by force
    ultimately show "io_targets A io (initial A) \<inter> {t1,t2} = {}"
      using observable_io_targets[OF \<open>observable A\<close> \<open>io \<in> L A\<close>]
      by (metis (no_types, opaque_lifting) inf_bot_left insert_disjoint(2) insert_iff singletonD) 
  qed

  show "io \<in> LS M q1 \<union> LS M q2"
    using separator_path_targets(4)[OF assms(1) \<open>path A (initial A) p\<close>] \<open>p_io p = io\<close> by auto
qed


lemma is_separator_sym :
  "is_separator M q1 q2 A t1 t2 \<Longrightarrow> is_separator M q2 q1 A t2 t1"
  unfolding is_separator_def Int_commute[of "LS M q2" "LS M q1"] by meson 


lemma state_separator_from_canonical_separator_is_separator :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M" 
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "is_separator M q1 q2 A (Inr q1) (Inr q2)"
proof -
  let ?C = "canonical_separator M q1 q2"
  have "observable ?C"
    using canonical_separator_observable[OF assms(2,3,4)] by assumption

  have "is_submachine A ?C" 
  and   p1: "single_input A"
  and   p2: "acyclic A"
  and   p4: "deadlock_state A (Inr q1)"
  and   p5: "deadlock_state A (Inr q2)"
  and   p6: "((Inr q1) \<in> reachable_states A)"
  and   p7: "((Inr q2) \<in> reachable_states A)"
  and   "\<And> q . q \<in> reachable_states A \<Longrightarrow> q \<noteq> Inr q1 \<Longrightarrow> q \<noteq> Inr q2 \<Longrightarrow> (isl q \<and> \<not> deadlock_state A q)"
  and   compl: "\<And> q x t . q \<in> reachable_states A \<Longrightarrow> x \<in> (inputs M) \<Longrightarrow> (\<exists> t \<in> transitions A . t_source t = q \<and> t_input t = x) \<Longrightarrow> t \<in> transitions ?C \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow> t \<in> transitions A"
    using is_state_separator_from_canonical_separator_simps[OF assms(1)]
    unfolding canonical_separator_simps[OF assms(3,4)]
    by blast+

  have p3: "observable A" 
    using state_separator_from_canonical_separator_observable[OF assms(1-4)] by assumption

  have p8: "(\<forall>t\<in>reachable_states A. t \<noteq> Inr q1 \<and> t \<noteq> Inr q2 \<longrightarrow> \<not> deadlock_state A t)"
    using \<open>\<And> q . q \<in> reachable_states A \<Longrightarrow> q \<noteq> Inr q1 \<Longrightarrow> q \<noteq> Inr q2 \<Longrightarrow> (isl q \<and> \<not> deadlock_state A q)\<close> by simp

  have "\<And> io . io \<in> L A \<Longrightarrow> 
        (io \<in> LS M q1 - LS M q2 \<longrightarrow> io_targets A io (initial A) = {Inr q1}) \<and>
        (io \<in> LS M q2 - LS M q1 \<longrightarrow> io_targets A io (initial A) = {Inr q2}) \<and>
        (io \<in> LS M q1 \<inter> LS M q2 \<longrightarrow> io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}) \<and>
        (\<forall>x yq yt. io @ [(x, yq)] \<in> LS M q1 \<and> io @ [(x, yt)] \<in> LS A (initial A) \<longrightarrow> io @ [(x, yq)] \<in> LS A (initial A)) \<and>
        (\<forall>x yq2 yt. io @ [(x, yq2)] \<in> LS M q2 \<and> io @ [(x, yt)] \<in> LS A (initial A) \<longrightarrow> io @ [(x, yq2)] \<in> LS A (initial A))"
  proof -
    fix io assume "io \<in> L A"

    have "io \<in> LS M q1 - LS M q2 \<Longrightarrow> io_targets A io (initial A) = {Inr q1}"
      using state_separator_from_canonical_separator_language_target(1)[OF assms(1) \<open>io \<in> L A\<close> assms(2,3,4,5)] by assumption
    moreover have "io \<in> LS M q2 - LS M q1 \<Longrightarrow> io_targets A io (initial A) = {Inr q2}"
      using state_separator_from_canonical_separator_language_target(2)[OF assms(1) \<open>io \<in> L A\<close> assms(2,3,4,5)] by assumption
    moreover have "io \<in> LS M q1 \<inter> LS M q2 \<Longrightarrow> io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}"
      using state_separator_from_canonical_separator_language_target(3)[OF assms(1) \<open>io \<in> L A\<close> assms(2,3,4,5)] by assumption
    moreover have "\<And> x yq yt. io @ [(x, yq)] \<in> LS M q1 \<Longrightarrow> io @ [(x, yt)] \<in> L A \<Longrightarrow> io @ [(x, yq)] \<in> L A"
    proof -
      fix x yq yt assume "io @ [(x, yq)] \<in> LS M q1" and "io @ [(x, yt)] \<in> L A"

      obtain pA tA where "path A (initial A) (pA@[tA])" and "p_io (pA@[tA]) = io @ [(x, yt)]"
        using language_initial_path_append_transition[OF \<open>io @ [(x, yt)] \<in> L A\<close>] by blast
      then have "path A (initial A) pA" and "p_io pA = io"
        by auto
      then have "path ?C (initial ?C) pA"
        using submachine_path_initial[OF \<open>is_submachine A ?C\<close>] by auto

      obtain p1 t1 where "path M q1 (p1@[t1])" and "p_io (p1@[t1]) = io @ [(x, yq)]"
        using language_path_append_transition[OF \<open>io @ [(x, yq)] \<in> LS M q1\<close>] by blast
      then have "path M q1 p1" and "p_io p1 = io" and "t1 \<in> transitions M" and "t_input t1 = x" and "t_output t1 = yq" and "t_source t1 = target q1 p1"
        by auto

      let ?q = "target (initial A) pA"
      have "?q \<in> states A"
        using path_target_is_state \<open>path A (initial A) (pA@[tA])\<close> by auto
      have "?q \<in> reachable_states A"
        using \<open>path A (initial A) pA\<close> reachable_states_intro by blast

      have "tA \<in> transitions A" and "t_input tA = x" and "t_output tA = yt" and "t_source tA = target (initial A) pA"
        using \<open>path A (initial A) (pA@[tA])\<close> \<open>p_io (pA@[tA]) = io @ [(x, yt)]\<close> by auto
      then have "x \<in> (inputs M)"
        using \<open>is_submachine A ?C\<close> 
        unfolding is_submachine.simps canonical_separator_simps[OF assms(3,4)] by auto
      
      have "\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x"
        using \<open>tA \<in> transitions A\<close> \<open>t_input tA = x\<close> \<open>t_source tA = target (initial A) pA\<close> by blast

      have "io \<in> LS M q2"
        using submachine_language[OF \<open>is_submachine A ?C\<close>] \<open>io @ [(x, yt)] \<in> L A\<close> 
        using canonical_separator_language_prefix[OF _ assms(3,4,2,5), of io "(x,yt)"] by blast
      then obtain p2 where "path M q2 p2" and "p_io p2 = io"
        by auto
      


      show "io @ [(x, yq)] \<in> L A" 
      proof (cases "\<exists> t2 \<in> transitions M . t_source t2 = target q2 p2 \<and> t_input t2 = x \<and> t_output t2 = yq")
        case True
        then obtain t2 where "t2 \<in> transitions M" and "t_source t2 = target q2 p2" and "t_input t2 = x" and "t_output t2 = yq"
          by blast
        then have "path M q2 (p2@[t2])" and "p_io (p2@[t2]) = io@[(x,yq)]"
          using path_append_transition[OF \<open>path M q2 p2\<close>] \<open>p_io p2 = io\<close> by auto
        then have "io @ [(x, yq)] \<in> LS M q2"
          unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
        then have "io@[(x,yq)] \<in> L ?C"
          using  canonical_separator_language_intersection[OF \<open>io @ [(x, yq)] \<in> LS M q1\<close> _ assms(3,4)] by blast
        
        obtain pA' tA' where "path ?C (initial ?C) (pA'@[tA'])" and "p_io (pA'@[tA']) = io@[(x,yq)]"
          using language_initial_path_append_transition[OF \<open>io @ [(x, yq)] \<in> L ?C\<close>] by blast
        then have "path ?C (initial ?C) pA'" and "p_io pA' = io" and "tA' \<in> transitions ?C" and "t_source tA' = target (initial ?C) pA'" and "t_input tA' = x" and "t_output tA' = yq"
          by auto

        have "pA = pA'"
          using observable_path_unique[OF \<open>observable ?C\<close> \<open>path ?C (initial ?C) pA'\<close> \<open>path ?C (initial ?C) pA\<close>]
          using \<open>p_io pA' = io\<close> \<open>p_io pA = io\<close> by auto
        then have "t_source tA' = target (initial A) pA"
          using \<open>t_source tA' = target (initial ?C) pA'\<close>
          using is_state_separator_from_canonical_separator_initial[OF assms(1,3,4)]
          using canonical_separator_initial[OF assms(3,4)] by fastforce


        have "tA' \<in> transitions A"
          using compl[OF \<open>?q \<in> reachable_states A\<close> \<open>x \<in> (inputs M)\<close> \<open>\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x\<close> \<open>tA' \<in> transitions ?C\<close> \<open>t_source tA' = target (initial A) pA\<close> \<open>t_input tA' = x\<close>] by assumption
        then have "path A (initial A) (pA@[tA'])" 
          using \<open>path A (initial A) pA\<close> \<open>t_source tA' = target (initial A) pA\<close> using path_append_transition by metis
        moreover have "p_io (pA@[tA']) = io@[(x,yq)]"
          using \<open>t_input tA' = x\<close> \<open>t_output tA' = yq\<close> \<open>p_io pA = io\<close> by auto
        
        ultimately show ?thesis 
          using language_state_containment
          by (metis (mono_tags, lifting)) 
          
      next
        case False

        let ?P = "product (from_FSM M q1) (from_FSM M q2)"
        let ?qq = "(target q1 p1, target q2 p2)"
        let ?tA = "(Inl (target q1 p1, target q2 p2), x, yq, Inr q1)"

        have "path (from_FSM M q1) (initial (from_FSM M q1)) p1" 
          using from_FSM_path_initial[OF \<open>q1 \<in> states M\<close>] \<open>path M q1 p1\<close> by auto
        have "path (from_FSM M q2) (initial (from_FSM M q2)) p2" 
          using from_FSM_path_initial[OF \<open>q2 \<in> states M\<close>] \<open>path M q2 p2\<close> by auto
        have "p_io p1 = p_io p2"
          using \<open>p_io p1 = io\<close> \<open>p_io p2 = io\<close> by auto
        
        have "?qq \<in> states ?P" 
          using reachable_states_intro[OF product_path_from_paths(1)[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close> \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close> \<open>p_io p1 = p_io p2\<close>]]
          unfolding product_path_from_paths(2)[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close> \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close> \<open>p_io p1 = p_io p2\<close>] from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)] 
          using reachable_state_is_state
          by metis
        moreover have "\<exists>q'. (target q1 p1, x, yq, q') \<in> FSM.transitions M"
          using \<open>t1 \<in> FSM.transitions M\<close> \<open>t_input t1 = x\<close> \<open>t_output t1 = yq\<close> \<open>t_source t1 = target q1 p1\<close>
          by (metis prod.collapse) 
        moreover have "\<not>(\<exists>q'. (target q2 p2, x, yq, q') \<in> FSM.transitions M)"
          using \<open>t1 \<in> FSM.transitions M\<close> \<open>t_input t1 = x\<close> \<open>t_output t1 = yq\<close> \<open>t_source t1 = target q1 p1\<close> False
          by fastforce
        ultimately have "?tA \<in> (distinguishing_transitions_left M q1 q2)"
          unfolding distinguishing_transitions_left_def 
          by blast

        then have "(Inl (target q1 p1, target q2 p2), x, yq, Inr q1) \<in> transitions ?C"
          using canonical_separator_distinguishing_transitions_left_containment[OF _ assms(3,4)] by metis

        let ?pP = "zip_path p1 p2"
        let ?pC = "map shift_Inl ?pP"
        have "path ?P (initial ?P) ?pP" 
        and  "target (initial ?P) ?pP = (target q1 p1, target q2 p2)"
          using  product_path_from_paths[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close>
                                            \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close>
                                            \<open>p_io p1 = p_io p2\<close>]
          using assms(3,4) by auto

        have "length p1 = length p2"
          using \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq by blast 
        then have "p_io ?pP = io"
          using \<open>p_io p1 = io\<close>  by (induction p1 p2 arbitrary: io rule: list_induct2; auto)
        

        have "path ?C (initial ?C) ?pC"
          using canonical_separator_path_shift[OF assms(3,4)] \<open>path ?P (initial ?P) ?pP\<close> by simp

        have "target (initial ?C) ?pC = Inl (target q1 p1, target q2 p2)"
          using path_map_target[of Inl "initial ?P" Inl id id ?pP ]
          using \<open>target (initial ?P) ?pP = (target q1 p1, target q2 p2)\<close>
          unfolding canonical_separator_simps[OF assms(3,4)] product_simps from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)]
          by fastforce
        
        have "p_io ?pC = io"
          using \<open>p_io ?pP = io\<close> by auto
        have "p_io pA = p_io ?pC"
          unfolding \<open>p_io ?pC = io\<close>
          using \<open>p_io pA = io\<close> by assumption
  
        then have "?pC = pA"
          using observable_path_unique[OF \<open>observable ?C\<close> \<open>path ?C (initial ?C) pA\<close> \<open>path ?C (initial ?C) ?pC\<close>] by auto
        then have "t_source ?tA = target (initial A) pA"
          using \<open>target (initial ?C) ?pC = Inl (target q1 p1, target q2 p2)\<close>
          unfolding is_state_separator_from_canonical_separator_initial[OF assms(1,3,4)]
                    canonical_separator_simps[OF assms(3,4)] by force

        have "?tA \<in> transitions A"
          using compl[OF \<open>?q \<in> reachable_states A\<close> \<open>x \<in> (inputs M)\<close> \<open>\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x\<close> \<open>?tA \<in> transitions ?C\<close> \<open>t_source ?tA = target (initial A) pA\<close> ]
          unfolding snd_conv fst_conv by simp

        have *: "path A (initial A) (pA@[?tA])"
          using path_append_transition[OF \<open>path A (initial A) pA\<close> \<open>?tA \<in> transitions A\<close>  \<open>t_source ?tA = target (initial A) pA\<close>] by assumption

        have **: "p_io (pA@[?tA]) = io@[(x,yq)]"
          using \<open>p_io pA = io\<close> by auto

        show ?thesis 
          using language_state_containment[OF * **] by assumption
      qed
    qed

    
    moreover have "\<And> x yq yt. io @ [(x, yq)] \<in> LS M q2 \<Longrightarrow> io @ [(x, yt)] \<in> L A \<Longrightarrow> io @ [(x, yq)] \<in> L A"
    proof -
      fix x yq yt assume "io @ [(x, yq)] \<in> LS M q2" and "io @ [(x, yt)] \<in> L A"

      obtain pA tA where "path A (initial A) (pA@[tA])" and "p_io (pA@[tA]) = io @ [(x, yt)]"
        using language_initial_path_append_transition[OF \<open>io @ [(x, yt)] \<in> L A\<close>] by blast
      then have "path A (initial A) pA" and "p_io pA = io"
        by auto
      then have "path ?C (initial ?C) pA"
        using submachine_path_initial[OF \<open>is_submachine A ?C\<close>] by auto

      obtain p2 t2 where "path M q2 (p2@[t2])" and "p_io (p2@[t2]) = io @ [(x, yq)]"
        using language_path_append_transition[OF \<open>io @ [(x, yq)] \<in> LS M q2\<close>] by blast
      then have "path M q2 p2" and "p_io p2 = io" and "t2 \<in> transitions M" and "t_input t2 = x" and "t_output t2 = yq" and "t_source t2 = target q2 p2"
        by auto

      let ?q = "target (initial A) pA"
      have "?q \<in> states A"
        using path_target_is_state \<open>path A (initial A) (pA@[tA])\<close> by auto

      have "tA \<in> transitions A" and "t_input tA = x" and "t_output tA = yt" and "t_source tA = target (initial A) pA"
        using \<open>path A (initial A) (pA@[tA])\<close> \<open>p_io (pA@[tA]) = io @ [(x, yt)]\<close> by auto
      then have "x \<in> (inputs M)"
        using \<open>is_submachine A ?C\<close> 
        unfolding is_submachine.simps canonical_separator_simps[OF assms(3,4)] by auto
      
      have "\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x"
        using \<open>tA \<in> transitions A\<close> \<open>t_input tA = x\<close> \<open>t_source tA = target (initial A) pA\<close> by blast

      have "io \<in> LS M q1"
        using submachine_language[OF \<open>is_submachine A ?C\<close>] \<open>io @ [(x, yt)] \<in> L A\<close> 
        using canonical_separator_language_prefix[OF _ assms(3,4,2,5), of io "(x,yt)"] by blast
      then obtain p1 where "path M q1 p1" and "p_io p1 = io"
        by auto
      


      show "io @ [(x, yq)] \<in> L A" 
      proof (cases "\<exists> t1 \<in> transitions M . t_source t1 = target q1 p1 \<and> t_input t1 = x \<and> t_output t1 = yq")
        case True
        then obtain t1 where "t1 \<in> transitions M" and "t_source t1 = target q1 p1" and "t_input t1 = x" and "t_output t1 = yq"
          by blast
        then have "path M q1 (p1@[t1])" and "p_io (p1@[t1]) = io@[(x,yq)]"
          using path_append_transition[OF \<open>path M q1 p1\<close>] \<open>p_io p1 = io\<close> by auto
        then have "io @ [(x, yq)] \<in> LS M q1"
          unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
        then have "io@[(x,yq)] \<in> L ?C"
          using  canonical_separator_language_intersection[OF _ \<open>io @ [(x, yq)] \<in> LS M q2\<close> assms(3,4)] by blast
        
        obtain pA' tA' where "path ?C (initial ?C) (pA'@[tA'])" and "p_io (pA'@[tA']) = io@[(x,yq)]"
          using language_initial_path_append_transition[OF \<open>io @ [(x, yq)] \<in> L ?C\<close>] by blast
        then have "path ?C (initial ?C) pA'" and "p_io pA' = io" and "tA' \<in> transitions ?C" and "t_source tA' = target (initial ?C) pA'" and "t_input tA' = x" and "t_output tA' = yq"
          by auto

        have "pA = pA'"
          using observable_path_unique[OF \<open>observable ?C\<close> \<open>path ?C (initial ?C) pA'\<close> \<open>path ?C (initial ?C) pA\<close>]
          using \<open>p_io pA' = io\<close> \<open>p_io pA = io\<close> by auto
        then have "t_source tA' = target (initial A) pA"
          using \<open>t_source tA' = target (initial ?C) pA'\<close>
          using is_state_separator_from_canonical_separator_initial[OF assms(1,3,4)] 
          unfolding canonical_separator_simps[OF assms(3,4)] by auto

        have "?q \<in> reachable_states A"
          using \<open>path A (initial A) pA\<close> reachable_states_intro by blast

        have "tA' \<in> transitions A"
          using compl[OF \<open>?q \<in> reachable_states A\<close> \<open>x \<in> (inputs M)\<close> \<open>\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x\<close> \<open>tA' \<in> transitions ?C\<close> \<open>t_source tA' = target (initial A) pA\<close> \<open>t_input tA' = x\<close>] by assumption
        then have "path A (initial A) (pA@[tA'])" 
          using \<open>path A (initial A) pA\<close> \<open>t_source tA' = target (initial A) pA\<close> using path_append_transition by metis
        moreover have "p_io (pA@[tA']) = io@[(x,yq)]"
          using \<open>t_input tA' = x\<close> \<open>t_output tA' = yq\<close> \<open>p_io pA = io\<close> by auto
        
        ultimately show ?thesis 
          using language_state_containment
          by (metis (mono_tags, lifting)) 
          
      next
        case False

        let ?P = "product (from_FSM M q1) (from_FSM M q2)"
        let ?qq = "(target q1 p1, target q2 p2)"
        let ?tA = "(Inl (target q1 p1, target q2 p2), x, yq, Inr q2)"

        have "path (from_FSM M q1) (initial (from_FSM M q1)) p1" 
          using from_FSM_path_initial[OF \<open>q1 \<in> states M\<close>] \<open>path M q1 p1\<close> by auto
        have "path (from_FSM M q2) (initial (from_FSM M q2)) p2" 
          using from_FSM_path_initial[OF \<open>q2 \<in> states M\<close>] \<open>path M q2 p2\<close> by auto
        have "p_io p1 = p_io p2"
          using \<open>p_io p1 = io\<close> \<open>p_io p2 = io\<close> by auto

        have "?qq \<in> states ?P"
          using reachable_states_intro[OF product_path_from_paths(1)[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close> \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close> \<open>p_io p1 = p_io p2\<close>]]
          unfolding product_path_from_paths(2)[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close> \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close> \<open>p_io p1 = p_io p2\<close>] from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)] 
          using reachable_state_is_state by metis
        moreover have "\<exists>q'. (target q2 p2, x, yq, q') \<in> FSM.transitions M"
          using \<open>t2 \<in> FSM.transitions M\<close> \<open>t_input t2 = x\<close> \<open>t_output t2 = yq\<close> \<open>t_source t2 = target q2 p2\<close>
          by (metis prod.collapse) 
        moreover have "\<not>(\<exists>q'. (target q1 p1, x, yq, q') \<in> FSM.transitions M)"
          using \<open>t2 \<in> FSM.transitions M\<close> \<open>t_input t2 = x\<close> \<open>t_output t2 = yq\<close> \<open>t_source t2 = target q2 p2\<close> False
          by fastforce
        ultimately have "?tA \<in> (distinguishing_transitions_right M q1 q2)"
          unfolding distinguishing_transitions_right_def 
          by blast

        then have "?tA \<in> transitions ?C"
          using canonical_separator_distinguishing_transitions_right_containment[OF _ assms(3,4)] by metis

        let ?pP = "zip_path p1 p2"
        let ?pC = "map shift_Inl ?pP"
        have "path ?P (initial ?P) ?pP" 
        and  "target (initial ?P) ?pP = (target q1 p1, target q2 p2)"
          using  product_path_from_paths[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) p1\<close>
                                            \<open>path (from_FSM M q2) (initial (from_FSM M q2)) p2\<close>
                                            \<open>p_io p1 = p_io p2\<close>]
          using assms(3,4) by auto

        have "length p1 = length p2"
          using \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq by blast 
        then have "p_io ?pP = io"
          using \<open>p_io p1 = io\<close>  by (induction p1 p2 arbitrary: io rule: list_induct2; auto)
        

        have "path ?C (initial ?C) ?pC"
          using canonical_separator_path_shift[OF assms(3,4)] \<open>path ?P (initial ?P) ?pP\<close> by simp

        have "target (initial ?C) ?pC = Inl (target q1 p1, target q2 p2)"
          using path_map_target[of Inl "initial ?P" Inl id id ?pP ]
          using \<open>target (initial ?P) ?pP = (target q1 p1, target q2 p2)\<close>
          unfolding canonical_separator_simps[OF assms(3,4)] product_simps from_FSM_simps[OF assms(3)] from_FSM_simps[OF assms(4)] by force
        
        have "p_io ?pC = io"
          using \<open>p_io ?pP = io\<close> by auto
        have "p_io pA = p_io ?pC"
          unfolding \<open>p_io ?pC = io\<close>
          using \<open>p_io pA = io\<close> by assumption
  
        then have "?pC = pA"
          using observable_path_unique[OF \<open>observable ?C\<close> \<open>path ?C (initial ?C) pA\<close> \<open>path ?C (initial ?C) ?pC\<close>] by auto
        then have "t_source ?tA = target (initial A) pA"
          using \<open>target (initial ?C) ?pC = Inl (target q1 p1, target q2 p2)\<close>
          unfolding is_state_separator_from_canonical_separator_initial[OF assms(1,3,4)]
                    canonical_separator_simps[OF assms(3,4)] by force

        have "?q \<in> reachable_states A"
          using \<open>path A (initial A) pA\<close> reachable_states_intro by blast
        have "?tA \<in> transitions A"
          using compl[OF \<open>?q \<in> reachable_states A\<close> \<open>x \<in> (inputs M)\<close> \<open>\<exists>t\<in>(transitions A). t_source t = target (initial A) pA \<and> t_input t = x\<close> \<open>?tA \<in> transitions ?C\<close> \<open>t_source ?tA = target (initial A) pA\<close> ]
          unfolding snd_conv fst_conv by simp

        have *: "path A (initial A) (pA@[?tA])"
          using path_append_transition[OF \<open>path A (initial A) pA\<close> \<open>?tA \<in> transitions A\<close>  \<open>t_source ?tA = target (initial A) pA\<close>] by assumption

        have **: "p_io (pA@[?tA]) = io@[(x,yq)]"
          using \<open>p_io pA = io\<close> by auto

        show ?thesis 
          using language_state_containment[OF * **] by assumption
      qed
    qed


    ultimately show "(io \<in> LS M q1 - LS M q2 \<longrightarrow> io_targets A io (initial A) = {Inr q1}) \<and>
        (io \<in> LS M q2 - LS M q1 \<longrightarrow> io_targets A io (initial A) = {Inr q2}) \<and>
        (io \<in> LS M q1 \<inter> LS M q2 \<longrightarrow> io_targets A io (initial A) \<inter> {Inr q1, Inr q2} = {}) \<and>
        (\<forall>x yq yt. io @ [(x, yq)] \<in> LS M q1 \<and> io @ [(x, yt)] \<in> LS A (initial A) \<longrightarrow> io @ [(x, yq)] \<in> LS A (initial A)) \<and>
        (\<forall>x yq2 yt. io @ [(x, yq2)] \<in> LS M q2 \<and> io @ [(x, yt)] \<in> LS A (initial A) \<longrightarrow> io @ [(x, yq2)] \<in> LS A (initial A))" 
      by blast 
  qed

  moreover have "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = Inr q1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2"
    using canonical_separator_maximal_path_distinguishes_left[OF assms(1) _ _ \<open>observable M\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>q1 \<noteq> q2\<close>] by blast
  moreover have "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p = Inr q2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1"
    using canonical_separator_maximal_path_distinguishes_right[OF assms(1) _ _ \<open>observable M\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>q1 \<noteq> q2\<close>] by blast
  moreover have "\<And> p . path A (initial A) p \<Longrightarrow> target (initial A) p \<noteq> Inr q1 \<Longrightarrow> target (initial A) p \<noteq> Inr q2 \<Longrightarrow> p_io p \<in> LS M q1 \<inter> LS M q2"
  proof -
    fix p assume "path A (initial A) p" and "target (initial A) p \<noteq> Inr q1" and "target (initial A) p \<noteq> Inr q2"

    have "path ?C (initial ?C) p"
      using submachine_path_initial[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)] \<open>path A (initial A) p\<close>] by assumption

    have "target (initial ?C) p \<noteq> Inr q1" and "target (initial ?C) p \<noteq> Inr q2"
      using \<open>target (initial A) p \<noteq> Inr q1\<close> \<open>target (initial A) p \<noteq> Inr q2\<close>
      unfolding is_state_separator_from_canonical_separator_initial[OF assms(1,3,4)] canonical_separator_initial[OF assms(3,4)] by blast+

    then have "isl (target (initial ?C) p)"
      using canonical_separator_path_initial(4)[OF \<open>path ?C (initial ?C) p\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>observable M\<close> \<open>q1 \<noteq> q2\<close>]
      by auto 

    then show "p_io p \<in> LS M q1 \<inter> LS M q2"
      using \<open>path ?C (initial ?C) p\<close> canonical_separator_path_targets_language(1)[OF _ \<open>observable M\<close> \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>q1 \<noteq> q2\<close>] 
      by auto
  qed

  moreover have "(inputs A) \<subseteq> (inputs M)"
    using \<open>is_submachine A ?C\<close>
    unfolding is_submachine.simps canonical_separator_simps[OF assms(3,4)] by auto

  ultimately show ?thesis
    unfolding is_separator_def
    using p1 p2 p3 p4 p5 p6 p7 p8 \<open>q1 \<noteq> q2\<close>
    by (meson sum.simps(2))
qed

  
lemma is_separator_separated_state_is_state :
  assumes "is_separator M q1 q2 A t1 t2"
  shows "q1 \<in> states M" and "q2 \<in> states M"
proof -
  have "initial A \<noteq> t1"
    using separator_initial[OF assms(1)] by blast

  have "t1 \<in> reachable_states A"
  and  "\<And> p . path A (FSM.initial A) p \<Longrightarrow> target (FSM.initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2"
  and  "t2 \<in> reachable_states A"
  and  "\<And> p . path A (FSM.initial A) p \<Longrightarrow> target (FSM.initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1"
    using is_separator_simps[OF assms(1)] 
    by blast+

  obtain p1 where "path A (FSM.initial A) p1" and "target (FSM.initial A) p1 = t1"
    using \<open>t1 \<in> reachable_states A\<close> unfolding reachable_states_def by auto
  then have "p_io p1 \<in> LS M q1 - LS M q2"
    using \<open>\<And> p . path A (FSM.initial A) p \<Longrightarrow> target (FSM.initial A) p = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2\<close> 
    by blast
  then show "q1 \<in> states M" unfolding LS.simps
    using path_begin_state by fastforce 

  obtain p2 where "path A (FSM.initial A) p2" and "target (FSM.initial A) p2 = t2"
    using \<open>t2 \<in> reachable_states A\<close> unfolding reachable_states_def by auto
  then have "p_io p2 \<in> LS M q2 - LS M q1"
    using \<open>\<And> p . path A (FSM.initial A) p \<Longrightarrow> target (FSM.initial A) p = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1\<close> 
    by blast
  then show "q2 \<in> states M" unfolding LS.simps
    using path_begin_state by fastforce 
qed

end