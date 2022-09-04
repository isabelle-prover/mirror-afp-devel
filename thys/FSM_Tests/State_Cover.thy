section \<open>State Cover\<close>

text \<open>This theory introduces a simple depth-first strategy for computing state covers.\<close>


theory State_Cover
imports FSM 
begin

subsection \<open>Basic Definitions\<close>

type_synonym ('a,'b) state_cover = "('a \<times> 'b) list set"
type_synonym ('a,'b,'c) state_cover_assignment = "'a \<Rightarrow> ('b \<times> 'c) list"

fun is_state_cover :: "('a,'b,'c) fsm \<Rightarrow> ('b,'c) state_cover \<Rightarrow> bool" where
  "is_state_cover M SC = ([] \<in> SC \<and> (\<forall> q \<in> reachable_states M . \<exists> io \<in> SC . q \<in> io_targets M io (initial M)))"

fun is_state_cover_assignment :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> bool" where
  "is_state_cover_assignment M f = (f (initial M) = [] \<and> (\<forall> q \<in> reachable_states M . q \<in> io_targets M (f q) (initial M)))"

lemma state_cover_assignment_from_state_cover :
  assumes "is_state_cover M SC"
obtains f where "is_state_cover_assignment M f"
            and "\<And> q . q \<in> reachable_states M \<Longrightarrow> f q \<in> SC"
proof -
  define f where f: "f = (\<lambda> q . (if q = initial M then [] else (SOME io . io \<in> SC \<and> q \<in> io_targets M io (initial M))))"

  have "f (initial M) = []"
    using f by auto
  moreover have "\<And> q . q \<in> reachable_states M \<Longrightarrow> f q \<in> SC \<and> q \<in> io_targets M (f q) (initial M)"
  proof -
    fix q assume "q \<in> reachable_states M"
    show "f q \<in> SC \<and> q \<in> io_targets M (f q) (initial M)"
    proof (cases "q = initial M")
      case True
      have "q \<in> io_targets M (f q) (FSM.initial M)"
        unfolding True \<open>f (initial M) = []\<close> by auto
      then show ?thesis
        using True assms \<open>f (initial M) = []\<close> by auto         
    next
      case False
      then have "f q = (SOME io . io \<in> SC \<and> q \<in> io_targets M io (initial M))"
        using f by auto
      moreover have "\<exists> io . io \<in> SC \<and> q \<in> io_targets M io (initial M)"
        using assms \<open>q \<in> reachable_states M\<close>
        by (meson is_state_cover.simps)     
      ultimately show ?thesis
        by (metis (no_types, lifting) someI_ex)         
    qed
  qed
  ultimately show ?thesis using that[of f]
    by (meson is_state_cover_assignment.elims(3))
qed

lemma is_state_cover_assignment_language :
  assumes "is_state_cover_assignment M V"
  and     "q \<in> reachable_states M"
shows "V q \<in> L M"
  using assms io_targets_language
  by (metis is_state_cover_assignment.simps) 

lemma is_state_cover_assignment_observable_after :
  assumes "observable M"
  and     "is_state_cover_assignment M V"
  and     "q \<in> reachable_states M"
shows "after_initial M (V q) = q"
proof -
  have "q \<in> io_targets M (V q) (initial M)"
    using assms(2,3)
    by auto 
  then have "io_targets M (V q) (initial M) = {q}"
    using observable_io_targets[OF assms(1) io_targets_language[OF \<open>q \<in> io_targets M (V q) (initial M)\<close>]]
    by (metis singletonD) 

  then obtain p where "path M (initial M) p" and "p_io p = V q" and "target (initial M) p = q"
    unfolding io_targets.simps
    by blast
  then show "after_initial M (V q) = q"
    using after_path[OF assms(1), of "initial M" p]
    by simp
qed

lemma non_initialized_state_cover_assignment_from_non_initialized_state_cover :
  assumes "\<And> q . q \<in> reachable_states M \<Longrightarrow> \<exists> io \<in> L M \<inter> SC . q \<in> io_targets M io (initial M)"
obtains f where "\<And> q . q \<in> reachable_states M \<Longrightarrow> q \<in> io_targets M (f q) (initial M)"
            and "\<And> q . q \<in> reachable_states M \<Longrightarrow> f q \<in> L M \<inter>  SC"
proof -
  define f where f: "f = (\<lambda> q . (SOME io . io \<in> L M \<inter> SC \<and> q \<in> io_targets M io (initial M)))"

  have "\<And> q . q \<in> reachable_states M \<Longrightarrow> f q \<in> L M \<inter>  SC \<and> q \<in> io_targets M (f q) (initial M)"
  proof -
    fix q assume "q \<in> reachable_states M"
    show "f q \<in> L M \<inter> SC \<and> q \<in> io_targets M (f q) (initial M)"
    proof -
      have "f q = (SOME io . io \<in> L M \<inter> SC \<and> q \<in> io_targets M io (initial M))"
        using f by auto
      moreover have "\<exists> io . io \<in> L M \<inter> SC \<and> q \<in> io_targets M io (initial M)"
        using assms \<open>q \<in> reachable_states M\<close>
        by (meson Int_iff)    
      ultimately show ?thesis
        by (metis (no_types, lifting) someI_ex)         
    qed
  qed
  then show ?thesis using that[of f]
    by blast
qed

lemma state_cover_assignment_inj :
  assumes "is_state_cover_assignment M V"
  and     "observable M"
  and     "q1 \<in> reachable_states M"
  and     "q2 \<in> reachable_states M"
  and     "q1 \<noteq> q2"
shows "V q1 \<noteq> V q2"
proof (rule ccontr)
  assume "\<not> V q1 \<noteq> V q2" 

  then have "io_targets M (V q1) (initial M) = io_targets M (V q2) (initial M)"
    by auto
  then have "q1 = q2"
    using assms(2)
  proof -
    have f1: "\<forall>a f. a \<notin> FSM.states (f::('a, 'b, 'c) fsm) \<or> FSM.initial (FSM.from_FSM f a) = a"
      by (meson from_FSM_simps(1))
    obtain ff :: "('a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm" and pps :: "('a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list" where
      f2: "M = ff V M \<and> V = pps V M \<and> pps V M (FSM.initial (ff V M)) = [] \<and> (\<forall>a. a \<notin> reachable_states (ff V M) \<or> a \<in> io_targets (ff V M) (pps V M a) (FSM.initial (ff V M)))"
      using assms(1) by fastforce
    then have f3: "q2 \<in> FSM.states (ff V M)"
      by (simp add: \<open>q2 \<in> reachable_states M\<close> reachable_state_is_state)
    then have f4: "\<exists>ps. FSM.initial (FSM.from_FSM M q2) = target (FSM.initial (ff V M)) ps \<and> path (ff V M) (FSM.initial (ff V M)) ps \<and> p_io ps = V q2"
      using f2 \<open>q2 \<in> reachable_states M\<close> assms(1) by auto
    have "q1 \<in> {target (FSM.initial M) ps |ps. path M (FSM.initial M) ps \<and> p_io ps = V q2}"
      by (metis (no_types) \<open>io_targets M (V q1) (FSM.initial M) = io_targets M (V q2) (FSM.initial M)\<close> \<open>q1 \<in> reachable_states M\<close> assms(1) io_targets.simps is_state_cover_assignment.simps)
    then have "\<exists>ps. FSM.initial (FSM.from_FSM M q1) = target (FSM.initial (ff V M)) ps \<and> path (ff V M) (FSM.initial (ff V M)) ps \<and> p_io ps = V q2"
      using f2 by (simp add: \<open>q1 \<in> reachable_states M\<close> reachable_state_is_state)
    then show ?thesis
      using f4 f3 f2 f1 by (metis (no_types) \<open>observable M\<close> \<open>q1 \<in> reachable_states M\<close> observable_path_io_target reachable_state_is_state singletonD singletonI)
  qed 
  then show "False"
    using \<open>q1 \<noteq> q2\<close> by blast
qed


lemma state_cover_assignment_card :
  assumes "is_state_cover_assignment M V"
  and     "observable M"
shows "card (V ` reachable_states M) = card (reachable_states M)"
proof -  
  have "inj_on V (reachable_states M)"
    using state_cover_assignment_inj[OF assms] by (meson inj_onI)

  then have "card (reachable_states M) \<le> card (V ` reachable_states M)"
    using fsm_states_finite restrict_to_reachable_states_simps(2)
    by (simp add: card_image) 
  moreover have "card (V ` reachable_states M) \<le> card (reachable_states M)"
    using fsm_states_finite  
    using card_image_le
    by (metis restrict_to_reachable_states_simps(2)) 
  ultimately show ?thesis by simp
qed


lemma state_cover_assignment_language :
  assumes "is_state_cover_assignment M V"
  shows "V ` reachable_states M \<subseteq> L M"
  using assms unfolding is_state_cover_assignment.simps
  using language_io_target_append by fastforce 


fun is_minimal_state_cover :: "('a,'b,'c) fsm \<Rightarrow> ('b,'c) state_cover \<Rightarrow> bool" where
  "is_minimal_state_cover M SC = (\<exists> f . (SC = f ` reachable_states M) \<and> (is_state_cover_assignment M f))"

lemma minimal_state_cover_is_state_cover :
  assumes "is_minimal_state_cover M SC"
  shows "is_state_cover M SC"
proof -
  obtain f where "f (initial M) = []" and "(SC = f ` reachable_states M)" and "(\<And> q . q \<in> reachable_states M \<Longrightarrow> q \<in> io_targets M (f q) (initial M))"
    using assms by auto

  show ?thesis unfolding is_state_cover.simps \<open>(SC = f ` reachable_states M)\<close>
  proof -
    have "f ` FSM.reachable_states M \<subseteq> L M" 
    proof 
      fix io assume "io \<in> f ` FSM.reachable_states M"
      then obtain q where "q \<in> reachable_states M" and "io = f q"
        by blast
      then have "q \<in> io_targets M (f q) (initial M)"
        using \<open>(\<And> q . q \<in> reachable_states M \<Longrightarrow> q \<in> io_targets M (f q) (initial M))\<close> by blast
      then show "io \<in> L M"
        unfolding \<open>io = f q \<close> by force
    qed

    moreover have "\<forall>q\<in>FSM.reachable_states M. \<exists>io\<in>f ` FSM.reachable_states M. q \<in> io_targets M io (FSM.initial M)"
      using \<open>(\<And> q . q \<in> reachable_states M \<Longrightarrow> q \<in> io_targets M (f q) (initial M))\<close> by blast

    ultimately show "[] \<in> f ` FSM.reachable_states M \<and> (\<forall>q\<in>FSM.reachable_states M. \<exists>io\<in>f ` FSM.reachable_states M. q \<in> io_targets M io (FSM.initial M))"
      using \<open>f (initial M) = []\<close> reachable_states_initial by force
  qed
qed

lemma state_cover_assignment_after :
  assumes "observable M" 
  and     "is_state_cover_assignment M V"
  and     "q \<in> reachable_states M"
shows "V q \<in> L M" and "after_initial M (V q) = q" 
proof -
  have "V q \<in> L M \<and> after_initial M (V q) = q"
  using assms(3) proof (induct rule: reachable_states_induct)
    case init
    have "V (FSM.initial M) = []"
      using assms(2) 
      by auto
    then show ?case 
      by auto      
  next
    case (transition t)
    then have "t_target t \<in> reachable_states M"
      using reachable_states_next 
      by metis
    then have "t_target t \<in> io_targets M (V (t_target t)) (FSM.initial M)"
      using assms(2) 
      unfolding is_state_cover_assignment.simps
      by auto
    then obtain p where "path M (initial M) p" and "target (initial M) p = t_target t" and "p_io p = V (t_target t)"
      by auto
    then have "V (t_target t) \<in> L M"
      by force
    then show ?case 
      using after_path[OF assms(1) \<open>path M (initial M) p\<close>]
      unfolding \<open>p_io p = V (t_target t)\<close> \<open>target (initial M) p = t_target t\<close>
      by simp
  qed
  then show "V q \<in> L M" and "after_initial M (V q) = q" 
    by simp+
qed

(* transitions considered covered by a state cover in the SPY and SPYH-Methods *)
definition covered_transitions :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> ('a,'b,'c) transition set" where
  "covered_transitions M V \<alpha> = (let
    ts = the_elem (paths_for_io M (initial M) \<alpha>)
  in
    List.set (filter (\<lambda>t . ((V (t_source t)) @ [(t_input t, t_output t)]) = (V (t_target t))) ts))"


subsection \<open>State Cover Computation\<close>


fun reaching_paths_up_to_depth :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> ('a,'b,'c) path option) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> ('a,'b,'c) path option)" where 
  "reaching_paths_up_to_depth M nexts dones assignment 0 = assignment" |
  "reaching_paths_up_to_depth M nexts dones assignment (Suc k) = (let
      usable_transitions = filter (\<lambda> t . t_source t \<in> nexts \<and> t_target t \<notin> dones \<and> t_target t \<notin> nexts) (transitions_as_list M);
      targets = map t_target usable_transitions;
      transition_choice = Map.empty(targets [\<mapsto>] usable_transitions);
      assignment' = assignment(targets [\<mapsto>] (map (\<lambda>q' . case transition_choice q' of Some t \<Rightarrow> (case assignment (t_source t) of Some p \<Rightarrow> p@[t])) targets));
      nexts' = set targets;
      dones' = nexts \<union> dones
    in reaching_paths_up_to_depth M nexts' dones' assignment' k)"



lemma reaching_paths_up_to_depth_set : 
  assumes "nexts = {q . (\<exists> p . path M (initial M) p \<and> target (initial M) p = q \<and> length p = n) \<and> (\<nexists> p . path M (initial M) p \<and> target (initial M) p = q \<and> length p < n)}"
      and "dones = {q . \<exists> p . path M (initial M) p \<and> target (initial M) p = q \<and> length p < n}"
      and "\<And> q . assignment q = None = (\<nexists>p . path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n)"
      and "\<And> q p . assignment q = Some p \<Longrightarrow> path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n"
      and "dom assignment = nexts \<union> dones"
  shows "((reaching_paths_up_to_depth M nexts dones assignment k) q = None) = (\<nexists>p . path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k)"
    and "((reaching_paths_up_to_depth M nexts dones assignment k) q = Some p) \<Longrightarrow> path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k"
    and "q \<in> nexts \<union> dones \<Longrightarrow> (reaching_paths_up_to_depth M nexts dones assignment k) q = assignment q"
proof -
  have "(((reaching_paths_up_to_depth M nexts dones assignment k) q = None) = (\<nexists>p . path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k))
        \<and> (((reaching_paths_up_to_depth M nexts dones assignment k) q = Some p) \<longrightarrow> path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k)
        \<and> (q \<in> nexts \<union> dones \<longrightarrow> (reaching_paths_up_to_depth M nexts dones assignment k) q = assignment q)"
  using assms proof (induction k arbitrary: n q nexts dones assignment)
    case 0

    have *:"((reaching_paths_up_to_depth M nexts dones assignment 0) q) = assignment q"
      by auto
    show ?case 
      unfolding * using "0.prems"(3,4)[of q] by simp
  next
    case (Suc k)

    define usable_transitions where d1: "usable_transitions = filter (\<lambda> t . t_source t \<in> nexts \<and> t_target t \<notin> dones \<and> t_target t \<notin> nexts) (transitions_as_list M)"
    moreover define targets where d2: "targets = map t_target usable_transitions"
    moreover define transition_choice where d3: "transition_choice = Map.empty(targets [\<mapsto>] usable_transitions)"
    moreover define assignment' where d4: "assignment' = assignment(targets [\<mapsto>] (map (\<lambda>q' . case transition_choice q' of Some t \<Rightarrow> (case assignment (t_source t) of Some p \<Rightarrow> p@[t])) targets))"
    ultimately have d5: "reaching_paths_up_to_depth M nexts dones assignment (Suc k) = reaching_paths_up_to_depth M (set targets) (nexts \<union> dones) assignment' k"
      unfolding reaching_paths_up_to_depth.simps Let_def by force

    let ?nexts' = "(set targets)"
    let ?dones' = "(nexts \<union> dones)"

    have p1: "?nexts' = {q. (\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p = Suc n) \<and>
                            (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < Suc n)}" (is "?nexts' = ?PS")
    proof -
      have "\<And> q . q \<in> ?nexts' \<Longrightarrow> q \<in> ?PS"
      proof -
        fix q assume "q \<in> ?nexts'"
        then obtain t where "t \<in> transitions M"
                        and "t_source t \<in> nexts" 
                        and "t_target t = q"
                        and "t_target t \<notin> dones"
                        and "t_target t \<notin> nexts"
          unfolding d2 d1 using transitions_as_list_set[of M] by force                        

        obtain p where "path M (initial M) p" and "target (initial M) p = t_source t" and "length p = n"
          using \<open>t_source t \<in> nexts\<close> unfolding Suc.prems by blast
        then have "path M (initial M) (p@[t])" and "target (initial M) (p@[t]) = q"
          unfolding \<open>t_target t = q\<close>[symmetric] using \<open>t \<in> transitions M\<close> by auto
        then have "(\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p = Suc n)"
          using \<open>length p = n\<close> by (metis length_append_singleton)  
        moreover have "(\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < Suc n)"
          using \<open>t_target t \<notin> dones\<close> \<open>t_target t \<notin> nexts\<close> unfolding \<open>t_target t = q\<close> Suc.prems
          using less_antisym by blast 
        ultimately show "q \<in> ?PS"
          by blast
      qed
      moreover have "\<And> q . q \<in> ?PS \<Longrightarrow> q \<in> ?nexts'" 
      proof -
        fix q assume "q \<in> ?PS"
        then obtain p where "path M (initial M) p" and "target (initial M) p = q" and "length p = Suc n"
          by auto

        let ?p = "butlast p"
        let ?t = "last p"


        have "p = ?p@[?t]"
          using \<open>length p = Suc n\<close>
          by (metis append_butlast_last_id list.size(3) nat.simps(3)) 
        then have "path M (initial M) (?p@[?t])" 
          using \<open>path M (initial M) p\<close> by auto

        have "path M (FSM.initial M) ?p"
             "?t \<in> FSM.transitions M"
             "t_source ?t = target (FSM.initial M) ?p"
          using path_append_transition_elim[OF \<open>path M (initial M) (?p@[?t])\<close>] by blast+

        have "t_target ?t = q"
          using \<open>target (initial M) p = q\<close> \<open>p = ?p@[?t]\<close> unfolding target.simps visited_states.simps
          by (metis (no_types, lifting) last_ConsR last_map map_is_Nil_conv snoc_eq_iff_butlast) 
        moreover have "t_source ?t \<in> nexts"
        proof -
          have "length ?p = n"
            using \<open>p = ?p@[?t]\<close> \<open>length p = Suc n\<close> by auto
          then have "(\<exists> p . path M (initial M) p \<and> target (initial M) p = t_source ?t \<and> length p = n)"
            using \<open>path M (FSM.initial M) ?p\<close> \<open>t_source ?t = target (FSM.initial M) ?p\<close>
            by metis 
          moreover have "(\<nexists> p . path M (initial M) p \<and> target (initial M) p = t_source ?t \<and> length p < n)"
          proof 
            assume "\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = t_source ?t \<and> length p < n"
            then obtain p' where "path M (FSM.initial M) p'" and "target (FSM.initial M) p' = t_source ?t" and "length p' < n"
              by blast
            then have "path M (initial M) (p'@[?t])" and "length (p'@[?t]) < Suc n"
              using \<open>?t \<in> FSM.transitions M\<close> by auto
            moreover have "target (initial M) (p'@[?t]) = q"
              using \<open>t_target ?t = q\<close> by auto
            ultimately show "False"
              using \<open>q \<in> ?PS\<close>
              by (metis (mono_tags, lifting) mem_Collect_eq)
          qed
          ultimately show ?thesis
            unfolding Suc.prems by blast
        qed
        moreover have "q \<notin> dones" and "q \<notin> nexts"
          unfolding Suc.prems using \<open>q \<in> ?PS\<close>
          using less_SucI by blast+
        ultimately have "t_source ?t \<in> nexts \<and> t_target ?t \<notin> dones \<and> t_target ?t \<notin> nexts"
          by simp
        then show "q \<in> ?nexts'"
          unfolding d2 d1 using transitions_as_list_set[of M] \<open>?t \<in> FSM.transitions M\<close> \<open>t_target ?t = q\<close>
          by auto 
      qed
      ultimately show ?thesis
        by blast
    qed

    have p2: "?dones' = {q. \<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < Suc n}" (is "?dones' = ?PS")
    proof -
      have "\<And> q . q \<in> ?dones' \<Longrightarrow> q \<in> ?PS" 
        unfolding Suc.prems
        using less_SucI by blast 
      moreover have "\<And> q . q \<in> ?PS \<Longrightarrow> q \<in> ?dones'"
      proof -
        fix q assume "q \<in> ?PS"
        show "q \<in> ?dones'" proof (cases "\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < n")
          case True
          then show ?thesis unfolding Suc.prems by blast
        next
          case False

          obtain p where *: "path M (FSM.initial M) p \<and> target (FSM.initial M) p = q" and "length p < Suc n" 
            using \<open>q \<in> ?PS\<close> by blast
          then have "length p = n"
            using False by force

          then show ?thesis 
            using * False unfolding Suc.prems by blast
        qed
      qed
      ultimately show ?thesis
        by blast
    qed

    have p3: "(\<And>q. (assignment' q = None) = (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n))"
    and  p4: "(\<And>q p. assignment' q = Some p \<Longrightarrow> path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n)"
    and  p5: "dom assignment' = ?nexts' \<union> ?dones'"
    proof -

      have "dom transition_choice = set targets"
        unfolding d3 d2 by auto

      show "dom assignment' = ?nexts' \<union> ?dones'"
        by (simp add: \<open>dom assignment = nexts \<union> dones\<close> d4)

      have helper: "\<And> f P (n::nat) . {x . (\<exists> y . P x y \<and> f y = n) \<and> (\<nexists> y . P x y \<and> f y < n)} \<union> {x . (\<exists> y . P x y \<and> f y < n)}= {x . (\<exists> y . P x y \<and> f y \<le> n)}"
        by force
      
      have dom': "dom assignment' = {q. \<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n}"
        unfolding \<open>dom assignment' = ?nexts' \<union> ?dones'\<close> p1 p2 
        using helper[of "\<lambda> q p . path M (FSM.initial M) p \<and> target (FSM.initial M) p = q" length "Suc n"] by force 


      have *: "\<And> q . q \<in> ?nexts' \<Longrightarrow> \<exists> p . assignment' q = Some p \<and> path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n"
      proof -
        fix q assume "q \<in> ?nexts'"
        then obtain t where "transition_choice q = Some t" 
          using \<open>dom transition_choice = set targets\<close> d2 d3 by blast 
        then have "t \<in> set usable_transitions" 
              and "t_target t = q"
              and "q \<in> set targets"
          unfolding d3 d2 using map_upds_map_set_left[of t_target usable_transitions q t] by auto
        then have "t_source t \<in> nexts" and "t \<in> transitions M"
          unfolding d1 using transitions_as_list_set[of M] by auto
        then obtain p where "assignment (t_source t) = Some p"
          using Suc.prems(1,3,4)
          by fastforce
        then have "path M (FSM.initial M) p \<and> target (FSM.initial M) p = t_source t \<and> length p \<le> n"
          using Suc.prems(4) by blast
        then have "path M (FSM.initial M) (p@[t]) \<and> target (FSM.initial M) (p@[t]) = q \<and> length (p@[t]) \<le> Suc n"
          using \<open>t \<in> transitions M\<close> \<open>t_target t = q\<close> by auto
        moreover have "assignment' q = Some (p@[t])" 
        proof -
          have "assignment' q = [targets [\<mapsto>] (map (\<lambda>q' . case transition_choice q' of Some t \<Rightarrow> (case assignment (t_source t) of Some p \<Rightarrow> p@[t])) targets)] q"
            unfolding d4 using map_upds_overwrite[OF \<open>q \<in> set targets\<close>, of "map (\<lambda>q' . case transition_choice q' of Some t \<Rightarrow> (case assignment (t_source t) of Some p \<Rightarrow> p@[t])) targets" assignment]
            by auto
          also have "\<dots> = Some (case transition_choice q of Some t \<Rightarrow> case assignment (t_source t) of Some p \<Rightarrow> p @ [t])"
            using map_upds_map_set_right[OF \<open>q \<in> set targets\<close>] by auto
          also have "\<dots> = Some (p@[t])"
            using \<open>transition_choice q = Some t\<close>  \<open>assignment (t_source t) = Some p\<close> by simp
          finally show ?thesis .
        qed
        ultimately show "\<exists> p . assignment' q = Some p \<and> path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n"
          by simp
      qed      
      
      show "(\<And>q. (assignment' q = None) = (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n))"
        using dom' by blast
      
      show "(\<And>q p. assignment' q = Some p \<Longrightarrow> path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n)"
      proof - 
        fix q p assume "assignment' q = Some p"

        show "path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> Suc n"
        proof (cases "q \<in> ?nexts'")
          case True
          show ?thesis using *[OF True] \<open>assignment' q = Some p\<close>
            by simp 
        next
          case False
          moreover have "\<And> q . assignment q \<noteq> assignment' q \<Longrightarrow> q \<in> ?nexts'"
            unfolding d4
            by (metis (no_types) map_upds_apply_nontin) 
          ultimately have "assignment' q = assignment q"
            by force
          then show ?thesis 
            using Suc.prems(4) \<open>assignment' q = Some p\<close>
            by (simp add: le_SucI) 
        qed
      qed
    qed


    have "\<And> q . (reaching_paths_up_to_depth M (set targets) (nexts \<union> dones) assignment' k q = None) =
          (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> n + Suc k) \<and>
          (reaching_paths_up_to_depth M (set targets) (nexts \<union> dones) assignment' k q = Some p \<longrightarrow>
           path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> n + Suc k)"
      using Suc.IH[OF p1 p2 p3 p4 p5] by auto

    moreover have "(q \<in> nexts \<union> dones \<longrightarrow> reaching_paths_up_to_depth M nexts dones assignment (Suc k) q = assignment q)"
    proof - 
      have "\<And> q . (q \<in> set targets \<union> (nexts \<union> dones) \<Longrightarrow> reaching_paths_up_to_depth M (set targets) (nexts \<union> dones) assignment' k q = assignment' q)"
        using Suc.IH[OF p1 p2 p3 p4 p5] by auto
      moreover have "\<And> q . assignment q \<noteq> assignment' q \<Longrightarrow> q \<in> ?nexts'"
        unfolding d4
        by (metis (no_types) map_upds_apply_nontin) 
      ultimately show ?thesis
        unfolding d5
        by (metis (mono_tags, lifting) Un_iff mem_Collect_eq p1 p2) 
    qed
    ultimately show ?case
      unfolding d5 by blast
  qed

  then show "((reaching_paths_up_to_depth M nexts dones assignment k) q = None) = (\<nexists>p . path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k)"
        and "((reaching_paths_up_to_depth M nexts dones assignment k) q = Some p) \<Longrightarrow> path M (initial M) p \<and> target (initial M) p = q \<and> length p \<le> n+k" 
        and "q \<in> nexts \<union> dones \<Longrightarrow> (reaching_paths_up_to_depth M nexts dones assignment k) q = assignment q"
    by blast+
qed



fun get_state_cover_assignment :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment" where
  "get_state_cover_assignment M = (let 
      path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)
    in (\<lambda> q . case path_assignments q of Some p \<Rightarrow> p_io p | None \<Rightarrow> []))"



lemma get_state_cover_assignment_is_state_cover_assignment : 
  "is_state_cover_assignment M (get_state_cover_assignment M)"
  unfolding is_state_cover_assignment.simps
proof 

  define path_assignments where "path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)"
  then have *:"\<And> q . get_state_cover_assignment M q = (case path_assignments q of Some p \<Rightarrow> p_io p | None \<Rightarrow> [])"
    by auto
    

  have c1: " {FSM.initial M} =
    {q. (\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p = 0) \<and>
      (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0)}" 
    by auto
  have c2:  "{} = {q. \<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0}"
    by auto
  have c3: "(\<And>q. ([FSM.initial M \<mapsto> []] q = None) =
        (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0))" by auto
  have c4: "(\<And>q p. [FSM.initial M \<mapsto> []] q = Some p \<Longrightarrow>
          path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0)"
    by (metis (no_types, lifting) c3 le_zero_eq length_0_conv map_upd_Some_unfold option.discI) 
  have c5: "dom [FSM.initial M \<mapsto> []] = {FSM.initial M} \<union> {}"
    by simp

  have p1: "\<And> q . (path_assignments q = None) =
                   (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1))"
   and p2: "\<And> q p . path_assignments q = Some p \<Longrightarrow>
                     path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1)"
   and p3: "path_assignments (initial M) = Some []"
    unfolding \<open>path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)\<close>
    using reaching_paths_up_to_depth_set[OF c1 c2 c3 c4 c5] by auto

  show "get_state_cover_assignment M (FSM.initial M) = []"
    unfolding * p3 by auto

  show "\<forall>q\<in>reachable_states M. q \<in> io_targets M (get_state_cover_assignment M q) (FSM.initial M)"
  proof 
    fix q assume "q \<in> reachable_states M"
    then have "q \<in> reachable_k M (FSM.initial M) (FSM.size M - 1)"
      using reachable_k_states by metis
    then obtain p where "target (initial M) p = q" and "path M (initial M) p" and "length p \<le> size M - 1"
      by auto
    then have "path_assignments q \<noteq> None"
      using p1 by fastforce
    then obtain p' where "get_state_cover_assignment M q = p_io p'"
                     and "path M (FSM.initial M) p'" and "target (FSM.initial M) p' = q"
      using p2 unfolding * by force
    then show "q \<in> io_targets M (get_state_cover_assignment M q) (initial M)" 
      unfolding io_targets.simps unfolding \<open>get_state_cover_assignment M q = p_io p'\<close> by blast
  qed
qed



subsection \<open>Computing Reachable States via State Cover Computation\<close>


lemma restrict_to_reachable_states[code]:
  "restrict_to_reachable_states M = (let 
      path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)
    in filter_states M (\<lambda> q . path_assignments q \<noteq> None))"
proof -
  define path_assignments where "path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)"    
  then have *: "(let 
      path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)
    in filter_states M (\<lambda> q . path_assignments q \<noteq> None)) = filter_states M (\<lambda> q . path_assignments q \<noteq> None)"
    by simp

  have c1: " {FSM.initial M} =
    {q. (\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p = 0) \<and>
      (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0)}" 
    by auto
  have c2:  "{} = {q. \<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0}"
    by auto
  have c3: "(\<And>q. ([FSM.initial M \<mapsto> []] q = None) =
        (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0))" by auto
  have c4: "(\<And>q p. [FSM.initial M \<mapsto> []] q = Some p \<Longrightarrow>
          path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0)"
    by (metis (no_types, lifting) c3 le_zero_eq length_0_conv map_upd_Some_unfold option.discI) 
  have c5: "dom [FSM.initial M \<mapsto> []] = {FSM.initial M} \<union> {}"
    by simp

  have p1: "\<And> q . (path_assignments q = None) =
                   (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1))"
   and p2: "\<And> q p . path_assignments q = Some p \<Longrightarrow>
                     path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1)"
   and p3: "path_assignments (initial M) = Some []"
    unfolding \<open>path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)\<close>
    using reaching_paths_up_to_depth_set[OF c1 c2 c3 c4 c5] by auto


  have "\<And> q . path_assignments q \<noteq> None \<longleftrightarrow> q \<in> reachable_states M"
  proof 
    show "\<And>q. path_assignments q \<noteq> None \<Longrightarrow> q \<in> reachable_states M"
      using p2 unfolding reachable_states_def
      by blast 
    show "\<And>q. q \<in> reachable_states M \<Longrightarrow> path_assignments q \<noteq> None"
    proof -
      fix q assume "q \<in> reachable_states M"
      then have "q \<in> reachable_k M (FSM.initial M) (FSM.size M - 1)"
        using reachable_k_states by metis
      then obtain p where "target (initial M) p = q" and "path M (initial M) p" and "length p \<le> size M - 1"
        by auto
      then show "path_assignments q \<noteq> None"
        using p1 by fastforce
    qed
  qed
  then show ?thesis
    unfolding restrict_to_reachable_states.simps * by simp
qed



declare [[code drop: reachable_states]]
lemma reachable_states_refined[code] : 
  "reachable_states M = (let 
      path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)
    in Set.filter (\<lambda> q . path_assignments q \<noteq> None) (states M))"
proof -
  define path_assignments where "path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)"    
  then have *: "(let 
      path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)
    in Set.filter (\<lambda> q . path_assignments q \<noteq> None) (states M)) = Set.filter (\<lambda> q . path_assignments q \<noteq> None) (states M)"
    by simp

  have c1: " {FSM.initial M} =
    {q. (\<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p = 0) \<and>
      (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0)}" 
    by auto
  have c2:  "{} = {q. \<exists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p < 0}"
    by auto
  have c3: "(\<And>q. ([FSM.initial M \<mapsto> []] q = None) =
        (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0))" by auto
  have c4: "(\<And>q p. [FSM.initial M \<mapsto> []] q = Some p \<Longrightarrow>
          path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> 0)"
    by (metis (no_types, lifting) c3 le_zero_eq length_0_conv map_upd_Some_unfold option.discI) 
  have c5: "dom [FSM.initial M \<mapsto> []] = {FSM.initial M} \<union> {}"
    by simp

  have p1: "\<And> q . (path_assignments q = None) =
                   (\<nexists>p. path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1))"
   and p2: "\<And> q p . path_assignments q = Some p \<Longrightarrow>
                     path M (FSM.initial M) p \<and> target (FSM.initial M) p = q \<and> length p \<le> (FSM.size M - 1)"
   and p3: "path_assignments (initial M) = Some []"
    unfolding \<open>path_assignments = reaching_paths_up_to_depth M {initial M} {} [initial M \<mapsto> []] (size M -1)\<close>
    using reaching_paths_up_to_depth_set[OF c1 c2 c3 c4 c5] by auto


  have "\<And> q . path_assignments q \<noteq> None \<longleftrightarrow> q \<in> reachable_states M"
  proof 
    show "\<And>q. path_assignments q \<noteq> None \<Longrightarrow> q \<in> reachable_states M"
      using p2 unfolding reachable_states_def
      by blast 
    show "\<And>q. q \<in> reachable_states M \<Longrightarrow> path_assignments q \<noteq> None"
    proof -
      fix q assume "q \<in> reachable_states M"
      then have "q \<in> reachable_k M (FSM.initial M) (FSM.size M - 1)"
        using reachable_k_states by metis
      then obtain p where "target (initial M) p = q" and "path M (initial M) p" and "length p \<le> size M - 1"
        by auto
      then show "path_assignments q \<noteq> None"
        using p1 by fastforce
    qed
  qed
  then show ?thesis
    unfolding * using reachable_state_is_state by force
qed


lemma minimal_sequence_to_failure_from_state_cover_assignment_ob :
  assumes "L M \<noteq> L I"
  and     "is_state_cover_assignment M V"
  and     "(L M \<inter> (V ` reachable_states M)) = (L I \<inter> (V ` reachable_states M))"
obtains ioT ioX where "ioT \<in> (V ` reachable_states M)"
                  and "ioT @ ioX \<in> (L M - L I) \<union> (L I - L M)"
                  and "\<And> io q . q \<in> reachable_states M \<Longrightarrow> (V q)@io \<in> (L M - L I) \<union> (L I - L M) \<Longrightarrow> length ioX \<le> length io"
proof -

  let ?exts = "{io . \<exists> q \<in> reachable_states M . (V q)@io \<in> (L M - L I) \<union> (L I - L M)}"
  define exMin where exMin: "exMin = arg_min length (\<lambda> io . io \<in> ?exts)"
  
  have "V (initial M) = []"
    using assms(2) by auto
  moreover have "\<exists> io . io \<in> (L M - L I) \<union> (L I - L M)"
    using assms(1) by blast 
  ultimately have "?exts \<noteq> {}"
    using reachable_states_initial by (metis (mono_tags, lifting) append_self_conv2 empty_iff mem_Collect_eq) 
  then have "exMin \<in> ?exts \<and> (\<forall> io' . io' \<in> ?exts \<longrightarrow> length exMin \<le> length io')"
    using exMin arg_min_nat_lemma by (metis (no_types, lifting) all_not_in_conv)
  then show ?thesis 
    using that by blast
qed


end