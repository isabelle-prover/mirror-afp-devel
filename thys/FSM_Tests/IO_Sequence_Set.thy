section \<open>Properties of Sets of IO Sequences\<close>

text \<open>This theory contains various definitions for properties of sets of IO-traces.\<close>

theory IO_Sequence_Set
imports FSM
begin


fun output_completion :: "('a \<times> 'b) list set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) list set" where
  "output_completion P Out = P \<union> {io@[(fst xy, y)] | io xy y . y \<in> Out \<and> io@[xy] \<in> P \<and> io@[(fst xy, y)] \<notin> P}"


fun output_complete_sequences :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "output_complete_sequences M P = (\<forall> io \<in> P . io = [] \<or> (\<forall> y \<in> (outputs M) . (butlast io)@[(fst (last io), y)] \<in> P))"


fun acyclic_sequences :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "acyclic_sequences M q P = (\<forall> p . (path M q p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states q p))"

fun acyclic_sequences' :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "acyclic_sequences' M q P = (\<forall> io \<in> P . \<forall> p \<in> (paths_for_io M q io) .  distinct (visited_states q p))"

lemma acyclic_sequences_alt_def[code] : "acyclic_sequences M P = acyclic_sequences' M P"
  unfolding acyclic_sequences'.simps acyclic_sequences.simps paths_for_io_def
  by blast

fun single_input_sequences :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "single_input_sequences M P = (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_targets M xys1 (initial M) = io_targets M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)"

fun single_input_sequences' :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "single_input_sequences' M P = (\<forall> io1 \<in> P . \<forall> io2 \<in> P . io1 = [] \<or> io2 = [] \<or> ((io_targets M (butlast io1) (initial M) = io_targets M (butlast io2) (initial M)) \<longrightarrow> fst (last io1) = fst (last io2)))"

lemma single_input_sequences_alt_def[code] : "single_input_sequences M P = single_input_sequences' M P"
  unfolding single_input_sequences.simps single_input_sequences'.simps
  by (metis append_butlast_last_id append_is_Nil_conv butlast_snoc last_snoc not_Cons_self)

fun output_complete_for_FSM_sequences_from_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences_from_state M q P = (\<forall> io xy t . io@[xy] \<in> P \<and> t \<in> transitions M \<and> t_source t \<in> io_targets M io q \<and> t_input t = fst xy \<longrightarrow> io@[(fst xy, t_output t)] \<in> P)"

lemma output_complete_for_FSM_sequences_from_state_alt_def :
  shows "output_complete_for_FSM_sequences_from_state M q P = (\<forall> xys xy y . (xys@[xy] \<in> P \<and> (\<exists> q' \<in> (io_targets M xys q) . [(fst xy,y)] \<in> LS M q')) \<longrightarrow> xys@[(fst xy,y)] \<in> P)"  
proof -
  have "\<And> xys xy y q' . q' \<in> (io_targets M xys q) \<Longrightarrow> [(fst xy,y)] \<in> LS M q' \<Longrightarrow> \<exists> t . t \<in> transitions M \<and> t_source t \<in> io_targets M xys q \<and> t_input t = fst xy \<and> t_output t = y" 
    unfolding io_targets.simps LS.simps
    using path_append path_append_transition_elim(2) by fastforce 

  moreover have "\<And> xys xy y t . t \<in> transitions M \<Longrightarrow> t_source t \<in> io_targets M xys q \<Longrightarrow> t_input t = fst xy \<Longrightarrow> t_output t = y \<Longrightarrow> \<exists> q' \<in> (io_targets M xys q) . [(fst xy,y)] \<in> LS M q'"
    unfolding io_targets.simps LS.simps
  proof -
    fix xys :: "('b \<times> 'c) list" and xy :: "'b \<times> 'd" and y :: 'c and t :: "'a \<times> 'b \<times> 'c \<times> 'a"
    assume a1: "t_input t = fst xy"
    assume a2: "t_output t = y"
    assume a3: "t_source t \<in> {target q p |p. path M q p \<and> p_io p = xys}"
    assume a4: "t \<in> FSM.transitions M"
    have "\<forall>p f. [f (p::'a \<times> 'b \<times> 'c \<times> 'a)::'b \<times> 'c] = map f [p]"
      by simp
    then have "\<exists>a. (\<exists>ps. [(t_input t, t_output t)] = p_io ps \<and> path M a ps) \<and> a \<in> {target q ps |ps. path M q ps \<and> p_io ps = xys}"
      using a4 a3 by (meson single_transition_path)
    then have "\<exists>a. [(t_input t, t_output t)] \<in> {p_io ps |ps. path M a ps} \<and> a \<in> {target q ps |ps. path M q ps \<and> p_io ps = xys}"
      by auto
    then show "\<exists>a\<in>{target q ps |ps. path M q ps \<and> p_io ps = xys}. [(fst xy, y)] \<in> {p_io ps |ps. path M a ps}"
      using a2 a1 by (metis (no_types, lifting)) 
  qed

  ultimately show ?thesis
    unfolding output_complete_for_FSM_sequences_from_state.simps by blast
qed

fun output_complete_for_FSM_sequences_from_state' :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences_from_state' M q P = (\<forall> io\<in>P . \<forall> t \<in> transitions M . io = [] \<or> (t_source t \<in> io_targets M (butlast io) q \<and> t_input t = fst (last io) \<longrightarrow> (butlast io)@[(fst (last io), t_output t)] \<in> P))"

lemma output_complete_for_FSM_sequences_alt_def'[code] : "output_complete_for_FSM_sequences_from_state M q P = output_complete_for_FSM_sequences_from_state' M q P"
  unfolding output_complete_for_FSM_sequences_from_state.simps output_complete_for_FSM_sequences_from_state'.simps
  by (metis last_snoc snoc_eq_iff_butlast)

fun deadlock_states_sequences :: "('a,'b,'c) fsm \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "deadlock_states_sequences M Q P = (\<forall> xys \<in> P . 
                                        ((io_targets M xys (initial M) \<subseteq> Q 
                                          \<and> \<not> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
                                      \<or> (\<not> io_targets M xys (initial M) \<inter> Q = {} 
                                          \<and> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))" 

fun reachable_states_sequences :: "('a,'b,'c) fsm \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "reachable_states_sequences M Q P = (\<forall> q \<in> Q . \<exists> xys \<in> P . q \<in> io_targets M xys (initial M))"

fun prefix_closed_sequences :: "('b \<times> 'c) list set \<Rightarrow> bool" where
  "prefix_closed_sequences P = (\<forall> xys1 xys2 . xys1@xys2 \<in> P \<longrightarrow> xys1 \<in> P)"

fun prefix_closed_sequences' :: "('b \<times> 'c) list set \<Rightarrow> bool" where
  "prefix_closed_sequences' P = (\<forall> io \<in> P . io = [] \<or> (butlast io) \<in> P)"

lemma prefix_closed_sequences_alt_def[code] : "prefix_closed_sequences P = prefix_closed_sequences' P"
proof 
  show "prefix_closed_sequences P \<Longrightarrow> prefix_closed_sequences' P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps
    by (metis append_butlast_last_id) 

  have "\<And>xys1 xys2. \<forall>io\<in>P. io = [] \<or> butlast io \<in> P \<Longrightarrow> xys1 @ xys2 \<in> P \<Longrightarrow> xys1 \<in> P"
  proof -
    fix xys1 xys2 assume "\<forall>io\<in>P. io = [] \<or> butlast io \<in> P" and "xys1 @ xys2 \<in> P"
    then show "xys1 \<in> P"
    proof (induction xys2 rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a xys2)
      then show ?case
        by (metis append.assoc snoc_eq_iff_butlast) 
    qed
  qed

  then show "prefix_closed_sequences' P \<Longrightarrow> prefix_closed_sequences P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps by blast 
qed

subsection \<open>Completions\<close>

definition prefix_completion :: "'a list set \<Rightarrow> 'a list set" where
  "prefix_completion P = {xs . \<exists> ys . xs@ys \<in> P}"

lemma prefix_completion_closed :
  "prefix_closed_sequences (prefix_completion P)"
  unfolding prefix_closed_sequences.simps prefix_completion_def
  by auto 

lemma prefix_completion_source_subset :
  "P \<subseteq> prefix_completion P" 
  unfolding prefix_completion_def
  by (metis (no_types, lifting) append_Nil2 mem_Collect_eq subsetI) 


definition output_completion_for_FSM :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> ('b \<times> 'c) list set" where
  "output_completion_for_FSM M P = P \<union> { io@[(x,y')] | io x y' . (y' \<in> (outputs M)) \<and> (\<exists> y . io@[(x,y)] \<in> P)}"

lemma output_completion_for_FSM_complete :
  shows "output_complete_sequences M (output_completion_for_FSM M P)"
  unfolding output_completion_for_FSM_def output_complete_sequences.simps 
proof 
  fix io assume *: "io \<in> P \<union> {io @ [(x, y')] |io x y'. y' \<in> (outputs M) \<and> (\<exists>y. io @ [(x, y)] \<in> P)}"
  show   "io = [] \<or>
          (\<forall>y\<in>(outputs M).
              butlast io @ [(fst (last io), y)]
              \<in> P \<union> {io @ [(x, y')] |io x y'. y' \<in> (outputs M) \<and> (\<exists>y. io @ [(x, y)] \<in> P)})"
  proof (cases io rule: rev_cases)
    case Nil
    then show ?thesis by blast
  next
    case (snoc ys y)
    then show ?thesis proof (cases "io \<in> P")
      case True  
      then have "butlast io @ [(fst (last io), (snd (last io)))] \<in> P" using snoc by auto
      then show ?thesis using snoc by blast
    next
      case False
      then show ?thesis
        using "*" by auto 
    qed 
  qed
qed

lemma output_completion_for_FSM_length :
  assumes "\<forall> io \<in> P . length io \<le> k"
  shows   "\<forall> io \<in> output_completion_for_FSM M P. length io \<le> k" 
  using assms unfolding output_completion_for_FSM_def
  by auto 

lemma output_completion_for_FSM_code[code] :
  "output_completion_for_FSM M P = P \<union> (\<Union>(image (\<lambda>(y,io) . if length io = 0 then {} else {((butlast io)@[(fst (last io),y)])})  ((outputs M) \<times> P)))"  
proof -
  let ?OC = "{io @ [(x, y')] |io x y'. y' \<in> FSM.outputs M \<and> (\<exists>y. io @ [(x, y)] \<in> P)}"
  let ?OC' = "(\<Union>(y, io)\<in>FSM.outputs M \<times> P. if length io = 0 then {} else {butlast io @ [(fst (last io), y)]})"

  have "?OC = ?OC'"
  proof -
    have "?OC \<subseteq> ?OC'"
    proof 
      fix io' assume "io' \<in> ?OC"
      then obtain io x y y' where "io' = io @ [(x, y')]"
                            and   "y' \<in> FSM.outputs M"
                            and   "io @ [(x, y)] \<in> P"
        by blast
      then have "(y',io @ [(x, y)]) \<in> FSM.outputs M \<times> P" by blast
      moreover have "length (io @ [(x, y)]) \<noteq> 0" by auto
      ultimately show "io' \<in> ?OC'"
        unfolding \<open>io' = io @ [(x, y')]\<close> by force
    qed
    moreover have "?OC' \<subseteq> ?OC" 
    proof 
      fix io' assume "io' \<in> ?OC'"
      then obtain y io where "y \<in> outputs M" and "io \<in> P"
                       and "io' \<in> (if length io = 0 then {} else {butlast io @ [(fst (last io), y)]})"
        by auto
      then have "io' = butlast io @ [(fst (last io), y)]"
        by (meson empty_iff singletonD)
      have "io \<noteq> []"
        using \<open>io' \<in> (if length io = 0 then {} else {butlast io @ [(fst (last io), y)]})\<close>
        by auto 

      then have "butlast io @ [(fst (last io), snd (last io))] \<in> P"
        by (simp add: \<open>io \<in> P\<close>)

      then show "io' \<in> ?OC"
        using \<open>y \<in> outputs M\<close> \<open>io \<in> P\<close>
        unfolding \<open>io' = butlast io @ [(fst (last io), y)]\<close> by blast
    qed
    ultimately show ?thesis by blast
  qed

  then show ?thesis 
    unfolding output_completion_for_FSM_def
    by simp 
qed


end