section \<open>Finite State Machines\<close>

text \<open>This theory defines well-formed finite state machines and introduces various closely related 
      notions, as well as a selection of basic properties and definitions.\<close>

theory FSM
  imports FSM_Impl "HOL-Library.Quotient_Type" "HOL-Library.Product_Lexorder"
begin


subsection \<open>Well-formed Finite State Machines\<close>

text \<open>A value of type @{text "fsm_impl"} constitutes a well-formed FSM if its contained sets are 
      finite and the initial state and the components of each transition are contained in their 
      respective sets.\<close>

abbreviation(input) "well_formed_fsm (M :: ('state, 'input, 'output) fsm_impl) 
     \<equiv> (initial M \<in> states M
      \<and> finite (states M)
      \<and> finite (inputs M)
      \<and> finite (outputs M)
      \<and> finite (transitions M)
      \<and> (\<forall> t \<in> transitions M . t_source t \<in> states M \<and> 
                                t_input t \<in> inputs M \<and> 
                                t_target t \<in> states M \<and> 
                                t_output t \<in> outputs M)) " 

typedef ('state, 'input, 'output) fsm = 
  "{ M :: ('state, 'input, 'output) fsm_impl . well_formed_fsm M}"
  morphisms fsm_impl_of_fsm Abs_fsm 
proof -
  obtain q :: 'state where "True" by blast
  have "well_formed_fsm (FSMI q {q} {} {} {})" by auto
  then show ?thesis by blast
qed


setup_lifting type_definition_fsm

lift_definition initial :: "('state, 'input, 'output) fsm \<Rightarrow> 'state" is FSM_Impl.initial done
lift_definition states :: "('state, 'input, 'output) fsm \<Rightarrow> 'state set" is FSM_Impl.states done
lift_definition inputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'input set" is FSM_Impl.inputs done
lift_definition outputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'output set" is FSM_Impl.outputs done
lift_definition transitions :: 
  "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input \<times> 'output \<times> 'state) set" 
  is FSM_Impl.transitions done

lift_definition fsm_from_list :: "'a \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> ('a, 'b, 'c) fsm" 
  is FSM_Impl.fsm_impl_from_list 
proof -
  fix q  :: 'a 
  fix ts :: "('a,'b,'c) transition list"
  show "well_formed_fsm (fsm_impl_from_list q ts)" 
    by (induction ts; auto)
qed



lemma fsm_initial[intro]: "initial M \<in> states M" 
  by (transfer; blast)
lemma fsm_states_finite: "finite (states M)" 
  by (transfer; blast)
lemma fsm_inputs_finite: "finite (inputs M)" 
  by (transfer; blast)
lemma fsm_outputs_finite: "finite (outputs M)" 
  by (transfer; blast)
lemma fsm_transitions_finite: "finite (transitions M)" 
  by (transfer; blast)
lemma fsm_transition_source[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_source t \<in> states M" 
  by (transfer; blast)
lemma fsm_transition_target[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_target t \<in> states M" 
  by (transfer; blast)
lemma fsm_transition_input[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_input t \<in> inputs M" 
  by (transfer; blast)
lemma fsm_transition_output[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_output t \<in> outputs M" 
  by (transfer; blast)


instantiation fsm :: (type,type,type) equal
begin                                  
definition equal_fsm :: "('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> bool" where
  "equal_fsm x y = (initial x = initial y \<and> states x = states y \<and> inputs x = inputs y \<and> outputs x = outputs y \<and> transitions x = transitions y)"

instance
  apply (intro_classes)
  unfolding equal_fsm_def 
  apply transfer
  using fsm_impl.expand by auto
end 



subsubsection \<open>Example FSMs\<close>


definition m_ex_H :: "(integer,integer,integer) fsm" where
  "m_ex_H = fsm_from_list 1 [ (1,0,0,2),
                              (1,0,1,4),
                              (1,1,1,4),
                              (2,0,0,2),
                              (2,1,1,4),
                              (3,0,1,4),
                              (3,1,0,1),
                              (3,1,1,3),
                              (4,0,0,3),
                              (4,1,0,1)]"


definition m_ex_9 :: "(integer,integer,integer) fsm" where
  "m_ex_9 = fsm_from_list 0 [ (0,0,2,2),
                              (0,0,3,2),
                              (0,1,0,3),
                              (0,1,1,3),
                              (1,0,3,2),
                              (1,1,1,3),
                              (2,0,2,2),
                              (2,1,3,3),
                              (3,0,2,2),
                              (3,1,0,2),
                              (3,1,1,1)]"

definition m_ex_DR :: "(integer,integer,integer) fsm" where
  "m_ex_DR = fsm_from_list 0  [(0,0,0,100),
                               (100,0,0,101), 
                               (100,0,1,101),
                               (101,0,0,102),
                               (101,0,1,102),
                               (102,0,0,103),
                               (102,0,1,103),
                               (103,0,0,104),
                               (103,0,1,104),
                               (104,0,0,100),
                               (104,0,1,100),
                               (104,1,0,400),
                               (0,0,2,200),
                               (200,0,2,201),
                               (201,0,2,202),
                               (202,0,2,203),
                               (203,0,2,200),
                               (203,1,0,400),
                               (0,1,0,300),
                               (100,1,0,300),
                               (101,1,0,300),
                               (102,1,0,300),
                               (103,1,0,300),
                               (200,1,0,300),
                               (201,1,0,300),
                               (202,1,0,300),
                               (300,0,0,300),
                               (300,1,0,300),
                               (400,0,0,300),
                               (400,1,0,300)]"


subsection \<open>Transition Function h and related functions\<close>

lift_definition h :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" 
  is FSM_Impl.h .

lemma h_simps[simp]: "FSM.h M (q,x) = { (y,q') . (q,x,y,q') \<in> transitions M }"
  by (transfer; auto)

lift_definition h_obs :: "('state, 'input, 'output) fsm \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> 'output \<Rightarrow> 'state option" 
  is FSM_Impl.h_obs .

lemma h_obs_simps[simp]: "FSM.h_obs M q x y = (let 
      tgts = snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))
    in if card tgts = 1
      then Some (the_elem tgts)
      else None)"
  by (transfer; auto)

fun defined_inputs' :: "(('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "defined_inputs' hM iM q = {x \<in> iM . hM (q,x) \<noteq> {}}"

fun defined_inputs :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "defined_inputs M q = defined_inputs' (h M) (inputs M) q"

lemma defined_inputs_set : "defined_inputs M q = {x \<in> inputs M . h M (q,x) \<noteq> {} }"
  by auto

fun transitions_from' :: "(('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) transition set" where
  "transitions_from' hM iM q = \<Union>(image (\<lambda>x . image (\<lambda>(y,q') . (q,x,y,q')) (hM (q,x))) iM)"

fun transitions_from :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) transition set" where
  "transitions_from M q = transitions_from' (h M) (inputs M) q"


lemma transitions_from_set : 
  assumes "q \<in> states M" 
  shows "transitions_from M q = {t \<in> transitions M . t_source t = q}"
proof -
  have "\<And> t . t \<in> transitions_from M q \<Longrightarrow> t \<in> transitions M \<and> t_source t = q" by auto
  moreover have "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = q \<Longrightarrow> t \<in> transitions_from M q" 
  proof -
    fix t assume "t \<in> transitions M" and "t_source t = q"
    then have "(t_output t, t_target t) \<in> h M (q,t_input t)" and "t_input t \<in> inputs M" by auto
    then have "t_input t \<in> defined_inputs' (h M) (inputs M) q" 
      unfolding defined_inputs'.simps \<open>t_source t = q\<close> by blast

    have "(q, t_input t, t_output t, t_target t) \<in> transitions M"
      using \<open>t_source t = q\<close> \<open>t \<in> transitions M\<close> by auto
    then have "(q, t_input t, t_output t, t_target t) \<in> (\<lambda>(y, q'). (q, t_input t, y, q')) ` h M (q, t_input t)"
      using \<open>(t_output t, t_target t) \<in> h M (q,t_input t)\<close>
      unfolding h.simps
      by (metis (no_types, lifting) image_iff prod.case_eq_if surjective_pairing)
    then have "t \<in> (\<lambda>(y, q'). (q, t_input t, y, q')) ` h M (q, t_input t)"
      using \<open>t_source t = q\<close> by (metis prod.collapse) 
    then show "t \<in> transitions_from M q" 
       
      unfolding transitions_from.simps transitions_from'.simps 
      using \<open>t_input t \<in> defined_inputs' (h M) (inputs M) q\<close>
      using \<open>t_input t \<in> FSM.inputs M\<close> by blast
  qed
  ultimately show ?thesis by blast
qed


fun h_from :: "('state, 'input, 'output) fsm \<Rightarrow> 'state \<Rightarrow> ('input \<times> 'output \<times> 'state) set" where
  "h_from M q = { (x,y,q') . (q,x,y,q') \<in> transitions M }"


lemma h_from[code] : "h_from M q = (let m = set_as_map (transitions M) 
                                     in (case m q of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding set_as_map_def by force


fun h_out :: "('a,'b,'c) fsm \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'c set" where
  "h_out M (q,x) = {y . \<exists> q' . (q,x,y,q') \<in> transitions M}"

lemma h_out_code[code]: 
  "h_out M = (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M))) qx of 
                            Some yqs \<Rightarrow> yqs | 
                            None \<Rightarrow> {}))"
proof -
  

  let ?f = "(\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  
  have "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` (transitions M)}) qx"
    unfolding set_as_map_def by auto
  
  moreover have "\<And> qx . (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` (transitions M)}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> (transitions M)}) qx" 
    by force
    
  ultimately have "?f = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> (transitions M)})" 
    by blast
  then have "?f = (\<lambda> (q,x) . {y | y . \<exists> q' . (q, x, y, q') \<in> (transitions M)})" by force
  
  then show ?thesis by force 
qed

lemma h_out_alt_def : 
  "h_out M (q,x) = {t_output t | t . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x}"
  unfolding h_out.simps
  by auto


subsection \<open>Size\<close>

instantiation fsm  :: (type,type,type) size 
begin

definition size where [simp, code]: "size (m::('a, 'b, 'c) fsm) = card (states m)"

instance ..
end

lemma fsm_size_Suc :
  "size M > 0"
  unfolding FSM.size_def
  using fsm_states_finite[of M] fsm_initial[of M]
  using card_gt_0_iff by blast 


subsection \<open>Paths\<close>

inductive path :: "('state, 'input, 'output) fsm \<Rightarrow> 'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> bool" 
  where
  nil[intro!] : "q \<in> states M \<Longrightarrow> path M q []" |
  cons[intro!] : "t \<in> transitions M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_nil_elim[elim!]: "path M q []"
inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"

fun visited_states :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state list" where
  "visited_states q p = (q # map t_target p)"

fun target :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state" where
  "target q p = last (visited_states q p)"

lemma target_nil [simp] : "target q [] = q" by auto
lemma target_snoc [simp] : "target q (p@[t]) = t_target t" by auto


lemma path_begin_state :
  assumes "path M q p"
  shows   "q \<in> states M" 
  using assms by (cases; auto) 

lemma path_append[intro!] :
  assumes "path M q p1"
      and "path M (target q p1) p2"
  shows "path M q (p1@p2)"
  using assms by (induct p1 arbitrary: p2; auto) 

lemma path_target_is_state :
  assumes "path M q p"
  shows   "target q p \<in> states M"
using assms by (induct p; auto)

lemma path_suffix :
  assumes "path M q (p1@p2)"
  shows "path M (target q p1) p2"
using assms by (induction p1 arbitrary: q; auto)

lemma path_prefix :
  assumes "path M q (p1@p2)"
  shows "path M q p1"
using assms by (induction p1 arbitrary: q; auto; (metis path_begin_state))

lemma path_append_elim[elim!] :
  assumes "path M q (p1@p2)"
  obtains "path M q p1"
      and "path M (target q p1) p2"
  by (meson assms path_prefix path_suffix)

lemma path_append_target:
  "target q (p1@p2) = target (target q p1) p2" 
  by (induction p1) (simp+)

lemma path_append_target_hd :
  assumes "length p > 0"
  shows "target q p = target (t_target (hd p)) (tl p)"
using assms by (induction p) (simp+)

lemma path_transitions :
  assumes "path M q p"
  shows "set p \<subseteq> transitions M"
  using assms by (induct p arbitrary: q; fastforce)

lemma path_append_transition[intro!] :
  assumes "path M q p"
  and     "t \<in> transitions M"
  and     "t_source t = target q p" 
shows "path M q (p@[t])"
  by (metis assms(1) assms(2) assms(3) cons fsm_transition_target nil path_append)

lemma path_append_transition_elim[elim!] :
  assumes "path M q (p@[t])"
shows "path M q p"
and   "t \<in> transitions M"
and   "t_source t = target q p" 
  using assms by auto

lemma path_prepend_t : "path M q' p \<Longrightarrow> (q,x,y,q') \<in> transitions M \<Longrightarrow> path M q ((q,x,y,q')#p)" 
  by (metis (mono_tags, lifting) fst_conv path.intros(2) prod.sel(2)) 

lemma path_target_append : "target q1 p1 = q2 \<Longrightarrow> target q2 p2 = q3 \<Longrightarrow> target q1 (p1@p2) = q3" 
  by auto

lemma single_transition_path : "t \<in> transitions M \<Longrightarrow> path M (t_source t) [t]" by auto

lemma path_source_target_index :
  assumes "Suc i < length p"
  and     "path M q p"
shows "t_target (p ! i) = t_source (p ! (Suc i))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t ps)
  then have "path M q ps" and "t_source t = target q ps" and "t \<in> transitions M" by auto
  
  show ?case proof (cases "Suc i < length ps")
    case True
    then have "t_target (ps ! i) = t_source (ps ! Suc i)" 
      using snoc.IH \<open>path M q ps\<close> by auto
    then show ?thesis
      by (simp add: Suc_lessD True nth_append) 
  next
    case False
    then have "Suc i = length ps"
      using snoc.prems(1) by auto
    then have "(ps @ [t]) ! Suc i = t"
      by auto

    show ?thesis proof (cases "ps = []")
      case True
      then show ?thesis using \<open>Suc i = length ps\<close> by auto
    next
      case False
      then have "target q ps = t_target (last ps)"
        unfolding target.simps visited_states.simps
        by (simp add: last_map) 
      then have "target q ps = t_target (ps ! i)"
        using \<open>Suc i = length ps\<close>
        by (metis False diff_Suc_1 last_conv_nth) 
      then show ?thesis 
        using \<open>t_source t = target q ps\<close>
        by (metis \<open>(ps @ [t]) ! Suc i = t\<close> \<open>Suc i = length ps\<close> lessI nth_append) 
    qed
  qed   
qed

lemma paths_finite : "finite { p . path M q p \<and> length p \<le> k }"
proof -
  have "{ p . path M q p \<and> length p \<le> k } \<subseteq> {xs . set xs \<subseteq> transitions M \<and> length xs \<le> k}"
    by (metis (no_types, lifting) Collect_mono path_transitions)     
  then show "finite { p . path M q p \<and> length p \<le> k }"
    using finite_lists_length_le[OF fsm_transitions_finite[of M], of k]
    by (metis (mono_tags) finite_subset) 
qed

lemma visited_states_prefix :
  assumes "q' \<in> set (visited_states q p)"
  shows   "\<exists> p1 p2 . p = p1@p2 \<and> target q p1 = q'"
using assms proof (induction p arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case 
  proof (cases "q' \<in> set (visited_states (t_target a) p)")
    case True
    then obtain p1 p2 where "p = p1 @ p2 \<and> target (t_target a) p1 = q'"
      using Cons.IH by blast
    then have "(a#p) = (a#p1)@p2 \<and> target q (a#p1) = q'"
      by auto
    then show ?thesis by blast
  next
    case False
    then have "q' = q" 
      using Cons.prems by auto     
    then show ?thesis
      by auto 
  qed
qed 

lemma visited_states_are_states :
  assumes "path M q1 p"
  shows "set (visited_states q1 p) \<subseteq> states M" 
  by (metis assms path_prefix path_target_is_state subsetI visited_states_prefix) 
  
lemma transition_subset_path : 
  assumes "transitions A \<subseteq> transitions B"
  and "path A q p"
  and "q \<in> states B"
shows "path B q p"
using assms(2) proof (induction p rule: rev_induct)
  case Nil
  show ?case using assms(3) by auto
next
  case (snoc t p)
  then show ?case using assms(1) path_suffix
    by fastforce   
qed

subsubsection \<open>Paths of fixed length\<close>

fun paths_of_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> (('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" 
  where
  "paths_of_length' prev q hM iM 0 = {prev}" |
  "paths_of_length' prev q hM iM (Suc k) = 
    (let hF = transitions_from' hM iM q
      in \<Union> (image (\<lambda> t . paths_of_length' (prev@[t]) (t_target t) hM iM k) hF))"

fun paths_of_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_of_length M q k = paths_of_length' [] q (h M) (inputs M) k"



subsubsection \<open>Paths up to fixed length\<close>

fun paths_up_to_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> (('a \<times>'b) \<Rightarrow> (('c\<times>'a) set)) \<Rightarrow> 'b set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" 
  where
  "paths_up_to_length' prev q hM iM 0 = {prev}" |
  "paths_up_to_length' prev q hM iM (Suc k) = 
    (let hF = transitions_from' hM iM q
      in insert prev (\<Union> (image (\<lambda> t . paths_up_to_length' (prev@[t]) (t_target t) hM iM k) hF)))"

fun paths_up_to_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_up_to_length M q k = paths_up_to_length' [] q (h M) (inputs M) k"


lemma paths_up_to_length'_set :
  assumes "q \<in> states M"
  and     "path M q prev"
shows "paths_up_to_length' prev (target q prev) (h M) (inputs M) k 
        = {(prev@p) | p . path M (target q prev) p \<and> length p \<le> k}"
using assms(2) proof (induction k arbitrary: prev)
  case 0
  show ?case unfolding paths_up_to_length'.simps using path_target_is_state[OF "0.prems"(1)] by auto
next
  case (Suc k)
  
  have "\<And> p . p \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k) 
          \<Longrightarrow> p \<in> {(prev@p) | p . path M (target q prev) p \<and> length p \<le> Suc k}"
  proof -
    fix p assume "p \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k)"
    then show "p \<in> {(prev@p) | p . path M (target q prev) p \<and> length p \<le> Suc k}" 
    proof (cases "p = prev")
      case True
      show ?thesis using path_target_is_state[OF Suc.prems(1)] unfolding True by (simp add: nil) 
    next
      case False
      then have "p \<in> (\<Union> (image (\<lambda>t. paths_up_to_length' (prev@[t]) (t_target t) (h M) (inputs M) k) 
                                (transitions_from' (h M) (inputs M) (target q prev))))"
        using \<open>p \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k)\<close>
        unfolding paths_up_to_length'.simps Let_def by blast
      then obtain t where "t \<in> \<Union>(image (\<lambda>x . image (\<lambda>(y,q') . ((target q prev),x,y,q')) 
                                                    (h M ((target q prev),x))) (inputs M))"
                    and   "p \<in> paths_up_to_length' (prev@[t]) (t_target t) (h M) (inputs M) k"
        unfolding transitions_from'.simps by blast

      have "t \<in> transitions M" and "t_source t = (target q prev)"
        using \<open>t \<in> \<Union>(image (\<lambda>x . image (\<lambda>(y,q') . ((target q prev),x,y,q')) 
                                        (h M ((target q prev),x))) (inputs M))\<close> by auto
      then have "path M q (prev@[t])"
        using Suc.prems(1) using path_append_transition by simp

      have "(target q (prev @ [t])) = t_target t" by auto
      

      show ?thesis 
        using \<open>p \<in> paths_up_to_length' (prev@[t]) (t_target t) (h M) (inputs M) k\<close>
        using Suc.IH[OF \<open>path M q (prev@[t])\<close>] 
        unfolding \<open>(target q (prev @ [t])) = t_target t\<close>
        using \<open>path M q (prev @ [t])\<close> by auto 
    qed
  qed

  moreover have "\<And> p . p \<in> {(prev@p) | p . path M (target q prev) p \<and> length p \<le> Suc k} 
                  \<Longrightarrow> p \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k)"
  proof -
    fix p assume "p \<in> {(prev@p) | p . path M (target q prev) p \<and> length p \<le> Suc k}"
    then obtain p' where "p = prev@p'"
                   and   "path M (target q prev) p'" 
                   and   "length p' \<le> Suc k"
      by blast

    have "prev@p' \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k)"
    proof (cases p')
      case Nil
      then show ?thesis by auto
    next
      case (Cons t p'')

      then have "t \<in> transitions M" and "t_source t = (target q prev)"
        using \<open>path M (target q prev) p'\<close> by auto
      then have "path M q (prev@[t])"
        using Suc.prems(1) using path_append_transition by simp
      
      have "(target q (prev @ [t])) = t_target t" by auto

      have "length p'' \<le> k" using \<open>length p' \<le> Suc k\<close> Cons by auto
      moreover have "path M (target q (prev@[t])) p''"
        using \<open>path M (target q prev) p'\<close> unfolding Cons
        by auto
      ultimately have "p \<in> paths_up_to_length' (prev @ [t]) (t_target t) (h M) (FSM.inputs M) k"
        using Suc.IH[OF \<open>path M q (prev@[t])\<close>] 
        unfolding \<open>(target q (prev @ [t])) = t_target t\<close> \<open>p = prev@p'\<close> Cons by simp
      then have "prev@t#p'' \<in> paths_up_to_length' (prev @ [t]) (t_target t) (h M) (FSM.inputs M) k"
        unfolding \<open>p = prev@p'\<close> Cons by auto

      have "t \<in> (\<lambda>(y, q'). (t_source t, t_input t, y, q')) ` 
                              {(y, q'). (t_source t, t_input t, y, q') \<in> FSM.transitions M}"
        using \<open>t \<in> transitions M\<close>
        by (metis (no_types, lifting) case_prodI mem_Collect_eq pair_imageI surjective_pairing)  
      then have "t \<in> transitions_from' (h M) (inputs M) (target q prev)"
        unfolding transitions_from'.simps 
        using fsm_transition_input[OF \<open>t \<in> transitions M\<close>] 
        unfolding \<open>t_source t = (target q prev)\<close>[symmetric] h_simps 
        by blast

      then show ?thesis 
        using \<open>prev @ t # p'' \<in> paths_up_to_length' (prev@[t]) (t_target t) (h M) (FSM.inputs M) k\<close> 
        unfolding \<open>p = prev@p'\<close> Cons paths_up_to_length'.simps Let_def by blast
    qed
    then show "p \<in> paths_up_to_length' prev (target q prev) (h M) (inputs M) (Suc k)"
      unfolding \<open>p = prev@p'\<close> by assumption
  qed

  ultimately show ?case by blast
qed


lemma paths_up_to_length_set :
  assumes "q \<in> states M"
shows "paths_up_to_length M q k = {p . path M q p \<and> length p \<le> k}" 
  unfolding paths_up_to_length.simps 
  using paths_up_to_length'_set[OF assms nil[OF assms], of k]  by auto




subsubsection \<open>Calculating Acyclic Paths\<close>

fun acyclic_paths_up_to_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> ('a  \<Rightarrow> (('b\<times>'c\<times>'a) set)) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" 
  where
  "acyclic_paths_up_to_length' prev q hF visitedStates 0 = {prev}" |
  "acyclic_paths_up_to_length' prev q hF visitedStates (Suc k) = 
    (let tF = Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedStates) (hF q)
      in (insert prev (\<Union> (image (\<lambda> (x,y,q') . acyclic_paths_up_to_length' (prev@[(q,x,y,q')]) q' hF (insert q' visitedStates) k) tF))))"


fun p_source :: "'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> 'a"
  where "p_source q p = hd (visited_states q p)"

lemma acyclic_paths_up_to_length'_prev : 
  "p' \<in> acyclic_paths_up_to_length' (prev@prev') q hF visitedStates k \<Longrightarrow> \<exists> p'' . p' = prev@p''" 
  by (induction k arbitrary: p' q visitedStates prev'; auto)

lemma acyclic_paths_up_to_length'_set :
  assumes "path M (p_source q prev) prev"
  and     "\<And> q' . hF q' = {(x,y,q'') | x y q'' . (q',x,y,q'') \<in> transitions M}"
  and     "distinct (visited_states (p_source q prev) prev)"
  and     "visitedStates = set (visited_states (p_source q prev) prev)"
shows "acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates k 
        = { prev@p | p . path M (p_source q prev) (prev@p) 
                          \<and> length p \<le> k 
                          \<and> distinct (visited_states (p_source q prev) (prev@p)) }"
using assms proof (induction k arbitrary: q hF prev visitedStates)
  case 0
  then show ?case by auto
next
  case (Suc k)

  let ?tgt = "(target (p_source q prev) prev)"

  have "\<And> p . (prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k) 
            \<Longrightarrow> path M (p_source q prev) (prev@p) 
                \<and> length p \<le> Suc k 
                \<and> distinct (visited_states (p_source q prev) (prev@p))"
  proof -
    fix p assume "(prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k)"
    then consider (a) "(prev@p) = prev" |
                  (b) "(prev@p) \<in> (\<Union> (image (\<lambda> (x,y,q') . acyclic_paths_up_to_length' (prev@[(?tgt,x,y,q')]) q' hF (insert q' visitedStates) k) 
                                             (Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedStates) (hF (target (p_source q prev) prev)))))"
      by auto
    then show "path M (p_source q prev) (prev@p) \<and> length p \<le> Suc k \<and> distinct (visited_states (p_source q prev) (prev@p))"
    proof (cases)
      case a
      then show ?thesis using Suc.prems(1,3) by auto
    next
      case b
      then obtain x y q' where *: "(x,y,q') \<in> Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedStates) (hF ?tgt)"
                         and   **:"(prev@p) \<in> acyclic_paths_up_to_length' (prev@[(?tgt,x,y,q')]) q' hF (insert q' visitedStates) k"
        by auto

      let ?t = "(?tgt,x,y,q')"

      from * have "?t \<in> transitions M" and "q' \<notin> visitedStates"
        using Suc.prems(2)[of ?tgt] by simp+ 
      moreover have "t_source ?t = target (p_source q prev) prev"
        by simp
      moreover have "p_source (p_source q prev) (prev@[?t]) = p_source q prev"
        by auto
      ultimately have p1: "path M (p_source (p_source q prev) (prev@[?t])) (prev@[?t])" 
        using Suc.prems(1)
        by (simp add: path_append_transition) 
      
      
      have "q' \<notin> set (visited_states (p_source q prev) prev)"
        using \<open>q' \<notin> visitedStates\<close> Suc.prems(4) by auto
      then have p2: "distinct (visited_states (p_source (p_source q prev) (prev@[?t])) (prev@[?t]))"
        using Suc.prems(3) by auto

      have p3: "(insert q' visitedStates) 
                  = set (visited_states (p_source (p_source q prev) (prev@[?t])) (prev@[?t]))"
        using Suc.prems(4) by auto

      have ***: "(target (p_source (p_source q prev) (prev @ [(target (p_source q prev) prev, x, y, q')])) 
                         (prev @ [(target (p_source q prev) prev, x, y, q')])) 
                  = q'"
        by auto

      show ?thesis
        using Suc.IH[OF p1 Suc.prems(2) p2 p3] ** 
        unfolding *** 
        unfolding \<open>p_source (p_source q prev) (prev@[?t]) = p_source q prev\<close>
      proof -
        assume "acyclic_paths_up_to_length' (prev @ [(target (p_source q prev) prev, x, y, q')]) q' hF (insert q' visitedStates) k 
                  = {(prev @ [(target (p_source q prev) prev, x, y, q')]) @ p |p. 
                        path M (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ p) 
                        \<and> length p \<le> k 
                        \<and> distinct (visited_states (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ p))}"
        then have "\<exists>ps. prev @ p = (prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps 
                        \<and> path M (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps) 
                        \<and> length ps \<le> k 
                        \<and> distinct (visited_states (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps))"
          using \<open>prev @ p \<in> acyclic_paths_up_to_length' (prev @ [(target (p_source q prev) prev, x, y, q')]) q' hF (insert q' visitedStates) k\<close> 
          by blast
        then show ?thesis
          by (metis (no_types) Suc_le_mono append.assoc append.right_neutral append_Cons length_Cons same_append_eq)
      qed 
    qed
  qed
  moreover have "\<And> p' . p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k) 
                        \<Longrightarrow> \<exists> p'' . p' = prev@p''"
    using acyclic_paths_up_to_length'_prev[of _ prev "[]" "target (p_source q prev) prev" hF visitedStates "Suc k"] 
    by force
  ultimately have fwd: "\<And> p' . p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k) 
                          \<Longrightarrow> p' \<in> { prev@p | p . path M (p_source q prev) (prev@p) 
                                                    \<and> length p \<le> Suc k 
                                                    \<and> distinct (visited_states (p_source q prev) (prev@p)) }"
    by blast

  have "\<And> p . path M (p_source q prev) (prev@p) 
                \<Longrightarrow> length p \<le> Suc k 
                \<Longrightarrow> distinct (visited_states (p_source q prev) (prev@p)) 
                \<Longrightarrow> (prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k)"
  proof -
    fix p assume "path M (p_source q prev) (prev@p)"
          and    "length p \<le> Suc k"
          and    "distinct (visited_states (p_source q prev) (prev@p))"

    show "(prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k)"
    proof (cases p)
      case Nil
      then show ?thesis by auto
    next
      case (Cons t p')

      then have "t_source t = target (p_source q (prev)) (prev)" and "t \<in> transitions M"
        using \<open>path M (p_source q prev) (prev@p)\<close> by auto
      
      have "path M (p_source q (prev@[t])) ((prev@[t])@p')"
      and  "path M (p_source q (prev@[t])) ((prev@[t]))"
        using Cons \<open>path M (p_source q prev) (prev@p)\<close> by auto
      have "length p' \<le> k"
        using Cons \<open>length p \<le> Suc k\<close> by auto
      have "distinct (visited_states (p_source q (prev@[t])) ((prev@[t])@p'))"
      and  "distinct (visited_states (p_source q (prev@[t])) ((prev@[t])))" 
        using Cons \<open>distinct (visited_states (p_source q prev) (prev@p))\<close> by auto
      then have "t_target t \<notin> visitedStates"
        using Suc.prems(4) by auto

      let ?vN = "insert (t_target t) visitedStates"
      have "?vN = set (visited_states (p_source q (prev @ [t])) (prev @ [t]))"
        using Suc.prems(4) by auto

      have "prev@p = prev@([t]@p')"
        using Cons by auto

      have "(prev@[t])@p' \<in> acyclic_paths_up_to_length' (prev @ [t]) (target (p_source q (prev @ [t])) (prev @ [t])) hF (insert (t_target t) visitedStates) k" 
        using Suc.IH[of q "prev@[t]", OF \<open>path M (p_source q (prev@[t])) ((prev@[t]))\<close> Suc.prems(2)
                                         \<open>distinct (visited_states (p_source q (prev@[t])) ((prev@[t])))\<close> 
                                         \<open>?vN = set (visited_states (p_source q (prev @ [t])) (prev @ [t]))\<close> ]
        using \<open>path M (p_source q (prev@[t])) ((prev@[t])@p')\<close>
              \<open>length p' \<le> k\<close>
              \<open>distinct (visited_states (p_source q (prev@[t])) ((prev@[t])@p'))\<close> 
        by force

      then have "(prev@[t])@p' \<in> acyclic_paths_up_to_length' (prev@[t]) (t_target t) hF ?vN k"
        by auto
      moreover have "(t_input t,t_output t, t_target t) \<in> Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedStates) (hF (t_source t))"
        using Suc.prems(2)[of "t_source t"] \<open>t \<in> transitions M\<close> \<open>t_target t \<notin> visitedStates\<close>
      proof -
        have "\<exists>b c a. snd t = (b, c, a) \<and> (t_source t, b, c, a) \<in> FSM.transitions M"
          by (metis (no_types) \<open>t \<in> FSM.transitions M\<close> prod.collapse)
        then show ?thesis
          using \<open>hF (t_source t) = {(x, y, q'') |x y q''. (t_source t, x, y, q'') \<in> FSM.transitions M}\<close> 
                \<open>t_target t \<notin> visitedStates\<close> 
          by fastforce
      qed 
      ultimately have "\<exists> (x,y,q') \<in> (Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedStates) (hF (target (p_source q prev) prev))) .
                        (prev@[t])@p' \<in> (acyclic_paths_up_to_length' (prev@[((target (p_source q prev) prev),x,y,q')]) q' hF (insert q' visitedStates) k)"
        unfolding \<open>t_source t = target (p_source q (prev)) (prev)\<close>
        by (metis (no_types, lifting) \<open>t_source t = target (p_source q prev) prev\<close> case_prodI prod.collapse) 
       
      then show ?thesis unfolding \<open>prev@p = prev@[t]@p'\<close> 
        unfolding acyclic_paths_up_to_length'.simps Let_def by force
    qed
  qed
  then have rev: "\<And> p' . p' \<in> {prev@p | p . path M (p_source q prev) (prev@p) 
                                              \<and> length p \<le> Suc k 
                                              \<and> distinct (visited_states (p_source q prev) (prev@p))} 
                        \<Longrightarrow> p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedStates (Suc k)"
    by blast
  
  show ?case
    using fwd rev by blast
qed 


fun acyclic_paths_up_to_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "acyclic_paths_up_to_length M q k = {p. path M q p \<and> length p \<le> k \<and> distinct (visited_states q p)}"

lemma acyclic_paths_up_to_length_code[code] :
  "acyclic_paths_up_to_length M q k = (if q \<in> states M 
      then acyclic_paths_up_to_length' [] q (m2f (set_as_map (transitions M))) {q} k
      else {})"
proof (cases "q \<in> states M")
  case False
  then have "acyclic_paths_up_to_length M q k = {}" 
    using path_begin_state by fastforce
  then show ?thesis using False by auto
next
  case True
  then have *: "path M (p_source q []) []" by auto
  have **: "(\<And>q'. (m2f (set_as_map (transitions M))) q' = {(x, y, q'') |x y q''. (q', x, y, q'') \<in> FSM.transitions M})"
    unfolding set_as_map_def by auto 
  have ***: "distinct (visited_states (p_source q []) [])"
    by auto
  have ****: "{q} = set (visited_states (p_source q []) [])"
    by auto
  
  show ?thesis
    using acyclic_paths_up_to_length'_set[OF * ** *** ****, of k ] 
    using True by auto
qed


lemma path_map_target : "target (f4 q) (map (\<lambda> t . (f1 (t_source t), f2 (t_input t), f3 (t_output t), f4 (t_target t))) p) = f4 (target q p)" 
  by (induction p; auto)


lemma path_length_sum :
  assumes "path M q p" 
  shows "length p = (\<Sum> q \<in> states M . length (filter (\<lambda>t. t_target t = q) p))"
  using assms
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then have "length xs = (\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) xs))"
    by auto
  
  have *: "t_target x \<in> states M"
    using \<open>path M q (xs @ [x])\<close> by auto
  then have **: "length (filter (\<lambda>t. t_target t = t_target x) (xs @ [x])) 
                  = Suc (length (filter (\<lambda>t. t_target t = t_target x) xs))"
    by auto

  have "\<And> q . q \<in> states M \<Longrightarrow> q \<noteq> t_target x 
          \<Longrightarrow> length (filter (\<lambda>t. t_target t = q) (xs @ [x])) = length (filter (\<lambda>t. t_target t = q) xs)"
    by simp
  then have ***: "(\<Sum>q\<in>states M - {t_target x}. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) 
                  = (\<Sum>q\<in>states M - {t_target x}. length (filter (\<lambda>t. t_target t = q) xs))"
    using fsm_states_finite[of M]
    by (metis (no_types, lifting) DiffE insertCI sum.cong)

  have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) 
          = (\<Sum>q\<in>states M - {t_target x}. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) 
              + (length (filter (\<lambda>t. t_target t = t_target x) (xs @ [x])))"
    using * fsm_states_finite[of M]
  proof -
    have "(\<Sum>a\<in>insert (t_target x) (states M). length (filter (\<lambda>p. t_target p = a) (xs @ [x]))) 
            = (\<Sum>a\<in>states M. length (filter (\<lambda>p. t_target p = a) (xs @ [x])))"
      by (simp add: \<open>t_target x \<in> states M\<close> insert_absorb)
    then show ?thesis
      by (simp add: \<open>finite (states M)\<close> sum.insert_remove)
  qed  
  moreover have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) xs)) 
                  = (\<Sum>q\<in>states M - {t_target x}. length (filter (\<lambda>t. t_target t = q) xs)) 
                      + (length (filter (\<lambda>t. t_target t = t_target x) xs))"
    using * fsm_states_finite[of M]
  proof -
    have "(\<Sum>a\<in>insert (t_target x) (states M). length (filter (\<lambda>p. t_target p = a) xs)) 
            = (\<Sum>a\<in>states M. length (filter (\<lambda>p. t_target p = a) xs))"
      by (simp add: \<open>t_target x \<in> states M\<close> insert_absorb)
    then show ?thesis
      by (simp add: \<open>finite (states M)\<close> sum.insert_remove)
  qed  

  ultimately have "(\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) 
                    = Suc (\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) xs))"
    using ** *** by auto
    
  then show ?case
    by (simp add: \<open>length xs = (\<Sum>q\<in>states M. length (filter (\<lambda>t. t_target t = q) xs))\<close>) 
qed


lemma path_loop_cut :
  assumes "path M q p"
  and     "t_target (p ! i) = t_target (p ! j)"
  and     "i < j"
  and     "j < length p"
shows "path M q ((take (Suc i) p) @ (drop (Suc j) p))"
and   "target q ((take (Suc i) p) @ (drop (Suc j) p)) = target q p"
and   "length ((take (Suc i) p) @ (drop (Suc j) p)) < length p"
and   "path M (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p))"
and   "target (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p)) = (target q (take (Suc i) p))"
proof -
    
  have "p = (take (Suc j) p) @ (drop (Suc j) p)"
    by auto
  also have "\<dots> = ((take (Suc i) (take (Suc j) p)) @ (drop (Suc i) (take (Suc j) p))) @ (drop (Suc j) p)"
    by (metis append_take_drop_id)
  also have "\<dots> = ((take (Suc i) p) @ (drop (Suc i) (take (Suc j) p))) @ (drop (Suc j) p)"
    using \<open>i < j\<close> by simp 
  finally have "p = (take (Suc i) p) @ (drop (Suc i) (take (Suc j) p)) @ (drop (Suc j) p)"
    by simp

  then have "path M q ((take (Suc i) p) @ (drop (Suc i) (take (Suc j) p)) @ (drop (Suc j) p))"
       and  "path M q (((take (Suc i) p) @ (drop (Suc i) (take (Suc j) p))) @ (drop (Suc j) p))"
    using \<open>path M q p\<close> by auto

  have "path M q (take (Suc i) p)" and "path M (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p) @ drop (Suc j) p)"
    using path_append_elim[OF \<open>path M q ((take (Suc i) p) @ (drop (Suc i) (take (Suc j) p)) @ (drop (Suc j) p))\<close>] 
    by blast+

  
  have *: "(take (Suc i) p @ drop (Suc i) (take (Suc j) p)) = (take (Suc j) p)"
      using \<open>i < j\<close> append_take_drop_id
      by (metis \<open>(take (Suc i) (take (Suc j) p) @ drop (Suc i) (take (Suc j) p)) @ drop (Suc j) p = (take (Suc i) p @ drop (Suc i) (take (Suc j) p)) @ drop (Suc j) p\<close> append_same_eq)

  have "path M q (take (Suc j) p)" and "path M (target q (take (Suc j) p)) (drop (Suc j) p)"
    using path_append_elim[OF \<open>path M q (((take (Suc i) p) @ (drop (Suc i) (take (Suc j) p))) @ (drop (Suc j) p))\<close>] 
    unfolding *
    by blast+

  have **: "(target q (take (Suc j) p)) = (target q (take (Suc i) p))"
  proof -
    have "p ! i = last (take (Suc i) p)"
      by (metis Suc_lessD assms(3) assms(4) less_trans_Suc take_last_index)
    moreover have "p ! j = last (take (Suc j) p)"
      by (simp add: assms(4) take_last_index)
    ultimately show ?thesis
      using assms(2) unfolding * target.simps visited_states.simps
      by (simp add: last_map) 
  qed

  show "path M q ((take (Suc i) p) @ (drop (Suc j) p))"
    using \<open>path M q (take (Suc i) p)\<close> \<open>path M (target q (take (Suc j) p)) (drop (Suc j) p)\<close> unfolding ** by auto

  show "target q ((take (Suc i) p) @ (drop (Suc j) p)) = target q p"
    by (metis "**" append_take_drop_id path_append_target)
    
  show "length ((take (Suc i) p) @ (drop (Suc j) p)) < length p"
  proof -
    have ***: "length p = length ((take (Suc j) p) @ (drop (Suc j) p))"
      by auto

    have "length (take (Suc i) p) < length (take (Suc j) p)"
      using assms(3,4)
      by (simp add: min_absorb2) 

    have scheme: "\<And> a b c . length a < length b \<Longrightarrow> length (a@c) < length (b@c)"
      by auto
    
    show ?thesis 
      unfolding *** using scheme[OF \<open>length (take (Suc i) p) < length (take (Suc j) p)\<close>, of "(drop (Suc j) p)"]
      by assumption
  qed

  show "path M (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p))"
    using \<open>path M (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p) @ drop (Suc j) p)\<close> by blast

  show "target (target q (take (Suc i) p)) (drop (Suc i) (take (Suc j) p)) = (target q (take (Suc i) p))"
    by (metis "*" "**" path_append_target) 
qed
      

lemma path_prefix_take :
  assumes "path M q p"
  shows "path M q (take i p)"
proof -
  have "p = (take i p)@(drop i p)" by auto
  then have "path M q ((take i p)@(drop i p))" using assms by auto
  then show ?thesis
    by blast 
qed



subsection \<open>Acyclic Paths\<close>

lemma cyclic_path_loop :
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
shows "\<exists> p1 p2 p3 . p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target q p1 = target q (p1@p2)"
using assms proof (induction p arbitrary: q)
  case (nil M q)
  then show ?case by auto
next
  case (cons t M ts)
  then show ?case 
  proof (cases "distinct (visited_states (t_target t) ts)")
    case True
    then have "q \<in> set (visited_states (t_target t) ts)"
      using cons.prems by simp 
    then obtain p2 p3 where "ts = p2@p3" and "target (t_target t) p2 = q" 
      using visited_states_prefix[of q "t_target t" ts] by blast
    then have "(t#ts) = []@(t#p2)@p3 \<and> (t#p2) \<noteq> [] \<and> target q [] = target q ([]@(t#p2))"
      using cons.hyps by auto
    then show ?thesis by blast
  next
    case False
    then obtain p1 p2 p3 where "ts = p1@p2@p3" and "p2 \<noteq> []" 
                           and "target (t_target t) p1 = target (t_target t) (p1@p2)" 
      using cons.IH by blast
    then have "t#ts = (t#p1)@p2@p3 \<and> p2 \<noteq> [] \<and> target q (t#p1) = target q ((t#p1)@p2)"
      by simp
    then show ?thesis by blast    
  qed
qed


lemma cyclic_path_pumping :
  assumes "path M (initial M) p" 
      and "\<not> distinct (visited_states (initial M) p)"
  shows "\<exists> p . path M (initial M) p \<and> length p \<ge> n"
proof -
  from assms obtain p1 p2 p3 where "p = p1 @ p2 @ p3" and "p2 \<noteq> []" 
                               and "target (initial M) p1 = target (initial M) (p1 @ p2)"
    using cyclic_path_loop[of M "initial M" p] by blast
  then have "path M (target (initial M) p1) p3"
    using path_suffix[of M "initial M" "p1@p2" p3] \<open>path M (initial M) p\<close> by auto
  
  have "path M (initial M) p1"
    using path_prefix[of M "initial M" p1 "p2@p3"] \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> 
    by auto
  have "path M (initial M) ((p1@p2)@p3)"
    using \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> 
    by auto
  have "path M (target (initial M) p1) p2" 
    using path_suffix[of M "initial M" p1 p2, OF path_prefix[of M "initial M" "p1@p2" p3, OF \<open>path M (initial M) ((p1@p2)@p3)\<close>]] 
    by assumption
  have "target (target (initial M) p1) p2 = (target (initial M) p1)"
    using path_append_target \<open>target (initial M) p1 = target (initial M) (p1 @ p2)\<close> 
    by auto
  
  have "path M (initial M) (p1 @ (concat (replicate n p2)) @ p3)"  
  proof (induction n)
    case 0 
    then show ?case 
      using path_append[OF \<open>path M (initial M) p1\<close> \<open>path M (target (initial M) p1) p3\<close>]  
      by auto
  next
    case (Suc n)
    then show ?case
      using \<open>path M (target (initial M) p1) p2\<close> \<open>target (target (initial M) p1) p2 = target (initial M) p1\<close> 
      by auto 
  qed
  moreover have "length (p1 @ (concat (replicate n p2)) @ p3) \<ge> n"
  proof -
    have "length (concat (replicate n p2)) = n * (length p2)" 
      using concat_replicate_length by metis
    moreover have "length p2 > 0"
      using \<open>p2 \<noteq> []\<close> by auto
    ultimately have "length (concat (replicate n p2)) \<ge> n"
      by (simp add: Suc_leI)
    then show ?thesis by auto
  qed
  ultimately show "\<exists> p . path M (initial M) p \<and> length p \<ge> n" by blast
qed


lemma cyclic_path_shortening : 
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
shows "\<exists> p' . path M q p' \<and> target q p' = target q p \<and> length p' < length p"
proof -
  obtain p1 p2 p3 where *: "p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target q p1 = target q (p1@p2)" 
    using cyclic_path_loop[OF assms] by blast
  then have "path M q (p1@p3)"
    using assms(1) by force
  moreover have "target q (p1@p3) = target q p"
    by (metis (full_types) * path_append_target)
  moreover have "length (p1@p3) < length p"
    using * by auto
  ultimately show ?thesis by blast
qed


lemma acyclic_path_from_cyclic_path :
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
obtains p' where "path M q p'" and "target q p = target q p'" and "distinct (visited_states q p')"
proof -
  
  let ?paths = "{p' . (path M q p' \<and> target q p' = target q p \<and> length p' \<le> length p)}"
  let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
  have "?paths \<noteq> empty" 
    using assms(1) by auto
  moreover have "finite ?paths" 
    using paths_finite[of M q "length p"]
    by (metis (no_types, lifting) Collect_mono rev_finite_subset)
  ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" 
    by (meson arg_min_nat_lemma equals0I)
  then have "path M q ?minPath" and "target q ?minPath = target q p" 
    by auto
  
  moreover have "distinct (visited_states q ?minPath)"
  proof (rule ccontr)
    assume "\<not> distinct (visited_states q ?minPath)"
    have "\<exists> p' . path M q p' \<and> target q p' = target q p \<and> length p' < length ?minPath" 
      using cyclic_path_shortening[OF \<open>path M q ?minPath\<close> \<open>\<not> distinct (visited_states q ?minPath)\<close>] minPath_def
            \<open>target q ?minPath= target q p\<close> by auto
    then show "False" 
      using minPath_def using arg_min_nat_le dual_order.strict_trans1 by auto 
  qed

  ultimately show ?thesis
    by (simp add: that)
qed    


lemma acyclic_path_length_limit :
  assumes "path M q p"
  and     "distinct (visited_states q p)"
shows "length p < size M"
proof (rule ccontr)
  assume *: "\<not> length p < size M"
  then have "length p \<ge> card (states M)"
    using size_def by auto
  then have "length (visited_states q p) > card (states M)"
    by auto
  moreover have "set (visited_states q p) \<subseteq> states M"
    by (metis assms(1) path_prefix path_target_is_state subsetI visited_states_prefix)
  ultimately have "\<not> distinct (visited_states q p)"
    using distinct_card[OF assms(2)] 
    using List.finite_set[of "visited_states q p"]
    by (metis card_mono fsm_states_finite leD) 
  then show "False" using assms(2) by blast
qed





subsection \<open>Reachable States\<close>

definition reachable :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable M q = (\<exists> p . path M (initial M) p \<and> target (initial M) p = q)"

definition reachable_states :: "('a,'b,'c) fsm \<Rightarrow> 'a set" where
  "reachable_states M  = {target (initial M) p | p . path M (initial M) p }"

abbreviation "size_r M \<equiv> card (reachable_states M)"

lemma acyclic_paths_set :
  "acyclic_paths_up_to_length M q (size M - 1) = {p . path M q p \<and> distinct (visited_states q p)}"
  unfolding acyclic_paths_up_to_length.simps using acyclic_path_length_limit[of M q]
  by (metis (no_types, lifting) One_nat_def Suc_pred cyclic_path_shortening leD list.size(3) 
       not_less_eq_eq not_less_zero path.intros(1) path_begin_state) 


(* inefficient calculation, as a state may be target of a large number of acyclic paths *)
lemma reachable_states_code[code] : 
  "reachable_states M = image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
proof -
  have "\<And> q' . q' \<in> reachable_states M 
            \<Longrightarrow> q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
  proof -
    fix q' assume "q' \<in> reachable_states M"
    then obtain p where "path M (initial M) p" and "target (initial M) p = q'"
      unfolding reachable_states_def by blast
    
    obtain p' where "path M (initial M) p'" and "target (initial M) p' = q'" 
                and "distinct (visited_states (initial M) p')"
    proof (cases "distinct (visited_states (initial M) p)")
      case True
      then show ?thesis using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q'\<close> that by auto
    next
      case False
      then show ?thesis 
        using acyclic_path_from_cyclic_path[OF \<open>path M (initial M) p\<close>] 
        unfolding \<open>target (initial M) p = q'\<close> using that by blast
    qed
    then show "q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_set by force
  qed
  moreover have "\<And> q' . q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1)) 
                    \<Longrightarrow> q' \<in> reachable_states M"
    unfolding reachable_states_def acyclic_paths_set by blast
  ultimately show ?thesis by blast
qed



lemma reachable_states_intro[intro!] :
  assumes "path M (initial M) p"
  shows "target (initial M) p \<in> reachable_states M"
  using assms unfolding reachable_states_def by auto


lemma reachable_states_initial :
  "initial M \<in> reachable_states M"
  unfolding reachable_states_def by auto


lemma reachable_states_next : 
  assumes "q \<in> reachable_states M" and "t \<in> transitions M" and "t_source t = q" 
  shows "t_target t \<in> reachable_states M" 
proof -
  from \<open>q \<in> reachable_states M\<close> obtain p where * :"path M (initial M) p"
                                        and   **:"target (initial M) p = q"
    unfolding reachable_states_def by auto

  then have "path M (initial M) (p@[t])" using assms(2,3) path_append_transition by metis
  moreover have "target (initial M) (p@[t]) = t_target t" by auto
  ultimately show ?thesis 
    unfolding reachable_states_def
    by (metis (mono_tags, lifting) mem_Collect_eq)
qed


lemma reachable_states_path :
  assumes "q \<in> reachable_states M"
  and     "path M q p"
  and     "t \<in> set p"
shows "t_source t \<in> reachable_states M"
using assms unfolding reachable_states_def proof (induction p arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons t' p')
  then show ?case proof (cases "t = t'")
    case True
    then show ?thesis using Cons.prems(1,2) by force
  next
    case False then show ?thesis using Cons
      by (metis (mono_tags, lifting) path_cons_elim reachable_states_def reachable_states_next 
            set_ConsD) 
  qed
qed


lemma reachable_states_initial_or_target :
  assumes "q \<in> reachable_states M"
  shows "q = initial M \<or> (\<exists> t \<in> transitions M . t_source t \<in> reachable_states M \<and> t_target t = q)"
proof -
  obtain p where "path M (initial M) p" and "target (initial M) p = q"
    using assms unfolding reachable_states_def by auto 
  
  show ?thesis proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> by auto
  next
    case (snoc p' t)
    
    have "t \<in> transitions M"
      using \<open>path M (initial M) p\<close> unfolding snoc by auto
    moreover have "t_target t = q"
      using \<open>target (initial M) p = q\<close> unfolding snoc by auto
    moreover have "t_source t \<in> reachable_states M"
      using \<open>path M (initial M) p\<close> unfolding snoc
      by (metis append_is_Nil_conv last_in_set last_snoc not_Cons_self2 reachable_states_initial reachable_states_path) 

    ultimately show ?thesis
      by blast 
  qed 
qed

lemma reachable_state_is_state : 
  "q \<in> reachable_states M \<Longrightarrow> q \<in> states M" 
  unfolding reachable_states_def using path_target_is_state by fastforce 

lemma reachable_states_finite : "finite (reachable_states M)"
  using fsm_states_finite[of M] reachable_state_is_state[of _ M]
  by (meson finite_subset subset_eq)  


subsection \<open>Language\<close>

abbreviation "p_io (p :: ('state,'input,'output) path) \<equiv> map (\<lambda> t . (t_input t, t_output t)) p"

fun language_state_for_input :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> ('input \<times> 'output) list set" where
  "language_state_for_input M q xs = {p_io p | p . path M q p \<and> map fst (p_io p) = xs}"

fun LS\<^sub>i\<^sub>n :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> 'input list set \<Rightarrow> ('input \<times> 'output) list set" where
  "LS\<^sub>i\<^sub>n M q xss = {p_io p | p . path M q p \<and> map fst (p_io p) \<in> xss}"

abbreviation(input) "L\<^sub>i\<^sub>n M \<equiv> LS\<^sub>i\<^sub>n M (initial M)"

lemma language_state_for_input_inputs : 
  assumes "io \<in> language_state_for_input M q xs"
  shows "map fst io = xs" 
  using assms by auto

lemma language_state_for_inputs_inputs : 
  assumes "io \<in> LS\<^sub>i\<^sub>n M q xss"
  shows "map fst io \<in> xss" using assms by auto 


fun LS :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> ('input \<times> 'output) list set" where
  "LS M q = { p_io p | p . path M q p }"

abbreviation "L M \<equiv> LS M (initial M)"

lemma language_state_containment :
  assumes "path M q p"
  and     "p_io p = io"
shows "io \<in> LS M q"
  using assms by auto

lemma language_prefix : 
  assumes "io1@io2 \<in> LS M q"
  shows "io1 \<in> LS M q"
proof -
  obtain p where "path M q p" and "p_io p = io1@io2" 
    using assms by auto
  let ?tp = "take (length io1) p"
  have "path M q ?tp"
    by (metis (no_types) \<open>path M q p\<close> append_take_drop_id path_prefix) 
  moreover have "p_io ?tp = io1"
    using \<open>p_io p = io1@io2\<close> by (metis append_eq_conv_conj take_map) 
  ultimately show ?thesis
    by force 
qed

lemma language_contains_empty_sequence : "[] \<in> L M" 
  by auto


lemma language_state_split :
  assumes "io1 @ io2 \<in> LS M q1"
  obtains  p1 p2 where "path M q1 p1" 
                   and "path M (target q1 p1) p2"  
                   and "p_io p1 = io1" 
                   and "p_io p2 = io2"
proof -
  obtain p12 where "path M q1 p12" and "p_io p12 = io1 @ io2"
    using assms unfolding LS.simps by auto

  let ?p1 = "take (length io1) p12"
  let ?p2 = "drop (length io1) p12"

  have "p12 = ?p1 @ ?p2" 
    by auto
  then have "path M q1 (?p1 @ ?p2)"
    using \<open>path M q1 p12\<close> by auto

  have "path M q1 ?p1" and "path M (target q1 ?p1) ?p2"
    using path_append_elim[OF \<open>path M q1 (?p1 @ ?p2)\<close>] by blast+
  moreover have "p_io ?p1 = io1"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis append_eq_conv_conj take_map)
  moreover have "p_io ?p2 = io2"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis (no_types) \<open>p_io p12 = io1 @ io2\<close> append_eq_conv_conj drop_map) 
  ultimately show ?thesis using that by blast
qed


lemma language_initial_path_append_transition :
  assumes "ios @ [io] \<in> L M"
  obtains p t where "path M (initial M) (p@[t])" and "p_io (p@[t]) = ios @ [io]"
proof -
  obtain pt where "path M (initial M) pt" and "p_io pt = ios @ [io]"
    using assms unfolding LS.simps by auto
  then have "pt \<noteq> []"
    by auto
  then obtain p t where "pt = p @ [t]"
    using rev_exhaust by blast  
  then have "path M (initial M) (p@[t])" and "p_io (p@[t]) = ios @ [io]"
    using \<open>path M (initial M) pt\<close> \<open>p_io pt = ios @ [io]\<close> by auto
  then show ?thesis using that by simp
qed

lemma language_path_append_transition :
  assumes "ios @ [io] \<in> LS M q"
  obtains p t where "path M q (p@[t])" and "p_io (p@[t]) = ios @ [io]"
proof -
  obtain pt where "path M q pt" and "p_io pt = ios @ [io]"
    using assms unfolding LS.simps by auto
  then have "pt \<noteq> []"
    by auto
  then obtain p t where "pt = p @ [t]"
    using rev_exhaust by blast  
  then have "path M q (p@[t])" and "p_io (p@[t]) = ios @ [io]"
    using \<open>path M q pt\<close> \<open>p_io pt = ios @ [io]\<close> by auto
  then show ?thesis using that by simp
qed


lemma language_split :
  assumes "io1@io2 \<in> L M"
  obtains p1 p2 where "path M (initial M) (p1@p2)" and "p_io p1 = io1" and "p_io p2 = io2"
proof -
  from assms obtain p where "path M (initial M) p" and "p_io p = io1 @ io2"
    by auto

  let ?p1 = "take (length io1) p"
  let ?p2 = "drop (length io1) p"

  have "path M (initial M) (?p1@?p2)"
    using \<open>path M (initial M) p\<close> by simp 
  moreover have "p_io ?p1 = io1" 
    using \<open>p_io p = io1 @ io2\<close>
    by (metis append_eq_conv_conj take_map) 
  moreover have "p_io ?p2 = io2" 
    using \<open>p_io p = io1 @ io2\<close>
    by (metis append_eq_conv_conj drop_map)
  ultimately show ?thesis using that by blast
qed



lemma language_io : 
  assumes "io \<in> LS M q"
  and     "(x,y) \<in> set io"
shows "x \<in> (inputs M)"
and   "y \<in> outputs M"
proof -
  obtain p where "path M q p" and "p_io p = io"
    using \<open>io \<in> LS M q\<close> by auto
  then obtain t where "t \<in> set p" and "t_input t = x" and "t_output t = y"
    using \<open>(x,y) \<in> set io\<close> by auto
  
  have "t \<in> transitions M"
    using \<open>path M q p\<close> \<open>t \<in> set p\<close>
    by (induction p; auto)

  show "x \<in> (inputs M)"
    using \<open>t \<in> transitions M\<close> \<open>t_input t = x\<close> by auto

  show "y \<in> outputs M"
    using \<open>t \<in> transitions M\<close> \<open>t_output t = y\<close> by auto
qed


lemma path_io_split :
  assumes "path M q p"
  and     "p_io p = io1@io2"
shows "path M q (take (length io1) p)"
and   "p_io (take (length io1) p) = io1"
and   "path M (target q (take (length io1) p)) (drop (length io1) p)"
and   "p_io (drop (length io1) p) = io2"
proof -
  have "length io1 \<le> length p"
    using \<open>p_io p = io1@io2\<close> 
    unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric]
    by auto

  have "p = (take (length io1) p)@(drop (length io1) p)"
    by simp
  then have *: "path M q ((take (length io1) p)@(drop (length io1) p))"
    using \<open>path M q p\<close> by auto

  show "path M q (take (length io1) p)"
       and  "path M (target q (take (length io1) p)) (drop (length io1) p)"
    using path_append_elim[OF *] by blast+

  show "p_io (take (length io1) p) = io1"
    using \<open>p = (take (length io1) p)@(drop (length io1) p)\<close> \<open>p_io p = io1@io2\<close>
    by (metis append_eq_conv_conj take_map) 

  show "p_io (drop (length io1) p) = io2"
    using \<open>p = (take (length io1) p)@(drop (length io1) p)\<close> \<open>p_io p = io1@io2\<close>
    by (metis append_eq_conv_conj drop_map)
qed


lemma language_intro :
  assumes "path M q p"
  shows "p_io p \<in> LS M q"
  using assms unfolding LS.simps by auto


lemma language_prefix_append :
  assumes "io1 @ (p_io p) \<in> L M"
shows   "io1 @ p_io (take i p) \<in> L M"
proof -
  fix i
  have "p_io p = (p_io (take i p)) @ (p_io (drop i p))"
    by (metis append_take_drop_id map_append) 
  then have "(io1 @ (p_io (take i p))) @ (p_io (drop i p)) \<in> L M"
    using \<open>io1 @ p_io p \<in> L M\<close> by auto
  show "io1 @ p_io (take i p) \<in> L M" 
    using language_prefix[OF \<open>(io1 @ (p_io (take i p))) @ (p_io (drop i p)) \<in> L M\<close>] 
    by assumption
qed


lemma language_finite: "finite {io . io \<in> L M \<and> length io \<le> k}"
proof -
  have "{io . io \<in> L M \<and> length io \<le> k} \<subseteq> p_io  ` {p. path M (FSM.initial M) p \<and> length p \<le> k}"
    by auto
  then show ?thesis
    using paths_finite[of M "initial M" k]
    using finite_surj by auto 
qed

lemma LS_prepend_transition : 
  assumes "t \<in> transitions M"
  and     "io \<in> LS M (t_target t)"
shows "(t_input t, t_output t) # io \<in> LS M (t_source t)"
proof -
  obtain p where "path M (t_target t) p" and "p_io p = io"
    using assms(2) by auto
  then have "path M (t_source t) (t#p)" and "p_io (t#p) = (t_input t, t_output t) # io"
    using assms(1) by auto
  then show ?thesis 
    unfolding LS.simps
    by (metis (mono_tags, lifting) mem_Collect_eq) 
qed

lemma language_empty_IO :
  assumes "inputs M = {} \<or> outputs M = {}"
  shows "L M = {[]}"
proof -
  consider "inputs M = {}" | "outputs M = {}" using assms by blast
  then show ?thesis proof cases
    case 1

    show "L M = {[]}"
      using language_io(1)[of _ M "initial M"] unfolding 1
      by (metis (no_types, opaque_lifting) ex_in_conv is_singletonI' is_singleton_the_elem language_contains_empty_sequence set_empty2 singleton_iff surj_pair) 
  next
    case 2
    show "L M = {[]}"
      using language_io(2)[of _ M "initial M"] unfolding 2
      by (metis (no_types, opaque_lifting) ex_in_conv is_singletonI' is_singleton_the_elem language_contains_empty_sequence set_empty2 singleton_iff surj_pair) 
  qed
qed

lemma language_equivalence_from_isomorphism_helper :
  assumes "bij_betw f (states M1) (states M2)"
  and     "f (initial M1) = initial M2"
  and     "\<And> q x y q' . q \<in> states M1 \<Longrightarrow> q' \<in> states M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M1 \<longleftrightarrow> (f q,x,y,f q') \<in> transitions M2"
  and     "q \<in> states M1"
shows "LS M1 q \<subseteq> LS M2 (f q)"
proof 
  fix io assume "io \<in> LS M1 q"

  then obtain p where "path M1 q p" and "p_io p = io"
    by auto

  let ?f = "\<lambda>(q,x,y,q') . (f q,x,y,f q')"
  let ?p = "map ?f p"

  have "f q \<in> states M2"
    using assms(1,4)
    using bij_betwE by auto 

  have "path M2 (f q) ?p"
  using \<open>path M1 q p\<close> proof (induction p rule: rev_induct)
    case Nil
    show ?case using \<open>f q \<in> states M2\<close> by auto
  next
    case (snoc a p)
    then have "path M2 (f q) (map ?f p)"
      by auto

    have "target (f q) (map ?f p) = f (target q p)"
      using \<open>f (initial M1) = initial M2\<close> assms(2)
      by (induction p; auto)
    then have "t_source (?f a) = target (f q) (map ?f p)"
      by (metis (no_types, lifting) case_prod_beta' fst_conv path_append_transition_elim(3) snoc.prems)
  
    have "a \<in> transitions M1"
      using snoc.prems by auto
    then have "?f a \<in> transitions M2"
      by (metis (mono_tags, lifting) assms(3) case_prod_beta fsm_transition_source fsm_transition_target surjective_pairing)
      
    have "map ?f (p@[a]) = (map ?f p)@[?f a]"
      by auto

    show ?case 
      unfolding \<open>map ?f (p@[a]) = (map ?f p)@[?f a]\<close>
      using path_append_transition[OF \<open>path M2 (f q) (map ?f p)\<close> \<open>?f a \<in> transitions M2\<close> \<open>t_source (?f a) = target (f q) (map ?f p)\<close>]
      by assumption
  qed
  moreover have "p_io ?p = io"
    using \<open>p_io p = io\<close>
    by (induction p; auto)
  ultimately show "io \<in> LS M2 (f q)"
    using language_state_containment by fastforce
qed


lemma language_equivalence_from_isomorphism :
  assumes "bij_betw f (states M1) (states M2)"
  and     "f (initial M1) = initial M2"
  and     "\<And> q x y q' . q \<in> states M1 \<Longrightarrow> q' \<in> states M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M1 \<longleftrightarrow> (f q,x,y,f q') \<in> transitions M2"
  and     "q \<in> states M1"
shows "LS M1 q = LS M2 (f q)"
proof 
  show "LS M1 q \<subseteq> LS M2 (f q)"
    using language_equivalence_from_isomorphism_helper[OF assms] .

  have "f q \<in> states M2"
    using assms(1,4)
    using bij_betwE by auto 
  have "(inv_into (FSM.states M1) f (f q)) = q"
    by (meson assms(1) assms(4) bij_betw_imp_inj_on inv_into_f_f) 


  have "bij_betw (inv_into (states M1) f) (states M2) (states M1)"
    using bij_betw_inv_into[OF assms(1)] .
  moreover have "(inv_into (states M1) f) (initial M2) = (initial M1)"
    using assms(1,2)
    by (metis bij_betw_inv_into_left fsm_initial) 
  moreover have "\<And> q x y q' . q \<in> states M2 \<Longrightarrow> q' \<in> states M2 \<Longrightarrow> (q,x,y,q') \<in> transitions M2 \<longleftrightarrow> ((inv_into (states M1) f) q,x,y,(inv_into (states M1) f) q') \<in> transitions M1"
  proof 
    fix q x y q' assume "q \<in> states M2" and "q' \<in> states M2"
    
    show "(q,x,y,q') \<in> transitions M2 \<Longrightarrow> ((inv_into (states M1) f) q,x,y,(inv_into (states M1) f) q') \<in> transitions M1"
    proof -
      assume a1: "(q, x, y, q') \<in> FSM.transitions M2"
      have f2: "\<forall>f B A. \<not> bij_betw f B A \<or> (\<forall>b. (b::'b) \<notin> B \<or> (f b::'a) \<in> A)"
        using bij_betwE by blast
      then have f3: "inv_into (states M1) f q \<in> states M1"
        using \<open>q \<in> states M2\<close> calculation(1) by blast
      have "inv_into (states M1) f q' \<in> states M1"
        using f2 \<open>q' \<in> states M2\<close> calculation(1) by blast
      then show ?thesis
        using f3 a1 \<open>q \<in> states M2\<close> \<open>q' \<in> states M2\<close> assms(1) assms(3) bij_betw_inv_into_right by fastforce
    qed

    show "((inv_into (states M1) f) q,x,y,(inv_into (states M1) f) q') \<in> transitions M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M2"
    proof -
      assume a1: "(inv_into (states M1) f q, x, y, inv_into (states M1) f q') \<in> FSM.transitions M1"
      have f2: "\<forall>f B A. \<not> bij_betw f B A \<or> (\<forall>b. (b::'b) \<notin> B \<or> (f b::'a) \<in> A)"
        by (metis (full_types) bij_betwE)
      then have f3: "inv_into (states M1) f q' \<in> states M1"
        using \<open>q' \<in> states M2\<close> calculation(1) by blast
      have "inv_into (states M1) f q \<in> states M1"
        using f2 \<open>q \<in> states M2\<close> calculation(1) by blast
      then show ?thesis
        using f3 a1 \<open>q \<in> states M2\<close> \<open>q' \<in> states M2\<close> assms(1) assms(3) bij_betw_inv_into_right by fastforce
    qed
  qed
  ultimately show "LS M2 (f q) \<subseteq> LS M1 q"
    using language_equivalence_from_isomorphism_helper[of "(inv_into (states M1) f)" M2 M1, OF _ _ _ \<open>f q \<in> states M2\<close>]
    unfolding \<open>(inv_into (FSM.states M1) f (f q)) = q\<close>
    by blast
qed



lemma language_equivalence_from_isomorphism_helper_reachable :
  assumes "bij_betw f (reachable_states M1) (reachable_states M2)"
  and     "f (initial M1) = initial M2"
  and     "\<And> q x y q' . q \<in> reachable_states M1 \<Longrightarrow> q' \<in> reachable_states M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M1 \<longleftrightarrow> (f q,x,y,f q') \<in> transitions M2"
shows "L M1 \<subseteq> L M2"
proof 
  fix io assume "io \<in> L M1"

  then obtain p where "path M1 (initial M1) p" and "p_io p = io"
    by auto

  let ?f = "\<lambda>(q,x,y,q') . (f q,x,y,f q')"
  let ?p = "map ?f p"

  have "path M2 (initial M2) ?p"
  using \<open>path M1 (initial M1) p\<close> proof (induction p rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc a p)
    then have "path M2 (initial M2) (map ?f p)"
      by auto

    have "target (initial M2) (map ?f p) = f (target (initial M1) p)"
      using \<open>f (initial M1) = initial M2\<close> assms(2)
      by (induction p; auto)
    then have "t_source (?f a) = target (initial M2) (map ?f p)"
      by (metis (no_types, lifting) case_prod_beta' fst_conv path_append_transition_elim(3) snoc.prems)
      

    have "t_source a \<in> reachable_states M1"
      using \<open>path M1 (FSM.initial M1) (p @ [a])\<close>
      by (metis path_append_transition_elim(3) path_prefix reachable_states_intro) 
    have "t_target a \<in> reachable_states M1"
      using \<open>path M1 (FSM.initial M1) (p @ [a])\<close>
      by (meson \<open>t_source a \<in> reachable_states M1\<close> path_append_transition_elim(2) reachable_states_next) 

    have "a \<in> transitions M1"
      using snoc.prems by auto
    then have "?f a \<in> transitions M2"
      using assms(3)[OF \<open>t_source a \<in> reachable_states M1\<close> \<open>t_target a \<in> reachable_states M1\<close>]
      by (metis (mono_tags, lifting) prod.case_eq_if prod.collapse)
      
    have "map ?f (p@[a]) = (map ?f p)@[?f a]"
      by auto

    show ?case 
      unfolding \<open>map ?f (p@[a]) = (map ?f p)@[?f a]\<close>
      using path_append_transition[OF \<open>path M2 (initial M2) (map ?f p)\<close> \<open>?f a \<in> transitions M2\<close> \<open>t_source (?f a) = target (initial M2) (map ?f p)\<close>]
      by assumption
  qed
  moreover have "p_io ?p = io"
    using \<open>p_io p = io\<close>
    by (induction p; auto)
  ultimately show "io \<in> L M2"
    using language_state_containment by fastforce
qed
    


lemma language_equivalence_from_isomorphism_reachable :
  assumes "bij_betw f (reachable_states M1) (reachable_states M2)"
  and     "f (initial M1) = initial M2"
  and     "\<And> q x y q' . q \<in> reachable_states M1 \<Longrightarrow> q' \<in> reachable_states M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M1 \<longleftrightarrow> (f q,x,y,f q') \<in> transitions M2"
shows "L M1 = L M2"
proof 
  show "L M1 \<subseteq> L M2"
    using language_equivalence_from_isomorphism_helper_reachable[OF assms] .

  have "bij_betw (inv_into (reachable_states M1) f) (reachable_states M2) (reachable_states M1)"
    using bij_betw_inv_into[OF assms(1)] .
  moreover have "(inv_into (reachable_states M1) f) (initial M2) = (initial M1)"
    using assms(1,2) reachable_states_initial
    by (metis bij_betw_inv_into_left) 
  moreover have "\<And> q x y q' . q \<in> reachable_states M2 \<Longrightarrow> q' \<in> reachable_states M2 \<Longrightarrow> (q,x,y,q') \<in> transitions M2 \<longleftrightarrow> ((inv_into (reachable_states M1) f) q,x,y,(inv_into (reachable_states M1) f) q') \<in> transitions M1"
  proof 
    fix q x y q' assume "q \<in> reachable_states M2" and "q' \<in> reachable_states M2"
    
    show "(q,x,y,q') \<in> transitions M2 \<Longrightarrow> ((inv_into (reachable_states M1) f) q,x,y,(inv_into (reachable_states M1) f) q') \<in> transitions M1"
    proof -
      assume a1: "(q, x, y, q') \<in> FSM.transitions M2"
      have f2: "\<forall>f B A. \<not> bij_betw f B A \<or> (\<forall>b. (b::'b) \<notin> B \<or> (f b::'a) \<in> A)"
        using bij_betwE by blast
      then have f3: "inv_into (FSM.reachable_states M1) f q \<in> FSM.reachable_states M1"
        using \<open>q \<in> FSM.reachable_states M2\<close> calculation(1) by blast
      have "inv_into (FSM.reachable_states M1) f q' \<in> FSM.reachable_states M1"
        using f2 \<open>q' \<in> FSM.reachable_states M2\<close> calculation(1) by blast
      then show ?thesis
        using f3 a1 \<open>q \<in> FSM.reachable_states M2\<close> \<open>q' \<in> FSM.reachable_states M2\<close> assms(1) assms(3) bij_betw_inv_into_right by fastforce
    qed

    show "((inv_into (reachable_states M1) f) q,x,y,(inv_into (reachable_states M1) f) q') \<in> transitions M1 \<Longrightarrow> (q,x,y,q') \<in> transitions M2"
    proof -
      assume a1: "(inv_into (FSM.reachable_states M1) f q, x, y, inv_into (FSM.reachable_states M1) f q') \<in> FSM.transitions M1"
      have f2: "\<forall>f B A. \<not> bij_betw f B A \<or> (\<forall>b. (b::'b) \<notin> B \<or> (f b::'a) \<in> A)"
        by (metis (full_types) bij_betwE)
      then have f3: "inv_into (FSM.reachable_states M1) f q' \<in> FSM.reachable_states M1"
        using \<open>q' \<in> FSM.reachable_states M2\<close> calculation(1) by blast
      have "inv_into (FSM.reachable_states M1) f q \<in> FSM.reachable_states M1"
        using f2 \<open>q \<in> FSM.reachable_states M2\<close> calculation(1) by blast
      then show ?thesis
        using f3 a1 \<open>q \<in> FSM.reachable_states M2\<close> \<open>q' \<in> FSM.reachable_states M2\<close> assms(1) assms(3) bij_betw_inv_into_right by fastforce
    qed
  qed
  ultimately show "L M2 \<subseteq> L M1"
    using language_equivalence_from_isomorphism_helper_reachable[of "(inv_into (reachable_states M1) f)" M2 M1]
    by blast
qed

lemma language_empty_io :
  assumes "inputs M = {} \<or> outputs M = {}"
  shows "L M = {[]}"
proof -
  have "transitions M = {}"
    using assms fsm_transition_input fsm_transition_output
    by auto
  then have "\<And> p . path M (initial M) p \<Longrightarrow> p = []"
    by (metis empty_iff path.cases)
  then show ?thesis 
    unfolding LS.simps
    by blast
qed



subsection \<open>Basic FSM Properties\<close>

subsubsection \<open>Completely Specified\<close>

fun completely_specified :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "completely_specified M = (\<forall> q \<in> states M . \<forall> x \<in> inputs M . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x)"


lemma completely_specified_alt_def : 
  "completely_specified M = (\<forall> q \<in> states M . \<forall> x \<in> inputs M . \<exists> q' y . (q,x,y,q') \<in> transitions M)"
  by force

lemma completely_specified_alt_def_h : 
  "completely_specified M = (\<forall> q \<in> states M . \<forall> x \<in> inputs M . h M (q,x) \<noteq> {})"
  by force



fun completely_specified_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "completely_specified_state M q = (\<forall> x \<in> inputs M . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_states :
  "completely_specified M = (\<forall> q \<in> states M . completely_specified_state M q)"
  unfolding completely_specified.simps completely_specified_state.simps by force

lemma completely_specified_state_alt_def_h : 
  "completely_specified_state M q = (\<forall> x \<in> inputs M . h M (q,x) \<noteq> {})"
  by force


lemma completely_specified_path_extension : 
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "path M q p"
  and     "x \<in> (inputs M)"
obtains t where "t \<in> transitions M" and "t_input t = x" and "t_source t = target q p"
proof -
  have "target q p \<in> states M"
    using path_target_is_state \<open>path M q p\<close> by metis
  then obtain t where "t \<in> transitions M" and "t_input t = x" and "t_source t = target q p"
    using \<open>completely_specified M\<close> \<open>x \<in> (inputs M)\<close> 
    unfolding completely_specified.simps by blast
  then show ?thesis using that by blast
qed


lemma completely_specified_language_extension :
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "io \<in> LS M q"
  and     "x \<in> (inputs M)"
obtains y where "io@[(x,y)] \<in> LS M q"
proof -
  obtain p where "path M q p" and "p_io p = io"
    using \<open>io \<in> LS M q\<close> by auto
  
  moreover obtain t where "t \<in> transitions M" and "t_input t = x" and "t_source t = target q p"
    using completely_specified_path_extension[OF assms(1,2) \<open>path M q p\<close> assms(4)] by blast

  ultimately have "path M q (p@[t])" and "p_io (p@[t]) = io@[(x,t_output t)]"
    by (simp add: path_append_transition)+
    
  then have "io@[(x,t_output t)] \<in> LS M q"
    using language_state_containment[of M q "p@[t]" "io@[(x,t_output t)]"] by auto
  then show ?thesis using that by blast
qed
  

lemma path_of_length_ex :
  assumes "completely_specified M"
  and     "q \<in> states M"
  and     "inputs M \<noteq> {}"
shows "\<exists> p . path M q p \<and> length p = k" 
using assms(2) proof (induction k arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc k)

  obtain t where "t_source t = q" and "t \<in> transitions M"
    by (meson Suc.prems assms(1) assms(3) completely_specified.simps equals0I)
  then have "t_target t \<in> states M"
    using fsm_transition_target by blast
  then obtain p where "path M (t_target t) p \<and> length p = k"
    using Suc.IH by blast
  then show ?case 
    using \<open>t_source t = q\<close> \<open>t \<in> transitions M\<close>
    by auto 
qed


subsubsection \<open>Deterministic\<close>

fun deterministic :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "deterministic M = (\<forall> t1 \<in> transitions M . 
                        \<forall> t2 \<in> transitions M . 
                          (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2) 
                          \<longrightarrow> (t_output t1 = t_output t2 \<and> t_target t1 = t_target t2))" 

lemma deterministic_alt_def : 
  "deterministic M = (\<forall> q1 x y' y''  q1' q1'' . (q1,x,y',q1') \<in> transitions M \<and> (q1,x,y'',q1'') \<in> transitions M \<longrightarrow> y' = y'' \<and> q1' = q1'')" 
  by auto

lemma deterministic_alt_def_h : 
  "deterministic M = (\<forall> q1 x yq yq' . (yq \<in> h M (q1,x) \<and> yq' \<in> h M (q1,x)) \<longrightarrow> yq = yq')"
  by auto



subsubsection \<open>Observable\<close>

fun observable :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "observable M = (\<forall> t1 \<in> transitions M . 
                    \<forall> t2 \<in> transitions M . 
                      (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2) 
                        \<longrightarrow> t_target t1 = t_target t2)" 

lemma observable_alt_def : 
  "observable M = (\<forall> q1 x y q1' q1'' . (q1,x,y,q1') \<in> transitions M \<and> (q1,x,y,q1'') \<in> transitions M \<longrightarrow> q1' = q1'')" 
  by auto

lemma observable_alt_def_h : 
  "observable M = (\<forall> q1 x yq yq' . (yq \<in> h M (q1,x) \<and> yq' \<in> h M (q1,x)) \<longrightarrow> fst yq = fst yq' \<longrightarrow> snd yq = snd yq')"
  by auto


lemma language_append_path_ob :
  assumes "io@[(x,y)] \<in> L M"
  obtains p t where "path M (initial M) (p@[t])" and "p_io p = io" and "t_input t = x" and "t_output t = y"
proof -
  obtain p p2 where "path M (initial M) p" and "path M (target (initial M) p) p2"  and "p_io p = io" and "p_io p2 = [(x,y)]"
    using language_state_split[OF assms] by blast

  obtain t where "p2 = [t]" and "t_input t = x" and "t_output t = y"
    using \<open>p_io p2 = [(x,y)]\<close> by auto

  have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close> \<open>path M (target (initial M) p) p2\<close> unfolding \<open>p2 = [t]\<close> by auto
  then show ?thesis using that[OF _ \<open>p_io p = io\<close> \<open>t_input t = x\<close> \<open>t_output t = y\<close>]
    by simp 
qed


subsubsection \<open>Single Input\<close>

(* each state has at most one input, but may have none *)
fun single_input :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "single_input M = (\<forall> t1 \<in> transitions M . 
                      \<forall> t2 \<in> transitions M . 
                        t_source t1 = t_source t2 \<longrightarrow> t_input t1 = t_input t2)" 


lemma single_input_alt_def : 
  "single_input M = (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> transitions M \<and> (q1,x',y',q1'') \<in> transitions M \<longrightarrow> x = x')"
  by fastforce

lemma single_input_alt_def_h : 
  "single_input M = (\<forall> q x x' . (h M (q,x) \<noteq> {} \<and> h M (q,x') \<noteq> {}) \<longrightarrow> x = x')"
  by force
    

subsubsection \<open>Output Complete\<close>

fun output_complete :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "output_complete M = (\<forall> t \<in> transitions M . 
                          \<forall> y \<in> outputs M . 
                            \<exists> t' \<in> transitions M . t_source t = t_source t' \<and> 
                                                    t_input t = t_input t' \<and> 
                                                    t_output t' = y)" 

lemma output_complete_alt_def : 
  "output_complete M = (\<forall> q x . (\<exists> y q' . (q,x,y,q') \<in> transitions M) \<longrightarrow> (\<forall> y \<in> (outputs M) . \<exists> q' . (q,x,y,q') \<in> transitions M))" 
  by force

lemma output_complete_alt_def_h : 
  "output_complete M = (\<forall> q x . h M (q,x) \<noteq> {} \<longrightarrow> (\<forall> y \<in> outputs M . \<exists> q' . (y,q') \<in> h M (q,x)))"
  by force



subsubsection \<open>Acyclic\<close>

fun acyclic :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "acyclic M = (\<forall> p . path M (initial M) p \<longrightarrow> distinct (visited_states (initial M) p))"


lemma visited_states_length : "length (visited_states q p) = Suc (length p)" by auto

lemma visited_states_take : 
  "(take (Suc n) (visited_states q p)) = (visited_states q (take n p))"
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case by (cases "n \<le> length xs"; auto)
qed


(* very inefficient calculation *)
lemma acyclic_code[code] : 
  "acyclic M = (\<not>(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . 
                    \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> 
                                           t_target t \<in> set (visited_states (initial M) p)))"
proof -
  have "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . 
          \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> 
                t_target t \<in> set (visited_states (initial M) p)) 
        \<Longrightarrow> \<not> FSM.acyclic M"
  proof -
    assume "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . 
              \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> 
                                    t_target t \<in> set (visited_states (initial M) p))"
    then obtain p t where "path M (initial M) p"
                    and   "distinct (visited_states (initial M) p)"
                    and   "t \<in> transitions M"
                    and   "t_source t = target (initial M) p" 
                    and   "t_target t \<in> set (visited_states (initial M) p)"
      unfolding acyclic_paths_set by blast
    then have "path M (initial M) (p@[t])"
      by (simp add: path_append_transition) 
    moreover have "\<not> (distinct (visited_states (initial M) (p@[t])))"
      using \<open>t_target t \<in> set (visited_states (initial M) p)\<close> by auto
    ultimately show "\<not> FSM.acyclic M"
      by (meson acyclic.elims(2))
  qed
  moreover have "\<not> FSM.acyclic M \<Longrightarrow> 
                  (\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . 
                    \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> 
                                          t_target t \<in> set (visited_states (initial M) p))"
  proof -
    assume "\<not> FSM.acyclic M"
    then obtain p where "path M (initial M) p"
                  and   "\<not> distinct (visited_states (initial M) p)"
      by auto
    then obtain n where "distinct (take (Suc n) (visited_states (initial M) p))"
                  and   "\<not> distinct (take (Suc (Suc n)) (visited_states (initial M) p))"
      using maximal_distinct_prefix by blast
    then have "distinct (visited_states (initial M) (take n p))"
         and   "\<not> distinct (visited_states (initial M)(take (Suc n) p))"
      unfolding visited_states_take by simp+

    then obtain p' t' where *: "take n p = p'"
                      and   **: "take (Suc n) p = p' @ [t']"
      by (metis Suc_less_eq \<open>\<not> distinct (visited_states (FSM.initial M) p)\<close> 
            le_imp_less_Suc not_less_eq_eq take_all take_hd_drop)
    
    have ***: "visited_states (FSM.initial M) (p' @ [t']) = (visited_states (FSM.initial M) p')@[t_target t']"
      by auto

    have "path M (initial M) p'"
      using * \<open>path M (initial M) p\<close>
      by (metis append_take_drop_id path_prefix)
    then have "p' \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      using \<open>distinct (visited_states (initial M) (take n p))\<close>
      unfolding * acyclic_paths_set by blast
    moreover have "t' \<in> transitions M \<and> t_source t' = target (initial M) p'"
      using * ** \<open>path M (initial M) p\<close>
      by (metis append_take_drop_id path_append_elim path_cons_elim)
       
    moreover have "t_target t' \<in> set (visited_states (initial M) p')"
      using \<open>distinct (visited_states (initial M) (take n p))\<close> 
            \<open>\<not> distinct (visited_states (initial M)(take (Suc n) p))\<close>
      unfolding * ** *** by auto 
    ultimately show "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . 
                      \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> 
                                            t_target t \<in> set (visited_states (initial M) p))"
      by blast
  qed
  ultimately show ?thesis by blast
qed




lemma acyclic_alt_def : "acyclic M = finite (L M)"
proof 
  show "acyclic M \<Longrightarrow> finite (L M)"
  proof -
    assume "acyclic M"
    then have "{ p . path M (initial M) p} \<subseteq> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_set by auto
    moreover have "finite (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_up_to_length.simps using paths_finite[of M "initial M" "size M - 1"]
      by (metis (mono_tags, lifting) Collect_cong \<open>FSM.acyclic M\<close> acyclic.elims(2)) 
    ultimately have "finite { p . path M (initial M) p}"
      using finite_subset by blast
    then show "finite (L M)"
      unfolding LS.simps by auto
  qed

  show "finite (L M) \<Longrightarrow> acyclic M"
  proof (rule ccontr)
    assume "finite (L M)"
    assume "\<not> acyclic M"
    
    obtain max_io_len where "\<forall>io \<in> L M . length io < max_io_len"
      using finite_maxlen[OF \<open>finite (L M)\<close>] by blast
    then have "\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len"
    proof -
      fix p assume "path M (initial M) p"
      show "length p < max_io_len"
      proof (rule ccontr)
        assume "\<not> length p < max_io_len"
        then have "\<not> length (p_io p) < max_io_len" by auto
        moreover have "p_io p \<in> L M"
          unfolding LS.simps using \<open>path M (initial M) p\<close> by blast
        ultimately show "False"
          using \<open>\<forall>io \<in> L M . length io < max_io_len\<close> by blast
      qed
    qed

    obtain p where "path M (initial M) p" and "\<not> distinct (visited_states (initial M) p)"
      using \<open>\<not> acyclic M\<close> unfolding acyclic.simps by blast
    then obtain pL where "path M (initial M) pL" and "max_io_len \<le> length pL"
      using cyclic_path_pumping[of M p max_io_len] by blast
    then show "False"
      using \<open>\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len\<close>
      using not_le by blast 
  qed
qed


lemma acyclic_finite_paths_from_reachable_state :
  assumes "acyclic M"
  and     "path M (initial M) p" 
  and     "target (initial M) p = q"
    shows "finite {p . path M q p}"
proof -
  from assms have "{ p . path M (initial M) p} \<subseteq> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
    unfolding acyclic_paths_set by auto
  moreover have "finite (acyclic_paths_up_to_length M (initial M) (size M - 1))"
    unfolding acyclic_paths_up_to_length.simps using paths_finite[of M "initial M" "size M - 1"]
    by (metis (mono_tags, lifting) Collect_cong \<open>FSM.acyclic M\<close> acyclic.elims(2)) 
  ultimately have "finite { p . path M (initial M) p}"
    using finite_subset by blast

  show "finite {p . path M q p}"
  proof (cases "q \<in> states M")
    case True
        
    have "image (\<lambda>p' . p@p') {p' . path M q p'} \<subseteq> {p' . path M (initial M) p'}"
    proof 
      fix x assume "x \<in> image (\<lambda>p' . p@p') {p' . path M q p'}"
      then obtain p' where "x = p@p'" and "p' \<in> {p' . path M q p'}"
        by blast
      then have "path M q p'" by auto
      then have "path M (initial M) (p@p')"
        using path_append[OF \<open>path M (initial M) p\<close>] \<open>target (initial M) p = q\<close> by auto
      then show "x \<in> {p' . path M (initial M) p'}" using \<open>x = p@p'\<close> by blast
    qed
    
    then have "finite (image (\<lambda>p' . p@p') {p' . path M q p'})"
      using \<open>finite { p . path M (initial M) p}\<close> finite_subset by auto 
    show ?thesis using finite_imageD[OF \<open>finite (image (\<lambda>p' . p@p') {p' . path M q p'})\<close>]
      by (meson inj_onI same_append_eq) 
  next
    case False
    then show ?thesis
      by (meson not_finite_existsD path_begin_state) 
  qed
qed


lemma acyclic_paths_from_reachable_states :
  assumes "acyclic M" 
  and     "path M (initial M) p'" 
  and     "target (initial M) p' = q"
  and     "path M q p"
shows "distinct (visited_states q p)"
proof -
  have "path M (initial M) (p'@p)"
    using assms(2,3,4) path_append by metis
  then have "distinct (visited_states (initial M) (p'@p))"
    using assms(1) unfolding acyclic.simps by blast
  then have "distinct (initial M # (map t_target p') @ map t_target p)"
    by auto
  moreover have "initial M # (map t_target p') @ map t_target p 
                  = (butlast (initial M # map t_target p')) @ ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  ultimately have "distinct ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  then show ?thesis 
    using \<open>target (initial M) p' = q\<close> unfolding visited_states.simps target.simps by simp
qed

definition LS_acyclic :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set" where
  "LS_acyclic M q = {p_io p | p .  path M q p \<and> distinct (visited_states q p)}"

lemma LS_acyclic_code[code] : 
  "LS_acyclic M q = image p_io (acyclic_paths_up_to_length M q (size M - 1))"
  unfolding acyclic_paths_set LS_acyclic_def by blast

lemma LS_from_LS_acyclic : 
  assumes "acyclic M" 
  shows "L M = LS_acyclic M (initial M)"
proof -
  obtain pps :: "(('b \<times> 'c) list \<Rightarrow> bool) \<Rightarrow> (('b \<times> 'c) list \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'c) list" where
    f1: "\<forall>p pa. (\<not> p (pps pa p)) = pa (pps pa p) \<or> Collect p = Collect pa"
    by (metis (no_types) Collect_cong)
  have "\<forall>ps. \<not> path M (FSM.initial M) ps \<or> distinct (visited_states (FSM.initial M) ps)"
    using acyclic.simps assms by blast
  then have "(\<nexists>ps. pps (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa) 
                       (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa 
                                    \<and> distinct (visited_states (FSM.initial M) psa)) 
                  = p_io ps \<and> path M (FSM.initial M) ps \<and> distinct (visited_states (FSM.initial M) ps)) 
            \<noteq> (\<exists>ps. pps (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa) 
                        (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa 
                                    \<and> distinct (visited_states (FSM.initial M) psa)) 
                  = p_io ps \<and> path M (FSM.initial M) ps)"
    by blast
  then have "{p_io ps |ps. path M (FSM.initial M) ps \<and> distinct (visited_states (FSM.initial M) ps)} 
              = {p_io ps |ps. path M (FSM.initial M) ps}"
    using f1 
    by (meson \<open>\<forall>ps. \<not> path M (FSM.initial M) ps \<or> distinct (visited_states (FSM.initial M) ps)\<close>) 
  then show ?thesis
    by (simp add: LS_acyclic_def)
qed



lemma cyclic_cycle :
  assumes "\<not> acyclic M"
  shows "\<exists> q p . path M q p \<and> p \<noteq> [] \<and> target q p = q" 
proof -
  from \<open>\<not> acyclic M\<close> obtain p t where "path M (initial M) (p@[t])" 
                                  and "\<not>distinct (visited_states (initial M) (p@[t]))"
    by (metis (no_types, opaque_lifting) Nil_is_append_conv acyclic.simps append_take_drop_id 
          maximal_distinct_prefix rev_exhaust visited_states_take)
     

  show ?thesis
  proof (cases "initial M \<in> set (map t_target (p@[t]))")
    case True
    then obtain i where "last (take i (map t_target (p@[t]))) = initial M" 
                    and "i \<le> length (map t_target (p@[t]))" and "0 < i"
      using list_contains_last_take by metis

    let ?p = "take i (p@[t])"
    have "path M (initial M) (?p@(drop i (p@[t])))" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis append_take_drop_id)  
    then have "path M (initial M) ?p" by auto
    moreover have "?p \<noteq> []" using \<open>0 < i\<close> by auto
    moreover have "target (initial M) ?p = initial M"
      using \<open>last (take i (map t_target (p@[t]))) = initial M\<close> 
      unfolding target.simps visited_states.simps
      by (metis (no_types, lifting) calculation(2) last_ConsR list.map_disc_iff take_map) 
    ultimately show ?thesis by blast
  next
    case False
    then have "\<not> distinct (map t_target (p@[t]))"
      using \<open>\<not>distinct (visited_states (initial M) (p@[t]))\<close> 
      unfolding visited_states.simps 
      by auto
    then obtain i j where "i < j" and "j < length (map t_target (p@[t]))" 
                      and "(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j"
      using non_distinct_repetition_indices by blast

    let ?pre_i = "take (Suc i) (p@[t])"
    let ?p = "take ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"
    let ?post_j = "drop ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"

    have "p@[t] = ?pre_i @ ?p @ ?post_j"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close>
      by (metis append_take_drop_id) 
    then have "path M (target (initial M) ?pre_i) ?p" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis path_prefix path_suffix) 

    have "?p \<noteq> []"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto

    have "i < length (map t_target (p@[t]))"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto
    have "(target (initial M) ?pre_i) = (map t_target (p@[t])) ! i"
      unfolding target.simps visited_states.simps  
      using take_last_index[OF \<open>i < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>i < length (map t_target (p @ [t]))\<close> 
          last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    
    have "?pre_i@?p = take (Suc j) (p@[t])"
      by (metis (no_types) \<open>i < j\<close> add_Suc add_diff_cancel_left' less_SucI less_imp_Suc_add take_add)
    moreover have "(target (initial M) (take (Suc j) (p@[t]))) = (map t_target (p@[t])) ! j"
      unfolding target.simps visited_states.simps  
      using take_last_index[OF \<open>j < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>j < length (map t_target (p @ [t]))\<close> 
            last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    ultimately have "(target (initial M) (?pre_i@?p)) = (map t_target (p@[t])) ! j"
      by auto
    then have "(target (initial M) (?pre_i@?p)) = (map t_target (p@[t])) ! i"
      using \<open>(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j\<close> by simp
    moreover have "(target (initial M) (?pre_i@?p)) = (target (target (initial M) ?pre_i) ?p)"
      unfolding target.simps visited_states.simps last.simps by auto
    ultimately have "(target (target (initial M) ?pre_i) ?p) = (map t_target (p@[t])) ! i"
      by auto
    then have "(target (target (initial M) ?pre_i) ?p) = (target (initial M) ?pre_i)"
      using \<open>(target (initial M) ?pre_i) = (map t_target (p@[t])) ! i\<close> by auto

    show ?thesis
      using \<open>path M (target (initial M) ?pre_i) ?p\<close> \<open>?p \<noteq> []\<close> 
            \<open>(target (target (initial M) ?pre_i) ?p) = (target (initial M) ?pre_i)\<close>
      by blast
  qed
qed


lemma cyclic_cycle_rev :
  fixes M :: "('a,'b,'c) fsm"
  assumes "path M (initial M) p'"
  and     "target (initial M) p' = q" 
  and     "path M q p"
  and     "p \<noteq> []"
  and     "target q p = q"
shows "\<not> acyclic M"
  using assms unfolding acyclic.simps target.simps visited_states.simps
  using distinct.simps(2) by fastforce

lemma acyclic_initial :
  assumes "acyclic M"
  shows "\<not> (\<exists> t \<in> transitions M . t_target t = initial M \<and> 
                                  (\<exists> p . path M (initial M) p \<and> target (initial M) p = t_source t))"
  by (metis append_Cons assms cyclic_cycle_rev list.distinct(1) path.simps 
        path_append path_append_transition_elim(3) single_transition_path) 

lemma cyclic_path_shift : 
  assumes "path M q p"
  and     "target q p = q"
shows "path M (target q (take i p)) ((drop i p) @ (take i p))"
  and "target (target q (take i p)) ((drop i p) @ (take i p)) = (target q (take i p))"
proof -
  show "path M (target q (take i p)) ((drop i p) @ (take i p))"
    by (metis append_take_drop_id assms(1) assms(2) path_append path_append_elim path_append_target)
  show "target (target q (take i p)) ((drop i p) @ (take i p)) = (target q (take i p))"
    by (metis append_take_drop_id assms(2) path_append_target)
qed


lemma cyclic_path_transition_states_property :
  assumes "\<exists> t \<in> set p . P (t_source t)"
  and     "\<forall> t \<in> set p . P (t_source t) \<longrightarrow> P (t_target t)"
  and     "path M q p"
  and     "target q p = q"
shows "\<forall> t \<in> set p . P (t_source t)"
  and "\<forall> t \<in> set p . P (t_target t)"
proof -
  obtain t0 where "t0 \<in> set p" and "P (t_source t0)"
    using assms(1) by blast
  then obtain i where "i < length p" and "p ! i = t0"
    by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target q (take i p)) ?p"
    using cyclic_path_shift(1)[OF assms(3,4), of i] by assumption
  
  have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed
  then have "\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)"
    using assms(2) by blast
  
  have "\<And> j . j < length ?p \<Longrightarrow> P (t_source (?p ! j))"
  proof -
    fix j assume "j < length ?p"
    then show "P (t_source (?p ! j))"
    proof (induction j)
      case 0
      then show ?case 
        using \<open>p ! i = t0\<close> \<open>P (t_source t0)\<close>
        by (metis \<open>i < length p\<close> drop_eq_Nil hd_append2 hd_conv_nth hd_drop_conv_nth leD 
              length_greater_0_conv)  
    next
      case (Suc j)
      then have "P (t_source (?p ! j))"
        by auto
      then have "P (t_target (?p ! j))"
        using Suc.prems \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        using Suc_lessD nth_mem by blast 
      moreover have "t_target (?p ! j) = t_source (?p ! (Suc j))"
        using path_source_target_index[OF Suc.prems \<open>path M (target q (take i p)) ?p\<close>] 
        by assumption
      ultimately show ?case 
        using \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        by simp
    qed
  qed
  then have "\<forall> t \<in> set ?p . P (t_source t)"
    by (metis in_set_conv_nth)
  then show "\<forall> t \<in> set p . P (t_source t)"
    using \<open>set ?p = set p\<close> by blast
  then show "\<forall> t \<in> set p . P (t_target t)"
    using assms(2) by blast
qed


lemma cycle_incoming_transition_ex :
  assumes "path M q p"
  and     "p \<noteq> []"
  and     "target q p = q"
  and     "t \<in> set p"
shows "\<exists> tI \<in> set p . t_target tI = t_source t"
proof -
  obtain i where "i < length p" and "p ! i = t"
    using assms(4) by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target q (take i p)) ?p"
  and  "target (target q (take i p)) ?p = target q (take i p)"
    using cyclic_path_shift[OF assms(1,3), of i] by linarith+

  have "p = (take i p @ drop i p)" by auto
  then have "path M (target q (take i p)) (drop i p)" 
    using path_suffix assms(1) by metis
  moreover have "t = hd (drop i p)"
    using \<open>i < length p\<close> \<open>p ! i = t\<close>
    by (simp add: hd_drop_conv_nth) 
  ultimately have "path M (target q (take i p)) [t]"
    by (metis \<open>i < length p\<close> append_take_drop_id assms(1) path_append_elim take_hd_drop)
  then have "t_source t = (target q (take i p))"
    by auto  
  moreover have "t_target (last ?p) = (target q (take i p))" 
    using \<open>path M (target q (take i p)) ?p\<close> \<open>target (target q (take i p)) ?p = target q (take i p)\<close> 
          assms(2)
    unfolding target.simps visited_states.simps last.simps
    by (metis (no_types, lifting) \<open>p = take i p @ drop i p\<close> append_is_Nil_conv last_map 
          list.map_disc_iff)
    
  
  moreover have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed

  ultimately show ?thesis
    by (metis \<open>i < length p\<close> append_is_Nil_conv drop_eq_Nil last_in_set leD) 
qed


lemma acyclic_paths_finite :
  "finite {p . path M q p \<and> distinct (visited_states q p) }"
proof -
  have "\<And> p . path M q p \<Longrightarrow> distinct (visited_states q p) \<Longrightarrow> distinct p"
  proof -
    fix p assume "path M q p" and "distinct (visited_states q p)"
    then have "distinct (map t_target p)" by auto
    then show "distinct p" by (simp add: distinct_map) 
  qed
  
  then show ?thesis
    using distinct_lists_finite[OF fsm_transitions_finite, of M]  path_transitions[of M q]
    by (metis (no_types, lifting) infinite_super mem_Collect_eq path_transitions subsetI)
qed


lemma acyclic_no_self_loop :
  assumes "acyclic M"
  and     "q \<in> reachable_states M"
shows "\<not> (\<exists> x y . (q,x,y,q) \<in> transitions M)" 
proof 
  assume "\<exists>x y. (q, x, y, q) \<in> FSM.transitions M"
  then obtain x y where "(q, x, y, q) \<in> FSM.transitions M" by blast
  moreover obtain p where "path M (initial M) p" and "target (initial M) p = q"
    using assms(2) unfolding reachable_states_def by blast
  ultimately have "path M (initial M) (p@[(q,x,y,q)])" 
    by (simp add: path_append_transition) 
  moreover have "\<not> (distinct (visited_states (initial M) (p@[(q,x,y,q)])))"
    using \<open>target (initial M) p = q\<close> unfolding visited_states.simps target.simps by (cases p rule: rev_cases; auto)
  ultimately show "False"
    using assms(1) unfolding acyclic.simps
    by meson 
qed


subsubsection \<open>Deadlock States\<close>

fun deadlock_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where 
  "deadlock_state M q = (\<not>(\<exists> t \<in> transitions M . t_source t = q))"

lemma deadlock_state_alt_def : "deadlock_state M q = (LS M q \<subseteq> {[]})" 
proof 
  show "deadlock_state M q \<Longrightarrow> LS M q \<subseteq> {[]}" 
  proof -
    assume "deadlock_state M q"
    moreover have "\<And> p . deadlock_state M q \<Longrightarrow> path M q p \<Longrightarrow> p = []"
      unfolding deadlock_state.simps by (metis path.cases) 
    ultimately show "LS M q \<subseteq> {[]}"
      unfolding LS.simps by blast
  qed
  show "LS M q \<subseteq> {[]} \<Longrightarrow> deadlock_state M q"
    unfolding LS.simps deadlock_state.simps using path.cases[of M q] by blast
qed

lemma deadlock_state_alt_def_h : "deadlock_state M q = (\<forall> x \<in> inputs M . h M (q,x) = {})" 
  unfolding deadlock_state.simps h.simps 
  using fsm_transition_input by force


lemma acyclic_deadlock_reachable :
  assumes "acyclic M"
  shows "\<exists> q \<in> reachable_states M . deadlock_state M q"
proof (rule ccontr)
  assume "\<not> (\<exists>q\<in>reachable_states M. deadlock_state M q)"
  then have *: "\<And> q . q \<in> reachable_states M \<Longrightarrow> (\<exists> t \<in> transitions M . t_source t = q)"
    unfolding deadlock_state.simps by blast

  let ?p = "arg_max_on length {p. path M (initial M) p}"
  

  have "finite {p. path M (initial M) p}" 
    by (metis Collect_cong acyclic_finite_paths_from_reachable_state assms eq_Nil_appendI fsm_initial 
          nil path_append path_append_elim) 
    
  moreover have "{p. path M (initial M) p} \<noteq> {}" 
    by auto
  ultimately obtain p where "path M (initial M) p" 
                        and "\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p" 
    using max_length_elem
    by (metis mem_Collect_eq not_le_imp_less)

  then obtain t where "t \<in> transitions M" and "t_source t = target (initial M) p"
    using *[of "target (initial M) p"] unfolding reachable_states_def
    by blast

  then have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close>
    by (simp add: path_append_transition)

  then show "False"
    using \<open>\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p\<close>
    by (metis impossible_Cons length_rotate1 rotate1.simps(2)) 
qed

lemma deadlock_prefix :
  assumes "path M q p"
  and     "t \<in> set (butlast p)"
shows "\<not> (deadlock_state M (t_target t))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t' p')
  
  show ?case proof (cases "t \<in> set (butlast p')")
    case True
    show ?thesis 
      using snoc.IH[OF _ True] snoc.prems(1)
      by blast 
  next
    case False
    then have "p' = (butlast p')@[t]"
      using snoc.prems(2) by (metis append_butlast_last_id append_self_conv2 butlast_snoc 
                                in_set_butlast_appendI list_prefix_elem set_ConsD)
    then have "path M q ((butlast p'@[t])@[t'])"
      using snoc.prems(1)
      by auto 
    
    have "t' \<in> transitions M" and "t_source t' = target q (butlast p'@[t])"
      using path_suffix[OF \<open>path M q ((butlast p'@[t])@[t'])\<close>]
      by auto
    then have "t' \<in> transitions M \<and> t_source t' = t_target t"
      unfolding target.simps visited_states.simps by auto
    then show ?thesis 
      unfolding deadlock_state.simps using \<open>t' \<in> transitions M\<close> by blast
  qed
qed


lemma states_initial_deadlock :
  assumes "deadlock_state M (initial M)"
  shows "reachable_states M = {initial M}"
  
proof -
  have "\<And> q . q \<in> reachable_states M \<Longrightarrow> q = initial M"
  proof -
    fix q assume "q \<in> reachable_states M"
    then obtain p where "path M (initial M) p" and "target (initial M) p = q"
      unfolding reachable_states_def by auto
    
    show "q = initial M" proof (cases p)
      case Nil
      then show ?thesis using \<open>target (initial M) p = q\<close> by auto
    next
      case (Cons t p')
      then have "False" using assms \<open>path M (initial M) p\<close> unfolding deadlock_state.simps
        by auto 
      then show ?thesis by simp
    qed
  qed
  then show ?thesis
    using reachable_states_initial[of M] by blast
qed

subsubsection \<open>Other\<close>

fun completed_path :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> bool" where
  "completed_path M q p = deadlock_state M (target q p)"

fun minimal :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> states M . \<forall> q' \<in> states M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"

lemma minimal_alt_def : "minimal M = (\<forall> q q' . q \<in> states M \<longrightarrow> q' \<in> states M \<longrightarrow> LS M q = LS M q' \<longrightarrow> q = q')" 
  by auto  

definition retains_outputs_for_states_and_inputs :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "retains_outputs_for_states_and_inputs M S 
    = (\<forall> tS \<in> transitions S . 
        \<forall> tM \<in> transitions M . 
          (t_source tS = t_source tM \<and> t_input tS = t_input tM) \<longrightarrow> tM \<in> transitions S)"





subsection \<open>IO Targets and Observability\<close>

fun paths_for_io' :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_io' f [] q prev = {prev}" |
  "paths_for_io' f ((x,y)#io) q prev = \<Union>(image (\<lambda>yq' . paths_for_io' f io (snd yq') (prev@[(q,x,y,(snd yq'))])) (Set.filter (\<lambda>yq' . fst yq' = y) (f (q,x))))"

lemma paths_for_io'_set :
  assumes "q \<in> states M"
  shows   "paths_for_io' (h M) io q prev = {prev@p | p . path M q p \<and> p_io p = io}"
using assms proof (induction io arbitrary: q prev)
  case Nil
  then show ?case by auto
next
  case (Cons xy io)
  obtain x y where "xy = (x,y)"
    by (meson surj_pair) 

  let ?UN = "\<Union>(image (\<lambda>yq' . paths_for_io' (h M) io (snd yq') (prev@[(q,x,y,(snd yq'))])) 
                      (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x))))"

  have "?UN = {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
  proof 
    have "\<And> p . p \<in> ?UN \<Longrightarrow> p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
    proof -
      fix p assume "p \<in> ?UN"
      then obtain q' where "(y,q') \<in> (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x)))"
                     and   "p \<in> paths_for_io' (h M) io q' (prev@[(q,x,y,q')])"
        by auto
      
      from \<open>(y,q') \<in> (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x)))\<close> have "q' \<in> states M" 
                                                                     and "(q,x,y,q') \<in> transitions M"
        using fsm_transition_target unfolding h.simps by auto

      have "p \<in> {(prev @ [(q, x, y, q')]) @ p |p. path M q' p \<and> p_io p = io}"
        using \<open>p \<in> paths_for_io' (h M) io q' (prev@[(q,x,y,q')])\<close>
        unfolding Cons.IH[OF \<open>q' \<in> states M\<close>] by assumption
      moreover have "{(prev @ [(q, x, y, q')]) @ p |p. path M q' p \<and> p_io p = io} 
                      \<subseteq> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
        using \<open>(q,x,y,q') \<in> transitions M\<close>
        using cons by force 
      ultimately show "p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}" 
        by blast
    qed
    then show "?UN \<subseteq> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
      by blast

    have "\<And> p . p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io} \<Longrightarrow> p \<in> ?UN"
    proof -
      fix pp assume "pp \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
      then obtain p where "pp = prev@p" and "path M q p" and "p_io p = (x,y)#io"
        by fastforce
      then obtain t p' where "p = t#p'" and "path M q (t#p')" and "p_io (t#p') = (x,y)#io" 
                         and "p_io p' = io"
        by (metis (no_types, lifting) map_eq_Cons_D)
      then have "path M (t_target t) p'" and "t_source t = q" and "t_input t = x" 
                                         and "t_output t = y" and "t_target t \<in> states M"
                                         and "t \<in> transitions M"
        by auto

      have "(y,t_target t) \<in> Set.filter (\<lambda>yq'. fst yq' = y) (h M (q, x))"
        using \<open>t \<in> transitions M\<close> \<open>t_output t = y\<close> \<open>t_input t = x\<close> \<open>t_source t = q\<close>
        unfolding h.simps
        by auto 
      moreover have "(prev@p) \<in> paths_for_io' (h M) io (snd (y,t_target t)) (prev @ [(q, x, y, snd (y,t_target t))])"
        using Cons.IH[OF \<open>t_target t \<in> states M\<close>, of "prev@[(q, x, y, t_target t)]"]
        using \<open>p = t # p'\<close> \<open>p_io p' = io\<close> \<open>path M (t_target t) p'\<close> \<open>t_input t = x\<close> 
              \<open>t_output t = y\<close> \<open>t_source t = q\<close> 
        by auto

      ultimately show "pp \<in> ?UN" unfolding \<open>pp = prev@p\<close>
        by blast 
    qed
    then show "{prev@p | p . path M q p \<and> p_io p = (x,y)#io} \<subseteq> ?UN"
      by (meson subsetI) 
  qed

  then show ?case
    by (simp add: \<open>xy = (x, y)\<close>) 
qed



definition paths_for_io :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_io M q io = {p . path M q p \<and> p_io p = io}"

lemma paths_for_io_set_code[code] :
  "paths_for_io M q io = (if q \<in> states M then paths_for_io' (h M) io q [] else {})"
  using paths_for_io'_set[of q M io "[]"]
  unfolding paths_for_io_def
proof -
  have "{[] @ ps |ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.states M then paths_for_io' (h M) io q [] else {}) 
        \<longrightarrow> {ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.states M then paths_for_io' (h M) io q [] else {})"
    by auto
  moreover
    { assume "{[] @ ps |ps. path M q ps \<and> p_io ps = io} \<noteq> (if q \<in> FSM.states M then paths_for_io' (h M) io q [] else {})"
      then have "q \<notin> FSM.states M"
        using \<open>q \<in> FSM.states M \<Longrightarrow> paths_for_io' (h M) io q [] = {[] @ p |p. path M q p \<and> p_io p = io}\<close> by force
      then have "{ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.states M then paths_for_io' (h M) io q [] else {})"
      using path_begin_state by force }
  ultimately show "{ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.states M then paths_for_io' (h M) io q [] else {})"
    by linarith
qed 


fun io_targets :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets M io q = {target q p | p . path M q p \<and> p_io p = io}"

lemma io_targets_code[code] : "io_targets M io q = image (target q) (paths_for_io M q io)"
  unfolding io_targets.simps paths_for_io_def by blast

lemma io_targets_states :
  "io_targets M io q \<subseteq> states M"
  using path_target_is_state by fastforce



lemma observable_transition_unique :
  assumes "observable M"
      and "t \<in> transitions M"
    shows "\<exists>! t' \<in> transitions M . t_source t' = t_source t \<and> 
                                    t_input t' = t_input t \<and> 
                                    t_output t' = t_output t"
  by (metis assms observable.elims(2) prod.expand)

lemma observable_path_unique :
  assumes "observable M"
  and     "path M q p"
  and     "path M q p'"
  and     "p_io p = p_io p'"
shows "p = p'"
proof -
  have "length p = length p'"
    using assms(4) map_eq_imp_length_eq by blast 
  then show ?thesis
    using \<open>p_io p = p_io p'\<close> \<open>path M q p\<close> \<open>path M q p'\<close>
  proof (induction p p' arbitrary: q rule: list_induct2)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs y ys)
    then have *: "x \<in> transitions M \<and> y \<in> transitions M \<and> t_source x = t_source y 
                                    \<and> t_input x = t_input y \<and> t_output x = t_output y" 
      by auto
    then have "t_target x = t_target y" 
      using assms(1) observable.elims(2) by blast 
    then have "x = y"
      by (simp add: "*" prod.expand) 
      

    have "p_io xs = p_io ys" 
      using Cons by auto

    moreover have "path M (t_target x) xs" 
      using Cons by auto
    moreover have "path M (t_target x) ys"
      using Cons \<open>t_target x = t_target y\<close> by auto
    ultimately have "xs = ys" 
      using Cons by auto

    then show ?case 
      using \<open>x = y\<close> by simp
  qed
qed


lemma observable_io_targets : 
  assumes "observable M"
  and "io \<in> LS M q"
obtains q'
where "io_targets M io q = {q'}"
proof -

  obtain p where "path M q p" and "p_io p = io" 
    using assms(2) by auto 
  then have "target q p \<in> io_targets M io q"
    by auto   

  have "\<exists> q' . io_targets M io q = {q'}"
  proof (rule ccontr)
    assume "\<not>(\<exists>q'. io_targets M io q = {q'})"
    then have "\<exists> q' . q' \<noteq> target q p \<and> q' \<in> io_targets M io q"
    proof -
      have "\<not> io_targets M io q \<subseteq> {target q p}"
        using \<open>\<not>(\<exists>q'. io_targets M io q = {q'})\<close> \<open>target q p \<in> io_targets M io q\<close> by blast
      then show ?thesis
        by blast
    qed       
    then obtain q' where "q' \<noteq> target q p" and "q' \<in> io_targets M io q" 
      by blast
    then obtain p' where "path M q p'" and "target q p' = q'" and "p_io p' = io"
      by auto 
    then have "p_io p = p_io p'" 
      using \<open>p_io p = io\<close> by simp
    then have "p = p'"
      using observable_path_unique[OF assms(1) \<open>path M q p\<close> \<open>path M q p'\<close>] by simp
    then show "False"
      using \<open>q' \<noteq> target q p\<close> \<open>target q p' = q'\<close> by auto
  qed

  then show ?thesis using that by blast
qed


lemma observable_path_io_target : 
  assumes "observable M"
  and     "path M q p"
shows "io_targets M (p_io p) q = {target q p}"
  using observable_io_targets[OF assms(1) language_state_containment[OF assms(2)], of "p_io p"] 
        singletonD[of "target q p"]
  unfolding io_targets.simps
proof -
  assume a1: "\<And>a. target q p \<in> {a} \<Longrightarrow> target q p = a"
  assume "\<And>thesis. \<lbrakk>p_io p = p_io p; \<And>q'. {target q pa |pa. path M q pa \<and> p_io pa = p_io p} = {q'} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
  then obtain aa :: 'a where "\<And>b. {target q ps |ps. path M q ps \<and> p_io ps = p_io p} = {aa} \<or> b"
    by meson
  then show "{target q ps |ps. path M q ps \<and> p_io ps = p_io p} = {target q p}"
    using a1 assms(2) by blast
qed


lemma completely_specified_io_targets : 
  assumes "completely_specified M"
  shows "\<forall> q \<in> io_targets M io (initial M) . \<forall> x \<in> (inputs M) . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x"
  by (meson assms completely_specified.elims(2) io_targets_states subsetD)
  


lemma observable_path_language_step :
  assumes "observable M"
      and "path M q p"
      and "\<not> (\<exists>t\<in>transitions M.
               t_source t = target q p \<and>
               t_input t = x \<and> t_output t = y)"
    shows "(p_io p)@[(x,y)] \<notin> LS M q"
using assms proof (induction p rule: rev_induct)
  case Nil
  show ?case proof
    assume "p_io [] @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = [(x,y)]" unfolding LS.simps
      by force 
    then obtain t where "p' = [t]" by blast
    
    have "t\<in>transitions M" and "t_source t = target q []"
      using \<open>path M q p'\<close> \<open>p' = [t]\<close> by auto
    moreover have "t_input t = x \<and> t_output t = y"
      using \<open>p_io p' = [(x,y)]\<close> \<open>p' = [t]\<close> by auto
    ultimately show "False"
      using Nil.prems(3) by blast
  qed
next
  case (snoc t p)
  
  from \<open>path M q (p @ [t])\<close> have "path M q p" and "t_source t = target q p" 
                                              and "t \<in> transitions M" 
    by auto

  show ?case proof
    assume "p_io (p @ [t]) @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = p_io (p @ [t]) @ [(x, y)]"
      by auto
    then obtain p'' t' t'' where "p' = p''@[t']@[t'']"
      by (metis (no_types, lifting) append.assoc map_butlast map_is_Nil_conv snoc_eq_iff_butlast)
    then have "path M q p''" 
      using \<open>path M q p'\<close> by blast
    
    
    have "p_io p'' = p_io p"
      using \<open>p' = p''@[t']@[t'']\<close> \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> by auto
    then have "p'' = p"
      using observable_path_unique[OF assms(1) \<open>path M q p''\<close> \<open>path M q p\<close>] by blast

    have "t_source t' = target q p''" and "t' \<in> transitions M"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    then have "t_source t' = t_source t"
      using \<open>p'' = p\<close> \<open>t_source t = target q p\<close> by auto 
    moreover have "t_input t' = t_input t \<and> t_output t' = t_output t"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> transitions M\<close> \<open>t' \<in> transitions M\<close> assms(1) unfolding observable.simps 
      by (meson prod.expand) 

    have "t'' \<in> transitions M" and "t_source t'' = target q (p@[t])"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> \<open>t' = t\<close> by auto
    moreover have "t_input t'' = x \<and> t_output t'' = y"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    ultimately show "False"
      using snoc.prems(3) by blast
  qed
qed

lemma observable_io_targets_language :
  assumes "io1 @ io2 \<in> LS M q1"
  and     "observable M"
  and     "q2 \<in> io_targets M io1 q1"
shows "io2 \<in> LS M q2" 
proof -
  obtain p1 p2 where "path M q1 p1" and "path M (target q1 p1) p2"  
                 and "p_io p1 = io1" and "p_io p2 = io2"
    using language_state_split[OF assms(1)] by blast
  then have "io1 \<in> LS M q1" and "io2 \<in> LS M (target q1 p1)"
    by auto
  
  have "target q1 p1 \<in> io_targets M io1 q1"
    using \<open>path M q1 p1\<close> \<open>p_io p1 = io1\<close>
    unfolding io_targets.simps by blast
  then have "target q1 p1 = q2"
    using observable_io_targets[OF assms(2) \<open>io1 \<in> LS M q1\<close>]
    by (metis assms(3) singletonD) 
  then show ?thesis
    using \<open>io2 \<in> LS M (target q1 p1)\<close> by auto
qed


lemma io_targets_language_append :
  assumes "q1 \<in> io_targets M io1 q"
  and     "io2 \<in> LS M q1"
shows "io1@io2 \<in> LS M q" 
proof -
  obtain p1 where "path M q p1" and "p_io p1 = io1" and "target q p1 = q1" 
    using assms(1) by auto
  moreover obtain p2 where "path M q1 p2" and "p_io p2 = io2" 
    using assms(2) by auto
  ultimately have "path M q (p1@p2)" and "p_io (p1@p2) = io1@io2"
    by auto
  then show ?thesis 
    using language_state_containment[of M q "p1@p2" "io1@io2"] by simp
qed


lemma io_targets_next :
  assumes "t \<in> transitions M"
  shows "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
unfolding io_targets.simps
proof 
  fix q assume "q \<in> {target (t_target t) p |p. path M (t_target t) p \<and> p_io p = io}"
  then obtain p where "path M (t_target t) p \<and> p_io p = io \<and> target (t_target t) p = q"
    by auto
  then have "path M (t_source t) (t#p) \<and> p_io (t#p) = p_io [t] @ io \<and> target (t_source t) (t#p) = q"
    using FSM.path.cons[OF assms] by auto
  then show "q \<in> {target (t_source t) p |p. path M (t_source t) p \<and> p_io p = p_io [t] @ io}"
    by blast
qed


lemma observable_io_targets_next :
  assumes "observable M"
  and     "t \<in> transitions M"
shows "io_targets M (p_io [t] @ io) (t_source t) = io_targets M io (t_target t)" 
proof 
  show "io_targets M (p_io [t] @ io) (t_source t) \<subseteq> io_targets M io (t_target t)"
  proof 
    fix q assume "q \<in> io_targets M (p_io [t] @ io) (t_source t)"
    then obtain p where "q = target (t_source t) p" 
                    and "path M (t_source t) p"
                    and "p_io p = p_io [t] @ io"
      unfolding io_targets.simps by blast
    then have "q = t_target (last p)" unfolding target.simps visited_states.simps
      using last_map by auto 

    obtain t' p' where "p = t' # p'"
      using \<open>p_io p = p_io [t] @ io\<close> by auto
    then have "t' \<in> transitions M" and "t_source t' = t_source t"
      using \<open>path M (t_source t) p\<close> by auto
    moreover have "t_input t' = t_input t" and "t_output t' = t_output t"
      using \<open>p = t' # p'\<close> \<open>p_io p = p_io [t] @ io\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> transitions M\<close> \<open>observable M\<close> unfolding observable.simps
      by (meson prod.expand) 

    then have "path M (t_target t) p'"
      using \<open>path M (t_source t) p\<close> \<open>p = t' # p'\<close> by auto
    moreover have "p_io p' = io"
      using \<open>p_io p = p_io [t] @ io\<close> \<open>p = t' # p'\<close> by auto
    moreover have "q = target (t_target t) p'"
      using \<open>q = target (t_source t) p\<close> \<open>p = t' # p'\<close> \<open>t' = t\<close> by auto
    ultimately show "q \<in> io_targets M io (t_target t)"
      by auto
  qed

  show "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
    using io_targets_next[OF assms(2)] by assumption
qed



lemma observable_language_target :
  assumes "observable M"
  and     "q \<in> io_targets M io1 (initial M)"
  and     "t \<in> io_targets T io1 (initial T)"
  and     "L T \<subseteq> L M"
shows "LS T t \<subseteq> LS M q"
proof 
  fix io2 assume "io2 \<in> LS T t"
  then obtain pT2 where "path T t pT2" and "p_io pT2 = io2"
    by auto  
  
  obtain pT1 where "path T (initial T) pT1" and "p_io pT1 = io1" and "target (initial T) pT1 = t"
    using \<open>t \<in> io_targets T io1 (initial T)\<close> by auto
  then have "path T (initial T) (pT1@pT2)" 
    using \<open>path T t pT2\<close> using path_append by metis
  moreover have "p_io (pT1@pT2) = io1@io2"
    using \<open>p_io pT1 = io1\<close> \<open>p_io pT2 = io2\<close> by auto
  ultimately have "io1@io2 \<in> L T"
    using language_state_containment[of T] by auto
  then have "io1@io2 \<in> L M"
    using \<open>L T \<subseteq> L M\<close> by blast
  then obtain pM where "path M (initial M) pM" and "p_io pM = io1@io2"
    by auto

  let ?pM1 = "take (length io1) pM"
  let ?pM2 = "drop (length io1) pM"

  have "path M (initial M) (?pM1@?pM2)"
    using \<open>path M (initial M) pM\<close> by auto
  then have "path M (initial M) ?pM1" and "path M (target (initial M) ?pM1) ?pM2"
    by blast+
  
  have "p_io ?pM1 = io1"
    using \<open>p_io pM = io1@io2\<close> 
    by (metis append_eq_conv_conj take_map)
  have "p_io ?pM2 = io2"
    using \<open>p_io pM = io1@io2\<close> 
    by (metis append_eq_conv_conj drop_map)

  obtain pM1 where "path M (initial M) pM1" and "p_io pM1 = io1" and "target (initial M) pM1 = q"
    using \<open>q \<in> io_targets M io1 (initial M)\<close> by auto

  have "pM1 = ?pM1"
    using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) pM1\<close> \<open>path M (initial M) ?pM1\<close>]
    unfolding \<open>p_io pM1 = io1\<close> \<open>p_io ?pM1 = io1\<close> by simp

  then have "path M q ?pM2"
    using \<open>path M (target (initial M) ?pM1) ?pM2\<close> \<open>target (initial M) pM1 = q\<close> by auto
  then show "io2 \<in> LS M q"
    using language_state_containment[OF _ \<open>p_io ?pM2 = io2\<close>, of M] by auto
qed


lemma observable_language_target_failure :
  assumes "observable M"
  and     "q \<in> io_targets M io1 (initial M)"
  and     "t \<in> io_targets T io1 (initial T)"
  and     "\<not> LS T t \<subseteq> LS M q"
shows "\<not> L T \<subseteq> L M"
  using observable_language_target[OF assms(1,2,3)] assms(4) by blast
    

lemma language_path_append_transition_observable :
  assumes "(p_io p) @ [(x,y)] \<in> LS M q"
  and     "path M q p"
  and     "observable M"
  obtains t where "path M q (p@[t])" and "t_input t = x" and "t_output t = y"
proof -
  obtain p' t where "path M q (p'@[t])" and "p_io (p'@[t]) = (p_io p) @ [(x,y)]"
    using language_path_append_transition[OF assms(1)] by blast
  then have "path M q p'" and "p_io p' = p_io p" and "t_input t = x" and "t_output t = y"
    by auto

  have "p' = p"
    using observable_path_unique[OF assms(3) \<open>path M q p'\<close> \<open>path M q p\<close> \<open>p_io p' = p_io p\<close>] by assumption
  then have "path M q (p@[t])"
    using \<open>path M q (p'@[t])\<close> by auto
  then show ?thesis using that \<open>t_input t = x\<close> \<open>t_output t = y\<close> by metis
qed


lemma language_io_target_append :
  assumes "q' \<in> io_targets M io1 q"
  and     "io2 \<in> LS M q'"
shows "(io1@io2) \<in> LS M q"
proof - 
  obtain p2 where "path M q' p2" and "p_io p2 = io2"
    using assms(2) by auto

  moreover obtain p1 where "q' = target q p1" and "path M q p1" and "p_io p1 = io1"
    using assms(1) by auto

  ultimately show ?thesis unfolding LS.simps
    by (metis (mono_tags, lifting) map_append mem_Collect_eq path_append) 
qed


lemma observable_path_suffix :
  assumes "(p_io p)@io \<in> LS M q"
  and     "path M q p"
  and     "observable M"
obtains p' where "path M (target q p) p'" and "p_io p' = io"
proof -
  obtain p1 p2 where "path M q p1" and "path M (target q p1) p2"  and "p_io p1 = p_io p" and "p_io p2 = io"
    using language_state_split[OF assms(1)] by blast

  have "p1 = p"
    using observable_path_unique[OF assms(3,2) \<open>path M q p1\<close> \<open>p_io p1 = p_io p\<close>[symmetric]]
    by simp

  show ?thesis using that[of p2] \<open>path M (target q p1) p2\<close> \<open>p_io p2 = io\<close> unfolding \<open>p1 = p\<close>
    by blast
qed


lemma io_targets_finite :
  "finite (io_targets M io q)"
proof -
  have "(io_targets M io q) \<subseteq> {target q p | p . path M q p \<and> length p \<le> length io}"
    unfolding io_targets.simps length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by force
  moreover have "finite {target q p | p . path M q p \<and> length p \<le> length io}"
    using paths_finite[of M q "length io"]
    by simp 
  ultimately show ?thesis
    using rev_finite_subset by blast 
qed

lemma language_next_transition_ob :
  assumes "(x,y)#ios \<in> LS M q"
obtains t where "t_source t = q"
            and "t \<in> transitions M"
            and "t_input t = x"
            and "t_output t = y"
            and "ios \<in> LS M (t_target t)"
proof -
  obtain p where "path M q p" and "p_io p = (x,y)#ios"
    using assms unfolding LS.simps mem_Collect_eq
    by (metis (no_types, lifting)) 
  then obtain t p' where "p = t#p'"
    by blast

  have "t_source t = q"
   and "t \<in> transitions M"
   and "path M (t_target t) p'"
    using \<open>path M q p\<close> unfolding \<open>p = t#p'\<close> by auto
  moreover have "t_input t = x"
            and "t_output t = y"
            and "p_io p' = ios"
    using \<open>p_io p = (x,y)#ios\<close> unfolding \<open>p = t#p'\<close> by auto
  ultimately show ?thesis using that[of t] by auto
qed

lemma h_observable_card :
  assumes "observable M"
  shows "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) \<le> 1"
  and "finite (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)))"
proof -
  have "snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) = {q' . (q,x,y,q') \<in> transitions M}"
    unfolding h.simps by force
  moreover have "{q' . (q,x,y,q') \<in> transitions M} = {} \<or> (\<exists> q' . {q' . (q,x,y,q') \<in> transitions M} = {q'})"
    using assms unfolding observable_alt_def by blast
  ultimately show "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) \<le> 1"
              and "finite (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)))"
    by auto
qed

lemma h_obs_None : 
  assumes "observable M"
shows "(h_obs M q x y = None) = (\<nexists>q' . (q,x,y,q') \<in> transitions M)"
proof 
  show "(h_obs M q x y = None) \<Longrightarrow> (\<nexists>q' . (q,x,y,q') \<in> transitions M)"
  proof -
    assume "h_obs M q x y = None"
    then have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) \<noteq> 1"
      by auto
    then have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = 0"
      using h_observable_card(1)[OF assms, of y q x] by presburger
    then have "(snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = {}"
      using h_observable_card(2)[OF assms, of y q x] card_0_eq[of "(snd ` Set.filter (\<lambda>(y', q'). y' = y) (h M (q, x)))"] by blast
    then show ?thesis 
      unfolding h.simps by force
  qed
  show "(\<nexists>q' . (q,x,y,q') \<in> transitions M) \<Longrightarrow> (h_obs M q x y = None)"
  proof -
    assume "(\<nexists>q' . (q,x,y,q') \<in> transitions M)"
    then have "snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) = {}"
      unfolding h.simps by force
    then have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = 0"
      by simp
    then show ?thesis
      unfolding h_obs_simps Let_def \<open>snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) = {}\<close>
      by auto
  qed
qed

lemma h_obs_Some : 
  assumes "observable M"
  shows "(h_obs M q x y = Some q') = ({q' . (q,x,y,q') \<in> transitions M} = {q'})"
proof 
  have *: "snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) = {q' . (q,x,y,q') \<in> transitions M}"
    unfolding h.simps by force

  show "h_obs M q x y = Some q' \<Longrightarrow> ({q' . (q,x,y,q') \<in> transitions M} = {q'})"
  proof -
    assume "h_obs M q x y = Some q'"
    then have "(snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) \<noteq> {}"
      by force 
    then have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) > 0"
      unfolding h_simps using fsm_transitions_finite[of M]
      by (metis assms card_0_eq h_observable_card(2) h_simps neq0_conv) 
    moreover have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) \<le> 1"
      using assms unfolding observable_alt_def h_simps
      by (metis assms h_observable_card(1) h_simps)
    ultimately have "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = 1"
      by auto
    then have "(snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = {q'}" 
      using \<open>h_obs M q x y = Some q'\<close> unfolding h_obs_simps Let_def        
      by (metis card_1_singletonE option.inject the_elem_eq) 
    then show ?thesis 
      using * unfolding h.simps by blast
  qed

  show "({q' . (q,x,y,q') \<in> transitions M} = {q'}) \<Longrightarrow> (h_obs M q x y = Some q')"
  proof -
    assume "({q' . (q,x,y,q') \<in> transitions M} = {q'})"
    then have "snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x)) = {q'}"
      unfolding h.simps by force
    then show ?thesis
      unfolding Let_def
      by simp 
  qed
qed

lemma h_obs_state :
  assumes "h_obs M q x y = Some q'"
  shows "q' \<in> states M"
proof (cases "card (snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = 1")
  case True
  then have "(snd ` Set.filter (\<lambda> (y',q') . y' = y) (h M (q,x))) = {q'}" 
    using \<open>h_obs M q x y = Some q'\<close> unfolding h_obs_simps Let_def        
    by (metis card_1_singletonE option.inject the_elem_eq) 
  then have "(q,x,y,q') \<in> transitions M"
    unfolding h_simps by auto
  then show ?thesis
    by (metis fsm_transition_target snd_conv) 
next
  case False
  then have "h_obs M q x y = None"
    using False unfolding h_obs_simps Let_def by auto
  then show ?thesis using assms by auto 
qed 


fun after :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> 'a" where
  "after M q [] = q" |
  "after M q ((x,y)#io) = after M (the (h_obs M q x y)) io"

(*abbreviation(input) "after_initial M io \<equiv> after M (initial M) io" *)
abbreviation "after_initial M io \<equiv> after M (initial M) io"

lemma after_path :
  assumes "observable M"
  and     "path M q p"
shows "after M q (p_io p) = target q p"
using assms(2) proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons t p)
  then have "t \<in> transitions M" and "path M (t_target t) p" and "t_source t = q"
    by auto

  have "\<And> q' . (q, t_input t, t_output t, q') \<in> FSM.transitions M \<Longrightarrow> q' = t_target t"
    using observable_transition_unique[OF assms(1) \<open>t \<in> transitions M\<close>] \<open>t \<in> transitions M\<close> 
    using \<open>t_source t = q\<close> assms(1) by auto 
  then have "({q'. (q, t_input t, t_output t, q') \<in> FSM.transitions M} = {t_target t})"
    using \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close> by auto
  then have "(h_obs M q (t_input t) (t_output t)) = Some (t_target t)"
    using h_obs_Some[OF assms(1), of q "t_input t" "t_output t" "t_target t"]
    by blast 
  then have "after M q (p_io (t#p)) = after M (t_target t) (p_io p)"    
    by auto
  moreover have "target (t_target t) p = target q (t#p)"
    using \<open>t_source t = q\<close> by auto
  ultimately show ?case 
    using Cons.IH[OF \<open>path M (t_target t) p\<close>] 
    by simp
qed

lemma observable_after_path :
  assumes "observable M"
  and     "io \<in> LS M q"
obtains p where "path M q p"
            and "p_io p = io"
            and "target q p = after M q io"
  using after_path[OF assms(1)]
  using assms(2) by auto

lemma h_obs_from_LS :
  assumes "observable M"
  and     "[(x,y)] \<in> LS M q"
obtains q' where "h_obs M q x y = Some q'"
  using assms(2) h_obs_None[OF assms(1), of q x y] by force 

lemma after_h_obs :
  assumes "observable M"
  and     "h_obs M q x y = Some q'"
shows "after M q [(x,y)] = q'"
proof -
  have "path M q [(q,x,y,q')]"
    using assms(2) unfolding h_obs_Some[OF assms(1)]
    using single_transition_path by fastforce 
  then show ?thesis
    using assms(2) after_path[OF assms(1), of q "[(q,x,y,q')]"] by auto
qed

lemma after_h_obs_prepend :
  assumes "observable M"
  and     "h_obs M q x y = Some q'"
  and     "io \<in> LS M q'"
shows "after M q ((x,y)#io) = after M q' io" 
proof -
  obtain p where "path M q' p" and "p_io p = io"
    using assms(3) by auto
  then have "after M q' io = target q' p"
    using after_path[OF assms(1)]
    by blast 

  have "path M q ((q,x,y,q')#p)"
    using assms(2) path_prepend_t[OF \<open>path M q' p\<close>, of q x y] unfolding h_obs_Some[OF assms(1)] by auto
  moreover have "p_io ((q,x,y,q')#p) = (x,y)#io"
    using \<open>p_io p = io\<close> by auto
  ultimately have "after M q ((x,y)#io) = target q ((q,x,y,q')#p)"
    using after_path[OF assms(1), of q "(q,x,y,q')#p"] by simp
  moreover have "target q ((q,x,y,q')#p) = target q' p"
    by auto
  ultimately show ?thesis
    using \<open>after M q' io = target q' p\<close> by simp
qed

lemma after_split :
  assumes "observable M"
  and     "\<alpha>@\<gamma> \<in> LS M q"
shows "after M (after M q \<alpha>) \<gamma> = after M q (\<alpha> @ \<gamma>)"
proof -
  obtain p1 p2 where "path M q p1" and "path M (target q p1) p2" and "p_io p1 = \<alpha>" and "p_io p2 = \<gamma>"
    using language_state_split[OF assms(2)] 
    by blast
  then have "path M q (p1@p2)" and "p_io (p1@p2) = (\<alpha> @ \<gamma>)"
    by auto
  then have "after M q (\<alpha> @ \<gamma>) = target q (p1@p2)"
    using assms(1)
    by (metis (mono_tags, lifting) after_path) 
  moreover have "after M q \<alpha> = target q p1"
    using \<open>path M q p1\<close> \<open>p_io p1 = \<alpha>\<close> assms(1)
    by (metis (mono_tags, lifting) after_path) 
  moreover have "after M (target q p1) \<gamma> = target (target q p1) p2"
    using \<open>path M (target q p1) p2\<close> \<open>p_io p2 = \<gamma>\<close> assms(1)
    by (metis (mono_tags, lifting) after_path)
  moreover have "target (target q p1) p2 = target q (p1@p2)"
    by auto
  ultimately show ?thesis 
    by auto
qed


lemma after_io_targets :
  assumes "observable M"
  and     "io \<in> LS M q"
shows "after M q io = the_elem (io_targets M io q)"
proof -
  have "after M q io \<in> io_targets M io q"
    using after_path[OF assms(1)] assms(2)
    unfolding io_targets.simps LS.simps
    by blast 
  then show ?thesis
    using observable_io_targets[OF assms]
    by (metis singletonD the_elem_eq)
qed
    


lemma after_language_subset :
  assumes "observable M"
  and     "\<alpha>@\<gamma> \<in> L M"
  and     "\<beta> \<in> LS M (after_initial M (\<alpha>@\<gamma>))"
shows "\<gamma>@\<beta> \<in> LS M (after_initial M \<alpha>)"
  by (metis after_io_targets after_split assms(1) assms(2) assms(3) language_io_target_append language_prefix observable_io_targets observable_io_targets_language singletonI the_elem_eq)


lemma after_language_append_iff :
  assumes "observable M"
  and     "\<alpha>@\<gamma> \<in> L M"
shows "\<beta> \<in> LS M (after_initial M (\<alpha>@\<gamma>)) = (\<gamma>@\<beta> \<in> LS M (after_initial M \<alpha>))"
  by (metis after_io_targets after_language_subset after_split assms(1) assms(2) language_prefix observable_io_targets observable_io_targets_language singletonI the_elem_eq) 


lemma h_obs_language_iff :
  assumes "observable M"
  shows "(x,y)#io \<in> LS M q = (\<exists> q' . h_obs M q x y = Some q' \<and> io \<in> LS M q')"
    (is "?P1 = ?P2")
proof 
  show "?P1 \<Longrightarrow> ?P2"
  proof -
    assume ?P1
    then obtain t p where "t \<in> transitions M"
                      and "path M (t_target t) p"
                      and "t_input t = x"
                      and "t_output t = y"
                      and "t_source t = q"
                      and "p_io p = io"
      by auto
    then have "(q,x,y,t_target t) \<in> transitions M"
      by auto
    then have "h_obs M q x y = Some (t_target t)"
      unfolding h_obs_Some[OF assms]
      using assms by auto 
    moreover have "io \<in> LS M (t_target t)"
      using \<open>path M (t_target t) p\<close> \<open>p_io p = io\<close>
      by auto
    ultimately show ?P2
      by blast
  qed
  show "?P2 \<Longrightarrow> ?P1"
    unfolding h_obs_Some[OF assms] using LS_prepend_transition[where io=io and M=M]
    by (metis fst_conv mem_Collect_eq singletonI snd_conv)
qed

lemma after_language_iff :
  assumes "observable M"
  and     "\<alpha> \<in> LS M q"
shows "(\<gamma> \<in> LS M (after M q \<alpha>)) = (\<alpha>@\<gamma> \<in> LS M q)"
  by (metis after_io_targets assms(1) assms(2) language_io_target_append observable_io_targets observable_io_targets_language singletonI the_elem_eq)

(* TODO: generalise to non-observable FSMs *)
lemma language_maximal_contained_prefix_ob :
  assumes "io \<notin> LS M q"
  and     "q \<in> states M"
  and     "observable M"
obtains io' x y io'' where "io = io'@[(x,y)]@io''"
                       and "io' \<in> LS M q"
                       and "io'@[(x,y)] \<notin> LS M q"
proof -
  have "\<exists> io' x y io'' . io = io'@[(x,y)]@io'' \<and> io' \<in> LS M q \<and> io'@[(x,y)] \<notin> LS M q"
    using assms(1,2) proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)

    obtain x y where "xy = (x,y)"
      by fastforce

    show ?case proof (cases "h_obs M q x y")
      case None
      then have "[]@[(x,y)] \<notin> LS M q"
        unfolding h_obs_None[OF assms(3)] by auto
      moreover have "[] \<in> LS M q"
        using Cons.prems by auto
      moreover have "(x,y)#io = []@[(x,y)]@io"
        using Cons.prems 
        unfolding \<open>xy = (x,y)\<close> by auto
      ultimately show ?thesis
        unfolding \<open>xy = (x,y)\<close> by blast
    next
      case (Some q')
      then have "io \<notin> LS M q'"
        using h_obs_language_iff[OF assms(3), of x y io q] Cons.prems(1) 
        unfolding \<open>xy = (x,y)\<close>
        by auto
      then obtain io' x' y' io'' where "io = io'@[(x',y')]@io''"
                                   and "io' \<in> LS M q'"
                                   and "io'@[(x',y')] \<notin> LS M q'" 
        using Cons.IH[OF _ h_obs_state[OF Some]]
        by blast

      have "xy#io = (xy#io')@[(x',y')]@io''"
        using \<open>io = io'@[(x',y')]@io''\<close> by auto
      moreover have "(xy#io') \<in> LS M q"
        using \<open>io' \<in> LS M q'\<close> Some 
        unfolding \<open>xy = (x,y)\<close> h_obs_language_iff[OF assms(3)]
        by blast
      moreover have "(xy#io')@[(x',y')] \<notin> LS M q"
        using \<open>io'@[(x',y')] \<notin> LS M q'\<close> Some h_obs_language_iff[OF assms(3), of x y "io'@[(x',y')]" q]
        unfolding \<open>xy = (x,y)\<close> 
        by auto
      ultimately show ?thesis
        by blast
    qed
  qed
  then show ?thesis 
    using that by blast
qed

lemma after_is_state :
  assumes "observable M"
  assumes "io \<in> LS M q"
  shows "FSM.after M q io \<in> states M" 
  using assms
  by (metis observable_after_path path_target_is_state) 

lemma after_reachable_initial :
  assumes "observable M"
  and     "io \<in> L M"
shows "after_initial M io \<in> reachable_states M" 
proof -
  obtain p where "path M (initial M) p" and "p_io p = io"
    using assms(2) by auto
  then have "after_initial M io = target (initial M) p"
    using after_path[OF assms(1)]
    by blast 
  then show ?thesis
    unfolding reachable_states_def using \<open>path M (initial M) p\<close> by blast
qed

lemma after_transition :
  assumes "observable M"
  and     "(q,x,y,q') \<in> transitions M"
shows "after M q [(x,y)] = q'"
  using after_path[OF assms(1) single_transition_path[OF assms(2)]] 
  by auto

lemma after_transition_exhaust :
  assumes "observable M"
  and     "t \<in> transitions M"
shows "t_target t = after M (t_source t) [(t_input t, t_output t)]"
  using after_transition[OF assms(1)] assms(2)
  by (metis surjective_pairing) 

lemma after_reachable :
  assumes "observable M"
  and     "io \<in> LS M q"
  and     "q \<in> reachable_states M"
shows "after M q io \<in> reachable_states M"
proof -
  obtain p where "path M q p" and "p_io p = io"
    using assms(2) by auto
  then have "after M q io = target q p"
    using after_path[OF assms(1)] by force

  obtain p' where "path M (initial M) p'" and "target (initial M) p' = q"
    using assms(3) unfolding reachable_states_def by blast

  then have "path M (initial M) (p'@p)"
    using \<open>path M q p\<close> by auto
  moreover have "after M q io = target (initial M) (p'@p)"
    using \<open>target (initial M) p' = q\<close>
    unfolding \<open>after M q io = target q p\<close> 
    by auto
  ultimately show ?thesis
    unfolding reachable_states_def by blast
qed

lemma observable_after_language_append :
  assumes "observable M"
  and     "io1 \<in> LS M q"
  and     "io2 \<in> LS M (after M q io1)"
shows "io1@io2 \<in> LS M q"
  using observable_after_path[OF assms(1,2)] assms(3)
proof -
  assume a1: "\<And>thesis. (\<And>p. \<lbrakk>path M q p; p_io p = io1; target q p = after M q io1\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  have "\<exists>ps. io2 = p_io ps \<and> path M (after M q io1) ps"
    using \<open>io2 \<in> LS M (after M q io1)\<close> by auto
  moreover
  { assume "(\<exists>ps. io2 = p_io ps \<and> path M (after M q io1) ps) \<and> (\<forall>ps. io1 @ io2 \<noteq> p_io ps \<or> \<not> path M q ps)"
    then have "io1 @ io2 \<in> {p_io ps |ps. path M q ps}"
      using a1 by (metis (lifting) map_append path_append) }
  ultimately show ?thesis
    by auto
qed 


lemma observable_after_language_none :
  assumes "observable M"
  and     "io1 \<in> LS M q"
  and     "io2 \<notin> LS M (after M q io1)"
shows "io1@io2 \<notin> LS M q"
  using after_path[OF assms(1)] language_state_split[of  io1 io2 M q]
  by (metis (mono_tags, lifting) assms(3) language_intro) 


lemma observable_after_eq :
  assumes "observable M"
  and     "after M q io1 = after M q io2"
  and     "io1 \<in> LS M q"
  and     "io2 \<in> LS M q"
shows "io1@io \<in> LS M q \<longleftrightarrow> io2@io \<in> LS M q"
  using observable_after_language_append[OF assms(1,3), of io]
        observable_after_language_append[OF assms(1,4), of io]
        assms(2)
  by (metis assms(1) language_prefix observable_after_language_none) 

lemma observable_after_target : 
  assumes "observable M"
  and     "io @ io' \<in> LS M q"
  and     "path M (FSM.after M q io) p"
  and     "p_io p = io'"
shows "target (FSM.after M q io) p = (FSM.after M q (io @ io'))"
proof -
  obtain p' where "path M q p'" and "p_io p' = io @ io'"
    using \<open>io @ io' \<in> LS M q\<close> by auto

  then have "path M q (take (length io) p')"
        and "p_io (take (length io) p') = io"
        and "path M (target q (take (length io) p')) (drop (length io) p')"
        and "p_io (drop (length io) p') = io'"
    using path_io_split[of M q p' io io']
    by auto
  then have "FSM.after M q io = target q (take (length io) p')"
    using after_path assms(1) by fastforce
  then have "p = (drop (length io) p')"   
    using \<open>path M (target q (take (length io) p')) (drop (length io) p')\<close> \<open>p_io (drop (length io) p') = io'\<close>
          assms(3,4)
          observable_path_unique[OF \<open>observable M\<close>]
    by force

  have "(FSM.after M q (io @ io')) = target q p'"
    using after_path[OF \<open>observable M\<close> \<open>path M q p'\<close>] unfolding \<open>p_io p' = io @ io'\<close> .
  moreover have "target (FSM.after M q io) p = target q p'"
    using \<open>FSM.after M q io = target q (take (length io) p')\<close>
    by (metis \<open>p = drop (length io) p'\<close> append_take_drop_id path_append_target) 
  ultimately show ?thesis
    by simp
qed


fun is_in_language :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times>'c) list \<Rightarrow> bool" where
  "is_in_language M q [] = True" |
  "is_in_language M q ((x,y)#io) = (case h_obs M q x y of
    None \<Rightarrow> False |
    Some q' \<Rightarrow> is_in_language M q' io)"

lemma is_in_language_iff :
  assumes "observable M"
  and     "q \<in> states M"
  shows "is_in_language M q io \<longleftrightarrow> io \<in> LS M q"
using assms(2) proof (induction io arbitrary: q)
  case Nil
  then show ?case
    by auto 
next
  case (Cons xy io)

  obtain x y where "xy = (x,y)"
    using prod.exhaust by metis

  show ?case 
    unfolding \<open>xy = (x,y)\<close>
    unfolding h_obs_language_iff[OF assms(1), of x y io q] 
    unfolding is_in_language.simps
    apply (cases "h_obs M q x y") 
    apply auto[1]
    by (metis Cons.IH h_obs_state option.simps(5))  
qed

lemma observable_paths_for_io :
  assumes "observable M"
  and     "io \<in> LS M q"
obtains p where "paths_for_io M q io = {p}"
proof -
  obtain p where "path M q p" and "p_io p = io"
    using assms(2) by auto
  then have "p \<in> paths_for_io M q io"
    unfolding paths_for_io_def 
    by blast
  then show ?thesis 
    using that[of p]
    using observable_path_unique[OF assms(1) \<open>path M q p\<close>] \<open>p_io p = io\<close>
    unfolding paths_for_io_def 
    by force
qed

lemma io_targets_language :
  assumes "q' \<in> io_targets M io q"
  shows "io \<in> LS M q"
  using assms by auto


lemma observable_after_reachable_surj :
  assumes "observable M"
  shows "(after_initial M) ` (L M) = reachable_states M"
proof 
  show "after_initial M ` L M \<subseteq> reachable_states M"
    using after_reachable[OF assms _ reachable_states_initial]
    by blast
  show "reachable_states M \<subseteq> after_initial M ` L M"
    unfolding reachable_states_def
    using after_path[OF assms]
    using image_iff by fastforce 
qed


lemma observable_minimal_size_r_language_distinct :
  assumes "minimal M1"
  and     "minimal M2"
  and     "observable M1"
  and     "observable M2"
  and     "size_r M1 < size_r M2" 
shows "L M1 \<noteq> L M2"
proof 
  assume "L M1 = L M2"

  define V where "V = (\<lambda> q . SOME io . io \<in> L M1 \<and> after_initial M2 io = q)"

  have "\<And> q . q \<in> reachable_states M2 \<Longrightarrow> V q \<in> L M1 \<and> after_initial M2 (V q) = q"
  proof -
    fix q assume "q \<in> reachable_states M2"
    then have "\<exists> io . io \<in> L M1 \<and> after_initial M2 io = q"
      unfolding \<open>L M1 = L M2\<close>
      by (metis assms(4) imageE observable_after_reachable_surj)
    then show "V q \<in> L M1 \<and> after_initial M2 (V q) = q"
      unfolding V_def 
      using someI_ex[of "\<lambda> io . io \<in> L M1 \<and> after_initial M2 io = q"] by blast
  qed
  then have "(after_initial M1) ` V ` reachable_states M2 \<subseteq> reachable_states M1"
    by (metis assms(3) image_mono image_subsetI observable_after_reachable_surj)
  then have "card (after_initial M1 ` V ` reachable_states M2) \<le> size_r M1"
    using reachable_states_finite[of M1]
    by (meson card_mono) 

  have "(after_initial M2) ` V ` reachable_states M2 = reachable_states M2"
  proof 
    show "after_initial M2 ` V ` reachable_states M2 \<subseteq> reachable_states M2"
      using \<open>\<And> q . q \<in> reachable_states M2 \<Longrightarrow> V q \<in> L M1 \<and> after_initial M2 (V q) = q\<close> by auto
    show "reachable_states M2 \<subseteq> after_initial M2 ` V ` reachable_states M2"
      using \<open>\<And> q . q \<in> reachable_states M2 \<Longrightarrow> V q \<in> L M1 \<and> after_initial M2 (V q) = q\<close> observable_after_reachable_surj[OF assms(4)] unfolding \<open>L M1 = L M2\<close>
      using image_iff by fastforce
  qed
  then have "card ((after_initial M2) ` V ` reachable_states M2) = size_r M2" 
    by auto

  have *: "finite (V ` reachable_states M2)"
    by (simp add: reachable_states_finite) 

  have **: "card ((after_initial M1) ` V ` reachable_states M2) < card ((after_initial M2) ` V ` reachable_states M2)"
    using assms(5) \<open>card (after_initial M1 ` V ` reachable_states M2) \<le> size_r M1\<close>
    unfolding \<open>card ((after_initial M2) ` V ` reachable_states M2) = size_r M2\<close> 
    by linarith

  obtain io1 io2 where "io1 \<in> V ` reachable_states M2"
                       "io2 \<in> V ` reachable_states M2" 
                       "after_initial M2 io1 \<noteq> after_initial M2 io2" 
                       "after_initial M1 io1 = after_initial M1 io2"
    using finite_card_less_witnesses[OF * **]
    by blast
  then have "io1 \<in> L M1" and "io2 \<in> L M1" and "io1 \<in> L M2" and "io2 \<in> L M2"
    using \<open>\<And> q . q \<in> reachable_states M2 \<Longrightarrow> V q \<in> L M1 \<and> after_initial M2 (V q) = q\<close> unfolding \<open>L M1 = L M2\<close>
    by auto
  then have "after_initial M1 io1 \<in> reachable_states M1"
            "after_initial M1 io2 \<in> reachable_states M1"
            "after_initial M2 io1 \<in> reachable_states M2"
            "after_initial M2 io2 \<in> reachable_states M2"
    using after_reachable[OF assms(3) _ reachable_states_initial] after_reachable[OF assms(4) _ reachable_states_initial]
    by blast+

  obtain io3 where "io3 \<in> LS M2 (after_initial M2 io1) = (io3 \<notin> LS M2 (after_initial M2 io2))"
    using reachable_state_is_state[OF \<open>after_initial M2 io1 \<in> reachable_states M2\<close>] 
          reachable_state_is_state[OF \<open>after_initial M2 io2 \<in> reachable_states M2\<close>] 
          \<open>after_initial M2 io1 \<noteq> after_initial M2 io2\<close> assms(2)
    unfolding minimal.simps by blast
  then have "io1@io3 \<in> L M2 = (io2@io3 \<notin> L M2)"
    using observable_after_language_append[OF assms(4) \<open>io1 \<in> L M2\<close>]
          observable_after_language_append[OF assms(4) \<open>io2 \<in> L M2\<close>]
          observable_after_language_none[OF assms(4) \<open>io1 \<in> L M2\<close>]
          observable_after_language_none[OF assms(4) \<open>io2 \<in> L M2\<close>]
    by blast
  moreover have "io1@io3 \<in> L M1 = (io2@io3 \<in> L M1)"
    by (meson \<open>after_initial M1 io1 = after_initial M1 io2\<close> \<open>io1 \<in> L M1\<close> \<open>io2 \<in> L M1\<close> assms(3) observable_after_eq) 
  ultimately show False
    using \<open>L M1 = L M2\<close> by blast
qed

(* language equivalent minimal FSMs have the same number of reachable states *)
lemma minimal_equivalence_size_r :
  assumes "minimal M1"
  and     "minimal M2"
  and     "observable M1"
  and     "observable M2"
  and     "L M1 = L M2"
shows "size_r M1 = size_r M2" 
  using observable_minimal_size_r_language_distinct[OF assms(1-4)]
        observable_minimal_size_r_language_distinct[OF assms(2,1,4,3)]
        assms(5)
  using nat_neq_iff by auto


subsection \<open>Conformity Relations\<close>

fun is_io_reduction_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd \<Rightarrow> bool" where
  "is_io_reduction_state A a B b = (LS A a \<subseteq> LS B b)"

abbreviation(input) "is_io_reduction A B \<equiv> is_io_reduction_state A (initial A) B (initial B)" 
notation 
  is_io_reduction ("_ \<preceq> _")


fun is_io_reduction_state_on_inputs :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'b list set \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd \<Rightarrow> bool" where
  "is_io_reduction_state_on_inputs A a U B b = (LS\<^sub>i\<^sub>n A a U \<subseteq> LS\<^sub>i\<^sub>n B b U)"

abbreviation(input) "is_io_reduction_on_inputs A U B \<equiv> is_io_reduction_state_on_inputs A (initial A) U B (initial B)" 
notation 
  is_io_reduction_on_inputs ("_ \<preceq>\<lbrakk>_\<rbrakk> _")





subsection \<open>A Pass Relation for Reduction and Test Represented as Sets of Input-Output Sequences\<close>

definition pass_io_set :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "pass_io_set M ios = (\<forall> io x y . io@[(x,y)] \<in> ios \<longrightarrow> (\<forall> y' . io@[(x,y')] \<in> L M \<longrightarrow> io@[(x,y')] \<in> ios))"

definition pass_io_set_maximal :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list set \<Rightarrow> bool" where
  "pass_io_set_maximal M ios = (\<forall> io x y io' . io@[(x,y)]@io' \<in> ios \<longrightarrow> (\<forall> y' . io@[(x,y')] \<in> L M \<longrightarrow> (\<exists> io''. io@[(x,y')]@io'' \<in> ios)))"


lemma pass_io_set_from_pass_io_set_maximal :
  "pass_io_set_maximal M ios = pass_io_set M {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios}"
proof -
  have "\<And> io x y io' . io@[(x,y)]@io' \<in> ios \<Longrightarrow> io@[(x,y)] \<in> {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios}"
    by auto
  moreover have "\<And> io x y . io@[(x,y)] \<in> {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios} \<Longrightarrow> \<exists> io' . io@[(x,y)]@io' \<in> ios"
    by auto
  ultimately show ?thesis
    unfolding pass_io_set_def pass_io_set_maximal_def
    by meson 
qed


lemma pass_io_set_maximal_from_pass_io_set :
  assumes "finite ios"
  and     "\<And> io' io'' . io'@io'' \<in> ios \<Longrightarrow> io' \<in> ios"
shows "pass_io_set M ios = pass_io_set_maximal M {io' \<in> ios . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> ios)}"
proof -
  have "\<And> io x y . io@[(x,y)] \<in> ios \<Longrightarrow> \<exists> io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)}"
  proof -
    fix io x y assume "io@[(x,y)] \<in> ios"
    show "\<exists> io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)}"
      using finite_set_elem_maximal_extension_ex[OF \<open>io@[(x,y)] \<in> ios\<close> assms(1)] by force
  qed
  moreover have "\<And> io x y io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)} \<Longrightarrow> io@[(x,y)] \<in> ios"
    using \<open>\<And> io' io'' . io'@io'' \<in> ios \<Longrightarrow> io' \<in> ios\<close> by force
  ultimately show ?thesis
    unfolding pass_io_set_def pass_io_set_maximal_def 
    by meson 
qed


subsection \<open>Relaxation of IO based test suites to sets of input sequences\<close>

abbreviation(input) "input_portion xs \<equiv> map fst xs"

lemma equivalence_io_relaxation :
  assumes "(L M1 = L M2) \<longleftrightarrow> (L M1 \<inter> T = L M2 \<inter> T)"
shows "(L M1 = L M2) \<longleftrightarrow> ({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')})" 
proof 
  show "(L M1 = L M2) \<Longrightarrow> ({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')})"
    by blast
  show "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> L M1 = L M2" 
  proof -
    have *:"\<And> M . {io . io \<in> L M \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = L M \<inter> {io . \<exists> io' \<in> T . input_portion io = input_portion io'}"
      by blast

    have "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> (L M1 \<inter> T = L M2 \<inter> T)"
      unfolding * by blast
    then show "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} = {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> L M1 = L M2"
      using assms by blast
  qed
qed

lemma reduction_io_relaxation :
  assumes "(L M1 \<subseteq> L M2) \<longleftrightarrow> (L M1 \<inter> T \<subseteq> L M2 \<inter> T)"
shows "(L M1 \<subseteq> L M2) \<longleftrightarrow> ({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')})" 
proof 
  show "(L M1 \<subseteq> L M2) \<Longrightarrow> ({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')})"
    by blast
  show "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> L M1 \<subseteq> L M2" 
  proof -
    have *:"\<And> M . {io . io \<in> L M \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> L M \<inter> {io . \<exists> io' \<in> T . input_portion io = input_portion io'}"
      by blast

    have "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> (L M1 \<inter> T \<subseteq> L M2 \<inter> T)"
      unfolding * by blast
    then show "({io . io \<in> L M1 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')} \<subseteq> {io . io \<in> L M2 \<and> (\<exists> io' \<in> T . input_portion io = input_portion io')}) \<Longrightarrow> L M1 \<subseteq> L M2"
      using assms by blast
  qed
qed



subsection \<open>Submachines\<close>

fun is_submachine :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> transitions A \<subseteq> transitions B \<and> inputs A = inputs B \<and> outputs A = outputs B \<and> states A \<subseteq> states B)"
  

lemma submachine_path_initial :
  assumes "is_submachine A B"
  and     "path A (initial A) p"
shows "path B (initial B) p"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a p)
  then show ?case
    by fastforce
qed
   

lemma submachine_path :
  assumes "is_submachine A B"
  and     "path A q p"
shows "path B q p"
  by (meson assms(1) assms(2) is_submachine.elims(2) path_begin_state subsetD transition_subset_path)
  

lemma submachine_reduction : 
  assumes "is_submachine A B"
  shows "is_io_reduction A B"
  using submachine_path[OF assms] assms by auto 


lemma complete_submachine_initial :
  assumes "is_submachine A B"
      and "completely_specified A"
  shows "completely_specified_state B (initial B)"
  using assms(1) assms(2) fsm_initial subset_iff by fastforce


lemma submachine_language :
  assumes "is_submachine S M"
  shows "L S \<subseteq> L M"
  by (meson assms is_io_reduction_state.elims(2) submachine_reduction)


lemma submachine_observable :
  assumes "is_submachine S M"
  and     "observable M"
shows "observable S"
  using assms unfolding is_submachine.simps observable.simps by blast


lemma submachine_transitive :
  assumes "is_submachine S M"
  and     "is_submachine S' S"
shows "is_submachine S' M"
  using assms unfolding is_submachine.simps by force


lemma transitions_subset_path :
  assumes "set p \<subseteq> transitions M"
  and     "p \<noteq> []"
  and     "path S q p"
shows "path M q p"
  using assms by (induction p arbitrary: q; auto)


lemma transition_subset_paths :
  assumes "transitions S \<subseteq> transitions M"
  and "initial S \<in> states M"
  and "inputs S = inputs M"
  and "outputs S = outputs M"
  and "path S (initial S) p"
shows "path M (initial S) p"
  using assms(5) proof (induction p rule: rev_induct)
case Nil
  then show ?case using assms(2) by auto
next
  case (snoc t p)
  then have "path S (initial S) p" 
        and "t \<in> transitions S" 
        and "t_source t = target (initial S) p" 
        and "path M (initial S) p"
    by auto

  have "t \<in> transitions M"
    using assms(1) \<open>t \<in> transitions S\<close> by auto
  moreover have "t_source t \<in> states M"
    using \<open>t_source t = target (initial S) p\<close> \<open>path M (initial S) p\<close>
    using path_target_is_state by fastforce 
  ultimately have "t \<in> transitions M"
    using \<open>t \<in> transitions S\<close> assms(3,4) by auto
  then show ?case
    using \<open>path M (initial S) p\<close>
    using snoc.prems by auto 
qed 


lemma submachine_reachable_subset :
  assumes "is_submachine A B"
shows "reachable_states A \<subseteq> reachable_states B" 
  using assms submachine_path_initial[OF assms] 
  unfolding is_submachine.simps reachable_states_def by force


lemma submachine_simps :
  assumes "is_submachine A B"
shows "initial A = initial B"
and   "states A \<subseteq> states B"
and   "inputs A = inputs B"
and   "outputs A = outputs B"
and   "transitions A \<subseteq> transitions B"
  using assms unfolding is_submachine.simps by blast+


lemma submachine_deadlock :
  assumes "is_submachine A B"
      and "deadlock_state B q"
    shows "deadlock_state A q"
  using assms(1) assms(2) in_mono by auto 



subsection \<open>Changing Initial States\<close>

lift_definition from_FSM :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.from_FSMI
  by simp 

lemma from_FSM_simps[simp]:
  assumes "q \<in> states M"
  shows
  "initial (from_FSM M q) = q"  
  "inputs (from_FSM M q) = inputs M"
  "outputs (from_FSM M q) = outputs M"
  "transitions (from_FSM M q) = transitions M"
  "states (from_FSM M q) = states M" using assms by (transfer; simp)+


lemma from_FSM_path_initial :
  assumes "q \<in> states M"
  shows "path M q p = path (from_FSM M q) (initial (from_FSM M q)) p"
  by (metis assms from_FSM_simps(1) from_FSM_simps(4) from_FSM_simps(5) order_refl 
        transition_subset_path)


lemma from_FSM_path :
  assumes "q \<in> states M"
      and "path (from_FSM M q) q' p"
    shows "path M q' p"
  using assms(1) assms(2) path_transitions transitions_subset_path by fastforce


lemma from_FSM_reachable_states :
  assumes "q \<in> reachable_states M"
  shows "reachable_states (from_FSM M q) \<subseteq> reachable_states M"
proof
  from assms obtain p where "path M (initial M) p" and "target (initial M) p = q"
    unfolding reachable_states_def by blast
  then have "q \<in> states M"
    by (meson path_target_is_state)

  fix q' assume "q' \<in> reachable_states (from_FSM M q)"
  then obtain p' where "path (from_FSM M q) q p'" and "target q p' = q'"
    unfolding reachable_states_def from_FSM_simps[OF \<open>q \<in> states M\<close>] by blast
  then have "path M (initial M) (p@p')" and "target (initial M) (p@p') = q'"
    using from_FSM_path[OF \<open>q \<in> states M\<close> ] \<open>path M (initial M) p\<close>
    using \<open>target (FSM.initial M) p = q\<close> by auto

  then show "q' \<in> reachable_states M"
    unfolding reachable_states_def by blast
qed
  

lemma submachine_from :
  assumes "is_submachine S M"
      and "q \<in> states S"
  shows "is_submachine (from_FSM S q) (from_FSM M q)"
proof -
  have "path S q []"
    using assms(2) by blast
  then have "path M q []"
    by (meson assms(1) submachine_path)
  then show ?thesis
    using assms(1) assms(2) by force
qed


lemma from_FSM_path_rev_initial :
  assumes "path M q p"
  shows "path (from_FSM M q) q p"
  by (metis (no_types) assms from_FSM_path_initial from_FSM_simps(1) path_begin_state)


lemma from_from[simp] :  
  assumes "q1 \<in> states M"
  and     "q1' \<in> states M"
shows "from_FSM (from_FSM M q1) q1' = from_FSM M q1'" (is "?M = ?M'") 
proof -
  have *: "q1' \<in> states (from_FSM M q1)"
    using assms(2) unfolding from_FSM_simps(5)[OF assms(1)] by assumption
  
  have "initial ?M = initial ?M'"
  and  "states ?M = states ?M'"
  and  "inputs ?M = inputs ?M'"
  and  "outputs ?M = outputs ?M'"
  and  "transitions ?M = transitions ?M'"
    unfolding  from_FSM_simps[OF *] from_FSM_simps[OF assms(1)] from_FSM_simps[OF assms(2)] by simp+

  then show ?thesis by (transfer; force)
qed


lemma from_FSM_completely_specified : 
  assumes "completely_specified M"
shows "completely_specified (from_FSM M q)" proof (cases "q \<in> states M")
  case True
  then show ?thesis
    using assms by auto 
next
  case False
  then have "from_FSM M q = M" by (transfer; auto)
  then show ?thesis using assms by auto
qed


lemma from_FSM_single_input : 
  assumes "single_input M"
shows "single_input (from_FSM M q)" proof (cases "q \<in> states M")
  case True
  then show ?thesis
    using assms
    by (metis from_FSM_simps(4) single_input.elims(1))  
next
  case False
  then have "from_FSM M q = M" by (transfer; auto)
  then show ?thesis using assms
    by presburger 
qed


lemma from_FSM_acyclic :
  assumes "q \<in> reachable_states M"
  and     "acyclic M"
shows "acyclic (from_FSM M q)"
  using assms(1)
        acyclic_paths_from_reachable_states[OF assms(2), of _ q]
        from_FSM_path[of q M q]
        path_target_is_state
        reachable_state_is_state[OF assms(1)]
        from_FSM_simps(1)
  unfolding acyclic.simps
            reachable_states_def
  by force
  


lemma from_FSM_observable :
  assumes "observable M"
shows "observable (from_FSM M q)"
proof (cases "q \<in> states M")
  case True
  then show ?thesis
    using assms
  proof -
    have f1: "\<forall>f. observable f = (\<forall>a b c aa ab. ((a::'a, b::'b, c::'c, aa) \<notin> FSM.transitions f \<or> (a, b, c, ab) \<notin> FSM.transitions f) \<or> aa = ab)"
      by force
    have "\<forall>a f. a \<notin> FSM.states (f::('a, 'b, 'c) fsm) \<or> FSM.transitions (FSM.from_FSM f a) = FSM.transitions f"
      by (meson from_FSM_simps(4))
    then show ?thesis
      using f1 True assms by presburger
  qed  
next
  case False
  then have "from_FSM M q = M" by (transfer; auto)
  then show ?thesis using assms by presburger
qed


lemma observable_language_next :
  assumes "io#ios \<in> LS M (t_source t)"
  and     "observable M"
  and     "t \<in> transitions M"
  and     "t_input t = fst io"
  and     "t_output t = snd io"
shows "ios \<in> L (from_FSM M (t_target t))"
proof -
  obtain p where "path M (t_source t) p" and "p_io p = io#ios"
    using assms(1)
  proof -
    assume a1: "\<And>p. \<lbrakk>path M (t_source t) p; p_io p = io # ios\<rbrakk> \<Longrightarrow> thesis"
    obtain pps :: "('a \<times> 'b) list \<Rightarrow> 'c \<Rightarrow> ('c, 'a, 'b) fsm \<Rightarrow> ('c \<times> 'a \<times> 'b \<times> 'c) list" where
      "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (pps x0 x1 x2) \<and> path x2 x1 (pps x0 x1 x2))"
      by moura
    then have "\<exists>ps. path M (t_source t) ps \<and> p_io ps = io # ios"
      using assms(1) by auto
    then show ?thesis
      using a1 by meson
  qed
  then obtain t' p' where "p = t' # p'"
    by auto
  then have "t' \<in> transitions M" and "t_source t' = t_source t" and "t_input t' = fst io" and "t_output t' = snd io" 
    using \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "t = t'"
    using assms(2,3,4,5) unfolding observable.simps
    by (metis (no_types, opaque_lifting) prod.expand) 

  then have "path M (t_target t) p'" and "p_io p' = ios"
    using \<open>p = t' # p'\<close> \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "path (from_FSM M (t_target t)) (initial (from_FSM M (t_target t))) p'"
    by (meson assms(3) from_FSM_path_initial fsm_transition_target)

  then show ?thesis using \<open>p_io p' = ios\<close> by auto
qed


lemma from_FSM_language :
  assumes "q \<in> states M"
  shows "L (from_FSM M q) = LS M q"
  using assms unfolding LS.simps by (meson from_FSM_path_initial)


lemma observable_transition_target_language_subset :
  assumes "LS M (t_source t1) \<subseteq> LS M (t_source t2)"
  and     "t1 \<in> transitions M"
  and     "t2 \<in> transitions M"
  and     "t_input t1 = t_input t2"
  and     "t_output t1 = t_output t2"
  and     "observable M"
shows "LS M (t_target t1) \<subseteq> LS M (t_target t2)"
proof (rule ccontr)
  assume "\<not> LS M (t_target t1) \<subseteq> LS M (t_target t2)"
  then obtain ioF where "ioF \<in> LS M (t_target t1)" and "ioF \<notin> LS M (t_target t2)"
    by blast
  then have "(t_input t1, t_output t1)#ioF \<in> LS M (t_source t1)"
    using LS_prepend_transition assms(2) by blast
  then have *: "(t_input t1, t_output t1)#ioF \<in> LS M (t_source t2)"
    using assms(1) by blast
  
  have "ioF \<in> LS M (t_target t2)"
    using observable_language_next[OF * \<open>observable M\<close> \<open>t2 \<in> transitions M\<close> ] unfolding assms(4,5) fst_conv snd_conv
    by (metis assms(3) from_FSM_language fsm_transition_target) 
  then show False
    using \<open>ioF \<notin> LS M (t_target t2)\<close> by blast
qed

lemma observable_transition_target_language_eq :
  assumes "LS M (t_source t1) = LS M (t_source t2)"
  and     "t1 \<in> transitions M"
  and     "t2 \<in> transitions M"
  and     "t_input t1 = t_input t2"
  and     "t_output t1 = t_output t2"
  and     "observable M"
shows "LS M (t_target t1) = LS M (t_target t2)"
  using observable_transition_target_language_subset[OF _ assms(2,3,4,5,6)]
        observable_transition_target_language_subset[OF _ assms(3,2) assms(4,5)[symmetric] assms(6)]
        assms(1) 
  by blast


lemma language_state_prepend_transition : 
  assumes "io \<in> LS (from_FSM A (t_target t)) (initial (from_FSM A (t_target t)))"
  and     "t \<in> transitions A"
shows "p_io [t] @ io \<in> LS A (t_source t)" 
proof -
  obtain p where "path (from_FSM A (t_target t)) (initial (from_FSM A (t_target t))) p"
           and   "p_io p = io"
    using assms(1) unfolding LS.simps by blast
  then have "path A (t_target t) p"
    by (meson assms(2) from_FSM_path_initial fsm_transition_target)
  then have "path A (t_source t) (t # p)"
    using assms(2) by auto
  then show ?thesis 
    using \<open>p_io p = io\<close> unfolding LS.simps
    by force 
qed

lemma observable_language_transition_target :
  assumes "observable M"
  and     "t \<in> transitions M"
  and     "(t_input t, t_output t) # io \<in> LS M (t_source t)"
shows "io \<in> LS M (t_target t)"
  by (metis (no_types) assms(1) assms(2) assms(3) from_FSM_language fsm_transition_target fst_conv observable_language_next snd_conv)

lemma LS_single_transition :
  "[(x,y)] \<in> LS M q \<longleftrightarrow> (\<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x \<and> t_output t = y)" 
proof 
  show "[(x, y)] \<in> LS M q \<Longrightarrow> \<exists>t\<in>FSM.transitions M. t_source t = q \<and> t_input t = x \<and> t_output t = y" 
    by auto
  show "\<exists>t\<in>FSM.transitions M. t_source t = q \<and> t_input t = x \<and> t_output t = y \<Longrightarrow> [(x, y)] \<in> LS M q"
    by (metis LS_prepend_transition from_FSM_language fsm_transition_target language_contains_empty_sequence)
qed

lemma h_obs_language_append :
  assumes "observable M"
  and     "u \<in> L M"
  and     "h_obs M (after_initial M u) x y \<noteq> None"
shows "u@[(x,y)] \<in> L M"
  using after_language_iff[OF assms(1,2), of "[(x,y)]"]
  using h_obs_None[OF assms(1)] assms(3)
  unfolding LS_single_transition
  by (metis old.prod.inject prod.collapse)


lemma h_obs_language_single_transition_iff :
  assumes "observable M"
  shows "[(x,y)] \<in> LS M q \<longleftrightarrow> h_obs M q x y \<noteq> None"
  using h_obs_None[OF assms(1), of q x y] 
  unfolding LS_single_transition
  by (metis fst_conv prod.exhaust_sel snd_conv)

(* TODO: generalise to non-observable FSMs *)
lemma minimal_failure_prefix_ob :
  assumes "observable M" 
  and     "observable I"
  and     "qM \<in> states M"
  and     "qI \<in> states I"
  and     "io \<in> LS I qI - LS M qM"
obtains io' xy io'' where "io = io'@[xy]@io''"
                      and "io' \<in> LS I qI \<inter> LS M qM"  
                      and "io'@[xy] \<in> LS I qI - LS M qM"
proof -
  have "\<exists> io' xy io'' . io = io'@[xy]@io'' \<and> io' \<in> LS I qI \<inter> LS M qM \<and> io'@[xy] \<in> LS I qI - LS M qM"
  using assms(3,4,5) proof (induction io arbitrary: qM qI)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)
    show ?case proof (cases "[xy] \<in> LS I qI - LS M qM")
      case True

      have "xy # io = []@[xy]@io" 
        by auto
      moreover have "[] \<in> LS I qI \<inter> LS M qM"
        using \<open>qM \<in> states M\<close> \<open>qI \<in> states I\<close> by auto
      moreover have "[]@[xy] \<in> LS I qI - LS M qM"
        using True by auto
      ultimately show ?thesis 
        by blast
    next
      case False

      obtain x y where "xy = (x,y)"
        by (meson surj_pair)

      have "[(x,y)] \<in> LS M qM"
        using \<open>xy = (x,y)\<close> False \<open>xy # io \<in> LS I qI - LS M qM\<close>
        by (metis DiffD1 DiffI append_Cons append_Nil language_prefix)
      then obtain qM' where "(qM,x,y,qM') \<in> transitions M"
        by auto
      then have "io \<notin> LS M qM'"
        using observable_language_transition_target[OF \<open>observable M\<close>]
              \<open>xy = (x,y)\<close> \<open>xy # io \<in> LS I qI - LS M qM\<close>
        by (metis DiffD2 LS_prepend_transition fst_conv snd_conv)

      have "[(x,y)] \<in> LS I qI"
        using \<open>xy = (x,y)\<close> \<open>xy # io \<in> LS I qI - LS M qM\<close>
        by (metis DiffD1 append_Cons append_Nil language_prefix)
      then obtain qI' where "(qI,x,y,qI') \<in> transitions I"
        by auto
      then have "io \<in> LS I qI'"
        using observable_language_next[of xy io I "(qI,x,y,qI')", OF _ \<open>observable I\<close>]
              \<open>xy # io \<in> LS I qI - LS M qM\<close> fsm_transition_target[OF \<open>(qI,x,y,qI') \<in> transitions I\<close>]
        unfolding \<open>xy = (x,y)\<close> fst_conv snd_conv
        by (metis DiffD1 from_FSM_language) 

      obtain io' xy' io'' where "io = io'@[xy']@io''" and "io' \<in> LS I qI' \<inter> LS M qM'" and "io'@[xy'] \<in> LS I qI' - LS M qM'"
        using \<open>io \<in> LS I qI'\<close> \<open>io \<notin> LS M qM'\<close>
              Cons.IH[OF fsm_transition_target[OF \<open>(qM,x,y,qM') \<in> transitions M\<close>]
                         fsm_transition_target[OF \<open>(qI,x,y,qI') \<in> transitions I\<close>] ] 
        unfolding fst_conv snd_conv
        by blast

      have "xy#io = (xy#io')@[xy']@io''"
        using \<open>io = io'@[xy']@io''\<close> \<open>xy = (x,y)\<close> by auto
      moreover have "xy#io' \<in> LS I qI \<inter> LS M qM"
        using LS_prepend_transition[OF \<open>(qI,x,y,qI') \<in> transitions I\<close>, of io'] 
        using LS_prepend_transition[OF \<open>(qM,x,y,qM') \<in> transitions M\<close>, of io'] 
        using \<open>io' \<in> LS I qI' \<inter> LS M qM'\<close>
        unfolding \<open>xy = (x,y)\<close> fst_conv snd_conv 
        by auto
      moreover have "(xy#io')@[xy'] \<in> LS I qI - LS M qM"
        using LS_prepend_transition[OF \<open>(qI,x,y,qI') \<in> transitions I\<close>, of "io'@[xy']"] 
        using observable_language_transition_target[OF \<open>observable M\<close> \<open>(qM,x,y,qM') \<in> transitions M\<close>, of "io'@[xy']"] 
        using \<open>io'@[xy'] \<in> LS I qI' - LS M qM'\<close>
        unfolding \<open>xy = (x,y)\<close> fst_conv snd_conv
        by fastforce
      ultimately show ?thesis 
        by blast
    qed
  qed
  then show ?thesis 
    using that by blast
qed

subsection \<open>Language and Defined Inputs\<close>

lemma defined_inputs_code : "defined_inputs M q = t_input ` Set.filter (\<lambda>t . t_source t = q) (transitions M)"
  unfolding defined_inputs_set by force

lemma defined_inputs_alt_def : "defined_inputs M q = {t_input t | t . t \<in> transitions M \<and> t_source t = q}"
  unfolding defined_inputs_code by force

lemma defined_inputs_language_diff :
  assumes "x \<in> defined_inputs M1 q1"
      and "x \<notin> defined_inputs M2 q2"
    obtains y where "[(x,y)] \<in> LS M1 q1 - LS M2 q2"
  using assms unfolding defined_inputs_alt_def
proof -
  assume a1: "x \<notin> {t_input t |t. t \<in> FSM.transitions M2 \<and> t_source t = q2}"
  assume a2: "x \<in> {t_input t |t. t \<in> FSM.transitions M1 \<and> t_source t = q1}"
  assume a3: "\<And>y. [(x, y)] \<in> LS M1 q1 - LS M2 q2 \<Longrightarrow> thesis"
  have f4: "\<nexists>p. x = t_input p \<and> p \<in> FSM.transitions M2 \<and> t_source p = q2"
    using a1 by blast
  obtain pp :: "'a \<Rightarrow> 'b \<times> 'a \<times> 'c \<times> 'b" where
    "\<forall>a. ((\<nexists>p. a = t_input p \<and> p \<in> FSM.transitions M1 \<and> t_source p = q1) \<or> a = t_input (pp a) \<and> pp a \<in> FSM.transitions M1 \<and> t_source (pp a) = q1) \<and> ((\<exists>p. a = t_input p \<and> p \<in> FSM.transitions M1 \<and> t_source p = q1) \<or> (\<forall>p. a \<noteq> t_input p \<or> p \<notin> FSM.transitions M1 \<or> t_source p \<noteq> q1))"
    by moura
  then have "x = t_input (pp x) \<and> pp x \<in> FSM.transitions M1 \<and> t_source (pp x) = q1"
    using a2 by blast
  then show ?thesis
    using f4 a3 by (metis (no_types) DiffI LS_single_transition)
qed 

lemma language_path_append :
  assumes "path M1 q1 p1"
  and     "io \<in> LS M1 (target q1 p1)"
shows "(p_io p1 @ io) \<in> LS M1 q1" 
proof -
  obtain p2 where "path M1 (target q1 p1) p2" and "p_io p2 = io"
    using assms(2) by auto
  then have "path M1 q1 (p1@p2)" 
    using assms(1) by auto
  moreover have "p_io (p1@p2) = (p_io p1 @ io)"
    using \<open>p_io p2 = io\<close> by auto
  ultimately show ?thesis
    by (metis (mono_tags, lifting) language_intro)
qed

lemma observable_defined_inputs_diff_ob :
  assumes "observable M1"
  and     "observable M2"
  and     "path M1 q1 p1"
  and     "path M2 q2 p2"
  and     "p_io p1 = p_io p2"
  and     "x \<in> defined_inputs M1 (target q1 p1)" 
  and     "x \<notin> defined_inputs M2 (target q2 p2)"
obtains y where "(p_io p1)@[(x,y)] \<in> LS M1 q1 - LS M2 q2"
proof -
  obtain y where "[(x,y)] \<in> LS M1 (target q1 p1) - LS M2 (target q2 p2)"
    using defined_inputs_language_diff[OF assms(6,7)] by blast
  then have "(p_io p1)@[(x,y)] \<in> LS M1 q1"
    using language_path_append[OF assms(3)]
    by blast
  moreover have "(p_io p1)@[(x,y)] \<notin> LS M2 q2"
    by (metis (mono_tags, lifting) DiffD2 \<open>[(x, y)] \<in> LS M1 (target q1 p1) - LS M2 (target q2 p2)\<close> assms(2) assms(4) assms(5) language_state_containment observable_path_suffix)
  ultimately show ?thesis 
    using that[of y] by blast
qed


lemma observable_defined_inputs_diff_language :
  assumes "observable M1"
  and     "observable M2"
  and     "path M1 q1 p1"
  and     "path M2 q2 p2"
  and     "p_io p1 = p_io p2"
  and     "defined_inputs M1 (target q1 p1) \<noteq> defined_inputs M2 (target q2 p2)"
shows "LS M1 q1 \<noteq> LS M2 q2"
proof -
  obtain x where "(x \<in> defined_inputs M1 (target q1 p1) - defined_inputs M2 (target q2 p2))
                  \<or> (x \<in> defined_inputs M2 (target q2 p2) - defined_inputs M1 (target q1 p1))"
    using assms by blast
  then consider "(x \<in> defined_inputs M1 (target q1 p1) - defined_inputs M2 (target q2 p2))" |
                "(x \<in> defined_inputs M2 (target q2 p2) - defined_inputs M1 (target q1 p1))" 
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis 
      using observable_defined_inputs_diff_ob[OF assms(1-5), of x] by blast
  next
    case 2
    then show ?thesis 
      using observable_defined_inputs_diff_ob[OF assms(2,1,4,3) assms(5)[symmetric], of x] by blast
  qed
qed

fun maximal_prefix_in_language :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times>'c) list \<Rightarrow> ('b \<times>'c) list" where
  "maximal_prefix_in_language M q [] = []" |
  "maximal_prefix_in_language M q ((x,y)#io) = (case h_obs M q x y of
    None \<Rightarrow> [] |
    Some q' \<Rightarrow> (x,y)#maximal_prefix_in_language M q' io)"

lemma maximal_prefix_in_language_properties :
  assumes "observable M"
  and     "q \<in> states M"
shows "maximal_prefix_in_language M q io \<in> LS M q"
and   "maximal_prefix_in_language M q io \<in> list.set (prefixes io)"
proof -
  have "maximal_prefix_in_language M q io \<in> LS M q \<and> maximal_prefix_in_language M q io \<in> list.set (prefixes io)"
    using assms(2) proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)

    obtain x y where "xy = (x,y)"
      using prod.exhaust by metis

    show ?case proof (cases "h_obs M q x y")
      case None
      then have "maximal_prefix_in_language M q (xy#io) = []"
        unfolding \<open>xy = (x,y)\<close>
        by auto
      then show ?thesis
        by (metis (mono_tags, lifting) Cons.prems append_self_conv2 from_FSM_language language_contains_empty_sequence mem_Collect_eq prefixes_set) 
    next
      case (Some q')
      then have *: "maximal_prefix_in_language M q (xy#io) = (x,y)#maximal_prefix_in_language M q' io"
        unfolding \<open>xy = (x,y)\<close>
        by auto

      have "q' \<in> states M"
        using h_obs_state[OF Some] by auto
      then have "maximal_prefix_in_language M q' io \<in> LS M q'" 
            and "maximal_prefix_in_language M q' io \<in> list.set (prefixes io)"
        using Cons.IH by auto

      have "maximal_prefix_in_language M q (xy # io) \<in> LS M q"
        unfolding *
        using Some \<open>maximal_prefix_in_language M q' io \<in> LS M q'\<close>
        by (meson assms(1) h_obs_language_iff)
      moreover have "maximal_prefix_in_language M q (xy # io) \<in> list.set (prefixes (xy # io))"
        unfolding * 
        unfolding \<open>xy = (x,y)\<close>
        using \<open>maximal_prefix_in_language M q' io \<in> list.set (prefixes io)\<close> append_Cons
        unfolding prefixes_set
        by auto 
      ultimately show ?thesis
        by blast
    qed
  qed
  then show "maximal_prefix_in_language M q io \<in> LS M q"
       and  "maximal_prefix_in_language M q io \<in> list.set (prefixes io)"
    by auto
qed


subsection \<open>Further Reachability Formalisations\<close>

(* states that are reachable in at most k transitions *)
fun reachable_k :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target q p | p . path M q p \<and> length p \<le> n}" 


lemma reachable_k_0_initial : "reachable_k M (initial M) 0 = {initial M}" 
  by auto

lemma reachable_k_states : "reachable_states M = reachable_k M (initial M) ( size M - 1)"
proof -
  have "\<And>q. q \<in> reachable_states M \<Longrightarrow> q \<in> reachable_k M (initial M) ( size M - 1)"
  proof -
    fix q assume "q \<in> reachable_states M"
    then obtain p where "path M (initial M) p" and "target (initial M) p = q"
      unfolding reachable_states_def by blast
    then obtain p' where "path M (initial M) p'"
                     and "target (initial M) p' = target (initial M) p" 
                     and "length p' < size M"
      by (metis acyclic_path_from_cyclic_path acyclic_path_length_limit)
    then show "q \<in> reachable_k M (initial M) ( size M - 1)"
      using \<open>target (FSM.initial M) p = q\<close> less_trans by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( size M - 1) \<Longrightarrow> x \<in> reachable_states M"
    unfolding reachable_states_def reachable_k.simps by blast
  
  ultimately show ?thesis by blast
qed


  
subsubsection \<open>Induction Schemes\<close>


  
lemma acyclic_induction [consumes 1, case_names reachable_state]:
  assumes "acyclic M"
      and "\<And> q . q \<in> reachable_states M \<Longrightarrow> (\<And> t . t \<in> transitions M \<Longrightarrow> ((t_source t = q) \<Longrightarrow> P (t_target t))) \<Longrightarrow> P q"
    shows "\<forall> q \<in> reachable_states M . P q"
proof 
  fix q assume "q \<in> reachable_states M"

  let ?k = "Max (image length {p . path M q p})"
  have "finite {p . path M q p}" using acyclic_finite_paths_from_reachable_state[OF assms(1)] 
    using \<open>q \<in> reachable_states M\<close> unfolding reachable_states_def by force
  then have k_prop: "(\<forall> p . path M q p \<longrightarrow> length p \<le> ?k)" by auto

  moreover have "\<And> q k . q \<in> reachable_states M \<Longrightarrow> (\<forall> p . path M q p \<longrightarrow> length p \<le> k) \<Longrightarrow> P q"
  proof -
    fix q k assume "q \<in> reachable_states M" and "(\<forall> p . path M q p \<longrightarrow> length p \<le> k)"
    then show "P q" 
    proof (induction k arbitrary: q)
      case 0
      then have "{p . path M q p} = {[]}" using reachable_state_is_state[OF \<open>q \<in> reachable_states M\<close>]
        by blast  
      then have "LS M q \<subseteq> {[]}" unfolding LS.simps by blast
      then have "deadlock_state M q" using deadlock_state_alt_def by metis
      then show ?case using assms(2)[OF \<open>q \<in> reachable_states M\<close>] unfolding deadlock_state.simps by blast
    next
      case (Suc k)
      have "\<And> t . t \<in> transitions M \<Longrightarrow> (t_source t = q) \<Longrightarrow> P (t_target t)"
      proof -
        fix t assume "t \<in> transitions M" and "t_source t = q" 
        then have "t_target t \<in> reachable_states M"
          using \<open>q \<in> reachable_states M\<close> using reachable_states_next by metis
        moreover have "\<forall>p. path M (t_target t) p \<longrightarrow> length p \<le> k"
          using Suc.prems(2) \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close> by auto
        ultimately show "P (t_target t)" 
          using Suc.IH unfolding reachable_states_def by blast 
      qed
      then show ?case using assms(2)[OF Suc.prems(1)] by blast
    qed
  qed

  ultimately show "P q" using \<open>q \<in> reachable_states M\<close> by blast
qed

lemma reachable_states_induct [consumes 1, case_names init transition] :
  assumes "q \<in> reachable_states M" 
  and "P (initial M)"
  and     "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t \<in> reachable_states M \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)"
shows "P q"
proof -
  from assms(1) obtain p where "path M (initial M) p" and "target (initial M) p = q"
    unfolding reachable_states_def by auto
  then show "P q"
  proof (induction p arbitrary: q rule: rev_induct)
    case Nil
    then show ?case using assms(2) by auto
  next
    case (snoc t p)

    then have "target (initial M) p = t_source t"
      by auto
    then have "P (t_source t)"
      using snoc.IH snoc.prems by auto
    moreover have "t \<in> transitions M"
      using snoc.prems by auto
    moreover have "t_source t \<in> reachable_states M"
      by (metis \<open>target (FSM.initial M) p = t_source t\<close> path_prefix reachable_states_intro snoc.prems(1))
    moreover have "t_target t = q"
      using snoc.prems by auto
    ultimately show ?case
      using assms(3) by blast
  qed
qed

lemma reachable_states_cases [consumes 1, case_names init transition] : 
  assumes "q \<in> reachable_states M"
  and     "P (initial M)"
  and     "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t \<in> reachable_states M \<Longrightarrow> P (t_target t)"
shows "P q"
  by (metis assms(1) assms(2) assms(3) reachable_states_induct)


subsection \<open>Further Path Enumeration Algorithms\<close>

fun paths_for_input' :: "('a \<Rightarrow> ('b \<times> 'c \<times> 'a) set) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_input' f [] q prev = {prev}" |
  "paths_for_input' f (x#xs) q prev = \<Union>(image (\<lambda>(x',y',q') . paths_for_input' f xs q' (prev@[(q,x,y',q')])) (Set.filter (\<lambda>(x',y',q') . x' = x) (f q)))"

lemma paths_for_input'_set :
  assumes "q \<in> states M"
  shows   "paths_for_input' (h_from M) xs q prev = {prev@p | p . path M q p \<and> map fst (p_io p) = xs}"
using assms proof (induction xs arbitrary: q prev)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  let ?UN = "\<Union>(image (\<lambda>(x',y',q') . paths_for_input' (h_from M) xs q' (prev@[(q,x,y',q')])) (Set.filter (\<lambda>(x',y',q') . x' = x) (h_from M q)))"

  have "?UN = {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}"
  proof 
    have "\<And> p . p \<in> ?UN \<Longrightarrow> p \<in> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}"
    proof -
      fix p assume "p \<in> ?UN"
      then obtain y' q' where "(x,y',q') \<in> (Set.filter (\<lambda>(x',y',q') . x' = x) (h_from M q))"
                     and   "p \<in> paths_for_input' (h_from M) xs q' (prev@[(q,x,y',q')])"
        by auto
      
      from \<open>(x,y',q') \<in> (Set.filter (\<lambda>(x',y',q') . x' = x) (h_from M q))\<close> have "q' \<in> states M" and "(q,x,y',q') \<in> transitions M"
        using fsm_transition_target unfolding h.simps by auto

      have "p \<in> {(prev @ [(q, x, y', q')]) @ p |p. path M q' p \<and> map fst (p_io p) = xs}"
        using \<open>p \<in> paths_for_input' (h_from M) xs q' (prev@[(q,x,y',q')])\<close>
        unfolding Cons.IH[OF \<open>q' \<in> states M\<close>] by assumption
      moreover have "{(prev @ [(q, x, y', q')]) @ p |p. path M q' p \<and> map fst (p_io p) = xs} 
                      \<subseteq> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}"
        using \<open>(q,x,y',q') \<in> transitions M\<close>
        using cons by force 
      ultimately show "p \<in> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}" 
        by blast
    qed
    then show "?UN \<subseteq> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}"
      by blast

    have "\<And> p . p \<in> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs} \<Longrightarrow> p \<in> ?UN"
    proof -
      fix pp assume "pp \<in> {prev@p | p . path M q p \<and> map fst (p_io p) = x#xs}"
      then obtain p where "pp = prev@p" and "path M q p" and "map fst (p_io p) = x#xs"
        by fastforce
      then obtain t p' where "p = t#p'" and "path M q (t#p')" and "map fst (p_io (t#p')) = x#xs" and "map fst (p_io p') = xs"
        by (metis (no_types, lifting) map_eq_Cons_D)
      then have "path M (t_target t) p'" and "t_source t = q" and "t_input t = x" and "t_target t \<in> states M" and "t \<in> transitions M"
        by auto

      have "(x,t_output t,t_target t) \<in> (Set.filter (\<lambda>(x',y',q') . x' = x) (h_from M q))"
        using \<open>t \<in> transitions M\<close> \<open>t_input t = x\<close> \<open>t_source t = q\<close>
        unfolding h.simps by auto 
      moreover have "(prev@p) \<in> paths_for_input' (h_from M) xs (t_target t) (prev@[(q,x,t_output t,t_target t)])"
        using Cons.IH[OF \<open>t_target t \<in> states M\<close>, of "prev@[(q, x, t_output t, t_target t)]"]
        using \<open>\<And>thesis. (\<And>t p'. \<lbrakk>p = t # p'; path M q (t # p'); map fst (p_io (t # p')) = x # xs; map fst (p_io p') = xs\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
              \<open>p = t # p'\<close> 
              \<open>paths_for_input' (h_from M) xs (t_target t) (prev @ [(q, x, t_output t, t_target t)]) 
                = {(prev @ [(q, x, t_output t, t_target t)]) @ p |p. path M (t_target t) p \<and> map fst (p_io p) = xs}\<close> 
              \<open>t_input t = x\<close> 
              \<open>t_source t = q\<close> 
        by fastforce

      ultimately show "pp \<in> ?UN" unfolding \<open>pp = prev@p\<close>
        by blast 
    qed
    then show "{prev@p | p . path M q p \<and> map fst (p_io p) = x#xs} \<subseteq> ?UN"
      by (meson subsetI) 
  qed

  then show ?case
    by (metis paths_for_input'.simps(2)) 
    
qed


definition paths_for_input :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_input M q xs = {p . path M q p \<and> map fst (p_io p) = xs}"

lemma paths_for_input_set_code[code] :
  "paths_for_input M q xs = (if q \<in> states M then paths_for_input' (h_from M) xs q [] else {})"
  using paths_for_input'_set[of q M xs "[]"] 
  unfolding paths_for_input_def
  by (cases "q \<in> states M"; auto; simp add: path_begin_state)


fun paths_up_to_length_or_condition_with_witness' :: 
    "('a \<Rightarrow> ('b \<times> 'c \<times> 'a) set) \<Rightarrow> (('a,'b,'c) path \<Rightarrow> 'd option) \<Rightarrow> ('a,'b,'c) path \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (('a,'b,'c) path \<times> 'd) set" 
  where
  "paths_up_to_length_or_condition_with_witness' f P prev 0 q = (case P prev of Some w \<Rightarrow> {(prev,w)} | None \<Rightarrow> {})" |
  "paths_up_to_length_or_condition_with_witness' f P prev (Suc k) q = (case P prev of 
    Some w \<Rightarrow> {(prev,w)} | 
    None \<Rightarrow> (\<Union>(image (\<lambda>(x,y,q') . paths_up_to_length_or_condition_with_witness' f P (prev@[(q,x,y,q')]) k q') (f q))))"



lemma paths_up_to_length_or_condition_with_witness'_set :
  assumes "q \<in> states M"
  shows   "paths_up_to_length_or_condition_with_witness' (h_from M) P prev k q 
            = {(prev@p,x) | p x . path M q p 
                                  \<and> length p \<le> k 
                                  \<and> P (prev@p) = Some x 
                                  \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> P (prev@p') = None)}"
using assms proof (induction k arbitrary: q prev)
  case 0
  then show ?case proof (cases "P prev")
    case None then show ?thesis by auto
  next
    case (Some w) 
    then show ?thesis by (simp add: "0.prems" nil)
  qed
next
  case (Suc k) 
  then show ?case proof (cases "P prev")
    case (Some w) 
    then have "(prev,w) \<in> {(prev@p,x) | p x . path M q p 
                                              \<and> length p \<le> Suc k 
                                              \<and> P (prev@p) = Some x 
                                              \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> P (prev@p') = None)}"
      by (simp add: Suc.prems nil) 
    then have "{(prev@p,x) | p x . path M q p 
                                    \<and> length p \<le> Suc k 
                                    \<and> P (prev@p) = Some x 
                                    \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> P (prev@p') = None)} 
              = {(prev,w)}"
      using Some by fastforce
      
    then show ?thesis using Some by auto
  next
    case None 

    have "(\<Union>(image (\<lambda>(x,y,q') . paths_up_to_length_or_condition_with_witness' (h_from M) P (prev@[(q,x,y,q')]) k q') (h_from M q))) 
            = {(prev@p,x) | p x . path M q p 
                                  \<and> length p \<le> Suc k 
                                  \<and> P (prev@p) = Some x 
                                  \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> P (prev@p') = None)}"
         (is "?UN = ?PX")
    proof -
      have *: "\<And> pp . pp \<in> ?UN \<Longrightarrow> pp \<in> ?PX"
      proof -
        fix pp assume "pp \<in> ?UN"
        then obtain x y q' where "(x,y,q') \<in> h_from M q"
                           and   "pp \<in> paths_up_to_length_or_condition_with_witness' (h_from M) P (prev@[(q,x,y,q')]) k q'"
          by blast
        then have "(q,x,y,q') \<in> transitions M" by auto
        then have "q' \<in> states M" using fsm_transition_target by auto
        
        obtain p w where "pp = ((prev@[(q,x,y,q')])@p,w)" 
                   and   "path M q' p"
                   and   "length p \<le> k"
                   and   "P ((prev @ [(q, x, y, q')]) @ p) = Some w"
                   and   "\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P ((prev @ [(q, x, y, q')]) @ p') = None"
          using \<open>pp \<in> paths_up_to_length_or_condition_with_witness' (h_from M) P (prev@[(q,x,y,q')]) k q'\<close> 
          unfolding Suc.IH[OF \<open>q' \<in> states M\<close>, of "prev@[(q,x,y,q')]"] 
          by blast
        
        have "path M q ((q,x,y,q')#p)" 
          using \<open>path M q' p\<close> \<open>(q,x,y,q') \<in> transitions M\<close> by (simp add: path_prepend_t) 
        moreover have "length ((q,x,y,q')#p) \<le> Suc k" 
          using \<open>length p \<le> k\<close> by auto
        moreover have "P (prev @ ([(q, x, y, q')] @ p)) = Some w" 
          using \<open>P ((prev @ [(q, x, y, q')]) @ p) = Some w\<close> by auto
        moreover have "\<And> p' p''. ((q,x,y,q')#p) = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P (prev @ p') = None" 
          using \<open>\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P ((prev @ [(q, x, y, q')]) @ p') = None\<close>
          using None 
          by (metis (no_types, opaque_lifting) append.simps(1) append_Cons append_Nil2 append_assoc 
                list.inject neq_Nil_conv) 

        ultimately show "pp \<in> ?PX" 
          unfolding \<open>pp = ((prev@[(q,x,y,q')])@p,w)\<close> by auto  
      qed
      
      have **: "\<And> pp . pp \<in> ?PX \<Longrightarrow> pp \<in> ?UN"
      proof -
        fix pp assume "pp \<in> ?PX"
        then obtain p' w where "pp = (prev @ p', w)"
                        and   "path M q p'"
                        and   "length p' \<le> Suc k"
                        and   "P (prev @ p') = Some w"
                        and   "\<And> p' p''. p' = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P (prev @ p') = None"
          by blast
        moreover obtain t p where "p' = t#p" using \<open>P (prev @ p') = Some w\<close> using None
          by (metis append_Nil2 list.exhaust option.distinct(1)) 
        
        
        have "pp = ((prev @ [t])@p, w)" 
          using \<open>pp = (prev @ p', w)\<close> unfolding \<open>p' = t#p\<close> by auto
        have "path M q (t#p)" 
          using \<open>path M q p'\<close> unfolding \<open>p' = t#p\<close> by auto
        have p2: "length (t#p) \<le> Suc k" 
          using \<open>length p' \<le> Suc k\<close> unfolding \<open>p' = t#p\<close> by auto
        have p3: "P ((prev @ [t])@p) = Some w" 
          using \<open>P (prev @ p') = Some w\<close> unfolding \<open>p' = t#p\<close> by auto
        have p4: "\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P ((prev@[t]) @ p') = None"
          using \<open>\<And> p' p''. p' = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> P (prev @ p') = None\<close> \<open>pp \<in> ?PX\<close> 
          unfolding \<open>pp = ((prev @ [t]) @ p, w)\<close> \<open>p' = t#p\<close> 
          by auto

        have "t \<in> transitions M" and p1: "path M (t_target t) p" and "t_source t = q"
          using \<open>path M q (t#p)\<close> by auto
        then have "t_target t \<in> states M" 
              and "(t_input t, t_output t, t_target t) \<in> h_from M q" 
              and "t_source t = q"
          using fsm_transition_target by auto
        then have "t = (q,t_input t, t_output t, t_target t)"
          by auto

        have "((prev @ [t])@p, w) \<in> paths_up_to_length_or_condition_with_witness' (h_from M) P (prev@[t]) k (t_target t)"
          unfolding Suc.IH[OF \<open>t_target t \<in> states M\<close>, of "prev@[t]"]
          using p1 p2 p3 p4 by auto
          

        then show "pp \<in> ?UN"
          unfolding \<open>pp = ((prev @ [t])@p, w)\<close>  
        proof -
          have "paths_up_to_length_or_condition_with_witness' (h_from M) P (prev @ [t]) k (t_target t) 
                = paths_up_to_length_or_condition_with_witness' (h_from M) P (prev @ [(q, t_input t, t_output t, t_target t)]) k (t_target t)"
            using \<open>t = (q, t_input t, t_output t, t_target t)\<close> by presburger
          then show "((prev @ [t]) @ p, w) \<in> (\<Union>(b, c, a)\<in>h_from M q. paths_up_to_length_or_condition_with_witness' (h_from M) P (prev @ [(q, b, c, a)]) k a)"
            using \<open>((prev @ [t]) @ p, w) \<in> paths_up_to_length_or_condition_with_witness' (h_from M) P (prev @ [t]) k (t_target t)\<close> 
                  \<open>(t_input t, t_output t, t_target t) \<in> h_from M q\<close> 
            by blast
        qed
      qed

      show ?thesis
        using subsetI[of ?UN ?PX, OF *] subsetI[of ?PX ?UN, OF **] subset_antisym by blast
    qed

    then show ?thesis 
      using None unfolding paths_up_to_length_or_condition_with_witness'.simps by simp
  qed
qed


definition paths_up_to_length_or_condition_with_witness :: 
  "('a,'b,'c) fsm \<Rightarrow> (('a,'b,'c) path \<Rightarrow> 'd option) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (('a,'b,'c) path \<times> 'd) set" 
  where
  "paths_up_to_length_or_condition_with_witness M P k q 
    = {(p,x) | p x . path M q p 
                      \<and> length p \<le> k 
                      \<and> P p = Some x 
                      \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> P p' = None)}"


lemma paths_up_to_length_or_condition_with_witness_code[code] :
  "paths_up_to_length_or_condition_with_witness M P k q 
    = (if q \<in> states M then paths_up_to_length_or_condition_with_witness' (h_from M) P [] k q
                      else {})" 
proof (cases "q \<in> states M")
  case True
  then show ?thesis 
    unfolding paths_up_to_length_or_condition_with_witness_def 
              paths_up_to_length_or_condition_with_witness'_set[OF True] 
    by auto
next
  case False
  then show ?thesis 
    unfolding paths_up_to_length_or_condition_with_witness_def
    using path_begin_state by fastforce 
qed


lemma paths_up_to_length_or_condition_with_witness_finite : 
  "finite (paths_up_to_length_or_condition_with_witness M P k q)"
proof -
  have "paths_up_to_length_or_condition_with_witness M P k q 
          \<subseteq> {(p, the (P p)) | p . path M q p \<and> length p \<le> k}"
    unfolding paths_up_to_length_or_condition_with_witness_def
    by auto 
  moreover have "finite {(p, the (P p)) | p . path M q p \<and> length p \<le> k}" 
    using paths_finite[of M q k]
    by simp 
  ultimately show ?thesis
    using rev_finite_subset by auto 
qed

  


subsection \<open>More Acyclicity Properties\<close>


lemma maximal_path_target_deadlock :
  assumes "path M (initial M) p"
  and     "\<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')"
shows "deadlock_state M (target (initial M) p)"
proof -
  have "\<not>(\<exists> t \<in> transitions M . t_source t = target (initial M) p)"
    using assms(2) unfolding is_prefix_prefix
    by (metis append_Nil2 assms(1) not_Cons_self2 path_append_transition same_append_eq)
  then show ?thesis by auto
qed

lemma path_to_deadlock_is_maximal :
  assumes "path M (initial M) p"
  and     "deadlock_state M (target (initial M) p)"
shows "\<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')"
proof 
  assume "\<exists>p'. path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p'"
  then obtain p' where "path M (initial M) p'" and "is_prefix p p'" and "p \<noteq> p'" by blast
  then have "length p' > length p"
    unfolding is_prefix_prefix by auto
  then obtain t p2 where "p' = p @ [t] @ p2"
    using \<open>is_prefix p p'\<close> unfolding is_prefix_prefix
    by (metis \<open>p \<noteq> p'\<close> append.left_neutral append_Cons append_Nil2 non_sym_dist_pairs'.cases) 
  then have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p'\<close> by auto
  then have "t \<in> transitions M" and "t_source t = target (initial M) p"
    by auto
  then show "False"
    using \<open>deadlock_state M (target (initial M) p)\<close> unfolding deadlock_state.simps by blast
qed



definition maximal_acyclic_paths :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) path set" where
  "maximal_acyclic_paths M = {p . path M (initial M) p 
                                  \<and> distinct (visited_states (initial M) p) 
                                  \<and> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p') 
                                              \<and> distinct (visited_states (initial M) (p@p')))}"


(* very inefficient construction *)
lemma maximal_acyclic_paths_code[code] :  
  "maximal_acyclic_paths M = (let ps = acyclic_paths_up_to_length M (initial M) (size M - 1)
                               in Set.filter (\<lambda>p . \<not> (\<exists> p' \<in> ps . p' \<noteq> p \<and> is_prefix p p')) ps)"
proof -
  have scheme1: "\<And> P p . (\<exists> p' . p' \<noteq> [] \<and> P (p@p')) = (\<exists> p' \<in> {p . P p} . p' \<noteq> p \<and> is_prefix p p')"
    unfolding is_prefix_prefix by blast

  have scheme2: "\<And> p . (path M (FSM.initial M) p 
                          \<and> length p \<le> FSM.size M - 1 
                          \<and> distinct (visited_states (FSM.initial M) p)) 
                      = (path M (FSM.initial M) p \<and> distinct (visited_states (FSM.initial M) p))"
    using acyclic_path_length_limit by fastforce 

  show ?thesis
    unfolding maximal_acyclic_paths_def acyclic_paths_up_to_length.simps Let_def 
    unfolding scheme1[of "\<lambda>p . path M (initial M) p \<and> distinct (visited_states (initial M) p)"]
    unfolding scheme2 by fastforce
qed



lemma maximal_acyclic_path_deadlock :
  assumes "acyclic M"
  and     "path M (initial M) p"
shows "\<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p') \<and> distinct (visited_states (initial M) (p@p'))) 
        = deadlock_state M (target (initial M) p)"
proof -
  have "deadlock_state M (target (initial M) p) \<Longrightarrow> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p') 
          \<and> distinct (visited_states (initial M) (p@p')))"
    unfolding deadlock_state.simps 
    using assms(2) by (metis path.cases path_suffix) 
  then show ?thesis
    by (metis acyclic.elims(2) assms(1) assms(2) is_prefix_prefix maximal_path_target_deadlock 
          self_append_conv) 
qed
  

lemma maximal_acyclic_paths_deadlock_targets : 
  assumes "acyclic M"
  shows "maximal_acyclic_paths M 
          = { p . path M (initial M) p \<and> deadlock_state M (target (initial M) p)}"
  using maximal_acyclic_path_deadlock[OF assms] 
  unfolding maximal_acyclic_paths_def
  by (metis (no_types, lifting) acyclic.elims(2) assms)


lemma cycle_from_cyclic_path :
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
obtains i j where
  "take j (drop i p) \<noteq> []"
  "target (target q (take i p)) (take j (drop i p)) = (target q (take i p))"
  "path M (target q (take i p)) (take j (drop i p))"
proof -
  obtain i j where "i < j" and "j < length (visited_states q p)" 
               and "(visited_states q p) ! i = (visited_states q p) ! j"
    using assms(2) non_distinct_repetition_indices by blast 

  have "(target q (take i p)) = (visited_states q p) ! i"
    using \<open>i < j\<close> \<open>j < length (visited_states q p)\<close>
    by (metis less_trans take_last_index target.simps visited_states_take)

  then have "(target q (take i p)) = (visited_states q p) ! j"
    using \<open>(visited_states q p) ! i = (visited_states q p) ! j\<close> by auto

  have p1: "take (j-i) (drop i p) \<noteq> []"
    using \<open>i < j\<close> \<open>j < length (visited_states q p)\<close> by auto 

  have "target (target q (take i p)) (take (j-i) (drop i p)) = (target q (take j p))"
    using \<open>i < j\<close> by (metis add_diff_inverse_nat less_asym' path_append_target take_add)
  then have p2: "target (target q (take i p)) (take (j-i) (drop i p)) = (target q (take i p))"
    using \<open>(target q (take i p)) = (visited_states q p) ! i\<close>
    using \<open>(target q (take i p)) = (visited_states q p) ! j\<close>
    by (metis \<open>j < length (visited_states q p)\<close> take_last_index target.simps visited_states_take)

  have p3: "path M (target q (take i p)) (take (j-i) (drop i p))"
    by (metis append_take_drop_id assms(1) path_append_elim)

  show ?thesis using p1 p2 p3 that by blast
qed



lemma acyclic_single_deadlock_reachable :
  assumes "acyclic M"
  and     "\<And> q' . q' \<in> reachable_states M \<Longrightarrow> q' = qd \<or> \<not> deadlock_state M q'"
shows "qd \<in> reachable_states M"
  using acyclic_deadlock_reachable[OF assms(1)]
  using assms(2) by auto 


lemma acyclic_paths_to_single_deadlock :
  assumes "acyclic M"
  and     "\<And> q' . q' \<in> reachable_states M \<Longrightarrow> q' = qd \<or> \<not> deadlock_state M q'"
  and     "q \<in> reachable_states M"
obtains p where "path M q p" and "target q p = qd"
proof -
  have "q \<in> states M" using assms(3) reachable_state_is_state by metis
  have "acyclic (from_FSM M q)"
    using from_FSM_acyclic[OF assms(3,1)] by assumption

  have *: "(\<And>q'. q' \<in> reachable_states (FSM.from_FSM M q) 
                \<Longrightarrow> q' = qd \<or> \<not> deadlock_state (FSM.from_FSM M q) q')"
    using assms(2) from_FSM_reachable_states[OF assms(3)] 
    unfolding deadlock_state.simps from_FSM_simps[OF \<open>q \<in> states M\<close>] by blast

  obtain p where "path (from_FSM M q) q p" and "target q p = qd"
    using acyclic_single_deadlock_reachable[OF \<open>acyclic (from_FSM M q)\<close> *]
    unfolding reachable_states_def from_FSM_simps[OF \<open>q \<in> states M\<close>]
    by blast 

  then show ?thesis
    using that by (metis \<open>q \<in> FSM.states M\<close> from_FSM_path) 
qed



subsection \<open>Elements as Lists\<close>

fun states_as_list :: "('a :: linorder, 'b, 'c) fsm \<Rightarrow> 'a list" where
  "states_as_list M = sorted_list_of_set (states M)"

lemma states_as_list_distinct : "distinct (states_as_list M)" by auto

lemma states_as_list_set : "set (states_as_list M) = states M"
  by (simp add: fsm_states_finite)


fun reachable_states_as_list :: "('a :: linorder, 'b, 'c) fsm \<Rightarrow> 'a list" where
  "reachable_states_as_list M = sorted_list_of_set (reachable_states M)"

lemma reachable_states_as_list_distinct : "distinct (reachable_states_as_list M)" by auto

lemma reachable_states_as_list_set : "set (reachable_states_as_list M) = reachable_states M"
  by (metis fsm_states_finite infinite_super reachable_state_is_state reachable_states_as_list.simps 
        set_sorted_list_of_set subsetI)  


fun inputs_as_list :: "('a, 'b :: linorder, 'c) fsm \<Rightarrow> 'b list" where
  "inputs_as_list M = sorted_list_of_set (inputs M)"

lemma inputs_as_list_set : "set (inputs_as_list M) = inputs M"
  by (simp add: fsm_inputs_finite)

lemma inputs_as_list_distinct : "distinct (inputs_as_list M)" by auto

fun transitions_as_list :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a,'b,'c) transition list" where
  "transitions_as_list M = sorted_list_of_set (transitions M)"

lemma transitions_as_list_set : "set (transitions_as_list M) = transitions M"
  by (simp add: fsm_transitions_finite)

fun outputs_as_list :: "('a,'b,'c :: linorder) fsm \<Rightarrow> 'c list" where
  "outputs_as_list M = sorted_list_of_set (outputs M)"

lemma outputs_as_list_set : "set (outputs_as_list M) = outputs M"
  by (simp add: fsm_outputs_finite)

fun ftransitions :: "('a :: linorder,'b :: linorder,'c :: linorder) fsm \<Rightarrow> ('a,'b,'c) transition fset" where
  "ftransitions M = fset_of_list (transitions_as_list M)"

fun fstates :: "('a :: linorder,'b,'c) fsm \<Rightarrow> 'a fset" where
  "fstates M = fset_of_list (states_as_list M)"

fun finputs :: "('a,'b :: linorder,'c) fsm \<Rightarrow> 'b fset" where
  "finputs M = fset_of_list (inputs_as_list M)"

fun foutputs :: "('a,'b,'c :: linorder) fsm \<Rightarrow> 'c fset" where
  "foutputs M = fset_of_list (outputs_as_list M)"

lemma fstates_set : "fset (fstates M) = states M" 
  using fsm_states_finite[of M] by (simp add: fset_of_list.rep_eq) 

lemma finputs_set : "fset (finputs M) = inputs M" 
  using fsm_inputs_finite[of M] by (simp add: fset_of_list.rep_eq) 

lemma foutputs_set : "fset (foutputs M) = outputs M" 
  using fsm_outputs_finite[of M] by (simp add: fset_of_list.rep_eq) 

lemma ftransitions_set: "fset (ftransitions M) = transitions M"
  by (metis (no_types) fset_of_list.rep_eq ftransitions.simps transitions_as_list_set)

lemma ftransitions_source:
  "q |\<in>| (t_source |`| ftransitions M) \<Longrightarrow> q \<in> states M" 
  using ftransitions_set[of M] fsm_transition_source[of _ M]
  by (metis (no_types, opaque_lifting) fimageE)

lemma ftransitions_target:
  "q |\<in>| (t_target |`| ftransitions M) \<Longrightarrow> q \<in> states M" 
  using ftransitions_set[of M] fsm_transition_target[of _ M]
  by (metis (no_types, lifting) fimageE)


subsection \<open>Responses to Input Sequences\<close>

fun language_for_input :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> ('b\<times>'c) list list" where
  "language_for_input M q [] = [[]]" |
  "language_for_input M q (x#xs) = 
      (let outs = outputs_as_list M
        in concat (map (\<lambda>y . case h_obs M q x y of None \<Rightarrow> [] | Some q' \<Rightarrow> map ((#) (x,y)) (language_for_input M q' xs)) outs))"  

lemma language_for_input_set :
  assumes "observable M"
  and     "q \<in> states M"
shows "list.set (language_for_input M q xs) = {io . io \<in> LS M q \<and> map fst io = xs}"
  using assms(2) proof (induction xs arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  have "list.set (language_for_input M q (x#xs)) \<subseteq> {io . io \<in> LS M q \<and> map fst io = (x#xs)}"
  proof 
    fix io assume "io \<in> list.set (language_for_input M q (x#xs))"
    then obtain y where "y \<in> outputs M"
                    and "io \<in> list.set (case h_obs M q x y of None \<Rightarrow> [] | Some q' \<Rightarrow> map ((#) (x,y)) (language_for_input M q' xs))"
      unfolding outputs_as_list_set[symmetric]
      by auto
    then obtain q' where "h_obs M q x y = Some q'" and "io \<in> list.set (map ((#) (x,y)) (language_for_input M q' xs))"
      by (cases "h_obs M q x y"; auto)

    then obtain io' where "io = (x,y)#io'"
                      and "io' \<in> list.set (language_for_input M q' xs)"
      by auto

    then have "io' \<in> LS M q'" and "map fst io' = xs"
      using Cons.IH[OF h_obs_state[OF \<open>h_obs M q x y = Some q'\<close>]]
      by blast+
    then have "(x,y)#io' \<in> LS M q"
      using \<open>h_obs M q x y = Some q'\<close>
      unfolding h_obs_language_iff[OF assms(1), of x y io' q] 
      by blast
    then show "io \<in> {io . io \<in> LS M q \<and> map fst io = (x#xs)}"
      unfolding \<open>io = (x,y)#io'\<close> 
      using \<open>map fst io' = xs\<close>
      by auto
  qed
  moreover have "{io . io \<in> LS M q \<and> map fst io = (x#xs)} \<subseteq> list.set (language_for_input M q (x#xs))"
  proof 
    have scheme : "\<And> x y f xs . y \<in> list.set (f x) \<Longrightarrow> x \<in> list.set xs \<Longrightarrow> y \<in> list.set (concat (map f xs))"
      by auto

    fix io assume "io \<in> {io . io \<in> LS M q \<and> map fst io = (x#xs)}"
    then have "io \<in> LS M q" and "map fst io = (x#xs)"
      by auto
    then obtain y io' where "io = (x,y)#io'"
      by fastforce
    then have "(x,y)#io' \<in> LS M q"
      using \<open>io \<in> LS M q\<close>
      by auto
    then obtain q' where "h_obs M q x y = Some q'" and "io' \<in> LS M q'"
      unfolding h_obs_language_iff[OF assms(1), of x y io' q] 
      by blast
    moreover have "io' \<in> list.set (language_for_input M q' xs)"
      using Cons.IH[OF h_obs_state[OF \<open>h_obs M q x y = Some q'\<close>]] \<open>io' \<in> LS M q'\<close> \<open>map fst io = (x#xs)\<close>
      unfolding \<open>io = (x,y)#io'\<close> by auto
    ultimately have "io \<in> list.set ((\<lambda> y .(case h_obs M q x y of None \<Rightarrow> [] | Some q' \<Rightarrow> map ((#) (x,y)) (language_for_input M q' xs))) y)"
      unfolding \<open>io = (x,y)#io'\<close>
      by force 
    moreover have "y \<in> list.set (outputs_as_list M)"
      unfolding outputs_as_list_set
      using language_io(2)[OF \<open>(x,y)#io' \<in> LS M q\<close>] by auto
    ultimately show "io \<in> list.set (language_for_input M q (x#xs))"
      unfolding language_for_input.simps Let_def
      using scheme[of io "(\<lambda> y .(case h_obs M q x y of None \<Rightarrow> [] | Some q' \<Rightarrow> map ((#) (x,y)) (language_for_input M q' xs)))" y]
      by blast
  qed
  ultimately show ?case
    by blast
qed


subsection \<open>Filtering Transitions\<close>

lift_definition filter_transitions :: 
  "('a,'b,'c) fsm \<Rightarrow> (('a,'b,'c) transition \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.filter_transitions 
proof -
  fix M  :: "('a,'b,'c) fsm_impl"
  fix P  :: "('a,'b,'c) transition \<Rightarrow> bool"
  assume "well_formed_fsm M"
  then show "well_formed_fsm (FSM_Impl.filter_transitions M P)" 
    unfolding FSM_Impl.filter_transitions.simps by force
qed


lemma filter_transitions_simps[simp] :
  "initial (filter_transitions M P) = initial M"
  "states (filter_transitions M P) = states M"
  "inputs (filter_transitions M P) = inputs M"
  "outputs (filter_transitions M P) = outputs M"
  "transitions (filter_transitions M P) = {t \<in> transitions M . P t}"
  by (transfer;auto)+


lemma filter_transitions_submachine :
  "is_submachine (filter_transitions M P) M" 
  unfolding filter_transitions_simps by fastforce


lemma filter_transitions_path :
  assumes "path (filter_transitions M P) q p"
  shows "path M q p"
  using path_begin_state[OF assms] 
        transition_subset_path[of "filter_transitions M P" M, OF _ assms]
  unfolding filter_transitions_simps by blast

lemma filter_transitions_reachable_states :
  assumes "q \<in> reachable_states (filter_transitions M P)"
  shows "q \<in> reachable_states M"
  using assms unfolding reachable_states_def filter_transitions_simps 
  using filter_transitions_path[of M P "initial M"]
  by blast


subsection \<open>Filtering States\<close>

lift_definition filter_states :: "('a,'b,'c) fsm \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.filter_states 
proof -
  fix M  :: "('a,'b,'c) fsm_impl"
  fix P  :: "'a \<Rightarrow> bool"
  assume *: "well_formed_fsm M"

  then show "well_formed_fsm (FSM_Impl.filter_states M P)" 
    by (cases "P (FSM_Impl.initial M)"; auto)
qed

lemma filter_states_simps[simp] :
  assumes "P (initial M)"
shows "initial (filter_states M P) = initial M"
      "states (filter_states M P) = Set.filter P (states M)"
      "inputs (filter_states M P) = inputs M"
      "outputs (filter_states M P) = outputs M"
      "transitions (filter_states M P) = {t \<in> transitions M . P (t_source t) \<and> P (t_target t)}"
  using assms by (transfer;auto)+


lemma filter_states_submachine :
  assumes "P (initial M)"
  shows "is_submachine (filter_states M P) M" 
  using filter_states_simps[of P M, OF assms] by fastforce



fun restrict_to_reachable_states :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm" where
  "restrict_to_reachable_states M = filter_states M (\<lambda> q . q \<in> reachable_states M)"


lemma restrict_to_reachable_states_simps[simp] :
shows "initial (restrict_to_reachable_states M) = initial M"
      "states (restrict_to_reachable_states M) = reachable_states M"
      "inputs (restrict_to_reachable_states M) = inputs M"
      "outputs (restrict_to_reachable_states M) = outputs M"
      "transitions (restrict_to_reachable_states M) 
          = {t \<in> transitions M . (t_source t) \<in> reachable_states M}"
proof -
  show "initial (restrict_to_reachable_states M) = initial M"
       "states (restrict_to_reachable_states M) = reachable_states M"
       "inputs (restrict_to_reachable_states M) = inputs M"
       "outputs (restrict_to_reachable_states M) = outputs M"
      
    using filter_states_simps[of "(\<lambda> q . q \<in> reachable_states M)", OF reachable_states_initial] 
    using reachable_state_is_state[of _ M] by auto

  have "transitions (restrict_to_reachable_states M) 
          = {t \<in> transitions M. (t_source t) \<in> reachable_states M \<and> (t_target t) \<in> reachable_states M}"
    using filter_states_simps[of "(\<lambda> q . q \<in> reachable_states M)", OF reachable_states_initial] 
    by auto
  then show "transitions (restrict_to_reachable_states M) 
              = {t \<in> transitions M . (t_source t) \<in> reachable_states M}"
    using reachable_states_next[of _ M] by auto
qed


lemma restrict_to_reachable_states_path :
  assumes "q \<in> reachable_states M"
  shows "path M q p = path (restrict_to_reachable_states M) q p"
proof 
  show "path M q p \<Longrightarrow> path (restrict_to_reachable_states M) q p"
  proof -
    assume "path M q p"
    then show "path (restrict_to_reachable_states M) q p" 
    using assms proof (induction p arbitrary: q rule: list.induct)
      case Nil
      then show ?case
        using restrict_to_reachable_states_simps(2) by fastforce 
    next
      case (Cons t' p')
      then have "path M (t_target t') p'" by auto
      moreover have "t_target t' \<in> reachable_states M" using Cons.prems
        by (metis path_cons_elim reachable_states_next) 
      ultimately show ?case using Cons.IH
        by (metis (no_types, lifting) Cons.prems(1) Cons.prems(2) mem_Collect_eq path.simps 
              path_cons_elim restrict_to_reachable_states_simps(5))        
    qed
  qed

  show "path (restrict_to_reachable_states M) q p \<Longrightarrow> path M q p"
    by (metis (no_types, lifting) assms mem_Collect_eq reachable_state_is_state 
          restrict_to_reachable_states_simps(5) subsetI transition_subset_path)
qed

lemma restrict_to_reachable_states_language :
  "L (restrict_to_reachable_states M) = L M"
  unfolding LS.simps
  unfolding restrict_to_reachable_states_simps
  unfolding restrict_to_reachable_states_path[OF reachable_states_initial, of M]
  by blast

lemma restrict_to_reachable_states_observable :
  assumes "observable M"
shows "observable (restrict_to_reachable_states M)"
  using assms unfolding observable.simps
  unfolding restrict_to_reachable_states_simps
  by blast

lemma restrict_to_reachable_states_minimal :
  assumes "minimal M"
  shows "minimal (restrict_to_reachable_states M)"
proof -
  have "\<And> q1 q2 . q1 \<in> reachable_states M \<Longrightarrow>
                   q2 \<in> reachable_states M \<Longrightarrow>
                   q1 \<noteq> q2 \<Longrightarrow> 
                   LS (restrict_to_reachable_states M) q1 \<noteq> LS (restrict_to_reachable_states M) q2" 
  proof -
    fix q1 q2 assume "q1 \<in> reachable_states M" and "q2 \<in> reachable_states M" and "q1 \<noteq> q2"
    then have "q1 \<in> states M" and "q2 \<in> states M"
      by (simp add: reachable_state_is_state)+
    then have "LS M q1 \<noteq> LS M q2"
      using \<open>q1 \<noteq> q2\<close> assms by auto
    then show "LS (restrict_to_reachable_states M) q1 \<noteq> LS (restrict_to_reachable_states M) q2"
      unfolding LS.simps
      unfolding restrict_to_reachable_states_path[OF \<open>q1 \<in> reachable_states M\<close>]
      unfolding restrict_to_reachable_states_path[OF \<open>q2 \<in> reachable_states M\<close>] .
  qed
  then show ?thesis
    unfolding minimal.simps restrict_to_reachable_states_simps
    by blast
qed

lemma restrict_to_reachable_states_reachable_states :
  "reachable_states (restrict_to_reachable_states M) = states (restrict_to_reachable_states M)"
proof 
  show "reachable_states (restrict_to_reachable_states M) \<subseteq> states (restrict_to_reachable_states M)"
    by (simp add: reachable_state_is_state subsetI) 
  show "states (restrict_to_reachable_states M) \<subseteq> reachable_states (restrict_to_reachable_states M)"
  proof 
    fix q assume "q \<in> states (restrict_to_reachable_states M)"
    then have "q \<in> reachable_states M"
      unfolding restrict_to_reachable_states_simps .
    then show "q \<in> reachable_states (restrict_to_reachable_states M)"
      unfolding reachable_states_def 
      unfolding restrict_to_reachable_states_simps
      unfolding restrict_to_reachable_states_path[OF reachable_states_initial, symmetric] .
  qed
qed


subsection \<open>Adding Transitions\<close>

lift_definition create_unconnected_fsm :: "'a \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.create_unconnected_FSMI by (transfer; simp)

lemma create_unconnected_fsm_simps :
  assumes "finite ns" and "finite ins" and "finite outs" and "q \<in> ns"
  shows "initial (create_unconnected_fsm q ns ins outs) = q"
        "states (create_unconnected_fsm q ns ins outs)   = ns"
        "inputs (create_unconnected_fsm q ns ins outs)  = ins"
        "outputs (create_unconnected_fsm q ns ins outs) = outs"
        "transitions (create_unconnected_fsm q ns ins outs) = {}"
  using assms by (transfer; auto)+

lift_definition create_unconnected_fsm_from_lists :: "'a \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.create_unconnected_fsm_from_lists by (transfer; simp)

lemma create_unconnected_fsm_from_lists_simps :
  assumes "q \<in> set ns"
  shows "initial (create_unconnected_fsm_from_lists q ns ins outs) = q"
        "states (create_unconnected_fsm_from_lists q ns ins outs)  = set ns"
        "inputs (create_unconnected_fsm_from_lists q ns ins outs)  = set ins"
        "outputs (create_unconnected_fsm_from_lists q ns ins outs) = set outs"
        "transitions (create_unconnected_fsm_from_lists q ns ins outs) = {}"
  using assms by (transfer; auto)+

lift_definition create_unconnected_fsm_from_fsets :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> 'c fset \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.create_unconnected_fsm_from_fsets by (transfer; simp)

lemma create_unconnected_fsm_from_fsets_simps :
  assumes "q |\<in>| ns"
  shows "initial (create_unconnected_fsm_from_fsets q ns ins outs) = q"
        "states (create_unconnected_fsm_from_fsets q ns ins outs)   = fset ns"
        "inputs (create_unconnected_fsm_from_fsets q ns ins outs)  = fset ins"
        "outputs (create_unconnected_fsm_from_fsets q ns ins outs) = fset outs"
        "transitions (create_unconnected_fsm_from_fsets q ns ins outs) = {}"
  using assms by (transfer; auto)+


lift_definition add_transitions :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) transition set \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.add_transitions 
proof -
  fix M  :: "('a,'b,'c) fsm_impl"
  fix ts :: "('a,'b,'c) transition set"
  assume *: "well_formed_fsm M"

  then show "well_formed_fsm (FSM_Impl.add_transitions M ts)" 
  proof (cases "\<forall> t \<in> ts . t_source t \<in> FSM_Impl.states M \<and> t_input t \<in> FSM_Impl.inputs M 
                            \<and> t_output t \<in> FSM_Impl.outputs M \<and> t_target t \<in> FSM_Impl.states M")
    case True
    then have "ts \<subseteq> FSM_Impl.states M \<times> FSM_Impl.inputs M \<times> FSM_Impl.outputs M \<times> FSM_Impl.states M" 
      by fastforce
    moreover have "finite (FSM_Impl.states M \<times> FSM_Impl.inputs M \<times> FSM_Impl.outputs M \<times> FSM_Impl.states M)" 
      using * by blast
    ultimately have "finite ts"
      using rev_finite_subset by auto 
    then show ?thesis using * by auto
  next
    case False
    then show ?thesis using * by auto
  qed
qed


lemma add_transitions_simps :
  assumes "\<And> t . t \<in> ts \<Longrightarrow> t_source t \<in> states M \<and> t_input t \<in> inputs M \<and> t_output t \<in> outputs M \<and> t_target t \<in> states M"
  shows "initial (add_transitions M ts) = initial M"
        "states (add_transitions M ts)  = states M"
        "inputs (add_transitions M ts)  = inputs M"
        "outputs (add_transitions M ts) = outputs M"
        "transitions (add_transitions M ts) = transitions M \<union> ts"
  using assms by (transfer; auto)+



lift_definition create_fsm_from_sets :: "'a \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> ('a,'b,'c) transition set \<Rightarrow> ('a,'b,'c) fsm" 
  is FSM_Impl.create_fsm_from_sets
proof -
  fix q :: 'a
  fix qs :: "'a set"
  fix ins :: "'b set"
  fix outs :: "'c set"
  fix ts :: "('a,'b,'c) transition set"

  show "well_formed_fsm (FSM_Impl.create_fsm_from_sets q qs ins outs ts)"
  proof (cases "q \<in> qs \<and> finite qs \<and> finite ins \<and> finite outs")
    case True

    let ?M = "(FSMI q qs ins outs {})"

    show ?thesis proof (cases "\<forall> t \<in> ts . t_source t \<in> FSM_Impl.states ?M \<and> t_input t \<in> FSM_Impl.inputs ?M 
                            \<and> t_output t \<in> FSM_Impl.outputs ?M \<and> t_target t \<in> FSM_Impl.states ?M")
      case True
      then have "ts \<subseteq> FSM_Impl.states ?M \<times> FSM_Impl.inputs ?M \<times> FSM_Impl.outputs ?M \<times> FSM_Impl.states ?M" 
        by fastforce
      moreover have "finite (FSM_Impl.states ?M \<times> FSM_Impl.inputs ?M \<times> FSM_Impl.outputs ?M \<times> FSM_Impl.states ?M)" 
        using \<open>q \<in> qs \<and> finite qs \<and> finite ins \<and> finite outs\<close> by force
      ultimately have "finite ts"
        using rev_finite_subset by auto 
      then show ?thesis by auto
    next
      case False
      then show ?thesis by auto
    qed
  next
    case False
    then show ?thesis by auto
  qed
qed

lemma create_fsm_from_sets_simps :
  assumes "q \<in> qs" and "finite qs" and "finite ins" and "finite outs"
  assumes "\<And> t . t \<in> ts \<Longrightarrow> t_source t \<in> qs \<and> t_input t \<in> ins \<and> t_output t \<in> outs \<and> t_target t \<in> qs"
  shows "initial (create_fsm_from_sets q qs ins outs ts) = q"
        "states (create_fsm_from_sets q qs ins outs ts)  = qs"
        "inputs (create_fsm_from_sets q qs ins outs ts)  = ins"
        "outputs (create_fsm_from_sets q qs ins outs ts) = outs"
        "transitions (create_fsm_from_sets q qs ins outs ts) = ts"
  using assms by (transfer; auto)+

lemma create_fsm_from_self : 
  "m = create_fsm_from_sets (initial m) (states m) (inputs m) (outputs m) (transitions m)"
proof -
  have *: "\<And> t . t \<in> transitions m \<Longrightarrow> t_source t \<in> states m \<and> t_input t \<in> inputs m \<and> t_output t \<in> outputs m \<and> t_target t \<in> states m"
    by auto
  show ?thesis
    using create_fsm_from_sets_simps[OF fsm_initial fsm_states_finite fsm_inputs_finite fsm_outputs_finite *, of "transitions m"]
    apply transfer
    by force
qed

lemma create_fsm_from_sets_surj : 
  assumes "finite (UNIV :: 'a set)" 
  and     "finite (UNIV :: 'b set)" 
  and     "finite (UNIV :: 'c set)"
shows "surj (\<lambda>(q::'a,Q,X::'b set,Y::'c set,T) . create_fsm_from_sets q Q X Y T)" 
proof
  show "range (\<lambda>(q::'a,Q,X::'b set,Y::'c set,T) . create_fsm_from_sets q Q X Y T) \<subseteq> UNIV"
    by simp
  show "UNIV \<subseteq> range (\<lambda>(q::'a,Q,X::'b set,Y::'c set,T) . create_fsm_from_sets q Q X Y T)"    
  proof 
    fix m assume "m \<in> (UNIV :: ('a,'b,'c) fsm set)"
    then have "m = create_fsm_from_sets (initial m) (states m) (inputs m) (outputs m) (transitions m)"
      using create_fsm_from_self by blast
    then have "m = (\<lambda>(q::'a,Q,X::'b set,Y::'c set,T) . create_fsm_from_sets q Q X Y T) (initial m,states m,inputs m,outputs m,transitions m)"
      by auto
    then show "m \<in> range (\<lambda>(q::'a,Q,X::'b set,Y::'c set,T) . create_fsm_from_sets q Q X Y T)"
      by blast
  qed
qed
      


subsection \<open>Distinguishability\<close>

definition distinguishes :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times>'c) list \<Rightarrow> bool" where
  "distinguishes M q1 q2 io = (io \<in> LS M q1 \<union> LS M q2 \<and> io \<notin> LS M q1 \<inter> LS M q2)"

definition minimally_distinguishes :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times>'c) list \<Rightarrow> bool" where
  "minimally_distinguishes M q1 q2 io = (distinguishes M q1 q2 io
                                          \<and> (\<forall> io' . distinguishes M q1 q2 io' \<longrightarrow> length io \<le> length io'))"

lemma minimally_distinguishes_ex :
  assumes "q1 \<in> states M"
      and "q2 \<in> states M"
      and "LS M q1 \<noteq> LS M q2"
obtains v where "minimally_distinguishes M q1 q2 v"
proof -
  let ?vs = "{v . distinguishes M q1 q2 v}"
  define vMin where vMin: "vMin = arg_min length (\<lambda>v . v \<in> ?vs)"
  
  obtain v' where "distinguishes M q1 q2 v'"
    using assms unfolding distinguishes_def by blast
  then have "vMin \<in> ?vs \<and> (\<forall> v'' . distinguishes M q1 q2 v'' \<longrightarrow> length vMin \<le> length v'')"
    unfolding vMin using arg_min_nat_lemma[of "\<lambda>v . distinguishes M q1 q2 v" v' length]
    by simp
  then show ?thesis 
    using that[of vMin] unfolding minimally_distinguishes_def by blast
qed

lemma distinguish_prepend :
  assumes "observable M"
      and "distinguishes M (FSM.after M q1 io) (FSM.after M q2 io) w"
      and "q1 \<in> states M"
      and "q2 \<in> states M"
      and "io \<in> LS M q1"
      and "io \<in> LS M q2"
shows "distinguishes M q1 q2 (io@w)"
proof -
  have "(io@w \<in> LS M q1) = (w \<in> LS M (after M q1 io))"
    using assms(1,3,5)
    by (metis after_language_iff)
  moreover have "(io@w \<in> LS M q2) = (w \<in> LS M (after M q2 io))"
    using assms(1,4,6)
    by (metis after_language_iff)
  ultimately show ?thesis
    using assms(2) unfolding distinguishes_def by blast
qed 

lemma distinguish_prepend_initial :
  assumes "observable M"
      and "distinguishes M (after_initial M (io1@io)) (after_initial M (io2@io)) w"
      and "io1@io \<in> L M"
      and "io2@io \<in> L M"
shows "distinguishes M (after_initial M io1) (after_initial M io2) (io@w)"
proof -
have f1: "\<forall>ps psa f a. (ps::('b \<times> 'c) list) @ psa \<notin> LS f (a::'a) \<or> ps \<in> LS f a"
  by (meson language_prefix)
  then have f2: "io1 \<in> L M"
    by (meson assms(3))
  have f3: "io2 \<in> L M"
    using f1 by (metis assms(4))
  have "io1 \<in> L M"
    using f1 by (metis assms(3))
  then show ?thesis
    by (metis after_is_state after_language_iff after_split assms(1) assms(2) assms(3) assms(4) distinguish_prepend f3)
qed

lemma minimally_distinguishes_no_prefix :
  assumes "observable M"
  and     "u@w \<in> L M"
  and     "v@w \<in> L M"
  and     "minimally_distinguishes M (after_initial M u) (after_initial M v) (w@w'@w'')"
  and     "w' \<noteq> []"
shows "\<not>distinguishes M (after_initial M (u@w)) (after_initial M (v@w)) w''"
proof 
  assume "distinguishes M (after_initial M (u @ w)) (after_initial M (v @ w)) w''"
  then have "distinguishes M (after_initial M u) (after_initial M v) (w@w'')"
    using assms(1-3) distinguish_prepend_initial by blast
  moreover have "length (w@w'') < length (w@w'@w'')"
    using assms(5) by auto
  ultimately show False
    using assms(4) unfolding minimally_distinguishes_def
    using leD by blast 
qed


lemma minimally_distinguishes_after_append :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "minimally_distinguishes M q1 q2 (w@w')"
  and     "w' \<noteq> []"
shows "minimally_distinguishes M (after M q1 w) (after M q2 w) w'"
proof -
  have "\<not> distinguishes M q1 q2 w"
    using assms(5,6)
    by (metis add.right_neutral add_le_cancel_left length_append length_greater_0_conv linorder_not_le minimally_distinguishes_def)
  then have "w \<in> LS M q1 = (w \<in> LS M q2)"
    unfolding distinguishes_def
    by blast 
  moreover have "(w@w') \<in> LS M q1 \<union> LS M q2"
    using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
    by blast
  ultimately have "w \<in> LS M q1" and "w \<in> LS M q2"
    by (meson Un_iff language_prefix)+

  have "(w@w') \<in> LS M q1 = (w' \<in> LS M (after M q1 w))"
    by (meson \<open>w \<in> LS M q1\<close> after_language_iff assms(1))
  moreover have "(w@w') \<in> LS M q2 = (w' \<in> LS M (after M q2 w))"
    by (meson \<open>w \<in> LS M q2\<close> after_language_iff assms(1))
  ultimately have "distinguishes M (after M q1 w) (after M q2 w) w'"
    using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
    by blast
  moreover have "\<And> w'' . distinguishes M (after M q1 w) (after M q2 w) w'' \<Longrightarrow> length w' \<le> length w''"
  proof -
    fix w'' assume "distinguishes M (after M q1 w) (after M q2 w) w''"
    then have "distinguishes M q1 q2 (w@w'')"
      by (metis \<open>w \<in> LS M q1\<close> \<open>w \<in> LS M q2\<close> assms(1) assms(3) assms(4) distinguish_prepend)
    then have "length (w@w') \<le> length (w@w'')"
      using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
      by blast
    then show "length w' \<le> length w''"
      by auto
  qed
  ultimately show ?thesis 
    unfolding minimally_distinguishes_def distinguishes_def 
    by blast
qed



lemma minimally_distinguishes_after_append_initial :
  assumes "observable M"
  and     "minimal M"
  and     "u \<in> L M"
  and     "v \<in> L M"
  and     "minimally_distinguishes M (after_initial M u) (after_initial M v) (w@w')"
  and     "w' \<noteq> []"
shows "minimally_distinguishes M (after_initial M (u@w)) (after_initial M (v@w)) w'"
proof -

  have "\<not> distinguishes M (after_initial M u) (after_initial M v) w"
    using assms(5,6)
    by (metis add.right_neutral add_le_cancel_left length_append length_greater_0_conv linorder_not_le minimally_distinguishes_def)    
  then have "w \<in> LS M (after_initial M u) = (w \<in> LS M (after_initial M v))"
    unfolding distinguishes_def
    by blast 
  moreover have "(w@w') \<in> LS M (after_initial M u) \<union> LS M (after_initial M v)"
    using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
    by blast
  ultimately have "w \<in> LS M (after_initial M u)" and "w \<in> LS M (after_initial M v)"
    by (meson Un_iff language_prefix)+

  have "(w@w') \<in> LS M (after_initial M u) = (w' \<in> LS M (after_initial M (u@w)))"
    by (meson \<open>w \<in> LS M (after_initial M u)\<close> after_language_append_iff after_language_iff assms(1) assms(3))
  moreover have "(w@w') \<in> LS M (after_initial M v) = (w' \<in> LS M (after_initial M (v@w)))"
    by (meson \<open>w \<in> LS M (after_initial M v)\<close> after_language_append_iff after_language_iff assms(1) assms(4))
  ultimately have "distinguishes M (after_initial M (u@w)) (after_initial M (v@w)) w'"
    using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
    by blast
  moreover have "\<And> w'' . distinguishes M (after_initial M (u@w)) (after_initial M (v@w)) w'' \<Longrightarrow> length w' \<le> length w''"
  proof -
    fix w'' assume "distinguishes M (after_initial M (u@w)) (after_initial M (v@w)) w''"
    then have "distinguishes M (after_initial M u) (after_initial M v) (w@w'')"
      by (meson \<open>w \<in> LS M (after_initial M u)\<close> \<open>w \<in> LS M (after_initial M v)\<close> after_language_iff assms(1) assms(3) assms(4) distinguish_prepend_initial)
    then have "length (w@w') \<le> length (w@w'')"
      using assms(5) unfolding minimally_distinguishes_def distinguishes_def 
      by blast
    then show "length w' \<le> length w''"
      by auto
  qed
  ultimately show ?thesis 
    unfolding minimally_distinguishes_def distinguishes_def 
    by blast
qed



lemma minimally_distinguishes_proper_prefixes_card :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "minimally_distinguishes M q1 q2 w"
  and     "S \<subseteq> states M"
shows "card {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S} \<le> card S - 1"
(is "?P S")
proof -

  define k where "k = card S"
  then show ?thesis
    using assms(6) 
  proof (induction k arbitrary: S rule: less_induct)
    case (less k)

    then have "finite S"
      by (metis fsm_states_finite rev_finite_subset)
    
    show ?case proof (cases k)
      case 0
      then have "S = {}"
        using less.prems \<open>finite S\<close> by auto
      then show ?thesis
        by fastforce     
    next
      case (Suc k')

      show ?thesis proof (cases "{w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S} = {}")
        case True
        then show ?thesis
          by (metis bot.extremum dual_order.eq_iff obtain_subset_with_card_n) 
      next
        case False
                                    
        define wk where wk: "wk = arg_max length (\<lambda>wk . wk \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S})"

        obtain wk' where *:"wk' \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S}"
          using False by blast
        have "finite {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S}"
          by (metis (no_types) Collect_mem_eq List.finite_set finite_Collect_conjI)
        then have "wk \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S}"
             and  "\<And> wk' . wk' \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S} \<Longrightarrow> length wk' \<le> length wk"
          using False unfolding wk
          using arg_max_nat_lemma[of "(\<lambda>wk . wk \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S})", OF *]
          by (meson finite_maxlen)+

        then have "wk \<in> set (prefixes w)" and "wk \<noteq> w" and "after M q1 wk \<in> S" and "after M q2 wk \<in> S"
          by blast+

        obtain wk_suffix where "w = wk@wk_suffix" and "wk_suffix \<noteq> []"
          using \<open>wk \<in> set (prefixes w)\<close>
          using prefixes_set_ob \<open>wk \<noteq> w\<close> 
          by blast 

        have "distinguishes M (after M q1 []) (after M q2 []) w"
          using \<open>minimally_distinguishes M q1 q2 w\<close>
          by (metis after.simps(1) minimally_distinguishes_def)      

        have "minimally_distinguishes M (after M q1 wk) (after M q2 wk) wk_suffix"
          using \<open>minimally_distinguishes M q1 q2 w\<close> \<open>wk_suffix \<noteq> []\<close>
          unfolding \<open>w = wk@wk_suffix\<close>
          using minimally_distinguishes_after_append[OF assms(1,2,3,4), of wk wk_suffix]
          by blast
        then have "distinguishes M (after M q1 wk) (after M q2 wk) wk_suffix"
          unfolding minimally_distinguishes_def 
          by auto
        then have "wk_suffix \<in> LS M (after M q1 wk) = (wk_suffix \<notin> LS M (after M q2 wk))"
          unfolding distinguishes_def by blast


        define S1 where S1: "S1 = Set.filter (\<lambda>q . wk_suffix \<in> LS M q) S"
        define S2 where S2: "S2 = Set.filter (\<lambda>q . wk_suffix \<notin> LS M q) S"

        
        have "S = S1 \<union> S2"
          unfolding S1 S2 by auto
        moreover have "S1 \<inter> S2 = {}" 
          unfolding S1 S2 by auto
        ultimately have "card S = card S1 + card S2"
          using \<open>finite S\<close> card_Un_disjoint by blast

        have "S1 \<subseteq> states M" and "S2 \<subseteq> states M"
          using \<open>S = S1 \<union> S2\<close> less.prems(2) by blast+

        have "S1 \<noteq> {}" and "S2 \<noteq> {}"
          using \<open>wk_suffix \<in> LS M (after M q1 wk) = (wk_suffix \<notin> LS M (after M q2 wk))\<close> \<open>after M q1 wk \<in> S\<close> \<open>after M q2 wk \<in> S\<close>
          unfolding S1 S2
          by (metis empty_iff member_filter)+
        then have "card S1 > 0" and "card S2 > 0"
          using \<open>S = S1 \<union> S2\<close> \<open>finite S\<close>
          by (meson card_0_eq finite_Un neq0_conv)+
        then have "card S1 < k" and "card S2 < k"
          using \<open>card S = card S1 + card S2\<close> unfolding less.prems
          by auto

        define W where W: "W = (\<lambda> S1 S2 . {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S1 \<and> after M q2 w' \<in> S2})"
        then have "\<And> S' S'' . W S' S'' \<subseteq> set (prefixes w)"
          by auto
        then have W_finite: "\<And> S' S'' . finite (W S' S'')"
          using List.finite_set[of "prefixes w"]
          by (meson finite_subset) 


        have "\<And> w' . w' \<in> W S S \<Longrightarrow> w' \<noteq> wk \<Longrightarrow> after M q1 w' \<in> S1 = (after M q2 w' \<in> S1)"
        proof -
          fix w' assume *:"w' \<in> W S S" and "w' \<noteq> wk"
          then have "w' \<in> set (prefixes w)" and "w' \<noteq> w" and "after M q1 w' \<in> S" and "after M q2 w' \<in> S"
            unfolding W
            by blast+ 

          then have "w' \<in> LS M q1"
            by (metis IntE UnCI UnE append_self_conv assms(5) distinguishes_def language_prefix leD length_append length_greater_0_conv less_add_same_cancel1 minimally_distinguishes_def prefixes_set_ob) 
          have "w' \<in> LS M q2"
            by (metis IntE UnCI \<open>w' \<in> LS M q1\<close> \<open>w' \<in> set (prefixes w)\<close> \<open>w' \<noteq> w\<close> append_Nil2 assms(5) distinguishes_def leD length_append length_greater_0_conv less_add_same_cancel1 minimally_distinguishes_def prefixes_set_ob) 

          have "length w' < length wk"
            using \<open>w' \<noteq> wk\<close> *
                  \<open>\<And> wk' . wk' \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S} \<Longrightarrow> length wk' \<le> length wk\<close>
            unfolding W
            by (metis (no_types, lifting) \<open>w = wk @ wk_suffix\<close> \<open>w' \<in> set (prefixes w)\<close> append_eq_append_conv le_neq_implies_less prefixes_set_ob) 
            
            
          show "after M q1 w' \<in> S1 = (after M q2 w' \<in> S1)"
          proof (rule ccontr)
            assume "(after M q1 w' \<in> S1) \<noteq> (after M q2 w' \<in> S1)"
            then have "(after M q1 w' \<in> S1 \<and> (after M q2 w' \<in> S2)) \<or> (after M q1 w' \<in> S2 \<and> (after M q2 w' \<in> S1))"
              using \<open>after M q1 w' \<in> S\<close> \<open>after M q2 w' \<in> S\<close>
              unfolding \<open>S = S1 \<union> S2\<close>
              by blast
            then have "wk_suffix \<in> LS M (after M q1 w') = (wk_suffix \<notin> LS M (after M q2 w'))"
              unfolding S1 S2
              by (metis member_filter)
            then have "distinguishes M (after M q1 w') (after M q2 w') wk_suffix"
              unfolding distinguishes_def by blast
            then have "distinguishes M q1 q2 (w'@wk_suffix)"
              using distinguish_prepend[OF assms(1) _ \<open>q1 \<in> states M\<close> \<open>q2 \<in> states M\<close> \<open>w' \<in> LS M q1\<close> \<open>w' \<in> LS M q2\<close>]
              by blast
            moreover have "length (w'@wk_suffix) < length (wk@wk_suffix)"
              using \<open>length w' < length wk\<close>
              by auto
            ultimately show False
              using \<open>minimally_distinguishes M q1 q2 w\<close> 
              unfolding \<open>w = wk@wk_suffix\<close> minimally_distinguishes_def 
              by auto
          qed
        qed



        have "\<And> x . x \<in> W S1 S2 \<union> W S2 S1 \<Longrightarrow> x = wk"
        proof - 
          fix x assume "x \<in> W S1 S2 \<union> W S2 S1"
          then have "x \<in> W S S"
            unfolding W \<open>S = S1 \<union> S2\<close> by blast
          show "x = wk"
            using \<open>x \<in> W S1 S2 \<union> W S2 S1\<close>
            using \<open>\<And> w' . w' \<in> W S S \<Longrightarrow> w' \<noteq> wk \<Longrightarrow> after M q1 w' \<in> S1 = (after M q2 w' \<in> S1)\<close>[OF \<open>x \<in> W S S\<close>]
            unfolding W
            using \<open>S1 \<inter> S2 = {}\<close>
            by blast 
        qed
        moreover have "wk \<in> W S1 S2 \<union> W S2 S1"
          unfolding W 
          using \<open>wk \<in> {w' . w' \<in> set (prefixes w) \<and> w' \<noteq> w \<and> after M q1 w' \<in> S \<and> after M q2 w' \<in> S}\<close>
                \<open>wk_suffix \<in> LS M (after M q1 wk) = (wk_suffix \<notin> LS M (after M q2 wk))\<close>
          by (metis (no_types, lifting) S1 Un_iff \<open>S = S1 \<union> S2\<close> mem_Collect_eq member_filter)
        ultimately have "W S1 S2 \<union> W S2 S1 = {wk}"
          by blast


        have "W S S = (W S1 S1 \<union> W S2 S2 \<union> (W S1 S2 \<union> W S2 S1))"
          unfolding W \<open>S = S1 \<union> S2\<close> by blast
        moreover have "W S1 S1 \<inter> W S2 S2 = {}"
          using \<open>S1 \<inter> S2 = {}\<close> unfolding W
          by blast
        moreover have "W S1 S1 \<inter> (W S1 S2 \<union> W S2 S1) = {}"
          unfolding W
          using \<open>S1 \<inter> S2 = {}\<close>
          by blast
        moreover have "W S2 S2 \<inter> (W S1 S2 \<union> W S2 S1) = {}"
          unfolding W
          using \<open>S1 \<inter> S2 = {}\<close>
          by blast
        moreover have "finite (W S1 S1)" and "finite (W S2 S2)" and "finite {wk}"
          using W_finite by auto
        ultimately have "card (W S S) = card (W S1 S1) + card (W S2 S2) + 1"
          unfolding \<open>W S1 S2 \<union> W S2 S1 = {wk}\<close>
          by (metis card_Un_disjoint finite_UnI inf_sup_distrib2 is_singletonI is_singleton_altdef sup_idem)
        moreover have "card (W S1 S1) \<le> card S1 - 1"
          using less.IH[OF \<open>card S1 < k\<close> _ \<open>S1 \<subseteq> states M\<close>]
          unfolding W by blast
        moreover have "card (W S2 S2) \<le> card S2 - 1"
          using less.IH[OF \<open>card S2 < k\<close> _ \<open>S2 \<subseteq> states M\<close>]
          unfolding W by blast
        ultimately have "card (W S S) \<le> card S - 1"
          using \<open>card S = card S1 + card S2\<close>
          using \<open>card S1 < k\<close> \<open>card S2 < k\<close> less.prems(1) by linarith
        then show ?thesis
          unfolding W .
      qed
    qed
  qed
qed

lemma minimally_distinguishes_proper_prefix_in_language :
  assumes "minimally_distinguishes M q1 q2 io"
  and     "io' \<in> set (prefixes io)"
  and     "io' \<noteq> io"
shows "io' \<in> LS M q1 \<inter> LS M q2"
proof -
  have "io \<in> LS M q1 \<or> io \<in> LS M q2"
    using assms(1) unfolding minimally_distinguishes_def distinguishes_def by blast
  then have "io' \<in> LS M q1 \<or> io' \<in> LS M q2"
    by (metis assms(2) prefixes_set_ob language_prefix) 

  have "length io' < length io"
    using assms(2,3) unfolding prefixes_set by auto
  then have "io' \<in> LS M q1 \<longleftrightarrow> io' \<in> LS M q2"
    using assms(1) unfolding minimally_distinguishes_def distinguishes_def
    by (metis Int_iff Un_Int_eq(1) Un_Int_eq(2) leD)
  then show ?thesis
    using \<open>io' \<in> LS M q1 \<or> io' \<in> LS M q2\<close>
    by blast
qed

lemma distinguishes_not_Nil:
  assumes "distinguishes M q1 q2 io"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "io \<noteq> []"
  using assms unfolding distinguishes_def by auto

fun does_distinguish :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> bool" where
  "does_distinguish M q1 q2 io = (is_in_language M q1 io \<noteq> is_in_language M q2 io)"

lemma does_distinguish_correctness :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
shows "does_distinguish M q1 q2 io = distinguishes M q1 q2 io"
  unfolding does_distinguish.simps
            is_in_language_iff[OF assms(1,2)] 
            is_in_language_iff[OF assms(1,3)]
            distinguishes_def
  by blast

lemma h_obs_distinguishes :
  assumes "observable M"
  and     "h_obs M q1 x y = Some q1'"
  and     "h_obs M q2 x y = None"
shows "distinguishes M q1 q2 [(x,y)]"
  using assms(2,3) LS_single_transition[of x y M] unfolding distinguishes_def h_obs_Some[OF assms(1)] h_obs_None[OF assms(1)]
  by (metis Int_iff UnI1 \<open>\<And>y x q. (h_obs M q x y = None) = (\<nexists>q'. (q, x, y, q') \<in> FSM.transitions M)\<close> assms(1) assms(2) fst_conv h_obs_language_iff option.distinct(1) snd_conv) 

lemma distinguishes_sym :
  assumes "distinguishes M q1 q2 io" 
  shows "distinguishes M q2 q1 io"
  using assms unfolding distinguishes_def by blast

lemma distinguishes_after_prepend :
  assumes "observable M"
  and     "h_obs M q1 x y \<noteq> None"
  and     "h_obs M q2 x y \<noteq> None"
  and     "distinguishes M (FSM.after M q1 [(x,y)]) (FSM.after M q2 [(x,y)]) \<gamma>"
shows "distinguishes M q1 q2 ((x,y)#\<gamma>)"
proof -
  have "[(x,y)] \<in> LS M q1"
    using assms(2) h_obs_language_single_transition_iff[OF assms(1)] by auto

  have "[(x,y)] \<in> LS M q2"
    using assms(3) h_obs_language_single_transition_iff[OF assms(1)] by auto  
  
  show ?thesis
    using after_language_iff[OF assms(1) \<open>[(x,y)] \<in> LS M q1\<close>, of \<gamma>] 
    using after_language_iff[OF assms(1) \<open>[(x,y)] \<in> LS M q2\<close>, of \<gamma>] 
    using assms(4)
    unfolding distinguishes_def
    by simp
qed

lemma distinguishes_after_initial_prepend :
  assumes "observable M"
  and     "io1 \<in> L M"
  and     "io2 \<in> L M"
  and     "h_obs M (after_initial M io1) x y \<noteq> None"
  and     "h_obs M (after_initial M io2) x y \<noteq> None"
  and     "distinguishes M (after_initial M (io1@[(x,y)])) (after_initial M (io2@[(x,y)])) \<gamma>"
shows "distinguishes M (after_initial M io1) (after_initial M io2) ((x,y)#\<gamma>)"
  by (metis after_split assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) distinguishes_after_prepend h_obs_language_append)


subsection \<open>Extending FSMs by single elements\<close>

lemma fsm_from_list_simps[simp] :
  "initial (fsm_from_list q ts) = (case ts of [] \<Rightarrow> q | (t#ts) \<Rightarrow> t_source t)"
  "states (fsm_from_list q ts) = (case ts of [] \<Rightarrow> {q} | (t#ts') \<Rightarrow> ((image t_source (set ts)) \<union> (image t_target (set ts))))"
  "inputs (fsm_from_list q ts) = image t_input (set ts)"
  "outputs (fsm_from_list q ts) = image t_output (set ts)"
  "transitions (fsm_from_list q ts) = set ts"
  by (cases ts; transfer; simp)+

lift_definition add_transition :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.add_transition
  by simp 

lemma add_transition_simps[simp]:
  assumes "t_source t \<in> states M" and "t_input t \<in> inputs M" and "t_output t \<in> outputs M" and "t_target t \<in> states M"
  shows
  "initial (add_transition M t) = initial M"  
  "inputs (add_transition M t) = inputs M"
  "outputs (add_transition M t) = outputs M"
  "transitions (add_transition M t) = insert t (transitions M)"
  "states (add_transition M t) = states M" using assms by (transfer; simp)+


lift_definition add_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.add_state
  by simp

lemma add_state_simps[simp]:
  "initial (add_state M q) = initial M"  
  "inputs (add_state M q) = inputs M"
  "outputs (add_state M q) = outputs M"
  "transitions (add_state M q) = transitions M"
  "states (add_state M q) = insert q (states M)" by (transfer; simp)+

lift_definition add_input :: "('a,'b,'c) fsm \<Rightarrow> 'b \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.add_input
  by simp

lemma add_input_simps[simp]:
  "initial (add_input M x) = initial M"  
  "inputs (add_input M x) = insert x (inputs M)"
  "outputs (add_input M x) = outputs M"
  "transitions (add_input M x) = transitions M"
  "states (add_input M x) = states M" by (transfer; simp)+

lift_definition add_output :: "('a,'b,'c) fsm \<Rightarrow> 'c \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.add_output
  by simp

lemma add_output_simps[simp]:
  "initial (add_output M y) = initial M"  
  "inputs (add_output M y) = inputs M"
  "outputs (add_output M y) = insert y (outputs M)"
  "transitions (add_output M y) = transitions M"
  "states (add_output M y) = states M" by (transfer; simp)+

lift_definition add_transition_with_components :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.add_transition_with_components
  by simp 

lemma add_transition_with_components_simps[simp]:
  "initial (add_transition_with_components M t) = initial M"  
  "inputs (add_transition_with_components M t) = insert (t_input t) (inputs M)"
  "outputs (add_transition_with_components M t) = insert (t_output t) (outputs M)"
  "transitions (add_transition_with_components M t) = insert t (transitions M)"
  "states (add_transition_with_components M t) = insert (t_target t) (insert (t_source t) (states M))"
  by (transfer; simp)+

subsection \<open>Renaming Elements\<close>

lift_definition rename_states :: "('a,'b,'c) fsm \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('d,'b,'c) fsm" is FSM_Impl.rename_states
  by simp 

lemma rename_states_simps[simp]:
  "initial (rename_states M f) = f (initial M)"  
  "states (rename_states M f) = f ` (states M)"  
  "inputs (rename_states M f) = inputs M"
  "outputs (rename_states M f) = outputs M"
  "transitions (rename_states M f) = (\<lambda>t . (f (t_source t), t_input t, t_output t, f (t_target t))) ` transitions M"
  by (transfer; simp)+


lemma rename_states_isomorphism_language_state :
  assumes "bij_betw f (states M) (f ` states M)" 
  and     "q \<in> states M"
shows "LS (rename_states M f) (f q) = LS M q"
proof -

  have *: "bij_betw f (FSM.states M) (FSM.states (FSM.rename_states M f))"
    using assms rename_states_simps by auto

  have **: "f (initial M) = initial (rename_states M f)"
    using rename_states_simps by auto

  have ***: "(\<And>q x y q'.
    q \<in> states M \<Longrightarrow>
    q' \<in> states M \<Longrightarrow> ((q, x, y, q') \<in> transitions M) = ((f q, x, y, f q') \<in> transitions (rename_states M f)))"
  proof 
    fix q x y q' assume "q \<in> states M" and "q' \<in> states M"

    show "(q, x, y, q') \<in> transitions M \<Longrightarrow> (f q, x, y, f q') \<in> transitions (rename_states M f)"
      unfolding assms rename_states_simps by force

    show "(f q, x, y, f q') \<in> transitions (rename_states M f) \<Longrightarrow> (q, x, y, q') \<in> transitions M"
    proof -
      assume "(f q, x, y, f q') \<in> transitions (rename_states M f)"
      then obtain t where "(f q, x, y, f q') = (f (t_source t), t_input t, t_output t, f (t_target t))"
                      and "t \<in> transitions M"
        unfolding assms rename_states_simps 
        by blast
      then have "t_source t \<in> states M" and "t_target t \<in> states M" and "f (t_source t) = f q" and "f (t_target t) = f q'" and "t_input t = x" and "t_output t = y"
        by auto

      have "f q \<in> states (rename_states M f)" and "f q' \<in> states (rename_states M f)"
        using \<open>(f q, x, y, f q') \<in> transitions (rename_states M f)\<close>
        by auto

      have "t_source t = q"
        using \<open>f (t_source t) = f q\<close> \<open>q \<in> states M\<close> \<open>t_source t \<in> states M\<close> 
        using assms unfolding bij_betw_def inj_on_def 
        by blast
      moreover have "t_target t = q'"
        using \<open>f (t_target t) = f q'\<close> \<open>q' \<in> states M\<close> \<open>t_target t \<in> states M\<close> 
        using assms unfolding bij_betw_def inj_on_def 
        by blast
      ultimately show "(q, x, y, q') \<in> transitions M"
        using \<open>t_input t = x\<close> \<open>t_output t = y\<close> \<open>t \<in> transitions M\<close>
        by auto
    qed
  qed

  show ?thesis
    using language_equivalence_from_isomorphism[OF * ** *** assms(2)]
    by blast
qed


lemma rename_states_isomorphism_language :
  assumes "bij_betw f (states M) (f ` states M)" 
  shows "L (rename_states M f) = L M"
  using rename_states_isomorphism_language_state[OF assms fsm_initial]
  unfolding rename_states_simps .

lemma rename_states_observable :
  assumes "bij_betw f (states M) (f ` states M)"
  and     "observable M"
shows "observable (rename_states M f)"  
proof -
  have "\<And> q1 x y q1' q1'' . (q1,x,y,q1') \<in> transitions (rename_states M f) \<Longrightarrow> (q1,x,y,q1'') \<in> transitions (rename_states M f) \<Longrightarrow> q1' = q1''"
  proof -
    fix q1 x y q1' q1'' 
    assume "(q1,x,y,q1') \<in> transitions (rename_states M f)" and "(q1,x,y,q1'') \<in> transitions (rename_states M f)"
    then obtain t' t'' where "t' \<in> transitions M"
                         and "t'' \<in> transitions M"
                         and "(f (t_source t'), t_input t', t_output t', f (t_target t')) = (q1,x,y,q1')"
                         and "(f (t_source t''), t_input t'', t_output t'', f (t_target t'')) = (q1,x,y,q1'')"
      unfolding rename_states_simps
      by force

    then have "f (t_source t') = f (t_source t'')"
      by auto
    moreover have "t_source t' \<in> states M" and "t_source t'' \<in> states M"
      using \<open>t' \<in> transitions M\<close> \<open>t'' \<in> transitions M\<close>
      by auto
    ultimately have "t_source t' = t_source t''"
      using assms(1)
      unfolding bij_betw_def inj_on_def by blast
    then have "t_target t' = t_target t''"
      using assms(2) unfolding observable.simps
      by (metis Pair_inject \<open>(f (t_source t''), t_input t'', t_output t'', f (t_target t'')) = (q1, x, y, q1'')\<close> \<open>(f (t_source t'), t_input t', t_output t', f (t_target t')) = (q1, x, y, q1')\<close> \<open>t' \<in> FSM.transitions M\<close> \<open>t'' \<in> FSM.transitions M\<close>) 
    then show "q1' = q1''"
      using \<open>(f (t_source t''), t_input t'', t_output t'', f (t_target t'')) = (q1, x, y, q1'')\<close> \<open>(f (t_source t'), t_input t', t_output t', f (t_target t')) = (q1, x, y, q1')\<close> by auto
  qed
  then show ?thesis
    unfolding observable_alt_def by blast
qed


lemma rename_states_minimal :
  assumes "bij_betw f (states M) (f ` states M)"
  and     "minimal M"
shows "minimal (rename_states M f)"
proof -
  have "\<And> q q' . q \<in> f ` FSM.states M \<Longrightarrow> q' \<in> f ` FSM.states M \<Longrightarrow> q \<noteq> q' \<Longrightarrow> LS (rename_states M f) q \<noteq> LS (rename_states M f) q'"
  proof -
    fix q q' assume "q \<in> f ` FSM.states M" and "q' \<in> f ` FSM.states M" and "q \<noteq> q'"

    then obtain fq fq' where "fq \<in> states M" and "fq' \<in> states M" and "q = f fq" and "q' = f fq'"
      by auto
    then have "fq \<noteq> fq'" 
      using \<open>q \<noteq> q'\<close> by auto 
    then have "LS M fq \<noteq> LS M fq'"
      by (meson \<open>fq \<in> FSM.states M\<close> \<open>fq' \<in> FSM.states M\<close> assms(2) minimal.elims(2))
    then show "LS (rename_states M f) q \<noteq> LS (rename_states M f) q'"
      using rename_states_isomorphism_language_state[OF assms(1)]
      by (simp add: \<open>fq \<in> FSM.states M\<close> \<open>fq' \<in> FSM.states M\<close> \<open>q = f fq\<close> \<open>q' = f fq'\<close>)
  qed
  then show ?thesis 
    by auto
qed


fun index_states :: "('a::linorder,'b,'c) fsm \<Rightarrow> (nat,'b,'c) fsm" where
  "index_states M = rename_states M (assign_indices (states M))"

lemma assign_indices_bij_betw: "bij_betw (assign_indices (FSM.states M)) (FSM.states M) (assign_indices (FSM.states M) ` FSM.states M)"
  using assign_indices_bij[OF fsm_states_finite[of M]]
  by (simp add: bij_betw_def) 


lemma index_states_language :
  "L (index_states M) = L M"
  using rename_states_isomorphism_language[of "assign_indices (states M)" M, OF assign_indices_bij_betw]
  by auto

lemma index_states_observable :
  assumes "observable M"
  shows "observable (index_states M)"
  using rename_states_observable[of "assign_indices (states M)", OF assign_indices_bij_betw assms]
  unfolding index_states.simps .

lemma index_states_minimal :
  assumes "minimal M"
  shows "minimal (index_states M)" 
  using rename_states_minimal[of "assign_indices (states M)", OF assign_indices_bij_betw assms]
  unfolding index_states.simps .



fun index_states_integer :: "('a::linorder,'b,'c) fsm \<Rightarrow> (integer,'b,'c) fsm" where
  "index_states_integer M = rename_states M (integer_of_nat \<circ> assign_indices (states M))"

lemma assign_indices_integer_bij_betw: "bij_betw (integer_of_nat \<circ> assign_indices (states M)) (FSM.states M) ((integer_of_nat \<circ> assign_indices (states M)) ` FSM.states M)"
proof -
  have *: "inj_on (assign_indices (FSM.states M)) (FSM.states M)" 
    using assign_indices_bij[OF fsm_states_finite[of M]]
    unfolding bij_betw_def
    by auto
  then have "inj_on (integer_of_nat \<circ> assign_indices (states M)) (FSM.states M)"
    unfolding inj_on_def
    by (metis comp_apply nat_of_integer_integer_of_nat)
  then show ?thesis
    unfolding bij_betw_def
    by auto
qed


lemma index_states_integer_language :
  "L (index_states_integer M) = L M"
  using rename_states_isomorphism_language[of "integer_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_integer_bij_betw]
  by auto

lemma index_states_integer_observable :
  assumes "observable M"
  shows "observable (index_states_integer M)"
  using rename_states_observable[of "integer_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_integer_bij_betw assms]
  unfolding index_states_integer.simps .

lemma index_states_integer_minimal :
  assumes "minimal M"
  shows "minimal (index_states_integer M)" 
  using rename_states_minimal[of "integer_of_nat \<circ> assign_indices (states M)" M, OF assign_indices_integer_bij_betw assms]
  unfolding index_states_integer.simps .

subsection \<open>Canonical Separators\<close>

lift_definition canonical_separator' :: "('a,'b,'c) fsm \<Rightarrow> (('a \<times> 'a),'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm" is FSM_Impl.canonical_separator'
proof -
  fix A :: "('a,'b,'c) fsm_impl"
  fix B :: "('a \<times> 'a,'b,'c) fsm_impl"
  fix q1 :: 'a
  fix q2 :: 'a
  assume "well_formed_fsm A" and "well_formed_fsm B"

  then have p1a: "fsm_impl.initial A \<in> fsm_impl.states A"
        and p2a: "finite (fsm_impl.states A)"
        and p3a: "finite (fsm_impl.inputs A)"
        and p4a: "finite (fsm_impl.outputs A)"
        and p5a: "finite (fsm_impl.transitions A)"
        and p6a: "(\<forall>t\<in>fsm_impl.transitions A.
            t_source t \<in> fsm_impl.states A \<and>
            t_input t \<in> fsm_impl.inputs A \<and> t_target t \<in> fsm_impl.states A \<and>
                                             t_output t \<in> fsm_impl.outputs A)"
        and p1b: "fsm_impl.initial B \<in> fsm_impl.states B"
        and p2b: "finite (fsm_impl.states B)"
        and p3b: "finite (fsm_impl.inputs B)"
        and p4b: "finite (fsm_impl.outputs B)"
        and p5b: "finite (fsm_impl.transitions B)"
        and p6b: "(\<forall>t\<in>fsm_impl.transitions B.
            t_source t \<in> fsm_impl.states B \<and>
            t_input t \<in> fsm_impl.inputs B \<and> t_target t \<in> fsm_impl.states B \<and>
                                             t_output t \<in> fsm_impl.outputs B)"
    by simp+

  let ?P = "FSM_Impl.canonical_separator' A B q1 q2"

  show "well_formed_fsm ?P" proof (cases "fsm_impl.initial B = (q1,q2)")
    case False
    then show ?thesis by auto
  next
    case True

    let ?f = "(\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  
    have "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx"
    proof -
      fix qx
      show "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx"
        unfolding set_as_map_def by (cases "\<exists>z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A"; auto)
    qed
    moreover have "\<And> qx . (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A}) qx"
    proof -
      fix qx 
      show "(\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A}) qx"
        by force
    qed
    ultimately have *:" ?f = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A})" 
      by blast
      
    let ?shifted_transitions' = "shifted_transitions (fsm_impl.transitions B)"
    let ?distinguishing_transitions_lr = "distinguishing_transitions ?f q1 q2 (fsm_impl.states B) (fsm_impl.inputs B)"
    let ?ts = "?shifted_transitions' \<union> ?distinguishing_transitions_lr"
  
    have "FSM_Impl.states ?P = (image Inl (FSM_Impl.states B)) \<union> {Inr q1, Inr q2}"
    and  "FSM_Impl.transitions ?P = ?ts"
      unfolding FSM_Impl.canonical_separator'.simps Let_def True by simp+

    have p2: "finite (fsm_impl.states ?P)"
      unfolding \<open>FSM_Impl.states ?P = (image Inl (FSM_Impl.states B)) \<union> {Inr q1, Inr q2}\<close> using p2b by blast
  
    have "fsm_impl.initial ?P = Inl (q1,q2)" by auto
    then have p1: "fsm_impl.initial ?P \<in> fsm_impl.states ?P" 
      using p1a p1b unfolding canonical_separator'.simps True by auto
    have p3: "finite (fsm_impl.inputs ?P)"
      using p3a p3b by auto
    have p4: "finite (fsm_impl.outputs ?P)"
      using p4a p4b by auto

    have "finite (fsm_impl.states B \<times> fsm_impl.inputs B)"
      using p2b p3b by blast
    moreover have **: "\<And> x q1 . finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A})"
    proof - 
      fix x q1
      have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A} = {t_output t | t . t \<in> fsm_impl.transitions A \<and> t_source t = q1 \<and> t_input t = x}"
        by auto
      then have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A} \<subseteq> image t_output (fsm_impl.transitions A)"
        unfolding fst_conv snd_conv by blast
      moreover have "finite (image t_output (fsm_impl.transitions A))"
        using p5a by auto
      ultimately show "finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A})"
        by (simp add: finite_subset)
    qed
    ultimately have "finite ?distinguishing_transitions_lr"
      unfolding * distinguishing_transitions_def by force
    moreover have "finite ?shifted_transitions'"
      unfolding shifted_transitions_def using p5b by auto
    ultimately have "finite ?ts" by blast
    then have p5: "finite (fsm_impl.transitions ?P)"
      by simp
     
    have "fsm_impl.inputs ?P = fsm_impl.inputs A \<union> fsm_impl.inputs B"
      using True by auto
    have "fsm_impl.outputs ?P = fsm_impl.outputs A \<union> fsm_impl.outputs B"
      using True by auto
  
    have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_source t \<in> fsm_impl.states ?P \<and> t_target t \<in> fsm_impl.states ?P"
      unfolding \<open>FSM_Impl.states ?P = (image Inl (FSM_Impl.states B)) \<union> {Inr q1, Inr q2}\<close> shifted_transitions_def 
      using p6b by force
    moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_source t \<in> fsm_impl.states ?P \<and> t_target t \<in> fsm_impl.states ?P"
      unfolding \<open>FSM_Impl.states ?P = (image Inl (FSM_Impl.states B)) \<union> {Inr q1, Inr q2}\<close> distinguishing_transitions_def * by force
    ultimately have "\<And> t . t \<in> ?ts \<Longrightarrow> t_source t \<in> fsm_impl.states ?P \<and> t_target t \<in> fsm_impl.states ?P"
      by blast
    moreover have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
    proof -
      have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs B \<and> t_output t \<in> fsm_impl.outputs B"
        unfolding shifted_transitions_def using p6b by auto
      then show "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
        unfolding \<open>fsm_impl.inputs ?P = fsm_impl.inputs A \<union> fsm_impl.inputs B\<close>
                  \<open>fsm_impl.outputs ?P = fsm_impl.outputs A \<union> fsm_impl.outputs B\<close> by blast
    qed
    moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
      unfolding * distinguishing_transitions_def using p6a p6b True by auto
    ultimately have p6: "(\<forall>t\<in>fsm_impl.transitions ?P.
              t_source t \<in> fsm_impl.states ?P \<and>
              t_input t \<in> fsm_impl.inputs ?P \<and> t_target t \<in> fsm_impl.states ?P \<and>
                                               t_output t \<in> fsm_impl.outputs ?P)"
      unfolding \<open>FSM_Impl.transitions ?P = ?ts\<close> by blast
  
    show "well_formed_fsm ?P"
      using p1 p2 p3 p4 p5 p6 by linarith
  qed
qed 


lemma canonical_separator'_simps :
  assumes "initial P = (q1,q2)"
  shows "initial (canonical_separator' M P q1 q2) = Inl (q1,q2)"
        "states (canonical_separator' M P q1 q2) = (image Inl (states P)) \<union> {Inr q1, Inr q2}"
        "inputs (canonical_separator' M P q1 q2) = inputs M \<union> inputs P"
        "outputs (canonical_separator' M P q1 q2) = outputs M \<union> outputs P"
        "transitions (canonical_separator' M P q1 q2) 
          = shifted_transitions (transitions P) 
              \<union> distinguishing_transitions (h_out M) q1 q2 (states P) (inputs P)"
  using assms unfolding h_out_code by (transfer; auto)+

lemma canonical_separator'_simps_without_assm :
        "initial (canonical_separator' M P q1 q2) = Inl (q1,q2)"
        "states (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then (image Inl (states P)) \<union> {Inr q1, Inr q2} else {Inl (q1,q2)})"
        "inputs (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then inputs M \<union> inputs P else {})"
        "outputs (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then outputs M \<union> outputs P else {})"
        "transitions (canonical_separator' M P q1 q2) = (if initial P = (q1,q2) then shifted_transitions (transitions P) \<union> distinguishing_transitions (h_out M) q1 q2 (states P) (inputs P) else {})"
  unfolding h_out_code by (transfer; simp add: Let_def)+

end