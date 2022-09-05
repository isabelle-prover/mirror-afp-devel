section \<open>SPY-Framework\<close>

text \<open>This theory defines the SPY-Framework and provides completeness properties.\<close>

theory SPY_Framework
imports H_Framework
begin

subsection \<open>Definition of the Framework\<close>

definition spy_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment) \<Rightarrow>                        
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('a,'b,'c) transition list \<Rightarrow> ('a,'b,'c) transition list) \<Rightarrow>                              
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) transition \<Rightarrow> (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) state_cover_assignment \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> (('b\<times>'c) prefix_tree) \<times> 'd) \<Rightarrow> 
                              (('a,'b,'c) fsm \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'd) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>
                              ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                              nat \<Rightarrow>
                              ('b\<times>'c) prefix_tree" 
  where
  "spy_framework M 
                 get_state_cover 
                 separate_state_cover
                 sort_unverified_transitions
                 establish_convergence
                 append_io_pair
                 cg_initial
                 cg_insert
                 cg_lookup
                 cg_merge
                 m 
  = (let
      rstates_set = reachable_states M;
      rstates     = reachable_states_as_list M;
      rstates_io  = List.product rstates (List.product (inputs_as_list M) (outputs_as_list M));
      undefined_io_pairs = List.filter (\<lambda> (q,(x,y)) . h_obs M q x y = None) rstates_io;
      V           = get_state_cover M;
      n           = size_r M;
      TG1         = separate_state_cover M V cg_initial cg_insert cg_lookup;
      sc_covered_transitions = (\<Union> q \<in> rstates_set . covered_transitions M V (V q));
      unverified_transitions = sort_unverified_transitions M V (filter (\<lambda>t . t_source t \<in> rstates_set \<and> t \<notin> sc_covered_transitions) (transitions_as_list M));
      verify_transition = (\<lambda> (T,G) t . let TGxy = append_io_pair M V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t);
                                           (T',G') = establish_convergence M V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t;
                                           G'' = cg_merge G' ((V (t_source t)) @ [(t_input t, t_output t)]) (V (t_target t))                                           
                                        in (T',G''));
      TG2         = foldl verify_transition TG1 unverified_transitions;
      verify_undefined_io_pair = (\<lambda> T (q,(x,y)) . fst (append_io_pair M V T (snd TG2) cg_insert cg_lookup q x y))
    in
      foldl verify_undefined_io_pair (fst TG2) undefined_io_pairs)"





subsection \<open>Required Conditions on Procedural Parameters\<close>

definition verifies_transition :: "(('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                    ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                    ('b\<times>'c) prefix_tree \<Rightarrow> 
                                    'd \<Rightarrow>
                                    ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                    ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                    nat \<Rightarrow>
                                    ('a,'b,'c) transition \<Rightarrow>  
                                    (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>   
                                  ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                  ('e,'b,'c) fsm \<Rightarrow>
                                  ('a,'b,'c) state_cover_assignment \<Rightarrow>    
                                  ('b\<times>'c) prefix_tree \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                  ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                  bool"
  where 
  "verifies_transition f M1 M2 V T0 cg_insert cg_lookup = 
    (\<forall> T G m t .
        (set T \<subseteq> set (fst (f M1 V T G cg_insert cg_lookup m t)))
        \<and> (finite_tree T \<longrightarrow> finite_tree (fst (f M1 V T G cg_insert cg_lookup m t)))
        \<and> (observable M1 \<longrightarrow>
            observable M2 \<longrightarrow>
            minimal M1 \<longrightarrow>
            minimal M2 \<longrightarrow>
            size_r M1 \<le> m \<longrightarrow>
            size M2 \<le> m \<longrightarrow>
            inputs M2 = inputs M1 \<longrightarrow>
            outputs M2 = outputs M1 \<longrightarrow>
            is_state_cover_assignment M1 V \<longrightarrow>
            preserves_divergence M1 M2 (V ` reachable_states M1) \<longrightarrow>
            V ` reachable_states M1 \<subseteq> set T \<longrightarrow>
            t \<in> transitions M1 \<longrightarrow>
            t_source t \<in> reachable_states M1 \<longrightarrow> 
            ((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t)) \<longrightarrow>
            ((V (t_source t)) @ [(t_input t,t_output t)]) \<in> L M2 \<longrightarrow>
            convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>
            convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
            L M1 \<inter> set (fst (f M1 V T G cg_insert cg_lookup m t)) = L M2 \<inter> set (fst (f M1 V T G cg_insert cg_lookup m t)) \<longrightarrow>
            (set T0 \<subseteq> set T) \<longrightarrow>
            (converge M2 ((V (t_source t)) @ [(t_input t,t_output t)]) (V (t_target t)))
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup m t))))"


definition verifies_io_pair :: "(('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                            ('a,'b,'c) state_cover_assignment \<Rightarrow>
                                            ('b\<times>'c) prefix_tree \<Rightarrow> 
                                            'd \<Rightarrow>
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow> 
                                            ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow> 
                                            'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow>  
                                            (('b\<times>'c) prefix_tree \<times> 'd)) \<Rightarrow>
                                          ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow>
                                          ('e,'b,'c) fsm \<Rightarrow>
                                          ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> 'd) \<Rightarrow>
                                          ('d \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) list list) \<Rightarrow>                                     
                                          bool"
  where 
  "verifies_io_pair f M1 M2 cg_insert cg_lookup = 
    (\<forall> V T G q x y .
        (set T \<subseteq> set (fst (f M1 V T G cg_insert cg_lookup q x y)))
        \<and> (finite_tree T \<longrightarrow> finite_tree (fst (f M1 V T G cg_insert cg_lookup q x y)))
        \<and> (observable M1 \<longrightarrow>
            observable M2 \<longrightarrow>
            minimal M1 \<longrightarrow>
            minimal M2 \<longrightarrow>
            inputs M2 = inputs M1 \<longrightarrow>
            outputs M2 = outputs M1 \<longrightarrow>
            is_state_cover_assignment M1 V \<longrightarrow>
            L M1 \<inter> (V ` reachable_states M1) = L M2 \<inter> V ` reachable_states M1 \<longrightarrow>
            q \<in> reachable_states M1 \<longrightarrow>
            x \<in> inputs M1 \<longrightarrow> 
            y \<in> outputs M1 \<longrightarrow> 
            convergence_graph_lookup_invar M1 M2 cg_lookup G \<longrightarrow>   
            convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<longrightarrow>
            L M1 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) \<longrightarrow>
            (\<exists> \<alpha> . 
                 converge M1 \<alpha> (V q) \<and> 
                 converge M2 \<alpha> (V q) \<and>
                 \<alpha> \<in> set (fst (f M1 V T G cg_insert cg_lookup q x y)) \<and>
                 \<alpha>@[(x,y)] \<in> set (fst (f M1 V T G cg_insert cg_lookup q x y)))
            \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup q x y))))"

(* functions that verify io pairs w.r.t. the SPY-Framework also handle io pairs w.r.t. the H-Framework *)
lemma verifies_io_pair_handled: 
  assumes "verifies_io_pair f M1 M2 cg_insert cg_lookup" 
shows "handles_io_pair f M1 M2 cg_insert cg_lookup"
proof -
  
  have *:"\<And> V T G q x y . set T \<subseteq> set (fst (f M1 V T G cg_insert cg_lookup q x y))"
    using assms unfolding verifies_io_pair_def 
    by metis 

  have ***:"\<And> V T G q x y . finite_tree T \<longrightarrow> finite_tree (fst (f M1 V T G cg_insert cg_lookup q x y))"
    using assms unfolding verifies_io_pair_def 
    by metis 

  have **:"\<And> V T G q x y.
        observable M1 \<Longrightarrow>
        observable M2 \<Longrightarrow>
        minimal M1 \<Longrightarrow>
        minimal M2 \<Longrightarrow>
        FSM.inputs M2 = FSM.inputs M1 \<Longrightarrow>
        FSM.outputs M2 = FSM.outputs M1 \<Longrightarrow>
        is_state_cover_assignment M1 V \<Longrightarrow>
        L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1 \<Longrightarrow>
        q \<in> reachable_states M1 \<Longrightarrow>
        x \<in> inputs M1 \<Longrightarrow>
        y \<in> outputs M1 \<Longrightarrow> 
        convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow>
        convergence_graph_insert_invar M1 M2 cg_lookup cg_insert \<Longrightarrow>
        L M1 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) \<Longrightarrow>
        ( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )
        \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup q x y))"
  proof -
    fix V T G q x y
    assume a01: "observable M1"
    moreover assume a02: "observable M2"
    moreover assume a03: "minimal M1"
    moreover assume a04: "minimal M2"
    moreover assume a05: "FSM.inputs M2 = FSM.inputs M1"
    moreover assume a06: "FSM.outputs M2 = FSM.outputs M1"
    moreover assume a07: "is_state_cover_assignment M1 V"
    moreover assume a09: "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
    moreover assume a10: "q \<in> reachable_states M1"
    moreover assume a11: "x \<in> inputs M1"
    moreover assume a12: "y \<in> outputs M1"
    moreover assume a13: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    moreover assume a14: "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
    moreover assume a15: "L M1 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (f M1 V T G cg_insert cg_lookup q x y))"


    ultimately have *:"(\<exists>\<alpha>. converge M1 \<alpha> (V q) \<and>
                          converge M2 \<alpha> (V q) \<and>
                          \<alpha> \<in> Prefix_Tree.set (fst (f M1 V T G cg_insert cg_lookup q x y)) \<and> \<alpha> @ [(x, y)] \<in> Prefix_Tree.set (fst (f M1 V T G cg_insert cg_lookup q x y)))"
               and **: "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup q x y))"
      using assms unfolding verifies_io_pair_def  
      by presburger+

    have "( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} )"
    proof -
      obtain \<alpha> where "converge M1 \<alpha> (V q)" and "converge M2 \<alpha> (V q)" and "\<alpha> @ [(x, y)] \<in> Prefix_Tree.set (fst (f M1 V T G cg_insert cg_lookup q x y))"
        using * by blast

      have "(V q)@[(x,y)] \<in> L M1 = (\<alpha>@[(x,y)] \<in> L M1)"
        using \<open>converge M1 \<alpha> (V q)\<close> using a01 a07
        by (meson converge_append_language_iff) 
      moreover have "(V q)@[(x,y)] \<in> L M2 = (\<alpha>@[(x,y)] \<in> L M2)"
        using \<open>converge M2 \<alpha> (V q)\<close> using a02 a07
        by (meson converge_append_language_iff) 
      moreover have "\<alpha> @ [(x, y)] \<in> L M1 = (\<alpha> @ [(x, y)] \<in> L M2)"
        using \<open>\<alpha> @ [(x, y)] \<in> Prefix_Tree.set (fst (f M1 V T G cg_insert cg_lookup q x y))\<close> a15
        by blast
      ultimately show ?thesis
        by blast
    qed
    then show "( L M1 \<inter> {(V q)@[(x,y)]} = L M2 \<inter> {(V q)@[(x,y)]} ) \<and> convergence_graph_lookup_invar M1 M2 cg_lookup (snd (f M1 V T G cg_insert cg_lookup q x y))"
      using ** by blast
  qed

  show ?thesis
    unfolding handles_io_pair_def
    using * *** ** by presburger
qed



subsection \<open>Completeness and Finiteness of the Framework\<close>

lemma spy_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('d,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
  and     "is_state_cover_assignment M1 (get_state_cover M1)"
  and     "\<And> xs . List.set xs = List.set (sort_unverified_transitions M1 (get_state_cover M1) xs)"
  and     "convergence_graph_initial_invar M1 M2 cg_lookup cg_initial"
  and     "convergence_graph_insert_invar M1 M2 cg_lookup cg_insert"
  and     "convergence_graph_merge_invar M1 M2 cg_lookup cg_merge"
  and     "separates_state_cover separate_state_cover M1 M2 cg_initial cg_insert cg_lookup"
  and     "verifies_transition establish_convergence M1 M2 (get_state_cover M1) (fst (separate_state_cover M1 (get_state_cover M1) cg_initial cg_insert cg_lookup)) cg_insert cg_lookup"
  and     "verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (spy_framework M1 get_state_cover separate_state_cover sort_unverified_transitions establish_convergence append_io_pair cg_initial cg_insert cg_lookup cg_merge m))
                          = (L M2 \<inter> set (spy_framework M1 get_state_cover separate_state_cover sort_unverified_transitions establish_convergence append_io_pair cg_initial cg_insert cg_lookup cg_merge m)))"
  (is "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))")
and "finite_tree (spy_framework M1 get_state_cover separate_state_cover sort_unverified_transitions establish_convergence append_io_pair cg_initial cg_insert cg_lookup cg_merge m)"
proof 
  show "(L M1 = L M2) \<Longrightarrow> ((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"
    by blast


  define rstates where rstates: "rstates = reachable_states_as_list M1"
  define rstates_io where rstates_io: "rstates_io = List.product rstates (List.product (inputs_as_list M1) (outputs_as_list M1))"
  define undefined_io_pairs where undefined_io_pairs: "undefined_io_pairs = List.filter (\<lambda> (q,(x,y)) . h_obs M1 q x y = None) rstates_io"
  define V where V: "V             = get_state_cover M1"
  define n where n: "n             = size_r M1"
  define TG1 where TG1: "TG1 = separate_state_cover M1 V cg_initial cg_insert cg_lookup"

  define sc_covered_transitions where sc_covered_transitions: "sc_covered_transitions = (\<Union> q \<in> reachable_states M1 . covered_transitions M1 V (V q))"
  define unverified_transitions where unverified_transitions: "unverified_transitions = sort_unverified_transitions M1 V (filter (\<lambda>t . t_source t \<in> reachable_states M1 \<and> t \<notin> sc_covered_transitions) (transitions_as_list M1))"
  define verify_transition where verify_transition: "verify_transition = (\<lambda> (T,G) t . let TGxy = append_io_pair M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t);
                                                                                          (T',G') = establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t;
                                       G'' = cg_merge G' ((V (t_source t)) @ [(t_input t, t_output t)]) (V (t_target t))                                           
                                    in (T',G''))"
  define TG2 where TG2: "TG2       = (foldl verify_transition TG1 unverified_transitions)"
  define verify_undefined_io_pair where verify_undefined_io_pair: "verify_undefined_io_pair = (\<lambda> T (q,(x,y)) . fst (append_io_pair M1 V T (snd TG2) cg_insert cg_lookup q x y))" 
  define T3 where T3: "T3            = foldl verify_undefined_io_pair (fst TG2) undefined_io_pairs"

  have "?TS = T3"
    unfolding rstates rstates_io undefined_io_pairs V n TG1 sc_covered_transitions unverified_transitions verify_transition TG2 verify_undefined_io_pair T3
    unfolding spy_framework_def Let_def
    by force
  then have "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3"
    by simp

  have "is_state_cover_assignment M1 V"
    unfolding V using assms(9) .

  (* basic properties of T1 and G1 *)

  define T1 where T1: "T1 = fst TG1"
  moreover define G1 where G1: "G1 = snd TG1"
  ultimately have "TG1 = (T1,G1)" 
    by auto 

  have T1_state_cover: "V ` reachable_states M1 \<subseteq> set T1"
  and  T1_finite: "finite_tree T1"
    using \<open>separates_state_cover separate_state_cover M1 M2 cg_initial cg_insert cg_lookup\<close>
    unfolding T1 TG1 separates_state_cover_def
    by blast+
  

  have T1_V_div: "(L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> preserves_divergence M1 M2 (V ` reachable_states M1)"
   and G1_invar: "(L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G1" 
    using \<open>separates_state_cover separate_state_cover M1 M2 cg_initial cg_insert cg_lookup\<close>
    unfolding T1 G1 TG1 separates_state_cover_def
    using assms(1-4,7,8) \<open>is_state_cover_assignment M1 V\<close> assms(12,11) 
    by blast+

  have "verifies_transition establish_convergence M1 M2 V T1 cg_insert cg_lookup"
    using assms(15)
    unfolding T1 TG1 V .

  (* properties of transition filtering and sorting *)

  have sc_covered_transitions_alt_def: "sc_covered_transitions = {t . t \<in> transitions M1 \<and> t_source t \<in> reachable_states M1 \<and> (V (t_target t) = (V (t_source t))@[(t_input t, t_output t)])}"
    (is "?A = ?B")
  proof 
    show "?A \<subseteq> ?B"
    proof 
      fix t assume "t \<in> ?A"
      then obtain q where "t \<in> covered_transitions M1 V (V q)" and "q \<in> reachable_states M1"
        unfolding sc_covered_transitions 
        by blast
      then have "V q \<in> L M1" and "after_initial M1 (V q) = q"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+

      then obtain p where "path M1 (initial M1) p" and "p_io p = V q"
        by auto
      then have *: "the_elem (paths_for_io M1 (initial M1) (V q)) = p"
        using observable_paths_for_io[OF assms(1) \<open>V q \<in> L M1\<close>]
        unfolding paths_for_io_def
        by (metis (mono_tags, lifting) assms(1) mem_Collect_eq observable_path_unique singletonI the_elem_eq)
      
      have "t \<in> list.set p" and "V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)"
        using \<open>t \<in> covered_transitions M1 V (V q)\<close> 
        unfolding covered_transitions_def Let_def * 
        by auto

      have "t \<in> transitions M1"
        using \<open>t \<in> list.set p\<close> \<open>path M1 (initial M1) p\<close>
        by (meson path_transitions subsetD) 
      moreover have "t_source t \<in> reachable_states M1"
        using reachable_states_path[OF reachable_states_initial \<open>path M1 (initial M1) p\<close> \<open>t \<in> list.set p\<close>] .
      ultimately show "t \<in> ?B"
        using \<open>V (t_source t) @ [(t_input t, t_output t)] = V (t_target t)\<close>
        by auto
    qed

    show "?B \<subseteq> ?A"
    proof 
      fix t assume "t \<in> ?B"
      then have "t \<in> transitions M1" 
                "t_source t \<in> reachable_states M1" 
                "(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)"
        by auto
      then have "t_target t \<in> reachable_states M1"
        using reachable_states_next[of "t_source t" M1 t] 
        by blast
      then have "V (t_target t) \<in> L M1" and "after_initial M1 (V (t_target t)) = (t_target t)"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+
      then obtain p where "path M1 (initial M1) p" and "p_io p = V (t_target t)"
        by auto
      then have *: "the_elem (paths_for_io M1 (initial M1) (V (t_target t))) = p"
        using observable_paths_for_io[OF assms(1) \<open>V (t_target t) \<in> L M1\<close>]
        unfolding paths_for_io_def
        by (metis (mono_tags, lifting) assms(1) mem_Collect_eq observable_path_unique singletonI the_elem_eq)

      
      have "V (t_source t) \<in> L M1" and "after_initial M1 (V (t_source t)) = (t_source t)"
        using \<open>t_source t \<in> reachable_states M1\<close>
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
        by blast+
      then obtain p' where "path M1 (initial M1) p'" and "p_io p' = V (t_source t)"
        by auto
      
      have "path M1 (initial M1) (p'@[t])"
        using after_path[OF assms(1) \<open>path M1 (initial M1) p'\<close>] \<open>path M1 (initial M1) p'\<close> \<open>t\<in>transitions M1\<close>
        unfolding \<open>p_io p' = V (t_source t)\<close>
        unfolding \<open>after_initial M1 (V (t_source t)) = (t_source t)\<close>
        by (metis path_append single_transition_path)
      moreover have "p_io (p'@[t]) = p_io p"
        using \<open>p_io p' = V (t_source t)\<close> 
        unfolding \<open>p_io p = V (t_target t)\<close>  \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>[symmetric]
        by auto
      ultimately have "p'@[t] = p"
        using observable_path_unique[OF assms(1) _ \<open>path M1 (initial M1) p\<close>]
        by force
      then have "t \<in> list.set p"
        by auto
      then have "t \<in> covered_transitions M1 V (V (t_target t))"
        using \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>
        unfolding covered_transitions_def Let_def *
        by auto
      then show "t \<in> ?A"
        using \<open>t_target t \<in> reachable_states M1\<close>
        unfolding sc_covered_transitions 
        by blast
    qed
  qed

  have T1_covered_transitions_conv: "\<And> t . (L M1 \<inter> set T1 = (L M2 \<inter> set T1)) \<Longrightarrow> t \<in> sc_covered_transitions \<Longrightarrow> converge M2 (V (t_target t)) ((V (t_source t))@[(t_input t, t_output t)])"
  proof -
    fix t assume "(L M1 \<inter> set T1 = (L M2 \<inter> set T1))"
                 "t \<in> sc_covered_transitions"

    then have "t \<in> transitions M1" 
              "t_source t \<in> reachable_states M1" 
              "(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)"
      unfolding sc_covered_transitions_alt_def
      by auto
    then have "t_target t \<in> reachable_states M1"
      using reachable_states_next[of "t_source t" M1 t] 
      by blast
    then have "V (t_target t) \<in> L M1"
      using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close>]
      by blast   
    moreover have "V (t_target t) \<in> set T1"
      using T1_state_cover \<open>t_target t \<in> reachable_states M1\<close>
      by blast
    ultimately have "V (t_target t) \<in> L M2"
      using \<open>(L M1 \<inter> set T1 = (L M2 \<inter> set T1))\<close>
      by blast
    then show "converge M2 (V (t_target t)) ((V (t_source t))@[(t_input t, t_output t)])"
      unfolding \<open>(V (t_source t))@[(t_input t, t_output t)] = V (t_target t)\<close>
      by auto
  qed


  have unverified_transitions_alt_def : "list.set unverified_transitions = {t . t \<in> transitions M1 \<and> t_source t \<in> reachable_states M1 \<and> (V (t_target t) \<noteq> (V (t_source t))@[(t_input t, t_output t)])}"
    unfolding unverified_transitions sc_covered_transitions_alt_def V
    unfolding assms(10)[symmetric] 
    using transitions_as_list_set[of M1]
    by auto


  (* remaining properties before the computation of TG2 *)

  have cg_insert_invar : "\<And> G \<gamma> . \<gamma> \<in> L M1 \<Longrightarrow> \<gamma> \<in> L M2 \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_insert G \<gamma>)"
    using assms(12)
    unfolding convergence_graph_insert_invar_def
    by blast

  have cg_merge_invar : "\<And> G \<gamma> \<gamma>'. convergence_graph_lookup_invar M1 M2 cg_lookup G \<Longrightarrow> converge M1 \<gamma> \<gamma>' \<Longrightarrow> converge M2 \<gamma> \<gamma>' \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup (cg_merge G \<gamma> \<gamma>')"
    using assms(13)
    unfolding convergence_graph_merge_invar_def
    by blast


  (* properties of the computation of TG2 *)

  define T2 where T2: "T2 = fst TG2"
  define G2 where G2: "G2 = snd TG2"

  (* idea: in each application of verify_transition, a further transition of unverified_transitions
           (q,x,y,q') is covered - that is
            - traces \<alpha>.(x/y), \<beta> are added to the test suite such that
              - \<alpha> converges with V s in both M1 and M2
              - \<beta> converges with V s' in both M1 and M2
              - \<alpha>.(x/y) converges with \<beta> in both M1 and M2 
            - the test suite is added as required to establish this convergence
            - the convergence graph is updated, respecting the lookup-invariants due to convergence (in merge)
  *)
                                                                            
  have verify_transition_retains_testsuite: "\<And> t T G . set T \<subseteq> set (fst (verify_transition (T,G) t))"
  proof -
    fix t T G
    define TGxy where TGxy: "TGxy = append_io_pair M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)"
    obtain T' G' where TG': "(T',G') = establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t"
      using prod.exhaust by metis
    define G'' where G'': "G'' = cg_merge G' ((V (t_source t)) @ [(t_input t, t_output t)]) (V (t_target t))"

    have *:"verify_transition (T,G) t = (T',G'')"
      using TG'[symmetric]
      unfolding verify_transition G'' TGxy Let_def case_prod_conv 
      by force

    have "set T \<subseteq> set (fst TGxy)"
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close>
      unfolding verifies_io_pair_def TGxy 
      by blast
    also have "set (fst TGxy) \<subseteq> set (fst (T',G'))"
      using \<open>verifies_transition establish_convergence M1 M2 V T1 cg_insert cg_lookup\<close>
      unfolding TG' verifies_transition_def
      by blast
    finally show "set T \<subseteq> set (fst (verify_transition (T,G) t))"
      unfolding * fst_conv .
  qed

  have verify_transition_retains_finiteness: "\<And> t T G . finite_tree T \<Longrightarrow> finite_tree (fst (verify_transition (T,G) t))"
  proof -
    fix T :: "('b\<times>'c) prefix_tree"
    fix t G assume "finite_tree T"

    define TGxy where TGxy: "TGxy = append_io_pair M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)"
    obtain T' G' where TG': "(T',G') = establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t"
      using prod.exhaust by metis
    define G'' where G'': "G'' = cg_merge G' ((V (t_source t)) @ [(t_input t, t_output t)]) (V (t_target t))"

    have *:"verify_transition (T,G) t = (T',G'')"
      using TG'[symmetric]
      unfolding verify_transition G'' TGxy Let_def case_prod_conv 
      by force

    have "finite_tree (fst TGxy)"
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close> \<open>finite_tree T\<close>
      unfolding verifies_io_pair_def TGxy 
      by blast
    then have "finite_tree (fst (T',G'))"
      using \<open>verifies_transition establish_convergence M1 M2 V T1 cg_insert cg_lookup\<close>
      unfolding TG' verifies_transition_def
      by blast
    then show "finite_tree (fst (verify_transition (T,G) t))"
      unfolding * fst_conv .
  qed


  define covers_unverified_transition 
    where covers_unverified_transition: "covers_unverified_transition  = (\<lambda>t (T',G') .
                                                ((\<exists> \<alpha> \<beta> . converge M1 \<alpha> (V (t_source t)) \<and>
                                                          converge M2 \<alpha> (V (t_source t)) \<and>
                                                          converge M1 \<beta> (V (t_target t)) \<and>
                                                          converge M2 \<beta> (V (t_target t)) \<and>
                                                          \<alpha>@[(t_input t,t_output t)] \<in> (set T') \<and>
                                                          \<beta> \<in> (set T'))
                                                  \<and> (converge M2 ((V (t_source t)) @ [(t_input t,t_output t)]) (V (t_target t)))
                                                  \<and> convergence_graph_lookup_invar M1 M2 cg_lookup G'))"

  have verify_transition_cover_prop: "\<And> t T G . (L M1 \<inter> (set (fst (verify_transition (T,G) t))) = L M2 \<inter> (set (fst (verify_transition (T,G) t))))
                                          \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G
                                          \<Longrightarrow> t \<in> transitions M1
                                          \<Longrightarrow> t_source t \<in> reachable_states M1
                                          \<Longrightarrow> ((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))
                                          \<Longrightarrow> set T1 \<subseteq> set T
                                          \<Longrightarrow> covers_unverified_transition t (verify_transition (T,G) t)"
  proof -
    fix t T G
    assume a1: "(L M1 \<inter> (set (fst (verify_transition (T,G) t))) = L M2 \<inter> (set (fst (verify_transition (T,G) t))))"
    assume a2: "convergence_graph_lookup_invar M1 M2 cg_lookup G"
    assume a3: "t \<in> transitions M1"
    assume a4: "t_source t \<in> reachable_states M1"
    assume a5: "set T1 \<subseteq> set T"
    assume a6: "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"

    define TGxy where TGxy: "TGxy = append_io_pair M1 V T G cg_insert cg_lookup (t_source t) (t_input t) (t_output t)"
    obtain T' G' where TG': "(T',G') = establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t"
      using prod.exhaust by metis
    have T':  "T'  = fst (establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t)"
     and G':  "G'  = snd (establish_convergence M1 V (fst TGxy) (snd TGxy) cg_insert cg_lookup m t)"
      unfolding TG'[symmetric] by auto
    define G'' where G'': "G'' = cg_merge G' ((V (t_source t)) @ [(t_input t, t_output t)]) (V (t_target t))"

    have "verify_transition (T,G) t = (T',G'')"
      using TG'[symmetric]
      unfolding verify_transition G'' TGxy Let_def case_prod_conv 
      by force
    then have "set T \<subseteq> set T'"
      using verify_transition_retains_testsuite[of T G t] unfolding T' 
      by auto
    then have "(L M1 \<inter> (set T1) = L M2 \<inter> (set T1))"
      using a1 a5 unfolding \<open>verify_transition (T,G) t = (T',G'')\<close> fst_conv 
      by blast
    then have *: "preserves_divergence M1 M2 (V ` reachable_states M1)"
      using T1_V_div
      by auto

    have "set (fst TGxy) \<subseteq> set (fst (T',G'))"
      using \<open>verifies_transition establish_convergence M1 M2 V T1 cg_insert cg_lookup\<close>
      unfolding TG' verifies_transition_def
      by blast
    then have "set (fst TGxy) \<subseteq> set (fst (verify_transition (T,G) t))"
      unfolding \<open>verify_transition (T,G) t = (T',G'')\<close> fst_conv .
    then have "L M1 \<inter> set (fst TGxy) = L M2 \<inter> set (fst TGxy)"
      using a1 by blast

    have "L M1 \<inter> set T' = L M2 \<inter> set T'" and "L M1 \<inter> set T = L M2 \<inter> set T"
      using a1 \<open>set T \<subseteq> set T'\<close> unfolding T' \<open>verify_transition (T,G) t = (T',G'')\<close> fst_conv 
      by blast+

    have **: "V ` reachable_states M1 \<subseteq> set T"
      using a5 T1_state_cover by blast

    have "L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
      using T1_state_cover \<open>L M1 \<inter> Prefix_Tree.set T1 = L M2 \<inter> Prefix_Tree.set T1\<close> by blast

    

    have "(\<exists>\<alpha>. converge M1 \<alpha> (V (t_source t)) \<and>
            converge M2 \<alpha> (V (t_source t)) \<and>
            \<alpha> \<in> Prefix_Tree.set (fst TGxy) \<and>
            \<alpha> @ [((t_input t), (t_output t))] \<in> Prefix_Tree.set (fst TGxy))"
    and  "convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGxy)"
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close>
      unfolding verifies_io_pair_def  
      using assms(1-4,7,8) \<open>is_state_cover_assignment M1 V\<close> \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close> a4 fsm_transition_input[OF a3] fsm_transition_output[OF a3] a2 \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close> \<open>L M1 \<inter> set (fst TGxy) = L M2 \<inter> set (fst TGxy)\<close>
      unfolding TGxy
      by blast+ 

    then obtain w where "converge M1 w (V (t_source t))"
                        "converge M2 w (V (t_source t))"
                        "w \<in> Prefix_Tree.set (fst TGxy)"
                        "w @ [((t_input t), (t_output t))] \<in> set (fst TGxy)"
      by blast
    then have "w @ [((t_input t), (t_output t))] \<in> L M1 \<longleftrightarrow> w @ [((t_input t), (t_output t))] \<in> L M2"
      using \<open>L M1 \<inter> set (fst TGxy) = L M2 \<inter> set (fst TGxy)\<close>
      by blast
    moreover have "w @ [((t_input t), (t_output t))] \<in> L M1 \<longleftrightarrow> V (t_source t) @ [(t_input t, t_output t)] \<in> L M1"
      using \<open>converge M1 w (V (t_source t))\<close>
      by (meson assms(1) converge_append_language_iff) 
    moreover have "V (t_source t) @ [(t_input t, t_output t)] \<in> L M1"
      using state_cover_transition_converges[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>t \<in> transitions M1\<close> \<open>t_source t \<in> reachable_states M1\<close>]
      by auto
    ultimately have "w @ [(t_input t, t_output t)] \<in> L M2"
      by blast
    then have "V (t_source t) @ [(t_input t, t_output t)] \<in> L M2"
      using \<open>converge M2 w (V (t_source t))\<close>
      by (meson assms(2) converge_append_language_iff) 
    have "V ` reachable_states M1 \<subseteq> set T"
      using a5 T1_state_cover by blast

    have "set T \<subseteq> set (fst TGxy)"
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close> 
      unfolding verifies_io_pair_def TGxy by blast
    then have "set T1 \<subseteq> set (fst TGxy)"
      using a5 by blast 
    then have "\<And> io . set (after T1 io) \<subseteq> set (after (fst TGxy) io)"
      unfolding after_set by auto   

    have "V ` reachable_states M1 \<subseteq> set (fst TGxy)"
      using "**" \<open>Prefix_Tree.set T \<subseteq> Prefix_Tree.set (fst TGxy)\<close> by auto

    have p2: "converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))" 
     and "convergence_graph_lookup_invar M1 M2 cg_lookup G'"
      using \<open>verifies_transition establish_convergence M1 M2 V T1 cg_insert cg_lookup\<close>
      unfolding verifies_transition_def
      using assms(1-8) \<open>is_state_cover_assignment M1 V\<close> \<open>preserves_divergence M1 M2 (V ` reachable_states M1)\<close> \<open>V ` reachable_states M1 \<subseteq> set (fst TGxy)\<close> a3 a4 a6 \<open>V (t_source t) @ [(t_input t, t_output t)] \<in> L M2\<close> \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd TGxy)\<close> \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close> \<open>L M1 \<inter> set T' = L M2 \<inter> set T'\<close> 
      using \<open>set T1 \<subseteq> set (fst TGxy)\<close>
      unfolding T' G'      
      by blast+

    have "w @ [((t_input t), (t_output t))] \<in> set T'"
      using \<open>w @ [((t_input t), (t_output t))] \<in> set (fst TGxy)\<close>
      using T' \<open>Prefix_Tree.set (fst TGxy) \<subseteq> Prefix_Tree.set (fst (T', G'))\<close> by auto 

    have p1: "(\<exists>\<alpha> \<beta>.
                converge M1 \<alpha> (V (t_source t)) \<and>
                converge M2 \<alpha> (V (t_source t)) \<and>
                converge M1 \<beta> (V (t_target t)) \<and>
                converge M2 \<beta> (V (t_target t)) \<and>
                \<alpha> @ [(t_input t, t_output t)] \<in> set T' \<and>
                \<beta> \<in> set T')"
    proof -
      have "V (t_source t) \<in> L M1"
        using state_cover_assignment_after(1)[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>t_source t \<in> reachable_states M1\<close>] .
      have "V (t_target t) \<in> L M1"
        using state_cover_assignment_after(1)[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> reachable_states_next[OF \<open>t_source t \<in> reachable_states M1\<close> \<open>t \<in> transitions M1\<close>]] 
        by auto


      note \<open>converge M1 w (V (t_source t))\<close> and \<open>converge M2 w (V (t_source t))\<close>
      moreover have "converge M1 (V (t_target t)) (V (t_target t))"
        using \<open>V (t_target t) \<in> L M1\<close> by auto 
      moreover have "converge M2 (V (t_target t)) (V (t_target t))"
        using reachable_states_next[OF \<open>t_source t \<in> reachable_states M1\<close> \<open>t \<in> transitions M1\<close>] \<open>V (t_target t) \<in> L M1\<close> \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
        by auto
      moreover note \<open>w @ [(t_input t, t_output t)] \<in> set T'\<close> 
      moreover have "V (t_target t) \<in> set T'" 
        using \<open>V ` reachable_states M1 \<subseteq> set T\<close> \<open>set T \<subseteq> set T'\<close> reachable_states_next[OF \<open>t_source t \<in> reachable_states M1\<close> \<open>t \<in> transitions M1\<close>]
        by auto
      ultimately show ?thesis 
        by blast
    qed

    have p3: "convergence_graph_lookup_invar M1 M2 cg_lookup G''"
      unfolding G''
      using cg_merge_invar[OF \<open>convergence_graph_lookup_invar M1 M2 cg_lookup G'\<close>]
            state_cover_transition_converges[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> a3 a4]
            \<open>converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))\<close>
      by blast
    show "covers_unverified_transition t (verify_transition (T,G) t)"
      using p1 p2 p3
      unfolding \<open>verify_transition (T,G) t = (T',G'')\<close> fst_conv snd_conv covers_unverified_transition
      by blast
  qed



  have verify_transition_foldl_invar_1: "\<And> ts . list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> 
                set T1 \<subseteq> set (fst (foldl verify_transition (T1, G1) ts)) \<and> finite_tree (fst (foldl verify_transition (T1, G1) ts))"
  proof -
    fix ts assume "list.set ts \<subseteq> list.set unverified_transitions" 
    then show "set T1 \<subseteq> set (fst (foldl verify_transition (T1, G1) ts)) \<and> finite_tree (fst (foldl verify_transition (T1, G1) ts))"
    proof (induction ts rule: rev_induct)
      case Nil
      then show ?case 
        using T1_finite by auto
    next
      case (snoc t ts)
      then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1"
        unfolding unverified_transitions_alt_def 
        by force+

      have p1: "list.set ts \<subseteq> list.set unverified_transitions"
        using snoc.prems(1) by auto

      have "set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t])))"
        using verify_transition_retains_testsuite unfolding foldl_append foldl.simps
        by (metis eq_fst_iff)

      have **: "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))"  
       and ***: "finite_tree (fst (foldl verify_transition (T1, G1) ts))"
        using snoc.IH[OF p1] 
        by auto          
    
      have "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) (ts@[t])))"
        using ** verify_transition_retains_testsuite \<open>set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t])))\<close> 
        by auto 
      moreover have "finite_tree (fst (foldl verify_transition (T1, G1) (ts@[t])))"
        using verify_transition_retains_finiteness[OF ***, of "snd (foldl verify_transition (T1, G1) ts)"] 
        by auto
      ultimately show ?case 
        by simp
    qed
  qed 
  then have T2_invar_1: "set T1 \<subseteq> set T2"
        and T2_finite : "finite_tree T2"
    unfolding TG2 G2 T2 \<open>TG1 = (T1,G1)\<close>
    by auto

  have verify_transition_foldl_invar_2: "\<And> ts . list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> 
                L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) \<Longrightarrow> 
                convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) ts))"
  proof -
    fix ts assume "list.set ts \<subseteq> list.set unverified_transitions" 
              and "L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts))"
    then show "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) ts))"
    proof (induction ts rule: rev_induct)
      case Nil
      then show ?case 
        using G1_invar by auto
    next
      case (snoc t ts)
      then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1" and "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"
        unfolding unverified_transitions_alt_def 
        by force+

      have p1: "list.set ts \<subseteq> list.set unverified_transitions"
        using snoc.prems(1) by auto

      have "set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t])))"
        using verify_transition_retains_testsuite unfolding foldl_append foldl.simps
        by (metis eq_fst_iff)
      then have p2: "L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts))"
        using snoc.prems(2)
        by blast 

      have *:"convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) ts))"                                                           
        using snoc.IH[OF p1 p2] 
        by auto          

      have **: "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))"
        using verify_transition_foldl_invar_1[OF p1] by blast
    
      have "covers_unverified_transition t (verify_transition (fst (foldl verify_transition (T1, G1) ts), snd (foldl verify_transition (T1, G1) ts)) t)"          
        using verify_transition_cover_prop[OF _ * \<open>t \<in> transitions M1\<close> \<open>t_source t \<in> reachable_states M1\<close> \<open>((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))\<close> **] snoc.prems(2)
        unfolding prod.collapse
        by auto
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (verify_transition (fst (foldl verify_transition (T1, G1) ts), snd (foldl verify_transition (T1, G1) ts)) t))"
        unfolding covers_unverified_transition
        by auto
      then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) (ts@[t])))"
        by auto
      moreover have "Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) (ts@[t])))"
        using ** verify_transition_retains_testsuite \<open>set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t])))\<close> 
        by auto 
      ultimately show ?case 
        by simp
    qed
  qed 
  then have T2_invar_2: "L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G2"
    unfolding TG2 G2 T2 \<open>TG1 = (T1,G1)\<close> by auto

  have T2_cover: "\<And> t . L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> t \<in> list.set unverified_transitions \<Longrightarrow> covers_unverified_transition t (T2,G2)"
  proof -
    have "\<And> t ts . t \<in> list.set ts \<Longrightarrow> list.set ts \<subseteq> list.set unverified_transitions \<Longrightarrow> L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) \<Longrightarrow> covers_unverified_transition t (foldl verify_transition (T1, G1) ts)"
    proof -
      fix t ts
      assume "t \<in> list.set ts" and "list.set ts \<subseteq> list.set unverified_transitions" and "L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts))"

      then show "covers_unverified_transition t (foldl verify_transition (T1, G1) ts)"
      proof (induction ts rule: rev_induct)
        case Nil
        then show ?case by auto
      next
        case (snoc t' ts)

        then have "t \<in> transitions M1" and "t_source t \<in> reachable_states M1" and "((V (t_source t)) @ [(t_input t,t_output t)]) \<noteq> (V (t_target t))"
          unfolding unverified_transitions_alt_def by force+

        have "t' \<in> transitions M1" and "t_source t' \<in> reachable_states M1" and "((V (t_source t')) @ [(t_input t',t_output t')]) \<noteq> (V (t_target t'))"
          using snoc.prems(2)
          unfolding unverified_transitions_alt_def 
          by auto

        have "set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t'])))"
          using verify_transition_retains_testsuite unfolding foldl_append foldl.simps
          by (metis eq_fst_iff)
        then have "L M1 \<inter> set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> set (fst (foldl verify_transition (T1, G1) ts))"
          using snoc.prems(3) 
          by blast

        have *: "L M1 \<inter> Prefix_Tree.set (fst (verify_transition (foldl verify_transition (T1, G1) ts) t')) = L M2 \<inter> Prefix_Tree.set (fst (verify_transition (foldl verify_transition (T1, G1) ts) t'))"
          using snoc.prems(3) by auto

        have "L M1 \<inter> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))"
          using \<open>set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t'])))\<close> snoc.prems(3)
          by auto
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) ts)) \<and> Prefix_Tree.set T1 \<subseteq> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))"
          using snoc.prems(2) verify_transition_foldl_invar_1[of ts] verify_transition_foldl_invar_2[of ts]
          by auto
        then have covers_t': "covers_unverified_transition t' (verify_transition (fst (foldl verify_transition (T1, G1) ts), snd (foldl verify_transition (T1, G1) ts)) t')"          
          using verify_transition_cover_prop[OF _ _ \<open>t' \<in> transitions M1\<close> \<open>t_source t' \<in> reachable_states M1\<close> \<open>((V (t_source t')) @ [(t_input t',t_output t')]) \<noteq> (V (t_target t'))\<close>, of "(fst (foldl verify_transition (T1, G1) ts))" "(snd (foldl verify_transition (T1, G1) ts))" ]
          unfolding prod.collapse
          using *
          by auto
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (verify_transition (fst (foldl verify_transition (T1, G1) ts), snd (foldl verify_transition (T1, G1) ts)) t'))"
          unfolding covers_unverified_transition
          by force
        then have "convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) (ts@[t'])))"
          by auto            

        show ?case proof (cases "t = t'")
          case True
          then show ?thesis 
            using covers_t' by auto
        next
          case False
          then have "t \<in> list.set ts"
            using snoc.prems(1) by auto

          have "list.set ts \<subseteq> list.set (unverified_transitions)"
            using snoc.prems(2) by auto

          have "covers_unverified_transition t (foldl verify_transition (T1, G1) ts)"
            using snoc.IH[OF \<open>t \<in> list.set ts\<close>] snoc.prems(2) \<open>L M1 \<inter> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts)) = L M2 \<inter> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))\<close>
            by auto
          then have "covers_unverified_transition t (fst (foldl verify_transition (T1, G1) ts), snd (foldl verify_transition (T1, G1) ts))"
            by auto
          then have "(\<exists>\<alpha> \<beta>. converge M1 \<alpha> (V (t_source t)) \<and>
                            converge M2 \<alpha> (V (t_source t)) \<and>
                            converge M1 \<beta> (V (t_target t)) \<and>
                            converge M2 \<beta> (V (t_target t)) \<and> \<alpha> @ [(t_input t, t_output t)] \<in> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts)) \<and> \<beta> \<in> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) ts))) \<and>
                            converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))"
            unfolding covers_unverified_transition
            by blast 
          moreover have "set (fst (foldl verify_transition (T1, G1) ts)) \<subseteq> set (fst (foldl verify_transition (T1, G1) (ts@[t'])))"
            using verify_transition_retains_testsuite[of "(fst (foldl verify_transition (T1, G1) ts))" "(snd (foldl verify_transition (T1, G1) ts))"]
            unfolding prod.collapse 
            by auto         
          ultimately have "(\<exists>\<alpha> \<beta>. 
                            converge M1 \<alpha> (V (t_source t)) \<and>
                            converge M2 \<alpha> (V (t_source t)) \<and>
                            converge M1 \<beta> (V (t_target t)) \<and>
                            converge M2 \<beta> (V (t_target t)) \<and> \<alpha> @ [(t_input t, t_output t)] \<in> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) (ts@[t']))) \<and> \<beta> \<in> Prefix_Tree.set (fst (foldl verify_transition (T1, G1) (ts@[t'])))) \<and>
                            converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t))"
            by blast
          then have "covers_unverified_transition t (fst (foldl verify_transition (T1, G1) (ts@[t'])), snd (foldl verify_transition (T1, G1) (ts@[t'])))"
            unfolding covers_unverified_transition
            using \<open>convergence_graph_lookup_invar M1 M2 cg_lookup (snd (foldl verify_transition (T1, G1) (ts@[t'])))\<close>
            by blast
          then show ?thesis
            by auto
        qed
      qed
    qed

    then show "\<And> t . L M1 \<inter> set T2 = L M2 \<inter> set T2 \<Longrightarrow> t \<in> list.set unverified_transitions \<Longrightarrow> covers_unverified_transition t (T2,G2)"
      unfolding TG2 T2 G2 \<open>TG1 = (T1,G1)\<close>
      by simp
  qed


  (* properties of T3 derived from those of T1 and T2 and the assumption that T3 is passed by M2 *)

  have verify_undefined_io_pair_retains_testsuite: "\<And> qxy T . set T \<subseteq> set (verify_undefined_io_pair T qxy)"
  proof -
    fix qxy :: "('a \<times> 'b \<times> 'c)"
    fix T
    obtain q x y where "qxy = (q,x,y)"
      using prod.exhaust by metis
    show \<open>set T \<subseteq> set (verify_undefined_io_pair T qxy)\<close>
      unfolding \<open>qxy = (q,x,y)\<close>
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close>
      unfolding verifies_io_pair_def verify_undefined_io_pair case_prod_conv
      by blast
  qed
  have verify_undefined_io_pair_folding_retains_testsuite: "\<And> qxys T . set T \<subseteq> set (foldl verify_undefined_io_pair T qxys)"
  proof -
    fix qxys T
    show "set T \<subseteq> set (foldl verify_undefined_io_pair T qxys)"
      using verify_undefined_io_pair_retains_testsuite
      by (induction qxys rule: rev_induct; force) 
  qed

  have verify_undefined_io_pair_retains_finiteness: "\<And> qxy T . finite_tree T \<Longrightarrow> finite_tree (verify_undefined_io_pair T qxy)"
  proof -
    fix qxy :: "('a \<times> 'b \<times> 'c)"
    fix T :: "('b\<times>'c) prefix_tree"
    assume "finite_tree T"
    obtain q x y where "qxy = (q,x,y)"
      using prod.exhaust by metis
    show \<open>finite_tree (verify_undefined_io_pair T qxy)\<close>
      unfolding \<open>qxy = (q,x,y)\<close>
      using \<open>verifies_io_pair append_io_pair M1 M2 cg_insert cg_lookup\<close> \<open>finite_tree T\<close>
      unfolding verifies_io_pair_def verify_undefined_io_pair case_prod_conv
      by blast
  qed
  have verify_undefined_io_pair_folding_retains_finiteness: "\<And> qxys T . finite_tree T \<Longrightarrow> finite_tree (foldl verify_undefined_io_pair T qxys)"
  proof -
    fix qxys 
    fix T :: "('b\<times>'c) prefix_tree"
    assume "finite_tree T"
    then show "finite_tree (foldl verify_undefined_io_pair T qxys)"
      using verify_undefined_io_pair_retains_finiteness
      by (induction qxys rule: rev_induct; force) 
  qed

  have "set T2 \<subseteq> set T3"
    unfolding T3 T2
  proof (induction undefined_io_pairs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then show ?case 
      using verify_undefined_io_pair_retains_testsuite[of "(foldl verify_undefined_io_pair (fst TG2) xs)" x]
      by force
  qed
  then have passes_T2: "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T2 = L M2 \<inter> set T2"
    using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (L M1 \<inter> set T3 = L M2 \<inter> set T3)\<close>
    by blast


  have "set T1 \<subseteq> set T3"
  and  G2_invar: "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> convergence_graph_lookup_invar M1 M2 cg_lookup G2"
    using T2_invar_1 T2_invar_2[OF passes_T2] \<open>set T2 \<subseteq> set T3\<close> 
    by auto
  then have passes_T1: "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T1 = L M2 \<inter> set T1"
    using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3\<close>
    by blast

  have T3_preserves_divergence : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> preserves_divergence M1 M2 (V ` reachable_states M1)"
    using T1_V_div[OF passes_T1] .

  have T3_state_cover : "V ` reachable_states M1 \<subseteq> set T3"
    using T1_state_cover \<open>set T1 \<subseteq> set T3\<close>
    by blast

  have T3_covers_transitions : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> t . t \<in> transitions M1 \<Longrightarrow> t_source t \<in> reachable_states M1 \<Longrightarrow> 
          (\<exists>\<alpha> \<beta>.
            converge M1 \<alpha> (V (t_source t)) \<and>
            converge M2 \<alpha> (V (t_source t)) \<and>
            converge M1 \<beta> (V (t_target t)) \<and>
            converge M2 \<beta> (V (t_target t)) \<and> 
            \<alpha> @ [(t_input t, t_output t)] \<in> set T3 \<and> 
            \<beta> \<in> set T3)
          \<and> converge M2 (V (t_source t) @ [(t_input t, t_output t)]) (V (t_target t)))"
    (is "((L M1 \<inter> set ?TS') = (L M2 \<inter> set ?TS')) \<Longrightarrow> (\<And> t . t \<in> transitions M1 \<Longrightarrow> t_source t \<in> reachable_states M1 \<Longrightarrow> ?P1 t T3 \<and> ?P2 t)")
  proof -
    fix t assume "t \<in> transitions M1" and "t_source t \<in> reachable_states M1" and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"
    then consider "t \<in> sc_covered_transitions" | "t \<in> list.set unverified_transitions"
      unfolding sc_covered_transitions_alt_def unverified_transitions_alt_def
      by blast
    then show "?P1 t T3 \<and> ?P2 t"
    proof cases
      case 1         

      have "(V (t_source t)) \<in> L M1"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>t_source t \<in> reachable_states M1\<close>]
        by auto
      then have p3: "converge M1 (V (t_source t)) (V (t_source t))"
        by auto

      have "(V (t_source t)) \<in> L M2"
        using passes_T1[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] T1_state_cover \<open>t_source t \<in> reachable_states M1\<close> \<open>(V (t_source t)) \<in> L M1\<close>
        by (metis IntI image_subset_iff inf.cobounded1 subsetD)
      then have p4: "converge M2 (V (t_source t)) (V (t_source t))"
        by auto
      
      have "t_target t \<in> reachable_states M1"
        using reachable_states_next[OF \<open>t_source t \<in> reachable_states M1\<close> \<open>t \<in> transitions M1\<close>] 
        by auto
      then have "(V (t_target t)) \<in> L M1"
        using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> ]
        by auto 
      then have p5: "converge M1 (V (t_target t)) (V (t_target t))"
        by auto  

      have "(V (t_target t)) \<in> L M2"
        using passes_T1[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] T1_state_cover \<open>t_target t \<in> reachable_states M1\<close> \<open>(V (t_target t)) \<in> L M1\<close> 
        by blast
      then have p6: "converge M2 (V (t_target t)) (V (t_target t))"
        by auto

      have p8: "(V (t_target t)) \<in> set T3"
        using T3_state_cover \<open>t_target t \<in> reachable_states M1\<close>
        by auto
      then have p7: "(V (t_source t)) @ [(t_input t, t_output t)] \<in> set T3"
        using 1 
        unfolding sc_covered_transitions_alt_def
        by auto

      have "?P2 t"
        using T1_covered_transitions_conv[OF passes_T1[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] 1] 
        by auto
      then show ?thesis
        using p3 p4 p5 p6 p7 p8
        by blast
    next
      case 2

      show ?thesis 
        using T2_cover[OF passes_T2[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] 2] \<open>set T2 \<subseteq> set T3\<close>
        unfolding covers_unverified_transition 
        by blast
    qed
  qed

  have T3_covers_defined_io_pairs : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> q x y q' . q \<in> reachable_states M1 \<Longrightarrow> h_obs M1 q x y = Some q' \<Longrightarrow>
          (\<exists>\<alpha> \<beta>.
            converge M1 \<alpha> (V q) \<and>
            converge M2 \<alpha> (V q) \<and>
            converge M1 \<beta> (V q') \<and>
            converge M2 \<beta> (V q') \<and> 
            \<alpha> @ [(x,y)] \<in> set T3 \<and> 
            \<beta> \<in> set T3)
          \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q'))" 
    (is "((L M1 \<inter> set ?TS') = (L M2 \<inter> set ?TS')) \<Longrightarrow> (\<And> q x y q' . q \<in> reachable_states M1 \<Longrightarrow> h_obs M1 q x y = Some q' \<Longrightarrow> ?P q x y q')")
  proof -
    fix q x y q' assume "q \<in> reachable_states M1" and "h_obs M1 q x y = Some q'" and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"
    then have "(q,x,y,q') \<in> transitions M1" and "t_source (q,x,y,q') \<in> reachable_states M1"
      using h_obs_Some[OF assms(1)] by auto
    moreover have "converge M1 (V q @ [(x,y)]) (V q')" 
      using state_cover_transition_converges[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> calculation]
      by auto
    ultimately show "?P q x y q'"
      using T3_covers_transitions[of "(q,x,y,q')", OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] 
      unfolding fst_conv snd_conv
      by blast
  qed

    


  (* properties of T3 w.r.t. undefined io pairs *)

  have rstates_io_set : "list.set rstates_io = {(q,(x,y)) . q \<in> reachable_states M1 \<and> x \<in> inputs M1 \<and> y \<in> outputs M1}"
    unfolding rstates_io rstates 
    using reachable_states_as_list_set[of M1] inputs_as_list_set[of M1] outputs_as_list_set[of M1] 
    by force
  then have undefined_io_pairs_set : "list.set undefined_io_pairs = {(q,(x,y)) . q \<in> reachable_states M1 \<and> x \<in> inputs M1 \<and> y \<in> outputs M1 \<and> h_obs M1 q x y = None}"
    unfolding undefined_io_pairs 
    by auto

  have verify_undefined_io_pair_prop : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> q x y T . L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y))) \<Longrightarrow> 
                                                    q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow>
                                                    V ` reachable_states M1 \<subseteq> set T \<Longrightarrow>
                                                    \<exists> \<alpha>. converge M1 \<alpha> (V q) \<and> 
                                                         converge M2 \<alpha> (V q) \<and> 
                                                         \<alpha> \<in> set (verify_undefined_io_pair T (q,(x,y))) \<and>
                                                         \<alpha>@[(x,y)] \<in> set (verify_undefined_io_pair T (q,(x,y))))"
  proof -
    fix q x y T
    assume "L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y)))"
       and "q \<in> reachable_states M1" and "x \<in> inputs M1" and "y \<in> outputs M1"
       and "V ` reachable_states M1 \<subseteq> set T"
       and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"

    have " L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1"
      using T3_state_cover \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> Prefix_Tree.set T3 = L M2 \<inter> Prefix_Tree.set T3\<close> \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> 
      by blast

    have "L M1 \<inter> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y))"
      using \<open>L M1 \<inter> set (verify_undefined_io_pair T (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair T (q,(x,y)))\<close>
      unfolding verify_undefined_io_pair case_prod_conv combine_set G2
      by blast


    have "(\<exists>\<alpha>. converge M1 \<alpha> (V q) \<and>
          converge M2 \<alpha> (V q) \<and>
          \<alpha> \<in> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y)) \<and>
          \<alpha> @ [(x, y)] \<in> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y)))"
      using assms(16)
      unfolding verifies_io_pair_def 
      using assms(1-4,7,8) \<open>is_state_cover_assignment M1 V\<close> \<open>L M1 \<inter> V ` reachable_states M1 = L M2 \<inter> V ` reachable_states M1\<close>
            \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>
            G2_invar[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>] \<open>convergence_graph_insert_invar M1 M2 cg_lookup cg_insert\<close>
            \<open>L M1 \<inter> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y)) = L M2 \<inter> set (fst (append_io_pair M1 V T G2 cg_insert cg_lookup q x y))\<close> 
      by blast
    then show "\<exists> \<alpha>. converge M1 \<alpha> (V q) \<and> 
               converge M2 \<alpha> (V q) \<and> 
               \<alpha> \<in> set (verify_undefined_io_pair T (q,(x,y))) \<and>
               \<alpha>@[(x,y)] \<in> set (verify_undefined_io_pair T (q,(x,y)))"
      unfolding verify_undefined_io_pair G2 case_prod_conv combine_set
      by blast
  qed

  have T3_covers_undefined_io_pairs : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> h_obs M1 q x y = None \<Longrightarrow>
          (\<exists> \<alpha> .
               converge M1 \<alpha> (V q) \<and> 
               converge M2 \<alpha> (V q) \<and>
               \<alpha> \<in> set T3\<and>
               \<alpha>@[(x,y)] \<in> set T3))" 
  proof -
    fix q x y assume "q \<in> reachable_states M1" and "x \<in> inputs M1" and "y \<in> outputs M1" and "h_obs M1 q x y = None" and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"

    have "\<And> q x y qxys T . L M1 \<inter> set (foldl verify_undefined_io_pair T qxys) = L M2 \<inter> set (foldl verify_undefined_io_pair T qxys) \<Longrightarrow> (V ` reachable_states M1) \<subseteq> set T \<Longrightarrow> (q,(x,y)) \<in> list.set qxys \<Longrightarrow> list.set qxys \<subseteq> list.set undefined_io_pairs \<Longrightarrow> 
              (\<exists> \<alpha> .
               converge M1 \<alpha> (V q) \<and> 
               converge M2 \<alpha> (V q) \<and>
               \<alpha> \<in> set (foldl verify_undefined_io_pair T qxys)\<and>
               \<alpha>@[(x,y)] \<in> set (foldl verify_undefined_io_pair T qxys))"
      (is "\<And> q x y qxys T . ?P1 qxys T \<Longrightarrow> (V ` reachable_states M1) \<subseteq> set T \<Longrightarrow> (q,(x,y)) \<in> list.set qxys \<Longrightarrow> list.set qxys \<subseteq> list.set undefined_io_pairs \<Longrightarrow> ?P2 q x y qxys T")
    proof -
      fix q x y qxys T
      assume "?P1 qxys T" and "(q,(x,y)) \<in> list.set qxys" and "list.set qxys \<subseteq> list.set undefined_io_pairs" and "(V ` reachable_states M1) \<subseteq> set T"
      then show "?P2 q x y qxys T"
      proof (induction qxys rule: rev_induct)
        case Nil
        then show ?case by auto
      next
        case (snoc a qxys)

        have "set (foldl verify_undefined_io_pair T qxys) \<subseteq> set (foldl verify_undefined_io_pair T (qxys@[a]))"
          using verify_undefined_io_pair_retains_testsuite 
          by auto
        then have *:"L M1 \<inter> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys) = L M2 \<inter> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys)"
          using snoc.prems(1)
          by blast

        have **: "V ` reachable_states M1 \<subseteq> Prefix_Tree.set (foldl verify_undefined_io_pair T qxys)"
          using snoc.prems(4) verify_undefined_io_pair_folding_retains_testsuite
          by blast

        show ?case proof (cases "a = (q,(x,y))")
          case True
          then have ***: "q \<in> reachable_states M1"
            using snoc.prems(3) 
            unfolding undefined_io_pairs_set
            by auto 

          have "x \<in> inputs M1" and "y \<in> outputs M1"
            using snoc.prems(2,3) unfolding undefined_io_pairs_set by auto

          have ****: "L M1 \<inter> set (verify_undefined_io_pair (foldl verify_undefined_io_pair T qxys) (q,(x,y))) = L M2 \<inter> set (verify_undefined_io_pair (foldl verify_undefined_io_pair T qxys) (q,(x,y)))"
            using snoc.prems(1) unfolding True by auto
            
          show ?thesis
            using verify_undefined_io_pair_prop[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> **** *** \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> **]
            unfolding True 
            by auto
        next
          case False
          then have "(q, x, y) \<in> list.set qxys" and "list.set qxys \<subseteq> list.set undefined_io_pairs"
            using snoc.prems(2,3) by auto
          then show ?thesis 
            using snoc.IH[OF * _ _  snoc.prems(4)]
            using \<open>set (foldl verify_undefined_io_pair T qxys) \<subseteq> set (foldl verify_undefined_io_pair T (qxys@[a]))\<close>
            by blast
        qed
      qed
    qed
    moreover have "L M1 \<inter> set (foldl verify_undefined_io_pair T2 undefined_io_pairs) = L M2 \<inter> set (foldl verify_undefined_io_pair T2 undefined_io_pairs)"
      using \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3\<close>  \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close>
      unfolding T3 T2 .
    moreover have "(V ` reachable_states M1) \<subseteq> set T2"
      using T1_state_cover T2 T2_invar_1 passes_T2 by fastforce
    moreover have "(q,(x,y)) \<in> list.set undefined_io_pairs"
      unfolding undefined_io_pairs_set
      using \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close> \<open>h_obs M1 q x y = None\<close>
      by blast
    ultimately show "(\<exists> \<alpha> .
               converge M1 \<alpha> (V q) \<and> 
               converge M2 \<alpha> (V q) \<and>
               \<alpha> \<in> set T3\<and>
               \<alpha>@[(x,y)] \<in> set T3)"
      unfolding T3 T2 
      by blast
  qed

  (* obtain the transition cover contained in the test suite 
      - this is the set of witnesses for the convergence of all transitions
        and the set of transitions added to cover undefined io 
  *)

  define TCfun where TCfun: "TCfun = (\<lambda> (q,(x,y)) . case h_obs M1 q x y of 
                                None \<Rightarrow> {{\<alpha>, \<alpha>@[(x,y)]} | \<alpha> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> \<alpha> \<in> set T3 \<and> \<alpha>@[(x,y)] \<in> set T3} |
                                Some q' \<Rightarrow> {{\<alpha>,\<alpha>@[(x,y)], \<beta>} | \<alpha> \<beta> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> converge M1 \<beta> (V q') \<and> converge M2 \<beta> (V q') \<and> \<alpha> @ [(x,y)] \<in> set T3 \<and> \<beta> \<in> set T3 \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q')})"
  define TC where TC: "TC = Set.insert [] (\<Union>(\<Union> (TCfun ` (reachable_states M1 \<times> (inputs M1 \<times> outputs M1)))))"


  (* establish that this transition cover is sufficient to prove equivalence by showing that it is
    - initialised 
    - a proper transition cover
    - convergence preserving
  *)


  have TCfun_nonempty: "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> (\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> TCfun (q,(x,y)) \<noteq> {})"
  proof -
    fix q x y assume *:"q \<in> reachable_states M1" and **:"x \<in> inputs M1" and ***:"y \<in> outputs M1" and "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"

    show "TCfun (q,(x,y)) \<noteq> {}"
    proof (cases "h_obs M1 q x y")
      case None
      then have "TCfun (q,(x,y)) = {{\<alpha>, \<alpha> @ [(x, y)]} |\<alpha>. converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> \<alpha> \<in> set T3 \<and> \<alpha> @ [(x, y)] \<in> set T3}"
        unfolding TCfun by auto
      moreover have "{{\<alpha>, \<alpha> @ [(x, y)]} |\<alpha>. converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> \<alpha> \<in> set T3 \<and> \<alpha> @ [(x, y)] \<in> set T3} \<noteq> {}"
        using T3_covers_undefined_io_pairs[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> * ** *** None]
        by blast
      ultimately show ?thesis 
        by blast 
    next
      case (Some q')
      then have "TCfun (q,(x,y)) = {{\<alpha>,\<alpha>@[(x,y)], \<beta>} | \<alpha> \<beta> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> converge M1 \<beta> (V q') \<and> converge M2 \<beta> (V q') \<and> \<alpha> @ [(x,y)] \<in> set T3 \<and> \<beta> \<in> set T3 \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q')}"
        using TCfun by auto
      moreover have "{{\<alpha>,\<alpha>@[(x,y)], \<beta>} | \<alpha> \<beta> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> converge M1 \<beta> (V q') \<and> converge M2 \<beta> (V q') \<and> \<alpha> @ [(x,y)] \<in> set T3 \<and> \<beta> \<in> set T3 \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q')} \<noteq> {}"
        using T3_covers_defined_io_pairs[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> * Some]
        by blast
      ultimately show ?thesis 
        by blast 
    qed
  qed

  have TC_in_T3: "TC \<subseteq> set T3"
  proof
    fix \<alpha> assume "\<alpha> \<in> TC"
    show "\<alpha> \<in> set T3"
    proof (cases "\<alpha> = []")
      case True
      then show ?thesis 
        using T3_state_cover \<open>is_state_cover_assignment M1 V\<close> reachable_states_initial[of M1]
        by auto
    next
      case False
      then obtain q x y where "q \<in> reachable_states M1"
                        and "x \<in> inputs M1"
                        and "y \<in> outputs M1"
                        and "\<alpha> \<in> \<Union> (TCfun (q,(x,y)))"
        using \<open>\<alpha> \<in> TC\<close> unfolding TC 
        by auto

      show "\<alpha> \<in> set T3"
        using \<open>\<alpha> \<in> \<Union> (TCfun (q,(x,y)))\<close> set_prefix[of "\<alpha>" "[(x,y)]" T3] unfolding TCfun 
        by (cases "h_obs M1 q x y";auto)
    qed
  qed

    

  have TC_is_transition_cover : "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> transition_cover M1 TC"
  proof -
    assume "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))"

    have "\<And> q x y . q \<in> reachable_states M1 \<Longrightarrow> x \<in> inputs M1 \<Longrightarrow> y \<in> outputs M1 \<Longrightarrow> \<exists>\<alpha>. \<alpha> \<in> TC \<and> \<alpha> @ [(x, y)] \<in> TC \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
    proof -
      fix q x y assume "q \<in> reachable_states M1"
                   and "x \<in> inputs M1"
                   and "y \<in> outputs M1"
      then have "(q,(x,y)) \<in> (reachable_states M1 \<times> FSM.inputs M1 \<times> FSM.outputs M1)"
        by blast

      show "\<exists>\<alpha>. \<alpha> \<in> TC \<and> \<alpha> @ [(x, y)] \<in> TC \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
      proof (cases "h_obs M1 q x y")
        case None
        then have "TCfun (q,(x,y)) = {{\<alpha>, \<alpha> @ [(x, y)]} |\<alpha>. converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> \<alpha> \<in> set T3 \<and> \<alpha> @ [(x, y)] \<in> set T3}"
          unfolding TCfun by auto
        then obtain \<alpha> where "converge M1 \<alpha> (V q)" and "\<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y)))"
          using TCfun_nonempty[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>]
          by auto
        then have "after_initial M1 \<alpha> = q"
          using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>q \<in> reachable_states M1\<close>]
          using convergence_minimal[OF assms(3,1)]
          by (metis converge.elims(2))
        then have "\<exists>\<alpha>. \<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
          using \<open>\<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y)))\<close>
          using \<open>converge M1 \<alpha> (V q)\<close> converge.elims(2) by blast
        moreover have "\<Union> (TCfun (q,(x,y))) \<subseteq> TC"
          unfolding TC using \<open>(q,(x,y)) \<in> (reachable_states M1 \<times> FSM.inputs M1 \<times> FSM.outputs M1)\<close>
          by blast
        ultimately show ?thesis              
          by blast
      next
        case (Some q')
        then have "TCfun (q,(x,y)) = {{\<alpha>,\<alpha>@[(x,y)], \<beta>} | \<alpha> \<beta> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> converge M1 \<beta> (V q') \<and> converge M2 \<beta> (V q') \<and> \<alpha> @ [(x,y)] \<in> set T3 \<and> \<beta> \<in> set T3 \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q')}"
          using TCfun 
          by auto
        moreover obtain S where "S \<in> TCfun (q,(x,y))"
          using TCfun_nonempty[OF \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS))\<close> \<open>q \<in> reachable_states M1\<close> \<open>x \<in> inputs M1\<close> \<open>y \<in> outputs M1\<close>]
          by blast
        ultimately obtain \<alpha> where "converge M1 \<alpha> (V q)" and "\<alpha> \<in> S \<and> \<alpha> @ [(x, y)] \<in> S"
          by auto 
        then have "after_initial M1 \<alpha> = q"
          using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>q \<in> reachable_states M1\<close>]
          using convergence_minimal[OF assms(3,1)]
          by (metis converge.elims(2))
        moreover have "\<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y)))"
          using \<open>\<alpha> \<in> S \<and> \<alpha> @ [(x, y)] \<in> S\<close> \<open>S \<in> TCfun (q,(x,y))\<close>
          by auto
        ultimately have "\<exists>\<alpha>. \<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> \<in> L M1 \<and> after_initial M1 \<alpha> = q"
          using \<open>\<alpha> \<in> \<Union> (TCfun (q,(x,y))) \<and> \<alpha> @ [(x, y)] \<in> \<Union> (TCfun (q,(x,y)))\<close>
          using \<open>converge M1 \<alpha> (V q)\<close> converge.elims(2) by blast
        moreover have "\<Union> (TCfun (q,(x,y))) \<subseteq> TC"
          unfolding TC using \<open>(q,(x,y)) \<in> (reachable_states M1 \<times> FSM.inputs M1 \<times> FSM.outputs M1)\<close>
          by blast
        ultimately show ?thesis              
          by blast
      qed
    qed
    then show ?thesis
      unfolding transition_cover_def 
      by blast
  qed

  have TC_preserves_convergence: "preserves_convergence M1 M2 TC"
  proof -
    have "\<And> \<alpha> \<beta> . \<alpha> \<in> L M1 \<inter> TC \<Longrightarrow> \<beta> \<in> L M1 \<inter> TC \<Longrightarrow> converge M1 \<alpha> \<beta> \<Longrightarrow> converge M2 \<alpha> \<beta>"
    proof -
      fix \<alpha> \<beta> assume "\<alpha> \<in> L M1 \<inter> TC" 
                     "\<beta> \<in> L M1 \<inter> TC" 
                     "converge M1 \<alpha> \<beta>"

      have *: "\<And> \<alpha> . \<alpha> \<in> L M1 \<Longrightarrow> \<alpha> \<in> TC \<Longrightarrow> \<exists> q . q \<in> reachable_states M1 \<and> converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q)"
      proof -
        fix \<alpha> assume "\<alpha> \<in> L M1" and "\<alpha> \<in> TC"

        show "\<exists> q . q \<in> reachable_states M1 \<and> converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q)"
        proof (cases "\<alpha> = []")
          case True

          then have "V (initial M1) = \<alpha>"
            using \<open>is_state_cover_assignment M1 V\<close> reachable_states_initial[of M1]
            by auto
          then have "converge M1 \<alpha> (V (initial M1))" and "converge M2 \<alpha> (V (initial M1))"
            unfolding True by auto
          then show ?thesis
            using reachable_states_initial[of M1]
            by auto
        next
          case False
          then have "\<alpha> \<in> (\<Union>(\<Union> (TCfun ` (reachable_states M1 \<times> (inputs M1 \<times> outputs M1)))))"
            using \<open>\<alpha> \<in> TC\<close>
            unfolding TC
            by blast
          then obtain q x y where "q \<in> reachable_states M1"
                              and "x \<in> inputs M1"
                              and "y \<in> outputs M1"
                              and "\<alpha> \<in> \<Union> (TCfun (q,(x,y)))"
            unfolding TC by auto

          show "\<exists> q . q \<in> reachable_states M1 \<and> converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q)"
          proof (cases "h_obs M1 q x y")
            case None
            then have "TCfun (q,(x,y)) = {{\<alpha>, \<alpha> @ [(x, y)]} |\<alpha>. converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> \<alpha> \<in> set T3 \<and> \<alpha> @ [(x, y)] \<in> set T3}"
              unfolding TCfun by auto
            then obtain \<alpha>' where "\<alpha> \<in> {\<alpha>', \<alpha>' @ [(x, y)]}"
                             and "converge M1 \<alpha>' (V q)"
                             and "converge M2 \<alpha>' (V q)"
              using \<open>\<alpha> \<in> \<Union> (TCfun (q,(x,y)))\<close> 
              by auto

            have "[(x,y)] \<notin> LS M1 q"
              using None unfolding h_obs_None[OF assms(1)] LS_single_transition 
              by auto
            moreover have "after_initial M1 \<alpha>' = q"
              using \<open>converge M1 \<alpha>' (V q)\<close> 
              using state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>q \<in> reachable_states M1\<close>]
              using convergence_minimal[OF assms(3,1) _ _]
              by (metis converge.elims(2))
            ultimately have "\<alpha>' @ [(x, y)] \<notin> L M1"
              using after_language_iff[OF assms(1), of \<alpha>' "initial M1" "[(x,y)]"]  \<open>converge M1 \<alpha>' (V q)\<close>
              by (meson converge.elims(2)) 
            then have "\<alpha>' = \<alpha>"
              using \<open>\<alpha> \<in> {\<alpha>', \<alpha>' @ [(x, y)]}\<close> \<open>\<alpha> \<in> L M1\<close>
              by blast
            then show ?thesis 
              using \<open>q \<in> reachable_states M1\<close> \<open>converge M1 \<alpha>' (V q)\<close> \<open>converge M2 \<alpha>' (V q)\<close>
              by blast
          next
            case (Some q')
            then have "q' \<in> reachable_states M1"
                unfolding h_obs_Some[OF assms(1)]
                using reachable_states_next[OF \<open>q \<in> reachable_states M1\<close>, of "(q,x,y,q')"]
                by auto

            have "TCfun (q,(x,y)) = {{\<alpha>,\<alpha>@[(x,y)], \<beta>} | \<alpha> \<beta> . converge M1 \<alpha> (V q) \<and> converge M2 \<alpha> (V q) \<and> converge M1 \<beta> (V q') \<and> converge M2 \<beta> (V q') \<and> \<alpha> @ [(x,y)] \<in> set T3 \<and> \<beta> \<in> set T3 \<and> converge M1 (V q @ [(x,y)]) (V q') \<and> converge M2 (V q @ [(x,y)]) (V q')}"
              using Some TCfun 
              by auto
            then obtain \<alpha>' \<beta> where "\<alpha> \<in> {\<alpha>',\<alpha>'@[(x,y)], \<beta>}"
                               and "converge M1 \<alpha>' (V q)"
                               and "converge M2 \<alpha>' (V q)"
                               and "converge M1 \<beta> (V q')"
                               and "converge M2 \<beta> (V q')"
                               and "converge M1 (V q @ [(x,y)]) (V q')"
                               and "converge M2 (V q @ [(x,y)]) (V q')"
              using \<open>\<alpha> \<in> \<Union> (TCfun (q,(x,y)))\<close> 
              by auto

            then consider "\<alpha> = \<alpha>'" | "\<alpha> = \<alpha>'@[(x,y)]" | "\<alpha> = \<beta>"
              by blast
            then show ?thesis proof cases
              case 1
              then show ?thesis 
                using \<open>q \<in> reachable_states M1\<close> \<open>converge M1 \<alpha>' (V q)\<close> \<open>converge M2 \<alpha>' (V q)\<close>
                by blast
            next
              case 2

              have "converge M1 (\<alpha>'@[(x,y)]) (V q @ [(x,y)])"
                using \<open>converge M1 \<alpha>' (V q)\<close>  \<open>converge M1 (V q @ [(x,y)]) (V q')\<close>
                using converge_append[OF assms(1), of "V q" \<alpha>' "[(x,y)]"]
                by auto
              then have "converge M1 (\<alpha>'@[(x,y)]) (V q')"
                using \<open>converge M1 \<beta> (V q')\<close> \<open>converge M1 (V q @ [(x,y)]) (V q')\<close>
                by auto

              have "converge M2 (\<alpha>'@[(x,y)]) (V q @ [(x,y)])"
                using \<open>converge M2 \<alpha>' (V q)\<close>  \<open>converge M2 (V q @ [(x,y)]) (V q')\<close>
                using converge_append[OF assms(2), of "V q" \<alpha>' "[(x,y)]"]
                by auto
              then have "converge M2 (\<alpha>'@[(x,y)]) (V q')"
                using \<open>converge M2 \<beta> (V q')\<close> \<open>converge M2 (V q @ [(x,y)]) (V q')\<close>
                by auto
                
              show ?thesis
                using 2 \<open>q' \<in> reachable_states M1\<close> \<open>converge M1 (\<alpha>'@[(x,y)]) (V q')\<close> \<open>converge M2 (\<alpha>'@[(x,y)]) (V q')\<close>
                by auto
            next
              case 3
              then show ?thesis 
                using \<open>converge M1 \<beta> (V q')\<close> \<open>converge M2 \<beta> (V q')\<close> \<open>q' \<in> reachable_states M1\<close>
                by blast
            qed
          qed
        qed
      qed

      obtain q where "q \<in> reachable_states M1" and "converge M1 \<alpha> (V q)" and "converge M2 \<alpha> (V q)"
        using * \<open>\<alpha> \<in> L M1 \<inter> TC\<close>
        by blast

      obtain q' where "q' \<in> reachable_states M1" and "converge M1 \<beta> (V q')" and "converge M2 \<beta> (V q')"
        using * \<open>\<beta> \<in> L M1 \<inter> TC\<close>
        by blast

      have "converge M1 (V q) (V q')"
        using \<open>converge M1 \<alpha> (V q)\<close> \<open>converge M1 \<beta> (V q')\<close> \<open>converge M1 \<alpha> \<beta>\<close>
        by auto
      then have "q = q'"
        using convergence_minimal[OF assms(3,1), of "V q" "V q'"]
        unfolding state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>q \<in> reachable_states M1\<close>]
                  state_cover_assignment_after[OF assms(1) \<open>is_state_cover_assignment M1 V\<close> \<open>q' \<in> reachable_states M1\<close>]
        by auto
      then have "V q = V q'"
        by auto
      then show "converge M2 \<alpha> \<beta>"
        using \<open>converge M2 \<alpha> (V q)\<close> \<open>converge M2 \<beta> (V q')\<close>
        by auto
    qed

    then show ?thesis
      unfolding preserves_convergence.simps
      by blast
  qed

  have "[] \<in> TC"
    unfolding TC by blast
    
  show "((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 = L M2"
    using initialised_convergence_preserving_transition_cover_is_complete[OF assms(1-4,7,8) 
                                                                             \<open>((L M1 \<inter> set ?TS) = (L M2 \<inter> set ?TS)) \<Longrightarrow> L M1 \<inter> set T3 = L M2 \<inter> set T3\<close> 
                                                                             TC_in_T3 
                                                                             TC_is_transition_cover 
                                                                             \<open>[] \<in> TC\<close> 
                                                                             TC_preserves_convergence]
    by assumption

    
  show "finite_tree ?TS"
    using T2 T2_finite T3 verify_undefined_io_pair_folding_retains_finiteness 
    by (simp add: \<open>?TS = T3\<close>)
qed

end