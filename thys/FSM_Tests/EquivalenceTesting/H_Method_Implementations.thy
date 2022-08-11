section \<open>Implementations of the H-Method\<close>

theory H_Method_Implementations
imports Intermediate_Frameworks Pair_Framework "../Distinguishability" Test_Suite_Representations "../OFSM_Tables_Refined" "HOL-Library.List_Lexorder"
begin

subsection \<open>Using the H-Framework\<close>

definition h_method_via_h_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "h_method_via_h_framework = h_framework_dynamic (\<lambda> M V t X l . False)"

definition h_method_via_h_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "h_method_via_h_framework_lists M m completeInputTraces useInputHeuristic = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (h_method_via_h_framework M m completeInputTraces useInputHeuristic))"

lemma h_method_via_h_framework_completeness_and_finiteness :
  fixes M1 :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  fixes M2 :: "('e,'b,'c) fsm"
  assumes "observable M1"
  and     "observable M2"
  and     "minimal M1"
  and     "minimal M2"
  and     "size_r M1 \<le> m"
  and     "size M2 \<le> m"
  and     "inputs M2 = inputs M1"
  and     "outputs M2 = outputs M1"
shows "(L M1 = L M2) \<longleftrightarrow> ((L M1 \<inter> set (h_method_via_h_framework M1 m completeInputTraces useInputHeuristic)) = (L M2 \<inter> set (h_method_via_h_framework M1 m completeInputTraces useInputHeuristic)))"
and "finite_tree (h_method_via_h_framework M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_completeness_and_finiteness[OF assms]
  unfolding h_method_via_h_framework_def 
  by blast+

lemma h_method_via_h_framework_lists_completeness :
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
shows "(L M1 = L M2) \<longleftrightarrow> list_all (passes_test_case M2 (initial M2)) (h_method_via_h_framework_lists M1 m completeInputTraces useInputHeuristic)"
  using h_framework_dynamic_lists_completeness[OF assms]
  unfolding h_method_via_h_framework_lists_def h_framework_dynamic_lists_def h_method_via_h_framework_def
  by blast



subsection \<open>Using the Pair-Framework\<close>

subsubsection \<open>Selection of Distinguishing Traces\<close>

fun add_distinguishing_sequence_if_required :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> ('a,'b::linorder,'c::linorder) fsm \<Rightarrow> (('b\<times>'c) list \<times> 'a) \<times> (('b\<times>'c) list \<times> 'a) \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_distinguishing_sequence_if_required dist_fun M ((\<alpha>,q1), (\<beta>,q2)) t = (if intersection_is_distinguishing M (after t \<alpha>) q1 (after t \<beta>) q2
    then empty
    else insert empty (dist_fun q1 q2))"

lemma add_distinguishing_sequence_if_required_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>" 
  and     "\<And> q1 q2 . q1 \<in> states M \<Longrightarrow> q2 \<in> states M \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M q1 q2 (dist_fun q1 q2)"
shows "\<exists> io \<in> set ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
proof (cases "intersection_is_distinguishing M (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)")
  case True
  then have "(add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t = empty"
    by auto
  then have "set ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) = (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    using Prefix_Tree.set_empty
    by (metis Int_insert_right inf.absorb_iff2 inf_bot_right insert_is_Un set_Nil sup_absorb2) 
  moreover have "\<exists> io \<in> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
    using True unfolding intersection_is_distinguishing_correctness[OF assms(1) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)]]
    by auto 
  ultimately show ?thesis 
    by blast
next
  case False
  then have "set ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = set (insert empty (dist_fun (after_initial M \<alpha>) (after_initial M \<beta>)))"
    by auto
  then have "dist_fun (after_initial M \<alpha>) (after_initial M \<beta>) \<in> set ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    unfolding insert_set by auto
  then show ?thesis 
    using assms(6)[OF after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5)] by blast
qed

lemma add_distinguishing_sequence_if_required_finite : 
  "finite_tree ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
proof (cases "intersection_is_distinguishing M (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)")
  case True
  then have "((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = empty"
    by auto
  then show ?thesis
    using empty_finite_tree by simp
next
  case False
  then have "((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = (insert empty (dist_fun (after_initial M \<alpha>) (after_initial M \<beta>)))"
    by auto
  then show ?thesis
    using insert_finite_tree[OF empty_finite_tree] by metis
qed

fun add_distinguishing_sequence_and_complete_if_required :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> bool \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> (('b\<times>'c) list \<times> 'a) \<times> (('b\<times>'c) list \<times> 'a) \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_distinguishing_sequence_and_complete_if_required distFun completeInputTraces M ((\<alpha>,q1), (\<beta>,q2)) t = 
    (if intersection_is_distinguishing M (after t \<alpha>) q1 (after t \<beta>) q2
      then empty
      else let w = distFun q1 q2;
               T = insert empty w
            in if completeInputTraces 
              then let T1 = from_list (language_for_input M q1 (map fst w));
                       T2 = from_list (language_for_input M q2 (map fst w))
                   in Prefix_Tree.combine T (Prefix_Tree.combine T1 T2)
              else T)" 

lemma add_distinguishing_sequence_and_complete_if_required_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>" 
  and     "\<And> q1 q2 . q1 \<in> states M \<Longrightarrow> q2 \<in> states M \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M q1 q2 (dist_fun q1 q2)"
shows "\<exists> io \<in> set ((add_distinguishing_sequence_and_complete_if_required dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
proof (cases "intersection_is_distinguishing M (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)")
  case True
  then have "(add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t = empty"
    by auto
  then have "set ((add_distinguishing_sequence_if_required dist_fun M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) = (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    using Prefix_Tree.set_empty
    by (metis Int_insert_right inf.absorb_iff2 inf_bot_right insert_is_Un set_Nil sup_absorb2) 
  moreover have "\<exists> io \<in> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
    using True unfolding intersection_is_distinguishing_correctness[OF assms(1) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)]]
    by auto 
  ultimately show ?thesis 
    by blast
next
  case False
  then have "set (insert empty (dist_fun (after_initial M \<alpha>) (after_initial M \<beta>))) \<subseteq> set ((add_distinguishing_sequence_and_complete_if_required dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
    using combine_set[of "insert empty (dist_fun (after_initial M \<alpha>) (after_initial M \<beta>))"] 
    unfolding add_distinguishing_sequence_and_complete_if_required.simps Let_def 
    by (cases c; fastforce)
  moreover have "dist_fun (after_initial M \<alpha>) (after_initial M \<beta>) \<in> set (insert empty (dist_fun (after_initial M \<alpha>) (after_initial M \<beta>)))"
    unfolding insert_set by auto
  ultimately have "dist_fun (after_initial M \<alpha>) (after_initial M \<beta>) \<in> set ((add_distinguishing_sequence_and_complete_if_required dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    by blast
  then show ?thesis 
    using assms(6)[OF after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5)] 
    by (meson distinguishes_def) 
qed

lemma add_distinguishing_sequence_and_complete_if_required_finite : 
  "finite_tree ((add_distinguishing_sequence_and_complete_if_required dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
proof (cases "intersection_is_distinguishing M (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)")
  case True
  then have "((add_distinguishing_sequence_and_complete_if_required dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) = empty"
    by auto
  then show ?thesis
    using empty_finite_tree by simp
next
  case False

  define w where w: "w = dist_fun (after_initial M \<alpha>) (after_initial M \<beta>)"
  define T where T: "T = insert empty w"
  define T1 where T1: "T1 = from_list (language_for_input M (after_initial M \<alpha>) (map fst w))"
  define T2 where T2: "T2 = from_list (language_for_input M (after_initial M \<beta>) (map fst w))"

  have "finite_tree T"
    using insert_finite_tree[OF empty_finite_tree]
    unfolding T by auto
  moreover have "finite_tree (Prefix_Tree.combine T (Prefix_Tree.combine T1 T2))"
    using combine_finite_tree[OF \<open>finite_tree T\<close> combine_finite_tree[OF from_list_finite_tree from_list_finite_tree]]
    unfolding T1 T2
    by auto
  ultimately show ?thesis
    using False
    unfolding add_distinguishing_sequence_and_complete_if_required.simps w T T1 T2 Let_def
    by presburger
qed




function find_cheapest_distinguishing_trace :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> ('b\<times>'c) list \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'a \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> 'a \<Rightarrow> (('b\<times>'c) list \<times> nat \<times> nat)" where
  "find_cheapest_distinguishing_trace M distFun ios (PT m1) q1 (PT m2) q2 = 
    (let
      f = (\<lambda> (\<omega>,l,w) (x,y) . if (x,y) \<notin> list.set ios then (\<omega>,l,w) else  
            (let 
              w1L = if (PT m1) = empty then 0 else 1;
              w1C = if (x,y) \<in> dom m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if (PT m2) = empty then 0 else 1;
              w2C = if (x,y) \<in> dom m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in 
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2' 
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' 
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))
     in 
       foldl f (distFun q1 q2, 0, 3) ios)"
  by pat_completeness auto
termination   
proof -

  let ?f = "(\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"

  have "\<And>(M::('a,'b::linorder,'c::linorder) fsm) 
          (distFun :: ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)) 
          (ios :: ('b\<times>'c) list)
           m1 (q1::'a) m2 (q2::'a) x y t2' q1' q2'.
       \<not> (x, y) \<notin> list.set ios \<Longrightarrow>
       m1 (x, y) = None \<Longrightarrow>
       m2 (x, y) = Some t2' \<Longrightarrow>
       ((M, distFun, ios, Prefix_Tree.empty, q1', t2', q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
  proof -
    fix M::"('a,'b::linorder,'c::linorder) fsm" 
    fix distFun :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)"
    fix ios :: "('b\<times>'c) list"
    fix m1 m2 :: "('b\<times>'c) \<rightharpoonup> ('b\<times>'c) prefix_tree"
    fix t2'
    fix q1 q2 q1' q2' :: 'a
    fix x 
    fix y 

    assume "m1 (x, y) = None"
    assume "m2 (x, y) = Some t2'"
    assume "\<not> (x, y) \<notin> list.set ios"

    define pre where "pre = (M, distFun, ios, PT m1, q1, PT m2, q2)"
    define post where "post = (M, distFun, ios, Prefix_Tree.empty::('b\<times>'c) prefix_tree, q1', t2', q2')"

    have "height_over ios empty \<le> height_over ios (PT m1)"
      unfolding height_over.simps height_over_empty by auto
    then have "?f post < ?f pre" 
      unfolding pre_def post_def case_prod_conv
      by (meson \<open>\<not> (x, y) \<notin> list.set ios\<close> \<open>m2 (x, y) = Some t2'\<close> add_le_less_mono height_over_subtree_less) 
    then show "((M, distFun, ios, Prefix_Tree.empty, q1', t2', q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
      unfolding pre_def[symmetric] post_def[symmetric]
      by simp 
  qed

  moreover have "\<And>(M::('a,'b::linorder,'c::linorder) fsm) 
          (distFun :: ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)) 
          (ios :: ('b\<times>'c) list)
           m1 (q1::'a) m2 (q2::'a) x y t1' q1' q2'.
       \<not> (x, y) \<notin> list.set ios \<Longrightarrow>
       m1 (x, y) = Some t1' \<Longrightarrow>
       m2 (x, y) = None \<Longrightarrow>
       ((M, distFun, ios, t1', q1', empty, q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
  proof -
    fix M::"('a,'b::linorder,'c::linorder) fsm" 
    fix distFun :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)"
    fix ios :: "('b\<times>'c) list"
    fix m1 m2 :: "('b\<times>'c) \<rightharpoonup> ('b\<times>'c) prefix_tree"
    fix t1'
    fix q1 q2 q1' q2' :: 'a
    fix x :: 'b
    fix y :: 'c

    assume "m1 (x, y) = Some t1'"
    assume "m2 (x, y) = None"
    assume "\<not> (x, y) \<notin> list.set ios"


    define pre where "pre = (M, distFun, ios, PT m1, q1, PT m2, q2)"
    define post where "post = (M, distFun, ios, t1', q1',  Prefix_Tree.empty::('b\<times>'c) prefix_tree, q2')"

    have "height_over ios empty \<le> height_over ios (PT m2)"
      unfolding height_over.simps height_over_empty by auto
    then have "?f post < ?f pre" 
      unfolding pre_def post_def case_prod_conv
      by (meson \<open>\<not> (x, y) \<notin> list.set ios\<close> \<open>m1 (x, y) = Some t1'\<close> add_mono_thms_linordered_field(3) height_over_subtree_less)
    then show "((M, distFun, ios, t1', q1', Prefix_Tree.empty, q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
      unfolding pre_def[symmetric] post_def[symmetric]
      by simp 
  qed


  moreover have "\<And>(M::('a,'b::linorder,'c::linorder) fsm) 
          (distFun :: ('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)) 
          (ios :: ('b\<times>'c) list)
           m1 (q1::'a) m2 (q2::'a) x y t1' t2' q1' q2'.
       \<not> (x, y) \<notin> list.set ios \<Longrightarrow>
       m1 (x, y) = Some t1' \<Longrightarrow>
       m2 (x, y) = Some t2' \<Longrightarrow>
       ((M, distFun, ios, t1', q1', t2', q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
  proof -
    fix M::"('a,'b::linorder,'c::linorder) fsm" 
    fix distFun :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list)"
    fix ios :: "('b\<times>'c) list"
    fix m1 m2 :: "('b\<times>'c) \<rightharpoonup> ('b\<times>'c) prefix_tree"
    fix t1' t2' :: "('b\<times>'c) prefix_tree"
    fix q1 q2 q1' q2' :: 'a
    fix x :: 'b
    fix y :: 'c

    define pre where "pre = (M, distFun, ios, PT m1, q1, PT m2, q2)"
    define post where "post = (M, distFun, ios, t1', q1', t2', q2')"

    assume "m1 (x, y) = Some t1'"
    moreover assume "m2 (x, y) = Some t2'"
    moreover assume "\<not> (x, y) \<notin> list.set ios"
    ultimately have "?f post < ?f pre" 
      unfolding pre_def post_def case_prod_conv
      by (meson add_less_mono height_over_subtree_less)
    then show "((M, distFun, ios, t1', q1',t2', q2'), M, distFun, ios,
        PT m1, q1, PT m2, q2)
       \<in> measure (\<lambda>(M, dF, ios, t1, q1, t2, q2). height_over ios t1 + height_over ios t2)"
      unfolding pre_def[symmetric] post_def[symmetric]
      by simp 
  qed

  ultimately show ?thesis
    by (relation "measure (\<lambda> (M,dF,ios,t1,q1,t2,q2) . height_over ios t1 + height_over ios t2)"; simp)
qed




(* removes the elem-check on (x,y) and ios *)
lemma find_cheapest_distinguishing_trace_alt_def :
  "find_cheapest_distinguishing_trace M distFun ios (PT m1) q1 (PT m2) q2 = 
    (let
      f = (\<lambda> (\<omega>,l,w) (x,y). 
            (let 
              w1L = if (PT m1) = empty then 0 else 1;
              w1C = if (x,y) \<in> dom m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if (PT m2) = empty then 0 else 1;
              w2C = if (x,y) \<in> dom m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in  
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2' 
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2'  
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))
     in 
       foldl f (distFun q1 q2, 0, 3) ios)"
  (is "find_cheapest_distinguishing_trace M distFun ios (PT m1) q1 (PT m2) q2 = ?find_cheapest_distinguishing_trace")

proof -
  define f' where "f' = (\<lambda> (\<omega>,l,w) (x,y) . 
            (let 
              w1L = if (PT m1) = empty then 0 else 1;
              w1C = if (x,y) \<in> dom m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if (PT m2) = empty then 0 else 1;
              w2C = if (x,y) \<in> dom m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in  
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' 
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))"

  define f where "f = (\<lambda> (\<omega>,l,w) (x,y) . if (x,y) \<notin> list.set ios then (\<omega>,l,w) else  
            (let 
              w1L = if (PT m1) = empty then 0 else 1;
              w1C = if (x,y) \<in> dom m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if (PT m2) = empty then 0 else 1;
              w2C = if (x,y) \<in> dom m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in 
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2'
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2'
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))"
  then have "f = (\<lambda> y x . if x \<notin> list.set ios then y else f' y x)"
    unfolding f'_def by fast
  moreover have "find_cheapest_distinguishing_trace M distFun ios (PT m1) q1 (PT m2) q2 = foldl f (distFun q1 q2, 0, 3) ios"
    unfolding find_cheapest_distinguishing_trace.simps f_def[symmetric] by auto
  ultimately have "find_cheapest_distinguishing_trace M distFun ios (PT m1) q1 (PT m2) q2 = foldl (\<lambda> y x . if x \<notin> list.set ios then y else f' y x) (distFun q1 q2, 0, 3) ios"
    by auto
  then show ?thesis
    unfolding f'_def[symmetric]  
    using foldl_elem_check[of ios "list.set ios"]
    by auto
qed


lemma find_cheapest_distinguishing_trace_code[code] :
  "find_cheapest_distinguishing_trace M distFun ios (MPT m1) q1 (MPT m2) q2 = 
    (let
      f = (\<lambda> (\<omega>,l,w) (x,y) . 
            (let 
              w1L = if is_leaf (MPT m1) then 0 else 1;
              w1C = if (x,y) \<in> Mapping.keys m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if is_leaf (MPT m2) then 0 else 1;
              w2C = if(x,y) \<in> Mapping.keys m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in  
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case Mapping.lookup m1 (x,y) of
                      None \<Rightarrow> (case Mapping.lookup m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2' 
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case Mapping.lookup m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2'  
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))
     in 
       foldl f (distFun q1 q2, 0, 3) ios)"
  unfolding find_cheapest_distinguishing_trace_alt_def MPT_def
  by (simp add: keys_dom_lookup) 



lemma find_cheapest_distinguishing_trace_is_distinguishing_trace :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M" 
  and     "q1 \<noteq> q2"   
  and     "\<And> q1 q2 . q1 \<in> states M \<Longrightarrow> q2 \<in> states M \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M q1 q2 (distFun q1 q2)"
shows "distinguishes M q1 q2 (fst (find_cheapest_distinguishing_trace M distFun ios t1 q1 t2 q2))"
  using assms(3,4,5)
proof (induction "height_over ios t1 + height_over ios t2" arbitrary: t1 q1 t2 q2 rule: less_induct)
  case less

  obtain m1 where "t1 = PT m1"
    using prefix_tree.exhaust by blast
  obtain m2 where "t2 = PT m2"
    using prefix_tree.exhaust by blast


  define f where "f = (\<lambda> (\<omega>,l,w) (x,y) . 
            (let 
              w1L = if (PT m1) = empty then 0 else 1;
              w1C = if (x,y) \<in> dom m1 then 0 else 1;
              w1 = min w1L w1C;
              w2L = if (PT m2) = empty then 0 else 1;
              w2C = if (x,y) \<in> dom m2 then 0 else 1;
              w2 = min w2L w2C;
              w' = w1 + w2
            in  
              case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' 
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w)))))))"

  then have "find_cheapest_distinguishing_trace M distFun ios t1 q1 t2 q2 = foldl f (distFun q1 q2, 0, 3) ios"
    unfolding \<open>t1 = PT m1\<close> \<open>t2 = PT m2\<close> 
    unfolding find_cheapest_distinguishing_trace_alt_def Let_def
    by fast

  define ios' where "ios'=ios"

  have "list.set ios' \<subseteq> list.set ios \<Longrightarrow> distinguishes M q1 q2 (fst (foldl f (distFun q1 q2, 0, 3) ios'))"
  proof (induction ios' rule: rev_induct)
    case Nil
    then show ?case using assms(6)[OF less.prems] by auto
  next
    case (snoc xy ios')

    obtain x y where "xy = (x,y)"
      using prod.exhaust by metis
    moreover obtain \<omega> l w where "(foldl f (distFun q1 q2, 0, 3) ios') = (\<omega>,l,w)"
      using prod.exhaust by metis
    ultimately have "foldl f (distFun q1 q2, 0, 3) (ios'@[xy]) = f (\<omega>,l,w) (x,y)"
      by auto
    
    have "distinguishes M q1 q2 \<omega>"
      using \<open>(foldl f (distFun q1 q2, 0, 3) ios') = (\<omega>,l,w)\<close> snoc by auto

    have "(x,y) \<in> list.set ios"
      using snoc.prems unfolding \<open>xy = (x,y)\<close> by auto

    define w1L where "w1L = (if (PT m1) = empty then 0 else 1::nat)"
    define w1C where "w1C = (if (x,y) \<in> dom m1 then 0 else 1::nat)"
    define w1 where "w1 = min w1L w1C"
    define w2L where "w2L = (if (PT m2) = empty then 0 else 1::nat)"
    define w2C where "w2C = (if (x,y) \<in> dom m2 then 0 else 1::nat)"
    define w2 where "w2 = min w2L w2C"
    define w' where "w' = w1 + w2"

    have *:"f (\<omega>,l,w) (x,y) = (case h_obs M q1 x y of
                None \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> (\<omega>,l,w) |
                  Some _ \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w)) |
                Some q1' \<Rightarrow> (case h_obs M q2 x y of 
                  None \<Rightarrow> if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w) |
                  Some q2' \<Rightarrow> (if q1' = q2' 
                    then (\<omega>,l,w)
                    else (case m1 (x,y) of
                      None \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let \<omega>' = distFun q1' q2';
                                    l' = 2 + 2 * length \<omega>'
                                in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w) | 
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w)) |
                      Some t1' \<Rightarrow> (case m2 (x,y) of
                        None \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w) |
                        Some t2' \<Rightarrow> let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' 
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w))))))"
      unfolding w1_def w2_def w'_def w1L_def w1C_def w2L_def w2C_def
      unfolding f_def case_prod_conv Let_def 
      by fast

    have "distinguishes M q1 q2 (fst (f (\<omega>,l,w) (x,y)))"
    proof (cases "h_obs M q1 x y")
      case None
      then show ?thesis proof (cases "h_obs M q2 x y")
        case None
        have "f (\<omega>,l,w) (x,y) = (\<omega>,l,w)"
          unfolding *
          unfolding \<open>h_obs M q1 x y = None\<close> None by auto
        then show ?thesis 
          using \<open>distinguishes M q1 q2 \<omega>\<close> by auto
      next
        case (Some a)
        have "f (\<omega>,l,w) (x,y) = (if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w))"
          unfolding * None Some by auto
        moreover have "distinguishes M q1 q2 [(x,y)]"
          using distinguishes_sym[OF h_obs_distinguishes[OF assms(1) Some None]] .
        ultimately show ?thesis
          using \<open>distinguishes M q1 q2 \<omega>\<close> by auto
      qed
    next
      case (Some q1')
      then have "q1' \<in> states M"
        by (meson h_obs_state)
      
      show ?thesis proof (cases "h_obs M q2 x y")
        case None
        have "f (\<omega>,l,w) (x,y) = (if w' = 0 \<or> w' \<le> w then ([(x,y)],w1C+w2C,w') else (\<omega>,l,w))"
          unfolding * None Some by auto
        moreover have "distinguishes M q1 q2 [(x,y)]"
          using h_obs_distinguishes[OF assms(1) Some None] .
        ultimately show ?thesis
          using \<open>distinguishes M q1 q2 \<omega>\<close> by auto
      next
        case (Some q2')     
        then have "q2' \<in> states M"
          by (meson h_obs_state)
        
        show ?thesis proof (cases "q1' = q2'")
          case True
          have "f (\<omega>,l,w) (x,y) = (\<omega>,l,w)"
            unfolding *
            unfolding \<open>h_obs M q1 x y = Some q1'\<close> Some True by auto
          then show ?thesis 
            using \<open>distinguishes M q1 q2 \<omega>\<close> by auto
        next
          case False
          
          have dist': "\<And> \<omega> . distinguishes M q1' q2' \<omega> \<Longrightarrow> distinguishes M q1 q2 ((x,y)#\<omega>)"
            using distinguishes_after_prepend[OF assms(1), of q1 x y q2]
            using \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close>
            unfolding after_h_obs[OF assms(1) \<open>h_obs M q1 x y = Some q1'\<close>]
            unfolding after_h_obs[OF assms(1) \<open>h_obs M q2 x y = Some q2'\<close>] 
            by auto
          
          show ?thesis proof (cases "m1 (x,y)")
            case None
            show ?thesis proof (cases "m2 (x,y)")
              case None

              have **: "f (\<omega>,l,w) (x,y) = (let \<omega>' = distFun q1' q2';  l' = 2 + 2 * length \<omega>'
                                       in if (w' < w) \<or> (w' = w \<and> l' < l) then ((x,y)#\<omega>',l',w') else (\<omega>,l,w))"
                unfolding *
                unfolding \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close> \<open>m1 (x, y) = None\<close> \<open>m2 (x, y) = None\<close>
                using False
                by auto

              have "distinguishes M q1' q2' (distFun q1' q2')"
                using \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> assms(6) False by blast
              then have "distinguishes M q1 q2 ((x,y)#(distFun q1' q2'))"
                using dist' by auto
              then  show ?thesis 
                using \<open>distinguishes M q1 q2 \<omega>\<close>
                unfolding ** Let_def by auto
            next
              case (Some t2')

              have **: "f (\<omega>,l,w) (x,y) = (let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'
                                    in if (w'' + w1 < w) \<or> (w'' + w1 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w1) else (\<omega>,l,w))"
                unfolding *
                unfolding \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close> \<open>m1 (x, y) = None\<close> \<open>m2 (x, y) = Some t2'\<close>
                using False
                by auto

              obtain \<omega>'' l'' w'' where ***:"find_cheapest_distinguishing_trace M distFun ios Prefix_Tree.empty q1' t2' q2' = (\<omega>'', l'', w'')"
                using prod.exhaust by metis

              have "distinguishes M q1' q2' (fst (find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2'))"
              proof -

                have "height_over ios empty + height_over ios t2' < height_over ios t1 + height_over ios t2"
                  using height_over_subtree_less[of m2 "(x,y)", OF \<open>m2 (x,y) = Some t2'\<close> \<open>(x,y) \<in> list.set ios\<close> ]
                  unfolding height_over_empty \<open>t2 = PT m2\<close>[symmetric]
                  by (simp add: \<open>t1 = PT m1\<close>)
                then show ?thesis
                  using less.hyps[OF _ \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> False]
                  by blast
              qed
              then have "distinguishes M q1 q2 ((x,y)#(fst (find_cheapest_distinguishing_trace M distFun ios empty q1' t2' q2')))"
                using dist' by blast
              then  show ?thesis 
                using \<open>distinguishes M q1 q2 \<omega>\<close>                
                unfolding ** *** Let_def fst_conv case_prod_conv by auto
            qed
          next
            case (Some t1')
            show ?thesis proof (cases "m2 (x,y)")
              case None

              have **: "f (\<omega>,l,w) (x,y) = (let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' 
                                in if (w'' + w2 < w) \<or> (w'' + w2 = w \<and> l''+1 < l) then ((x,y)#\<omega>'',l''+1,w''+w2) else (\<omega>,l,w))"
                unfolding *
                unfolding \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close> \<open>m1 (x, y) = Some t1'\<close> \<open>m2 (x, y) = None\<close>
                using False
                by auto

              obtain \<omega>'' l'' w'' where ***:"find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2' = (\<omega>'', l'', w'')"
                using prod.exhaust by metis

              have "distinguishes M q1' q2' (fst (find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2'))"
              proof -

                have "height_over ios t1' + height_over ios empty < height_over ios t1 + height_over ios t2"
                  using height_over_subtree_less[of m1 "(x,y)", OF \<open>m1 (x,y) = Some t1'\<close> \<open>(x,y) \<in> list.set ios\<close> ]
                  unfolding height_over_empty \<open>t1 = PT m1\<close>[symmetric]
                  by (simp add: \<open>t2 = PT m2\<close>)
                then show ?thesis
                  using less.hyps[OF _ \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> False]
                  by blast
              qed
              then have "distinguishes M q1 q2 ((x,y)#(fst (find_cheapest_distinguishing_trace M distFun ios t1' q1' empty q2')))"
                using dist' by blast
              then  show ?thesis 
                using \<open>distinguishes M q1 q2 \<omega>\<close>                
                unfolding ** *** Let_def fst_conv case_prod_conv by auto
            next
              case (Some t2')

              have **: "f (\<omega>,l,w) (x,y) = (let (\<omega>'',l'',w'') = find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' 
                                    in if (w'' < w) \<or> (w'' = w \<and> l'' < l) then ((x,y)#\<omega>'',l'',w'') else (\<omega>,l,w))"
                unfolding *
                unfolding \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close> \<open>m1 (x, y) = Some t1'\<close> \<open>m2 (x, y) = Some t2'\<close>
                using False
                by auto
              obtain \<omega>'' l'' w'' where ***:"find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2' = (\<omega>'', l'', w'')"
                using prod.exhaust by metis

              have "distinguishes M q1' q2' (fst (find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2'))"
              proof -

                have "height_over ios t1' + height_over ios t2' < height_over ios t1 + height_over ios t2"
                  using height_over_subtree_less[of m1 "(x,y)", OF \<open>m1 (x,y) = Some t1'\<close> \<open>(x,y) \<in> list.set ios\<close> ]
                  using height_over_subtree_less[of m2 "(x,y)", OF \<open>m2 (x,y) = Some t2'\<close> \<open>(x,y) \<in> list.set ios\<close> ]
                  unfolding \<open>t1 = PT m1\<close>[symmetric] \<open>t2 = PT m2\<close>[symmetric]
                  by auto
                then show ?thesis
                  using less.hyps[OF _ \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> False]
                  by blast
              qed
              then have "distinguishes M q1 q2 ((x,y)#(fst (find_cheapest_distinguishing_trace M distFun ios t1' q1' t2' q2')))"
                using dist' by blast
              then  show ?thesis 
                using \<open>distinguishes M q1 q2 \<omega>\<close>                
                unfolding ** *** Let_def fst_conv case_prod_conv by auto
            qed
          qed
        qed
      qed
    qed
    then show ?case 
      unfolding \<open>foldl f (distFun q1 q2, 0, 3) (ios'@[xy]) = f (\<omega>,l,w) (x,y)\<close> .
  qed 
      

  then show ?case 
    unfolding \<open>find_cheapest_distinguishing_trace M distFun ios t1 q1 t2 q2 = foldl f (distFun q1 q2, 0, 3) ios\<close>
              \<open>ios' = ios\<close>
    by blast
qed


fun add_cheapest_distinguishing_trace :: "('a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list) \<Rightarrow> bool \<Rightarrow> ('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> (('b\<times>'c) list \<times> 'a) \<times> (('b\<times>'c) list \<times> 'a) \<Rightarrow> ('b\<times>'c) prefix_tree \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "add_cheapest_distinguishing_trace distFun completeInputTraces M ((\<alpha>,q1), (\<beta>,q2)) t = 
    (let w = (fst (find_cheapest_distinguishing_trace M distFun (List.product (inputs_as_list M) (outputs_as_list M)) (after t \<alpha>) q1 (after t \<beta>) q2));
         T = insert empty w
      in if completeInputTraces 
        then let T1 = complete_inputs_to_tree M q1 (outputs_as_list M) (map fst w);
                 T2 = complete_inputs_to_tree M q2 (outputs_as_list M) (map fst w)
             in Prefix_Tree.combine T (Prefix_Tree.combine T1 T2)
        else T)" 


lemma add_cheapest_distinguishing_trace_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "\<alpha> \<in> L M"
  and     "\<beta> \<in> L M" 
  and     "after_initial M \<alpha> \<noteq> after_initial M \<beta>" 
  and     "\<And> q1 q2 . q1 \<in> states M \<Longrightarrow> q2 \<in> states M \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> distinguishes M q1 q2 (dist_fun q1 q2)"
shows "\<exists> io \<in> set ((add_cheapest_distinguishing_trace dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>)) .  distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) io"
proof -
  define w where "w = (fst (find_cheapest_distinguishing_trace M dist_fun (List.product (inputs_as_list M) (outputs_as_list M)) (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)))"

  have "set (insert empty w) \<subseteq> set ((add_cheapest_distinguishing_trace dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
    using combine_set[of "insert empty w"] w_def
    unfolding add_cheapest_distinguishing_trace.simps Let_def 
    by (cases c; fastforce)
  moreover have "w \<in> set (insert empty w)"
    unfolding insert_set by auto
  ultimately have "w \<in> set ((add_cheapest_distinguishing_trace dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t) \<union> (set (after t \<alpha>) \<inter> set (after t \<beta>))"
    by blast
  moreover have "distinguishes M (after_initial M \<alpha>) (after_initial M \<beta>) w"
    using find_cheapest_distinguishing_trace_is_distinguishing_trace[OF assms(1,2) after_is_state[OF assms(1,3)] after_is_state[OF assms(1,4)] assms(5,6)]
    unfolding w_def 
    by blast
  ultimately show ?thesis 
    by blast 
qed

lemma add_cheapest_distinguishing_trace_finite : 
  "finite_tree ((add_cheapest_distinguishing_trace dist_fun c M) ((\<alpha>,after_initial M \<alpha>),(\<beta>,after_initial M \<beta>)) t)"
proof -

  define w where w: "w = (fst (find_cheapest_distinguishing_trace M dist_fun (List.product (inputs_as_list M) (outputs_as_list M)) (after t \<alpha>) (after_initial M \<alpha>) (after t \<beta>) (after_initial M \<beta>)))"
  define T where T: "T = insert empty w"
  define T1 where T1: "T1 = complete_inputs_to_tree M (after_initial M \<alpha>) (outputs_as_list M) (map fst w)"
  define T2 where T2: "T2 = complete_inputs_to_tree M (after_initial M \<beta>) (outputs_as_list M) (map fst w)"

  have "finite_tree T"
    using insert_finite_tree[OF empty_finite_tree]
    unfolding T by auto
  moreover have "finite_tree (Prefix_Tree.combine T (Prefix_Tree.combine T1 T2))"
    using combine_finite_tree[OF \<open>finite_tree T\<close> combine_finite_tree[OF complete_inputs_to_tree_finite_tree complete_inputs_to_tree_finite_tree]]
    unfolding T1 T2
    by auto
  ultimately show ?thesis
    unfolding add_cheapest_distinguishing_trace.simps w T T1 T2 Let_def
    by presburger
qed





subsubsection \<open>Implementation\<close>

definition h_method_via_pair_framework :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "h_method_via_pair_framework M m = pair_framework_h_components M m (add_distinguishing_sequence_if_required (get_distinguishing_sequence_from_ofsm_tables M))"

lemma h_method_via_pair_framework_completeness_and_finiteness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> set (h_method_via_pair_framework M m) = L I \<inter> set (h_method_via_pair_framework M m))"
and   "finite_tree (h_method_via_pair_framework M m)"
  using pair_framework_h_components_completeness_and_finiteness[OF assms(1,2,3,5,4,6,7), where get_separating_traces="(add_distinguishing_sequence_if_required (get_distinguishing_sequence_from_ofsm_tables M))", OF add_distinguishing_sequence_if_required_distinguishes[OF assms(1,3), where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] add_distinguishing_sequence_if_required_finite[where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] ]
  using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]
  unfolding h_method_via_pair_framework_def[symmetric]
  by blast+

definition h_method_via_pair_framework_2 :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "h_method_via_pair_framework_2 M m c = pair_framework_h_components M m (add_distinguishing_sequence_and_complete_if_required (get_distinguishing_sequence_from_ofsm_tables M) c)"

lemma h_method_via_pair_framework_2_completeness_and_finiteness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> set (h_method_via_pair_framework_2 M m c) = L I \<inter> set (h_method_via_pair_framework_2 M m c))"
and   "finite_tree (h_method_via_pair_framework_2 M m c)"
  using pair_framework_h_components_completeness_and_finiteness[OF assms(1,2,3,5,4,6,7), where get_separating_traces="(add_distinguishing_sequence_and_complete_if_required (get_distinguishing_sequence_from_ofsm_tables M) c)", OF add_distinguishing_sequence_and_complete_if_required_distinguishes[OF assms(1,3), where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] add_distinguishing_sequence_and_complete_if_required_finite[where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] ]
  using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]
  unfolding h_method_via_pair_framework_2_def[symmetric]
  by blast+

definition h_method_via_pair_framework_3 :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('b\<times>'c) prefix_tree" where
  "h_method_via_pair_framework_3 M m c1 c2 = pair_framework_h_components_2 M m (add_cheapest_distinguishing_trace (get_distinguishing_sequence_from_ofsm_tables M) c2) c1"

lemma h_method_via_pair_framework_3_completeness_and_finiteness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> (L M \<inter> set (h_method_via_pair_framework_3 M m c1 c2) = L I \<inter> set (h_method_via_pair_framework_3 M m c1 c2))"
and   "finite_tree (h_method_via_pair_framework_3 M m c1 c2)"
  using pair_framework_h_components_2_completeness_and_finiteness[OF assms(1,2,3,5,4,6,7), where get_separating_traces="(add_cheapest_distinguishing_trace (get_distinguishing_sequence_from_ofsm_tables M) c2)", OF add_cheapest_distinguishing_trace_distinguishes[OF assms(1,3), where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] add_cheapest_distinguishing_trace_finite[where dist_fun="(get_distinguishing_sequence_from_ofsm_tables M)"] ]
  using get_distinguishing_sequence_from_ofsm_tables_distinguishes[OF assms(1,3)]
  unfolding h_method_via_pair_framework_3_def[symmetric]
  by blast+


definition h_method_via_pair_framework_lists :: "('a::linorder,'b::linorder,'c::linorder) fsm \<Rightarrow> nat \<Rightarrow> (('b\<times>'c) \<times> bool) list list" where
  "h_method_via_pair_framework_lists M m = sorted_list_of_maximal_sequences_in_tree (test_suite_from_io_tree M (initial M) (h_method_via_pair_framework M m))"

lemma h_method_implementation_lists_completeness :
  assumes "observable M"
  and     "observable I"
  and     "minimal M"
  and     "size I \<le> m"
  and     "m \<ge> size_r M"
  and     "inputs I = inputs M"
  and     "outputs I = outputs M"
shows "(L M = L I) \<longleftrightarrow> list_all (passes_test_case I (initial I)) (h_method_via_pair_framework_lists M m)"
unfolding h_method_via_pair_framework_lists_def
            h_method_via_pair_framework_completeness_and_finiteness(1)[OF assms]
            passes_test_cases_from_io_tree[OF assms(1,2) fsm_initial fsm_initial h_method_via_pair_framework_completeness_and_finiteness(2)[OF assms]]
  by blast

subsubsection \<open>Code Equations\<close>

(* to avoid repeated computation of the same OFSM-tables by get_distinguishing_sequence_from_ofsm_tables,
   we pre-compute all distinguishing traces *)
lemma h_method_via_pair_framework_code[code] :
  "h_method_via_pair_framework M m = (let 
    tables = (compute_ofsm_tables M (size M - 1));
    distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                      (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
    distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
    distFun = add_distinguishing_sequence_if_required distHelper 
  in pair_framework_h_components M m distFun)"
  unfolding h_method_via_pair_framework_def
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger

lemma h_method_via_pair_framework_2_code[code] :
  "h_method_via_pair_framework_2 M m c = (let 
    tables = (compute_ofsm_tables M (size M - 1));
    distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                      (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
    distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
    distFun = add_distinguishing_sequence_and_complete_if_required distHelper c
  in pair_framework_h_components M m distFun)"
  unfolding h_method_via_pair_framework_2_def
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger

lemma h_method_via_pair_framework_3_code[code] :
  "h_method_via_pair_framework_3 M m c1 c2 = (let 
    tables = (compute_ofsm_tables M (size M - 1));
    distMap = mapping_of (map (\<lambda> (q1,q2) . ((q1,q2), get_distinguishing_sequence_from_ofsm_tables_with_provided_tables tables M q1 q2))
                      (filter (\<lambda> qq . fst qq \<noteq> snd qq) (List.product (states_as_list M) (states_as_list M))));
    distHelper = (\<lambda> q1 q2 . if q1 \<in> states M \<and> q2 \<in> states M \<and> q1 \<noteq> q2 then the (Mapping.lookup distMap (q1,q2)) else get_distinguishing_sequence_from_ofsm_tables M q1 q2);
    distFun = add_cheapest_distinguishing_trace distHelper c2 
  in pair_framework_h_components_2 M m distFun c1)"
  unfolding h_method_via_pair_framework_3_def 
  apply (subst get_distinguishing_sequence_from_ofsm_tables_precomputed[of M])
  unfolding Let_def
  by presburger

end