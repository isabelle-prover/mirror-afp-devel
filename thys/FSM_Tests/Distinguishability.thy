section \<open>Computation of distinguishing traces based on OFSM tables\<close>

text \<open>This theory implements an algorithm for finding minimal length distinguishing
      traces for observable minimal FSMs based on OFSM tables.\<close>


theory Distinguishability
  imports Minimisation HOL.List
begin 

subsection \<open>Finding Diverging OFSM Tables\<close>

(* some k such that the class of state q does not change in any OFSM table after the k-th table *)
definition ofsm_table_fixpoint_value :: "('a,'b,'c) fsm \<Rightarrow> nat" where
  "ofsm_table_fixpoint_value M = (SOME k . (\<forall> q . q \<in> states M \<longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k q) \<and> (\<forall> q k' . q \<in> states M \<longrightarrow> k' \<ge> k \<longrightarrow> ofsm_table M (\<lambda>q . states M) k' q = ofsm_table M (\<lambda>q . states M) k q))"

(* find the minimal k such that states q1 and q2 fall in different classes in the k-th table *)
function find_first_distinct_ofsm_table_gt :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "find_first_distinct_ofsm_table_gt M q1 q2 k = 
      (if q1 \<in> states M \<and> q2 \<in> states M \<and> ((ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2))
        then (if ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2
              then k
              else find_first_distinct_ofsm_table_gt M q1 q2 (Suc k))
        else 0)"
  using prod_cases4 by blast+
termination   
proof -
  {
    fix M :: "('a,'b,'c) fsm"
    fix q1 q2 k
    assume "q1 \<in> FSM.states M \<and> q2 \<in> FSM.states M \<and> ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2" 
           "ofsm_table M (\<lambda>q . states M) k q1 = ofsm_table M (\<lambda>q . states M) k q2"
    then have "q1 \<in> FSM.states M" and "q2 \<in> FSM.states M"
          and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
      by force+
  
  
    let ?k = "ofsm_table_fixpoint_value M"
    obtain k' where "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k' q" and "\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> k' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) k' q"
      using ofsm_table_fix_length[of M "(\<lambda>q . states M)"] 
      by blast
    then have "(\<forall> q . q \<in> states M \<longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k' q) \<and> (\<forall> q k'' . q \<in> states M \<longrightarrow> k'' \<ge> k' \<longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) k' q)"
      by blast
    then have *:"\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) ?k q"  
          and **: "\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> ?k \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) ?k q"
      using some_eq_imp[of "\<lambda> k . (\<forall> q . q \<in> states M \<longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k q) \<and> (\<forall> q k' . q \<in> states M \<longrightarrow> k' \<ge> k \<longrightarrow> ofsm_table M (\<lambda>q . states M) k' q = ofsm_table M (\<lambda>q . states M) k q)" ?k k']
      unfolding ofsm_table_fixpoint_value_def
      by blast+
  
    have "?k > k"
      using * 
            \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close>
            \<open>ofsm_table M (\<lambda>q . states M) k q1 = ofsm_table M (\<lambda>q . states M) k q2\<close>
            **[OF \<open>q1 \<in> states M\<close>]
            **[OF \<open>q2 \<in> states M\<close>]
      by (metis \<open>q1 \<in> FSM.states M \<and> q2 \<in> FSM.states M \<and> ofsm_table_fix M (\<lambda>q. FSM.states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q. FSM.states M) 0 q2\<close> leI)
    then have "?k - Suc k < ?k - k"
      by simp
  } note t = this

  show ?thesis
    apply (relation "measure (\<lambda> (M, q1, q2, k) . ofsm_table_fixpoint_value M - k)")
      apply auto[1]
    apply (simp del: observable.simps ofsm_table_fix.simps) 
    by (erule t) 
qed


partial_function (tailrec) find_first_distinct_ofsm_table_no_check :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  find_first_distinct_ofsm_table_no_check_def[code]:
    "find_first_distinct_ofsm_table_no_check M q1 q2 k = 
      (if ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2
          then k
          else find_first_distinct_ofsm_table_no_check M q1 q2 (Suc k))"

(* a version of find_first_distinct_ofsm_table_gt that avoids repeating the same checks in each
  recursive step *)
fun find_first_distinct_ofsm_table_gt' :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "find_first_distinct_ofsm_table_gt' M q1 q2 k = 
      (if q1 \<in> states M \<and> q2 \<in> states M \<and> ((q2 \<notin> ofsm_table_fix M (\<lambda>q . states M) 0 q1))
        then find_first_distinct_ofsm_table_no_check M q1 q2 k
        else 0)"


lemma find_first_distinct_ofsm_table_gt_code[code] :
  "find_first_distinct_ofsm_table_gt M q1 q2 k = find_first_distinct_ofsm_table_gt' M q1 q2 k"
proof (cases "q1 \<in> states M \<and> q2 \<in> states M \<and> ((ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2))")
  case False
  have "find_first_distinct_ofsm_table_gt M q1 q2 k = 0"
    using False
    by (metis find_first_distinct_ofsm_table_gt.simps) 
  moreover have "find_first_distinct_ofsm_table_gt' M q1 q2 k = 0"
  proof (cases "q1 \<in> states M \<and> q2 \<in> states M")
    case True
    then have "q1 \<in> FSM.states M" and "q2 \<in> FSM.states M"
          and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 = ofsm_table_fix M (\<lambda>q . states M) 0 q2"
      using False by force+
    then have "q2 \<in> ofsm_table_fix M (\<lambda>q . states M) 0 q1"
      using ofsm_table_fix_eq_if_elem[of q1 M q2]
      using minimise_initial_partition 
      by blast 
    then show ?thesis
      by (metis find_first_distinct_ofsm_table_gt'.simps) 
  next
    case False
    then show ?thesis by (meson find_first_distinct_ofsm_table_gt'.simps) 
  qed
  ultimately show ?thesis 
    by simp
next
  case True
  then have "q1 \<in> FSM.states M" and "q2 \<in> FSM.states M"
        and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    by force+
  then have "q2 \<notin> ofsm_table_fix M (\<lambda>q . states M) 0 q1"
      using ofsm_table_fix_eq_if_elem[of q1 M q2]
      using minimise_initial_partition  
      by blast 
  
  obtain k' where "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k' q" and "\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> k' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) k' q"
    using ofsm_table_fix_length[of M "(\<lambda>q . states M) "] 
    by blast

  have f1: "find_first_distinct_ofsm_table_gt M q1 q2 =
              (\<lambda>x. if ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2 
                then x
                else find_first_distinct_ofsm_table_gt M q1 q2 (Suc x))"
    using find_first_distinct_ofsm_table_gt.simps[of M q1 q2]
    using True
    by meson

  have f2: "find_first_distinct_ofsm_table_no_check M q1 q2 =
              (\<lambda>x. if ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2 
                then x
                else find_first_distinct_ofsm_table_no_check M q1 q2 (Suc x))"
    using True find_first_distinct_ofsm_table_no_check.simps[of M q1 q2]
    by meson

  have "(\<And>x. k' \<le> x \<Longrightarrow> ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2)"
    using \<open>\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> k' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) k' q\<close> \<open>q1 \<in> FSM.states M\<close> \<open>q2 \<in> FSM.states M\<close>
    by (metis True \<open>\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) k' q\<close>) 


  have "find_first_distinct_ofsm_table_gt' M q1 q2 k = find_first_distinct_ofsm_table_no_check M q1 q2 k"
    using True \<open>q2 \<notin> ofsm_table_fix M (\<lambda>q . states M) 0 q1\<close> find_first_distinct_ofsm_table_gt'.simps[of M]
    by meson
  then show ?thesis
    using recursion_renaming_helper[OF f1 f2 \<open>(\<And>x. k' \<le> x \<Longrightarrow> ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2)\<close>, of k'] 
    by simp
qed

lemma find_first_distinct_ofsm_table_gt_is_first_gt :
  assumes "q1 \<in> FSM.states M" 
      and "q2 \<in> FSM.states M"
      and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
shows "ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table_gt M q1 q2 k) q1 \<noteq> ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table_gt M q1 q2 k) q2"
  and "k \<le> k' \<Longrightarrow> k' < (find_first_distinct_ofsm_table_gt M q1 q2 k) \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2"
proof -

  have f: "find_first_distinct_ofsm_table_gt M q1 q2 =
              (\<lambda>x. if ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2 
                then x
                else find_first_distinct_ofsm_table_gt M q1 q2 (Suc x))"
    using assms find_first_distinct_ofsm_table_gt.simps[of M]
    by meson

  obtain kx where "\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) kx q" and "\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> kx \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) kx q"
    using ofsm_table_fix_length[of M "(\<lambda>q . states M)"] 
    by blast
  have P: "(\<And>x. kx \<le> x \<Longrightarrow> ofsm_table M (\<lambda>q . states M) x q1 \<noteq> ofsm_table M (\<lambda>q . states M) x q2)"
    using \<open>\<And> q k'' . q \<in> states M \<Longrightarrow> k'' \<ge> kx \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k'' q = ofsm_table M (\<lambda>q . states M) kx q\<close> \<open>q1 \<in> FSM.states M\<close> \<open>q2 \<in> FSM.states M\<close>
    by (metis assms \<open>\<And> q . q \<in> states M \<Longrightarrow> ofsm_table_fix M (\<lambda>q . states M) 0 q = ofsm_table M (\<lambda>q . states M) kx q\<close>)

  show "ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table_gt M q1 q2 k) q1 \<noteq> ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table_gt M q1 q2 k) q2"
    using minimal_fixpoint_helper(1)[OF f P, of kx k] .

  show "k \<le> k' \<Longrightarrow> k' < (find_first_distinct_ofsm_table_gt M q1 q2 k) \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2"
    using minimal_fixpoint_helper(2)[OF f P, of kx k k'] 
    by auto 
qed

abbreviation(input) "find_first_distinct_ofsm_table M q1 q2 \<equiv> find_first_distinct_ofsm_table_gt M q1 q2 0" 

lemma find_first_distinct_ofsm_table_is_first :
  assumes "q1 \<in> FSM.states M" 
      and "q2 \<in> FSM.states M"
      and "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
shows "ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table M q1 q2) q1 \<noteq> ofsm_table M (\<lambda>q . states M) (find_first_distinct_ofsm_table M q1 q2) q2"
  and "k' < (find_first_distinct_ofsm_table M q1 q2) \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k' q1 = ofsm_table M (\<lambda>q . states M) k' q2"
  using find_first_distinct_ofsm_table_gt_is_first_gt[OF assms, of 0] by blast+ 


(* find IO pair (x,y) such that q1 and q2 are immediately distinguishable by it or
   the states reached by this IO pair reach from q1 and q2 respectively reach distinct
   classes in the (k-1)-th table *)
fun select_diverging_ofsm_table_io :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) \<times> ('a option \<times> 'a option)" where
  "select_diverging_ofsm_table_io M q1 q2 k = (let
      ins = inputs_as_list M;
      outs = outputs_as_list M;
      table = ofsm_table M (\<lambda>q . states M) (k-1);
      f = (\<lambda> (x,y) . case (h_obs M q1 x y, h_obs M q2 x y) 
                   of
                      (Some q1', Some q2')  \<Rightarrow> if table q1' \<noteq> table q2'
                                                  then Some ((x,y),(Some q1', Some q2'))
                                                  else None |
                      (None,None)           \<Rightarrow> None |
                      (Some q1', None)      \<Rightarrow> Some ((x,y),(Some q1', None)) |
                      (None, Some q2')      \<Rightarrow> Some ((x,y),(None, Some q2')))
      in 
        hd (List.map_filter f (List.product ins outs)))" 


lemma select_diverging_ofsm_table_io_Some :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "ofsm_table M (\<lambda>q . states M) (Suc k) q1 \<noteq> ofsm_table M (\<lambda>q . states M) (Suc k) q2"
obtains x y 
  where "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
    and "\<And> q1' q2' . h_obs M q1 x y = Some q1' \<Longrightarrow> h_obs M q2 x y = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
    and "h_obs M q1 x y \<noteq> None \<or> h_obs M q2 x y \<noteq> None"
proof -

  let ?res = "select_diverging_ofsm_table_io M q1 q2 (Suc k)"

  define f where f: "f = (\<lambda> (x,y) . case (h_obs M q1 x y, h_obs M q2 x y) 
                                of
                                  (Some q1', Some q2') \<Rightarrow> if ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'
                                                            then Some ((x,y),(Some q1', Some q2'))
                                                            else None |
                                  (None,None) \<Rightarrow> None |
                                  (Some q1', None) \<Rightarrow> Some ((x,y),(Some q1', None)) |
                                  (None, Some q2') \<Rightarrow> Some ((x,y),(None, Some q2')))"

  have f1: "\<And> x y . f (x,y) \<noteq> None \<Longrightarrow> f (x,y) = Some ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
  proof -
    fix x y assume "f (x,y) \<noteq> None"
    then show "f (x,y) = Some ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
      unfolding f by (cases "h_obs M q1 x y"; cases "h_obs M q2 x y"; auto)
  qed

  have f2 : "\<And> q1' q2' x y . f (x,y) = Some ((x,y),(Some q1', Some q2')) \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
  proof -
    fix q1' q2' x y assume *: "f (x,y) = Some ((x,y),(Some q1', Some q2'))"
    then have **: "f (x,y) = Some ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
      using f1 by auto
    show "ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
      using * ** unfolding f by (cases "h_obs M q1 x y"; cases "h_obs M q2 x y"; auto)
  qed

  have f3: "\<And> x y . f (x,y) \<noteq> None \<Longrightarrow> h_obs M q1 x y \<noteq> None \<or> h_obs M q2 x y \<noteq> None"
  proof -
    fix x y assume "f (x,y) \<noteq> None"
    then show "h_obs M q1 x y \<noteq> None \<or> h_obs M q2 x y \<noteq> None"
      unfolding f by (cases "h_obs M q1 x y"; cases "h_obs M q2 x y"; auto)
  qed


  have *: "select_diverging_ofsm_table_io M q1 q2 (Suc k) = hd (List.map_filter f (List.product (inputs_as_list M) (outputs_as_list M)))"
    unfolding f select_diverging_ofsm_table_io.simps Let_def
    using diff_Suc_1 by presburger 
  
  
  let ?P = "\<forall> x y . x \<in> inputs M \<longrightarrow> y \<in> outputs M \<longrightarrow> (h_obs M q1 x y = None \<longleftrightarrow> h_obs M q2 x y = None)"
  show ?thesis proof (cases ?P)
    case False
    then obtain x y where "x \<in> inputs M" and "y \<in> outputs M" and "\<not> (h_obs M q1 x y = None \<longleftrightarrow> h_obs M q2 x y = None)"
      by blast
    then consider "h_obs M q1 x y = None \<and> (\<exists> q2' . h_obs M q2 x y = Some q2')" |
                  "h_obs M q2 x y = None \<and> (\<exists> q1' . h_obs M q1 x y = Some q1')"
      by fastforce
    then show ?thesis proof cases
      case 1
      then obtain q2' where "h_obs M q1 x y = None" and "h_obs M q2 x y = Some q2'" by blast
      then have "f (x,y) = Some ((x,y),(None, Some q2'))"
        unfolding f by force
      moreover have "(x,y) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
        using \<open>y \<in> outputs M\<close> outputs_as_list_set[of M]
        using \<open>x \<in> inputs M\<close> inputs_as_list_set[of M] 
        using image_iff by fastforce 
      ultimately have "(List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M))) \<noteq> []"
        unfolding List.map_filter_def
        by (metis (mono_tags, lifting) Nil_is_map_conv filter_empty_conv option.discI)
      then have **: "?res \<in> set (List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M)))"
        unfolding * using hd_in_set by simp
      
      obtain xR yR where "(xR,yR) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
                     and res: "f (xR,yR) = Some ?res"
        using map_filter_elem[OF **]
        by (metis prod.exhaust_sel) 
        
      have p1: "?res = ((xR,yR),(h_obs M q1 xR yR, h_obs M q2 xR yR))"   
        using res f1
        by (metis option.distinct(1) option.sel) 
      then have p2: "\<And> q1' q2' . h_obs M q1 xR yR = Some q1' \<Longrightarrow> h_obs M q2 xR yR = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
        using res f1 f2 by auto
      have p3: "h_obs M q1 xR yR \<noteq> None \<or> h_obs M q2 xR yR \<noteq> None"
        using res f3 by blast 

      show ?thesis using that p1 p2 p3 by blast
    next
      case 2
      then obtain q1' where "h_obs M q2 x y = None" and "h_obs M q1 x y = Some q1'" by blast
      then have "f (x,y) = Some ((x,y),(Some q1', None))"
        unfolding f by force
      moreover have "(x,y) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
        using \<open>y \<in> outputs M\<close> outputs_as_list_set[of M]
        using \<open>x \<in> inputs M\<close> inputs_as_list_set[of M] 
        using image_iff by fastforce 
      ultimately have "(List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M))) \<noteq> []"
        unfolding List.map_filter_def
        by (metis (mono_tags, lifting) Nil_is_map_conv filter_empty_conv option.discI)
      then have **: "?res \<in> set (List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M)))"
        unfolding * using hd_in_set by simp
      
      obtain xR yR where "(xR,yR) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
                     and res: "f (xR,yR) = Some ?res"
        using map_filter_elem[OF **]
        by (metis prod.exhaust_sel) 
        
      have p1: "?res = ((xR,yR),(h_obs M q1 xR yR, h_obs M q2 xR yR))"   
        using res f1
        by (metis option.distinct(1) option.sel) 
      then have p2: "\<And> q1' q2' . h_obs M q1 xR yR = Some q1' \<Longrightarrow> h_obs M q2 xR yR = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
        using res f1 f2 by auto
      have p3: "h_obs M q1 xR yR \<noteq> None \<or> h_obs M q2 xR yR \<noteq> None"
        using res f3 by blast 

      show ?thesis using that p1 p2 p3 by blast
    qed
  next 
    case True

    obtain io where "length io \<le> Suc k" and "io \<in> LS M q1 \<union> LS M q2" and "io \<notin> LS M q1 \<inter> LS M q2"
      using \<open>ofsm_table M (\<lambda>q . states M) (Suc k) q1 \<noteq> ofsm_table M (\<lambda>q . states M) (Suc k) q2\<close>
      unfolding ofsm_table_set[OF assms(2) minimise_initial_partition] ofsm_table_set[OF assms(3) minimise_initial_partition] 
      unfolding is_in_language_iff[OF assms(1,2)] is_in_language_iff[OF assms(1,3)]
      by blast  
    then have "io \<noteq> []"
      using assms(2) assms(3) by auto 
    then have "io = [hd io] @ tl io"
      by (metis append.left_neutral append_Cons list.exhaust_sel)    
    then obtain x y where "hd io = (x,y)"
      by (meson prod.exhaust_sel)
  
    have "[(x,y)] \<in> LS M q1 \<inter> LS M q2"
    proof -
      have "[(x,y)] \<in> LS M q1 \<union> LS M q2"
        using \<open>io \<in> LS M q1 \<union> LS M q2\<close> language_prefix \<open>hd io = (x,y)\<close> \<open>io = [hd io] @ tl io\<close>
        by (metis Un_iff) 
      then have "x \<in> inputs M" and "y \<in> outputs M"
        by auto
      
      consider "[(x,y)] \<in> LS M q1" | "[(x,y)] \<in> LS M q2"
        using \<open>[(x,y)] \<in> LS M q1 \<union> LS M q2\<close> by blast
      then show ?thesis 
      proof cases
        case 1
        then have "h_obs M q1 x y \<noteq> None"
          using h_obs_None[OF \<open>observable M\<close>] unfolding LS_single_transition by auto
        then have "h_obs M q2 x y \<noteq> None"
          using True \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by meson
        then show ?thesis 
          using 1 h_obs_None[OF \<open>observable M\<close>] 
          by (metis IntI LS_single_transition fst_conv snd_conv) 
      next
        case 2
        then have "h_obs M q2 x y \<noteq> None"
          using h_obs_None[OF \<open>observable M\<close>] unfolding LS_single_transition by auto
        then have "h_obs M q1 x y \<noteq> None"
          using True \<open>x \<in> inputs M\<close> \<open>y \<in> outputs M\<close> by meson
        then show ?thesis 
          using 2 h_obs_None[OF \<open>observable M\<close>] 
          by (metis IntI LS_single_transition fst_conv snd_conv) 
      qed
    qed
    then obtain q1' q2' where "(q1,x,y,q1') \<in> transitions M" 
                          and "(q2,x,y,q2') \<in> transitions M"
      using LS_single_transition by force
    then have "q1' \<in> states M" and "q2' \<in> states M" using fsm_transition_target by auto
  
    have "tl io \<in> LS M q1' \<union> LS M q2'"
      using observable_language_transition_target[OF \<open>observable M\<close> \<open>(q1,x,y,q1') \<in> transitions M\<close>]
            observable_language_transition_target[OF \<open>observable M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>]
            \<open>io \<in> LS M q1 \<union> LS M q2\<close>
      unfolding fst_conv snd_conv
      by (metis Un_iff \<open>hd io = (x, y)\<close> \<open>io = [hd io] @ tl io\<close> append_Cons append_Nil) 
    moreover have "tl io \<notin> LS M q1' \<inter> LS M q2'"
      using observable_language_transition_target[OF \<open>observable M\<close> \<open>(q1,x,y,q1') \<in> transitions M\<close>]
            observable_language_transition_target[OF \<open>observable M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>]
            \<open>io \<in> LS M q1 \<union> LS M q2\<close>
      unfolding fst_conv snd_conv
      by (metis Int_iff LS_prepend_transition \<open>(q1, x, y, q1') \<in> FSM.transitions M\<close> \<open>(q2, x, y, q2') \<in> FSM.transitions M\<close> \<open>hd io = (x, y)\<close> \<open>io \<noteq> []\<close> \<open>io \<notin> LS M q1 \<inter> LS M q2\<close> fst_conv list.collapse snd_conv)    
    moreover have "length (tl io) \<le> k"
      using \<open>length io \<le> Suc k\<close> by auto
    ultimately have "ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
      unfolding ofsm_table_set_observable[OF assms(1) \<open>q1' \<in> states M\<close> minimise_initial_partition]  ofsm_table_set_observable[OF assms(1) \<open>q2' \<in> states M\<close> minimise_initial_partition]
      using \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> after_is_state[OF assms(1)]
      by blast    
    moreover have "h_obs M q1 x y = Some q1'"
      using \<open>(q1,x,y,q1') \<in> transitions M\<close> \<open>observable M\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] observable_alt_def by auto
    moreover have "h_obs M q2 x y = Some q2'"
      using \<open>(q2,x,y,q2') \<in> transitions M\<close> \<open>observable M\<close> unfolding h_obs_Some[OF \<open>observable M\<close>] observable_alt_def by auto
    ultimately have "f (x,y) = Some ((x,y),(Some q1', Some q2'))"
      unfolding f by force
        
    moreover have "(x,y) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
      using fsm_transition_output[OF \<open>(q1,x,y,q1') \<in> transitions M\<close>] outputs_as_list_set[of M]
      using fsm_transition_input[OF \<open>(q1,x,y,q1') \<in> transitions M\<close>] inputs_as_list_set[of M] 
      using image_iff by fastforce 
    ultimately have "(List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M))) \<noteq> []"
      unfolding List.map_filter_def
      by (metis (mono_tags, lifting) Nil_is_map_conv filter_empty_conv option.discI)
    then have **: "?res \<in> set (List.map_filter f (List.product(inputs_as_list M) (outputs_as_list M)))"
      unfolding * using hd_in_set by simp
    
    obtain xR yR where "(xR,yR) \<in> set (List.product(inputs_as_list M) (outputs_as_list M))"
                   and res: "f (xR,yR) = Some ?res"
      using map_filter_elem[OF **]
      by (metis prod.exhaust_sel) 
      
    have p1: "?res = ((xR,yR),(h_obs M q1 xR yR, h_obs M q2 xR yR))"   
      using res f1
      by (metis option.distinct(1) option.sel) 
    then have p2: "\<And> q1' q2' . h_obs M q1 xR yR = Some q1' \<Longrightarrow> h_obs M q2 xR yR = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
      using res f1 f2 by auto
    have p3: "h_obs M q1 xR yR \<noteq> None \<or> h_obs M q2 xR yR \<noteq> None"
      using res f3 by blast 
    show ?thesis using that p1 p2 p3 by blast
  qed
qed


subsection \<open>Assembling Distinguishing Traces\<close>

(* assembles a distinguishing sequence for q1 and q2 that reside in distinct classes in the 
   (k+1)-th table by recursively appending IO pairs that distinguish the current states
   or lead to distinct classes in the next lower table *)
fun assemble_distinguishing_sequence_from_ofsm_table :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('b \<times> 'c) list" where
  "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 0 = []" | 
  "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = (case 
      select_diverging_ofsm_table_io M q1 q2 (Suc k) 
    of
      ((x,y),(Some q1',Some q2')) \<Rightarrow> (x,y) # (assemble_distinguishing_sequence_from_ofsm_table M q1' q2' k) |
      ((x,y),_)                   \<Rightarrow> [(x,y)])"


lemma assemble_distinguishing_sequence_from_ofsm_table_distinguishes :
  assumes "observable M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "ofsm_table M (\<lambda>q . states M) k q1 \<noteq> ofsm_table M (\<lambda>q . states M) k q2"
shows "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<in> LS M q1 \<union> LS M q2"
and   "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<notin> LS M q1 \<inter> LS M q2"
and   "butlast (assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k) \<in> LS M q1 \<inter> LS M q2"
proof -
  have "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<in> LS M q1 \<union> LS M q2
        \<and> assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<notin> LS M q1 \<inter> LS M q2
        \<and> butlast (assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k) \<in> LS M q1 \<inter> LS M q2"
    using assms(2,3,4) 
  proof (induction k arbitrary: q1 q2)
    case 0
    then show ?case by auto 
  next
    case (Suc k) 

    obtain x y where s1: "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(h_obs M q1 x y, h_obs M q2 x y))"
                 and s2: "\<And> q1' q2' . h_obs M q1 x y = Some q1' \<Longrightarrow> h_obs M q2 x y = Some q2' \<Longrightarrow> ofsm_table M (\<lambda>q . states M) k q1' \<noteq> ofsm_table M (\<lambda>q . states M) k q2'"
                 and s3: "h_obs M q1 x y \<noteq> None \<or> h_obs M q2 x y \<noteq> None"
      using select_diverging_ofsm_table_io_Some[OF assms(1) Suc.prems]
      by blast

    consider (a) "h_obs M q1 x y = None \<and> h_obs M q2 x y \<noteq> None" |
             (b) "h_obs M q1 x y \<noteq> None \<and> h_obs M q2 x y = None" |
             (c) "h_obs M q1 x y \<noteq> None \<and> h_obs M q2 x y \<noteq> None"
      using s3 by blast
    then show ?case proof cases
      case a
      then obtain q2' where "h_obs M q1 x y = None" and "h_obs M q2 x y = Some q2'"
        by blast
      then have "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(None, Some q2'))"
        using s1 by auto
      then have *:"assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = [(x,y)]"
        by auto

      have "[(x,y)] \<in> LS M q1 \<union> LS M q2"
        using \<open>h_obs M q2 x y = Some q2'\<close> LS_single_transition[of x y M]
        by (metis UnI2 h_obs_None[OF \<open>observable M\<close>] a fst_conv snd_conv)
      moreover have "[(x,y)] \<notin> LS M q1 \<inter> LS M q2"
        using \<open>h_obs M q1 x y = None\<close> LS_single_transition[of x y M] 
        unfolding h_obs_None[OF \<open>observable M\<close>] by force
      moreover have "butlast [(x,y)] \<in> LS M q1 \<inter> LS M q2"
        using Suc.prems(1,2) by auto
      ultimately show ?thesis
        unfolding * by simp
    next
      case b
      then obtain q1' where "h_obs M q2 x y = None" and "h_obs M q1 x y = Some q1'"
        by blast
      then have "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(Some q1',None))"
        using s1 by auto
      then have *:"assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = [(x,y)]"
        by auto

      have "[(x,y)] \<in> LS M q1 \<union> LS M q2"
        using \<open>h_obs M q1 x y = Some q1'\<close> LS_single_transition[of x y M]
        by (metis UnI1 assms(1) b fst_conv h_obs_None snd_conv)        
      moreover have "[(x,y)] \<notin> LS M q1 \<inter> LS M q2"
        using \<open>h_obs M q2 x y = None\<close> LS_single_transition[of x y M] 
        unfolding h_obs_None[OF \<open>observable M\<close>] by force
      moreover have "butlast [(x,y)] \<in> LS M q1 \<inter> LS M q2"
        using Suc.prems(1,2) by auto
      ultimately show ?thesis
        unfolding * by simp
    next
      case c
      then obtain q1' q2' where "h_obs M q1 x y = Some q1'" and "h_obs M q2 x y = Some q2'"
        by blast
      then have "select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),(Some q1', Some q2'))"
        using s1 by auto
      then have "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = (x,y) # (assemble_distinguishing_sequence_from_ofsm_table M q1' q2' k)"
        by auto
      moreover define subseq where subseq: "subseq = (assemble_distinguishing_sequence_from_ofsm_table M q1' q2' k)"
      ultimately have *:"assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = (x,y) # subseq"
        by auto

      have "(q1,x,y,q1') \<in> transitions M"
        using \<open>h_obs M q1 x y = Some q1'\<close> h_obs_Some[OF \<open>observable M\<close>] by blast
      then have "q1' \<in> states M" 
        using fsm_transition_target by auto
      have "(q2,x,y,q2') \<in> transitions M"
        using \<open>h_obs M q2 x y = Some q2'\<close> h_obs_Some[OF \<open>observable M\<close>] by blast
      then have "q2' \<in> states M" 
        using fsm_transition_target by auto

      have i1: "subseq \<in> LS M q1' \<union> LS M q2'"
      and  i2: "subseq \<notin> LS M q1' \<inter> LS M q2'"
      and  i3: "butlast subseq \<in> LS M q1' \<inter> LS M q2'"
        using Suc.IH[OF \<open>q1' \<in> states M\<close> \<open>q2' \<in> states M\<close> s2[OF \<open>h_obs M q1 x y = Some q1'\<close> \<open>h_obs M q2 x y = Some q2'\<close>]]
        unfolding subseq by blast+

      have "(x,y) # subseq \<in> LS M q1 \<union> LS M q2"
        using i1 \<open>(q1,x,y,q1') \<in> transitions M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>
        by (metis LS_prepend_transition Un_iff fst_conv snd_conv) 
      moreover have "(x,y) # subseq \<notin> LS M q1 \<inter> LS M q2"
        using observable_language_transition_target[OF \<open>observable M\<close> \<open>(q1,x,y,q1') \<in> transitions M\<close>, of subseq]
              observable_language_transition_target[OF \<open>observable M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>, of subseq]
              i2
        unfolding fst_conv snd_conv
        by blast
      moreover have "butlast ((x,y) # subseq) \<in> LS M q1 \<inter> LS M q2"
        using i3 \<open>(q1,x,y,q1') \<in> transitions M\<close> \<open>(q2,x,y,q2') \<in> transitions M\<close>
        by (metis Int_iff LS_prepend_transition LS_single_transition append_butlast_last_id butlast.simps(2) fst_conv language_prefix snd_conv) 
       ultimately show ?thesis
        unfolding * by simp
    qed
  qed

  then show "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<in> LS M q1 \<union> LS M q2"
       and  "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k \<notin> LS M q1 \<inter> LS M q2"
       and  "butlast (assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k) \<in> LS M q1 \<inter> LS M q2"
    by blast+
qed


lemma assemble_distinguishing_sequence_from_ofsm_table_length :
  "length (assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k) \<le> k"
proof (induction k arbitrary: q1 q2)
  case 0
  then show ?case by auto
next
  case (Suc k)
  obtain x y A B where *:"select_diverging_ofsm_table_io M q1 q2 (Suc k) = ((x,y),A,B)"
    using prod.exhaust by metis
  
  show ?case proof (cases A)
    case None
    then have "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = [(x,y)]"
      unfolding assemble_distinguishing_sequence_from_ofsm_table.simps * case_prod_conv by auto
    then show ?thesis
      by (metis Suc_le_length_iff length_Cons list.distinct(1) not_less_eq_eq) 
  next
    case (Some q1')
    show ?thesis proof (cases B)
      case None
      then have "assemble_distinguishing_sequence_from_ofsm_table M q1 q2 (Suc k) = [(x,y)]"
        unfolding assemble_distinguishing_sequence_from_ofsm_table.simps * case_prod_conv Some by auto
      then show ?thesis 
        by (metis Suc_le_length_iff length_Cons list.distinct(1) not_less_eq_eq) 
    next
      case (Some q2')
      show ?thesis 
        unfolding assemble_distinguishing_sequence_from_ofsm_table.simps * \<open>A = Some q1'\<close> Some case_prod_conv
        using Suc.IH[of q1' q2']
        by simp 
    qed
  qed
qed

lemma ofsm_table_fix_partition_fixpoint_trivial_partition :
  assumes "q \<in> states M"
shows "ofsm_table_fix M (\<lambda>q. FSM.states M) 0 q = ofsm_table M (\<lambda>q. FSM.states M) (size M - 1) q"
proof -
  have "((\<lambda>q. FSM.states M) ` FSM.states M) = {states M}"
    using fsm_initial[of M]
    by auto 
  then have *:"card ((\<lambda>q. FSM.states M) ` FSM.states M) = 1"
    by auto
  
  show ?thesis
    using ofsm_table_fix_partition_fixpoint[OF minimise_initial_partition _ assms, of "size M"]
    unfolding *
    by blast
qed



fun get_distinguishing_sequence_from_ofsm_tables :: "('a,'b::linorder,'c::linorder) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list" where
  "get_distinguishing_sequence_from_ofsm_tables M q1 q2 = (let
      k = find_first_distinct_ofsm_table M q1 q2
  in assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k)"



lemma get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> LS M q1 \<union> LS M q2"
and   "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<notin> LS M q1 \<inter> LS M q2"
and   "butlast (get_distinguishing_sequence_from_ofsm_tables M q1 q2) \<in> LS M q1 \<inter> LS M q2"
proof -
  have "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    using \<open>minimal M\<close> unfolding minimal_observable_code[OF assms(1)]
    using assms(3,4,5) by blast

  let ?k = "find_first_distinct_ofsm_table_gt M q1 q2 0"
  have "ofsm_table M (\<lambda>q . states M) ?k q1 \<noteq> ofsm_table M (\<lambda>q . states M) ?k q2"
    using find_first_distinct_ofsm_table_is_first(1)[OF assms(3,4) \<open>ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2\<close>] .

  have *:"get_distinguishing_sequence_from_ofsm_tables M q1 q2 = assemble_distinguishing_sequence_from_ofsm_table M q1 q2 ?k"
    by auto
  
  show "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<in> LS M q1 \<union> LS M q2"
  and  "get_distinguishing_sequence_from_ofsm_tables M q1 q2 \<notin> LS M q1 \<inter> LS M q2"
  and  "butlast (get_distinguishing_sequence_from_ofsm_tables M q1 q2) \<in> LS M q1 \<inter> LS M q2"
    using assemble_distinguishing_sequence_from_ofsm_table_distinguishes[OF assms(1,3,4) \<open>ofsm_table M (\<lambda>q . states M) ?k q1 \<noteq> ofsm_table M (\<lambda>q . states M) ?k q2\<close>]
    unfolding * 
    by blast+
qed

lemma get_distinguishing_sequence_from_ofsm_tables_distinguishes :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "distinguishes M q1 q2 (get_distinguishing_sequence_from_ofsm_tables M q1 q2)"
  using get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms]
  unfolding distinguishes_def
  by blast

subsection \<open>Minimal Distinguishing Traces\<close>

lemma get_distinguishing_sequence_from_ofsm_tables_is_minimally_distinguishing :
  fixes M :: "('a,'b::linorder,'c::linorder) fsm"
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
shows "minimally_distinguishes M q1 q2 (get_distinguishing_sequence_from_ofsm_tables M q1 q2)"
proof -

  have *:"ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    using \<open>minimal M\<close> unfolding minimal_observable_code[OF assms(1)]
    using assms(3,4,5) by blast

  obtain k where "k = find_first_distinct_ofsm_table M q1 q2"
             and "get_distinguishing_sequence_from_ofsm_tables M q1 q2 = assemble_distinguishing_sequence_from_ofsm_table M q1 q2 k"
    by auto
  then have "length (get_distinguishing_sequence_from_ofsm_tables M q1 q2) \<le> k"
    using assemble_distinguishing_sequence_from_ofsm_table_length
    by metis
  moreover have "\<And> io . length io < k \<Longrightarrow> \<not>distinguishes M q1 q2 io"
  proof -
    fix io :: "('b \<times> 'c) list" 
    assume "length io < k"
    then have "ofsm_table M (\<lambda>q. FSM.states M) (length io) q1 = ofsm_table M (\<lambda>q. FSM.states M) (length io) q2"
      using find_first_distinct_ofsm_table_is_first[OF assms(3,4) *]
      unfolding \<open>k = find_first_distinct_ofsm_table M q1 q2\<close>
      by blast
    then show "\<not>distinguishes M q1 q2 io"
      using ofsm_table_set_observable[OF assms(1,3) minimise_initial_partition]
      using ofsm_table_set_observable[OF assms(1,4) minimise_initial_partition]
      unfolding distinguishes_def
      by (metis (mono_tags, lifting) Int_iff Un_iff assms(3) le_refl mem_Collect_eq ofsm_table_containment) 
  qed
  ultimately show ?thesis
    using get_distinguishing_sequence_from_ofsm_tables_is_distinguishing_trace(1,2)[OF assms]
    unfolding minimally_distinguishes_def distinguishes_def
    using le_neq_implies_less not_le_imp_less 
    by blast
qed


lemma minimally_distinguishes_length :
  assumes "observable M"
  and     "minimal M"
  and     "q1 \<in> states M"
  and     "q2 \<in> states M"
  and     "q1 \<noteq> q2"
  and     "minimally_distinguishes M q1 q2 io"
shows "length io \<le> size M - 1"
proof -

  have "ofsm_table_fix M (\<lambda>q . states M) 0 q1 \<noteq> ofsm_table_fix M (\<lambda>q . states M) 0 q2"
    using \<open>minimal M\<close> unfolding minimal_observable_code[OF assms(1)]
    using assms(3,4,5) by blast
  then have "ofsm_table M (\<lambda>q. FSM.states M) (FSM.size M - 1) q1 \<noteq> ofsm_table M (\<lambda>q. FSM.states M) (FSM.size M - 1) q2"
    using ofsm_table_fix_partition_fixpoint_trivial_partition assms(3,4)
    by metis 
  then obtain io' where "distinguishes M q1 q2 io'" and "length io' \<le> size M - 1"
    unfolding ofsm_table_set_observable[OF assms(1,3) minimise_initial_partition]
    unfolding ofsm_table_set_observable[OF assms(1,4) minimise_initial_partition]
    unfolding distinguishes_def
    by blast 
  then show ?thesis
    using assms(6) unfolding minimally_distinguishes_def
    using dual_order.trans by blast 
qed

end