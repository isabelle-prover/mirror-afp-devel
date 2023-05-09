section "Dequeue Proofs"

theory RealTimeDeque_Dequeue_Proof
imports Deque RealTimeDeque_Aux States_Proof
begin
 
lemma list_deqL' [simp]: "\<lbrakk>invar deque; listL deque \<noteq> []; deqL' deque = (x, deque')\<rbrakk>
   \<Longrightarrow> x # listL deque' = listL deque"
proof(induction deque arbitrary: x rule: deqL'.induct)
  case (4 left right length_right)

  then obtain left' where pop_left[simp]: "Idle.pop left = (x, left')"
    by(auto simp: Let_def split: if_splits stack.splits prod.splits idle.splits)

  then obtain stack_left' length_left' 
    where left'[simp]: "left' = idle.Idle stack_left' length_left'"
    using idle.exhaust by blast

  from 4 have invar_left': "invar left'"
    using Idle_Proof.invar_pop[of left]
    by auto

  then have size_left' [simp]: "size stack_left' = length_left'"
    by auto

  have size_left'_size_left [simp]: "size stack_left' = (size left) - 1"
    using Idle_Proof.size_pop_sub[of left x left']
    by auto

  show ?case
  proof(cases "3 * length_left' \<ge> length_right")
    case True
    with 4 pop_left show ?thesis
      using Idle_Proof.pop_list[of left x left']
      by auto
  next
    case False
    note Start_Rebalancing = False

    then show ?thesis
    proof(cases "length_left' \<ge> 1")
      case True
      let ?big = "Big1 (Current [] 0 right (size right - Suc length_left')) 
                           right [] (size right - Suc length_left')"
      let ?small = "Small1 (Current [] 0 stack_left' (Suc (2 * length_left'))) stack_left' []"
      let ?states = "States Left ?big ?small"

      from 4 Start_Rebalancing True invar_left' have invar: "invar ?states"
        by(auto simp: Let_def rev_take rev_drop)

      with 4 Start_Rebalancing True invar_left'
      have "States_Aux.listL ?states = tl (Idle_Aux.list left) @ rev (Stack_Aux.list right)"
        using pop_list_tl'[of left x left'] 
        by (auto simp del: take_rev_def)
    
      with invar 
      have "States_Aux.listL ((step^^6) ?states) = 
            tl (Idle_Aux.list left) @ rev (Stack_Aux.list right)"
        using step_n_listL[of ?states 6]
        by presburger
      
      with 4 Start_Rebalancing True show ?thesis 
        by(auto simp: Let_def)
    next
      case False
      from False Start_Rebalancing 4 have [simp]:"size left = 1"
        using size_left' size_left'_size_left by auto
        
      with False Start_Rebalancing 4 have [simp]: "Idle_Aux.list left = [x]"
        by(induction left)(auto simp: length_one_hd split: stack.splits)

      obtain right1 right2 where "right = Stack right1 right2"
        using Stack_Aux.list.cases by blast

      with False Start_Rebalancing 4 show ?thesis 
        by(induction right1 right2 rule: small_deque.induct) auto
    qed 
  qed
next
  case (5 big small)

  then have start_invar: "invar (States Left big small)"
    by auto

  from 5 have small_invar: "invar small"
    by auto

  from 5 have small_size: "0 < size small"
    by auto

  with 5(3) obtain small' where pop: "Small.pop small = (x, small')"
    by(cases small)
      (auto simp: Let_def split: states.splits direction.splits state_splits prod.splits)

  let ?states_new = "States Left big small'"
  let ?states_stepped = "(step^^4) ?states_new"

  have invar: "invar ?states_new"
    using pop start_invar small_size invar_pop_small[of Left big small x small']
    by auto

  have "x # Small_Aux.list_current small' = Small_Aux.list_current small"
    using small_invar small_size pop Small_Proof.pop_list_current[of small x small'] by auto
    
  then have listL: 
      "x # States_Aux.listL ?states_new = 
       Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    using invar small_size Small_Proof.pop_list_current[of small x small'] 5(1)
    by auto      

  from invar have "invar ?states_stepped"
    using invar_step_n by blast

  then have states_listL_list_current [simp]: "x # States_Aux.listL ?states_stepped = 
                Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    using States_Proof.step_n_listL invar listL by metis

  then have "listL (deqL (Rebal (States Left big small))) = States_Aux.listL ?states_stepped"
    by(auto simp: Let_def pop split: prod.splits direction.splits states.splits state_splits)

  then have states_listL_list_current: 
      "x # listL (deqL (Rebal (States Left big small))) =
       Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    by auto

  with 5(1) have "listL (Rebal (States Left big small)) = 
                  Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    by auto

  with states_listL_list_current 
  have "x # listL (deqL (Rebal (States Left big small))) = 
        listL (Rebal (States Left big small))"
    by auto

  with 5 show ?case by auto
next
  case (6 big small)
  then have start_invar: "invar (States Right big small)"
    by auto

  from 6 have big_invar: "invar big"
    by auto

  from 6 have big_size: "0 < size big"
    by auto

  with 6(3) obtain big' where pop: "Big.pop big = (x, big')"
    by(cases big)
      (auto simp: Let_def split: prod.splits direction.splits states.splits state_splits)

  let ?states_new = "States Right big' small"
  let ?states_stepped = "(step^^4) ?states_new"

  have invar: "invar ?states_new"
    using pop start_invar big_size invar_pop_big[of Right big small]
    by auto

  have big_list_current: "x # Big_Aux.list_current big' = Big_Aux.list_current big"
    using big_invar big_size pop by auto
    
  then have listL: 
    "x # States_Aux.listL ?states_new = 
     Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    proof(cases "States_Aux.lists ?states_new")
      case (Pair bigs smalls)
      with invar big_list_current show ?thesis
        using app_rev[of smalls bigs]
        by(auto split: prod.splits)
    qed

  from invar have four_steps: "invar ?states_stepped"
    using invar_step_n by blast

  then have [simp]: 
      "x # States_Aux.listL ?states_stepped = 
       Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    using States_Proof.step_n_listL[of ?states_new 4] invar listL
    by auto

  then have "listL (deqL (Rebal (States Right big small))) = 
              States_Aux.listL ?states_stepped"
    by(auto simp: Let_def pop split: prod.splits direction.splits states.splits state_splits)

  then have listL_list_current: 
      "x # listL (deqL (Rebal (States Right big small))) = 
       Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    by auto

  with 6(1) have "listL (Rebal (States Right big small)) = 
                  Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    using invar_list_big_first[of "States Right big small"] by fastforce

  with listL_list_current have 
    "x # listL (deqL (Rebal (States Right big small))) = 
     listL (Rebal (States Right big small))"
    by auto

  with 6 show ?case by auto
qed auto

lemma list_deqL [simp]:
    "\<lbrakk>invar deque; listL deque \<noteq> []\<rbrakk> \<Longrightarrow> listL (deqL deque) = tl (listL deque)"
  using cons_tl[of "fst (deqL' deque)" "listL (deqL deque)" "listL deque"]
  by(auto split: prod.splits)

lemma list_firstL [simp]:
    "\<lbrakk>invar deque; listL deque \<noteq> []\<rbrakk> \<Longrightarrow> firstL deque = hd (listL deque)"
  using cons_hd[of "fst (deqL' deque)" "listL (deqL deque)" "listL deque"] 
  by(auto split: prod.splits)

lemma invar_deqL:
    "\<lbrakk>invar deque; \<not> is_empty deque\<rbrakk> \<Longrightarrow> invar (deqL deque)"
proof(induction deque rule: deqL'.induct)
  case (4 left right length_right)
  then obtain x left' where pop_left[simp]: "Idle.pop left = (x, left')"
    by fastforce

  then obtain stack_left' length_left' 
    where left'[simp]: "left' = idle.Idle stack_left' length_left'"
    using idle.exhaust by blast

  from 4 have invar_left': "invar left'" "invar left"
    using Idle_Proof.invar_pop by fastforce+

  have [simp]: "size stack_left' = size left - 1" 
    by (metis Idle_Proof.size_pop_sub left' pop_left size_idle.simps)

  have [simp]: "length_left' = size left - 1" 
    using invar_left' by auto

  from 4 have list: "x # Idle_Aux.list left' = Idle_Aux.list left"
    using Idle_Proof.pop_list[of left x left']
    by auto

  show ?case 
  proof(cases "length_right \<le> 3 * size left'")
    case True
    with 4 invar_left' show ?thesis
      by(auto simp: Stack_Proof.size_empty[symmetric])
  next
    case False
    note Start_Rebalancing = False
    then show ?thesis 
    proof(cases "1 \<le> size left'")
      case True
      let ?big = 
        "Big1 
            (Current [] 0 right (size right - Suc length_left')) 
            right [] (size right - Suc length_left')"
      let ?small = "Small1 (Current [] 0 stack_left' (Suc (2 * length_left'))) stack_left' []"
      let ?states = "States Left ?big ?small"

      from 4 Start_Rebalancing True invar_left' 
      have invar: "invar ?states"
        by(auto simp: Let_def rev_take rev_drop)

      then have invar_stepped: "invar ((step^^6) ?states)"
        using invar_step_n by blast

      from 4 Start_Rebalancing True 
      have remaining_steps: "6 < remaining_steps ?states"
        by auto

      then have remaining_steps_end: "0 < remaining_steps ((step^^6) ?states)"
        by(simp only: remaining_steps_n_steps_sub[of ?states 6] invar)

      from 4 Start_Rebalancing True  
      have size_ok': "size_ok' ?states (remaining_steps ?states - 6)"
        by auto
         
      then have size_ok: "size_ok ((step^^6) ?states)"
        using invar remaining_steps size_ok_steps by blast

      from True Start_Rebalancing 4 show ?thesis
        using remaining_steps_end size_ok invar_stepped
        by(auto simp: Let_def)
    next
      case False
      from False Start_Rebalancing 4 have [simp]: "size left = 1"
        by auto
        
      with False Start_Rebalancing 4 have [simp]: "Idle_Aux.list left = [x]"  
        using list[symmetric]
        by(auto simp: list Stack_Proof.list_empty_size)
     
      obtain right1 right2 where "right = Stack right1 right2"
        using Stack_Aux.list.cases by blast

      with False Start_Rebalancing 4 show ?thesis 
        by(induction right1 right2 rule: small_deque.induct) auto
    qed
  qed
next
  case (5 big small)
  
  obtain x small' where small' [simp]: "Small.pop small = (x, small')"
    by fastforce

  let ?states = "States Left big small'"
  let ?states_stepped = "(step^^4) ?states"

  obtain big_stepped small_stepped where stepped [simp]: 
       "?states_stepped = States Left big_stepped small_stepped"
     by (metis remaining_steps_states.cases step_n_same)

  from 5 have invar: "invar ?states"
    using invar_pop_small[of Left big small x small']
    by auto

  then have invar_stepped: "invar ?states_stepped"
    using invar_step_n by blast

  show ?case
  proof(cases "4 < remaining_steps ?states")
    case True

    then have remaining_steps: "0 < remaining_steps ?states_stepped"
      using invar remaining_steps_n_steps_sub[of ?states 4]
      by simp

    from True have size_ok: "size_ok ?states_stepped"
      using step_4_pop_small_size_ok[of Left big small x small'] 5(1)
      by auto

    from remaining_steps size_ok invar_stepped show ?thesis
      by(cases big_stepped; cases small_stepped) (auto simp: Let_def split!: common_state.split)
  next
    case False
    then have remaining_steps_stepped: "remaining_steps ?states_stepped = 0"
      using invar by(auto simp del: stepped)

    then obtain small_current small_idle big_current big_idle where idle [simp]: "
      States Left big_stepped small_stepped = 
      States Left 
          (Big2 (common_state.Idle big_current big_idle))
          (Small3 (common_state.Idle small_current small_idle))
      "
      using remaining_steps_idle' invar_stepped remaining_steps_stepped
      by fastforce

    have size_new_small : "1 < size_new small" 
      using 5 by auto

    have [simp]: "size_new small = Suc (size_new small')" 
      using 5 by auto

    have [simp]: "size_new small' = size_new small_stepped"
      using invar step_n_size_new_small stepped
      by metis

    have [simp]: "size_new small_stepped = size small_idle" 
      using idle invar_stepped
      by(cases small_stepped) auto

    have [simp]: "\<not>is_empty small_idle"
      using size_new_small
      by (simp add: Idle_Proof.size_not_empty)

    have [simp]: "size_new big = size_new big_stepped"
      by (metis invar step_n_size_new_big stepped)

    have [simp]: "size_new big_stepped = size big_idle" 
      using idle invar_stepped
      by(cases big_stepped) auto
      
    have "0 < size big_idle" 
      using 5 by auto
  
    then have [simp]: "\<not>is_empty big_idle"
      by (auto simp: Idle_Proof.size_not_empty)

    have [simp]: "size small_idle \<le> 3 * size big_idle"
      using 5 by auto

    have [simp]: "size big_idle \<le> 3 * size small_idle"
      using 5 by auto

    show ?thesis
      using invar_stepped by auto 
  qed
next
  case (6 big small)
  
  obtain x big' where big' [simp]: "Big.pop big = (x, big')"
    by fastforce

  let ?states = "States Right big' small"
  let ?states_stepped = "(step^^4) ?states"

  obtain big_stepped small_stepped where stepped [simp]: 
       "?states_stepped = States Right big_stepped small_stepped"
     by (metis remaining_steps_states.cases step_n_same)

  from 6 have invar: "invar ?states"
    using invar_pop_big[of Right big small x big']
    by auto

  then have invar_stepped: "invar ?states_stepped"
    using invar_step_n by blast

  show ?case
  proof(cases "4 < remaining_steps ?states")
    case True

    then have remaining_steps: "0 < remaining_steps ?states_stepped"
      using invar remaining_steps_n_steps_sub[of ?states 4]
      by simp

    from True have size_ok: "size_ok ?states_stepped"
      using step_4_pop_big_size_ok[of Right big small x big'] 6(1)
      by auto

    from remaining_steps size_ok invar_stepped show ?thesis
      by(cases big_stepped; cases small_stepped) (auto simp: Let_def split!: common_state.split)
  next
    case False
    then have remaining_steps_stepped: "remaining_steps ?states_stepped = 0"
      using invar by(auto simp del: stepped)

    then obtain small_current small_idle big_current big_idle where idle [simp]: "
      States Right big_stepped small_stepped = 
      States Right 
          (Big2 (common_state.Idle big_current big_idle))
          (Small3 (common_state.Idle small_current small_idle))
      "
      using remaining_steps_idle' invar_stepped remaining_steps_stepped
      by fastforce

    have size_new_big : "1 < size_new big" 
      using 6 by auto

    have [simp]: "size_new big = Suc (size_new big')" 
      using 6 by auto

    have [simp]: "size_new big' = size_new big_stepped"
      using invar step_n_size_new_big stepped
      by metis

    have [simp]: "size_new big_stepped = size big_idle" 
      using idle invar_stepped
      by(cases big_stepped) auto

    have [simp]: "\<not>is_empty big_idle"
      using size_new_big
      by (simp add: Idle_Proof.size_not_empty)

    have [simp]: "size_new small = size_new small_stepped"
      by (metis invar step_n_size_new_small stepped)

    have [simp]: "size_new small_stepped = size small_idle" 
      using idle invar_stepped
      by(cases small_stepped) auto
      
    have "0 < size small_idle" 
      using 6 by auto
  
    then have [simp]: "\<not>is_empty small_idle"
      by (auto simp: Idle_Proof.size_not_empty)

    have [simp]: "size big_idle \<le> 3 * size small_idle"
      using 6 by auto

    have [simp]: "size small_idle \<le> 3 * size big_idle"
      using 6 by auto

    show ?thesis
      using invar_stepped by auto 
  qed
qed auto

end
