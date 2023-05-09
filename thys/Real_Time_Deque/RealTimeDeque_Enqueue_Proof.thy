section "Enqueue Proofs"

theory RealTimeDeque_Enqueue_Proof
imports Deque RealTimeDeque_Aux States_Proof
begin

lemma list_enqL: "invar deque \<Longrightarrow> listL (enqL x deque) = x # listL deque"
proof(induction x deque rule: enqL.induct)
  case (5 x left right length_right)

  obtain left' length_left' where pushed [simp]: 
      "Idle.push x left = idle.Idle left' length_left'"
    using is_empty_idle.cases by blast

  then have invar_left': "invar (idle.Idle left' length_left')"
    using Idle_Proof.invar_push[of left x] 5 by auto

  show ?case
  proof(cases "length_left' \<le> 3 * length_right")
    case True
    then show ?thesis 
      using Idle_Proof.push_list[of x left]
      by(auto simp: Let_def)
  next
    case False
    let ?length_left = "length_left' - length_right - 1"
    let ?length_right = "2 * length_right + 1"
    let ?big = "Big1  (Current [] 0 left' ?length_left) left' [] ?length_left"
    let ?small = "Small1 (Current [] 0 right ?length_right) right []"
    let ?states = "States Right ?big ?small"
    let ?states_stepped = "(step^^6) ?states"

    from False 5 invar_left' have invar: "invar ?states"
      by(auto simp: rev_drop rev_take)

    then have "States_Aux.listL ?states = x # Idle_Aux.list left @ rev (Stack_Aux.list right)"
      using Idle_Proof.push_list[of x left]
      by(auto)

    then have "States_Aux.listL ?states_stepped = x # Idle_Aux.list left @ rev (Stack_Aux.list right)"
      by (metis invar step_n_listL)

    with False show ?thesis 
      by(auto simp: Let_def)
  qed
next
  case (6 x big small)
  let ?small = "Small.push x small"
  let ?states = "States Left big ?small"
  let ?states_stepped = "(step^^4) ?states"

  obtain big_stepped small_stepped where stepped:
      "?states_stepped = States Left big_stepped small_stepped"
    by (metis remaining_steps_states.cases step_n_same)

  from 6 have "invar ?states"
    using invar_push_small[of Left big small x]
    by auto
                        
  then have 
      "States_Aux.listL ?states_stepped = 
       x # Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    using step_n_listL by fastforce

  with 6 show ?case
    by(cases big_stepped; cases small_stepped)
      (auto simp: Let_def stepped split!: common_state.split)
next
  case (7 x big small)

  let ?big = "Big.push x big"
  let ?states = "States Right ?big small"
  let ?states_stepped = "(step^^4) ?states"

  obtain big_stepped small_stepped where stepped:
      "?states_stepped = States Right big_stepped small_stepped"
    by (metis remaining_steps_states.cases step_n_same)

   from 7 have list_invar:
    "list_current_small_first (States Right big small) = list_small_first (States Right big small)"
    by auto

  from 7 have invar: "invar ?states"
    using invar_push_big[of Right big small x]
    by auto
                        
  then have
      "States_Aux.listL ?states = x # Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    using app_rev[of _ _ _ "x # Big_Aux.list_current big"]
    by(auto split: prod.split)

  then have 
      "States_Aux.listL ?states_stepped = 
       x # Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    by (metis invar step_n_listL)

  with list_invar show ?case
    using app_rev[of "Small_Aux.list_current small" "Big_Aux.list_current big"]
    by(cases big_stepped; cases small_stepped)   
      (auto simp: Let_def stepped split!: prod.split common_state.split)
qed auto

lemma invar_enqL: "invar deque \<Longrightarrow> invar (enqL x deque)"
proof(induction x deque rule: enqL.induct)
  case (5 x left right length_right)
  obtain left' length_left' where pushed [simp]: 
      "Idle.push x left = idle.Idle left' length_left'"
    using is_empty_idle.cases by blast

  then have invar_left': "invar (idle.Idle left' length_left')"
    using Idle_Proof.invar_push[of left x] 5 by auto 

  have [simp]: "size left' = Suc (size left)"
    using Idle_Proof.size_push[of x left] 
    by auto 

  show ?case
  proof(cases "length_left' \<le> 3 * length_right")
    case True
    with 5 show ?thesis 
      using invar_left' Idle_Proof.size_push[of x left] Stack_Proof.size_not_empty[of left']
      by auto
  next
    case False
    let ?length_left = "length_left' - length_right - 1"
    let ?length_right = "Suc (2 * length_right)"
    let ?states = "States Right 
          (Big1 (Current [] 0 left' ?length_left) left' [] ?length_left)
          (Small1 (Current [] 0 right ?length_right) right [])"
    let ?states_stepped = "(step^^6) ?states"

    from invar_left' 5 False have invar: "invar ?states" 
      by(auto simp: rev_drop rev_take)

    then have invar_stepped: "invar ?states_stepped"
      using invar_step_n by blast 

    from False invar_left' 5 have remaining_steps: "6 < remaining_steps ?states" 
      using Stack_Proof.size_not_empty[of right]
      by auto

    then have remaining_steps_stepped: "0 < remaining_steps ?states_stepped" 
      using invar remaining_steps_n_steps_sub
      by (metis zero_less_diff)

    from False invar_left' 5 have "size_ok' ?states (remaining_steps ?states - 6)"
      using Stack_Proof.size_not_empty[of right] 
            size_not_empty
      by auto

    then have size_ok_stepped: "size_ok ?states_stepped" 
      using size_ok_steps[of ?states 6] remaining_steps invar
      by blast
   
    from False show ?thesis 
      using invar_stepped remaining_steps_stepped size_ok_stepped
      by(auto simp: Let_def)
  qed
next
  case (6 x big small)
  let ?small = "Small.push x small"
  let ?states = "States Left big ?small"
  let ?states_stepped = "(step^^4) ?states"

  from 6 have invar: "invar ?states"
    using invar_push_small[of Left big small x]
    by auto

  then have invar_stepped: "invar ?states_stepped"
    using invar_step_n by blast

  show ?case
   proof(cases "4 < remaining_steps ?states")
     case True

     obtain big_stepped small_stepped where stepped [simp]: 
       "?states_stepped = States Left big_stepped small_stepped"
       by (metis remaining_steps_states.cases step_n_same)
      
     from True have remaining_steps: "0 < remaining_steps ?states_stepped"
       using invar remaining_steps_n_steps_sub[of ?states 4]
       by simp

     from True 6(1) have size_ok: "size_ok ?states_stepped"
       using 
          step_4_push_small_size_ok[of Left big small x] 
          remaining_steps_push_small[of Left big small x]
       by auto

     from remaining_steps size_ok invar_stepped show ?thesis
       by(cases big_stepped; cases small_stepped) 
         (auto simp: Let_def split!: common_state.split)
   next
     case False
     then have remaining_steps_stepped: "remaining_steps ?states_stepped = 0"
       using invar by auto

     then obtain small_current small_idle big_current big_idle where idle [simp]: "
      ?states_stepped = 
      States Left 
          (Big2 (common_state.Idle big_current big_idle))
          (Small3 (common_state.Idle small_current small_idle))
      "
       using remaining_steps_idle' invar_stepped remaining_steps_stepped step_n_same
       by (smt (verit) invar_states.elims(2))

     from 6 have [simp]: "size_new (Small.push x small) = Suc (size_new small)"
       using Small_Proof.size_new_push by auto

     have [simp]: "size small_idle = size_new (Small.push x small)"
       using invar invar_stepped step_n_size_new_small[of Left big "Small.push x small" 4]
       by auto

     then have [simp]: "\<not>is_empty small_idle" 
       using Idle_Proof.size_not_empty[of small_idle]
       by auto

     have size_new_big [simp]: "0 < size_new big"
       using 6
       by auto

     then have [simp]: "size big_idle = size_new big"
       using invar invar_stepped step_n_size_new_big[of Left big "Small.push x small" 4]
       by auto
      
     then have [simp]: "\<not>is_empty big_idle" 
       using Idle_Proof.size_not_empty size_new_big
       by metis

     have size_ok_1: "size small_idle \<le> 3 * size big_idle"
       using 6 by auto

     have size_ok_2: "size big_idle \<le> 3 * size small_idle"
      using 6 by auto

     from False show ?thesis 
       using invar_stepped size_ok_1 size_ok_2
       by auto
   qed
next
  case (7 x big small)
  let ?big = "Big.push x big"
  let ?states = "States Right ?big small"
  let ?states_stepped = "(step^^4) ?states"

  from 7 have invar: "invar ?states"
    using invar_push_big[of Right big small x]
    by auto

  then have invar_stepped: "invar ?states_stepped"
    using invar_step_n by blast

  show ?case
   proof(cases "4 < remaining_steps ?states")
     case True
     
     obtain big_stepped small_stepped where stepped [simp]:
       "?states_stepped = States Right big_stepped small_stepped"
       by (metis remaining_steps_states.cases step_n_same)
      
     from True have remaining_steps: "0 < remaining_steps ?states_stepped"
       using invar remaining_steps_n_steps_sub[of ?states 4]
       by simp

     from True 7(1) have size_ok: "size_ok ?states_stepped"
       using 
          step_4_push_big_size_ok[of Right big small x] 
          remaining_steps_push_big[of Right big small x]
       by auto

     from remaining_steps size_ok invar_stepped show ?thesis
       by(cases big_stepped; cases small_stepped) 
         (auto simp: Let_def split!: common_state.split)
   next
     case False
     then have remaining_steps_stepped: "remaining_steps ?states_stepped = 0"
       using invar by auto

     then obtain small_current small_idle big_current big_idle where idle [simp]: "
      ?states_stepped = 
      States Right 
          (Big2 (common_state.Idle big_current big_idle))
          (Small3 (common_state.Idle small_current small_idle))
      "
       using remaining_steps_idle' invar_stepped remaining_steps_stepped step_n_same
       by (smt (verit) invar_states.elims(2))

     from 7 have [simp]: "size_new (Big.push x big) = Suc (size_new big)"
       using Big_Proof.size_new_push by auto

     have [simp]: "size big_idle = size_new (Big.push x big)"
       using invar invar_stepped step_n_size_new_big[of Right "Big.push x big" small 4]
       by auto

     then have [simp]: "\<not>is_empty big_idle" 
       using Idle_Proof.size_not_empty[of big_idle]
       by auto

     have size_new_small [simp]: "0 < size_new small"
       using 7
       by auto

     then have [simp]: "size small_idle = size_new small"
       using invar invar_stepped step_n_size_new_small[of Right "Big.push x big" small 4]
       by auto
      
     then have [simp]: "\<not>is_empty small_idle" 
       using Idle_Proof.size_not_empty size_new_small
       by metis

     have size_ok_1: "size small_idle \<le> 3 * size big_idle"
       using 7 by auto

     have size_ok_2: "size big_idle \<le> 3 * size small_idle"
      using 7 by auto

     from False show ?thesis 
       using invar_stepped size_ok_1 size_ok_2
       by auto
   qed
qed auto

end

