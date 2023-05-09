section "Common Proofs"

theory Common_Proof
imports Common_Aux Idle_Proof Current_Proof
begin

lemma take_rev_drop: "take_rev n xs @ acc = drop (length xs - n) (rev xs) @ acc"
  unfolding take_rev_def using rev_take by blast

lemma take_rev_step: "xs \<noteq> [] \<Longrightarrow> take_rev n (tl xs) @ (hd xs # acc) = take_rev (Suc n) xs @ acc"
  by (simp add: take_Suc)

lemma take_rev_empty [simp]: "take_rev n [] = []"
  by simp

lemma take_rev_tl_hd: 
    "0 < n \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> take_rev  n xs @ ys = take_rev (n - (Suc 0)) (tl xs) @ (hd xs #ys)"
  by (simp add: take_rev_step del: take_rev_def)

lemma take_rev_nth: 
    "n < length xs \<Longrightarrow> x = xs ! n \<Longrightarrow> x # take_rev n xs @ ys = take_rev (Suc n) xs @ ys"
  by (simp add: take_Suc_conv_app_nth)

lemma step_list [simp]: "invar common \<Longrightarrow> list (step common) = list common"
proof(induction common rule: step_common_state.induct)
  case (1 idle)
  then show ?case by auto
next
  case (2 current aux new moved)

  then show ?case 
  proof(cases current)
    case (Current extra added old remained)
    
    with 2 have aux_not_empty: "aux \<noteq> []"
        by auto

    from 2 Current show ?thesis 
    proof(cases "remained \<le> Suc moved")
      case True
     
      with 2 Current have "remained - length new = 1"
        by auto

      with True Current 2 aux_not_empty show ?thesis 
        by auto
    next
      case False
      with Current show ?thesis 
        by(auto simp: aux_not_empty take_rev_step Suc_diff_Suc simp del: take_rev_def)
    qed
  qed
qed

lemma step_list_current [simp]: "invar common \<Longrightarrow> list_current (step common) = list_current common"
  by(cases common)(auto split: current.splits)

lemma push_list [simp]: "list (push x common) = x # list common"
proof(induction x common rule: push.induct)
  case (1 x stack stackSize)
  then show ?case 
    by auto
next
  case (2 x current aux new moved)
  then show ?case 
    by(induction x current rule: Current.push.induct) auto
qed

lemma invar_step: "invar (common :: 'a common_state) \<Longrightarrow> invar (step common)" 
proof(induction "common" rule: invar_common_state.induct)
  case (1 idle)
  then show ?case
    by auto
next
  case (2 current aux new moved)
  then show ?case
  proof(cases current)
    case (Current extra added old remained)
    then show ?thesis
    proof(cases "aux = []")
      case True
      with 2 Current show ?thesis by auto 
    next
      case False
      note AUX_NOT_EMPTY = False

      then show ?thesis
      proof(cases "remained \<le> Suc (length new)")
        case True
        with 2 Current False 
          have "take (Suc (length new)) (Stack_Aux.list old) = take (size old) (hd aux # new)"
            by(auto simp: le_Suc_eq take_Cons')
         
        with 2 Current True show ?thesis 
          by auto
      next
        case False
        with 2 Current AUX_NOT_EMPTY show ?thesis 
          by(auto simp: take_rev_step Suc_diff_Suc simp del: take_rev_def)
      qed
    qed
  qed
qed

lemma invar_push: "invar common \<Longrightarrow> invar (push x common)"
proof(induction x common rule: push.induct)
  case (1 x current stack stackSize)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case
    proof(induction x stack rule: Stack.push.induct)
      case (1 x left right)
      then show ?case by auto
    qed
  qed
next
  case (2 x current aux new moved)
  then show ?case
  proof(induction x current rule: Current.push.induct)
    case (1 x extra added old remained)
    then show ?case by auto
  qed
qed

lemma invar_pop: "\<lbrakk>
  0 < size common; 
  invar common;
  pop common = (x, common')
\<rbrakk> \<Longrightarrow> invar common'"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then obtain idle' where idle: "Idle.pop idle = (x, idle')"
    by(auto split: prod.splits)

  obtain current' where current: "drop_first current = current'"
    by auto

  from 1 current idle show ?case 
    using Idle_Proof.size_pop[of idle x idle', symmetric] 
        size_new_pop[of current] 
        size_pop_sub[of current _ current']
    by(auto simp: Idle_Proof.invar_pop invar_pop eq_snd_iff take_tl size_not_empty)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
    proof(cases "remained - Suc 0 \<le> length new")
      case True

      with 1 have [simp]: 
          "0 < size old" 
          "Stack_Aux.list old \<noteq> []" 
          "aux \<noteq> []"
          "length new = remained - Suc 0"
        by(auto simp: Stack_Proof.size_not_empty Stack_Proof.list_not_empty)

      then have [simp]: "Suc 0 \<le> size old" 
        by linarith

      from 1 have "0 < remained"
        by auto

      then have "take remained (Stack_Aux.list old)
          = hd (Stack_Aux.list old) # take (remained - Suc 0) (tl (Stack_Aux.list old))"
        by (metis Suc_pred \<open>Stack_Aux.list old \<noteq> []\<close> list.collapse take_Suc_Cons)

      with 1 True show ?thesis 
        using Stack_Proof.pop_list[of old] 
        by(auto simp: Stack_Proof.size_not_empty)
    next
      case False
      with 1 have "remained - Suc 0 \<le> length aux + length new" by auto

      with 1 False show ?thesis 
        using Stack_Proof.pop_list[of old]
        apply(auto simp: Suc_diff_Suc take_tl Stack_Proof.size_not_empty tl_append_if)
        by (simp add: Suc_diff_le rev_take tl_drop_2 tl_take)
    qed
   next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma push_list_current [simp]: "list_current (push x left) = x # list_current left"
  by(induction x left rule: push.induct) auto

lemma pop_list [simp]: "invar common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common') \<Longrightarrow>
   x # list common' = list common"
proof(induction common arbitrary: x rule: pop.induct)
  case 1
  then show ?case
    by(auto simp: size_not_empty split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case
    proof(cases "remained - Suc 0 \<le> length new")
      case True

      from 1 True have [simp]: 
          "aux \<noteq> []" "0 < remained" 
          "Stack_Aux.list old \<noteq> []" "remained - length new = 1"
        by(auto simp: Stack_Proof.size_not_empty Stack_Proof.list_not_empty)

      then have "take remained (Stack_Aux.list old) = hd aux # take (size old - Suc 0) new
             \<Longrightarrow> Stack.first old = hd aux"
        by (metis first_hd hd_take list.sel(1))
     
      with 1 True take_hd[of aux] show ?thesis 
        by(auto simp: Suc_leI)
    next
      case False
      then show ?thesis 
      proof(cases "remained - length new = length aux")
        case True

        then have length_minus_1: "remained - Suc (length new) = length aux - 1"
          by simp

        from 1 have not_empty: "0 < remained" "0 < size old"  "aux \<noteq> []" "\<not> is_empty old"
          by(auto simp: Stack_Proof.size_not_empty)

        from 1 True not_empty have "take 1 (Stack_Aux.list old) = take 1 (rev aux)"
          using take_1[of 
                remained 
                "size old" 
                "Stack_Aux.list old"  
                "(rev aux) @ take (size old + length new - remained) new"
                ] 
          by(simp)
         
        then have "[last aux] = [Stack.first old]"
          using take_last first_take not_empty
          by fastforce

        then have "last aux = Stack.first old"
          by auto

        with 1 True False show ?thesis 
          using not_empty last_drop_rev[of aux]
          by(auto simp: take_rev_drop length_minus_1 simp del: take_rev_def)
       next
        case False

        with 1 have a: "take (remained - length new) aux \<noteq> []"
          by auto

        from 1 False have b: "\<not> is_empty old"
          by(auto simp: Stack_Proof.size_not_empty)

        from 1 have c: "remained - Suc (length new) < length aux"
          by auto

        from 1 have not_empty: 
            "0 < remained" 
            "0 < size old" 
            "0 < remained - length new" 
            "0 < length aux" 
          by auto

        with False have 
           "take remained (Stack_Aux.list old) =
            take (size old) (take_rev (remained - length new) aux @ new)
            \<Longrightarrow> take (Suc 0) (Stack_Aux.list old) =
                take (Suc 0) (rev (take (remained - length new) aux))"
          using take_1[of
                remained 
                "size old" 
                "Stack_Aux.list old" 
                " (take_rev (remained - length new) aux @ new)"
              ]
          by(auto simp: not_empty Suc_le_eq)

        with 1 False have 
            "take 1 (Stack_Aux.list old) = take 1 (rev (take (remained - length new) aux))"
          by auto
          
        then have d: "[Stack.first old] = [last (take (remained - length new) aux)]"
          using take_last first_take a b
          by metis

        have "last (take (remained - length new) aux) # rev (take (remained - Suc (length new)) aux) 
            = rev (take (remained - length new) aux)"
          using Suc_diff_Suc c not_empty
          by (metis a drop_drop last_drop_rev plus_1_eq_Suc rev_take zero_less_diff)
          
        with 1(1) 1(3) False not_empty d show ?thesis 
          by(cases "remained - length new = 1") (auto)
      qed
    qed
  next
    case 2
    then show ?case by auto
  qed
qed

lemma pop_list_current: "invar common \<Longrightarrow> 0 < size common \<Longrightarrow> pop common = (x, common')
   \<Longrightarrow> x # list_current common' = list_current common"
proof(induction common arbitrary: x rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case (1 stack stackSize)
    then show ?case
    proof(induction current rule: Current.pop.induct)
      case (1 added old remained)
      then have "Stack.first old = Stack.first stack"
        using take_first[of old stack]
        by auto

      with 1 show ?case 
        by(auto simp: Stack_Proof.size_not_empty Stack_Proof.list_not_empty)
    next
      case (2 x xs added old remained)
      then have "0 < size stack" 
        by auto

      with Stack_Proof.size_not_empty Stack_Proof.list_not_empty
      have not_empty: "\<not> is_empty stack" "Stack_Aux.list stack \<noteq> []"
        by auto

      with 2 have "hd (Stack_Aux.list stack) = x"
        using take_hd'[of "Stack_Aux.list stack" x "xs @ Stack_Aux.list old"]
        by auto
       
      with 2 show ?case 
        using first_list[of stack] not_empty
        by auto
    qed
  qed
next
  case (2 current)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then have "\<not> is_empty old"
      by(auto simp: Stack_Proof.size_not_empty)

    with 1 show ?case
      using first_pop
      by(auto simp: Stack_Proof.list_not_empty)
  next
    case 2
    then show ?case by auto
  qed
qed

lemma list_current_size [simp]: 
  "\<lbrakk>0 < size common; list_current common = []; invar common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invar_common_state.induct)
  case 1
  then show ?case
    using list_size by auto
next
  case (2 current)
  then have "invar current" 
            "Current_Aux.list current = []"  
            "0 < size current" 
    by(auto split: current.splits)
 
  then show ?case using list_size by auto
qed

lemma list_size [simp]: "\<lbrakk>0 < size common; list common = []; invar common\<rbrakk> \<Longrightarrow> False"
proof(induction common rule: invar_common_state.induct)
  case 1
  then show ?case
    using list_size Idle_Proof.size_empty
    by auto
next
  case (2 current aux new moved)
  then have "invar current" 
            "Current_Aux.list current = []"  
            "0 < size current" 
    by(auto split: current.splits)
 
  then show ?case using list_size by auto
qed
  
lemma step_size [simp]: "invar (common :: 'a common_state) \<Longrightarrow> size (step common) = size common"
proof(induction common rule: step_common_state.induct)
  case 1
  then show ?case by auto
next
  case 2
  then show ?case 
    by(auto simp: min_def split: current.splits)
qed

lemma step_size_new [simp]: "invar (common :: 'a common_state)
   \<Longrightarrow> size_new (step common) = size_new common"
proof(induction common rule: step_common_state.induct)
  case (1 current idle)
  then show ?case by auto
next
  case (2 current aux new moved)
  then show ?case by(auto split: current.splits)
qed

lemma remaining_steps_step [simp]: "\<lbrakk>invar (common :: 'a common_state); remaining_steps common > 0\<rbrakk>
   \<Longrightarrow> Suc (remaining_steps (step common)) = remaining_steps common"
  by(induction common)(auto split: current.splits)

lemma remaining_steps_step_sub [simp]: "\<lbrakk>invar (common :: 'a common_state)\<rbrakk>
 \<Longrightarrow> remaining_steps (step common) = remaining_steps common - 1"
  by(induction common)(auto split: current.splits)

lemma remaining_steps_step_0 [simp]: "\<lbrakk>invar (common :: 'a common_state); remaining_steps common = 0\<rbrakk>
   \<Longrightarrow> remaining_steps (step common) = 0"
  by(induction common)(auto split: current.splits)

lemma remaining_steps_push [simp]: "invar common
   \<Longrightarrow> remaining_steps (push x common) = remaining_steps common"
  by(induction x common rule: Common.push.induct)(auto split: current.splits)

lemma remaining_steps_pop: "\<lbrakk>invar common; pop common = (x, common')\<rbrakk> 
  \<Longrightarrow> remaining_steps common' \<le> remaining_steps common"
proof(induction common rule: pop.induct)
  case (1 current idle)
  then show ?case 
  proof(induction idle rule: Idle.pop.induct)
    case 1
    then show ?case  
      by(induction current rule: Current.pop.induct) auto
  qed
next
  case (2 current aux new moved)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_push [simp]: "invar common \<Longrightarrow> size (push x common) = Suc (size common)"
  by(induction x common rule: push.induct) (auto split: current.splits)
 
lemma size_new_push [simp]: "invar common \<Longrightarrow> size_new (push x common) = Suc (size_new common)"
  by(induction x common rule: Common.push.induct) (auto split: current.splits)

lemma size_pop [simp]: "\<lbrakk>invar common; 0 < size common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow> Suc (size common') = size common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case 
    using size_drop_first_sub[of current] Idle_Proof.size_pop_sub[of idle]
    by(auto simp: size_not_empty split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_new_pop [simp]: "\<lbrakk>invar common; 0 < size_new common; pop common = (x, common')\<rbrakk>
   \<Longrightarrow>  Suc (size_new common') = size_new common"
proof(induction common rule: Common.pop.induct)
  case (1 current idle)
  then show ?case
    using size_new_pop[of current]
    by(auto split: prod.splits)
next
  case (2 current aux new moved)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case by auto
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma size_size_new: "\<lbrakk>invar (common :: 'a common_state); 0 < size common\<rbrakk> \<Longrightarrow> 0 < size_new common"
  by(cases common) auto

end