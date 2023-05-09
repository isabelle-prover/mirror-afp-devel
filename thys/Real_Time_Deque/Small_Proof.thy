section "Small Proofs"

theory Small_Proof 
imports Common_Proof Small_Aux
begin

lemma step_size [simp]: "invar (small :: 'a small_state) \<Longrightarrow> size (step small) = size small"
  by(induction small rule: step_small_state.induct)(auto split: current.splits)

lemma step_size_new [simp]: 
    "invar (small :: 'a small_state) \<Longrightarrow> size_new (step small) = size_new small"
  by(induction small rule: step_small_state.induct)(auto split: current.splits)

lemma size_push [simp]: "invar small \<Longrightarrow> size (push x small) = Suc (size small)"
  by(induction x small rule: push.induct) (auto split: current.splits)

lemma size_new_push [simp]: "invar small \<Longrightarrow> size_new (push x small) = Suc (size_new small)"
  by(induction x small rule: push.induct) (auto split: current.splits)  

lemma size_pop [simp]: "\<lbrakk>invar small; 0 < size small; pop small = (x, small')\<rbrakk>
   \<Longrightarrow> Suc (size small') = size small"
proof(induction small rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto split: prod.splits)
next
  case (2 current small auxS)
  then show ?case
    using Current_Proof.size_pop[of current] 
    by(induction current rule: Current.pop.induct) auto
next
  case (3 current auxS big newS count)
  then show ?case 
    using Current_Proof.size_pop[of current] 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_new_pop [simp]: "\<lbrakk>invar small; 0 < size_new small; pop small = (x, small')\<rbrakk>
   \<Longrightarrow> Suc (size_new small') = size_new small"
proof(induction small rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto split: prod.splits)
next
  case (2 current small auxS)
  then show ?case 
  by(induction current rule: Current.pop.induct) auto
next
  case (3 current auxS big newS count)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_size_new: "\<lbrakk>invar (small :: 'a small_state); 0 < size small\<rbrakk> \<Longrightarrow> 0 < size_new small"
  by(induction small)(auto simp: size_size_new)

lemma step_list_current [simp]: "invar small \<Longrightarrow> list_current (step small) = list_current small"
  by(induction small rule: step_small_state.induct)(auto split: current.splits)

lemma step_list_common [simp]:
    "\<lbrakk>small = Small3 common; invar small\<rbrakk> \<Longrightarrow> list (step small) = list small"
  by auto

lemma step_list_Small2 [simp]: 
  assumes
    "small = (Small2 current aux big new count)" 
    "invar small"
  shows
    "list (step small) = list small"
proof -

  have size_not_empty: "(0 < size big) = (\<not> is_empty big)"
    by (simp add: Stack_Proof.size_not_empty)

  have "\<not> is_empty big
     \<Longrightarrow> rev (Stack_Aux.list (Stack.pop big)) @ [Stack.first big] = rev (Stack_Aux.list big)"
    by(induction big rule: Stack.pop.induct) auto

  with assms show ?thesis 
    using Stack_Proof.size_pop[of big] size_not_empty
    by(auto simp: Stack_Proof.list_empty split: current.splits)
qed
  
lemma invar_step: "invar (small :: 'a small_state) \<Longrightarrow> invar (step small)" 
proof(induction small rule: step_small_state.induct)
  case (1 state)
  then show ?case 
    by(auto simp: invar_step)
next
  case (2 current small aux)
  then show ?case
  proof(cases "is_empty small")
      case True
      with 2 show ?thesis
        by auto
    next
      case False

      with 2 have "rev (Stack_Aux.list small) @ aux = 
                   rev (Stack_Aux.list (Stack.pop small)) @ Stack.first small # aux" 
        by(auto simp: rev_app_single Stack_Proof.list_not_empty)

      with 2 show ?thesis 
        by(auto split: current.splits)
    qed 
next
  case (3 current auxS big newS count)
  then show ?case
  proof(cases "is_empty big")
    case True

    then have big_size [simp]: "size big = 0"
      by (simp add: Stack_Proof.size_empty)
    
    with True 3 show ?thesis
    proof(cases current)
      case (Current extra added old remained)
      with 3 True show ?thesis
      proof(cases "remained \<le> count")
        case True
        with 3 Current show ?thesis
          using Stack_Proof.size_empty[of big]
          by auto
      next
        case False
        with True 3 Current show ?thesis 
          by(auto)
        qed
    qed
  next
    case False
    with 3 show ?thesis 
      using Stack_Proof.size_pop[of big]
      by(auto simp: Stack_Proof.size_not_empty split: current.splits)
  qed
qed

lemma invar_push: "invar small \<Longrightarrow> invar (push x small)"
  by(induction x small rule: push.induct)(auto simp: invar_push split: current.splits)

lemma invar_pop: "\<lbrakk>
  0 < size small; 
  invar small;
  pop small = (x, small')
\<rbrakk> \<Longrightarrow> invar small'"
proof(induction small arbitrary: x rule: pop.induct)
case (1 state)
  then show ?case 
    by(auto simp: invar_pop split: prod.splits)
next
  case (2 current small auxS)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then show ?case 
      by(cases "size small < size old")
        (auto simp: rev_take Suc_diff_le drop_Suc tl_drop)
  next
    case 2
    then show ?case by auto
  qed
next
  case (3 current auxS big newS count)
  then show ?case
    by (induction current rule: Current.pop.induct)
       (auto simp: rev_take Suc_diff_le drop_Suc tl_drop)
qed

lemma push_list_common [simp]: "small = Small3 common \<Longrightarrow> list (push x small) = x # list small"
  by auto

lemma push_list_current [simp]: "list_current (push x small) = x # list_current small"
  by(induction x small rule: push.induct) auto

lemma pop_list_current [simp]: "\<lbrakk>invar small; 0 < size small; Small.pop small = (x, small')\<rbrakk>
  \<Longrightarrow> x # list_current small' = list_current small"
proof(induction small arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: pop_list_current split: prod.splits)
next
  case (2 current small auxS)
  then have "invar current" 
    by(auto split: current.splits)

  with 2 show ?case 
    by auto
next
  case (3 current auxS big newS count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    then have "\<not>is_empty old" 
      by(auto simp: Stack_Proof.size_not_empty)

    with 1 show ?case 
      by(auto simp: rev_take drop_Suc drop_tl)
  next
    case 2
    then show ?case 
      by auto
  qed
qed

lemma list_current_size [simp]: "\<lbrakk>0 < size small; list_current small = []; invar small\<rbrakk> \<Longrightarrow> False"
proof(induction small)
  case (Small1 current)
  then have "invar current" 
    by(auto split: current.splits)

  with Small1 show ?case 
    using Current_Proof.list_size
    by auto
next
  case Small2
  then show ?case 
    by(auto split: current.splits)
next
  case Small3
  then show ?case 
    using list_current_size by auto
qed

lemma list_Small2 [simp]: "\<lbrakk>
  0 < size (Small2 current auxS big newS count); 
  invar (Small2 current auxS big newS count)
\<rbrakk> \<Longrightarrow>
   fst (Current.pop current) # list (Small2 (drop_first current) auxS big newS count) =
   list (Small2 current auxS big newS count)"
  by(induction current rule: Current.pop.induct)
    (auto simp: first_hd rev_take Suc_diff_le)

end