section \<open>Top-Level Proof\<close>

theory RealTimeDeque_Proof
imports RealTimeDeque_Dequeue_Proof RealTimeDeque_Enqueue_Proof
begin

lemma swap_lists_left: "invar (States Left big small) \<Longrightarrow> 
    States_Aux.listL (States Left big small) = rev (States_Aux.listL (States Right big small))"
  by(auto split: prod.splits big_state.splits small_state.splits)

lemma swap_lists_right: "invar (States Right big small) \<Longrightarrow> 
    States_Aux.listL (States Right big small) = rev (States_Aux.listL (States Left big small))"
  by(auto split: prod.splits big_state.splits small_state.splits)

lemma swap_list [simp]: "invar q \<Longrightarrow> listR (swap q) = listL q"
proof(induction q)
  case (Rebal states)
  then show ?case
    apply(cases states)
    using swap_lists_left swap_lists_right
    by (metis (full_types) RealTimeDeque_Aux.listL.simps(6) direction.exhaust invar_deque.simps(6) swap.simps(6) swap.simps(7))
qed auto

lemma swap_list': "invar q \<Longrightarrow> listL (swap q) = listR q"
  using swap_list rev_swap
  by blast

lemma lists_same: "lists (States Left big small) = lists (States Right big small)"
  by(induction "States Left big small" rule: lists.induct) auto

lemma invar_swap: "invar q \<Longrightarrow> invar (swap q)"
  by(induction q rule: swap.induct) (auto simp: lists_same split: prod.splits)

lemma listL_is_empty: "invar deque \<Longrightarrow> is_empty deque = (listL deque = [])"
  using Idle_Proof.list_empty listL_remaining_steps 
  by(cases deque) auto

interpretation RealTimeDeque: Deque where
  empty    = empty    and
  enqL     = enqL     and
  enqR     = enqR     and
  firstL   = firstL   and
  firstR   = firstR   and
  deqL     = deqL     and
  deqR     = deqR     and
  is_empty = is_empty and
  listL    = listL    and
  invar    = invar
proof (standard, goal_cases)
  case 1
  then show ?case 
    by (simp add: empty_def)
next
  case 2
  then show ?case
    by(simp add: list_enqL)
next
  case (3 q x)

  then have "listL (enqL x (swap q)) = x # listR q"
    by (simp add: list_enqL invar_swap swap_list')

  with 3 show ?case
    by (simp add: invar_enqL invar_swap)
next
  case 4
  then show ?case
    using list_deqL by simp
next
  case (5 q)
  then have "listL (deqL (swap q)) = tl (listR q)"
    using 5 list_deqL swap_list' invar_swap by fastforce

  then have "listR (swap (deqL (swap q))) = tl (listR q)"
    using 5 swap_list' invar_deqL invar_swap listL_is_empty swap_list
    by metis

  then show ?case     
    by(auto split: prod.splits)
next
  case 6
  then show ?case
    using list_firstL by simp
next
  case (7 q)

  from 7 have [simp]: "listR q = listL (swap q)"
    by (simp add: invar_swap swap_list')

  from 7 have [simp]: "firstR q = firstL (swap q)"
    by(auto split: prod.splits)

  from 7 have "listL (swap q) \<noteq> []"
    by auto

  with 7 have "firstL (swap q) = hd (listL (swap q))"
    using invar_swap list_firstL by blast
  
  then show ?case 
    using \<open>firstR q = firstL (swap q)\<close> by auto
next
  case 8
  then show ?case 
    using listL_is_empty by auto
next
  case 9
  then show ?case
    by (simp add: empty_def)
next
  case 10
  then show ?case 
    by(simp add: invar_enqL)
next
  case 11
  then show ?case 
    by (simp add: invar_enqL invar_swap)
next
  case 12
  then show ?case
    using invar_deqL by simp
next
  case (13 q)
  then have "invar (swap (deqL (swap q)))"
    by (metis invar_deqL invar_swap listL_is_empty rev.simps(1) swap_list)

  then show ?case
    by (auto split: prod.splits)
qed

end
