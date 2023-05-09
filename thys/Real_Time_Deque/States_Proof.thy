section "Big + Small Proofs"

theory States_Proof
imports States_Aux Big_Proof Small_Proof
begin

lemmas state_splits = idle.splits common_state.splits small_state.splits big_state.splits
lemmas invar_steps = Big_Proof.invar_step Common_Proof.invar_step Small_Proof.invar_step

lemma invar_list_big_first: 
    "invar states \<Longrightarrow> list_big_first states = list_current_big_first states"
  using app_rev
  by(cases states)(auto split: prod.splits)

lemma step_lists [simp]: "invar states \<Longrightarrow> lists (step states) = lists states"
proof(induction states rule: lists.induct)
  case (1 dir currentB big auxB count currentS small auxS)
  then show ?case 
  proof(induction 
      "(States dir (Big1 currentB big auxB count) (Small1 currentS small auxS))" 
      rule: step_states.induct)
    case 1
    then show ?case 
      by(cases currentB) auto
  next
    case ("2_1" count')
    then have "0 < size big"
      by(cases currentB) auto

    then have big_not_empty: "Stack_Aux.list big \<noteq> []"
      by (simp add: Stack_Proof.size_not_empty Stack_Proof.list_empty)

    with "2_1" show ?case 
      using 
          take_rev_step[of "Stack_Aux.list big" count' auxB] 
          Stack_Proof.list_empty[symmetric, of small]       
      apply (cases currentB)
      by(auto simp: first_hd funpow_swap1 take_rev_step simp del: take_rev_def)
    qed
next
  case ("2_1" dir common small)
  then show ?case 
    using step_list_Small2[of small]
    by(auto split: small_state.splits)
next
  case ("2_2" dir big current auxS big newS count)
  then show ?case 
    using step_list_Small2[of "Small2 current auxS big newS count"]
    by auto
next
  case ("2_3" dir big common)
  then show ?case 
    by auto
qed
  
lemma step_lists_current [simp]: 
    "invar states \<Longrightarrow> lists_current (step states) = lists_current states"
  by(induction states rule: step_states.induct)(auto split: current.splits)

lemma push_big: "lists (States dir big small) = (big', small')
   \<Longrightarrow> lists (States dir (Big.push x big) small) = (x # big', small')"
proof(induction "States dir (Big.push x big) small" rule: lists.induct)
  case 1
  then show ?case
  proof(induction x big rule: Big.push.induct)
    case 1
    then show ?case 
      by auto
  next
    case (2 x current big aux count)
    then show ?case 
      by(cases current) auto
  qed
next
  case "2_1"
  then show ?case 
    by(cases big) auto
qed auto

lemma push_small_lists: "
  invar (States dir big small)
   \<Longrightarrow> lists (States dir big (Small.push x small)) = (big', x # small') \<longleftrightarrow> 
       lists (States dir big small) = (big', small')"
  apply(induction "States dir big (Small.push x small)" rule: lists.induct)
  by (auto split: current.splits small_state.splits)

lemma list_small_big: "
    list_small_first (States dir big small) = list_current_small_first (States dir big small) \<longleftrightarrow>
    list_big_first (States dir big small) = list_current_big_first (States dir big small)"
  using app_rev 
  by(auto split: prod.splits)

lemma list_big_first_pop_big [simp]: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> x # list_big_first (States dir big' small) = list_big_first (States dir big small)"
  by(induction "States dir big small" rule: lists.induct)(auto split: prod.splits)

lemma list_current_big_first_pop_big [simp]: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> x # list_current_big_first (States dir big' small) =
    list_current_big_first (States dir big small)"
  by auto

lemma lists_big_first_pop_big: "\<lbrakk>
  invar (States dir big small);
   0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> list_big_first (States dir big' small) = list_current_big_first (States dir big' small)"
  by (metis invar_list_big_first list_big_first_pop_big list_current_big_first_pop_big list.sel(3))

lemma lists_small_first_pop_big: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> list_small_first (States dir big' small) = list_current_small_first (States dir big' small)"
  by (meson lists_big_first_pop_big list_small_big)

lemma list_small_first_pop_small [simp]: "\<lbrakk>
  invar (States dir big small);
   0 < size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> x # list_small_first (States dir big small') = list_small_first (States dir big small)"
proof(induction "States dir big small" rule: lists.induct)
  case (1 currentB big auxB count currentS small auxS) 
  then show ?case
    by(cases currentS)(auto simp: Cons_eq_appendI)
next
  case ("2_1" common)
  then show ?case  
  proof(induction small rule: Small.pop.induct)
    case (1 common)
    then show ?case 
      by(cases "Common.pop common")(auto simp: Cons_eq_appendI)
  next
    case 2
    then show ?case by auto
  next
    case 3
    then show ?case 
      by(cases "Common.pop common")(auto simp: Cons_eq_appendI)
  qed
next
  case ("2_2" current)
  then show ?case 
    by(induction current rule: Current.pop.induct)
      (auto simp: first_hd rev_take Suc_diff_le)
next
  case ("2_3" common)
  then show ?case 
    by(cases "Common.pop common")(auto simp: Cons_eq_appendI)
qed

lemma list_current_small_first_pop_small [simp]: "\<lbrakk>
  invar (States dir big small);
  0 < size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> x # list_current_small_first (States dir big small') =
     list_current_small_first (States dir big small)"
  by auto

lemma lists_small_first_pop_small: "\<lbrakk>
  invar (States dir big small);
  0 < size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> list_small_first (States dir big small') = list_current_small_first (States dir big small')"
  by (metis (no_types, opaque_lifting) invar_states.simps list.sel(3) 
      list_current_small_first_pop_small list_small_first_pop_small)

lemma invars_pop_big: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> invar big' \<and> invar small"
  by(auto simp: Big_Proof.invar_pop)

lemma invar_pop_big_aux: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> (case (big', small) of 
        (Big1 _ big _ count, Small1 (Current _ _ old remained) small _) \<Rightarrow> 
          size big - count = remained - size old \<and> count \<ge> size small
      | (_, Small1 _ _ _) \<Rightarrow> False
      | (Big1 _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
  by(auto split: big_state.splits small_state.splits prod.splits)

lemma invar_pop_big: "\<lbrakk>
  invar (States dir big small);
  0 < size big;
  Big.pop big = (x, big')\<rbrakk>
 \<Longrightarrow> invar (States dir big' small)"
  using invars_pop_big[of dir big small x big']  
        lists_small_first_pop_big[of dir big small x big']
        invar_pop_big_aux[of dir big small x big']
  by auto

lemma invars_pop_small: "\<lbrakk>
  invar (States dir big small);
  0 < size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow>  invar big  \<and> invar small'"
  by(auto simp: Small_Proof.invar_pop)

lemma invar_pop_small_aux: "\<lbrakk>
  invar (States dir big small);
  0 < size small;
  Small.pop small = (x, small')\<rbrakk>
 \<Longrightarrow> (case (big, small') of 
        (Big1 _ big _ count, Small1 (Current _ _ old remained) small _) \<Rightarrow> 
          size big - count = remained - size old \<and> count \<ge> size small
      | (_, Small1 _ _ _) \<Rightarrow> False
      | (Big1 _ _ _ _, _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
proof(induction small rule: Small.pop.induct)
  case 1
  then show ?case
    by(auto split: big_state.splits small_state.splits prod.splits)
next
  case (2 current)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case 1
    then show ?case 
      by(auto split: big_state.splits)
  next
    case 2
    then show ?case 
      by(auto split: big_state.splits)
  qed
next
  case 3
  then show ?case 
    by(auto split: big_state.splits)
qed
  
lemma invar_pop_small: "\<lbrakk>
    invar (States dir big small);
    0 < size small;
    Small.pop small = (x, small')
  \<rbrakk> \<Longrightarrow> invar (States dir big small')"
  using invars_pop_small[of dir big small x small']  
        lists_small_first_pop_small[of dir big small x small']
        invar_pop_small_aux[of dir big small x small']
  by fastforce  

lemma invar_push_big: "invar (States dir big small) \<Longrightarrow> invar (States dir (Big.push x big) small)"
proof(induction x big arbitrary: small rule: Big.push.induct)
  case 1
  then show ?case
    by(auto simp: Common_Proof.invar_push)
next
  case (2 x current big aux count)
  then show ?case 
    by(cases current)(auto split: prod.splits small_state.splits)
qed

lemma invar_push_small: "invar (States dir big small)
   \<Longrightarrow> invar (States dir big (Small.push x small))"
proof(induction x small arbitrary: big rule: Small.push.induct)
  case (1 x state)
  then show ?case 
    by(auto simp: Common_Proof.invar_push split: big_state.splits)
next
  case (2 x current small auxS)
  then show ?case
    by(induction x current rule: Current.push.induct)(auto split: big_state.splits)
next
  case (3 x current auxS big newS count)
  then show ?case 
    by(induction x current rule: Current.push.induct)(auto split: big_state.splits)
qed

lemma step_invars:"\<lbrakk>invar states; step states = States dir big small\<rbrakk> \<Longrightarrow> invar big \<and> invar small"
proof(induction states rule: step_states.induct)
  case (1 dir currentB big' auxB currentS small' auxS)
  with Big_Proof.invar_step have "invar (Big1 currentB big' auxB 0)"
    by auto
  with 1 have invar_big: "invar big"
    using Big_Proof.invar_step[of "Big1 currentB big' auxB 0"]
    by auto

  from 1 have invar_small: "invar small"
    using Stack_Proof.list_empty_size[of small']
    by(cases currentS) auto
  
  from invar_small invar_big show ?case
    by simp
next
  case ("2_1" dir current big aux count small)
  then show ?case 
    using Big_Proof.invar_step[of "Big1 current big aux (Suc count)"]  
          Small_Proof.invar_step[of small]
    by simp
next
  case "2_2"
  then show ?case 
    by(auto simp: Common_Proof.invar_step Small_Proof.invar_step)
next
  case ("2_3" dir big current auxS big' newS count)
  then show ?case 
    using Big_Proof.invar_step[of big] 
          Small_Proof.invar_step[of "Small2 current auxS big' newS count"]
    by auto
next
  case "2_4"
  then show ?case 
    by(auto simp: Common_Proof.invar_step Big_Proof.invar_step)
qed

lemma step_lists_small_first: "invar states \<Longrightarrow>
   list_small_first (step states) = list_current_small_first (step states)"
  using step_lists_current step_lists  invar_states.elims(2)
  by fastforce

lemma invar_step_aux: "invar states \<Longrightarrow>(case step states of 
        (States _ (Big1 _ big _ count) (Small1 (Current _ _ old remained) small _)) \<Rightarrow> 
          size big - count = remained - size old \<and> count \<ge> size small
      | (States _ _  (Small1 _ _ _)) \<Rightarrow> False
      | (States _ (Big1 _ _ _ _) _) \<Rightarrow> False
      | _ \<Rightarrow> True
      )"
proof(induction states rule: step_states.induct)
  case ("2_1" dir current big aux count small)
  then show ?case
  proof(cases small)
    case (Small1 current small auxS)
    with "2_1" show ?thesis 
      using Stack_Proof.size_empty[symmetric, of small]
      by(auto split: current.splits)
  qed auto 
qed (auto split: big_state.splits small_state.splits) 

lemma invar_step: "invar (states :: 'a states) \<Longrightarrow> invar (step states)" 
  using invar_step_aux[of states] step_lists_small_first[of states]
  by(cases "step states")(auto simp: step_invars)

lemma step_consistent [simp]: 
  "\<lbrakk>\<And>states. invar (states :: 'a states) \<Longrightarrow>  P (step states) = P states; invar states\<rbrakk>
   \<Longrightarrow> P states = P ((step ^^n) states)" 
  by(induction n arbitrary: states)
    (auto simp: States_Proof.invar_step funpow_swap1)

lemma step_consistent_2: 
  "\<lbrakk>\<And>states. \<lbrakk>invar (states :: 'a states); P states\<rbrakk> \<Longrightarrow>  P (step states); invar states;  P states\<rbrakk>
   \<Longrightarrow> P ((step ^^n) states)" 
  by(induction n arbitrary: states)
    (auto simp: States_Proof.invar_step funpow_swap1)

lemma size_ok'_Suc: "size_ok' states (Suc steps) \<Longrightarrow> size_ok' states steps"
  by(induction states steps rule: size_ok'.induct) auto

lemma size_ok'_decline: "size_ok' states x \<Longrightarrow> x \<ge> y \<Longrightarrow> size_ok' states y"
  by(induction states x rule: size_ok'.induct) auto

lemma remaining_steps_0 [simp]: "\<lbrakk>invar (states :: 'a states); remaining_steps states = 0\<rbrakk>
   \<Longrightarrow> remaining_steps (step states) = 0"
  by(induction states rule: step_states.induct) 
    (auto split: current.splits small_state.splits)

lemma remaining_steps_0': "\<lbrakk>invar (states :: 'a states); remaining_steps states = 0\<rbrakk>
   \<Longrightarrow> remaining_steps ((step ^^ n) states) = 0"
  by(induction n arbitrary: states)(auto simp: invar_step funpow_swap1)

lemma remaining_steps_decline_Suc: 
  "\<lbrakk>invar (states :: 'a states); 0 < remaining_steps states\<rbrakk>
     \<Longrightarrow> Suc (remaining_steps (step states)) = remaining_steps states"
proof(induction states rule: step_states.induct)
  case 1
  then show ?case 
     by(auto simp: max_def split: big_state.splits small_state.splits current.splits)
next
  case ("2_1" _ _ _ _ _ small)
  then show ?case 
    by(cases small)(auto split: current.splits)
next
  case ("2_2" dir big small)
  then show ?case 
  proof(cases small)
    case (Small2 current auxS big newS count)
    with "2_2" show ?thesis 
      using Stack_Proof.size_empty_2[of big]
      by(cases current) auto
  qed auto
next
  case ("2_3" dir big current auxS big' newS count)
  then show ?case 
  proof(induction big)
    case Big1
    then show ?case by auto
  next
    case Big2
    then show ?case 
      using Stack_Proof.size_empty_2[of big']
      by(cases current) auto
  qed
next
  case ("2_4" _ big)
  then show ?case 
    by(cases big) auto
qed

lemma remaining_steps_decline_sub [simp]: "invar (states :: 'a states)
     \<Longrightarrow> remaining_steps (step states) = remaining_steps states - 1"
  using Suc_sub[of "remaining_steps (step states)" "remaining_steps states"]
  by(cases "0 < remaining_steps states") (auto simp: remaining_steps_decline_Suc)

lemma remaining_steps_decline: "invar (states :: 'a states)
   \<Longrightarrow> remaining_steps (step states) \<le> remaining_steps states"
  using remaining_steps_decline_sub[of states] by auto

lemma remaining_steps_decline_n_steps [simp]: 
  "\<lbrakk>invar (states :: 'a states); remaining_steps states \<le> n\<rbrakk>
   \<Longrightarrow> remaining_steps ((step ^^ n) states) = 0"
  by(induction n arbitrary: states)(auto simp: funpow_swap1 invar_step)

lemma remaining_steps_n_steps_plus [simp]: 
  "\<lbrakk>n \<le> remaining_steps states; invar (states :: 'a states)\<rbrakk>
    \<Longrightarrow> remaining_steps ((step ^^ n) states) + n = remaining_steps states" 
  by(induction n arbitrary: states)(auto simp: funpow_swap1 invar_step)

lemma remaining_steps_n_steps_sub [simp]: "invar (states :: 'a states)
    \<Longrightarrow> remaining_steps ((step ^^ n) states) = remaining_steps states - n"
  by(induction n arbitrary: states)(auto simp: funpow_swap1 invar_step)

lemma step_size_new_small [simp]: 
  "\<lbrakk>invar (States dir big small); step (States dir big small) = States dir' big' small'\<rbrakk>
   \<Longrightarrow> size_new small' = size_new small"
proof(induction "States dir big small" rule: step_states.induct)
  case 1
  then show ?case 
    by auto
next
  case "2_1"
  then show ?case 
    by(auto split: small_state.splits)
next
  case "2_2"
  then show ?case 
    by(auto split: small_state.splits current.splits)
next
  case "2_3"
  then show ?case 
    by(auto split: current.splits)
next
  case "2_4"
  then show ?case 
    by auto
qed

lemma step_size_new_small_2 [simp]:
 "invar states \<Longrightarrow> size_new_small (step states) = size_new_small states"
  by(cases states; cases "step states") auto

lemma step_size_new_big [simp]:
 "\<lbrakk>invar (States dir big small); step (States dir big small) = States dir' big' small'\<rbrakk>
   \<Longrightarrow> size_new big' = size_new big"
proof(induction "States dir big small" rule: step_states.induct)
  case 1
  then show ?case 
    by(auto split: current.splits)
next
  case "2_1"
  then show ?case 
    by auto
next
  case "2_2"
  then show ?case 
    by auto
next
  case "2_3"
  then show ?case 
    by(auto split: big_state.splits)
next
  case "2_4"
  then show ?case 
    by(auto split: big_state.splits)
qed

lemma step_size_new_big_2 [simp]:
 "invar states \<Longrightarrow> size_new_big (step states) = size_new_big states"
  by(cases states; cases "step states") auto

lemma step_size_small [simp]:
 "\<lbrakk>invar (States dir big small); step (States dir big small) = States dir' big' small'\<rbrakk>
    \<Longrightarrow> size small' = size small"
proof(induction "States dir big small" rule: step_states.induct)
  case "2_3"
  then show ?case 
    by(auto split: current.splits)
qed auto

lemma step_size_small_2 [simp]:
 "invar states \<Longrightarrow> size_small (step states) = size_small states"
  by(cases states; cases "step states") auto

lemma step_size_big [simp]: 
  "\<lbrakk>invar (States dir big small); step (States dir big small) = States dir' big' small'\<rbrakk>
     \<Longrightarrow> size big' = size big"
proof(induction "States dir big small" rule: step_states.induct)
  case 1
  then show ?case 
    by(auto split: current.splits)
next
  case "2_1"
  then show ?case 
    by(auto split: small_state.splits current.splits)
next
  case "2_2"
  then show ?case 
    by(auto split: small_state.splits current.splits)
next
  case "2_3"
  then show ?case 
    by(auto split: current.splits big_state.splits)
next
  case "2_4"
  then show ?case 
    by(auto split: big_state.splits)
qed

lemma step_size_big_2 [simp]:
 "invar states \<Longrightarrow> size_big (step states) = size_big states"
  by(cases states; cases "step states") auto

lemma step_size_ok_1: "\<lbrakk>
    invar (States dir big small);
    step (States dir big small) = States dir' big' small';
    size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small'"
  using step_size_new_small step_size_new_big remaining_steps_decline
  by (smt (verit, ccfv_SIG) add.commute le_trans nat_add_left_cancel_le)

lemma step_size_ok_2: "\<lbrakk>
  invar (States dir big small); 
  step (States dir big small) = States dir' big' small';
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> size_new small' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new big'"
  using remaining_steps_decline step_size_new_small step_size_new_big
  by (smt (verit, best) add_le_mono le_refl le_trans)

lemma step_size_ok_3: "\<lbrakk>
  invar (States dir big small); 
  step (States dir big small) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size small
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size small'"
  using remaining_steps_decline step_size_small
  by (metis Suc_eq_plus1 Suc_le_mono le_trans)

lemma step_size_ok_4: "\<lbrakk>
  invar (States dir big small); 
  step (States dir big small) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size big
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size big'"
  using remaining_steps_decline step_size_big
  by (metis (no_types, lifting) add_mono_thms_linordered_semiring(3) order.trans)

lemma step_size_ok: "\<lbrakk>invar states; size_ok states\<rbrakk> \<Longrightarrow> size_ok (step states)"
  using step_size_ok_1 step_size_ok_2 step_size_ok_3 step_size_ok_4
  by (smt (verit) invar_states.elims(1) size_ok'.elims(3) size_ok'.simps)

lemma step_n_size_ok: "\<lbrakk>invar states; size_ok states\<rbrakk> \<Longrightarrow> size_ok ((step ^^ n) states)"
  using step_consistent_2[of size_ok states n] step_size_ok by blast
 
lemma step_push_size_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  step (States dir big (Small.push x small)) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size small' = Suc (size small)"
  using 
    invar_push_small[of dir big small x]
    step_size_small[of dir big "Small.push x small" dir' big' small']
    size_push[of small x]
  by simp

lemma step_push_size_new_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  step (States dir big (Small.push x small)) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size_new small' = Suc (size_new small)"
  using 
    invar_push_small[of dir big small x]
    step_size_new_small[of dir big "Small.push x small" dir' big' small']
    size_new_push[of small x]
  by simp

lemma step_push_size_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  step (States dir (Big.push x big) small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size big' = Suc (size big)"
  using 
    invar_push_big[of dir big small x]
    Big_Proof.size_push[of big]
    step_size_big[of dir "Big.push x big" small dir' big' small']
  by simp

lemma step_push_size_new_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  step (States dir (Big.push x big) small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size_new big' = Suc (size_new big)"
  using 
    invar_push_big[of dir big small x] 
    step_size_new_big[of dir "Big.push x big" small dir' big' small']
    Big_Proof.size_new_push[of big x]
  by simp

lemma step_pop_size_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  0 < size big; 
  Big.pop big = (x, bigP); 
  step (States dir bigP small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size big') = size big"
  using 
    invar_pop_big[of dir big small x bigP] 
    step_size_big[of dir bigP small dir' big' small']  
    Big_Proof.size_pop[of big x bigP]
  by simp

lemma step_pop_size_new_big [simp]: "\<lbrakk>
  invar (States dir big small);
  0 < size big; Big.pop big = (x, bigP); 
  step (States dir bigP small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size_new big') = size_new big"
  using 
    invar_pop_big[of dir big small x bigP] 
    Big_Proof.size_size_new[of big]
    step_size_new_big[of dir bigP small dir' big' small']  
    Big_Proof.size_new_pop[of big x bigP]
  by simp

lemma step_n_size_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  (step ^^ n) (States dir big small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size small' = size small"
  using step_consistent[of size_small "States dir big small" n]
  by simp

lemma step_n_size_big [simp]: 
  "\<lbrakk>invar (States dir big small); (step ^^ n) (States dir big small) = States dir' big' small'\<rbrakk>
    \<Longrightarrow> size big' = size big"
  using step_consistent[of size_big "States dir big small" n]
  by simp

lemma step_n_size_new_small [simp]: 
  "\<lbrakk>invar (States dir big small); (step ^^ n) (States dir big small) = States dir' big' small'\<rbrakk>
    \<Longrightarrow> size_new small' = size_new small"
  using step_consistent[of size_new_small "States dir big small" n]
  by simp

lemma step_n_size_new_big [simp]: 
  "\<lbrakk>invar (States dir big small); (step ^^ n) (States dir big small) = States dir' big' small'\<rbrakk>
   \<Longrightarrow> size_new big' = size_new big"
  using step_consistent[of size_new_big "States dir big small" n]
  by simp

lemma step_n_push_size_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  (step ^^ n) (States dir big (Small.push x small)) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size small' = Suc (size small)"
  using step_n_size_small invar_push_small Small_Proof.size_push
  by (metis invar_states.simps)

lemma step_n_push_size_new_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  (step ^^ n) (States dir big (Small.push x small)) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size_new small' = Suc (size_new small)"
  by (metis Small_Proof.size_new_push invar_states.simps invar_push_small step_n_size_new_small)

lemma step_n_push_size_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  (step ^^ n) (States dir (Big.push x big) small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size big' = Suc (size big)"
  by (metis Big_Proof.size_push invar_states.simps invar_push_big step_n_size_big)

lemma step_n_push_size_new_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  (step ^^ n) (States dir (Big.push x big) small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> size_new big' = Suc (size_new big)"
  by (metis Big_Proof.size_new_push invar_states.simps invar_push_big step_n_size_new_big)

lemma step_n_pop_size_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  0 < size small; 
  Small.pop small = (x, smallP);
  (step ^^ n) (States dir big smallP) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size small') = size small"
  using invar_pop_small size_pop step_n_size_small
  by (metis (no_types, opaque_lifting) invar_states.simps)

lemma step_n_pop_size_new_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  0 < size small; 
  Small.pop small = (x, smallP);
  (step ^^ n) (States dir big smallP) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size_new small') = size_new small"
  using invar_pop_small size_new_pop step_n_size_new_small size_size_new
  by (metis (no_types, lifting) invar_states.simps)

lemma step_n_pop_size_big [simp]: "\<lbrakk>
  invar (States dir big small);
  0 < size big; Big.pop big = (x, bigP);
  (step ^^ n) (States dir bigP small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size big') = size big"
  using invar_pop_big Big_Proof.size_pop step_n_size_big 
  by fastforce

lemma step_n_pop_size_new_big: "\<lbrakk>
  invar (States dir big small);
  0 < size big; Big.pop big = (x, bigP);
  (step ^^ n) (States dir bigP small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> Suc (size_new big') = size_new big"
  using invar_pop_big Big_Proof.size_new_pop step_n_size_new_big Big_Proof.size_size_new
  by (metis (no_types, lifting)  invar_states.simps)

lemma remaining_steps_push_small [simp]: "invar (States dir big small)
    \<Longrightarrow> remaining_steps (States dir big small) = 
        remaining_steps (States dir big (Small.push x small))"
  by(induction x small rule: Small.push.induct)(auto split: current.splits)   

lemma remaining_steps_pop_small: 
  "\<lbrakk>invar (States dir big small); 0 < size small; Small.pop small = (x, smallP)\<rbrakk>
    \<Longrightarrow> remaining_steps (States dir big smallP) \<le> remaining_steps (States dir big small)"
proof(induction small rule: Small.pop.induct)
  case 1
  then show ?case 
    by(auto simp: Common_Proof.remaining_steps_pop max.coboundedI2 split: prod.splits)
next
  case (2 current small auxS)
  then show ?case
    by(induction current rule: Current.pop.induct)(auto split: big_state.splits) 
next
  case (3 current auxS big newS count)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma remaining_steps_pop_big: 
  "\<lbrakk>invar (States dir big small); 0 < size big; Big.pop big = (x, bigP)\<rbrakk>
    \<Longrightarrow> remaining_steps (States dir bigP small) \<le> remaining_steps (States dir big small)"
proof(induction big rule: Big.pop.induct)
  case (1 state)
  then show ?case
  proof(induction state rule: Common.pop.induct)
    case (1 current idle)
    then show ?case 
      by(cases idle)(auto split: small_state.splits)
  next
    case (2 current aux new moved)
    then show ?case 
      by(induction current rule: Current.pop.induct)(auto split: small_state.splits)
  qed
next
  case (2 current big aux count)
  then show ?case
  proof(induction current rule: Current.pop.induct)
    case 1
    then show ?case 
      by(auto split: small_state.splits current.splits)
  next
    case 2
    then show ?case 
      by(auto split: small_state.splits current.splits)
  qed
qed

lemma remaining_steps_push_big [simp]: "invar (States dir big small)
   \<Longrightarrow> remaining_steps (States dir (Big.push x big) small) = 
       remaining_steps (States dir big small)"
  by(induction x big rule: Big.push.induct)(auto split: small_state.splits current.splits)

lemma step_4_remaining_steps_push_big [simp]: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir (Big.push x big) small) = States dir' big' small'\<rbrakk>
    \<Longrightarrow> remaining_steps (States dir' big' small') = remaining_steps (States dir big small) - 4"
  by (metis invar_push_big remaining_steps_n_steps_sub remaining_steps_push_big )

lemma step_4_remaining_steps_push_small [simp]: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
 (step^^4) (States dir big (Small.push x small)) = States dir' big' small'
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') = remaining_steps (States dir big small) - 4"
  by (metis invar_push_small remaining_steps_n_steps_sub remaining_steps_push_small)

lemma step_4_remaining_steps_pop_big: "\<lbrakk>
  invar (States dir big small); 
  0 < size big; 
  Big.pop big = (x, bigP); 
  4 \<le> remaining_steps (States dir bigP small);
  (step^^4) (States dir bigP small) = States dir' big' small'
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') \<le> remaining_steps (States dir big small) - 4"
  by (metis add_le_imp_le_diff invar_pop_big remaining_steps_pop_big remaining_steps_n_steps_plus)

lemma step_4_remaining_steps_pop_small: "\<lbrakk>
  invar (States dir big small); 
  0 < size small; 
  Small.pop small = (x, smallP); 
  4 \<le> remaining_steps (States dir big smallP);
  (step^^4) (States dir big smallP) = States dir' big' small'
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') \<le> remaining_steps (States dir big small) - 4"
  by (metis add_le_imp_le_diff invar_pop_small remaining_steps_n_steps_plus remaining_steps_pop_small)

lemma step_4_pop_small_size_ok_1: "\<lbrakk>
  invar (States dir big small);
  0 < size small; 
  Small.pop small = (x, smallP); 
  4 \<le> remaining_steps (States dir big smallP);
  (step^^4) (States dir big smallP) = States dir' big' small'; 
  remaining_steps (States dir big small) + 1 \<le> 4 * size small
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size small'"
  by (smt (verit, ccfv_SIG) add.left_commute add.right_neutral add_le_cancel_left distrib_left_numeral dual_order.trans invar_pop_small le_add_diff_inverse2 mult.right_neutral plus_1_eq_Suc remaining_steps_n_steps_sub remaining_steps_pop_small step_n_pop_size_small)
  
lemma step_4_pop_big_size_ok_1: "\<lbrakk>
  invar (States dir big small); 
  0 < size big; Big.pop big = (x, bigP); 
  4 \<le> remaining_steps (States dir bigP small);
  (step^^4) (States dir bigP small) = States dir' big' small'; 
  remaining_steps (States dir big small) + 1 \<le> 4 * size small
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size small'"
  by (smt (verit, ccfv_SIG) add_leE add_le_cancel_right invar_pop_big order_trans remaining_steps_pop_big step_n_size_small remaining_steps_n_steps_plus)

lemma step_4_pop_small_size_ok_2: "\<lbrakk>
  invar (States dir big small); 
  0 < size small; 
  Small.pop small = (x, smallP); 
  4 \<le> remaining_steps (States dir big smallP);
  (step^^4) (States dir big smallP) = States dir' big' small'; 
  remaining_steps (States dir big small) + 1 \<le> 4 * size big
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size big'"
  by (smt (z3) add.commute add_leE invar_pop_small le_add_diff_inverse2 nat_add_left_cancel_le remaining_steps_n_steps_sub step_n_size_big remaining_steps_pop_small)

lemma step_4_pop_big_size_ok_2: 
  assumes
    "invar (States dir big small)"
    "0 < size big"
    "Big.pop big = (x, bigP)"
    "remaining_steps (States dir bigP small) \<ge> 4"
    "((step ^^ 4) (States dir bigP small)) =  States dir' big' small'"
    "remaining_steps (States dir big small) + 1 \<le> 4 * size big"
  shows
    "remaining_steps (States dir' big' small') + 1 \<le> 4 * size big'"
proof -
  from assms have "remaining_steps  (States dir bigP small) + 1 \<le> 4 * size big"
    by (meson add_le_cancel_right order.trans remaining_steps_pop_big)

  with assms show ?thesis
    by (smt (z3) Suc_diff_le Suc_eq_plus1 add_mult_distrib2 diff_diff_add diff_is_0_eq invar_pop_big mult_numeral_1_right numerals(1) plus_1_eq_Suc remaining_steps_n_steps_sub step_n_pop_size_big)
qed

lemma step_4_pop_small_size_ok_3: 
  assumes
    "invar (States dir big small)"
    "0 < size small"
    "Small.pop small = (x, smallP)"
    "remaining_steps (States dir big smallP) \<ge> 4"
    "((step ^^ 4) (States dir big smallP)) = States dir' big' small'"
    "size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big" 
  shows
    "size_new small' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new big'"
  by (smt (verit, best) add_leD2 add_mono_thms_linordered_semiring(1) add_mono_thms_linordered_semiring(3) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) invar_pop_small le_add2 le_add_diff_inverse order_trans plus_1_eq_Suc remaining_steps_n_steps_sub remaining_steps_pop_small step_n_pop_size_new_small step_n_size_new_big)

lemma step_4_pop_big_size_ok_3_aux: "\<lbrakk>
  0 < size big; 
  4 \<le> remaining_steps (States dir big small);
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> size_new small + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * (size_new big - 1)"
  by linarith

lemma step_4_pop_big_size_ok_3: 
    assumes
      "invar (States dir big small)"
      "0 < size big" 
      "Big.pop big = (x, bigP) "
      "remaining_steps (States dir bigP small) \<ge> 4"
      "((step ^^ 4) (States dir bigP small)) = (States dir' big' small')"
      "size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big"
    shows
      "size_new small' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new big'"
proof-
  from assms 
  have "size_new small + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * (size_new big - 1)"
    by (meson dual_order.trans remaining_steps_pop_big step_4_pop_big_size_ok_3_aux)

  then 
  have "size_new small + remaining_steps (States dir' big' small') + 2 \<le> 3 * (size_new big - 1)"
    by (smt (verit, ccfv_SIG) add_le_mono assms(1) assms(2) assms(3) assms(4) assms(5) dual_order.trans le_antisym less_or_eq_imp_le nat_less_le step_4_remaining_steps_pop_big)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_big step_n_size_new_small step_n_pop_size_new_big)
qed

lemma step_4_pop_small_size_ok_4_aux: "\<lbrakk>
  0 < size small; 
  4 \<le> remaining_steps (States dir big small);
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * (size_new small - 1)"
  by linarith

lemma step_4_pop_small_size_ok_4:
    assumes
      "invar (States dir big small)"
      "0 < size small"
      "Small.pop small = (x, smallP)"
      "remaining_steps (States dir big smallP) \<ge> 4"
      "((step ^^ 4) (States dir big smallP)) = (States dir' big' small')"
      "size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small"
    shows
       "size_new big' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small'"
proof-
  from assms step_4_pop_small_size_ok_4_aux 
  have "size_new big + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * (size_new small - 1)"
    by (smt (verit, best) add_leE le_add_diff_inverse remaining_steps_pop_small)

  with assms 
  have "size_new big + remaining_steps (States dir' big' small') + 2 \<le> 3 * (size_new small - 1)"
    by (smt (verit, best) add_le_cancel_left add_mono_thms_linordered_semiring(3) diff_le_mono invar_pop_small order_trans remaining_steps_n_steps_sub remaining_steps_pop_small)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_small step_n_size_new_big step_n_pop_size_new_small)
qed

lemma step_4_pop_big_size_ok_4_aux: "\<lbrakk>
  0 < size big; 
  4 \<le> remaining_steps (States dir big small);
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big - 1 + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * size_new small"
  by linarith

lemma step_4_pop_big_size_ok_4: 
  assumes
    "invar (States dir big small)"
    "0 < size big "
    "Big.pop big = (x, bigP)"
    "remaining_steps (States dir bigP small) \<ge> 4"
    "((step ^^ 4) (States dir bigP small)) = (States dir' big' small')"
    "size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small"
  shows
    "size_new big' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small'"
proof -
  from assms step_4_pop_big_size_ok_4_aux
  have "(size_new big - 1) + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * size_new small"
    by linarith

  with assms 
  have "(size_new big - 1) + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small"
    by (meson add_le_mono dual_order.eq_iff order_trans step_4_remaining_steps_pop_big)

  with assms show ?thesis 
    by (metis diff_Suc_1 invar_pop_big step_n_size_new_small step_n_pop_size_new_big)
qed

lemma step_4_push_small_size_ok_1: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir big (Small.push x small)) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size small
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size small'"
  by (smt (z3) add.commute add_leD1 add_le_mono le_add1 le_add_diff_inverse2 mult_Suc_right nat_1_add_1 numeral_Bit0 step_n_push_size_small step_4_remaining_steps_push_small)

lemma step_4_push_big_size_ok_1: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir (Big.push x big) small) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size small
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size small'"
  by (smt (verit, ccfv_SIG) Nat.le_diff_conv2 add_leD2 invar_push_big le_add1 le_add_diff_inverse2 remaining_steps_n_steps_sub remaining_steps_push_big step_n_size_small)

lemma step_4_push_small_size_ok_2: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir big (Small.push x small)) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size big
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size big'"
  by (metis (full_types) Suc_diff_le Suc_eq_plus1 invar_push_small less_Suc_eq_le less_imp_diff_less step_4_remaining_steps_push_small step_n_size_big)

lemma step_4_push_big_size_ok_2: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir (Big.push x big) small) = States dir' big' small';
  remaining_steps (States dir big small) + 1 \<le> 4 * size big
\<rbrakk> \<Longrightarrow> remaining_steps (States dir' big' small') + 1 \<le> 4 * size big'"
  by (smt (verit, ccfv_SIG) add.commute add_diff_cancel_left' add_leD1 add_le_mono invar_push_big mult_Suc_right nat_le_iff_add one_le_numeral remaining_steps_n_steps_sub remaining_steps_push_big step_n_push_size_big)

lemma step_4_push_small_size_ok_3_aux: "\<lbrakk>
  4 \<le> remaining_steps (States dir big small); 
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> Suc (size_new small) + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * size_new big"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_small_size_ok_3: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir big (Small.push x small)) = States dir' big' small';
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> size_new small' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new big'"
  using step_n_size_new_big step_n_push_size_new_small step_4_remaining_steps_push_small
  by (metis invar_push_small step_4_push_small_size_ok_3_aux)

lemma step_4_push_big_size_ok_3_aux: "\<lbrakk>
  4 \<le> remaining_steps (States dir big small); 
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> size_new small + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * Suc (size_new big)"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_big_size_ok_3: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir (Big.push x big) small) = States dir' big' small';
  size_new small + remaining_steps (States dir big small) + 2 \<le> 3 * size_new big
\<rbrakk> \<Longrightarrow> size_new small' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new big'"
  by (metis invar_push_big remaining_steps_n_steps_sub remaining_steps_push_big step_4_push_big_size_ok_3_aux step_n_push_size_new_big step_n_size_new_small)

lemma step_4_push_small_size_ok_4_aux: "\<lbrakk>
  4 \<le> remaining_steps (States dir big small); 
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * Suc (size_new small)"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_small_size_ok_4: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir big (Small.push x small)) = States dir' big' small';
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small'"
  by (metis invar_push_small step_n_size_new_big step_n_push_size_new_small step_4_remaining_steps_push_small step_4_push_small_size_ok_4_aux)

lemma step_4_push_big_size_ok_4_aux: "\<lbrakk>
  4 \<le> remaining_steps (States dir big small); 
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> Suc (size_new big) + (remaining_steps (States dir big small) - 4) + 2 \<le> 3 * size_new small"
  using distrib_left dual_order.trans le_add_diff_inverse2 by force

lemma step_4_push_big_size_ok_4: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small);
  (step^^4) (States dir (Big.push x big) small) = States dir' big' small';
  size_new big + remaining_steps (States dir big small) + 2 \<le> 3 * size_new small
\<rbrakk> \<Longrightarrow> size_new big' + remaining_steps (States dir' big' small') + 2 \<le> 3 * size_new small'"
  by (metis invar_push_big remaining_steps_n_steps_sub remaining_steps_push_big step_4_push_big_size_ok_4_aux step_n_push_size_new_big step_n_size_new_small)

lemma step_4_push_small_size_ok: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small); 
  size_ok (States dir big small)
\<rbrakk> \<Longrightarrow> size_ok ((step^^4) (States dir big (Small.push x small)))"
  using step_4_push_small_size_ok_1 step_4_push_small_size_ok_2 step_4_push_small_size_ok_3 step_4_push_small_size_ok_4 
  by (smt (verit) size_ok'.elims(3) size_ok'.simps)

lemma step_4_push_big_size_ok: "\<lbrakk>
  invar (States dir big small); 
  4 \<le> remaining_steps (States dir big small); 
  size_ok (States dir big small)
\<rbrakk> \<Longrightarrow> size_ok ((step^^4) (States dir (Big.push x big) small))"
  using step_4_push_big_size_ok_1 step_4_push_big_size_ok_2 step_4_push_big_size_ok_3 step_4_push_big_size_ok_4
  by (smt (verit) size_ok'.elims(3) size_ok'.simps)

lemma step_4_pop_small_size_ok: "\<lbrakk>
  invar (States dir big small); 
  0 < size small; 
  Small.pop small = (x, smallP); 
  4 \<le> remaining_steps (States dir big smallP);
  size_ok (States dir big small)
\<rbrakk> \<Longrightarrow> size_ok ((step^^4) (States dir big smallP))"
  by (smt (verit) size_ok'.elims(3) size_ok'.simps step_4_pop_small_size_ok_1 step_4_pop_small_size_ok_2 step_4_pop_small_size_ok_3 step_4_pop_small_size_ok_4)

lemma step_4_pop_big_size_ok: "\<lbrakk>
  invar (States dir big small); 
  0 < size big; Big.pop big = (x, bigP); 
  4 \<le> remaining_steps (States dir bigP small);
  size_ok (States dir big small)
\<rbrakk> \<Longrightarrow> size_ok ((step^^4) (States dir bigP small))"
  using step_4_pop_big_size_ok_1 step_4_pop_big_size_ok_2 step_4_pop_big_size_ok_3 step_4_pop_big_size_ok_4
  by (smt (verit) size_ok'.elims(3) size_ok'.simps)

lemma size_ok_size_small: "size_ok (States dir big small) \<Longrightarrow> 0 < size small"
  by auto

lemma size_ok_size_big: "size_ok (States dir big small) \<Longrightarrow> 0 < size big"
  by auto

lemma size_ok_size_new_small: "size_ok (States dir big small) \<Longrightarrow> 0 < size_new small"
  by auto

lemma size_ok_size_new_big: "size_ok (States dir big small) \<Longrightarrow> 0 < size_new big"
  by auto

lemma step_size_ok': "\<lbrakk>invar states; size_ok' states n\<rbrakk> \<Longrightarrow> size_ok' (step states) n"
  by (smt (verit, ccfv_SIG) size_ok'.elims(2) size_ok'.elims(3) step_size_big step_size_new_big step_size_new_small step_size_small)

lemma step_same: "step (States dir big small) = States dir' big' small' \<Longrightarrow> dir = dir'"
  by(induction "States dir big small" rule: step_states.induct) auto

lemma step_n_same: "(step^^n) (States dir big small) = States dir' big' small' \<Longrightarrow> dir = dir'"
proof(induction n arbitrary: big small big' small')
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain big'' small'' where "step (States dir big small) = States dir big'' small''"
    by (metis states.exhaust step_same)

  with Suc show ?case
    by(auto simp: funpow_swap1)
qed
  
lemma step_listL: "invar states \<Longrightarrow> listL (step states) = listL states"
proof(induction states rule: listL.induct)
  case (1 big small)
  then have "list_small_first (States Left big small) = 
             Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    by auto

  then have "list_small_first (step (States Left big small)) = 
             Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    using 1 step_lists by fastforce

  then have "listL (step (States Left big small)) =
             Small_Aux.list_current small @ rev (Big_Aux.list_current big)"
    by (smt (verit, ccfv_SIG) "1" invar_states.elims(2) States_Proof.invar_step listL.simps(1) step_same)

  with 1 show ?case 
    by auto
next
  case (2 big small)
  then have a: "list_big_first (States Right big small) = 
             Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
     using invar_list_big_first[of "States Right big small"]
     by auto

   then have "list_big_first (step (States Right big small)) = 
              Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    using 2 step_lists by fastforce

  then have "listL (step (States Right big small)) =
             Big_Aux.list_current big @ rev (Small_Aux.list_current small)"
    by (metis(full_types) listL.cases listL.simps(2) step_same)

  with 2 show ?case 
    using a by force
qed

lemma step_n_listL: "invar states \<Longrightarrow> listL ((step^^n) states) = listL states"
  using step_consistent[of listL states] step_listL
  by metis

lemma listL_remaining_steps: 
  assumes
    "listL states = []"
    "0 < remaining_steps states"
    "invar states"
    "size_ok states"
  shows
    "False"
proof(cases states)
  case (States dir big small)
  with assms show ?thesis 
    using Small_Proof.list_current_size size_ok_size_small
    by(cases dir; cases "lists (States dir big small)") auto
qed
   
lemma invar_step_n: "invar (states :: 'a states) \<Longrightarrow> invar ((step^^n) states)"
  by (simp add: invar_step step_consistent_2)

lemma step_n_size_ok': "\<lbrakk>invar states; size_ok' states x\<rbrakk> \<Longrightarrow> size_ok' ((step ^^ n) states) x"
proof(induction n arbitrary: states x)
  case 0
  then show ?case by auto
next
  case Suc
  then show ?case  
    using invar_step_n step_size_ok'
    by fastforce
qed

lemma size_ok_steps: "\<lbrakk>
  invar states;
  size_ok' states (remaining_steps states - n)
\<rbrakk> \<Longrightarrow> size_ok ((step ^^ n) states)"
  by (simp add: step_n_size_ok')

lemma remaining_steps_idle: "invar states
  \<Longrightarrow> remaining_steps states = 0 \<longleftrightarrow> (
    case states of 
       States _ (Big2 (Common.Idle _ _)) (Small3 (Common.Idle _ _))  \<Rightarrow> True 
    | _ \<Rightarrow> False) "
  by(cases states)
    (auto split: big_state.split small_state.split common_state.split current.splits)

lemma remaining_steps_idle': 
  "\<lbrakk>invar (States dir big small); remaining_steps (States dir big small) = 0\<rbrakk>
    \<Longrightarrow> \<exists>big_current big_idle small_current small_idle. States dir big small = 
          States dir 
            (Big2 (common_state.Idle big_current big_idle)) 
            (Small3 (common_state.Idle small_current small_idle))"
  using remaining_steps_idle[of "States dir big small"]
  by(cases big; cases small) (auto split!: common_state.splits)

end
