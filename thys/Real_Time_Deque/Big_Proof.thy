section "Big Proofs"

theory Big_Proof
imports Big_Aux Common_Proof
begin

lemma step_list [simp]: "invar big \<Longrightarrow> list (step big) = list big"
proof(induction big rule: step_big_state.induct)
  case 1
  then show ?case 
    by auto
next
  case 2
  then show ?case
    by(auto split: current.splits)
next
  case 3
  then show ?case 
    by(auto simp: rev_take take_drop drop_Suc tl_take rev_drop split: current.splits)
qed
    
lemma step_list_current [simp]: "invar big \<Longrightarrow> list_current (step big) = list_current big"
  by(induction big rule: step_big_state.induct)(auto split: current.splits)

lemma push_list [simp]: "list (push x big) = x # list big"
proof(induction x big rule: push.induct)
  case (1 x state)
  then show ?case 
    by auto
next
  case (2 x current big aux count)
  then show ?case
    by(induction x current rule: Current.push.induct) auto
qed

lemma list_Big1: "\<lbrakk>
    0 < size (Big1 current big aux count); 
    invar (Big1 current big aux count)
\<rbrakk> \<Longrightarrow> first current # list (Big1 (drop_first current) big aux count) =
      list (Big1 current big aux count)" 
proof(induction current rule: Current.pop.induct)
  case (1 added old remained)
  then have [simp]: "remained - Suc 0 < length (take_rev count (Stack_Aux.list big) @ aux)"
    by(auto simp: le_diff_conv)

  (* TODO: *)
  then have "
   \<lbrakk>0 < size old; 0 < remained; added = 0; remained - count \<le> length aux; count \<le> size big;
     Stack_Aux.list old =
     rev (take (size old - size big) aux) @ rev (take (size old) (rev (Stack_Aux.list big)));
     take remained (rev (take (size old - size big) aux)) @
     take (remained - min (length aux) (size old - size big))
      (rev (take (size old) (rev (Stack_Aux.list big)))) =
     rev (take (remained - count) aux) @ rev (take remained (rev (take count (Stack_Aux.list big))))\<rbrakk>
    \<Longrightarrow> hd (rev (take (size old - size big) aux) @ rev (take (size old) (rev (Stack_Aux.list big)))) =
        (rev (take count (Stack_Aux.list big)) @ aux) ! (remained - Suc 0)"
    by (smt (verit) Suc_pred hd_drop_conv_nth hd_rev hd_take last_snoc length_rev length_take min.absorb2 rev_append take_rev_def size_list_length take_append take_hd_drop)

  with 1 have [simp]: "Stack.first old = (take_rev count (Stack_Aux.list big) @ aux) ! (remained - Suc 0)"
    by(auto simp: take_hd_drop first_hd)
 
  from 1 show ?case
    using take_rev_nth[of 
          "remained - Suc 0" "take_rev count (Stack_Aux.list big) @ aux" "Stack.first old" "[]"
        ]
    by auto
next
  case 2
  then show ?case by auto
qed

lemma size_list [simp]: "\<lbrakk>0 < size big; invar big; list big = []\<rbrakk> \<Longrightarrow> False"
proof(induction big rule: list.induct)
  case 1
  then show ?case
    using list_size by auto
next
  case 2
  then show ?case
    by (metis list.distinct(1) list_Big1)
qed

lemma pop_list [simp]: "\<lbrakk>0 < size big; invar big; Big.pop big = (x, big')\<rbrakk>
   \<Longrightarrow> x # list big' = list big"
proof(induction big arbitrary: x rule: list.induct)
  case 1
  then show ?case  
    by(auto split: prod.splits)
next
  case 2
  then show ?case 
    by (metis Big.pop.simps(2) list_Big1 prod.inject)
qed

lemma pop_list_tl: "\<lbrakk>0 < size big; invar big; pop big = (x, big')\<rbrakk> \<Longrightarrow> list big' = tl (list big)"
  using pop_list cons_tl[of x "list big'" "list big"] 
  by force

(* TODO: *)
lemma invar_step: "invar (big :: 'a big_state) \<Longrightarrow> invar (step big)" 
proof(induction big rule: step_big_state.induct)
  case 1
  then show ?case 
    by(auto simp: invar_step)
next
  case (2 current big aux)

  then obtain extra old remained where current:
      "current = Current extra (length extra) old remained"
    by(auto split: current.splits)

  (* TODO: *)
  with 2 have "\<lbrakk>
     current = Current extra (length extra) old remained; 
     remained \<le> length aux;
     Stack_Aux.list old =
      rev (take (size old - size big) aux) @ rev (take (size old) (rev (Stack_Aux.list big)));
     take remained (rev (take (size old - size big) aux)) @
     take (remained - min (length aux) (size old - size big))
      (rev (take (size old) (rev (Stack_Aux.list big)))) =
     rev (take remained aux)\<rbrakk>
    \<Longrightarrow> remained \<le> size old"
    by(metis length_rev length_take min.absorb_iff2 size_list_length take_append)

  with 2 current have "remained - size old = 0"
    by auto 

  with current 2 show ?case
    by(auto simp: take_rev_drop drop_rev)
next
  case (3 current big aux count)
  then have "0 < size big"
    by(auto split: current.splits)

  then have big_not_empty:  "Stack_Aux.list big \<noteq> []"
    by(auto simp: Stack_Proof.size_not_empty  Stack_Proof.list_not_empty)

  with 3 have a: "
      rev (Stack_Aux.list big) @ aux =
      rev (Stack_Aux.list (Stack.pop big)) @ Stack.first big # aux"
    by(auto simp: rev_tl_hd first_hd split: current.splits)

  from 3 have "0 < size big" 
    by(auto split: current.splits)
  
  from 3 big_not_empty have "
      take_rev (Suc count) (Stack_Aux.list big) @  aux = 
      take_rev count (Stack_Aux.list (Stack.pop big)) @ (Stack.first big # aux)"
    using take_rev_tl_hd[of "Suc count" "Stack_Aux.list big" aux]
    by(auto simp: Stack_Proof.list_not_empty split: current.splits)
 
  with 3 a show ?case
    by(auto split: current.splits)
qed

lemma invar_push: "invar big \<Longrightarrow> invar (push x big)"
  by(induction x big rule: push.induct)(auto simp: invar_push split: current.splits)

(* TODO: *)
lemma invar_pop: "\<lbrakk>
  0 < size big; 
  invar big;
  pop big = (x, big')
\<rbrakk> \<Longrightarrow> invar big'"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case
    by(auto simp: invar_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
    have linarith: "\<And>x y z. x - y \<le> z \<Longrightarrow> x - (Suc y) \<le> z" 
      by linarith

    have a: " \<lbrakk>remained \<le> count + length aux; 0 < remained; added = 0; x = Stack.first old;
         big' = Big1 (Current [] 0 (Stack.pop old) (remained - Suc 0)) big aux count;
         count \<le> size big; Stack_Aux.list old = rev aux @ Stack_Aux.list big;
         take remained (rev aux) @ take (remained - length aux) (Stack_Aux.list big) =
         drop (count + length aux - remained) (rev aux) @
         drop (count - remained) (take count (Stack_Aux.list big));
         \<not> size old \<le> length aux + size big\<rbrakk>
        \<Longrightarrow> tl (rev aux @ Stack_Aux.list big) = rev aux @ Stack_Aux.list big"
      by (metis le_refl length_append length_rev size_list_length)

    have b: "\<lbrakk>remained \<le> length (take_rev count (Stack_Aux.list big) @ aux); 0 < size old; 
          0 < remained; added = 0;
         x = Stack.first old;
         big' = Big1 (Current [] 0 (Stack.pop old) (remained - Suc 0)) big aux count;
         remained - count \<le> length aux; count \<le> size big;
         Stack_Aux.list old =
           drop (length aux - (size old - size big)) (rev aux) @
           drop (size big - size old) (Stack_Aux.list big);
         take remained (drop (length aux - (size old - size big)) (rev aux)) @
         take (remained + (length aux - (size old - size big)) - length aux)
          (drop (size big - size old) (Stack_Aux.list big)) =
         drop (length (take_rev count (Stack_Aux.list big) @ aux) - remained)
          (rev (take_rev count (Stack_Aux.list big) @ aux))\<rbrakk>
        \<Longrightarrow> tl (drop (length aux - (size old - size big)) (rev aux) @
                drop (size big - size old) (Stack_Aux.list big)) =
            drop (length aux - (size old - Suc (size big))) (rev aux) @
            drop (Suc (size big) - size old) (Stack_Aux.list big)"
      apply(cases "size old - size big \<le> length aux"; cases "size old \<le> size big")
      by(auto simp: tl_drop_2 Suc_diff_le le_diff_conv le_refl a)

    from 1 have "remained \<le> length (take_rev count (Stack_Aux.list big) @ aux)"
      by(auto)

    with 1 show ?case 
      apply(auto simp: rev_take take_tl drop_Suc Suc_diff_le tl_drop linarith simp del: take_rev_def)
      using b
      apply (metis \<open>remained \<le> length (take_rev count (Stack_Aux.list big) @ aux)\<close> le_diff_conv rev_append rev_take take_append)
      by (smt (verit, del_insts) Nat.diff_cancel tl_append_if Suc_diff_le append_self_conv2 diff_add_inverse diff_diff_cancel diff_is_0_eq diff_le_mono drop_eq_Nil2 length_rev nle_le not_less_eq_eq plus_1_eq_Suc tl_drop_2)
  next
    case (2 x xs added old remained)
    then show ?case by auto
  qed
qed

lemma push_list_current [simp]: "list_current (push x big) = x # list_current big"
  by(induction x big rule: push.induct) auto

lemma pop_list_current [simp]: "\<lbrakk>invar big; 0 < size big; Big.pop big = (x, big')\<rbrakk>
   \<Longrightarrow> x # list_current big' = list_current big"
proof(induction big arbitrary: x rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: pop_list_current split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
  proof(induction current rule: Current.pop.induct)
    case (1 added old remained)
  
    then have 
        "rev (take (size old - size big) aux) @ rev (take (size old) (rev (Stack_Aux.list big))) \<noteq> []" 
      using 
        order_less_le_trans[of 0 "size old" "size big"] 
        order_less_le_trans[of 0 count "size big"]
      by(auto simp: Stack_Proof.size_not_empty Stack_Proof.list_not_empty)
     
    with 1 show ?case
      by(auto simp: first_hd)
  next
    case (2 x xs added old remained)
    then show ?case
      by auto
  qed
qed

lemma list_current_size: "\<lbrakk>0 < size big; list_current big = []; invar big\<rbrakk> \<Longrightarrow> False"
proof(induction big rule: list_current.induct)
  case 1
  then show ?case 
    using list_current_size
    by simp
next
  case (2 current uu uv uw)
  then show ?case 
    apply(cases current)
    by(auto simp: Stack_Proof.size_not_empty Stack_Proof.list_empty)
qed

lemma step_size: "invar (big :: 'a big_state) \<Longrightarrow> size big = size (step big)"
  by(induction big rule: step_big_state.induct)(auto split: current.splits)

lemma remaining_steps_step [simp]: "\<lbrakk>invar (big :: 'a big_state); remaining_steps big > 0\<rbrakk>
   \<Longrightarrow> Suc (remaining_steps (step big)) = remaining_steps big"
  by(induction big rule: step_big_state.induct)(auto split: current.splits)

lemma remaining_steps_step_0 [simp]: "\<lbrakk>invar (big :: 'a big_state); remaining_steps big = 0\<rbrakk> 
    \<Longrightarrow> remaining_steps (step big) = 0"
  by(induction big)(auto split: current.splits)

lemma remaining_steps_push: "invar big \<Longrightarrow> remaining_steps (push x big) = remaining_steps big"
  by(induction x big rule: push.induct)(auto split: current.splits)

lemma remaining_steps_pop: "\<lbrakk>invar big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> remaining_steps big' \<le> remaining_steps big"
proof(induction big rule: pop.induct)
  case (1 state)
  then show ?case 
    by(auto simp: remaining_steps_pop split: prod.splits)
next
  case (2 current big aux count)
  then show ?case 
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_push [simp]: "invar big \<Longrightarrow> size (push x big) = Suc (size big)"
  by(induction x big rule: push.induct)(auto split: current.splits)

lemma size_new_push [simp]: "invar big \<Longrightarrow> size_new (push x big) = Suc (size_new big)"
  by(induction x big rule: Big.push.induct)(auto split: current.splits)

lemma size_pop [simp]: "\<lbrakk>invar big; 0 < size big; pop big = (x, big')\<rbrakk>
   \<Longrightarrow> Suc (size big') = size big"
proof(induction big rule: pop.induct)
  case 1
  then show ?case 
    by(auto split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_new_pop [simp]: "\<lbrakk>invar big; 0 < size_new big; pop big = (x, big')\<rbrakk>
    \<Longrightarrow> Suc (size_new big') = size_new big"
proof(induction big rule: pop.induct)
  case 1
  then show ?case 
    by(auto split: prod.splits)
next
  case (2 current big aux count)
  then show ?case
    by(induction current rule: Current.pop.induct) auto
qed

lemma size_size_new: "\<lbrakk>invar (big :: 'a big_state); 0 < size big\<rbrakk> \<Longrightarrow> 0 < size_new big"
  by(induction big)(auto simp: size_size_new)

end
