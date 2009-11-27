(*  Title:      JinjaThreads/Compiler/Execs.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Semantics for the weak bisimulation proof from intermediate language to byte code} *}

theory Execs imports Tau begin

inductive exec_meth :: "jvm_prog \<Rightarrow> instr list \<Rightarrow> ex_table \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> jvm_thread_action \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  for P :: "jvm_prog" and ins :: "instr list" and xt :: "ex_table"
  where
  exec_instr: 
  "\<lbrakk> (ta, xcp, h', [(stk', loc', arbitrary, arbitrary, pc')]) \<in> set (exec_instr (ins ! pc) P h stk loc arbitrary arbitrary pc []);
     pc < length ins;
     check_instr (ins ! pc) P h stk loc arbitrary arbitrary pc [] \<rbrakk>
  \<Longrightarrow> exec_meth P ins xt h (stk, loc, pc, None) ta h' (stk', loc', pc', xcp)"

| exec_catch:
  "\<lbrakk> match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc', d)\<rfloor>; d \<le> size stk \<rbrakk>
  \<Longrightarrow> exec_meth P ins xt h (stk, loc, pc, \<lfloor>xcp\<rfloor>) \<epsilon> h (Addr xcp # drop (size stk - d) stk, loc, pc', None)"

declare match_ex_table_app [simp del]
  match_ex_table_eq_NoneI [simp del]
  compxE2_size_convs [simp del]
  compxE2_stack_xlift_convs [simp del]
  compxEs2_stack_xlift_convs [simp del]

lemma exec_meth_length_compE2D [dest]:
  "exec_meth P (compE2 e) (compxE2 e 0 d) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<Longrightarrow> pc < length (compE2 e)"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compE2)
done

lemma exec_meth_length_compEs2D [dest]:
  "exec_meth P (compEs2 es) (compxEs2 es 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp') \<Longrightarrow> pc < length (compEs2 es)"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compEs2)
done

lemma check_instr_stk_offer:
  "check_instr ins P h stk loc C M pc []
  \<Longrightarrow> check_instr ins P h (stk @ stk'') loc C M pc []"
apply(cases ins)
apply(auto simp add: nth_append hd_append neq_Nil_conv tl_append split: list.split)
done

lemma exec_instr_stk_offer:
  assumes check: "check_instr (ins ! pc) P h stk loc C M pc frs"
  and exec: "(ta', xcp', h', (stk', loc', C, M, pc') # frs) \<in> set (exec_instr (ins ! pc) P h stk loc C M pc frs)"
  shows "(ta', xcp', h', (stk' @ stk'', loc', C, M, pc') # frs) \<in> set (exec_instr (ins ! pc) P h (stk @ stk'') loc C M pc frs)"
using assms
proof(cases "ins ! pc")
  case (Invoke M n)
  thus ?thesis using exec check
    by(force split: split_if_asm sum.splits split del: split_if simp add: split_beta nth_append min_def extRet2JVM_def[folded sum_case_def] elim!: is_ArrE)
qed(fastsimp simp add: nth_append is_Ref_def has_method_def nth_Cons split_beta hd_append tl_append neq_Nil_conv split: list.split split_if_asm nat.splits elim!: is_ArrE)+

lemma exec_meth_stk_offer:
  assumes exec: "exec_meth P ins xt h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_meth P ins (stack_xlift (length stk'') xt)  h (stk @ stk'', loc, pc, xcp) ta h' (stk' @ stk'', loc', pc', xcp')"
using exec
proof(cases)
  case (exec_catch h xcp pc pc'' d stk loc)
  from `match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc'', d)\<rfloor>`
  have "match_ex_table P (cname_of h xcp) pc (stack_xlift (length stk'') xt) = \<lfloor>(pc'', length stk'' + d)\<rfloor>"
    by(simp add: match_ex_table_stack_xlift)
  moreover have "length stk'' + d \<le> length (stk @ stk'')" using `d \<le> length stk` by simp
  ultimately have "exec_meth P ins (stack_xlift (length stk'') xt) h ((stk @ stk''), loc, pc, \<lfloor>xcp\<rfloor>) \<epsilon> h ((Addr xcp # drop (length (stk @ stk'') - (length stk'' + d)) (stk @ stk'')), loc, pc'', None)"
    by(rule exec_meth.exec_catch)
  with exec_catch show ?thesis by(simp)
next
  case (exec_instr ta' xcp' h' stk' loc' pc' pc h stk loc)
  from `check_instr (ins ! pc) P h stk loc arbitrary arbitrary pc []`
  have "check_instr (ins ! pc) P h (stk @ stk'') loc arbitrary arbitrary pc []"
    by(rule check_instr_stk_offer)
  moreover from `check_instr (ins ! pc) P h stk loc arbitrary arbitrary  pc []`
    `(ta', xcp', h', [(stk', loc', arbitrary,arbitrary , pc')]) \<in> set (exec_instr (ins ! pc) P h stk loc arbitrary arbitrary pc [])`
  have "(ta', xcp', h', [(stk' @ stk'', loc', arbitrary, arbitrary, pc')]) \<in> set (exec_instr (ins ! pc) P h (stk @ stk'') loc arbitrary arbitrary pc [])"
    by(rule exec_instr_stk_offer)
  ultimately show ?thesis using exec_instr by(auto intro: exec_meth.exec_instr)
qed

  
lemma exec_meth_append_xt [intro]:
  "exec_meth P ins xt  h s ta h' s'
  \<Longrightarrow> exec_meth P (ins @ ins') (xt @ xt')  h s ta h' s'"
apply(erule exec_meth.cases)
 apply(auto)
 apply(rule exec_instr)
   apply(clarsimp simp add: nth_append)
  apply(simp)
 apply(simp add: nth_append)
apply(rule exec_catch)
by(simp)

lemma exec_meth_append [intro]:
  "exec_meth P ins xt h s ta h' s' \<Longrightarrow> exec_meth P (ins @ ins') xt  h s ta h' s'"
by(rule exec_meth_append_xt[where xt'="[]", simplified])

lemma append_exec_meth_xt:
  assumes exec: "exec_meth P ins xt h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and jump: "jump_ok ins 0 n"
  and pcs: "pcs xt' \<subseteq> {0..<length ins'}"
  shows "exec_meth P (ins' @ ins) (xt' @ shift (length ins') xt)  h (stk, loc, (length ins' + pc), xcp) ta h' (stk', loc', (length ins' + pc'), xcp')"
using exec
proof(cases)
  case (exec_catch h xcp pc pc'' d stk loc)
  from `match_ex_table P (cname_of h xcp) pc xt = \<lfloor>(pc'', d)\<rfloor>`
  have "match_ex_table P (cname_of h xcp) (length ins' + pc) (shift (length ins') xt) = \<lfloor>(length ins' + pc'', d)\<rfloor>"
    by(simp add: match_ex_table_shift)
  moreover from pcs have "length ins' + pc \<notin> pcs xt'" by(auto)
  ultimately have "match_ex_table P (cname_of h xcp) (length ins' + pc) (xt' @ shift (length ins') xt) = \<lfloor>(length ins' + pc'', d)\<rfloor>"
    by(simp add: match_ex_table_append_not_pcs)
  with exec_catch show ?thesis by(auto dest: exec_meth.exec_catch)
next
  case (exec_instr ta' xcp' h' stk' loc' pc' pc h stk loc)
  note exec = `(ta', xcp', h', [(stk', loc', arbitrary, arbitrary, pc')]) \<in> set (exec_instr (ins ! pc) P h stk loc arbitrary arbitrary pc [])`
  hence "(ta', xcp', h', [(stk', loc', arbitrary, arbitrary, length ins' + pc')]) \<in> set (exec_instr (ins ! pc) P h stk loc arbitrary arbitrary (length ins' + pc) [])"
  proof(cases "ins ! pc")
    case (Goto i)
    with jump `pc < length ins` have "- int pc  \<le> i" "i < int (length ins - pc + n)"
      by(auto dest: jump_ok_GotoD)
    with exec Goto show ?thesis by(auto)
  next
    case (IfFalse i)
    with jump `pc < length ins` have "- int pc  \<le> i" "i < int (length ins - pc + n)"
      by(auto dest: jump_ok_IfFalseD)
    with exec IfFalse show ?thesis by(auto)
  next
    case (Invoke M n)
    with exec show ?thesis 
      by(force split: split_if_asm sum.splits split del: split_if simp add: split_beta nth_append min_def extRet2JVM_def[folded sum_case_def] elim!: is_ArrE)
  qed(auto simp add: split_beta split: split_if_asm)
  moreover from `check_instr (ins ! pc) P h stk loc arbitrary arbitrary pc []`
  have "check_instr (ins ! pc) P h stk loc arbitrary arbitrary (length ins' + pc) []"
    by(cases "ins ! pc", auto)
  ultimately have "exec_meth P (ins' @ ins) (xt' @ shift (length ins') xt)  h (stk, loc, (length ins' + pc), None) ta' h' (stk', loc', (length ins' + pc'), xcp')"
    using `pc < length ins` by -(rule exec_meth.exec_instr, simp_all)
  thus ?thesis using exec_instr by(auto)
qed

lemma append_exec_meth:
  assumes exec: "exec_meth P ins xt  h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and jump: "jump_ok ins 0 n"
  shows "exec_meth P (ins' @ ins) (shift (length ins') xt) h (stk, loc, (length ins' + pc), xcp) ta h' (stk', loc', (length ins' + pc'), xcp')"
using assms by(rule append_exec_meth_xt [where xt'="[]", simplified])

lemma exec_meth_take_xt':
  "\<lbrakk> exec_meth P (ins @ ins') (xt' @ xt) h (stk, loc, pc, xcp) ta h' s';
    pc < length ins; pc \<notin> pcs xt \<rbrakk>
  \<Longrightarrow> exec_meth P ins xt' h (stk, loc, pc, xcp) ta h' s'"
apply(erule exec_meth.cases)
apply(auto intro: exec_meth.intros simp add: match_ex_table_append nth_append dest: match_ex_table_pcsD)
done

lemma exec_meth_take_xt:
  "\<lbrakk> exec_meth P (ins @ ins') (xt' @ shift (length ins) xt) h (stk, loc, pc, xcp) ta h' s';
    pc < length ins \<rbrakk>
  \<Longrightarrow> exec_meth P ins xt' h (stk, loc, pc, xcp) ta h' s'"
by(auto intro: exec_meth_take_xt')

lemma exec_meth_take:
  "\<lbrakk> exec_meth P (ins @ ins') xt h (stk, loc, pc, xcp) ta h' s';
    pc < length ins \<rbrakk>
  \<Longrightarrow> exec_meth P ins xt   h (stk, loc, pc, xcp) ta h' s'"
by(auto intro: exec_meth_take_xt[where xt = "[]"])


lemma exec_meth_drop_xt:
  assumes exec: "exec_meth P (ins @ ins') (xt @ shift (length ins) xt') h (stk, loc, (length ins + pc), xcp) ta h' (stk', loc', pc', xcp')"
  and xt: "pcs xt \<subseteq> {..<length ins}"
  and jump: "jump_ok ins' 0 n"
  shows "exec_meth P ins' xt' h (stk, loc, pc, xcp) ta h' (stk', loc', (pc' - length ins), xcp')"
using exec
proof(cases rule: exec_meth.cases)
  case (exec_instr TA XCP' H' STK' LOC' PC' PC H STK LOC)
  hence [simp]: "H = h" "STK = stk" "LOC = loc" "PC = length ins + pc" "xcp = None" "XCP' = xcp'"
    "TA = ta" "H' = h'" "STK' = stk'" "LOC' = loc'" "PC' = pc'" by auto
  from `PC < length (ins @ ins')` have pc: "pc < length ins'" by simp
  moreover with `(TA, XCP', H', [(STK', LOC', arbitrary, arbitrary, PC')]) \<in> set (exec_instr ((ins @ ins') ! PC) P H STK LOC arbitrary arbitrary PC [])`
  have "(ta, xcp', h', [(stk', loc', arbitrary, arbitrary, PC' - length ins)]) \<in> set (exec_instr (ins' ! pc) P h stk loc arbitrary arbitrary pc [])"
    apply(cases "ins' ! pc")
    apply(simp_all add: split_beta split: split_if_asm split del: split_if)
    apply(force split: sum.splits simp add: min_def extRet2JVM_def[folded sum_case_def])+
    done
  moreover from `check_instr ((ins @ ins') ! PC) P H STK LOC arbitrary arbitrary PC []` jump pc
  have "check_instr (ins' ! pc) P h stk loc arbitrary arbitrary pc []"
    by(cases "ins' ! pc", auto dest: jump_ok_GotoD jump_ok_IfFalseD)
  ultimately show ?thesis by(auto intro: exec_meth.intros)
next
  case (exec_catch H XCP PC PC' D STK LOC)
  hence [simp]: "H = h" "STK = stk" "LOC = loc" "PC = length ins + pc" "xcp = \<lfloor>XCP\<rfloor>"
    "ta = \<epsilon>" "h' = h" "stk' = Addr XCP # drop (length stk - D) stk" "loc' = loc" "PC' = pc'" "xcp' = None" by auto
  from `match_ex_table P (cname_of H XCP) PC (xt @ shift (length ins) xt') = \<lfloor>(PC', D)\<rfloor>` xt
  have "match_ex_table P (cname_of h XCP) pc xt' = \<lfloor>(pc' - length ins, D)\<rfloor>"
    by(auto simp add: match_ex_table_append dest: match_ex_table_shift_pcD match_ex_table_pcsD)
  with `D \<le> length STK` show ?thesis by(auto intro: exec_meth.intros)
qed

lemma exec_meth_drop:
  "\<lbrakk> exec_meth P (ins @ ins') (shift (length ins) xt) h (stk, loc, (length ins + pc), xcp) ta h' (stk', loc', pc', xcp');
     jump_ok ins' 0 b \<rbrakk>
   \<Longrightarrow> exec_meth P ins' xt h (stk, loc, pc, xcp) ta h' (stk', loc', (pc' - length ins), xcp')"
by(auto intro: exec_meth_drop_xt[where xt = "[]"])

lemma exec_meth_drop_xt_pc:
  assumes exec: "exec_meth P (ins @ ins') (xt @ shift (length ins) xt') h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc \<ge> length ins"
  and pcs: "pcs xt \<subseteq> {..<length ins}"
  and jump: "jump_ok ins' 0 n'"
  shows "pc' \<ge> length ins"
using exec
proof(cases rule: exec_meth.cases)
  case exec_instr thus ?thesis using jump pc
    apply(cases "ins' ! (pc - length ins)")
    apply(safe)
    apply(simp_all add: split_beta nth_append split: split_if_asm)
    apply(force split: sum.splits simp add: min_def extRet2JVM_def[folded sum_case_def] dest: jump_ok_GotoD jump_ok_IfFalseD)+
    done
next
  case exec_catch thus ?thesis using pcs pc
    by(auto dest: match_ex_table_pcsD match_ex_table_shift_pcD simp add: match_ex_table_append)
qed

lemmas exec_meth_drop_pc = exec_meth_drop_xt_pc[where xt="[]", simplified, standard]

definition exec_move :: "J1_prog \<Rightarrow> expr1 \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
where "exec_move P e \<equiv> exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0)"

definition exec_moves :: "J1_prog \<Rightarrow> expr1 list \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
where "exec_moves P es \<equiv> exec_meth (compP2 P) (compEs2 es) (compxEs2 es 0 0)"

lemma exec_move_newArrayI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (newA T\<lfloor>e\<rceil>) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_newArray:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (newA T\<lfloor>e\<rceil>) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_CastI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (Cast T e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Cast:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (Cast T e) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_BinOpI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e \<guillemotleft>bop\<guillemotright> e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_BinOp1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e \<guillemotleft>bop\<guillemotright> e') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_BinOpI2:
  assumes exec: "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastsimp split: bop.splits intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_LAssI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (V := e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_LAss:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (V := e) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_AAccI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<lfloor>e'\<rceil>) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_AAcc1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e\<lfloor>e'\<rceil>) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_AAccI2:
  assumes exec: "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e1\<lfloor>e2\<rceil>) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastsimp intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_AAssI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<lfloor>e'\<rceil> := e'') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_AAss1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (e\<lfloor>e'\<rceil> := e'') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s' assume "?rhs ta h' s'"
  thus "?lhs ta h' s'" by(rule exec_move_AAssI1)
next
  fix ta h' s' assume "?lhs ta h' s'"
  hence "exec_meth (compP2 P) (compE2 e @ compE2 e' @ compE2 e'' @ [AStore, Push Unit])
     (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' 0 (Suc 0) @ compxE2 e'' (length (compE2 e')) (Suc (Suc 0))))
     h (stk, loc, pc, xcp) ta h' s'" by(simp add: exec_move_def shift_compxE2 add_ac)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed

lemma exec_move_AAssI2:
  assumes exec: "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e1\<lfloor>e2\<rceil> := e3) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth (compP2 P) (compE2 e2 @ compE2 e3 @ [AStore, Push Unit]) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) h (stk @ [v], loc, pc, xcp) ta h' (stk' @ [v], loc', pc', xcp')"
    by(rule exec_meth_append_xt)
  hence "exec_meth (compP2 P) (compE2 e1 @ compE2 e2 @ compE2 e3 @ [AStore, Push Unit]) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 0 (Suc 0) @ shift (length (compE2 e2)) (compxE2 e3 0 (Suc (Suc 0))))) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 add_ac)
qed

lemma exec_move_AAssI3:
  assumes exec: "exec_move P e3 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e1\<lfloor>e2\<rceil> := e3) h (stk @ [v', v], loc, length (compE2 e1) + length (compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1) + length (compE2 e2) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e3) (compxE2 e3 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v', v]", simplified stack_xlift_compxE2, simplified]
  have "exec_meth (compP2 P) (compE2 e3 @ [AStore, Push Unit]) (compxE2 e3 0 (Suc (Suc 0))) h (stk @ [v', v], loc, pc, xcp) ta h' (stk' @ [v', v], loc', pc', xcp')"
    by(rule exec_meth_append)
  hence "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ compE2 e3 @ [AStore, Push Unit]) 
                   ((compxE2 e1 0 0 @ compxE2 e2 (length (compE2 e1)) (Suc 0)) @ shift (length (compE2 e1 @ compE2 e2)) (compxE2 e3 0 (Suc (Suc 0)))) h (stk @ [v', v], loc, length (compE2 e1 @ compE2 e2) + pc, xcp) ta h' (stk' @ [v', v], loc', length (compE2 e1 @ compE2 e2) + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(auto simp add: exec_move_def shift_compxE2 add_ac)
qed

lemma exec_move_ALengthI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<bullet>length) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_ALength:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e\<bullet>length) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_FAccI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<bullet>F{D}) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_FAcc:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e\<bullet>F{D}) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_FAssI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<bullet>F{D} := e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_FAss1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e\<bullet>F{D} := e') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_FAssI2:
  assumes exec: "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e1\<bullet>F{D} := e2) h (stk @ [v], loc, length (compE2 e1) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e1) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_move_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastsimp intro: append_exec_meth_xt simp add: exec_move_def compxE2_size_convs compxE2_stack_xlift_convs)
qed

lemma exec_move_CallI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e\<bullet>M(es)) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Call1:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (e\<bullet>M(es)) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def
by(auto intro!: ext intro: exec_meth_take_xt simp add: compxE2_size_convs)

lemma exec_move_CallI2:
  assumes exec: "exec_moves P es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (e\<bullet>M(es)) h (stk @ [v], loc, length (compE2 e) + pc, xcp) ta h' (stk' @ [v], loc', length (compE2 e) + pc', xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compEs2 es) (compxEs2 es 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_moves_def .
  from exec_meth_stk_offer[OF this, where stk''="[v]"] show ?thesis
    by(fastsimp intro: append_exec_meth_xt simp add: exec_move_def compxEs2_size_convs compxEs2_stack_xlift_convs)
qed

lemma exec_move_BlockNoneI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P {V:T=None; e}\<^bsub>cr\<^esub> h s ta h' s'"
unfolding exec_move_def by simp

lemma exec_move_BlockNone:
  "exec_move P {V:T=None; e}\<^bsub>cr\<^esub> = exec_move P e"
unfolding exec_move_def by(simp)

lemma exec_move_BlockSomeI:
  assumes exec: "exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> h (stk, loc, Suc (Suc pc), xcp) ta h' (stk', loc', Suc (Suc pc'), xcp')"
proof -
  let ?ins = "[Push v, Store V]"
  from exec have "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) (?ins @ compE2 e) (shift (length ?ins) (compxE2 e 0 0)) h (stk, loc, length ?ins + pc, xcp) ta h' (stk', loc', length ?ins + pc', xcp')"
    by(rule append_exec_meth) auto
  thus ?thesis by(simp add: exec_move_def shift_compxE2)
qed

lemma exec_move_BlockSome:
  "exec_move P {V:T=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> h (stk, loc, Suc (Suc pc), xcp) ta h' (stk', loc', Suc (Suc pc'), xcp') =
   exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')" (is "?lhs = ?rhs")
proof
  assume ?rhs thus ?lhs by(rule exec_move_BlockSomeI)
next
  let ?ins = "[Push v, Store V]"
  assume ?lhs
  hence "exec_meth (compP2 P) (?ins @ compE2 e) (shift (length ?ins) (compxE2 e 0 0)) h (stk, loc, length ?ins + pc, xcp) ta h' (stk', loc', length ?ins + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2)
  hence "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', length ?ins + pc' - length ?ins, xcp')"
    by(rule exec_meth_drop) auto
  thus ?rhs by(simp add: exec_move_def)
qed

lemma exec_move_SyncI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (sync\<^bsub>V\<^esub> (e) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Sync1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (sync\<^bsub>V\<^esub> (e) e') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth (compP2 P) (compE2 e @ Store V # Load V # MEnter # compE2 e' @ [Load V, MExit, Goto 4, Load V, MExit, Throw])
                   (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' 3 0 @ [(3, 3 + length (compE2 e'), Throwable, 6 + length (compE2 e'), 0)]))
                   h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: shift_compxE2 add_ac exec_move_def)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_SyncI1)

lemma exec_move_SyncI2:
  assumes exec: "exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (sync\<^bsub>V\<^esub> (o') e) h (stk, loc, (Suc (Suc (Suc (length (compE2 o') + pc)))), xcp) ta h' (stk', loc', (Suc (Suc (Suc (length (compE2 o') + pc')))), xcp')"
proof -
  let ?e = "compE2 o' @ [Store V, Load V, MEnter]"
  let ?e' = "[Load V, MExit, Goto 4, Load V, MExit, Throw]"
  from exec have "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) ((?e @ compE2 e) @ ?e') ((compxE2 o' 0 0 @ shift (length ?e) (compxE2 e 0 0)) @ [(length ?e, length ?e + length (compE2 e), Throwable, length ?e + length (compE2 e) + 3, 0)]) h (stk, loc, (length ?e + pc), xcp) ta h' (stk', loc', (length ?e + pc'), xcp')"
    by(rule exec_meth_append_xt[OF append_exec_meth_xt]) auto
  thus ?thesis by(simp add: nat_number shift_compxE2 exec_move_def)
qed

lemma exec_move_SeqI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (e;;e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Seq1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (e;;e') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth (compP2 P) (compE2 e @ Pop # compE2 e') (compxE2 e 0 0 @ shift (length (compE2 e)) (compxE2 e' (Suc 0) 0)) h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: exec_move_def shift_compxE2)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_SeqI1)

lemma exec_move_SeqI2:
  assumes exec: "exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc' ,xcp')"
  shows "exec_move P (e';;e) h (stk, loc, (Suc (length (compE2 e') + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e') + pc')), xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) ((compE2 e' @ [Pop]) @ compE2 e) (compxE2 e' 0 0 @ shift (length (compE2 e' @ [Pop])) (compxE2 e 0 0)) h (stk, loc, (length ((compE2 e') @ [Pop]) + pc), xcp) ta h' (stk', loc', (length ((compE2 e') @ [Pop]) + pc'), xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Seq2:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (e';;e) h (stk, loc, Suc (length (compE2 e') + pc), xcp) ta
                             h' (stk', loc', Suc (length (compE2 e') + pc'), xcp') =
         exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e' @ [Pop]"
  assume ?lhs
  hence "exec_meth (compP2 P) (?E @ compE2 e) (compxE2 e' 0 0 @ shift (length ?E) (compxE2 e 0 0)) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2)
  from exec_meth_drop_xt[OF this] show ?rhs unfolding exec_move_def by fastsimp
qed(rule exec_move_SeqI2)

lemma exec_move_CondI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (if (e) e1 else e2) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Cond1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (if (e) e1 else e2) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  let ?E = "IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ Goto (1 + int (length (compE2 e2))) # compE2 e2"
  let ?xt = "compxE2 e1 (Suc 0) 0 @ compxE2 e2 (Suc (Suc (length (compE2 e1)))) 0"
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth (compP2 P) (compE2 e @ ?E) (compxE2 e 0 0 @ shift (length (compE2 e)) ?xt) h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: exec_move_def shift_compxE2 add_ac)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_CondI1)

lemma exec_move_CondI2:
  assumes exec: "exec_move P e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (if (e) e1 else e2) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compE2 e1) (compxE2 e1 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) (((compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) @ compE2 e1) @ Goto (1 + int (length (compE2 e2))) # compE2 e2) ((compxE2 e 0 0 @ shift (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))])) (compxE2 e1 0 0)) @ (compxE2 e2 (Suc (Suc (length (compE2 e) + length (compE2 e1)))) 0)) h (stk, loc, (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) + pc), xcp) ta h' (stk', loc', (length (compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]) + pc'), xcp')"
    by -(rule exec_meth_append_xt, rule append_exec_meth_xt, auto)
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Cond2:
  assumes pc: "pc < length (compE2 e1)"
  shows "exec_move P (if (e) e1 else e2) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp') = exec_move P e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E1 = "compE2 e @ [IfFalse (2 + int (length (compE2 e1)))]"
  let ?E2 = "Goto (1 + int (length (compE2 e2))) # compE2 e2"
  assume ?lhs
  hence "exec_meth (compP2 P) (?E1 @ compE2 e1 @ ?E2) (compxE2 e 0 0 @ shift (length ?E1) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (compxE2 e2 (Suc 0) 0))) h (stk, loc, length ?E1 + pc, xcp) ta h' (stk', loc', length ?E1 + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 add_ac)
  thus ?rhs unfolding exec_move_def
    by -(rule exec_meth_take_xt,drule exec_meth_drop_xt,auto simp add: pc)
qed(rule exec_move_CondI2)

lemma exec_move_CondI3:
  assumes exec: "exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (if (e) e1 else e2) h (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), xcp) ta h' (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + pc')), xcp')"
proof -
  let ?E = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  let ?xt = "compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0"
  from exec have "exec_meth (compP2 P) (compE2 e2) (compxE2 e2 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) (?E @ compE2 e2) (?xt @ shift (length ?E) (compxE2 e2 0 0)) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: shift_compxE2 exec_move_def)
qed

lemma exec_move_Cond3:
  "exec_move P (if (e) e1 else e2) h (stk, loc, Suc (Suc (length (compE2 e) + length (compE2 e1) + pc)), xcp) ta
                                   h' (stk', loc', Suc (Suc (length (compE2 e) + length (compE2 e1) + pc')), xcp') =
   exec_move P e2 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ IfFalse (2 + int (length (compE2 e1))) # compE2 e1 @ [Goto (1 + int (length (compE2 e2)))]"
  let ?xt = "compxE2 e 0 0 @ compxE2 e1 (Suc (length (compE2 e))) 0"
  assume ?lhs
  hence "exec_meth (compP2 P) (?E @ compE2 e2) (?xt @ shift (length ?E) (compxE2 e2 0 0)) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: shift_compxE2 exec_move_def)
  thus ?rhs unfolding exec_move_def by -(drule exec_meth_drop_xt, auto)
qed(rule exec_move_CondI3)

lemma exec_move_WhileI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (while (e) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_While1:
  assumes pc: "pc < length (compE2 e)"
  shows "exec_move P (while (e) e') h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
  (is "?lhs = ?rhs")
proof(rule ext iffI)+
  let ?E = "IfFalse (3 + int (length (compE2 e'))) # compE2 e' @ [Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e')))), Push Unit]"
  let ?xt = "compxE2 e' (Suc 0) 0"
  fix ta h' s'
  assume "?lhs ta h' s'"
  hence "exec_meth (compP2 P) (compE2 e @ ?E) (compxE2 e 0 0 @ shift (length (compE2 e)) ?xt) h (stk, loc, pc, xcp) ta h' s'"
    by(simp add: exec_move_def shift_compxE2 add_ac)
  thus "?rhs ta h' s'" unfolding exec_move_def using pc by(rule exec_meth_take_xt)
qed(rule exec_move_WhileI1)

lemma exec_move_WhileI2:
  assumes exec: "exec_move P e1 h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (while (e) e1) h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
proof -
  let ?E = "compE2 e @ [IfFalse (3 + int (length (compE2 e1)))]"
  let ?E' = "[Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e1)))), Push Unit]"
  from exec have "exec_meth (compP2 P) (compE2 e1) (compxE2 e1 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) ((?E @ compE2 e1) @ ?E') (compxE2 e 0 0 @ shift (length ?E) (compxE2 e1 0 0)) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by -(rule exec_meth_append, rule append_exec_meth_xt, auto)
  thus ?thesis by(simp add: shift_compxE2 exec_move_def add_ac)
qed

lemma exec_move_While2:
  assumes pc: "pc < length (compE2 e')"
  shows "exec_move P (while (e) e') h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) ta
                                    h' (stk', loc', (Suc (length (compE2 e) + pc')), xcp') =
         exec_move P e' h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ [IfFalse (3 + int (length (compE2 e')))]"
  let ?E' = "[Pop, Goto (- int (length (compE2 e)) + (-2 - int (length (compE2 e')))), Push Unit]"
  assume ?lhs
  hence "exec_meth (compP2 P) ((?E @ compE2 e') @ ?E') (compxE2 e 0 0 @ shift (length ?E) (compxE2 e' 0 0)) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 add_ac)
  thus ?rhs unfolding exec_move_def using pc
    by -(drule exec_meth_take, simp, drule exec_meth_drop_xt, auto)
qed(rule exec_move_WhileI2)

lemma exec_move_ThrowI:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (throw e) h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_Throw:
  "pc < length (compE2 e) \<Longrightarrow> exec_move P (throw e) h (stk, loc, pc, xcp) = exec_move P e h (stk, loc, pc, xcp)"
unfolding exec_move_def by(auto intro!: ext intro: exec_meth_take)

lemma exec_move_TryI1:
  "exec_move P e h s ta h' s' \<Longrightarrow> exec_move P (try e catch(C V) e') h s ta h' s'"
unfolding exec_move_def by auto

lemma exec_move_TryI2:
  assumes exec: "exec_move P e h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_move P (try e' catch(C V) e) h (stk, loc, Suc (Suc (length (compE2 e') + pc)), xcp) ta h' (stk', loc', Suc (Suc (length (compE2 e') + pc')), xcp')"
proof -
  let ?e = "compE2 e' @ [Goto (int(size (compE2 e))+2), Store V]"
  from exec have "exec_meth (compP2 P) (compE2 e) (compxE2 e 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: exec_move_def)
  hence "exec_meth (compP2 P) ((?e @ compE2 e) @ []) ((compxE2 e' 0 0 @ shift (length ?e) (compxE2 e 0 0)) @ [(0, length (compE2 e'), C, Suc (length (compE2 e')), 0)]) h (stk, loc, (length ?e + pc), xcp) ta h' (stk', loc', (length ?e + pc'), xcp')"
    by(rule exec_meth_append_xt[OF append_exec_meth_xt]) auto
  thus ?thesis by(simp add: nat_number shift_compxE2 exec_move_def)
qed

lemma exec_move_Try2:
  "exec_move P (try e catch(C V) e') h (stk, loc, Suc (Suc (length (compE2 e) + pc)), xcp) ta
                                     h' (stk', loc', Suc (Suc (length (compE2 e) + pc')), xcp') =
   exec_move P e' h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  (is "?lhs = ?rhs")
proof
  let ?E = "compE2 e @ [Goto (int(size (compE2 e'))+2), Store V]"
  let ?xt = "[(0, length (compE2 e), C, Suc (length (compE2 e)), 0)]"
  assume lhs: ?lhs
  hence pc: "pc < length (compE2 e')"
    by(fastsimp elim!: exec_meth.cases simp add: exec_move_def match_ex_table_append match_ex_entry dest: match_ex_table_pcsD)
  from lhs have "exec_meth (compP2 P) ((?E @ compE2 e') @ []) ((compxE2 e 0 0 @ shift (length ?E) (compxE2 e' 0 0)) @ ?xt) h (stk, loc, length ?E + pc, xcp) ta h' (stk', loc', length ?E + pc', xcp')"
    by(simp add: exec_move_def shift_compxE2 add_ac)
  thus ?rhs unfolding exec_move_def using pc
    by-(drule exec_meth_drop_xt[OF exec_meth_take_xt'], auto)
qed(rule exec_move_TryI2)


inductive \<tau>Exec_move :: "J1_prog \<Rightarrow> expr1 \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  for P :: "J1_prog" and e :: "expr1" and h :: heap
  where
  \<tau>Exec_refl: "\<tau>Exec_move P e h s s"

| \<tau>Exec_step:
  "\<lbrakk> \<tau>Exec_move P e h s (stk', loc', pc', xcp');
     exec_move P e h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>move2 e pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_move P e h s s'"

lemmas \<tau>Exec1step = \<tau>Exec_step[OF \<tau>Exec_refl]
lemmas \<tau>Exec2step = \<tau>Exec_step[OF \<tau>Exec_step, OF \<tau>Exec_refl]
lemmas \<tau>Exec3step = \<tau>Exec_step[OF \<tau>Exec_step, OF \<tau>Exec_step, OF \<tau>Exec_refl]

lemma \<tau>Exec_move_rtrancl:
  "\<tau>Exec_move P e h = (\<lambda>(stk, loc, pc, xcp) s'. exec_move P e h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>move2 e pc xcp)^**"
  (is "?lhs = ?rhs")
proof((rule ext)+, rule iffI)
  fix s s' assume "?lhs s s'" thus "?rhs s s'"
    by(induct rule: \<tau>Exec_move.induct)(auto elim: rtranclp.rtrancl_into_rtrancl)
next
  fix s s' assume "?rhs s s'" thus "?lhs s s'"
    by(induct rule: rtranclp.induct)(auto intro: \<tau>Exec_move.intros)
qed

lemmas \<tau>Exec_move_induct = rtranclp_induct[where r="\<lambda>(stk, loc, pc, xcp) s'. exec_move P e h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>move2 e pc xcp", folded \<tau>Exec_move_rtrancl, simplified split_paired_all split_beta fst_conv snd_conv, standard, consumes 1, case_names refl step]

lemma \<tau>Exec_move_trans [trans]: 
  "\<lbrakk> \<tau>Exec_move P e h s s'; \<tau>Exec_move P e h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_move P e h s s''"
unfolding \<tau>Exec_move_rtrancl
by(rule rtranclp_trans)

lemmas \<tau>Exec_move_induct_split = \<tau>Exec_move.induct[split_format (complete), consumes 1, case_names \<tau>Exec_refl \<tau>Exec_step]

lemma \<tau>Exec_move_induct_None [consumes 1, case_names refl normal xcp]:
  assumes major: "\<tau>Exec_move P e h (stk, loc, pc, None) (stk', loc', pc', xcp')"
  and refl: "\<And>stk loc pc. Q stk loc pc stk loc pc"
  and one: "\<And>stk loc pc stk' loc' pc' stk'' loc'' pc''.
            \<lbrakk> \<tau>Exec_move P e h (stk, loc, pc, None) (stk', loc', pc', None);
              exec_move P e h (stk', loc', pc', None) \<epsilon> h (stk'', loc'', pc'', None);
              \<tau>move2 e pc' None;
              Q stk loc pc stk' loc' pc' \<rbrakk>
            \<Longrightarrow> Q stk loc pc stk'' loc'' pc''"
  and xcp: "\<And>stk loc pc stk' loc' pc' a stk'' loc'' pc''.
            \<lbrakk> \<tau>Exec_move P e h (stk, loc, pc, None) (stk', loc', pc', None);
              exec_move P e h (stk', loc', pc', None) \<epsilon> h (stk', loc', pc', \<lfloor>a\<rfloor>);
              exec_move P e h (stk', loc', pc', \<lfloor>a\<rfloor>) \<epsilon> h (stk'', loc'', pc'', None);
              \<tau>move2 e pc' None; \<tau>move2 e pc' \<lfloor>a\<rfloor>;
              Q stk loc pc stk' loc' pc' \<rbrakk>
            \<Longrightarrow> Q stk loc pc stk'' loc'' pc''"
  shows "Q stk loc pc stk' loc' pc'"
using major
proof(induct stk loc pc xcp\<equiv>"None::addr option" stk' loc' pc' xcp' rule: \<tau>Exec_move_induct_split)
  case \<tau>Exec_refl show ?case by (rule refl)
next
  case (\<tau>Exec_step stk loc pc xcp stk' loc' pc' xcp' stk'' loc'' pc'' xcp'')
  from `xcp = None` `xcp = None \<Longrightarrow> Q stk loc pc stk' loc' pc'`
  have Q: "Q stk loc pc stk' loc' pc'" by blast
  show ?case
  proof(cases xcp'')
    case None
    show ?thesis
    proof(cases xcp')
      case None
      from `\<tau>Exec_move P e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')` `\<tau>move2 e pc' xcp'` Q
	`exec_move P e h (stk', loc', pc', xcp') \<epsilon> h (stk'', loc'', pc'', xcp'')`
      show ?thesis unfolding `xcp = None` None `xcp'' = None`
	by-(rule one)
    next
      case (Some a)
      with `\<tau>Exec_move P e h (stk, loc, pc, xcp) (stk', loc', pc', xcp')` `xcp = None`
      obtain STK LOC PC XCP
	where exec: "\<tau>Exec_move P e h (stk, loc, pc, None) (STK, LOC, PC, XCP)"
	and exec': "exec_move P e h (STK, LOC, PC, XCP) \<epsilon> h (stk', loc', pc', \<lfloor>a\<rfloor>)"
	and \<tau>: "\<tau>move2 e PC XCP"
	by(auto elim: \<tau>Exec_move.cases)
      from exec' have [simp]: "STK = stk'" "LOC = loc'" "PC = pc'" "XCP = None"
	by(auto elim: exec_meth.cases simp add: exec_move_def dest: exec_instr_xcp_unchanged)
      with Q `\<tau>move2 e pc' xcp'` exec \<tau> exec'
      show ?thesis using `exec_move P e h (stk', loc', pc', xcp') \<epsilon> h (stk'', loc'', pc'', xcp'')`
	`xcp = None` `xcp'' = None` Some by simp(rule xcp)
    qed
  next
    case (Some a)
    with `exec_move P e h (stk', loc', pc', xcp') \<epsilon> h (stk'', loc'', pc'', xcp'')`
    have "stk'' = stk'" "loc'' = loc'" "pc'' = pc'"
      by(auto simp add: exec_move_def elim: exec_meth.cases dest: exec_instr_xcp_unchanged)
    with Q show ?thesis by simp
  qed
qed


lemmas \<tau>Exec_move_converse_cases = converse_rtranclpE[where r="\<lambda>(stk, loc, pc, xcp) s'. exec_move P e h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>move2 e pc xcp", where x="(stk, loc, pc, xcp)", folded \<tau>Exec_move_rtrancl, simplified split_beta fst_conv snd_conv, standard, consumes 1, case_names refl step]


inductive \<tau>Exec_moves :: "J1_prog \<Rightarrow> expr1 list \<Rightarrow> heap \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> (val list \<times> val list \<times> pc \<times> addr option) \<Rightarrow> bool"
  for P :: "J1_prog" and es :: "expr1 list" and h :: heap
  where
  \<tau>Execs_refl: "\<tau>Exec_moves P es h s s"

| \<tau>Execs_step:
  "\<lbrakk> \<tau>Exec_moves P es h s (stk', loc', pc', xcp'); 
     exec_moves P es h (stk', loc', pc', xcp') \<epsilon> h s';
     \<tau>moves2 es pc' xcp' \<rbrakk>
  \<Longrightarrow> \<tau>Exec_moves P es h s s'"

lemmas \<tau>Execs1step = \<tau>Execs_step[OF \<tau>Execs_refl]
lemmas \<tau>Execs2step = \<tau>Execs_step[OF \<tau>Execs_step, OF \<tau>Execs_refl]
lemmas \<tau>Execs3step = \<tau>Execs_step[OF \<tau>Execs_step, OF \<tau>Execs_step, OF \<tau>Execs_refl]

lemma \<tau>Exec_moves_rtrancl:
  "\<tau>Exec_moves P es h = (\<lambda>(stk, loc, pc, xcp) s'. exec_moves P es h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>moves2 es pc xcp)^**"
  (is "?lhs = ?rhs")
proof((rule ext)+, rule iffI)
  fix s s' assume "?lhs s s'" thus "?rhs s s'"
    by(induct rule: \<tau>Exec_moves.induct)(auto elim: rtranclp.rtrancl_into_rtrancl)
next
  fix s s' assume "?rhs s s'" thus "?lhs s s'"
    by(induct rule: rtranclp.induct)(auto intro: \<tau>Exec_moves.intros)
qed


lemmas \<tau>Exec_moves_induct = rtranclp_induct[where r="\<lambda>(stk, loc, pc, xcp) s'. exec_moves P es h (stk, loc, pc, xcp) \<epsilon> h s' \<and> \<tau>moves2 es pc xcp", folded \<tau>Exec_moves_rtrancl, simplified split_paired_all split_beta fst_conv snd_conv, standard, consumes 1, case_names refl step]


lemma \<tau>Exec_moves_trans [trans]: 
  "\<lbrakk> \<tau>Exec_moves P es h s s'; \<tau>Exec_moves P es h s' s'' \<rbrakk> \<Longrightarrow> \<tau>Exec_moves P es h s s''"
unfolding \<tau>Exec_moves_rtrancl
by(rule rtranclp_trans)

lemmas \<tau>Exec_moves_induct_split = \<tau>Exec_moves.induct[split_format (complete), standard, consumes 1, case_names \<tau>Execs_refl \<tau>Execs_step]


lemma \<tau>Exec_move_\<tau>Exec_moves:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_moves P (e # es) h s s'"
apply(induct rule: \<tau>Exec_move_induct)
 apply(rule \<tau>Execs_refl)
apply(erule \<tau>Execs_step)
apply(auto intro: \<tau>moves2Hd simp add: exec_move_def exec_moves_def)
done

lemma exec_moves_append: "exec_moves P es h s ta h' s' \<Longrightarrow> exec_moves P (es @ es') h s ta h' s'"
by(auto simp add: exec_moves_def)

lemma \<tau>Exec_moves_append [intro]:
  "\<tau>Exec_moves P es h s s' \<Longrightarrow> \<tau>Exec_moves P (es @ es') h s s'"
apply(induct rule: \<tau>Exec_moves.induct)
 apply(rule \<tau>Execs_refl)
apply(erule \<tau>Execs_step, auto intro: exec_moves_append)
done

lemma append_exec_moves:
  assumes len: "length vs = length es'"
  and exec: "exec_moves P es h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  shows "exec_moves P (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ta h' ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
proof -
  from exec have "exec_meth (compP2 P) (compEs2 es) (compxEs2 es 0 0) h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
    unfolding exec_moves_def .
  hence "exec_meth (compP2 P) (compEs2 es) (stack_xlift (length vs) (compxEs2 es 0 0))  h ((stk @ vs), loc, pc, xcp) ta h' ((stk' @ vs), loc', pc', xcp')" by(rule exec_meth_stk_offer)
  hence "exec_meth (compP2 P) (compEs2 es' @ compEs2 es) (compxEs2 es' 0 0 @ shift (length (compEs2 es')) (stack_xlift (length (vs)) (compxEs2 es 0 0))) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp) ta h' ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
    by(rule append_exec_meth_xt) auto
  thus ?thesis by(simp add: exec_moves_def stack_xlift_compxEs2 shift_compxEs2 len)
qed

lemma append_\<tau>Exec_moves:
  assumes len: "length vs = length es'"
  shows "\<tau>Exec_moves P es h  (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_moves P (es' @ es) h ((stk @ vs), loc, (length (compEs2 es') + pc), xcp)  ((stk' @ vs), loc', (length (compEs2 es') + pc'), xcp')"
proof(induct rule: \<tau>Exec_moves_induct_split)
  case \<tau>Execs_refl thus ?case by(rule \<tau>Exec_moves.\<tau>Execs_refl)
next
  case \<tau>Execs_step thus ?case
    by(auto elim!: \<tau>Exec_moves.\<tau>Execs_step append_exec_moves[OF len] intro: append_\<tau>moves2)
qed

lemma NewArray_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (newA T\<lfloor>e\<rceil>) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_newArrayI elim!: \<tau>Exec_step)

lemma Cast_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (Cast T e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CastI elim!: \<tau>Exec_step)

lemma BinOp_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P e1 h s s' \<Longrightarrow> \<tau>Exec_move P (e1 \<guillemotleft>bop\<guillemotright> e2) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_BinOpI1 elim!: \<tau>Exec_step)

lemma BinOp_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P e2 h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (e \<guillemotleft>bop\<guillemotright> e2)  h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_BinOpI2 elim!: \<tau>Exec_step)

lemma LAss_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P E h s s' \<Longrightarrow> \<tau>Exec_move P (V:=E) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_LAssI elim!: \<tau>Exec_step)

lemma AAcc_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P a h s s' \<Longrightarrow> \<tau>Exec_move P (a\<lfloor>i\<rceil>) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_AAccI1 elim!: \<tau>Exec_step)

lemma AAcc_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P i h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (a\<lfloor>i\<rceil>) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_AAccI2 elim!: \<tau>Exec_step)

lemma AAss_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P a h s s' \<Longrightarrow> \<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_AAssI1 elim!: \<tau>Exec_step)

lemma AAss_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P i h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ((stk @ [v]), loc, (length (compE2 a) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 a) + pc'), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_AAssI2 elim!: \<tau>Exec_step)

lemma AAss_\<tau>Exec_meth_xt3:
  "\<tau>Exec_move P e h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (a\<lfloor>i\<rceil> := e) h ((stk @ [v, v']), loc, (length (compE2 a) + length (compE2 i) + pc), xcp) ((stk' @ [v, v']), loc', (length (compE2 a) + length (compE2 i) + pc'), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_AAssI3 elim!: \<tau>Exec_step)

lemma ALength_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P a h s s' \<Longrightarrow> \<tau>Exec_move P (a\<bullet>length) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_ALengthI elim!: \<tau>Exec_step)

lemma FAcc_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (e\<bullet>F{D}) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_FAccI elim!: \<tau>Exec_step)

lemma FAss_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (e\<bullet>F{D} := e') h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_FAssI1 elim!: \<tau>Exec_step)

lemma FAss_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P e' h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (e\<bullet>F{D} := e') h ((stk @ [v]), loc, (length (compE2 e) + pc), xcp) ((stk' @ [v]), loc', (length (compE2 e) + pc'), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_FAssI2 elim!: \<tau>Exec_step)

lemma Call_\<tau>Exec_meth_xtObj [elim!]:
  "\<tau>Exec_move P obj h s s' \<Longrightarrow> \<tau>Exec_move P (obj\<bullet>M'(es)) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CallI1 elim!: \<tau>Exec_step)

lemma Call_\<tau>Exec_meth_xtParams [elim!]:
  "\<tau>Exec_moves P es   h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (obj\<bullet>M'(es))   h ((stk @ [v]), loc, (length (compE2 obj) + pc), xcp)  ((stk' @ [v]), loc', (length (compE2 obj) + pc'), xcp')"
by(induct rule: \<tau>Exec_moves_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CallI2 elim!: \<tau>Exec_step)

lemma Block_\<tau>Exec_meth_xtSome [elim!]:
  "\<tau>Exec_move P E   h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P {V:T=\<lfloor>v\<rfloor>; E}\<^bsub>cr\<^esub> h (stk, loc, (Suc (Suc pc)), xcp)  (stk', loc', (Suc (Suc pc')), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_BlockSomeI elim!: \<tau>Exec_step)

lemma Block_\<tau>Exec_meth_xtNone [elim!]:
  "\<tau>Exec_move P E h s s' \<Longrightarrow> \<tau>Exec_move P {V:T=None; E}\<^bsub>cr\<^esub> h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_BlockNoneI elim!: \<tau>Exec_step)

lemma Sync_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P o' h s s' \<Longrightarrow> \<tau>Exec_move P (sync\<^bsub>V\<^esub> (o') e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_SyncI1 elim!: \<tau>Exec_step)

lemma Insync_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P e  h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (sync\<^bsub>V\<^esub> (o') e)  h (stk, loc, (Suc (Suc (Suc (length (compE2 o') + pc)))), xcp) (stk', loc', (Suc (Suc (Suc (length (compE2 o') + pc')))), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_SyncI2 elim!: \<tau>Exec_step)

lemma Seq_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (e;;e') h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_SeqI1 elim!: \<tau>Exec_step)

lemma Seq_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P e h (stk, loc, pc, xcp)  (stk', loc', pc' ,xcp') \<Longrightarrow>
   \<tau>Exec_move P (e';;e) h (stk, loc, (Suc (length (compE2 e') + pc)), xcp) (stk', loc', (Suc (length (compE2 e') + pc')), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_SeqI2 elim!: \<tau>Exec_step)

lemma Cond_\<tau>Exec_meth_xt_Cond [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (if (e) e1 else e2) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CondI1 elim!: \<tau>Exec_step)

lemma Cond_\<tau>Exec_meth_xt_then:
  "\<tau>Exec_move P e1  h (stk, loc, pc, xcp)  (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_move P (if (e) e1 else e2)  h (stk, loc, (Suc (length (compE2 e) + pc)), xcp) (stk', loc', (Suc (length (compE2 e) + pc')), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CondI2 elim!: \<tau>Exec_step)

lemma Cond_\<tau>Exec_meth_xt_else:
  "\<tau>Exec_move P e2  h (stk, loc ,pc, xcp)  (stk', loc', pc', xcp') \<Longrightarrow>
   \<tau>Exec_move P (if (e) e1 else e2)  h (stk, loc, (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 e) + length (compE2 e1) + pc'))), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_CondI3 elim!: \<tau>Exec_step)

lemma While_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P c h s s' \<Longrightarrow> \<tau>Exec_move P (while (c) e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_WhileI1 elim!: \<tau>Exec_step)

lemma While_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P E h (stk, loc, pc, xcp) (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (while (c) E)  h (stk, loc ,(Suc (length (compE2 c) + pc)), xcp) (stk', loc', (Suc (length (compE2 c) + pc')), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_WhileI2 elim!: \<tau>Exec_step)

lemma Throw_\<tau>Exec_meth_xt [elim!]:
  "\<tau>Exec_move P e h s s' \<Longrightarrow> \<tau>Exec_move P (throw e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_ThrowI elim!: \<tau>Exec_step)

lemma Try_\<tau>Exec_meth_xt1 [elim!]:
  "\<tau>Exec_move P E h s s' \<Longrightarrow> \<tau>Exec_move P (try E catch(C' V) e) h s s'"
by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_TryI1 elim!: \<tau>Exec_step)

lemma Try_\<tau>Exec_meth_xt2:
  "\<tau>Exec_move P e  h (stk, loc, pc, xcp)  (stk', loc', pc', xcp')
  \<Longrightarrow> \<tau>Exec_move P (try E catch(C' V) e)  h (stk, loc, (Suc (Suc (length (compE2 E) + pc))), xcp)  (stk', loc', (Suc (Suc (length (compE2 E) + pc'))), xcp')"
by(induct rule: \<tau>Exec_move_induct_split)(auto intro: \<tau>Exec_refl \<tau>move2_\<tau>moves2.intros exec_move_TryI2 elim!: \<tau>Exec_step)

lemma \<tau>Exec_moves_map_Val:
  "P,E \<turnstile>1 map Val vs [::] Ts
  \<Longrightarrow> \<tau>Exec_moves P (map Val vs) h ([], xs, 0, None) ((rev vs), xs, (length (compEs2 (map Val vs))), None)"
proof(induct vs arbitrary: pc stk Ts rule: rev_induct)
  case Nil thus ?case by(auto intro: \<tau>Execs_refl)
next
  case (snoc v vs')
  let ?E = "compEs2 (map Val vs')"
  from snoc have "\<tau>Exec_moves P (map Val (vs' @ [v]))  h ([], xs, 0, None)  ((rev vs'), xs, (length ?E), None)"
    by(auto elim: WTs1_snoc_cases)
  also {
    from `P,E \<turnstile>1 map Val (vs' @ [v]) [::] Ts`
    have "exec_meth (compP2 P) (?E @ [Push v]) (compxEs2 (map Val vs') 0 0 @ shift (length ?E) [])   h ((rev vs'), xs, (length ?E + 0), None) \<epsilon> h ((v # rev vs'), xs, (length ?E + Suc 0), None)"
      by -(rule append_exec_meth_xt[OF exec_instr],auto elim: WTs1_snoc_cases)
    moreover have "\<tau>moves2 (map Val vs' @ [Val v]) (length (compEs2 (map Val vs')) + 0) None"
      by(rule append_\<tau>moves2 \<tau>moves2Hd \<tau>move2Val)+
    ultimately have "\<tau>Exec_moves P (map Val (vs' @ [v]))   h ((rev vs'), xs, (length ?E), None)  ((rev (vs' @ [v])), xs, (length (compEs2 (map Val (vs' @ [v])))), None)"
      by -(rule \<tau>Execs1step, auto simp add: exec_moves_def) }
  finally show ?case .
qed

lemma \<tau>Exec_move_blocks1 [simp]:
  "\<tau>Exec_move P (blocks1 n Ts body) h s s' = \<tau>Exec_move P body h s s'"
  (is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs thus ?rhs
    by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>Exec_step simp add: exec_move_def)
next
  assume ?rhs thus ?lhs
    by(induct rule: \<tau>Exec_move.induct)(auto intro: \<tau>Exec_refl \<tau>Exec_step simp add: exec_move_def)
qed

inductive
  exec_1' :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_thread_action \<Rightarrow> jvm_state \<Rightarrow> bool"
  for P :: jvm_prog
  where
  exec_1_Normal:
  "\<lbrakk> (ta, xcp', h', frs') \<in> set (exec_instr (instrs_of P C M ! pc) P h stk loc C M pc frs);
     pc < length (instrs_of P C M);
     check_instr (instrs_of P C M ! pc) P h stk loc C M pc frs \<rbrakk>
  \<Longrightarrow> exec_1' P (None, h, (stk, loc, C, M, pc) # frs) ta (xcp', h', frs')"

|  exec_1_Throw:
  "(ta, \<sigma>) = exception_step P (\<epsilon>, \<lfloor>a\<rfloor>, h, f # frs)
  \<Longrightarrow> exec_1' P (\<lfloor>a\<rfloor>, h, f # frs) ta \<sigma>"

inductive \<tau>Exec_1 :: "J1_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool"
  for P :: J1_prog
  where
  \<tau>Exec_1_refl:  "\<tau>Exec_1 P \<sigma> \<sigma>"
| \<tau>Exec_1_step: "\<lbrakk> \<tau>Exec_1 P \<sigma> \<sigma>'; exec_1' (compP2 P) \<sigma>' \<epsilon> \<sigma>''; \<tau>Move2 P \<sigma>' \<rbrakk> \<Longrightarrow> \<tau>Exec_1 P \<sigma> \<sigma>''"

lemmas \<tau>Exec_1step = \<tau>Exec_1_step[OF \<tau>Exec_1_refl]
lemmas \<tau>Exec_2step = \<tau>Exec_1_step[OF \<tau>Exec_1_step, OF \<tau>Exec_1_refl]
lemmas \<tau>Exec_3step = \<tau>Exec_1_step[OF \<tau>Exec_1_step, OF \<tau>Exec_1_step, OF \<tau>Exec_1_refl]

lemma \<tau>Exec_1_induct [consumes 1, case_names refl step]:
  "\<lbrakk> \<tau>Exec_1 P \<sigma> \<sigma>'; Q \<sigma>;
     \<And>\<sigma>' \<sigma>''. \<lbrakk> \<tau>Exec_1 P \<sigma> \<sigma>'; exec_1' (compP2 P) \<sigma>' \<epsilon> \<sigma>''; \<tau>Move2 P \<sigma>'; Q \<sigma>' \<rbrakk> \<Longrightarrow> Q \<sigma>''\<rbrakk>
  \<Longrightarrow> Q \<sigma>'"
by(induct rule: \<tau>Exec_1.induct)(auto)

lemma \<tau>Exec_1_trans [trans]: 
  assumes one: "\<tau>Exec_1 P \<sigma> \<sigma>'"
  and two: "\<tau>Exec_1 P \<sigma>' \<sigma>''"
  shows "\<tau>Exec_1 P \<sigma> \<sigma>''"
using two one
by(induct rule: \<tau>Exec_1_induct)(auto intro: \<tau>Exec_1_step)

declare compxE2_size_convs[simp del] compxEs2_size_convs[simp del]
declare compxE2_stack_xlift_convs[simp del] compxEs2_stack_xlift_convs[simp del]

lemma exec_instr_frs_offer:
  "(ta, xcp', h', (stk', loc', C, M, pc') # frs) \<in> set (exec_instr ins P h stk loc C M pc frs)
  \<Longrightarrow> (ta, xcp', h', (stk', loc', C, M, pc') # frs @ frs') \<in> set (exec_instr ins P h stk loc C M pc (frs @ frs'))"
apply(cases ins)
apply(simp_all add: nth_append split_beta split: split_if_asm)
apply(force split: sum.split_asm simp add: extRet2JVM_def[folded sum_case_def])+
done

lemma check_instr_frs_offer:
  "\<lbrakk> check_instr ins P h stk loc C M pc frs; ins \<noteq> Return \<rbrakk>
  \<Longrightarrow> check_instr ins P h stk loc C M pc (frs @ frs')"
by(cases ins)(simp_all)

lemma exec_instr_CM_change:
  "(ta, xcp', h', (stk', loc', C, M, pc') # frs) \<in> set (exec_instr ins P h stk loc C M pc frs)
  \<Longrightarrow> (ta, xcp', h', (stk', loc', C', M', pc') # frs) \<in> set (exec_instr ins P h stk loc C' M' pc frs)"
apply(cases ins)
apply(simp_all add: nth_append split_beta neq_Nil_conv split: split_if_asm)
apply(force split: sum.split_asm simp add: extRet2JVM_def[folded sum_case_def])+
done

lemma check_instr_CM_change:
  "\<lbrakk> check_instr ins P h stk loc C M pc frs; ins \<noteq> Return \<rbrakk>
  \<Longrightarrow> check_instr ins P h stk loc C' M' pc frs"
by(cases ins)(simp_all)

lemma exec_move_exec_1':
  assumes exec: "exec_move P body h (stk, loc, pc, xcp) ta h' (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = body in D"
  shows "exec_1' (compP2 P) (xcp, h, (stk, loc, C, M, pc) # frs) ta (xcp', h', (stk', loc', C, M, pc') # frs)"
using exec unfolding exec_move_def
proof(cases)
  case (exec_instr TA XCP' H' STK' LOC' PC' PC H STK LOC)
  hence [simp]: "H = h" "STK = stk" "LOC = loc" "PC = pc" "xcp = None" "TA = ta" "H' = h'" 
    "STK' = stk'" "LOC' = loc'" "PC' = pc'" "XCP' = xcp'"
    and exec: "(ta, xcp', h', [(stk', loc', arbitrary, arbitrary, pc')])
                \<in> set (exec_instr (compE2 body ! pc) (compP2 P) h stk loc arbitrary arbitrary pc [])" by auto
  from exec have "(ta, xcp', h', [(stk', loc', C, M, pc')])
                \<in> set (exec_instr (compE2 body ! pc) (compP2 P) h stk loc C M pc [])"
    by(rule exec_instr_CM_change)
  from exec_instr_frs_offer[OF this, of frs]
  have "(ta, xcp', h', (stk', loc', C, M, pc') # frs)
        \<in> set (exec_instr (compE2 body ! pc) (compP2 P) h stk loc C M pc frs)" by simp
  moreover
  from check_instr_frs_offer[OF `check_instr (compE2 body ! PC) (compP2 P) H STK LOC arbitrary arbitrary PC []`, of frs]
    compE2_not_Return[of body] `PC < length (compE2 body)`
  have "check_instr (compE2 body ! PC) (compP2 P) H STK LOC C M PC frs"
    by(simp)(rule check_instr_CM_change, simp_all add: in_set_conv_nth)
  ultimately show ?thesis using sees_method_compP[OF sees, where f=compMb2] `PC < length (compE2 body)`
    by(auto simp add: compP2_def compMb2_def nth_append intro: exec_1_Normal)
next
  case exec_catch
  thus ?thesis using sees_method_compP[OF sees, of compMb2]
    by(auto simp add: compMb2_def compP2_def intro: exec_1_Throw)
qed

lemma \<tau>Exec_move_\<tau>Exec_1:
  assumes move: "\<tau>Exec_move P body h (stk, loc, pc, xcp) (stk', loc', pc', xcp')"
  and sees: "P \<turnstile> C sees M : Ts\<rightarrow>T = body in D"
  shows "\<tau>Exec_1 P (xcp, h, (stk, loc, C, M, pc) # frs') (xcp', h, (stk', loc', C, M, pc') # frs')"
using move
proof(induct rule: \<tau>Exec_move.induct[split_format (complete)])
  case \<tau>Exec_refl thus ?case by(rule \<tau>Exec_1_refl)
next
  case (\<tau>Exec_step stk loc pc xcp stk' loc' pc' xcp' stk'' loc'' pc'' xcp'')
  note ` \<tau>Exec_1 P (xcp, h, (stk, loc, C, M, pc) # frs') (xcp', h, (stk', loc', C, M, pc') # frs')`
  moreover from `exec_move P body h (stk', loc', pc', xcp') \<epsilon> h (stk'', loc'', pc'', xcp'')` sees
  have "exec_1' (compP2 P) (xcp', h, (stk', loc', C, M, pc') # frs') \<epsilon> (xcp'', h, (stk'', loc'', C, M, pc'') # frs')"
    by(rule exec_move_exec_1')
  moreover {
    fix a assume [simp]: "xcp' = \<lfloor>a\<rfloor>" 
    from sees_method_compP[OF sees, of compMb2]
    have "ex_table_of (compP2 P) C M = compxE2 body 0 0" by(simp add: compP2_def compMb2_def)
    with `exec_move P body h (stk', loc', pc', xcp') \<epsilon> h (stk'', loc'', pc'', xcp'')`
    have "match_ex_table (compP2 P) (cname_of h a) pc' (ex_table_of (compP2 P) C M) \<noteq> None" "pc' < length (compE2 body)"
      by(auto simp add: exec_move_def elim: exec_meth.cases) }
  with `\<tau>move2 body pc' xcp'` sees sees_method_compP[OF sees, of compMb2]
  have "\<tau>Move2 P (xcp', h, (stk', loc', C, M, pc') # frs')" by(clarsimp simp add: compMb2_def compP2_def)
  ultimately show ?case by(rule \<tau>Exec_1_step)
qed


inductive \<tau>Red :: "J1_prog \<Rightarrow> heap \<Rightarrow> expr1 \<Rightarrow> val list \<Rightarrow> expr1 \<Rightarrow> val list \<Rightarrow> bool"
  for P :: "J1_prog" and h :: heap
  where
  \<tau>Red_refl: "\<tau>Red P h e xs e xs"

| \<tau>Red_step:
  "\<lbrakk> \<tau>Red P h e xs e' xs'; P \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move1 e' \<rbrakk>
  \<Longrightarrow> \<tau>Red P h e xs e'' xs''"

lemmas \<tau>Red1step = \<tau>Red_step[OF \<tau>Red_refl]
lemmas \<tau>Red2step = \<tau>Red_step[OF \<tau>Red_step, OF \<tau>Red_refl]
lemmas \<tau>Red3step = \<tau>Red_step[OF \<tau>Red_step, OF \<tau>Red_step, OF \<tau>Red_refl]

lemma \<tau>Red_induct [consumes 1, case_names refl step]:
  "\<lbrakk> \<tau>Red P h e xs e' xs'; Q e xs;
     \<And>e' xs' e'' xs''.
       \<lbrakk> \<tau>Red P h e xs e' xs';
         P \<turnstile>1 \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>;
         \<tau>move1 e'; Q e' xs' \<rbrakk>
       \<Longrightarrow> Q e'' xs''\<rbrakk>
  \<Longrightarrow> Q e' xs'"
by(induct rule: \<tau>Red.induct)(auto)

inductive \<tau>Reds :: "J1_prog \<Rightarrow> heap \<Rightarrow> expr1 list \<Rightarrow> val list \<Rightarrow> expr1 list \<Rightarrow> val list \<Rightarrow> bool"
  for P :: "J1_prog" and h :: heap
  where
  \<tau>Reds_refl: "\<tau>Reds P h es xs es xs"

| \<tau>Reds_step:
  "\<lbrakk> \<tau>Reds P h es xs es' xs'; P \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves1 es' \<rbrakk>
  \<Longrightarrow> \<tau>Reds P h es xs es'' xs''"

lemmas \<tau>Reds1step = \<tau>Reds_step[OF \<tau>Reds_refl]
lemmas \<tau>Reds2step = \<tau>Reds_step[OF \<tau>Reds_step, OF \<tau>Reds_refl]
lemmas \<tau>Reds3step = \<tau>Reds_step[OF \<tau>Reds_step, OF \<tau>Reds_step, OF \<tau>Reds_refl]

lemma \<tau>Reds_induct [consumes 1, case_names refl step]:
  "\<lbrakk> \<tau>Reds P h es xs es' xs'; Q es xs;
     \<And>es' xs' es'' xs''.
       \<lbrakk> \<tau>Reds P h es xs es' xs';
         P \<turnstile>1 \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>;
         \<tau>moves1 es'; Q es' xs' \<rbrakk>
       \<Longrightarrow> Q es'' xs''\<rbrakk>
  \<Longrightarrow> Q es' xs'"
by(induct rule: \<tau>Reds.induct)(auto)


lemma NewArray_\<tau>Red_xt [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (newA T\<lfloor>e\<rceil>) xs (newA T\<lfloor>e'\<rceil>) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros New1ArrayRed \<tau>move1NewArray)

lemma Cast_\<tau>Red_xt [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (Cast T e) xs (Cast T e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Cast1Red \<tau>move1Cast)

lemma BinOp_\<tau>Red_xt1 [elim!]:
  "\<tau>Red P h e1 xs e1' xs' \<Longrightarrow> \<tau>Red P h (e1 \<guillemotleft>bop\<guillemotright> e2) xs (e1' \<guillemotleft>bop\<guillemotright> e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Bin1OpRed1 \<tau>move1BinOp1)

lemma \<tau>Red_preserves_len: "\<tau>Red P h e xs e' xs' \<Longrightarrow> length xs' = length xs"
by(induct rule: \<tau>Red.induct)(auto dest: red1_preserves_len)

lemma Block_None_\<tau>Red_xt:
  "\<lbrakk> \<tau>Red P h e xs e' xs'; V < length xs \<rbrakk> \<Longrightarrow> \<tau>Red P h {V:T=None; e}\<^bsub>cr\<^esub> xs {V:T=None; e'}\<^bsub>cr\<^esub> xs'"
by(induct rule: \<tau>Red.induct)
  (auto intro: \<tau>Red.intros dest: \<tau>Red_preserves_len intro: \<tau>move1Block elim!: \<tau>Red_step Block1RedNone)

lemma \<tau>Red_inj_\<tau>Reds: "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Reds P h (e # es) xs (e' # es) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Reds.intros List1Red1 \<tau>moves1Hd)

lemma \<tau>Reds_cons_\<tau>Reds: "\<tau>Reds P h es xs es' xs' \<Longrightarrow> \<tau>Reds P h (Val v # es) xs (Val v # es') xs'"
by(induct rule: \<tau>Reds.induct)(auto intro: \<tau>Reds.intros List1Red2 \<tau>moves1Tl)

lemma \<tau>Red_rtrancl_conv:
  "\<tau>Red P h = (\<lambda>e xs e' xs'. (\<lambda>(e, xs) (e', xs'). P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle> \<and> \<tau>move1 e)^** (e, xs) (e', xs'))"
proof(rule ext)+
  fix e xs e' xs'
  show "\<tau>Red P h e xs e' xs' \<longleftrightarrow> (\<lambda>(e, xs) (e', xs'). P \<turnstile>1 \<langle>e,(h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e',(h, xs')\<rangle> \<and> \<tau>move1 e)\<^sup>*\<^sup>* (e, xs) (e', xs')" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs thus ?rhs
      by induct(auto elim: rtranclp.rtrancl_into_rtrancl)
  next
    assume ?rhs thus ?lhs
      by(induct a\<equiv>"(e, xs)" b\<equiv>"(e', xs')" arbitrary: e xs e' xs' rule: rtranclp.induct)
        (blast intro: \<tau>Red_step intro: \<tau>Red_refl)+
  qed
qed


lemma converse_\<tau>RedE:
  assumes "\<tau>Red P h e xs e'' xs''"
  obtains "e = e''" "xs = xs''"
        | e' xs' where "P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>" "\<tau>move1 e" "\<tau>Red P h e' xs' e'' xs''"
using assms unfolding \<tau>Red_rtrancl_conv
by(rule converse_rtranclpE)(blast)+

lemma converse_\<tau>Red_step:
  "\<lbrakk> P \<turnstile>1 \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move1 e; \<tau>Red P h e' xs' e'' xs'' \<rbrakk> \<Longrightarrow> \<tau>Red P h e xs e'' xs''"
unfolding \<tau>Red_rtrancl_conv
apply(rule converse_rtranclp_into_rtranclp)
 prefer 2
 apply(assumption)
apply(simp)
done

lemma Block_\<tau>Red_None [elim!]:
  "\<lbrakk> \<tau>Red P h e xs e' xs'; V < length xs' \<rbrakk> \<Longrightarrow> \<tau>Red P h {V:T=None; e}\<^bsub>cr\<^esub> xs {V:T=None; e'}\<^bsub>cr\<^esub> xs'"
apply(induct rule: \<tau>Red.induct)
apply(fastsimp intro: \<tau>Red_refl elim!: \<tau>Red_step intro: Block1RedNone \<tau>move1Block dest: red1_preserves_len)+
done

lemma Block_\<tau>Red_Some:
  "\<lbrakk> \<tau>Red P h e (xs[V := v]) e' xs'; e \<noteq> e' \<or> xs[V := v] \<noteq> xs'; V < length xs \<rbrakk> 
  \<Longrightarrow> \<tau>Red P h {V:Ty=\<lfloor>v\<rfloor>; e}\<^bsub>cr\<^esub> xs {V:Ty=None; e'}\<^bsub>cr\<^esub> xs'"
apply(erule converse_\<tau>RedE)
 apply(simp)
apply(rule converse_\<tau>Red_step)
  apply(erule (1) Block1RedSome)
 apply(erule \<tau>move1Block)
apply(drule red1_preserves_len)
apply(frule \<tau>Red_preserves_len)
by clarsimp

lemma exec_meth_length_compE2_stack_xliftD:
  "exec_meth P (compE2 e) (stack_xlift d (compxE2 e 0 0)) h (stk, loc, pc, xcp) ta h' s'
  \<Longrightarrow> pc < length (compE2 e)"
by(cases s')(auto simp add: stack_xlift_compxE2)

lemma exec_meth_length_pc_xt_Nil:
  "exec_meth P ins [] h (stk, loc, pc, xcp) ta h' s' \<Longrightarrow> pc < length ins"
apply(erule exec_meth.cases)
apply(auto dest: match_ex_table_pc_length_compE2)
done

lemma BinOp_\<tau>Red_xt2 [elim!]:
  "\<tau>Red P h e2 xs e2' xs' \<Longrightarrow> \<tau>Red P h (Val v \<guillemotleft>bop\<guillemotright> e2) xs (Val v \<guillemotleft>bop\<guillemotright> e2') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Bin1OpRed2 \<tau>move1BinOp2)

lemma \<tau>Red_trans [trans]: 
  assumes one: "\<tau>Red P h e xs e' xs'"
  and two: "\<tau>Red P h e' xs' e'' xs''"
  shows "\<tau>Red P h e xs e'' xs''"
using two one
by(induct rule: \<tau>Red_induct)(auto intro: \<tau>Red_step)

lemma BinOp_exec2D:
  assumes exec: "exec_meth (compP2 P) (compE2 (e1 \<guillemotleft>bop\<guillemotright> e2)) (compxE2 (e1 \<guillemotleft>bop\<guillemotright> e2) 0 0) h (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc < length (compE2 e2)"
  shows "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp') \<and> pc' \<ge> length (compE2 e1)"
proof
  from exec have "exec_meth (compP2 P) ((compE2 e1 @ compE2 e2) @ (case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]))
     (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h
     (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxE2_size_convs compxE2_stack_xlift_convs)
  hence exec': "exec_meth (compP2 P) (compE2 e1 @ compE2 e2) (compxE2 e1 0 0 @ shift (length (compE2 e1)) (stack_xlift (length [v1]) (compxE2 e2 0 0))) h
     (stk @ [v1], loc, length (compE2 e1) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take) (simp add: pc)
  thus "exec_meth (compP2 P) (compE2 e2) (stack_xlift (length [v1]) (compxE2 e2 0 0)) h
     (stk @ [v1], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 e1), xcp')"
    by(rule exec_meth_drop_xt) auto
  from exec' show "pc' \<ge> length (compE2 e1)"
   by(rule exec_meth_drop_xt_pc)(auto)
qed  

lemma \<tau>Red_ThrowD [dest]: "\<tau>Red P h (Throw a) xs e'' xs'' \<Longrightarrow> e'' = Throw a \<and> xs'' = xs"
by(induct e\<equiv>"Throw a :: expr1" xs e'' xs'' rule: \<tau>Red.induct)(auto)


lemma LAss_\<tau>Red [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (V := e) xs (V := e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros LAss1Red \<tau>move1LAss)

lemma AAcc_\<tau>Red_xt1 [elim!]:
  "\<tau>Red P h a xs a' xs' \<Longrightarrow> \<tau>Red P h (a\<lfloor>i\<rceil>) xs (a'\<lfloor>i\<rceil>) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros AAcc1Red1 \<tau>move1AAcc1)

lemma AAcc_\<tau>Red_xt2 [elim!]:
  "\<tau>Red P h i xs i' xs' \<Longrightarrow> \<tau>Red P h (Val a\<lfloor>i\<rceil>) xs (Val a\<lfloor>i'\<rceil>) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros AAcc1Red2 \<tau>move1AAcc2)

lemma AAss_\<tau>Red_xt1 [elim!]:
  "\<tau>Red P h a xs a' xs' \<Longrightarrow> \<tau>Red P h (a\<lfloor>i\<rceil> := e) xs (a'\<lfloor>i\<rceil> := e) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros AAss1Red1 \<tau>move1AAss1)

lemma AAss_\<tau>Red_xt2 [elim!]:
  "\<tau>Red P h i xs i' xs' \<Longrightarrow> \<tau>Red P h (Val a\<lfloor>i\<rceil> := e) xs (Val a\<lfloor>i'\<rceil> := e) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros AAss1Red2 \<tau>move1AAss2)

lemma AAss_\<tau>Red_xt3 [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (Val a\<lfloor>Val i\<rceil> := e) xs (Val a\<lfloor>Val i\<rceil> := e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros AAss1Red3 \<tau>move1AAss3)

lemma ALength_\<tau>Red_xt [elim!]:
  "\<tau>Red P h a xs a' xs' \<Longrightarrow> \<tau>Red P h (a\<bullet>length) xs (a'\<bullet>length) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros ALength1Red \<tau>move1ALength)

lemma FAcc_\<tau>Red_xt [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (e\<bullet>F{D}) xs (e'\<bullet>F{D}) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros FAcc1Red \<tau>move1FAcc)

lemma FAss_\<tau>Red_xt1 [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (e\<bullet>F{D} := e2) xs (e'\<bullet>F{D} := e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros FAss1Red1 \<tau>move1FAss1)

lemma FAss_\<tau>Red_xt2 [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (Val v\<bullet>F{D} := e) xs (Val v\<bullet>F{D} := e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros FAss1Red2 \<tau>move1FAss2)

lemma Call_\<tau>Red_obj [elim!]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (e\<bullet>M(ps)) xs (e'\<bullet>M(ps)) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Call1Obj \<tau>move1CallObj)

lemma Call_\<tau>Red_param [elim!]:
  "\<tau>Reds P h es xs es' xs' \<Longrightarrow> \<tau>Red P h (Val v\<bullet>M(es)) xs (Val v\<bullet>M(es')) xs'"
by(induct rule: \<tau>Reds.induct)(auto intro: \<tau>Red.intros Call1Params \<tau>move1CallParams)

lemma Call_execParamD:
  assumes exec: "exec_meth (compP2 P) (compE2 (obj\<bullet>M'(ps))) (compxE2 (obj\<bullet>M'(ps)) 0 0) h (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
  and pc: "pc < length (compEs2 ps)"
  shows "exec_meth (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp') \<and> pc' \<ge> length (compE2 obj)"
proof
  from exec have "exec_meth (compP2 P) ((compE2 obj @ compEs2 ps) @ [Invoke M' (length ps)])
     (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) h
     (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(simp add: compxEs2_size_convs compxEs2_stack_xlift_convs)
  hence exec': "exec_meth (compP2 P) (compE2 obj @ compEs2 ps) (compxE2 obj 0 0 @ shift (length (compE2 obj)) (stack_xlift (length [v]) (compxEs2 ps 0 0))) h
     (stk @ [v], loc, length (compE2 obj) + pc, xcp) ta h' (stk', loc', pc', xcp')"
    by(rule exec_meth_take)(simp add: pc)
  thus "exec_meth (compP2 P) (compEs2 ps) (stack_xlift (length [v]) (compxEs2 ps 0 0)) h (stk @ [v], loc, pc, xcp) ta h' (stk', loc', pc' - length (compE2 obj), xcp')"
    by(rule exec_meth_drop_xt) auto
  from exec' show "pc' \<ge> length (compE2 obj)"
   by(rule exec_meth_drop_xt_pc)(auto)
qed  

lemma Sync_\<tau>Red [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (sync\<^bsub>V\<^esub> (e) e2) xs (sync\<^bsub>V\<^esub> (e') e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Synchronized1Red1 \<tau>move1Sync)

lemma InSync_\<tau>Red_1 [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (insync\<^bsub>V\<^esub> (a) e) xs (insync\<^bsub>V\<^esub> (a) e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Synchronized1Red2 \<tau>move1InSync)

lemma Seq_\<tau>Red [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (e;;e2) xs (e';;e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Seq1Red \<tau>move1Seq)

lemma Cond_\<tau>Red [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (if (e) e1 else e2) xs (if (e') e1 else e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Cond1Red \<tau>move1Cond)

lemma Throw_\<tau>Red [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (throw e) xs (throw e') xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Throw1Red \<tau>move1Throw)

lemma Try_\<tau>Red [elim]:
  "\<tau>Red P h e xs e' xs' \<Longrightarrow> \<tau>Red P h (try e catch(C V) e2) xs (try e' catch(C V) e2) xs'"
by(induct rule: \<tau>Red.induct)(auto intro: \<tau>Red.intros Try1Red \<tau>move1Try)

lemma \<tau>Reds_trans [trans]: 
  assumes one: "\<tau>Reds P h es xs es' xs'"
  and two: "\<tau>Reds P h es' xs' es'' xs''"
  shows "\<tau>Reds P h es xs es'' xs''"
using two one
by(induct rule: \<tau>Reds_induct)(auto intro: \<tau>Reds_step)

inductive \<tau>Red1 :: "J1_prog \<Rightarrow> heap \<Rightarrow> (expr1 \<times> locals1) \<times> ((expr1 \<times> locals1) list) \<Rightarrow>
                           (expr1 \<times> locals1) \<times> ((expr1 \<times> locals1) list) \<Rightarrow> bool"
for P ::J1_prog and h :: heap
where
  \<tau>Red1_refl: "\<tau>Red1 P h exs exs"
| \<tau>Red1_step: "\<lbrakk> \<tau>Red1 P h exs (ex', exs'); P \<turnstile>1 \<langle>ex'/exs', h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex''/exs'', h\<rangle>; \<tau>Move1 (ex', exs') \<rbrakk> \<Longrightarrow> \<tau>Red1 P h exs (ex'', exs'')"

lemmas \<tau>Red1_1step = \<tau>Red1_step[OF \<tau>Red1_refl]
lemmas \<tau>Red1_2step = \<tau>Red1_step[OF \<tau>Red1_step, OF \<tau>Red1_refl]
lemmas \<tau>Red1_3step = \<tau>Red1_step[OF \<tau>Red1_step, OF \<tau>Red1_step, OF \<tau>Red1_refl]

lemma \<tau>Red1_induct [consumes 1, case_names refl step]:
  "\<lbrakk> \<tau>Red1 P h exs exs'; Q exs;
     \<And>exs' ex'' exs''.
       \<lbrakk> \<tau>Red1 P h exs exs';
         P \<turnstile>1 \<langle>fst exs'/snd exs', h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex''/exs'', h\<rangle>;
         \<tau>Move1 exs'; Q exs' \<rbrakk>
       \<Longrightarrow> Q (ex'', exs'')\<rbrakk>
  \<Longrightarrow> Q exs'"
by(induct rule: \<tau>Red1.induct)(auto)

lemma \<tau>Red1_rtrancl_conv:
  "\<tau>Red1 P h = (\<lambda>(ex, exs) (ex', exs'). P \<turnstile>1 \<langle>ex/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex'/exs', h\<rangle> \<and> \<tau>Move1 (ex, exs))^**"
  (is "_ = (?r)^**")
proof(intro ext)
  fix exs exs'
  show "\<tau>Red1 P h exs exs' = ?r^** exs exs'" (is "?lhs = ?rhs")
  proof
    assume ?lhs thus ?rhs
      by(induct)(auto intro: rtranclp.rtrancl_into_rtrancl)
  next
    assume ?rhs thus ?lhs
      by(induct)(auto intro: \<tau>Red1.intros)
  qed
qed

lemma \<tau>Red1_trans [trans]:
  "\<lbrakk> \<tau>Red1 P h exs exs'; \<tau>Red1 P h exs' exs'' \<rbrakk> \<Longrightarrow> \<tau>Red1 P h exs exs''"
unfolding \<tau>Red1_rtrancl_conv by(rule rtranclp_trans)

lemma \<tau>Red_into_\<tau>Red1:
  "\<tau>Red P h e xs e'' xs'' \<Longrightarrow> \<tau>Red1 P h ((e, xs), exs) ((e'', xs''), exs)"
apply(induct rule: \<tau>Red.induct)
apply(fastsimp intro: \<tau>Red1.intros dest: red1Red)+
done

lemma \<tau>Red_preserves_B:
 "\<lbrakk> \<tau>Red P h e xs e' xs'; \<B> e n \<rbrakk> \<Longrightarrow> \<B> e' n"
apply(induct rule: \<tau>Red.induct)
apply(auto intro: red1_preserves_B)
done

theorem \<tau>Red1_subject_reduction:
  assumes wf: "wf_prog wf_md P"
  and hconf: "P \<turnstile> h \<surd>"
  shows "\<lbrakk> \<tau>Red P h e xs e' xs'; P,E,h \<turnstile>1 e:T;
     P,h,A \<turnstile>1 xs (:\<le>) E @ env_exp e;
     \<D>1 (length E) e \<lfloor>A\<rfloor>; \<B> e (length E) \<rbrakk>
  \<Longrightarrow> \<exists>A' T'. P,h,A' \<turnstile>1 xs' (:\<le>) E @ env_exp e' \<and> 
          \<D>1 (length E) e' \<lfloor>A'\<rfloor> \<and> P,E,h \<turnstile>1 e' : T' \<and> P \<turnstile> T' \<le> T"
apply(induct rule: \<tau>Red.induct)
 apply fastsimp
apply clarsimp
apply(frule (1) \<tau>Red_preserves_B)
apply(frule red1_preserves_lconf_defass)
    apply(simp_all)
apply(frule subject_reduction1[OF wf])
apply(auto intro: hconf widen_trans)
done

lemma \<tau>Red_max_vars: "\<tau>Red P h e xs e' xs' \<Longrightarrow> max_vars e' \<le> max_vars e"
apply(induct rule: \<tau>Red.induct)
apply(auto dest: red1_max_vars)
done

lemma exec_meth_\<tau>_heap_unchanged:
  "\<lbrakk> \<tau>move2 e pc None; (ta, xcp', h', frs') \<in> set (exec_instr (compE2 e ! pc) P h stk loc C M pc' frs) \<rbrakk> \<Longrightarrow> h' = h"

  and exec_meth_\<tau>s_heap_unchanged:
  "\<lbrakk> \<tau>moves2 es pc None; (ta, xcp', h', frs') \<in> set (exec_instr (compEs2 es ! pc) P h stk loc C M pc' frs) \<rbrakk> \<Longrightarrow> h' = h"
apply(induct e pc xcp\<equiv>"None::addr option" and es pc xcp\<equiv>"None :: addr option"
      arbitrary: ta h' frs' stk loc C M frs pc' xcp' and ta h' frs' stk loc C M frs pc' xcp'
      rule: \<tau>move2_\<tau>moves2.inducts)
apply(auto dest: \<tau>move2_pc_length_compE2 \<tau>moves2_pc_length_compEs2 simp add: nth_append split: split_if_asm)
apply(auto simp add: nth_Cons nth_append dest: \<tau>move2_pc_length_compE2 split: nat.split_asm split_if_asm)
done


lemma \<tau>Exec_1_rtranclpD:
  "\<tau>Exec_1 P (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> (\<lambda>((xcp, frs), h) ((xcp', frs'), h'). exec_1' (compP2 P) (xcp, h, frs) \<epsilon> (xcp', h', frs') \<and> \<tau>Move2 P (xcp, h, frs))^** ((xcp, frs), h) ((xcp', frs'), h')"
apply(induct s\<equiv>"(xcp,h,frs)" s'\<equiv>"(xcp', h', frs')" arbitrary: xcp h frs xcp' h' frs' rule: \<tau>Exec_1.induct)
apply(fastsimp intro: rtranclp.rtrancl_into_rtrancl)+
done

lemma \<tau>Red1_rtranclpD:
  "\<tau>Red1 P h s s' \<Longrightarrow> (\<lambda>((ex, exs), h) ((ex', exs'), h'). P \<turnstile>1 \<langle>ex/exs, h\<rangle> -\<epsilon>\<rightarrow> \<langle>ex'/exs', h'\<rangle> \<and> \<tau>Move1 (ex, exs))^** (s, h) (s', h)"
apply(induct rule: \<tau>Red1.induct)
apply(auto intro: rtranclp.rtrancl_into_rtrancl)
done

end