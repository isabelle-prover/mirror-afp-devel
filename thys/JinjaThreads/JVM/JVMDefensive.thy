(*  Title:      JinjaThreads/JVM/JVMDefensive.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{A Defensive JVM} *}

theory JVMDefensive
imports JVMExec "../Common/Conform"
begin

text {*
  Extend the state space by one element indicating a type error (or
  other abnormal termination) *}
datatype 'a type_error = TypeError | Normal 'a

consts
  check_instr :: "[instr, jvm_prog, heap, val list, val list, 
                  cname, mname, pc, frame list] \<Rightarrow> bool"
primrec 
check_instr_Load:
  "check_instr (Load n) P h stk loc C M\<^isub>0 pc frs = 
  (n < length loc)"

check_instr_Store:
  "check_instr (Store n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> n < length loc)"

check_instr_Push:
  "check_instr (Push v) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (\<not>is_Addr v)"

check_instr_New:
  "check_instr (New C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  is_class P C"

check_instr_NewArray:
  "check_instr (NewArray T) P h stk loc C0 M0 pc frs =
  (is_type P T \<and> 0 < length stk \<and> is_Intg (hd stk))"

check_instr_ALoad:
  "check_instr ALoad P h stk loc C0 M0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and>
  (let ref = hd (tl stk)
   in is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
        h (the_Addr ref) \<noteq> None \<and> is_Arr (the (h (the_Addr ref))))))"

check_instr_AStore:
  "check_instr AStore P h stk loc C0 M0 pc frs =
  (2 < length stk \<and> is_Intg (hd (tl stk)) \<and>
  (let ref = hd (tl (tl stk))
   in is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow>
        h (the_Addr ref) \<noteq> None \<and> is_Arr (the (h (the_Addr ref))))))"

check_instr_Getfield:
  "check_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and> 
  (let (C', T) = field P C F; ref = hd stk in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> \<not> is_Arr (the (h (the_Addr ref))) \<and>
      (let (D,vs) = the_obj (the (h (the_Addr ref))) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> vs (F,C) \<noteq> None \<and> P,h \<turnstile> the (vs (F,C)) :\<le> T))))" 

check_instr_Putfield:
  "check_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (1 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F:T in C') \<and>
  (let (C', T) = field P C F; v = hd stk; ref = hd (tl stk) in 
    C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
      h (the_Addr ref) \<noteq> None \<and> \<not> is_Arr (the (h (the_Addr ref))) \<and>
      (let D = fst (the_obj (the (h (the_Addr ref)))) in 
        P \<turnstile> D \<preceq>\<^sup>* C \<and> P,h \<turnstile> v :\<le> T))))" 

check_instr_Checkcast:
  "check_instr (Checkcast T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_type P T \<and> is_Ref (hd stk))"

check_instr_Invoke:
  "check_instr (Invoke M n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (n < length stk \<and> is_Ref (stk!n) \<and>  
  (stk!n \<noteq> Null \<longrightarrow> 
    (let a = the_Addr (stk!n); 
         C = cname_of h a;
         Ts = fst (snd (method P C M))
    in h a \<noteq> None \<and>  
       (\<not> is_Arr (the (h a)) \<and> P \<turnstile> C has M \<and> P,h \<turnstile> rev (take n stk) [:\<le>] Ts \<or> 
        \<not> is_Arr (the (h a)) \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M = start \<and> n = 0 \<and> is_class P Thread \<or>
        \<not> is_Arr (the (h a)) \<and> P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M = join \<and> n = 0 \<and> is_class P Thread \<or>
        M = wait \<and> n = 0 \<or>
        M = notify \<and> n = 0 \<or>
        M = notifyAll \<and> n =0))))" 

check_instr_Return:
  "check_instr Return P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> ((0 < length frs) \<longrightarrow> 
    (P \<turnstile> C\<^isub>0 has M\<^isub>0) \<and>    
    (let v = hd stk; 
         T = fst (snd (snd (method P C\<^isub>0 M\<^isub>0)))
     in P,h \<turnstile> v :\<le> T)))"
 
check_instr_Pop:
  "check_instr Pop P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (0 < length stk)"

check_instr_IAdd:
  "check_instr IAdd P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk \<and> is_Intg (hd stk) \<and> is_Intg (hd (tl stk)))"

check_instr_IfFalse:
  "check_instr (IfFalse b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Bool (hd stk) \<and> 0 \<le> int pc+b)"

check_instr_CmpEq:
  "check_instr CmpEq P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (1 < length stk)"

check_instr_Goto:
  "check_instr (Goto b) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 \<le> int pc+b)"

check_instr_Throw:
  "check_instr Throw P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (0 < length stk \<and> is_Ref (hd stk))"

check_instr_MEnter:
  "check_instr MEnter P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"

check_instr_MExit:
  "check_instr MExit P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   (0 < length stk \<and> is_Ref (hd stk))"



constdefs
  check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool"
  "check P \<sigma> \<equiv> let (xcpt, h, frs) = \<sigma> in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,M,pc)#frs' \<Rightarrow> 
                P \<turnstile> C has M \<and>
                (let (C',Ts,T,mxs,mxl\<^isub>0,ins,xt) = method P C M; i = ins!pc in
                 pc < size ins \<and> size stk \<le> mxs \<and>
                 check_instr i P h stk loc C M pc frs'))"


  exec_d :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> ((addr,thread_id,jvm_thread_state,heap,addr) thread_action \<times> jvm_state) list type_error"
  "exec_d P \<sigma> \<equiv> if check P \<sigma> then Normal (exec (P, \<sigma>)) else TypeError"


inductive
  exec_1_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
       ("_ \<turnstile> _ -_-jvmd\<rightarrow> _" [61,61,0,61] 60)
  for P :: jvm_prog
where
  exec_1_d_ErrorI: "exec_d P \<sigma> = TypeError \<Longrightarrow> P \<turnstile> Normal \<sigma> -\<epsilon>-jvmd\<rightarrow> TypeError"
| exec_1_d_NormalI: "\<lbrakk> exec_d P \<sigma> = Normal \<Sigma>; (tas, \<sigma>') \<in> set \<Sigma> \<rbrakk>  \<Longrightarrow> P \<turnstile> Normal \<sigma> -tas-jvmd\<rightarrow> Normal \<sigma>'"

lemma jvmd_NormalD:
  "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' \<Longrightarrow> check P \<sigma> \<and> (ta, \<sigma>') \<in> set (exec (P, \<sigma>)) \<and> (\<exists>h f frs. \<sigma> = (None, h, f # frs))"
apply(erule exec_1_d.cases, auto simp add: exec_d_def split: split_if_asm)
 apply(case_tac a, auto)
 apply(case_tac b, auto)
apply(case_tac a, auto)
 apply(case_tac b, auto)
apply(case_tac b, auto)
done

lemma jvmd_NormalE:
  assumes "P \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'"
  obtains h f frs where "check P \<sigma>" "(ta, \<sigma>') \<in> set (exec (P, \<sigma>))" "\<sigma> = (None, h, f # frs)"
using assms
by(auto dest: jvmd_NormalD)


-- "reflexive transitive closure:"

definition
  exec_star_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> (addr,thread_id,jvm_thread_state,heap,addr) thread_action list \<Rightarrow> jvm_state type_error \<Rightarrow> bool"
                 ("_ \<turnstile>/ _ -_-jvmd\<rightarrow>*/ _" [61,61,0,61] 60)
where
  "P \<turnstile> \<sigma> -tas-jvmd\<rightarrow>* \<sigma>' \<equiv> stepify_pred (exec_1_d P) \<sigma> tas \<sigma>'"

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

lemma if_neq [dest!]:
  "(if P then A else B) \<noteq> B \<Longrightarrow> P"
  by (cases P, auto)

lemma exec_d_no_errorI [intro]:
  "check P \<sigma> \<Longrightarrow> exec_d P \<sigma> \<noteq> TypeError"
  by (unfold exec_d_def) simp

theorem no_type_error_commutes:
  "exec_d P \<sigma> \<noteq> TypeError \<Longrightarrow> exec_d P \<sigma> = Normal (exec (P, \<sigma>))"
  by (unfold exec_d_def, auto)


lemma defensive_imp_aggressive_1:
  "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow> (Normal \<sigma>') \<Longrightarrow> P \<turnstile> \<sigma> -tas-jvm\<rightarrow> \<sigma>'"
by(auto elim!: exec_1_d.cases intro!: exec_1.intros simp add: exec_d_def split: split_if_asm)


lemma defensive_imp_aggressive:
  assumes "P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>')"
  shows "P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
proof -
  have "\<And>x y. P \<turnstile> x -tas-jvmd\<rightarrow>* y \<Longrightarrow> \<forall>\<sigma> \<sigma>'. x = Normal \<sigma> \<longrightarrow> y = Normal \<sigma>' \<longrightarrow>  P \<turnstile> \<sigma> -tas-jvm\<rightarrow>* \<sigma>'"
    apply(unfold exec_star_d_def)
    apply(erule stepify_pred.induct)
     apply(unfold exec_star_def)
     apply(fastsimp intro: stepify_pred_refl)
    apply(fold exec_star_d_def)
    apply(simp split: type_error.splits)
    apply(case_tac a, simp, simp)
    apply(case_tac a', simp)
     apply(erule exec_1_d.cases)
      apply(simp)
     apply(simp)
    apply(simp)
    apply(case_tac a'', simp, simp)
    apply(drule defensive_imp_aggressive_1)
    by(rule stepify_pred_step)
  with `P \<turnstile> (Normal \<sigma>) -tas-jvmd\<rightarrow>* (Normal \<sigma>')`
  show ?thesis
    by blast
qed


lemma check_exec_hext:
  assumes exec: "(ta, xcp', h', frs') \<in> set (exec (P, None, h, frs))"
  and check: "check P (None, h, frs)"
  shows "h \<unlhd> h'"
proof -
  from exec have "frs \<noteq> []" by(auto)
  then obtain f Frs where frs [simp]: "frs = f # Frs"
    by(fastsimp simp add: neq_Nil_conv)
  obtain stk loc C0 M0 pc where f [simp]: "f = (stk, loc, C0, M0, pc)"
    by(cases f, blast)
  from check obtain C' Ts T mxs mxl0 ins xt
    where mthd: "method P C0 M0 = (C', Ts, T, mxs, mxl0, ins, xt)"
    and check_ins: "check_instr (ins ! pc) P h stk loc C0 M0 pc Frs"
    and "pc < length ins"
    and "length stk \<le> mxs"
    by(auto simp add: check_def, blast)
  show ?thesis
  proof(cases xcp')
    case None
    with exec mthd
    have "(ta, None, h', frs') \<in> (\<lambda>(tas, xcpt', h', frs'). (tas, case xcpt' of None \<Rightarrow> (None, h', frs') | \<lfloor>a\<rfloor> \<Rightarrow> find_handler P a h ((stk, loc, C0, M0, pc) # Frs))) ` 
                                 set (exec_instr (ins ! pc) P h stk loc C0 M0 pc Frs)" by(auto)
    thus ?thesis
    proof(rule imageE)
      fix x
      assume xexec: "x \<in> set (exec_instr (ins ! pc) P h stk loc C0 M0 pc Frs)"
	and imagex: "(ta, None, h', frs') = (\<lambda>(tas, xcpt', h', frs').
                      (tas, case xcpt' of None \<Rightarrow> (None, h', frs')
                                         | \<lfloor>a\<rfloor> \<Rightarrow> find_handler P a h ((stk, loc, C0, M0, pc) # Frs))) x"
      obtain ta'' xcpt'' h'' frs'' where x: "x = (ta'', xcpt'', h'', frs'')"
	by(cases x, blast)
      with imagex have xexec': "(None, h', frs') = (case xcpt'' of None \<Rightarrow> (None, h'', frs'')
                                                                  | \<lfloor>a\<rfloor> \<Rightarrow> find_handler P a h ((stk, loc, C0, M0, pc) # Frs))"
	and "ta = ta''" by(auto)
      show ?thesis
      proof(cases xcpt'')
	case None
	with xexec' have "h' = h''" "frs' = frs''" by auto
	with `ta = ta''` x xexec None
	have taexec: "(ta, None, h', frs') \<in> set (exec_instr (ins ! pc) P h stk loc C0 M0 pc Frs)" by simp
	thus ?thesis
	proof(cases "ins ! pc")
	  case (New C)
	  moreover with check_ins taexec obtain a where "new_Addr h = \<lfloor>a\<rfloor>" by(auto)
	  moreover hence "h a = None" by(auto dest: new_Addr_SomeD)
	  moreover note taexec
	  ultimately show ?thesis by(auto intro!: hext_new)
	next
	  case (NewArray T)
	  moreover with check_ins taexec
	  obtain a where "new_Addr h = \<lfloor>a\<rfloor>"
	    by(simp split: if_splits)
	  moreover hence "h a = None"
	    by(auto dest: new_Addr_SomeD)
	  ultimately show ?thesis using taexec
	    by(auto intro!: hext_new split: split_if_asm)
	next
	  case AStore
	  with taexec check_ins show ?thesis
	    by(auto intro: hext_upd_arr elim!: is_ArrE simp add: split_beta split: split_if_asm)
	next
	  case Putfield
	  with taexec check_ins show ?thesis
	    by(auto intro: hext_upd_obj elim!: is_ArrE simp add: split_beta is_Ref_def split: split_if_asm)
	qed(auto simp add: split_beta split: split_if_asm)
      next
	case (Some a)
	with xexec' `frs = f # Frs` `f = (stk, loc, C0, M0, pc)`
	have "(None, h', frs') = find_handler P a h frs" by(simp)
	hence "h' = fst (snd (find_handler P a h frs))"
	  by - (drule sym, simp)
	hence "h = h'"
	  by(auto intro: find_handler_preserves_heap[symmetric])
	thus ?thesis by auto
      qed
    qed
  next
    case (Some a)
    with exec mthd obtain ad where "(\<lfloor>a\<rfloor>, h', frs') = find_handler P ad h Frs" by(auto)
    hence "h' = fst (snd (find_handler P ad h Frs))" by - (drule sym, simp)
    hence "h = h'" by(auto intro: find_handler_preserves_heap[symmetric])
    thus ?thesis by auto
  qed
qed

lemma exec_1_d_hext:
  "\<lbrakk> P \<turnstile> Normal (None, h, frs) -ta-jvmd\<rightarrow> Normal (xcp', h', frs') \<rbrakk> \<Longrightarrow> h \<unlhd> h'"
apply(auto elim!: exec_1_d.cases simp add: exec_d_def split: split_if_asm intro: check_exec_hext)
done


end
