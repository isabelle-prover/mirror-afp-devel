theory JVMExec_Execute
imports
  "../JVM/JVMExec"
  ExternalCall_Execute
begin

subsection {* Manual translation of the JVM to @{text "Cset"} *}

locale JVM_heap_execute = heap_execute +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id" 
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr" 
  and empty_heap :: "'heap" 
  and new_obj :: "'heap \<Rightarrow> String.literal \<Rightarrow> 'heap \<times> 'addr option" 
  and new_arr :: "'heap \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> 'heap \<times> 'addr option" 
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<Rightarrow> ty option" 
  and array_length :: "'heap \<Rightarrow> 'addr \<Rightarrow> nat" 
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val Cset.set" 
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap Cset.set"

sublocale JVM_heap_execute < execute!: JVM_heap_base
  addr2thread_id thread_id2addr 
  empty_heap new_obj new_arr typeof_addr array_length
  "\<lambda>h a ad v. v \<in> member (heap_read h a ad)" "\<lambda>h a ad v h'. h' \<in> Cset.member (heap_write h a ad v)"
.

context JVM_heap_execute begin

definition exec_instr ::
  "'addr instr \<Rightarrow> 'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> 'addr val list
  \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> 'addr frame list 
  \<Rightarrow> (('addr, 'thread_id, 'heap) jvm_thread_action \<times> ('addr, 'heap) jvm_state) Cset.set"
where
  "exec_instr i P t h stk loc C M pc frs
  = Cset.Set (execute.exec_instr i P t h stk loc C M pc frs)"

lemma member_exec_instr [simp]:
  "member (exec_instr i P t h stk loc C M pc frs) = execute.exec_instr i P t h stk loc C M pc frs"
by(simp add: exec_instr_def)

lemma exec_instr_code [code]:
  "exec_instr (Load n) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
   Cset.set [(\<epsilon>, (None, h, ((loc ! n) # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs))]"
  "exec_instr (Store n) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
   Cset.set [(\<epsilon>, (None, h, (tl stk, loc[n:=hd stk], C\<^isub>0, M\<^isub>0, pc+1)#frs))]"
  "exec_instr (Push v) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
   Cset.set [(\<epsilon>, (None, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs))]"
  "exec_instr (New C) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
   Cset.single 
     (let (h', ao) = new_obj h C
      in case ao of None \<Rightarrow> (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt OutOfMemory\<rfloor>, h', (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
                | Some a \<Rightarrow> (\<lbrace>NewObj a C\<rbrace>, None, h', (Addr a # stk, loc, C\<^isub>0, M\<^isub>0, pc + 1)#frs))"
  "exec_instr (NewArray T) P t h stk loc C0 M0 pc frs =
   Cset.single
    (let si = the_Intg (hd stk);
         i = nat (sint si)
      in (if si <s 0
          then (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
          else (let (h', ao) = new_arr h T i
                in case ao of None \<Rightarrow> (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt OutOfMemory\<rfloor>, h', (stk, loc, C0, M0, pc) # frs)
                          | Some a \<Rightarrow> (\<lbrace>NewArr a T i\<rbrace>, None, h', (Addr a # tl stk, loc, C0, M0, pc + 1) # frs))))"
  "exec_instr ALoad P t h stk loc C0 M0 pc frs =
   (let i = the_Intg (hd stk);
        va = hd (tl stk);
        a = the_Addr va
    in (if va = Null then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
        else if i <s 0 \<or> int (array_length h a) \<le> sint i then
             Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
        else do {
           v \<leftarrow> heap_read h a (ACell (nat (sint i)));
           Cset.single (\<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>, None, h, (v # tl (tl stk), loc, C0, M0, pc + 1) # frs)
        }))"
  "exec_instr AStore P t h stk loc C0 M0 pc frs =
  (let ve = hd stk;
       vi = hd (tl stk);
       va = hd (tl (tl stk))
   in (if va = Null then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
       else (let i = the_Intg vi;
                 idx = nat (sint i);
                 a = the_Addr va;
                 T = the (typeof_addr h a);
                 U = the (execute.typeof_h h ve)
             in (if i <s 0 \<or> int (array_length h a) \<le> sint i then
                      Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
                 else if P \<turnstile> U \<le> the_Array T then 
                      do {
                         h' \<leftarrow> heap_write h a (ACell idx) ve;
                         Cset.single (\<lbrace>WriteMem a (ACell idx) ve\<rbrace>, None, h', (tl (tl (tl stk)), loc, C0, M0, pc+1) # frs)
                      }
                 else Cset.single (\<epsilon>, (\<lfloor>execute.addr_of_sys_xcpt ArrayStore\<rfloor>, h, (stk, loc, C0, M0, pc) # frs))))))"
  "exec_instr ALength P t h stk loc C0 M0 pc frs =
   Cset.single
     (\<epsilon>, (let va = hd stk
          in if va = Null
             then (\<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
             else (None, h, (Intg (word_of_int (int (array_length h (the_Addr va)))) # tl stk, loc, C0, M0, pc+1) # frs)))"
  "exec_instr (Getfield F C) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
   (let v = hd stk
    in if v = Null then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
       else let a = the_Addr v
            in do {
               v' \<leftarrow> heap_read h a (CField C F);
               Cset.single (\<lbrace>ReadMem a (CField C F) v'\<rbrace>, None, h, (v' # (tl stk), loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)
            })"
  "exec_instr (Putfield F C) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  (let v = hd stk;
       r = hd (tl stk)
   in if r = Null then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
      else let a = the_Addr r
           in do {
                h' \<leftarrow> heap_write h a (CField C F) v;
                Cset.single (\<lbrace>WriteMem a (CField C F) v\<rbrace>, None, h', (tl (tl stk), loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)
              })"
 "exec_instr (Checkcast T) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  Cset.single
    (\<epsilon>, let U = the (typeof\<^bsub>h\<^esub> (hd stk))
        in if P \<turnstile> U \<le> T then (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)
           else (\<lfloor>execute.addr_of_sys_xcpt ClassCast\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs))"
  "exec_instr (Instanceof T) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   Cset.single (\<epsilon>, None, h, (Bool (hd stk \<noteq> Null \<and> P \<turnstile> the (typeof\<^bsub>h\<^esub> (hd stk)) \<le> T) # tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)"
  "exec_instr (Invoke M n) P t h stk loc C0 M0 pc frs =
   (let r = stk ! n
    in (if r = Null then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
        else (let ps = rev (take n stk);
                  a = the_Addr r;
                  T = the (typeof_addr h a);
                  C = the (class_type_of T);
                  (D,M',Ts,meth)= method P C M
         in case meth of 
               Native \<Rightarrow>
                      do {
                        (ta, va, h') \<leftarrow> red_external_aggr P t a M ps h;
                        Cset.single (extTA2JVM P ta, extRet2JVM n h' stk loc C0 M0 pc frs va)
                      }
            | \<lfloor>(mxs,mxl\<^isub>0,ins,xt)\<rfloor> \<Rightarrow>
              let f' = ([],[r]@ps@(replicate mxl\<^isub>0 undefined_value),D,M,0)
              in Cset.single (\<epsilon>, None, h, f' # (stk, loc, C0, M0, pc) # frs))))"
  "exec_instr Return P t h stk\<^isub>0 loc\<^isub>0 C\<^isub>0 M\<^isub>0 pc frs =
   Cset.single 
      (\<epsilon>, (if frs=[] then (None, h, []) 
          else 
            let v = hd stk\<^isub>0; 
                (stk,loc,C,m,pc) = hd frs;
                 n = length (fst (snd (method P C\<^isub>0 M\<^isub>0)))
            in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs)) )"
  "exec_instr Pop P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = Cset.single (\<epsilon>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs))"
  "exec_instr Dup P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = Cset.single (\<epsilon>, (None, h, (hd stk # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs))"
  "exec_instr Swap P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = Cset.single (\<epsilon>, (None, h, (hd (tl stk) # hd stk # tl (tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )"
  "exec_instr (BinOpInstr bop) P t h stk loc C0 M0 pc frs =
   Cset.single 
     (\<epsilon>, 
      case the (execute.binop bop (hd (tl stk)) (hd stk)) of
        Inl v \<Rightarrow> (None, h, (v # tl (tl stk), loc, C0, M0, pc + 1) # frs)
      | Inr a \<Rightarrow> (Some a, h, (stk, loc, C0, M0, pc) # frs))"
  "exec_instr (IfFalse i) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   Cset.single
     (\<epsilon>, (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
          in (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc')#frs)) )"
  "exec_instr (Goto i) P t h stk loc C\<^isub>0 M\<^isub>0 pc frs = Cset.single (\<epsilon>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, nat(int pc+i))#frs))"
  "exec_instr ThrowExc P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
   Cset.single 
     (\<epsilon>, (let xp' = if hd stk = Null then \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr(hd stk)\<rfloor>
          in (xp', h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs)) )"
 "exec_instr MEnter P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  Cset.single
    (let v = hd stk
     in if v = Null
        then (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
        else (\<lbrace>Lock\<rightarrow>the_Addr v, SyncLock (the_Addr v)\<rbrace>, None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs))"
 "exec_instr MExit P t h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (let v = hd stk
   in if v = Null
      then Cset.single (\<epsilon>, \<lfloor>execute.addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs)
      else Cset.set [(\<lbrace>Unlock\<rightarrow>the_Addr v, SyncUnlock (the_Addr v)\<rbrace>, None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs),
                     (\<lbrace>UnlockFail\<rightarrow>the_Addr v\<rbrace>, \<lfloor>execute.addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)])"
apply(simp_all add: JVM_heap_base.exec_instr.simps Cset.set_eq_iff)
apply(auto 4 3 intro: rev_bexI)
apply(auto split: extCallRet.splits)
done

definition exec :: "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state \<Rightarrow> ('addr, 'thread_id, 'heap) jvm_ta_state Cset.set"
where
  "exec P t s = Cset.Set (execute.exec P t s)"

lemma member_exec: "member (exec P t s) = execute.exec P t s"
by(simp add: exec_def)

lemma member_exec_mem: "member (exec P t s) tas' \<longleftrightarrow> tas' \<in> execute.exec P t s"
by(simp add: member_exec mem_def)

lemma exec_code:
  "exec P t (xcp, h, []) = Cset.empty"
  "exec P t (None, h, (stk, loc, C, M, pc) # frs) = exec_instr (instrs_of P C M ! pc) P t h stk loc C M pc frs"
  "exec P t (\<lfloor>a\<rfloor>, h, fr # frs) = Cset.single (\<epsilon>, execute.exception_step P a h fr frs)"
by(simp_all add: Cset.set_eq_iff member_exec)

definition exec_1 ::
  "'addr jvm_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'heap) jvm_state
   \<Rightarrow> (('addr, 'thread_id, 'heap) jvm_thread_action \<times> ('addr, 'heap) jvm_state) Predicate.pred"
where "exec_1 P t \<sigma> = pred_of_cset (exec P t \<sigma>)"

lemma exec_1I: "execute.exec_1 P t \<sigma> ta \<sigma>' \<Longrightarrow> Predicate.eval (exec_1 P t \<sigma>) (ta, \<sigma>')"
by(erule execute.exec_1.cases)(simp add: exec_1_def member_exec_mem)

lemma exec_1E:
  assumes "Predicate.eval (exec_1 P t \<sigma>) (ta, \<sigma>')"
  obtains "execute.exec_1 P t \<sigma> ta \<sigma>'"
using assms
by(auto simp add: exec_1_def member_exec_mem intro: execute.exec_1.intros)

lemma exec_1_eq [simp]:
  "Predicate.eval (exec_1 P t \<sigma>) (ta, \<sigma>') \<longleftrightarrow> execute.exec_1 P t \<sigma> ta \<sigma>'"
by(auto intro: exec_1I elim: exec_1E)

lemma exec_1_eq':
  "Predicate.eval (exec_1 P t \<sigma>) = (\<lambda>(ta, \<sigma>'). execute.exec_1 P t \<sigma> ta \<sigma>')"
by(rule ext)(simp split: prod.split)

end

lemmas [code] = 
  JVM_heap_execute.exec_instr_code
  JVM_heap_base.exception_step.simps
  JVM_heap_execute.exec_code
  JVM_heap_execute.exec_1_def

end