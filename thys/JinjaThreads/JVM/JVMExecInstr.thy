(*  Title:      JinjaThreads/JVM/JVMExecInstr.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{JVM Instruction Semantics} *}

theory JVMExecInstr
imports JVMInstructions JVMState "../Common/Exceptions"
begin

consts
  exec_instr :: "instr \<Rightarrow> jvm_prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> frame list \<Rightarrow>
    ((addr,thread_id,jvm_thread_state,heap,addr) thread_action \<times> jvm_state) list"

primrec
exec_instr_Load:
 "exec_instr (Load n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
      [(\<epsilon>, (None, h, ((loc ! n) # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"

 "exec_instr (Store n) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
      [(\<epsilon>, (None, h, (tl stk, loc[n:=hd stk], C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"

exec_instr_Push:
 "exec_instr (Push v) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
      [(\<epsilon>, (None, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"

exec_instr_New:
 "exec_instr (New C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (case new_Addr h of
          None \<Rightarrow>   (Some (addr_of_sys_xcpt OutOfMemory), h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs)
        | Some a \<Rightarrow> (None, h(a\<mapsto>blank P C), (Addr a#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

exec_instr_NewArray:
  "exec_instr (NewArray T) P h stk loc C0 M0 pc frs =
  [(\<epsilon>, (let si = the_Intg (hd stk)
        in (if (si < 0)
            then (\<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else (case new_Addr h of
                    None \<Rightarrow> (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
                  | \<lfloor>a\<rfloor>  \<Rightarrow> (None, h(a \<mapsto> Arr T si (\<lambda>i. default_val T)), (Addr a # tl stk, loc, C0, M0, pc + 1) # frs)))) )]"

exec_instr_ALoad:
  "exec_instr ALoad P h stk loc C0 M0 pc frs =
   [(\<epsilon>, (let i = the_Intg (hd stk);
             va = hd (tl stk);
             (T, si, el) = the_arr (the (h (the_Addr va)));
             xp = if va = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> 
                  else if i < 0 \<or> si \<le> i then \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>
                  else None
         in (xp, h, (el i # tl (tl stk), loc, C0, M0, pc + 1) # frs)) )]"

exec_instr_AStore:
  "exec_instr AStore P h stk loc C0 M0 pc frs =
  [(\<epsilon>, (let ve = hd stk;
            vi = hd (tl stk);
            va = hd (tl (tl stk))
        in (if va = Null
            then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else (let i = the_Intg vi;
                      (T, si, el) = the_arr (the (h (the_Addr va)));
                      h' = h((the_Addr va) \<mapsto> Arr T si (el(i := ve)))
                 in (if i < 0 \<or> si \<le> i
                     then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
                     else if cast_ok P T h ve
                          then (None, h', (tl (tl (tl stk)), loc, C0, M0, pc+1) # frs)
                          else (\<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>, h, (stk, loc, C0, M0, pc) # frs))))) )]"


 "exec_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let v      = hd stk;
            xp'    = if v=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
            (D,fs) = the_obj(the(h(the_Addr v)))
        in (xp', h, (the(fs(F,C))#(tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

 "exec_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let v    = hd stk;
            r    = hd (tl stk);
            xp'  = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
            a    = the_Addr r;
            (D,fs) = the_obj (the (h a));
            h'  = h(a \<mapsto> (Obj D (fs((F,C) \<mapsto> v))))
       in (xp', h', (tl (tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

 "exec_instr (Checkcast T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let v   = hd stk;
            xp' = if \<not>cast_ok P T h v then \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> else None
        in (xp', h, (stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"



exec_instr_Invoke:
 "exec_instr (Invoke M n) P h stk loc C0 M0 pc frs =
  (let ps = take n stk;
       r = stk ! n
   in (if r = Null
       then [(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)]
       else (let C = fst(the_obj(the(h(the_Addr r))))
             in (if P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M = start \<and> n = 0
                 then (let (D,M',Ts,mxs,mxl0,ins,xt) = method P C run;
                           stk' = Unit # tl stk
                       in [(\<epsilon>\<lbrace>\<^bsub>t\<^esub> ThreadExists (the_Addr r)\<rbrace>, \<lfloor>addr_of_sys_xcpt IllegalThreadState\<rfloor>, h, (stk', loc, C0, M0, pc) # frs), (\<epsilon>\<lbrace>\<^bsub>t\<^esub> NewThread (the_Addr r) (None, [([],r # replicate mxl0 arbitrary,D,run,0)]) h\<rbrace>, None, h, (stk', loc, C0, M0, pc+1) # frs)])
                 else if P \<turnstile> C \<preceq>\<^sup>* Thread \<and> M = join \<and> n = 0
                 then [(\<epsilon>\<lbrace>\<^bsub>c\<^esub> Join (the_Addr r)\<rbrace>, None, h, (Unit # tl stk, loc, C0, M0, pc + 1) # frs)]
                 else if M = wait \<and> n = 0
                 then (let stk' = Unit # tl stk;
                           a = the_Addr r
                       in [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Suspend a\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a, ReleaseAcquire\<rightarrow>a\<rbrace>, None, h, (stk', loc, C0, M0, pc + 1) # frs),
                           (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk', loc, C0, M0, pc) # frs) ])
                 else if M = notify \<and> n = 0
                 then (let stk' = Unit # tl stk;
                           a = the_Addr r
                       in [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> Notify a\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, None, h, (stk', loc, C0, M0, pc + 1) # frs),
                           (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk', loc, C0, M0, pc) # frs) ])
                 else if M = notifyAll \<and> n = 0
                 then (let stk' = Unit # tl stk;
                           a = the_Addr r
                       in [(\<epsilon>\<lbrace>\<^bsub>w\<^esub> NotifyAll a\<rbrace>\<lbrace>\<^bsub>l\<^esub> Unlock\<rightarrow>a, Lock\<rightarrow>a\<rbrace>, None, h, (stk', loc, C0, M0, pc + 1) # frs),
                           (\<epsilon>\<lbrace>\<^bsub>l\<^esub> UnlockFail\<rightarrow>a \<rbrace>, \<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk', loc, C0, M0, pc) # frs) ])
                 else [(\<epsilon>, (let xp' = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
                               (D,M',Ts,mxs,mxl\<^isub>0,ins,xt)= method P C M;
                               f'  = ([],[r]@(rev ps)@(replicate mxl\<^isub>0 arbitrary),D,M,0)
                            in (xp', h, f'#(stk, loc, C0, M0, pc)#frs)) )]))))"

 "exec_instr Return P h stk\<^isub>0 loc\<^isub>0 C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (if frs=[] then (None, h, []) else 
       let v = hd stk\<^isub>0; 
           (stk,loc,C,m,pc) = hd frs;
           n = length (fst (snd (method P C\<^isub>0 M\<^isub>0)))
       in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs)) )]"

 "exec_instr Pop P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
      [(\<epsilon>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"

 "exec_instr IAdd P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let i\<^isub>2 = the_Intg (hd stk);
            i\<^isub>1 = the_Intg (hd (tl stk))
        in (None, h, (Intg (i\<^isub>1+i\<^isub>2)#(tl (tl stk)), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

 "exec_instr (IfFalse i) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let pc' = if hd stk = Bool False then nat(int pc+i) else pc+1
        in (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc')#frs)) )]"

 "exec_instr CmpEq P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let v\<^isub>2 = hd stk;
            v\<^isub>1 = hd (tl stk)
        in (None, h, (Bool (v\<^isub>1=v\<^isub>2) # tl (tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

exec_instr_Goto:
 "exec_instr (Goto i) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
      [(\<epsilon>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, nat(int pc+i))#frs) )]"

 "exec_instr Throw P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let xp' = if hd stk = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr(hd stk)\<rfloor>
        in (xp', h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs)) )]"

exec_instr_MEnter:
 "exec_instr MEnter P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [ let v = hd stk
    in if v = Null
       then (\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs))
       else (\<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>the_Addr v\<rbrace>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)) ]"

exec_instr_MExit:
 "exec_instr MExit P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (let v = hd stk
   in if v = Null
      then [(\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs) )]
      else [(\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>the_Addr v\<rbrace>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)),
            (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>the_Addr v\<rbrace>, (\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)) ])"

lemma exec_instr_not_empty:
  "exec_instr I P h stk loc C0 M0 pc frs \<noteq> []"
by(cases I, auto simp add: split_beta)


lemma exec_instr_Store:
  "exec_instr (Store n) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs= 
   [(\<epsilon>, (None, h, (stk, loc[n:=v], C\<^isub>0, M\<^isub>0, pc+1)#frs) )]" 
  by simp

lemma exec_instr_NewArray:
  "exec_instr (NewArray T) P h (Intg si # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (if (si < 0) then (\<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, (Intg si # stk, loc, C0, M0, pc) # frs)
         else (case new_Addr h of
                 None \<Rightarrow> (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (Intg si # stk, loc, C0, M0, pc) # frs)
               | \<lfloor>a\<rfloor>  \<Rightarrow> (None, h(a \<mapsto> Arr T si (\<lambda>i. default_val T)), (Addr a # stk, loc, C0, M0, pc + 1) # frs))) )]"
  by simp

lemma exec_instr_ALoad:
  "exec_instr ALoad P h (Intg i # va # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (let (T, si, el) = the_arr (the (h (the_Addr va)));
             xp = if va = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> 
                  else if i < 0 \<or> si \<le> i then \<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>
                  else None
        in (xp, h, (el i # stk, loc, C0, M0, pc + 1) # frs)) )]"
  by simp

lemma exec_instr_AStore:
  "exec_instr AStore P h (ve # vi # va # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (if va = Null
         then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (ve # vi # va # stk, loc, C0, M0, pc) # frs)
         else (let i = the_Intg vi;
                   (T, si, el) = the_arr (the (h (the_Addr va)));
                   h' = h((the_Addr va) \<mapsto> Arr T si (el(i := ve)))
               in (if i < 0 \<or> si \<le> i
                   then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (ve # vi # va # stk, loc, C0, M0, pc) # frs)
                   else if cast_ok P T h ve
                        then (None, h', (stk, loc, C0, M0, pc+1) # frs)
                        else (\<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>, h, (ve # vi # va # stk, loc, C0, M0, pc) # frs)))) )]"
  by(simp only: exec_instr_AStore Let_def hd.simps tl.simps)

lemma exec_instr_Getfield:
 "exec_instr (Getfield F C) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let xp'    = if v=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
            (D,fs) = the_obj(the(h(the_Addr v)))
        in (xp', h, (the(fs(F,C))#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"
  by simp

lemma exec_instr_Putfield:
 "exec_instr (Putfield F C) P h (v#r#stk) loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let xp'  = if r=Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else None;
            a    = the_Addr r;
            (D,fs) = the_obj(the (h a));
            h'  = h(a \<mapsto> (Obj D (fs((F,C) \<mapsto> v))))
        in (xp', h', (stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"
  by simp

lemma exec_instr_Checkcast:
 "exec_instr (Checkcast T) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let xp' = if \<not>cast_ok P T h v then \<lfloor>addr_of_sys_xcpt ClassCast\<rfloor> else None
        in (xp', h, (v#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"
  by simp

lemma exec_instr_Return:
 "exec_instr Return P h (v#stk\<^isub>0) loc\<^isub>0 C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (if frs=[] then (None, h, []) else 
       let (stk,loc,C,m,pc) = hd frs;
            n = length (fst (snd (method P C\<^isub>0 M\<^isub>0)))
       in (None, h, (v#(drop (n+1) stk),loc,C,m,pc+1)#tl frs)) )]"
  by simp

lemma exec_instr_IPop:
 "exec_instr Pop P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs = 
      [(\<epsilon>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"
  by simp

lemma exec_instr_IAdd:
 "exec_instr IAdd P h (Intg i\<^isub>2 # Intg i\<^isub>1 # stk) loc C\<^isub>0 M\<^isub>0 pc frs =
      [(\<epsilon>, (None, h, (Intg (i\<^isub>1+i\<^isub>2)#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"
  by simp

lemma exec_instr_IfFalse:
 "exec_instr (IfFalse i) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let pc' = if v = Bool False then nat(int pc+i) else pc+1
        in (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc')#frs)) )]"
  by simp

lemma exec_instr_CmpEq:
 "exec_instr CmpEq P h (v\<^isub>2#v\<^isub>1#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (None, h, (Bool (v\<^isub>1=v\<^isub>2) # stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs) )]"
  by simp

lemma exec_instr_Throw:
 "exec_instr Throw P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let xp' = if v = Null then \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor> else \<lfloor>the_Addr v\<rfloor>
        in (xp', h, (v#stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs)) )]"
  by simp

lemma exec_instr_MEnter:
 "exec_instr MEnter P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [ if v = Null
    then (\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs))
    else (\<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>the_Addr v\<rbrace>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)) ]"
  by simp

lemma exec_instr_MExit:
 "exec_instr MExit P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  (if v = Null
  then [(\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs) )]
  else [(\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>the_Addr v\<rbrace>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)),
        (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>the_Addr v\<rbrace>, (\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)) ])"
  by simp

end
