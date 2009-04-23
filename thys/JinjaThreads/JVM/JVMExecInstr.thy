(*  Title:      JinjaThreads/JVM/JVMExecInstr.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler
*)

header {* \isaheader{JVM Instruction Semantics} *}

theory JVMExecInstr
imports JVMInstructions JVMState "../Common/ExternalCall"
begin

primrec extRet2JVM :: "nat \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> pc \<Rightarrow> frame list \<Rightarrow> (val + addr) \<Rightarrow> jvm_state"
where
  "extRet2JVM n h stk loc C M pc frs (Inl v) = (None, h, (v # drop (Suc n) stk, loc, C, M, pc + 1) # frs)"
| "extRet2JVM n h stk loc C M pc frs (Inr a) = (\<lfloor>a\<rfloor>, h, (stk, loc, C, M, pc) # frs)"

lemma eq_extRet2JVM_conv [simp]:
  "(xcp, h', frs') = extRet2JVM n h stk loc C M pc frs va \<longleftrightarrow> 
   h' = h \<and> (case va of Inl v \<Rightarrow> xcp = None \<and> frs' = (v # drop (Suc n) stk, loc, C, M, pc + 1) # frs
                      | Inr a \<Rightarrow> xcp = \<lfloor>a\<rfloor> \<and> frs' = (stk, loc, C, M, pc) # frs)"
by(cases va) auto

definition extNTA2JVM :: "jvm_prog \<Rightarrow> (cname \<times> mname \<times> addr) \<Rightarrow> jvm_thread_state"
where "extNTA2JVM P \<equiv> (\<lambda>(C, M, a). let (D,M',Ts,mxs,mxl0,ins,xt) = method P C M
                                   in (None, [([],Addr a # replicate mxl0 arbitrary, D, M, 0)]))"

abbreviation extTA2JVM :: "jvm_prog \<Rightarrow> external_thread_action \<Rightarrow> jvm_thread_action"
where "extTA2JVM P \<equiv> convert_extTA (extNTA2JVM P)"

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
                  | \<lfloor>a\<rfloor>  \<Rightarrow> (None, h(a \<mapsto> Arr T (replicate (nat si) (default_val T))), (Addr a # tl stk, loc, C0, M0, pc + 1) # frs)))) )]"

exec_instr_ALoad:
  "exec_instr ALoad P h stk loc C0 M0 pc frs =
   [(\<epsilon>, (let i = the_Intg (hd stk);
             va = hd (tl stk);
             (T, el) = the_arr (the (h (the_Addr va)))
         in if va = Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else if i < 0 \<or> int (length el) \<le> i then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else (None, h, (el ! nat i # tl (tl stk), loc, C0, M0, pc + 1) # frs)) )]"

exec_instr_AStore:
  "exec_instr AStore P h stk loc C0 M0 pc frs =
  [(\<epsilon>, (let ve = hd stk;
            vi = hd (tl stk);
            va = hd (tl (tl stk))
        in (if va = Null
            then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else (let i = the_Intg vi;
                      (T, el) = the_arr (the (h (the_Addr va)));
                      h' = h((the_Addr va) \<mapsto> Arr T (el[nat i := ve]))
                 in (if i < 0 \<or> int (length el) \<le> i
                     then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
                     else if cast_ok P T h ve
                          then (None, h', (tl (tl (tl stk)), loc, C0, M0, pc+1) # frs)
                          else (\<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>, h, (stk, loc, C0, M0, pc) # frs))))) )]"

exec_instr_ALength:
  "exec_instr ALength P h stk loc C0 M0 pc frs =
   [(\<epsilon>, (let va = hd stk
         in if va = Null
            then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C0, M0, pc) # frs)
            else let (T, elem) = the_arr (the (h (the_Addr va)))
                 in (None, h, (Intg (int (length elem)) # tl stk, loc, C0, M0, pc+1) # frs)))]"


 "exec_instr (Getfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let v      = hd stk;
            (D,fs) = the_obj(the(h(the_Addr v)))
        in if v=Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
           else (None, h, (the(fs(F,C))#(tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

 "exec_instr (Putfield F C) P h stk loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let v    = hd stk;
            r    = hd (tl stk);
            a    = the_Addr r;
            (D,fs) = the_obj (the (h a));
            h'  = h(a \<mapsto> (Obj D (fs((F,C) \<mapsto> v))))
        in if r=Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
           else (None, h', (tl (tl stk), loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

 "exec_instr (Checkcast T) P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (let v   = hd stk
        in if \<not> cast_ok P T h v then (\<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
           else (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"

exec_instr_Invoke:
 "exec_instr (Invoke M n) P h stk loc C0 M0 pc frs =
  (let ps = rev (take n stk);
       r = stk ! n;
       a = the_Addr r;
       T = the(typeof\<^bsub>h\<^esub> (Addr a));
       C = fst(the_obj(the(h a)));
       old_frs = (stk, loc, C0, M0, pc) # frs
   in (if r = Null then [(\<epsilon>, \<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, old_frs)]
       else if is_external_call P T M (length ps)
            then map (\<lambda>(ta, va, h). (extTA2JVM P ta, extRet2JVM n h stk loc C0 M0 pc frs va)) (red_external_list P a M ps h)
       else let (D,M',Ts,mxs,mxl\<^isub>0,ins,xt)= method P C M;
                f'  = ([],[r]@ps@(replicate mxl\<^isub>0 arbitrary),D,M,0)
            in [(\<epsilon>, None, h, f' # old_frs)]))"


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
       then (\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs))
       else (\<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>the_Addr v\<rbrace>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)) ]"

exec_instr_MExit:
 "exec_instr MExit P h stk loc C\<^isub>0 M\<^isub>0 pc frs =
  (let v = hd stk
   in if v = Null
      then [(\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs) )]
      else [(\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>the_Addr v\<rbrace>, (None, h, (tl stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)),
            (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>the_Addr v\<rbrace>, (\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)) ])"

lemma exec_instr_not_empty:
  "exec_instr I P h stk loc C0 M0 pc frs \<noteq> []"
proof(cases I)
  case (Invoke M n)
  moreover {
    assume "is_external_call P (the (typeof\<^bsub>h\<^esub> (Addr (the_Addr (stk ! n))))) M (length (rev (take n stk)))"
    hence "red_external_list P (the_Addr (stk ! n)) M (rev (take n stk)) h \<noteq> []"
      by(rule is_external_call_red_external_list_not_Nil) }
  ultimately show ?thesis by(clarsimp simp add: split_beta)
qed(auto simp add: split_beta)

lemma exec_instr_Store:
  "exec_instr (Store n) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs= 
   [(\<epsilon>, (None, h, (stk, loc[n:=v], C\<^isub>0, M\<^isub>0, pc+1)#frs) )]" 
  by simp

lemma exec_instr_NewArray:
  "exec_instr (NewArray T) P h (Intg si # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (if (si < 0) then (\<lfloor>addr_of_sys_xcpt NegativeArraySize\<rfloor>, h, (Intg si # stk, loc, C0, M0, pc) # frs)
         else (case new_Addr h of
                 None \<Rightarrow> (\<lfloor>addr_of_sys_xcpt OutOfMemory\<rfloor>, h, (Intg si # stk, loc, C0, M0, pc) # frs)
               | \<lfloor>a\<rfloor>  \<Rightarrow> (None, h(a \<mapsto> Arr T (replicate (nat si) (default_val T))), (Addr a # stk, loc, C0, M0, pc + 1) # frs))) )]"
  by simp

lemma exec_instr_ALoad:
  "exec_instr ALoad P h (Intg i # va # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (let (T, el) = the_arr (the (h (the_Addr va)))
         in if va = Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (Intg i # va # stk, loc, C0, M0, pc) # frs)
            else if i < 0 \<or> int (length el) \<le> i
                 then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (Intg i # va # stk, loc, C0, M0, pc) # frs)
            else (None, h, (el ! nat i # stk, loc, C0, M0, pc + 1) # frs)) )]"
  by(simp add: split_beta)

lemma exec_instr_AStore:
  "exec_instr AStore P h (ve # Intg i # va # stk) loc C0 M0 pc frs =
   [(\<epsilon>, (if va = Null
         then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (ve # Intg i # va # stk, loc, C0, M0, pc) # frs)
         else (let (T, el) = the_arr (the (h (the_Addr va)));
                   h' = h((the_Addr va) \<mapsto> Arr T (el[nat i := ve]))
               in (if i < 0 \<or> int (length el) \<le> i
                   then (\<lfloor>addr_of_sys_xcpt ArrayIndexOutOfBounds\<rfloor>, h, (ve # Intg i # va # stk, loc, C0, M0, pc) # frs)
                   else if cast_ok P T h ve
                        then (None, h', (stk, loc, C0, M0, pc+1) # frs)
                        else (\<lfloor>addr_of_sys_xcpt ArrayStore\<rfloor>, h, (ve # Intg i # va # stk, loc, C0, M0, pc) # frs)))) )]"
  by(simp add: exec_instr_AStore split_beta)

lemma exec_instr_ALength:
  "exec_instr ALength P h (va # stk) loc C0 M0 pc frs =
   [(\<epsilon>, if va = Null
        then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (va # stk, loc, C0, M0, pc) # frs)
        else let (T, elem) = the_arr (the (h (the_Addr va)))
             in (None, h, (Intg (int (length elem)) # stk, loc, C0, M0, pc+1) # frs))]"
  by(simp only: exec_instr_ALength Let_def hd.simps tl.simps)


lemma exec_instr_Getfield:
 "exec_instr (Getfield F C) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, let (D,fs) = the_obj(the(h(the_Addr v)))
       in if v=Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
          else (None, h, (the(fs(F,C))#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs))]"
  by(simp add: split_beta)

lemma exec_instr_Putfield:
 "exec_instr (Putfield F C) P h (v#r#stk) loc C\<^isub>0 M\<^isub>0 pc frs = 
  [(\<epsilon>, (let  a    = the_Addr r;
            (D,fs) = the_obj(the (h a));
            h'  = if r=Null then h else h(a \<mapsto> (Obj D (fs((F,C) \<mapsto> v))))
        in if r=Null then (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (v # r # stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)
           else (None, h', (stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)))]"
  by(simp add: split_beta)

lemma exec_instr_Checkcast:
 "exec_instr (Checkcast T) P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  [(\<epsilon>, (if \<not> cast_ok P T h v then (\<lfloor>addr_of_sys_xcpt ClassCast\<rfloor>, h, (v # stk, loc,  C\<^isub>0, M\<^isub>0, pc) # frs)
        else (None, h, (v#stk, loc, C\<^isub>0, M\<^isub>0, pc+1)#frs)) )]"
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
    then (\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs))
    else (\<epsilon>\<lbrace>\<^bsub>l\<^esub>Lock\<rightarrow>the_Addr v\<rbrace>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)) ]"
  by simp

lemma exec_instr_MExit:
 "exec_instr MExit P h (v#stk) loc C\<^isub>0 M\<^isub>0 pc frs =
  (if v = Null
  then [(\<epsilon>, (\<lfloor>addr_of_sys_xcpt NullPointer\<rfloor>, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc)#frs) )]
  else [(\<epsilon>\<lbrace>\<^bsub>l\<^esub>Unlock\<rightarrow>the_Addr v\<rbrace>, (None, h, (stk, loc, C\<^isub>0, M\<^isub>0, pc + 1) # frs)),
        (\<epsilon>\<lbrace>\<^bsub>l\<^esub>UnlockFail\<rightarrow>the_Addr v\<rbrace>, (\<lfloor>addr_of_sys_xcpt IllegalMonitorState\<rfloor>, h, (v # stk, loc, C\<^isub>0, M\<^isub>0, pc) # frs)) ])"
  by simp

lemma exec_instr_xcp_unchanged:
  "(ta, \<lfloor>xcp\<rfloor>, h', frs') \<in> set (exec_instr (ins ! pc) P h stk loc C M pc frs)
  \<Longrightarrow> h' = h \<and> frs' = (stk, loc, C, M, pc) # frs"
apply(cases "ins ! pc")
apply(simp_all split: split_if_asm add: split_beta)
apply(auto split: sum.split_asm dest: red_external_list_xcp_heap_unchanged)
done

end
