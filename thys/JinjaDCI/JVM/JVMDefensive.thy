(*  Title:      JinjaDCI/JVM/JVMDefensive.thy
    Author:     Gerwin Klein, Susannah Mansky
    Copyright   GPL

    Based on the Jinja theory JVM/JVMDefensive.thy by Gerwin Klein
*)

section \<open> A Defensive JVM \<close>

theory JVMDefensive
imports JVMExec "../Common/Conform"
begin

text \<open>
  Extend the state space by one element indicating a type error (or
  other abnormal termination) \<close>
datatype 'a type_error = TypeError | Normal 'a

fun is_Addr :: "val \<Rightarrow> bool" where
  "is_Addr (Addr a) \<longleftrightarrow> True"
| "is_Addr v \<longleftrightarrow> False"

fun is_Intg :: "val \<Rightarrow> bool" where
  "is_Intg (Intg i) \<longleftrightarrow> True"
| "is_Intg v \<longleftrightarrow> False"

fun is_Bool :: "val \<Rightarrow> bool" where
  "is_Bool (Bool b) \<longleftrightarrow> True"
| "is_Bool v \<longleftrightarrow> False"

definition is_Ref :: "val \<Rightarrow> bool" where
  "is_Ref v \<longleftrightarrow> v = Null \<or> is_Addr v"

primrec check_instr :: "[instr, jvm_prog, heap, val list, val list, 
                  cname, mname, pc, frame list, sheap] \<Rightarrow> bool" where
  check_instr_Load:
    "check_instr (Load n) P h stk loc C M\<^sub>0 pc frs sh = 
    (n < length loc)"

| check_instr_Store:
    "check_instr (Store n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (0 < length stk \<and> n < length loc)"

| check_instr_Push:
    "check_instr (Push v) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (\<not>is_Addr v)"

| check_instr_New:
    "check_instr (New C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    is_class P C"

| check_instr_Getfield:
    "check_instr (Getfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (0 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F,NonStatic:T in C') \<and> 
    (let (C', b, T) = field P C F; ref = hd stk in 
      C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
        h (the_Addr ref) \<noteq> None \<and> 
        (let (D,vs) = the (h (the_Addr ref)) in 
          P \<turnstile> D \<preceq>\<^sup>* C \<and> vs (F,C) \<noteq> None \<and> P,h \<turnstile> the (vs (F,C)) :\<le> T))))" 

| check_instr_Getstatic:
    "check_instr (Getstatic C F D) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    ((\<exists>T. P \<turnstile> C sees F,Static:T in D) \<and> 
    (let (C', b, T) = field P C F in 
      C' = D \<and> (sh D \<noteq> None \<longrightarrow>
        (let (sfs,i) = the (sh D) in 
          sfs F \<noteq> None \<and> P,h \<turnstile> the (sfs F) :\<le> T))))" 

| check_instr_Putfield:
    "check_instr (Putfield F C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (1 < length stk \<and> (\<exists>C' T. P \<turnstile> C sees F,NonStatic:T in C') \<and>
    (let (C', b, T) = field P C F; v = hd stk; ref = hd (tl stk) in 
      C' = C \<and> is_Ref ref \<and> (ref \<noteq> Null \<longrightarrow> 
        h (the_Addr ref) \<noteq> None \<and> 
        (let D = fst (the (h (the_Addr ref))) in 
          P \<turnstile> D \<preceq>\<^sup>* C \<and> P,h \<turnstile> v :\<le> T))))" 

| check_instr_Putstatic:
    "check_instr (Putstatic C F D) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (0 < length stk \<and> (\<exists>T. P \<turnstile> C sees F,Static:T in D) \<and>
    (let (C', b, T) = field P C F; v = hd stk in 
      C' = D \<and> P,h \<turnstile> v :\<le> T))" 

| check_instr_Checkcast:
    "check_instr (Checkcast C) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (0 < length stk \<and> is_class P C \<and> is_Ref (hd stk))"

| check_instr_Invoke:
    "check_instr (Invoke M n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (n < length stk \<and> is_Ref (stk!n) \<and>  
    (stk!n \<noteq> Null \<longrightarrow> 
      (let a = the_Addr (stk!n); 
           C = cname_of h a;
           Ts = fst (snd (snd (method P C M)))
      in h a \<noteq> None \<and> P \<turnstile> C has M,NonStatic \<and> 
         P,h \<turnstile> rev (take n stk) [:\<le>] Ts)))"

| check_instr_Invokestatic:
    "check_instr (Invokestatic C M n) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (n \<le> length stk \<and>
      (let Ts = fst (snd (snd (method P C M)))
      in P \<turnstile> C has M,Static \<and> 
         P,h \<turnstile> rev (take n stk) [:\<le>] Ts))"
 
| check_instr_Return:
    "check_instr Return P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (case (M\<^sub>0 = clinit) of False \<Rightarrow> (0 < length stk \<and> ((0 < length frs) \<longrightarrow> 
                                      (\<exists>b. P \<turnstile> C\<^sub>0 has M\<^sub>0,b) \<and>    
                                      (let v = hd stk; 
                                           T = fst (snd (snd (snd (method P C\<^sub>0 M\<^sub>0))))
                                       in P,h \<turnstile> v :\<le> T)))
                        | True \<Rightarrow> P \<turnstile> C\<^sub>0 has M\<^sub>0,Static)"
 
| check_instr_Pop:
    "check_instr Pop P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = 
    (0 < length stk)"

| check_instr_IAdd:
    "check_instr IAdd P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (1 < length stk \<and> is_Intg (hd stk) \<and> is_Intg (hd (tl stk)))"

| check_instr_IfFalse:
    "check_instr (IfFalse b) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (0 < length stk \<and> is_Bool (hd stk) \<and> 0 \<le> int pc+b)"

| check_instr_CmpEq:
    "check_instr CmpEq P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (1 < length stk)"

| check_instr_Goto:
    "check_instr (Goto b) P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (0 \<le> int pc+b)"

| check_instr_Throw:
    "check_instr Throw P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
    (0 < length stk \<and> is_Ref (hd stk))"

definition check :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> bool" where
  "check P \<sigma> = (let (xcpt, h, frs, sh) = \<sigma> in
               (case frs of [] \<Rightarrow> True | (stk,loc,C,M,pc,ics)#frs' \<Rightarrow> 
                \<exists>b. P \<turnstile> C has M, b \<and>
                (let (C',b,Ts,T,mxs,mxl\<^sub>0,ins,xt) = method P C M; i = ins!pc in
                 pc < size ins \<and> size stk \<le> mxs \<and>
                 check_instr i P h stk loc C M pc frs' sh)))"


definition exec_d :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state option type_error" where
  "exec_d P \<sigma> = (if check P \<sigma> then Normal (exec (P, \<sigma>)) else TypeError)"


inductive_set
  exec_1_d :: "jvm_prog \<Rightarrow> (jvm_state type_error \<times> jvm_state type_error) set" 
  and exec_1_d' :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
                   (\<open>_ \<turnstile> _ -jvmd\<rightarrow>\<^sub>1 _\<close> [61,61,61]60)
  for P :: jvm_prog
where
  "P \<turnstile> \<sigma> -jvmd\<rightarrow>\<^sub>1 \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> exec_1_d P"
| exec_1_d_ErrorI: "exec_d P \<sigma> = TypeError \<Longrightarrow> P \<turnstile> Normal \<sigma> -jvmd\<rightarrow>\<^sub>1 TypeError"
| exec_1_d_NormalI: "exec_d P \<sigma> = Normal (Some \<sigma>') \<Longrightarrow> P \<turnstile> Normal \<sigma> -jvmd\<rightarrow>\<^sub>1 Normal \<sigma>'"

\<comment> \<open>reflexive transitive closure:\<close>
definition exec_all_d :: "jvm_prog \<Rightarrow> jvm_state type_error \<Rightarrow> jvm_state type_error \<Rightarrow> bool" 
    (\<open>_ \<turnstile> _ -jvmd\<rightarrow> _\<close> [61,61,61]60) where
  exec_all_d_def1: "P \<turnstile> \<sigma> -jvmd\<rightarrow> \<sigma>' \<longleftrightarrow> (\<sigma>,\<sigma>') \<in> (exec_1_d P)\<^sup>*"

notation (ASCII)
  "exec_all_d"  (\<open>_ |- _ -jvmd-> _\<close> [61,61,61]60)

lemma exec_1_d_eq:
  "exec_1_d P = {(s,t). \<exists>\<sigma>. s = Normal \<sigma> \<and> t = TypeError \<and> exec_d P \<sigma> = TypeError} \<union> 
                {(s,t). \<exists>\<sigma> \<sigma>'. s = Normal \<sigma> \<and> t = Normal \<sigma>' \<and> exec_d P \<sigma> = Normal (Some \<sigma>')}"
by (auto elim!: exec_1_d.cases intro!: exec_1_d.intros)


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


lemma defensive_imp_aggressive:
  "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>') \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
(*<*)
proof -
  have "\<And>x y. P \<turnstile> x -jvmd\<rightarrow> y \<Longrightarrow> \<forall>\<sigma> \<sigma>'. x = Normal \<sigma> \<longrightarrow> y = Normal \<sigma>' \<longrightarrow>  P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
  proof -
    fix x y assume xy: "P \<turnstile> x -jvmd\<rightarrow> y"
    then have "(x, y) \<in> (exec_1_d P)\<^sup>*" by (unfold exec_all_d_def1)
    then show "\<forall>\<sigma> \<sigma>'. x = Normal \<sigma> \<longrightarrow> y = Normal \<sigma>' \<longrightarrow>  P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
    proof(induct rule: rtrancl_induct)
      case base
      then show ?case by (simp add: exec_all_def)
    next
      case (step y' z')
      show ?case proof(induct rule: exec_1_d.cases[OF step.hyps(2)])
        case (2 \<sigma> \<sigma>')
        then have "(\<sigma>, \<sigma>') \<in> {(\<sigma>, \<sigma>'). exec (P, \<sigma>) = \<lfloor>\<sigma>'\<rfloor>}\<^sup>*" using step
          by(fastforce simp: exec_d_def split: type_error.splits if_split_asm)
        then show ?case using step 2 by (auto simp: exec_all_def)
      qed simp
    qed
  qed
  moreover
  assume "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>')" 
  ultimately
  show "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'" by blast
qed
(*>*)

end
