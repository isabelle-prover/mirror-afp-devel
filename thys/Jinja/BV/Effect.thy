(*  Title:      HOL/MicroJava/BV/Effect.thy
    ID:         $Id: Effect.thy,v 1.2 2006-04-30 09:25:21 lsf37 Exp $
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Effect of Instructions on the State Type} *}

theory Effect
imports JVM_SemiType "../JVM/JVMExceptions"
begin

-- FIXME
locale prog =
  fixes P :: "'a prog"

locale jvm_method = prog +
  fixes mxs :: nat  
  fixes mxl\<^isub>0 :: nat   
  fixes Ts :: "ty list" 
  fixes T\<^isub>r :: ty
  fixes "is" :: "instr list" 
  fixes xt :: ex_table

  fixes mxl :: nat
  defines mxl_def: "mxl \<equiv> 1+size Ts+mxl\<^isub>0"

text {* Program counter of successor instructions: *}
consts
  succs :: "instr \<Rightarrow> ty\<^isub>i \<Rightarrow> pc \<Rightarrow> pc list"
primrec 
  "succs (Load idx) \<tau> pc     = [pc+1]"
  "succs (Store idx) \<tau> pc    = [pc+1]"
  "succs (Push v) \<tau> pc       = [pc+1]"
  "succs (Getfield F C) \<tau> pc = [pc+1]"
  "succs (Putfield F C) \<tau> pc = [pc+1]"
  "succs (New C) \<tau> pc        = [pc+1]"
  "succs (Checkcast C) \<tau> pc  = [pc+1]"
  "succs Pop \<tau> pc            = [pc+1]"
  "succs IAdd \<tau> pc           = [pc+1]"
  "succs CmpEq \<tau> pc          = [pc+1]"
succs_IfFalse:
  "succs (IfFalse b) \<tau> pc    = [pc+1, nat (int pc + b)]"
succs_Goto:
  "succs (Goto b) \<tau> pc       = [nat (int pc + b)]"
succs_Return:
  "succs Return \<tau> pc         = []"  
succs_Invoke:
  "succs (Invoke M n) \<tau> pc   = (if (fst \<tau>)!n = NT then [] else [pc+1])"
succs_Throw:
  "succs Throw \<tau> pc          = []"

text "Effect of instruction on the state type:"

consts the_class:: "ty \<Rightarrow> cname"
recdef the_class "{}"
"the_class(Class C) = C"

consts 
eff\<^isub>i :: "instr \<times> 'm prog \<times> ty\<^isub>i \<Rightarrow> ty\<^isub>i"

recdef eff\<^isub>i "{}"
eff\<^isub>i_Load:
"eff\<^isub>i (Load n,  P, (ST, LT))          = (ok_val (LT ! n) # ST, LT)"
eff\<^isub>i_Store:
"eff\<^isub>i (Store n, P, (T#ST, LT))        = (ST, LT[n:= OK T])"
eff\<^isub>i_Push:
"eff\<^isub>i (Push v, P, (ST, LT))             = (the (typeof v) # ST, LT)"
eff\<^isub>i_Getfield:
"eff\<^isub>i (Getfield F C, P, (T#ST, LT))    = (snd (field P C F) # ST, LT)"
eff\<^isub>i_Putfield:
"eff\<^isub>i (Putfield F C, P, (T\<^isub>1#T\<^isub>2#ST, LT)) = (ST,LT)"
eff\<^isub>i_New:
"eff\<^isub>i (New C, P, (ST,LT))               = (Class C # ST, LT)"
eff\<^isub>i_Checkcast:
"eff\<^isub>i (Checkcast C, P, (T#ST,LT))       = (Class C # ST,LT)"
eff\<^isub>i_Pop:
"eff\<^isub>i (Pop, P, (T#ST,LT))               = (ST,LT)"
eff\<^isub>i_IAdd:
"eff\<^isub>i (IAdd, P,(T\<^isub>1#T\<^isub>2#ST,LT))           = (Integer#ST,LT)"
eff\<^isub>i_CmpEq:
"eff\<^isub>i (CmpEq, P, (T\<^isub>1#T\<^isub>2#ST,LT))         = (Boolean#ST,LT)"
eff\<^isub>i_IfFalse:
"eff\<^isub>i (IfFalse b, P, (T\<^isub>1#ST,LT))        = (ST,LT)"
eff\<^isub>i_Invoke:
"eff\<^isub>i (Invoke M n, P, (ST,LT))          =
  (let C = the_class (ST!n); (D,Ts,T\<^isub>r,b) = method P C M
   in (T\<^isub>r # drop (n+1) ST, LT))"
eff\<^isub>i_Goto:
"eff\<^isub>i (Goto n, P, s)                    = s"


consts
  is_relevant_class :: "instr \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" 
recdef is_relevant_class "{}"
rel_Getfield:
  "is_relevant_class (Getfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
rel_Putfield:
  "is_relevant_class (Putfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
rel_Checcast:
  "is_relevant_class (Checkcast D)  = (\<lambda>P C. P \<turnstile> ClassCast \<preceq>\<^sup>* C)" 
rel_New:
  "is_relevant_class (New D)        = (\<lambda>P C. P \<turnstile> OutOfMemory \<preceq>\<^sup>* C)" 
rel_Throw:
  "is_relevant_class Throw          = (\<lambda>P C. True)"
rel_Invoke:
  "is_relevant_class (Invoke M n)   = (\<lambda>P C. True)"
rel_default:
  "is_relevant_class i              = (\<lambda>P C. False)"

constdefs
  is_relevant_entry :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool" 
  "is_relevant_entry P i pc e \<equiv> let (f,t,C,h,d) = e in is_relevant_class i P C \<and> pc \<in> {f..<t}"

  relevant_entries :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ex_table" 
  "relevant_entries P i pc \<equiv> filter (is_relevant_entry P i pc)"

  xcpt_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ty\<^isub>i 
               \<Rightarrow> ex_table \<Rightarrow> (pc \<times> ty\<^isub>i') list"                               
  "xcpt_eff i P pc \<tau> et \<equiv> let (ST,LT) = \<tau> in 
  map (\<lambda>(f,t,C,h,d). (h, Some (Class C#drop (size ST - d) ST, LT))) (relevant_entries P i pc et)"

  norm_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty\<^isub>i \<Rightarrow> (pc \<times> ty\<^isub>i') list"
  "norm_eff i P pc \<tau> \<equiv> map (\<lambda>pc'. (pc',Some (eff\<^isub>i (i,P,\<tau>)))) (succs i \<tau> pc)"

  eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i' \<Rightarrow> (pc \<times> ty\<^isub>i') list"
  "eff i P pc et t \<equiv>
  case t of           
    None \<Rightarrow> []          
  | Some \<tau> \<Rightarrow> (norm_eff i P pc \<tau>) @ (xcpt_eff i P pc \<tau> et)"


lemma eff_None:
  "eff i P pc xt None = []"
by (simp add: eff_def)

lemma eff_Some:
  "eff i P pc xt (Some \<tau>) = norm_eff i P pc \<tau> @ xcpt_eff i P pc \<tau> xt"
by (simp add: eff_def)

(* FIXME: getfield, \<exists>T D. P \<turnstile> C sees F:T in D \<and> .. *)

text "Conditions under which eff is applicable:"
consts
app\<^isub>i :: "instr \<times> 'm prog \<times> pc \<times> nat \<times> ty \<times> ty\<^isub>i \<Rightarrow> bool"

recdef app\<^isub>i "{}" 
app\<^isub>i_Load:
"app\<^isub>i (Load n, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
  (n < length LT \<and> LT ! n \<noteq> Err \<and> length ST < mxs)"
app\<^isub>i_Store:
"app\<^isub>i (Store n, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = 
  (n < length LT)"
app\<^isub>i_Push:
"app\<^isub>i (Push v, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
  (length ST < mxs \<and> typeof v \<noteq> None)"
app\<^isub>i_Getfield:
"app\<^isub>i (Getfield F C, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = 
  (\<exists>T\<^isub>f. P \<turnstile> C sees F:T\<^isub>f in C \<and> P \<turnstile> T \<le> Class C)"
app\<^isub>i_Putfield:
"app\<^isub>i (Putfield F C, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST, LT)) = 
  (\<exists>T\<^isub>f. P \<turnstile> C sees F:T\<^isub>f in C \<and> P \<turnstile> T\<^isub>2 \<le> (Class C) \<and> P \<turnstile> T\<^isub>1 \<le> T\<^isub>f)" 
app\<^isub>i_New:
"app\<^isub>i (New C, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
  (is_class P C \<and> length ST < mxs)"
app\<^isub>i_Checkcast:
"app\<^isub>i (Checkcast C, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
  (is_class P C \<and> is_refT T)"
app\<^isub>i_Pop:
"app\<^isub>i (Pop, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
  True"
app\<^isub>i_IAdd:
"app\<^isub>i (IAdd, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST,LT)) = (T\<^isub>1 = T\<^isub>2 \<and> T\<^isub>1 = Integer)"
app\<^isub>i_CmpEq:
"app\<^isub>i (CmpEq, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST,LT)) =
  (T\<^isub>1 = T\<^isub>2 \<or> is_refT T\<^isub>1 \<and> is_refT T\<^isub>2)"
app\<^isub>i_IfFalse:
"app\<^isub>i (IfFalse b, P, pc, mxs, T\<^isub>r, (Boolean#ST,LT)) = 
  (0 \<le> int pc + b)"
app\<^isub>i_Goto:
"app\<^isub>i (Goto b, P, pc, mxs, T\<^isub>r, s) = 
  (0 \<le> int pc + b)"
app\<^isub>i_Return:
"app\<^isub>i (Return, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
  (P \<turnstile> T \<le> T\<^isub>r)"
app\<^isub>i_Throw:
"app\<^isub>i (Throw, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
  is_refT T"
app\<^isub>i_Invoke:
"app\<^isub>i (Invoke M n, P, pc, mxs, T\<^isub>r, (ST,LT)) =
  (n < length ST \<and> 
  (ST!n \<noteq> NT \<longrightarrow>
    (\<exists>C D Ts T m. ST!n = Class C \<and> P \<turnstile> C sees M:Ts \<rightarrow> T = m in D \<and>
                  P \<turnstile> rev (take n ST) [\<le>] Ts)))"
  
app\<^isub>i_default:
"app\<^isub>i (i,P, pc,mxs,T\<^isub>r,s) = False"


constdefs
  xcpt_app :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i \<Rightarrow> bool"
  "xcpt_app i P pc mxs xt \<tau> \<equiv> \<forall>(f,t,C,h,d) \<in> set (relevant_entries P i pc xt). is_class P C \<and> d \<le> size (fst \<tau>) \<and> d < mxs"

  app :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> 
           ty\<^isub>i' \<Rightarrow> bool"                                          
  "app i P mxs T\<^isub>r pc mpc xt t \<equiv> case t of None \<Rightarrow> True | Some \<tau> \<Rightarrow> 
  app\<^isub>i (i,P,pc,mxs,T\<^isub>r,\<tau>) \<and> xcpt_app i P pc mxs xt \<tau> \<and> 
  (\<forall>(pc',\<tau>') \<in> set (eff i P pc xt t). pc' < mpc)"


lemma app_Some:
  "app i P mxs T\<^isub>r pc mpc xt (Some \<tau>) = 
  (app\<^isub>i (i,P,pc,mxs,T\<^isub>r,\<tau>) \<and> xcpt_app i P pc mxs xt \<tau> \<and> 
  (\<forall>(pc',s') \<in> set (eff i P pc xt (Some \<tau>)). pc' < mpc))"
by (simp add: app_def)

locale eff = jvm_method +
  fixes eff\<^isub>i and app\<^isub>i and eff and app 
  fixes norm_eff and xcpt_app and xcpt_eff

  fixes mpc
  defines "mpc \<equiv> size is"

  defines "eff\<^isub>i i \<tau> \<equiv> Effect.eff\<^isub>i (i,P,\<tau>)"
  notes eff\<^isub>i_simps [simp] = Effect.eff\<^isub>i.simps [where P = P, folded eff\<^isub>i_def]

  defines "app\<^isub>i i pc \<tau> \<equiv> Effect.app\<^isub>i (i, P, pc, mxs, T\<^isub>r, \<tau>)"
  notes app\<^isub>i_simps [simp] = Effect.app\<^isub>i.simps [where P=P and mxs=mxs and T\<^isub>r=T\<^isub>r, folded app\<^isub>i_def]

  defines "xcpt_eff i pc \<tau> \<equiv> Effect.xcpt_eff i P pc \<tau> xt"
  notes xcpt_eff = Effect.xcpt_eff_def [of _ P _ _ xt, folded xcpt_eff_def]

  defines "norm_eff i pc \<tau> \<equiv> Effect.norm_eff i P pc \<tau>"
  notes norm_eff = Effect.norm_eff_def [of _ P, folded norm_eff_def eff\<^isub>i_def]

  defines "eff i pc \<equiv> Effect.eff i P pc xt"
  notes eff = Effect.eff_def [of _ P  _ xt, folded eff_def norm_eff_def xcpt_eff_def]

  defines "xcpt_app i pc \<tau> \<equiv> Effect.xcpt_app i P pc mxs xt \<tau>"
  notes xcpt_app = Effect.xcpt_app_def [of _ P _ mxs xt, folded xcpt_app_def]

  defines "app i pc \<equiv> Effect.app i P mxs T\<^isub>r pc mpc xt"
  notes app = Effect.app_def [of _ P mxs T\<^isub>r _ mpc xt, folded app_def xcpt_app_def app\<^isub>i_def eff_def]


lemma length_cases2:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l ST LT. P (l#ST,LT)"
  shows "P s"
  by (cases s, cases "fst s", auto)


lemma length_cases3:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l ST LT. P (l#ST,LT)"
  shows "P s"
(*<*)
proof -
  obtain xs LT where "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil thus ?thesis by (simp!)
  next
    fix l xs' assume "xs = l#xs'"
    thus ?thesis by (simp!)
  qed
qed
(*>*)

lemma length_cases4:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l l' LT. P ([l,l'],LT)"
  assumes "\<And>l l' ST LT. P (l#l'#ST,LT)"
  shows "P s"
(*<*)
proof -
  obtain xs LT where "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil thus ?thesis by (simp!)
  next
    fix l xs' assume "xs = l#xs'"
    thus ?thesis
    proof (cases xs')
      case Nil thus ?thesis by (simp!)
    next
      fix l' ST assume "xs' = l'#ST"
      thus ?thesis by (simp!)
    qed
  qed
qed
(*>*)

text {* 
\medskip
simp rules for @{term app}
*}
lemma appNone[simp]: "app i P mxs T\<^isub>r pc mpc et None = True" 
  by (simp add: app_def)


lemma appLoad[simp]:
"app\<^isub>i (Load idx, P, T\<^isub>r, mxs, pc, s) = (\<exists>ST LT. s = (ST,LT) \<and> idx < length LT \<and> LT!idx \<noteq> Err \<and> length ST < mxs)"
  by (cases s, simp)

lemma appStore[simp]:
"app\<^isub>i (Store idx,P,pc,mxs,T\<^isub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT) \<and> idx < length LT)"
  by (rule length_cases2, auto)

lemma appPush[simp]:
"app\<^isub>i (Push v,P,pc,mxs,T\<^isub>r,s) =
 (\<exists>ST LT. s = (ST,LT) \<and> length ST < mxs \<and> typeof v \<noteq> None)"
  by (cases s, simp)

lemma appGetField[simp]:
"app\<^isub>i (Getfield F C,P,pc,mxs,T\<^isub>r,s) = 
 (\<exists> oT vT ST LT. s = (oT#ST, LT) \<and> 
  P \<turnstile> C sees F:vT in C \<and> P \<turnstile> oT \<le> (Class C))"
  by (rule length_cases2 [of _ s]) auto

lemma appPutField[simp]:
"app\<^isub>i (Putfield F C,P,pc,mxs,T\<^isub>r,s) = 
 (\<exists> vT vT' oT ST LT. s = (vT#oT#ST, LT) \<and>
  P \<turnstile> C sees F:vT' in C \<and> P \<turnstile> oT \<le> (Class C) \<and> P \<turnstile> vT \<le> vT')"
  by (rule length_cases4 [of _ s], auto)

lemma appNew[simp]:
  "app\<^isub>i (New C,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>ST LT. s=(ST,LT) \<and> is_class P C \<and> length ST < mxs)"
  by (cases s, simp)

lemma appCheckcast[simp]: 
  "app\<^isub>i (Checkcast C,P,pc,mxs,T\<^isub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_class P C \<and> is_refT T)"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma app\<^isub>iPop[simp]: 
"app\<^isub>i (Pop,P,pc,mxs,T\<^isub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT))"
  by (rule length_cases2, auto)

lemma appIAdd[simp]:
"app\<^isub>i (IAdd,P,pc,mxs,T\<^isub>r,s) = (\<exists>ST LT. s = (Integer#Integer#ST,LT))"
(*<*)
proof -
  obtain ST LT where [simp]: "s = (ST,LT)" by (cases s)
  have "ST = [] \<or> (\<exists>T. ST = [T]) \<or> (\<exists>T\<^isub>1 T\<^isub>2 ST'. ST = T\<^isub>1#T\<^isub>2#ST')"
    by (cases ST, auto, case_tac list, auto)
  moreover
  { assume "ST = []" hence ?thesis by simp }
  moreover
  { fix T assume "ST = [T]" hence ?thesis by (cases T, auto) }
  moreover
  { fix T\<^isub>1 T\<^isub>2 ST' assume "ST = T\<^isub>1#T\<^isub>2#ST'"
    hence ?thesis by (cases T\<^isub>1, auto)
  }
  ultimately show ?thesis by blast
qed
(*>*)


lemma appIfFalse [simp]:
"app\<^isub>i (IfFalse b,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>ST LT. s = (Boolean#ST,LT) \<and> 0 \<le> int pc + b)"
(*<*)
  apply (rule length_cases2)
  apply simp
  apply (case_tac l) 
  apply auto
  done
(*>*)

lemma appCmpEq[simp]:
"app\<^isub>i (CmpEq,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>T\<^isub>1 T\<^isub>2 ST LT. s = (T\<^isub>1#T\<^isub>2#ST,LT) \<and> (\<not>is_refT T\<^isub>1 \<and> T\<^isub>2 = T\<^isub>1 \<or> is_refT T\<^isub>1 \<and> is_refT T\<^isub>2))"
  by (rule length_cases4, auto)

lemma appReturn[simp]:
"app\<^isub>i (Return,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> P \<turnstile> T \<le> T\<^isub>r)" 
  by (rule length_cases2, auto)

lemma appThrow[simp]:
  "app\<^isub>i (Throw,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)  

lemma effNone: 
  "(pc', s') \<in> set (eff i P pc et None) \<Longrightarrow> s' = None"
  by (auto simp add: eff_def xcpt_eff_def norm_eff_def)


text {* some helpers to make the specification directly executable: *}
declare list_all2_Nil [code]
declare list_all2_Cons [code]

lemma relevant_entries_append [simp]:
  "relevant_entries P i pc (xt @ xt') = relevant_entries P i pc xt @ relevant_entries P i pc xt'"
  by (unfold relevant_entries_def) simp

lemma xcpt_app_append [iff]:
  "xcpt_app i P pc mxs (xt@xt') \<tau> = (xcpt_app i P pc mxs xt \<tau> \<and> xcpt_app i P pc mxs xt' \<tau>)"
  by (unfold xcpt_app_def) fastsimp

lemma xcpt_eff_append [simp]:
  "xcpt_eff i P pc \<tau> (xt@xt') = xcpt_eff i P pc \<tau> xt @ xcpt_eff i P pc \<tau> xt'"
 by (unfold xcpt_eff_def, cases \<tau>) simp

lemma app_append [simp]:
  "app i P pc T mxs mpc (xt@xt') \<tau> = (app i P pc T mxs mpc xt \<tau> \<and> app i P pc T mxs mpc xt' \<tau>)"
  by (unfold app_def eff_def) auto

end
