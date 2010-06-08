(*  Title:      JinjaThreads/BV/Effect.thy
    Author:     Gerwin Klein, Andreas Lochbihler
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
primrec succs :: "instr \<Rightarrow> ty\<^isub>i \<Rightarrow> pc \<Rightarrow> pc list"
where
  "succs (Load idx) \<tau> pc     = [pc+1]"
| "succs (Store idx) \<tau> pc    = [pc+1]"
| "succs (Push v) \<tau> pc       = [pc+1]"
| "succs (Getfield F C) \<tau> pc = [pc+1]"
| "succs (Putfield F C) \<tau> pc = [pc+1]"
| "succs (New C) \<tau> pc        = [pc+1]"
| "succs (NewArray T) \<tau> pc   = [pc+1]"
| "succs ALoad \<tau> pc          = (if (fst \<tau>)!1 = NT then [] else [pc+1])"
| "succs AStore \<tau> pc         = (if (fst \<tau>)!2 = NT then [] else [pc+1])"
| "succs ALength \<tau> pc        = (if (fst \<tau>)!0 = NT then [] else [pc+1])"
| "succs (Checkcast C) \<tau> pc  = [pc+1]"
| "succs (Instanceof T) \<tau> pc  = [pc+1]"
| "succs Pop \<tau> pc            = [pc+1]"
| "succs Dup \<tau> pc            = [pc+1]"
| "succs (BinOpInstr b) \<tau> pc = [pc+1]"
| succs_IfFalse:
  "succs (IfFalse b) \<tau> pc    = [pc+1, nat (int pc + b)]"
| succs_Goto:
  "succs (Goto b) \<tau> pc       = [nat (int pc + b)]"
| succs_Return:
  "succs Return \<tau> pc         = []"  
| succs_Invoke:
  "succs (Invoke M n) \<tau> pc   = (if (fst \<tau>)!n = NT then [] else [pc+1])"
| succs_Throw:
  "succs ThrowExc \<tau> pc          = []"
| "succs MEnter \<tau> pc         = (if (fst \<tau>)!0 = NT then [] else [pc+1])"
| "succs MExit \<tau> pc          = (if (fst \<tau>)!0 = NT then [] else [pc+1])"

text "Effect of instruction on the state type:"

fun eff\<^isub>i :: "instr \<times> 'm prog \<times> ty\<^isub>i \<Rightarrow> ty\<^isub>i"
where
  eff\<^isub>i_Load:
  "eff\<^isub>i (Load n,  P, (ST, LT))          = (ok_val (LT ! n) # ST, LT)"

| eff\<^isub>i_Store:
  "eff\<^isub>i (Store n, P, (T#ST, LT))        = (ST, LT[n:= OK T])"

| eff\<^isub>i_Push:
  "eff\<^isub>i (Push v, P, (ST, LT))             = (the (typeof v) # ST, LT)"

| eff\<^isub>i_Getfield:
  "eff\<^isub>i (Getfield F C, P, (T#ST, LT))    = (snd (field P C F) # ST, LT)"

| eff\<^isub>i_Putfield:
  "eff\<^isub>i (Putfield F C, P, (T\<^isub>1#T\<^isub>2#ST, LT)) = (ST,LT)"

| eff\<^isub>i_New:
  "eff\<^isub>i (New C, P, (ST,LT))               = (Class C # ST, LT)"

| eff\<^isub>i_NewArray:
  "eff\<^isub>i (NewArray Ty, P, (T#ST,LT))       = (Ty\<lfloor>\<rceil> # ST,LT)"

| eff\<^isub>i_ALoad:
  "eff\<^isub>i (ALoad, P, (T1#T2#ST,LT))       = (the_Array T2# ST,LT)"

| eff\<^isub>i_AStore:
  "eff\<^isub>i (AStore, P, (T1#T2#T3#ST,LT))  = (ST,LT)"

| eff\<^isub>i_ALength:
  "eff\<^isub>i (ALength, P, (T1#ST,LT))  = (Integer#ST,LT)"

| eff\<^isub>i_Checkcast:
  "eff\<^isub>i (Checkcast Ty, P, (T#ST,LT))       = (Ty # ST,LT)"

| eff\<^isub>i_Instanceof:
  "eff\<^isub>i (Instanceof Ty, P, (T#ST,LT))       = (Boolean # ST,LT)"

| eff\<^isub>i_Pop:
  "eff\<^isub>i (Pop, P, (T#ST,LT))               = (ST,LT)"

| eff\<^isub>i_Dup:
  "eff\<^isub>i (Dup, P, (T#ST,LT))               = (T#T#ST,LT)"

| eff\<^isub>i_BinOpInstr:
  "eff\<^isub>i (BinOpInstr bop, P, (T2#T1#ST,LT)) = ((THE T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)#ST, LT)"

| eff\<^isub>i_IfFalse:
  "eff\<^isub>i (IfFalse b, P, (T\<^isub>1#ST,LT))        = (ST,LT)"

| eff\<^isub>i_Invoke:
  "eff\<^isub>i (Invoke M n, P, (ST,LT))          =
  (let T = ST ! n;
       C = the_Class T;
       Ts = rev(take n ST);
       U = if is_external_call P T M 
           then (THE U. \<exists>Ts'. P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T\<bullet>M(Ts') :: U) 
           else fst (snd (snd (method P C M)))
   in (U # drop (n+1) ST, LT))"

| eff\<^isub>i_Goto:
  "eff\<^isub>i (Goto n, P, s)                    = s"

| eff\<^isub>i_MEnter:
  "eff\<^isub>i (MEnter, P, (T1#ST,LT))           = (ST,LT)"

| eff\<^isub>i_MExit:
  "eff\<^isub>i (MExit, P, (T1#ST,LT))            = (ST,LT)"


fun is_relevant_class :: "instr \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool" 
where
  rel_Getfield:
  "is_relevant_class (Getfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Putfield:
  "is_relevant_class (Putfield F D) = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)" 
| rel_Checcast:
  "is_relevant_class (Checkcast T)  = (\<lambda>P C. P \<turnstile> ClassCast \<preceq>\<^sup>* C)" 
| rel_New:
  "is_relevant_class (New D)        = (\<lambda>P C. P \<turnstile> OutOfMemory \<preceq>\<^sup>* C)" 
| rel_Throw:
  "is_relevant_class ThrowExc       = (\<lambda>P C. True)"
| rel_Invoke:
  "is_relevant_class (Invoke M n)   = (\<lambda>P C. True)"
| rel_NewArray:
  "is_relevant_class (NewArray T)   = (\<lambda>P C. (P \<turnstile> OutOfMemory \<preceq>\<^sup>* C) \<or> (P \<turnstile> NegativeArraySize \<preceq>\<^sup>* C))"
| rel_ALoad:
  "is_relevant_class ALoad          = (\<lambda>P C. P \<turnstile> ArrayIndexOutOfBounds \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_AStore:
  "is_relevant_class AStore         = (\<lambda>P C. P \<turnstile> ArrayIndexOutOfBounds \<preceq>\<^sup>* C \<or> P \<turnstile> ArrayStore \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_ALength:
  "is_relevant_class ALength        = (\<lambda>P C. P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_MEnter:
  "is_relevant_class MEnter         = (\<lambda>P C. P \<turnstile> IllegalMonitorState \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_MExit:
  "is_relevant_class MExit          = (\<lambda>P C. P \<turnstile> IllegalMonitorState \<preceq>\<^sup>* C \<or> P \<turnstile> NullPointer \<preceq>\<^sup>* C)"
| rel_default:
  "is_relevant_class i              = (\<lambda>P C. False)"

definition is_relevant_entry :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool" 
where
  "is_relevant_entry P i pc e \<equiv> 
   let (f,t,C,h,d) = e 
   in (case C of None \<Rightarrow> True | \<lfloor>C'\<rfloor> \<Rightarrow> is_relevant_class i P C') \<and> pc \<in> {f..<t}"

definition relevant_entries :: "'m prog \<Rightarrow> instr \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ex_table" 
where
  "relevant_entries P i pc \<equiv> filter (is_relevant_entry P i pc)"

definition xcpt_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ty\<^isub>i \<Rightarrow> ex_table \<Rightarrow> (pc \<times> ty\<^isub>i') list"
where
  "xcpt_eff i P pc \<tau> et \<equiv> let (ST,LT) = \<tau> in 
  map (\<lambda>(f,t,C,h,d). (h, Some ((case C of None \<Rightarrow> Class Throwable | Some C' \<Rightarrow> Class C')#drop (size ST - d) ST, LT))) (relevant_entries P i pc et)"

definition norm_eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty\<^isub>i \<Rightarrow> (pc \<times> ty\<^isub>i') list"
where "norm_eff i P pc \<tau> \<equiv> map (\<lambda>pc'. (pc',Some (eff\<^isub>i (i,P,\<tau>)))) (succs i \<tau> pc)"

definition eff :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i' \<Rightarrow> (pc \<times> ty\<^isub>i') list"
where
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

fun app\<^isub>i :: "instr \<times> 'm prog \<times> pc \<times> nat \<times> ty \<times> ty\<^isub>i \<Rightarrow> bool"
where
  app\<^isub>i_Load:
  "app\<^isub>i (Load n, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
    (n < length LT \<and> LT ! n \<noteq> Err \<and> length ST < mxs)"
| app\<^isub>i_Store:
  "app\<^isub>i (Store n, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = 
    (n < length LT)"
| app\<^isub>i_Push:
  "app\<^isub>i (Push v, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
    (length ST < mxs \<and> typeof v \<noteq> None)"
| app\<^isub>i_Getfield:
  "app\<^isub>i (Getfield F C, P, pc, mxs, T\<^isub>r, (T#ST, LT)) = 
    (\<exists>T\<^isub>f. P \<turnstile> C sees F:T\<^isub>f in C \<and> P \<turnstile> T \<le> Class C)"
| app\<^isub>i_Putfield:
  "app\<^isub>i (Putfield F C, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST, LT)) = 
    (\<exists>T\<^isub>f. P \<turnstile> C sees F:T\<^isub>f in C \<and> P \<turnstile> T\<^isub>2 \<le> (Class C) \<and> P \<turnstile> T\<^isub>1 \<le> T\<^isub>f)" 
| app\<^isub>i_New:
  "app\<^isub>i (New C, P, pc, mxs, T\<^isub>r, (ST,LT)) = 
    (is_class P C \<and> length ST < mxs)"
| app\<^isub>i_NewArray:
  "app\<^isub>i (NewArray Ty, P, pc, mxs, T\<^isub>r, (Integer#ST,LT)) = 
    is_type P Ty"
|  app\<^isub>i_ALoad:
  "app\<^isub>i (ALoad, P, pc, mxs, T\<^isub>r, (T1#T2#ST,LT)) = 
    (T1 = Integer \<and> (T2 \<noteq> NT \<longrightarrow> (\<exists>Ty. T2 = Ty\<lfloor>\<rceil>)))"
| app\<^isub>i_AStore:
  "app\<^isub>i (AStore, P, pc, mxs, T\<^isub>r, (T1#T2#T3#ST,LT)) = 
    (T2 = Integer \<and> (T3 \<noteq> NT \<longrightarrow> (\<exists>Ty. T3 = Ty\<lfloor>\<rceil>)))"
| app\<^isub>i_ALength:
  "app\<^isub>i (ALength, P, pc, mxs, T\<^isub>r, (T1#ST,LT)) = 
    (T1 = NT \<or> (\<exists>Ty. T1 = Ty\<lfloor>\<rceil>))"
| app\<^isub>i_Checkcast:
  "app\<^isub>i (Checkcast Ty, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
    (is_type P Ty (* \<and> is_refT T *) )"
| app\<^isub>i_Instanceof:
  "app\<^isub>i (Instanceof Ty, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
    (is_type P Ty \<and> is_refT T)"
| app\<^isub>i_Pop:
  "app\<^isub>i (Pop, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
    True"
| app\<^isub>i_Dup:
  "app\<^isub>i (Dup, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
    (Suc (length ST) < mxs)"
| app\<^isub>i_BinOpInstr:
  "app\<^isub>i (BinOpInstr bop, P, pc, mxs, T\<^isub>r, (T2#T1#ST,LT)) = (\<exists>T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)"
| app\<^isub>i_IfFalse:
  "app\<^isub>i (IfFalse b, P, pc, mxs, T\<^isub>r, (Boolean#ST,LT)) = 
    (0 \<le> int pc + b)"
| app\<^isub>i_Goto:
  "app\<^isub>i (Goto b, P, pc, mxs, T\<^isub>r, s) =  (0 \<le> int pc + b)"
| app\<^isub>i_Return:
  "app\<^isub>i (Return, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = (P \<turnstile> T \<le> T\<^isub>r)"
| app\<^isub>i_Throw:
  "app\<^isub>i (ThrowExc, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
    (T = NT \<or> (\<exists>C. T = Class C \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable))"
| app\<^isub>i_Invoke:
  "app\<^isub>i (Invoke M n, P, pc, mxs, T\<^isub>r, (ST,LT)) =
    (n < length ST \<and> 
    (ST!n \<noteq> NT \<longrightarrow>
      (if is_external_call P (ST ! n) M then \<exists>U Ts. P \<turnstile> rev (take n ST) [\<le>] Ts \<and> P \<turnstile> ST ! n\<bullet>M(Ts) :: U
       else \<exists>C D Ts T m. ST!n = Class C \<and> P \<turnstile> C sees M:Ts \<rightarrow> T = m in D \<and> P \<turnstile> rev (take n ST) [\<le>] Ts)))"
| app\<^isub>i_MEnter:
  "app\<^isub>i (MEnter,P, pc,mxs,T\<^isub>r,(T#ST,LT)) = (is_refT T)"
| app\<^isub>i_MExit:
  "app\<^isub>i (MExit,P, pc,mxs,T\<^isub>r,(T#ST,LT)) = (is_refT T)"
| app\<^isub>i_default:
  "app\<^isub>i (i,P, pc,mxs,T\<^isub>r,s) = False"


definition xcpt_app :: "instr \<Rightarrow> 'm prog \<Rightarrow> pc \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i \<Rightarrow> bool"
where
  "xcpt_app i P pc mxs xt \<tau> \<equiv> \<forall>(f,t,C,h,d) \<in> set (relevant_entries P i pc xt). (case C of None \<Rightarrow> True | Some C' \<Rightarrow> is_class P C') \<and> d \<le> size (fst \<tau>) \<and> d < mxs"

definition app :: "instr \<Rightarrow> 'm prog \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i' \<Rightarrow> bool"
where
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
  by (cases s, cases "fst s") (auto intro!: assms)


lemma length_cases3:
  assumes "\<And>LT. P ([],LT)"
  assumes "\<And>l LT. P ([l],LT)"
  assumes "\<And>l ST LT. P (l#ST,LT)"
  shows "P s"
(*<*)
proof -
  obtain xs LT where s: "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil thus ?thesis using s assms by (simp)
  next
    fix l xs' assume "xs = l#xs'"
    thus ?thesis using s assms by (simp)
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
  obtain xs LT where s: "s = (xs,LT)" by (cases s)
  show ?thesis
  proof (cases xs)
    case Nil thus ?thesis using s assms by (simp)
  next
    fix l xs' assume xs: "xs = l#xs'"
    thus ?thesis
    proof (cases xs')
      case Nil thus ?thesis using s assms xs by (simp)
    next
      fix l' ST assume xs': "xs' = l'#ST"
      thus ?thesis using s assms xs xs' by (simp)
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

lemma appNewArray[simp]:
  "app\<^isub>i (NewArray Ty,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>ST LT. s=(Integer#ST,LT) \<and> is_type P Ty)"
  by (cases s, simp, cases "fst s", simp)(cases "hd (fst s)", auto)

lemma appALoad[simp]:
  "app\<^isub>i (ALoad,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>T ST LT. s=(Integer#T#ST,LT) \<and> (T \<noteq> NT \<longrightarrow> (\<exists>T'.  T = T'\<lfloor>\<rceil>)))"
proof -
  obtain ST LT where [simp]: "s = (ST, LT)" by (cases s)
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

lemma appAStore[simp]:
  "app\<^isub>i (AStore,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>T U ST LT. s=(T#Integer#U#ST,LT) \<and> (U \<noteq> NT \<longrightarrow> (\<exists>T'. U = T'\<lfloor>\<rceil>)))"
proof -
  obtain ST LT where [simp]: "s = (ST, LT)" by (cases s)
  have "ST = [] \<or> (\<exists>T. ST = [T]) \<or> (\<exists>T\<^isub>1 T\<^isub>2. ST = [T\<^isub>1, T\<^isub>2]) \<or> (\<exists>T1 T2 T3 ST'. ST = T1 # T2 # T3 # ST')"
    by (cases ST, auto, case_tac list, auto, case_tac lista, auto)
  moreover
  { assume "ST = []" hence ?thesis by simp }
  moreover
  { fix T assume "ST = [T]" hence ?thesis by(simp) }
  moreover
  { fix T1 T2 assume "ST = [T1, T2]" hence ?thesis by simp }
  moreover
  { fix T1 T2 T3 ST' assume "ST = T1 # T2 # T3 # ST'" hence ?thesis by(cases T2, auto) }
  ultimately show ?thesis by blast
qed

lemma appALength[simp]:
  "app\<^isub>i (ALength,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>T ST LT. s=(T#ST,LT) \<and> (T \<noteq> NT \<longrightarrow> (\<exists>T'.  T = T'\<lfloor>\<rceil>)))"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma appCheckcast[simp]: 
  "app\<^isub>i (Checkcast Ty,P,pc,mxs,T\<^isub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_type P Ty (* \<and> is_refT T *))"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma appInstanceof[simp]: 
  "app\<^isub>i (Instanceof Ty,P,pc,mxs,T\<^isub>r,s) =  
  (\<exists>T ST LT. s = (T#ST,LT) \<and> is_type P Ty \<and> is_refT T)"
  by (cases s, cases "fst s", simp add: app_def) (cases "hd (fst s)", auto)

lemma app\<^isub>iPop[simp]: 
"app\<^isub>i (Pop,P,pc,mxs,T\<^isub>r,s) = (\<exists>ts ST LT. s = (ts#ST,LT))"
  by (rule length_cases2, auto)

lemma appDup[simp]:
"app\<^isub>i (Dup,P,pc,mxs,T\<^isub>r,s) =
 (\<exists>T ST LT. s = (T#ST,LT) \<and> Suc (length ST) < mxs)"
by (cases s, cases "fst s", simp_all)


lemma appBinOp[simp]:
"app\<^isub>i (BinOpInstr bop,P,pc,mxs,T\<^isub>r,s) = (\<exists>T1 T2 ST LT T. s = (T2 # T1 # ST, LT) \<and> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T)"
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
    hence ?thesis by simp
  }
  ultimately show ?thesis by blast
qed

lemma appIfFalse [simp]:
"app\<^isub>i (IfFalse b,P,pc,mxs,T\<^isub>r,s) = 
  (\<exists>ST LT. s = (Boolean#ST,LT) \<and> 0 \<le> int pc + b)"
  apply (rule length_cases2)
  apply simp
  apply (case_tac l) 
  apply auto
  done

lemma appReturn[simp]:
"app\<^isub>i (Return,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s = (T#ST,LT) \<and> P \<turnstile> T \<le> T\<^isub>r)" 
  by (rule length_cases2, auto)

lemma appThrow[simp]:
  "app\<^isub>i (ThrowExc,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> (T = NT \<or> (\<exists>C. T = Class C \<and> P \<turnstile> C \<preceq>\<^sup>* Throwable)))"
  by (rule length_cases2, auto)  

lemma appMEnter[simp]:
  "app\<^isub>i (MEnter,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)  

lemma appMExit[simp]:
  "app\<^isub>i (MExit,P,pc,mxs,T\<^isub>r,s) = (\<exists>T ST LT. s=(T#ST,LT) \<and> is_refT T)"
  by (rule length_cases2, auto)

lemma effNone: 
  "(pc', s') \<in> set (eff i P pc et None) \<Longrightarrow> s' = None"
  by (auto simp add: eff_def xcpt_eff_def norm_eff_def)


lemma relevant_entries_append [simp]:
  "relevant_entries P i pc (xt @ xt') = relevant_entries P i pc xt @ relevant_entries P i pc xt'"
  by (unfold relevant_entries_def) simp

lemma xcpt_app_append [iff]:
  "xcpt_app i P pc mxs (xt@xt') \<tau> = (xcpt_app i P pc mxs xt \<tau> \<and> xcpt_app i P pc mxs xt' \<tau>)"
unfolding xcpt_app_def by force

lemma xcpt_eff_append [simp]:
  "xcpt_eff i P pc \<tau> (xt@xt') = xcpt_eff i P pc \<tau> xt @ xcpt_eff i P pc \<tau> xt'"
 by (unfold xcpt_eff_def, cases \<tau>) simp

lemma app_append [simp]:
  "app i P pc T mxs mpc (xt@xt') \<tau> = (app i P pc T mxs mpc xt \<tau> \<and> app i P pc T mxs mpc xt' \<tau>)"
  by (unfold app_def eff_def) auto


subsection {* Code generator setup *}

declare list_all2_Nil [code]
declare list_all2_Cons [code]

lemma eff\<^isub>i_BinOpInstr_code:
  "eff\<^isub>i (BinOpInstr bop, P, (T2#T1#ST,LT)) = (Predicate.the (WTrt_binop_i_i_i_i_o P T1 bop T2) # ST, LT)"
by(simp add: the_WTrt_binop_code)

lemma eff\<^isub>i_Invoke_code:
  "eff\<^isub>i (Invoke M n, P, (ST,LT)) =
  (let T = ST ! n;
       C = the_Class T;
       Ts = rev(take n ST);
       U = if is_external_call P T M 
           then Predicate.the (Predicate.bind (external_WT_i_i_i_o_o P T M)
                                              (\<lambda>(Ts', U). if P \<turnstile> Ts [\<le>] Ts' then Predicate.single U else bot))
           else fst (snd (snd (method P C M)))
   in (U # drop (n+1) ST, LT))"
apply(clarsimp simp add: Predicate.the_def Predicate.bind_def Predicate.single_def eval_external_WT_i_i_i_o_o_conv)
apply(rule arg_cong[where f=The])
apply(rule ext)
apply blast
done

lemmas eff\<^isub>i_code[code] =
  eff\<^isub>i_Load eff\<^isub>i_Store eff\<^isub>i_Push eff\<^isub>i_Getfield eff\<^isub>i_Putfield eff\<^isub>i_New eff\<^isub>i_NewArray eff\<^isub>i_ALoad
  eff\<^isub>i_AStore eff\<^isub>i_ALength eff\<^isub>i_Checkcast eff\<^isub>i_Instanceof eff\<^isub>i_Pop eff\<^isub>i_Dup eff\<^isub>i_BinOpInstr_code
  eff\<^isub>i_IfFalse eff\<^isub>i_Invoke_code eff\<^isub>i_Goto eff\<^isub>i_MEnter eff\<^isub>i_MExit

lemma app\<^isub>i_Getfield_code:
  "app\<^isub>i (Getfield F C, P, pc, mxs, T\<^isub>r, (T#ST, LT)) \<longleftrightarrow>
  Predicate.holds (Predicate.bind (sees_field_i_i_i_o_i P C F C) (\<lambda>T. Predicate.single ())) \<and> P \<turnstile> T \<le> Class C"
by(clarsimp simp add: Predicate.bind_def Predicate.single_def holds_eq eval_sees_field_i_i_i_o_i_conv)
 
lemma app\<^isub>i_Putfield_code:
  "app\<^isub>i (Putfield F C, P, pc, mxs, T\<^isub>r, (T\<^isub>1#T\<^isub>2#ST, LT)) \<longleftrightarrow>
   P \<turnstile> T\<^isub>2 \<le> (Class C) \<and>
   Predicate.holds (Predicate.bind (sees_field_i_i_i_o_i P C F C) (\<lambda>T. if P \<turnstile> T\<^isub>1 \<le> T then Predicate.single () else bot))"
by(auto simp add: Predicate.bind_def Predicate.single_def holds_eq eval_sees_field_i_i_i_o_i_conv)

lemma app\<^isub>i_ALoad_code:
  "app\<^isub>i (ALoad, P, pc, mxs, T\<^isub>r, (T1#T2#ST,LT)) = 
   (T1 = Integer \<and> (case T2 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False))"
by(simp add: split: ty.split)

lemma app\<^isub>i_AStore_code:
  "app\<^isub>i (AStore, P, pc, mxs, T\<^isub>r, (T1#T2#T3#ST,LT)) = 
  (T2 = Integer \<and> (case T3 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False))"
by(simp add: split: ty.split)

lemma app\<^isub>i_ALength_code:
  "app\<^isub>i (ALength, P, pc, mxs, T\<^isub>r, (T1#ST,LT)) = 
   (case T1 of Ty\<lfloor>\<rceil> \<Rightarrow> True | NT \<Rightarrow> True | _ \<Rightarrow> False)"
by(simp add: split: ty.split)

lemma app\<^isub>i_BinOpInstr_code:
  "app\<^isub>i (BinOpInstr bop, P, pc, mxs, T\<^isub>r, (T2#T1#ST,LT)) = 
   Predicate.holds (Predicate.bind (WTrt_binop_i_i_i_i_o P T1 bop T2) (\<lambda>T. Predicate.single ()))"
by(simp add: Predicate.bind_def Predicate.single_def holds_eq eval_WTrt_binop_i_i_i_i_o)

lemma app\<^isub>i_Invoke_code:
  "app\<^isub>i (Invoke M n, P, pc, mxs, T\<^isub>r, (ST,LT)) =
  (n < length ST \<and> 
  (ST!n \<noteq> NT \<longrightarrow>
    (if is_external_call P (ST ! n) M 
     then Predicate.holds (Predicate.bind (external_WT_i_i_i_o_o P (ST ! n) M) 
                                          (\<lambda>(Ts, U). if P \<turnstile> rev (take n ST) [\<le>] Ts then Predicate.single () else bot))
     else (case ST ! n of Class C \<Rightarrow> 
               Predicate.holds (Predicate.bind (Method_i_i_i_o_o_o_o P C M) 
                                               (\<lambda>(Ts, _). if P \<turnstile> rev (take n ST) [\<le>] Ts then Predicate.single () else bot))
                              | _ \<Rightarrow> False))))"
by(auto simp add: Predicate.bind_def Predicate.single_def holds_eq eval_external_WT_i_i_i_o_o_conv eval_Method_i_i_i_o_o_o_o_conv split: ty.split)

lemma app\<^isub>i_Throw_code:
  "app\<^isub>i (ThrowExc, P, pc, mxs, T\<^isub>r, (T#ST,LT)) = 
  (case T of NT \<Rightarrow> True | Class C \<Rightarrow> P \<turnstile> C \<preceq>\<^sup>* Throwable | _ \<Rightarrow> False)"
by(simp split: ty.split)

lemmas app\<^isub>i_code [code] =
  app\<^isub>i_Load app\<^isub>i_Store app\<^isub>i_Push
  app\<^isub>i_Getfield_code app\<^isub>i_Putfield_code
  app\<^isub>i_New app\<^isub>i_NewArray
  app\<^isub>i_ALoad_code app\<^isub>i_AStore_code app\<^isub>i_ALength_code
  app\<^isub>i_Checkcast app\<^isub>i_Instanceof
  app\<^isub>i_Pop app\<^isub>i_Dup app\<^isub>i_BinOpInstr_code app\<^isub>i_IfFalse app\<^isub>i_Goto
  app\<^isub>i_Return app\<^isub>i_Throw_code app\<^isub>i_Invoke_code app\<^isub>i_MEnter app\<^isub>i_MExit
  app\<^isub>i_default

end
