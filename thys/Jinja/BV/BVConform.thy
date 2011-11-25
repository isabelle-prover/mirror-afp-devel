(*  Title:      HOL/MicroJava/BV/Correct.thy

    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)

header {* \isaheader{BV Type Safety Invariant} *}

theory BVConform
imports BVSpec "../JVM/JVMExec" "../Common/Conform"
begin


definition confT :: "'c prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty err \<Rightarrow> bool" 
           ("_,_ |- _ :<=T _" [51,51,51,51] 50)
where
  "P,h |- v :<=T E \<equiv> case E of Err \<Rightarrow> True | OK T \<Rightarrow> P,h \<turnstile> v :\<le> T"

notation (xsymbols)
  confT  ("_,_ \<turnstile> _ :\<le>\<^sub>\<top> _" [51,51,51,51] 50)

abbreviation
  confTs :: "'c prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty\<^isub>l \<Rightarrow> bool" 
            ("_,_ |- _ [:<=T] _" [51,51,51,51] 50) where
  "P,h |- vs [:<=T] Ts \<equiv> list_all2 (confT P h) vs Ts"

notation (xsymbols)
  confTs  ("_,_ \<turnstile> _ [:\<le>\<^sub>\<top>] _" [51,51,51,51] 50)

definition conf_f  :: "jvm_prog \<Rightarrow> heap \<Rightarrow> ty\<^isub>i \<Rightarrow> bytecode \<Rightarrow> frame \<Rightarrow> bool"
where
  "conf_f P h \<equiv> \<lambda>(ST,LT) is (stk,loc,C,M,pc).
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is"

lemma conf_f_def2:
  "conf_f P h (ST,LT) is (stk,loc,C,M,pc) \<equiv>
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is"
  by (simp add: conf_f_def)


primrec conf_fs :: "[jvm_prog,heap,ty\<^isub>P,mname,nat,ty,frame list] \<Rightarrow> bool"
where
  "conf_fs P h \<Phi> M\<^isub>0 n\<^isub>0 T\<^isub>0 [] = True"
| "conf_fs P h \<Phi> M\<^isub>0 n\<^isub>0 T\<^isub>0 (f#frs) =
  (let (stk,loc,C,M,pc) = f in
  (\<exists>ST LT Ts T mxs mxl\<^isub>0 is xt.
    \<Phi> C M ! pc = Some (ST,LT) \<and> 
    (P \<turnstile> C sees M:Ts \<rightarrow> T = (mxs,mxl\<^isub>0,is,xt) in C) \<and>
    (\<exists>D Ts' T' m D'.  
       is!pc = (Invoke M\<^isub>0 n\<^isub>0) \<and> ST!n\<^isub>0 = Class D \<and>
       P \<turnstile> D sees M\<^isub>0:Ts' \<rightarrow> T' = m in D' \<and> P \<turnstile> T\<^isub>0 \<le> T') \<and>
    conf_f P h (ST, LT) is f \<and> conf_fs P h \<Phi> M (size Ts) T frs))"


definition correct_state :: "[jvm_prog,ty\<^isub>P,jvm_state] \<Rightarrow> bool"
                  ("_,_ |- _ [ok]"  [61,0,0] 61)
where
  "correct_state P \<Phi> \<equiv> \<lambda>(xp,h,frs).
  case xp of
     None \<Rightarrow> (case frs of
             [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> P\<turnstile> h\<surd> \<and> 
             (let (stk,loc,C,M,pc) = f
              in \<exists>Ts T mxs mxl\<^isub>0 is xt \<tau>.
                    (P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl\<^isub>0,is,xt) in C) \<and>
                    \<Phi> C M ! pc = Some \<tau> \<and>
                    conf_f P h \<tau> is f \<and> conf_fs P h \<Phi> M (size Ts) T fs))
  | Some x \<Rightarrow> frs = []" 

notation (xsymbols)
 correct_state  ("_,_ \<turnstile> _ \<surd>"  [61,0,0] 61)



section {* Values and @{text "\<top>"} *}

lemma confT_Err [iff]: "P,h \<turnstile> x :\<le>\<^sub>\<top> Err" 
  by (simp add: confT_def)

lemma confT_OK [iff]:  "P,h \<turnstile> x :\<le>\<^sub>\<top> OK T = (P,h \<turnstile> x :\<le> T)"
  by (simp add: confT_def)

lemma confT_cases:
  "P,h \<turnstile> x :\<le>\<^sub>\<top> X = (X = Err \<or> (\<exists>T. X = OK T \<and> P,h \<turnstile> x :\<le> T))"
  by (cases X) auto

lemma confT_hext [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> x :\<le>\<^sub>\<top> T"
  by (cases T) (blast intro: conf_hext)+

lemma confT_widen [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; P \<turnstile> T \<le>\<^sub>\<top> T' \<rbrakk> \<Longrightarrow> P,h \<turnstile> x :\<le>\<^sub>\<top> T'"
  by (cases T', auto intro: conf_widen)


section {* Stack and Registers *}

lemmas confTs_Cons1 [iff] = list_all2_Cons1 [of "confT P h"] for P h

lemma confTs_confT_sup:
  "\<lbrakk> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT; n < size LT; LT!n = OK T; P \<turnstile> T \<le> T' \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (loc!n) :\<le> T'"
(*<*)
  apply (frule list_all2_lengthD)
  apply (drule list_all2_nthD, simp)
  apply simp
  apply (erule conf_widen, assumption+)
  done
(*>*)

lemma confTs_hext [intro?]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
  by (fast elim: list_all2_mono confT_hext)    

lemma confTs_widen [intro?, trans]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> P \<turnstile> LT [\<le>\<^sub>\<top>] LT' \<Longrightarrow> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'"
  by (rule list_all2_trans, rule confT_widen)

lemma confTs_map [iff]:
  "\<And>vs. (P,h \<turnstile> vs [:\<le>\<^sub>\<top>] map OK Ts) = (P,h \<turnstile> vs [:\<le>] Ts)"
  by (induct Ts) (auto simp add: list_all2_Cons2)

lemma reg_widen_Err [iff]:
  "\<And>LT. (P \<turnstile> replicate n Err [\<le>\<^sub>\<top>] LT) = (LT = replicate n Err)"
  by (induct n) (auto simp add: list_all2_Cons1)
    
lemma confTs_Err [iff]:
  "P,h \<turnstile> replicate n v [:\<le>\<^sub>\<top>] replicate n Err"
  by (induct n) auto

  
section {* correct-frames *}

lemmas [simp del] = fun_upd_apply

lemma conf_fs_hext:
  "\<And>M n T\<^isub>r. 
  \<lbrakk> conf_fs P h \<Phi> M n T\<^isub>r frs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_fs P h' \<Phi> M n T\<^isub>r frs"
(*<*)
apply (induct frs)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold conf_f_def)
apply (simp (no_asm_use))
apply clarify
apply (fast elim!: confs_hext confTs_hext)
done
(*>*)

end
