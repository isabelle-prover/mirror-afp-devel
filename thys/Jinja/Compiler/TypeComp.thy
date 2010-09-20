(*  Title:      Jinja/Compiler/TypeComp.thy
    ID:         $Id: TypeComp.thy,v 1.11 2008-07-28 08:55:13 fhaftmann Exp $
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Preservation of Well-Typedness} *}

theory TypeComp
imports Compiler "../BV/BVSpec"
begin

(*<*)
declare nth_append[simp]
(*>*)

locale TC0 =
  fixes P :: "J\<^isub>1_prog" and mxl :: nat
begin

definition "ty E e = (THE T. P,E \<turnstile>\<^sub>1 e :: T)"

definition "ty\<^isub>l E A' = map (\<lambda>i. if i \<in> A' \<and> i < size E then OK(E!i) else Err) [0..<mxl]"

definition "ty\<^isub>i' ST E A = (case A of None \<Rightarrow> None | \<lfloor>A'\<rfloor> \<Rightarrow> Some(ST, ty\<^isub>l E A'))"

definition "after E A ST e = ty\<^isub>i' (ty E e # ST) E (A \<squnion> \<A> e)"

end

lemma (in TC0) ty_def2 [simp]: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> ty E e = T"
(*<*)
apply (unfold ty_def)
apply(blast intro: the_equality WT\<^isub>1_unique)
done
(*>*)

lemma (in TC0) [simp]: "ty\<^isub>i' ST E None = None"
(*<*)by (simp add: ty\<^isub>i'_def)(*>*)

lemma (in TC0) ty\<^isub>l_app_diff[simp]:
 "ty\<^isub>l (E@[T]) (A - {size E}) = ty\<^isub>l E A"
(*<*)by(auto simp add:ty\<^isub>l_def hyperset_defs)(*>*)


lemma (in TC0) ty\<^isub>i'_app_diff[simp]:
 "ty\<^isub>i' ST (E @ [T]) (A \<ominus> size E) = ty\<^isub>i' ST E A"
(*<*)by(auto simp add:ty\<^isub>i'_def hyperset_defs)(*>*)


lemma (in TC0) ty\<^isub>l_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^isub>l E A' [\<le>\<^sub>\<top>] ty\<^isub>l E A"
(*<*)by(auto simp:ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>i'_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^isub>i' ST E \<lfloor>A'\<rfloor> \<le>' ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>l_env_antimono:
 "P \<turnstile> ty\<^isub>l (E@[T]) A [\<le>\<^sub>\<top>] ty\<^isub>l E A" 
(*<*)by(auto simp:ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>i'_env_antimono:
 "P \<turnstile> ty\<^isub>i' ST (E@[T]) A \<le>' ty\<^isub>i' ST E A" 
(*<*)by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>i'_incr:
 "P \<turnstile> ty\<^isub>i' ST (E @ [T]) \<lfloor>insert (size E) A\<rfloor> \<le>' ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>l_incr:
 "P \<turnstile> ty\<^isub>l (E @ [T]) (insert (size E) A) [\<le>\<^sub>\<top>] ty\<^isub>l E A"
(*<*)by(auto simp: hyperset_defs ty\<^isub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^isub>l_in_types:
 "set E \<subseteq> types P \<Longrightarrow> ty\<^isub>l E A \<in> list mxl (err (types P))"
(*<*)by(auto simp add:ty\<^isub>l_def intro!:listI dest!: nth_mem)(*>*)

locale TC1 = TC0
begin

primrec compT :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^isub>1 \<Rightarrow> ty\<^isub>i' list" and
   compTs :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^isub>1 list \<Rightarrow> ty\<^isub>i' list" where
"compT E A ST (new C) = []"
| "compT E A ST (Cast C e) =  
   compT E A ST e @ [after E A ST e]"
| "compT E A ST (Val v) = []"
| "compT E A ST (e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2) =
  (let ST\<^isub>1 = ty E e\<^isub>1#ST; A\<^isub>1 = A \<squnion> \<A> e\<^isub>1 in
   compT E A ST e\<^isub>1 @ [after E A ST e\<^isub>1] @
   compT E A\<^isub>1 ST\<^isub>1 e\<^isub>2 @ [after E A\<^isub>1 ST\<^isub>1 e\<^isub>2])"
| "compT E A ST (Var i) = []"
| "compT E A ST (i := e) = compT E A ST e @
   [after E A ST e, ty\<^isub>i' ST E (A \<squnion> \<A> e \<squnion> \<lfloor>{i}\<rfloor>)]"
| "compT E A ST (e\<bullet>F{D}) = 
   compT E A ST e @ [after E A ST e]"
| "compT E A ST (e\<^isub>1\<bullet>F{D} := e\<^isub>2) =
  (let ST\<^isub>1 = ty   E e\<^isub>1#ST; A\<^isub>1 = A \<squnion> \<A> e\<^isub>1; A\<^isub>2 = A\<^isub>1 \<squnion> \<A> e\<^isub>2 in
   compT E A ST e\<^isub>1 @ [after E A ST e\<^isub>1] @
   compT E A\<^isub>1 ST\<^isub>1 e\<^isub>2 @ [after E A\<^isub>1 ST\<^isub>1 e\<^isub>2] @
   [ty\<^isub>i' ST E A\<^isub>2])"
| "compT E A ST {i:T; e} = compT (E@[T]) (A\<ominus>i) ST e"
| "compT E A ST (e\<^isub>1;;e\<^isub>2) =
  (let A\<^isub>1 = A \<squnion> \<A> e\<^isub>1 in
   compT E A ST e\<^isub>1 @ [after E A ST e\<^isub>1, ty\<^isub>i' ST E A\<^isub>1] @
   compT E A\<^isub>1 ST e\<^isub>2)"
| "compT E A ST (if (e) e\<^isub>1 else e\<^isub>2) =
   (let A\<^isub>0 = A \<squnion> \<A> e; \<tau> = ty\<^isub>i' ST E A\<^isub>0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A\<^isub>0 ST e\<^isub>1 @ [after E A\<^isub>0 ST e\<^isub>1, \<tau>] @
    compT E A\<^isub>0 ST e\<^isub>2)"
| "compT E A ST (while (e) c) =
   (let A\<^isub>0 = A \<squnion> \<A> e;  A\<^isub>1 = A\<^isub>0 \<squnion> \<A> c; \<tau> = ty\<^isub>i' ST E A\<^isub>0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A\<^isub>0 ST c @ [after E A\<^isub>0 ST c, ty\<^isub>i' ST E A\<^isub>1, ty\<^isub>i' ST E A\<^isub>0])"
| "compT E A ST (throw e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e\<bullet>M(es)) =
   compT E A ST e @ [after E A ST e] @
   compTs E (A \<squnion> \<A> e) (ty   E e # ST) es"
| "compT E A ST (try e\<^isub>1 catch(C i) e\<^isub>2) =
   compT E A ST e\<^isub>1 @ [after E A ST e\<^isub>1] @
   [ty\<^isub>i' (Class C#ST) E A, ty\<^isub>i' ST (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @
   compT (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e\<^isub>2"
| "compTs E A ST [] = []"
| "compTs  E A ST (e#es) = compT E A ST e @ [after E A ST e] @
                            compTs E (A \<squnion> (\<A> e)) (ty E e # ST) es"

definition compT\<^isub>a :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^isub>1 \<Rightarrow> ty\<^isub>i' list" where
  "compT\<^isub>a E A ST e = compT E A ST e @ [after E A ST e]"

end

lemma compE\<^isub>2_not_Nil[simp]: "compE\<^isub>2 e \<noteq> []"
(*<*)by(induct e) auto(*>*)

lemma (in TC1) compT_sizes[simp]:
shows "\<And>E A ST. size(compT E A ST e) = size(compE\<^isub>2 e) - 1"
and "\<And>E A ST. size(compTs E A ST es) = size(compEs\<^isub>2 es)"
(*<*)
apply(induct e and es)
apply(auto split:bop.splits nat_diff_split)
done
(*>*)


lemma (in TC1) [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compT E None ST e)"
and [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compTs E None ST es)"
(*<*)by(induct e and es) (simp_all add:after_def)(*>*)


lemma (in TC0) pair_eq_ty\<^isub>i'_conv:
  "(\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST\<^isub>0 E A) =
  (case A of None \<Rightarrow> False | Some A \<Rightarrow> (ST = ST\<^isub>0 \<and> LT = ty\<^isub>l E A))"
(*<*)by(simp add:ty\<^isub>i'_def)(*>*)


lemma (in TC0) pair_conv_ty\<^isub>i':
  "\<lfloor>(ST, ty\<^isub>l E A)\<rfloor> = ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(simp add:ty\<^isub>i'_def)(*>*)

(*<*)
declare (in TC0)
  ty\<^isub>i'_antimono [intro!] after_def[simp]
  pair_conv_ty\<^isub>i'[simp] pair_eq_ty\<^isub>i'_conv[simp]
(*>*)


lemma (in TC1) compT_LT_prefix:
 "\<And>E A ST\<^isub>0. \<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST\<^isub>0 e); \<B> e (size E) \<rbrakk>
               \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^isub>i' ST E A"
and
 "\<And>E A ST\<^isub>0. \<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST\<^isub>0 es); \<B>s es (size E) \<rbrakk>
               \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^isub>i' ST E A"
(*<*)
proof(induct e and es)
  case FAss thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case BinOp thus ?case
    by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans split:bop.splits)
next
  case Seq thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case While thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cond thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Block thus ?case
    by(force simp add:hyperset_defs ty\<^isub>i'_def simp del:pair_conv_ty\<^isub>i'
             elim!:sup_state_opt_trans)
next
  case Call thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cons_exp thus ?case
    by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case TryCatch thus ?case
    by(fastsimp simp:hyperset_defs intro!:(* ty\<^isub>i'_env_antimono *) ty\<^isub>i'_incr
                elim!:sup_state_opt_trans)
qed (auto simp:hyperset_defs)

declare (in TC0)
  ty\<^isub>i'_antimono [rule del] after_def[simp del]
  pair_conv_ty\<^isub>i'[simp del] pair_eq_ty\<^isub>i'_conv[simp del]
(*>*)


lemma [iff]: "OK None \<in> states P mxs mxl"
(*<*)by(simp add: JVM_states_unfold)(*>*)

lemma (in TC0) after_in_states:
 "\<lbrakk> wf_prog p P; P,E \<turnstile>\<^sub>1 e :: T; set E \<subseteq> types P; set ST \<subseteq> types P;
    size ST + max_stack e \<le> mxs \<rbrakk>
 \<Longrightarrow> OK (after E A ST e) \<in> states P mxs mxl"
(*<*)
apply(subgoal_tac "size ST + 1 \<le> mxs")
 apply(simp add: after_def ty\<^isub>i'_def JVM_states_unfold ty\<^isub>l_in_types)
 apply(blast intro!:listI WT\<^isub>1_is_type)
using max_stack1[of e] apply simp
done
(*>*)


lemma (in TC0) OK_ty\<^isub>i'_in_statesI[simp]:
  "\<lbrakk> set E \<subseteq> types P; set ST \<subseteq> types P; size ST \<le> mxs \<rbrakk>
  \<Longrightarrow> OK (ty\<^isub>i' ST E A) \<in> states P mxs mxl"
(*<*)
apply(simp add:ty\<^isub>i'_def JVM_states_unfold ty\<^isub>l_in_types)
apply(blast intro!:listI)
done
(*>*)


lemma is_class_type_aux: "is_class P C \<Longrightarrow> is_type P (Class C)"
(*<*)by(simp)(*>*)

(*<*)
declare is_type_simps[simp del] subsetI[rule del]
(*>*)

theorem (in TC1) compT_states:
assumes wf: "wf_prog p P"
shows "\<And>E T A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 e :: T; set E \<subseteq> types P; set ST \<subseteq> types P;
    size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compT E A ST e) \<subseteq> states P mxs mxl"
(*<*)(is "\<And>E T A ST. PROP ?P e E T A ST")(*>*)

and "\<And>E Ts A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 es[::]Ts;  set E \<subseteq> types P; set ST \<subseteq> types P;
    size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compTs E A ST es) \<subseteq> states P mxs mxl"
(*<*)(is "\<And>E Ts A ST. PROP ?Ps es E Ts A ST")
proof(induct e and es)
  case new thus ?case by(simp)
next
  case (Cast C e) thus ?case by (auto simp:after_in_states[OF wf])
next
  case Val thus  ?case by(simp)
next
  case Var thus ?case by(simp)
next
  case LAss thus ?case  by(auto simp:after_in_states[OF wf])
next
  case FAcc thus ?case by(auto simp:after_in_states[OF wf])
next
  case FAss thus ?case
    by(auto simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Seq thus ?case
    by(auto simp:image_Un after_in_states[OF wf])
next
  case BinOp thus ?case
    by(auto simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Cond thus ?case
    by(force simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case While thus ?case
    by(auto simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Block thus ?case by(auto)
next
  case (TryCatch e\<^isub>1 C i e\<^isub>2)
  moreover have "size ST + 1 \<le> mxs" using TryCatch.prems max_stack1[of e\<^isub>1] by auto
  ultimately show ?case  
    by(auto simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf]
                  is_class_type_aux)
next
  case Nil_exp thus ?case by simp
next
  case Cons_exp thus ?case
    by(auto simp:image_Un  WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case throw thus ?case
    by(auto simp: WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Call thus ?case
    by(auto simp:image_Un WT\<^isub>1_is_type[OF wf] after_in_states[OF wf])
qed

declare is_type_simps[simp] subsetI[intro!]
(*>*)


definition shift :: "nat \<Rightarrow> ex_table \<Rightarrow> ex_table"
where
  "shift n xt \<equiv> map (\<lambda>(from,to,C,handler,depth). (from+n,to+n,C,handler+n,depth)) xt"


lemma [simp]: "shift 0 xt = xt"
(*<*)by(induct xt)(auto simp:shift_def)(*>*)

lemma [simp]: "shift n [] = []"
(*<*)by(simp add:shift_def)(*>*)

lemma [simp]: "shift n (xt\<^isub>1 @ xt\<^isub>2) = shift n xt\<^isub>1 @ shift n xt\<^isub>2"
(*<*)by(simp add:shift_def)(*>*)

lemma [simp]: "shift m (shift n xt) = shift (m+n) xt"
(*<*)by(induct xt)(auto simp:shift_def)(*>*)

lemma [simp]: "pcs (shift n xt) = {pc+n|pc. pc \<in> pcs xt}"
(*<*)
apply(auto simp:shift_def pcs_def)
apply(rule_tac x = "x-n" in exI)
apply (force split:nat_diff_split)
done
(*>*)


lemma shift_compxE\<^isub>2:
shows "\<And>pc pc' d. shift pc (compxE\<^isub>2 e pc' d) = compxE\<^isub>2 e (pc' + pc) d"
and  "\<And>pc pc' d. shift pc (compxEs\<^isub>2 es pc' d) = compxEs\<^isub>2 es (pc' + pc) d"
(*<*)
apply(induct e and es)
apply(auto simp:shift_def add_ac)
done
(*>*)


lemma compxE\<^isub>2_size_convs[simp]:
shows "n \<noteq> 0 \<Longrightarrow> compxE\<^isub>2 e n d = shift n (compxE\<^isub>2 e 0 d)"
and "n \<noteq> 0 \<Longrightarrow> compxEs\<^isub>2 es n d = shift n (compxEs\<^isub>2 es 0 d)"
(*<*)by(simp_all add:shift_compxE\<^isub>2)(*>*)

locale TC2 = TC1 +
  fixes T\<^isub>r :: ty and mxs :: pc
begin

definition
  wt_instrs :: "instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i' list \<Rightarrow> bool"
    ("(\<turnstile> _, _ /[::]/ _)" [0,0,51] 50) where
  "\<turnstile> is,xt [::] \<tau>s \<longleftrightarrow> size is < size \<tau>s \<and> pcs xt \<subseteq> {0..<size is} \<and>
  (\<forall>pc< size is. P,T\<^isub>r,mxs,size \<tau>s,xt \<turnstile> is!pc,pc :: \<tau>s)"

end

notation TC2.wt_instrs ("(_,_,_ \<turnstile>/ _, _ /[::]/ _)" [50,50,50,50,50,51] 50)

(*<*)
lemmas (in TC2) wt_defs =
  wt_instrs_def wt_instr_def app_def eff_def norm_eff_def
(*>*)

lemma (in TC2) [simp]: "\<tau>s \<noteq> [] \<Longrightarrow> \<turnstile> [],[] [::] \<tau>s"
(*<*) by (simp add: wt_defs) (*>*)

lemma [simp]: "eff i P pc et None = []"
(*<*)by (simp add: Effect.eff_def)(*>*)

(*<*)
declare split_comp_eq[simp del]
(*>*)

lemma wt_instr_appR:
 "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s;
    pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s; mpc \<le> mpc' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc',xt \<turnstile> is!pc,pc :: \<tau>s@\<tau>s'"
(*<*)by (fastsimp simp:wt_instr_def app_def)(*>*)


lemma relevant_entries_shift [simp]:
  "relevant_entries P i (pc+n) (shift n xt) = shift n (relevant_entries P i pc xt)"
(*<*)
  apply (induct xt)
  apply (unfold relevant_entries_def shift_def) 
   apply simp
  apply (auto simp add: is_relevant_entry_def)
  done
(*>*)


lemma [simp]:
  "xcpt_eff i P (pc+n) \<tau> (shift n xt) =
   map (\<lambda>(pc,\<tau>). (pc + n, \<tau>)) (xcpt_eff i P pc \<tau> xt)"
(*<*)
apply(simp add: xcpt_eff_def)
apply(cases \<tau>)
apply(auto simp add: shift_def)
done
(*>*)


lemma  [simp]:
  "app\<^isub>i (i, P, pc, m, T, \<tau>) \<Longrightarrow>
   eff i P (pc+n) (shift n xt) (Some \<tau>) =
   map (\<lambda>(pc,\<tau>). (pc+n,\<tau>)) (eff i P pc xt (Some \<tau>))"
(*<*)
apply(simp add:eff_def norm_eff_def)
apply(cases "i",auto)
done
(*>*)


lemma [simp]:
  "xcpt_app i P (pc+n) mxs (shift n xt) \<tau> = xcpt_app i P pc mxs xt \<tau>"
(*<*)by (simp add: xcpt_app_def) (auto simp add: shift_def)(*>*)


lemma wt_instr_appL:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc + size \<tau>s',shift (size \<tau>s') xt \<turnstile> i,pc+size \<tau>s' :: \<tau>s'@\<tau>s"
(*<*)
apply(auto simp:wt_instr_def app_def)
prefer 2 apply(fast)
prefer 2 apply(fast)
apply(cases "i",auto)
done
(*>*)


lemma wt_instr_Cons:
  "\<lbrakk> P,T,m,mpc - 1,[] \<turnstile> i,pc - 1 :: \<tau>s;
     0 < pc; 0 < mpc; pc < size \<tau>s + 1; mpc \<le> size \<tau>s + 1 \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>#\<tau>s"
(*<*)
apply(drule wt_instr_appL[where \<tau>s' = "[\<tau>]"])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done
(*>*)


lemma wt_instr_append:
  "\<lbrakk> P,T,m,mpc - size \<tau>s',[] \<turnstile> i,pc - size \<tau>s' :: \<tau>s;
     size \<tau>s' \<le> pc; size \<tau>s' \<le> mpc; pc < size \<tau>s + size \<tau>s'; mpc \<le> size \<tau>s + size \<tau>s' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>s'@\<tau>s"
(*<*)
apply(drule wt_instr_appL[where \<tau>s' = \<tau>s'])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done
(*>*)


lemma xcpt_app_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_app i P pc mxs xt \<tau>"
(*<*)
by (auto simp add: xcpt_app_def relevant_entries_def is_relevant_entry_def pcs_def)
(*>*)


lemma xcpt_eff_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_eff i P pc \<tau> xt = []"
(*<*)
by (cases \<tau>)
   (auto simp add: is_relevant_entry_def xcpt_eff_def relevant_entries_def pcs_def
           intro!: filter_False)
(*>*)


lemma pcs_shift:
  "pc < n \<Longrightarrow> pc \<notin> pcs (shift n xt)" 
(*<*)by (auto simp add: shift_def pcs_def)(*>*)


lemma wt_instr_appRx:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s; pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt @ shift (size is) xt' \<turnstile> is!pc,pc :: \<tau>s"
(*<*)by (auto simp:wt_instr_def eff_def app_def xcpt_app_pcs xcpt_eff_pcs)(*>*)


lemma wt_instr_appLx: 
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc \<notin> pcs xt' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt'@xt \<turnstile> i,pc :: \<tau>s"
(*<*)by (auto simp:wt_instr_def app_def eff_def xcpt_app_pcs xcpt_eff_pcs)(*>*)


lemma (in TC2) wt_instrs_extR:
  "\<turnstile> is,xt [::] \<tau>s \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s @ \<tau>s'"
(*<*)by(auto simp add:wt_instrs_def wt_instr_appR)(*>*)


lemma (in TC2) wt_instrs_ext:
  "\<lbrakk> \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>2; size \<tau>s\<^isub>1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
(*<*)
apply(clarsimp simp:wt_instrs_def)
apply(rule conjI, fastsimp)
apply(rule conjI, fastsimp)
apply clarsimp
apply(rule conjI, fastsimp simp:wt_instr_appRx)
apply clarsimp
apply(erule_tac x = "pc - size is\<^isub>1" in allE)+
apply(thin_tac "?P \<longrightarrow> ?Q")
apply(erule impE, arith) 
apply(drule_tac \<tau>s' = "\<tau>s\<^isub>1" in wt_instr_appL)
  apply arith
 apply simp
apply(fastsimp simp add:add_commute intro!: wt_instr_appLx)
done
(*>*)

corollary (in TC2) wt_instrs_ext2:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>2; \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; size \<tau>s\<^isub>1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
(*<*)by(rule wt_instrs_ext)(*>*)


corollary (in TC2) wt_instrs_ext_prefix [trans]:
  "\<lbrakk> \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>3;
     size \<tau>s\<^isub>1 = size is\<^isub>1; \<tau>s\<^isub>3 \<le> \<tau>s\<^isub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
(*<*)by(bestsimp simp:prefix_def elim: wt_instrs_ext dest:wt_instrs_extR)(*>*)


corollary (in TC2) wt_instrs_app:
  assumes is\<^isub>1: "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@[\<tau>]"
  assumes is\<^isub>2: "\<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>2"
  assumes s: "size \<tau>s\<^isub>1 = size is\<^isub>1"
  shows "\<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>#\<tau>s\<^isub>2"
(*<*)
proof -
  from is\<^isub>1 have "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] (\<tau>s\<^isub>1@[\<tau>])@\<tau>s\<^isub>2"
    by (rule wt_instrs_extR)
  hence "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>#\<tau>s\<^isub>2" by simp
  from this is\<^isub>2 s show ?thesis by (rule wt_instrs_ext) 
qed
(*>*)


corollary (in TC2) wt_instrs_app_last[trans]:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>2; \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1;
     last \<tau>s\<^isub>1 = \<tau>;  size \<tau>s\<^isub>1 = size is\<^isub>1+1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
(*<*)
apply(cases \<tau>s\<^isub>1 rule:rev_cases)
 apply simp
apply(simp add:wt_instrs_app)
done
(*>*)


corollary (in TC2) wt_instrs_append_last[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s; P,T\<^isub>r,mxs,mpc,[] \<turnstile> i,pc :: \<tau>s;
     pc = size is; mpc = size \<tau>s; size is + 1 < size \<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> is@[i],xt [::] \<tau>s"
(*<*)
apply(clarsimp simp add:wt_instrs_def)
apply(rule conjI, fastsimp)
apply(fastsimp intro!:wt_instr_appLx[where xt = "[]",simplified]
               dest!:less_antisym)
done
(*>*)


corollary (in TC2) wt_instrs_app2:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>'#\<tau>s\<^isub>2;  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>#\<tau>s\<^isub>1@[\<tau>'];
     xt' = xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2;  size \<tau>s\<^isub>1+1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2,xt' [::] \<tau>#\<tau>s\<^isub>1@\<tau>'#\<tau>s\<^isub>2"
(*<*)using wt_instrs_app[where ?\<tau>s\<^isub>1.0 = "\<tau> # \<tau>s\<^isub>1"] by simp (*>*)


corollary (in TC2) wt_instrs_app2_simp[trans,simp]:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>'#\<tau>s\<^isub>2;  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>#\<tau>s\<^isub>1@[\<tau>']; size \<tau>s\<^isub>1+1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>1@\<tau>'#\<tau>s\<^isub>2"
(*<*)using wt_instrs_app[where ?\<tau>s\<^isub>1.0 = "\<tau> # \<tau>s\<^isub>1"] by simp(*>*)


corollary (in TC2) wt_instrs_Cons[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,xt [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>'#\<tau>s"
(*<*)
using wt_instrs_app2[where ?is\<^isub>1.0 = "[i]" and ?\<tau>s\<^isub>1.0 = "[]" and ?is\<^isub>2.0 = "is"
                      and ?xt\<^isub>1.0 = "[]"]
by simp


corollary (in TC2) wt_instrs_Cons2[trans]:
  assumes \<tau>s: "\<turnstile> is,xt [::] \<tau>s"
  assumes i: "P,T\<^isub>r,mxs,mpc,[] \<turnstile> i,0 :: \<tau>#\<tau>s"
  assumes mpc: "mpc = size \<tau>s + 1"
  shows "\<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>s"
(*<*)
proof -
  from \<tau>s have "\<tau>s \<noteq> []" by (auto simp: wt_instrs_def)
  with mpc i have "\<turnstile> [i],[] [::] [\<tau>]@\<tau>s" by (simp add: wt_instrs_def)
  with \<tau>s show ?thesis by (fastsimp dest: wt_instrs_ext)
qed
(*>*)


lemma (in TC2) wt_instrs_last_incr[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s@[\<tau>]; P \<turnstile> \<tau> \<le>' \<tau>' \<rbrakk> \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s@[\<tau>']"
(*<*)
apply(clarsimp simp add:wt_instrs_def wt_instr_def)
apply(rule conjI)
apply(fastsimp)
apply(clarsimp)
apply(rename_tac pc' tau')
apply(erule allE, erule (1) impE)
apply(clarsimp)
apply(drule (1) bspec)
apply(clarsimp)
apply(subgoal_tac "pc' = size \<tau>s")
prefer 2
apply(clarsimp simp:app_def)
apply(drule (1) bspec)
apply(clarsimp)
apply(auto elim!:sup_state_opt_trans)
done
(*>*)


lemma [iff]: "xcpt_app i P pc mxs [] \<tau>"
(*<*)by (simp add: xcpt_app_def relevant_entries_def)(*>*)


lemma [simp]: "xcpt_eff i P pc \<tau> [] = []"
(*<*)by (simp add: xcpt_eff_def relevant_entries_def)(*>*)


lemma (in TC2) wt_New:
  "\<lbrakk> is_class P C; size ST < mxs \<rbrakk> \<Longrightarrow>
   \<turnstile> [New C],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (Class C#ST) E A]"
(*<*)by(simp add:wt_defs ty\<^isub>i'_def)(*>*)


lemma (in TC2) wt_Cast:
  "is_class P C \<Longrightarrow>
   \<turnstile> [Checkcast C],[] [::] [ty\<^isub>i' (Class D # ST) E A, ty\<^isub>i' (Class C # ST) E A]"
(*<*)by(simp add: ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Push:
  "\<lbrakk> size ST < mxs; typeof v = Some T \<rbrakk>
  \<Longrightarrow> \<turnstile> [Push v],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (T#ST) E A]"
(*<*)by(simp add: ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Pop:
 "\<turnstile> [Pop],[] [::] (ty\<^isub>i' (T#ST) E A # ty\<^isub>i' ST E A # \<tau>s)"
(*<*)by(simp add: ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_CmpEq:
  "\<lbrakk> P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> [CmpEq],[] [::] [ty\<^isub>i' (T\<^isub>2 # T\<^isub>1 # ST) E A, ty\<^isub>i' (Boolean # ST) E A]"
(*<*) by(auto simp:ty\<^isub>i'_def wt_defs elim!: refTE not_refTE) (*>*)


lemma (in TC2) wt_IAdd:
  "\<turnstile> [IAdd],[] [::] [ty\<^isub>i' (Integer#Integer#ST) E A, ty\<^isub>i' (Integer#ST) E A]"
(*<*)by(simp add:ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Load:
  "\<lbrakk> size ST < mxs; size E \<le> mxl; i \<in>\<in> A; i < size E \<rbrakk>
  \<Longrightarrow> \<turnstile> [Load i],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (E!i # ST) E A]"
(*<*)by(auto simp add:ty\<^isub>i'_def wt_defs ty\<^isub>l_def hyperset_defs)(*>*)


lemma (in TC2) wt_Store:
 "\<lbrakk> P \<turnstile> T \<le> E!i; i < size E; size E \<le> mxl \<rbrakk> \<Longrightarrow>
  \<turnstile> [Store i],[] [::] [ty\<^isub>i' (T#ST) E A, ty\<^isub>i' ST E (\<lfloor>{i}\<rfloor> \<squnion> A)]"
(*<*)
by(auto simp:hyperset_defs nth_list_update ty\<^isub>i'_def wt_defs ty\<^isub>l_def
        intro:list_all2_all_nthI)
(*>*)


lemma (in TC2) wt_Get:
 "\<lbrakk> P \<turnstile> C sees F:T in D \<rbrakk> \<Longrightarrow>
  \<turnstile> [Getfield F D],[] [::] [ty\<^isub>i' (Class C # ST) E A, ty\<^isub>i' (T # ST) E A]"
(*<*)by(auto simp: ty\<^isub>i'_def wt_defs dest: sees_field_idemp sees_field_decl_above)(*>*)


lemma (in TC2) wt_Put:
  "\<lbrakk> P \<turnstile> C sees F:T in D; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow>
  \<turnstile> [Putfield F D],[] [::] [ty\<^isub>i' (T' # Class C # ST) E A, ty\<^isub>i' ST E A]"
(*<*)by(auto intro: sees_field_idemp sees_field_decl_above simp: ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Throw:
  "\<turnstile> [Throw],[] [::] [ty\<^isub>i' (Class C # ST) E A, \<tau>']"
(*<*)by(auto simp: ty\<^isub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_IfFalse:
  "\<lbrakk> 2 \<le> i; nat i < size \<tau>s + 2; P \<turnstile> ty\<^isub>i' ST E A \<le>' \<tau>s ! nat(i - 2) \<rbrakk>
  \<Longrightarrow> \<turnstile> [IfFalse i],[] [::] ty\<^isub>i' (Boolean # ST) E A # ty\<^isub>i' ST E A # \<tau>s"
(*<*)
apply(clarsimp simp add: ty\<^isub>i'_def wt_defs)
apply(auto simp add: nth_Cons split:nat.split)
apply(simp add:nat_diff_distrib)
done
(*>*)


lemma wt_Goto:
 "\<lbrakk> 0 \<le> int pc + i; nat (int pc + i) < size \<tau>s; size \<tau>s \<le> mpc;
    P \<turnstile> \<tau>s!pc \<le>' \<tau>s ! nat (int pc + i) \<rbrakk>
 \<Longrightarrow> P,T,mxs,mpc,[] \<turnstile> Goto i,pc :: \<tau>s"
(*<*)by(clarsimp simp add: TC2.wt_defs)(*>*)


lemma (in TC2) wt_Invoke:
  "\<lbrakk> size es = size Ts'; P \<turnstile> C sees M: Ts\<rightarrow>T = m in D; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> \<turnstile> [Invoke M (size es)],[] [::] [ty\<^isub>i' (rev Ts' @ Class C # ST) E A, ty\<^isub>i' (T#ST) E A]"
(*<*)by(fastsimp simp add: ty\<^isub>i'_def wt_defs)(*>*)


corollary (in TC2) wt_instrs_app3[simp]:
  "\<lbrakk> \<turnstile> is\<^isub>2,[] [::] (\<tau>' # \<tau>s\<^isub>2);  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau> # \<tau>s\<^isub>1 @ [\<tau>']; size \<tau>s\<^isub>1+1 = size is\<^isub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> (is\<^isub>1 @ is\<^isub>2),xt\<^isub>1 [::] \<tau> # \<tau>s\<^isub>1 @ \<tau>' # \<tau>s\<^isub>2"
(*<*)using wt_instrs_app2[where ?xt\<^isub>2.0 = "[]"] by (simp add:shift_def)(*>*)


corollary (in TC2) wt_instrs_Cons3[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,[] [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> (i # is),[] [::] \<tau> # \<tau>' # \<tau>s"
(*<*)
using wt_instrs_Cons[where ?xt = "[]"]
by (simp add:shift_def)

(*<*)
declare nth_append[simp del]
(*>*)

lemma (in TC2) wt_instrs_xapp[trans]:
  "\<lbrakk> \<turnstile> is\<^isub>1 @ is\<^isub>2, xt [::] \<tau>s\<^isub>1 @ ty\<^isub>i' (Class C # ST) E A # \<tau>s\<^isub>2;
     \<forall>\<tau> \<in> set \<tau>s\<^isub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
      size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^isub>i' ST E A;
     size is\<^isub>1 = size \<tau>s\<^isub>1; is_class P C; size ST < mxs  \<rbrakk> \<Longrightarrow>
  \<turnstile> is\<^isub>1 @ is\<^isub>2, xt @ [(0,size is\<^isub>1 - 1,C,size is\<^isub>1,size ST)] [::] \<tau>s\<^isub>1 @ ty\<^isub>i' (Class C # ST) E A # \<tau>s\<^isub>2"
(*<*)
apply(simp add:wt_instrs_def)
apply(rule conjI)
 apply(clarsimp)
 apply arith
apply clarsimp
apply(erule allE, erule (1) impE)
apply(clarsimp simp add: wt_instr_def app_def eff_def)
apply(rule conjI)
 apply (thin_tac "\<forall>x\<in> ?A \<union> ?B. ?P x")
 apply (thin_tac "\<forall>x\<in> ?A \<union> ?B. ?P x")
 apply (clarsimp simp add: xcpt_app_def relevant_entries_def)
 apply (simp add: nth_append is_relevant_entry_def split: split_if_asm)
  apply (drule_tac x="\<tau>s\<^isub>1!pc" in bspec)
   apply (blast intro: nth_mem) 
  apply fastsimp   
apply (rule conjI)
 apply clarsimp
 apply (erule disjE, blast)
 apply (erule disjE, blast)
 apply (clarsimp simp add: xcpt_eff_def relevant_entries_def split: split_if_asm)
apply clarsimp
apply (erule disjE, blast)
apply (erule disjE, blast)
apply (clarsimp simp add: xcpt_eff_def relevant_entries_def split: split_if_asm)
apply (simp add: nth_append is_relevant_entry_def split: split_if_asm)
 apply (drule_tac x = "\<tau>s\<^isub>1!pc" in bspec)
  apply (blast intro: nth_mem) 
 apply (fastsimp simp add: ty\<^isub>i'_def)
done

declare nth_append[simp]
(*>*)

lemma drop_Cons_Suc:
  "\<And>xs. drop n xs = y#ys \<Longrightarrow> drop (Suc n) xs = ys"
  apply (induct n)
   apply simp
  apply (simp add: drop_Suc)
  done

lemma drop_mess:
  "\<lbrakk>Suc (length xs\<^isub>0) \<le> length xs; drop (length xs - Suc (length xs\<^isub>0)) xs = x # xs\<^isub>0\<rbrakk> 
  \<Longrightarrow> drop (length xs - length xs\<^isub>0) xs = xs\<^isub>0"
apply (cases xs)
 apply simp
apply (simp add: Suc_diff_le)
apply (case_tac "length list - length xs\<^isub>0")
 apply simp
apply (simp add: drop_Cons_Suc)
done

(*<*)
declare (in TC0)
  after_def[simp] pair_eq_ty\<^isub>i'_conv[simp]
(*>*)

lemma (in TC1) compT_ST_prefix:
 "\<And>E A ST\<^isub>0. \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST\<^isub>0 e) \<Longrightarrow> 
  size ST\<^isub>0 \<le> size ST \<and> drop (size ST - size ST\<^isub>0) ST = ST\<^isub>0"
and
 "\<And>E A ST\<^isub>0. \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST\<^isub>0 es) \<Longrightarrow> 
  size ST\<^isub>0 \<le> size ST \<and> drop (size ST - size ST\<^isub>0) ST = ST\<^isub>0"
(*<*)
proof(induct e and es)
  case (FAss e\<^isub>1 F D e\<^isub>2)
  moreover {
    let ?ST\<^isub>0 = "ty E e\<^isub>1 # ST\<^isub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST\<^isub>0 e\<^isub>2)"
    with FAss
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case TryCatch thus ?case by auto
next
  case Block thus ?case by auto
next
  case Seq thus ?case by auto
next
  case While thus ?case by auto
next
  case Cond thus ?case by auto
next
  case (Call e M es)
  moreover {
    let ?ST\<^isub>0 = "ty E e # ST\<^isub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^isub>0 es)"
    with Call
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (Cons_exp e es)
  moreover {
    let ?ST\<^isub>0 = "ty E e # ST\<^isub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^isub>0 es)"
    with Cons_exp
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (BinOp e\<^isub>1 bop e\<^isub>2)
  moreover {
    let ?ST\<^isub>0 = "ty E e\<^isub>1 # ST\<^isub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST\<^isub>0 e\<^isub>2)"
    with BinOp 
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case new thus ?case by auto
next
  case Val thus ?case by auto    
next
  case Cast thus ?case by auto
next
  case Var thus ?case by auto
next
  case LAss thus ?case by auto
next
  case throw thus ?case by auto
next
  case FAcc thus ?case by auto
next
  case Nil_exp thus ?case by auto
qed 

declare (in TC0) 
  after_def[simp del] pair_eq_ty\<^isub>i'_conv[simp del]
(*>*)

(* FIXME *)
lemma fun_of_simp [simp]: "fun_of S x y = ((x,y) \<in> S)" 
(*<*) by (simp add: fun_of_def)(*>*)

theorem (in TC2) compT_wt_instrs: "\<And>E T A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 e :: T; \<D> e A; \<B> e (size E); 
    size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl \<rbrakk>
  \<Longrightarrow> \<turnstile> compE\<^isub>2 e, compxE\<^isub>2 e 0 (size ST) [::]
                 ty\<^isub>i' ST E A # compT E A ST e @ [after E A ST e]"
(*<*)(is "\<And>E T A ST. PROP ?P e E T A ST")(*>*)

and "\<And>E Ts A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 es[::]Ts;  \<D>s es A; \<B>s es (size E); 
    size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl \<rbrakk>
  \<Longrightarrow> let \<tau>s = ty\<^isub>i' ST E A # compTs E A ST es in
       \<turnstile> compEs\<^isub>2 es,compxEs\<^isub>2 es 0 (size ST) [::] \<tau>s \<and>
       last \<tau>s = ty\<^isub>i' (rev Ts @ ST) E (A \<squnion> \<A>s es)"
(*<*)
(is "\<And>E Ts A ST. PROP ?Ps es E Ts A ST")
proof(induct e and es)
  case (TryCatch e\<^isub>1 C i e\<^isub>2)
  hence [simp]: "i = size E" by simp
  have wt\<^isub>1: "P,E \<turnstile>\<^sub>1 e\<^isub>1 :: T" and wt\<^isub>2: "P,E@[Class C] \<turnstile>\<^sub>1 e\<^isub>2 :: T"
    and "class": "is_class P C" using TryCatch by auto
  let ?A\<^isub>1 = "A \<squnion> \<A> e\<^isub>1" let ?A\<^isub>i = "A \<squnion> \<lfloor>{i}\<rfloor>" let ?E\<^isub>i = "E @ [Class C]"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>1 = "compT E A ST e\<^isub>1"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (T#ST) E ?A\<^isub>1" let ?\<tau>\<^isub>2 = "ty\<^isub>i' (Class C#ST) E A"
  let ?\<tau>\<^isub>3 = "ty\<^isub>i' ST ?E\<^isub>i ?A\<^isub>i" let ?\<tau>s\<^isub>2 = "compT ?E\<^isub>i ?A\<^isub>i ST e\<^isub>2"
  let ?\<tau>\<^isub>2' = "ty\<^isub>i' (T#ST) ?E\<^isub>i (?A\<^isub>i \<squnion> \<A> e\<^isub>2)"
  let ?\<tau>' = "ty\<^isub>i' (T#ST) E (A \<squnion> \<A> e\<^isub>1 \<sqinter> (\<A> e\<^isub>2 \<ominus> i))"
  let ?go = "Goto (int(size(compE\<^isub>2 e\<^isub>2)) + 2)"
  have "PROP ?P e\<^isub>2 ?E\<^isub>i T ?A\<^isub>i ST" by fact
  hence "\<turnstile> compE\<^isub>2 e\<^isub>2,compxE\<^isub>2 e\<^isub>2 0 (size ST) [::] (?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2) @ [?\<tau>\<^isub>2']"
    using TryCatch.prems by(auto simp:after_def)
  also have "?A\<^isub>i \<squnion> \<A> e\<^isub>2 = (A \<squnion> \<A> e\<^isub>2) \<squnion> \<lfloor>{size E}\<rfloor>"
    by(fastsimp simp:hyperset_defs)
  also have "P \<turnstile> ty\<^isub>i' (T#ST) ?E\<^isub>i \<dots> \<le>' ty\<^isub>i' (T#ST) E (A \<squnion> \<A> e\<^isub>2)"
    by(simp add:hyperset_defs ty\<^isub>l_incr ty\<^isub>i'_def)
  also have "P \<turnstile> \<dots> \<le>' ty\<^isub>i' (T#ST) E (A \<squnion> \<A> e\<^isub>1 \<sqinter> (\<A> e\<^isub>2 \<ominus> i))"
    by(auto intro!: ty\<^isub>l_antimono simp:hyperset_defs ty\<^isub>i'_def)
  also have "(?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2) @ [?\<tau>'] = ?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>']" by simp
  also have "\<turnstile> [Store i],[] [::] ?\<tau>\<^isub>2 # [] @ [?\<tau>\<^isub>3]"
    using TryCatch.prems
    by(auto simp:nth_list_update wt_defs ty\<^isub>i'_def ty\<^isub>l_def
      list_all2_conv_all_nth hyperset_defs)
  also have "[] @ (?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>']) = (?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>'])" by simp
  also have "P,T\<^isub>r,mxs,size(compE\<^isub>2 e\<^isub>2)+3,[] \<turnstile> ?go,0 :: ?\<tau>\<^isub>1#?\<tau>\<^isub>2#?\<tau>\<^isub>3#?\<tau>s\<^isub>2 @ [?\<tau>']"
    by (auto simp: hyperset_defs ty\<^isub>i'_def wt_defs nth_Cons nat_add_distrib
      fun_of_def intro: ty\<^isub>l_antimono list_all2_refl split:nat.split)
  also have "\<turnstile> compE\<^isub>2 e\<^isub>1,compxE\<^isub>2 e\<^isub>1 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>1]"
    using TryCatch by(auto simp:after_def)
  also have "?\<tau> # ?\<tau>s\<^isub>1 @ ?\<tau>\<^isub>1 # ?\<tau>\<^isub>2 # ?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>'] =
             (?\<tau> # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>1]) @ ?\<tau>\<^isub>2 # ?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>']" by simp
  also have "compE\<^isub>2 e\<^isub>1 @ ?go  # [Store i] @ compE\<^isub>2 e\<^isub>2 =
             (compE\<^isub>2 e\<^isub>1 @ [?go]) @ (Store i # compE\<^isub>2 e\<^isub>2)" by simp
  also 
  let "?Q \<tau>" = "\<forall>ST' LT'. \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> 
    size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^isub>i' ST E A"
  {
    have "?Q (ty\<^isub>i' ST E A)" by (clarsimp simp add: ty\<^isub>i'_def)
    moreover have "?Q (ty\<^isub>i' (T # ST) E ?A\<^isub>1)" 
      by (fastsimp simp add: ty\<^isub>i'_def hyperset_defs intro!: ty\<^isub>l_antimono)
    moreover have "\<And>\<tau>. \<tau> \<in> set (compT E A ST e\<^isub>1) \<Longrightarrow> ?Q \<tau>" using TryCatch.prems
      by clarsimp (frule compT_ST_prefix,
                   fastsimp dest!: compT_LT_prefix simp add: ty\<^isub>i'_def)
    ultimately
    have "\<forall>\<tau>\<in>set (ty\<^isub>i' ST E A # compT E A ST e\<^isub>1 @ [ty\<^isub>i' (T # ST) E ?A\<^isub>1]). ?Q \<tau>" 
      by auto
  }
  also from TryCatch.prems max_stack1[of e\<^isub>1] have "size ST + 1 \<le> mxs" by auto
  ultimately show ?case using wt\<^isub>1 wt\<^isub>2 TryCatch.prems "class"
    by (simp add:after_def)
next
  case new thus ?case by(auto simp add:after_def wt_New)
next
  case (BinOp e\<^isub>1 bop e\<^isub>2) 
  let ?op = "case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]"
  have T: "P,E \<turnstile>\<^sub>1 e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T" by fact
  then obtain T\<^isub>1 T\<^isub>2 where T\<^isub>1: "P,E \<turnstile>\<^sub>1 e\<^isub>1 :: T\<^isub>1" and T\<^isub>2: "P,E \<turnstile>\<^sub>1 e\<^isub>2 :: T\<^isub>2" and 
    bopT: "case bop of Eq \<Rightarrow> (P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1) \<and> T = Boolean 
                    | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer" by auto
  let ?A\<^isub>1 = "A \<squnion> \<A> e\<^isub>1" let ?A\<^isub>2 = "?A\<^isub>1 \<squnion> \<A> e\<^isub>2"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>1 = "compT E A ST e\<^isub>1"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (T\<^isub>1#ST) E ?A\<^isub>1" let ?\<tau>s\<^isub>2 = "compT E ?A\<^isub>1 (T\<^isub>1#ST) e\<^isub>2"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' (T\<^isub>2#T\<^isub>1#ST) E ?A\<^isub>2" let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A\<^isub>2"
  from bopT have "\<turnstile> ?op,[] [::] [?\<tau>\<^isub>2,?\<tau>']" 
    by (cases bop) (auto simp add: wt_CmpEq wt_IAdd)
  also have "PROP ?P e\<^isub>2 E T\<^isub>2 ?A\<^isub>1 (T\<^isub>1#ST)" by fact
  with BinOp.prems T\<^isub>2 
  have "\<turnstile> compE\<^isub>2 e\<^isub>2, compxE\<^isub>2 e\<^isub>2 0 (size (T\<^isub>1#ST)) [::] ?\<tau>\<^isub>1#?\<tau>s\<^isub>2@[?\<tau>\<^isub>2]" 
    by (auto simp: after_def)
  also from BinOp T\<^isub>1 have "\<turnstile> compE\<^isub>2 e\<^isub>1, compxE\<^isub>2 e\<^isub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>1@[?\<tau>\<^isub>1]" 
    by (auto simp: after_def)
  finally show ?case using T T\<^isub>1 T\<^isub>2 by (simp add: after_def hyperUn_assoc)
next
  case (Cons_exp e es)
  have "P,E \<turnstile>\<^sub>1 e # es [::] Ts" by fact
  then obtain T\<^isub>e Ts' where 
    T\<^isub>e: "P,E \<turnstile>\<^sub>1 e :: T\<^isub>e" and Ts': "P,E \<turnstile>\<^sub>1 es [::] Ts'" and
    Ts: "Ts = T\<^isub>e#Ts'" by auto
  let ?A\<^isub>e = "A \<squnion> \<A> e"  
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>e = "compT E A ST e"  
  let ?\<tau>\<^isub>e = "ty\<^isub>i' (T\<^isub>e#ST) E ?A\<^isub>e" let ?\<tau>s' = "compTs E ?A\<^isub>e (T\<^isub>e#ST) es"
  let ?\<tau>s = "?\<tau> # ?\<tau>s\<^isub>e @ (?\<tau>\<^isub>e # ?\<tau>s')"
  have Ps: "PROP ?Ps es E Ts' ?A\<^isub>e (T\<^isub>e#ST)" by fact
  with Cons_exp.prems T\<^isub>e Ts'
  have "\<turnstile> compEs\<^isub>2 es, compxEs\<^isub>2 es 0 (size (T\<^isub>e#ST)) [::] ?\<tau>\<^isub>e#?\<tau>s'" by (simp add: after_def)
  also from Cons_exp T\<^isub>e have "\<turnstile> compE\<^isub>2 e, compxE\<^isub>2 e 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>e@[?\<tau>\<^isub>e]" 
    by (auto simp: after_def)
  moreover
  from Ps Cons_exp.prems T\<^isub>e Ts' Ts
  have "last ?\<tau>s = ty\<^isub>i' (rev Ts@ST) E (?A\<^isub>e \<squnion> \<A>s es)" by simp
  ultimately show ?case using T\<^isub>e by (simp add: after_def hyperUn_assoc)
next
  case (FAss e\<^isub>1 F D e\<^isub>2)
  hence Void: "P,E \<turnstile>\<^sub>1 e\<^isub>1\<bullet>F{D} := e\<^isub>2 :: Void" by auto
  then obtain C T T' where    
    C: "P,E \<turnstile>\<^sub>1 e\<^isub>1 :: Class C" and sees: "P \<turnstile> C sees F:T in D" and
    T': "P,E \<turnstile>\<^sub>1 e\<^isub>2 :: T'" and T'_T: "P \<turnstile> T' \<le> T" by auto
  let ?A\<^isub>1 = "A \<squnion> \<A> e\<^isub>1" let ?A\<^isub>2 = "?A\<^isub>1 \<squnion> \<A> e\<^isub>2"  
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>1 = "compT E A ST e\<^isub>1"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (Class C#ST) E ?A\<^isub>1" let ?\<tau>s\<^isub>2 = "compT E ?A\<^isub>1 (Class C#ST) e\<^isub>2"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' (T'#Class C#ST) E ?A\<^isub>2" let ?\<tau>\<^isub>3 = "ty\<^isub>i' ST E ?A\<^isub>2"
  let ?\<tau>' = "ty\<^isub>i' (Void#ST) E ?A\<^isub>2"
  from FAss.prems sees T'_T 
  have "\<turnstile> [Putfield F D,Push Unit],[] [::] [?\<tau>\<^isub>2,?\<tau>\<^isub>3,?\<tau>']"
    by (fastsimp simp add: wt_Push wt_Put)
  also have "PROP ?P e\<^isub>2 E T' ?A\<^isub>1 (Class C#ST)" by fact
  with FAss.prems T' 
  have "\<turnstile> compE\<^isub>2 e\<^isub>2, compxE\<^isub>2 e\<^isub>2 0 (size ST+1) [::] ?\<tau>\<^isub>1#?\<tau>s\<^isub>2@[?\<tau>\<^isub>2]"
    by (auto simp add: after_def hyperUn_assoc) 
  also from FAss C have "\<turnstile> compE\<^isub>2 e\<^isub>1, compxE\<^isub>2 e\<^isub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>1@[?\<tau>\<^isub>1]" 
    by (auto simp add: after_def)
  finally show ?case using Void C T' by (simp add: after_def hyperUn_assoc) 
next
  case Val thus ?case by(auto simp:after_def wt_Push)
next
  case Cast thus ?case by (auto simp:after_def wt_Cast)
next
  case (Block i T\<^isub>i e)
  let ?\<tau>s = "ty\<^isub>i' ST E A # compT (E @ [T\<^isub>i]) (A\<ominus>i) ST e"
  have IH: "PROP ?P e (E@[T\<^isub>i]) T (A\<ominus>i) ST" by fact
  hence "\<turnstile> compE\<^isub>2 e, compxE\<^isub>2 e 0 (size ST) [::]
         ?\<tau>s @ [ty\<^isub>i' (T#ST) (E@[T\<^isub>i]) (A\<ominus>(size E) \<squnion> \<A> e)]"
    using Block.prems by (auto simp add: after_def)
  also have "P \<turnstile> ty\<^isub>i' (T # ST) (E@[T\<^isub>i]) (A \<ominus> size E \<squnion> \<A> e) \<le>'
                 ty\<^isub>i' (T # ST) (E@[T\<^isub>i]) ((A \<squnion> \<A> e) \<ominus> size E)"
     by(auto simp add:hyperset_defs intro: ty\<^isub>i'_antimono)
  also have "\<dots> = ty\<^isub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
  also have "P \<turnstile> \<dots> \<le>' ty\<^isub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
     by(auto simp add:hyperset_defs intro: ty\<^isub>i'_antimono)
  finally show ?case using Block.prems by(simp add: after_def)
next
  case Var thus ?case by(auto simp:after_def wt_Load)
next
  case FAcc thus ?case by(auto simp:after_def wt_Get)
next
  case (LAss i e) thus ?case using max_stack1[of e]
    by(auto simp: hyper_insert_comm after_def wt_Store wt_Push)
next
  case Nil_exp thus ?case by auto
next
  case throw thus ?case by(auto simp add: after_def wt_Throw)
next
  case (While e c)
  obtain Tc where wte: "P,E \<turnstile>\<^sub>1 e :: Boolean" and wtc: "P,E \<turnstile>\<^sub>1 c :: Tc"
    and [simp]: "T = Void" using While by auto
  have [simp]: "ty E (while (e) c) = Void" using While by simp
  let ?A\<^isub>0 = "A \<squnion> \<A> e" let ?A\<^isub>1 = "?A\<^isub>0 \<squnion> \<A> c"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>e = "compT E A ST e"
  let ?\<tau>\<^isub>e = "ty\<^isub>i' (Boolean#ST) E ?A\<^isub>0" let ?\<tau>\<^isub>1 = "ty\<^isub>i' ST E ?A\<^isub>0"
  let ?\<tau>s\<^isub>c = "compT E ?A\<^isub>0 ST c" let ?\<tau>\<^isub>c = "ty\<^isub>i' (Tc#ST) E ?A\<^isub>1"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' ST E ?A\<^isub>1" let ?\<tau>' = "ty\<^isub>i' (Void#ST) E ?A\<^isub>0"
  let ?\<tau>s = "(?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]) @ ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2, ?\<tau>\<^isub>1, ?\<tau>']"
  have "\<turnstile> [],[] [::] [] @ ?\<tau>s" by(simp add:wt_instrs_def)
  also
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE\<^isub>2 e,compxE\<^isub>2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]"
    using While.prems by (auto simp:after_def)
  also
  have "[] @ ?\<tau>s = (?\<tau> # ?\<tau>s\<^isub>e) @ ?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c,?\<tau>\<^isub>2,?\<tau>\<^isub>1,?\<tau>']" by simp
  also
  let ?n\<^isub>e = "size(compE\<^isub>2 e)"  let ?n\<^isub>c = "size(compE\<^isub>2 c)"
  let ?if = "IfFalse (int ?n\<^isub>c + 3)"
  have "\<turnstile> [?if],[] [::] ?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2, ?\<tau>\<^isub>1, ?\<tau>']"
    by(simp add: wt_instr_Cons wt_instr_append wt_IfFalse
                 nat_add_distrib split: nat_diff_split)
  also
  have "(?\<tau> # ?\<tau>s\<^isub>e) @ (?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2, ?\<tau>\<^isub>1, ?\<tau>']) = ?\<tau>s" by simp
  also
  have "PROP ?P c E Tc ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE\<^isub>2 c,compxE\<^isub>2 c 0 (size ST) [::] ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c]"
    using While.prems wtc by (auto simp:after_def)
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e,?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>c) @ [?\<tau>\<^isub>c,?\<tau>\<^isub>2,?\<tau>\<^isub>1,?\<tau>']" by simp
  also have "\<turnstile> [Pop],[] [::] [?\<tau>\<^isub>c, ?\<tau>\<^isub>2]"  by(simp add:wt_Pop)
  also have "(?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e,?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>c) @ [?\<tau>\<^isub>c,?\<tau>\<^isub>2,?\<tau>\<^isub>1,?\<tau>'] = ?\<tau>s" by simp
  also let ?go = "Goto (-int(?n\<^isub>c+?n\<^isub>e+2))"
  have "P \<turnstile> ?\<tau>\<^isub>2 \<le>' ?\<tau>" by(fastsimp intro: ty\<^isub>i'_antimono simp: hyperset_defs)
  hence "P,T\<^isub>r,mxs,size ?\<tau>s,[] \<turnstile> ?go,?n\<^isub>e+?n\<^isub>c+2 :: ?\<tau>s"
    by(simp add: wt_Goto split: nat_diff_split)
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e,?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2]) @ [?\<tau>\<^isub>1, ?\<tau>']"
    by simp
  also have "\<turnstile> [Push Unit],[] [::] [?\<tau>\<^isub>1,?\<tau>']"
    using While.prems max_stack1[of c] by(auto simp add:wt_Push)
  finally show ?case using wtc wte
    by (simp add:after_def)
next
  case (Cond e e\<^isub>1 e\<^isub>2)
  obtain T\<^isub>1 T\<^isub>2 where wte: "P,E \<turnstile>\<^sub>1 e :: Boolean"
    and wt\<^isub>1: "P,E \<turnstile>\<^sub>1 e\<^isub>1 :: T\<^isub>1" and wt\<^isub>2: "P,E \<turnstile>\<^sub>1 e\<^isub>2 :: T\<^isub>2"
    and sub\<^isub>1: "P \<turnstile> T\<^isub>1 \<le> T" and sub\<^isub>2: "P \<turnstile> T\<^isub>2 \<le> T"
    using Cond by auto
  have [simp]: "ty E (if (e) e\<^isub>1 else e\<^isub>2) = T" using Cond by simp
  let ?A\<^isub>0 = "A \<squnion> \<A> e" let ?A\<^isub>2 = "?A\<^isub>0 \<squnion> \<A> e\<^isub>2" let ?A\<^isub>1 = "?A\<^isub>0 \<squnion> \<A> e\<^isub>1"
  let ?A' = "?A\<^isub>0 \<squnion> \<A> e\<^isub>1 \<sqinter> \<A> e\<^isub>2"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' ST E ?A\<^isub>0" let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A'"
  let ?\<tau>s\<^isub>2 = "compT E ?A\<^isub>0 ST e\<^isub>2"
  have "PROP ?P e\<^isub>2 E T\<^isub>2 ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE\<^isub>2 e\<^isub>2, compxE\<^isub>2 e\<^isub>2 0 (size ST) [::] (?\<tau>\<^isub>2#?\<tau>s\<^isub>2) @ [ty\<^isub>i' (T\<^isub>2#ST) E ?A\<^isub>2]"
    using Cond.prems wt\<^isub>2 by(auto simp add:after_def)
  also have "P \<turnstile> ty\<^isub>i' (T\<^isub>2#ST) E ?A\<^isub>2 \<le>' ?\<tau>'" using sub\<^isub>2
    by(auto simp add: hyperset_defs ty\<^isub>i'_def intro!: ty\<^isub>l_antimono)
  also
  let ?\<tau>\<^isub>3 = "ty\<^isub>i' (T\<^isub>1 # ST) E ?A\<^isub>1"
  let ?g\<^isub>2 = "Goto(int (size (compE\<^isub>2 e\<^isub>2) + 1))"
  from sub\<^isub>1 have "P,T\<^isub>r,mxs,size(compE\<^isub>2 e\<^isub>2)+2,[] \<turnstile> ?g\<^isub>2,0 :: ?\<tau>\<^isub>3#(?\<tau>\<^isub>2#?\<tau>s\<^isub>2)@[?\<tau>']"
    by(auto simp: hyperset_defs wt_defs nth_Cons ty\<^isub>i'_def
             split:nat.split intro!: ty\<^isub>l_antimono)
  also
  let ?\<tau>s\<^isub>1 = "compT E ?A\<^isub>0 ST e\<^isub>1"
  have "PROP ?P e\<^isub>1 E T\<^isub>1 ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE\<^isub>2 e\<^isub>1,compxE\<^isub>2 e\<^isub>1 0 (size ST) [::] ?\<tau>\<^isub>2 # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>3]"
    using Cond.prems wt\<^isub>1 by(auto simp add:after_def)
  also
  let ?\<tau>s\<^isub>1\<^isub>2 = "?\<tau>\<^isub>2 # ?\<tau>s\<^isub>1 @ ?\<tau>\<^isub>3 # (?\<tau>\<^isub>2 # ?\<tau>s\<^isub>2) @ [?\<tau>']"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (Boolean#ST) E ?A\<^isub>0"
  let ?g\<^isub>1 = "IfFalse(int (size (compE\<^isub>2 e\<^isub>1) + 2))"
  let ?code = "compE\<^isub>2 e\<^isub>1 @ ?g\<^isub>2 # compE\<^isub>2 e\<^isub>2"
  have "\<turnstile> [?g\<^isub>1],[] [::] [?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>1\<^isub>2"
    by(simp add: wt_IfFalse nat_add_distrib split:nat_diff_split)
  also (wt_instrs_ext2) have "[?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>1\<^isub>2 = ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>1\<^isub>2" by simp also
  let ?\<tau> = "ty\<^isub>i' ST E A"
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE\<^isub>2 e, compxE\<^isub>2 e 0 (size ST) [::] ?\<tau> # compT E A ST e @ [?\<tau>\<^isub>1]"
    using Cond.prems wte by(auto simp add:after_def)
  finally show ?case using wte wt\<^isub>1 wt\<^isub>2 by(simp add:after_def hyperUn_assoc)
next
  case (Call e M es)
  obtain C D Ts m Ts' where C: "P,E \<turnstile>\<^sub>1 e :: Class C"
    and method: "P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"
    and wtes: "P,E \<turnstile>\<^sub>1 es [::] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
    using Call.prems by auto
  from wtes have same_size: "size es = size Ts'" by(rule WTs\<^isub>1_same_size)
  let ?A\<^isub>0 = "A \<squnion> \<A> e" let ?A\<^isub>1 = "?A\<^isub>0 \<squnion> \<A>s es"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>e = "compT E A ST e"
  let ?\<tau>\<^isub>e = "ty\<^isub>i' (Class C # ST) E ?A\<^isub>0"
  let ?\<tau>s\<^isub>e\<^isub>s = "compTs E ?A\<^isub>0 (Class C # ST) es"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (rev Ts' @ Class C # ST) E ?A\<^isub>1"
  let ?\<tau>' = "ty\<^isub>i' (T # ST) E ?A\<^isub>1"
  have "\<turnstile> [Invoke M (size es)],[] [::] [?\<tau>\<^isub>1,?\<tau>']"
    by(rule wt_Invoke[OF same_size method subs])
  also
  have "PROP ?Ps es E Ts' ?A\<^isub>0 (Class C # ST)" by fact
  hence "\<turnstile> compEs\<^isub>2 es,compxEs\<^isub>2 es 0 (size ST+1) [::] ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s"
        "last (?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) = ?\<tau>\<^isub>1"
    using Call.prems wtes by(auto simp add:after_def)
  also have "(?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) @ [?\<tau>'] = ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s @ [?\<tau>']" by simp
  also have "\<turnstile> compE\<^isub>2 e,compxE\<^isub>2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]"
    using Call C by(auto simp add:after_def)
  finally show ?case using Call.prems C by(simp add:after_def hyperUn_assoc)
next
  case Seq thus ?case
    by(auto simp:after_def)
      (fastsimp simp:wt_Push wt_Pop hyperUn_assoc
                intro:wt_instrs_app2 wt_instrs_Cons)
qed
(*>*)


lemma [simp]: "types (compP f P) = types P"
(*<*)by auto(*>*)

lemma [simp]: "states (compP f P) mxs mxl = states P mxs mxl"
(*<*)by (simp add: JVM_states_unfold)(*>*)

lemma [simp]: "app\<^isub>i (i, compP f P, pc, mpc, T, \<tau>) = app\<^isub>i (i, P, pc, mpc, T, \<tau>)"
(*<*)
  apply (cases \<tau>)  
  apply (cases i)
  apply auto
   apply (fastsimp dest!: sees_method_compPD)
  apply (force dest: sees_method_compP)
  done
(*>*)
  
lemma [simp]: "is_relevant_entry (compP f P) i = is_relevant_entry P i"
(*<*)
  apply (rule ext)+
  apply (unfold is_relevant_entry_def)
  apply (cases i)
  apply auto
  done
(*>*)

lemma [simp]: "relevant_entries (compP f P) i pc xt = relevant_entries P i pc xt"
(*<*) by (simp add: relevant_entries_def)(*>*)

lemma [simp]: "app i (compP f P) mpc T pc mxl xt \<tau> = app i P mpc T pc mxl xt \<tau>"
(*<*)
  apply (simp add: app_def xcpt_app_def eff_def xcpt_eff_def norm_eff_def)
  apply (fastsimp simp add: image_def)
  done
(*>*)

lemma [simp]: "app i P mpc T pc mxl xt \<tau> \<Longrightarrow> eff i (compP f P) pc xt \<tau> = eff i P pc xt \<tau>"
(*<*)
  apply (clarsimp simp add: eff_def norm_eff_def xcpt_eff_def app_def)
  apply (cases i)
  apply auto
  done
(*>*)

lemma [simp]: "subtype (compP f P) = subtype P"
(*<*)
  apply (rule ext)+
  apply (simp)
  done
(*>*)
  
lemma [simp]: "compP f P \<turnstile> \<tau> \<le>' \<tau>' = P \<turnstile> \<tau> \<le>' \<tau>'"
(*<*) by (simp add: sup_state_opt_def sup_state_def sup_ty_opt_def)(*>*)

lemma [simp]: "compP f P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s = P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s"
(*<*)by (simp add: wt_instr_def cong: conj_cong)(*>*)

declare TC1.compT_sizes[simp]  TC0.ty_def2[simp]

context TC2
begin

lemma compT_method:
  fixes e and A and C and Ts and mxl\<^isub>0
  defines [simp]: "E \<equiv> Class C # Ts"
    and [simp]: "A \<equiv> \<lfloor>{..size Ts}\<rfloor>"
    and [simp]: "A' \<equiv> A \<squnion> \<A> e"
    and [simp]: "mxl\<^isub>0 \<equiv> max_vars e"
  assumes mxs: "max_stack e = mxs"
    and mxl: "Suc (length Ts + max_vars e) = mxl"
  assumes assm: "wf_prog p P" "P,E \<turnstile>\<^sub>1 e :: T" "\<D> e A" "\<B> e (size E)"
    "set E \<subseteq> types P" "P \<turnstile> T \<le> T\<^isub>r"
  shows "wt_method (compP\<^isub>2 P) C Ts T\<^isub>r mxs mxl\<^isub>0 (compE\<^isub>2 e @ [Return])
    (compxE\<^isub>2 e 0 0) (ty\<^isub>i' [] E A # compT\<^isub>a E A [] e)"
(*<*)
using assms apply (simp add: wt_method_def compT\<^isub>a_def after_def mxl)
apply (rule conjI)
apply (simp add: check_types_def OK_ty\<^isub>i'_in_statesI)
apply (rule conjI)
apply (drule (1) WT\<^isub>1_is_type)
apply simp
apply (insert max_stack1 [of e])
apply (rule OK_ty\<^isub>i'_in_statesI) apply (simp_all add: mxs)[3]
apply (erule compT_states(1))
apply assumption
apply (simp_all add: mxs mxl)[4]
apply (rule conjI)
apply (auto simp add: wt_start_def ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth
  nth_Cons mxl split: nat.split dest: less_antisym)[1]
apply (frule (1) TC2.compT_wt_instrs [of P _ _ _ _ "[]" "max_stack e" "Suc (length Ts + max_vars e)" T\<^isub>r])
apply simp_all
apply (clarsimp simp: after_def)
apply (rule conjI)
apply (clarsimp simp: wt_instrs_def after_def mxl mxs)
apply clarsimp
apply (drule (1) less_antisym)
apply (clarsimp simp: wt_defs xcpt_app_pcs xcpt_eff_pcs ty\<^isub>i'_def)
apply (cases "size (compE\<^isub>2 e)")
 apply (simp del: compxE\<^isub>2_size_convs nth_append add: neq_Nil_conv)
apply (simp add: mxl)
done
(*>*)

end

definition compTP :: "J\<^isub>1_prog \<Rightarrow> ty\<^isub>P" where
  "compTP P C M = (
  let (D,Ts,T,e) = method P C M;
       E = Class C # Ts;
       A = \<lfloor>{..size Ts}\<rfloor>;
       mxl = 1 + size Ts + max_vars e
  in  (TC0.ty\<^isub>i' mxl [] E A # TC1.compT\<^isub>a P mxl E A [] e))"

theorem wt_compP\<^isub>2:
  "wf_J\<^isub>1_prog P \<Longrightarrow> wf_jvm_prog (compP\<^isub>2 P)"
(*<*)
  apply (simp add: wf_jvm_prog_def wf_jvm_prog_phi_def)
  apply(rule_tac x = "compTP P" in exI)
  apply (rule wf_prog_compPI)
   prefer 2 apply assumption
  apply (clarsimp simp add: wf_mdecl_def)
  apply (simp add: compTP_def)
  apply (rule TC2.compT_method [simplified])
       apply (rule refl)
       apply (rule refl)
       apply assumption
       apply assumption
       apply assumption
       apply assumption
    apply (drule (1) sees_wf_mdecl)
    apply (simp add: wf_mdecl_def)
   apply (blast intro: sees_method_is_class)
  apply assumption
  done
(*>*)

theorem wt_J2JVM:
  "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
(*<*)
apply(simp only:o_def J2JVM_def)
apply(blast intro:wt_compP\<^isub>2 compP\<^isub>1_pres_wf)
done

end
