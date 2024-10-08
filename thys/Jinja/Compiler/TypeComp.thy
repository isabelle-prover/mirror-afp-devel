(*  Title:      Jinja/Compiler/TypeComp.thy

    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

section \<open>Preservation of Well-Typedness\<close>

theory TypeComp
imports Compiler "../BV/BVSpec"
begin

(*<*)
declare nth_append[simp]
(*>*)

locale TC0 =
  fixes P :: "J\<^sub>1_prog" and mxl :: nat
begin

definition "ty E e = (THE T. P,E \<turnstile>\<^sub>1 e :: T)"

definition "ty\<^sub>l E A' = map (\<lambda>i. if i \<in> A' \<and> i < size E then OK(E!i) else Err) [0..<mxl]"

definition "ty\<^sub>i' ST E A = (case A of None \<Rightarrow> None | \<lfloor>A'\<rfloor> \<Rightarrow> Some(ST, ty\<^sub>l E A'))"

definition "after E A ST e = ty\<^sub>i' (ty E e # ST) E (A \<squnion> \<A> e)"

end

lemma (in TC0) ty_def2 [simp]: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> ty E e = T"
(*<*)by(unfold ty_def) (blast intro: the_equality WT\<^sub>1_unique)(*>*)

lemma (in TC0) [simp]: "ty\<^sub>i' ST E None = None"
(*<*)by (simp add: ty\<^sub>i'_def)(*>*)

lemma (in TC0) ty\<^sub>l_app_diff[simp]:
 "ty\<^sub>l (E@[T]) (A - {size E}) = ty\<^sub>l E A"
(*<*)by(auto simp add:ty\<^sub>l_def hyperset_defs)(*>*)


lemma (in TC0) ty\<^sub>i'_app_diff[simp]:
 "ty\<^sub>i' ST (E @ [T]) (A \<ominus> size E) = ty\<^sub>i' ST E A"
(*<*)by(auto simp add:ty\<^sub>i'_def hyperset_defs)(*>*)


lemma (in TC0) ty\<^sub>l_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^sub>l E A' [\<le>\<^sub>\<top>] ty\<^sub>l E A"
(*<*)by(auto simp:ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>i'_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^sub>i' ST E \<lfloor>A'\<rfloor> \<le>' ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>l_env_antimono:
 "P \<turnstile> ty\<^sub>l (E@[T]) A [\<le>\<^sub>\<top>] ty\<^sub>l E A" 
(*<*)by(auto simp:ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>i'_env_antimono:
 "P \<turnstile> ty\<^sub>i' ST (E@[T]) A \<le>' ty\<^sub>i' ST E A" 
(*<*)by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>i'_incr:
 "P \<turnstile> ty\<^sub>i' ST (E @ [T]) \<lfloor>insert (size E) A\<rfloor> \<le>' ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(auto simp:ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>l_incr:
 "P \<turnstile> ty\<^sub>l (E @ [T]) (insert (size E) A) [\<le>\<^sub>\<top>] ty\<^sub>l E A"
(*<*)by(auto simp: hyperset_defs ty\<^sub>l_def list_all2_conv_all_nth)(*>*)


lemma (in TC0) ty\<^sub>l_in_types:
 "set E \<subseteq> types P \<Longrightarrow> ty\<^sub>l E A \<in> nlists mxl (err (types P))"
(*<*)by(auto simp add:ty\<^sub>l_def intro!:nlistsI dest!: nth_mem)(*>*)

locale TC1 = TC0
begin

primrec compT :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^sub>1 \<Rightarrow> ty\<^sub>i' list" and
   compTs :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^sub>1 list \<Rightarrow> ty\<^sub>i' list" where
"compT E A ST (new C) = []"
| "compT E A ST (Cast C e) =  
   compT E A ST e @ [after E A ST e]"
| "compT E A ST (Val v) = []"
| "compT E A ST (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) =
  (let ST\<^sub>1 = ty E e\<^sub>1#ST; A\<^sub>1 = A \<squnion> \<A> e\<^sub>1 in
   compT E A ST e\<^sub>1 @ [after E A ST e\<^sub>1] @
   compT E A\<^sub>1 ST\<^sub>1 e\<^sub>2 @ [after E A\<^sub>1 ST\<^sub>1 e\<^sub>2])"
| "compT E A ST (Var i) = []"
| "compT E A ST (i := e) = compT E A ST e @
   [after E A ST e, ty\<^sub>i' ST E (A \<squnion> \<A> e \<squnion> \<lfloor>{i}\<rfloor>)]"
| "compT E A ST (e\<bullet>F{D}) = 
   compT E A ST e @ [after E A ST e]"
| "compT E A ST (e\<^sub>1\<bullet>F{D} := e\<^sub>2) =
  (let ST\<^sub>1 = ty   E e\<^sub>1#ST; A\<^sub>1 = A \<squnion> \<A> e\<^sub>1; A\<^sub>2 = A\<^sub>1 \<squnion> \<A> e\<^sub>2 in
   compT E A ST e\<^sub>1 @ [after E A ST e\<^sub>1] @
   compT E A\<^sub>1 ST\<^sub>1 e\<^sub>2 @ [after E A\<^sub>1 ST\<^sub>1 e\<^sub>2] @
   [ty\<^sub>i' ST E A\<^sub>2])"
| "compT E A ST {i:T; e} = compT (E@[T]) (A\<ominus>i) ST e"
| "compT E A ST (e\<^sub>1;;e\<^sub>2) =
  (let A\<^sub>1 = A \<squnion> \<A> e\<^sub>1 in
   compT E A ST e\<^sub>1 @ [after E A ST e\<^sub>1, ty\<^sub>i' ST E A\<^sub>1] @
   compT E A\<^sub>1 ST e\<^sub>2)"
| "compT E A ST (if (e) e\<^sub>1 else e\<^sub>2) =
   (let A\<^sub>0 = A \<squnion> \<A> e; \<tau> = ty\<^sub>i' ST E A\<^sub>0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A\<^sub>0 ST e\<^sub>1 @ [after E A\<^sub>0 ST e\<^sub>1, \<tau>] @
    compT E A\<^sub>0 ST e\<^sub>2)"
| "compT E A ST (while (e) c) =
   (let A\<^sub>0 = A \<squnion> \<A> e;  A\<^sub>1 = A\<^sub>0 \<squnion> \<A> c; \<tau> = ty\<^sub>i' ST E A\<^sub>0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A\<^sub>0 ST c @ [after E A\<^sub>0 ST c, ty\<^sub>i' ST E A\<^sub>1, ty\<^sub>i' ST E A\<^sub>0])"
| "compT E A ST (throw e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e\<bullet>M(es)) =
   compT E A ST e @ [after E A ST e] @
   compTs E (A \<squnion> \<A> e) (ty   E e # ST) es"
| "compT E A ST (try e\<^sub>1 catch(C i) e\<^sub>2) =
   compT E A ST e\<^sub>1 @ [after E A ST e\<^sub>1] @
   [ty\<^sub>i' (Class C#ST) E A, ty\<^sub>i' ST (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @
   compT (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e\<^sub>2"
| "compTs E A ST [] = []"
| "compTs  E A ST (e#es) = compT E A ST e @ [after E A ST e] @
                            compTs E (A \<squnion> (\<A> e)) (ty E e # ST) es"

definition compT\<^sub>a :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr\<^sub>1 \<Rightarrow> ty\<^sub>i' list" where
  "compT\<^sub>a E A ST e = compT E A ST e @ [after E A ST e]"

end

lemma compE\<^sub>2_not_Nil[simp]: "compE\<^sub>2 e \<noteq> []"
(*<*)by(induct e) auto(*>*)

lemma (in TC1) compT_sizes[simp]:
shows "\<And>E A ST. size(compT E A ST e) = size(compE\<^sub>2 e) - 1"
and "\<And>E A ST. size(compTs E A ST es) = size(compEs\<^sub>2 es)"
(*<*)
by(induct e and es rule: compE\<^sub>2.induct compEs\<^sub>2.induct)
  (auto split:bop.splits nat_diff_split)
(*>*)


lemma (in TC1) [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compT E None ST e)"
and [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compTs E None ST es)"
(*<*)by(induct e and es rule: compT.induct compTs.induct) (simp_all add:after_def)(*>*)


lemma (in TC0) pair_eq_ty\<^sub>i'_conv:
  "(\<lfloor>(ST, LT)\<rfloor> = ty\<^sub>i' ST\<^sub>0 E A) =
  (case A of None \<Rightarrow> False | Some A \<Rightarrow> (ST = ST\<^sub>0 \<and> LT = ty\<^sub>l E A))"
(*<*)by(simp add:ty\<^sub>i'_def)(*>*)


lemma (in TC0) pair_conv_ty\<^sub>i':
  "\<lfloor>(ST, ty\<^sub>l E A)\<rfloor> = ty\<^sub>i' ST E \<lfloor>A\<rfloor>"
(*<*)by(simp add:ty\<^sub>i'_def)(*>*)

(*<*)
declare (in TC0)
  ty\<^sub>i'_antimono [intro!] after_def[simp]
  pair_conv_ty\<^sub>i'[simp] pair_eq_ty\<^sub>i'_conv[simp]
(*>*)


lemma (in TC1) compT_LT_prefix:
 "\<And>E A ST\<^sub>0. \<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST\<^sub>0 e); \<B> e (size E) \<rbrakk>
               \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^sub>i' ST E A"
and
 "\<And>E A ST\<^sub>0. \<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST\<^sub>0 es); \<B>s es (size E) \<rbrakk>
               \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^sub>i' ST E A"
(*<*)
proof(induct e and es rule: compT.induct compTs.induct)
  case FAss thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case BinOp thus ?case
    by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans split:bop.splits)
next
  case Seq thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case While thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cond thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Block thus ?case
    by(force simp add:hyperset_defs ty\<^sub>i'_def simp del:pair_conv_ty\<^sub>i'
             elim!:sup_state_opt_trans)
next
  case Call thus ?case by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cons_exp thus ?case
    by(fastforce simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case TryCatch thus ?case
    by(fastforce simp:hyperset_defs intro!:(* ty\<^sub>i'_env_antimono *) ty\<^sub>i'_incr
                elim!:sup_state_opt_trans)
qed (auto simp:hyperset_defs)

declare (in TC0)
  ty\<^sub>i'_antimono [rule del] after_def[simp del]
  pair_conv_ty\<^sub>i'[simp del] pair_eq_ty\<^sub>i'_conv[simp del]
(*>*)


lemma [iff]: "OK None \<in> states P mxs mxl"
(*<*)by(simp add: JVM_states_unfold)(*>*)

lemma (in TC0) after_in_states:
assumes wf: "wf_prog p P" and wt: "P,E \<turnstile>\<^sub>1 e :: T"
  and Etypes: "set E \<subseteq> types P" and STtypes: "set ST \<subseteq> types P"
  and stack: "size ST + max_stack e \<le> mxs"
shows "OK (after E A ST e) \<in> states P mxs mxl"
(*<*)
proof -
  have "size ST + 1 \<le> mxs" using max_stack1[of e] wt stack
    by fastforce
  then show ?thesis using assms
    by(simp add: after_def ty\<^sub>i'_def JVM_states_unfold ty\<^sub>l_in_types)
      (blast intro!:nlistsI WT\<^sub>1_is_type)
qed
(*>*)


lemma (in TC0) OK_ty\<^sub>i'_in_statesI[simp]:
  "\<lbrakk> set E \<subseteq> types P; set ST \<subseteq> types P; size ST \<le> mxs \<rbrakk>
  \<Longrightarrow> OK (ty\<^sub>i' ST E A) \<in> states P mxs mxl"
(*<*)
by(simp add:ty\<^sub>i'_def JVM_states_unfold ty\<^sub>l_in_types)
  (blast intro!:nlistsI)
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
proof(induct e and es rule: compT.induct compTs.induct)
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
    by(auto simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Seq thus ?case
    by(auto simp:image_Un after_in_states[OF wf])
next
  case BinOp thus ?case
    by(auto simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Cond thus ?case
    by(force simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case While thus ?case
    by(auto simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Block thus ?case by(auto)
next
  case (TryCatch e\<^sub>1 C i e\<^sub>2)
  moreover have "size ST + 1 \<le> mxs" using TryCatch.prems max_stack1[of e\<^sub>1] by auto
  ultimately show ?case  
    by(auto simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf]
                  is_class_type_aux)
next
  case Nil_exp thus ?case by simp
next
  case Cons_exp thus ?case
    by(auto simp:image_Un  WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case throw thus ?case
    by(auto simp: WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
next
  case Call thus ?case
    by(auto simp:image_Un WT\<^sub>1_is_type[OF wf] after_in_states[OF wf])
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

lemma [simp]: "shift n (xt\<^sub>1 @ xt\<^sub>2) = shift n xt\<^sub>1 @ shift n xt\<^sub>2"
(*<*)by(simp add:shift_def)(*>*)

lemma [simp]: "shift m (shift n xt) = shift (m+n) xt"
(*<*)by(induct xt)(auto simp:shift_def)(*>*)

lemma [simp]: "pcs (shift n xt) = {pc+n|pc. pc \<in> pcs xt}"
(*<*)
proof -
  { fix x f t C h d
    assume "(f,t,C,h,d) \<in> set xt" and "f + n \<le> x"
      and "x < t + n"
    then have "\<exists>pc. x = pc + n \<and> (\<exists>x\<in>set xt. pc \<in> (case x of (f, t, C, h, d) \<Rightarrow> {f..<t}))"
      by(rule_tac x = "x-n" in exI) (force split:nat_diff_split)
  }
  then show ?thesis by(auto simp:shift_def pcs_def) fast
qed
(*>*)


lemma shift_compxE\<^sub>2:
shows "\<And>pc pc' d. shift pc (compxE\<^sub>2 e pc' d) = compxE\<^sub>2 e (pc' + pc) d"
and  "\<And>pc pc' d. shift pc (compxEs\<^sub>2 es pc' d) = compxEs\<^sub>2 es (pc' + pc) d"
(*<*)
by(induct e and es rule: compxE\<^sub>2.induct compxEs\<^sub>2.induct)
  (auto simp:shift_def ac_simps)
(*>*)


lemma compxE\<^sub>2_size_convs[simp]:
shows "n \<noteq> 0 \<Longrightarrow> compxE\<^sub>2 e n d = shift n (compxE\<^sub>2 e 0 d)"
and "n \<noteq> 0 \<Longrightarrow> compxEs\<^sub>2 es n d = shift n (compxEs\<^sub>2 es 0 d)"
(*<*)by(simp_all add:shift_compxE\<^sub>2)(*>*)

locale TC2 = TC1 +
  fixes T\<^sub>r :: ty and mxs :: pc
begin

definition
  wt_instrs :: "instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^sub>i' list \<Rightarrow> bool"
    (\<open>(\<turnstile> _, _ /[::]/ _)\<close> [0,0,51] 50) where
  "\<turnstile> is,xt [::] \<tau>s \<longleftrightarrow> size is < size \<tau>s \<and> pcs xt \<subseteq> {0..<size is} \<and>
  (\<forall>pc< size is. P,T\<^sub>r,mxs,size \<tau>s,xt \<turnstile> is!pc,pc :: \<tau>s)"

end

notation TC2.wt_instrs (\<open>(_,_,_ \<turnstile>/ _, _ /[::]/ _)\<close> [50,50,50,50,50,51] 50)

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
(*<*)by (fastforce simp:wt_instr_def app_def)(*>*)


lemma relevant_entries_shift [simp]:
  "relevant_entries P i (pc+n) (shift n xt) = shift n (relevant_entries P i pc xt)"
(*<*)
proof(induct xt)
  case Nil
  then show ?case by (simp add: relevant_entries_def shift_def)
next
  case (Cons a xt)
  then show ?case 
    by (auto simp add: relevant_entries_def shift_def is_relevant_entry_def)
qed
(*>*)


lemma [simp]:
  "xcpt_eff i P (pc+n) \<tau> (shift n xt) =
   map (\<lambda>(pc,\<tau>). (pc + n, \<tau>)) (xcpt_eff i P pc \<tau> xt)"
(*<*)
proof -
  obtain ST LT where "\<tau> = (ST, LT)" by(cases \<tau>) simp
  then show ?thesis by(simp add: xcpt_eff_def) (auto simp add: shift_def)
qed
(*>*)


lemma  [simp]:
  "app\<^sub>i (i, P, pc, m, T, \<tau>) \<Longrightarrow>
   eff i P (pc+n) (shift n xt) (Some \<tau>) =
   map (\<lambda>(pc,\<tau>). (pc+n,\<tau>)) (eff i P pc xt (Some \<tau>))"
(*<*)by(cases "i") (auto simp add:eff_def norm_eff_def)(*>*)


lemma [simp]:
  "xcpt_app i P (pc+n) mxs (shift n xt) \<tau> = xcpt_app i P pc mxs xt \<tau>"
(*<*)by (simp add: xcpt_app_def) (auto simp add: shift_def)(*>*)


lemma wt_instr_appL:
assumes "P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s" and "pc < size \<tau>s" and "mpc \<le> size \<tau>s"
shows "P,T,m,mpc + size \<tau>s',shift (size \<tau>s') xt \<turnstile> i,pc+size \<tau>s' :: \<tau>s'@\<tau>s"
(*<*)
proof -
  let ?t = "(\<tau>s'@\<tau>s)!(pc+size \<tau>s')"
  show ?thesis
  proof(cases ?t)
    case (Some \<tau>)
    obtain ST LT where [simp]: "\<tau> = (ST, LT)" by(cases \<tau>) simp
    have "app\<^sub>i (i, P, pc + length \<tau>s', m, T, \<tau>)"
      using Some assms by(cases "i") (auto simp:wt_instr_def app_def)
    moreover {
      fix pc' \<tau>' assume "(pc',\<tau>') \<in> set (eff i P pc xt ?t)"
      then have "P \<turnstile> \<tau>' \<le>' \<tau>s!pc'" and "pc' < mpc"
        using Some assms by(auto simp:wt_instr_def app_def)
    }
    ultimately show ?thesis using Some assms
      by(fastforce simp:wt_instr_def app_def)
  qed (auto simp:wt_instr_def app_def)
qed
(*>*)


lemma wt_instr_Cons:
assumes wti: "P,T,m,mpc - 1,[] \<turnstile> i,pc - 1 :: \<tau>s"
  and pcl: "0 < pc" and mpcl: "0 < mpc"
  and pcu: "pc < size \<tau>s + 1" and mpcu: "mpc \<le> size \<tau>s + 1"
shows "P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>#\<tau>s"
(*<*)
proof -
  have "pc - 1 < length \<tau>s" using pcl pcu by arith
  moreover have "mpc - 1 \<le> length \<tau>s" using mpcl mpcu by arith
  ultimately have
    "P,T,m,mpc - 1 + length [\<tau>],shift (length [\<tau>]) [] \<turnstile> i,pc - 1 + length [\<tau>] :: [\<tau>] @ \<tau>s"
    by(rule wt_instr_appL[where \<tau>s' = "[\<tau>]", OF wti])
  then show ?thesis using pcl mpcl by (simp split:nat_diff_split_asm)
qed
(*>*)


lemma wt_instr_append:
assumes wti: "P,T,m,mpc - size \<tau>s',[] \<turnstile> i,pc - size \<tau>s' :: \<tau>s"
  and pcl: "size \<tau>s' \<le> pc" and mpcl: "size \<tau>s' \<le> mpc"
  and pcu: "pc < size \<tau>s + size \<tau>s'" and mpcu: "mpc \<le> size \<tau>s + size \<tau>s'"
shows "P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>s'@\<tau>s"
(*<*)
proof -
  have "pc - length \<tau>s' < length \<tau>s" using pcl pcu by arith
  moreover have "mpc - length \<tau>s' \<le> length \<tau>s" using mpcl mpcu by arith
thm wt_instr_appL[where \<tau>s' = "\<tau>s'", OF wti]
  ultimately have "P,T,m,mpc - length \<tau>s' + length \<tau>s',shift (length \<tau>s') []
                     \<turnstile> i,pc - length \<tau>s' + length \<tau>s' :: \<tau>s' @ \<tau>s"
    by(rule wt_instr_appL[where \<tau>s' = "\<tau>s'", OF wti])
  then show ?thesis using pcl mpcl by (simp split:nat_diff_split_asm)
qed
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
assumes wt\<^sub>1: "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2" and wt\<^sub>2: "\<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>2"
  and \<tau>s_size: "size \<tau>s\<^sub>1 = size is\<^sub>1"
 shows "\<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
(*<*)
proof -
  let ?is = "is\<^sub>1@is\<^sub>2" and ?xt = "xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2"
    and ?\<tau>s = "\<tau>s\<^sub>1@\<tau>s\<^sub>2"
  have "size ?is < size ?\<tau>s" using wt\<^sub>2 \<tau>s_size by(fastforce simp:wt_instrs_def)
  moreover have "pcs ?xt \<subseteq> {0..<size ?is}" using wt\<^sub>1 wt\<^sub>2
    by(fastforce simp:wt_instrs_def)
  moreover {
    fix pc assume pc: "pc<size ?is"
    have "P,T\<^sub>r,mxs,size ?\<tau>s,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
    proof(cases "pc < length is\<^sub>1")
      case True then show ?thesis using wt\<^sub>1 pc
        by(fastforce simp: wt_instrs_def wt_instr_appRx)
    next
      case False
      then have "pc - length is\<^sub>1 < length is\<^sub>2" using pc by fastforce
      then have "P,T\<^sub>r,mxs,length \<tau>s\<^sub>2,xt\<^sub>2 \<turnstile> is\<^sub>2 ! (pc - length is\<^sub>1),pc - length is\<^sub>1 :: \<tau>s\<^sub>2"
        using wt\<^sub>2 by(clarsimp simp: wt_instrs_def)
      moreover have "pc - length is\<^sub>1 < length \<tau>s\<^sub>2" using pc wt\<^sub>2
        by(clarsimp simp: wt_instrs_def) arith
      moreover have "length \<tau>s\<^sub>2 \<le> length \<tau>s\<^sub>2" by simp
      moreover have "pc - length is\<^sub>1 + length \<tau>s\<^sub>1 \<notin> pcs xt\<^sub>1" using wt\<^sub>1 \<tau>s_size
        by(fastforce simp: wt_instrs_def)
      ultimately have "P,T\<^sub>r,mxs,length \<tau>s\<^sub>2 + length \<tau>s\<^sub>1,xt\<^sub>1 @ shift (length \<tau>s\<^sub>1) xt\<^sub>2
                         \<turnstile> is\<^sub>2 ! (pc - length is\<^sub>1),pc - length is\<^sub>1 + length \<tau>s\<^sub>1 :: \<tau>s\<^sub>1 @ \<tau>s\<^sub>2"
        by(rule wt_instr_appLx[OF wt_instr_appL[where \<tau>s' = "\<tau>s\<^sub>1"]])
      then show ?thesis using False \<tau>s_size by(simp add:add.commute)
    qed
  }
  ultimately show ?thesis by(clarsimp simp:wt_instrs_def)
qed
(*>*)

corollary (in TC2) wt_instrs_ext2:
  "\<lbrakk> \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>2; \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2; size \<tau>s\<^sub>1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
(*<*)by(rule wt_instrs_ext)(*>*)


corollary (in TC2) wt_instrs_ext_prefix [trans]:
  "\<lbrakk> \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2; \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>s\<^sub>3;
     size \<tau>s\<^sub>1 = size is\<^sub>1; prefix \<tau>s\<^sub>3 \<tau>s\<^sub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
(*<*)by(bestsimp simp:prefix_def elim: wt_instrs_ext dest:wt_instrs_extR)(*>*)


corollary (in TC2) wt_instrs_app:
  assumes is\<^sub>1: "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@[\<tau>]"
  assumes is\<^sub>2: "\<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>2"
  assumes s: "size \<tau>s\<^sub>1 = size is\<^sub>1"
  shows "\<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>#\<tau>s\<^sub>2"
(*<*)
proof -
  from is\<^sub>1 have "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] (\<tau>s\<^sub>1@[\<tau>])@\<tau>s\<^sub>2"
    by (rule wt_instrs_extR)
  hence "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1@\<tau>#\<tau>s\<^sub>2" by simp
  from this is\<^sub>2 s show ?thesis by (rule wt_instrs_ext) 
qed
(*>*)


corollary (in TC2) wt_instrs_app_last[trans]:
assumes "\<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>2" "\<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>s\<^sub>1"
  "last \<tau>s\<^sub>1 = \<tau>" "size \<tau>s\<^sub>1 = size is\<^sub>1+1"
shows "\<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>s\<^sub>1@\<tau>s\<^sub>2"
(*<*)
using assms proof(cases \<tau>s\<^sub>1 rule:rev_cases)
  case (snoc ys y)
  then show ?thesis using assms by(simp add:wt_instrs_app)
qed simp
(*>*)


corollary (in TC2) wt_instrs_append_last[trans]:
assumes wtis: "\<turnstile> is,xt [::] \<tau>s" and wti: "P,T\<^sub>r,mxs,mpc,[] \<turnstile> i,pc :: \<tau>s"
  and pc: "pc = size is" and mpc: "mpc = size \<tau>s" and is_\<tau>s: "size is + 1 < size \<tau>s"
shows "\<turnstile> is@[i],xt [::] \<tau>s"
(*<*)
proof -
  have pc_xt: "pc \<notin> pcs xt" using wtis pc by (fastforce simp:wt_instrs_def)
  have "pcs xt \<subseteq> {..<Suc (length is)}" using wtis by (fastforce simp:wt_instrs_def)
  moreover {
    fix pc' assume pc': "\<not> pc' < length is" "pc' < Suc (length is)"
    have "P,T\<^sub>r,mxs,length \<tau>s,xt \<turnstile> i,pc' :: \<tau>s"
      using wt_instr_appLx[where xt = "[]",simplified,OF wti pc_xt]
            less_antisym[OF pc'] pc mpc by simp
  }
  ultimately show ?thesis using wtis is_\<tau>s by(clarsimp simp add:wt_instrs_def)
qed
(*>*)


corollary (in TC2) wt_instrs_app2:
  "\<lbrakk> \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>'#\<tau>s\<^sub>2;  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>#\<tau>s\<^sub>1@[\<tau>'];
     xt' = xt\<^sub>1 @ shift (size is\<^sub>1) xt\<^sub>2;  size \<tau>s\<^sub>1+1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2,xt' [::] \<tau>#\<tau>s\<^sub>1@\<tau>'#\<tau>s\<^sub>2"
(*<*)using wt_instrs_app[where ?\<tau>s\<^sub>1.0 = "\<tau> # \<tau>s\<^sub>1"] by simp (*>*)


corollary (in TC2) wt_instrs_app2_simp[trans,simp]:
  "\<lbrakk> \<turnstile> is\<^sub>2,xt\<^sub>2 [::] \<tau>'#\<tau>s\<^sub>2;  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau>#\<tau>s\<^sub>1@[\<tau>']; size \<tau>s\<^sub>1+1 = size is\<^sub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^sub>1@is\<^sub>2, xt\<^sub>1@shift (size is\<^sub>1) xt\<^sub>2 [::] \<tau>#\<tau>s\<^sub>1@\<tau>'#\<tau>s\<^sub>2"
(*<*)using wt_instrs_app[where ?\<tau>s\<^sub>1.0 = "\<tau> # \<tau>s\<^sub>1"] by simp(*>*)


corollary (in TC2) wt_instrs_Cons[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,xt [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>'#\<tau>s"
(*<*)
using wt_instrs_app2[where ?is\<^sub>1.0 = "[i]" and ?\<tau>s\<^sub>1.0 = "[]" and ?is\<^sub>2.0 = "is"
                      and ?xt\<^sub>1.0 = "[]"]
by simp


corollary (in TC2) wt_instrs_Cons2[trans]:
  assumes \<tau>s: "\<turnstile> is,xt [::] \<tau>s"
  assumes i: "P,T\<^sub>r,mxs,mpc,[] \<turnstile> i,0 :: \<tau>#\<tau>s"
  assumes mpc: "mpc = size \<tau>s + 1"
  shows "\<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>s"
(*<*)
proof -
  from \<tau>s have "\<tau>s \<noteq> []" by (auto simp: wt_instrs_def)
  with mpc i have "\<turnstile> [i],[] [::] [\<tau>]@\<tau>s" by (simp add: wt_instrs_def)
  with \<tau>s show ?thesis by (fastforce dest: wt_instrs_ext)
qed
(*>*)


lemma (in TC2) wt_instrs_last_incr[trans]:
assumes wtis: "\<turnstile> is,xt [::] \<tau>s@[\<tau>]" and ss: "P \<turnstile> \<tau> \<le>' \<tau>'"
shows "\<turnstile> is,xt [::] \<tau>s@[\<tau>']"
(*<*)
proof -
  let ?\<tau>s = "\<tau>s@[\<tau>]" and ?\<tau>s' = "\<tau>s@[\<tau>']"
  { fix pc assume pc: "pc< size is"
    let ?i = "is!pc"
    have app_pc: "app (is ! pc) P mxs T\<^sub>r pc (length ?\<tau>s) xt (\<tau>s ! pc)"
      using wtis pc by(clarsimp simp add:wt_instrs_def wt_instr_def)
    then have Apc\<tau>': "\<And>pc' \<tau>'. (pc',\<tau>') \<in> set (eff ?i P pc xt (?\<tau>s!pc))
     \<Longrightarrow> pc' < length ?\<tau>s"
      using wtis pc by(fastforce simp add:wt_instrs_def app_def)
    have Aepc\<tau>': "\<And>pc' \<tau>'. (pc',\<tau>') \<in> set (eff ?i P pc xt (?\<tau>s!pc))
     \<Longrightarrow> P \<turnstile> \<tau>' \<le>' ?\<tau>s!pc'"
      using wtis pc by(fastforce simp add:wt_instrs_def wt_instr_def)
    { fix pc1 \<tau>1 assume pc\<tau>1: "(pc1,\<tau>1) \<in> set (eff ?i P pc xt (?\<tau>s'!pc))"
      then have epc\<tau>': "(pc1,\<tau>1) \<in> set (eff ?i P pc xt (?\<tau>s!pc))"
          using wtis pc by(simp add:wt_instrs_def)
      have "P \<turnstile> \<tau>1 \<le>' ?\<tau>s'!pc1"
      proof(cases "pc1 < length \<tau>s")
        case True
        then show ?thesis using wtis pc pc\<tau>1
          by(fastforce simp add:wt_instrs_def wt_instr_def)
      next
        case False
        then have "pc1 < length ?\<tau>s" using Apc\<tau>'[OF epc\<tau>'] by simp
        then have [simp]: "pc1 = size \<tau>s" using False by clarsimp
        have "P \<turnstile> \<tau>1 \<le>' \<tau>" using Aepc\<tau>'[OF epc\<tau>'] by simp
        then have "P \<turnstile> \<tau>1 \<le>' \<tau>'" by(rule sup_state_opt_trans[OF _ ss])
        then show ?thesis by simp
      qed
    }
    then have "P,T\<^sub>r,mxs,size ?\<tau>s',xt \<turnstile> is!pc,pc :: ?\<tau>s'" using wtis pc
      by(clarsimp simp add:wt_instrs_def wt_instr_def)
  }
  then show ?thesis using wtis by(simp add:wt_instrs_def)
qed
(*>*)


lemma [iff]: "xcpt_app i P pc mxs [] \<tau>"
(*<*)by (simp add: xcpt_app_def relevant_entries_def)(*>*)


lemma [simp]: "xcpt_eff i P pc \<tau> [] = []"
(*<*)by (simp add: xcpt_eff_def relevant_entries_def)(*>*)


lemma (in TC2) wt_New:
  "\<lbrakk> is_class P C; size ST < mxs \<rbrakk> \<Longrightarrow>
   \<turnstile> [New C],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (Class C#ST) E A]"
(*<*)by(simp add:wt_defs ty\<^sub>i'_def)(*>*)


lemma (in TC2) wt_Cast:
  "is_class P C \<Longrightarrow>
   \<turnstile> [Checkcast C],[] [::] [ty\<^sub>i' (Class D # ST) E A, ty\<^sub>i' (Class C # ST) E A]"
(*<*)by(simp add: ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Push:
  "\<lbrakk> size ST < mxs; typeof v = Some T \<rbrakk>
  \<Longrightarrow> \<turnstile> [Push v],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (T#ST) E A]"
(*<*)by(simp add: ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Pop:
 "\<turnstile> [Pop],[] [::] (ty\<^sub>i' (T#ST) E A # ty\<^sub>i' ST E A # \<tau>s)"
(*<*)by(simp add: ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_CmpEq:
  "\<lbrakk> P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> [CmpEq],[] [::] [ty\<^sub>i' (T\<^sub>2 # T\<^sub>1 # ST) E A, ty\<^sub>i' (Boolean # ST) E A]"
(*<*) by(auto simp:ty\<^sub>i'_def wt_defs elim!: refTE not_refTE) (*>*)


lemma (in TC2) wt_IAdd:
  "\<turnstile> [IAdd],[] [::] [ty\<^sub>i' (Integer#Integer#ST) E A, ty\<^sub>i' (Integer#ST) E A]"
(*<*)by(simp add:ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Load:
  "\<lbrakk> size ST < mxs; size E \<le> mxl; i \<in>\<in> A; i < size E \<rbrakk>
  \<Longrightarrow> \<turnstile> [Load i],[] [::] [ty\<^sub>i' ST E A, ty\<^sub>i' (E!i # ST) E A]"
(*<*)by(auto simp add:ty\<^sub>i'_def wt_defs ty\<^sub>l_def hyperset_defs)(*>*)


lemma (in TC2) wt_Store:
 "\<lbrakk> P \<turnstile> T \<le> E!i; i < size E; size E \<le> mxl \<rbrakk> \<Longrightarrow>
  \<turnstile> [Store i],[] [::] [ty\<^sub>i' (T#ST) E A, ty\<^sub>i' ST E (\<lfloor>{i}\<rfloor> \<squnion> A)]"
(*<*)
by(auto simp:hyperset_defs nth_list_update ty\<^sub>i'_def wt_defs ty\<^sub>l_def
        intro:list_all2_all_nthI)
(*>*)


lemma (in TC2) wt_Get:
 "\<lbrakk> P \<turnstile> C sees F:T in D \<rbrakk> \<Longrightarrow>
  \<turnstile> [Getfield F D],[] [::] [ty\<^sub>i' (Class C # ST) E A, ty\<^sub>i' (T # ST) E A]"
(*<*)by(auto simp: ty\<^sub>i'_def wt_defs dest: sees_field_idemp sees_field_decl_above)(*>*)


lemma (in TC2) wt_Put:
  "\<lbrakk> P \<turnstile> C sees F:T in D; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow>
  \<turnstile> [Putfield F D],[] [::] [ty\<^sub>i' (T' # Class C # ST) E A, ty\<^sub>i' ST E A]"
(*<*)by(auto intro: sees_field_idemp sees_field_decl_above simp: ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_Throw:
  "\<turnstile> [Throw],[] [::] [ty\<^sub>i' (Class C # ST) E A, \<tau>']"
(*<*)by(auto simp: ty\<^sub>i'_def wt_defs)(*>*)


lemma (in TC2) wt_IfFalse:
  "\<lbrakk> 2 \<le> i; nat i < size \<tau>s + 2; P \<turnstile> ty\<^sub>i' ST E A \<le>' \<tau>s ! nat(i - 2) \<rbrakk>
  \<Longrightarrow> \<turnstile> [IfFalse i],[] [::] ty\<^sub>i' (Boolean # ST) E A # ty\<^sub>i' ST E A # \<tau>s"
(*<*)
by(simp add: ty\<^sub>i'_def wt_defs eval_nat_numeral nat_diff_distrib)
(*>*)


lemma wt_Goto:
 "\<lbrakk> 0 \<le> int pc + i; nat (int pc + i) < size \<tau>s; size \<tau>s \<le> mpc;
    P \<turnstile> \<tau>s!pc \<le>' \<tau>s ! nat (int pc + i) \<rbrakk>
 \<Longrightarrow> P,T,mxs,mpc,[] \<turnstile> Goto i,pc :: \<tau>s"
(*<*)by(clarsimp simp add: TC2.wt_defs)(*>*)


lemma (in TC2) wt_Invoke:
  "\<lbrakk> size es = size Ts'; P \<turnstile> C sees M: Ts\<rightarrow>T = m in D; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> \<turnstile> [Invoke M (size es)],[] [::] [ty\<^sub>i' (rev Ts' @ Class C # ST) E A, ty\<^sub>i' (T#ST) E A]"
(*<*)by(fastforce simp add: ty\<^sub>i'_def wt_defs)(*>*)


corollary (in TC2) wt_instrs_app3[simp]:
  "\<lbrakk> \<turnstile> is\<^sub>2,[] [::] (\<tau>' # \<tau>s\<^sub>2);  \<turnstile> is\<^sub>1,xt\<^sub>1 [::] \<tau> # \<tau>s\<^sub>1 @ [\<tau>']; size \<tau>s\<^sub>1+1 = size is\<^sub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> (is\<^sub>1 @ is\<^sub>2),xt\<^sub>1 [::] \<tau> # \<tau>s\<^sub>1 @ \<tau>' # \<tau>s\<^sub>2"
(*<*)using wt_instrs_app2[where ?xt\<^sub>2.0 = "[]"] by (simp add:shift_def)(*>*)


corollary (in TC2) wt_instrs_Cons3[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,[] [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> (i # is),[] [::] \<tau> # \<tau>' # \<tau>s"
(*<*)
using wt_instrs_Cons[where ?xt = "[]"]
by (simp add:shift_def)

(*<*)
declare nth_append[simp del]
declare [[simproc del: list_to_set_comprehension]]
(*>*)

lemma (in TC2) wt_instrs_xapp[trans]:
assumes wtis: "\<turnstile> is\<^sub>1 @ is\<^sub>2, xt [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class C # ST) E A # \<tau>s\<^sub>2"
  and P_\<tau>s\<^sub>1: "\<forall>\<tau> \<in> set \<tau>s\<^sub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
    size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A"
  and is_\<tau>s: "size is\<^sub>1 = size \<tau>s\<^sub>1" and PC: "is_class P C" and ST_mxs: "size ST < mxs"
shows "\<turnstile> is\<^sub>1 @ is\<^sub>2, xt @ [(0,size is\<^sub>1 - 1,C,size is\<^sub>1,size ST)] [::] \<tau>s\<^sub>1 @ ty\<^sub>i' (Class C # ST) E A # \<tau>s\<^sub>2"
(*<*)(is "\<turnstile> ?is, xt@[?xte] [::] ?\<tau>s" is "\<turnstile> ?is, ?xt' [::] ?\<tau>s")
proof -
  let ?is = "is\<^sub>1 @ is\<^sub>2" and ?\<tau>s = "\<tau>s\<^sub>1 @ ty\<^sub>i' (Class C # ST) E A # \<tau>s\<^sub>2"
  let ?xte = "(0,size is\<^sub>1 - 1,C,size is\<^sub>1,size ST)"
  let ?xt' = "xt @ [?xte]"
  have P_\<tau>s\<^sub>1': "\<And>\<tau>. \<tau> \<in> set \<tau>s\<^sub>1 \<Longrightarrow> (\<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow>
     size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A)"
    using P_\<tau>s\<^sub>1 by fast
  have "size ?is < size ?\<tau>s" and "pcs ?xt' \<subseteq> {0..<size ?is}"
    and P_pc: "\<And>pc. pc< size ?is \<Longrightarrow> P,T\<^sub>r,mxs,size ?\<tau>s,xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
    using wtis by(simp_all add:wt_instrs_def)
  moreover {
    fix pc let ?mpc = "size ?\<tau>s" and ?i = "?is!pc" and ?t = "?\<tau>s!pc"
    assume "pc< size ?is"
    then have wti: "P,T\<^sub>r,mxs,?mpc,xt \<turnstile> ?i,pc :: ?\<tau>s" by(rule P_pc)
    then have app: "app ?i P mxs T\<^sub>r pc ?mpc xt ?t"
       and eff_ss: "\<And>pc' \<tau>'. (pc',\<tau>') \<in> set (eff ?i P pc xt (?\<tau>s!pc))
                           \<Longrightarrow> P \<turnstile> \<tau>' \<le>' ?\<tau>s!pc'"
      by(fastforce simp add: wt_instr_def)+
    have "app ?i P mxs T\<^sub>r pc ?mpc ?xt' ?t
             \<and> (\<forall>(pc',\<tau>') \<in> set (eff ?i P pc ?xt' ?t). P \<turnstile> \<tau>' \<le>' ?\<tau>s!pc')"
    proof (cases ?t)
      case (Some \<tau>)
      obtain ST' LT' where \<tau>: "\<tau> = (ST', LT')" by(cases \<tau>) simp
      have app\<^sub>i: "app\<^sub>i (?i,P,pc,mxs,T\<^sub>r,\<tau>)" and xcpt_app: "xcpt_app ?i P pc mxs xt \<tau>"
         and eff_pc: "\<And>pc' \<tau>'. (pc',\<tau>') \<in> set (eff ?i P pc xt ?t) \<Longrightarrow> pc' < ?mpc"
        using Some app by(fastforce simp add: app_def)+
      have "xcpt_app ?i P pc mxs ?xt' \<tau>"
      proof(cases "pc < length \<tau>s\<^sub>1 - 1")
        case False then show ?thesis using Some \<tau> is_\<tau>s xcpt_app
          by (clarsimp simp: xcpt_app_def relevant_entries_def
                             is_relevant_entry_def)
      next
        case True
        then have True': "pc < length \<tau>s\<^sub>1" by simp
        then have "\<tau>s\<^sub>1 ! pc = ?t" by(fastforce simp: nth_append)
        moreover have \<tau>s\<^sub>1_pc: "\<tau>s\<^sub>1 ! pc \<in> set \<tau>s\<^sub>1" by(rule nth_mem[OF True'])
        ultimately show ?thesis
         using Some \<tau> PC ST_mxs xcpt_app P_\<tau>s\<^sub>1'[OF \<tau>s\<^sub>1_pc]
          by (simp add: xcpt_app_def relevant_entries_def)
      qed
      moreover {
        fix pc' \<tau>' assume efft: "(pc',\<tau>') \<in> set (eff ?i P pc ?xt' ?t)"
        have "pc' < ?mpc \<and> P \<turnstile> \<tau>' \<le>' ?\<tau>s!pc'" (is "?P1 \<and> ?P2")
        proof(cases "(pc',\<tau>') \<in> set (eff ?i P pc xt ?t)")
          case True
          have ?P1 using True by(rule eff_pc)
          moreover have ?P2 using True by(rule eff_ss)
          ultimately show ?thesis by simp
        next
          case False
          then have xte: "(pc',\<tau>') \<in> set (xcpt_eff ?i P pc \<tau> [?xte])"
            using efft Some by(clarsimp simp: eff_def)
          then have ?P1 using Some \<tau> is_\<tau>s
            by(clarsimp simp: xcpt_eff_def relevant_entries_def split: if_split_asm)
          moreover have ?P2
          proof(cases "pc < length \<tau>s\<^sub>1 - 1")
            case False': False
            then show ?thesis using False Some \<tau> xte is_\<tau>s
              by(simp add: xcpt_eff_def relevant_entries_def is_relevant_entry_def)
          next
            case True
            then have True': "pc < length \<tau>s\<^sub>1" by simp
            have \<tau>s\<^sub>1_pc: "\<tau>s\<^sub>1 ! pc \<in> set \<tau>s\<^sub>1" by(rule nth_mem[OF True'])
            have "P \<turnstile> \<lfloor>(Class C # drop (length ST' - length ST) ST', LT')\<rfloor>
                         \<le>' ty\<^sub>i' (Class C # ST) E A"
               using True' Some \<tau> P_\<tau>s\<^sub>1'[OF \<tau>s\<^sub>1_pc]
              by (fastforce simp: nth_append ty\<^sub>i'_def)
            then show ?thesis using \<tau> xte is_\<tau>s
              by(simp add: xcpt_eff_def relevant_entries_def split: if_split_asm)
          qed
          ultimately show ?thesis by simp
        qed
      }
      ultimately show ?thesis using Some app\<^sub>i by(fastforce simp add: app_def)
    qed simp
    then have "P,T\<^sub>r,mxs,size ?\<tau>s,?xt' \<turnstile> ?is!pc,pc :: ?\<tau>s"
      by(simp add: wt_instr_def)
  }
  ultimately show ?thesis by(simp add:wt_instrs_def)
qed

declare [[simproc add: list_to_set_comprehension]]
declare nth_append[simp]
(*>*)

lemma drop_Cons_Suc:
  "\<And>xs. drop n xs = y#ys \<Longrightarrow> drop (Suc n) xs = ys"
proof(induct n)
  case (Suc n) then show ?case by(simp add: drop_Suc)
qed simp

lemma drop_mess:
assumes "Suc (length xs\<^sub>0) \<le> length xs"
  and "drop (length xs - Suc (length xs\<^sub>0)) xs = x # xs\<^sub>0"
shows "drop (length xs - length xs\<^sub>0) xs = xs\<^sub>0"
using assms proof(cases xs)
  case (Cons a list) then show ?thesis using assms
  proof(cases "length list - length xs\<^sub>0")
    case Suc then show ?thesis using Cons assms
      by (simp add: Suc_diff_le drop_Cons_Suc)
  qed simp
qed simp

(*<*)
declare (in TC0)
  after_def[simp] pair_eq_ty\<^sub>i'_conv[simp]
(*>*)

lemma (in TC1) compT_ST_prefix:
 "\<And>E A ST\<^sub>0. \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST\<^sub>0 e) \<Longrightarrow> 
  size ST\<^sub>0 \<le> size ST \<and> drop (size ST - size ST\<^sub>0) ST = ST\<^sub>0"
and
 "\<And>E A ST\<^sub>0. \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST\<^sub>0 es) \<Longrightarrow> 
  size ST\<^sub>0 \<le> size ST \<and> drop (size ST - size ST\<^sub>0) ST = ST\<^sub>0"
(*<*)
proof(induct e and es rule: compT.induct compTs.induct)
  case (FAss e\<^sub>1 F D e\<^sub>2)
  moreover {
    let ?ST\<^sub>0 = "ty E e\<^sub>1 # ST\<^sub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST\<^sub>0 e\<^sub>2)"
    with FAss
    have "length ?ST\<^sub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^sub>0) ST = ?ST\<^sub>0" by blast
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
    let ?ST\<^sub>0 = "ty E e # ST\<^sub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^sub>0 es)"
    with Call
    have "length ?ST\<^sub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^sub>0) ST = ?ST\<^sub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (Cons_exp e es)
  moreover {
    let ?ST\<^sub>0 = "ty E e # ST\<^sub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^sub>0 es)"
    with Cons_exp
    have "length ?ST\<^sub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^sub>0) ST = ?ST\<^sub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (BinOp e\<^sub>1 bop e\<^sub>2)
  moreover {
    let ?ST\<^sub>0 = "ty E e\<^sub>1 # ST\<^sub>0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST\<^sub>0 e\<^sub>2)"
    with BinOp 
    have "length ?ST\<^sub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^sub>0) ST = ?ST\<^sub>0" by blast
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
  after_def[simp del] pair_eq_ty\<^sub>i'_conv[simp del]
(*>*)

(* FIXME *)
lemma fun_of_simp [simp]: "fun_of S x y = ((x,y) \<in> S)" 
(*<*) by (simp add: fun_of_def)(*>*)

theorem (in TC2) compT_wt_instrs: "\<And>E T A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 e :: T; \<D> e A; \<B> e (size E); 
    size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl \<rbrakk>
  \<Longrightarrow> \<turnstile> compE\<^sub>2 e, compxE\<^sub>2 e 0 (size ST) [::]
                 ty\<^sub>i' ST E A # compT E A ST e @ [after E A ST e]"
(*<*)(is "\<And>E T A ST. PROP ?P e E T A ST")(*>*)

and "\<And>E Ts A ST.
  \<lbrakk> P,E \<turnstile>\<^sub>1 es[::]Ts;  \<D>s es A; \<B>s es (size E); 
    size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl \<rbrakk>
  \<Longrightarrow> let \<tau>s = ty\<^sub>i' ST E A # compTs E A ST es in
       \<turnstile> compEs\<^sub>2 es,compxEs\<^sub>2 es 0 (size ST) [::] \<tau>s \<and>
       last \<tau>s = ty\<^sub>i' (rev Ts @ ST) E (A \<squnion> \<A>s es)"
(*<*)
(is "\<And>E Ts A ST. PROP ?Ps es E Ts A ST")
proof(induct e and es rule: compxE\<^sub>2.induct compxEs\<^sub>2.induct)
  case (TryCatch e\<^sub>1 C i e\<^sub>2)
  hence [simp]: "i = size E" by simp
  have wt\<^sub>1: "P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T" and wt\<^sub>2: "P,E@[Class C] \<turnstile>\<^sub>1 e\<^sub>2 :: T"
    and "class": "is_class P C" using TryCatch by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>i = "A \<squnion> \<lfloor>{i}\<rfloor>" let ?E\<^sub>i = "E @ [Class C]"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (T#ST) E ?A\<^sub>1" let ?\<tau>\<^sub>2 = "ty\<^sub>i' (Class C#ST) E A"
  let ?\<tau>\<^sub>3 = "ty\<^sub>i' ST ?E\<^sub>i ?A\<^sub>i" let ?\<tau>s\<^sub>2 = "compT ?E\<^sub>i ?A\<^sub>i ST e\<^sub>2"
  let ?\<tau>\<^sub>2' = "ty\<^sub>i' (T#ST) ?E\<^sub>i (?A\<^sub>i \<squnion> \<A> e\<^sub>2)"
  let ?\<tau>' = "ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> i))"
  let ?go = "Goto (int(size(compE\<^sub>2 e\<^sub>2)) + 2)"
  have "PROP ?P e\<^sub>2 ?E\<^sub>i T ?A\<^sub>i ST" by fact
  hence "\<turnstile> compE\<^sub>2 e\<^sub>2,compxE\<^sub>2 e\<^sub>2 0 (size ST) [::] (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2) @ [?\<tau>\<^sub>2']"
    using TryCatch.prems by(auto simp:after_def)
  also have "?A\<^sub>i \<squnion> \<A> e\<^sub>2 = (A \<squnion> \<A> e\<^sub>2) \<squnion> \<lfloor>{size E}\<rfloor>"
    by(fastforce simp:hyperset_defs)
  also have "P \<turnstile> ty\<^sub>i' (T#ST) ?E\<^sub>i \<dots> \<le>' ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>2)"
    by(simp add:hyperset_defs ty\<^sub>l_incr ty\<^sub>i'_def)
  also have "P \<turnstile> \<dots> \<le>' ty\<^sub>i' (T#ST) E (A \<squnion> \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> i))"
    by(auto intro!: ty\<^sub>l_antimono simp:hyperset_defs ty\<^sub>i'_def)
  also have "(?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2) @ [?\<tau>'] = ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']" by simp
  also have "\<turnstile> [Store i],[] [::] ?\<tau>\<^sub>2 # [] @ [?\<tau>\<^sub>3]"
    using TryCatch.prems
    by(auto simp:nth_list_update wt_defs ty\<^sub>i'_def ty\<^sub>l_def
      list_all2_conv_all_nth hyperset_defs)
  also have "[] @ (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']) = (?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>'])" by simp
  also have "P,T\<^sub>r,mxs,size(compE\<^sub>2 e\<^sub>2)+3,[] \<turnstile> ?go,0 :: ?\<tau>\<^sub>1#?\<tau>\<^sub>2#?\<tau>\<^sub>3#?\<tau>s\<^sub>2 @ [?\<tau>']"
    by (auto simp: hyperset_defs ty\<^sub>i'_def wt_defs nth_Cons nat_add_distrib
      fun_of_def intro: ty\<^sub>l_antimono list_all2_refl split:nat.split)
  also have "\<turnstile> compE\<^sub>2 e\<^sub>1,compxE\<^sub>2 e\<^sub>1 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>1]"
    using TryCatch by(auto simp:after_def)
  also have "?\<tau> # ?\<tau>s\<^sub>1 @ ?\<tau>\<^sub>1 # ?\<tau>\<^sub>2 # ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>'] =
             (?\<tau> # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>1]) @ ?\<tau>\<^sub>2 # ?\<tau>\<^sub>3 # ?\<tau>s\<^sub>2 @ [?\<tau>']" by simp
  also have "compE\<^sub>2 e\<^sub>1 @ ?go  # [Store i] @ compE\<^sub>2 e\<^sub>2 =
             (compE\<^sub>2 e\<^sub>1 @ [?go]) @ (Store i # compE\<^sub>2 e\<^sub>2)" by simp
  also 
  let "?Q \<tau>" = "\<forall>ST' LT'. \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> 
    size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^sub>i' ST E A"
  {
    have "?Q (ty\<^sub>i' ST E A)" by (clarsimp simp add: ty\<^sub>i'_def)
    moreover have "?Q (ty\<^sub>i' (T # ST) E ?A\<^sub>1)" 
      by (fastforce simp add: ty\<^sub>i'_def hyperset_defs intro!: ty\<^sub>l_antimono)
    moreover have "\<And>\<tau>. \<tau> \<in> set (compT E A ST e\<^sub>1) \<Longrightarrow> ?Q \<tau>" using TryCatch.prems
      by clarsimp (frule compT_ST_prefix,
                   fastforce dest!: compT_LT_prefix simp add: ty\<^sub>i'_def)
    ultimately
    have "\<forall>\<tau>\<in>set (ty\<^sub>i' ST E A # compT E A ST e\<^sub>1 @ [ty\<^sub>i' (T # ST) E ?A\<^sub>1]). ?Q \<tau>" 
      by auto
  }
  also from TryCatch.prems max_stack1[of e\<^sub>1] have "size ST + 1 \<le> mxs" by auto
  ultimately show ?case using wt\<^sub>1 wt\<^sub>2 TryCatch.prems "class"
    by (simp add:after_def)
next
  case new thus ?case by(auto simp add:after_def wt_New)
next
  case (BinOp e\<^sub>1 bop e\<^sub>2) 
  let ?op = "case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]"
  have T: "P,E \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T" by fact
  then obtain T\<^sub>1 T\<^sub>2 where T\<^sub>1: "P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T\<^sub>1" and T\<^sub>2: "P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T\<^sub>2" and 
    bopT: "case bop of Eq \<Rightarrow> (P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1) \<and> T = Boolean 
                    | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer" by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>2 = "?A\<^sub>1 \<squnion> \<A> e\<^sub>2"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (T\<^sub>1#ST) E ?A\<^sub>1" let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>1 (T\<^sub>1#ST) e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' (T\<^sub>2#T\<^sub>1#ST) E ?A\<^sub>2" let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A\<^sub>2"
  from bopT have "\<turnstile> ?op,[] [::] [?\<tau>\<^sub>2,?\<tau>']" 
    by (cases bop) (auto simp add: wt_CmpEq wt_IAdd)
  also have "PROP ?P e\<^sub>2 E T\<^sub>2 ?A\<^sub>1 (T\<^sub>1#ST)" by fact
  with BinOp.prems T\<^sub>2 
  have "\<turnstile> compE\<^sub>2 e\<^sub>2, compxE\<^sub>2 e\<^sub>2 0 (size (T\<^sub>1#ST)) [::] ?\<tau>\<^sub>1#?\<tau>s\<^sub>2@[?\<tau>\<^sub>2]" 
    by (auto simp: after_def)
  also from BinOp T\<^sub>1 have "\<turnstile> compE\<^sub>2 e\<^sub>1, compxE\<^sub>2 e\<^sub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>1@[?\<tau>\<^sub>1]" 
    by (auto simp: after_def)
  finally show ?case using T T\<^sub>1 T\<^sub>2 by (simp add: after_def hyperUn_assoc)
next
  case (Cons_exp e es)
  have "P,E \<turnstile>\<^sub>1 e # es [::] Ts" by fact
  then obtain T\<^sub>e Ts' where 
    T\<^sub>e: "P,E \<turnstile>\<^sub>1 e :: T\<^sub>e" and Ts': "P,E \<turnstile>\<^sub>1 es [::] Ts'" and
    Ts: "Ts = T\<^sub>e#Ts'" by auto
  let ?A\<^sub>e = "A \<squnion> \<A> e"  
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"  
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (T\<^sub>e#ST) E ?A\<^sub>e" let ?\<tau>s' = "compTs E ?A\<^sub>e (T\<^sub>e#ST) es"
  let ?\<tau>s = "?\<tau> # ?\<tau>s\<^sub>e @ (?\<tau>\<^sub>e # ?\<tau>s')"
  have Ps: "PROP ?Ps es E Ts' ?A\<^sub>e (T\<^sub>e#ST)" by fact
  with Cons_exp.prems T\<^sub>e Ts'
  have "\<turnstile> compEs\<^sub>2 es, compxEs\<^sub>2 es 0 (size (T\<^sub>e#ST)) [::] ?\<tau>\<^sub>e#?\<tau>s'" by (simp add: after_def)
  also from Cons_exp T\<^sub>e have "\<turnstile> compE\<^sub>2 e, compxE\<^sub>2 e 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>e@[?\<tau>\<^sub>e]" 
    by (auto simp: after_def)
  moreover
  from Ps Cons_exp.prems T\<^sub>e Ts' Ts
  have "last ?\<tau>s = ty\<^sub>i' (rev Ts@ST) E (?A\<^sub>e \<squnion> \<A>s es)" by simp
  ultimately show ?case using T\<^sub>e by (simp add: after_def hyperUn_assoc)
next
  case (FAss e\<^sub>1 F D e\<^sub>2)
  hence Void: "P,E \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D} := e\<^sub>2 :: Void" by auto
  then obtain C T T' where    
    C: "P,E \<turnstile>\<^sub>1 e\<^sub>1 :: Class C" and sees: "P \<turnstile> C sees F:T in D" and
    T': "P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T'" and T'_T: "P \<turnstile> T' \<le> T" by auto
  let ?A\<^sub>1 = "A \<squnion> \<A> e\<^sub>1" let ?A\<^sub>2 = "?A\<^sub>1 \<squnion> \<A> e\<^sub>2"  
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>1 = "compT E A ST e\<^sub>1"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (Class C#ST) E ?A\<^sub>1" let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>1 (Class C#ST) e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' (T'#Class C#ST) E ?A\<^sub>2" let ?\<tau>\<^sub>3 = "ty\<^sub>i' ST E ?A\<^sub>2"
  let ?\<tau>' = "ty\<^sub>i' (Void#ST) E ?A\<^sub>2"
  from FAss.prems sees T'_T 
  have "\<turnstile> [Putfield F D,Push Unit],[] [::] [?\<tau>\<^sub>2,?\<tau>\<^sub>3,?\<tau>']"
    by (fastforce simp add: wt_Push wt_Put)
  also have "PROP ?P e\<^sub>2 E T' ?A\<^sub>1 (Class C#ST)" by fact
  with FAss.prems T' 
  have "\<turnstile> compE\<^sub>2 e\<^sub>2, compxE\<^sub>2 e\<^sub>2 0 (size ST+1) [::] ?\<tau>\<^sub>1#?\<tau>s\<^sub>2@[?\<tau>\<^sub>2]"
    by (auto simp add: after_def hyperUn_assoc) 
  also from FAss C have "\<turnstile> compE\<^sub>2 e\<^sub>1, compxE\<^sub>2 e\<^sub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^sub>1@[?\<tau>\<^sub>1]" 
    by (auto simp add: after_def)
  finally show ?case using Void C T' by (simp add: after_def hyperUn_assoc) 
next
  case Val thus ?case by(auto simp:after_def wt_Push)
next
  case Cast thus ?case by (auto simp:after_def wt_Cast)
next
  case (Block i T\<^sub>i e)
  let ?\<tau>s = "ty\<^sub>i' ST E A # compT (E @ [T\<^sub>i]) (A\<ominus>i) ST e"
  have IH: "PROP ?P e (E@[T\<^sub>i]) T (A\<ominus>i) ST" by fact
  hence "\<turnstile> compE\<^sub>2 e, compxE\<^sub>2 e 0 (size ST) [::]
         ?\<tau>s @ [ty\<^sub>i' (T#ST) (E@[T\<^sub>i]) (A\<ominus>(size E) \<squnion> \<A> e)]"
    using Block.prems by (auto simp add: after_def)
  also have "P \<turnstile> ty\<^sub>i' (T # ST) (E@[T\<^sub>i]) (A \<ominus> size E \<squnion> \<A> e) \<le>'
                 ty\<^sub>i' (T # ST) (E@[T\<^sub>i]) ((A \<squnion> \<A> e) \<ominus> size E)"
     by(auto simp add:hyperset_defs intro: ty\<^sub>i'_antimono)
  also have "\<dots> = ty\<^sub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
  also have "P \<turnstile> \<dots> \<le>' ty\<^sub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
     by(auto simp add:hyperset_defs intro: ty\<^sub>i'_antimono)
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
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A> c"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (Boolean#ST) E ?A\<^sub>0" let ?\<tau>\<^sub>1 = "ty\<^sub>i' ST E ?A\<^sub>0"
  let ?\<tau>s\<^sub>c = "compT E ?A\<^sub>0 ST c" let ?\<tau>\<^sub>c = "ty\<^sub>i' (Tc#ST) E ?A\<^sub>1"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' ST E ?A\<^sub>1" let ?\<tau>' = "ty\<^sub>i' (Void#ST) E ?A\<^sub>0"
  let ?\<tau>s = "(?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]) @ ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']"
  have "\<turnstile> [],[] [::] [] @ ?\<tau>s" by(simp add:wt_instrs_def)
  also
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE\<^sub>2 e,compxE\<^sub>2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]"
    using While.prems by (auto simp:after_def)
  also
  have "[] @ ?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e) @ ?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>']" by simp
  also
  let ?n\<^sub>e = "size(compE\<^sub>2 e)"  let ?n\<^sub>c = "size(compE\<^sub>2 c)"
  let ?if = "IfFalse (int ?n\<^sub>c + 3)"
  have "\<turnstile> [?if],[] [::] ?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']" 
  proof-{
      show ?thesis
        apply (rule wt_IfFalse)
          apply simp
         apply simp
        apply (subgoal_tac "length (compE\<^sub>2 c) = length (compT E (A \<squnion> \<A> e) ST c) + 1" 
                           "nat (int (length (compE\<^sub>2 c)) + 3 - 2) > length (compT E (A \<squnion> \<A> e) ST c)")
          apply simp+
        done
    }
  qed
  also
  have "(?\<tau> # ?\<tau>s\<^sub>e) @ (?\<tau>\<^sub>e # ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2, ?\<tau>\<^sub>1, ?\<tau>']) = ?\<tau>s" by simp
  also
  have "PROP ?P c E Tc ?A\<^sub>0 ST" by fact
  hence "\<turnstile> compE\<^sub>2 c,compxE\<^sub>2 c 0 (size ST) [::] ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c]"
    using While.prems wtc by (auto simp:after_def)
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c) @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>']" by simp
  also have "\<turnstile> [Pop],[] [::] [?\<tau>\<^sub>c, ?\<tau>\<^sub>2]"  by(simp add:wt_Pop)
  also have "(?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c) @ [?\<tau>\<^sub>c,?\<tau>\<^sub>2,?\<tau>\<^sub>1,?\<tau>'] = ?\<tau>s" by simp
  also let ?go = "Goto (-int(?n\<^sub>c+?n\<^sub>e+2))"
  have "P \<turnstile> ?\<tau>\<^sub>2 \<le>' ?\<tau>" by(fastforce intro: ty\<^sub>i'_antimono simp: hyperset_defs)
  hence "P,T\<^sub>r,mxs,size ?\<tau>s,[] \<turnstile> ?go,?n\<^sub>e+?n\<^sub>c+2 :: ?\<tau>s" 
  proof-{
      let ?t1 = "ty\<^sub>i' ST E A" let ?t2 = "ty\<^sub>i' (Boolean # ST) E (A \<squnion> \<A> e)" let ?t3 = "ty\<^sub>i' ST E (A \<squnion> \<A> e)"
      let ?t4 = "[ty\<^sub>i' (Tc # ST) E (A \<squnion> \<A> e \<squnion> \<A> c), ty\<^sub>i' ST E (A \<squnion> \<A> e \<squnion> \<A> c), ty\<^sub>i' ST E (A \<squnion> \<A> e), ty\<^sub>i' (Void # ST) E (A \<squnion> \<A> e)]"
      let ?c = " compT E (A \<squnion> \<A> e) ST c" let ?e = "compT E A ST e" 
      assume ass: "P \<turnstile> ty\<^sub>i' ST E (A \<squnion> \<A> e \<squnion> \<A> c) \<le>' ?t1"      
      show ?thesis
        apply (rule wt_Goto)
        apply simp
          apply simp
         apply simp
      proof-{
          let ?s1 = "((?t1 # ?e @ [?t2]) @ ?t3 # ?c)"          
          have "length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2 > length ?s1" by auto
          hence "(?s1 @ ?t4) ! (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2) =
                     ?t4 ! (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2 - length ?s1)" 
            by (auto simp only:nth_append split: if_splits)
          hence "(?s1 @ ?t4) ! (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2) = ty\<^sub>i' ST E (A \<squnion> \<A> e \<squnion> \<A> c)" 
            using compT_sizes by auto 
          hence "P \<turnstile> (?s1 @ ?t4) ! (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2) \<le>' ty\<^sub>i' ST E A" 
            using ass by simp
          thus "P \<turnstile> ((?t1 # ?e @ [?t2]) @ ?t3 # ?c @ ?t4) ! (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2) \<le>'
                    ((?t1 # ?e @ [?t2]) @ ?t3 # ?c @ ?t4) ! nat (int (length (compE\<^sub>2 e) + length (compE\<^sub>2 c) + 2) +
                      - int (length (compE\<^sub>2 c) + length (compE\<^sub>2 e) + 2))"
            by simp
        }qed
    }qed
  also have "?\<tau>s = (?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e,?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>c @ [?\<tau>\<^sub>c, ?\<tau>\<^sub>2]) @ [?\<tau>\<^sub>1, ?\<tau>']"
    by simp
  also have "\<turnstile> [Push Unit],[] [::] [?\<tau>\<^sub>1,?\<tau>']"
    using While.prems max_stack1[of c] by(auto simp add:wt_Push)
  finally show ?case using wtc wte
    by (simp add:after_def)
next
  case (Cond e e\<^sub>1 e\<^sub>2)
  obtain T\<^sub>1 T\<^sub>2 where wte: "P,E \<turnstile>\<^sub>1 e :: Boolean"
    and wt\<^sub>1: "P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T\<^sub>1" and wt\<^sub>2: "P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T\<^sub>2"
    and sub\<^sub>1: "P \<turnstile> T\<^sub>1 \<le> T" and sub\<^sub>2: "P \<turnstile> T\<^sub>2 \<le> T"
    using Cond by auto
  have [simp]: "ty E (if (e) e\<^sub>1 else e\<^sub>2) = T" using Cond by simp
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>2 = "?A\<^sub>0 \<squnion> \<A> e\<^sub>2" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A> e\<^sub>1"
  let ?A' = "?A\<^sub>0 \<squnion> \<A> e\<^sub>1 \<sqinter> \<A> e\<^sub>2"
  let ?\<tau>\<^sub>2 = "ty\<^sub>i' ST E ?A\<^sub>0" let ?\<tau>' = "ty\<^sub>i' (T#ST) E ?A'"
  let ?\<tau>s\<^sub>2 = "compT E ?A\<^sub>0 ST e\<^sub>2"
  have "PROP ?P e\<^sub>2 E T\<^sub>2 ?A\<^sub>0 ST" by fact
  hence "\<turnstile> compE\<^sub>2 e\<^sub>2, compxE\<^sub>2 e\<^sub>2 0 (size ST) [::] (?\<tau>\<^sub>2#?\<tau>s\<^sub>2) @ [ty\<^sub>i' (T\<^sub>2#ST) E ?A\<^sub>2]"
    using Cond.prems wt\<^sub>2 by(auto simp add:after_def)
  also have "P \<turnstile> ty\<^sub>i' (T\<^sub>2#ST) E ?A\<^sub>2 \<le>' ?\<tau>'" using sub\<^sub>2
    by(auto simp add: hyperset_defs ty\<^sub>i'_def intro!: ty\<^sub>l_antimono)
  also
  let ?\<tau>\<^sub>3 = "ty\<^sub>i' (T\<^sub>1 # ST) E ?A\<^sub>1"
  let ?g\<^sub>2 = "Goto(int (size (compE\<^sub>2 e\<^sub>2) + 1))"
  from sub\<^sub>1 have "P,T\<^sub>r,mxs,size(compE\<^sub>2 e\<^sub>2)+2,[] \<turnstile> ?g\<^sub>2,0 :: ?\<tau>\<^sub>3#(?\<tau>\<^sub>2#?\<tau>s\<^sub>2)@[?\<tau>']"
    by(auto simp: hyperset_defs wt_defs nth_Cons ty\<^sub>i'_def
             split:nat.split intro!: ty\<^sub>l_antimono)
  also
  let ?\<tau>s\<^sub>1 = "compT E ?A\<^sub>0 ST e\<^sub>1"
  have "PROP ?P e\<^sub>1 E T\<^sub>1 ?A\<^sub>0 ST" by fact
  hence "\<turnstile> compE\<^sub>2 e\<^sub>1,compxE\<^sub>2 e\<^sub>1 0 (size ST) [::] ?\<tau>\<^sub>2 # ?\<tau>s\<^sub>1 @ [?\<tau>\<^sub>3]"
    using Cond.prems wt\<^sub>1 by(auto simp add:after_def)
  also
  let ?\<tau>s\<^sub>1\<^sub>2 = "?\<tau>\<^sub>2 # ?\<tau>s\<^sub>1 @ ?\<tau>\<^sub>3 # (?\<tau>\<^sub>2 # ?\<tau>s\<^sub>2) @ [?\<tau>']"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (Boolean#ST) E ?A\<^sub>0"
  let ?g\<^sub>1 = "IfFalse(int (size (compE\<^sub>2 e\<^sub>1) + 2))"
  let ?code = "compE\<^sub>2 e\<^sub>1 @ ?g\<^sub>2 # compE\<^sub>2 e\<^sub>2"
  have "\<turnstile> [?g\<^sub>1],[] [::] [?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>1\<^sub>2"  
  proof-{
    show ?thesis 
      apply clarsimp
      apply (rule wt_IfFalse)
        apply (simp only:nat_add_distrib)
       apply simp
      apply (auto simp only:nth_append split:if_splits)     
      apply (simp only:compT_sizes)
      apply simp
      done
  }qed
  also (wt_instrs_ext2) have "[?\<tau>\<^sub>1] @ ?\<tau>s\<^sub>1\<^sub>2 = ?\<tau>\<^sub>1 # ?\<tau>s\<^sub>1\<^sub>2" by simp also
  let ?\<tau> = "ty\<^sub>i' ST E A"
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE\<^sub>2 e, compxE\<^sub>2 e 0 (size ST) [::] ?\<tau> # compT E A ST e @ [?\<tau>\<^sub>1]"
    using Cond.prems wte by(auto simp add:after_def)
  finally show ?case using wte wt\<^sub>1 wt\<^sub>2 by(simp add:after_def hyperUn_assoc)
next
  case (Call e M es)
  obtain C D Ts m Ts' where C: "P,E \<turnstile>\<^sub>1 e :: Class C"
    and "method": "P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"
    and wtes: "P,E \<turnstile>\<^sub>1 es [::] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
    using Call.prems by auto
  from wtes have same_size: "size es = size Ts'" by(rule WTs\<^sub>1_same_size)
  let ?A\<^sub>0 = "A \<squnion> \<A> e" let ?A\<^sub>1 = "?A\<^sub>0 \<squnion> \<A>s es"
  let ?\<tau> = "ty\<^sub>i' ST E A" let ?\<tau>s\<^sub>e = "compT E A ST e"
  let ?\<tau>\<^sub>e = "ty\<^sub>i' (Class C # ST) E ?A\<^sub>0"
  let ?\<tau>s\<^sub>e\<^sub>s = "compTs E ?A\<^sub>0 (Class C # ST) es"
  let ?\<tau>\<^sub>1 = "ty\<^sub>i' (rev Ts' @ Class C # ST) E ?A\<^sub>1"
  let ?\<tau>' = "ty\<^sub>i' (T # ST) E ?A\<^sub>1"
  have "\<turnstile> [Invoke M (size es)],[] [::] [?\<tau>\<^sub>1,?\<tau>']"
    by(rule wt_Invoke[OF same_size "method" subs])
  also
  have "PROP ?Ps es E Ts' ?A\<^sub>0 (Class C # ST)" by fact
  hence "\<turnstile> compEs\<^sub>2 es,compxEs\<^sub>2 es 0 (size ST+1) [::] ?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s"
        "last (?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s) = ?\<tau>\<^sub>1"
    using Call.prems wtes by(auto simp add:after_def)
  also have "(?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s) @ [?\<tau>'] = ?\<tau>\<^sub>e # ?\<tau>s\<^sub>e\<^sub>s @ [?\<tau>']" by simp
  also have "\<turnstile> compE\<^sub>2 e,compxE\<^sub>2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^sub>e @ [?\<tau>\<^sub>e]"
    using Call C by(auto simp add:after_def)
  finally show ?case using Call.prems C by(simp add:after_def hyperUn_assoc)
next
  case Seq thus ?case
    by(auto simp:after_def)
      (fastforce simp:wt_Push wt_Pop hyperUn_assoc
                intro:wt_instrs_app2 wt_instrs_Cons)
qed
(*>*)


lemma [simp]: "types (compP f P) = types P"
(*<*)by auto(*>*)

lemma [simp]: "states (compP f P) mxs mxl = states P mxs mxl"
(*<*)by (simp add: JVM_states_unfold)(*>*)

lemma [simp]: "app\<^sub>i (i, compP f P, pc, mpc, T, \<tau>) = app\<^sub>i (i, P, pc, mpc, T, \<tau>)"
(*<*)(is "?A = ?B")
proof -
  obtain ST LT where \<tau>: "\<tau> = (ST, LT)" by(cases \<tau>) simp
  then show ?thesis proof(cases i)
    case Invoke show ?thesis
    proof(rule iffI)
      assume ?A then show ?B using Invoke \<tau>
        by auto (fastforce dest!: sees_method_compPD)
    next
      assume ?B then show ?A using Invoke \<tau>
        by auto (force dest: sees_method_compP)
    qed
  qed auto
qed
(*>*)
  
lemma [simp]: "is_relevant_entry (compP f P) i = is_relevant_entry P i"
(*<*)
proof -
  { fix pc e
    have "is_relevant_entry (compP f P) i pc e = is_relevant_entry P i pc e"
      by(cases i) (auto simp: is_relevant_entry_def)
  }
  then show ?thesis by fast
qed
(*>*)

lemma [simp]: "relevant_entries (compP f P) i pc xt = relevant_entries P i pc xt"
(*<*) by (simp add: relevant_entries_def)(*>*)

lemma [simp]: "app i (compP f P) mpc T pc mxl xt \<tau> = app i P mpc T pc mxl xt \<tau>"
(*<*)
by (simp add: app_def xcpt_app_def eff_def xcpt_eff_def norm_eff_def)
   (fastforce simp add: image_def)
(*>*)

lemma [simp]:
assumes "app i P mpc T pc mxl xt \<tau>"
shows "eff i (compP f P) pc xt \<tau> = eff i P pc xt \<tau>"
(*<*)
using assms
proof(clarsimp simp: eff_def norm_eff_def xcpt_eff_def app_def, cases i)
qed auto
(*>*)

lemma [simp]: "subtype (compP f P) = subtype P"
(*<*)by (rule ext)+ simp(*>*)
  
lemma [simp]: "compP f P \<turnstile> \<tau> \<le>' \<tau>' = P \<turnstile> \<tau> \<le>' \<tau>'"
(*<*) by (simp add: sup_state_opt_def sup_state_def sup_ty_opt_def)(*>*)

lemma [simp]: "compP f P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s = P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s"
(*<*)by (simp add: wt_instr_def cong: conj_cong)(*>*)

declare TC1.compT_sizes[simp]  TC0.ty_def2[simp]

context TC2
begin

lemma compT_method:
  fixes e and A and C and Ts and mxl\<^sub>0
  defines [simp]: "E \<equiv> Class C # Ts"
    and [simp]: "A \<equiv> \<lfloor>{..size Ts}\<rfloor>"
    and [simp]: "A' \<equiv> A \<squnion> \<A> e"
    and [simp]: "mxl\<^sub>0 \<equiv> max_vars e"
  assumes mxs: "max_stack e = mxs"
    and mxl: "Suc (length Ts + max_vars e) = mxl"
  assumes wf: "wf_prog p P" and wte: "P,E \<turnstile>\<^sub>1 e :: T" and \<D>: "\<D> e A"
    and \<B>: "\<B> e (size E)" and E_P: "set E \<subseteq> types P" and wid: "P \<turnstile> T \<le> T\<^sub>r"
  shows "wt_method (compP\<^sub>2 P) C Ts T\<^sub>r mxs mxl\<^sub>0 (compE\<^sub>2 e @ [Return])
    (compxE\<^sub>2 e 0 0) (ty\<^sub>i' [] E A # compT\<^sub>a E A [] e)"
(*<*)(is "wt_method ?P C Ts T\<^sub>r mxs mxl\<^sub>0 ?is ?xt ?\<tau>s")
proof -
  let ?n = "length E + mxl\<^sub>0"
  have wt_compE: "P,T\<^sub>r,mxs \<turnstile> compE\<^sub>2 e, compxE\<^sub>2 e 0 (length []) [::]
        TC0.ty\<^sub>i' ?n [] E A # TC1.compT P ?n E A [] e @[TC0.after P ?n E A [] e]"
    using mxs TC2.compT_wt_instrs [OF wte \<D> \<B>, of "[]" mxs ?n T\<^sub>r] by simp

  have "OK (ty\<^sub>i' [T] E A') \<in> states P mxs mxl"
    using mxs WT\<^sub>1_is_type[OF wf wte E_P] max_stack1[of e] OK_ty\<^sub>i'_in_statesI[OF E_P]
      by simp
  moreover have "OK ` set (compT E A [] e) \<subseteq> states P mxs mxl"
    using mxs mxl wid compT_states(1)[OF wf wte E_P] by simp
  ultimately have "check_types ?P mxs ?n (map OK ?\<tau>s)"
    using mxl wte E_P by (simp add: compT\<^sub>a_def after_def check_types_def)
  moreover have "wt_start ?P C Ts mxl\<^sub>0 ?\<tau>s" using mxl
    by (auto simp: wt_start_def ty\<^sub>i'_def ty\<^sub>l_def list_all2_conv_all_nth nth_Cons
             split: nat.split)
  moreover {
    fix pc assume pc: "pc < size ?is"
    then have "?P,T\<^sub>r,mxs,size ?is,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
    proof(cases "pc < length (compE\<^sub>2 e)")
      case True
      then show ?thesis using mxs wte wt_compE
        by (clarsimp simp: compT\<^sub>a_def mxl after_def wt_instrs_def)
    next
      case False
      have "length (compE\<^sub>2 e) = pc" using less_antisym[OF False] pc by simp
      then show ?thesis using mxl wte E_P wid
        by (clarsimp simp: compT\<^sub>a_def after_def wt_defs xcpt_app_pcs xcpt_eff_pcs ty\<^sub>i'_def)
    qed
  }
  moreover have "0 < size ?is" and "size ?\<tau>s = size ?is"
    using wte by (simp_all add: compT\<^sub>a_def)
  ultimately show ?thesis by(simp add: wt_method_def)
qed
(*>*)

end

definition compTP :: "J\<^sub>1_prog \<Rightarrow> ty\<^sub>P" where
  "compTP P C M = (
  let (D,Ts,T,e) = method P C M;
       E = Class C # Ts;
       A = \<lfloor>{..size Ts}\<rfloor>;
       mxl = 1 + size Ts + max_vars e
  in  (TC0.ty\<^sub>i' mxl [] E A # TC1.compT\<^sub>a P mxl E A [] e))"

theorem wt_compP\<^sub>2:
assumes wf: "wf_J\<^sub>1_prog P" shows "wf_jvm_prog (compP\<^sub>2 P)"
(*<*)
proof -
  let ?\<Phi> = "compTP P" and ?f = compMb\<^sub>2
  let ?wf\<^sub>2 = "\<lambda>P C (M, Ts, T\<^sub>r, mxs, mxl\<^sub>0, is, xt).
              wt_method P C Ts T\<^sub>r mxs mxl\<^sub>0 is xt (?\<Phi> C M)"
    and ?P = "compP ?f P"
  { fix C M Ts T m
    assume cM: "P \<turnstile> C sees M :  Ts\<rightarrow>T = m in C"
      and wfm: "wf_mdecl wf_J\<^sub>1_mdecl P C (M,Ts,T,m)"
    then have Ts_types: "\<forall>T'\<in>set Ts. is_type P T'"
     and T_type: "is_type P T" and wfm\<^sub>1: "wf_J\<^sub>1_mdecl P C (M,Ts,T,m)"
      by(simp_all add: wf_mdecl_def)
    then obtain T' where wte: "P,Class C#Ts \<turnstile>\<^sub>1 m :: T'" and wid: "P \<turnstile> T' \<le> T"
       and \<D>: "\<D> m \<lfloor>{..size Ts}\<rfloor>" and \<B>: "\<B> m (Suc (size Ts))"
      by(auto simp: wf_mdecl_def)
    have CTs_P: "is_class P C \<and> set Ts \<subseteq> types P"
      using sees_wf_mdecl[OF wf cM] sees_method_is_class[OF cM]
       by (clarsimp simp: wf_mdecl_def)

    have "?wf\<^sub>2 ?P C (M,Ts,T,?f m)"
      using cM TC2.compT_method [simplified, OF _ _ wf wte \<D> \<B> CTs_P wid]
       by(simp add: compTP_def)
    then have "wf_mdecl ?wf\<^sub>2 ?P C (M, Ts, T, ?f m)"
      using Ts_types T_type by(simp add: wf_mdecl_def)
  }
  then have "wf_prog ?wf\<^sub>2 (compP ?f P)" by(rule wf_prog_compPI[OF _ wf])
  then show ?thesis by (simp add: wf_jvm_prog_def wf_jvm_prog_phi_def) fast
qed
(*>*)

theorem wt_J2JVM:
  "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
(*<*)
by(simp only:o_def J2JVM_def)
  (blast intro:wt_compP\<^sub>2 compP\<^sub>1_pres_wf)

end
