(*  Title:      JinjaThreads/Compiler/TypeComp.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

header {* \isaheader{Preservation of Well-Typedness in Stage 2} *}

theory TypeComp
imports Compiler2_AddOn "J1WellForm" "../BV/BVSpec" List_Prefix
begin


(*<*)
declare nth_append[simp]
(*>*)


locale TC0 =
  fixes P :: J1_prog and mxl :: nat and wfmd
  assumes wf_prog: "wf_prog wfmd P"
begin

definition ty :: "ty list \<Rightarrow> expr1 \<Rightarrow> ty"
where "ty E e \<equiv> THE T. P,E \<turnstile>1 e :: T"

definition ty\<^isub>l :: "ty list \<Rightarrow> nat set \<Rightarrow> ty\<^isub>l"
where "ty\<^isub>l E A' \<equiv> map (\<lambda>i. if i \<in> A' \<and> i < size E then OK(E!i) else Err) [0..<mxl]"

definition ty\<^isub>i' :: "ty list \<Rightarrow> ty list \<Rightarrow> nat set option \<Rightarrow> ty\<^isub>i'"
where "ty\<^isub>i' ST E A \<equiv> case A of None \<Rightarrow> None | \<lfloor>A'\<rfloor> \<Rightarrow> Some(ST, ty\<^isub>l E A')"

definition after :: "ty list \<Rightarrow> nat set option \<Rightarrow> ty list \<Rightarrow> expr1 \<Rightarrow> ty\<^isub>i'"
  where "after E A ST e \<equiv> ty\<^isub>i' (ty E e # ST) E (A \<squnion> \<A> e)"

lemma ty_def2 [simp]: "P,E \<turnstile>1 e :: T \<Longrightarrow> ty E e = T"
apply(unfold ty_def ty_def)
apply(blast intro: the_equality WT1_unique[OF wf_prog])
done

lemma ty\<^isub>i'_None [simp]: "ty\<^isub>i' ST E None = None"
by(simp add:ty\<^isub>i'_def)

lemma ty\<^isub>l_app_diff[simp]:
 "ty\<^isub>l (E@[T]) (A - {size E}) = ty\<^isub>l E A"
by(auto simp add:ty\<^isub>l_def hyperset_defs)

lemma ty\<^isub>i'_app_diff[simp]:
 "ty\<^isub>i' ST (E @ [T]) (A \<ominus> size E) = ty\<^isub>i' ST E A"
by(auto simp add:ty\<^isub>i'_def hyperset_defs)

lemma ty\<^isub>l_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^isub>l E A' [\<le>\<^sub>\<top>] ty\<^isub>l E A"
by(auto simp:ty\<^isub>l_def list_all2_conv_all_nth)


lemma ty\<^isub>i'_antimono:
 "A \<subseteq> A' \<Longrightarrow> P \<turnstile> ty\<^isub>i' ST E \<lfloor>A'\<rfloor> \<le>' ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)

lemma ty\<^isub>l_env_antimono:
 "P \<turnstile> ty\<^isub>l (E@[T]) A [\<le>\<^sub>\<top>] ty\<^isub>l E A" 
by(auto simp:ty\<^isub>l_def list_all2_conv_all_nth)


lemma ty\<^isub>i'_env_antimono:
 "P \<turnstile> ty\<^isub>i' ST (E@[T]) A \<le>' ty\<^isub>i' ST E A" 
by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)


lemma ty\<^isub>i'_incr:
 "P \<turnstile> ty\<^isub>i' ST (E @ [T]) \<lfloor>insert (size E) A\<rfloor> \<le>' ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
by(auto simp:ty\<^isub>i'_def ty\<^isub>l_def list_all2_conv_all_nth)


lemma ty\<^isub>l_incr:
 "P \<turnstile> ty\<^isub>l (E @ [T]) (insert (size E) A) [\<le>\<^sub>\<top>] ty\<^isub>l E A"
by(auto simp: hyperset_defs ty\<^isub>l_def list_all2_conv_all_nth)


lemma ty\<^isub>l_in_types:
 "set E \<subseteq> types P \<Longrightarrow> ty\<^isub>l E A \<in> list mxl (err (types P))"
by(auto simp add:ty\<^isub>l_def intro!:listI dest!: nth_mem)


primrec compT :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr1 \<Rightarrow> ty\<^isub>i' list"
  and compTs :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr1 list \<Rightarrow> ty\<^isub>i' list"
where
  "compT E A ST (new C) = []"
| "compT E A ST (newA T\<lfloor>e\<rceil>) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (Cast C e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (Val v) = []"
| "compT E A ST (e1 \<guillemotleft>bop\<guillemotright> e2) =
  (let ST1 = ty E e1#ST; A1 = A \<squnion> \<A> e1 in
   compT E A ST e1 @ [after E A ST e1] @
   compT E A1 ST1 e2 @ [after E A1 ST1 e2])"
| "compT E A ST (Var i) = []"
| "compT E A ST (i := e) = compT E A ST e @ [after E A ST e, ty\<^isub>i' ST E (A \<squnion> \<A> e \<squnion> \<lfloor>{i}\<rfloor>)]"
| "compT E A ST (a\<lfloor>i\<rceil>) =
  (let ST1 = ty E a # ST; A1 = A \<squnion> \<A> a
   in  compT E A ST a @ [after E A ST a] @ compT E A1 ST1 i @ [after E A1 ST1 i])"
| "compT E A ST (a\<lfloor>i\<rceil> := e) =
  (let ST1 = ty E a # ST; A1 = A \<squnion> \<A> a;
       ST2 = ty E i # ST1; A2 = A1 \<squnion> \<A> i; A3 = A2 \<squnion> \<A> e
   in compT E A ST a @ [after E A ST a] @ compT E A1 ST1 i @ [after E A1 ST1 i] @ compT E A2 ST2 e @ [after E A2 ST2 e, ty\<^isub>i' ST E A3])"
| "compT E A ST (a\<bullet>length) = compT E A ST a @ [after E A ST a]"
| "compT E A ST (e\<bullet>F{D}) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e1\<bullet>F{D} := e2) =
  (let ST1 = ty E e1#ST; A1 = A \<squnion> \<A> e1; A2 = A1 \<squnion> \<A> e2
   in  compT E A ST e1 @ [after E A ST e1] @ compT E A1 ST1 e2 @ [after E A1 ST1 e2] @ [ty\<^isub>i' ST E A2])"
| "compT E A ST {i:T=vo; e}\<^bsub>cr\<^esub> = 
  (case vo of None \<Rightarrow> compT (E@[T]) (A\<ominus>i) ST e
             | \<lfloor>v\<rfloor> \<Rightarrow> [after E A ST (Val v), ty\<^isub>i' ST (E@[T]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @ compT (E@[T]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e)"

| "compT E A ST (sync\<^bsub>i\<^esub> (e1) e2) =
  (let A1 = A \<squnion> \<A> e1 \<squnion> \<lfloor>{i}\<rfloor>; E1 = E @ [Class Object]; ST2 = ty E1 e2 # ST; A2 = A1 \<squnion> \<A> e2
   in  compT E A ST e1 @ [after E A ST e1, ty\<^isub>i' ST E1 A1, ty\<^isub>i' (Class Object # ST) E1 A1, ty\<^isub>i' ST E1 A1] @ compT E1 A1 ST e2 @ 
       [ty\<^isub>i' ST2 E1 A2, ty\<^isub>i' (Class Object # ST2) E1 A2, ty\<^isub>i' ST2 E1 A2, 
        ty\<^isub>i' (Class Throwable # ST) E1 A1, ty\<^isub>i' (Class Object # Class Throwable # ST) E1 A1, ty\<^isub>i' (Class Throwable # ST) E1 A1])"
| "compT E A ST (insync\<^bsub>i\<^esub> (a) e) = []"

| "compT E A ST (e1;;e2) =
  (let A1 = A \<squnion> \<A> e1 in
   compT E A ST e1 @ [after E A ST e1, ty\<^isub>i' ST E A1] @
   compT E A1 ST e2)"
| "compT E A ST (if (e) e1 else e2) =
   (let A0 = A \<squnion> \<A> e; \<tau> = ty\<^isub>i' ST E A0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A0 ST e1 @ [after E A0 ST e1, \<tau>] @
    compT E A0 ST e2)"
| "compT E A ST (while (e) c) =
   (let A0 = A \<squnion> \<A> e;  A1 = A0 \<squnion> \<A> c; \<tau> = ty\<^isub>i' ST E A0 in
    compT E A ST e @ [after E A ST e, \<tau>] @
    compT E A0 ST c @ [after E A0 ST c, ty\<^isub>i' ST E A1, ty\<^isub>i' ST E A0])"
| "compT E A ST (throw e) = compT E A ST e @ [after E A ST e]"
| "compT E A ST (e\<bullet>M(es)) =
   compT E A ST e @ [after E A ST e] @
   compTs E (A \<squnion> \<A> e) (ty E e # ST) es"
| "compT E A ST (try e1 catch(C i) e2) =
   compT E A ST e1 @ [after E A ST e1] @
   [ty\<^isub>i' (Class C#ST) E A, ty\<^isub>i' ST (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>)] @
   compT (E@[Class C]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e2"

| "compTs E A ST [] = []"
| "compTs E A ST (e#es) = compT E A ST e @ [after E A ST e] @
                            compTs E (A \<squnion> (\<A> e)) (ty E e # ST) es"


definition compTa :: "ty list \<Rightarrow> nat hyperset \<Rightarrow> ty list \<Rightarrow> expr1 \<Rightarrow> ty\<^isub>i' list"
where "compTa E A ST e \<equiv> compT E A ST e @ [after E A ST e]"

lemmas compE2_not_Nil = compE2_neq_Nil
declare compE2_not_Nil[simp]

lemma compT_sizes[simp]:
shows "\<And>E A ST. size(compT E A ST e) = size(compE2 e) - 1"
and "\<And>E A ST. size(compTs E A ST es) = size(compEs2 es)"
apply(induct e and es)
apply(auto split:bop.splits nat_diff_split)
done


lemma compT_None_not_Some [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compT E None ST e)"
  and compTs_None_not_Some [simp]: "\<And>ST E. \<lfloor>\<tau>\<rfloor> \<notin> set (compTs E None ST es)"
by(induct e and es) (simp_all add:after_def)


lemma pair_eq_ty\<^isub>i'_conv:
  "(\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST\<^isub>0 E A) = (case A of None \<Rightarrow> False | Some A \<Rightarrow> (ST = ST\<^isub>0 \<and> LT = ty\<^isub>l E A))"
by(simp add:ty\<^isub>i'_def)

lemma pair_conv_ty\<^isub>i': "\<lfloor>(ST, ty\<^isub>l E A)\<rfloor> = ty\<^isub>i' ST E \<lfloor>A\<rfloor>"
by(simp add:ty\<^isub>i'_def)

declare ty\<^isub>i'_antimono [intro!] after_def[simp] pair_conv_ty\<^isub>i'[simp] pair_eq_ty\<^isub>i'_conv[simp]

lemma compT_LT_prefix:
  "\<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST0 e); \<B> e (size E) \<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^isub>i' ST E A"
  and compTs_LT_prefix:
  "\<lbrakk> \<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST0 es); \<B>s es (size E) \<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST,LT)\<rfloor> \<le>' ty\<^isub>i' ST E A"
proof(induct e and es arbitrary: E A ST0 and E A ST0)
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
  case (Block V T vo exp cr)
  note IH = `\<And>E A ST0. \<lbrakk>\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 exp); \<B> exp (length E)\<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST, LT)\<rfloor> \<le>' ty\<^isub>i' ST E A`
  from `\<B> {V:T=vo; exp}\<^bsub>cr\<^esub> (length E)` have [simp]: "V = length E" and B: "\<B> exp (length (E@[T]))" by auto
  note STLT = `\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 {V:T=vo; exp}\<^bsub>cr\<^esub>)`
  show ?case
  proof(cases vo)
    case None
    note None[simp]
    from STLT have "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT (E @ [T]) (A \<ominus> length E) ST0 exp)" by simp
    from IH[OF this B] show ?thesis by(simp)
  next
    case (Some v)
    note Some[simp]
    from STLT have "((\<lfloor>(ST, LT)\<rfloor> = after E A ST0 (Val v)) \<or> (\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST0 (E@[T]) (A \<squnion> \<lfloor>{length E}\<rfloor>))) \<or>
                    \<lfloor>(ST, LT)\<rfloor> \<in> set (compT (E@[T]) (A \<squnion> \<lfloor>{length E}\<rfloor>) ST0 exp)" by simp
    thus ?thesis apply -
    proof(erule disjE)+
      assume "\<lfloor>(ST, LT)\<rfloor> = after E A ST0 (Val v)" thus ?thesis by simp
    next
      assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST0 (E @ [T]) (A \<squnion> \<lfloor>{length E}\<rfloor>)" thus ?thesis
	by(auto simp add: hyperset_defs intro: ty\<^isub>i'_incr)
    next
      assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT (E @ [T]) (A \<squnion> \<lfloor>{length E}\<rfloor>) ST0 exp)"
      from IH[OF this B] show ?thesis
	by(rule sup_state_opt_trans)(simp only: ty\<^isub>i'_def, auto intro: ty\<^isub>i'_incr)
    qed
  qed
next
  case Call thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case Cons_exp thus ?case
    by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case TryCatch thus ?case
    by(fastsimp simp:hyperset_defs intro!: ty\<^isub>i'_incr
                elim!:sup_state_opt_trans)
next
  case (newArray T E) thus ?case by(auto simp add: hyperset_defs)
next
  case AAcc thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case AAss thus ?case by(fastsimp simp:hyperset_defs elim!:sup_state_opt_trans)
next
  case ALen thus ?case by(auto simp add: hyperset_defs)
next
  case (Synchronized i exp1 exp2)
  note IH1 = `\<And>E A ST0. \<lbrakk>\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 exp1); \<B> exp1 (length E)\<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST, LT)\<rfloor> \<le>' ty\<^isub>i' ST E A`
  note IH2 = `\<And>E A ST0. \<lbrakk>\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 exp2); \<B> exp2 (length E)\<rbrakk> \<Longrightarrow> P \<turnstile> \<lfloor>(ST, LT)\<rfloor> \<le>' ty\<^isub>i' ST E A`
  from `\<B> (sync\<^bsub>i\<^esub> (exp1) exp2) (length E)`
  have [simp]: "i = length E" and B1: "\<B> exp1 (length E)" and B2: "\<B> exp2 (length (E@[Class Object]))" by auto
  from `\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 (sync\<^bsub>i\<^esub> (exp1) exp2))` 
  have "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 exp1) \<or>
        \<lfloor>(ST, LT)\<rfloor> = after E A ST0 exp1 \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST0 (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) \<or>
        \<lfloor>(ST, LT)\<rfloor> \<in> set (compT (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) ST0 exp2)  \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (ty (E @ [Class Object]) exp2 # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2) \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # ty (E @ [Class Object]) exp2 # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2) \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Throwable # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) \<or>
        \<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # Class Throwable # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)"
    by(auto simp only: compT_compTs.simps Let_def set_append set.simps mem_simps)
  thus ?case unfolding disj_assoc[symmetric] apply -
  proof(erule disjE)+
    assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ST0 exp1)"
    from IH1[OF this B1] show ?thesis by simp
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = after E A ST0 exp1"
    thus ?thesis by(auto simp add: hyperset_defs)
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' ST0 (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) ST0 exp2)"
    from IH2[OF this B2] show ?thesis
      by(rule sup_state_opt_trans)(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # ty (E @ [Class Object]) exp2 # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (ty (E @ [Class Object]) exp2 # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Throwable # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  next
    assume "\<lfloor>(ST, LT)\<rfloor> = ty\<^isub>i' (Class Object # Class Throwable # ST0) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)"
    thus ?thesis by(auto simp add: hyperset_defs intro: sup_state_opt_trans[OF ty\<^isub>i'_incr])
  qed
qed (auto simp:hyperset_defs)

declare ty\<^isub>i'_antimono [rule del] after_def[simp del] pair_conv_ty\<^isub>i'[simp del] pair_eq_ty\<^isub>i'_conv[simp del]

lemma OK_None_states [iff]: "OK None \<in> states P mxs mxl"
by(simp add: JVM_states_unfold)

lemma [simp]: "x \<in> is_type P \<longleftrightarrow> is_type P x"
by(auto simp add: mem_def)

lemma after_in_states:
 "\<lbrakk> P,E \<turnstile>1 e :: T; set E \<subseteq> is_type P; set ST \<subseteq> is_type P; size ST + max_stack e \<le> mxs \<rbrakk>
 \<Longrightarrow> OK (after E A ST e) \<in> states P mxs mxl"
apply(subgoal_tac "size ST + 1 \<le> mxs")
 apply(simp add:after_def ty\<^isub>i'_def JVM_states_unfold ty\<^isub>l_in_types)
 apply(clarify intro!: exI)
 apply(rule conjI)
  apply(rule exI[where x="length ST + 1"], fastsimp)
 apply(clarsimp)
 apply(rule conjI[OF WT1_is_type[OF wf_prog]], auto intro: listI)
using max_stack1[of e] by simp

lemma OK_ty\<^isub>i'_in_statesI [simp]:
  "\<lbrakk> set E \<subseteq> is_type P; set ST \<subseteq> is_type P; size ST \<le> mxs \<rbrakk>
  \<Longrightarrow> OK (ty\<^isub>i' ST E A) \<in> states P mxs mxl"
apply(simp add:ty\<^isub>i'_def JVM_states_unfold ty\<^isub>l_in_types)
apply(blast intro!:listI)
done



lemma is_class_type_aux: "is_class P C \<Longrightarrow> is_type P (Class C)"
by(simp)

declare is_type.simps[simp del] subsetI[rule del]

theorem
  shows compT_states:
  "\<lbrakk> P,E \<turnstile>1 e :: T; set E \<subseteq> is_type P; set ST \<subseteq> is_type P;
     size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compT E A ST e) \<subseteq> states P mxs mxl"
  (is "PROP ?P e E T A ST")

  and compTs_states: 
  "\<lbrakk> P,E \<turnstile>1 es[::]Ts;  set E \<subseteq> is_type P; set ST \<subseteq> is_type P;
    size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl \<rbrakk>
  \<Longrightarrow> OK ` set(compTs E A ST es) \<subseteq> states P mxs mxl"
    (is "PROP ?Ps es E Ts A ST")
proof(induct e and es arbitrary: E T A ST and E Ts A ST)
  case new thus ?case by(simp)
next
  case (Cast C e) thus ?case by (auto simp:after_in_states)
next
  case Val thus  ?case by(simp)
next
  case Var thus ?case by(simp)
next
  case LAss thus ?case  by(auto simp:after_in_states)
next
  case FAcc thus ?case by(auto simp:after_in_states)
next
  case FAss thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case Seq thus ?case
    by(auto simp:image_Un after_in_states)
next
  case BinOp thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case Cond thus ?case
    by(force simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case While thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case (Block i ty vo exp cr)
  have IH: "\<And>E T A ST. PROP ?P exp E T A ST" by fact
  from `P,E \<turnstile>1 {i:ty=vo; exp}\<^bsub>cr\<^esub> :: T` have wte: "P,E@[ty] \<turnstile>1 exp :: T" and ty: "is_type P ty" by auto
  from ty `set E \<subseteq> is_type P` have E': "set (E@[ty]) \<subseteq> is_type P" by auto
  from `length ST + max_stack {i:ty=vo; exp}\<^bsub>cr\<^esub> \<le> mxs`
  have lenST: "length ST + max_stack exp \<le> mxs" by auto
  from `length E + max_vars {i:ty=vo; exp}\<^bsub>cr\<^esub> \<le> mxl`
  have lenE: "length (E@[ty]) + max_vars exp \<le> mxl" by auto
  note IH' = IH[OF wte E' `set ST \<subseteq> is_type P` lenST lenE]
  show ?case
  proof(cases vo)
    case None thus ?thesis by(auto intro: IH')
  next
    case (Some v)
    from max_stack1[of exp] lenST have "Suc (length ST) \<le> mxs" by simp
    with Some `P,E \<turnstile>1 {i:ty=vo; exp}\<^bsub>cr\<^esub> :: T` `set E \<subseteq> is_type P` `set ST \<subseteq> is_type P`
    have "OK (after E A ST (Val v)) \<in> states P mxs mxl" by(auto intro: after_in_states)
    with Some E' `set ST \<subseteq> is_type P` lenST
    show ?thesis by(auto intro: IH')
  qed
next
  case (TryCatch e\<^isub>1 C i e\<^isub>2)
  moreover have "size ST + 1 \<le> mxs" using TryCatch.prems max_stack1[of e\<^isub>1] by auto
  ultimately show ?case  
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states
                  is_class_type_aux)
next
  case Nil_exp thus ?case by simp
next
  case Cons_exp thus ?case
    by(auto simp:image_Un  WT1_is_type[OF wf_prog] after_in_states)
next
  case throw thus ?case
    by(auto simp: WT1_is_type[OF wf_prog] after_in_states)
next
  case Call thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case newArray thus ?case
    by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case AAcc thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case AAss thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case ALen thus ?case by(auto simp:image_Un WT1_is_type[OF wf_prog] after_in_states)
next
  case InSynchronized thus ?case by auto
next
  case (Synchronized i exp1 exp2)
  note IH1 = `\<And>E T A ST. PROP ?P exp1 E T A ST`
  note IH2 = `\<And>E T A ST. PROP ?P exp2 E T A ST`
  from `P,E \<turnstile>1 sync\<^bsub>i\<^esub> (exp1) exp2 :: T` obtain T1
    where wt1: "P,E \<turnstile>1 exp1 :: T1" and T1: "is_refT T1" "T1 \<noteq> NT"
    and wt2: "P,E@[Class Object] \<turnstile>1 exp2 :: T" by auto
  note E = `set E \<subseteq> is_type P` with wf_prog
  have E': "set (E@[Class Object]) \<subseteq> is_type P" by(auto simp add: is_type.simps)
  from wf_prog wt2 E' have T: "is_type P T" by(rule WT1_is_type)
  note ST = `set ST \<subseteq> is_type P` with wf_prog
  have ST': "set (Class Object # ST) \<subseteq> is_type P" by(auto simp add: is_type.simps)
  from `length ST + max_stack (sync\<^bsub>i\<^esub> (exp1) exp2) \<le> mxs` max_stack1[of exp2]
  have lenST1: "length ST + max_stack exp1 \<le> mxs"
    and lenST2: "length ST + max_stack exp2 \<le> mxs"
    and lenSTS: "Suc (Suc (length ST)) \<le> mxs" by auto
  from `length E + max_vars (sync\<^bsub>i\<^esub> (exp1) exp2) \<le> mxl`
  have lenE1: "length E + max_vars exp1 \<le> mxl"
    and lenE2: "length (E@[Class Object]) + max_vars exp2 \<le> mxl" by auto
  from wf_prog have throwable: "is_type P (Class Throwable)" unfolding is_type.simps
    by(rule converse_subcls_is_class[where C=OutOfMemory])(auto intro: xcpt_subcls_Throwable wf_prog is_class_xcpt)
  show ?case
    unfolding compT_compTs.simps Let_def set.simps set_append image_insert image_Un image_empty 
      Un_subset_iff insert_subset conj_assoc[symmetric] apply -
  proof(rule conjI)+
    from IH1[OF wt1 E ST lenST1 lenE1] show "OK ` set (compT E A ST exp1) \<subseteq> states P mxs mxl" .
  next
    from wt1 E ST lenST1 show "OK (after E A ST exp1) \<in> states P mxs mxl" by(auto simp add: after_in_states)
  next
    from E' ST lenST1 show "OK (ty\<^isub>i' ST (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl" by(simp)
  next
    from lenSTS E' ST'
    show "OK (ty\<^isub>i' (Class Object # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl" by simp
  next
    from E' ST lenST1 show "OK (ty\<^isub>i' ST (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl" by(simp)
  next
    from IH2[OF wt2 E' ST lenST2 lenE2]
    show "OK ` set (compT (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>) ST exp2) \<subseteq> states P mxs mxl" .
  next
    from E' wt2 lenSTS ST T
    show "OK (ty\<^isub>i' (ty (E @ [Class Object]) exp2 # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2)) \<in> states P mxs mxl"
      by(simp)
  next
    from E' wt2 lenSTS ST T
    show "OK (ty\<^isub>i' (ty (E @ [Class Object]) exp2 # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2)) \<in> states P mxs mxl"
      by(simp)
  next
    from E' wt2 lenSTS ST T
    show "OK (ty\<^isub>i' (Class Object # ty (E @ [Class Object]) exp2 # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor> \<squnion> \<A> exp2)) \<in> states P mxs mxl"
      by simp
  next
    from E' lenSTS ST throwable
    show " OK (ty\<^isub>i' (Class Throwable # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl" by simp
  next
    from E lenSTS ST' throwable
    show "OK (ty\<^isub>i' (Class Object # Class Throwable # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl"
      by simp
  next
    from E ST' lenSTS throwable
    show "OK (ty\<^isub>i' (Class Throwable # ST) (E @ [Class Object]) (A \<squnion> \<A> exp1 \<squnion> \<lfloor>{i}\<rfloor>)) \<in> states P mxs mxl" by simp
  qed auto
qed

declare is_type.simps[simp] subsetI[intro!]

end


locale TC2 = TC0 +
  fixes T\<^isub>r :: ty and mxs :: pc
begin
  
definition
  wt_instrs :: "instr list \<Rightarrow> ex_table \<Rightarrow> ty\<^isub>i' list \<Rightarrow> bool" ("(\<turnstile> _, _ /[::]/ _)" [0,0,51] 50)
where
  "\<turnstile> is,xt [::] \<tau>s \<equiv> size is < size \<tau>s \<and> pcs xt \<subseteq> {0..<size is} \<and> (\<forall>pc< size is. P,T\<^isub>r,mxs,size \<tau>s,xt \<turnstile> is!pc,pc :: \<tau>s)"

lemmas wt_defs = wt_instrs_def wt_instr_def app_def eff_def norm_eff_def

lemma wt_instrs_Nil [simp]: "\<tau>s \<noteq> [] \<Longrightarrow> \<turnstile> [],[] [::] \<tau>s"
by(simp add:wt_defs)

end


lemma eff_None [simp]: "eff i P pc et None = []"
by (simp add: Effect.eff_def)

declare split_comp_eq[simp del]

lemma wt_instr_appR:
 "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s;
    pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s; mpc \<le> mpc' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc',xt \<turnstile> is!pc,pc :: \<tau>s@\<tau>s'"
by (fastsimp simp:wt_instr_def app_def)


lemma relevant_entries_shift [simp]:
  "relevant_entries P i (pc+n) (shift n xt) = shift n (relevant_entries P i pc xt)"
  apply (induct xt)
  apply (unfold relevant_entries_def shift_def) 
   apply simp
  apply (auto simp add: is_relevant_entry_def)
  done



lemma xcpt_eff_shift [simp]:
  "xcpt_eff i P (pc+n) \<tau> (shift n xt) =
   map (\<lambda>(pc,\<tau>). (pc + n, \<tau>)) (xcpt_eff i P pc \<tau> xt)"
apply(simp add: xcpt_eff_def)
apply(cases \<tau>)
apply(auto simp add: shift_def map_compose [symmetric])
done


lemma  eff_shift [simp]:
  "app\<^isub>i (i, P, pc, m, T, \<tau>) \<Longrightarrow>
   eff i P (pc+n) (shift n xt) (Some \<tau>) =
   map (\<lambda>(pc,\<tau>). (pc+n,\<tau>)) (eff i P pc xt (Some \<tau>))"
apply(simp add:eff_def norm_eff_def)
apply(cases "i",auto)
done


lemma xcpt_app_shift [simp]:
  "xcpt_app i P (pc+n) m (shift n xt) \<tau> = xcpt_app i P pc m xt \<tau>"
by (simp add: xcpt_app_def) (auto simp add: shift_def)


lemma wt_instr_appL:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc + size \<tau>s',shift (size \<tau>s') xt \<turnstile> i,pc+size \<tau>s' :: \<tau>s'@\<tau>s"
apply(clarsimp simp add: wt_instr_def app_def)
apply(auto)
apply(cases "i", auto)
done


lemma wt_instr_Cons:
  "\<lbrakk> P,T,m,mpc - 1,[] \<turnstile> i,pc - 1 :: \<tau>s;
     0 < pc; 0 < mpc; pc < size \<tau>s + 1; mpc \<le> size \<tau>s + 1 \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>#\<tau>s"
apply(drule wt_instr_appL[where \<tau>s' = "[\<tau>]"])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done


lemma wt_instr_append:
  "\<lbrakk> P,T,m,mpc - size \<tau>s',[] \<turnstile> i,pc - size \<tau>s' :: \<tau>s;
     size \<tau>s' \<le> pc; size \<tau>s' \<le> mpc; pc < size \<tau>s + size \<tau>s'; mpc \<le> size \<tau>s + size \<tau>s' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,[] \<turnstile> i,pc :: \<tau>s'@\<tau>s"
apply(drule wt_instr_appL[where \<tau>s' = \<tau>s'])
apply arith
apply arith
apply (simp split:nat_diff_split_asm)
done


lemma xcpt_app_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_app i P pc mxs xt \<tau>"
by (auto simp add: xcpt_app_def relevant_entries_def is_relevant_entry_def pcs_def)


lemma xcpt_eff_pcs:
  "pc \<notin> pcs xt \<Longrightarrow> xcpt_eff i P pc \<tau> xt = []"
by (cases \<tau>)
   (auto simp add: is_relevant_entry_def xcpt_eff_def relevant_entries_def pcs_def
           intro!: filter_False)


lemma pcs_shift:
  "pc < n \<Longrightarrow> pc \<notin> pcs (shift n xt)" 
by (auto simp add: shift_def pcs_def)

lemma xcpt_eff_shift_pc_ge_n: assumes "x \<in> set (xcpt_eff i P pc \<tau> (shift n xt))"
  shows "n \<le> pc"
proof -
  { assume "pc < n"
    hence "pc \<notin> pcs (shift n xt)" by(rule pcs_shift)
    with assms have False
      by(auto simp add: pcs_def xcpt_eff_def is_relevant_entry_def relevant_entries_def split_beta cong: filter_cong) }
  thus ?thesis by(cases "n \<le> pc")(auto)
qed



lemma wt_instr_appRx:
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> is!pc,pc :: \<tau>s; pc < size is; size is < size \<tau>s; mpc \<le> size \<tau>s \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt @ shift (size is) xt' \<turnstile> is!pc,pc :: \<tau>s"
apply(clarsimp simp:wt_instr_def eff_def app_def)
apply(fastsimp dest: xcpt_eff_shift_pc_ge_n intro!: xcpt_app_pcs[OF pcs_shift])
done

lemma wt_instr_appLx: 
  "\<lbrakk> P,T,m,mpc,xt \<turnstile> i,pc :: \<tau>s; pc \<notin> pcs xt' \<rbrakk>
  \<Longrightarrow> P,T,m,mpc,xt'@xt \<turnstile> i,pc :: \<tau>s"
by (auto simp:wt_instr_def app_def eff_def xcpt_app_pcs xcpt_eff_pcs)


context TC2 begin

lemma wt_instrs_extR:
  "\<turnstile> is,xt [::] \<tau>s \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s @ \<tau>s'"
by(auto simp add:wt_instrs_def wt_instr_appR)


lemma wt_instrs_ext:
  "\<lbrakk> \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>2; size \<tau>s\<^isub>1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
apply(clarsimp simp:wt_instrs_def)
apply(rule conjI, fastsimp)
apply(rule conjI, fastsimp simp add: pcs_shift_conv)
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


corollary wt_instrs_ext2:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>2; \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; size \<tau>s\<^isub>1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
by(rule wt_instrs_ext)


corollary wt_instrs_ext_prefix [trans]:
  "\<lbrakk> \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2; \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>s\<^isub>3;
     size \<tau>s\<^isub>1 = size is\<^isub>1; \<tau>s\<^isub>3 \<le> \<tau>s\<^isub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
by(bestsimp simp:prefix_def elim: wt_instrs_ext dest:wt_instrs_extR)


corollary wt_instrs_app:
  assumes is\<^isub>1: "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@[\<tau>]"
  assumes is\<^isub>2: "\<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>2"
  assumes s: "size \<tau>s\<^isub>1 = size is\<^isub>1"
  shows "\<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>#\<tau>s\<^isub>2"
proof -
  from is\<^isub>1 have "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] (\<tau>s\<^isub>1@[\<tau>])@\<tau>s\<^isub>2"
    by (rule wt_instrs_extR)
  hence "\<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1@\<tau>#\<tau>s\<^isub>2" by simp
  from this is\<^isub>2 s show ?thesis by (rule wt_instrs_ext) 
qed


corollary wt_instrs_app_last[trans]:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>2; \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>s\<^isub>1;
     last \<tau>s\<^isub>1 = \<tau>;  size \<tau>s\<^isub>1 = size is\<^isub>1+1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>s\<^isub>1@\<tau>s\<^isub>2"
apply(cases \<tau>s\<^isub>1 rule:rev_cases)
 apply simp
apply(simp add:wt_instrs_app)
done


corollary wt_instrs_append_last[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s; P,T\<^isub>r,mxs,mpc,[] \<turnstile> i,pc :: \<tau>s;
     pc = size is; mpc = size \<tau>s; size is + 1 < size \<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> is@[i],xt [::] \<tau>s"
apply(clarsimp simp add:wt_instrs_def)
apply(rule conjI, fastsimp)
apply(fastsimp intro!:wt_instr_appLx[where xt = "[]",simplified]
               dest!:less_antisym)
done


corollary wt_instrs_app2:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>'#\<tau>s\<^isub>2;  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>#\<tau>s\<^isub>1@[\<tau>'];
     xt' = xt\<^isub>1 @ shift (size is\<^isub>1) xt\<^isub>2;  size \<tau>s\<^isub>1+1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2,xt' [::] \<tau>#\<tau>s\<^isub>1@\<tau>'#\<tau>s\<^isub>2"
using wt_instrs_app[where ?\<tau>s\<^isub>1.0 = "\<tau> # \<tau>s\<^isub>1"] by simp


corollary wt_instrs_app2_simp[trans,simp]:
  "\<lbrakk> \<turnstile> is\<^isub>2,xt\<^isub>2 [::] \<tau>'#\<tau>s\<^isub>2;  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau>#\<tau>s\<^isub>1@[\<tau>']; size \<tau>s\<^isub>1+1 = size is\<^isub>1 \<rbrakk>
  \<Longrightarrow> \<turnstile> is\<^isub>1@is\<^isub>2, xt\<^isub>1@shift (size is\<^isub>1) xt\<^isub>2 [::] \<tau>#\<tau>s\<^isub>1@\<tau>'#\<tau>s\<^isub>2"
using wt_instrs_app[where ?\<tau>s\<^isub>1.0 = "\<tau> # \<tau>s\<^isub>1"] by simp


corollary wt_instrs_Cons[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,xt [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>'#\<tau>s"
using wt_instrs_app2[where ?is\<^isub>1.0 = "[i]" and ?\<tau>s\<^isub>1.0 = "[]" and ?is\<^isub>2.0 = "is"
                      and ?xt\<^isub>1.0 = "[]"]
by simp


corollary wt_instrs_Cons2[trans]:
  assumes \<tau>s: "\<turnstile> is,xt [::] \<tau>s"
  assumes i: "P,T\<^isub>r,mxs,mpc,[] \<turnstile> i,0 :: \<tau>#\<tau>s"
  assumes mpc: "mpc = size \<tau>s + 1"
  shows "\<turnstile> i#is,shift 1 xt [::] \<tau>#\<tau>s"
proof -
  from \<tau>s have "\<tau>s \<noteq> []" by (auto simp: wt_instrs_def)
  with mpc i have "\<turnstile> [i],[] [::] [\<tau>]@\<tau>s" by (simp add: wt_instrs_def)
  with \<tau>s show ?thesis by (fastsimp dest: wt_instrs_ext)
qed


lemma wt_instrs_last_incr[trans]:
  "\<lbrakk> \<turnstile> is,xt [::] \<tau>s@[\<tau>]; P \<turnstile> \<tau> \<le>' \<tau>' \<rbrakk> \<Longrightarrow> \<turnstile> is,xt [::] \<tau>s@[\<tau>']"
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

end

lemma [iff]: "xcpt_app i P pc mxs [] \<tau>"
by (simp add: xcpt_app_def relevant_entries_def)


lemma [simp]: "xcpt_eff i P pc \<tau> [] = []"
by (simp add: xcpt_eff_def relevant_entries_def)

context TC2 begin

lemma wt_New:
  "\<lbrakk> is_class P C; size ST < mxs \<rbrakk> \<Longrightarrow>
   \<turnstile> [New C],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (Class C#ST) E A]"
by(simp add:wt_defs ty\<^isub>i'_def)


lemma wt_Cast:
  "is_type P T \<Longrightarrow>
   \<turnstile> [Checkcast T],[] [::] [ty\<^isub>i' (U # ST) E A, ty\<^isub>i' (T # ST) E A]"
by(simp add: ty\<^isub>i'_def wt_defs)


lemma wt_Push:
  "\<lbrakk> size ST < mxs; typeof v = Some T \<rbrakk>
  \<Longrightarrow> \<turnstile> [Push v],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (T#ST) E A]"
by(simp add: ty\<^isub>i'_def wt_defs)


lemma wt_Pop:
 "\<turnstile> [Pop],[] [::] (ty\<^isub>i' (T#ST) E A # ty\<^isub>i' ST E A # \<tau>s)"
by(simp add: ty\<^isub>i'_def wt_defs)


lemma wt_CmpEq:
  "\<lbrakk> P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> [CmpEq],[] [::] [ty\<^isub>i' (T\<^isub>2 # T\<^isub>1 # ST) E A, ty\<^isub>i' (Boolean # ST) E A]"
by(auto simp:ty\<^isub>i'_def wt_defs elim!: refTE not_refTE)


lemma wt_IAdd:
  "\<turnstile> [IAdd],[] [::] [ty\<^isub>i' (Integer#Integer#ST) E A, ty\<^isub>i' (Integer#ST) E A]"
by(simp add:ty\<^isub>i'_def wt_defs)


lemma wt_Load:
  "\<lbrakk> size ST < mxs; size E \<le> mxl; i \<in>\<in> A; i < size E \<rbrakk>
  \<Longrightarrow> \<turnstile> [Load i],[] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (E!i # ST) E A]"
by(auto simp add:ty\<^isub>i'_def wt_defs ty\<^isub>l_def hyperset_defs intro: widens_refl)


lemma wt_Store:
 "\<lbrakk> P \<turnstile> T \<le> E!i; i < size E; size E \<le> mxl \<rbrakk> \<Longrightarrow>
  \<turnstile> [Store i],[] [::] [ty\<^isub>i' (T#ST) E A, ty\<^isub>i' ST E (\<lfloor>{i}\<rfloor> \<squnion> A)]"
by(auto simp:hyperset_defs nth_list_update ty\<^isub>i'_def wt_defs ty\<^isub>l_def
        intro:list_all2_all_nthI)


lemma wt_Get:
 "\<lbrakk> P \<turnstile> C sees F:T in D \<rbrakk> \<Longrightarrow>
  \<turnstile> [Getfield F D],[] [::] [ty\<^isub>i' (Class C # ST) E A, ty\<^isub>i' (T # ST) E A]"
by(auto simp: ty\<^isub>i'_def wt_defs dest: sees_field_idemp sees_field_decl_above intro: widens_refl)


lemma wt_Put:
  "\<lbrakk> P \<turnstile> C sees F:T in D; P \<turnstile> T' \<le> T \<rbrakk> \<Longrightarrow>
  \<turnstile> [Putfield F D],[] [::] [ty\<^isub>i' (T' # Class C # ST) E A, ty\<^isub>i' ST E A]"
by(auto intro: sees_field_idemp sees_field_decl_above simp: ty\<^isub>i'_def wt_defs)


lemma wt_Throw:
  "P \<turnstile> C \<preceq>\<^sup>* Throwable \<Longrightarrow> \<turnstile> [Throw],[] [::] [ty\<^isub>i' (Class C # ST) E A, \<tau>']"
by(simp add: ty\<^isub>i'_def wt_defs)


lemma wt_IfFalse:
  "\<lbrakk> 2 \<le> i; nat i < size \<tau>s + 2; P \<turnstile> ty\<^isub>i' ST E A \<le>' \<tau>s ! nat(i - 2) \<rbrakk>
  \<Longrightarrow> \<turnstile> [IfFalse i],[] [::] ty\<^isub>i' (Boolean # ST) E A # ty\<^isub>i' ST E A # \<tau>s"
apply(clarsimp simp add: ty\<^isub>i'_def wt_defs)
apply(auto simp add: nth_Cons split:nat.split)
apply(simp add:nat_diff_distrib)
done

lemma wt_Goto:
 "\<lbrakk> 0 \<le> int pc + i; nat (int pc + i) < size \<tau>s; size \<tau>s \<le> mpc;
    P \<turnstile> \<tau>s!pc \<le>' \<tau>s ! nat (int pc + i) \<rbrakk>
 \<Longrightarrow> P,T,mxs,mpc,[] \<turnstile> Goto i,pc :: \<tau>s"
by(clarsimp simp add: wt_defs)

lemma wt_Invoke:
  "\<lbrakk> size es = size Ts'; P \<turnstile> C sees M: Ts\<rightarrow>T = m in D; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> \<turnstile> [Invoke M (size es)],[] [::] [ty\<^isub>i' (rev Ts' @ Class C # ST) E A, ty\<^isub>i' (T#ST) E A]"
apply(clarsimp simp add: ty\<^isub>i'_def wt_defs)
apply(fastsimp dest: external_call_not_sees_method[OF wf_prog] intro: widens_refl)
done

corollary wt_instrs_app3[simp]:
  "\<lbrakk> \<turnstile> is\<^isub>2,[] [::] (\<tau>' # \<tau>s\<^isub>2);  \<turnstile> is\<^isub>1,xt\<^isub>1 [::] \<tau> # \<tau>s\<^isub>1 @ [\<tau>']; size \<tau>s\<^isub>1+1 = size is\<^isub>1\<rbrakk>
  \<Longrightarrow> \<turnstile> (is\<^isub>1 @ is\<^isub>2),xt\<^isub>1 [::] \<tau> # \<tau>s\<^isub>1 @ \<tau>' # \<tau>s\<^isub>2"
using wt_instrs_app2[where ?xt\<^isub>2.0 = "[]"] by (simp add:shift_def)


corollary wt_instrs_Cons3[simp]:
  "\<lbrakk> \<tau>s \<noteq> []; \<turnstile> [i],[] [::] [\<tau>,\<tau>']; \<turnstile> is,[] [::] \<tau>'#\<tau>s \<rbrakk>
  \<Longrightarrow> \<turnstile> (i # is),[] [::] \<tau> # \<tau>' # \<tau>s"
using wt_instrs_Cons[where ?xt = "[]"]
by (simp add:shift_def)

declare nth_append[simp del]

lemma wt_instrs_xapp[trans]:
  "\<lbrakk> \<turnstile> is\<^isub>1 @ is\<^isub>2, xt [::] \<tau>s\<^isub>1 @ ty\<^isub>i' (Class C # ST) E A # \<tau>s\<^isub>2;
     \<forall>\<tau> \<in> set \<tau>s\<^isub>1. \<forall>ST' LT'. \<tau> = Some(ST',LT') \<longrightarrow> 
      size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^isub>i' ST E A;
     size is\<^isub>1 = size \<tau>s\<^isub>1; is_class P C; size ST < mxs  \<rbrakk> \<Longrightarrow>
  \<turnstile> is\<^isub>1 @ is\<^isub>2, xt @ [(0,size is\<^isub>1 - Suc n,C,size is\<^isub>1,size ST)] [::] \<tau>s\<^isub>1 @ ty\<^isub>i' (Class C # ST) E A # \<tau>s\<^isub>2"
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

end

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

lemma drop_mess2:
  assumes len: "Suc (Suc (length xs0)) \<le> length xs" 
  and drop: "drop (length xs - Suc (Suc (length xs0))) xs = x1 # x2 # xs0"
  shows "drop (length xs - length xs0) xs = xs0"
proof(cases xs)
  case Nil with assms show ?thesis by simp
next
  case (Cons x xs')
  note Cons[simp]
  show ?thesis
  proof(cases xs')
    case Nil with assms show ?thesis by(simp)
  next
    case (Cons x' xs'')
    note Cons[simp]
    show ?thesis 
    proof(rule drop_mess)
      from len show "Suc (length xs0) \<le> length xs" by simp
    next
      have "drop (length xs - length (x2 # xs0)) xs = x2 # xs0"
      proof(rule drop_mess)
	from len show "Suc (length (x2 # xs0)) \<le> length xs" by(simp)
      next
	from drop show "drop (length xs - Suc (length (x2 # xs0))) xs = x1 # x2 # xs0" by simp
      qed
      thus "drop (length xs - Suc (length xs0)) xs = x2 # xs0" by(simp)
    qed
  qed
qed

context TC0 begin

declare after_def[simp] pair_eq_ty\<^isub>i'_conv[simp]

lemma compT_ST_prefix: 
  "\<lfloor>(ST,LT)\<rfloor> \<in> set(compT E A ST0 e) \<Longrightarrow> size ST0 \<le> size ST \<and> drop (size ST - size ST0) ST = ST0"

  and compTs_ST_prefix:
  "\<lfloor>(ST,LT)\<rfloor> \<in> set(compTs E A ST0 es) \<Longrightarrow> size ST0 \<le> size ST \<and> drop (size ST - size ST0) ST = ST0"
proof(induct e and es arbitrary: E A ST0 and E A ST0)
  case (FAss e\<^isub>1 F D e\<^isub>2)
  moreover {
    let ?ST\<^isub>0 = "ty E e\<^isub>1 # ST0"
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
    let ?ST\<^isub>0 = "ty E e # ST0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^isub>0 es)"
    with Call
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (Cons_exp e es)
  moreover {
    let ?ST\<^isub>0 = "ty E e # ST0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compTs E A ?ST\<^isub>0 es)"
    with Cons_exp
    have "length ?ST\<^isub>0 \<le> length ST \<and> drop (size ST - size ?ST\<^isub>0) ST = ?ST\<^isub>0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (BinOp e\<^isub>1 bop e\<^isub>2)
  moreover {
    let ?ST\<^isub>0 = "ty E e\<^isub>1 # ST0"
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
next
  case newArray thus ?case by auto
next
  case (AAcc exp1 exp2)
  moreover {
    let ?ST0 = "ty E exp1 # ST0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST0 exp2)"
    with AAcc
    have "length ?ST0 \<le> length ST \<and> drop (size ST - size ?ST0) ST = ?ST0" by blast
    hence ?case  by (clarsimp simp add: drop_mess)
  }
  ultimately show ?case by auto
next
  case (AAss exp1 exp2 exp3)
  moreover {
    let ?ST0 = "ty E exp1 # ST0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST0 exp2)"
    with AAss
    have "length ?ST0 \<le> length ST \<and> drop (size ST - size ?ST0) ST = ?ST0" by blast
    hence ?case by (clarsimp simp add: drop_mess)
  } moreover {
    let ?ST0 = "ty E exp2 # ty E exp1 # ST0"
    fix A assume "\<lfloor>(ST, LT)\<rfloor> \<in> set (compT E A ?ST0 exp3)"
    with AAss
    have "length ?ST0 \<le> length ST \<and> drop (size ST - size ?ST0) ST = ?ST0" by blast
    hence ?case by (fastsimp intro: drop_mess2)
  }
  ultimately show ?case by simp auto
next
  case ALen thus ?case by auto
next
  case Synchronized thus ?case by auto
next
  case InSynchronized thus ?case by auto
qed 

declare after_def[simp del] pair_eq_ty\<^isub>i'_conv[simp del]

end

(* FIXME *)
lemma fun_of_simp [simp]: "fun_of S x y = ((x,y) \<in> S)" 
by (simp add: fun_of_def)

declare widens_refl [iff]

lemma shift_Cons: 
  "shift n ((f,t,C,pc,d) # xts) = (f+n,t+n,C,pc+n,d) # shift n xts"
by(simp add: shift_def)

context TC2 begin

theorem compT_wt_instrs:
  "\<lbrakk> P,E \<turnstile>1 e :: T; \<D> e A; \<B> e (size E); size ST + max_stack e \<le> mxs; size E + max_vars e \<le> mxl; set E \<subseteq> is_type P \<rbrakk>
  \<Longrightarrow> \<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ty\<^isub>i' ST E A # compT E A ST e @ [after E A ST e]"
  (is "PROP ?P e E T A ST")

  and compTs_wt_instrs:
  "\<lbrakk> P,E \<turnstile>1 es[::]Ts;  \<D>s es A; \<B>s es (size E); size ST + max_stacks es \<le> mxs; size E + max_varss es \<le> mxl; set E \<subseteq> is_type P \<rbrakk>
  \<Longrightarrow> let \<tau>s = ty\<^isub>i' ST E A # compTs E A ST es
      in \<turnstile> compEs2 es,compxEs2 es 0 (size ST) [::] \<tau>s \<and> last \<tau>s = ty\<^isub>i' (rev Ts @ ST) E (A \<squnion> \<A>s es)"
  (is "PROP ?Ps es E Ts A ST")
proof(induct e and es arbitrary: E T A ST and E Ts A ST)
  case (TryCatch e\<^isub>1 C i e\<^isub>2)
  hence [simp]: "i = size E" by simp
  have wt\<^isub>1: "P,E \<turnstile>1 e\<^isub>1 :: T" and wt\<^isub>2: "P,E@[Class C] \<turnstile>1 e\<^isub>2 :: T"
    and "class": "is_class P C" using TryCatch by auto
  let ?A\<^isub>1 = "A \<squnion> \<A> e\<^isub>1" let ?A\<^isub>i = "A \<squnion> \<lfloor>{i}\<rfloor>" let ?E\<^isub>i = "E @ [Class C]"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>1 = "compT E A ST e\<^isub>1"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (T#ST) E ?A\<^isub>1" let ?\<tau>\<^isub>2 = "ty\<^isub>i' (Class C#ST) E A"
  let ?\<tau>\<^isub>3 = "ty\<^isub>i' ST ?E\<^isub>i ?A\<^isub>i" let ?\<tau>s\<^isub>2 = "compT ?E\<^isub>i ?A\<^isub>i ST e\<^isub>2"
  let ?\<tau>\<^isub>2' = "ty\<^isub>i' (T#ST) ?E\<^isub>i (?A\<^isub>i \<squnion> \<A> e\<^isub>2)"
  let ?\<tau>' = "ty\<^isub>i' (T#ST) E (A \<squnion> \<A> e\<^isub>1 \<sqinter> (\<A> e\<^isub>2 \<ominus> i))"
  let ?go = "Goto (int(size(compE2 e\<^isub>2)) + 2)"
  have "PROP ?P e\<^isub>2 ?E\<^isub>i T ?A\<^isub>i ST" by fact
  hence "\<turnstile> compE2 e\<^isub>2,compxE2 e\<^isub>2 0 (size ST) [::] (?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2) @ [?\<tau>\<^isub>2']"
    using TryCatch.prems "class" by(auto simp:after_def)
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
  also have "P,T\<^isub>r,mxs,size(compE2 e\<^isub>2)+3,[] \<turnstile> ?go,0 :: ?\<tau>\<^isub>1#?\<tau>\<^isub>2#?\<tau>\<^isub>3#?\<tau>s\<^isub>2 @ [?\<tau>']"
    by(auto simp: hyperset_defs ty\<^isub>i'_def wt_defs nth_Cons nat_add_distrib
      fun_of_def intro: ty\<^isub>l_antimono list_all2_refl split:nat.split)
  also have "\<turnstile> compE2 e\<^isub>1,compxE2 e\<^isub>1 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>1]"
    using TryCatch by(auto simp:after_def)
  also have "?\<tau> # ?\<tau>s\<^isub>1 @ ?\<tau>\<^isub>1 # ?\<tau>\<^isub>2 # ?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>'] =
             (?\<tau> # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>1]) @ ?\<tau>\<^isub>2 # ?\<tau>\<^isub>3 # ?\<tau>s\<^isub>2 @ [?\<tau>']" by simp
  also have "compE2 e\<^isub>1 @ ?go  # [Store i] @ compE2 e\<^isub>2 =
             (compE2 e\<^isub>1 @ [?go]) @ (Store i # compE2 e\<^isub>2)" by simp
  also 
  let "?Q \<tau>" = "\<forall>ST' LT'. \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> 
    size ST \<le> size ST' \<and> P \<turnstile> Some (drop (size ST' - size ST) ST',LT') \<le>' ty\<^isub>i' ST E A"
  {
    have "?Q (ty\<^isub>i' ST E A)" by(clarsimp simp add: ty\<^isub>i'_def)
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
    by (simp add:after_def)(erule_tac x=0 in meta_allE, simp)
next
  case (Synchronized i e1 e2)
  note wt = `P,E \<turnstile>1 sync\<^bsub>i\<^esub> (e1) e2 :: T`
  then obtain U where wt1: "P,E \<turnstile>1 e1 :: U"
    and U: "is_refT U" "U \<noteq> NT"
    and wt2: "P,E@[Class Object] \<turnstile>1 e2 :: T" by auto
  from `\<B> (sync\<^bsub>i\<^esub> (e1) e2) (length E)` have [simp]: "i = length E"
    and B1: "\<B> e1 (length E)" and B2: "\<B> e2 (length (E@[Class Object]))" by auto
  
  note lenST = `length ST + max_stack (sync\<^bsub>i\<^esub> (e1) e2) \<le> mxs` 
  note lenE = `length E + max_vars (sync\<^bsub>i\<^esub> (e1) e2) \<le> mxl`

  let ?A1 = "A \<squnion> \<A> e1" let ?A2 = "?A1 \<squnion> \<lfloor>{length E}\<rfloor>"
  let ?A3 = "?A2 \<squnion> \<A> e2" let ?A4 = "?A1 \<squnion> \<A> e2"
  let ?E1 = "E @ [Class Object]"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s1 = "compT E A ST e1"
  let ?\<tau>1 = "ty\<^isub>i' (U#ST) E ?A1" let ?\<tau>1' = "ty\<^isub>i' ST ?E1 ?A2"
  let ?\<tau>1'' = "ty\<^isub>i' (Class Object#ST) ?E1 ?A2" let ?\<tau>1''' = "ty\<^isub>i' ST ?E1 ?A2"
  let ?\<tau>s2 = "compT ?E1 ?A2 ST e2"
  let ?\<tau>2 = "ty\<^isub>i' (T#ST) ?E1 ?A3" let ?\<tau>2' = "ty\<^isub>i' (Class Object#T#ST) ?E1 ?A3"
  let ?\<tau>2'' = ?\<tau>2
  let ?\<tau>3 = "ty\<^isub>i' (Class Throwable#ST) ?E1 ?A2"
  let ?\<tau>3' = "ty\<^isub>i' (Class Object#Class Throwable#ST) ?E1 ?A2"
  let ?\<tau>3'' = ?\<tau>3
  let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A4"

  from lenE lenST max_stack1[of e2] U 
  have "\<turnstile> [Load i, MExit, Throw], [] [::] [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp add: ty\<^isub>i'_def ty\<^isub>l_def wt_defs hyperset_defs nth_Cons split: nat.split)
  also have "P,T\<^isub>r,mxs,5,[] \<turnstile> Goto 4,0 :: [?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^isub>i'_def wt_defs intro: ty\<^isub>l_antimono ty\<^isub>l_incr)
  also have "P,T\<^isub>r,mxs,6,[] \<turnstile> MExit,0 :: [?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^isub>i'_def wt_defs intro: ty\<^isub>l_antimono ty\<^isub>l_incr)
  also from lenE lenST max_stack1[of e2]
  have "P,T\<^isub>r,mxs,7,[] \<turnstile> Load i,0 :: [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(auto simp: hyperset_defs ty\<^isub>i'_def wt_defs ty\<^isub>l_def intro: ty\<^isub>l_antimono)
  also from `\<D> (sync\<^bsub>i\<^esub> (e1) e2) A` have "\<D> e2 (A \<squnion> \<A> e1 \<squnion> \<lfloor>{length E}\<rfloor>)"
    by(auto elim!: D_mono' simp add: hyperset_defs)
  with `PROP ?P e2 ?E1 T ?A2 ST` Synchronized wt2 is_class_Object[OF wf_prog]
  have "\<turnstile> compE2 e2, compxE2 e2 0 (size ST) [::] ?\<tau>1'''#?\<tau>s2@[?\<tau>2]"
    by(auto simp add: after_def)
  finally have "\<turnstile> (compE2 e2 @ [Load i, MExit, Goto 4]) @ [Load i, MExit, Throw], compxE2 e2 0 (size ST) [::]
             (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']) @ [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(simp)
  hence "\<turnstile> (compE2 e2 @ [Load i, MExit, Goto 4]) @ [Load i, MExit, Throw],
           compxE2 e2 0 (size ST) @ [(0, size (compE2 e2 @ [Load i, MExit, Goto 4]) - Suc 2, Throwable, size (compE2 e2 @ [Load i, MExit, Goto 4]), size ST)] [::]
           (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']) @ [?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
  proof(rule wt_instrs_xapp)
    from wf_prog show "is_class P Throwable"
      by(rule converse_subcls_is_class[OF _ xcpt_subcls_Throwable, where C = OutOfMemory])(auto intro: wf_prog is_class_xcpt )
  next
    from lenST show "length ST < mxs" by simp
  next
    show "\<forall>\<tau>\<in>set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'']). \<forall>ST' LT'.
          \<tau> = \<lfloor>(ST', LT')\<rfloor> \<longrightarrow> length ST \<le> length ST' \<and>
          P \<turnstile> \<lfloor>(drop (length ST' - length ST) ST',  LT')\<rfloor> \<le>' ty\<^isub>i' ST (E @ [Class Object]) (A \<squnion> \<A> e1 \<squnion> \<lfloor>{length E}\<rfloor>)"
    proof(rule ballI allI impI)+
      fix \<tau> ST' LT'
      assume "\<tau>\<in>set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2''])" "\<tau> = \<lfloor>(ST', LT')\<rfloor>"
      hence \<tau>: "\<lfloor>(ST', LT')\<rfloor> \<in> set (?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2''])" by simp
      show "length ST \<le> length ST' \<and> P \<turnstile> \<lfloor>(drop (length ST' - length ST) ST',  LT')\<rfloor> \<le>' ty\<^isub>i' ST (E @ [Class Object]) (A \<squnion> \<A> e1 \<squnion> \<lfloor>{length E}\<rfloor>)"
      proof(cases "\<lfloor>(ST', LT')\<rfloor> \<in> set ?\<tau>s2")
	case True
	thus ?thesis
	  by -(frule compT_ST_prefix, drule compT_LT_prefix[OF _ B2], simp add: ty\<^isub>i'_def)
      next
	case False
	with \<tau> show ?thesis
	  by(auto simp add: ty\<^isub>i'_def hyperset_defs intro: ty\<^isub>l_antimono)
      qed
    qed
  qed simp
  hence "\<turnstile> compE2 e2 @ [Load i, MExit, Goto 4, Load i, MExit, Throw],
           compxE2 e2 0 (size ST) @ [(0, size (compE2 e2), Throwable, Suc (Suc (Suc (size (compE2 e2)))), size ST)] [::]
           ?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']" by simp
  also from wt1 `set E \<subseteq> is_type P` have "is_type P U" by(rule WT1_is_type[OF wf_prog])
  with U have "P \<turnstile> U \<le> Class Object" by(auto elim!: is_refT.cases intro: subcls_C_Object[OF _ wf_prog] widen_array_object)
  with lenE lenST max_stack1[of e2]
  have "\<turnstile> [Store i, Load i, MEnter], [] [::] [?\<tau>1, ?\<tau>1', ?\<tau>1''] @ [?\<tau>1''']"
    by(auto simp add: ty\<^isub>i'_def ty\<^isub>l_def wt_defs hyperset_defs nth_Cons nth_list_update list_all2_conv_all_nth split: nat.split)
  finally have "\<turnstile> Store i # Load i # MEnter # compE2 e2 @ [Load i, MExit, Goto 4, Load i, MExit, Throw],
               compxE2 e2 3 (size ST) @ [(3, 3 + size (compE2 e2), Throwable, 6 + size (compE2 e2), size ST)]
            [::] ?\<tau>1 # ?\<tau>1' # ?\<tau>1'' # ?\<tau>1''' # ?\<tau>s2 @ [?\<tau>2, ?\<tau>2', ?\<tau>2'', ?\<tau>3, ?\<tau>3', ?\<tau>3'', ?\<tau>']"
    by(simp add: nat_number shift_def)
  also from `PROP ?P e1 E U A ST` wt1 B1 `\<D> (sync\<^bsub>i\<^esub> (e1) e2) A` lenE lenST `set E \<subseteq> is_type P`
  have "\<turnstile> compE2 e1, compxE2 e1 0 (size ST) [::] ?\<tau>#?\<tau>s1@[?\<tau>1]"
    by(auto simp add: after_def)
  finally show ?case using wt1 wt2 wt by(simp add: after_def add_ac shift_Cons)
next
  case new thus ?case by(auto simp add:after_def wt_New)
next
  case (BinOp e\<^isub>1 bop e\<^isub>2) 
  let ?op = "case bop of Eq \<Rightarrow> [CmpEq] | Add \<Rightarrow> [IAdd]"
  have T: "P,E \<turnstile>1 e\<^isub>1 \<guillemotleft>bop\<guillemotright> e\<^isub>2 :: T" by fact
  then obtain T\<^isub>1 T\<^isub>2 where T\<^isub>1: "P,E \<turnstile>1 e\<^isub>1 :: T\<^isub>1" and T\<^isub>2: "P,E \<turnstile>1 e\<^isub>2 :: T\<^isub>2" and 
    bopT: "case bop of Eq \<Rightarrow> (P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<or> P \<turnstile> T\<^isub>2 \<le> T\<^isub>1) \<and> T = Boolean 
                    | Add \<Rightarrow> T\<^isub>1 = Integer \<and> T\<^isub>2 = Integer \<and> T = Integer" by fastsimp
  let ?A\<^isub>1 = "A \<squnion> \<A> e\<^isub>1" let ?A\<^isub>2 = "?A\<^isub>1 \<squnion> \<A> e\<^isub>2"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>1 = "compT E A ST e\<^isub>1"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (T\<^isub>1#ST) E ?A\<^isub>1" let ?\<tau>s\<^isub>2 = "compT E ?A\<^isub>1 (T\<^isub>1#ST) e\<^isub>2"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' (T\<^isub>2#T\<^isub>1#ST) E ?A\<^isub>2" let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A\<^isub>2"
  from bopT have "\<turnstile> ?op,[] [::] [?\<tau>\<^isub>2,?\<tau>']" 
    by (cases bop) (auto simp add: wt_CmpEq wt_IAdd)
  also have "PROP ?P e\<^isub>2 E T\<^isub>2 ?A\<^isub>1 (T\<^isub>1#ST)" by fact
  with BinOp.prems T\<^isub>2 
  have "\<turnstile> compE2 e\<^isub>2, compxE2 e\<^isub>2 0 (size (T\<^isub>1#ST)) [::] ?\<tau>\<^isub>1#?\<tau>s\<^isub>2@[?\<tau>\<^isub>2]" 
    by (auto simp: after_def)
  also from BinOp T\<^isub>1 have "\<turnstile> compE2 e\<^isub>1, compxE2 e\<^isub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>1@[?\<tau>\<^isub>1]" 
    by (auto simp: after_def)
  finally show ?case using T T\<^isub>1 T\<^isub>2 by (simp add: after_def hyperUn_assoc)
next
  case (Cons_exp e es)
  have "P,E \<turnstile>1 e # es [::] Ts" by fact
  then obtain T\<^isub>e Ts' where 
    T\<^isub>e: "P,E \<turnstile>1 e :: T\<^isub>e" and Ts': "P,E \<turnstile>1 es [::] Ts'" and
    Ts: "Ts = T\<^isub>e#Ts'" by auto
  let ?A\<^isub>e = "A \<squnion> \<A> e"  
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>e = "compT E A ST e"  
  let ?\<tau>\<^isub>e = "ty\<^isub>i' (T\<^isub>e#ST) E ?A\<^isub>e" let ?\<tau>s' = "compTs E ?A\<^isub>e (T\<^isub>e#ST) es"
  let ?\<tau>s = "?\<tau> # ?\<tau>s\<^isub>e @ (?\<tau>\<^isub>e # ?\<tau>s')"
  have Ps: "PROP ?Ps es E Ts' ?A\<^isub>e (T\<^isub>e#ST)" by fact
  with Cons_exp.prems T\<^isub>e Ts'
  have "\<turnstile> compEs2 es, compxEs2 es 0 (size (T\<^isub>e#ST)) [::] ?\<tau>\<^isub>e#?\<tau>s'" by (simp add: after_def)
  also from Cons_exp T\<^isub>e have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>e@[?\<tau>\<^isub>e]" 
    by (auto simp: after_def)
  moreover
  from Ps Cons_exp.prems T\<^isub>e Ts' Ts
  have "last ?\<tau>s = ty\<^isub>i' (rev Ts@ST) E (?A\<^isub>e \<squnion> \<A>s es)" by simp
  ultimately show ?case using T\<^isub>e
    by(auto simp add: after_def hyperUn_assoc shift_compxEs2 stack_xlift_compxEs2 simp del: compxE2_size_convs compxEs2_size_convs compxEs2_stack_xlift_convs compxE2_stack_xlift_convs intro: wt_instrs_app2)
next
  case (FAss e\<^isub>1 F D e\<^isub>2)
  hence Void: "P,E \<turnstile>1 e\<^isub>1\<bullet>F{D} := e\<^isub>2 :: Void" by auto
  then obtain C T T' where    
    C: "P,E \<turnstile>1 e\<^isub>1 :: Class C" and sees: "P \<turnstile> C sees F:T in D" and
    T': "P,E \<turnstile>1 e\<^isub>2 :: T'" and T'_T: "P \<turnstile> T' \<le> T" by auto
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
  have "\<turnstile> compE2 e\<^isub>2, compxE2 e\<^isub>2 0 (size ST+1) [::] ?\<tau>\<^isub>1#?\<tau>s\<^isub>2@[?\<tau>\<^isub>2]"
    by (auto simp add: after_def hyperUn_assoc) 
  also from FAss C have "\<turnstile> compE2 e\<^isub>1, compxE2 e\<^isub>1 0 (size ST) [::] ?\<tau>#?\<tau>s\<^isub>1@[?\<tau>\<^isub>1]" 
    by (auto simp add: after_def)
  finally show ?case using Void C T' by (simp add: after_def hyperUn_assoc) 
next
  case Val thus ?case by(auto simp:after_def wt_Push)
next
  case (Cast T exp) thus ?case by (auto simp:after_def wt_Cast)
next
  case (Block i Ti vo e cr)
  note IH = `\<And>E T A ST. PROP ?P e E T A ST`
  from `P,E \<turnstile>1 {i:Ti=vo; e}\<^bsub>cr\<^esub> :: T` have wte: "P,E@[Ti] \<turnstile>1 e :: T"
    and Ti: "is_type P Ti" by auto
  from `length ST + max_stack {i:Ti=vo; e}\<^bsub>cr\<^esub> \<le> mxs`
  have lenST: "length ST + max_stack e \<le> mxs" by simp
  from `length E + max_vars {i:Ti=vo; e}\<^bsub>cr\<^esub> \<le> mxl`
  have lenE: "length (E@[Ti]) + max_vars e \<le> mxl" by simp
  from `\<B> {i:Ti=vo; e}\<^bsub>cr\<^esub> (length E)` have [simp]: "i = length E"
    and B: "\<B> e (length (E@[Ti]))" by auto
  note IH' = IH[OF wte _ B lenST lenE]
  show ?case
  proof(cases vo)
    case None
    let ?\<tau>s = "ty\<^isub>i' ST E A # compT (E @ [Ti]) (A\<ominus>i) ST e"
    from None `\<D> {i:Ti=vo; e}\<^bsub>cr\<^esub> A` IH'[of "A \<ominus> i"] wte `set E \<subseteq> is_type P` Ti
    have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau>s @ [ty\<^isub>i' (T#ST) (E@[Ti]) (A\<ominus>(size E) \<squnion> \<A> e)]"
      by(auto simp add: after_def)
    also have "P \<turnstile> ty\<^isub>i' (T # ST) (E@[Ti]) (A \<ominus> size E \<squnion> \<A> e) \<le>' ty\<^isub>i' (T # ST) (E@[Ti]) ((A \<squnion> \<A> e) \<ominus> size E)"
      by(auto simp add:hyperset_defs intro: ty\<^isub>i'_antimono)
    also have "\<dots> = ty\<^isub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
    also have "P \<turnstile> \<dots> \<le>' ty\<^isub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
      by(auto simp add:hyperset_defs intro: ty\<^isub>i'_antimono)
    finally show ?thesis using Block.prems None by(simp add: after_def)
  next
    case (Some v) note Some[simp]
    from `P,E \<turnstile>1 {i:Ti=vo; e}\<^bsub>cr\<^esub> :: T` obtain Tv
      where Tv: "P,E \<turnstile>1 Val v :: Tv" "P \<turnstile> Tv \<le> Ti" by(auto)
    from `\<D> {i:Ti=vo; e}\<^bsub>cr\<^esub> A` IH'[of "A \<squnion> \<lfloor>{i}\<rfloor>"] wte `set E \<subseteq> is_type P` Ti
    have "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ty\<^isub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) # compT (E @ [Ti]) (A \<squnion> \<lfloor>{i}\<rfloor>) ST e @ [ty\<^isub>i' (T#ST) (E@[Ti]) (A \<squnion> \<lfloor>{size E}\<rfloor> \<squnion> \<A> e)]"
      by(auto simp add: after_def)
    from lenST max_stack1[of e] Tv
    have "\<turnstile> [Push v], [] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (ty E (Val v) # ST) E A]"
      by(auto intro: wt_Push)
    moreover from Tv lenE
    have "\<turnstile> [Store (length E)], [] [::] [ty\<^isub>i' (Tv # ST) (E @ [Ti]) (A \<ominus> length E), ty\<^isub>i' ST (E @ [Ti]) (\<lfloor>{length E}\<rfloor> \<squnion> (A \<ominus> length E))]"
      by -(rule wt_Store, auto)
    moreover have "ty\<^isub>i' (Tv # ST) (E @ [Ti]) (A \<ominus> length E) = ty\<^isub>i' (Tv # ST) E A" by(simp add: ty\<^isub>i'_def)
    moreover have "\<lfloor>{length E}\<rfloor> \<squnion> (A \<ominus> length E) = A \<squnion> \<lfloor>{length E}\<rfloor>" by(simp add: hyperset_defs)
    ultimately have "\<turnstile> [Push v, Store (length E)], [] [::] [ty\<^isub>i' ST E A, ty\<^isub>i' (Tv # ST) E A, ty\<^isub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>)]"
      using Tv by(simp)
    moreover {
      from IH'[of "A \<squnion> \<lfloor>{length E}\<rfloor>"] `\<D> {i:Ti=vo; e}\<^bsub>cr\<^esub> A` wte `set E \<subseteq> is_type P` Ti
      have "\<turnstile> compE2 e, compxE2 e 0 (length ST) [::]  (ty\<^isub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) # compT (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) ST e) @ [ty\<^isub>i' (T # ST) (E @ [Ti]) (A \<squnion> (\<A> e \<squnion> \<lfloor>{length E}\<rfloor>))]"
	by(simp add: after_def)
      also have "P \<turnstile> ty\<^isub>i' (T # ST) (E @ [Ti]) (A \<squnion> (\<A> e \<squnion> \<lfloor>{length E}\<rfloor>)) \<le>' ty\<^isub>i' (T # ST) (E @ [Ti]) ((A \<squnion> \<A> e) \<ominus> length E)"
	by(auto simp add: hyperset_defs intro: ty\<^isub>i'_antimono)
      also have "\<dots> = ty\<^isub>i' (T # ST) E (A \<squnion> \<A> e)" by simp
      also have "P \<turnstile> \<dots> \<le>' ty\<^isub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))"
	by(auto simp add:hyperset_defs intro: ty\<^isub>i'_antimono)
      finally have "\<turnstile> compE2 e, compxE2 e 0 (length ST) [::] ty\<^isub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) # compT (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>) ST e @ [ty\<^isub>i' (T # ST) E (A \<squnion> (\<A> e \<ominus> i))]"
	by simp }
    ultimately show ?thesis using Tv `P,E \<turnstile>1 {i:Ti=vo; e}\<^bsub>cr\<^esub> :: T` wte
      by(simp add: after_def)
        (erule wt_instrs_app[of "[Push v, Store (length E)]" "[]" "[ty\<^isub>i' ST E A, ty\<^isub>i' (Tv # ST) E A]" "ty\<^isub>i' ST (E @ [Ti]) (A \<squnion> \<lfloor>{length E}\<rfloor>)", simplified])
  qed
next
  case Var thus ?case by(auto simp:after_def wt_Load)
next
  case FAcc thus ?case by(auto simp:after_def wt_Get)
next
  case (LAss i e) thus ?case using max_stack1[of e]
    by(auto simp: hyper_insert_comm after_def wt_Store wt_Push simp del: hyperUn_comm hyperUn_leftComm)
next
  case Nil_exp thus ?case by auto
next
  case throw thus ?case by(auto simp add: after_def wt_Throw)
next
  case (While e c)
  obtain Tc where wte: "P,E \<turnstile>1 e :: Boolean" and wtc: "P,E \<turnstile>1 c :: Tc"
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
  hence "\<turnstile> compE2 e,compxE2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]"
    using While.prems by (auto simp:after_def)
  also
  have "[] @ ?\<tau>s = (?\<tau> # ?\<tau>s\<^isub>e) @ ?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c,?\<tau>\<^isub>2,?\<tau>\<^isub>1,?\<tau>']" by simp
  also
  let ?n\<^isub>e = "size(compE2 e)"  let ?n\<^isub>c = "size(compE2 c)"
  let ?if = "IfFalse (int ?n\<^isub>c + 3)"
  have "\<turnstile> [?if],[] [::] ?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2, ?\<tau>\<^isub>1, ?\<tau>']"
    by(simp add: wt_instr_Cons wt_instr_append wt_IfFalse
                 nat_add_distrib split: nat_diff_split)
  also
  have "(?\<tau> # ?\<tau>s\<^isub>e) @ (?\<tau>\<^isub>e # ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c, ?\<tau>\<^isub>2, ?\<tau>\<^isub>1, ?\<tau>']) = ?\<tau>s" by simp
  also
  have "PROP ?P c E Tc ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE2 c,compxE2 c 0 (size ST) [::] ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>c @ [?\<tau>\<^isub>c]"
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
  obtain T\<^isub>1 T\<^isub>2 where wte: "P,E \<turnstile>1 e :: Boolean"
    and wt\<^isub>1: "P,E \<turnstile>1 e\<^isub>1 :: T\<^isub>1" and wt\<^isub>2: "P,E \<turnstile>1 e\<^isub>2 :: T\<^isub>2"
    and sub\<^isub>1: "P \<turnstile> T\<^isub>1 \<le> T" and sub\<^isub>2: "P \<turnstile> T\<^isub>2 \<le> T"
    using Cond by auto
  have [simp]: "ty E (if (e) e\<^isub>1 else e\<^isub>2) = T" using Cond by simp
  let ?A\<^isub>0 = "A \<squnion> \<A> e" let ?A\<^isub>2 = "?A\<^isub>0 \<squnion> \<A> e\<^isub>2" let ?A\<^isub>1 = "?A\<^isub>0 \<squnion> \<A> e\<^isub>1"
  let ?A' = "?A\<^isub>0 \<squnion> \<A> e\<^isub>1 \<sqinter> \<A> e\<^isub>2"
  let ?\<tau>\<^isub>2 = "ty\<^isub>i' ST E ?A\<^isub>0" let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A'"
  let ?\<tau>s\<^isub>2 = "compT E ?A\<^isub>0 ST e\<^isub>2"
  have "PROP ?P e\<^isub>2 E T\<^isub>2 ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE2 e\<^isub>2, compxE2 e\<^isub>2 0 (size ST) [::] (?\<tau>\<^isub>2#?\<tau>s\<^isub>2) @ [ty\<^isub>i' (T\<^isub>2#ST) E ?A\<^isub>2]"
    using Cond.prems wt\<^isub>2 by(auto simp add:after_def)
  also have "P \<turnstile> ty\<^isub>i' (T\<^isub>2#ST) E ?A\<^isub>2 \<le>' ?\<tau>'" using sub\<^isub>2
    by(auto simp add: hyperset_defs ty\<^isub>i'_def intro!: ty\<^isub>l_antimono)
  also
  let ?\<tau>\<^isub>3 = "ty\<^isub>i' (T\<^isub>1 # ST) E ?A\<^isub>1"
  let ?g\<^isub>2 = "Goto(int (size (compE2 e\<^isub>2) + 1))"
  from sub\<^isub>1 have "P,T\<^isub>r,mxs,size(compE2 e\<^isub>2)+2,[] \<turnstile> ?g\<^isub>2,0 :: ?\<tau>\<^isub>3#(?\<tau>\<^isub>2#?\<tau>s\<^isub>2)@[?\<tau>']"
    by(cases "length (compE2 e\<^isub>2)")
      (auto simp: hyperset_defs wt_defs nth_Cons ty\<^isub>i'_def neq_Nil_conv
             split:nat.split intro!: ty\<^isub>l_antimono)
  also let ?\<tau>s\<^isub>1 = "compT E ?A\<^isub>0 ST e\<^isub>1"
  have "PROP ?P e\<^isub>1 E T\<^isub>1 ?A\<^isub>0 ST" by fact
  hence "\<turnstile> compE2 e\<^isub>1,compxE2 e\<^isub>1 0 (size ST) [::] ?\<tau>\<^isub>2 # ?\<tau>s\<^isub>1 @ [?\<tau>\<^isub>3]"
    using Cond.prems wt\<^isub>1 by(auto simp add:after_def)
  also
  let ?\<tau>s\<^isub>1\<^isub>2 = "?\<tau>\<^isub>2 # ?\<tau>s\<^isub>1 @ ?\<tau>\<^isub>3 # (?\<tau>\<^isub>2 # ?\<tau>s\<^isub>2) @ [?\<tau>']"
  let ?\<tau>\<^isub>1 = "ty\<^isub>i' (Boolean#ST) E ?A\<^isub>0"
  let ?g\<^isub>1 = "IfFalse(int (size (compE2 e\<^isub>1) + 2))"
  let ?code = "compE2 e\<^isub>1 @ ?g\<^isub>2 # compE2 e\<^isub>2"
  have "\<turnstile> [?g\<^isub>1],[] [::] [?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>1\<^isub>2"
    by(simp add: wt_IfFalse nat_add_distrib split:nat_diff_split)
  also (wt_instrs_ext2) have "[?\<tau>\<^isub>1] @ ?\<tau>s\<^isub>1\<^isub>2 = ?\<tau>\<^isub>1 # ?\<tau>s\<^isub>1\<^isub>2" by simp also
  let ?\<tau> = "ty\<^isub>i' ST E A"
  have "PROP ?P e E Boolean A ST" by fact
  hence "\<turnstile> compE2 e, compxE2 e 0 (size ST) [::] ?\<tau> # compT E A ST e @ [?\<tau>\<^isub>1]"
    using Cond.prems wte by(auto simp add:after_def)
  finally show ?case using wte wt\<^isub>1 wt\<^isub>2 by(simp add:after_def hyperUn_assoc)
next
  case (Call e M es)
  from `P,E \<turnstile>1 e\<bullet>M(es) :: T` show ?case apply -
  proof(ind_cases "P,E \<turnstile>1 e\<bullet>M(es) :: T")
    fix C D Ts m Ts'
    assume C: "P,E \<turnstile>1 e :: Class C"
      and method: "P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"
      and iec: "\<not> is_external_call P (Class C) M (length es)"
      and wtes: "P,E \<turnstile>1 es [::] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
    from wtes have same_size: "size es = size Ts'" by(rule WTs1_same_size)
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
    hence "\<turnstile> compEs2 es,compxEs2 es 0 (size ST+1) [::] ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s"
      "last (?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) = ?\<tau>\<^isub>1"
      using Call.prems wtes by(auto simp add:after_def)
    also have "(?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) @ [?\<tau>'] = ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s @ [?\<tau>']" by simp
    also have "\<turnstile> compE2 e,compxE2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]"
      using Call C by(auto simp add:after_def)
    finally show ?thesis using Call.prems C
      by(simp add:after_def hyperUn_assoc shift_compxEs2 stack_xlift_compxEs2 del: compxEs2_stack_xlift_convs compxEs2_size_convs)
  next
    fix Te Ts
    assume wte: "P,E \<turnstile>1 e :: Te" and wtes: "P,E \<turnstile>1 es [::] Ts"
      and wtext: "P \<turnstile> Te\<bullet>M(Ts) :: T"
    from wtes have same_size: "size es = size Ts" by(rule WTs1_same_size)
    let ?A\<^isub>0 = "A \<squnion> \<A> e" let ?A\<^isub>1 = "?A\<^isub>0 \<squnion> \<A>s es"
    let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>s\<^isub>e = "compT E A ST e"
    let ?\<tau>\<^isub>e = "ty\<^isub>i' (Te # ST) E ?A\<^isub>0"
    let ?\<tau>s\<^isub>e\<^isub>s = "compTs E ?A\<^isub>0 (Te # ST) es"
    let ?\<tau>\<^isub>1 = "ty\<^isub>i' (rev Ts @ Te # ST) E ?A\<^isub>1"
    let ?\<tau>' = "ty\<^isub>i' (T # ST) E ?A\<^isub>1"
    from wte wtext same_size external_WT_is_external_call[OF wtext]
    have "\<turnstile> [Invoke M (size es)],[] [::] [?\<tau>\<^isub>1,?\<tau>']"
      by(auto simp add: ty\<^isub>i'_def wt_defs external_WT_The_conv)
    also
    have "PROP ?Ps es E Ts ?A\<^isub>0 (Te # ST)" by fact
    hence "\<turnstile> compEs2 es,compxEs2 es 0 (size ST+1) [::] ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s"
      "last (?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) = ?\<tau>\<^isub>1"
      using Call.prems wtes by(auto simp add:after_def)
    also have "(?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s) @ [?\<tau>'] = ?\<tau>\<^isub>e # ?\<tau>s\<^isub>e\<^isub>s @ [?\<tau>']" by simp
    also have "\<turnstile> compE2 e,compxE2 e 0 (size ST) [::] ?\<tau> # ?\<tau>s\<^isub>e @ [?\<tau>\<^isub>e]"
      using Call wte by(auto simp add:after_def)
    finally show ?thesis using Call.prems wte
      by(simp add:after_def hyperUn_assoc shift_compxEs2 stack_xlift_compxEs2 del: compxEs2_stack_xlift_convs compxEs2_size_convs)
  qed
next
  case Seq thus ?case
    by(auto simp:after_def)
      (fastsimp simp:wt_Push wt_Pop hyperUn_assoc
                intro:wt_instrs_app2 wt_instrs_Cons)
next
  case (newArray Ta e)
  from `P,E \<turnstile>1 newA Ta\<lfloor>e\<rceil> :: T`
  have "\<turnstile> [NewArray Ta], [] [::] [ty\<^isub>i' (Integer # ST) E (A \<squnion> \<A> e), ty\<^isub>i' (Ta\<lfloor>\<rceil> # ST) E (A \<squnion> \<A> e)]"
    by(auto simp:hyperset_defs ty\<^isub>i'_def wt_defs ty\<^isub>l_def)
  with newArray show ?case by(auto simp: after_def)
next
  case (ALen exp)
  { fix T
    have "\<turnstile> [ALength], [] [::] [ty\<^isub>i' (T\<lfloor>\<rceil> # ST) E (A \<squnion> \<A> exp), ty\<^isub>i' (Integer # ST) E (A \<squnion> \<A> exp)]"
      by(auto simp:hyperset_defs ty\<^isub>i'_def wt_defs ty\<^isub>l_def) }
  with ALen show ?case by(auto simp add: after_def)
next
  case (AAcc a i)
  from `P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T` have wta: "P,E \<turnstile>1 a :: T\<lfloor>\<rceil>" and wti: "P,E \<turnstile>1 i :: Integer" by auto
  let ?A1 = "A \<squnion> \<A> a" let ?A2 = "?A1 \<squnion> \<A> i"  
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>sa = "compT E A ST a"
  let ?\<tau>1 = "ty\<^isub>i' (T\<lfloor>\<rceil>#ST) E ?A1" let ?\<tau>si = "compT E ?A1 (T\<lfloor>\<rceil>#ST) i"
  let ?\<tau>2 = "ty\<^isub>i' (Integer#T\<lfloor>\<rceil>#ST) E ?A2" let ?\<tau>' = "ty\<^isub>i' (T#ST) E ?A2"
  have "\<turnstile> [ALoad], [] [::] [?\<tau>2,?\<tau>']" by(auto simp add: ty\<^isub>i'_def wt_defs)
  also have "PROP ?P i E Integer ?A1 (T\<lfloor>\<rceil>#ST)" by fact
  with wti AAcc have "\<turnstile> compE2 i, compxE2 i 0 (size ST+1) [::] ?\<tau>1#?\<tau>si@[?\<tau>2]"
    by(auto simp add: after_def)
  also from wta AAcc have "\<turnstile> compE2 a, compxE2 a 0 (size ST) [::] ?\<tau>#?\<tau>sa@[?\<tau>1]" 
    by(auto simp add: after_def)
  finally show ?case using wta wti `P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T` by(simp add: after_def hyperUn_assoc)
next
  case (AAss a i e)
  note wt = `P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T`
  then obtain Ta U where wta: "P,E \<turnstile>1 a :: Ta\<lfloor>\<rceil>" and wti: "P,E \<turnstile>1 i :: Integer"
    and wte: "P,E \<turnstile>1 e :: U" and U: "P \<turnstile> U \<le> Ta" and [simp]: "T = Void" by auto
  let ?A1 = "A \<squnion> \<A> a" let ?A2 = "?A1 \<squnion> \<A> i" let ?A3 = "?A2 \<squnion> \<A> e"
  let ?\<tau> = "ty\<^isub>i' ST E A" let ?\<tau>sa = "compT E A ST a"
  let ?\<tau>1 = "ty\<^isub>i' (Ta\<lfloor>\<rceil>#ST) E ?A1" let ?\<tau>si = "compT E ?A1 (Ta\<lfloor>\<rceil>#ST) i"
  let ?\<tau>2 = "ty\<^isub>i' (Integer#Ta\<lfloor>\<rceil>#ST) E ?A2" let ?\<tau>se = "compT E ?A2 (Integer#Ta\<lfloor>\<rceil>#ST) e"
  let ?\<tau>3 = "ty\<^isub>i' (U#Integer#Ta\<lfloor>\<rceil>#ST) E ?A3" let ?\<tau>4 = "ty\<^isub>i' ST E ?A3"
  let ?\<tau>' = "ty\<^isub>i' (Void#ST) E ?A3"
  from `length ST + max_stack (a\<lfloor>i\<rceil> := e) \<le> mxs`
  have "\<turnstile> [AStore, Push Unit], [] [::] [?\<tau>3,?\<tau>4,?\<tau>']"
    by(auto simp add: ty\<^isub>i'_def wt_defs nth_Cons split: nat.split)
  also have "PROP ?P e E U ?A2 (Integer#Ta\<lfloor>\<rceil>#ST)" by fact
  with wte AAss have "\<turnstile> compE2 e, compxE2 e 0 (size ST+2) [::] ?\<tau>2#?\<tau>se@[?\<tau>3]"
    by(auto simp add: after_def)
  also have "PROP ?P i E Integer ?A1 (Ta\<lfloor>\<rceil>#ST)" by fact
  with wti AAss have "\<turnstile> compE2 i, compxE2 i 0 (size ST+1) [::] ?\<tau>1#?\<tau>si@[?\<tau>2]"
    by(auto simp add: after_def)
  also from wta AAss have "\<turnstile> compE2 a, compxE2 a 0 (size ST) [::] ?\<tau>#?\<tau>sa@[?\<tau>1]" 
    by(auto simp add: after_def)
  finally show ?case using wta wti wte `P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T`
    by(simp add: after_def hyperUn_assoc)
next
  case (InSynchronized i a exp) thus ?case by auto
qed

end

lemma [simp]: "is_type (compP f P) = is_type P"
by(auto simp add: mem_def)

lemma states_compP [simp]: "states (compP f P) mxs mxl = states P mxs mxl"
by (simp add: JVM_states_unfold)

lemma WT_external_compP' [simp]: "external_WT (compP f P) = external_WT P"
by(auto simp add: expand_fun_eq)

lemma [simp]: "app\<^isub>i (i, compP f P, pc, mpc, T, \<tau>) = app\<^isub>i (i, P, pc, mpc, T, \<tau>)"
proof -
  { fix ST LT
    have "app\<^isub>i (i, compP f P, pc, mpc, T, (ST, LT)) = app\<^isub>i (i, P, pc, mpc, T, (ST, LT))"
    proof(cases i)
      case (Invoke M n)
      have "\<And>C Ts D. (\<exists>T m. compP f P \<turnstile> C sees M: Ts\<rightarrow>T = m in D) \<longleftrightarrow> (\<exists>T m. P \<turnstile> C sees M: Ts\<rightarrow>T = m in D)"
	by(auto dest!: sees_method_compPD dest: sees_method_compP)
      with Invoke show ?thesis by clarsimp
    qed(simp_all) }
  thus ?thesis by(cases \<tau>) simp
qed

  
lemma [simp]: "is_relevant_entry (compP f P) i = is_relevant_entry P i"
  apply (rule ext)+
  apply (unfold is_relevant_entry_def)
  apply (cases i)
  apply auto
  done

lemma [simp]: "relevant_entries (compP f P) i pc xt = relevant_entries P i pc xt"
by (simp add: relevant_entries_def)

lemma [simp]: "app i (compP f P) mpc T pc mxl xt \<tau> = app i P mpc T pc mxl xt \<tau>"
  apply (simp add: app_def xcpt_app_def eff_def xcpt_eff_def norm_eff_def)
  apply (fastsimp simp add: image_def)
  done

lemma [simp]: "app i P mpc T pc mxl xt \<tau> \<Longrightarrow> eff i (compP f P) pc xt \<tau> = eff i P pc xt \<tau>"
  apply (clarsimp simp add: eff_def norm_eff_def xcpt_eff_def app_def)
  apply (cases i)
  apply auto
  done

lemma [simp]: "widen (compP f P) = widen P"
  apply (rule ext)+
  apply (simp)
  done
  
lemma [simp]: "compP f P \<turnstile> \<tau> \<le>' \<tau>' = P \<turnstile> \<tau> \<le>' \<tau>'"
by (simp add: sup_state_opt_def sup_state_def sup_ty_opt_def)(*>*)

lemma [simp]: "compP f P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s = P,T,mpc,mxl,xt \<turnstile> i,pc :: \<tau>s"
by (simp add: wt_instr_def cong: conj_cong)

declare TC0.compT_sizes[OF TC0.intro, simp]  TC0.ty_def2[OF TC0.intro, simp]

lemma [simp]: "x \<in> is_type P \<longleftrightarrow> is_type P x"
by(auto simp add: mem_def)

lemma compT_method:
  fixes e and A and C and Ts and mxl\<^isub>0
  defines [simp]: "E \<equiv> Class C # Ts"
      and [simp]: "A \<equiv> \<lfloor>{..size Ts}\<rfloor>"
      and [simp]: "A' \<equiv> A \<squnion> \<A> e"
      and [simp]: "mxs \<equiv> max_stack e"
      and [simp]: "mxl\<^isub>0 \<equiv> max_vars e"
      and [simp]: "mxl \<equiv> 1 + size Ts + mxl\<^isub>0"
  assumes wf_prog: "wf_prog p P"
  shows "\<lbrakk> P,E \<turnstile>1 e :: T; \<D> e A; \<B> e (size E); set E \<subseteq> is_type P; P \<turnstile> T \<le> T' \<rbrakk> \<Longrightarrow>
   wt_method (compP2 P) C Ts T' mxs mxl\<^isub>0 (compE2 e @ [Return]) (compxE2 e 0 0)
      (TC0.ty\<^isub>i' mxl [] E A # TC0.compTa P mxl E A [] e)"
using wf_prog
apply(simp add:wt_method_def TC0.compTa_def[OF TC0.intro[OF wf_prog]] TC0.after_def[OF TC0.intro[OF wf_prog]] TC0.compT_sizes[OF TC0.intro[OF wf_prog]] compP2_def compMb2_def)
apply(rule conjI)
 apply(simp add:check_types_def TC0.OK_ty\<^isub>i'_in_statesI[OF TC0.intro[OF wf_prog]])
 apply(rule conjI)
  apply(frule WT1_is_type[OF wf_prog])
   apply simp
  apply(insert max_stack1[of e])
  apply(fastsimp intro!: TC0.OK_ty\<^isub>i'_in_statesI[OF TC0.intro])
 apply(erule (1) TC0.compT_states[OF TC0.intro])
    apply simp
   apply simp
  apply simp
 apply simp
apply(rule conjI)
 apply(fastsimp simp add:wt_start_def TC0.ty\<^isub>i'_def[OF TC0.intro] TC0.ty\<^isub>l_def[OF TC0.intro] list_all2_conv_all_nth nth_Cons split:nat.split dest:less_antisym)
apply (frule (1) TC2.compT_wt_instrs[OF TC2.intro[OF TC0.intro], where ST = "[]" and mxs = "max_stack e" and mxl = "1 + size Ts + max_vars e"])
     apply simp
    apply simp
   apply simp
  apply simp
 apply simp
apply (clarsimp simp:TC2.wt_instrs_def[OF TC2.intro[OF TC0.intro]] TC0.after_def[OF TC0.intro])
apply(rule conjI)
 apply (fastsimp)
apply(clarsimp)
apply(drule (1) less_antisym)
apply(thin_tac "\<forall>x. ?P x")
apply(clarsimp simp:TC2.wt_defs[OF TC2.intro,OF TC0.intro] xcpt_app_pcs xcpt_eff_pcs TC0.ty\<^isub>i'_def[OF TC0.intro])
apply(cases "size (compE2 e)")
 apply (simp del: compxE2_size_convs compxE2_stack_xlift_convs nth_append  add: neq_Nil_conv)
apply (simp)
done
(*>*)


constdefs
  compTP :: "J1_prog \<Rightarrow> ty\<^isub>P"
  "compTP P C M  \<equiv>
  let (D,Ts,T,e) = method P C M;
       E = Class C # Ts;
       A = \<lfloor>{..size Ts}\<rfloor>;
       mxl = 1 + size Ts + max_vars e
  in  (TC0.ty\<^isub>i' mxl [] E A # TC0.compTa P mxl E A [] e)"

theorem wt_compP2:
  "wf_J1_prog P \<Longrightarrow> wf_jvm_prog (compP2 P)"
  apply (simp add: wf_jvm_prog_def wf_jvm_prog_phi_def compP2_def compMb2_def)
  apply(rule_tac x = "compTP P" in exI)
  apply (rule wf_prog_compPI)
   prefer 2 apply assumption
  apply (clarsimp simp add: wf_mdecl_def)
  apply (simp add: compTP_def)
  apply (rule compT_method [simplified compP2_def compMb2_def, simplified])
       apply assumption+
    apply (drule (1) sees_wf_mdecl)
    apply (simp add: wf_mdecl_def)
   apply (fastsimp intro: sees_method_is_class)
  apply assumption
  done


(*
theorem wt_J2JVM:
  "wf_J_prog P \<Longrightarrow> wf_jvm_prog (J2JVM P)"
apply(simp only:o_def J2JVM_def)
apply(blast intro:wt_compP\<^isub>2 compP\<^isub>1_pres_wf)
done
*)

end
