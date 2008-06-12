(*  Title:      JinjaThreads/Framework/FWLifting.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Lifting of thread-local properties to the multithreaded case} *}

theory FWLifting imports FWWellform begin

definition
  ts_ok :: "('x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('l, 't,'x) thread_info \<Rightarrow> 'm \<Rightarrow> bool"
where
  "ts_ok P ts m \<equiv> \<forall>t. case (ts t) of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> P x m"

lemma ts_okI:
  "\<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> P x m \<rbrakk> \<Longrightarrow> ts_ok P ts m"
by(auto simp add: ts_ok_def)

lemma ts_okE:
  "\<lbrakk> ts_ok P ts m; \<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> P x m \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp add: ts_ok_def)

lemma ts_okD:
  "\<lbrakk> ts_ok P ts m; ts t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> P x m"
by(auto simp add: ts_ok_def)

lemma ts_ok_True [simp]:
  "ts_ok (\<lambda>m x. True) ts m"
by(auto intro: ts_okI)

lemma ts_ok_conj:
  "ts_ok (\<lambda>x m. P x m \<and> Q x m) = (\<lambda>ts m. ts_ok P ts m \<and> ts_ok Q ts m)"
apply(auto intro: ts_okI intro!: ext dest: ts_okD) 
done

definition
  ts_inv :: "('i \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t \<rightharpoonup> 'i) \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> 'm \<Rightarrow> bool"
where
  "ts_inv P I ts m \<equiv> \<forall>t. case (ts t) of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i x m" 

lemma ts_invI:
  "\<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i x m \<rbrakk> \<Longrightarrow> ts_inv P I ts m"
by(simp add: ts_inv_def)

lemma ts_invE:
  "\<lbrakk> ts_inv P I ts m; \<forall>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<longrightarrow> (\<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i x m) \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
by(auto simp add: ts_inv_def)

lemma ts_invD:
  "\<lbrakk> ts_inv P I ts m; ts t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i x m"
by(auto simp add: ts_inv_def)

definition
  inv_ext :: "('t \<rightharpoonup> 'i) \<Rightarrow> ('t \<rightharpoonup> 'i) \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "I \<unlhd> I'  \<equiv> (\<forall>t. case I t of None \<Rightarrow> True | \<lfloor>i\<rfloor> \<Rightarrow> I' t = \<lfloor>i\<rfloor>)"

lemma inv_extI:
  "(\<And>t i. I t = \<lfloor>i\<rfloor> \<Longrightarrow> I' t = \<lfloor>i\<rfloor>) \<Longrightarrow> I \<unlhd> I'"
by(simp add: inv_ext_def)

lemma inv_extE:
  "\<lbrakk> I \<unlhd> I'; \<forall>t i. I t = \<lfloor>i\<rfloor> \<longrightarrow> I' t = \<lfloor>i\<rfloor> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(simp add: inv_ext_def)

lemma inv_extD:
  "\<lbrakk> I \<unlhd> I'; I t = \<lfloor>i\<rfloor> \<rbrakk> \<Longrightarrow> I' t = \<lfloor>i\<rfloor>"
by(simp add: inv_ext_def)

lemma inv_ext_refl [iff]:
  fixes I:: "'t \<rightharpoonup> 'i"
  shows "I \<unlhd> I"
by(auto intro: inv_extI)

lemma inv_ext_trans [trans]:
  fixes I :: "'t \<rightharpoonup> 'i"
  shows "\<lbrakk> I \<unlhd> I'; I' \<unlhd> I'' \<rbrakk> \<Longrightarrow> I \<unlhd> I''" 
by(auto intro: inv_extI dest: inv_extD)

lemma inv_ext_upd: "I t = None \<Longrightarrow> I \<unlhd> I(t := v)"
by(auto intro!: inv_extI)


definition
  ts_inv_ok :: "('l,'t,'x) thread_info \<Rightarrow> ('t \<rightharpoonup> 'i) \<Rightarrow> bool"
where
  "ts_inv_ok ts I \<equiv> \<forall>t. ts t = None \<longleftrightarrow> I t = None"

lemma ts_inv_okI:
  "(\<And>t. ts t = None \<longleftrightarrow> I t = None) \<Longrightarrow> ts_inv_ok ts I"
apply(clarsimp simp add: ts_inv_ok_def)
done

lemma ts_inv_okI2:
  "(\<And>t. (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>)) \<Longrightarrow> ts_inv_ok ts I"
apply(force simp add: ts_inv_ok_def)
done

lemma ts_inv_okE:
  "\<lbrakk> ts_inv_ok ts I; \<forall>t. ts t = None \<longleftrightarrow> I t = None \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(force simp add: ts_inv_ok_def)
done

lemma ts_inv_okE2:
  "\<lbrakk> ts_inv_ok ts I; \<forall>t. (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
apply(force simp add: ts_inv_ok_def)
done

lemma ts_inv_okD:
  "ts_inv_ok ts I \<Longrightarrow> (ts t = None) \<longleftrightarrow> (I t = None)"
apply(erule ts_inv_okE, blast)
done

lemma ts_inv_okD2:
  "ts_inv_ok ts I \<Longrightarrow> (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>)"
apply(erule ts_inv_okE2, blast)
done

lemma ts_inv_ok_upd_ts:
  "\<lbrakk> ts t = \<lfloor>x\<rfloor>; ts_inv_ok ts I \<rbrakk> \<Longrightarrow> ts_inv_ok (ts(t \<mapsto> x')) I"
by(auto dest!: ts_inv_okD intro!: ts_inv_okI split: if_splits)


fun upd_inv :: "('t \<rightharpoonup> 'i) \<Rightarrow> ('i \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('t \<rightharpoonup> 'i)"
where
  "upd_inv I P (NewThread t x m) = I(t \<mapsto> SOME i. P i x m)"
| "upd_inv I P _ = I"

fun upd_invs :: "('t \<rightharpoonup> 'i) \<Rightarrow> ('i \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> ('t \<rightharpoonup> 'i)"
where
  "upd_invs I P [] = I"
| "upd_invs I P (ta#tas) = upd_invs (upd_inv I P ta) P tas"

lemma upd_invs_append [simp]:
  "upd_invs I P (xs @ ys) = upd_invs (upd_invs I P xs) P ys"
apply(induct xs arbitrary: I)
apply(auto)
done

lemma ts_inv_ok_upd_inv:
 "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updT ts ta) (upd_inv I P ta)"
apply(cases ta)
apply(auto intro!: ts_inv_okI elim: ts_inv_okD del: iffI)
done

lemma ts_inv_ok_upd_invs:
  "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs ts tas) (upd_invs I P tas)"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = `\<And>ts I. ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs ts TAS) (upd_invs I P TAS)`
  note esok = `ts_inv_ok TS I`
  from esok have "ts_inv_ok (redT_updT TS TA) (upd_inv I P TA)"
    by -(rule ts_inv_ok_upd_inv)
  hence "ts_inv_ok (redT_updTs (redT_updT TS TA) TAS) (upd_invs (upd_inv I P TA) P TAS)"
    by - (rule IH)
  thus ?case by simp
qed

lemma ts_inv_ok_inv_ext_upd_inv:
  "\<lbrakk> ts_inv_ok ts I; thread_ok ts m ta \<rbrakk> \<Longrightarrow> I \<unlhd> upd_inv I P ta"
apply(cases ta, auto intro!: inv_ext_upd dest: ts_inv_okD)
done

lemma ts_inv_ok_inv_ext_upd_invs:
  "\<lbrakk> ts_inv_ok ts I; thread_oks ts m tas\<rbrakk>
  \<Longrightarrow> I \<unlhd> upd_invs I P tas"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = `\<And>ts I. \<lbrakk> ts_inv_ok ts I; thread_oks ts m TAS\<rbrakk> \<Longrightarrow> I \<unlhd> upd_invs I P TAS`
  note esinv = `ts_inv_ok TS I`
  note cct = `thread_oks TS m (TA # TAS)`
  from esinv cct have "ts_inv_ok (redT_updT TS TA) (upd_inv I P TA)"
    by(auto intro: ts_inv_ok_upd_inv)
  with cct have "upd_inv I P TA \<unlhd> upd_invs (upd_inv I P TA) P TAS"
    by(auto intro: IH)
  moreover from esinv cct have "I \<unlhd> upd_inv I P TA"
    by(auto intro: ts_inv_ok_inv_ext_upd_inv)
  ultimately show ?case by(auto elim: inv_ext_trans)
qed

lemma upd_invs_Some:
  "\<lbrakk> thread_oks ts m' tas; I t = \<lfloor>i\<rfloor>; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_invs I Q tas t = \<lfloor>i\<rfloor>"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = `\<And>ts I. \<lbrakk>thread_oks ts m' TAS; I t = \<lfloor>i\<rfloor>; ts t = \<lfloor>x\<rfloor>\<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = \<lfloor>i\<rfloor>`
  note cct = `thread_oks TS m' (TA # TAS)`
  note it = `I t = \<lfloor>i\<rfloor>`
  note est = `TS t = \<lfloor>x\<rfloor>`
  from cct have cctta: "thread_ok TS m' TA"
    and ccttas: "thread_oks (redT_updT TS TA) m' TAS" by auto
  from cctta it est have "upd_inv I Q TA t = \<lfloor>i\<rfloor>"
    by(cases TA, auto)
  moreover
  have "redT_updT TS TA t = \<lfloor>x\<rfloor>" using cctta est
    by - (rule redT_updT_Some) 
  ultimately have "upd_invs (upd_inv I Q TA) Q TAS t = \<lfloor>i\<rfloor>" using ccttas
    by -(erule IH)
  thus ?case by simp
qed

lemma upd_inv_Some_eq:
  "\<lbrakk> thread_ok ts m' ta; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_inv I Q ta t = I t"
by(cases ta, auto)

lemma upd_invs_Some_eq: "\<lbrakk> thread_oks ts m' tas; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_invs I Q tas t = I t"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = `\<And>ts I. \<lbrakk>thread_oks ts m' TAS; ts t = \<lfloor>x\<rfloor>\<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = I t`
  note cct = `thread_oks TS m' (TA # TAS)`
  note est = `TS t = \<lfloor>x\<rfloor>`
  from cct est have "upd_invs (upd_inv I Q TA) Q TAS t = upd_inv I Q TA t"
    apply(clarsimp)
    apply(erule IH)
    by(rule redT_updT_Some)
  also from cct est have "\<dots> = I t" 
    by(auto elim: upd_inv_Some_eq)
  finally show ?case by simp
qed


lemma SOME_new_thread_upd_invs:
  assumes Qsome: "Q (SOME i. Q i x m) x m"
  and nt: "NewThread t x m \<in> set tas"
  and cct: "thread_oks ts m' tas"
  shows "\<exists>i. upd_invs I Q tas t = \<lfloor>i\<rfloor> \<and> Q i x m"
proof(rule exI[where x="SOME i. Q i x m"])
  from nt cct have "upd_invs I Q tas t = \<lfloor>SOME i. Q i x m\<rfloor>"
  proof(induct tas arbitrary: ts I)
    case Nil thus ?case by simp
  next
    case (Cons TA TAS TS I)
    note IH = `\<And>ts I. \<lbrakk> NewThread t x m \<in> set TAS; thread_oks ts m' TAS \<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = \<lfloor>SOME i. Q i x m\<rfloor>`
    note nt = `NewThread t x m \<in> set (TA # TAS)`
    note cct = `thread_oks TS m' (TA # TAS)`
    { assume nt': "NewThread t x m \<in> set TAS"
      from cct have ?case
	apply(clarsimp)
	by(rule IH[OF nt']) }
    moreover
    { assume ta: "TA = NewThread t x m"
      with cct have rup: "redT_updT TS TA t = \<lfloor>(x, no_wait_locks)\<rfloor>"
	by(simp)
      from cct have cctta: "thread_oks (redT_updT TS TA) m' TAS" by simp
      from ta have "upd_inv I Q TA t = \<lfloor>SOME i. Q i x m\<rfloor>"
	by(simp)
      hence ?case 
	by(clarsimp simp add: upd_invs_Some_eq[OF cctta, OF rup]) }
    ultimately show ?case using nt by auto
  qed
  with Qsome show "upd_invs I Q tas t = \<lfloor>SOME i. Q i x m\<rfloor> \<and> Q (SOME i. Q i x m) x m"
    by(simp)
qed

end
