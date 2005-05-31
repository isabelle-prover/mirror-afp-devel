(*  Title:      Jinja/J/execute_WellType.thy
    ID:         $Id: execute_WellType.thy,v 1.1 2005-05-31 23:21:04 lsf37 Exp $
    Author:     Christoph Petzinger
    Copyright   2004 Technische Universitaet Muenchen
*)

header {* \isaheader{Code Generation For WellType} *}

theory execute_WellType
imports WellType Examples
begin

(* --- widens --- *)
consts widens :: "'m prog \<Rightarrow> (ty list \<times> ty list) set"
inductive "widens P"
intros
  widensNil:  "([], []) \<in> widens P"
  widensCons: "P \<turnstile> T \<le> U \<Longrightarrow> (Ts, Us) \<in> widens P \<Longrightarrow> (T # Ts, U # Us) \<in> widens P"

lemma widens_eq:
  "(P \<turnstile> Ts [\<le>] Us) = ((Ts, Us) \<in> widens P)"
proof
  show "\<And> Us. P \<turnstile> Ts [\<le>] Us \<Longrightarrow> (Ts, Us) \<in> widens P"
  proof (induct Ts)
    case Nil
    note NilT=Nil
    thus ?case
    proof (cases Us)
      case Nil
      with NilT show ?thesis by (simp add: widens.intros)
    next
      case (Cons u us)
      with NilT show ?thesis by simp
    qed
  next
    case (Cons t ts)
    thus ?case by (auto simp add: widens.intros)
  qed
next
  assume "(Ts, Us) \<in> widens P"
  thus "P \<turnstile> Ts [\<le>] Us" by (induct Ts Us, auto simp add: fun_of_def)
qed

(* --- WTBinOp --- *)
lemma WTBinOpEq:
  "\<lbrakk>P,E \<turnstile> e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; (P \<turnstile> T\<^isub>1 \<le> T\<^isub>2) \<or> (P \<turnstile> T\<^isub>2 \<le> T\<^isub>1)\<rbrakk> \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Eq\<guillemotright> e\<^isub>2 :: Boolean"
by (simp add: WT_WTs.WTBinOpEq)

lemma WTBinOpAdd:
  "\<lbrakk>P,E \<turnstile> e\<^isub>1 :: T\<^isub>1;  P,E \<turnstile> e\<^isub>2 :: T\<^isub>2; T\<^isub>1 = Integer; T\<^isub>2 = Integer\<rbrakk> \<Longrightarrow> P,E \<turnstile> e\<^isub>1 \<guillemotleft>Add\<guillemotright> e\<^isub>2 :: Integer"
by (simp add: WTBinOpAdd)

(* Could not finish proof \<Rightarrow> WT_WTs.WTCond replaced with new intros WT_WTs.WTCond1 and WT_WTs.WTCond2 *)
(* --- WTCond --- *)
(*
lemma TRSubclsWf:
  "wf ( (subcls1 P)\<^sup>* )"
sorry

lemma TRSubclsLe:
  assumes noteq: "C \<noteq> D" and subcls: "P \<turnstile> C \<preceq>\<^sup>* D"
  shows "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
proof (cases "C = Object")
  case True
  note Obj=True
  thus ?thesis
  proof (cases "D = Object")
    case True
    with noteq Obj show ?thesis by simp
  next
    case False
    with subcls Obj show ?thesis by simp
  qed
next
  case False
  note Obj=False
  with noteq subcls show ?thesis
  proof (cases "D = Object")
    case True
    with noteq show ?thesis by simp
  next
    case False
    with noteq subcls Obj show ?thesis by (rule_tac wf_not_sym, simp add: TRSubclsWf)
  qed
qed

lemma TRSubclsEq:
  assumes subcls1: "P \<turnstile> C \<preceq>\<^sup>* D" and subcls2: "P \<turnstile> D \<preceq>\<^sup>* C"
  shows "C = D"
proof (cases "C = Object")
  case True
  with subcls1 have "D = Object" by simp
  thus ?thesis by simp
next
  case False
  with subcls2 have Obj: "D \<noteq> Object" by auto
  with False subcls1 subcls2 show ?thesis
  proof (cases "C = D")
    case True thus ?thesis by simp
  next
    case False with Obj subcls1 subcls2 show ?thesis by (simp add: TRSubclsLe)
  qed
qed

lemma TRWidenEq:
  "\<lbrakk> P \<turnstile> T\<^isub>1 \<le> T\<^isub>2; P \<turnstile> T\<^isub>2 \<le> T\<^isub>1\<rbrakk> \<Longrightarrow> T\<^isub>1 = T\<^isub>2"
by (cases T\<^isub>1,auto, cases T\<^isub>2,auto simp add:TRSubclsEq)
*)

lemma WTCond1:
  "\<lbrakk>P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2; P \<turnstile> T\<^isub>1 \<le> T\<^isub>2;
    P \<turnstile> T\<^isub>2 \<le> T\<^isub>1 \<longrightarrow> T\<^isub>1 = T\<^isub>2 \<rbrakk> \<Longrightarrow> P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T\<^isub>2"
by (fastsimp)

lemma WTCond2:
  "\<lbrakk>P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^isub>1::T\<^isub>1;  P,E \<turnstile> e\<^isub>2::T\<^isub>2; P \<turnstile> T\<^isub>2 \<le> T\<^isub>1;
    P \<turnstile> T\<^isub>1 \<le> T\<^isub>2 \<longrightarrow> T\<^isub>1 = T\<^isub>2 \<rbrakk> \<Longrightarrow> P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 :: T\<^isub>1"
by (fastsimp)

lemmas [code ind] =
  WT_WTs.WTNew
  WT_WTs.WTCast
  WT_WTs.WTVal
  WT_WTs.WTVar
         WTBinOpEq WTBinOpAdd (*WT.WT_WTs.WTBinOp*)
  WT_WTs.WTLAss
  WT_WTs.WTFAcc[unfolded sees_field_def, OF _ exI, OF _ conjI]
  WT_WTs.WTFAss[unfolded sees_field_def, OF _ exI, OF _ conjI]
  WT_WTs.WTCall[unfolded Method_def, OF _ exI, OF _ conjI, simplified widens_eq]
  WT_WTs.WTBlock
  WT_WTs.WTSeq
  WTCond1
  WTCond2
  WT_WTs.WTWhile
  WT_WTs.WTThrow
  WT_WTs.WTTry
  WT_WTs.WTNil
  WT_WTs.WTCons


generate_code
  test1 = "[], empty  \<turnstile> testExpr1 :: _"
  test2 = "[], empty  \<turnstile> testExpr2 :: _"
  test3 = "[], empty(''V'' \<mapsto> Integer)  \<turnstile> testExpr3 :: _"
  test4 = "[], empty(''V'' \<mapsto> Integer)  \<turnstile> testExpr4 :: _"
  test5 = "[classObject, (''C'',(''Object'',[(''F'',Integer)],[]))], empty  \<turnstile> testExpr5 :: _"
  test6 = "[classObject, classI], empty  \<turnstile> testExpr6 :: _"

ML {* if Seq.hd test1 = Integer then () else error "" *}
ML {* if Seq.hd test2 = Integer then () else error "" *}
ML {* if Seq.hd test3 = Integer then () else error "" *}
ML {* if Seq.hd test4 = Void then () else error "" *}
ML {* if Seq.hd test5 = Void then () else error "" *}
ML {* if Seq.hd test6 = Integer then () else error "" *}

generate_code 
  testmb_isNull     = "[classObject, classA], empty([this] [\<mapsto>] [Class ''A'']) \<turnstile> mb_isNull :: _"
  testmb_add        = "[classObject, classA], empty([this,''i''] [\<mapsto>] [Class ''A'',Integer]) \<turnstile> mb_add :: _"
  testmb_mult_cond  = "[classObject, classA], empty([this,''j''] [\<mapsto>] [Class ''A'',Integer]) \<turnstile> mb_mult_cond :: _"
  testmb_mult_block = "[classObject, classA], empty([this,''i'',''j'',''temp''] [\<mapsto>] [Class ''A'',Integer,Integer,Integer]) \<turnstile> mb_mult_block :: _"
  testmb_mult       = "[classObject, classA], empty([this,''i'',''j''] [\<mapsto>] [Class ''A'',Integer,Integer]) \<turnstile> mb_mult :: _"

ML {* if Seq.hd testmb_isNull = Boolean then () else error "" *}
ML {* if Seq.hd testmb_add = Integer then () else error "" *}
ML {* if Seq.hd testmb_mult_cond = Boolean then () else error "" *}
ML {* if Seq.hd testmb_mult_block = Void then () else error "" *}
ML {* if Seq.hd testmb_mult = Integer then () else error "" *}

generate_code
  test = "[classObject, classA], empty \<turnstile> testExpr_ClassA :: _"

ML {* if Seq.hd test = Integer then () else error "" *}


end