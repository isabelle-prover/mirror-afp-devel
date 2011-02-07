(*  Title:      JinjaThreads/Common/WellForm_Exec.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Executable type inference} *}

theory WellType_Exec imports
  WellType
  "../Common/SemiType"
  "../Common/ExternalCallWF"
begin

declare Listn.lesub_list_impl_same_size[simp del]
declare listE_length [simp del]


inductive WT_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ ::' _"   [51,51,51]50)
  and WTs_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [::''] _"   [51,51,51]50)
  for P :: "J_prog"
  where

  WTNew_code:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile> new C ::' Class C"

| WTNewArray_code:
  "\<lbrakk> P,E \<turnstile> e ::' Integer; is_type P T \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> newA T\<lfloor>e\<rceil> ::' T\<lfloor>\<rceil>"

| WTCast_code:
  "\<lbrakk> P,E \<turnstile> e ::' T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> Cast U e ::' U"

| WTInstanceOf_code:
  "\<lbrakk> P,E \<turnstile> e ::' T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U; is_refT T; is_refT U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e instanceof U ::' Boolean"

| WTVal_code:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile> Val v ::' T"

| WTVar_code:
  "E V = Some T \<Longrightarrow>
  P,E \<turnstile> Var V ::' T"

| WTBinOp_code:
  "\<lbrakk> P,E \<turnstile> e1 ::' T1; P,E \<turnstile> e2 ::' T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e1\<guillemotleft>bop\<guillemotright>e2 ::' T"

| WTLAss_code:
  "\<lbrakk> E V = Some T;  P,E \<turnstile> e ::' T';  P \<turnstile> T' \<le> T;  V \<noteq> this \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> V:=e ::' Void"

| WTAAcc_code:
  "\<lbrakk> P,E \<turnstile> a ::' T\<lfloor>\<rceil>; P,E \<turnstile> i ::' Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> ::' T"

| WTAAss_code:
  "\<lbrakk> P,E \<turnstile> a ::' T\<lfloor>\<rceil>; P,E \<turnstile> i ::' Integer; P,E \<turnstile> e ::' T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> a\<lfloor>i\<rceil> := e ::' Void"

| WTALength_code:
  "P,E \<turnstile> a ::' T\<lfloor>\<rceil> \<Longrightarrow> P,E \<turnstile> a\<bullet>length ::' Integer"

| WTFAcc_code:
  "\<lbrakk> P,E \<turnstile> e ::' Class C;  P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>F{D} ::' T"

| WTFAss_code:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 ::' Class C;  P \<turnstile> C sees F:T (fm) in D;  P,E \<turnstile> e\<^isub>2 ::' T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^isub>1\<bullet>F{D}:=e\<^isub>2 ::' Void"

| WTCall_code:
  "\<lbrakk> P,E \<turnstile> e ::' Class C; \<not> is_external_call P (Class C) M; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     P,E \<turnstile> es [::'] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) ::' T"

| WTExternal_code:
  "\<lbrakk> P,E \<turnstile> e ::' T; P,E \<turnstile> es [::'] Ts; P \<turnstile> T\<bullet>M(Ts') :: U; P \<turnstile> Ts [\<le>] Ts' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<bullet>M(es) ::' U"

| WTBlock_code:
  "\<lbrakk> is_type P T;  P,E(V \<mapsto> T) \<turnstile> e ::' T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> case typeof v of None \<Rightarrow> False | Some T' \<Rightarrow> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> {V:T=vo; e} ::' T'"

| WTSynchronized_code:
  "\<lbrakk> P,E \<turnstile> o' ::' T; is_refT T; T \<noteq> NT; P,E \<turnstile> e ::' T' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> sync(o') e ::' T'"

| WTSeq_code:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1::'T\<^isub>1;  P,E \<turnstile> e\<^isub>2::'T\<^isub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile> e\<^isub>1;;e\<^isub>2 ::' T\<^isub>2"
| WTCond_code:
  "\<lbrakk> P,E \<turnstile> e ::' Boolean;  P,E \<turnstile> e\<^isub>1::'T\<^isub>1;  P,E \<turnstile> e\<^isub>2::'T\<^isub>2; SemiType.sup P T\<^isub>1 T\<^isub>2 = OK T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> if (e) e\<^isub>1 else e\<^isub>2 ::' T"

| WTWhile_code:
  "\<lbrakk> P,E \<turnstile> e ::' Boolean;  P,E \<turnstile> c::'T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> while (e) c ::' Void"

| WTThrow_code:
  "\<lbrakk> P,E \<turnstile> e ::' Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> 
  P,E \<turnstile> throw e ::' Void"

| WTTry_code:
  "\<lbrakk> P,E \<turnstile> e\<^isub>1 ::' T;  P,E(V \<mapsto> Class C) \<turnstile> e\<^isub>2 ::' T; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> try e\<^isub>1 catch(C V) e\<^isub>2 ::' T"

| WTNil_code: "P,E \<turnstile> [] [::'] []"

| WTCons_code: "\<lbrakk> P,E \<turnstile> e ::' T; P,E \<turnstile> es [::'] Ts \<rbrakk> \<Longrightarrow> P,E \<turnstile> e#es [::'] T#Ts"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [detect_switches, skip_proof]
  WT_code
.

(*

primrec WT_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty err"
  and WTs_code :: "J_prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list err"
where 
  WT_code_New: 
  "WT_code P E (new C) = (if is_class P C then OK (Class C) else Err)"

| WT_code_NewArray: 
  "WT_code P E (newA T\<lfloor>e\<rceil>) = 
   (if is_type P T
    then Err.lift (\<lambda>T'. if T' = Integer then OK (Array T) else Err) (WT_code P E e)
    else Err)"

| WT_code_Cast:
  "WT_code P E (Cast U e) =
   (if is_type P U
    then Err.lift (\<lambda>T. if P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U then OK U else Err) (WT_code P E e)
    else Err)"

| WT_code_InstanceOf:
  "WT_code P E (e instanceof U) =
   (if is_type P U \<and> is_refT U
    then Err.lift (\<lambda>T. if is_refT T \<and> (P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U) then OK Boolean else Err) (WT_code P E e)
    else Err)"

| WT_code_Val: 
  "WT_code P E (Val v) = (case typeof v of None \<Rightarrow> Err | Some T \<Rightarrow> OK T)"

| WT_code_Var:
  "WT_code P E (Var V) = (case E V of None \<Rightarrow> Err | Some T \<Rightarrow> OK T)"

| WT_code_BinOp:
  "WT_code P E (e1\<guillemotleft>bop\<guillemotright>e2) =
  Err.lift2 (\<lambda>T1 T2. 
             let T = WT_binop_i_i_i_i_o P T1 bop T2
             in (if Predicate.is_empty T then Err else OK (Predicate.the T)))
            (WT_code P E e1) (WT_code P E e2)"

| WT_code_LAss:
  "WT_code P E (V := e) =
   (if V = this then Err
    else (case E V of None \<Rightarrow> Err
          | Some U \<Rightarrow> Err.lift (\<lambda>T. if P \<turnstile> T \<le> U then OK Void else Err) (WT_code P E e)))"

| WT_code_AAcc:
  "WT_code P E (a\<lfloor>i\<rceil>) =
   Err.lift2 (\<lambda>T1 T2. case T1 of Array U \<Rightarrow> if T2 = Integer then OK U else Err | _ \<Rightarrow> Err)
             (WT_code P E a) (WT_code P E i)"

| WT_code_AAss:
  "WT_code P E (a\<lfloor>i\<rceil> := e) =
   Err.lift (\<lambda>T1. case T1 of 
                    Array U \<Rightarrow> Err.lift2 (\<lambda>T2 T3. if T2 = Integer \<and> P \<turnstile> T3 \<le> U then OK Void else Err)
                                        (WT_code P E i) (WT_code P E e)
                  | _ \<Rightarrow> Err)
            (WT_code P E a)"

| WT_code_ALength:
  "WT_code P E (a\<bullet>length) =
   Err.lift (\<lambda>T. case T of Array U \<Rightarrow> OK Integer | _ \<Rightarrow> Err) (WT_code P E a)"

| WT_code_FAcc:
  "WT_code P E (e\<bullet>F{D}) =
   Err.lift (\<lambda>T. case T of
                   Class C \<Rightarrow> let Tf = sees_field_i_i_i_o_o_i P C F D
                             in (if Predicate.is_empty Tf then Err else OK (fst (Predicate.the Tf)))
                 | _ \<Rightarrow> Err)
            (WT_code P E e)"

| WT_code_FAss:
  "WT_code P E (e\<bullet>F{D} := e') =
   Err.lift2 (\<lambda>T1 T2.
                 case T1 of 
                   Class C \<Rightarrow>
                   let Tf = sees_field_i_i_i_o_o_i P C F D
                   in (if Predicate.is_empty Tf then Err
                       else if P \<turnstile> T2 \<le> fst (Predicate.the Tf) then OK Void else Err)
                 | _ \<Rightarrow> Err)
             (WT_code P E e) (WT_code P E e')"

| WT_code_Call:
  "WT_code P E (e\<bullet>M(es)) =
   Err.lift2 (\<lambda>T Ts.
               let Text = external_WT_i_i_i_o_o P T M
               in (if Predicate.is_empty Text 
                  then (case T of 
                          Class C \<Rightarrow> 
                          (if is_external_call P (Class C) M then Err
                           else (let see = Method_i_i_i_o_o_o_o P C M
                                 in (if Predicate.is_empty see then Err
                                     else let (Ts', T, meth, D) = Predicate.the see
                                          in (if P \<turnstile> Ts [\<le>] Ts' then OK T else Err))))
                        | _ \<Rightarrow> Err)
                  else let (Ts', U) = Predicate.the Text
                       in if P \<turnstile> Ts [\<le>] Ts' then OK U else Err))
              (WT_code P E e) (WTs_code P E es)"


| WT_code_Block:
  "WT_code P E {V:U=vo; e} =
  (if is_type P U
   then Err.lift (\<lambda>T. case vo of None \<Rightarrow> OK T 
                        | Some v \<Rightarrow> case typeof v of None \<Rightarrow> Err
                                   | Some Tv \<Rightarrow> if P \<turnstile> Tv \<le> U then OK T else Err)
                 (WT_code P (E(V \<mapsto> U)) e)
   else Err)"

| WT_code_Synchronized:
  "WT_code P E (sync\<^bsub>v\<^esub>(e) e') =
   Err.lift2 (\<lambda>T1 T2. if is_refT T1 \<and> T1 \<noteq> NT then OK T2 else Err) (WT_code P E e) (WT_code P E e')"

| WT_code_InSynchronized:
  "WT_code P E (insync\<^bsub>V\<^esub>(a) e) = Err"

| WT_code_Seq:
  "WT_code P E (e;;e') =
   Err.lift2 (\<lambda>T1 T2. OK T2) (WT_code P E e) (WT_code P E e')"

| WT_code_Cond:
  "WT_code P E (if (e) e1 else e2) =
   Err.lift (\<lambda>T. if T = Boolean then Err.lift2 (SemiType.sup P) (WT_code P E e1) (WT_code P E e2) else Err)
            (WT_code P E e)"

| WT_code_While:
  "WT_code P E (while (e) c) =
   Err.lift2 (\<lambda>T1 T2. if T1 = Boolean then OK Void else Err) (WT_code P E e) (WT_code P E c)"

| WT_code_Throw:
  "WT_code P E (throw e) =
   Err.lift (\<lambda>T. case T of Class C \<Rightarrow> if P \<turnstile> C \<preceq>\<^sup>* Throwable then OK Void else Err | _ \<Rightarrow> Err) (WT_code P E e)"

| WT_code_Try:
  "WT_code P E (try e catch(C V) e') =
   (if P \<turnstile> C \<preceq>\<^sup>* Throwable
    then Err.lift2 (\<lambda>T1 T2. if T1 = T2 then OK T2 else Err) (WT_code P E e) (WT_code P (E(V \<mapsto> Class C)) e')
    else Err)"

| WTs_code_Nil:
  "WTs_code P E [] = OK []"

| WTs_code_Cons:
  "WTs_code P E (e # es) =
   Err.lift2 (\<lambda>T Ts. OK (T # Ts)) (WT_code P E e) (WTs_code P E es)"

lemma lift_eq_OK_conv:
  "Err.lift f e = OK b \<longleftrightarrow> (\<exists>a. e = OK a \<and> f a = OK b)"
by(cases e)(simp_all add: lift_def)

lemma lift2_eq_OK_conv:
  "Err.lift2 f e e' = OK c \<longleftrightarrow> (\<exists>a b. e = OK a \<and> e' = OK b \<and> f a b = OK c)"
by(cases e)(case_tac [2] e', simp_all add: lift2_def)

declare 
  lift_eq_OK_conv [simp]
  lift2_eq_OK_conv [simp]

*)

lemma assumes wf: "wf_prog wf_md P"
  shows WT_is_type: "\<lbrakk> P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> is_type P T"
  and WTs_is_type: "\<lbrakk> P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> set Ts \<subseteq> types P"
apply(induct rule: WT_WTs.inducts)
apply simp
apply simp
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (fastsimp intro:nth_mem simp add: ran_def)
apply(simp add: WT_binop_is_type)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply (simp add:sees_field_is_type[OF _ wf])
apply(simp)
apply(fastsimp dest: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply(fastsimp dest: WT_external_is_type[OF wf])
apply(fastsimp simp add: ran_def split: split_if_asm)
apply(simp add: is_class_Object[OF wf])
apply(simp)
apply(simp)
apply(fastsimp intro: is_lub_is_type[OF wf])
apply(simp)
apply(simp)
apply simp
apply simp
apply simp
done

lemma assumes wf: "wf_prog wf_md P"
  shows WT_code_into_WT: 
  "\<lbrakk> P,E \<turnstile> e ::' T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e :: T"

  and WTs_code_into_WTs:
  "\<lbrakk> P,E \<turnstile> es [::'] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [::] Ts"
proof(induct rule: WT_code_WTs_code.inducts)
  case (WTBlock_code U E V e' T vo)
  from `is_type P U` `ran E \<subseteq> types P`
  have "ran (E(V \<mapsto> U)) \<subseteq> types P" by(auto simp add: ran_def)
  hence "P,E(V \<mapsto> U) \<turnstile> e' :: T" by(rule WTBlock_code)
  with `is_type P U` show ?case
    using `case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> case typeof v of None \<Rightarrow> False | \<lfloor>T'\<rfloor> \<Rightarrow> P \<turnstile> T' \<le> U` by auto
next
  case (WTCond_code E e e1 T1 e2 T2 T)
  from `ran E \<subseteq> types P` have "P,E \<turnstile> e :: Boolean" "P,E \<turnstile> e1 :: T1" "P,E \<turnstile> e2 :: T2"
    by(rule WTCond_code)+
  moreover with `ran E \<subseteq> types P` have "is_type P T1" "is_type P T2"
    by(blast intro: WT_is_type[OF wf])+
  hence "P \<turnstile> lub(T1, T2) = T" using `sup P T1 T2 = OK T` by(rule sup_is_lubI[OF wf])
  ultimately show ?case ..
next
  case (WTTry_code E e1 T V C e2)
  from `ran E \<subseteq> types P` have "P,E \<turnstile> e1 :: T" by(rule WTTry_code)
  moreover from `P \<turnstile> C \<preceq>\<^sup>* Throwable` have "is_class P C"
    by(rule is_class_sub_Throwable[OF wf])
  with `ran E \<subseteq> types P` have "ran (E(V \<mapsto> Class C)) \<subseteq> types P"
    by(auto simp add: ran_def)
  hence "P,E(V \<mapsto> Class C) \<turnstile> e2 :: T" by(rule WTTry_code)
  ultimately show ?case using `P \<turnstile> C \<preceq>\<^sup>* Throwable` ..
qed blast+

(*
lemma assumes wf: "wf_prog wf_md P"
  shows WT_code_OK_into_WT: 
  "\<lbrakk> WT_code P E e = OK T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e :: T"

  and WTs_code_OK_into_WTs:
  "\<lbrakk> WTs_code P E es = OK Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [::] Ts"
proof(induct e and es arbitrary: E T L and E Ts L)
  case (BinOp e1 bop e2)
  from `WT_code P E (e1 \<guillemotleft>bop\<guillemotright> e2) = OK T`
  obtain T1 T2 where e1: "WT_code P E e1 = OK T1" 
    and e2: "WT_code P E e2 = OK T2"
    and bop: "\<not> Predicate.is_empty (WT_binop_i_i_i_i_o P T1 bop T2)"
    and T: "T = Predicate.the (WT_binop_i_i_i_i_o P T1 bop T2)"
    by(auto split: split_if_asm)
  from bop T have "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T"
    apply(auto elim!: not_is_emptyE WT_binop_i_i_i_i_oE simp add: Predicate.the_def)
    apply(rule theI2)
    apply(erule WT_binop_i_i_i_i_oI)
    apply(auto elim: WT_binop_i_i_i_i_oE dest: WT_binop_fun)
    done
  moreover from e1 `ran E \<subseteq> types P` 
  have "P,E \<turnstile> e1 :: T1" by(rule BinOp)
  moreover from e2 `ran E \<subseteq> types P` 
  have "P,E \<turnstile> e2 :: T2" by(rule BinOp)
  ultimately show ?case by auto
next
  case (AAcc a i) thus ?case
    by(clarsimp)(case_tac aa, (fastsimp split: split_if_asm)+)
next
  case (AAss a i e) thus ?case
    by clarsimp(case_tac aa, (fastsimp split: split_if_asm)+)
next
  case (ALen a) thus ?case
    by clarsimp(case_tac aa, (fastsimp split: split_if_asm)+)
next
  case (FAcc e F D)
  from `WT_code P E (e\<bullet>F{D}) = OK T`
  obtain C fm where e: "WT_code P E e = OK (Class C)"
    and sees: "\<not> Predicate.is_empty (sees_field_i_i_i_o_o_i P C F D)"
    and T: "T = fst (Predicate.the (sees_field_i_i_i_o_o_i P C F D))"
    by clarsimp(case_tac a, auto split: split_if_asm)
  from sees T have "P \<turnstile> C sees F:T (snd (Predicate.the (sees_field_i_i_i_o_o_i P C F D))) in D"
    apply(auto elim!: not_is_emptyE sees_field_i_i_i_o_o_iE simp add: Predicate.the_def)
    apply(rule theI2)
    apply(erule sees_field_i_i_i_o_o_iI)
    apply(auto elim: sees_field_i_i_i_o_o_iE dest: sees_field_fun)
    done
  moreover from e `ran E \<subseteq> types P`
  have "P,E \<turnstile> e :: Class C" by(rule FAcc)
  ultimately show ?case by auto
next
  case (FAss e F D e')
  from `WT_code P E (e\<bullet>F{D} := e') = OK T`
  obtain C T2 where e: "WT_code P E e = OK (Class C)"
    and e': "WT_code P E e' = OK T2"
    and sees: "\<not> Predicate.is_empty (sees_field_i_i_i_o_o_i P C F D)"
    and sub: "P \<turnstile> T2 \<le> fst (Predicate.the (sees_field_i_i_i_o_o_i P C F D))"
    and T: "T = Void" by(clarsimp)(case_tac a, auto split: split_if_asm)
  from sees have "P \<turnstile> C sees F:fst (Predicate.the (sees_field_i_i_i_o_o_i P C F D)) (snd (Predicate.the (sees_field_i_i_i_o_o_i P C F D))) in D"
    apply(auto elim!: not_is_emptyE sees_field_i_i_i_o_o_iE simp add: Predicate.the_def)
    apply(rule theI2)
    apply(erule sees_field_i_i_i_o_o_iI)
    apply(auto elim: sees_field_i_i_i_o_o_iE dest: sees_field_fun)
    done
  moreover from e `ran E \<subseteq> types P` have "P,E \<turnstile> e :: Class C" by(rule FAss)
  moreover from e' `ran E \<subseteq> types P` have "P,E \<turnstile> e' :: T2" by(rule FAss)
  ultimately show ?case using sub T by fastsimp
next
  case (Call e M es)
  note WT_code = `WT_code P E (e\<bullet>M(es)) = OK T`
  then obtain T1 Ts where e: "WT_code P E e = OK T1"
    and es: "WTs_code P E es = OK Ts" by(auto)
  from e `ran E \<subseteq> types P` have wte: "P,E \<turnstile> e :: T1" by(rule Call)
  from es `ran E \<subseteq> types P` have wtes: "P,E \<turnstile> es [::] Ts" by(rule Call)
  show ?case
  proof(cases "Predicate.is_empty (external_WT_i_i_i_o_o P T1 M)")
    case True
    with WT_code e es obtain C where T1: "T1 = Class C"
      and nec: "\<not> is_external_call P (Class C) M"
      and sees: "\<not> Predicate.is_empty (Method_i_i_i_o_o_o_o P C M)"
      and sub: "P \<turnstile> Ts [\<le>] fst (Predicate.the (Method_i_i_i_o_o_o_o P C M))"
      and T: "T = fst (snd (Predicate.the (Method_i_i_i_o_o_o_o P C M)))"
      by(cases T1)(auto split: split_if_asm simp: split_beta)
    let ?meth = "fst (snd (snd (Predicate.the (Method_i_i_i_o_o_o_o P C M))))"
    from sees
    have "P \<turnstile> C sees M:fst (Predicate.the (Method_i_i_i_o_o_o_o P C M))\<rightarrow>fst (snd (Predicate.the (Method_i_i_i_o_o_o_o P C M))) = (fst ?meth, snd ?meth) in snd (snd (snd (Predicate.the (Method_i_i_i_o_o_o_o P C M))))"
      apply(auto elim!: not_is_emptyE simp add: Predicate.the_def split_beta)
      apply(rule theI2, assumption)
      apply(auto elim: Method_i_i_i_o_o_o_oE dest: sees_method_fun intro: Method_i_i_i_o_o_o_oI)
      done
    with wte nec show ?thesis using wtes sub unfolding T1 T by(rule WTCall)
  next
    case False
    with WT_code e es have T: "T = snd (Predicate.the (external_WT_i_i_i_o_o P T1 M))"
      and sub: "P \<turnstile> Ts [\<le>] fst (Predicate.the (external_WT_i_i_i_o_o P T1 M))"
      by(auto simp add: split_beta split: split_if_asm)
    from False T have "P \<turnstile> T1\<bullet>M(fst (Predicate.the (external_WT_i_i_i_o_o P T1 M))) :: T"
      apply(auto simp add: Predicate.the_def elim!: not_is_emptyE)
      apply(rule theI2)
      apply(auto elim: external_WT_i_i_i_o_oE dest: external_WT_determ intro: external_WT_i_i_i_o_oI)
      done
    with wte wtes show ?thesis using sub by(rule WTExternal)
  qed
next
  case (Block V U vo e)
  from `WT_code P E {V:U=vo; e} = OK T`
  have e: "WT_code P (E(V \<mapsto> U)) e = OK T"
    and vo: "case vo of None \<Rightarrow> True | Some v \<Rightarrow> case typeof v of None \<Rightarrow> False | Some Tv \<Rightarrow> P \<turnstile> Tv \<le> U"
    and U: "is_type P U" by(auto split: split_if_asm)
  from `ran E \<subseteq> types P` U
  have "ran (E(V \<mapsto> U)) \<subseteq> types P" by(auto simp add: ran_def)
  with e have "P,E(V \<mapsto> U) \<turnstile> e :: T" by(rule Block)
  with U vo show ?case by auto
next
  case (Cond e e1 e2)
  note ran = `ran E \<subseteq> types P`
  from `WT_code P E (if (e) e1 else e2) = OK T`
  obtain T1 T2 where e: "WT_code P E e = OK Boolean"
    and e1: "WT_code P E e1 = OK T1"
    and e2: "WT_code P E e2 = OK T2"
    and sup: "sup P T1 T2 = OK T"
    by(auto split: split_if_asm)
  from e ran have wte: "P,E \<turnstile> e :: Boolean" by(rule Cond)
  moreover from e1 ran have wte1: "P,E \<turnstile> e1 :: T1" by(rule Cond)
  moreover from e2 ran have wte2: "P,E \<turnstile> e2 :: T2" by(rule Cond)
  moreover from wte1 wte2 ran have "is_type P T1" "is_type P T2"
    by(blast intro: WT_is_type[OF wf])+
  hence "P \<turnstile> lub(T1, T2) = T" using sup by(rule sup_is_lubI[OF wf])
  ultimately show ?case ..
next
  case (throw e)
  thus ?case by(clarsimp)(case_tac a, auto split: split_if_asm)
next
  case (TryCatch e C V e')
  from `WT_code P E (try e catch(C V) e') = OK T`
  have e: "WT_code P E e = OK T"
    and e': "WT_code P (E(V \<mapsto> Class C)) e' = OK T"
    and sub: "P \<turnstile> C \<preceq>\<^sup>* Throwable"
    by(simp_all split: split_if_asm)
  from e `ran E \<subseteq> types P`
  have "P,E \<turnstile> e :: T" by(rule TryCatch)
  moreover from wf sub have "is_class P C" by(rule is_class_sub_Throwable)
  with `ran E \<subseteq> types P` have "ran (E(V \<mapsto> Class C)) \<subseteq> types P"
    by(auto simp add: ran_def)
  with e' have "P,E(V \<mapsto> Class C) \<turnstile> e' :: T" by(rule TryCatch)
  ultimately show ?case using sub by auto
qed(auto split: split_if_asm)
*)

lemma assumes wf: "wf_prog wf_md P"
  shows WT_into_WT_code: 
  "\<lbrakk> P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e ::' T"

  and WT_into_WTs_code_OK:
  "\<lbrakk> P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [::'] Ts"
proof(induct rule: WT_WTs.inducts)
  case (WTBlock U E V e' T vo)
  from `is_type P U` `ran E \<subseteq> types P`
  have "ran (E(V \<mapsto> U)) \<subseteq> types P" by(auto simp add: ran_def)
  hence "P,E(V \<mapsto> U) \<turnstile> e' ::' T" by(rule WTBlock)
  with `is_type P U` show ?case
    using `case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> U`
    by(auto intro: WTBlock_code)
next
  case (WTCond E e e1 T1 e2 T2 T)
  from `ran E \<subseteq> types P` have "P,E \<turnstile> e ::' Boolean" "P,E \<turnstile> e1 ::' T1" "P,E \<turnstile> e2 ::' T2"
    by(rule WTCond)+
  moreover from `P,E \<turnstile> e1 :: T1` `P,E \<turnstile> e2 :: T2` `ran E \<subseteq> types P` have "is_type P T1" "is_type P T2"
    by(blast intro: WT_is_type[OF wf])+
  hence "sup P T1 T2 = OK T" using `P \<turnstile> lub(T1, T2) = T` by(rule is_lub_subD[OF wf])
  ultimately show ?case ..
next
  case (WTTry E e1 T V C e2)
  from `ran E \<subseteq> types P` have "P,E \<turnstile> e1 ::' T" by(rule WTTry)
  moreover from `P \<turnstile> C \<preceq>\<^sup>* Throwable` have "is_class P C"
    by(rule is_class_sub_Throwable[OF wf])
  with `ran E \<subseteq> types P` have "ran (E(V \<mapsto> Class C)) \<subseteq> types P"
    by(auto simp add: ran_def)
  hence "P,E(V \<mapsto> Class C) \<turnstile> e2 ::' T" by(rule WTTry)
  ultimately show ?case using `P \<turnstile> C \<preceq>\<^sup>* Throwable` ..
qed(blast intro: WT_code_WTs_code.intros)+

(*
lemma assumes wf: "wf_prog wf_md P"
  shows WT_into_WT_code_OK: 
  "\<lbrakk> P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> WT_code P E e = OK T"

  and WT_into_WTs_code_OK:
  "\<lbrakk> P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> WTs_code P E es = OK Ts"
proof(induct rule: WT_WTs.inducts)
  case (WTBinOp E e1 T1 bop e2 T2 T)
  from `P \<turnstile> T1\<guillemotleft>T2\<guillemotright>e2 :: T`
  have "\<not> Predicate.is_empty (WT_binop_i_i_i_i_o P T1 T2 e2)"
    by(auto dest: is_emptyD intro: WT_binop_i_i_i_i_oI)
  moreover from `P \<turnstile> T1\<guillemotleft>T2\<guillemotright>e2 :: T`
  have "Predicate.the (WT_binop_i_i_i_i_o P T1 T2 e2) = T"
    by(auto simp add: Predicate.the_def intro: WT_binop_i_i_i_i_oI elim: WT_binop_i_i_i_i_oE)
  ultimately show ?case using WTBinOp by simp
next
  case (WTFAcc E e C F T fm D)
  from `P \<turnstile> C sees F:T (fm) in D`
  have "\<not> Predicate.is_empty (sees_field_i_i_i_o_o_i P C F D)"
    by(auto dest: is_emptyD intro: sees_field_i_i_i_o_o_iI)
  moreover from `P \<turnstile> C sees F:T (fm) in D`
  have "Predicate.the (sees_field_i_i_i_o_o_i P C F D) = (T, fm)"
    by(fastsimp simp add: Predicate.the_def intro: sees_field_i_i_i_o_o_iI elim: sees_field_i_i_i_o_o_iE dest: sees_field_fun)
  ultimately show ?case using WTFAcc by simp
next
  case (WTFAss E e1 C F T fm D e2 T2)
  from `P \<turnstile> C sees F:T (fm) in D`
  have "\<not> Predicate.is_empty (sees_field_i_i_i_o_o_i P C F D)"
    by(auto dest: is_emptyD intro: sees_field_i_i_i_o_o_iI)
  moreover from `P \<turnstile> C sees F:T (fm) in D`
  have "Predicate.the (sees_field_i_i_i_o_o_i P C F D) = (T, fm)"
    by(fastsimp simp add: Predicate.the_def intro: sees_field_i_i_i_o_o_iI elim: sees_field_i_i_i_o_o_iE dest: sees_field_fun)
  ultimately show ?case using WTFAss by simp
next
  case (WTCall E e C M Ts T pns body D es Ts')
  from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have "\<not> Predicate.is_empty (Method_i_i_i_o_o_o_o P C M)"
    by(auto dest: is_emptyD intro: Method_i_i_i_o_o_o_oI)
  moreover from `P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D`
  have "Predicate.the (Method_i_i_i_o_o_o_o P C M) = (Ts, T, (pns, body), D)"
    by(auto simp add: Predicate.the_def intro: Method_i_i_i_o_o_o_oI elim!: Method_i_i_i_o_o_o_oE dest: sees_method_fun)
  moreover have "Predicate.is_empty (external_WT_i_i_i_o_o P (Class C) M)"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    thus False using `\<not> is_external_call P (Class C) M`
      by(auto elim!: not_is_emptyE external_WT_i_i_i_o_oE dest: external_WT_is_external_call)
  qed
  ultimately show ?case using WTCall by(simp)
next
  case (WTExternal E e T es Ts M Us U)
  from `P \<turnstile> T\<bullet>M(Us) :: U`
  have "\<not> Predicate.is_empty (external_WT_i_i_i_o_o P T M)"
    by(auto dest: is_emptyD intro: external_WT_i_i_i_o_oI)
  moreover from `P \<turnstile> T\<bullet>M(Us) :: U`
  have "Predicate.the (external_WT_i_i_i_o_o P T M) = (Us, U)"
    by(auto simp add: Predicate.the_def intro: external_WT_i_i_i_o_oI elim!: external_WT_i_i_i_o_oE dest: external_WT_determ)
  ultimately show ?case using WTExternal by simp
next
  case (WTBlock T E V e U vo)
  from `is_type P T` `ran E \<subseteq> types P`
  have "ran (E(V \<mapsto> T)) \<subseteq> types P" by(auto simp add: ran_def)
  thus ?case using WTBlock by(auto simp add: fun_upd_def)
next
  case (WTCond E e e1 T1 e2 T2 T)
  from wf `P,E \<turnstile> e1 :: T1` `ran E \<subseteq> types P`
  have "is_type P T1" by(rule WT_is_type)
  moreover from wf `P,E \<turnstile> e2 :: T2` `ran E \<subseteq> types P`
  have "is_type P T2" by(rule WT_is_type)
  ultimately have "SemiType.sup P T1 T2 = OK T"
    using `P \<turnstile> lub(T1, T2) = T` by(rule is_lub_subD[OF wf])
  thus ?case using WTCond by simp
next
  case (WTTry E e1 T V C e2)
  from wf `P \<turnstile> C \<preceq>\<^sup>* Throwable` have "is_class P C"
    by(rule is_class_sub_Throwable)
  with `ran E \<subseteq> types P` have "ran (E(V \<mapsto> Class C)) \<subseteq> types P"
    by(auto simp add: ran_def)
  with WTTry show ?case by(simp add: fun_upd_def)
qed simp_all
*)

theorem WT_eq_WT_code:
  assumes "wf_prog wf_md P"
  and "ran E \<subseteq> types P"
  shows "P,E \<turnstile> e :: T \<longleftrightarrow> P,E \<turnstile> e ::' T"
using assms by(blast intro: WT_code_into_WT WT_into_WT_code)
(*
theorem WT_eq_WT_code:
  assumes "wf_prog wf_md P"
  and "ran E \<subseteq> types P"
  shows "P,E \<turnstile> e :: T \<longleftrightarrow> WT_code P E e = OK T"
using assms by(blast intro: WT_code_OK_into_WT WT_into_WT_code_OK)
*)
end