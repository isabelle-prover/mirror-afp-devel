section\<open>Accounts\<close>
theory Accounts
imports Valuetypes
begin

type_synonym Balance = Valuetype
type_synonym Identifier = String.literal

(*
Contract None means not initialized yet
*)
datatype atype =
    EOA
  | Contract Identifier

record account =
  bal :: Balance
  type :: "atype option"
  contracts :: nat

lemma bind_case_atype_cong [fundef_cong]:
  assumes "x = x'"
      and "x = EOA \<Longrightarrow> f s = f' s"
      and "\<And>a. x = Contract a \<Longrightarrow> g a s = g' a s"
    shows "(case x of EOA \<Rightarrow> f | Contract a \<Rightarrow> g a) s
         = (case x' of EOA \<Rightarrow> f' | Contract a \<Rightarrow> g' a) s"
  using assms by (cases x, auto)

definition emptyAcc :: account
  where "emptyAcc = \<lparr>bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, type = None, contracts = 0\<rparr>"

declare emptyAcc_def [solidity_symbex]

type_synonym Accounts = "Address \<Rightarrow> account"

definition emptyAccount :: "Accounts"
where
  "emptyAccount _ = emptyAcc"

declare emptyAccount_def [solidity_symbex]

definition addBalance :: "Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
where
  "addBalance ad val acc =
    (if ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0
      then (let v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val
         in if (v < 2^256)
           then Some (acc(ad := acc ad \<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>))
           else None)
      else None)"

declare addBalance_def [solidity_symbex]

lemma addBalance_val1:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
using assms unfolding addBalance_def by (simp add:Let_def split:if_split_asm)

lemma addBalance_val2:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256"
using assms unfolding addBalance_def by (simp add:Let_def split:if_split_asm)

lemma addBalance_limit:
  assumes "addBalance ad val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) < 2 ^ 256"
proof
  fix ad'
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) < 2 ^ 256"
  proof (cases "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0")
    case t1: True
    define v where v_def: "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
    with assms(2) have "v \<ge>0" by (simp add: t1)
    then show ?thesis
    proof (cases "v < 2^256")
      case t2: True
      with t1 v_def have "addBalance ad val acc = Some (acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>))" unfolding addBalance_def by simp
      with t2 `v \<ge>0` show ?thesis using assms Read_ShowL_id by auto
    next
      case False
      with t1 v_def show ?thesis using assms(1) unfolding addBalance_def by simp
    qed
  next
    case False
    then show ?thesis using assms(1) unfolding addBalance_def by simp
  qed
qed

lemma addBalance_add:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding addBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma addBalance_mono:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad))"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding addBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms unfolding addBalance_def by (simp split:if_split_asm)
qed

lemma addBalance_eq:
  assumes "addBalance ad val acc = Some acc'"
      and "ad \<noteq> ad'"
    shows "bal (acc ad') = bal (acc' ad')"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding addBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

definition subBalance :: "Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
  where
  "subBalance ad val acc =
    (if ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0
      then (let v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val
         in if (v \<ge> 0)
           then Some (acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>))
           else None)
      else None)"

declare subBalance_def [solidity_symbex]

lemma subBalance_val1:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
using assms unfolding subBalance_def by (simp split:if_split_asm)

lemma subBalance_val2:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
using assms unfolding subBalance_def by (simp split:if_split_asm)

lemma subBalance_sub:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding subBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma subBalance_limit:
  assumes "subBalance ad val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) < 2 ^ 256"
proof
  fix ad'
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) < 2 ^ 256"
  proof (cases "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0")
    case t1: True
    define v where v_def: "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
    with assms(2) t1 have "v < 2 ^ 256" by (smt (verit))
    then show ?thesis
    proof (cases "v \<ge> 0")
      case t2: True
      with t1 v_def have "subBalance ad val acc = Some (acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>))" unfolding subBalance_def by simp
      with t2 `v < 2 ^ 256` show ?thesis using assms Read_ShowL_id by auto
    next
      case False
      with t1 v_def show ?thesis using assms(1) unfolding subBalance_def by simp
    qed
  next
    case False
    then show ?thesis using assms(1) unfolding subBalance_def by simp
  qed
qed

lemma subBalance_mono:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad))"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding subBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms unfolding subBalance_def by (simp split:if_split_asm)
qed

lemma subBalance_eq:
  assumes "subBalance ad val acc = Some acc'"
      and "ad \<noteq> ad'"
    shows "(bal (acc ad')) = (bal (acc' ad'))"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = acc(ad := acc ad\<lparr>bal:=ShowL\<^sub>i\<^sub>n\<^sub>t v\<rparr>)" unfolding subBalance_def by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

definition transfer :: "Address \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
where
  "transfer ads addr val acc =
    (case subBalance ads val acc of
      Some acc' \<Rightarrow> addBalance addr val acc'
    | None \<Rightarrow> None)"

declare transfer_def [solidity_symbex]

lemma transfer_val1:
  assumes "transfer ads addr val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)
  then show "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0" using subBalance_val1[OF *] by simp
qed

lemma transfer_val2:
  assumes "transfer ads addr val acc = Some acc'"
      and "ads \<noteq> addr"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256" using addBalance_val2[OF **] by simp
  with * show ?thesis using assms(2) subBalance_eq[OF *] by simp
qed

lemma transfer_val3:
  assumes "transfer ads addr val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
using assms by (auto simp add: Let_def subBalance_def transfer_def split:if_split_asm)

lemma transfer_add:
  assumes "transfer ads addr val acc = Some acc'"
      and "addr \<noteq> ads"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' addr)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  with assms(2) have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr))" using subBalance_eq[OF *] by simp
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' addr)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id by simp
qed

lemma transfer_sub:
  assumes "transfer ads addr val acc = Some acc'"
      and "addr \<noteq> ads"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val" using subBalance_sub[OF *] by simp
  moreover from assms(2) have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ads))" using addBalance_eq[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id by simp
qed

lemma transfer_same:
  assumes "transfer ad ad' val acc = Some acc'"
      and "ad = ad'"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad))"
proof -
  from assms obtain acc'' where *: "subBalance ad val acc = Some acc''" by (simp add: subBalance_def transfer_def split:if_split_asm)
  with assms have **: "addBalance ad val acc'' = Some acc'" by (simp add: transfer_def split:if_split_asm)
  moreover from * have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val" using subBalance_sub by simp
  moreover from ** have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) = ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add by simp
  ultimately show ?thesis by simp
qed

lemma transfer_mono:
  assumes "transfer ads addr val acc = Some acc'"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' addr)) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr))"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  show ?thesis
  proof (cases "addr = ads")
    case True
    with * have "acc'' = acc(addr:=acc addr\<lparr>bal := ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)\<rparr>)" by (simp add:Let_def subBalance_def split: if_split_asm)
    moreover from ** have "acc'=acc''(addr:=acc'' addr\<lparr>bal := ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)\<rparr>)" unfolding addBalance_def by (simp add:Let_def split: if_split_asm)
    ultimately show ?thesis using Read_ShowL_id by auto
  next
    case False
    then have "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc addr)) \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc'' addr))" using subBalance_eq[OF *] by simp
    also have "\<dots> \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' addr))" using addBalance_mono[OF **] by simp
    finally show ?thesis .
  qed
qed

lemma transfer_eq:
  assumes "transfer ads addr val acc = Some acc'"
      and "ad \<noteq> ads"
      and "ad \<noteq> addr"
    shows "bal (acc' ad) = bal (acc ad)"
using assms by (auto simp add: Let_def addBalance_def subBalance_def transfer_def split:if_split_asm)

lemma transfer_limit:
  assumes "transfer ads addr val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc ad)) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad)) < 2 ^ 256"
proof
  fix ad'
  from assms(1) obtain acc'' where "subBalance ads val acc = Some acc''" and "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split: if_split_asm)
  with subBalance_limit[OF _ assms(2)]
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (bal (acc' ad')) < 2 ^ 256"
    using addBalance_limit by presburger
qed

lemma transfer_type_same:
  assumes "transfer ads addr val acc = Some acc'"
    shows "type (acc' ad) = type (acc ad)"
using assms by (auto simp add: Let_def addBalance_def subBalance_def transfer_def split:if_split_asm)

lemma transfer_contracts_same:
  assumes "transfer ads addr val acc = Some acc'"
    shows "contracts (acc' ad) = contracts (acc ad)"
using assms by (auto simp add: Let_def addBalance_def subBalance_def transfer_def split:if_split_asm)


end