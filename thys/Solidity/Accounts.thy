section\<open>Accounts\<close>
theory Accounts
imports Valuetypes
begin

type_synonym Balance = Valuetype
 
type_synonym Accounts = "Address \<Rightarrow> Balance"

fun emptyAccount :: "Accounts"
where
  "emptyAccount _ = ShowL\<^sub>i\<^sub>n\<^sub>t 0"

fun accessBalance :: "Accounts \<Rightarrow> Address \<Rightarrow> Balance"
where
  "accessBalance acc ad = acc ad"

fun updateBalance :: "Address \<Rightarrow> Balance \<Rightarrow> Accounts \<Rightarrow> Accounts"
where
  "updateBalance ad bal acc = (\<lambda>i. (if i = ad then bal else acc i))"

fun addBalance :: "Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
where
  "addBalance ad val acc =
    (if ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0
      then (let v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val
         in if (v < 2^256)
           then Some (updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc)
           else None)
      else None)"

lemma addBalance_val:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256"
using assms by (simp add:Let_def split:if_split_asm)

lemma addBalance_limit:
  assumes "addBalance ad val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) < 2 ^ 256"
proof
  fix ad'
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') < 2 ^ 256"
  proof (cases "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0")
    case t1: True
    define v where v_def: "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
    with assms(2) have "v \<ge>0" by (simp add: t1)
    then show ?thesis
    proof (cases "v < 2^256")
      case t2: True
      with t1 v_def have "addBalance ad val acc = Some (updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc)" by simp
      with t2 `v \<ge>0` show ?thesis using assms Read_ShowL_id by auto
    next
      case False
      with t1 v_def show ?thesis using assms(1) by simp
    qed
  next
    case False
    then show ?thesis using assms(1) by simp
  qed
qed

lemma addBalance_add:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma addBalance_mono:
  assumes "addBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad)"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma addBalance_eq:
  assumes "addBalance ad val acc = Some acc'"
      and "ad \<noteq> ad'"
    shows "(accessBalance acc ad') = (accessBalance acc' ad')"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

fun subBalance :: "Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
  where
  "subBalance ad val acc =
    (if ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0
      then (let v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val
         in if (v \<ge> 0)
           then Some (updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc)
           else None)
      else None)"

lemma subBalance_val:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
using assms by (simp split:if_split_asm)

lemma subBalance_sub:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma subBalance_limit:
  assumes "subBalance ad val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) < 2 ^ 256"
proof
  fix ad'
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') < 2 ^ 256"
  proof (cases "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0")
    case t1: True
    define v where v_def: "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
    with assms(2) t1 have "v < 2 ^ 256" by (smt (verit))
    then show ?thesis
    proof (cases "v \<ge> 0")
      case t2: True
      with t1 v_def have "subBalance ad val acc = Some (updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc)" by simp
      with t2 `v < 2 ^ 256` show ?thesis using assms Read_ShowL_id by auto
    next
      case False
      with t1 v_def show ?thesis using assms(1) by simp
    qed
  next
    case False
    then show ?thesis using assms(1) by simp
  qed
qed

lemma subBalance_mono:
  assumes "subBalance ad val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad)"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

lemma subBalance_eq:
  assumes "subBalance ad val acc = Some acc'"
      and "ad \<noteq> ad'"
    shows "(accessBalance acc ad') = (accessBalance acc' ad')"
proof -
  define v where "v = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
  with assms have "acc' = updateBalance ad (ShowL\<^sub>i\<^sub>n\<^sub>t v) acc" by (simp add:Let_def split:if_split_asm)
  thus ?thesis using v_def Read_ShowL_id assms by (simp split:if_split_asm)
qed

fun transfer :: "Address \<Rightarrow> Address \<Rightarrow> Valuetype \<Rightarrow> Accounts \<Rightarrow> Accounts option"
where
  "transfer ads addr val acc =
    (case subBalance ads val acc of
      Some acc' \<Rightarrow> addBalance addr val acc'
    | None \<Rightarrow> None)"

lemma transfer_val1:
  assumes "transfer ads addr val acc = Some acc'"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)
  then show "ReadL\<^sub>i\<^sub>n\<^sub>t val \<ge> 0" using subBalance_val[OF *] by simp
qed

lemma transfer_val2:
  assumes "transfer ads addr val acc = Some acc'"
      and "ads \<noteq> addr"
    shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)

  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' addr) + ReadL\<^sub>i\<^sub>n\<^sub>t val < 2^256" using addBalance_val[OF **] by simp
  with * show ?thesis using assms(2) subBalance_eq[OF *] by simp
qed

lemma transfer_add:
  assumes "transfer ads addr val acc = Some acc'"
      and "addr \<noteq> ads"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' addr) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr) + ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)

  with assms(2) have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' addr)" using subBalance_eq[OF *] by simp
  moreover have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' addr) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' addr) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id by simp
qed

lemma transfer_sub:
  assumes "transfer ads addr val acc = Some acc'"
      and "addr \<noteq> ads"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ads) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ads) - ReadL\<^sub>i\<^sub>n\<^sub>t val"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)

  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' ads) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ads) - ReadL\<^sub>i\<^sub>n\<^sub>t val" using subBalance_sub[OF *] by simp
  moreover from assms(2) have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ads) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' ads)" using addBalance_eq[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id by simp
qed

lemma transfer_mono:
  assumes "transfer ads addr val acc = Some acc'"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' addr) \<ge> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)

  show ?thesis
  proof (cases "addr = ads")
    case True
    with * have "acc'' = updateBalance addr (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr) - ReadL\<^sub>i\<^sub>n\<^sub>t val)) acc" by (simp add:Let_def split: if_split_asm)
    moreover from ** have "acc'=updateBalance addr (ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' addr) + ReadL\<^sub>i\<^sub>n\<^sub>t val)) acc''" by (simp add:Let_def split: if_split_asm)
    ultimately show ?thesis using Read_ShowL_id by auto
  next
    case False
    then have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc addr) \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' addr)" using subBalance_eq[OF *] by simp
    also have "\<dots> \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' addr)" using addBalance_mono[OF **] by simp
    finally show ?thesis .
  qed
qed

lemma transfer_eq:
  assumes "transfer ads addr val acc = Some acc'"
      and "ad \<noteq> ads"
      and "ad \<noteq> addr"
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp split:if_split_asm)

  from assms(3) have "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc'' ad)" using addBalance_eq[OF **] by simp
  also from assms(2) have "\<dots> = ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad)" using subBalance_eq[OF *] by simp
  finally show ?thesis .
qed

lemma transfer_limit:
  assumes "transfer ads addr val acc = Some acc'"
     and "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc ad) < 2 ^ 256"
   shows "\<forall>ad. ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad) < 2 ^ 256"
proof
  fix ad'
  from assms(1) obtain acc'' where "subBalance ads val acc = Some acc''" and "addBalance addr val acc'' = Some acc'" by (simp split: if_split_asm)
  with subBalance_limit[OF _ assms(2)]
  show "ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (accessBalance acc' ad') < 2 ^ 256"
    using addBalance_limit by presburger
qed

end