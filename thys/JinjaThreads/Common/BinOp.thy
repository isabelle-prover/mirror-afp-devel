(*  Title:      JinjaThreads/Common/BinOp.thy
    Author:     Andreas Lochbihler
*)

header{* \isaheader{ Binary Operators } *}

theory BinOp imports Conform begin

datatype bop =  -- "names of binary operations"
    Eq
  | NotEq
  | LessThan
  | LessOrEqual
  | GreaterThan
  | GreaterOrEqual
  | Add    
  | Subtract
  | Mult
  | Div
  | Mod
  | BinAnd
  | BinOr
  | BinXor
  | ShiftLeft
  | ShiftRightZeros
  | ShiftRightSigned

section{* The semantics of binary operators *}

fun binop_LessThan :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_LessThan (Intg i1) (Intg i2) = Some (Bool (i1 <s i2))"
| "binop_LessThan v1 v2 = None"

fun binop_LessOrEqual :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_LessOrEqual (Intg i1) (Intg i2) = Some (Bool (i1 <=s i2))"
| "binop_LessOrEqual v1 v2 = None"

fun binop_GreaterThan :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_GreaterThan (Intg i1) (Intg i2) = Some (Bool (i2 <s i1))"
| "binop_GreaterThan v1 v2 = None"

fun binop_GreaterOrEqual :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_GreaterOrEqual (Intg i1) (Intg i2) = Some (Bool (i2 <=s i1))"
| "binop_GreaterOrEqual v1 v2 = None"

fun binop_Add :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_Add (Intg i1) (Intg i2) = Some (Intg (i1 + i2))"
| "binop_Add v1 v2 = None"

fun binop_Subtract :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_Subtract (Intg i1) (Intg i2) = Some (Intg (i1 - i2))"
| "binop_Subtract v1 v2 = None"

fun binop_Mult :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_Mult (Intg i1) (Intg i2) = Some (Intg (i1 * i2))"
| "binop_Mult v1 v2 = None"

fun binop_Mod :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_Mod (Intg i1) (Intg i2) = Some (Intg (i1 mod i2))"
| "binop_Mod v1 v2 = None"

fun binop_Div :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_Div (Intg i1) (Intg i2) = Some (Intg (i1 div i2))"
| "binop_Div v1 v2 = None"

fun binop_BinAnd :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_BinAnd (Intg i1) (Intg i2) = Some (Intg (i1 AND i2))"
| "binop_BinAnd (Bool b1) (Bool b2) = Some (Bool (b1 \<and> b2))"
| "binop_BinAnd v1 v2 = None"

fun binop_BinOr :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_BinOr (Intg i1) (Intg i2) = Some (Intg (i1 OR i2))"
| "binop_BinOr (Bool b1) (Bool b2) = Some (Bool (b1 \<or> b2))"
| "binop_BinOr v1 v2 = None"

fun binop_BinXor :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_BinXor (Intg i1) (Intg i2) = Some (Intg (i1 XOR i2))"
| "binop_BinXor (Bool b1) (Bool b2) = Some (Bool (b1 \<noteq> b2))"
| "binop_BinXor v1 v2 = None"

fun binop_ShiftLeft :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_ShiftLeft (Intg i1) (Intg i2) = Some (Intg (i1 << unat (i2 AND 0x1f)))"
| "binop_ShiftLeft v1 v2 = None"

fun binop_ShiftRightZeros :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_ShiftRightZeros (Intg i1) (Intg i2) = Some (Intg (i1 >> unat (i2 AND 0x1f)))"
| "binop_ShiftRightZeros v1 v2 = None"

fun binop_ShiftRightSigned :: "val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop_ShiftRightSigned (Intg i1) (Intg i2) = Some (Intg (i1 >>> unat (i2 AND 0x1f)))"
| "binop_ShiftRightSigned v1 v2 = None"

primrec binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop Eq v1 v2 =  Some (Bool (v1 = v2))"
| "binop NotEq v1 v2 = Some (Bool (v1 \<noteq> v2))"
| "binop LessThan = binop_LessThan"
| "binop LessOrEqual = binop_LessOrEqual"
| "binop GreaterThan = binop_GreaterThan"
| "binop GreaterOrEqual = binop_GreaterOrEqual"
| "binop Add = binop_Add"
| "binop Subtract = binop_Subtract"
| "binop Mult = binop_Mult"
| "binop Mod = binop_Mod"
| "binop Div = binop_Div"
| "binop BinAnd = binop_BinAnd"
| "binop BinOr = binop_BinOr"
| "binop BinXor = binop_BinXor"
| "binop ShiftLeft = binop_ShiftLeft"
| "binop ShiftRightZeros = binop_ShiftRightZeros"
| "binop ShiftRightSigned = binop_ShiftRightSigned"

lemma [simp]:
  "(binop_LessThan v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 <s i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop_LessOrEqual v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 <=s i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop_GreaterThan v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i2 <s i1))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop_GreaterOrEqual v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i2 <=s i1))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop_Add v\<^isub>1 v\<^isub>2  = Some v) = (\<exists>i\<^isub>1 i\<^isub>2. v\<^isub>1 = Intg i\<^isub>1 \<and> v\<^isub>2 = Intg i\<^isub>2 \<and> v = Intg(i\<^isub>1+i\<^isub>2))"
(*<*)
apply(cases v\<^isub>1)
apply auto
apply(cases v\<^isub>2)
apply auto
done
(*>*)

lemma [simp]:
  "(binop_Subtract v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 - i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop_Mult v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 * i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop_Mod v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 mod i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop_Div v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 div i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop_BinAnd v1 v2 = Some v) \<longleftrightarrow> 
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<and> b2)) \<or> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 AND i2))"
by(cases v1, simp_all)(case_tac [!] v2, auto)

lemma [simp]:
  "(binop_BinOr v1 v2 = Some v) \<longleftrightarrow> 
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<or> b2)) \<or>
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 OR i2))"
by(cases v1, simp_all)(case_tac [!] v2, auto)

lemma [simp]:
  "(binop_BinXor v1 v2 = Some v) \<longleftrightarrow>
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<noteq> b2)) \<or>
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 XOR i2))"
by(cases v1, simp_all)(case_tac [!] v2, auto)

lemma [simp]:
  "(binop_ShiftLeft v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 << unat (i2 AND 0x1f)))"
by(cases v1, auto)(cases v2, auto)

lemma [simp]:
  "(binop_ShiftRightZeros v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 >> unat (i2 AND 0x1f)))"
by(cases v1, auto)(cases v2, auto)

lemma [simp]:
  "(binop_ShiftRightSigned v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg (i1 >>> unat (i2 AND 0x1f)))"
by(cases v1, auto)(cases v2, auto)

section {* Typing for binary operators *}

inductive WT_binop :: "'m prog \<Rightarrow> ty \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _\<guillemotleft>_\<guillemotright>_ :: _" [51,0,0,0,51] 50)
where
  WT_binop_Eq:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: Boolean"

| WT_binop_NotEq:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: Boolean"

| WT_binop_LessThan:
  "P \<turnstile> Integer\<guillemotleft>LessThan\<guillemotright>Integer :: Boolean"

| WT_binop_LessOrEqual:
  "P \<turnstile> Integer\<guillemotleft>LessOrEqual\<guillemotright>Integer :: Boolean"

| WT_binop_GreaterThan:
  "P \<turnstile> Integer\<guillemotleft>GreaterThan\<guillemotright>Integer :: Boolean"

| WT_binop_GreaterOrEqual:
  "P \<turnstile> Integer\<guillemotleft>GreaterOrEqual\<guillemotright>Integer :: Boolean"

| WT_binop_Add:
  "P \<turnstile> Integer\<guillemotleft>Add\<guillemotright>Integer :: Integer"

| WT_binop_Subtract:
  "P \<turnstile> Integer\<guillemotleft>Subtract\<guillemotright>Integer :: Integer"

| WT_binop_Mult:
  "P \<turnstile> Integer\<guillemotleft>Mult\<guillemotright>Integer :: Integer"

| WT_binop_Div:
  "P \<turnstile> Integer\<guillemotleft>Div\<guillemotright>Integer :: Integer"

| WT_binop_Mod:
  "P \<turnstile> Integer\<guillemotleft>Mod\<guillemotright>Integer :: Integer"

| WT_binop_BinAnd_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinAnd\<guillemotright>Boolean :: Boolean"

| WT_binop_BinAnd_Int:
  "P \<turnstile> Integer\<guillemotleft>BinAnd\<guillemotright>Integer :: Integer"

| WT_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean :: Boolean"

| WT_binop_BinOr_Int:
  "P \<turnstile> Integer\<guillemotleft>BinOr\<guillemotright>Integer :: Integer"

| WT_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean :: Boolean"

| WT_binop_BinXor_Int:
  "P \<turnstile> Integer\<guillemotleft>BinXor\<guillemotright>Integer :: Integer"

| WT_binop_ShiftLeft:
  "P \<turnstile> Integer\<guillemotleft>ShiftLeft\<guillemotright>Integer :: Integer"

| WT_binop_ShiftRightZeros:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightZeros\<guillemotright>Integer :: Integer"

| WT_binop_ShiftRightSigned:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightSigned\<guillemotright>Integer :: Integer"

lemma WT_binopI [intro]:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: Boolean"
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Mod \<or> bop = Div \<or> bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<or> 
   bop = ShiftLeft \<or> bop = ShiftRightZeros \<or> bop = ShiftRightSigned
   \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer :: Integer"
  "bop = LessThan \<or> bop = LessOrEqual \<or> bop = GreaterThan \<or> bop = GreaterOrEqual \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer :: Boolean"
  "bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<Longrightarrow> P \<turnstile> Boolean\<guillemotleft>bop\<guillemotright>Boolean :: Boolean"
by(auto intro: WT_binop.intros)

inductive_cases [elim]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>LessThan\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>LessOrEqual\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>GreaterThan\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>GreaterOrEqual\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Add\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Subtract\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Mult\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Div\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Mod\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinAnd\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinOr\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinXOr\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftLeft\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightZeros\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightSigned\<guillemotright>T2 :: T"

lemma WT_binop_fun: "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T' \<rbrakk> \<Longrightarrow> T = T'"
by(cases bop)(auto)

lemma WT_binop_is_type:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T"
by(cases bop) auto

inductive WTrt_binop :: "'m prog \<Rightarrow> ty \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _\<guillemotleft>_\<guillemotright>_ : _" [51,0,0,0,51] 50)
where
  WTrt_binop_Eq:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : Boolean"

| WTrt_binop_NotEq:
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : Boolean"

| WTrt_binop_LessThan:
  "P \<turnstile> Integer\<guillemotleft>LessThan\<guillemotright>Integer : Boolean"

| WTrt_binop_LessOrEqual:
  "P \<turnstile> Integer\<guillemotleft>LessOrEqual\<guillemotright>Integer : Boolean"

| WTrt_binop_GreaterThan:
  "P \<turnstile> Integer\<guillemotleft>GreaterThan\<guillemotright>Integer : Boolean"

| WTrt_binop_GreaterOrEqual:
  "P \<turnstile> Integer\<guillemotleft>GreaterOrEqual\<guillemotright>Integer : Boolean"

| WTrt_binop_Add:
  "P \<turnstile> Integer\<guillemotleft>Add\<guillemotright>Integer : Integer"

| WTrt_binop_Subtract:
  "P \<turnstile> Integer\<guillemotleft>Subtract\<guillemotright>Integer : Integer"

| WTrt_binop_Mult:
  "P \<turnstile> Integer\<guillemotleft>Mult\<guillemotright>Integer : Integer"

| WTrt_binop_Div:
  "P \<turnstile> Integer\<guillemotleft>Div\<guillemotright>Integer : Integer"

| WTrt_binop_Mod:
  "P \<turnstile> Integer\<guillemotleft>Mod\<guillemotright>Integer : Integer"

| WTrt_binop_BinAnd_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinAnd\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinAnd_Int:
  "P \<turnstile> Integer\<guillemotleft>BinAnd\<guillemotright>Integer : Integer"

| WTrt_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinOr_Int:
  "P \<turnstile> Integer\<guillemotleft>BinOr\<guillemotright>Integer : Integer"

| WTrt_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinXor_Int:
  "P \<turnstile> Integer\<guillemotleft>BinXor\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftLeft:
  "P \<turnstile> Integer\<guillemotleft>ShiftLeft\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftRightZeros:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightZeros\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftRightSigned:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightSigned\<guillemotright>Integer : Integer"

lemma WTrt_binopI [intro]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : Boolean"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Div \<or> bop = Mod \<or> bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<or>
   bop = ShiftLeft \<or> bop = ShiftRightZeros \<or> bop = ShiftRightSigned
   \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer : Integer"
  "bop = LessThan \<or> bop = LessOrEqual \<or> bop = GreaterThan \<or> bop = GreaterOrEqual \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer : Boolean"
  "bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<Longrightarrow> P \<turnstile> Boolean\<guillemotleft>bop\<guillemotright>Boolean : Boolean"
by(auto intro: WTrt_binop.intros)

inductive_cases WTrt_binop_cases [elim]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Add\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Subtract\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mult\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Div\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mod\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinAnd\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinOr\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinXOr\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftLeft\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightZeros\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightSigned\<guillemotright>T2 : T"

lemma WT_binop_WTrt_binop:
  "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<Longrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(auto elim: WT_binop.cases)

lemma (in heap) binop_progress:
  "\<lbrakk> typeof\<^bsub>h\<^esub> v1 = \<lfloor>T1\<rfloor>; typeof\<^bsub>h\<^esub> v2 = \<lfloor>T2\<rfloor>; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<rbrakk>
  \<Longrightarrow> \<exists>v. binop bop v1 v2 = \<lfloor>v\<rfloor> \<and> P,h \<turnstile> v :\<le> T"
by(cases bop)(auto elim!: WTrt_binop_cases)

lemma WTrt_binop_fun: "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T' \<rbrakk> \<Longrightarrow> T = T'"
by(cases bop)(auto)

lemma WTrt_binop_THE [simp]: "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<Longrightarrow> The (WTrt_binop P T1 bop T2) = T"
by(auto dest: WTrt_binop_fun)

lemma WTrt_binop_widen_mono:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; P \<turnstile> T1' \<le> T1; P \<turnstile> T2' \<le> T2 \<rbrakk> \<Longrightarrow> \<exists>T'. P \<turnstile> T1'\<guillemotleft>bop\<guillemotright>T2' : T' \<and> P \<turnstile> T' \<le> T"
by(cases bop)(auto elim!: WTrt_binop_cases)

lemma WTrt_binop_is_type:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T"
by(cases bop) auto

subsection {* Code generator setup *}

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  WT_binop 
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  WTrt_binop 
.

lemma eval_WTrt_binop_i_i_i_i_o:
  "Predicate.eval (WTrt_binop_i_i_i_i_o P T1 bop T2) T \<longleftrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(auto elim: WTrt_binop_i_i_i_i_oE intro: WTrt_binop_i_i_i_i_oI)

lemma the_WTrt_binop_code:
  "(THE T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T) = Predicate.the (WTrt_binop_i_i_i_i_o P T1 bop T2)"
by(simp add: Predicate.the_def eval_WTrt_binop_i_i_i_i_o)

end