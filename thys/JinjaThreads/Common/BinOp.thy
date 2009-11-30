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

section{* The semantics of binary operators *}

fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where
  "binop Eq v1 v2 = Some (Bool (v1 = v2))"
| "binop NotEq v1 v2 = Some (Bool (v1 \<noteq> v2))"
| "binop LessThan (Intg i1) (Intg i2) = Some (Bool (i1 < i2))"
| "binop LessOrEqual (Intg i1) (Intg i2) = Some (Bool (i1 \<le> i2))"
| "binop GreaterThan (Intg i1) (Intg i2) = Some (Bool (i1 > i2))"
| "binop GreaterOrEqual (Intg i1) (Intg i2) = Some (Bool (i1 \<ge> i2))"
| "binop Add (Intg i1) (Intg i2) = Some (Intg (i1 + i2))"
| "binop Subtract (Intg i1) (Intg i2) = Some (Intg (i1 - i2))"
| "binop Mult (Intg i1) (Intg i2) = Some (Intg (i1 * i2))"
| "binop Mod (Intg i1) (Intg i2) = Some (Intg (i1 mod i2))"
| "binop Div (Intg i1) (Intg i2) = Some (Intg (i1 div i2))"
| "binop BinAnd (Bool v1) (Bool v2) = Some (Bool (v1 \<and> v2))"
| "binop BinOr (Bool v1) (Bool v2) = Some (Bool (v1 \<or> v2))"
| "binop BinXor (Bool v1) (Bool v2) = Some (Bool (v1 \<noteq> v2))"
| "binop bop v\<^isub>1 v\<^isub>2 = None"

lemma [simp]:
  "(binop LessThan v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 < i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop LessOrEqual v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 \<le> i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop GreaterThan v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 > i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop GreaterOrEqual v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Bool (i1 \<ge> i2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop BinAnd v1 v2 = Some v) \<longleftrightarrow> (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<and> b2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop BinOr v1 v2 = Some v) \<longleftrightarrow> (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<or> b2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop BinXor v1 v2 = Some v) \<longleftrightarrow> (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> v = Bool (b1 \<noteq> b2))"
by(cases v1, simp_all)(cases v2, auto)

lemma [simp]:
  "(binop Add v\<^isub>1 v\<^isub>2  = Some v) = (\<exists>i\<^isub>1 i\<^isub>2. v\<^isub>1 = Intg i\<^isub>1 \<and> v\<^isub>2 = Intg i\<^isub>2 \<and> v = Intg(i\<^isub>1+i\<^isub>2))"
(*<*)
apply(cases v\<^isub>1)
apply auto
apply(cases v\<^isub>2)
apply auto
done
(*>*)

lemma [simp]:
  "(binop Subtract v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 - i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop Mult v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 * i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop Mod v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 mod i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

lemma [simp]:
  "(binop Div v1 v2 = Some v) \<longleftrightarrow> (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> v = Intg(i1 div i2))"
apply(cases v1, auto)
apply(cases v2, auto)
done

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

| WT_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean :: Boolean"

| WT_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean :: Boolean"

lemma WT_binopI [intro]:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: Boolean"
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Mod \<or> bop = Div \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer :: Integer"
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

| WTrt_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean : Boolean"

lemma WTrt_binopI [intro]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : Boolean"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Div \<or> bop = Mod \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer : Integer"
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

lemma WT_binop_WTrt_binop:
  "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<Longrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(auto elim: WT_binop.cases)

lemma binop_progress:
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

end