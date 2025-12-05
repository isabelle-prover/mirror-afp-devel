section\<open>Value types\<close>

theory Valuetypes
imports ReadShow
begin

fun iter :: "(nat \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'b"
where
  "iter f v x = (if x \<le> 0 then v  
                 else f (x-1) (iter f v (x-1)))"

fun iter' :: "(nat \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> 'b option"
where
  "iter' f v x = (if x \<le> 0 then Some v
                  else case iter' f v (x-1) of
                          Some v' \<Rightarrow> f (x-1) v'
                        | None \<Rightarrow> None)"

type_synonym address = String.literal
type_synonym location = String.literal
type_synonym valuetype = String.literal


typedef bits = "{8::nat,16,24,32,40,48,56,64,72,80,88,96,104,112,120,128,
          136,144,152,160,168,176,184,192,200,208,216,224,232,240,248,256}"
  morphisms to_nat to_bit by auto

setup_lifting type_definition_bits

lift_definition b8 :: "bits" is 8 by simp
lift_definition b16 :: "bits" is 16 by simp
lift_definition b24 :: "bits" is 24 by simp
lift_definition b32 :: "bits" is 32 by simp
lift_definition b40 :: "bits" is 40 by simp
lift_definition b48 :: "bits" is 48 by simp
lift_definition b56 :: "bits" is 56 by simp
lift_definition b64 :: "bits" is 64 by simp
lift_definition b72 :: "bits" is 72 by simp
lift_definition b80 :: "bits" is 80 by simp
lift_definition b88 :: "bits" is 88 by simp
lift_definition b96 :: "bits" is 96 by simp
lift_definition b104 :: "bits" is 104 by simp
lift_definition b112 :: "bits" is 112 by simp
lift_definition b120 :: "bits" is 120 by simp
lift_definition b128 :: "bits" is 128 by simp
lift_definition b136 :: "bits" is 136 by simp
lift_definition b144 :: "bits" is 144 by simp
lift_definition b152 :: "bits" is 152 by simp
lift_definition b160 :: "bits" is 160 by simp
lift_definition b168 :: "bits" is 168 by simp
lift_definition b176 :: "bits" is 176 by simp
lift_definition b184 :: "bits" is 184 by simp
lift_definition b192 :: "bits" is 192 by simp
lift_definition b200 :: "bits" is 200 by simp
lift_definition b208 :: "bits" is 208 by simp
lift_definition b216 :: "bits" is 216 by simp
lift_definition b224 :: "bits" is 224 by simp
lift_definition b232 :: "bits" is 232 by simp
lift_definition b240 :: "bits" is 240 by simp
lift_definition b248 :: "bits" is 248 by simp
lift_definition b256 :: "bits" is 256 by simp

declare b8.rep_eq[simp]
declare b16.rep_eq[simp]
declare b24.rep_eq[simp]
declare b32.rep_eq[simp]
declare b40.rep_eq[simp]
declare b48.rep_eq[simp]
declare b56.rep_eq[simp]
declare b64.rep_eq[simp]
declare b72.rep_eq[simp]
declare b80.rep_eq[simp]
declare b88.rep_eq[simp]
declare b96.rep_eq[simp]
declare b104.rep_eq[simp]
declare b112.rep_eq[simp]
declare b120.rep_eq[simp]
declare b128.rep_eq[simp]
declare b136.rep_eq[simp]
declare b144.rep_eq[simp]
declare b152.rep_eq[simp]
declare b160.rep_eq[simp]
declare b168.rep_eq[simp]
declare b176.rep_eq[simp]
declare b184.rep_eq[simp]
declare b192.rep_eq[simp]
declare b200.rep_eq[simp]
declare b208.rep_eq[simp]
declare b216.rep_eq[simp]
declare b224.rep_eq[simp]
declare b232.rep_eq[simp]
declare b240.rep_eq[simp]
declare b248.rep_eq[simp]
declare b256.rep_eq[simp]

instantiation bits :: linorder
begin
  lift_definition less_bits :: "bits \<Rightarrow> bits \<Rightarrow> bool" is "(<)" .
  lift_definition less_eq_bits :: "bits \<Rightarrow> bits \<Rightarrow> bool" is "(\<le>)" .
  instance by (standard; transfer; linarith)
end

instantiation bits::equal
begin
  lift_definition equal_bits :: "bits \<Rightarrow> bits \<Rightarrow> bool" is "(=)" .
  instance by (standard; transfer; linarith)
end

declare Valuetypes.less_bits.rep_eq[simp]
declare Valuetypes.less_eq_bits.rep_eq[simp]

lemma to_nat_g_0[simp]: "to_nat b'>0" using to_nat[of b'] by auto
lemma to_nat_max_g_0[simp]: "0 < max (to_nat b1) (to_nat b2)" using to_nat_g_0[of b1] to_nat_g_0[of b2] by linarith
lemma to_nat_max[simp]: "max (to_nat b1) (to_nat b2) = to_nat (max b1 b2)" by (simp add: max_def)

datatype types = TSInt bits
               | TUInt bits
               | TBool
               | TAddr


definition createSInt :: "bits \<Rightarrow> int \<Rightarrow> valuetype"
where
  "createSInt b v =
    (if v \<ge> 0

      then ShowL\<^sub>i\<^sub>n\<^sub>t (-(2^((to_nat b)-1)) + (v+2^((to_nat b)-1)) mod (2^(to_nat b)))
      else ShowL\<^sub>i\<^sub>n\<^sub>t (2^((to_nat b)-1) - (-v+2^((to_nat b)-1)-1) mod (2^(to_nat b)) - 1))"

value "createSInt b16 (-002)"

declare createSInt_def [solidity_symbex]

lemma upper_bound:
  fixes b::nat
    and c::int
  assumes "b > 0"
      and "c < 2^(b-1)"
    shows "c + 2^(b-1) < 2^b"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. (\<forall>(c::int)<2^b. (c + 2^b) < 2^(Suc b))" by simp
  show ?thesis using a1[OF b2] assms by simp
qed

lemma upper_bound2:
  fixes b::bits
      and c::int
    assumes "c < 2^to_nat b"
      and "c \<ge> 0"
    shows "c - (2^((to_nat b)-1)) < 2^((to_nat b)-1)"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. (\<forall>(c::int)<2^(Suc b). c\<ge>0 \<longrightarrow> (c - 2^b) < 2^b)" by simp
  show ?thesis using a1[OF b2] assms by simp
qed

lemma upper_bound3:
   fixes b::bits
     and v::int
 defines "x \<equiv> - (2 ^ ((to_nat b) - 1)) + (v + 2 ^ ((to_nat b) - 1)) mod 2 ^ (to_nat b)"
   shows "x < 2^((to_nat b)-1)"
  using upper_bound2 assms by auto

lemma upper_bound4:
  fixes b::bits
    and v::int
assumes "to_nat(b) > 0"
shows "2^((to_nat(b))-1) - (-v+2^((to_nat(b))-1)-1) mod (2^to_nat(b)) - 1 < 2 ^ ((to_nat(b)) - 1)"
  by (smt (verit) mod_int_pos_iff zero_less_power_eq)

lemma lower_bound:
    fixes b::bits
    shows "\<forall>(c::int) \<ge> -(2^((to_nat b)-1)). (-c + 2^((to_nat b)-1) - 1 < 2^(to_nat b))"
proof -
  have a1: "\<And>P. (\<forall>b::nat. P b) \<Longrightarrow> (\<forall>b>0. P ((b-1)::nat))" by simp
  have b2: "\<forall>b::nat. \<forall>(c::int) \<ge> -(2^b). (-c + (2^b) - 1) < 2^(Suc b)" by simp
  show ?thesis using a1[OF b2] by simp
qed

lemma lower_bound2:
  fixes b::bits
    and v::int
      defines "x \<equiv> 2^((to_nat b) - 1) - (-v+2^((to_nat b)-1)-1) mod 2^(to_nat b) - 1"
      shows "x \<ge> - (2 ^ ((to_nat b) - 1))"
  using upper_bound2 assms by auto

lemma createSInt_id_g0:
    fixes b::bits
      and v::int
  assumes "v \<ge> 0"
      and "v < 2^((to_nat b)-1)"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v"
proof -
  from assms have "v + 2^((to_nat b)-1) \<ge> 0" by simp
  moreover from assms have "v + (2^((to_nat b)-1)) < 2^(to_nat b)" using upper_bound[of "to_nat b"] by auto
  ultimately have "(v + 2^((to_nat b)-1)) mod (2^(to_nat b)) = v + 2^((to_nat b)-1)" by simp
  moreover from assms have "createSInt b v=ShowL\<^sub>i\<^sub>n\<^sub>t (-(2^((to_nat b)-1)) + (v+2^((to_nat b)-1)) mod (2^(to_nat b)))" unfolding createSInt_def by simp
  ultimately show ?thesis by simp
qed

lemma createSInt_id_l0:
    fixes b::bits
      and v::int
  assumes "v < 0"
      and "v \<ge> -(2^((to_nat b)-1))"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v"
proof -
  from assms have "-v + 2^((to_nat b)-1) - 1 \<ge> 0" by simp
  moreover from assms have "-v + 2^((to_nat b)-1) - 1 < 2^(to_nat b)" using lower_bound[of b] by auto 
  ultimately have "(-v + 2^((to_nat b)-1) - 1) mod (2^(to_nat b)) = (-v + 2^((to_nat b)-1) - 1)" by simp
  moreover from assms have "createSInt b v= ShowL\<^sub>i\<^sub>n\<^sub>t (2^((to_nat b)-1) - (-v+2^((to_nat b)-1)-1) mod (2^(to_nat b)) - 1)" unfolding createSInt_def by simp
  ultimately show ?thesis by simp
qed

lemma createSInt_id:
    fixes b::bits
      and v::int
  assumes "v < 2^((to_nat b)-1)"
      and "v \<ge> -(2^((to_nat b)-1))"
    shows "createSInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t v" using createSInt_id_g0 createSInt_id_l0 assms unfolding createSInt_def by simp

definition createUInt :: "bits \<Rightarrow> int \<Rightarrow> valuetype"
  where "createUInt b v = ShowL\<^sub>i\<^sub>n\<^sub>t (v mod (2^(to_nat b)))"
declare createUInt_def[solidity_symbex]

lemma createSInt_less:
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (createSInt b v) < 2^((to_nat(b) - 1))"
proof (cases "v \<ge> 0")
  case True
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (createSInt b v) = -(2^(to_nat(b) - 1)) + (v+2^(to_nat(b) - 1)) mod (2^to_nat(b))" unfolding createSInt_def using Read_ShowL_id by simp
  then show ?thesis using upper_bound3 by simp
next
  case False
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (createSInt b v) = 2^(to_nat(b) - 1) - (-v+2^(to_nat(b) - 1)-1) mod (2^(to_nat(b))) - 1" unfolding createSInt_def using Read_ShowL_id by simp
  then show ?thesis using upper_bound4 by simp
qed

lemma createSInt_greater:
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (createSInt b v) \<ge> - (2 ^ (to_nat(b) - 1))"
  using lower_bound2 Read_ShowL_id unfolding createSInt_def by simp

lemma "ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t STR ''001'') \<noteq> STR ''001''" by solidity_symbex

definition checkSInt :: "bits \<Rightarrow> valuetype \<Rightarrow> bool"
where
  "checkSInt b v = (ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> -(2^(to_nat(b) - 1)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(to_nat(b) - 1) 
                    \<and> ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t v) = v)"
declare checkSInt_def [solidity_symbex]

lemma createUInt_greater:
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (createUInt b v) \<ge> 0" using Read_ShowL_id unfolding createUInt_def by simp

lemma createUInt_less:
  shows "ReadL\<^sub>i\<^sub>n\<^sub>t (createUInt b v) < (2^(to_nat b))" using Read_ShowL_id unfolding createUInt_def by simp

lemma createUInt_id:
  assumes "v \<ge> 0"
      and "v < 2^(to_nat b)"
    shows "createUInt b v =  ShowL\<^sub>i\<^sub>n\<^sub>t v"
unfolding createUInt_def by (simp add: assms(1) assms(2))

definition checkUInt :: "bits \<Rightarrow> valuetype \<Rightarrow> bool"
where
  "checkUInt b v = (ReadL\<^sub>i\<^sub>n\<^sub>t v \<ge> 0 \<and> ReadL\<^sub>i\<^sub>n\<^sub>t v < 2^(to_nat b) \<and> ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t v) = v)"
declare checkUInt_def  [solidity_symbex]

definition createBool :: "bool \<Rightarrow> valuetype"
where
  "createBool b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l b"

declare createBool_def [solidity_symbex]

fun removeDot:: "char list \<Rightarrow> String.literal \<Rightarrow> String.literal"
  where 
"removeDot [] str = str"
| "removeDot (x # xs) str = (if x = CHR ''.'' then removeDot xs str else removeDot xs (str + (String.implode [x])))"



lemma removeDotNoDot:
  assumes "CHR ''.'' \<notin> set(String.explode st)"
    and "l = String.explode y"
  shows "(CHR ''.'' \<notin> set(String.explode(removeDot l st)))" using assms
proof(induction l arbitrary:y st)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then have a5:"l = literal.explode (String.implode (tl (literal.explode y)))"
    by (metis String.implode_explode_eq implode.rep_eq list.distinct(1) list.map_sel(2) list.sel(3))
  then have a10:"CHR ''.'' \<notin> set (literal.explode (removeDot l st))" using Cons by blast
  then show ?case
  proof(cases "a = CHR ''.'' ")
    case True
    then have "literal.explode (removeDot (a # l) st) = literal.explode(removeDot l st)" by simp
    then show ?thesis using a10 by simp
  next
    case False
    then have "CHR ''.'' \<notin> set (literal.explode (String.implode [a]))" using String.explode_implode_eq 
       String.implode_explode_eq implode.rep_eq 
      by (metis Cons.prems(2) in_set_replicate length_Cons list.sel(1) list.simps(8) list.simps(9) list.size(3) remdups_adj.simps(2) remdups_adj_singleton_iff)
    then have "CHR ''.'' \<notin> set (literal.explode (st + String.implode [a]))" using Cons(2)
      by (simp add: plus_literal.rep_eq)
    then have " CHR ''.'' \<notin> set (literal.explode (removeDot l (st + (String.implode [a]))))" 
      using Cons(1)[of "(st + (String.implode [a]))"] Cons(3) a5 by blast
    moreover have " (removeDot (a # l) st) = removeDot l (st + (String.implode [a]))" using False by simp
    ultimately show ?thesis by simp
  qed
qed

definition createAddress :: "address \<Rightarrow> valuetype"
where
    "createAddress ad = (if (CHR ''.'' \<notin> set(String.explode ad)) then ad else removeDot (String.explode(ad)) (STR ''''))"

lemma createAddressNoDots:
  shows "createAddress ad =t \<longrightarrow> CHR ''.'' \<notin> set(String.explode t)" using removeDotNoDot 
  using createAddress_def zero_literal.rep_eq by auto

declare createAddress_def [solidity_symbex]
(*
Second parameter is the target type/type that is returned
Same for convert
*)
fun comp :: "types \<Rightarrow> types \<Rightarrow> bool"
where
  "comp (TSInt b1) (TSInt b2) = (to_nat b1 \<le> to_nat b2)"
| "comp (TUInt b1) (TUInt b2) = (to_nat b1 \<le> to_nat b2)"
| "comp (TUInt b1) (TSInt b2) = (to_nat b1 < to_nat b2)"
| "comp TBool TBool = True"
| "comp TAddr TAddr = True"
| "comp _ _ = False"

fun convert :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype option"
where
  "convert (TSInt b1) (TSInt b2) v =
    (if to_nat b1 \<le> to_nat b2
      then Some v
      else None)"
| "convert (TUInt b1) (TUInt b2) v =
    (if to_nat b1 \<le> to_nat b2
      then Some v
      else None)"
| "convert (TUInt b1) (TSInt b2) v =
    (if to_nat b1 < to_nat b2
      then Some v
      else None)"
| "convert TBool TBool v = Some v"
| "convert TAddr TAddr v = Some v"
| "convert _ _ _ = None"

lemma convertSame:
  assumes "convert t1 t2 v = Some(v')"
  shows "v = v'" using assms by (cases t1; cases t2; (simp split:if_split_asm))


lemma convert_id[simp]:
  "convert tp tp kv = Some kv"
    by (metis types.exhaust convert.simps(1) convert.simps(2) convert.simps(4) convert.simps(5) order_refl)

(*Covered informally*)
fun olift ::
  "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "olift op (TSInt b1) (TSInt b2) v1 v2 =
    Some (createSInt (max b1 b2) (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt (max b1 b2))"
| "olift op (TUInt b1) (TUInt b2) v1 v2 =
    Some (createUInt (max b1 b2) (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TUInt (max b1 b2))"
| "olift op (TSInt b1) (TUInt b2) v1 v2 =
    (if to_nat b2 < to_nat b1
      then Some (createSInt b1 (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt b1)
      else None)"
| "olift op (TUInt b1) (TSInt b2) v1 v2 =
    (if to_nat b1 < to_nat b2
      then Some (createSInt b2 (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TSInt b2)
      else None)"
| "olift _ _ _ _ _ = None"

(*Covered*)
fun plift ::
  "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "plift op (TSInt b1) (TSInt b2) v1 v2 = Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)"
| "plift op (TUInt b1) (TUInt b2) v1 v2 = Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)"
| "plift op (TSInt b1) (TUInt b2) v1 v2 =
    (if to_nat b2 < to_nat b1
      then Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)
      else None)"
| "plift op (TUInt b1) (TSInt b2) v1 v2 =
    (if to_nat b1 < to_nat b2
      then Some (createBool (op \<lceil>v1\<rceil> \<lceil>v2\<rceil>), TBool)
      else None)" 
| "plift _ _ _ _ _ = None"

(*Covered*)
definition add :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "add = olift (+)"

(*Covered informally*)
definition sub :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "sub = olift (-)"

(*Covered informally*)
definition equal :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "equal = plift (=)"

(*Covered informally*)
definition less :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "less = plift (<)"

(*Covered informally*)
definition leq :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "leq = plift (\<le>)"

declare add_def sub_def equal_def leq_def less_def [solidity_symbex]

(*Covered*)
fun vtand :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "vtand TBool TBool a b =
    (if a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True \<and> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True then Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool)
    else Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool))"
| "vtand _ _ _ _ = None"

(*Covered informally*)
fun vtor :: "types \<Rightarrow> types \<Rightarrow> valuetype \<Rightarrow> valuetype \<Rightarrow> (valuetype * types) option"
where
  "vtor TBool TBool a b =
    (if a = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False \<and> b = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False
      then Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False, TBool)
      else Some (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True, TBool))"
| "vtor _ _ _ _ = None"

definition checkBool :: "valuetype  \<Rightarrow> bool"
where
  "checkBool v = (v = STR ''True'' \<or> v = STR ''False'')"

declare checkBool_def [solidity_symbex]

definition checkAddress :: "valuetype  \<Rightarrow> bool"
  where
    "checkAddress v = (CHR ''.'' \<notin> set(String.explode v))"

declare checkAddress_def [solidity_symbex]

primrec ival :: "types \<Rightarrow> valuetype"
where
  "ival (TSInt x) = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
| "ival (TUInt x) = ShowL\<^sub>i\<^sub>n\<^sub>t 0"
| "ival TBool = ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False"
| "ival TAddr = STR ''0x0000000000000000000000000000000000000000''"

declare convert.simps [simp del, solidity_symbex add]
declare olift.simps [simp del, solidity_symbex add]
declare plift.simps [simp del, solidity_symbex add]
declare vtand.simps [simp del, solidity_symbex add]
declare vtor.simps [simp del, solidity_symbex add]

end
