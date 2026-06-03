theory Solidity
imports State_Monad State "Finite-Map-Extras.Finite_Map_Extras"
begin

section \<open>Value types\<close>

datatype ('a) rvalue =
  Storage "'a valtype pointer option" |
  Memory (memloc: location) |
  Calldata "'a valtype pointer option" |
  Value (vt: "'a valtype") |
  Empty

definition kdbool where
  "kdbool = Value \<circ> Bool"

definition kdSint where
  "kdSint \<equiv> Value \<circ> Uint"

definition kdAddress where
  "kdAddress = Value \<circ> Address"

definition kdBytes where
  "kdBytes \<equiv> Value \<circ> Bytes"

fun lift_value_unary::"(('a::address) valtype \<Rightarrow> ('a::address) valtype option) \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "lift_value_unary op (rvalue.Value v) = op v \<bind> Some \<circ> rvalue.Value"
| "lift_value_unary op _ = None"

definition kdnot::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "kdnot = lift_value_unary vtnot"

fun lift_value_binary::"(('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option) \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "lift_value_binary op (rvalue.Value l) (rvalue.Value r) = op l r \<bind> Some \<circ> rvalue.Value"
| "lift_value_binary op _ _ = None"

definition kdequals where
  "kdequals = lift_value_binary vtequals"

definition kdless where
  "kdless = lift_value_binary vtless"

definition kdand where
  "kdand = lift_value_binary vtand"

definition kdor where
  "kdor = lift_value_binary vtor"

definition kdplus where
  "kdplus = lift_value_binary vtplus"

definition kdplus_safe where
  "kdplus_safe = lift_value_binary vtplus_safe"

definition kdminus where
  "kdminus = lift_value_binary vtminus"

definition kdminus_safe where
  "kdminus_safe = lift_value_binary vtminus_safe"

definition kdmult where
  "kdmult = lift_value_binary vtmult"

definition kdmult_safe where
  "kdmult_safe = lift_value_binary vtmult_safe"

definition kdmod where
  "kdmod = lift_value_binary vtmod"

definition kdbytes_index where
  "kdbytes_index = lift_value_binary vtbytes_index"

definition kdbytes_and where
  "kdbytes_and = lift_value_binary vtbytes_and"

definition kdbytes_or where
  "kdbytes_or = lift_value_binary vtbytes_or"

definition kdbytes_xor where
  "kdbytes_xor = lift_value_binary vtbytes_xor"

definition kdbytes_not where
  "kdbytes_not = lift_value_unary vtbytes_not"

definition kdbytes_cast where
  "kdbytes_cast m = lift_value_unary (vtbytes_cast m)"

type_synonym 'a expression_monad = "('a rvalue, ex, 'a state) state_monad"

definition newStack::"'a::address expression_monad" where
  "newStack = update (\<lambda>s. (Empty, s\<lparr>Stack:=fmempty\<rparr>))"

definition newMemory::"'a::address expression_monad" where
  "newMemory = update (\<lambda>s. (Empty, s\<lparr>Memory:=[]\<rparr>))"

definition newCalldata::"'a::address expression_monad" where
  "newCalldata = update (\<lambda>s. (Empty, s\<lparr>Calldata:=fmempty\<rparr>))"

fun the_value where
  "the_value (rvalue.Value x) = Some x"
| "the_value _ = None"

primrec lfold :: "('a::address) expression_monad list \<Rightarrow> (('a::address) valtype list, ex,('a::address) state) state_monad"
  where
    "lfold [] = return []"
  | "lfold (m#ms) =
      do {
        l \<leftarrow> m;
        l' \<leftarrow> option Err (\<lambda>_. the_value l);
        ls \<leftarrow> lfold ms;
        return (l' # ls)
      }"

section \<open>Constants\<close>

definition bool_monad where
  "bool_monad = return \<circ> kdbool"

definition true_monad::"('a::address) expression_monad" ("\<langle>T\<rangle>")  where
  "true_monad = bool_monad True"

definition false_monad::"('a::address) expression_monad"("\<langle>F\<rangle>")  where
  "false_monad = bool_monad False"

definition sint_monad ("(\<langle>sint\<rangle> _)" [70] 69) where
  "sint_monad = return \<circ> kdSint"

definition bytes_monad where
  "bytes_monad n xs  = (if n \<notin> {1..<33} \<or> n \<noteq> length xs then throw Err else return (kdBytes xs))"

definition address_monad where
  "address_monad = return \<circ> kdAddress"

definition bytes_monad2 where
  "bytes_monad2 = return \<circ> kdBytes"

locale Contract =
  fixes this :: "'a::address" (*address of executing contract*)
begin

definition this_monad where
  "this_monad = address_monad this"

end

locale Method =
  fixes msg_sender :: "'a::address" (*address of calling contract*)
    and msg_value :: "256 word" (*money send*)
    and timestamp :: "256 word" (*time stamp of a block*)
  assumes less_bound: "unat timestamp < 2^256"
begin

definition sender_monad  ("\<langle>sender\<rangle>") where
  "sender_monad = address_monad msg_sender"

definition value_monad ("\<langle>value\<rangle>") where
  "value_monad = sint_monad msg_value"

definition block_timestamp_monad ("\<langle>stamp\<rangle>") where
  "block_timestamp_monad = sint_monad timestamp"

end

locale Keccak256 =
  fixes keccak256::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue"
  and encodeABI::"('a::address) rvalue list \<Rightarrow> ('a::address) rvalue"
  assumes "\<And>x y. keccak256 x = keccak256 y \<Longrightarrow> x = y"
begin

definition keccak256_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" ("\<langle>keccak256\<rangle>") where
  "keccak256_monad m = 
    do {
      v \<leftarrow> m;
      return (keccak256 v)
    }"

definition encodeABI_monad::"('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" ("\<langle>encodeABI\<rangle>") where
  "encodeABI_monad ms =
    do {
      xs \<leftarrow> mfold ms;
      return (encodeABI xs)
    }"

end

section \<open>Unary Operations\<close>

definition lift_unary_monad ::"(('a::address) rvalue \<Rightarrow> ('a::address) rvalue option) \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "lift_unary_monad op lm = 
    do {
      lv \<leftarrow> lm;
      val \<leftarrow> option Err (K (op lv));
      return val
    }"

definition not_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" ("\<langle>\<not>\<rangle> _" 65) where
  "not_monad = lift_unary_monad kdnot"

section \<open>Binary Operations\<close>

definition lift_op_monad::"(('a::address) rvalue \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option) \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "lift_op_monad op lm rm = 
    do {
      lv \<leftarrow> lm;
      rv \<leftarrow> rm;
      val \<leftarrow> option Err (K (op lv rv));
      return val
    }"

lemma lift_op_monad_simp1:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Exception (e, s'')"
    shows "execute (lift_op_monad op lm rm) s = Exception (e, s'')"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp2:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = NT"
    shows "execute (lift_op_monad op lm rm) s = NT"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp3:
  assumes "execute lm s = Exception (e, s')"
    shows "execute (lift_op_monad op lm rm) s = Exception (e, s')"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp4:
  assumes "execute lm s = NT"
    shows "execute (lift_op_monad op lm rm) s = NT"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp5:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Normal (rv, s'')"
    shows "execute (lift_op_monad op lm rm) s = execute (option Err (K (op lv rv))) s''"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

definition equals_monad (infixl "\<langle>=\<rangle>" 65) where
  "equals_monad = lift_op_monad kdequals"

lemma equals_monad_simp1[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Exception (e, s'')"
    shows "execute (equals_monad lm rm) s = Exception (e, s'')"
  unfolding equals_monad_def by (rule lift_op_monad_simp1[OF assms])

lemma equals_monad_simp2[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = NT"
    shows "execute (equals_monad lm rm) s = NT"
  unfolding equals_monad_def by (rule lift_op_monad_simp2[OF assms])

lemma equals_monad_simp3[execute_simps]:
  assumes "execute lm s = Exception (e, s')"
    shows "execute (equals_monad lm rm) s = Exception (e, s')"
  unfolding equals_monad_def by (rule lift_op_monad_simp3[OF assms])

lemma equals_monad_simp4[execute_simps]:
  assumes "execute lm s = NT"
    shows "execute (equals_monad lm rm) s = NT"
  unfolding equals_monad_def by (rule lift_op_monad_simp4[OF assms])

lemma equals_monad_simp5[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Normal (rv, s'')"
    shows "execute (equals_monad lm rm) s = execute (option Err (K (kdequals lv rv))) s''"
  unfolding equals_monad_def by (rule lift_op_monad_simp5[OF assms])

definition less_monad (infixl "\<langle><\<rangle>" 65) where
  "less_monad = lift_op_monad kdless"

definition and_monad (infixl "\<langle>\<and>\<rangle>" 55) where
  "and_monad = lift_op_monad kdand"

definition or_monad (infixl "\<langle>\<or>\<rangle>" 54) where
  "or_monad = lift_op_monad kdor"

definition plus_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "plus_monad = lift_op_monad kdplus"

definition plus_monad_safe::
  "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad"
  (infixl "\<langle>+\<rangle>" 65)
where
  "plus_monad_safe = lift_op_monad kdplus_safe"

definition minus_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "minus_monad = lift_op_monad kdminus"

definition minus_monad_safe::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" (infixl "\<langle>-\<rangle>" 65) where
  "minus_monad_safe = lift_op_monad kdminus_safe"

definition mult_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "mult_monad = lift_op_monad kdmult"

definition mult_monad_safe::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" (infixl "\<langle>*\<rangle>" 65) where
  "mult_monad_safe = lift_op_monad kdmult_safe"

definition mod_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" (infixl "\<langle>%\<rangle>" 65) where
  "mod_monad = lift_op_monad kdmod"

definition bytes_index_monad where
  "bytes_index_monad = lift_op_monad kdbytes_index"

definition bytes_and_monad where
  "bytes_and_monad = lift_op_monad kdbytes_and"

definition bytes_or_monad where
  "bytes_or_monad = lift_op_monad kdbytes_or"

definition bytes_xor_monad where
  "bytes_xor_monad = lift_op_monad kdbytes_xor"

definition bytes_not_monad where
  "bytes_not_monad = lift_unary_monad kdbytes_not"

definition bytes_cast_monad where
  "bytes_cast_monad m = lift_unary_monad (kdbytes_cast m)"

section \<open>Store Lookups\<close>

definition (in Contract) storeLookup::
  "id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad"
  ("(_ ~\<^sub>s _)" [100, 100] 70) 
where
  "storeLookup i es =
    do {
      is \<leftarrow> lfold es;
      sd \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i));
      if storage_data.is_Value sd then return (rvalue.Value (storage_data.vt sd)) else return (rvalue.Storage (Some \<lparr>Location=i, Offset= is\<rparr>))
    }"

definition (in Contract) storeArrayLength::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "storeArrayLength i es =
    do {
      is \<leftarrow> lfold es;
      sd \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i));
      storage_check sd
        (K (throw Err))
        (\<lambda>sa. return (rvalue.Value (Uint (of_nat (length (storage_data.ar sd))))))
        (K (throw Err))
    }"

definition (in Contract) storeArrayLengthSafe::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "storeArrayLengthSafe i es =
    do {
      is \<leftarrow> lfold es;
      sd \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i));
      storage_check sd
        (K (throw Err))
        (\<lambda>sa. (if length (storage_data.ar sd) < 2^256 then return (Value (Uint (word_of_nat (length (storage_data.ar sd))))) else throw Err))
        (K (throw Err))
    }"


section \<open>Stack Lookups\<close>

definition stack_check where
  "stack_check i kf mf cf cp sf sp =
    do {
      k \<leftarrow> applyf Stack;
      case k $$ i of
        Some x \<Rightarrow>
          (case x of
            kdata.Value v \<Rightarrow> kf v
          | kdata.Storage (Some p) \<Rightarrow> sf (Location p) (Offset p)
          | kdata.Storage None \<Rightarrow> sp
          | kdata.Memory l \<Rightarrow> mf l
          | kdata.Calldata (Some p) \<Rightarrow> cf (Location p) (Offset p)
          | kdata.Calldata None \<Rightarrow> cp)
      | None \<Rightarrow> throw Err
    }"

definition(in Contract) stackLookup::
  "id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad"
  ("(_ ~ _)" [1000, 0] 70)
where
  "stackLookup i es =
    do {
      is \<leftarrow> lfold es;
      stack_check i
        (\<lambda>k. return (Value k))
        (\<lambda>l. do {
          l' \<leftarrow> option Err (\<lambda>s. mlookup (state.Memory s) is l);
          md  \<leftarrow> option Err (\<lambda>s. state.Memory s $ l');
          if mdata.is_Value md then return (rvalue.Value (mdata.vt md)) else return (rvalue.Memory l')
        })
        (\<lambda>l xs. do {
          sd \<leftarrow> option Err (\<lambda>s. state.Calldata s $$ l \<bind> clookup (xs@is));
          if call_data.is_Value sd then return (rvalue.Value (call_data.vt sd)) else return (rvalue.Calldata (Some \<lparr>Location=l, Offset=xs@is\<rparr>))
        })
        (
          return (rvalue.Calldata None)
        )
        (\<lambda>l xs. do {
          sd \<leftarrow> option Err (\<lambda>s. slookup (xs@is) (state.Storage s this l));
          if storage_data.is_Value sd then return (rvalue.Value (storage_data.vt sd)) else return (rvalue.Storage (Some \<lparr>Location=l, Offset=xs@is\<rparr>))
        })
        (
          return (rvalue.Storage None)
        )
    }"

definition(in Contract) arrayLength::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "arrayLength i es =
    do {
      is \<leftarrow> lfold es;
      stack_check i
        (K (throw Err))
        (\<lambda>l. do {
          l' \<leftarrow> option Err (\<lambda>s. mlookup (state.Memory s) is l);
          md  \<leftarrow> option Err (\<lambda>s. state.Memory s $ l');
          if mdata.is_Array md then return (rvalue.Value (Uint (of_nat (length (mdata.ar md))))) else throw Err
        })
        (\<lambda>l xs. do {
          sd \<leftarrow> option Err (\<lambda>s. state.Calldata s $$ l \<bind> clookup (xs@is));
          if call_data.is_Array sd then return (rvalue.Value (Uint (of_nat (length (call_data.ar sd))))) else throw Err
        })
        (throw Err)
        (\<lambda>l xs. do {
          sd \<leftarrow> option Err (\<lambda>s. slookup (xs@is) (state.Storage s this l));
          if storage_data.is_Array sd then return (rvalue.Value (Uint (of_nat (length (storage_data.ar sd))))) else throw Err
        })
        (throw Err)
    }"

section \<open>Skip\<close>

definition skip_monad:: "('a rvalue, ex, ('a::address) state) state_monad" ("\<langle>skip\<rangle>") where
"skip_monad = return Empty"

section \<open>Conditionals\<close>

definition cond_monad::
  "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad"
  ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
where
"cond_monad bm mt mf = 
  do {
    b \<leftarrow> equals_monad bm true_monad;
    if b = kdbool True then mt else if b = kdbool False then mf else throw Err
  }"

lemma execute_cond_monad_normal_E:
  assumes "execute (cond_monad bm mt mf) s = Normal (x, s')"
  obtains (1) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool True, s'')" and "execute mt s'' = Normal (x, s')"
        | (2) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool False, s'')" and "execute mf s'' = Normal (x, s')"
  using assms unfolding cond_monad_def
  by (cases "execute (equals_monad bm true_monad) s") (auto simp add: execute_simps split:if_split_asm)

lemma execute_cond_monad_exception_E:
  assumes "execute (cond_monad bm mt mf) s = Exception (x, s')"
  obtains (1) "execute (equals_monad bm true_monad) s = Exception (x, s')"
        | (2) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool True, s'')" and "execute mt s'' = Exception (x, s')"
        | (3) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool False, s'')" and "execute mf s'' = Exception (x, s')"
        | (4) a where "execute (equals_monad bm true_monad) s = Normal (a, s')" and "a \<noteq> kdbool True \<and> a \<noteq> kdbool False \<and> x = Err"
  using assms unfolding cond_monad_def
  by (cases "execute (equals_monad bm true_monad) s") (auto simp add: execute_simps split:if_split_asm)

lemma execute_cond_monad_simp1[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Normal (kdbool True, s')"
  shows "execute (cond_monad bm mt mf) s = execute mt s'"
  unfolding cond_monad_def by (simp add: execute_simps assms)

lemma execute_cond_monad_simp2[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Normal (kdbool False, s')"
  shows "execute (cond_monad bm mt mf) s = execute mf s'"
  unfolding cond_monad_def by (simp add: execute_simps assms kdbool_def)

lemma execute_cond_monad_simp3[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Exception (e, s')"
  shows "execute (cond_monad bm mt mf) s = Exception (e, s')"
  unfolding cond_monad_def by (simp add: execute_simps assms)

lemma execute_cond_monad_simp4[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = NT"
  shows "execute (cond_monad bm mt mf) s = NT"
  unfolding cond_monad_def by (simp add: execute_simps assms)

section \<open>Require/Assert\<close>

definition require_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "require_monad em = 
    do {
      e \<leftarrow> em;
      if e = kdbool True then return Empty else throw Err
    }"

definition assert_monad :: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" ("\<langle>assert\<rangle>") where
 "assert_monad bm = 
    cond_monad bm (return Empty) (throw Err)"

section \<open>Stack Assign\<close>

definition my_update_monad:: "(('a::address) state \<Rightarrow> 'b) \<Rightarrow> (('c \<Rightarrow> 'd) \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state) \<Rightarrow> ('b \<Rightarrow> 'd option) \<Rightarrow> 'a expression_monad" where
  "my_update_monad s u f = option Err (\<lambda>s'. f (s s')) \<bind> modify \<circ> u \<circ> K \<bind> K (return Empty)"

definition memory_update_monad:: "(('a::address valtype) memory \<Rightarrow> ('a::address valtype) memory option) \<Rightarrow> 'a expression_monad" where
  "memory_update_monad = my_update_monad state.Memory Memory_update"

context Contract
begin

definition storage_update:: "id \<Rightarrow> ('a::address valtype) storage_data \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "storage_update i d s = s\<lparr>Storage := (state.Storage s) (this := (state.Storage s this) (i := d))\<rparr>"

definition storage_update_monad where
  "storage_update_monad xs is sd p = option Err (\<lambda>s. updateStore (xs @ is) sd (state.Storage s this p)) \<bind> modify \<circ> (storage_update p) \<bind> K (return Empty)"

end

definition option_check where
  "option_check f m = option Err f \<bind> m"

fun (in Contract) assign_stack::
  "id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) expression_monad"
where
  "assign_stack i is (rvalue.Value v) =
    stack_check i
      (K (modify (stack_update i (kdata.Value v)) \<bind> K (return Empty)))
      (\<lambda>l. (memory_update_monad (\<lambda>m. mupdate is (l, (mdata.Value v), m))))
      (K (K (throw Err)))
      (throw Err)
      (\<lambda>l xs. storage_update_monad xs is (K (storage_data.Value v)) l)
      (throw Err)"
| "assign_stack i is (rvalue.Memory l) =
    stack_check i
      (K (throw Err))
      (\<lambda>l'. case_list is
        (modify (stack_update i (kdata.Memory l))\<bind> K (return Empty))
        (K (K (memory_update_monad (\<lambda>m. (m$l) \<bind> (\<lambda>v. mupdate is (l', v, m)))))))
      (K (K (throw Err)))
      (throw Err)
      (\<lambda>l' xs. option_check
        (\<lambda>s. copy_memory_storage (state.Memory s) l)
        (\<lambda>sd. storage_update_monad xs is (K sd) l'))
      (throw Err)"
| "assign_stack i is (rvalue.Calldata (Some p)) =
    stack_check i
      (K (throw Err))
      (\<lambda>l. option_check
        (\<lambda>s. state.Calldata s $$ (Location p) \<bind> clookup (Offset p))
        (\<lambda>cd. memory_update_monad (mupdate is \<circ> (copy_calldata_memory cd l))))
      (K (K (throw Err)))
      (modify (stack_update i (kdata.Calldata (Some p))) \<bind> K (return Empty))
      (\<lambda>l xs. option_check
        (\<lambda>s. state.Calldata s $$ (Location p) \<bind> clookup (Offset p @ is))
        (\<lambda>cd. storage_update_monad xs is (K (copy_calldata_storage cd)) l))
      (throw Err)"
| "assign_stack i is (rvalue.Calldata None) = throw Err"
| "assign_stack i is (rvalue.Storage (Some p)) =
    stack_check i
      (K (throw Err))
      (\<lambda>l. option_check
        (\<lambda>s. slookup (Offset p) (state.Storage s this (Location p)))
        (\<lambda>sd. memory_update_monad
          (\<lambda>m. copy_storage_memory sd l m \<bind>
            mupdate is)))
      (K (K (throw Err)))
      (throw Err)
      (\<lambda>l xs. case_list is
        (modify (stack_update i (kdata.Storage (Some p))) \<bind> K (return Empty))
        (K (K (option_check
          (\<lambda>s. slookup (Offset p @ is) (state.Storage s this (Location p)))
          (\<lambda>sd. storage_update_monad xs [] (K sd) l)))))
      (modify (stack_update i (kdata.Storage (Some p))) \<bind> K (return Empty))"
| "assign_stack i is (rvalue.Storage None) = throw Err"
| "assign_stack i is rvalue.Empty = throw Err"

definition (in Contract) assign_stack_monad::
  "String.literal \<Rightarrow> ('a rvalue, ex, 'a state) state_monad list \<Rightarrow> ('a rvalue, ex, 'a state) state_monad \<Rightarrow> ('a rvalue, ex, 'a state) state_monad"
  ("(_ _ ::= _)" [1000, 61, 0] 61)
where
  "assign_stack_monad i es m \<equiv> 
    do {
      val \<leftarrow> m;
      is \<leftarrow> lfold es;
      assign_stack i is val;
      return Empty
    }"

section \<open>Storage Assignment\<close>

fun (in Contract) assign_storage::
  "id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) expression_monad"
where
  "assign_storage i is (rvalue.Value v) = storage_update_monad [] is (K (storage_data.Value v)) i"
| "assign_storage i is (rvalue.Memory l) =
    (option_check
      (\<lambda>s. copy_memory_storage (state.Memory s) l)
      (\<lambda>sd. storage_update_monad [] is (K sd) i))"
| "assign_storage i is (rvalue.Calldata (Some p)) =
    (option_check
      (\<lambda>s. state.Calldata s $$ (Location p) \<bind> clookup (Offset p))
      (\<lambda>cd. storage_update_monad [] is (K (copy_calldata_storage cd)) i))"
| "assign_storage i is (rvalue.Calldata None) = throw Err"
| "assign_storage i is (rvalue.Storage (Some p)) =
    (option_check
      (\<lambda>s. slookup (Offset p) (state.Storage s this (Location p)))
      (\<lambda>sd. storage_update_monad [] is (K sd) i))"
| "assign_storage i is (rvalue.Storage None) = throw Err"
| "assign_storage i is rvalue.Empty = throw Err"

definition (in Contract) assign_storage_monad
("(_ _ ::=\<^sub>s _)" [61, 62, 61] 60)
  where
  "assign_storage_monad i es m \<equiv> 
    do {
      val \<leftarrow> m;
      is \<leftarrow> lfold es;
      assign_storage i is val
    }"

(*
  Note that m is evaluated first and then indexed expressions are evaluated from left to right.
  
  This can be seen by executing test() in the following example which outputs 3 before 1 and 2.
  
  pragma solidity >=0.7.0 <0.9.0;
  
  contract Test {
  
      event Log(uint _value);
  
      uint[5][5] myarray;
  
      function print(uint x) public returns (uint) {
          emit Log(x);
          return x;
      }
  
      function test() external {
          myarray[print(1)][print(2)] = print(3);
      }
  }
*)

section \<open>Loops\<close>

lemma true_monad_mono[mono]: "mono_sm (\<lambda>_. true_monad)"
  by (simp add: monotoneI sm_ordI)

lemma cond_K [partial_function_mono]: "mono_sm (\<lambda>f. K (f x) y)"
proof (rule monotoneI)
  fix xa::"'a \<Rightarrow> ('b, 'c, 'd) state_monad"
  and ya::" 'a \<Rightarrow> ('b, 'c, 'd) state_monad"
  assume "sm.le_fun xa ya"
  then show "sm_ord (K (xa x) y) (K (ya x) y)" using K.elims fun_ord_def by metis
qed

lemma lift_op_monad_mono:
  assumes "mono_sm A" and "mono_sm B"
  shows "mono_sm (\<lambda>f. lift_op_monad op (A f) (B f))"
  unfolding lift_op_monad_def
proof (rule bind_mono[OF assms(1)])
  fix lv
  show "mono_sm (\<lambda>f. B f \<bind> (\<lambda>rv. option Err (K (op lv rv)) \<bind> return))"
  proof (rule bind_mono[OF assms(2)])
    fix rv
    show "mono_sm (\<lambda>f. option Err (K (op lv rv)) \<bind> return)"
    proof (rule bind_mono)
      show "mono_sm (\<lambda>f. option Err (K (op lv rv)))" using option_monad_mono[of Err "K (op lv rv)"] by simp
    next
      fix y::"('x::address) rvalue"
      show "mono_sm (\<lambda>f. return y)" by (simp add: mono)
    qed
  qed
qed

lemma equals_monad_mono[mono]:
  assumes "mono_sm A" and "mono_sm B"
  shows "mono_sm (\<lambda>f. equals_monad (A f) (B f))"
  unfolding equals_monad_def by (rule lift_op_monad_mono[OF assms])

lemma cond_mono [partial_function_mono, mono]:
  assumes "mono_sm A" and "mono_sm B" and "mono_sm C"
  shows "mono_sm (\<lambda>f. cond_monad (A f) (B f) (C f))"
  unfolding cond_monad_def
proof (rule bind_mono)
  show "mono_sm (\<lambda>f. equals_monad (A f) true_monad)"
  proof (rule equals_monad_mono[OF assms(1)])
    show "mono_sm (\<lambda>f. true_monad)" by (simp add: mono)
  qed
next
  fix b
  show "mono_sm (\<lambda>f. if b = kdbool True then B f else if b = kdbool False then C f else throw Err)"
    by (rule Partial_Function.if_mono[OF assms(2)], rule Partial_Function.if_mono[OF assms(3)]) (rule throw_monad_mono) 
qed

partial_function (sm) while_monad :: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "while_monad c m = cond_monad c (bind m (K (while_monad c m))) (return Empty)"

text \<open>
  The partial function package provides us with three properties:
  \<^item> A simplifier rule @{thm while_monad.simps}
  \<^item> A general induction rule @{thm while_monad.fixp_induct}
  \<^item> An induction rule for partial correctness @{thm while_monad.raw_induct}
\<close>

section \<open>Internal Method Calls\<close>

definition icall where
"icall m = 
do {
  x \<leftarrow> applyf Stack;
  r \<leftarrow> m;
  modify (Stack_update (K x));
  return r
}"

lemma icall_mono[mono]:
  assumes "mono_sm (\<lambda>x. m x)"
  shows "mono_sm (\<lambda>x. icall (m x))"
  unfolding icall_def using assms by (simp add:mono)

section \<open>External Method Calls\<close>

definition ecall where
"ecall m = 
do {
  s \<leftarrow> get;
  r \<leftarrow> m;
  modify (\<lambda>s'. s'\<lparr>Stack := state.Stack s, Memory := state.Memory s, Calldata := state.Calldata s\<rparr>);
  return r
}"

lemma ecall_mono[mono]:
  assumes "mono_sm (\<lambda>x. m x)"
  shows "mono_sm (\<lambda>x. ecall (m x))"
  unfolding ecall_def using assms by (simp add:mono)

section \<open>Transfer\<close>

fun readValue:: "('a::address) rvalue \<Rightarrow> ((('a::address) valtype, ex, ('a::address) state) state_monad)" where
  "readValue (rvalue.Value x) = return x"
| "readValue _ = throw Err"

fun readAddress:: "('a::address) valtype \<Rightarrow> ((('a::address), ex, ('a::address) state) state_monad)" where
  "readAddress (Address x) = return x"
| "readAddress _ = throw Err"

fun readSint:: "('a::address) valtype \<Rightarrow> ((256 word, ex, ('a::address) state) state_monad)" where
  "readSint (Uint x) = return x"
| "readSint _ = throw Err"

context Contract
begin

abbreviation balance_update:: "nat \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "balance_update \<equiv> balances_update this"

definition inv:: "'a rvalue \<times> ('a::address) state + ex \<times> ('a::address) state \<Rightarrow> (('a::address) state \<Rightarrow> bool) \<Rightarrow> (('a::address) state \<Rightarrow> bool) \<Rightarrow> bool" where
  "inv r P Q \<equiv> (case r of Inl a \<Rightarrow> P (snd a)
                        | Inr a \<Rightarrow> Q (snd a))"

definition inv_state:: "((id \<Rightarrow> ('a::address valtype) storage_data) \<times> nat \<Rightarrow> bool) \<Rightarrow> ('a::address) state \<Rightarrow> bool"
  where "inv_state i s = i (state.Storage s this, state.Balances s this)"

definition post::
  "('a::address) state \<Rightarrow> 'a rvalue \<times> ('a::address) state + ex \<times> ('a::address) state
  \<Rightarrow> (('a::address) state \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) state \<Rightarrow> bool) \<Rightarrow> (('a::address) state \<Rightarrow> bool)
  \<Rightarrow> bool" where
  "post s r I_s I_e \<equiv> (case r of Inl a \<Rightarrow> I_s s (fst a) (snd a)
                               | Inr a \<Rightarrow> I_e (snd a))"

term "post s r (K (K (inv_state i))) e"

(*
  reduce post2 for "exc x" to post2 for "x"
*)
lemma post_exc_true:
  assumes "effect (exc x) s r"
      and "\<And>r. effect x s r \<Longrightarrow> post s r I (K True)"
    shows "post s r I (K True)"
  using assms(1) unfolding post_def effect_def exc_def
  apply (auto simp add:execute_simps) using assms(2) unfolding effect_def post_def
  by (smt (z3) case_prod_beta ex.case ex.exhaust fst_def is_Normal_def old.sum.simps(5) prod.collapse result.case_eq_if result.disc(2) result.disc(3) result.distinct_disc(1) result.sel(1) snd_def)

lemma post_exc_false:
  assumes "effect (exc x) s r"
      and "\<And>r. effect x s r \<Longrightarrow> post s r I (K False)"
    shows "post s r I (K False)"
  using assms(1) unfolding post_def effect_def exc_def
  apply (auto simp add:execute_simps) using assms(2) unfolding effect_def post_def
  apply (smt (z3) case_prod_beta ex.case ex.exhaust fst_def is_Normal_def old.sum.simps(5) prod.collapse result.case_eq_if result.disc(2) result.disc(3) result.distinct_disc(1) result.sel(1) snd_def)
  using assms(2) unfolding effect_def post_def
  by (metis (no_types, lifting) K.simps case_prod_beta case_sum_o_inj(2) result.case_eq_if result.disc(4)
      result.distinct_disc(5) surjective_sum)

(*
  reduce post to post2
*)
lemma post_true:
  assumes "effect (exc x) s r"
      and "I' s"
      and "post s r I (K True)"
    shows "post s r I I'"
  using assms unfolding post_def effect_def
  apply (auto simp add: execute_simps)
  unfolding exc_def apply (simp add:execute_simps)
  by (metis (mono_tags, lifting) ex.exhaust result.case_eq_if result.disc(4) result.disc(6) result.sel(2) snd_conv split_beta)

end

locale External = Contract +
  constrains this :: "'a::address"
  fixes external::"('d \<Rightarrow> 'a expression_monad) \<Rightarrow> ('a::address) expression_monad"
  assumes external_mono[mono]: "mono_sm (\<lambda>call. external call)"
begin

definition transfer_monad::
  "('d \<Rightarrow> 'a expression_monad) \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad"
("\<langle>transfer\<rangle>")  
where
  "transfer_monad call am vm = 
    do {
      ak \<leftarrow> am;
      av \<leftarrow> readValue ak;
      a  \<leftarrow> readAddress av;
      vk \<leftarrow> vm;
      vv \<leftarrow> readValue vk;
      v  \<leftarrow> readSint vv;
      assert Err (\<lambda>s. Balances s this \<ge> unat v);
      modify (\<lambda>s. balances_update this (Balances s this - unat v) s);
      modify (\<lambda>s. balances_update a (Balances s a + unat v) s);
      ecall (external call)
    }"

lemma transfer_mono[mono]:
  shows "monotone sm.le_fun sm_ord
     (\<lambda>f. transfer_monad f m n)"
  unfolding transfer_monad_def
  by (auto intro!: mono)

end

section \<open>Solidity\<close>

locale Solidity = Keccak256 + Method + External +
  constrains keccak256::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue"
         and msg_sender :: "'a::address"
         and this::"'a::address"
         and external::"('d \<Rightarrow> 'a expression_monad) \<Rightarrow> ('a::address) expression_monad"
begin
  definition init_balance:: "('a rvalue, ex, ('a::address) state) state_monad" where
    "init_balance = modify (\<lambda>s. balance_update (Balances s this + unat msg_value) s) \<bind> K (return Empty)"

  definition init_balance_np:: "('a rvalue, ex, ('a::address) state) state_monad" where
    "init_balance_np = modify (\<lambda>s. balance_update (Balances s this) s) \<bind> K (return Empty)"

end

section \<open>Arrays\<close>

definition array where "array i x = replicate i x"

lemma length_array[simp]: "length (array x y) = x"
  unfolding array_def
  by simp


lemma fold_map_write_replicate_length:
  assumes "fold_map Memory.write (replicate n (adata.Value v)) m = (x1, x2)"
    shows "length x1 = n"
  using assms
proof (induction n arbitrary: x1 m)
  case 0
  then show ?case by simp 
next
  case (Suc n)
  from Suc.prems obtain x1a
    where *: "fold_map Memory.write (replicate n (adata.Value v)) (m @ [mdata.Value v]) = (x1a, x2)"
      and **:"x1 = length m # x1a"
    by (auto simp add: array_def length_append_def split:prod.split_asm)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis using Suc.prems(1) by (auto split:prod.split_asm)
  next
    case False
    then show ?thesis using * Suc by (auto simp add: length_append_def)
  qed
qed

lemma fold_map_write_replicate_value:
  assumes "fold_map Memory.write (replicate n (adata.Value (Uint 0))) m = (x1, x2)"
      and "x < n"
    shows "x1 ! x < length x2 \<and> (\<exists>ix. x2 ! (x1 ! x) = mdata.Value (Uint ix))"
  using assms
proof (induction n arbitrary: x1 m x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems
    obtain x1a
      where *: "fold_map Memory.write (replicate n (adata.Value (Uint 0))) (m @ [mdata.Value (Uint 0)]) = (x1a, x2)"
        and **:"x1 = length m # x1a"
      by (simp add: length_append_def split:prod.split_asm)
  then show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis using Suc.prems(1,2) by (auto simp add: length_append_def)
  next
    case False
    then show ?thesis
    proof (cases "x = 0")
      case True
      moreover from False
        have "(replicate n (adata.Value (Uint 0))) \<noteq> []" by auto
      then have "sprefix (m @ [mdata.Value (Uint 0)]) x2"
        using write_fold_map_sprefix[of "(replicate n (adata.Value (Uint 0)))" " (m @ [mdata.Value (Uint 0)])"]
        unfolding sprefix_def using * by simp
      ultimately show ?thesis unfolding sprefix_def
        using ** sprefix_def by (auto simp add: array_def length_append_def split:prod.split_asm)
   next
      case _: False
      moreover have "x1a ! (x - 1) < length x2 \<and> (\<exists>ix. x2 ! (x1a ! (x - 1)) = mdata.Value (Uint ix))"
        using Suc.IH[OF *] Suc.prems(2) False by simp
      ultimately show ?thesis
        using * Suc.prems(1) by (auto simp add: length_append_def)
    qed
  qed
qed

lemma write_array_typing_value:
  assumes "Memory.write (adata.Array (array (unat si) (adata.Value (Uint 0)))) [] = (x1, x2)"
    shows "x1<length x2 \<and> (\<exists>ma0. x2 ! x1 = mdata.Array ma0 \<and> (\<forall>i<length ma0. (ma0 ! i) < length x2 \<and> (\<exists>ix. x2 ! (ma0 ! i) = mdata.Value (Uint ix))))"
proof -
  from assms obtain x1a x2a
    where *:"fold_map Memory.write (replicate (unat si) (adata.Value (Uint 0))) [] = (x1a, x2a)"
      and "x1 = length x2a"
      and "x2 = x2a @ [mdata.Array x1a]"
    by (simp add: array_def length_append_def split:prod.split_asm)
  moreover have "(\<forall>i<length x1a. (x1a ! i) < length x2a \<and> (\<exists>ix. x2 ! (x1a ! i) = mdata.Value (Uint ix)))"
  proof (rule allI, rule impI)
    fix i assume "i < length x1a"
    moreover have "length x1a = unat si" using fold_map_write_replicate_length[OF *] by simp
    ultimately show "(x1a ! i) < length x2a \<and> (\<exists>ix. x2 ! (x1a ! i) = mdata.Value (Uint ix))"
      using fold_map_write_replicate_value[OF *, of i]
      by (simp add: \<open>x2 = x2a @ [mdata.Array x1a]\<close> nth_append_left)
  qed
  ultimately show ?thesis by auto
qed

lemma mupdate_array_typing_value:
  assumes "state.Memory sa ! ml = mdata.Array ma0"
      and "\<forall>i<length ma0. (ma0 ! i) < length (state.Memory sa) \<and> (\<exists>ix. state.Memory sa ! (ma0 ! i) = mdata.Value (Uint ix))"
      and "mupdate [Uint xa] (ml, mdata.Value (Uint x), state.Memory sa) = Some yg"
    shows "\<exists>ma0. yg ! ml = mdata.Array ma0
          \<and> (\<forall>i<length ma0. (ma0 ! i) < length yg \<and> (\<exists>ix. yg ! (ma0 ! i) = mdata.Value (Uint ix)))"
proof -
  from assms have "ma0 ! unat xa \<noteq> ml"
  proof -
    from assms(1,2,3) obtain ix
      where "(ma0 ! (unat xa)) < length (state.Memory sa)"
        and "(state.Memory sa ! (ma0 ! (unat xa)) = mdata.Value (Uint ix))"
      by (auto simp add: case_memory_def nth_safe_def split:if_split_asm)
    then show ?thesis using assms(1) by auto
  qed
  then have "yg ! ml = mdata.Array ma0"
    using assms(1,3)
    by (auto simp add: case_memory_def nth_safe_def list_update_safe_def split:if_split_asm)
  moreover have "\<forall>i<length ma0. (ma0 ! i) < length yg \<and> (\<exists>ix. yg ! (ma0 ! i) = mdata.Value (Uint ix))"
  proof (rule allI, rule impI)
    fix i assume "i < length ma0"
    show "(ma0 ! i) < length yg \<and> (\<exists>ix. yg ! (ma0 ! i) = mdata.Value (Uint ix))"
    proof (cases "ma0 ! i = ma0 ! unat xa")
      case True
      then show ?thesis using assms(1,3) 
        by (auto simp add: case_memory_def nth_safe_def list_update_safe_def split:if_split_asm)
    next
      case False
      then show ?thesis using \<open>i < length ma0\<close> assms(1,2,3) 
        by (auto simp add: case_memory_def nth_safe_def list_update_safe_def split:if_split_asm)
    qed
  qed
  ultimately show ?thesis by blast
qed

section \<open>Declarations\<close>
(*
Used in ML code
*)
definition (in Contract) initStorage::"id \<Rightarrow> ('a::address valtype) storage_data \<Rightarrow> ('a::address) expression_monad" where
  "initStorage i v \<equiv> modify (\<lambda>s. storage_update i v s) \<bind> K (return Empty)"

definition kinit::"('a::address valtype) kdata \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
  "kinit v i \<equiv> modify (stack_update i v) \<bind> K (return Empty)"

definition init::"('a::address) valtype \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
  "init \<equiv> kinit \<circ> kdata.Value"

definition "write"::"('a::address valtype) adata \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
  "write c i \<equiv> update (\<lambda>s. let (l,m) = Memory.write c (state.Memory s) in (Empty, s\<lparr>Stack := fmupd i (kdata.Memory l) (Stack s), Memory := m\<rparr>))"

definition cinit::"('a::address valtype) call_data \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
  "cinit c i \<equiv> modify (calldata_update i c \<circ> stack_update i (kdata.Calldata (Some \<lparr>Location=i,Offset= []\<rparr>))) \<bind> K (return Empty)"

subsection \<open>Stack Variables\<close>

datatype VType =
  TBool | TSint | TAddress | TBytes nat \<comment> \<open>width should be restricted to [1..32]\<close>

subsection \<open>Default values\<close>

definition mapping where "mapping x = (\<lambda>_. x)"

fun default:: "VType \<Rightarrow> 'a::address valtype" where
   "default TBool = Bool False"
 | "default TSint = Uint 0"
 | "default TAddress = Address null"
 | "default (TBytes n) = Bytes (array n (CHR 0x00))"

definition decl::"VType \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad"
where
  "decl \<equiv> init \<circ> default"

(*
  This should be used in user code
*)
abbreviation decl'::"id \<Rightarrow> VType \<Rightarrow> ('a::address) expression_monad"
  ("(_ :: _)" [61, 61] 60)
where
  "decl' x y \<equiv> decl y x"

subsection \<open>Storage Variables\<close>

datatype SType =
  TValue VType | TArray nat SType | DArray SType | TMap SType SType | TEnum "SType list"

term "DArray (TValue (TBytes 1))"
ML \<open>
val it = \<^term>\<open>DArray (TValue (TBytes 1))\<close>
\<close>

fun sdefault:: "SType \<Rightarrow> 'a::address valtype storage_data" where
   "sdefault (TValue t) = storage_data.Value (default t)"
 | "sdefault (TArray l t) = storage_data.Array (array l (sdefault t))"
 | "sdefault (DArray t) = storage_data.Array []"
 | "sdefault (TMap _ t) = storage_data.Map (mapping (sdefault t))"
 | "sdefault (TEnum xs) = storage_data.Array []"

definition sinit::"id \<Rightarrow> ('a::address) expression_monad" where
  "sinit i \<equiv> modify (stack_update i (kdata.Storage None)) \<bind> K (return Empty)"

(*
  This should be used in user code
*)
fun sdecl::"SType \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
   "sdecl (TValue _) = K (throw Err)"
 | "sdecl _ = sinit"
declare sdecl.simps[simp del]

fun push where
  "push d (storage_data.Array xs) = Some (storage_data.Array (xs @@ d))"
| "push _ _ = None"

definition (in Contract) allocate::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address valtype) storage_data \<Rightarrow> ('a::address) expression_monad" where
  "allocate i es d =
    do {
      is \<leftarrow> lfold es;
      ar \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i) \<bind> push d);
      storage_update_monad [] is (K ar) i
    }"

subsection \<open>Calldata Variables\<close>

datatype CType =
  TValue VType | TArray nat CType | DArray CType | TEnum "CType list"

fun cdefault:: "CType \<Rightarrow> 'a::address valtype adata" where
   "cdefault (TValue t) = adata.Value (default t)"
 | "cdefault (TArray l t) = adata.Array (array l (cdefault t))"
 | "cdefault (DArray t) = adata.Array []"
 | "cdefault (TEnum xs) = adata.Array []"

subsection \<open>Memory Variables\<close>

(*
  This should be used in user code
*)
definition mdecl::"CType \<Rightarrow> id \<Rightarrow> ('a::address) expression_monad" where
  "mdecl = write \<circ> cdefault"

definition create_memory_array where
  "create_memory_array i t sm =
    do {
      s \<leftarrow> sm;
      (case s of
        rvalue.Value (Uint s') \<Rightarrow> write (adata.Array (array (unat s') (cdefault t))) i
      | _ \<Rightarrow> throw Err)
    }"

end