theory WP
imports Solidity "HOL-Eisbach.Eisbach"
begin

section "Weakest precondition calculus"

named_theorems wprules
named_theorems wperules
named_theorems wpdrules
named_theorems wpsimps

declare(in Contract) inv_state_def[wpsimps]
declare icall_def[wpsimps]
declare ecall_def[wpsimps]

method wp declares wprules wpdrules wperules wpsimps = (rule wprules | drule wpdrules | erule wperules | simp add: wpsimps)
method vcg declares wprules wpdrules wperules wpsimps = wp+

subsection "Simplification rules"

lemma mapping[wpsimps]:
  "mapping x y = x"
  unfolding mapping_def ..

lemma Value_vt[wpsimps]:
  assumes "storage_data.Value x = v"
    shows "storage_data.vt v = x"
  using assms by auto

subsubsection "Kdata"

lemma kdbool_simp[wpsimps]:
  "kdbool x = Value (Bool x)"
  unfolding kdbool_def by simp

lemma kdSint_simp[wpsimps]:
  "kdSint x = Value (Uint x)"
  unfolding kdSint_def by simp

lemma kdBytes_simp[wpsimps]:
  "kdBytes xs = Value (Bytes xs)"
  unfolding kdBytes_def by simp

lemma kdAddress_simp[wpsimps]:
  "kdAddress x = Value (Address x)"
  unfolding kdAddress_def by simp

lemma kdminus[wpsimps]:
  "kdminus (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l - r)))"
  unfolding kdminus_def vtminus_def by simp

lemma kdminus_safe[wpsimps]:
  assumes "r \<le> l"
  shows "kdminus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l - r)))"
  unfolding kdminus_safe_def using assms by (simp add: vtminus_safe.simps)

lemma kdminus_safe_dest[wpdrules]:
  assumes "kdminus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "r \<le> l \<and> ya = rvalue.Value (Uint (l - r))"
  using assms unfolding kdminus_safe_def by (simp split:if_split_asm add:vtminus_safe.simps)

lemma kdminus_storage[wpsimps]:
  "kdminus (rvalue.Storage x) z = None"
  unfolding kdminus_def vtminus_def by simp

lemma kdplus[wpsimps]:
  "kdplus (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l + r)))"
  unfolding kdplus_def vtplus_def by simp

lemma kdplus_safe[wpsimps]:
  assumes "unat l + unat r < 2^256"
  shows "kdplus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l + r)))"
  unfolding kdplus_safe_def using assms by (simp add:vtplus_safe.simps)

lemma kdplus_safe_dest[wpdrules]:
  assumes "kdplus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "unat l + unat r < 2^256 \<and> ya = rvalue.Value (Uint (l + r))"
  using assms unfolding kdplus_safe_def by (simp split:if_split_asm add:vtplus_safe.simps)

lemma kdmult[wpsimps]:
  "kdmult (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l * r)))"
  unfolding kdmult_def vtmult_def by simp

lemma kdmult_safe[wpsimps]:
  assumes "unat l * unat r < 2^256"
  shows "kdmult_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l * r)))"
  unfolding kdmult_safe_def using assms by (simp add:vtmult_safe.simps)

lemma kdmult_safe_dest[wpdrules]:
  assumes "kdmult_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "unat l * unat r < 2^256 \<and> ya = rvalue.Value (Uint (l * r))"
  using assms unfolding kdmult_safe_def by (simp split:if_split_asm add:vtmult_safe.simps)

subsubsection "Updates"

lemma stack_stack_update_diff[wpsimps]:
  assumes "i \<noteq> i'"
  shows "Stack (stack_update i x s) $$ i' = Stack s $$ i'"
  using assms unfolding stack_update_def by simp

lemma (in Contract) stack_storage_update[wpsimps]:
  "Stack (storage_update i x s) = Stack s"
  unfolding storage_update_def by simp

lemma stack_balances_update[wpsimps]:
  "Stack (balances_update i x s) = Stack s"
  unfolding balances_update_def by simp

lemma stack_calldata_update[wpsimps]:
  "Stack (calldata_update i x s) = Stack s"
  unfolding calldata_update_def by simp

lemma stack_update_eq[wpsimps]:
  "Stack (stack_update i x s) $$ i = Some x"
  unfolding stack_update_def by simp

lemma memory_balances_update[wpsimps]:
  "state.Memory (balances_update i x s) = state.Memory s"
  unfolding balances_update_def by simp

lemma memory_stack_update[wpsimps]:
  "state.Memory (stack_update i x s) = state.Memory s"
  unfolding stack_update_def by simp

lemma calldata_balances_update[wpsimps]:
  "state.Calldata (balances_update i x s) = state.Calldata s"
  unfolding balances_update_def by simp

lemma calldata_stack_update[wpsimps]:
  "state.Calldata (stack_update i x s) = state.Calldata s"
  unfolding stack_update_def by simp

lemma storage_stack_update[wpsimps]:
 "state.Storage (stack_update i v s) = state.Storage s"
  unfolding stack_update_def by simp

lemma storage_calldata_update[wpsimps]:
 "state.Storage (calldata_update i v s) = state.Storage s"
  unfolding calldata_update_def by simp

lemma storage_balances_update[wpsimps]:
 "state.Storage (balances_update i v s) = state.Storage s"
  unfolding balances_update_def by simp

lemma calldata_calldata_update[wpsimps]:
 "state.Calldata (calldata_update i v s) $$ i = Some v"
  unfolding calldata_update_def by simp

lemma calldata_calldata_update_neq[wpsimps]:
  assumes "i \<noteq> i'"
  shows "state.Calldata (calldata_update i v s) $$ i' = state.Calldata s $$ i'"
  using assms unfolding calldata_update_def by simp

lemma (in Contract) calldata_storage_update[wpsimps]:
 "state.Calldata (storage_update i v s) $$ i'  = state.Calldata s $$ i'"
 unfolding storage_update_def by simp
 
lemma (in Contract) storage_update_diff[wpsimps]:
  assumes "i \<noteq> i'"
  shows "state.Storage (storage_update i x s) this i' = state.Storage s this i'"
  using assms unfolding storage_update_def by simp

lemma (in Contract) storage_update_eq[wpsimps]:
  "state.Storage (storage_update i x s) this i = x"
  unfolding storage_update_def by simp

lemma (in Contract) balances_storage_update[wpsimps]:
  "Balances (storage_update i' x s) = Balances s"
  unfolding storage_update_def by simp

lemma balances_stack_update[wpsimps]:
  "Balances (stack_update i' x s) = Balances s"
  unfolding stack_update_def by simp

lemma balances_calldata_update[wpsimps]:
  "Balances (calldata_update i' x s) = Balances s"
  unfolding calldata_update_def by simp

lemma balances_balances_update_diff[wpsimps]:
  assumes "i \<noteq> i'"
  shows "Balances (balances_update i x s) i' = Balances s i'"
  using assms unfolding balances_update_def by simp

lemma balances_balances_update_same[wpsimps]:
  "Balances (balances_update i x s) i = x"
  unfolding balances_update_def by simp

lemma balances_update_balances[wpsimps]:
  "balances_update i (Balances s i) s = s"
  unfolding balances_update_def by simp

subsection "Destruction rules"

lemma some_some[wpdrules]:
  assumes "Some x = Some y"
  shows "x = y" using assms by simp

subsection "Weakest Precondition"

definition wp::"('a, 'b, 'c) state_monad \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> bool" where
  "wp f P E s \<equiv>
    (case execute f s of
      Normal (r,s') \<Rightarrow> P r s'
    | Exception (e,s') \<Rightarrow> E e s'
    | NT \<Rightarrow> True)"

lemma wpI:
  assumes "\<And>r s'. execute f s = Normal (r, s') \<Longrightarrow> P r s'"
      and "\<And>e s'. execute f s = Exception (e, s') \<Longrightarrow> E e s'"
    shows "wp f P E s"
  unfolding wp_def by (cases "execute f s" rule:result_cases) (simp_all add: assms)

lemma wpE:
  assumes "wp f P E s"
  obtains (1) r s' where "execute f s = Normal (r, s') \<and> P r s'"
        | (2) e s' where "execute f s = Exception (e, s') \<and> E e s'"
        | (3) "execute f s = NT"
  using assms unfolding wp_def by (cases "execute f s" rule:result_cases) simp_all

lemma wp_simp1:
  assumes "execute f s = Normal (r, s')"
    shows "wp f P E s = P r s'"
  unfolding wp_def by (cases "execute f s" rule:result_cases) (simp_all add: assms)

lemma wp_simp2:
  assumes "execute f s = Exception (e, s')"
    shows "wp f P E s = E e s'"
  unfolding wp_def by (cases "execute f s" rule:result_cases) (simp_all add: assms)

lemma wp_simp3:
  assumes "execute f s = NT"
    shows "wp f P E s"
  unfolding wp_def by (cases "execute f s" rule:result_cases) (simp_all add: assms)

lemma wp_if[wprules]:
  assumes "b \<Longrightarrow> wp a P E s"
      and "\<not> b \<Longrightarrow> wp c P E s"
  shows "wp (if b then a else c) P E s"
  using assms by simp

lemma wpreturn[wprules]: 
  assumes "P x s"
  shows "wp (return x) P E s"
  unfolding wp_def using assms by (simp add: execute_simps)

lemma wpget[wprules]: 
  assumes "P s s"
  shows "wp get P E s"
  unfolding wp_def using assms by (simp add: execute_simps)

lemma wpbind[wprules]:
  assumes "wp f (\<lambda>a. (wp (g a) P E)) E s"
  shows "wp (f \<bind> g) P E s"
proof (cases "execute f s")
  case nf: (n a s')
  then have **:"wp (g a) P E s'" using wp_def[of f "\<lambda>a. wp (g a) P E"] assms by simp
  show ?thesis
  proof (cases "execute (g a) s'")
    case ng: (n a' s'')
    then have "P a' s''" using wp_def[of "g a" P] ** by simp
    moreover from nf ng have "execute (f \<bind> g) s = Normal (a', s'')" by (simp add: execute_simps)
    ultimately show ?thesis using wp_def by fastforce
  next
    case (e e s'')
    then have "E e s''" using wp_def[of "g a" P] ** by simp
    moreover from nf e have "execute (f \<bind> g) s = Exception (e, s'')" by (simp add: execute_simps)
    ultimately show ?thesis using wp_def by fastforce
  next
    case t
    with nf have "execute (f \<bind> g) s = NT" by (simp add: execute_simps)
    then show ?thesis using wp_def by fastforce
  qed
next
  case (e e s')
  then have "E e s'" using wp_def[of f "\<lambda>a. wp (g a) P E"] assms by simp
  moreover from e have "execute (f \<bind> g) s = Exception (e, s')" by (simp add: execute_simps)
  ultimately show ?thesis using wp_def by fastforce
next
  case t
  then have "execute (f \<bind> g) s = NT" by (simp add: execute_simps)
  then show ?thesis using wp_def by fastforce
qed

lemma wpthrow[wprules]:
  assumes "E x s"
  shows "wp (throw x) P E s"
  unfolding wp_def using assms by (simp add: execute_simps)

lemma wp_lfold:
  assumes "P [] s"
  assumes "\<And>a list. xs = a#list \<Longrightarrow> wp (a \<bind> (\<lambda>l. option Err (\<lambda>_. the_value l) \<bind> (\<lambda>l'. lfold list \<bind> (\<lambda>ls. return (l' # ls))))) P E s"
  shows "wp (lfold xs) P E s"
  using assms  unfolding wp_def
  apply (cases xs)
  by (simp_all add: execute_simps)

lemma wp_lfold1:
  assumes "P [] s"
  shows "wp (lfold []) P E s"
  using assms  unfolding wp_def
  by (simp_all add: execute_simps)

lemma wp_lfold2:
  assumes "xs = a#list"
  assumes "wp (a \<bind> (\<lambda>l. option Err (\<lambda>_. the_value l) \<bind> (\<lambda>l'. lfold list \<bind> (\<lambda>ls. return (l' # ls))))) P E s"
  shows "wp (lfold xs) P E s"
  using assms  unfolding wp_def
  apply (cases xs)
  by (simp_all add: execute_simps)

lemma result_cases2[cases type: result]:
  fixes x :: "('a \<times> 's, 'e \<times> 's) result"
  obtains (n) a s e where "x = Normal (a, s) \<or> x = Exception (e, s)"
        | (t) "x = NT"
proof (cases x)
  case (n a s)
  then show ?thesis using that by simp
next
  case (e e)
  then show ?thesis using that by fastforce
next
  case t
  then show ?thesis using that by simp
qed

lemma wpmodify[wprules]:
  assumes "P () (f s)"
  shows "wp (modify f) P E s"
  unfolding wp_def using assms by (simp add: execute_simps)

lemma wpnewStack[wprules]:
  assumes "P Empty (s\<lparr>Stack := {$$}\<rparr>)"
  shows "wp newStack P E s"
  unfolding wp_def newStack_def using assms by (simp add: execute_simps)

lemma wpnewMemory[wprules]:
  assumes "P Empty (s\<lparr>Memory := []\<rparr>)"
  shows "wp newMemory P E s"
  unfolding wp_def newMemory_def using assms by (simp add: execute_simps)

lemma wpnewCalldata[wprules]:
  assumes "P Empty (s\<lparr>Calldata := {$$}\<rparr>)"
  shows "wp newCalldata P E s"
  unfolding wp_def newCalldata_def using assms by (simp add: execute_simps)

lemma wp_lift_op_monad:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (op a rv)) \<bind> return)) P E) E s"
  shows "wp (lift_op_monad op lm rm) P E s"
  unfolding lift_op_monad_def using assms by (rule wprules)

lemma wp_equals_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdequals a rv)) \<bind> return)) P E) E s"
  shows "wp (equals_monad lm rm) P E s"
  unfolding equals_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_less_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdless a rv)) \<bind> return)) P E) E s"
  shows "wp (less_monad lm rm) P E s"
  unfolding less_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_mod_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdmod a rv)) \<bind> return)) P E) E s"
  shows "wp (mod_monad lm rm) P E s"
  unfolding mod_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_minus_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdminus a rv)) \<bind> return)) P E) E s"
  shows "wp (minus_monad lm rm) P E s"
  unfolding minus_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_minus_monad_safe[wprules]:
  assumes " wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdminus_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (minus_monad_safe lm rm) P E s"
  unfolding minus_monad_safe_def using assms by (rule wp_lift_op_monad)

lemma wp_plus_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdplus a rv)) \<bind> return)) P E) E s"
  shows "wp (plus_monad lm rm) P E s"
  unfolding plus_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_plus_monad_safe[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdplus_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (plus_monad_safe lm rm) P E s"
  unfolding plus_monad_safe_def using assms by (rule wp_lift_op_monad)

lemma wp_mult_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdmult a rv)) \<bind> return)) P E) E s"
  shows "wp (mult_monad lm rm) P E s"
  unfolding mult_monad_def using assms by (rule wp_lift_op_monad)

lemma wp_mult_monad_safe[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdmult_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (mult_monad_safe lm rm) P E s"
  unfolding mult_monad_safe_def using assms by (rule wp_lift_op_monad)

lemma wp_bool_monad[wprules]:
  assumes "P (kdbool b) s"
  shows "wp (bool_monad b) P E s"
  unfolding bool_monad_def using assms by (simp add: wprules)

lemma (in Solidity)  wp_bytes_monad[wprules]:
  assumes "P ( kdBytes Bytes0) s"
    shows "wp (bytes_monad2 Bytes0) P E s"
  unfolding bytes_monad2_def  using assms by (simp add: wprules)

lemma wp_true_monad[wprules]:
  assumes "P (kdbool True) s"
  shows "wp true_monad P E s"
  unfolding true_monad_def using assms by (rule wp_bool_monad)

lemma wp_false_monad[wprules]:
  assumes "P (kdbool False) s"
  shows "wp false_monad P E s"
  unfolding false_monad_def using assms by (rule wp_bool_monad)

lemma wp_or_monad[wprules]:
  assumes "wp l (\<lambda>a. wp (r \<bind> (\<lambda>rv. option Err (K (lift_value_binary vtor a rv)) \<bind> return)) P E) E s"
  shows "wp (or_monad l r) P E s"
  unfolding or_monad_def kdor_def using assms by (rule wp_lift_op_monad)

lemma wp_sint_monad[wprules]:
  assumes "P (kdSint x) s"
  shows "wp (sint_monad x) P E s"
  unfolding sint_monad_def using assms by (simp add: wprules)

lemma wp_bytest_monad[wprules]:
  assumes "P (kdBytes x) s" "n = length x" "n \<in> {1..<33}"
  shows "wp (bytes_monad n x) P E s"
  unfolding bytes_monad_def using assms by (simp add: wprules)

lemma (in Method) wp_value_monad[wprules]:
  assumes "P (kdSint msg_value) s"
  shows "wp value_monad P E s"
  unfolding value_monad_def using assms by (rule wp_sint_monad)

lemma (in Method) wp_stamp_monad[wprules]:
  assumes "P (kdSint timestamp) s"
  shows "wp block_timestamp_monad P E s"
  unfolding block_timestamp_monad_def using assms by (rule wp_sint_monad)
             
lemma wp_cond_monad[wprules]:
  assumes "wp bm (\<lambda>a. wp (true_monad \<bind> (\<lambda>rv. option Err (K (kdequals a rv)) \<bind> return)) (\<lambda>a. wp (if a = kdbool True then mt else if a = kdbool False then fm else throw Err) P E) E) E s"
  shows "wp (cond_monad bm mt fm) P E s"
  unfolding cond_monad_def
  apply (rule wprules)+ by (rule assms)

lemma wp_and_monad[wprules]:
  assumes "wp (m1 \<bind> (\<lambda>v. m2 \<bind> (\<lambda>va. option Err (K (lift_value_binary (lift_bool_binary (\<and>)) v va))))) P E s"
  shows "wp ( m1 \<langle>\<and>\<rangle> m2 ) P E s"
  unfolding and_monad_def lift_op_monad_def kdand_def vtand_def
  using assms
  by (simp add:wpsimps)

lemma wp_assert_monad[wprules]:
  assumes "wp (Solidity.cond_monad bm (return Empty) (throw Err)) P E s"
  shows "wp (assert_monad bm) P E s"
  unfolding assert_monad_def
  using assms by simp

lemma wpoption[wprules]:
  assumes "\<And>y. f s = Some y \<Longrightarrow> P y s"
      and "f s = None \<Longrightarrow> E x s"
    shows "wp (option x f) P E s"
proof (cases "f s")
  case None
  then show ?thesis unfolding option_def wp_def using assms(2) by (simp add:execute_simps)
next
  case (Some a)
  then show ?thesis unfolding option_def wp_def using assms(1) by (simp add:execute_simps)
qed

lemma wp_lift_unary_monad:
  assumes "wp lm (\<lambda>a. wp (option Err (K (op a)) \<bind> return) P E) E s"
  shows "wp (lift_unary_monad op lm) P E s"
  unfolding lift_unary_monad_def apply (rule wprules)+ by (rule assms)

lemma wp_not_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (option Err (K (kdnot a)) \<bind> return) P E) E s"
  shows "wp (not_monad lm) P E s"
  unfolding not_monad_def using assms by (rule wp_lift_unary_monad)

lemma wp_address_monad[wprules]:
  assumes "P (kdAddress a) s"
  shows "wp (address_monad a) P E s"
  unfolding address_monad_def by (simp add: wprules assms)

lemma(in Method) wp_sender_monad[wprules]:
  assumes "P (kdAddress msg_sender) s"
  shows "wp sender_monad P E s"
  unfolding sender_monad_def using assms by (rule wp_address_monad)

lemma wp_require_monad[wprules]:
  assumes "wp (x \<bind> (\<lambda>v. if v = rvalue.Value (Bool True) then return Empty else throw Err)) P E s"
  shows "wp (require_monad x) P E s"
  unfolding require_monad_def using assms by (simp add:wpsimps)

lemma (in Contract) wp_storeLookup[wprules]:
  assumes "wp (lfold es)
     (\<lambda>a. wp (option Err (\<lambda>s. slookup a (state.Storage s this i)) \<bind>
              (\<lambda>sd. if storage_data.is_Value sd then return (rvalue.Value (storage_data.vt sd)) else return (rvalue.Storage (Some \<lparr>Location=i, Offset= a\<rparr>))))
           P E)
     E s"
    shows "wp (storeLookup i es) P E s"
  unfolding storeLookup_def by (rule wprules | auto simp add: assms split:if_split)+

lemma wpassert[wprules]:
  assumes "t s \<Longrightarrow> wp (return ()) P E s"
      and "\<not> t s \<Longrightarrow> wp (throw x) P E s"
    shows "wp (assert x t) P E s"
  unfolding wp_def apply (cases "execute (assert x t) s") apply (auto simp add: execute_simps)
  apply (metis assms(1) assms(2) execute_assert(1) execute_assert(2) wp_simp1)
  by (metis assms(1) assms(2) execute_assert(1) execute_assert(2) wp_simp2)

lemma wp_bool[wprules]:
  "wp (bool_monad b) (\<lambda>a _. a = kdbool b) (K x) s"
  unfolding bool_monad_def
  by (simp add: wprules)


lemma wpskip[wprules]: 
  assumes "P Empty s"
  shows "wp skip_monad P E s"
  unfolding skip_monad_def using assms by vcg

lemma effect_bind:
  assumes "effect (m \<bind> (\<lambda>x. n x)) ss r"
      and "execute m ss = Normal (a2, s)"
    shows "effect (n a2) s r"
  using assms unfolding cond_monad_def effect_def bind_def execute_create by simp

lemma effect_cond_monad:
  assumes "effect (Solidity.cond_monad c mt mf) ss r"
      and "execute (equals_monad c true_monad) ss = Normal (kdbool True, s)"
    shows "effect mt s r"
  using assms unfolding cond_monad_def
  by (metis (no_types, lifting) assms(1) execute_cond_monad_simp1 effect_def)

lemma wpwhile:
  assumes "\<And>s. iv s
            \<Longrightarrow> wp (equals_monad c true_monad)
                   (\<lambda>a s. (a = kdbool True \<longrightarrow> wp m (K iv) E s) \<and>
                          (a = kdbool False \<longrightarrow> P Empty s) \<and>
                          (a \<noteq> kdbool False \<and> a \<noteq> kdbool True \<longrightarrow> E Err s))
                E s"
      and "iv s"
    shows "wp (while_monad c m) P E s"
proof (cases "execute (while_monad c m) s" rule: result_cases2)
  case (n a s' ex)
  then obtain r where effect_while:"effect (while_monad c m) s r" unfolding effect_def by auto
  show ?thesis using assms
  proof (induction rule: while_monad.raw_induct[OF _ effect_while])
    case a: (1 while_monad' c m ss sn)
    have "wp (cond_monad c (bind m (K (while_monad c m))) (return Empty)) P E ss"
    proof (rule wpI)
      fix a s'
      assume "execute (cond_monad c (bind m (K (while_monad c m))) (return Empty)) ss = Normal (a, s')"
      then show "P a s'"
      proof (rule execute_cond_monad_normal_E)
        fix s''
        assume "execute (equals_monad c true_monad) ss = Normal (kdbool True, s'')"
        and "execute (m \<bind> K (while_monad c m)) s'' = Normal (a, s')"
        then have execute_equals: "execute (equals_monad c true_monad) ss = Normal (kdbool True, s'')"
        and "execute (m \<bind> K (while_monad c m)) s'' = Normal (a, s')" by simp+
        from this(2) show "P a s'"
        proof (rule execute_bind_normal_E)
          fix s''' x
          assume execute_m: "execute m s'' = Normal (x, s''')"
          and execute_while: "execute (K (while_monad c m) x) s''' = Normal (a, s')"
          moreover from a(3)[OF a(4)] have "wp m (K iv) E s''" using execute_equals unfolding wp_def by simp
          ultimately have "iv s'''" unfolding wp_def by (cases "execute m s''") (simp)+
          moreover from a(2) obtain sn where "effect (while_monad' c m) s''' sn"
          proof -
            from effect_cond_monad[OF a(2) execute_equals]
            have "effect (m \<bind> K (while_monad' c m)) s'' sn" by simp
            with effect_bind show ?thesis using that execute_m by fastforce
          qed
          ultimately have "wp (while_monad c m) P E s'''" using a(1)[OF _ a(3), where ?h=s'''] by simp
          with execute_while show "P a s'" unfolding wp_def by simp
        qed
      next
        fix s''
        assume execute_equals: "execute (equals_monad c true_monad) ss = Normal (kdbool False, s'')"
        and "execute (return Empty) s'' = Normal (a, s')"
        then have "s'' = s'" using execute_returnE by meson
        moreover from a(3)[OF a(4)] have "P Empty s''" using execute_equals unfolding wp_def by simp
        ultimately show "P a s'" by (metis \<open>execute (return Empty) s'' = Normal (a, s')\<close> execute_returnE(1))
      qed
    next
      fix x s'
      assume "execute (Solidity.cond_monad c (m \<bind> K (while_monad c m)) (return Empty)) ss = Exception (x, s')"
      then show "E x s'"
      proof (rule execute_cond_monad_exception_E)
        assume "execute (equals_monad c true_monad) ss = Exception (x, s')"
        then show "E x s'" using a(3)[OF a(4)] unfolding wp_def by simp
      next
        fix a
        assume "execute (equals_monad c true_monad) ss = Normal (a, s')"
        and "a \<noteq> kdbool True \<and> a \<noteq> kdbool False \<and> x = Err"
        then show "E x s'" using a(3)[OF a(4)] unfolding wp_def by simp
      next
        fix s''
        assume execute_equals: "execute (equals_monad c true_monad) ss = Normal (kdbool True, s'')"
        and "execute (m \<bind> K (while_monad c m)) s'' = Exception (x, s')"
        then have "execute (m \<bind> K (while_monad c m)) s'' = Exception (x, s')" by simp
        then show "E x s'"
        proof (rule execute_bind_exception_E)
          assume "execute m s'' = Exception (x, s')"
          then show "E x s'" using a(3)[OF a(4)] execute_equals unfolding wp_def by simp
        next
          fix a s'''
          assume execute_m: "execute m s'' = Normal (a, s''')"
          and execute_while:"execute (K (while_monad c m) a) s''' = Exception (x, s')"
          moreover from a(3)[OF a(4)] have "wp m (K iv) E s''" using execute_equals unfolding wp_def by simp
          ultimately have "iv s'''" unfolding wp_def by (cases "execute m s''") (simp)+
          moreover from a(2) obtain sn where "effect (while_monad' c m) s''' sn"
          proof -
            from effect_cond_monad[OF a(2) execute_equals]
            have "effect (m \<bind> K (while_monad' c m)) s'' sn" by simp
            with effect_bind show ?thesis using that execute_m by fastforce
          qed
          ultimately have "wp (while_monad c m) P E s'''" using a(1)[OF _ a(3), where ?h=s'''] by simp
          with execute_while show "E x s'" unfolding wp_def by simp
        qed
      next
        fix s''
        assume "execute (equals_monad c true_monad) ss = Normal (kdbool False, s'')"
        and "execute (return Empty) s'' = Exception (x, s')"
        then show "E x s'" by (simp add:execute_return)
      qed
    qed
    then show "wp (while_monad c m) P E ss" by (subst while_monad.simps)
  qed
next
  case t
  then show ?thesis unfolding wp_def by simp
qed

lemma wp_applyf[wprules]:
  assumes "P (f s) s"
  shows "wp (applyf f) P E s"
  unfolding applyf_def get_def return_def wp_def using assms by (auto simp add:wpsimps execute_simps)

lemma wp_case_option[wprules]:
  assumes "x = None \<Longrightarrow> wp a P E s"
      and "\<And>a. x = Some a \<Longrightarrow> wp (b a) P E s"
  shows "wp (case x of None \<Rightarrow> a | Some x \<Rightarrow> b x) P E s"
  unfolding wp_def apply (cases x, auto) apply (fold wp_def) by (simp add:assms)+

lemma wp_case_kdata[wprules]:
  assumes "\<And>x1. a = kdata.Storage x1 \<Longrightarrow> wp (S x1) P E s"
      and "\<And>x2. a = kdata.Memory x2 \<Longrightarrow> wp (M x2) P E s"
      and "\<And>x3. a = kdata.Calldata x3 \<Longrightarrow> wp (C x3) P E s"
      and "\<And>x4. a = kdata.Value x4 \<Longrightarrow> wp (V x4) P E s"
  shows "wp (case a of kdata.Storage p \<Rightarrow> S p | kdata.Memory l \<Rightarrow> M l | kdata.Calldata p \<Rightarrow> C p | kdata.Value x \<Rightarrow> V x) P E s"
  unfolding wp_def apply (cases a, auto) apply (fold wp_def) by (simp add:assms)+

lemma wp_init[wprules]:
  assumes "P Empty (stack_update i (kdata.Value v) s)"
  shows "wp (init v i) P E s"
  unfolding init_def wp_def kinit_def using assms by(auto simp add:wpsimps execute_simps)

lemma wp_decl[wprules]:
  assumes "wp (init (Solidity.default t) i) P E s"
  shows "wp (decl t i) P E s"
  unfolding decl_def using assms by simp

lemma wp_write[wprules]:
  assumes "\<And>x1 x2.
       Memory.write c (state.Memory s) = (x1, x2) \<Longrightarrow>
       P Empty (s\<lparr>Stack := Stack s(i $$:= kdata.Memory x1), Memory := x2\<rparr>)"
    shows "wp (write c i) P E s"
  unfolding write_def wp_def using assms by (auto simp add:wpsimps execute_simps split: prod.split)

lemma wp_sinit[wprules]:
  assumes "P Empty (stack_update i (kdata.Storage None) s)"
  shows "wp (sinit i) P E s"
  unfolding sinit_def wp_def using assms by (auto simp add:wpsimps execute_simps)

lemma wp_sdecl[wprules]:
  assumes "\<And>x51 x52. t = SType.TArray x51 x52 \<Longrightarrow> wp (sinit i) P E s"
      and "\<And>x6. t = SType.DArray x6 \<Longrightarrow> wp (sinit i) P E s"
      and "\<And>x71 x72. t = SType.TMap x71 x72 \<Longrightarrow> wp (sinit i) P E s"
      and "\<And>x8. t = SType.TEnum x8 \<Longrightarrow> wp (sinit i) P E s"
      and "\<And>x. t = SType.TValue x \<Longrightarrow> E Err s"
  shows "wp (sdecl t i) P E s"
  unfolding wp_def apply (case_tac t) using assms by (auto simp add:wpsimps sdecl.simps execute_simps wp_def)

lemma (in Contract) wp_initStorage[wprules]:
  assumes "P Empty (storage_update i v s)"
  shows "wp (initStorage i v) P E s"
  unfolding initStorage_def wp_def using assms by(auto simp add:wpsimps execute_simps)

lemma (in Solidity) wp_init_balance[wprules]:
  assumes "P Empty (balance_update (Balances s this + unat msg_value) s)"
  shows "wp init_balance P E s"
  unfolding init_balance_def wp_def using assms by (auto simp add:wpsimps execute_simps)

lemma (in Solidity) wp_init_balance_np[wprules]:
  assumes "P Empty (balance_update (Balances s this) s)"
  shows "wp init_balance_np P E s"
  unfolding init_balance_np_def wp_def using assms by (auto simp add:wpsimps execute_simps)

lemma (in Solidity) wp_cinit[wprules]:
  assumes "P Empty (calldata_update i c (stack_update i (kdata.Calldata (Some \<lparr>Location = i, Offset = []\<rparr>)) s))"
  shows "wp (cinit (c:: 'a valtype call_data) i) P E s"
  unfolding cinit_def  wp_def using assms by (auto simp add:wpsimps execute_simps)

lemma (in Contract) wp_assign_stack_monad[wprules]:
  assumes "wp m (\<lambda>a. wp (lfold is \<bind> (\<lambda>is. assign_stack i is a \<bind> (\<lambda>_. return Empty))) P E) E s"
  shows "wp (assign_stack_monad i is m) P E s"
  unfolding assign_stack_monad_def apply (rule wprules) using assms by simp

lemma (in Contract) wp_storage_update_monad[wprules]:
  assumes "\<And>y. updateStore (xs @ is) sd (state.Storage s this p) = Some y \<Longrightarrow> P Empty (storage_update p y s)"
      and "updateStore (xs @ is) sd (state.Storage s this p) = None \<Longrightarrow> E Err s"
  shows "wp (storage_update_monad xs is sd p) P E s"
  unfolding storage_update_monad_def by (rule wprules | simp add: assms)+

lemma (in Contract) wp_assign_storage1[wperules]:
  assumes "y = rvalue.Value v"
      and "wp (storage_update_monad [] is (K (storage_data.Value v)) i) P E s"
    shows "wp (assign_storage i is y) P E s"
  using assms by simp

lemma (in Contract) wp_assign_storage2[wprules]:
  assumes "wp (storage_update_monad [] is (K (storage_data.Value v)) i) P E s"
    shows "wp (assign_storage i is (rvalue.Value v)) P E s"
  using assms by simp

lemma (in Contract) wp_assign_storage_monad[wprules]:
  assumes "wp m (\<lambda>a. wp (lfold is \<bind> (\<lambda>is. assign_storage i is a)) P E) E s"
  shows "wp (assign_storage_monad i is m) P E s"
  unfolding assign_storage_monad_def apply (rule wprules) using assms by simp

lemma (in Contract) wp_stackLookup[wprules]:
  assumes "wp (lfold es)
     (\<lambda>a. wp (stack_check x (\<lambda>k. return (rvalue.Value k))
                (\<lambda>p. option Err (\<lambda>s. mlookup (state.Memory s) a p) \<bind>
                      (\<lambda>l. option Err (\<lambda>s. state.Memory s $ l) \<bind>
                            (\<lambda>md. if mdata.is_Value md then return (rvalue.Value (mdata.vt md))
                                   else return (rvalue.Memory l))))
                (\<lambda>p xs.
                    option Err (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs @ a)) \<bind>
                    (\<lambda>sd. if call_data.is_Value sd then return (rvalue.Value (call_data.vt sd))
                           else return (rvalue.Calldata (Some \<lparr>Location = p, Offset = xs @ a\<rparr>))))
                (return (rvalue.Calldata None))
                (\<lambda>p xs.
                    option Err (\<lambda>s. slookup (xs @ a) (state.Storage s this p)) \<bind>
                    (\<lambda>sd. if storage_data.is_Value sd then return (rvalue.Value (storage_data.vt sd))
                           else return (rvalue.Storage (Some \<lparr>Location = p, Offset = xs @ a\<rparr>))))
                (return (rvalue.Storage None)))
            P E)
     E s"
  shows "wp (stackLookup x es) P E s"
  unfolding stackLookup_def apply (vcg) using assms by simp

lemma (in Keccak256) wp_keccak256[wprules]:
  assumes "wp m (\<lambda>a. wp (return (keccak256 a)) P E) E s"
  shows "wp (keccak256_monad m) P E s"
  unfolding keccak256_monad_def using assms by (rule wprules)+

lemma (in Keccak256) wp_encodeABI[wprules]:
  assumes "wp (mfold m) (\<lambda>a. wp (return (encodeABI a)) P E) E s"
  shows "wp (encodeABI_monad m) P E s"
  unfolding encodeABI_monad_def using assms by (rule wprules)+ 

lemma (in External) wp_transfer_monad[wprules]:
  assumes " wp am
     (\<lambda>a. wp (readValue a \<bind>
               (\<lambda>av. readAddress av \<bind>
                      (\<lambda>a. vm \<bind>
                            (\<lambda>vk. readValue vk \<bind>
                                   (\<lambda>vv. readSint vv \<bind>
                                          (\<lambda>v.
assert Err (\<lambda>s. unat v \<le> Balances s this) \<bind>
(\<lambda>_. modify (\<lambda>s. balance_update (Balances s this - unat v) s) \<bind>
      (\<lambda>_. modify (\<lambda>s. balances_update a (Balances s a + unat v) s) \<bind>
            (\<lambda>_. ecall (external call))))))))))
            P E)
     E s"
  shows "wp (transfer_monad call am vm) P E s"
  unfolding transfer_monad_def apply (rule wprules)+ by (rule assms)

lemma wp_readValue[wprules]:
  assumes "P (storage_data.vt yp) s"
  shows "wp (readValue (rvalue.Value (storage_data.vt yp))) P E s"
  unfolding wp_def readValue.simps by (simp add:execute_return assms)

lemma wp_readAddress[wprules]:
  assumes "P yp s"
  shows "wp (readAddress (Address yp)) P E s"
  unfolding wp_def readAddress.simps by (simp add:execute_return assms)

lemma wp_stackCheck[wprules]:
  assumes "\<And>p. Stack s $$ i = Some (kdata.Storage (Some p)) \<Longrightarrow> wp (sf (Location p) (Offset p)) P E s"
      and "\<And>l. Stack s $$ i = Some (kdata.Memory l) \<Longrightarrow> wp (mf l) P E s"
      and "\<And>p. Stack s $$ i = Some (kdata.Calldata (Some p)) \<Longrightarrow> wp (cf (Location p) (Offset p)) P E s"
      and "\<And>v. Stack s $$ i = Some (kdata.Value v) \<Longrightarrow> wp (kf v) P E s"
      and "Stack s $$ i = None \<Longrightarrow> E Err s"
      and "Stack s $$ i = Some (kdata.Storage None) \<Longrightarrow> wp sp P E s"
      and "Stack s $$ i = Some (kdata.Calldata None) \<Longrightarrow> wp cp P E s"
    shows "wp (stack_check i kf mf cf cp sf sp) P E s"
  unfolding wp_def stack_check_def
  apply (simp add:execute_simps applyf_def get_def return_def bind_def)
  apply (cases "Stack s $$ i")
  apply (auto simp add:execute_simps)
  defer apply (case_tac a)
  apply (fold wp_def) using assms
  by (auto simp add:wprules)

lemma execute_normal:
  assumes "execute x s = Normal (a, b)"
  shows "effect x s (Inl (a,b))" using assms unfolding effect_def by simp

lemma execute_exception:
  assumes "execute x s = Exception (a, b)"
  shows "effect x s (Inr (a,b))" using assms unfolding effect_def by simp

lemma (in Contract) inv_wp:
  assumes "effect m s r"
      and "wp m (K x) (K y) s"
    shows "inv r x y"
  using assms unfolding inv_def effect_def wp_def apply (cases "execute m s") by auto

lemma (in Contract) post_wp:
  assumes "effect m s r"
      and "wp m (\<lambda>r s'. Is s r s') (K Ie) s"
    shows "post s r Is Ie"
  using assms unfolding post_def effect_def wp_def apply (cases "execute m s") by auto

lemma (in Contract) wp_storeArrayLength[wprules]:
  assumes "wp (lfold xs)
     (\<lambda>a. wp (option Err (\<lambda>s. slookup a (state.Storage s this v)) \<bind>
              (\<lambda>sd. storage_check sd (K (throw Err)) (\<lambda>sa. return (rvalue.Value (Uint (word_of_nat (length (storage_data.ar sd)))))) (K (throw Err))))
           P E)
     E s"
  shows "wp (storeArrayLength v xs) P E s"
  unfolding storeArrayLength_def apply vcg using assms by simp

lemma (in Contract) wp_storeArrayLengthSafe[wprules]:
  assumes "wp (lfold xs)
     (\<lambda>a. wp (option Err (\<lambda>s. slookup a (state.Storage s this v)) \<bind>
              (\<lambda>sd. storage_check sd (K (throw Err))
                     (\<lambda>sa. if length (storage_data.ar sd) < 2 ^ 256
                           then return (rvalue.Value (Uint (word_of_nat (length (storage_data.ar sd))))) else throw Err)
                     (K (throw Err))))
           P E)
     E s"
  shows "wp (storeArrayLengthSafe v xs) P E s"
  unfolding storeArrayLengthSafe_def apply vcg using assms by simp

lemma (in Contract) wp_arrayLength[wprules]:
  assumes "wp (lfold xs)
     (\<lambda>a. wp (stack_check v (K (throw Err))
                (\<lambda>p. option Err (\<lambda>s. mlookup (state.Memory s) a p) \<bind>
                      (\<lambda>l. option Err (\<lambda>s. state.Memory s $ l) \<bind>
                            (\<lambda>md. if mdata.is_Array md
                                   then return (rvalue.Value (Uint (word_of_nat (length (mdata.ar md))))) else throw Err)))
                (\<lambda>p xs.
                    option Err (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs @ a)) \<bind>
                    (\<lambda>sd. if call_data.is_Array sd then return (rvalue.Value (Uint (word_of_nat (length (call_data.ar sd)))))
                           else throw Err))
                (throw Err)
                (\<lambda>p xs.
                    option Err (\<lambda>s. slookup (xs @ a) (state.Storage s this p)) \<bind>
                    (\<lambda>sd. if storage_data.is_Array sd then return (rvalue.Value (Uint (word_of_nat (length (storage_data.ar sd)))))
                           else throw Err))
                (throw Err))
            P E)
     E s"
  shows "wp (arrayLength v xs) P E s"
  unfolding arrayLength_def apply vcg using assms by simp

lemma (in Contract) wp_storearrayLength[wprules]:
  assumes "slookup [] (state.Storage s this STR ''proposals'') = None \<Longrightarrow> E Err s"
 and "wp (storage_check (state.Storage s this STR ''proposals'') (K (throw Err))
         (\<lambda>sa. return (rvalue.Value (Uint (word_of_nat (length (storage_data.ar (state.Storage s this STR ''proposals''))))))) (K (throw Err)))
     P E s"
  shows "wp (storeArrayLength STR ''proposals'' []) P E s"
  unfolding storeArrayLength_def apply vcg using assms apply simp apply vcg done

lemma (in Contract) wp_storage_check[wprules]:
  assumes "\<And>v. sd = storage_data.Value v \<Longrightarrow> wp (vf v) P E s"
     and "\<And>a. sd = storage_data.Array a \<Longrightarrow> wp (af a) P E s"
     and "\<And>m. sd = storage_data.Map m \<Longrightarrow> wp (mf m) P E s"
  shows "wp (storage_check sd vf af mf) P E s"
  using assms apply (cases sd) by (simp add:wpsimps)+

lemma (in Contract) wp_allocate[wprules]:
  assumes "wp (lfold es)
     (\<lambda>a. wp (option Err (\<lambda>s. slookup a (state.Storage s this i) \<bind> push d) \<bind>
              (\<lambda>ar. storage_update_monad [] a (K ar) i))
           P E)
     E s"
  shows "wp (allocate i es d) P E s"
  unfolding allocate_def apply vcg using assms by simp

lemma (in Contract) wp_create_memory_array[wprules]:
  assumes "wp sm
     (\<lambda>a. wp (case a of
              rvalue.Value (Uint s') \<Rightarrow>
                Solidity.write (adata.Array (array (unat s') (cdefault t))) i
              | rvalue.Value _ \<Rightarrow> throw Err | _ \<Rightarrow> throw Err)
           P E)
     E s"
  shows "wp (create_memory_array i t sm) P E s"
  unfolding create_memory_array_def apply vcg using assms by simp

text \<open>
  Using postconditions for WP
\<close>
lemma (in Solidity) wp_post:
  assumes "(\<And>r. effect (c x) s r \<Longrightarrow> post s r P' (K True))"
      and "\<And>a sa. P' s a sa \<Longrightarrow> P a sa"
      and "\<And>sa e. Q e sa"
    shows "wp (c x) P Q s"
  using assms unfolding wp_def effect_def post_def inv_state_def
  by (cases "execute (c x) s") (auto)

declare(in Contract) wp_stackCheck[wprules del]

lemma (in Contract) wp_assign_stack_kdvalue[wprules]:
  assumes "Stack s $$ i = None \<Longrightarrow> E Err s"
      and "\<not>(\<exists>x2. Stack s $$ i = Some (kdata.Memory x2))"
      and "Stack s $$ i = Some (kdata.Storage None) \<Longrightarrow> E Err s"
      and "Stack s $$ i = Some (kdata.Calldata None) \<Longrightarrow> E Err s"
      and "\<And>aa. Stack s $$ i = Some (kdata.Storage (Some aa)) \<Longrightarrow>
          wp (storage_update_monad (Offset aa) is (K (storage_data.Value v)) (Location aa)) P E s"
      and "\<And>x4. Stack s $$ i = Some (kdata.Value x4) \<Longrightarrow>
          wp (modify (stack_update i (kdata.Value v)) \<bind> (\<lambda>a. return Empty)) P E s"
      and "\<And>a. Stack s $$ i = Some (kdata.Calldata (Some a)) \<Longrightarrow> E Err s"
    shows "wp (assign_stack i is (rvalue.Value v)) P E s"
  apply (vcg | auto simp add:assms stack_check_def)+
  using assms apply blast
  by (vcg | auto simp add:assms stack_check_def)+
declare(in Contract) wp_stackCheck[wprules]

declare write.simps [simp del]
declare mupdate.simps [simp del]
declare mlookup.simps [simp del]
declare alookup.simps [simp del]
declare locations.simps [simp del]

end