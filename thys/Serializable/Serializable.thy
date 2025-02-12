(*<*)
theory Serializable
  imports Main
begin
(*>*)

section \<open>Transactions\<close>

text \<open>We work with a rather abstract model of transactions comprised of read/write actions.\<close>

text \<open>Read/written values are natural numbers.\<close>
type_alias val = nat

text \<open>Transactions \<^typ>\<open>'xid\<close> may read from/write two addresses \<^typ>\<open>'addr\<close>.\<close>
datatype ('xid, 'addr) action = isRead:  Read  (xid_of: \<open>'xid\<close>) (addr_of: 'addr)
                              | isWrite: Write (xid_of: \<open>'xid\<close>) (addr_of: 'addr)

text \<open>A schedule is a sequence of actions.\<close>
type_synonym ('xid, 'addr) schedule = \<open>('xid, 'addr) action list\<close>

text \<open>A database, which is being modified by the read/write actions, maps addresses to values.\<close>
type_synonym 'addr db = \<open>'addr \<Rightarrow> val\<close>

text \<open>Each transaction has a local state, which is represented as the list of previously read values (and the addresses they have been read from).\<close>
type_synonym 'addr xstate = \<open>('addr \<times> val) list\<close>

text \<open>The values written by a transaction are given by a higher-order parameter and may depend on the previously read values.\<close>
context fixes write_logic :: \<open>'xid \<Rightarrow> 'addr xstate \<Rightarrow> 'addr \<Rightarrow> val\<close> begin

text \<open>Read values are recorded in the transaction's local state; writes modify the database.\<close>
fun action_effect :: \<open>('xid, 'addr) action \<Rightarrow> ('xid \<Rightarrow> 'addr xstate) \<times> 'addr db \<Rightarrow> ('xid \<Rightarrow> 'addr xstate) \<times> 'addr db\<close> where
  \<open>action_effect (Read xid addr) (xst, db) = (xst(xid := (addr, db addr) # xst xid), db)\<close>
| \<open>action_effect (Write xid addr) (xst, db) = (xst, db(addr := write_logic xid (xst xid) addr))\<close>

text \<open>We are interested in how a schedule modifies the database (local state changes are discarded at the end).\<close>
definition schedule_effect :: \<open>('xid, 'addr) schedule \<Rightarrow> 'addr db \<Rightarrow>'addr db\<close> where
  \<open>schedule_effect s db = snd (fold action_effect s (\<lambda>_. [], db))\<close>

end

text \<open>Actions that belong to the same transaction.\<close>
definition eq_xid where
  \<open>eq_xid a b = (xid_of a = xid_of b)\<close>

section \<open>Serial and Serializable Schedules\<close>

declare length_dropWhile_le[termination_simp]

text \<open>A serial schedule does not interleave actions of different transactions.\<close>
fun serial :: \<open>('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>serial [] = True\<close>
| \<open>serial (a # as) = (let bs = dropWhile (\<lambda>b. eq_xid a b) as
    in serial bs \<and> xid_of a \<notin> xid_of ` set bs)\<close>

text \<open>A schedule \<^term>\<open>s\<close> can be rearranged into schedule \<^term>\<open>t\<close> by a permutation \<^term>\<open>\<pi>\<close>,
which preserves the relative order of actions related by \<^term>\<open>eq\<close>.\<close>
definition permutes_upto where
  \<open>permutes_upto eq \<pi> s t = 
     (bij_betw \<pi> {..<length s} {..<length t} \<and>
      (\<forall>i<length s. s ! i = t ! \<pi> i) \<and>
      (\<forall>i<length s. \<forall>j<length s. i < j \<and> eq (s ! i) (s ! j) \<longrightarrow> \<pi> i < \<pi> j))\<close>

lemma permutes_upto_Nil[simp]: \<open>permutes_upto R \<pi> [] []\<close>
  by (auto simp: permutes_upto_def bij_betw_def)

text \<open>Two schedules are equivalent if one can be rearranged into another without
rearranging the actions of each transaction and in addition they have the
same effect on any database for any fixed write logic.\<close>
abbreviation equivalent :: \<open>('xid, 'addr) schedule \<Rightarrow> ('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>equivalent s t \<equiv> (\<exists>\<pi>. permutes_upto eq_xid \<pi> s t \<and> (\<forall>write_logic db. schedule_effect write_logic s db = schedule_effect write_logic t db))\<close>

text \<open>A schedule is serializable if it is equivalent to some serial schedule. Serializable schedules
thus provide isolation: even though actions of different transactions may be interleaved, the effect
from the point of view of each transaction is as if the transaction was the only one executing in the system
(as is the case in serial schedules).\<close>
definition serializable :: \<open>('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>serializable s = (\<exists>t. serial t \<and> equivalent s t)\<close>

section \<open>Conflict Serializable Schedules\<close>

text \<open>Two actions of different transactions are conflicting if they access the same address and at least one of them is a write.\<close>
definition conflict where
  \<open>conflict a b = (xid_of a \<noteq> xid_of b \<and> addr_of a = addr_of b \<and> (isWrite a \<or> isWrite b))\<close>

text \<open>Two schedules are conflict-equivalent if one can be rearranged into another without rearranging conflicting actions
or actions of one transaction. Note that unlike equivalence, the conflict-equivalence notion is purely syntactic, i.e.,
not talking about databases and action/schedule effects.\<close>
abbreviation conflict_equivalent :: \<open>('xid, 'addr) schedule \<Rightarrow> ('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>conflict_equivalent s t \<equiv> (\<exists>\<pi>. permutes_upto (sup eq_xid conflict) \<pi> s t)\<close>

text \<open>A schedule is conflict-serializable if it is conflict equivalent to some serial schedule.\<close>
definition conflict_serializable :: \<open>('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>conflict_serializable s = (\<exists>t. serial t \<and> conflict_equivalent s t)\<close>

section \<open>Conflict-Serializability Implies Serializability\<close>

text \<open>In the following, we prove that the syntactic notion implies the semantic one.
The key obsevation is that swapping non-conflicting actions of different transactions
preserves the overall effect on the database.\<close>

lemma swap_actions: \<open>\<not> conflict a b \<Longrightarrow> \<not> eq_xid a b \<Longrightarrow>
  action_effect wl a (action_effect wl b st) = action_effect wl b (action_effect wl a st)\<close>
  unfolding conflict_def eq_xid_def
  by (cases a; cases b; cases st) (auto simp add: fun_upd_twist insert_commute)

lemma swap_many_actions: \<open>\<forall>i < length p. \<not> conflict a (p ! i) \<and> \<not> eq_xid a (p ! i) \<Longrightarrow>
  action_effect wl a (fold (action_effect wl) p st) = fold (action_effect wl) p (action_effect wl a st)\<close>
proof (induct p arbitrary: st)
  case (Cons b p)
  from Cons(2) show ?case
    unfolding fold_simps
    by (subst Cons(1)[of \<open>action_effect wl b st\<close>]) (auto simp: swap_actions[of a b])
qed simp

lemma fold_action_effect_eq:
  assumes \<open>t = p @ a # u\<close>
  shows 
  \<open>fold (action_effect wl) s (action_effect wl a st) =
   fold (action_effect wl) (p @ u) (action_effect wl a st) \<Longrightarrow>
   \<forall>i < length p. \<not> conflict a (p ! i) \<and> \<not> eq_xid a (p ! i) \<Longrightarrow>
   fold (action_effect wl) (a # s) st = fold (action_effect wl) t st\<close>
  unfolding schedule_effect_def fold_simps fold_append o_apply assms
  by (subst swap_many_actions) auto

definition shift where
  \<open>shift \<pi> = (\<lambda>i. if i < \<pi> 0 then i else i - 1) o \<pi> o Suc\<close>

lemma bij_betw_remove: \<open>bij_betw f A B \<Longrightarrow> x \<in> A \<Longrightarrow> bij_betw f (A - {x}) (B - {f x})\<close>
  unfolding bij_betw_def by (auto simp: inj_on_def)

lemma permutes_upto_shift: 
  assumes \<open>permutes_upto eq \<pi> (a # s) t\<close>
  shows \<open>permutes_upto eq (shift \<pi>) s (take (\<pi> 0) t @ drop (Suc (\<pi> 0)) t)\<close>
proof -
  from assms have \<pi>: \<open>bij_betw \<pi> {..< Suc (length s)} {..< length t}\<close>
     \<open>\<And>i. i < length s + Suc 0 \<Longrightarrow> (a # s) ! i = t ! \<pi> i\<close>
     \<open>\<And>i j. i < j \<Longrightarrow> i < length s + Suc 0 \<Longrightarrow> j < length s + Suc 0 \<Longrightarrow>
       eq ((a # s) ! i) ((a # s) ! j) \<Longrightarrow> \<pi> i < \<pi> j\<close>
    unfolding permutes_upto_def by auto
  from \<pi>(1) have distinct: \<open>\<pi> (Suc i) \<noteq> \<pi> 0\<close> if \<open>i < length s\<close> for i
    using that unfolding bij_betw_def by (auto dest!: inj_onD[of \<pi> _ \<open>Suc i\<close> 0])
  from \<pi>(1) have le: \<open>\<pi> ` {..< Suc (length s)} \<subseteq> {..< length t}\<close>
    unfolding bij_betw_def by auto
  then have \<open>bij_betw (\<lambda>i. if i < \<pi> 0 then i else i - 1) ({..< length t} - {\<pi> 0}) {..< length t - 1}\<close>
    by (cases t) (auto 0 3 simp: bij_betw_def inj_on_def image_iff not_less subset_eq Ball_def)
  moreover have \<open>bij_betw \<pi> {Suc 0 ..< Suc (length s)} ({..< length t} - {\<pi> 0})\<close>
    using bij_betw_remove[where x = 0, OF \<pi>(1)]
    by (simp add: atLeast1_lessThan_eq_remove0)
  moreover have \<open>bij_betw Suc {..< length s} {Suc 0 ..< Suc (length s)}\<close>
    by (auto simp: lessThan_atLeast0)
  ultimately have \<open>bij_betw (shift \<pi>) {..< length s} {..< length t - Suc 0}\<close>
    unfolding shift_def by (auto intro: bij_betw_trans)
  moreover have \<open>s ! i = (take (\<pi> 0) t @ drop (Suc (\<pi> 0)) t) ! shift \<pi> i\<close> if \<open>i < length s\<close> for i
    using that \<pi>(2)[of \<open>Suc i\<close>] le distinct[of i]
    by (force simp: shift_def nth_append not_less subset_eq min_def)
  moreover have \<open>shift \<pi> i < shift \<pi> j\<close>
    if \<open>i<length s\<close> \<open>j<length s\<close> \<open>i < j\<close> \<open>eq (s ! i) (s ! j)\<close> for i j
    using that \<pi>(3)[of \<open>Suc i\<close> \<open>Suc j\<close>] le distinct[of i] distinct[of j]
    by (auto simp: shift_def not_less subset_eq)
  ultimately show ?thesis
    unfolding permutes_upto_def using le by (auto simp: min_def)
qed

lemma permutes_upto_prefix_upto:
  assumes \<open>permutes_upto eq \<pi> (t ! \<pi> 0 # s) t\<close> \<open>i < \<pi> 0\<close>
  shows \<open>\<not> eq (t ! \<pi> 0) (t ! i)\<close>
proof
  assume \<open>eq (t ! \<pi> 0) (t ! i)\<close>
  moreover
  from assms have \<pi>: \<open>bij_betw \<pi> {..< Suc (length s)} {..< length t}\<close>
     \<open>\<And>i. i < length s + Suc 0 \<Longrightarrow> (t ! \<pi> 0 # s) ! i = t ! \<pi> i\<close>
     \<open>\<And>i j. i < j \<Longrightarrow> i < length s + Suc 0 \<Longrightarrow> j < length s + Suc 0 \<Longrightarrow>
       eq ((t ! \<pi> 0 # s) ! i) ((t ! \<pi> 0 # s) ! j) \<Longrightarrow> \<pi> i < \<pi> j\<close>
    unfolding permutes_upto_def by auto
  define k where \<open>k = the_inv_into {..<Suc (length s)} \<pi> i\<close>
  from \<pi>(1) assms(2) have \<open>i < length t\<close>
    using bij_betwE lessThan_Suc_eq_insert_0 by fastforce
  with \<pi>(1) assms(2) have \<open>k > 0\<close> \<open>\<pi> k = i\<close> \<open>k < Suc (length s)\<close>
    using f_the_inv_into_f[of \<pi> \<open>{..<Suc (length s)}\<close> i]
          the_inv_into_into[of \<pi> \<open>{..<Suc (length s)}\<close> i, OF _ _ subset_refl]
    by (fastforce simp: bij_betw_def set_eq_iff image_iff k_def)+
  ultimately have \<open>\<pi> 0 < \<pi> k\<close>
    using \<pi>(2)[of k] by (intro \<pi>(3)[of 0 k]) auto
  with assms(2) \<open>\<pi> k = i\<close> show False by auto
qed

lemma conflict_equivalent_imp_equivalent:
  assumes \<open>conflict_equivalent s t\<close>
  shows \<open>equivalent s t\<close>
proof -
  from assms obtain \<pi> where \<pi>: \<open>permutes_upto (sup eq_xid conflict) \<pi> s t\<close>
    by blast
  moreover from \<pi> have \<open>fold (action_effect wl) s st = fold (action_effect wl) t st\<close> for wl st
  proof (induct s arbitrary: \<pi> t st)
    case Nil
    then show ?case
      by (force simp: permutes_upto_def bij_betw_def)
  next
    case (Cons a s)
    from Cons(2) have \<open>\<pi> 0 < length t\<close> and a: \<open>a = t ! \<pi> 0\<close>
      by (auto simp add: permutes_upto_def bij_betw_def)
    with Cons(2) show ?case
      by (intro fold_action_effect_eq)
        (auto simp only: length_take min_absorb2 less_imp_le nth_take
          intro!: id_take_nth_drop[of \<open>\<pi> 0\<close> t] Cons(1)[where \<pi>=\<open>shift \<pi>\<close>]
          dest: permutes_upto_prefix_upto elim!: permutes_upto_shift)
  qed
  then have \<open>schedule_effect wl s db = schedule_effect wl t db\<close> for wl db
    unfolding schedule_effect_def by auto
  ultimately show ?thesis
    unfolding permutes_upto_def by blast
qed

theorem conflict_serializable_imp_serializable: \<open>conflict_serializable s \<Longrightarrow> serializable s\<close>
  unfolding conflict_serializable_def serializable_def
  using conflict_equivalent_imp_equivalent by blast

section \<open> Schedules Generated by Strict Two-Phase Locking (S2PL). \<close>

text \<open>To enforce conflict-serializability database management systems use
locks. Locks come in two kinds: shared locks for reads and exclusive locks for writes.
An address can be accessed in a reading fashion by multiple transactions, each holding a shared lock.
If one transaction however holds an exclusive locks to write to an address, then no
other transaction can hold a lock (neither shared nor exclusive) for the same address.\<close>

datatype 'addr lock = S (addr_of: 'addr) | X (addr_of: 'addr)

fun lock_for where
  \<open>lock_for (Read _ addr) = S addr\<close>
| \<open>lock_for (Write _ addr) = X addr\<close>

definition valid_locks where
  \<open>valid_locks locks = (\<forall>addr xid1 xid2. X addr \<in> locks xid1 \<longrightarrow>
     X addr \<in> locks xid2 \<or> S addr \<in> locks xid2 \<longrightarrow> xid1 = xid2)\<close>

text \<open>A frequently used lock strategy is strict two phase locking (S2PL) in which
transactions attempt to acquire locks gradually (whenever they want to execute an action
that needs a particular lock) and release them all at once at the end of each transaction.

The following predicate checks whether a schedule could have been generated using the S2PL strategy.
To this end, the predicate checks for each action, whether the corresponding lock could have been acquired by
the transaction executing the action. We also allow lock upgrades (from shared to exclusive), i.e., one
transaction can hold both a shared and and exclusive lock

As in our model there is no explicit transaction end marker (commit),
we treat each transaction as finished immediately when it has executed its last action in the given schedule.
This is the moment, when the transaction's locks are released.\<close>

fun s2pl :: \<open>('xid \<Rightarrow> 'addr lock set) \<Rightarrow> ('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>s2pl locks [] = True\<close>
| \<open>s2pl locks (a # s) = 
     (let xid = xid_of a; addr = action.addr_of a
     in if \<exists>xid'. xid' \<noteq> xid \<and> (X addr \<in> locks xid' \<or> isWrite a \<and> S addr \<in> locks xid')
     then False
     else s2pl (locks(xid := if xid \<notin> xid_of ` set s then {} else locks xid \<union> {lock_for a})) s)\<close>

text \<open>We prove in the following that S2PL schedules are conflict-serializable (and thus also serializable).
The proof proceeds by induction on the number of transactions in a schedule. To construct the conflict-equivalent
serial schedule we always move the actions of the transaction that finished first in our S2PL schedule to the front.
To do so we show that these actions are not conflicting with any preceding actions (due to the acquired/held locks).\<close>

lemma conflict_equivalent_trans:
  \<open>conflict_equivalent s t \<Longrightarrow> conflict_equivalent t u \<Longrightarrow> conflict_equivalent s u\<close>
proof (elim exE)
  fix \<pi> \<pi>'
  assume \<open>permutes_upto (sup eq_xid conflict) \<pi> s t\<close> \<open>permutes_upto (sup eq_xid conflict) \<pi>' t u\<close>
  then show \<open>conflict_equivalent s u\<close>
    by (intro exI[of _ \<open>\<pi>' \<circ> \<pi>\<close>])
      (auto simp: permutes_upto_def bij_betw_trans dest: bij_betwE)
qed

lemma conflict_equivalent_append: \<open>conflict_equivalent s t \<Longrightarrow> conflict_equivalent (u @ s) (u @ t)\<close>
proof (elim exE)
  fix \<pi>
  assume \<pi>: \<open>permutes_upto (sup eq_xid conflict) \<pi> s t\<close>
  define \<pi>' where \<open>\<pi>' x = (if x < length u then x else \<pi> (x - length u) + length u)\<close> for x
  define \<pi>\<pi>' where \<open>\<pi>\<pi>' x = (if x < length u then x
    else the_inv_into {..<length s} \<pi> (x - length u) + length u)\<close> for x
  from \<pi> have \<open>bij_betw \<pi>' {..<length u + length s} {..<length u + length t}\<close>
    unfolding bij_betw_iff_bijections
    by (auto simp: permutes_upto_def bij_betw_def \<pi>'_def \<pi>\<pi>'_def
      the_inv_into_f_f f_the_inv_into_f split: if_splits
      intro!: exI[of _ \<pi>\<pi>'] the_inv_into_into[OF _ _ subset_refl, of _ \<open>{..<length s}\<close>, simplified])
  with \<pi> show \<open>conflict_equivalent (u @ s) (u @ t)\<close>
    by (intro exI[of _ \<pi>']) (auto simp: permutes_upto_def nth_append \<pi>'_def)
qed

lemma conflict_equivalent_Cons: \<open>conflict_equivalent s t \<Longrightarrow> conflict_equivalent (a # s) (a # t)\<close>
  by (metis append_Cons append_Nil conflict_equivalent_append)

lemma conflict_equivalent_rearrange:
  assumes \<open>\<And>i j. xid_of (s ! i) = xid \<Longrightarrow> j < i \<Longrightarrow> i < length s \<Longrightarrow> \<not> conflict (s ! j) (s ! i)\<close>
  shows \<open>conflict_equivalent s (filter ((=) xid \<circ> xid_of) s @ filter (Not \<circ> (=) xid \<circ> xid_of) s)\<close>
    (is \<open>conflict_equivalent s (?filter s)\<close>)
  using assms
proof (induct \<open>length (filter ((=) xid \<circ> xid_of) s)\<close> arbitrary: s)
  case 0
  then show ?case
    by (auto simp: filter_empty_conv permutes_upto_def intro!: exI[of _ id])
next
  case (Suc x)
  define i where \<open>i = (LEAST i. i < length s \<and> xid_of (s ! i) = xid)\<close>
  from Suc(2) have \<open>\<exists>i < length s. xid_of (s ! i) = xid\<close>
    by (auto simp: Suc_length_conv filter_eq_Cons_iff nth_append nth_Cons')
  then have \<open>i < length s \<and> xid_of (s ! i) = xid\<close>
    unfolding i_def by (elim LeastI_ex)
  note i = conjunct1[OF this] conjunct2[OF this]
  then have lessi: \<open>\<forall>j < i. xid_of (s ! j) \<noteq> xid\<close>
    using i_def less_trans not_less_Least by blast
  with i have filter_take: \<open>filter ((=) xid \<circ> xid_of) (take i s) = []\<close>
    by (intro filter_False[of \<open>take i s\<close> \<open>((=) xid \<circ> xid_of)\<close>]) (auto simp: nth_image[symmetric])
  with i have *: \<open>filter ((=) xid \<circ> xid_of) s = s ! i # filter ((=) xid \<circ> xid_of) (drop (Suc i) s)\<close>
    by (subst id_take_nth_drop[of i s]) auto
  from i Suc(3) have \<open>\<forall>j < i. \<not> conflict (s ! j) (s ! i)\<close> by blast
  with i lessi have \<open>conflict_equivalent s (s ! i # take i s @ drop (Suc i) s)\<close>
    (is \<open>conflict_equivalent s (s ! i # ?s)\<close>)
    by (intro exI[of _ \<open>\<lambda>k. if k = i then 0 else if k < i then k + 1 else k\<close>])
      (auto simp: permutes_upto_def min_def bij_betw_def inj_on_def nth_append eq_xid_def
      nth_Cons' dest!: gr0_implies_Suc)
  also from Suc(2-) i filter_take have \<open>conflict_equivalent (s ! i # ?s) (s ! i # ?filter ?s)\<close>
    by (intro conflict_equivalent_Cons Suc(1)) (auto simp: * nth_append)
  also (conflict_equivalent_trans) from i lessi filter_take have \<open>s ! i # ?filter ?s = ?filter s\<close>
    unfolding * by (subst (8) id_take_nth_drop[of i s]) fastforce+
  finally show ?case .
qed

lemma serial_append:
  \<open>serial s \<Longrightarrow> serial t \<Longrightarrow> xid_of ` set s \<inter> xid_of ` set t = {} \<Longrightarrow> serial (s @ t)\<close>
proof (induct s rule: serial.induct)
  case (2 a as)
  then show ?case 
    using dropWhile_eq_self_iff[THEN iffD2, of t \<open>eq_xid a\<close>]
    by (fastforce simp: Let_def image_iff dropWhile_append eq_xid_def[symmetric] dest: set_dropWhileD)
qed simp

lemma serial_same_xid: \<open>\<forall>x \<in> set s. xid_of x = xid \<Longrightarrow> serial s\<close>
  using dropWhile_eq_Nil_conv[of \<open>(\<lambda>x. xid = xid_of x)\<close> \<open>tl s\<close>]
  by (cases s) (auto simp: Let_def eq_xid_def[abs_def] equals0D simp del: dropWhile_eq_Nil_conv)

lemma conflict_equivalent_same_set: \<open>conflict_equivalent s t \<Longrightarrow> set s = set t\<close>
  unfolding permutes_upto_def bij_betw_def
  by (auto simp: set_eq_iff in_set_conv_nth Bex_def image_iff) metis+

lemma s2pl_filter:
  \<open>s2pl locks s \<Longrightarrow> s2pl (locks(xid := {})) (filter (Not o (=) xid o xid_of) s)\<close>
  by (induct locks s rule: s2pl.induct) (auto simp: Let_def fun_upd_twist split: if_splits)

lemma valid_locks_grab[simp]: \<open>valid_locks locks \<Longrightarrow>
  \<not> (\<exists>xid'. xid' \<noteq> xid_of a \<and>
      (X (action.addr_of a) \<in> locks xid' \<or> isWrite a \<and> S (action.addr_of a) \<in> locks xid')) \<Longrightarrow>
  valid_locks (locks(xid_of a := insert (lock_for a) (locks (xid_of a))))\<close>
  by (cases a) (auto simp: valid_locks_def)

lemma s2pl_suffix: \<open>valid_locks locks \<Longrightarrow> s2pl locks (s @ t) \<Longrightarrow>
  \<forall>a \<in> set s. \<exists>b \<in> set t. eq_xid a b \<Longrightarrow>
  \<exists>locks'. valid_locks locks' \<and> (\<forall>xid. locks xid \<subseteq> locks' xid) \<and> s2pl locks' t\<close>
proof (induct s arbitrary: locks)
  case (Cons a s)
  from Cons(1)[OF valid_locks_grab[of locks a]] Cons(2-) show ?case
    by (auto simp add: Let_def eq_xid_def fun_upd_def cong: if_cong split: if_splits) blast+
qed auto

lemma set_drop: \<open>l \<le> length xs \<Longrightarrow> set (drop l xs) = nth xs ` {l..<length xs}\<close>
  by (auto simp: set_conv_nth image_iff) (metis add.commute le_iff_add less_diff_conv)

lemma drop_eq_Cons: \<open>i < length xs \<Longrightarrow> drop i xs = xs ! i # drop (Suc i) xs\<close>
  by (subst id_take_nth_drop[of i xs]) auto

theorem s2pl_conflict_serializable: \<open>s2pl (\<lambda>_. {}) s \<Longrightarrow> conflict_serializable s\<close>
proof (induct \<open>card (xid_of ` set s)\<close> arbitrary: s)
  case 0
  then show ?case
    by (auto simp: conflict_serializable_def intro!: exI[of _ \<open>[]\<close>])
next
  case (Suc x)
  define i where \<open>i = (LEAST i. i < length s \<and> (\<forall>j \<in> {i+1 ..< length s}. \<not> eq_xid (s ! i) (s ! j)))\<close>
  have \<open>i < length s \<and> (\<forall>j \<in> {i+1 ..< length s}. \<not> eq_xid (s ! i) (s ! j))\<close>
    unfolding i_def by (rule LeastI[of _ \<open>length s - 1\<close>], use Suc(2) in \<open>cases s\<close>) auto
  note i = conjunct1[OF this] conjunct2[OF this, rule_format]
  define xid where \<open>xid = xid_of (s ! i)\<close>
  with i have xid: \<open>xid \<in> xid_of ` set s\<close>
    by (auto simp: image_iff in_set_conv_nth Bex_def)
  from i(1) have *: \<open>\<exists>k \<in> {i ..< length s}. eq_xid (s ! j) (s ! k)\<close> if \<open>j < i\<close> for j
  proof (cases \<open>xid = xid_of (s ! j)\<close>)
    case False
    with that i(1) show ?thesis
    proof (induct \<open>i - j\<close> arbitrary: j rule: less_induct)
      case less
      from \<open>j < i\<close> less_trans[OF \<open>j < i\<close> \<open>i < length s\<close>]
      obtain j' where \<open>j' \<in> {j+1 ..< length s}\<close> \<open>eq_xid (s ! j) (s ! j')\<close>
        by (subst (asm) i_def) (force dest: not_less_Least)
      with less(1)[of j'] less(2-) show ?case
        by (cases \<open>j' \<ge> i\<close>) (auto simp: diff_less_mono2 eq_xid_def)
    qed
  qed (auto simp: xid_def eq_xid_def Bex_def)
  have \<open>conflict_equivalent s (filter ((=) xid \<circ> xid_of) s @ filter (Not \<circ> (=) xid \<circ> xid_of) s)\<close>
  proof (intro conflict_equivalent_rearrange notI)
    fix k l
    let ?xid = \<open>xid_of (s ! k)\<close>
    assume kl: \<open>xid_of (s ! l) = xid\<close> \<open>k < l\<close> \<open>l < length s\<close> \<open>conflict (s ! k) (s ! l)\<close>
    with i(2) have li: \<open>l \<le> i\<close>
      unfolding xid_def eq_xid_def
      by (metis One_nat_def add.right_neutral add_Suc_right atLeastLessThan_iff not_less_eq_eq)
    from \<open>k < l\<close> have drop_alt: \<open>drop l s = drop (l - Suc k) (drop (Suc k) s)\<close>
      by auto
    from li kl have take_drop_l: \<open>\<forall>a\<in>set (take l s). \<exists>b\<in>set (drop l s). eq_xid a b\<close>
      by (force simp: nth_image[symmetric] set_drop Bex_def conj_commute
        dest!: *[OF less_le_trans])
    from li kl have \<open>\<forall>a\<in>set (take k s). \<exists>b\<in>set (drop k s). eq_xid a b\<close>
      by (force simp: nth_image[symmetric] set_drop Bex_def conj_commute
        dest!: *[OF less_le_trans[OF less_trans[OF _ \<open>k < l\<close>]]])
    with kl Suc(3) obtain locks where \<open>valid_locks locks\<close> \<open>s2pl locks (drop k s)\<close>
      using s2pl_suffix[of \<open>\<lambda>_. {}\<close> \<open>take k s\<close> \<open>drop k s\<close>] by (auto simp: valid_locks_def)
    with kl(2,3) Suc(3) *[of k]  \<open>l \<le> i\<close>
    have \<open>valid_locks (locks(?xid := locks ?xid \<union> {lock_for (s ! k)})) \<and>
      s2pl (locks(?xid := locks ?xid \<union> {lock_for (s ! k)})) (drop (Suc k) s)\<close>
      by (subst (asm) drop_eq_Cons)
        (auto simp: Let_def image_iff eq_xid_def[symmetric] set_drop split: if_splits)
    with kl(2) li Suc(3) obtain locks' where
      \<open>valid_locks locks'\<close>
      \<open>\<forall>xid. (locks(?xid := locks ?xid \<union> {lock_for (s ! k)})) xid \<subseteq> locks' xid\<close>
      \<open>s2pl locks' (drop l s)\<close>
      using take_drop_l unfolding drop_alt
      by (atomize_elim, intro s2pl_suffix[of _ \<open>take (l - Suc k) (drop (Suc k) s)\<close>])
        (auto simp del: drop_drop
          dest!: in_set_dropD[of _ n \<open>take (_ + n) _\<close> for n, folded take_drop])
    with kl show False
      by (subst (asm) drop_eq_Cons, simp)
        (cases \<open>s ! k\<close>; cases \<open>s ! l\<close>;
          auto simp: valid_locks_def xid_def Let_def conflict_def split: if_splits)
  qed
  moreover have \<open>card (xid_of ` {x \<in> set s. xid \<noteq> xid_of x}) = card (xid_of ` set s - {xid})\<close>
    by (rule arg_cong) auto
  with Suc(2-) have \<open>conflict_serializable (filter (Not \<circ> (=) xid \<circ> xid_of) s)\<close>
    using s2pl_filter[of \<open>\<lambda>_. {}\<close> s xid] xid
    by (intro Suc(1)) (auto simp: fun_upd_idem card_Diff_subset_Int)
  then obtain t where t: \<open>serial t\<close> \<open>conflict_equivalent (filter (Not \<circ> (=) xid \<circ> xid_of) s) t\<close>
    unfolding conflict_serializable_def by blast
  ultimately have \<open>conflict_equivalent s (filter ((=) xid \<circ> xid_of) s @ t)\<close>
    by (auto elim!: conflict_equivalent_trans conflict_equivalent_append)
  moreover from t have \<open>serial (filter ((=) xid \<circ> xid_of) s @ t)\<close>
    by (intro serial_append)
      (auto dest!: conflict_equivalent_same_set intro: serial_same_xid[of _ xid])
  ultimately show ?case
    unfolding conflict_serializable_def by blast
qed

corollary s2pl_serializable: \<open>s2pl (\<lambda>_. {}) s \<Longrightarrow> serializable s\<close>
  by (simp add: conflict_serializable_imp_serializable s2pl_conflict_serializable)

section \<open>Example Executing S2PL\<close>

text \<open>To make the S2PL check executable regardless of the transaction id type, we restrict the
quantification to transaction ids that are occurring in the schedule.\<close>

fun s2pl_code :: \<open>('xid \<Rightarrow> 'addr lock set) \<Rightarrow> ('xid, 'addr) schedule \<Rightarrow> bool\<close> where
  \<open>s2pl_code locks [] = True\<close>
| \<open>s2pl_code locks (a # s) = 
     (let xid = xid_of a; addr = action.addr_of a
     in if \<exists>xid' \<in> xid_of ` set s. xid' \<noteq> xid \<and> (X addr \<in> locks xid' \<or> isWrite a \<and> S addr \<in> locks xid')
     then False
     else s2pl_code (locks(xid := if xid \<notin> xid_of ` set s then {} else locks xid \<union> {lock_for a})) s)\<close>

lemma s2pl_code_cong: "(\<And>xid. xid \<in> xid_of ` set s \<Longrightarrow> f xid = g xid) \<Longrightarrow>
  (\<And>xid. xid \<notin> xid_of ` set s \<Longrightarrow> f xid = {}) \<Longrightarrow>
  s2pl f s = s2pl_code g s"
proof (induct s arbitrary: f g)
  case (Cons a s)
  from Cons(2-) show ?case
    unfolding s2pl.simps s2pl_code.simps Let_def
    by (intro if_cong[OF _ refl Cons(1)]) (auto 8 2 simp: image_iff)
qed simp

lemma s2pl_code[code_unfold]: "s2pl (\<lambda>_. {}) s = s2pl_code (\<lambda>_. {}) s"
  by (simp add: s2pl_code_cong)

definition "TB = (0 :: nat)"
definition "TA = (1 :: nat)"
definition "TC = (2 :: nat)"
definition "AX = (0 :: nat)"
definition "AY = (1 :: nat)"
definition "AZ = (2 :: nat)"

text \<open>Good example involving a lock upgrade by \<^term>\<open>TA\<close> and \<^term>\<open>TB\<close>\<close>
lemma \<open>s2pl (\<lambda>_. {})
  [Write TB AZ, Read TA AX, Read TB AY, Read TC AX, Write TB AY, Write TC AY, Write TA AX, Write TA AY]\<close>
  by eval

text \<open>Bad example: \<^term>\<open>TC\<close> cannot acquire exclusive lock for \<^term>\<open>AY\<close>, which is already held by \<^term>\<open>TA\<close>\<close>
lemma \<open>\<not> s2pl (\<lambda>_. {})
  [Read TA AX, Read TB AX, Read TC AX, Write TA AY, Write TC AY, Write TB AY, Write TA AZ]\<close>
  by eval

hide_const TB TA TC AX AY AZ
hide_fact TB_def TA_def TC_def AX_def AY_def AZ_def

(*<*)
end
(*>*)