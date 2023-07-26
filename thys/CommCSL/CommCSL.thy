section \<open>CommCSL\<close>

theory CommCSL
  imports Lang StateModel
begin

definition no_guard :: "('i, 'a) heap \<Rightarrow> bool" where
  "no_guard h \<longleftrightarrow> get_gs h = None \<and> (\<forall>k. get_gu h k = None)"

typedef 'a precondition = "{ pre :: ('a \<Rightarrow> 'a \<Rightarrow> bool) |pre. \<forall>a b. pre a b \<longrightarrow> (pre b a \<and> pre a a) }"
  using Sup2_E by auto

lemma charact_rep_prec:
  assumes "Rep_precondition pre a b"
  shows "Rep_precondition pre b a \<and> Rep_precondition pre a a"
  using Rep_precondition assms by fastforce

typedef ('i, 'a) indexed_precondition = "{ pre :: ('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) |pre. \<forall>a b k. pre k a b \<longrightarrow> (pre k b a \<and> pre k a a) }"
  using Sup2_E by auto

lemma charact_rep_indexed_prec:
  assumes "Rep_indexed_precondition pre k a b"
  shows "Rep_indexed_precondition pre k b a \<and> Rep_indexed_precondition pre k a a"
  by (metis (no_types, lifting) Abs_indexed_precondition_cases Rep_indexed_precondition_cases Rep_indexed_precondition_inverse assms mem_Collect_eq)

type_synonym 'a list_exp = "store \<Rightarrow> 'a list"

subsection \<open>Assertion Language\<close>

datatype ('i, 'a, 'v) assertion =
  Bool bexp
  | Emp
  | And "('i, 'a, 'v) assertion" "('i, 'a, 'v) assertion"
  | Star "('i, 'a, 'v) assertion" "('i, 'a, 'v) assertion"    ("_ * _" 70)
  | Low bexp
  | LowExp exp

  | PointsTo exp prat exp
  | Exists var "('i, 'a, 'v) assertion"

  | EmptyFullGuards

  | PreSharedGuards "'a precondition"
  | PreUniqueGuards "('i, 'a) indexed_precondition"


  | View "normal_heap \<Rightarrow> 'v" "('i, 'a, 'v) assertion" "store \<Rightarrow> 'v"
  | SharedGuard prat "store \<Rightarrow> 'a multiset"
  | UniqueGuard 'i "'a list_exp"

  | Imp bexp "('i, 'a, 'v) assertion"
  | NoGuard

inductive PRE_shared_simpler :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  Empty: "PRE_shared_simpler spre {#} {#}"
| Step: "\<lbrakk> PRE_shared_simpler spre a b ; spre xa xb \<rbrakk> \<Longrightarrow> PRE_shared_simpler spre (a + {# xa #}) (b + {# xb #})"


definition PRE_unique :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "PRE_unique upre uargs uargs' \<longleftrightarrow> length uargs = length uargs' \<and> (\<forall>i. i \<ge> 0 \<and> i < length uargs' \<longrightarrow> upre (uargs ! i) (uargs' ! i))"

fun hyper_sat :: "(store \<times> ('i, 'a) heap) \<Rightarrow> (store \<times> ('i, 'a) heap) \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> bool" ("_, _ \<Turnstile> _" [51, 65, 66] 50) where
  "(s, _), (s', _)  \<Turnstile> Bool b \<longleftrightarrow> bdenot b s \<and> bdenot b s'"
| "(_, h), (_, h') \<Turnstile> Emp \<longleftrightarrow> dom (get_fh h) = {} \<and> dom (get_fh h') = {}"
| "\<sigma>, \<sigma>' \<Turnstile> And A B \<longleftrightarrow> \<sigma>, \<sigma>' \<Turnstile> A \<and> \<sigma>, \<sigma>' \<Turnstile> B"

| "(s, h), (s', h')  \<Turnstile> Star A B \<longleftrightarrow> (\<exists>h1 h2 h1' h2'. Some h = Some h1 \<oplus> Some h2 \<and> Some h' = Some h1' \<oplus> Some h2'
  \<and> (s, h1), (s', h1') \<Turnstile> A \<and> (s, h2), (s', h2') \<Turnstile> B)"
| "(s, h), (s', h') \<Turnstile> Low e \<longleftrightarrow> bdenot e s = bdenot e s'"

| "(s, h), (s', h') \<Turnstile> PointsTo loc p x \<longleftrightarrow> get_fh h (edenot loc s) = Some (p, edenot x s) \<and> get_fh h' (edenot loc s') = Some (p, edenot x s')
\<and> dom (get_fh h) = {edenot loc s} \<and> dom (get_fh h') = {edenot loc s'}"
| "(s, h), (s', h') \<Turnstile> Exists x A \<longleftrightarrow> (\<exists>v v'. (s(x := v), h), (s'(x := v'), h') \<Turnstile> A)"

| "(s, h), (s', h') \<Turnstile> EmptyFullGuards \<longleftrightarrow> (get_gs h = Some (pwrite, {#}) \<and> (\<forall>k. get_gu h k = Some []) \<and> get_gs h' = Some (pwrite, {#}) \<and> (\<forall>k. get_gu h' k = Some []))"

| "(s, h), (s', h') \<Turnstile> PreSharedGuards spre \<longleftrightarrow>
  (\<exists>sargs sargs'. get_gs h = Some (pwrite, sargs) \<and> get_gs h' = Some (pwrite, sargs') \<and> PRE_shared_simpler (Rep_precondition spre) sargs sargs'
  \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty)"
| "(s, h), (s', h') \<Turnstile> PreUniqueGuards upre \<longleftrightarrow>
  (\<exists>uargs uargs'. (\<forall>k. get_gu h k = Some (uargs k)) \<and> (\<forall>k. get_gu h' k = Some (uargs' k)) \<and> (\<forall>k. PRE_unique (Rep_indexed_precondition upre k) (uargs k) (uargs' k)) \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty)"

| "(s, h), (s', h') \<Turnstile> View f J e \<longleftrightarrow> ((s, h), (s', h') \<Turnstile> J \<and> f (normalize (get_fh h)) = e s \<and> f (normalize (get_fh h')) = e s')"
| "(s, h), (s', h') \<Turnstile> SharedGuard \<pi> ms \<longleftrightarrow> ((\<forall>k. get_gu h k = None \<and> get_gu h' k = None) \<and> get_gs h = Some (\<pi>, ms s) \<and> get_gs h' = Some (\<pi>, ms s')
            \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty)"

| "(s, h), (s', h') \<Turnstile> UniqueGuard k lexp \<longleftrightarrow> (get_gs h = None \<and> get_gu h k = Some (lexp s) \<and> get_gu h' k = Some (lexp s') \<and> get_gs h' = None
            \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty \<and> (\<forall>k'. k' \<noteq> k \<longrightarrow> get_gu h k' = None \<and> get_gu h' k' = None))"

| "(s, h), (s', h') \<Turnstile> LowExp e \<longleftrightarrow> edenot e s = edenot e s'"

| "(s, h), (s', h') \<Turnstile> Imp b A \<longleftrightarrow> bdenot b s = bdenot b s' \<and> (bdenot b s \<longrightarrow> (s, h), (s', h') \<Turnstile> A)"

| "(s, h), (s', h') \<Turnstile> NoGuard \<longleftrightarrow> (get_gs h = None \<and> (\<forall>k. get_gu h k = None) \<and> get_gs h' = None \<and> (\<forall>k. get_gu h' k = None))"

lemma sat_PreUniqueE:
  assumes "(s, h), (s', h') \<Turnstile> PreUniqueGuards upre"
  shows "\<exists>uargs uargs'. (\<forall>k. get_gu h k = Some (uargs k)) \<and> (\<forall>k. get_gu h' k = Some (uargs' k)) \<and> (\<forall>k. PRE_unique (Rep_indexed_precondition upre k) (uargs k) (uargs' k))"
  using assms by auto


lemma decompose_heap_triple:
  "h = (get_fh h, get_gs h, get_gu h)"
  by simp


definition depends_only_on :: "(store \<Rightarrow> 'v) \<Rightarrow> var set \<Rightarrow> bool" where
  "depends_only_on e S \<longleftrightarrow> (\<forall>s s'. agrees S s s' \<longrightarrow> e s = e s')"

lemma depends_only_onI:
  assumes "\<And>s s' :: store. agrees S s s' \<Longrightarrow> e s = e s'"
  shows "depends_only_on e S"
  using assms depends_only_on_def by blast

definition fvS :: "(store \<Rightarrow> 'v) \<Rightarrow> var set" where
  "fvS e = (SOME S. depends_only_on e S)"

lemma fvSE:
  assumes "agrees (fvS e) s s'"
  shows "e s = e s'"
proof -
  have "depends_only_on e UNIV"
  proof (rule depends_only_onI)
    fix s s' :: store assume "agrees UNIV s s'"
    have "s = s'"
    proof (rule ext)
      fix x :: var have "x \<in> UNIV"
        by auto
      then show "s x = s' x"
        by (meson \<open>agrees UNIV s s'\<close> agrees_def)
    qed
    then show "e s = e s'" by simp
  qed
  then show ?thesis
    by (metis assms depends_only_on_def fvS_def someI_ex)
qed


fun fvA :: "('i, 'a, 'v) assertion \<Rightarrow> var set" where
  "fvA (Bool b) = fvB b"
| "fvA (And A B) = fvA A \<union> fvA B"
| "fvA (Star A B) = fvA A \<union> fvA B"
| "fvA (Low e) = fvB e"
| "fvA Emp = {}"
| "fvA (PointsTo v va vb) = fvE v \<union> fvE vb"
| "fvA (Exists x A) = fvA A - {x}"
| "fvA (SharedGuard _ e) = fvS e"
| "fvA (UniqueGuard _ e) = fvS e"
| "fvA (View view A e) = fvA A \<union> fvS e"
| "fvA (PreSharedGuards _) = {}"
| "fvA (PreUniqueGuards _) = {}"
| "fvA EmptyFullGuards = {}"
| "fvA (LowExp x) = fvE x"
| "fvA (Imp b A) = fvB b \<union> fvA A"

definition subS :: "var \<Rightarrow> exp \<Rightarrow> (store \<Rightarrow> 'v) \<Rightarrow> (store \<Rightarrow> 'v)" where
  "subS x E e = (\<lambda>s. e (s(x := edenot E s)))"

lemma subS_assign:
  "subS x E e s  \<longleftrightarrow> e (s(x := edenot E s))"
  by (simp add: subS_def)

fun collect_existentials :: "('i, 'a, nat) assertion \<Rightarrow> var set" where
  "collect_existentials (And A B) = collect_existentials A \<union> collect_existentials B"
| "collect_existentials (Star A B) = collect_existentials A \<union> collect_existentials B"
| "collect_existentials (Exists x A) = collect_existentials A \<union> {x}"
| "collect_existentials (View view A e) = collect_existentials A"
| "collect_existentials (Imp _ A) = collect_existentials A"
| "collect_existentials _ = {}"

fun subA :: "var \<Rightarrow> exp \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> ('i, 'a, nat) assertion" where
  "subA x E (And A B) = And (subA x E A) (subA x E B)"
| "subA x E (Star A B) = Star (subA x E A) (subA x E B)"
| "subA x E (Bool B) = Bool (subB x E B)"
| "subA x E (Low e) = Low (subB x E e)"
| "subA x E (LowExp e) = LowExp (subE x E e)"
| "subA x E (UniqueGuard k e) = UniqueGuard k (subS x E e)"
| "subA x E (SharedGuard \<pi> e) = SharedGuard \<pi> (subS x E e)"
| "subA x E (View view A e) = View view (subA x E A) (subS x E e)"
| "subA x E (PointsTo loc \<pi> e) = PointsTo (subE x E loc) \<pi> (subE x E e)"
| "subA x E (Exists y A) = (if x = y then Exists y A else Exists y (subA x E A))"
| "subA x E (Imp b A) = Imp (subB x E b) (subA x E A)"
| "subA _ _ A = A"

lemma subA_assign:
  assumes "collect_existentials A \<inter> fvE E = {}"
  shows "(s, h), (s', h') \<Turnstile> subA x E A \<longleftrightarrow> (s(x := edenot E s), h), (s'(x := edenot E s'), h') \<Turnstile> A"
  using assms
proof (induct A arbitrary: s h s' h')
  case (And A1 A2)
  then show ?case
    by (simp add: disjoint_iff_not_equal)
next
  case (Star A1 A2)
  then show ?case
    by (simp add: disjoint_iff_not_equal)
next
  case (Bool x)
  then show ?case
    by (metis hyper_sat.simps(1) subA.simps(3) subB_assign)
next
  case (Low x2)
  then show ?case
    by (metis (no_types, lifting) hyper_sat.simps(5) subA.simps(4) subB_assign)
next
  case (LowExp x2)
  then show ?case
    by (metis (no_types, lifting) hyper_sat.simps(14) subA.simps(5) subE_assign)
next
  case (PointsTo x1a x2 x3)
  then show ?case
    by (metis (no_types, lifting) hyper_sat.simps(6) subA.simps(9) subE_assign)
next
  case (Exists y A)
  then have asm0: "collect_existentials A \<inter> fvE E = {}"
    by auto
  show ?case (is "?A \<longleftrightarrow> ?B")
  proof
    show "?A \<Longrightarrow> ?B"
    proof -
      assume ?A
      show ?B
      proof (cases "x = y")
        case True
        then show ?thesis by (metis (no_types, opaque_lifting) \<open>?A\<close> fun_upd_upd hyper_sat.simps(7) subA.simps(10))
      next
        case False
        then obtain v v' where "(s(y := v), h), (s'(y := v'), h') \<Turnstile> subA x E A"
          using \<open>(s, h), (s', h') \<Turnstile> subA x E (Exists y A)\<close> by auto
        then have "((s(y := v))(x := edenot E (s(y := v))), h), ((s'(y := v'))(x := edenot E (s'(y := v'))), h') \<Turnstile> A"
          using Exists asm0 by blast
        moreover have "y \<notin> fvE E"
          using Exists.prems by force
        then have "edenot E (s(y := v)) = edenot E s \<and> edenot E (s'(y := v')) = edenot E s'"
          by (metis agrees_update exp_agrees)
        moreover have "(s(y := v))(x := edenot E s) = (s(x := edenot E s))(y := v)
        \<and> (s'(y := v'))(x := edenot E s') = (s'(x := edenot E s'))(y := v')"
          by (simp add: False fun_upd_twist)
        ultimately show ?thesis using False hyper_sat.simps(7)
          by metis
      qed
    qed
    assume ?B
    show ?A
    proof (cases "x = y")
      case True
      then show ?thesis
        using \<open>(s(x := edenot E s), h), (s'(x := edenot E s'), h') \<Turnstile> Exists y A\<close> by fastforce
    next
      case False
      then obtain v v' where "((s(x := edenot E s))(y := v), h), ((s'(x := edenot E s'))(y := v'), h') \<Turnstile> A"
        using \<open>(s(x := edenot E s), h), (s'(x := edenot E s'), h') \<Turnstile> Exists y A\<close> hyper_sat.simps(7) by blast
      moreover have "(s(y := v))(x := edenot E s) = (s(x := edenot E s))(y := v)
      \<and> (s'(y := v'))(x := edenot E s') = (s'(x := edenot E s'))(y := v')"
        by (simp add: False fun_upd_twist)
      then have "((s(y := v))(x := edenot E (s(y := v))), h), ((s'(y := v'))(x := edenot E (s'(y := v'))), h') \<Turnstile> A"
        using Exists.prems calculation by auto
      then show ?thesis
        by (metis Exists.hyps False asm0 hyper_sat.simps(7) subA.simps(10))
    qed
  qed
next
  case (View x1a A x3)
  then show ?case
    by (metis (mono_tags, lifting) collect_existentials.simps(4) hyper_sat.simps(11) subA.simps(8) subS_def)
next
  case (SharedGuard x1a x2)
  then show ?case
    by (metis (mono_tags, lifting) hyper_sat.simps(12) subA.simps(7) subS_def)
next
  case (UniqueGuard x)
  then show ?case
    by (metis (mono_tags, lifting) hyper_sat.simps(13) subA.simps(6) subS_def)
next
  case (Imp b A)
  then show ?case
    by (metis collect_existentials.simps(5) hyper_sat.simps(15) subA.simps(11) subB_assign)
qed (auto)

lemma PRE_uniqueI:
  assumes "length uargs = length uargs'"
      and "\<And>i. i \<ge> 0 \<and> i < length uargs' \<Longrightarrow> upre (uargs ! i) (uargs' ! i)"
    shows "PRE_unique upre uargs uargs'"
  using assms PRE_unique_def by blast

lemma PRE_unique_implies_tl:
  assumes "PRE_unique upre (ta # qa) (tb # qb)"
  shows "PRE_unique upre qa qb"
proof (rule PRE_uniqueI)
  show "length qa = length qb"
    by (metis PRE_unique_def assms diff_Suc_1 length_Cons)
  fix i assume "0 \<le> i \<and> i < length qb"
  then have "upre ((ta # qa) ! (i + 1)) ((tb # qb) ! (i + 1))"
    by (metis PRE_unique_def add_nonneg_nonneg assms discrete le_imp_less_Suc length_Cons zero_less_one_class.zero_le_one)
  then show "upre (qa ! i) (qb ! i)"
    by simp
qed


lemma charact_PRE_unique:
  assumes "PRE_unique (Rep_indexed_precondition pre k) a b"
  shows "PRE_unique (Rep_indexed_precondition pre k) b a \<and> PRE_unique (Rep_indexed_precondition pre k) a a"
  using assms
proof (induct "length a" arbitrary: a b)
  case 0
  then show ?case
    by (simp add: PRE_unique_def)
next
  case (Suc n)
  then obtain ha ta hb tb where "a = ha # ta" "b = hb # tb"
    by (metis One_nat_def PRE_unique_def Suc_le_length_iff le_add1 plus_1_eq_Suc)
  then have "n = length ta"
    using Suc.hyps(2) by auto
  then have "PRE_unique (Rep_indexed_precondition pre k) tb ta \<and> PRE_unique (Rep_indexed_precondition pre k) ta ta"
    by (metis PRE_unique_implies_tl Suc.hyps(1) Suc.prems \<open>a = ha # ta\<close> \<open>b = hb # tb\<close>)
  then show ?case
    by (metis PRE_unique_def Suc.prems charact_rep_indexed_prec)
qed

lemma charact_PRE_shared_simpler:
  assumes "PRE_shared_simpler rpre a b"
      and "Rep_precondition pre = rpre"
  shows "PRE_shared_simpler (Rep_precondition pre) b a \<and> PRE_shared_simpler (Rep_precondition pre) a a"
  using assms
proof (induct arbitrary: pre rule: PRE_shared_simpler.induct)
  case (Empty spre)
  then show ?case
    by (simp add: PRE_shared_simpler.Empty)
next
  case (Step spre a b xa xb)
  then have "spre xb xa \<and> spre xa xa" using charact_rep_prec by metis
  then show ?case
    by (metis PRE_shared_simpler.Step Step.hyps(2) Step.prems)
qed


lemma always_sat_refl_aux:
  assumes "(s, h), (s', h') \<Turnstile> A"
  shows "(s, h), (s, h) \<Turnstile> A"
  using assms
proof (induct A arbitrary: s h s' h')
  case (Star A B)
  then obtain ha hb ha' hb' where "Some h = Some ha \<oplus> Some hb" "Some h' = Some ha' \<oplus> Some hb'"
    "(s, ha), (s', ha') \<Turnstile> A" "(s, hb), (s', hb') \<Turnstile> B"
    by auto
  then have "(s, ha), (s, ha) \<Turnstile> A \<and> (s, hb), (s, hb) \<Turnstile> B"
    using Star.hyps(1) Star.hyps(2) by blast
  then show ?case
    using \<open>Some h = Some ha \<oplus> Some hb\<close> hyper_sat.simps(4) by blast
next
  case (Exists x A)
  then show ?case
    by (meson hyper_sat.simps(7))
next
  case (PreSharedGuards x)
  then show ?case
    using charact_PRE_shared_simpler by force
next
  case (PreUniqueGuards upre)
  then obtain uargs uargs' where "(\<forall>k. get_gu h k = Some (uargs k)) \<and>
        (\<forall>k. get_gu h' k = Some (uargs' k)) \<and> (\<forall>k. PRE_unique (Rep_indexed_precondition upre k) (uargs k) (uargs' k)) \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty"
    using hyper_sat.simps(10)[of s h s' h' upre] by blast
  then show "(s, h), (s, h) \<Turnstile> PreUniqueGuards upre"
    using charact_PRE_unique hyper_sat.simps(10)[of s h s h upre]
    by metis
qed (auto)

lemma always_sat_refl:
  assumes "\<sigma>, \<sigma>' \<Turnstile> A"
  shows "\<sigma>, \<sigma> \<Turnstile> A"
  by (metis always_sat_refl_aux assms prod.exhaust_sel)

lemma agrees_same_aux:
  assumes "agrees (fvA A) s s''"
    and "(s, h), (s', h') \<Turnstile> A"
  shows "(s'', h), (s', h') \<Turnstile> A"
  using assms
proof (induct A arbitrary: s s' s'' h h')
  case (Bool b)
  then show ?case by (simp add: bexp_agrees)
next
  case (And A1 A2)
  then show ?case using fvA.simps(2) hyper_sat.simps(3)
    by (metis (mono_tags, lifting) UnCI agrees_def)
next
  case (Star A B)
  then obtain ha hb ha' hb' where "Some h = Some ha \<oplus> Some hb" "Some h' = Some ha' \<oplus> Some hb'"
    "(s, ha), (s', ha') \<Turnstile> A" "(s, hb), (s', hb') \<Turnstile> B"
    by auto
  then have "(s'', ha), (s', ha') \<Turnstile> A \<and> (s'', hb), (s', hb') \<Turnstile> B"
    using Star.hyps[of s s'' _ s' _] Star.prems(1)
    by (simp add: agrees_def)
  then show ?case
    using \<open>Some h = Some ha \<oplus> Some hb\<close> \<open>Some h' = Some ha' \<oplus> Some hb'\<close> hyper_sat.simps(4) by blast
next
  case (Low e)
  then have "bdenot e s = bdenot e s''"
    by (metis bexp_agrees fvA.simps(4))
  then show ?case using Low by simp
next
  case (LowExp e)
  then have "edenot e s = edenot e s''"
    by (metis exp_agrees fvA.simps(14))
  then show ?case using LowExp by simp
next
  case (PointsTo l \<pi> v)
  then have "edenot l s = edenot l s'' \<and> edenot v s = edenot v s''"
    by (simp add: agrees_def exp_agrees)
  then show ?case using PointsTo by auto
next
  case (Exists x A)
  then obtain v v' where "(s(x := v), h), (s'(x := v'), h') \<Turnstile> A"
    by auto
  moreover have "agrees (fvA A) (s(x := v)) (s''(x := v))"
  proof (rule agreesI)
    fix y show "y \<in> fvA A \<Longrightarrow> (s(x := v)) y = (s''(x := v)) y"
      apply (cases "y = x")
       apply simp
      using Diff_iff[of y "fvA A" "{x}"] Exists.prems(1) agrees_def empty_iff fun_upd_apply[of s x v] fun_upd_apply[of s'' x v] fvA.simps(7) insert_iff
      by metis
  qed
  ultimately have "(s''(x := v), h), (s'(x := v'), h') \<Turnstile> A"
    using Exists.hyps by blast
  then show ?case by auto
next
  case (View x1a A e)
  then have "(s'', h), (s', h') \<Turnstile> A \<and> e s = e s''"
    using fvA.simps(10) fvSE hyper_sat.simps(11) agrees_union
    by metis
  then show ?case
    using View.prems(2) by auto
next
  case (SharedGuard x1a x2)
  then show ?case using fvSE by auto
next
  case (UniqueGuard x)
  then show ?case using fvSE by auto
next
  case (Imp b A)
  then show ?case
    by (metis agrees_union bexp_agrees fvA.simps(15) hyper_sat.simps(15))
qed (auto)

lemma agrees_same:
  assumes "agrees (fvA A) s s''"
  shows "(s, h), (s', h') \<Turnstile> A \<longleftrightarrow> (s'', h), (s', h') \<Turnstile> A"
  by (metis (mono_tags, lifting) agrees_def agrees_same_aux assms)

lemma sat_comm_aux:
  "(s, h), (s', h') \<Turnstile> A \<Longrightarrow> (s', h'), (s, h) \<Turnstile> A"
proof (induct A arbitrary: s h s' h')
  case (Star A B)
  then obtain ha hb ha' hb' where "Some h = Some ha \<oplus> Some hb" "Some h' = Some ha' \<oplus> Some hb'"
    "(s, ha), (s', ha') \<Turnstile> A" "(s, hb), (s', hb') \<Turnstile> B"
    by auto
  then have "(s', ha'), (s, ha) \<Turnstile> A \<and> (s', hb'), (s, hb) \<Turnstile> B"
    using Star.hyps(1) Star.hyps(2) by presburger
  then show ?case
    using \<open>Some h = Some ha \<oplus> Some hb\<close> \<open>Some h' = Some ha' \<oplus> Some hb'\<close> hyper_sat.simps(4) by blast
next
  case (Exists x A)
  then obtain v v' where "(s(x := v), h), (s'(x := v'), h') \<Turnstile> A"
    by auto
  then have "(s'(x := v'), h'), (s(x := v), h) \<Turnstile> A"
    using Exists.hyps by blast
  then show ?case by auto
next
  case (PreSharedGuards x)
  then show ?case
    by (meson charact_PRE_shared_simpler hyper_sat.simps(9))
next
  case (PreUniqueGuards upre)
  then obtain uargs uargs' where "(\<forall>k. get_gu h k = Some (uargs k)) \<and>
        (\<forall>k. get_gu h' k = Some (uargs' k)) \<and> (\<forall>k. PRE_unique (Rep_indexed_precondition upre k) (uargs k) (uargs' k)) \<and> get_fh h = Map.empty \<and> get_fh h' = Map.empty"
    using hyper_sat.simps(10)[of s h s' h' upre] by blast
  then show "(s', h'), (s, h) \<Turnstile> PreUniqueGuards upre"
    using charact_PRE_unique hyper_sat.simps(10)[of s' h' s h upre]
    by metis
qed (auto)

lemma sat_comm:
  "\<sigma>, \<sigma>' \<Turnstile> A \<longleftrightarrow> \<sigma>', \<sigma> \<Turnstile> A"
  using sat_comm_aux surj_pair by metis

definition precise where
  "precise J \<longleftrightarrow> (\<forall>s1 H1 h1 h1' s2 H2 h2 h2'. H1 \<succeq> h1 \<and> H1 \<succeq> h1' \<and> H2 \<succeq> h2 \<and> H2 \<succeq> h2'
  \<and> (s1, h1), (s2, h2) \<Turnstile> J \<and> (s1, h1'), (s2, h2') \<Turnstile> J \<longrightarrow> h1' = h1 \<and> h2' = h2)"

lemma preciseI:
  assumes "\<And>s1 H1 h1 h1' s2 H2 h2 h2'. H1 \<succeq> h1 \<and> H1 \<succeq> h1' \<and> H2 \<succeq> h2 \<and> H2 \<succeq> h2' \<Longrightarrow>
        (s1, h1), (s2, h2) \<Turnstile> J \<Longrightarrow> (s1, h1'), (s2, h2') \<Turnstile> J \<Longrightarrow> h1' = h1 \<and> h2' = h2"
  shows "precise J"
  using assms precise_def by blast

lemma preciseE:
  assumes "precise J"
      and "H1 \<succeq> h1 \<and> H1 \<succeq> h1' \<and> H2 \<succeq> h2 \<and> H2 \<succeq> h2'"
      and "(s1, h1), (s2, h2) \<Turnstile> J \<and> (s1, h1'), (s2, h2') \<Turnstile> J"
    shows "h1' = h1 \<and> h2' = h2"
  using assms(1) assms(2) assms(3) precise_def by blast



definition unary where
  "unary J \<longleftrightarrow> (\<forall>s h s' h'. (s, h), (s, h) \<Turnstile> J \<and> (s', h'), (s', h') \<Turnstile> J \<longrightarrow> (s, h), (s', h') \<Turnstile> J)"

lemma unaryI:
  assumes "\<And>s1 h1 s2 h2. (s1, h1), (s1, h1) \<Turnstile> J \<and> (s2, h2), (s2, h2) \<Turnstile> J \<Longrightarrow> (s1, h1), (s2, h2) \<Turnstile> J"
    shows "unary J"
  using assms unary_def by blast

lemma unary_smallerI:
  assumes "\<And>\<sigma>1 \<sigma>2. \<sigma>1, \<sigma>1 \<Turnstile> J \<and> \<sigma>2, \<sigma>2 \<Turnstile> J \<Longrightarrow> \<sigma>1, \<sigma>2 \<Turnstile> J"
    shows "unary J"
  using assms unary_def by blast

lemma unaryE:
  assumes "unary J"
      and "(s, h), (s, h) \<Turnstile> J \<and> (s', h'), (s', h') \<Turnstile> J"
    shows "(s, h), (s', h') \<Turnstile> J"
  using assms(1) assms(2) unary_def by blast


definition entails :: "('i, 'a, nat) assertion \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> bool" where
  "entails A B \<longleftrightarrow> (\<forall>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> A \<longrightarrow> \<sigma>, \<sigma>' \<Turnstile> B)"

lemma entailsI:
  assumes "\<And>x y. x, y \<Turnstile> A \<Longrightarrow> x, y \<Turnstile> B"
  shows "entails A B"
  using assms entails_def by blast

lemma sat_points_to:
  assumes "(s, h :: ('i, 'a) heap), (s, h) \<Turnstile> PointsTo a \<pi> e"
  shows "get_fh h = [edenot a s \<mapsto> (\<pi>, edenot e s)]"
proof -
  have "get_fh h (edenot a s) = Some (\<pi>, edenot e s) \<and> dom (get_fh h) = {edenot a s}"
    using assms by auto
  then show ?thesis
    by fastforce
qed



lemma unary_inv_then_view:
  assumes "unary J"
  shows "unary (View f J e)"
proof (rule unaryI)
  fix s h s' h'
  assume asm0: "(s, h), (s, h) \<Turnstile> View f J e \<and> (s', h'), (s', h') \<Turnstile> View f J e"
  then show "(s, h), (s', h') \<Turnstile> View f J e"
    by (meson assms hyper_sat.simps(11) unaryE)
qed

lemma precise_inv_then_view:
  assumes "precise J"
  shows "precise (View f J e)"
proof (rule preciseI)
  fix s1 H1 h1 h1' s2 H2 h2 h2'
  assume asm0: "H1 \<succeq> h1 \<and> H1 \<succeq> h1' \<and> H2 \<succeq> h2 \<and> H2 \<succeq> h2'" "(s1, h1), (s2, h2) \<Turnstile> View f J e"
    "(s1, h1'), (s2, h2') \<Turnstile> View f J e"
  then show "h1' = h1 \<and> h2' = h2"
    by (meson assms hyper_sat.simps(11) preciseE)
qed

fun syntactic_unary :: "('i, 'a, nat) assertion \<Rightarrow> bool" where
  "syntactic_unary (Bool b) \<longleftrightarrow> True"
| "syntactic_unary (And A B) \<longleftrightarrow> syntactic_unary A \<and> syntactic_unary B"
| "syntactic_unary (Star A B) \<longleftrightarrow> syntactic_unary A \<and> syntactic_unary B"
| "syntactic_unary (Low e) \<longleftrightarrow> False"
| "syntactic_unary Emp \<longleftrightarrow> True"
| "syntactic_unary (PointsTo v va vb) \<longleftrightarrow> True"
| "syntactic_unary (Exists x A) \<longleftrightarrow> syntactic_unary A"
| "syntactic_unary (SharedGuard _ e) \<longleftrightarrow> True"
| "syntactic_unary (UniqueGuard _ e) \<longleftrightarrow> True"
| "syntactic_unary (View view A e) \<longleftrightarrow> syntactic_unary A"
| "syntactic_unary (PreSharedGuards _) \<longleftrightarrow> False"
| "syntactic_unary (PreUniqueGuards _) \<longleftrightarrow> False"
| "syntactic_unary EmptyFullGuards \<longleftrightarrow> True"
| "syntactic_unary (LowExp x) \<longleftrightarrow> False"
| "syntactic_unary (Imp b A) \<longleftrightarrow> False"

lemma syntactic_unary_implies_unary:
  assumes "syntactic_unary A"
  shows "unary A"
  using assms
proof (induct A)
  case (And A1 A2)
  show ?case
  proof (rule unary_smallerI)
    fix \<sigma>1 \<sigma>2
    assume "\<sigma>1, \<sigma>1 \<Turnstile> And A1 A2 \<and> \<sigma>2, \<sigma>2 \<Turnstile> And A1 A2"
    then have "\<sigma>1, \<sigma>2 \<Turnstile> A1 \<and> \<sigma>1, \<sigma>2 \<Turnstile> A2"
      using And unary_def
      by (metis hyper_sat.simps(3) prod.exhaust_sel syntactic_unary.simps(2))
    then show "\<sigma>1, \<sigma>2 \<Turnstile> And A1 A2"
      using hyper_sat.simps(3) by blast
  qed
next
  case (Star A B)
  then have "unary A \<and> unary B" by simp
  show ?case
  proof (rule unaryI)
    fix s1 h1 s2 h2
    assume asm0: "(s1, h1), (s1, h1) \<Turnstile> Star A B \<and> (s2, h2), (s2, h2) \<Turnstile> Star A B"
    then obtain a1 b1 a2 b2 where "Some h1 = Some a1 \<oplus> Some b1" "(s1, a1), (s1, a1) \<Turnstile> A" "(s1, b1), (s1, b1) \<Turnstile> B"
     "Some h2 = Some a2 \<oplus> Some b2" "(s2, a2), (s2, a2) \<Turnstile> A" "(s2, b2), (s2, b2) \<Turnstile> B"
      by (meson always_sat_refl hyper_sat.simps(4))
    then have "(s1, a1), (s2, a2) \<Turnstile> A \<and> (s1, b1), (s2, b2) \<Turnstile> B"
      using \<open>unary A \<and> unary B\<close> unaryE by blast
    then show "(s1, h1), (s2, h2) \<Turnstile> Star A B"
      using \<open>Some h1 = Some a1 \<oplus> Some b1\<close> \<open>Some h2 = Some a2 \<oplus> Some b2\<close> hyper_sat.simps(4) by blast
  qed
next
  case (Exists x A)
  then have "unary A" by simp
  show ?case
  proof (rule unaryI)
    fix s1 h1 s2 h2
    assume "(s1, h1), (s1, h1) \<Turnstile> Exists x A \<and> (s2, h2), (s2, h2) \<Turnstile> Exists x A"
    then obtain v1 v2 where "(s1(x := v1), h1), (s1(x := v1), h1) \<Turnstile> A \<and> (s2(x := v2), h2), (s2(x := v2), h2) \<Turnstile> A"
      by (meson always_sat_refl hyper_sat.simps(7))
    then have "(s1(x := v1), h1), (s2(x := v2), h2) \<Turnstile> A"
      using \<open>unary A\<close> unary_def by blast
    then show "(s1, h1), (s2, h2) \<Turnstile> Exists x A" by auto
  qed
next
  case (View view A x)
  then have "unary A" by simp
  show ?case
  proof (rule unaryI)
    fix s1 h1 s2 h2
    assume asm0: "(s1, h1), (s1, h1) \<Turnstile> View view A x \<and> (s2, h2), (s2, h2) \<Turnstile> View view A x"
    then have "(s1, h1), (s2, h2) \<Turnstile> A"
      by (meson \<open>unary A\<close> hyper_sat.simps(11) unaryE)
    then show "(s1, h1), (s2, h2) \<Turnstile> View view A x"
      using asm0 by fastforce
  qed
qed (auto simp add: unary_def)

record ('i, 'a, 'v) single_context =
  view :: "(loc \<rightharpoonup> val) \<Rightarrow> 'v"
  abstract_view :: "'v \<Rightarrow> 'v"
  saction :: "'v \<Rightarrow> 'a \<Rightarrow> 'v"
  uaction :: "'i \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'v"
  invariant :: "('i, 'a, 'v) assertion"

type_synonym ('i, 'a, 'v) cont = "('i, 'a, 'v) single_context option"

definition no_guard_assertion where
  "no_guard_assertion A \<longleftrightarrow> (\<forall>s1 h1 s2 h2. (s1, h1), (s2, h2) \<Turnstile> A \<longrightarrow> no_guard h1 \<and> no_guard h2)"

text \<open>Axiom that says that view only depends on the part of the heap described by inv\<close>
definition view_function_of_inv :: "('i, 'a, nat) single_context \<Rightarrow> bool" where
  "view_function_of_inv \<Gamma> \<longleftrightarrow> (\<forall>(h :: ('i, 'a) heap) (h' :: ('i, 'a) heap) s. (s, h), (s, h) \<Turnstile> invariant \<Gamma> \<and> (h' \<succeq> h)
  \<longrightarrow> view \<Gamma> (normalize (get_fh h)) = view \<Gamma> (normalize (get_fh h')))"

definition wf_indexed_precondition :: "('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wf_indexed_precondition pre \<longleftrightarrow> (\<forall>a b k. pre k a b \<longrightarrow> (pre k b a \<and> pre k a a))"

definition wf_precondition :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wf_precondition pre \<longleftrightarrow> (\<forall>a b. pre a b \<longrightarrow> (pre b a \<and> pre a a))"


lemma wf_precondition_rep_prec:
  assumes "wf_precondition pre"
  shows "Rep_precondition (Abs_precondition pre) = pre"
  using Abs_precondition_inverse[of pre] assms mem_Collect_eq wf_precondition_def[of pre]
  by blast


lemma wf_indexed_precondition_rep_prec:
  assumes "wf_indexed_precondition pre"
  shows "Rep_indexed_precondition (Abs_indexed_precondition pre) = pre"
  using Abs_indexed_precondition_inverse[of pre] assms mem_Collect_eq wf_indexed_precondition_def[of pre]
  by blast


definition LowView where
  "LowView f A x = (Exists x (And (View f A (\<lambda>s. s x)) (LowExp (Evar x))))"

lemma LowViewE:
  assumes "(s, h), (s', h') \<Turnstile> LowView f A x"
      and "x \<notin> fvA A"
    shows "(s, h), (s', h') \<Turnstile> A \<and> f (normalize (get_fh h)) = f (normalize (get_fh h'))"
proof -
  obtain v v' where "(s(x := v), h), (s'(x := v'), h') \<Turnstile> And (View f A (\<lambda>s. s x)) (LowExp (Evar x))"
    by (metis LowView_def assms(1) hyper_sat.simps(7))
  then obtain "(s(x := v), h), (s'(x := v'), h') \<Turnstile> View f A (\<lambda>s. s x)"
        "(s(x := v), h), (s'(x := v'), h') \<Turnstile> LowExp (Evar x)"
    using hyper_sat.simps(3) by blast
  then obtain "(s(x := v), h), (s'(x := v'), h') \<Turnstile> A" "v = v'"
      "f (normalize (get_fh h)) = f (normalize (get_fh h'))"
    by simp
  moreover have "(s, h), (s', h') \<Turnstile> A"
    by (meson agrees_same agrees_update assms(2) calculation(1) sat_comm_aux)
  ultimately show ?thesis by blast
qed

lemma LowViewI:
  assumes "(s, h), (s', h') \<Turnstile> A"
      and "f (normalize (get_fh h)) = f (normalize (get_fh h'))"
      and "x \<notin> fvA A"
    shows "(s, h), (s', h') \<Turnstile> LowView f A x"
proof -
  let ?s = "s(x := f (normalize (get_fh h)))"
  let ?s' = "s'(x := f (normalize (get_fh h')))"
  have "(?s, h), (?s', h') \<Turnstile> A"
    by (meson agrees_same_aux agrees_update assms(1) assms(3) sat_comm_aux)
  then have "(?s, h), (?s', h') \<Turnstile> And (View f A (\<lambda>s. s x)) (LowExp (Evar x))"
    using assms(2) by auto
  then show ?thesis using LowView_def
    by (metis hyper_sat.simps(7))
qed

definition disjoint :: "('a set) \<Rightarrow> ('a set) \<Rightarrow> bool" 
  where "disjoint h1 h2 = (h1 \<inter> h2 = {})"

definition unambiguous where
  "unambiguous A x \<longleftrightarrow> (\<forall>s1 h1 s2 h2 v1 v2 v1' v2'. (s1(x := v1), h1), (s2(x := v2), h2) \<Turnstile> A
  \<and> (s1(x := v1'), h1), (s2(x := v2'), h2) \<Turnstile> A \<longrightarrow> v1 = v1' \<and> v2 = v2')"

definition all_axioms :: "('v \<Rightarrow> 'w) \<Rightarrow> ('v \<Rightarrow> 'a \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('i \<Rightarrow> 'v \<Rightarrow> 'b \<Rightarrow> 'v) \<Rightarrow> ('i \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_axioms \<alpha> sact spre uact upre \<longleftrightarrow>

\<comment>\<open>Every action's relational precondition is sufficient to preserve the low-ness of the abstract view of the resource value:\<close>
  (\<forall>v v' sarg sarg'. \<alpha> v = \<alpha> v' \<and> spre sarg sarg' \<longrightarrow> \<alpha> (sact v sarg) = \<alpha> (sact v' sarg')) \<and>
  (\<forall>v v' uarg uarg' i. \<alpha> v = \<alpha> v' \<and> upre i uarg uarg' \<longrightarrow> \<alpha> (uact i v uarg) = \<alpha> (uact i v' uarg')) \<and>

  (\<forall>sarg sarg'. spre sarg sarg' \<longrightarrow> spre sarg' sarg') \<and>
  (\<forall>uarg uarg' i. upre i uarg uarg' \<longrightarrow> upre i uarg' uarg') \<and>

\<comment>\<open>All relevant pairs of actions commute w.r.t. the abstract view:\<close>
  (\<forall>v v' sarg sarg'. \<alpha> v = \<alpha> v' \<and> spre sarg sarg \<and> spre sarg' sarg' \<longrightarrow> \<alpha> (sact (sact v sarg) sarg') = \<alpha> (sact (sact v' sarg') sarg)) \<and>
  (\<forall>v v' sarg uarg i. \<alpha> v = \<alpha> v' \<and> spre sarg sarg \<and> upre i uarg uarg \<longrightarrow> \<alpha> (sact (uact i v uarg) sarg) = \<alpha> (uact i (sact v' sarg) uarg)) \<and>
  (\<forall>v v' uarg uarg' i i'. i \<noteq> i' \<and> \<alpha> v = \<alpha> v' \<and> upre i uarg uarg \<and> upre i' uarg' uarg'
  \<longrightarrow> \<alpha> (uact i' (uact i v uarg) uarg') = \<alpha> (uact i (uact i' v' uarg') uarg))"

subsection \<open>Rules of the Logic\<close>

inductive CommCSL :: "('i, 'a, nat) cont \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> cmd \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> bool"
   ("_ \<turnstile> {_} _ {_}" [51,0,0] 81) where
  RuleSkip: "\<Delta> \<turnstile> {P} Cskip {P}"
| RuleAssign: "\<lbrakk> \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) ; collect_existentials P \<inter> fvE E = {} \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> {subA x E P} Cassign x E {P} "
| RuleNew: "\<lbrakk> x \<notin> fvE E; \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma> \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> {Emp} Calloc x E {PointsTo (Evar x) pwrite E}"
| RuleWrite: "\<lbrakk> \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> view_function_of_inv \<Gamma> ; v \<notin> fvE loc \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {Exists v (PointsTo loc pwrite (Evar v))} Cwrite loc E {PointsTo loc pwrite E}"
| "\<lbrakk> \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma> ; x \<notin> fvE E \<union> fvE e \<rbrakk> \<Longrightarrow>
  \<Delta> \<turnstile> {PointsTo E \<pi> e} Cread x E {And (PointsTo E \<pi> e) (Bool (Beq (Evar x) e))}"
| RuleShare: "\<lbrakk> \<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr> ; all_axioms \<alpha> sact spre uact upre ;
  Some \<Gamma> \<turnstile> {Star P EmptyFullGuards} C {Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre)))};
  view_function_of_inv \<Gamma> ; unary J ; precise J ; wf_indexed_precondition upre ; wf_precondition spre ; x \<notin> fvA J ;
  no_guard_assertion (Star P (LowView (\<alpha> \<circ> f) J x)) \<rbrakk> \<Longrightarrow> None \<turnstile> {Star P (LowView (\<alpha> \<circ> f) J x)} C {Star Q (LowView (\<alpha> \<circ> f) J x)}"
| RuleAtomicUnique: "\<lbrakk> \<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr> ;
  no_guard_assertion P ; no_guard_assertion Q ;
    None \<turnstile> {Star P (View f J (\<lambda>s. s x))} C {Star Q (View f J (\<lambda>s. uact index (s x) (map_to_arg (s uarg))))} ;
    precise J ; unary J ; view_function_of_inv \<Gamma> ; x \<notin> fvC C \<union> fvA P \<union> fvA Q \<union> fvA J ; uarg \<notin> fvC C ; 
    l \<notin> fvC C ; x \<notin> fvS (\<lambda>s. map_to_list (s l)) ; x \<notin> fvS (\<lambda>s. map_to_arg (s uarg) # map_to_list (s l)) \<rbrakk>
  \<Longrightarrow> Some \<Gamma> \<turnstile> {Star P (UniqueGuard index (\<lambda>s. map_to_list (s l)))} Catomic C {Star Q (UniqueGuard index (\<lambda>s. map_to_arg (s uarg) # map_to_list (s l)))}"
| RuleAtomicShared: "\<lbrakk> \<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr> ; no_guard_assertion P ; no_guard_assertion Q ;
  None \<turnstile> {Star P (View f J (\<lambda>s. s x))} C {Star Q (View f J (\<lambda>s. sact (s x) (map_to_arg (s sarg))))} ;
  precise J ; unary J ; view_function_of_inv \<Gamma> ; x \<notin> fvC C \<union> fvA P \<union> fvA Q \<union> fvA J ; sarg \<notin> fvC C ;
  ms \<notin> fvC C ; x \<notin> fvS (\<lambda>s. map_to_multiset (s ms)) ; x \<notin> fvS (\<lambda>s. {# map_to_arg (s sarg) #} + map_to_multiset (s ms)) \<rbrakk>
  \<Longrightarrow> Some \<Gamma> \<turnstile> {Star P (SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms)))} Catomic C {Star Q (SharedGuard \<pi> (\<lambda>s. {# map_to_arg (s sarg) #} + map_to_multiset (s ms)))}"
| RulePar: "\<lbrakk> \<Delta> \<turnstile> {P1} C1 {Q1} ; \<Delta> \<turnstile> {P2} C2 {Q2} ; disjoint (fvA P1 \<union> fvC C1 \<union> fvA Q1) (wrC C2) ;
  disjoint (fvA P2 \<union> fvC C2 \<union> fvA Q2) (wrC C1) ; \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C2) ;
  \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C1) ; precise P1 \<or> precise P2 \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {Star P1 P2} Cpar C1 C2 {Star Q1 Q2}"
| RuleIf1: "\<lbrakk> \<Delta> \<turnstile> {And P (Bool b)} C1 {Q} ; \<Delta> \<turnstile> {And P (Bool (Bnot b))} C2 {Q} \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {And P (Low b)} Cif b C1 C2 {Q}"
| RuleIf2: "\<lbrakk> \<Delta> \<turnstile> {And P (Bool b)} C1 {Q} ; \<Delta> \<turnstile> {And P (Bool (Bnot b))} C2 {Q} ; unary Q \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {P} Cif b C1 C2 {Q}"
| RuleSeq: "\<lbrakk> \<Delta> \<turnstile> {P} C1 {R} ; \<Delta> \<turnstile> {R} C2 {Q} \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> {P} Cseq C1 C2 {Q}"
| RuleFrame: "\<lbrakk> \<Delta> \<turnstile> {P} C {Q} ; disjoint (fvA R) (wrC C) ; precise P \<or> precise R \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {Star P R} C {Star Q R}"
| RuleCons: "\<lbrakk> \<Delta> \<turnstile> {P'} C {Q'} ; entails P P' ; entails Q' Q \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> {P} C {Q}"
| RuleExists: "\<lbrakk> \<Delta> \<turnstile> {P} C {Q} ; x \<notin> fvC C ; \<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) ; unambiguous P x \<rbrakk>
  \<Longrightarrow> \<Delta> \<turnstile> {Exists x P} C {Exists x Q}"
| RuleWhile1: "\<Delta> \<turnstile> {And I (Bool b)} C {And I (Low b)} \<Longrightarrow> \<Delta> \<turnstile> {And I (Low b)} Cwhile b C {And I (Bool (Bnot b))}"
| RuleWhile2: "\<lbrakk> unary I ; \<Delta> \<turnstile> {And I (Bool b)} C {I} \<rbrakk> \<Longrightarrow> \<Delta> \<turnstile> {I} Cwhile b C {And I (Bool (Bnot b))}"

end