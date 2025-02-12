theory Implicational_Logic_Natural_Deduction imports Main begin

datatype form =
  Pro nat (\<open>\<cdot>\<close>) |
  Imp form form (infixr \<open>\<rightarrow>\<close> 100)

primrec semantics (infix \<open>\<Turnstile>\<close> 50) where
  \<open>I \<Turnstile> \<cdot>n = I n\<close> |
  \<open>I \<Turnstile> p \<rightarrow> q = (I \<Turnstile> p \<longrightarrow> I \<Turnstile> q)\<close>

inductive Calculus (infix \<open>\<leadsto>\<close> 50) where
  Assm: \<open>p \<in> set A \<Longrightarrow> A \<leadsto> p\<close> |
  ImpI: \<open>p # A \<leadsto> q \<Longrightarrow> A \<leadsto> p \<rightarrow> q\<close> |
  ImpE: \<open>A \<leadsto> p \<rightarrow> q \<Longrightarrow> A \<leadsto> p \<Longrightarrow> A \<leadsto> q\<close> |
  ImpC: \<open>p \<rightarrow> _ # A \<leadsto> p \<Longrightarrow> A \<leadsto> p\<close>

abbreviation natural_deduction (\<open>\<turnstile> _\<close> [100] 100) where \<open>\<turnstile> p \<equiv> [] \<leadsto> p\<close>

theorem soundness: \<open>A \<leadsto> p \<Longrightarrow> \<forall>p \<in> set A. I \<Turnstile> p \<Longrightarrow> I \<Turnstile> p\<close>
  by (induct rule: Calculus.induct) auto

lemma weaken': \<open>A \<leadsto> p \<Longrightarrow> set A = set B \<Longrightarrow> B \<leadsto> p\<close>
proof (induct arbitrary: B rule: Calculus.induct)
  case ImpC
  with Calculus.ImpC show ?case
    using list.set(2) by metis
qed (auto intro: Calculus.intros)

lemma weak: \<open>A \<leadsto> p \<Longrightarrow> q # A \<leadsto> p\<close>
proof (induct rule: Calculus.induct)
  case ImpI
  with Calculus.ImpI show ?case
    using insert_commute list.set(2) weaken' by (metis (full_types))
next
  case ImpC
  with Calculus.ImpC show ?case
    using insert_commute list.set(2) weaken' by (metis (full_types))
qed (auto intro: Calculus.intros)

lemma add_assumptions: \<open>\<turnstile> p \<Longrightarrow> A \<leadsto> p\<close>
  by (induct A) (simp_all add: weak)

lemma weaken: \<open>A \<leadsto> p \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> B \<leadsto> p\<close>
proof (induct A arbitrary: p)
  case (Cons q A)
  moreover from this have \<open>A \<leadsto> q \<rightarrow> p\<close> and \<open>set A \<subseteq> set B\<close> and \<open>B \<leadsto> q\<close>
    by (simp_all add: Assm ImpI)
  ultimately show ?case
    using ImpE by blast
qed (simp add: add_assumptions)

lemma deduct: \<open>A \<leadsto> p \<rightarrow> q \<Longrightarrow> p # A \<leadsto> q\<close>
  using Assm ImpE list.set_intros(1) weak by meson

lemma Peirce: \<open>\<turnstile> ((p \<rightarrow> q) \<rightarrow> p) \<rightarrow> p\<close>
  using Assm ImpC ImpI deduct list.set_intros(1) by meson

lemma Simp: \<open>\<turnstile> p \<rightarrow> q \<rightarrow> p\<close>
  by (simp add: Assm ImpI)

lemma Tran: \<open>\<turnstile> (p \<rightarrow> q) \<rightarrow> (q \<rightarrow> r) \<rightarrow> p \<rightarrow> r\<close>
proof -
  have \<open>[p, q \<rightarrow> r, p \<rightarrow> q] \<leadsto> r\<close>
    using Assm ImpE list.set_intros(1) weak by meson
  then show ?thesis
    using ImpI by blast
qed

lemma Swap: \<open>\<turnstile> (p \<rightarrow> q \<rightarrow> r) \<rightarrow> q \<rightarrow> p \<rightarrow> r\<close>
proof -
  have \<open>[p, q, p \<rightarrow> q \<rightarrow> r] \<leadsto> r\<close>
    using Assm ImpE list.set_intros(1) weak by meson
  then show ?thesis
    using ImpI by blast
qed

lemma Tran': \<open>\<turnstile> (q \<rightarrow> r) \<rightarrow> (p \<rightarrow> q) \<rightarrow> p \<rightarrow> r\<close>
  using ImpE Swap Tran .

lemma Imp1: \<open>\<turnstile> (q \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using ImpE Peirce Tran Tran' by meson

lemma Imp2: \<open>\<turnstile> ((r \<rightarrow> s) \<rightarrow> s) \<rightarrow> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
  using ImpE Tran ImpE Tran Simp .

lemma Imp3: \<open>\<turnstile> ((q \<rightarrow> s) \<rightarrow> s) \<rightarrow> (r \<rightarrow> s) \<rightarrow> (q \<rightarrow> r) \<rightarrow> s\<close>
  using ImpE Tran Tran' by meson

fun pros where
  \<open>pros (p \<rightarrow> q) = remdups (pros p @ pros q)\<close> |
  \<open>pros p = (case p of \<cdot>n \<Rightarrow> [n] | _ \<Rightarrow> [])\<close>

lemma distinct_pros: \<open>distinct (pros p)\<close>
  by induct simp_all

abbreviation \<open>lift t s p \<equiv> if t then (p \<rightarrow> s) \<rightarrow> s else p \<rightarrow> s\<close>

abbreviation \<open>lifts I s \<equiv> map (\<lambda>n. lift (I n) s (\<cdot>n))\<close>

lemma lifts_weaken: \<open>lifts I s l \<leadsto> p \<Longrightarrow> set l \<subseteq> set l' \<Longrightarrow> lifts I s l' \<leadsto> p\<close>
proof -
  assume \<open>lifts I s l \<leadsto> p\<close>
  moreover assume \<open>set l \<subseteq> set l'\<close>
  then have \<open>set ((lifts I s) l) \<subseteq> set ((lifts I s) l')\<close>
    by auto
  ultimately show ?thesis
    using weaken by blast
qed

lemma lifts_pros_lift: \<open>lifts I s (pros p) \<leadsto> lift (I \<Turnstile> p) s p\<close>
proof (induct p)
  case (Imp q r)
  consider \<open>\<not> I \<Turnstile> q\<close> | \<open>I \<Turnstile> r\<close> | \<open>I \<Turnstile> q\<close> and \<open>\<not> I \<Turnstile> r\<close>
    by blast
  then show ?case
  proof cases
    case 1
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> q \<rightarrow> s\<close>
      using Imp(1) lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
      using Imp1 ImpE add_assumptions by blast
    with 1 show ?thesis
      by simp
  next
    case 2
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> (r \<rightarrow> s) \<rightarrow> s\<close>
      using Imp(2) lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> ((q \<rightarrow> r) \<rightarrow> s) \<rightarrow> s\<close>
      using Imp2 ImpE add_assumptions by blast
    with 2 show ?thesis
      by simp
  next
    case 3
    then have
      \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> (q \<rightarrow> s) \<rightarrow> s\<close>
      \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> r \<rightarrow> s\<close>
      using Imp lifts_weaken[where l' = \<open>pros (q \<rightarrow> r)\<close>] by simp_all
    then have \<open>lifts I s (pros (q \<rightarrow> r)) \<leadsto> (q \<rightarrow> r) \<rightarrow> s\<close>
      using Imp3 ImpE add_assumptions by blast
    with 3 show ?thesis
      by simp
  qed
qed (simp add: Assm)

lemma lifts_pros: \<open>I \<Turnstile> p \<Longrightarrow> lifts I p (pros p) \<leadsto> p\<close>
proof -
  assume \<open>I \<Turnstile> p\<close>
  then have \<open>lifts I p (pros p) \<leadsto> (p \<rightarrow> p) \<rightarrow> p\<close>
    using lifts_pros_lift[of I p p] by simp
  then show ?thesis
    using ImpC deduct by blast
qed

theorem completeness: \<open>\<forall>I. I \<Turnstile> p \<Longrightarrow> \<turnstile> p\<close>
proof -
  let ?A = \<open>\<lambda>l I. lifts I p l \<leadsto> p\<close>
  let ?B = \<open>\<lambda>l. \<forall>I. ?A l I \<and> distinct l\<close>
  assume \<open>\<forall>I. I \<Turnstile> p\<close>
  moreover have \<open>?B l \<Longrightarrow> (\<And>n l. ?B (n # l) \<Longrightarrow> ?B l) \<Longrightarrow> ?B []\<close> for l
    by (induct l) blast+
  moreover have \<open>?B (n # l) \<Longrightarrow> ?B l\<close> for n l
  proof -
    assume *: \<open>?B (n # l)\<close>
    show \<open>?B l\<close>
    proof
      fix I
      from * have
        \<open>?A (n # l) (I(n := True))\<close>
        \<open>?A (n # l) (I(n := False))\<close>
        by blast+
      moreover from * have \<open>\<forall>m \<in> set l. \<forall>t. (I(n := t)) m = I m\<close>
        by simp
      ultimately have
        \<open>((\<cdot>n \<rightarrow> p) \<rightarrow> p) # lifts I p l \<leadsto> p\<close>
        \<open>(\<cdot>n \<rightarrow> p) # lifts I p l \<leadsto> p\<close>
        by (simp_all cong: map_cong)
      then have \<open>?A l I\<close>
        using ImpE ImpI by blast
      moreover from * have \<open>distinct (n # l)\<close>
        by blast
      ultimately show \<open>?A l I \<and> distinct l\<close>
        by simp
    qed
  qed
  ultimately have \<open>?B []\<close>
    using lifts_pros distinct_pros by blast
  then show ?thesis
    by simp
qed

primrec chain where
  \<open>chain p [] = p\<close> |
  \<open>chain p (q # A) = q \<rightarrow> chain p A\<close>

lemma chain_rev: \<open>B \<leadsto> chain p A \<Longrightarrow> rev A @ B \<leadsto> p\<close>
  by (induct A arbitrary: B) (simp_all add: deduct)

lemma chain_deduct: \<open>\<turnstile> chain p A \<Longrightarrow> A \<leadsto> p\<close>
proof (induct A)
  case (Cons q A)
  then have \<open>rev (q # A) @ [] \<leadsto> p\<close>
    using chain_rev by blast
  moreover have \<open>set (rev (q # A) @ []) = set (q # A)\<close>
    by simp
  ultimately show ?case
    using weaken by blast
qed simp

lemma chain_semantics: \<open>I \<Turnstile> chain p A = ((\<forall>p \<in> set A. I \<Turnstile> p) \<longrightarrow> I \<Turnstile> p)\<close>
  by (induct A) auto

theorem main: \<open>A \<leadsto> p = (\<forall>I. (\<forall>p \<in> set A. I \<Turnstile> p) \<longrightarrow> I \<Turnstile> p)\<close>
  using chain_deduct chain_semantics completeness soundness by meson

end
