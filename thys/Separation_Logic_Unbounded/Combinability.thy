section \<open>Combinability\<close>

text \<open>This section corresponds to Section 3 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theory Combinability
  imports UnboundedLogic
begin

context logic
begin

text \<open>The definition of combinable assertions corresponds to Definition 4 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

definition combinable :: "('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "combinable \<Delta> A \<longleftrightarrow> (\<forall>p q. Star (Mult p A) (Mult q A), \<Delta> \<turnstile> Mult (sadd p q) A)"

lemma combinable_instantiate:
  assumes "combinable \<Delta> A"
      and "a, s, \<Delta> \<Turnstile> A"
      and "b, s, \<Delta> \<Turnstile> A"
      and "Some x = p \<odot> a \<oplus> q \<odot> b"
    shows "x, s, \<Delta> \<Turnstile> Mult (sadd p q) A"
  by (meson assms(1) assms(2) assms(3) assms(4) combinable_def entails_def logic.sat.simps(2) logic_axioms sat.simps(1))

lemma combinable_instantiate_one:
  assumes "combinable \<Delta> A"
      and "a, s, \<Delta> \<Turnstile> A"
      and "b, s, \<Delta> \<Turnstile> A"
      and "Some x = p \<odot> a \<oplus> q \<odot> b"
      and "sadd p q = one"
    shows "x, s, \<Delta> \<Turnstile> A"
  using assms(1) assms(2) assms(3) assms(4) assms(5) combinable_instantiate one_neutral by fastforce

lemma combinableI_old:
  assumes "\<And>a b p q x \<sigma> s. a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = (sadd p q) \<odot> x \<Longrightarrow> x, s, \<Delta> \<Turnstile> A"
  shows "combinable \<Delta> A"
proof -
  have "\<And>p q. Star (Mult p A) (Mult q A), \<Delta> \<turnstile> Mult (sadd p q) A"
  proof (rule entailsI)
    fix p q \<sigma> s
    assume "\<sigma>, s, \<Delta> \<Turnstile> Star (Mult p A) (Mult q A)"
    then obtain a b where "a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b"
      by auto
    moreover obtain x where "\<sigma> = (sadd p q) \<odot> x"
      using unique_inv by auto
    ultimately have "x, s, \<Delta> \<Turnstile> A" using assms
      by blast
    then show "\<sigma>, s, \<Delta> \<Turnstile> Mult (sadd p q) A"
      using \<open>\<sigma> = sadd p q \<odot> x\<close> by fastforce
    qed
  then show ?thesis
    by (simp add: combinable_def)
qed


lemma combinableI:
  assumes "\<And>a b p q x \<sigma> s. a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one \<Longrightarrow> x, s, \<Delta> \<Turnstile> A"
  shows "combinable \<Delta> A"
proof (rule combinableI_old)
  fix a b p q x \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x"
  let ?p = "smult (sinv (sadd p q)) p"
  let ?q = "smult (sinv (sadd p q)) q"
  have "Some x = ?p \<odot> a \<oplus> ?q \<odot> b"
  proof -
    have "Some ((smult (sinv (sadd p q)) (sadd p q)) \<odot> x) = ?p \<odot> a \<oplus> ?q \<odot> b"
      by (metis \<open>a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> double_mult logic.plus_mult logic_axioms)
    then show ?thesis
      by (simp add: one_neutral sinv_inverse smult_comm)
  qed
  moreover have "sadd ?p ?q = one"
    by (metis logic.smult_comm logic_axioms sinv_inverse smult_distrib)
  ultimately show "x, s, \<Delta> \<Turnstile> A"
    using \<open>a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> A \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> assms by blast
qed


lemma combinable_wand:
  assumes "combinable \<Delta> B"
    shows "combinable \<Delta> (Wand A B)"
proof (rule combinableI_old)
  fix a b p q x \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x"
  show "x, s, \<Delta> \<Turnstile> Wand A B"
  proof (rule sat_wand)
    fix aa \<sigma>'
    assume "aa, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = x \<oplus> aa"
    then have "Some ((sadd p q) \<odot> \<sigma>') = \<sigma> \<oplus> ((sadd p q) \<odot> aa)"
      by (simp add: \<open>a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> plus_mult)
    moreover have "Some ((sadd p q) \<odot> aa) = p \<odot> aa \<oplus> q \<odot> aa"
      by (simp add: distrib_mult)
    moreover have "a ## aa"
    proof -
      have "p \<odot> a ## (sadd p q) \<odot> aa"
        by (metis \<open>a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> asso2 calculation(1) commutative compatible_def option.discI)
      then show ?thesis
        using compatible_multiples by blast
    qed
    then obtain aaa where "Some aaa = a \<oplus> aa"
      using compatible_def by auto
    moreover have "b ## aa"
    proof -
      have "q \<odot> b ## (sadd p q) \<odot> aa"
        by (metis \<open>a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> asso2 calculation(1) compatible_def option.discI)
      then show ?thesis
        using compatible_multiples by blast
    qed
    then obtain baa where "Some baa = b \<oplus> aa"
      using compatible_def by auto
    ultimately have "Some (mult (sadd p q) \<sigma>') = p \<odot> aaa \<oplus> q \<odot> baa"
    proof -
      obtain a1 where "Some a1 = \<sigma> \<oplus> (p \<odot> aa)"
        by (metis \<open>Some (sadd p q \<odot> \<sigma>') = \<sigma> \<oplus> sadd p q \<odot> aa\<close> compatible_multiples option.exhaust_sel pre_logic.compatible_def unique_inv)
      then obtain a2 where "Some a2 = p \<odot> a \<oplus> (p \<odot> aa)"
        by (meson \<open>\<And>thesis. (\<And>aaa. Some aaa = a \<oplus> aa \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> plus_mult)
      then have "Some a1 = a2 \<oplus> q \<odot> b"
      proof -
        obtain bc where "q \<odot> b \<oplus> p \<odot> aa = Some bc"
          by (metis \<open>b ## aa\<close> compatible_iff compatible_multiples one_neutral option.exhaust_sel pre_logic.compatible_def)
        then have "\<sigma> \<oplus> p \<odot> aa = p \<odot> a \<oplus> bc"
          using asso1[of "p \<odot> a" "q \<odot> b" \<sigma> "p \<odot> aa" bc]
          by (metis \<open>a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close>)
        then show ?thesis
          by (metis \<open>Some a1 = \<sigma> \<oplus> p \<odot> aa\<close> \<open>Some a2 = p \<odot> a \<oplus> p \<odot> aa\<close> \<open>q \<odot> b \<oplus> p \<odot> aa = Some bc\<close> asso1 commutative)
      qed
      moreover have "a2 = p \<odot> aaa"
        by (metis \<open>Some a2 = p \<odot> a \<oplus> p \<odot> aa\<close> \<open>Some aaa = a \<oplus> aa\<close> option.inject plus_mult)
      moreover have "Some (q \<odot> baa) = q \<odot> b \<oplus> q \<odot> aa"
        by (simp add: \<open>Some baa = b \<oplus> aa\<close> plus_mult)
      ultimately show ?thesis
        by (metis \<open>Some (sadd p q \<odot> \<sigma>') = \<sigma> \<oplus> sadd p q \<odot> aa\<close> \<open>Some (sadd p q \<odot> aa) = p \<odot> aa \<oplus> q \<odot> aa\<close> \<open>Some a1 = \<sigma> \<oplus> p \<odot> aa\<close> asso1)
    qed
    moreover have "aaa, s, \<Delta> \<Turnstile> B \<and> baa, s, \<Delta> \<Turnstile> B"
      using \<open>Some aaa = a \<oplus> aa\<close> \<open>Some baa = b \<oplus> aa\<close> \<open>a, s, \<Delta> \<Turnstile> Wand A B \<and> b, s, \<Delta> \<Turnstile> Wand A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> \<open>aa, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = x \<oplus> aa\<close> by auto
    ultimately have "mult (sadd p q) \<sigma>', s, \<Delta> \<Turnstile> Mult (sadd p q) B"
      by (meson assms logic.combinable_def logic.entails_def logic_axioms sat.simps(1) sat.simps(2))
    then show "\<sigma>', s, \<Delta> \<Turnstile> B"
      using can_divide sat.simps(1) by metis
  qed
qed

lemma combinable_star:
  assumes "combinable \<Delta> A"
      and "combinable \<Delta> B"
    shows "combinable \<Delta> (Star A B)"
proof (rule combinableI_old)
  fix a b p q x \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> Star A B \<and> b, s, \<Delta> \<Turnstile> Star A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x"
  then obtain aa ab ba bb where "Some a = aa \<oplus> ab" "Some b = ba \<oplus> bb" "aa, s, \<Delta> \<Turnstile> A"
   "ab, s, \<Delta> \<Turnstile> B" "ba, s, \<Delta> \<Turnstile> A" "bb, s, \<Delta> \<Turnstile> B"
    by auto
  then obtain xa xb where "Some xa = p \<odot> aa \<oplus> q \<odot> ba" "Some xb = p \<odot> ab \<oplus> q \<odot> bb"
    by (metis \<open>a, s, \<Delta> \<Turnstile> Star A B \<and> b, s, \<Delta> \<Turnstile> Star A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> asso2 commutative compatible_iff compatible_multiples one_neutral option.discI option.exhaust_sel pre_logic.compatible_def)
  then have "xa, s, \<Delta> \<Turnstile> Mult (sadd p q) A"
    by (meson \<open>aa, s, \<Delta> \<Turnstile> A\<close> \<open>ba, s, \<Delta> \<Turnstile> A\<close> assms(1) entails_def logic.combinable_def logic.sat.simps(1) logic.sat.simps(2) logic_axioms)
  moreover have "xb, s, \<Delta> \<Turnstile> Mult (sadd p q) B"
    by (meson \<open>Some xb = p \<odot> ab \<oplus> q \<odot> bb\<close> \<open>ab, s, \<Delta> \<Turnstile> B\<close> \<open>bb, s, \<Delta> \<Turnstile> B\<close> assms(2) combinable_def entails_def sat.simps(1) sat.simps(2))
  moreover have "Some \<sigma> = xa \<oplus> xb"
    using \<open>Some a = aa \<oplus> ab\<close> \<open>Some b = ba \<oplus> bb\<close> \<open>Some xa = p \<odot> aa \<oplus> q \<odot> ba\<close> \<open>Some xb = p \<odot> ab \<oplus> q \<odot> bb\<close> \<open>a, s, \<Delta> \<Turnstile> Star A B \<and> b, s, \<Delta> \<Turnstile> Star A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> move_sum plus_mult by blast
  then obtain xa' xb' where "Some x = xa' \<oplus> xb'" "xa = sadd p q \<odot> xa'" "xb = sadd p q \<odot> xb'"
    by (metis \<open>a, s, \<Delta> \<Turnstile> Star A B \<and> b, s, \<Delta> \<Turnstile> Star A B \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b \<and> \<sigma> = sadd p q \<odot> x\<close> plus_mult unique_inv)
  ultimately show "x, s, \<Delta> \<Turnstile> Star A B"
    by (metis logic.can_divide logic_axioms sat.simps(1) sat.simps(2))
qed

lemma combinable_mult:
  assumes "combinable \<Delta> A"
  shows "combinable \<Delta> (Mult \<pi> A)"
proof (rule combinableI)
  fix a b p q x \<sigma> s
  assume asm: "a, s, \<Delta> \<Turnstile> Mult \<pi> A \<and> b, s, \<Delta> \<Turnstile> Mult \<pi> A \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  then obtain a' b' where "a', s, \<Delta> \<Turnstile> A" "b', s, \<Delta> \<Turnstile> A" "a = \<pi> \<odot> a'" "b = \<pi> \<odot> b'" by auto

  let ?p = "smult p \<pi>"
  let ?q = "smult q \<pi>"

  have "Some x = ?p \<odot> a' \<oplus> ?q \<odot> b'"
    by (simp add: \<open>a = \<pi> \<odot> a'\<close> \<open>b = \<pi> \<odot> b'\<close> asm double_mult)
  moreover have "sadd ?p ?q = \<pi>"
    using asm smult_comm smult_distrib sone_neutral by force
  ultimately show "x, s, \<Delta> \<Turnstile> Mult \<pi> A"
    by (metis \<open>a', s, \<Delta> \<Turnstile> A\<close> \<open>b', s, \<Delta> \<Turnstile> A\<close> assms combinable_instantiate)
qed

lemma combinable_and:
  assumes "combinable \<Delta> A"
      and "combinable \<Delta> B"
    shows "combinable \<Delta> (And A B)"
proof (rule combinableI)
  fix a b p q x \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> And A B \<and> b, s, \<Delta> \<Turnstile> And A B \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  then obtain "a, s, \<Delta> \<Turnstile> A" "b, s, \<Delta> \<Turnstile> A" "a, s, \<Delta> \<Turnstile> B" "b, s, \<Delta> \<Turnstile> B" by auto
  then show "x, s, \<Delta> \<Turnstile> And A B"
    by (meson \<open>a, s, \<Delta> \<Turnstile> And A B \<and> b, s, \<Delta> \<Turnstile> And A B \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one\<close> assms(1) assms(2) combinable_instantiate_one sat.simps(7))
qed


lemma combinable_forall:
  assumes "combinable \<Delta> A"
    shows "combinable \<Delta> (Forall x A)"
proof (rule combinableI)
  fix a b p q y \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> Forall x A \<and> b, s, \<Delta> \<Turnstile> Forall x A \<and> Some y = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  show "y, s, \<Delta> \<Turnstile> Forall x A"
  proof (rule sat_forall)
    fix v show "y, s(x := v), \<Delta> \<Turnstile> A"
      by (meson \<open>a, s, \<Delta> \<Turnstile> Forall x A \<and> b, s, \<Delta> \<Turnstile> Forall x A \<and> Some y = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one\<close> assms combinable_instantiate_one sat.simps(9))
  qed
qed




definition unambiguous where
  "unambiguous \<Delta> A x \<longleftrightarrow> (\<forall>\<sigma>1 \<sigma>2 v1 v2 s. \<sigma>1 ## \<sigma>2 \<and> \<sigma>1, s(x := v1), \<Delta> \<Turnstile> A \<and> \<sigma>2, s(x := v2), \<Delta> \<Turnstile> A \<longrightarrow> v1 = v2)"

lemma unambiguousI:
  assumes "\<And>\<sigma>1 \<sigma>2 v1 v2 s. \<sigma>1 ## \<sigma>2 \<and> \<sigma>1, s(x := v1), \<Delta> \<Turnstile> A \<and> \<sigma>2, s(x := v2), \<Delta> \<Turnstile> A \<Longrightarrow> v1 = v2"
  shows "unambiguous \<Delta> A x"
  by (simp add: assms unambiguous_def)

lemma unambiguous_star:
  assumes "unambiguous \<Delta> A x"
  shows "unambiguous \<Delta> (Star A B) x"
proof (rule unambiguousI)
  fix \<sigma>1 \<sigma>2 v1 v2 s
  assume "\<sigma>1 ## \<sigma>2 \<and> \<sigma>1, s(x := v1), \<Delta> \<Turnstile> Star A B \<and> \<sigma>2, s(x := v2), \<Delta> \<Turnstile> Star A B"
  then obtain a1 b1 a2 b2 where "Some \<sigma>1 = a1 \<oplus> b1" "Some \<sigma>2 = a2 \<oplus> b2" "a1, s(x := v1), \<Delta> \<Turnstile> A"
 "a2, s(x := v2), \<Delta> \<Turnstile> A" "b1, s(x := v1), \<Delta> \<Turnstile> B" "b2, s(x := v2), \<Delta> \<Turnstile> B" by auto
  then have "a1 ## a2"
    by (metis \<open>\<sigma>1 ## \<sigma>2 \<and> \<sigma>1, s(x := v1), \<Delta> \<Turnstile> Star A B \<and> \<sigma>2, s (x := v2), \<Delta> \<Turnstile> Star A B\<close> asso2 asso3 commutative)
  then show "v1 = v2"
    using \<open>a1, s(x := v1), \<Delta> \<Turnstile> A\<close> \<open>a2, s(x := v2), \<Delta> \<Turnstile> A\<close> assms unambiguous_def by fastforce
qed


lemma combinable_exists:
  assumes "combinable \<Delta> A"
      and "unambiguous \<Delta> A x"
    shows "combinable \<Delta> (Exists x A)"
proof (rule combinableI)
  fix a b p q y \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> Exists x A \<and> b, s, \<Delta> \<Turnstile> Exists x A \<and> Some y = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  then have "a ## b"
    by (metis logic.compatible_multiples logic_axioms option.discI pre_logic.compatible_def)
  moreover obtain v1 v2 where "a, s(x := v1), \<Delta> \<Turnstile> A" "b, s(x := v2), \<Delta> \<Turnstile> A"
    using \<open>a, s, \<Delta> \<Turnstile> Exists x A \<and> b, s, \<Delta> \<Turnstile> Exists x A \<and> Some y = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one\<close> by auto
  ultimately have "v1 = v2"
    using assms(2) unambiguous_def by force
  then show "y, s, \<Delta> \<Turnstile> Exists x A"
    by (metis (mono_tags, opaque_lifting) \<open>a, s(x := v1), \<Delta> \<Turnstile> A\<close> \<open>a, s, \<Delta> \<Turnstile> Exists x A \<and> b, s, \<Delta> \<Turnstile> Exists x A \<and> Some y = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one\<close> \<open>b, s(x := v2), \<Delta> \<Turnstile> A\<close> assms(1) combinable_instantiate_one logic.sat.simps(8) logic_axioms)
qed

lemma combinable_pure:
  assumes "pure A"
  shows "combinable \<Delta> A"
  using assms combinableI_old pure_def by blast


lemma combinable_imp:
  assumes "pure A"
      and "combinable \<Delta> B"
  shows "combinable \<Delta> (Imp A B)"
proof (rule combinableI)
  fix a b p q x \<sigma> s
  assume "a, s, \<Delta> \<Turnstile> Imp A B \<and> b, s, \<Delta> \<Turnstile> Imp A B \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  then show "x, s, \<Delta> \<Turnstile> Imp A B"
    using assms(1) assms(2) combinable_instantiate_one pure_def sat.simps(5)
    by metis
qed


lemma combinable_wildcard:
  assumes "combinable \<Delta> A"
  shows "combinable \<Delta> (Wildcard A)"
proof (rule combinableI)
  fix a b p q x \<sigma> s
  assume asm: "a, s, \<Delta> \<Turnstile> Wildcard A \<and> b, s, \<Delta> \<Turnstile> Wildcard A \<and> Some x = p \<odot> a \<oplus> q \<odot> b \<and> sadd p q = one"
  then obtain a' b' pa pb where "a', s, \<Delta> \<Turnstile> A" "b', s, \<Delta> \<Turnstile> A" "a = pa \<odot> a'" "b = pb \<odot> b'" by auto
  then have "Some x = (smult p pa) \<odot> a' \<oplus> (smult q pb) \<odot> b'"
    by (simp add: asm double_mult)
  then have "x, s, \<Delta> \<Turnstile> Mult (sadd (smult p pa) (smult q pb)) A"
    using \<open>a', s, \<Delta> \<Turnstile> A\<close> \<open>b', s, \<Delta> \<Turnstile> A\<close> assms combinable_instantiate by blast
  then show "x, s, \<Delta> \<Turnstile> Wildcard A"
    by fastforce
qed


end


end