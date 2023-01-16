section \<open>Distributivity and Factorisability\<close>

text \<open>This section corresponds to Section 2.4 and Figure 4 of the paper~\<^cite>\<open>"UnboundedSL"\<close>.\<close>

theory Distributivity
  imports UnboundedLogic
begin

context logic
begin

subsection DotPos

lemma DotPos:
  "A, \<Delta> \<turnstile> B \<longleftrightarrow> (Mult \<pi> A, \<Delta> \<turnstile> Mult \<pi> B)" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis (no_types, lifting) entails_def sat.simps(1))
  show "?B \<Longrightarrow> ?A"
    using can_divide entails_def sat.simps(1)
    by metis
qed

text \<open>Only one direction holds with a wildcard\<close>

lemma WildPos:
  "A, \<Delta> \<turnstile> B \<Longrightarrow> (Wildcard A, \<Delta> \<turnstile> Wildcard B)"
  by (metis (no_types, lifting) entails_def sat.simps(12))

subsection DotDot

lemma dot_mult1:
  "Mult p (Mult q A), \<Delta> \<turnstile> Mult (smult p q) A"
proof (rule entailsI)
  fix \<sigma> s
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Mult q A)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult (smult p q) A"
    using double_mult by auto
qed

lemma dot_mult2:
  "Mult (smult p q) A, \<Delta> \<turnstile> Mult p (Mult q A)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult (smult p q) A"
  then obtain a where "a, s, \<Delta> \<Turnstile> A" "\<sigma> = (smult p q) \<odot> a"
    by auto
  then have "q \<odot> a, s, \<Delta> \<Turnstile> Mult q A" by auto
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Mult q A)"  
    by (metis \<open>\<sigma> = smult p q \<odot> a\<close> double_mult sat.simps(1))
qed

lemma DotDot:
  "Mult p (Mult q A), \<Delta> \<equiv> Mult (smult p q) A"
  by (simp add: dot_mult1 dot_mult2 equivalent_def)

lemma can_factorize:
  "\<exists>r. q = smult r p"
  by (metis sinv_inverse smult_asso smult_comm sone_neutral)

lemma WildDot:
  "Wildcard (Mult p A), \<Delta> \<equiv> Wildcard A"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Mult p A) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
    using double_mult by fastforce
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
  then obtain q a where "\<sigma> = q \<odot> a" "a, s, \<Delta> \<Turnstile> A"
    using sat.simps(12) by blast
  then obtain r where "q = smult r p"
    using can_factorize by blast
  then have "\<sigma> = r \<odot> (p \<odot> a)"
    by (simp add: \<open>\<sigma> = q \<odot> a\<close> double_mult)
  then show "\<sigma>, s, \<Delta> \<Turnstile> Wildcard (Mult p A)"
    using \<open>a, s, \<Delta> \<Turnstile> A\<close> sat.simps(1) sat.simps(12) by blast
qed

lemma DotWild:
  "Mult p (Wildcard A), \<Delta> \<equiv> Wildcard A"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Mult p (Wildcard A) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
    using double_mult by fastforce
  fix \<sigma> s
  assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
  then obtain q a where "\<sigma> = q \<odot> a" "a, s, \<Delta> \<Turnstile> A"
    by force
  then obtain r where "q = smult p r"
    using can_factorize smult_comm by presburger
  then have "\<sigma> = p \<odot> (r \<odot> a)"
    by (simp add: \<open>\<sigma> = q \<odot> a\<close> double_mult)
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Wildcard A)"
    using \<open>a, s, \<Delta> \<Turnstile> A\<close> by auto
qed

lemma WildWild:
  "Wildcard (Wildcard A), \<Delta> \<equiv> Wildcard A"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Wildcard A) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
    using double_mult by fastforce
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Wildcard A)"
    by (metis one_neutral sat.simps(12))
qed




subsection DotStar

lemma dot_star1:
  "Mult p (Star A B), \<Delta> \<turnstile> Star (Mult p A) (Mult p B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Star A B)"
  then obtain a b x where "\<sigma> = p \<odot> x" "Some x = a \<oplus> b" "a, s, \<Delta> \<Turnstile> A" "b, s, \<Delta> \<Turnstile> B"
    by auto
  then show "\<sigma>, s, \<Delta> \<Turnstile> Star (Mult p A) (Mult p B)"
    using plus_mult by auto
qed


lemma dot_star2:
  "Star (Mult p A) (Mult p B), \<Delta> \<turnstile> Mult p (Star A B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Star (Mult p A) (Mult p B)"
  then obtain a b where "Some \<sigma> = (p \<odot> a) \<oplus> (p \<odot> b)" "a, s, \<Delta> \<Turnstile> A" "b, s, \<Delta> \<Turnstile> B"
    by auto
  then obtain x where "Some x = a \<oplus> b"
    by (metis plus_mult unique_inv)
  then have "\<sigma> = p \<odot> x"
    by (metis \<open>Some \<sigma> = p \<odot> a \<oplus> p \<odot> b\<close> option.sel plus_mult)
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Star A B)"
    using \<open>Some x = a \<oplus> b\<close> \<open>a, s, \<Delta> \<Turnstile> A\<close> \<open>b, s, \<Delta> \<Turnstile> B\<close> by auto
qed

lemma DotStar:
  "Mult p (Star A B), \<Delta> \<equiv> Star (Mult p A) (Mult p B)"
  by (simp add: dot_star1 dot_star2 equivalent_def)

lemma WildStar1:
  "Wildcard (Star A B), \<Delta> \<turnstile> Star (Wildcard A) (Wildcard B)"
proof (rule entailsI)
  fix \<sigma> s assume asm0: "\<sigma>, s, \<Delta> \<Turnstile> Wildcard (Star A B)"
  then obtain p ab a b where "\<sigma> = p \<odot> ab" "Some ab = a \<oplus> b" "a, s, \<Delta> \<Turnstile> A" "b, s, \<Delta> \<Turnstile> B"
    by auto
  then have "Some \<sigma> = (p \<odot> a) \<oplus> (p \<odot> b)"
    using plus_mult by blast
  then show "\<sigma>, s, \<Delta> \<Turnstile> Star (Wildcard A) (Wildcard B)"
    using \<open>a, s, \<Delta> \<Turnstile> A\<close> \<open>b, s, \<Delta> \<Turnstile> B\<close> by auto
qed


subsection DotWand


lemma dot_wand1:
  "Mult p (Wand A B), \<Delta> \<turnstile> Wand (Mult p A) (Mult p B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Wand A B)"
  then obtain x where "\<sigma> = p \<odot> x" "x, s, \<Delta> \<Turnstile> Wand A B"
    by auto
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand (Mult p A) (Mult p B)"
  proof (rule sat_wand)
    fix a \<sigma>'
    assume "a, s, \<Delta> \<Turnstile> Mult p A \<and> Some \<sigma>' = \<sigma> \<oplus> a"
    then obtain aa where "aa, s, \<Delta> \<Turnstile> A" "a = p \<odot> aa"
      by auto
    then obtain b where "Some b = x \<oplus> aa"
      by (metis \<open>\<sigma> = p \<odot> x\<close> \<open>a, s, \<Delta> \<Turnstile> Mult p A \<and> Some \<sigma>' = \<sigma> \<oplus> a\<close> compatible_def compatible_iff option.exhaust_sel)
    then have "b, s, \<Delta> \<Turnstile> B"
      using \<open>aa, s, \<Delta> \<Turnstile> A\<close> \<open>x, s, \<Delta> \<Turnstile> Wand A B\<close> by auto
    then show "\<sigma>', s, \<Delta> \<Turnstile> Mult p B"
      by (metis \<open>Some b = x \<oplus> aa\<close> \<open>\<sigma> = p \<odot> x\<close> \<open>a = p \<odot> aa\<close> \<open>a, s, \<Delta> \<Turnstile> Mult p A \<and> Some \<sigma>' = \<sigma> \<oplus> a\<close> can_divide option.inject plus_mult sat_mult)
  qed
qed

lemma dot_wand2:
  "Wand (Mult p A) (Mult p B), \<Delta> \<turnstile> Mult p (Wand A B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume asm: "\<sigma>, s, \<Delta> \<Turnstile> Wand (Mult p A) (Mult p B)"
  show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Wand A B)"
  proof (rule sat_mult)
    fix a assume "\<sigma> = p \<odot> a"
    show "a, s, \<Delta> \<Turnstile> Wand A B"
    proof (rule sat_wand)
      fix aa \<sigma>'
      assume "aa, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = a \<oplus> aa"
      then have "p \<odot> aa, s, \<Delta> \<Turnstile> Mult p A" by auto
      then have "Some (p \<odot> \<sigma>') = \<sigma> \<oplus> p \<odot> aa"
        by (simp add: \<open>\<sigma> = p \<odot> a\<close> \<open>aa, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = a \<oplus> aa\<close> plus_mult)
      then have "p \<odot> \<sigma>', s, \<Delta> \<Turnstile> Mult p B"
        using \<open>p \<odot> aa, s, \<Delta> \<Turnstile> Mult p A\<close> asm by force
      then show "\<sigma>', s, \<Delta> \<Turnstile> B"
        by (metis can_divide sat.simps(1))
    qed
  qed
qed

lemma DotWand:
  "Mult p (Wand A B), \<Delta> \<equiv> Wand (Mult p A) (Mult p B)"
  by (simp add: dot_wand1 dot_wand2 equivalent_def)


(* Again: Need intuitionism
lemma WildWand:
  "Wildcard (Wand A B), \<Delta> \<turnstile> Wand (Wildcard A) (Wildcard B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Wildcard (Wand A B)"
  then obtain x p where "\<sigma> = p \<odot> x" "x, s, \<Delta> \<Turnstile> Wand A B"
    by auto
  show "\<sigma>, s, \<Delta> \<Turnstile> Wand (Wildcard A) (Wildcard B)"
  proof (rule sat_wand)
    fix a \<sigma>'
    assume "a, s, \<Delta> \<Turnstile> Wildcard A \<and> Some \<sigma>' = \<sigma> \<oplus> a"
    then obtain aa q where "aa, s, \<Delta> \<Turnstile> A" "a = q \<odot> aa"
      by auto
    then obtain b where "Some b = x \<oplus> aa"
      by (metis \<open>\<sigma> = p \<odot> x\<close> \<open>a, s, \<Delta> \<Turnstile> Wildcard A \<and> Some \<sigma>' = \<sigma> \<oplus> a\<close> compatible_def compatible_multiples not_None_eq)



    then have "b, s, \<Delta> \<Turnstile> B"
      using \<open>aa, s, \<Delta> \<Turnstile> A\<close> \<open>x, s, \<Delta> \<Turnstile> Wand A B\<close> by auto


    then show "\<sigma>', s, \<Delta> \<Turnstile> Wildcard B"
      
      by (metis \<open>Some b = x \<oplus> aa\<close> \<open>\<sigma> = p \<odot> x\<close> \<open>a = p \<odot> aa\<close> \<open>a, s, \<Delta> \<Turnstile> Mult p A \<and> Some \<sigma>' = \<sigma> \<oplus> a\<close> can_divide option.inject plus_mult sat_mult)
  qed
qed

*)



subsection DotOr

lemma dot_or1:
  "Mult p (Or A B), \<Delta> \<turnstile> Or (Mult p A) (Mult p B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Or A B)"
  then obtain x where "\<sigma> = p \<odot> x" "x, s, \<Delta> \<Turnstile> A \<or> x, s, \<Delta> \<Turnstile> B"
    by auto
  then show "\<sigma>, s, \<Delta> \<Turnstile> Or (Mult p A) (Mult p B)"
  proof (cases "x, s, \<Delta> \<Turnstile> A")
    case True
    then show ?thesis 
      using \<open>\<sigma> = p \<odot> x\<close> by auto
  next
    case False
    then show ?thesis
      using \<open>\<sigma> = p \<odot> x\<close> \<open>x, s, \<Delta> \<Turnstile> A \<or> x, s, \<Delta> \<Turnstile> B\<close> by auto
  qed
qed

lemma dot_or2:
  "Or (Mult p A) (Mult p B), \<Delta> \<turnstile> Mult p (Or A B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Or (Mult p A) (Mult p B)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Or A B)"
  proof (cases "\<sigma>, s, \<Delta> \<Turnstile> Mult p A")
    case True
    then show ?thesis by auto
  next
    case False
    then show ?thesis
      using \<open>\<sigma>, s, \<Delta> \<Turnstile> Or (Mult p A) (Mult p B)\<close> by auto
  qed
qed

lemma DotOr:
  "Mult p (Or A B), \<Delta> \<equiv> Or (Mult p A) (Mult p B)"
  by (simp add: dot_or1 dot_or2 equivalent_def)

lemma WildOr:
  "Wildcard (Or A B), \<Delta> \<equiv> Or (Wildcard A) (Wildcard B)"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Or A B) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Or (Wildcard A) (Wildcard B)"
    by auto
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Or (Wildcard A) (Wildcard B) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Or A B)"
    by auto
qed


subsection DotAnd

lemma dot_and1:
  "Mult p (And A B), \<Delta> \<turnstile> And (Mult p A) (Mult p B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (And A B)"
  then obtain x where "\<sigma> = p \<odot> x" "x, s, \<Delta> \<Turnstile> A" "x, s, \<Delta> \<Turnstile> B"
    by auto
  then show "\<sigma>, s, \<Delta> \<Turnstile> And (Mult p A) (Mult p B)"
    by auto
qed

lemma dot_and2:
  "And (Mult p A) (Mult p B), \<Delta> \<turnstile> Mult p (And A B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> And (Mult p A) (Mult p B)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (And A B)"
    using logic.can_divide logic_axioms by fastforce
qed

lemma DotAnd:
  "And (Mult p A) (Mult p B), \<Delta> \<equiv> Mult p (And A B)"
  by (simp add: dot_and1 dot_and2 equivalent_def)

lemma WildAnd:
  "Wildcard (And A B), \<Delta> \<turnstile> And (Wildcard A) (Wildcard B)"
  using entails_def by fastforce



subsection DotImp


lemma dot_imp1:
  "Imp (Mult p A) (Mult p B), \<Delta> \<turnstile> Mult p (Imp A B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Imp (Mult p A) (Mult p B)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Imp A B)"
    using sat_mult by force
qed

lemma dot_imp2:
  "Mult p (Imp A B), \<Delta> \<turnstile> Imp (Mult p A) (Mult p B)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Imp A B)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Imp (Mult p A) (Mult p B)"
    using can_divide by auto
qed

lemma DotImp:
  "Mult p (Imp A B), \<Delta> \<equiv> Imp (Mult p A) (Mult p B)"
  by (simp add: dot_imp1 dot_imp2 equivalent_def)

subsection DotPure


lemma pure_mult1:
  assumes "pure A"
  shows "Mult p A, \<Delta> \<turnstile> A"
  using assms entails_def logic.pure_def logic_axioms by fastforce

lemma pure_mult2:
  assumes "pure A"
  shows "A, \<Delta> \<turnstile> Mult p A"
    using assms entailsI pure_def sat_mult
    by metis

lemma DotPure: 
  assumes "pure A"
  shows "Mult p A, \<Delta> \<equiv> A"
  by (simp add: assms equivalent_def pure_mult1 pure_mult2)

lemma WildPure: 
  assumes "pure A"
  shows "Wildcard A, \<Delta> \<equiv> A"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> A"
    using assms pure_def sat.simps(12) by blast
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard A"
    by (metis one_neutral sat.simps(12))
qed


subsection DotFull

lemma mult_one_same1:
  "Mult one A, \<Delta> \<turnstile> A"
  by (simp add: entails_def one_neutral)


lemma mult_one_same2:
  "A, \<Delta> \<turnstile> Mult one A"
  by (simp add: entailsI one_neutral)

lemma DotFull:
  "Mult one A, \<Delta> \<equiv> A"
  using equivalent_def mult_one_same1 mult_one_same2 by blast




subsection DotExists


lemma dot_exists1:
  "Mult p (Exists x A), \<Delta> \<turnstile> Exists x (Mult p A)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Exists x A)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Exists x (Mult p A)"
    by auto
qed

lemma dot_exists2:
  "Exists x (Mult p A), \<Delta> \<turnstile> Mult p (Exists x A)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Exists x (Mult p A)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Exists x A)" by auto
qed

lemma DotExists:
  "Mult p (Exists x A), \<Delta> \<equiv> Exists x (Mult p A)"
  by (simp add: dot_exists1 dot_exists2 equivalent_def)


lemma WildExists:
  "Wildcard (Exists x A), \<Delta> \<equiv> Exists x (Wildcard A)"
proof (rule equivalentI)
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Exists x A) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Exists x (Wildcard A)"
    by auto
  show "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> Exists x (Wildcard A) \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Wildcard (Exists x A)"
    by auto
qed

subsection DotForall

lemma dot_forall1:
  "Mult p (Forall x A), \<Delta> \<turnstile> Forall x (Mult p A)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Forall x A)"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Forall x (Mult p A)"
    by auto
qed

lemma dot_forall2:
  "Forall x (Mult p A), \<Delta> \<turnstile> Mult p (Forall x A)"
proof (rule entailsI)
  fix \<sigma> s \<Delta>
  assume "\<sigma>, s, \<Delta> \<Turnstile> Forall x (Mult p A)"
  obtain a where "\<sigma> = p \<odot> a"
    using sat.simps(1) sat_mult by blast
  have "a, s, \<Delta> \<Turnstile> Forall x A"
  proof (rule sat_forall)
    fix v show "a, s(x := v), \<Delta> \<Turnstile> A"
      using \<open>\<sigma> = p \<odot> a\<close> \<open>\<sigma>, s, \<Delta> \<Turnstile> Forall x (Mult p A)\<close> can_divide by auto
  qed
  then show "\<sigma>, s, \<Delta> \<Turnstile> Mult p (Forall x A)"
    using \<open>\<sigma> = p \<odot> a\<close> by auto
qed

lemma DotForall:
  "Mult p (Forall x A), \<Delta> \<equiv> Forall x (Mult p A)"
  by (simp add: dot_forall1 dot_forall2 equivalent_def)

lemma WildForall:
  "Wildcard (Forall x A), \<Delta> \<turnstile> Forall x (Wildcard A)"
  by (metis (no_types, lifting) entailsI sat.simps(12) sat.simps(9))

subsection Split

lemma split:
  "Mult (sadd a b) A, \<Delta> \<turnstile> Star (Mult a A) (Mult b A)"
proof (rule entailsI)
  fix \<sigma> s
  assume "\<sigma>, s, \<Delta> \<Turnstile> Mult (sadd a b) A"
  then show "\<sigma>, s, \<Delta> \<Turnstile> Star (Mult a A) (Mult b A)"
    using distrib_mult by fastforce
qed

end

end
