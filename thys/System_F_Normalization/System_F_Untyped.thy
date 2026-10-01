theory System_F_Untyped
  imports System_F
begin

datatype ulam =
    UVar nat
  | UApp ulam ulam
  | ULam ulam

fun u_shift :: "nat \<Rightarrow> ulam \<Rightarrow> ulam" where
  "u_shift k (UVar n) =
    (if n < k then UVar n else UVar (Suc n))"
| "u_shift k (UApp M N) = UApp (u_shift k M) (u_shift k N)"
| "u_shift k (ULam M) = ULam (u_shift (Suc k) M)"

fun u_subst :: "nat \<Rightarrow> ulam \<Rightarrow> ulam \<Rightarrow> ulam" where
  "u_subst k N (UVar n) =
    (if n < k then UVar n else
      if n = k then N else UVar (n - 1))"
| "u_subst k N (UApp M P) =
    UApp (u_subst k N M) (u_subst k N P)"
| "u_subst k N (ULam M) =
    ULam (u_subst (Suc k) (u_shift 0 N) M)"

definition u_subst0 :: "ulam \<Rightarrow> ulam \<Rightarrow> ulam"
where "u_subst0 N M = u_subst 0 N M"

lemma u_subst_shift:
  "u_subst k N (u_shift k M) = M"
  by (induct M arbitrary: k N rule: ulam.induct)
     (simp_all split: if_splits)

lemma u_shift_shift:
  "l \<le> k \<longrightarrow>
    u_shift l (u_shift k M) =
      u_shift (Suc k) (u_shift l M)"
proof (induct M arbitrary: k l rule: ulam.induct)
  case (UVar n)
  then show ?case
    by (auto split: if_splits; arith)
next
  case (UApp M P)
  then show ?case by (intro impI; simp_all; blast)
next
  case (ULam M)
  then show ?case by (intro impI; simp_all; blast)
qed

lemma u_shift_subst_comm:
  "l \<le> k \<longrightarrow>
    u_shift l (u_subst k N M) =
      u_subst (Suc k) (u_shift l N) (u_shift l M)"
proof (induct M arbitrary: k l N rule: ulam.induct)
  case (UVar n)
  then show ?case
    by (intro impI; simp split: if_splits; arith)
next
  case (UApp M P)
  then show ?case by (intro impI; simp_all; blast)
next
  case (ULam M)
  then show ?case
    by (intro impI; simp_all add: u_shift_shift; blast)
qed

lemma u_subst_comp_at:
  "l \<le> k \<longrightarrow>
    u_subst l (u_subst k N P)
      (u_subst (Suc k) (u_shift l N) M) =
    u_subst k N (u_subst l P M)"
proof (induct M arbitrary: k l N P rule: ulam.induct)
  case (UVar x)
  then show ?case
    by (intro impI; simp add: u_subst_shift split: if_splits; arith)
next
  case (UApp M P)
  then show ?case by (intro impI; simp_all; blast)
next
  case (ULam M)
  then show ?case
    by (intro impI; simp_all add: u_shift_shift u_shift_subst_comm; blast)
qed

inductive ubeta :: "ulam \<Rightarrow> ulam \<Rightarrow> bool"
  (\<open>_ \<longrightarrow>\<^sub>u _\<close> [80,80] 80) where
  uappL: "M \<longrightarrow>\<^sub>u M' \<Longrightarrow>
    UApp M N \<longrightarrow>\<^sub>u UApp M' N"
| uappR: "N \<longrightarrow>\<^sub>u N' \<Longrightarrow>
    UApp M N \<longrightarrow>\<^sub>u UApp M N'"
| ulam: "M \<longrightarrow>\<^sub>u M' \<Longrightarrow>
    ULam M \<longrightarrow>\<^sub>u ULam M'"
| ured: "UApp (ULam M) N \<longrightarrow>\<^sub>u u_subst0 N M"

inductive uSN :: "ulam \<Rightarrow> bool" where
  uSN_intro: "(\<And>M'. M \<longrightarrow>\<^sub>u M' \<Longrightarrow> uSN M') \<Longrightarrow> uSN M"

lemma uSN_preserved:
  assumes "uSN M" and "M \<longrightarrow>\<^sub>u M'"
  shows "uSN M'"
  using assms by (cases) auto

lemma u_subst_beta_at:
  assumes "M \<longrightarrow>\<^sub>u M'"
  shows "u_subst k N M \<longrightarrow>\<^sub>u u_subst k N M'"
  using assms
proof (induct arbitrary: k N rule: ubeta.induct)
  case (uappL M M' P)
  show ?case
    unfolding u_subst.simps
    by (rule ubeta.uappL, rule uappL(2)[of k N])
next
  case (uappR P P' M)
  show ?case
    unfolding u_subst.simps
    by (rule ubeta.uappR, rule uappR(2)[of k N])
next
  case (ulam M M')
  show ?case
    unfolding u_subst.simps
  apply (rule ubeta.ulam)
  using ulam(2)[of "Suc k" "u_shift 0 N"] .
next
  case (ured M P)
  have eq:
    "u_subst0 (u_subst k N P)
        (u_subst (Suc k) (u_shift 0 N) M) =
      u_subst k N (u_subst0 P M)"
    using u_subst_comp_at[of 0 k N P M]
    by (simp add: u_subst0_def)
  have root:
    "UApp (ULam (u_subst (Suc k) (u_shift 0 N) M))
        (u_subst k N P) \<longrightarrow>\<^sub>u
      u_subst0 (u_subst k N P)
        (u_subst (Suc k) (u_shift 0 N) M)"
    by (rule ubeta.ured)
  then show ?case using eq by (simp add: u_subst0_def)
qed

lemma uSN_subst_beta:
  assumes "M \<longrightarrow>\<^sub>u M'"
  shows "u_subst0 N M \<longrightarrow>\<^sub>u u_subst0 N M'"
  using u_subst_beta_at[OF assms, of 0 N]
  by (simp add: u_subst0_def)

lemma uSN_reflect_subst:
  assumes "uSN (u_subst0 (UVar 0) M)"
  shows "uSN M"
proof -
  have aux: "\<And>X. uSN X \<Longrightarrow>
      \<forall>M. X = u_subst0 (UVar 0) M \<longrightarrow> uSN M"
  proof -
    fix X
    assume "uSN X"
    then show "\<forall>M. X = u_subst0 (UVar 0) M \<longrightarrow> uSN M"
    proof (induct rule: uSN.induct)
      case (uSN_intro X)
      show ?case
      proof (intro allI impI)
        fix M
        assume eq: "X = u_subst0 (UVar 0) M"
        show "uSN M"
        proof (rule uSN.uSN_intro)
          fix M'
          assume redM: "M \<longrightarrow>\<^sub>u M'"
          have redX: "X \<longrightarrow>\<^sub>u u_subst0 (UVar 0) M'"
            using eq
            by (auto intro: uSN_subst_beta[OF redM])
          have ih:
            "\<forall>R. u_subst0 (UVar 0) M' =
              u_subst0 (UVar 0) R \<longrightarrow> uSN R"
            using uSN_intro(2)[OF redX] .
          from ih show "uSN M'" by blast
        qed
      qed
    qed
  qed
  then show "uSN M" using assms by blast
qed

inductive uFst :: "ulam \<Rightarrow> ulam \<Rightarrow> bool" where
  uFst_intro: "uFst (UApp M N) M"

lemma uSN_of_fst:
  assumes "uSN (UApp M N)"
  shows "uSN M"
proof -
  have aux: "\<And>X. uSN X \<Longrightarrow>
      \<forall>P Q. X = UApp P Q \<longrightarrow> uSN P"
  proof -
    fix X
    assume "uSN X"
    then show "\<forall>P Q. X = UApp P Q \<longrightarrow> uSN P"
    proof (induct rule: uSN.induct)
      case (uSN_intro X)
      show ?case
      proof (intro allI allI impI)
        fix P Q
        assume eq: "X = UApp P Q"
        show "uSN P"
        proof (rule uSN.uSN_intro)
          fix P'
          assume redP: "P \<longrightarrow>\<^sub>u P'"
          have redX: "X \<longrightarrow>\<^sub>u UApp P' Q"
            using eq redP by (auto intro: uappL)
          have ih: "\<forall>R S. UApp P' Q = UApp R S \<longrightarrow> uSN R"
            using uSN_intro(2)[OF redX] .
          from ih show "uSN P'" by blast
        qed
      qed
    qed
  qed
  then show "uSN M" using assms by blast
qed

lemma udouble_SN_aux:
  assumes a: "uSN a"
    and b: "uSN b"
    and hyp: "\<And>x z.
      \<lbrakk>\<And>y. x \<longrightarrow>\<^sub>u y \<Longrightarrow> uSN y;
       \<And>y. x \<longrightarrow>\<^sub>u y \<Longrightarrow> P y z;
       \<And>u. z \<longrightarrow>\<^sub>u u \<Longrightarrow> uSN u;
       \<And>u. z \<longrightarrow>\<^sub>u u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a
  have r: "\<And>b. uSN b \<Longrightarrow> P a b"
  proof (induct a rule: uSN.induct)
    case (uSN_intro x)
    note SNI' = uSN_intro
    have "uSN b" by fact
    thus ?case
    proof (induct b rule: uSN.induct)
      case (uSN_intro y)
      with SNI' show ?case
        by (metis uSN.simps hyp)
    qed
  qed
  from b show ?thesis by (rule r)
qed

lemma udouble_SN[consumes 2]:
  assumes a: "uSN a"
    and b: "uSN b"
    and c: "\<And>x z.
      \<lbrakk>\<And>y. x \<longrightarrow>\<^sub>u y \<Longrightarrow> P y z;
       \<And>u. z \<longrightarrow>\<^sub>u u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
  using a b c
  by (smt (verit, best) udouble_SN_aux)

definition uneutral :: "ulam \<Rightarrow> bool" where
  "uneutral M \<longleftrightarrow>
     (\<exists>k. M = UVar k) \<or>
     (\<exists>P Q. M = UApp P Q)"

text \<open>
  The neutral terms used by the candidate condition are variables and
  arbitrary applications.  In particular, applications are considered
  neutral even when their head is an abstraction.  This deliberately broad
  formulation makes the candidate closure stable under the full compatible
  reduction relation; the redex case is handled explicitly when the
  saturation lemmas analyze the reducts of an application.
\<close>

lemma uneutral_var:
  "uneutral (UVar k)"
  by (auto simp add: uneutral_def)

lemma uneutral_app:
  "uneutral (UApp M N)"
  by (auto simp add: uneutral_def)

definition uCR1 :: "ulam set \<Rightarrow> bool" where
  "uCR1 C \<longleftrightarrow> (\<forall>M. M \<in> C \<longrightarrow> uSN M)"

definition uCR2 :: "ulam set \<Rightarrow> bool" where
  "uCR2 C \<longleftrightarrow>
    (\<forall>M M'. M \<in> C \<longrightarrow> M \<longrightarrow>\<^sub>u M' \<longrightarrow> M' \<in> C)"

definition uCR3 :: "ulam set \<Rightarrow> bool" where
  "uCR3 C \<longleftrightarrow>
    (\<forall>M. uneutral M \<longrightarrow>
      (\<forall>M'. M \<longrightarrow>\<^sub>u M' \<longrightarrow> M' \<in> C) \<longrightarrow> M \<in> C)"

definition ucandidate :: "ulam set \<Rightarrow> bool" where
  "ucandidate C \<longleftrightarrow> uCR1 C \<and> uCR2 C \<and> uCR3 C"

definition uSN_set :: "ulam set" where
  "uSN_set = {M. uSN M}"

lemma uSN_set_candidate:
  "ucandidate uSN_set"
proof (unfold ucandidate_def, intro conjI)
  show "uCR1 uSN_set"
    unfolding uCR1_def uSN_set_def by simp
next
  show "uCR2 uSN_set"
    unfolding uCR2_def uSN_set_def
    by (blast intro: uSN_preserved)
next
  show "uCR3 uSN_set"
    unfolding uCR3_def uSN_set_def
    by (blast intro: uSN.uSN_intro)
qed

lemma uvar_mem_candidate:
  assumes "ucandidate C"
  shows "UVar k \<in> C"
  using assms
  unfolding ucandidate_def uCR3_def
  by (blast intro: uneutral_var elim: ubeta.cases)

definition uarr :: "ulam set \<Rightarrow> ulam set \<Rightarrow> ulam set" where
  "uarr C D = {M. \<forall>N. N \<in> C \<longrightarrow> UApp M N \<in> D}"

lemma uarr_CR2:
  assumes "uCR2 D"
  shows "uCR2 (uarr C D)"
  using assms
  unfolding uCR2_def uarr_def
  by (blast intro: uappL)

lemma uarr_CR1:
  assumes "uCR1 C" and "uCR1 D" and "uCR3 C"
  shows "uCR1 (uarr C D)"
proof (unfold uCR1_def, intro strip)
  fix M
  assume hM: "M \<in> uarr C D"
  have "UVar 0 \<in> C"
    using assms(3)
    unfolding uCR3_def
    by (blast intro: uneutral_var elim: ubeta.cases)
  then have "uSN (UApp M (UVar 0))"
    using assms(2) hM by (simp add: uCR1_def uarr_def)
  then show "uSN M" by (rule uSN_of_fst)
qed

lemma uarr_CR3:
  assumes "uCR1 C" and "uCR2 C" and "uCR3 C"
    and "uCR3 D"
  shows "uCR3 (uarr C D)"
proof (unfold uCR3_def, intro strip)
  fix M
  assume hM: "uneutral M"
  assume hMred: "\<forall>M'. M \<longrightarrow>\<^sub>u M' \<longrightarrow> M' \<in> uarr C D"
  show "M \<in> uarr C D"
  proof (simp add: uarr_def, intro strip)
    fix N
    assume N: "N \<in> C"
    have SN: "uSN N"
      using assms(1) N unfolding uCR1_def by blast
    show "UApp M N \<in> D"
    using SN N hM hMred
    proof (induct N rule: uSN.induct)
      case (uSN_intro N)
      note SNI' = uSN_intro
      have hN: "N \<in> C" by fact
      have neutral: "uneutral (UApp M N)"
        by (rule uneutral_app)
      have reds: "\<And>R. UApp M N \<longrightarrow>\<^sub>u R \<Longrightarrow> R \<in> D"
      proof -
        fix R
        assume red: "UApp M N \<longrightarrow>\<^sub>u R"
        then show "R \<in> D"
        proof (cases rule: ubeta.cases)
          case (uappL P)
          then show ?thesis using hMred hN
            by (auto simp add: uarr_def)
        next
          case (uappR Q)
          have "Q \<in> C"
            using hN assms(2) uappR unfolding uCR2_def by blast
          then show ?thesis using SNI' uappR
            by blast
        next
          case ured
          then show ?thesis using hM
            by (auto simp add: uneutral_def)
        qed
      qed
      show ?case using assms(4) neutral reds
        unfolding uCR3_def by blast
    qed
  qed
qed

lemma uarr_candidate:
  assumes "ucandidate C" and "ucandidate D"
  shows "ucandidate (uarr C D)"
  using assms
  unfolding ucandidate_def
  by (intro conjI; blast intro: uarr_CR1 uarr_CR2 uarr_CR3)

lemma ubeta_lam_cases:
  assumes "ULam M \<longrightarrow>\<^sub>u P"
  obtains M' where "M \<longrightarrow>\<^sub>u M'" and "P = ULam M'"
  using assms by (cases rule: ubeta.cases) auto

text \<open>
  The abstraction lemma is the semantic heart of the untyped development.
  Its premise says that substituting every argument from the domain
  candidate into the body produces an element of the codomain candidate.
  The proof first obtains strong normalization of the body by testing it
  with a fresh variable, and then uses simultaneous induction on body and
  argument reductions to establish the candidate condition for the
  application of the abstraction.
\<close>

lemma uabs_RED:
  assumes C: "ucandidate C"
    and D: "ucandidate D"
    and asm: "\<forall>s. s \<in> C \<longrightarrow> u_subst0 s M \<in> D"
  shows "ULam M \<in> uarr C D"
proof -
  have b1: "uSN M"
  proof -
    have "UVar 0 \<in> C"
      using C by (blast intro: uvar_mem_candidate)
    then have "u_subst0 (UVar 0) M \<in> D"
      using asm by blast
    then have "uSN (u_subst0 (UVar 0) M)"
      using D unfolding ucandidate_def uCR1_def by blast
    then have "uSN M" by (rule uSN_reflect_subst)
    moreover have "uCR1 D"
      using D unfolding ucandidate_def by blast
    ultimately show "uSN M" by blast
  qed
  show "ULam M \<in> uarr C D"
  proof (simp add: uarr_def, intro strip)
    fix u
    assume u: "u \<in> C"
    then have uSN: "uSN u"
      using C unfolding ucandidate_def uCR1_def by blast
    show "UApp (ULam M) u \<in> D"
    using b1 uSN u asm
    proof (induct M u rule: udouble_SN)
      fix M u
      assume ih1:
        "\<And>M'. \<lbrakk>M \<longrightarrow>\<^sub>u M';
          u \<in> C; \<forall>s. s \<in> C \<longrightarrow> u_subst0 s M' \<in> D\<rbrakk>
          \<Longrightarrow> UApp (ULam M') u \<in> D"
      assume ih2:
        "\<And>u'. \<lbrakk>u \<longrightarrow>\<^sub>u u';
          u' \<in> C; \<forall>s. s \<in> C \<longrightarrow> u_subst0 s M \<in> D\<rbrakk>
          \<Longrightarrow> UApp (ULam M) u' \<in> D"
      assume uC: "u \<in> C"
      assume hM: "\<forall>s. s \<in> C \<longrightarrow> u_subst0 s M \<in> D"
      have reds:
        "\<And>R. UApp (ULam M) u \<longrightarrow>\<^sub>u R \<Longrightarrow> R \<in> D"
      proof -
        fix R
        assume red: "UApp (ULam M) u \<longrightarrow>\<^sub>u R"
        then show "R \<in> D"
        proof (cases rule: ubeta.cases)
          case (uappL P)
          obtain M' where hred: "M \<longrightarrow>\<^sub>u M'"
              and P_eq: "P = ULam M'"
            using ubeta_lam_cases[OF uappL(2)] .
          have hM': "\<forall>s. s \<in> C \<longrightarrow> u_subst0 s M' \<in> D"
          proof (intro allI impI)
            fix s
            assume sC: "s \<in> C"
            have hsr: "u_subst0 s M \<longrightarrow>\<^sub>u u_subst0 s M'"
              using hred by (rule uSN_subst_beta)
            have D2: "uCR2 D"
              using D unfolding ucandidate_def by blast
            show "u_subst0 s M' \<in> D"
              using hM sC hsr D2
              unfolding uCR2_def by blast
          qed
          show ?thesis
            using ih1 hred uC hM' uappL P_eq by simp
        next
          case (uappR u')
          have C2: "uCR2 C"
            using C unfolding ucandidate_def by blast
          have "u' \<in> C"
            using uC C2 uappR unfolding uCR2_def by blast
          then show ?thesis
            using ih2 uappR hM by blast
        next
          case ured
          then show ?thesis using hM uC by blast
        qed
      qed
      have neutral: "uneutral (UApp (ULam M) u)"
        by (rule uneutral_app)
      show "UApp (ULam M) u \<in> D"
        using D neutral reds unfolding ucandidate_def uCR3_def by blast
    qed
  qed
qed

end
