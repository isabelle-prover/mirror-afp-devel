theory System_F_Normalization
  imports System_F_Erasure
begin

definition f_env_ok :: "(nat \<Rightarrow> ulam set) \<Rightarrow> bool" where
  "f_env_ok \<rho> \<longleftrightarrow> (\<forall>k. ucandidate (\<rho> k))"

definition f_all_sem :: "(ulam set \<Rightarrow> ulam set) \<Rightarrow> ulam set" where
  "f_all_sem F = {M. \<forall>C. ucandidate C \<longrightarrow> M \<in> F C}"

lemma f_all_candidate:
  assumes H: "\<forall>C. ucandidate C \<longrightarrow> ucandidate (F C)"
  shows "ucandidate (f_all_sem F)"
proof (unfold ucandidate_def, intro conjI)
  show "uCR1 (f_all_sem F)"
    unfolding uCR1_def f_all_sem_def
    using H uSN_set_candidate
    unfolding ucandidate_def uCR1_def
    by blast
next
  show "uCR2 (f_all_sem F)"
    unfolding uCR2_def f_all_sem_def
    using H
    unfolding ucandidate_def uCR2_def
    by blast
next
  show "uCR3 (f_all_sem F)"
    unfolding uCR3_def f_all_sem_def
    using H
    unfolding ucandidate_def uCR3_def
    by blast
qed

definition f_env_insert ::
  "nat \<Rightarrow> ulam set \<Rightarrow> (nat \<Rightarrow> ulam set) \<Rightarrow>
    nat \<Rightarrow> ulam set"
where
  "f_env_insert k C \<rho> n =
    (if n < k then \<rho> n else
      if n = k then C else \<rho> (n - 1))"

lemma f_env_insert_zero:
  "f_env_insert 0 C \<rho> = ty_env_cons C \<rho>"
proof (rule ext)
  fix x
  show "f_env_insert 0 C \<rho> x = ty_env_cons C \<rho> x"
  proof (cases x)
    case 0
    then show ?thesis
      by (simp add: f_env_insert_def ty_env_cons_def)
  next
    case (Suc n)
    then show ?thesis
      by (simp add: f_env_insert_def ty_env_cons_def split: if_splits)
qed
qed

lemma f_env_insert_suc_cons:
  "f_env_insert (Suc k) C (ty_env_cons D \<rho>) =
    ty_env_cons D (f_env_insert k C \<rho>)"
proof (rule ext)
  fix x
  show "f_env_insert (Suc k) C (ty_env_cons D \<rho>) x =
    ty_env_cons D (f_env_insert k C \<rho>) x"
  proof (induct x)
    case 0
    then show ?case
      by (simp add: f_env_insert_def ty_env_cons_def)
  next
    case (Suc n)
    then show ?case
    proof (cases n)
      case 0
      then show ?thesis
        by (simp add: f_env_insert_def ty_env_cons_def)
    next
      case (Suc m)
      then show ?thesis
        by (simp add: f_env_insert_def ty_env_cons_def
          split: if_splits; arith)
      qed
    qed
qed

lemma f_env_ok_cons:
  assumes "f_env_ok \<rho>" and "ucandidate C"
  shows "f_env_ok (ty_env_cons C \<rho>)"
  using assms
  unfolding f_env_ok_def ty_env_cons_def
  by (intro allI; case_tac k; simp_all)

fun f_sem :: "dty \<Rightarrow> (nat \<Rightarrow> ulam set) \<Rightarrow> ulam set" where
  "f_sem (TyVar k) \<rho> = \<rho> k"
| "f_sem (TyArr A B) \<rho> =
    uarr (f_sem A \<rho>) (f_sem B \<rho>)"
| "f_sem (TyAll A) \<rho> =
    f_all_sem (\<lambda>C. f_sem A (ty_env_cons C \<rho>))"

lemma f_sem_candidate:
  "f_env_ok \<rho> \<longrightarrow> ucandidate (f_sem A \<rho>)"
proof (induct A arbitrary: \<rho>)
  case (TyVar k)
  then show ?case
    unfolding f_sem.simps f_env_ok_def ucandidate_def by blast
next
  case (TyArr A B)
  then show ?case
    by (auto intro: uarr_candidate)
next
  case (TyAll A)
  have body:
    "f_env_ok \<rho> \<longrightarrow>
      (\<forall>C. ucandidate C \<longrightarrow>
        ucandidate (f_sem A (ty_env_cons C \<rho>)))"
    using TyAll(1)
    by (blast intro: f_env_ok_cons)
  then show ?case
    unfolding f_sem.simps
    by (intro impI; blast intro: f_all_candidate)
qed

lemma f_sem_ty_shift:
  "f_sem (ty_shift k A) (f_env_insert k C \<rho>) =
    f_sem A \<rho>"
proof (induct A arbitrary: k C \<rho>)
  case (TyVar n)
  then show ?case
    by (simp add: f_env_insert_def split: if_splits; arith)
next
  case (TyArr A B)
  then show ?case by simp
next
  case (TyAll A)
  have body_eq:
    "\<forall>D. f_sem (ty_shift (Suc k) A)
        (ty_env_cons D (f_env_insert k C \<rho>)) =
      f_sem A (ty_env_cons D \<rho>)"
    using TyAll(1)
    by (simp add: f_env_insert_suc_cons[symmetric])
  show ?case
    using body_eq
    by (simp add: f_all_sem_def)
qed

lemma f_sem_ty_subst:
  "f_sem (ty_subst k S A) \<rho> =
    f_sem A (f_env_insert k (f_sem S \<rho>) \<rho>)"
proof (induct A arbitrary: k S \<rho>)
  case (TyVar n)
  then show ?case
    by (simp add: f_env_insert_def split: if_splits; arith)
next
  case (TyArr A B)
  then show ?case by simp
next
  case (TyAll A)
  have shift0:
    "\<forall>D. f_sem (ty_shift 0 S) (ty_env_cons D \<rho>) =
      f_sem S \<rho>"
    using f_sem_ty_shift[of 0 S] f_env_insert_zero by simp
  have body_eq:
    "\<forall>D. f_sem (ty_subst (Suc k) (ty_shift 0 S) A)
        (ty_env_cons D \<rho>) =
      f_sem A
        (ty_env_cons D (f_env_insert k (f_sem S \<rho>) \<rho>))"
    using TyAll(1)
    by (simp add: shift0 f_sem_ty_shift f_env_insert_zero
      f_env_insert_suc_cons)
  show ?case
    using body_eq
    by (simp add: f_all_sem_def)
qed

definition f_tenv_cons :: "ulam \<Rightarrow> (nat \<Rightarrow> ulam) \<Rightarrow>
    nat \<Rightarrow> ulam"
where
  "f_tenv_cons N \<eta> n =
    (case n of 0 \<Rightarrow> N | Suc k \<Rightarrow> \<eta> k)"

definition f_tenv_shift :: "(nat \<Rightarrow> ulam) \<Rightarrow> nat \<Rightarrow> ulam"
where
  "f_tenv_shift \<eta> n =
    (case n of 0 \<Rightarrow> UVar 0 | Suc k \<Rightarrow> u_shift 0 (\<eta> k))"

definition f_env_subst ::
  "nat \<Rightarrow> ulam \<Rightarrow> (nat \<Rightarrow> ulam) \<Rightarrow>
    nat \<Rightarrow> ulam"
where
  "f_env_subst k N \<eta> n = u_subst k N (\<eta> n)"

lemma f_env_subst_shift:
  "f_env_subst (Suc k) (u_shift 0 N) (f_tenv_shift \<eta>) =
    f_tenv_shift (f_env_subst k N \<eta>)"
proof (rule ext)
  fix n
  show "f_env_subst (Suc k) (u_shift 0 N) (f_tenv_shift \<eta>) n =
    f_tenv_shift (f_env_subst k N \<eta>) n"
  proof (induct n)
    case 0
    then show ?case
      by (simp add: f_env_subst_def f_tenv_shift_def)
  next
    case (Suc n)
    then show ?case
      by (simp add: f_env_subst_def f_tenv_shift_def
        u_shift_subst_comm)
  qed
qed

lemma f_env_subst_shift0:
  "f_env_subst 0 N (f_tenv_shift \<eta>) =
    f_tenv_cons N \<eta>"
proof (rule ext)
  fix n
  show "f_env_subst 0 N (f_tenv_shift \<eta>) n =
    f_tenv_cons N \<eta> n"
  proof (induct n)
    case 0
    then show ?case
      by (simp add: f_env_subst_def f_tenv_shift_def f_tenv_cons_def
        u_subst0_def)
  next
    case (Suc n)
    then show ?case
      by (simp add: f_env_subst_def f_tenv_shift_def f_tenv_cons_def
        u_subst0_def u_subst_shift)
  qed
qed

fun f_interp :: "(nat \<Rightarrow> ulam) \<Rightarrow> dtm \<Rightarrow> ulam" where
  "f_interp \<eta> (TmVar n) = \<eta> n"
| "f_interp \<eta> (TmApp M N) =
    UApp (f_interp \<eta> M) (f_interp \<eta> N)"
| "f_interp \<eta> (TmLam A M) =
    ULam (f_interp (f_tenv_shift \<eta>) M)"
| "f_interp \<eta> (TmTAbs M) = f_interp \<eta> M"
| "f_interp \<eta> (TmTApp M A) = f_interp \<eta> M"

lemma f_interp_subst:
  "u_subst k N (f_interp \<eta> M) =
    f_interp (f_env_subst k N \<eta>) M"
proof (induct M arbitrary: k N \<eta> rule: dtm.induct)
  case (TmVar n)
  then show ?case by (simp add: f_env_subst_def)
next
  case (TmApp M P)
  then show ?case by simp
next
  case (TmLam A M)
  then show ?case
    by (simp add: f_env_subst_shift)
next
  case (TmTAbs M)
  then show ?case by simp
next
  case (TmTApp M A)
  then show ?case by simp
qed

lemma f_tenv_shift_id:
  "f_tenv_shift (\<lambda>n. UVar n) = (\<lambda>n. UVar n)"
proof (rule ext)
  fix x :: nat
  show "f_tenv_shift (\<lambda>n. UVar n) x = UVar x"
  proof (induct x)
    case 0
    then show ?case by (simp add: f_tenv_shift_def)
  next
    case (Suc n)
    then show ?case by (simp add: f_tenv_shift_def)
  qed
qed

lemma f_interp_id:
  "f_interp (\<lambda>n. UVar n) M = f_erase M"
  by (induct M rule: dtm.induct)
     (simp_all add: f_tenv_shift_id)

lemma f_interp_subst0_shift:
  "u_subst0 N (f_interp (f_tenv_shift \<eta>) M) =
    f_interp (f_tenv_cons N \<eta>) M"
  using f_interp_subst[of 0 N "f_tenv_shift \<eta>" M]
    f_env_subst_shift0
  by (simp add: u_subst0_def)

definition f_tenv_ok ::
  "dty list \<Rightarrow> (nat \<Rightarrow> ulam) \<Rightarrow>
    (nat \<Rightarrow> ulam set) \<Rightarrow> bool"
where
  "f_tenv_ok \<Gamma> \<eta> \<rho> \<longleftrightarrow>
    (\<forall>n A. ctx_mem \<Gamma> n A \<longrightarrow>
      \<eta> n \<in> f_sem A \<rho>)"

lemma f_ctx_mem_mapE:
  "ctx_mem (map (ty_shift 0) \<Gamma>) n B \<longrightarrow>
    (\<exists>A. ctx_mem \<Gamma> n A \<and> B = ty_shift 0 A)"
proof (induct \<Gamma> arbitrary: n B)
  case Nil
  then show ?case by (auto elim: ctx_mem.cases)
next
  case (Cons A \<Gamma>)
  then show ?case
  proof (intro impI)
    assume h: "ctx_mem (map (ty_shift 0) (A # \<Gamma>)) n B"
    have h': "ctx_mem (ty_shift 0 A # map (ty_shift 0) \<Gamma>) n B"
      using h by simp
    then show "\<exists>A'. ctx_mem (A # \<Gamma>) n A' \<and>
      B = ty_shift 0 A'"
    proof (cases rule: ctx_mem.cases)
      case ctx_zero
      then show ?thesis
        by (auto intro: ctx_mem.ctx_zero)
    next
      case ctx_suc
      have h'':
        "ctx_mem (map (ty_shift 0) \<Gamma>) (n - 1) B"
        using ctx_suc(1) ctx_suc(2) by simp
      have ex:
        "\<exists>A'. ctx_mem \<Gamma> (n - 1) A' \<and>
          B = ty_shift 0 A'"
        using Cons(1)[of "n - 1" B] h'' by blast
      have ex':
        "\<exists>A'. ctx_mem (A # \<Gamma>) (Suc (n - 1)) A' \<and>
          B = ty_shift 0 A'"
        using ex by (blast intro: ctx_mem.ctx_suc)
      from ex' ctx_suc(1) show ?thesis by simp
    qed
  qed
qed

lemma f_tenv_ok_cons:
  assumes hctx: "f_tenv_ok \<Gamma> \<eta> \<rho>"
    and hval: "N \<in> f_sem A \<rho>"
  shows "f_tenv_ok (A # \<Gamma>) (f_tenv_cons N \<eta>) \<rho>"
  using assms
  unfolding f_tenv_ok_def
  by (auto simp add: f_tenv_cons_def elim: ctx_mem.cases)

lemma f_tenv_ok_ty_shift:
  assumes hctx: "f_tenv_ok \<Gamma> \<eta> \<rho>"
    and henv: "f_env_ok \<rho>"
    and hcan: "ucandidate C"
  shows "f_tenv_ok (map (ty_shift 0) \<Gamma>) \<eta>
    (ty_env_cons C \<rho>)"
proof (unfold f_tenv_ok_def, intro allI allI impI)
  fix n B
  assume memB: "ctx_mem (map (ty_shift 0) \<Gamma>) n B"
  have ex:
    "\<exists>A. ctx_mem \<Gamma> n A \<and> B = ty_shift 0 A"
    using f_ctx_mem_mapE[of \<Gamma> n B] memB by blast
  have sh:
    "\<forall>A. f_sem (ty_shift 0 A) (ty_env_cons C \<rho>) =
      f_sem A \<rho>"
    using f_sem_ty_shift[of 0] f_env_insert_zero by simp
  have sem:
    "\<forall>A. ctx_mem \<Gamma> n A \<longrightarrow>
      \<eta> n \<in> f_sem (ty_shift 0 A) (ty_env_cons C \<rho>)"
    using hctx sh unfolding f_tenv_ok_def by blast
  from ex sem show "\<eta> n \<in> f_sem B (ty_env_cons C \<rho>)"
    by blast
qed

definition f_prop ::
  "dty list \<Rightarrow> dtm \<Rightarrow> dty \<Rightarrow> bool"
where
  "f_prop \<Gamma> M A \<longleftrightarrow>
    (\<forall>\<rho> \<eta>.
      f_env_ok \<rho> \<longrightarrow>
      f_tenv_ok \<Gamma> \<eta> \<rho> \<longrightarrow>
      f_interp \<eta> M \<in> f_sem A \<rho>)"

lemma f_fundamental:
  "typing k \<Gamma> M A \<Longrightarrow> f_prop \<Gamma> M A"
proof (induct rule: typing.induct)
  case ty_var
  then show ?case
    unfolding f_prop_def f_interp.simps f_sem.simps f_tenv_ok_def
    by blast
next
  case ty_app
  then show ?case
    unfolding f_prop_def f_interp.simps f_sem.simps uarr_def
    by blast
next
  case (ty_lam k0 A0 G0 M0 B0)
  show ?case
    unfolding f_prop_def f_interp.simps f_sem.simps
  proof (intro allI allI impI impI)
    fix \<rho> \<eta>
    assume env: "f_env_ok \<rho>"
    assume ctx: "f_tenv_ok G0 \<eta> \<rho>"
    have Ccan: "ucandidate (f_sem A0 \<rho>)"
      using f_sem_candidate[of \<rho> A0] env by blast
    have Dcan: "ucandidate (f_sem B0 \<rho>)"
      using f_sem_candidate[of \<rho> B0] env by blast
    have body:
      "\<forall>s. s \<in> f_sem A0 \<rho> \<longrightarrow>
        u_subst0 s (f_interp (f_tenv_shift \<eta>) M0) \<in> f_sem B0 \<rho>"
    proof (intro allI impI)
      fix s
      assume sA: "s \<in> f_sem A0 \<rho>"
      have ctxs:
        "f_tenv_ok (A0 # G0) (f_tenv_cons s \<eta>) \<rho>"
        using f_tenv_ok_cons[OF ctx sA] .
      have ih:
        "f_interp (f_tenv_cons s \<eta>) M0 \<in> f_sem B0 \<rho>"
        using ty_lam(3) env ctxs
        unfolding f_prop_def by blast
      have eq:
        "u_subst0 s (f_interp (f_tenv_shift \<eta>) M0) =
          f_interp (f_tenv_cons s \<eta>) M0"
        using f_interp_subst0_shift by blast
      from ih show
        "u_subst0 s (f_interp (f_tenv_shift \<eta>) M0) \<in> f_sem B0 \<rho>"
        using eq by simp
    qed
    have abs:
      "ULam (f_interp (f_tenv_shift \<eta>) M0) \<in>
        uarr (f_sem A0 \<rho>) (f_sem B0 \<rho>)"
      using Ccan Dcan body by (rule uabs_RED)
    then show "ULam (f_interp (f_tenv_shift \<eta>) M0) \<in>
      uarr (f_sem A0 \<rho>) (f_sem B0 \<rho>)" .
  qed
next
  case (ty_tabs k0 G0 M0 B0)
  show ?case
    unfolding f_prop_def
  proof (intro allI allI impI impI)
    fix \<rho> \<eta>
    assume env: "f_env_ok \<rho>"
    assume ctx: "f_tenv_ok G0 \<eta> \<rho>"
    have all:
      "\<forall>C. ucandidate C \<longrightarrow>
        f_interp \<eta> M0 \<in> f_sem B0 (ty_env_cons C \<rho>)"
    proof (intro allI impI)
      fix C
      assume Ccan: "ucandidate C"
      have envC: "f_env_ok (ty_env_cons C \<rho>)"
        using f_env_ok_cons[OF env Ccan] .
      have ctxC:
          "f_tenv_ok (map (ty_shift 0) G0) \<eta>
          (ty_env_cons C \<rho>)"
        using f_tenv_ok_ty_shift[OF ctx env Ccan] .
      have ih:
        "f_interp \<eta> M0 \<in> f_sem B0 (ty_env_cons C \<rho>)"
        using ty_tabs(2) envC ctxC
        unfolding f_prop_def by blast
      from ih show "f_interp \<eta> M0 \<in> f_sem B0 (ty_env_cons C \<rho>)"
        by assumption
    qed
    show "f_interp \<eta> (TmTAbs M0) \<in> f_sem (TyAll B0) \<rho>"
      using all unfolding f_interp.simps f_sem.simps f_all_sem_def by blast
  qed
next
  case (ty_tapp k0 G0 M0 B0 A0)
  show ?case
    unfolding f_prop_def
  proof (intro allI allI impI impI)
    fix \<rho> \<eta>
    assume env: "f_env_ok \<rho>"
    assume ctx: "f_tenv_ok G0 \<eta> \<rho>"
    have ih:
      "f_interp \<eta> M0 \<in> f_sem (TyAll B0) \<rho>"
      using ty_tapp(2) env ctx
      unfolding f_prop_def by blast
    have Acan: "ucandidate (f_sem A0 \<rho>)"
      using f_sem_candidate[of \<rho> A0] env by blast
    have body:
      "f_interp \<eta> M0 \<in>
        f_sem B0 (ty_env_cons (f_sem A0 \<rho>) \<rho>)"
      using ih Acan unfolding f_sem.simps f_all_sem_def by blast
    have sem_eq:
      "f_sem (ty_subst0 A0 B0) \<rho> =
        f_sem B0 (ty_env_cons (f_sem A0 \<rho>) \<rho>)"
      using f_sem_ty_subst[of 0 A0 B0 \<rho>] f_env_insert_zero
      by (simp add: ty_subst0_def)
    show "f_interp \<eta> (TmTApp M0 A0) \<in>
      f_sem (ty_subst0 A0 B0) \<rho>"
      using body sem_eq by simp
  qed
qed

lemma f_identity_tenv_ok:
  "f_tenv_ok \<Gamma> (\<lambda>n. UVar n) (\<lambda>_. uSN_set)"
proof (unfold f_tenv_ok_def, intro allI allI impI)
  fix n A
  assume "ctx_mem \<Gamma> n A"
  have can:
    "ucandidate (f_sem A (\<lambda>_. uSN_set))"
    using f_sem_candidate[of "(\<lambda>_. uSN_set)" A]
    by (simp add: f_env_ok_def uSN_set_candidate)
  from uvar_mem_candidate[OF can]
  show "UVar n \<in> f_sem A (\<lambda>_. uSN_set)" .
qed

lemma f_welltyped_fundamental:
  assumes "typing k \<Gamma> M A"
  shows "uSN (f_erase M)"
proof -
  have env: "f_env_ok (\<lambda>_. uSN_set)"
    unfolding f_env_ok_def
    by (simp add: uSN_set_candidate)
  have ctx:
    "f_tenv_ok \<Gamma> (\<lambda>n. UVar n) (\<lambda>_. uSN_set)"
    using f_identity_tenv_ok .
  have sem:
    "f_interp (\<lambda>n. UVar n) M \<in>
      f_sem A (\<lambda>_. uSN_set)"
    using f_fundamental[OF assms] env ctx
    unfolding f_prop_def by blast
  have semM:
    "f_erase M \<in> f_sem A (\<lambda>_. uSN_set)"
    using sem f_interp_id by simp
  have can:
    "ucandidate (f_sem A (\<lambda>_. uSN_set))"
    using f_sem_candidate[of "(\<lambda>_. uSN_set)" A] env by blast
  from can semM show "uSN (f_erase M)"
    unfolding ucandidate_def uCR1_def by blast
qed

theorem strong_normalization:
  assumes "typing k \<Gamma> M A"
  shows "SN M"
  using fSN_reflect[OF f_welltyped_fundamental[OF assms]] .

end
