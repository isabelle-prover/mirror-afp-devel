theory System_F_Subject_Reduction
  imports System_F
begin

text \<open>
  This theory records the independent type-preservation check for the
  de Bruijn presentation.  It is not needed by the normalization argument,
  but it validates the substitution operations used by both beta rules.
\<close>

fun ctx_insert :: "nat \<Rightarrow> dty \<Rightarrow> dty list \<Rightarrow> dty list" where
  "ctx_insert i B [] = [B]"
| "ctx_insert 0 B (A # \<Gamma>) = B # A # \<Gamma>"
| "ctx_insert (Suc i) B (A # \<Gamma>) = A # ctx_insert i B \<Gamma>"

lemma ctx_insert_Suc_cons:
  "ctx_insert (Suc i) B (A # \<Gamma>) = A # ctx_insert i B \<Gamma>"
  by simp

lemma map_ctx_insert:
  "map f (ctx_insert i B \<Gamma>) = ctx_insert i (f B) (map f \<Gamma>)"
proof (induct \<Gamma> arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons A \<Gamma>)
  then show ?case by (cases i) simp_all
qed

lemma ctx_mem_ctx_insert:
  assumes "ctx_mem \<Gamma> n A"
  shows "ctx_mem (ctx_insert i B \<Gamma>)
    (if n < i then n else Suc n) A"
using assms
proof (induct arbitrary: i B rule: ctx_mem.induct)
  case ctx_zero
  then show ?case by (cases i) (auto intro: ctx_mem.ctx_zero ctx_mem.ctx_suc)
next
  case (ctx_suc \<Gamma> n A C)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      using ctx_suc(1) by (auto intro: ctx_mem.ctx_suc)
  next
    case (Suc j)
    have ih:
      "ctx_mem (ctx_insert j B \<Gamma>)
        (if n < j then n else Suc n) A"
      using ctx_suc(2)[of j B] .
    from ih Suc show ?thesis
      by (cases "n < j") (auto intro: ctx_mem.ctx_suc)
  qed
qed

lemma ctx_mem_sucD:
  "ctx_mem (B # \<Gamma>) (Suc n) A \<Longrightarrow> ctx_mem \<Gamma> n A"
  by (erule ctx_mem.cases) simp_all

lemma ctx_mem_insert_cases:
  assumes "ctx_mem (ctx_insert i C \<Gamma>) n A" "i \<le> length \<Gamma>"
  shows "(n < i \<and> ctx_mem \<Gamma> n A) \<or>
    (n = i \<and> A = C) \<or>
    (i < n \<and> ctx_mem \<Gamma> (n - 1) A)"
using assms
proof (induct \<Gamma> arbitrary: i n C A)
  case Nil
  then show ?case
    by (cases i; cases n; auto elim: ctx_mem.cases)
next
  case (Cons D \<Gamma>)
  then show ?case
  proof (cases i)
    case 0
    have zero: "i = 0" using 0 .
    have mem0: "ctx_mem (C # D # \<Gamma>) n A"
      using Cons.prems(1) zero by simp
    then show ?thesis
      using mem0 zero
      by (cases rule: ctx_mem.cases)
         (auto intro: ctx_mem.ctx_zero ctx_mem.ctx_suc)
  next
    case (Suc j)
    have isuc: "i = Suc j" using Suc .
    show ?thesis
    proof (cases n)
      case 0
      have nzero: "n = 0" using 0 .
      have mem0: "ctx_mem (D # ctx_insert j C \<Gamma>) 0 A"
        using Cons.prems(1) isuc nzero by simp
      then show ?thesis
        using mem0 isuc nzero
        by (cases rule: ctx_mem.cases)
           (auto intro: ctx_mem.ctx_zero ctx_mem.ctx_suc)
    next
      case (Suc m)
      have nsuc: "n = Suc m" using Suc .
      have source:
        "ctx_mem (D # ctx_insert j C \<Gamma>) (Suc m) A"
        using Cons.prems(1) isuc nsuc by simp
      have mem:
        "ctx_mem (ctx_insert j C \<Gamma>) m A"
        using ctx_mem_sucD[OF source] .
      have len: "j \<le> length \<Gamma>"
        using Cons.prems(2) isuc by simp
      have ih:
        "(m < j \<and> ctx_mem \<Gamma> m A) \<or>
          (m = j \<and> A = C) \<or>
          (j < m \<and> ctx_mem \<Gamma> (m - 1) A)"
        using Cons.hyps[of j C m A] mem len .
      have lift:
        "j < m \<Longrightarrow> ctx_mem \<Gamma> (m - 1) A \<Longrightarrow>
          ctx_mem (D # \<Gamma>) m A"
      proof -
        assume jm: "j < m"
        assume mem': "ctx_mem \<Gamma> (m - 1) A"
        have mpos: "0 < m" using jm by arith
        have eq: "m = Suc (m - 1)" using Suc_pred'[OF mpos] .
        from ctx_mem.ctx_suc[OF mem'] show ?thesis
          using eq by simp
      qed
      show ?thesis
        using ih isuc nsuc
        by (auto simp add: ctx_insert.simps
          intro: lift
          intro: ctx_mem.ctx_zero ctx_mem.ctx_suc)
    qed
  qed
qed

lemma typing_weakening:
  "typing k \<Gamma> M A \<Longrightarrow>
    typing k (ctx_insert i B \<Gamma>) (tm_shift i M) A"
proof (induct arbitrary: i B rule: typing.induct)
  case (ty_var \<Gamma> n A k)
  then show ?case
  proof (cases "n < i")
    case True
    have mem:
        "ctx_mem (ctx_insert i B \<Gamma>)
          (if n < i then n else Suc n) A"
      using ctx_mem_ctx_insert[OF ty_var(1)] .
    then show ?thesis
      using True by (auto intro: typing.ty_var)
  next
    case False
    have mem:
        "ctx_mem (ctx_insert i B \<Gamma>)
          (if n < i then n else Suc n) A"
      using ctx_mem_ctx_insert[OF ty_var(1)] .
    then show ?thesis
      using False by (auto intro: typing.ty_var)
  qed
next
  case ty_app
  then show ?case
    unfolding tm_shift.simps
    by (blast intro: typing.ty_app)
next
  case (ty_lam k0 A0 \<Gamma>0 M0 B0)
  show ?case
    unfolding tm_shift.simps
  proof (rule typing.ty_lam)
    show "wf_ty k0 A0" using ty_lam(1) .
    show "typing k0 (A0 # ctx_insert i B \<Gamma>0)
        (tm_shift (Suc i) M0) B0"
      using ty_lam(3)[of "Suc i" B]
      by (simp add: ctx_insert_Suc_cons)
  qed
next
  case (ty_tabs k0 \<Gamma>0 M0 B0)
  show ?case
    unfolding tm_shift.simps
  proof (rule typing.ty_tabs)
    have ih:
      "typing (Suc k0)
        (ctx_insert i (ty_shift 0 B) (map (ty_shift 0) \<Gamma>0))
        (tm_shift i M0) B0"
      using ty_tabs(2)[of i "ty_shift 0 B"] .
    then show "typing (Suc k0)
        (map (ty_shift 0) (ctx_insert i B \<Gamma>0))
        (tm_shift i M0) B0"
      by (simp add: map_ctx_insert)
  qed
next
  case (ty_tapp k0 \<Gamma>0 M0 B0 A0)
  show ?case
    unfolding tm_shift.simps
  proof (rule typing.ty_tapp)
    show "typing k0 (ctx_insert i B \<Gamma>0) (tm_shift i M0)
        (TyAll B0)"
      using ty_tapp(2)[of i B] .
    show "wf_ty k0 A0" using ty_tapp(3) .
  qed
qed

lemma wf_ty_shift_at:
  assumes "wf_ty k A" "l \<le> k"
  shows "wf_ty (Suc k) (ty_shift l A)"
  using assms
proof (induct arbitrary: l rule: wf_ty.induct)
  case (wf_var n k l)
  then show ?case
  proof (cases "n < l")
    case True
    have "n < Suc k"
      using wf_var.hyps wf_var.prems by arith
    have wf: "wf_ty (Suc k) (TyVar n)"
      by (rule wf_ty.wf_var) fact
    then show ?thesis
      using wf by (simp add: ty_shift.simps True)
  next
    case False
    have "Suc n < Suc k"
      using wf_var.hyps by simp
    have wf: "wf_ty (Suc k) (TyVar (Suc n))"
      by (rule wf_ty.wf_var) fact
    then show ?thesis
      using wf by (simp add: ty_shift.simps False)
  qed
next
  case (wf_arr k A B l)
  then show ?case
    by (auto intro: wf_ty.wf_arr)
next
  case (wf_all k A l)
  then show ?case
    by (auto intro: wf_ty.wf_all)
qed

lemma wf_ty_shift:
  assumes "wf_ty k A"
  shows "wf_ty (Suc k) (ty_shift 0 A)"
  using wf_ty_shift_at[OF assms, of 0] by simp

lemma ctx_mem_map:
  assumes "ctx_mem \<Gamma> n A"
  shows "ctx_mem (map f \<Gamma>) n (f A)"
  using assms
  by (induct rule: ctx_mem.induct)
     (auto intro: ctx_mem.ctx_zero ctx_mem.ctx_suc)

lemma ty_shift_commute:
  assumes "i \<le> j"
  shows "ty_shift i (ty_shift j A) =
    ty_shift (Suc j) (ty_shift i A)"
  using assms
proof (induct A arbitrary: i j)
  case (TyVar n i j)
  then show ?case
    by (cases "n < i"; cases "n < j"; simp_all; arith)
next
  case (TyArr A B i j)
  then show ?case by simp
next
  case (TyAll A i j)
  then show ?case
    by (simp_all add: ty_shift.simps)
qed

lemma ty_subst_shift:
  assumes "l \<le> k"
  shows "ty_subst (Suc k) (ty_shift l S) (ty_shift l A) =
    ty_shift l (ty_subst k S A)"
  using assms
proof (induct A arbitrary: k l S)
  case (TyVar n k l S)
  then show ?case
    by (cases "n < l"; cases "n < k"; cases "n = k";
        simp_all split: if_splits; arith)
next
  case (TyArr A B k l S)
  then show ?case by simp
next
  case (TyAll A k l S)
  then show ?case
    by (simp_all add: ty_shift_commute)
qed

lemma ty_subst_ty_shift:
  "ty_subst (Suc k) (ty_shift 0 S) (ty_shift 0 A) =
    ty_shift 0 (ty_subst k S A)"
  using ty_subst_shift[of 0 k S A] by simp

lemma ty_subst_shift_suc:
  assumes "k \<le> l"
  shows "ty_subst k (ty_shift l S) (ty_shift (Suc l) A) =
    ty_shift l (ty_subst k S A)"
  using assms
proof (induct A arbitrary: k l S)
  case (TyVar n k l S)
  then show ?case
    by (cases "n < l"; cases "n < Suc l"; cases "n < k";
        cases "n = k"; simp_all split: if_splits; arith)
next
  case (TyArr A B k l S)
  then show ?case by simp
next
  case (TyAll A k l S)
  then show ?case
    by (simp_all add: ty_shift_commute)
qed

lemma typing_ty_shift_at:
  assumes "typing k \<Gamma> M A" "l \<le> k"
  shows "typing (Suc k) (map (ty_shift l) \<Gamma>)
    (tm_ty_shift l M) (ty_shift l A)"
  using assms
proof (induct arbitrary: l rule: typing.induct)
  case (ty_var \<Gamma> n A k l)
  then show ?case
    by (auto intro: typing.ty_var ctx_mem_map)
next
  case (ty_app k0 \<Gamma>0 M0 A0 B0 N0 l)
  have M:
    "typing (Suc k0) (map (ty_shift l) \<Gamma>0)
      (tm_ty_shift l M0) (TyArr (ty_shift l A0) (ty_shift l B0))"
    using ty_app(2)[OF ty_app(5)] by (simp add: ty_shift.simps)
  have N:
    "typing (Suc k0) (map (ty_shift l) \<Gamma>0)
      (tm_ty_shift l N0) (ty_shift l A0)"
    using ty_app(4)[OF ty_app(5)] by simp
  show ?case
    unfolding tm_ty_shift.simps
    using typing.ty_app[OF M N] by simp
next
  case (ty_lam k0 A0 \<Gamma>0 M0 B0 l)
  have wf:
    "wf_ty (Suc k0) (ty_shift l A0)"
    using wf_ty_shift_at[OF ty_lam(1) ty_lam(4)] by simp
  have body:
    "typing (Suc k0) (map (ty_shift l) (A0 # \<Gamma>0))
      (tm_ty_shift l M0) (ty_shift l B0)"
    using ty_lam(3)[OF ty_lam(4)] by simp
  then show ?case
    unfolding tm_ty_shift.simps
    using wf by (simp add: typing.ty_lam)
next
  case (ty_tabs k0 \<Gamma>0 M0 B0 l)
  have le: "Suc l \<le> Suc k0"
    using ty_tabs(3) by simp
  have body:
    "typing (Suc (Suc k0))
      (map (ty_shift (Suc l)) (map (ty_shift 0) \<Gamma>0))
      (tm_ty_shift (Suc l) M0) (ty_shift (Suc l) B0)"
    using ty_tabs(2)[of "Suc l", OF le] by simp
  have shift_comp:
    "(ty_shift (Suc l) \<circ> ty_shift 0) =
      (ty_shift 0 \<circ> ty_shift l)"
    by (rule ext; simp add: ty_shift_commute)
  have body':
    "typing (Suc (Suc k0))
      (map (ty_shift 0) (map (ty_shift l) \<Gamma>0))
      (tm_ty_shift (Suc l) M0) (ty_shift (Suc l) B0)"
    using body by (simp add: map_map shift_comp)
  have tabs:
    "typing (Suc k0) (map (ty_shift l) \<Gamma>0)
      (TmTAbs (tm_ty_shift (Suc l) M0))
      (TyAll (ty_shift (Suc l) B0))"
    using typing.ty_tabs[OF body'] by simp
  then show ?case
    by (simp add: tm_ty_shift.simps ty_shift.simps)
next
  case (ty_tapp k0 \<Gamma>0 M0 B0 A0 l)
  have M:
    "typing (Suc k0) (map (ty_shift l) \<Gamma>0)
      (tm_ty_shift l M0) (TyAll (ty_shift (Suc l) B0))"
    using ty_tapp(2)[OF ty_tapp(4)] by simp
  have W:
    "wf_ty (Suc k0) (ty_shift l A0)"
    using wf_ty_shift_at[OF ty_tapp(3) ty_tapp(4)] by simp
  have inst:
    "ty_subst0 (ty_shift l A0) (ty_shift (Suc l) B0) =
      ty_shift l (ty_subst0 A0 B0)"
    unfolding ty_subst0_def
    using ty_subst_shift_suc[of 0 l A0 B0] by simp
  have tapp:
    "typing (Suc k0) (map (ty_shift l) \<Gamma>0)
      (TmTApp (tm_ty_shift l M0) (ty_shift l A0))
      (ty_subst0 (ty_shift l A0) (ty_shift (Suc l) B0))"
    using typing.ty_tapp[OF M W] .
  then show ?case
    using inst by (simp add: tm_ty_shift.simps)
qed

lemma typing_ty_shift:
  "typing k \<Gamma> M A \<Longrightarrow>
    typing (Suc k) (map (ty_shift 0) \<Gamma>)
      (tm_ty_shift 0 M) (ty_shift 0 A)"
  using typing_ty_shift_at[of k \<Gamma> M A 0] by simp

lemma wf_ty_subst_pred:
  assumes "wf_ty n A" "wf_ty (n - 1) S" "j < n"
  shows "wf_ty (n - 1) (ty_subst j S A)"
  using assms
proof (induct arbitrary: S j rule: wf_ty.induct)
  case wf_var
  then show ?case
    by (auto split: if_splits
      intro: wf_ty.wf_var)
next
  case wf_arr
  then show ?case
    by (auto intro: wf_ty.wf_arr)
next
  case (wf_all k0 A0 S0 j0)
  have kpos: "0 < k0"
    using wf_all(4) by arith
  have shiftS: "wf_ty k0 (ty_shift 0 S0)"
    using wf_ty_shift[OF wf_all(3)] by (simp add: kpos)
  have inner: "wf_ty k0
      (ty_subst (Suc j0) (ty_shift 0 S0) A0)"
    using wf_all(2)[of "ty_shift 0 S0" "Suc j0"] shiftS wf_all(4)
    by simp
  then show ?case
    unfolding ty_subst.simps
    using inner
    by (auto intro: wf_ty.wf_all simp add: kpos)
qed

lemma wf_ty_subst_at:
  assumes "wf_ty (Suc k) A" "wf_ty k S" "j \<le> k"
  shows "wf_ty k (ty_subst j S A)"
  using wf_ty_subst_pred[of "Suc k" A S j] assms by simp

lemma ty_subst_shift_id:
  "ty_subst k T (ty_shift k A) = A"
proof (induct A arbitrary: k T)
  case (TyVar n k T)
  then show ?case
    by (cases "n < k"; cases "n = k";
        simp_all add: ty_subst.simps ty_shift.simps split: if_splits; arith)
next
  case (TyArr A1 A2 k T)
  show ?case
    unfolding ty_subst.simps ty_shift.simps
    using TyArr(1)[of k T] TyArr(2)[of k T] by simp
next
  case (TyAll A k T)
  show ?case
    unfolding ty_subst.simps ty_shift.simps
    using TyAll(1)[of "Suc k" "ty_shift 0 T"] by simp
qed

lemma ty_subst_comp_at:
  "i \<le> j \<longrightarrow>
    ty_subst i (ty_subst j S T)
      (ty_subst (Suc j) (ty_shift i S) A) =
    ty_subst j S (ty_subst i T A)"
proof (induct A arbitrary: i j S T rule: dty.induct)
  case (TyVar x)
  then show ?case
    by (intro impI; simp add: ty_subst_shift_id split: if_splits; arith)
next
  case (TyArr A1 A2)
  then show ?case
    by (intro impI; simp_all; blast)
next
  case (TyAll A)
  have result:
    "i \<le> j \<longrightarrow>
      ty_subst (Suc i) (ty_shift 0 (ty_subst j S T))
        (ty_subst (Suc (Suc j))
          (ty_shift 0 (ty_shift i S)) A) =
      ty_subst (Suc j) (ty_shift 0 S)
        (ty_subst (Suc i) (ty_shift 0 T) A)"
  proof (intro impI)
    assume le: "i \<le> j"
    have ih:
      "ty_subst (Suc i)
          (ty_subst (Suc j) (ty_shift 0 S) (ty_shift 0 T))
          (ty_subst (Suc (Suc j))
            (ty_shift (Suc i) (ty_shift 0 S)) A) =
        ty_subst (Suc j) (ty_shift 0 S)
          (ty_subst (Suc i) (ty_shift 0 T) A)"
      using TyAll(1)[of "Suc i" "Suc j" "ty_shift 0 S" "ty_shift 0 T"]
      using le by simp
    have comp:
      "ty_subst (Suc j) (ty_shift 0 S) (ty_shift 0 T) =
        ty_shift 0 (ty_subst j S T)"
      using ty_subst_shift[of 0 j S T] by simp
    have shift:
      "ty_shift (Suc i) (ty_shift 0 S) =
        ty_shift 0 (ty_shift i S)"
      using ty_shift_commute[of 0 i S] by simp
    have ih':
      "ty_subst (Suc i)
          (ty_subst (Suc j) (ty_shift 0 S) (ty_shift 0 T))
          (ty_subst (Suc (Suc j))
            (ty_shift 0 (ty_shift i S)) A) =
        ty_subst (Suc j) (ty_shift 0 S)
          (ty_subst (Suc i) (ty_shift 0 T) A)"
      using ih by (simp only: shift[symmetric])
    have outer:
      "ty_subst (Suc i) (ty_shift 0 (ty_subst j S T))
          (ty_subst (Suc (Suc j))
            (ty_shift 0 (ty_shift i S)) A) =
        ty_subst (Suc i)
          (ty_subst (Suc j) (ty_shift 0 S) (ty_shift 0 T))
          (ty_subst (Suc (Suc j))
            (ty_shift 0 (ty_shift i S)) A)"
      by (rule arg_cong[OF comp[symmetric]])
    from outer ih' show
      "ty_subst (Suc i) (ty_shift 0 (ty_subst j S T))
          (ty_subst (Suc (Suc j))
            (ty_shift 0 (ty_shift i S)) A) =
        ty_subst (Suc j) (ty_shift 0 S)
          (ty_subst (Suc i) (ty_shift 0 T) A)"
      by simp
  qed
  then show ?case by simp
qed

lemma ty_subst_comp:
  "ty_subst j S (ty_subst 0 T A) =
    ty_subst 0 (ty_subst j S T)
      (ty_subst (Suc j) (ty_shift 0 S) A)"
  using ty_subst_comp_at[of 0 j S T A] by simp

lemma typing_ty_subst_at_aux:
  assumes "typing n \<Gamma> M A" "n = Suc k" "wf_ty k S" "j \<le> k"
  shows "typing k (map (ty_subst j S) \<Gamma>)
    (tm_ty_subst j S M) (ty_subst j S A)"
  using assms
proof (induct arbitrary: k j S rule: typing.induct)
  case (ty_var \<Gamma> n0 A0 k0 k j S)
  then show ?case
    by (auto intro: typing.ty_var ctx_mem_map)
next
  case (ty_app k0 \<Gamma>0 M0 A0 B0 N0 k j S)
  have M:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (tm_ty_subst j S M0)
      (TyArr (ty_subst j S A0) (ty_subst j S B0))"
    using ty_app(2)[OF ty_app(5) ty_app(6) ty_app(7)] by simp
  have N:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (tm_ty_subst j S N0) (ty_subst j S A0)"
    using ty_app(4)[OF ty_app(5) ty_app(6) ty_app(7)] by simp
  show ?case
    unfolding tm_ty_subst.simps
    using typing.ty_app[OF M N] by simp
next
  case (ty_lam k0 A0 \<Gamma>0 M0 B0 k j S)
  have hA: "wf_ty (Suc k) A0"
    using ty_lam(1) ty_lam(4) by simp
  have wf:
    "wf_ty k (ty_subst j S A0)"
    using wf_ty_subst_at[OF hA ty_lam(5) ty_lam(6)] .
  have body:
    "typing k (map (ty_subst j S) (A0 # \<Gamma>0))
      (tm_ty_subst j S M0) (ty_subst j S B0)"
    using ty_lam(3)[OF ty_lam(4) ty_lam(5) ty_lam(6)] .
  have body':
    "typing k (ty_subst j S A0 # map (ty_subst j S) \<Gamma>0)
      (tm_ty_subst j S M0) (ty_subst j S B0)"
    using body by simp
  have lam:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (TmLam (ty_subst j S A0) (tm_ty_subst j S M0))
      (TyArr (ty_subst j S A0) (ty_subst j S B0))"
    using typing.ty_lam[OF wf body'] .
  show ?case
    unfolding tm_ty_subst.simps
    using lam by simp
next
  case (ty_tabs k0 \<Gamma>0 M0 B0 k j S)
  have k0_eq: "k0 = Suc k"
    using ty_tabs(3) by simp
  have le: "Suc j \<le> k0"
    using ty_tabs(5) k0_eq by simp
  have wfS: "wf_ty k0 (ty_shift 0 S)"
    using wf_ty_shift[OF ty_tabs(4)] k0_eq by simp
  have body:
    "typing k0
      (map (ty_subst (Suc j) (ty_shift 0 S))
        (map (ty_shift 0) \<Gamma>0))
      (tm_ty_subst (Suc j) (ty_shift 0 S) M0)
      (ty_subst (Suc j) (ty_shift 0 S) B0)"
    using ty_tabs(2) wfS le
    by simp
  have ctx_eq:
    "(ty_subst (Suc j) (ty_shift 0 S) \<circ> ty_shift 0) =
      (ty_shift 0 \<circ> ty_subst j S)"
    by (rule ext; simp add: ty_subst_ty_shift)
  have body':
    "typing k0
      (map (ty_shift 0) (map (ty_subst j S) \<Gamma>0))
      (tm_ty_subst (Suc j) (ty_shift 0 S) M0)
      (ty_subst (Suc j) (ty_shift 0 S) B0)"
    using body by (simp add: map_map ctx_eq)
  have tabs:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (TmTAbs (tm_ty_subst (Suc j) (ty_shift 0 S) M0))
      (TyAll (ty_subst (Suc j) (ty_shift 0 S) B0))"
    using typing.ty_tabs[of k "map (ty_subst j S) \<Gamma>0"
      "tm_ty_subst (Suc j) (ty_shift 0 S) M0"
      "ty_subst (Suc j) (ty_shift 0 S) B0"]
      body'
    by (simp add: k0_eq)
  then show ?case by simp
next
  case (ty_tapp k0 \<Gamma>0 M0 B0 A0 k j S)
  have hA: "wf_ty (Suc k) A0"
    using ty_tapp(3) ty_tapp(4) by simp
  have M:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (tm_ty_subst j S M0)
      (TyAll (ty_subst (Suc j) (ty_shift 0 S) B0))"
    using ty_tapp(2)[OF ty_tapp(4) ty_tapp(5) ty_tapp(6)] by simp
  have wf:
    "wf_ty k (ty_subst j S A0)"
    using wf_ty_subst_at[OF hA ty_tapp(5) ty_tapp(6)] .
  have tapp:
    "typing k (map (ty_subst j S) \<Gamma>0)
      (TmTApp (tm_ty_subst j S M0) (ty_subst j S A0))
      (ty_subst0 (ty_subst j S A0)
        (ty_subst (Suc j) (ty_shift 0 S) B0))"
    using typing.ty_tapp[OF M wf] .
  have result:
    "ty_subst j S (ty_subst0 A0 B0) =
      ty_subst0 (ty_subst j S A0)
        (ty_subst (Suc j) (ty_shift 0 S) B0)"
    using ty_subst_comp[of j S A0 B0] by (simp add: ty_subst0_def)
  then show ?case
    using tapp by (simp add: tm_ty_subst.simps result)
qed

lemma typing_ty_subst_at:
  assumes "typing (Suc k) \<Gamma> M A" "wf_ty k S" "j \<le> k"
  shows "typing k (map (ty_subst j S) \<Gamma>)
    (tm_ty_subst j S M) (ty_subst j S A)"
proof (rule typing_ty_subst_at_aux[of "Suc k" \<Gamma> M A k S j])
  show "typing (Suc k) \<Gamma> M A" using assms(1) .
  show "Suc k = Suc k" by simp
  show "wf_ty k S" using assms(2) .
  show "j \<le> k" using assms(3) .
qed

lemma typing_ty_subst:
  assumes "typing (Suc k) \<Gamma> M A" "wf_ty k S"
  shows "typing k (map (ty_subst 0 S) \<Gamma>)
    (tm_ty_subst 0 S M) (ty_subst 0 S A)"
  using typing_ty_subst_at[OF assms, of 0] by simp

lemma typing_tm_subst_at:
  assumes "typing k \<Gamma> N C"
    "typing k (ctx_insert i C \<Gamma>) M A"
    "i \<le> length \<Gamma>"
  shows "typing k \<Gamma> (tm_subst i N M) A"
  using assms
proof (induct M arbitrary: k \<Gamma> N C i A rule: dtm.induct)
  case (TmVar n k \<Gamma> N C i A)
  have hmem: "ctx_mem (ctx_insert i C \<Gamma>) n A"
    using TmVar.prems(2)
    by (cases rule: typing.cases) auto
  have mem:
    "(n < i \<and> ctx_mem \<Gamma> n A) \<or>
      (n = i \<and> A = C) \<or>
      (i < n \<and> ctx_mem \<Gamma> (n - 1) A)"
    using ctx_mem_insert_cases[OF hmem TmVar.prems(3)] .
  show ?case
    using mem TmVar.prems(1)
    by (auto simp add: tm_subst.simps
      intro: typing.ty_var ctx_mem.ctx_zero ctx_mem.ctx_suc)
next
  case (TmApp M P k \<Gamma> N C i A)
  obtain B where
    hM: "typing k (ctx_insert i C \<Gamma>) M (TyArr B A)" and
    hP: "typing k (ctx_insert i C \<Gamma>) P B"
    using TmApp.prems(2)
    by (cases rule: typing.cases) auto
  have M:
    "typing k \<Gamma>
      (tm_subst i N M) (TyArr B A)"
    using TmApp.hyps(1)[OF TmApp.prems(1) hM TmApp.prems(3)] .
  have N':
    "typing k \<Gamma> (tm_subst i N P) B"
    using TmApp.hyps(2)[OF TmApp.prems(1) hP TmApp.prems(3)] .
  show ?case
    unfolding tm_subst.simps
    using typing.ty_app[OF M N'] by simp
next
  case (TmLam D M k \<Gamma> N C i A)
  obtain B where
    typeA: "A = TyArr D B" and
    wfD: "wf_ty k D" and
    hM: "typing k (D # ctx_insert i C \<Gamma>) M B"
    using TmLam.prems(2)
    by (cases rule: typing.cases) auto
  have Nshift:
    "typing k (D # \<Gamma>) (tm_shift 0 N) C"
    using typing_weakening[OF TmLam.prems(1), of 0 D]
    by (cases \<Gamma>; simp)
  have len:
    "Suc i \<le> length (D # \<Gamma>)"
    using TmLam.prems(3) by simp
  have hM':
    "typing k (ctx_insert (Suc i) C (D # \<Gamma>)) M B"
    using hM by simp
  have body:
    "typing k (D # \<Gamma>)
      (tm_subst (Suc i) (tm_shift 0 N) M) B"
    using TmLam.hyps[OF Nshift hM' len]
    by simp
  have lam:
    "typing k \<Gamma>
      (TmLam D (tm_subst (Suc i) (tm_shift 0 N) M))
      (TyArr D B)"
    using typing.ty_lam[OF wfD body] .
  show ?case
    unfolding tm_subst.simps
    using lam typeA by simp
next
  case (TmTAbs M k \<Gamma> N C i A)
  obtain B where
    typeA: "A = TyAll B" and
    hM: "typing (Suc k) (map (ty_shift 0) (ctx_insert i C \<Gamma>)) M B"
    using TmTAbs.prems(2)
    by (cases rule: typing.cases) auto
  have Nshift:
    "typing (Suc k) (map (ty_shift 0) \<Gamma>)
      (tm_ty_shift 0 N) (ty_shift 0 C)"
    using typing_ty_shift[OF TmTAbs.prems(1)] .
  have hM':
    "typing (Suc k)
      (ctx_insert i (ty_shift 0 C) (map (ty_shift 0) \<Gamma>)) M B"
    using hM by (simp add: map_ctx_insert)
  have len:
    "i \<le> length (map (ty_shift 0) \<Gamma>)"
    using TmTAbs.prems(3) by simp
  have body:
    "typing (Suc k) (map (ty_shift 0) \<Gamma>)
      (tm_subst i (tm_ty_shift 0 N) M) B"
    using TmTAbs.hyps[OF Nshift hM' len] .
  have tabs:
    "typing k \<Gamma>
      (TmTAbs (tm_subst i (tm_ty_shift 0 N) M))
      (TyAll B)"
    using typing.ty_tabs[OF body] .
  show ?case
    unfolding tm_subst.simps
    using tabs typeA by simp
next
  case (TmTApp M D k \<Gamma> N C i A)
  obtain B where
    typeA: "A = ty_subst0 D B" and
    hM: "typing k (ctx_insert i C \<Gamma>) M (TyAll B)" and
    wfD: "wf_ty k D"
    using TmTApp.prems(2)
    by (cases rule: typing.cases) auto
  have M:
    "typing k \<Gamma> (tm_subst i N M) (TyAll B)"
    using TmTApp.hyps[OF TmTApp.prems(1) hM TmTApp.prems(3)] .
  have tapp:
    "typing k \<Gamma>
      (TmTApp (tm_subst i N M) D)
      (ty_subst0 D B)"
    using typing.ty_tapp[OF M wfD] .
  show ?case
    unfolding tm_subst.simps
    using tapp typeA by simp
qed

lemma typing_tm_subst0:
  assumes "typing k \<Gamma> N C"
    "typing k (C # \<Gamma>) M A"
  shows "typing k \<Gamma> (tm_subst0 N M) A"
proof -
  have major: "typing k (ctx_insert 0 C \<Gamma>) M A"
    using assms(2) by (cases \<Gamma>; simp)
  have sub:
    "typing k \<Gamma> (tm_subst 0 N M) A"
    using typing_tm_subst_at[OF assms(1) major] by simp
  then show ?thesis
    by (simp add: tm_subst0_def)
qed

theorem subject_reduction:
  assumes "typing k \<Gamma> M A" "M \<longrightarrow>\<^sub>\<beta> M'"
  shows "typing k \<Gamma> M' A"
  using assms(2) assms(1)
proof (induct arbitrary: k \<Gamma> A rule: beta.induct)
  case (beta_appL M M' N k \<Gamma> A)
  obtain B where
    hM: "typing k \<Gamma> M (TyArr B A)" and
    hN: "typing k \<Gamma> N B"
    using beta_appL.prems
    by (cases rule: typing.cases) auto
  have hM':
    "typing k \<Gamma> M' (TyArr B A)"
    using beta_appL.hyps(2)[OF hM] .
  show ?case
    using typing.ty_app[OF hM' hN] .
next
  case (beta_appR N N' M k \<Gamma> A)
  obtain B where
    hM: "typing k \<Gamma> M (TyArr B A)" and
    hN: "typing k \<Gamma> N (B)"
    using beta_appR.prems
    by (cases rule: typing.cases) auto
  have hN':
    "typing k \<Gamma> N' B"
    using beta_appR.hyps(2)[OF hN] .
  show ?case
    using typing.ty_app[OF hM hN'] .
next
  case (beta_lam M M' D k \<Gamma> A)
  obtain B where
    wfD: "wf_ty k D" and
    hM: "typing k (D # \<Gamma>) M B" and
    typeA: "A = TyArr D B"
    using beta_lam.prems
    by (cases rule: typing.cases) auto
  have hM':
    "typing k (D # \<Gamma>) M' B"
    using beta_lam.hyps(2)[OF hM] .
  have lam:
    "typing k \<Gamma> (TmLam D M') (TyArr D B)"
    using typing.ty_lam[OF wfD hM'] .
  show ?case
    using lam typeA by simp
next
  case (beta_tabs M M' k \<Gamma> A)
  obtain B where
    hM: "typing (Suc k) (map (ty_shift 0) \<Gamma>) M B" and
    typeA: "A = TyAll B"
    using beta_tabs.prems
    by (cases rule: typing.cases) auto
  have hM':
    "typing (Suc k) (map (ty_shift 0) \<Gamma>) M' B"
    using beta_tabs.hyps(2)[OF hM] .
  have tabs:
    "typing k \<Gamma> (TmTAbs M') (TyAll B)"
    using typing.ty_tabs[OF hM'] .
  show ?case
    using tabs typeA by simp
next
  case (beta_tapp M M' D k \<Gamma> A)
  obtain B where
    hM: "typing k \<Gamma> M (TyAll B)" and
    wfD: "wf_ty k D" and
    typeA: "A = ty_subst0 D B"
    using beta_tapp.prems
    by (cases rule: typing.cases) auto
  have hM':
    "typing k \<Gamma> M' (TyAll B)"
    using beta_tapp.hyps(2)[OF hM] .
  have tapp:
    "typing k \<Gamma> (TmTApp M' D) (ty_subst0 D B)"
    using typing.ty_tapp[OF hM' wfD] .
  show ?case
    using tapp typeA by simp
next
  case (beta_term D M N k \<Gamma> A)
  obtain B where
    hM: "typing k \<Gamma> (TmLam D M) (TyArr D B)" and
    hN: "typing k \<Gamma> N D" and
    typeA: "A = B"
    using beta_term.prems
    by (auto elim: typing.cases)
  obtain wfD: "wf_ty k D" and hbody: "typing k (D # \<Gamma>) M B"
    using hM
    by (auto elim: typing.cases)
  have sub:
    "typing k \<Gamma> (tm_subst0 N M) B"
    using typing_tm_subst0[OF hN hbody] .
  show ?case
    using sub typeA by simp
next
  case (beta_type M D k \<Gamma> A)
  obtain B where
    hM: "typing k \<Gamma> (TmTAbs M) (TyAll B)" and
    wfD: "wf_ty k D" and
    typeA: "A = ty_subst0 D B"
    using beta_type.prems
    by (cases rule: typing.cases) auto
  obtain hbody where
    hbody: "typing (Suc k) (map (ty_shift 0) \<Gamma>) M B"
    using hM
    by (cases rule: typing.cases) auto
  have ctx:
    "(ty_subst 0 D \<circ> ty_shift 0) = id"
    by (rule ext; simp add: ty_subst_shift_id)
  have sub:
    "typing k \<Gamma> (tm_ty_subst0 D M) (ty_subst0 D B)"
    using typing_ty_subst[OF hbody wfD]
    by (simp add: tm_ty_subst0_def ty_subst0_def map_map ctx)
  show ?case
    using sub typeA by simp
qed

end
