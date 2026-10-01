theory System_F
  imports Main
begin

datatype dty =
    TyVar nat
  | TyArr dty dty
  | TyAll dty

datatype dtm =
    TmVar nat
  | TmApp dtm dtm
  | TmLam dty dtm
  | TmTAbs dtm
  | TmTApp dtm dty

fun ty_shift :: "nat \<Rightarrow> dty \<Rightarrow> dty" where
  "ty_shift k (TyVar n) =
    (if n < k then TyVar n else TyVar (Suc n))"
| "ty_shift k (TyArr A B) = TyArr (ty_shift k A) (ty_shift k B)"
| "ty_shift k (TyAll A) = TyAll (ty_shift (Suc k) A)"

fun ty_subst :: "nat \<Rightarrow> dty \<Rightarrow> dty \<Rightarrow> dty" where
  "ty_subst k S (TyVar n) =
    (if n < k then TyVar n else
      if n = k then S else TyVar (n - 1))"
| "ty_subst k S (TyArr A B) =
    TyArr (ty_subst k S A) (ty_subst k S B)"
| "ty_subst k S (TyAll A) =
    TyAll (ty_subst (Suc k) (ty_shift 0 S) A)"

definition ty_subst0 :: "dty \<Rightarrow> dty \<Rightarrow> dty"
where
  "ty_subst0 S A = ty_subst 0 S A"

fun tm_shift :: "nat \<Rightarrow> dtm \<Rightarrow> dtm" where
  "tm_shift k (TmVar n) =
    (if n < k then TmVar n else TmVar (Suc n))"
| "tm_shift k (TmApp M N) = TmApp (tm_shift k M) (tm_shift k N)"
| "tm_shift k (TmLam A M) = TmLam A (tm_shift (Suc k) M)"
| "tm_shift k (TmTAbs M) = TmTAbs (tm_shift k M)"
| "tm_shift k (TmTApp M A) = TmTApp (tm_shift k M) A"

fun tm_ty_shift :: "nat \<Rightarrow> dtm \<Rightarrow> dtm" where
  "tm_ty_shift k (TmVar n) = TmVar n"
| "tm_ty_shift k (TmApp M P) =
    TmApp (tm_ty_shift k M) (tm_ty_shift k P)"
| "tm_ty_shift k (TmLam A M) =
    TmLam (ty_shift k A) (tm_ty_shift k M)"
| "tm_ty_shift k (TmTAbs M) =
    TmTAbs (tm_ty_shift (Suc k) M)"
| "tm_ty_shift k (TmTApp M A) =
    TmTApp (tm_ty_shift k M) (ty_shift k A)"

fun tm_subst :: "nat \<Rightarrow> dtm \<Rightarrow> dtm \<Rightarrow> dtm" where
  "tm_subst k N (TmVar n) =
    (if n < k then TmVar n else
      if n = k then N else TmVar (n - 1))"
| "tm_subst k N (TmApp M P) =
    TmApp (tm_subst k N M) (tm_subst k N P)"
| "tm_subst k N (TmLam A M) =
    TmLam A (tm_subst (Suc k) (tm_shift 0 N) M)"
| "tm_subst k N (TmTAbs M) =
    TmTAbs (tm_subst k (tm_ty_shift 0 N) M)"
| "tm_subst k N (TmTApp M A) =
    TmTApp (tm_subst k N M) A"

definition tm_subst0 :: "dtm \<Rightarrow> dtm \<Rightarrow> dtm"
where
  "tm_subst0 N M = tm_subst 0 N M"

fun tm_ty_subst :: "nat \<Rightarrow> dty \<Rightarrow> dtm \<Rightarrow> dtm" where
  "tm_ty_subst k S (TmVar n) = TmVar n"
| "tm_ty_subst k S (TmApp M N) =
    TmApp (tm_ty_subst k S M) (tm_ty_subst k S N)"
| "tm_ty_subst k S (TmLam A M) =
    TmLam (ty_subst k S A) (tm_ty_subst k S M)"
| "tm_ty_subst k S (TmTAbs M) =
    TmTAbs (tm_ty_subst (Suc k) (ty_shift 0 S) M)"
| "tm_ty_subst k S (TmTApp M A) =
    TmTApp (tm_ty_subst k S M) (ty_subst k S A)"

definition tm_ty_subst0 :: "dty \<Rightarrow> dtm \<Rightarrow> dtm"
where
  "tm_ty_subst0 S M = tm_ty_subst 0 S M"

definition ty_env_cons :: "'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
where
  "ty_env_cons C \<rho> n = (case n of 0 \<Rightarrow> C | Suc k \<Rightarrow> \<rho> k)"

definition tm_env_cons :: "dtm \<Rightarrow> (nat \<Rightarrow> dtm) \<Rightarrow> nat \<Rightarrow> dtm"
where
  "tm_env_cons N \<delta> n = (case n of 0 \<Rightarrow> N | Suc k \<Rightarrow> \<delta> k)"

definition tm_env_shift :: "(nat \<Rightarrow> dtm) \<Rightarrow> nat \<Rightarrow> dtm"
where
  "tm_env_shift \<delta> n =
    (case n of 0 \<Rightarrow> TmVar 0 | Suc k \<Rightarrow> tm_shift 0 (\<delta> k))"

fun tm_subst_env :: "(nat \<Rightarrow> dtm) \<Rightarrow> dtm \<Rightarrow> dtm" where
  "tm_subst_env \<delta> (TmVar k) = \<delta> k"
| "tm_subst_env \<delta> (TmApp M N) =
    TmApp (tm_subst_env \<delta> M) (tm_subst_env \<delta> N)"
| "tm_subst_env \<delta> (TmLam A M) =
    TmLam A (tm_subst_env (tm_env_shift \<delta>) M)"
| "tm_subst_env \<delta> (TmTAbs M) = TmTAbs (tm_subst_env \<delta> M)"
| "tm_subst_env \<delta> (TmTApp M A) =
    TmTApp (tm_subst_env \<delta> M) A"

inductive wf_ty :: "nat \<Rightarrow> dty \<Rightarrow> bool" where
  wf_var: "n < k \<Longrightarrow> wf_ty k (TyVar n)"
| wf_arr: "\<lbrakk>wf_ty k A; wf_ty k B\<rbrakk> \<Longrightarrow>
    wf_ty k (TyArr A B)"
| wf_all: "wf_ty (Suc k) A \<Longrightarrow> wf_ty k (TyAll A)"

inductive ctx_mem :: "dty list \<Rightarrow> nat \<Rightarrow> dty \<Rightarrow> bool" where
  ctx_zero: "ctx_mem (A # \<Gamma>) 0 A"
| ctx_suc: "ctx_mem \<Gamma> k A \<Longrightarrow> ctx_mem (B # \<Gamma>) (Suc k) A"

inductive typing :: "nat \<Rightarrow> dty list \<Rightarrow> dtm \<Rightarrow> dty \<Rightarrow> bool"
  (\<open>_ ; _ \<turnstile> _ : _\<close> [60,60,60,60] 60) where
  ty_var: "ctx_mem \<Gamma> n A \<Longrightarrow> typing k \<Gamma> (TmVar n) A"
| ty_app: "\<lbrakk>typing k \<Gamma> M (TyArr A B); typing k \<Gamma> N A\<rbrakk>
    \<Longrightarrow> typing k \<Gamma> (TmApp M N) B"
| ty_lam: "\<lbrakk>wf_ty k A; typing k (A # \<Gamma>) M B\<rbrakk>
    \<Longrightarrow> typing k \<Gamma> (TmLam A M) (TyArr A B)"
| ty_tabs: "typing (Suc k) (map (ty_shift 0) \<Gamma>) M B
    \<Longrightarrow> typing k \<Gamma> (TmTAbs M) (TyAll B)"
| ty_tapp: "\<lbrakk>typing k \<Gamma> M (TyAll B); wf_ty k A\<rbrakk>
    \<Longrightarrow> typing k \<Gamma> (TmTApp M A) (ty_subst0 A B)"

inductive beta :: "dtm \<Rightarrow> dtm \<Rightarrow> bool"
  (\<open>_ \<longrightarrow>\<^sub>\<beta> _\<close> [80,80] 80) where
  beta_appL: "M \<longrightarrow>\<^sub>\<beta> M' \<Longrightarrow>
    TmApp M N \<longrightarrow>\<^sub>\<beta> TmApp M' N"
| beta_appR: "N \<longrightarrow>\<^sub>\<beta> N' \<Longrightarrow>
    TmApp M N \<longrightarrow>\<^sub>\<beta> TmApp M N'"
| beta_lam: "M \<longrightarrow>\<^sub>\<beta> M' \<Longrightarrow>
    TmLam A M \<longrightarrow>\<^sub>\<beta> TmLam A M'"
| beta_tabs: "M \<longrightarrow>\<^sub>\<beta> M' \<Longrightarrow>
    TmTAbs M \<longrightarrow>\<^sub>\<beta> TmTAbs M'"
| beta_tapp: "M \<longrightarrow>\<^sub>\<beta> M' \<Longrightarrow>
    TmTApp M A \<longrightarrow>\<^sub>\<beta> TmTApp M' A"
| beta_term: "TmApp (TmLam A M) N \<longrightarrow>\<^sub>\<beta> tm_subst0 N M"
| beta_type: "TmTApp (TmTAbs M) A \<longrightarrow>\<^sub>\<beta> tm_ty_subst0 A M"

inductive SN :: "dtm \<Rightarrow> bool" where
  SN_intro: "(\<And>M'. M \<longrightarrow>\<^sub>\<beta> M' \<Longrightarrow> SN M') \<Longrightarrow> SN M"

end
