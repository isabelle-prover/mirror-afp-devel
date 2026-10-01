theory System_F_Erasure
  imports System_F System_F_Untyped
begin

fun f_erase :: "dtm \<Rightarrow> ulam" where
  "f_erase (TmVar n) = UVar n"
| "f_erase (TmApp M N) = UApp (f_erase M) (f_erase N)"
| "f_erase (TmLam A M) = ULam (f_erase M)"
| "f_erase (TmTAbs M) = f_erase M"
| "f_erase (TmTApp M A) = f_erase M"

lemma f_erase_tm_shift:
  "f_erase (tm_shift k M) = u_shift k (f_erase M)"
  by (induct M arbitrary: k rule: dtm.induct) simp_all

lemma f_erase_tm_ty_shift:
  "f_erase (tm_ty_shift k M) = f_erase M"
  by (induct M arbitrary: k rule: dtm.induct) simp_all

lemma f_erase_tm_subst:
  "f_erase (tm_subst k N M) =
    u_subst k (f_erase N) (f_erase M)"
  by (induct M arbitrary: k N rule: dtm.induct)
     (simp_all add: f_erase_tm_shift f_erase_tm_ty_shift)

lemma f_erase_tm_ty_subst:
  "f_erase (tm_ty_subst k S M) = f_erase M"
  by (induct M arbitrary: k S rule: dtm.induct) simp_all

lemma f_erase_tm_subst0:
  "f_erase (tm_subst0 N M) =
    u_subst0 (f_erase N) (f_erase M)"
  by (simp add: tm_subst0_def u_subst0_def f_erase_tm_subst)

lemma f_erase_tm_ty_subst0:
  "f_erase (tm_ty_subst0 S M) = f_erase M"
  by (simp add: tm_ty_subst0_def f_erase_tm_ty_subst)

fun f_type_count :: "dtm \<Rightarrow> nat" where
  "f_type_count (TmVar n) = 0"
| "f_type_count (TmApp M N) = f_type_count M + f_type_count N"
| "f_type_count (TmLam A M) = f_type_count M"
| "f_type_count (TmTAbs M) = Suc (f_type_count M)"
| "f_type_count (TmTApp M A) = Suc (f_type_count M)"

lemma f_type_count_tm_ty_subst:
  "f_type_count (tm_ty_subst k S M) = f_type_count M"
  by (induct M arbitrary: k S rule: dtm.induct) simp_all

lemma f_type_count_tm_ty_subst0:
  "f_type_count (tm_ty_subst0 S M) = f_type_count M"
  by (simp add: tm_ty_subst0_def f_type_count_tm_ty_subst)

lemma f_beta_progress:
  assumes "M \<longrightarrow>\<^sub>\<beta> M'"
  shows "ubeta (f_erase M) (f_erase M') \<or>
    f_erase M = f_erase M' \<and>
      f_type_count M' < f_type_count M"
  using assms
proof (induct rule: beta.induct)
  case beta_appL
  then show ?case
    by (auto intro: ubeta.uappL)
next
  case beta_appR
  then show ?case
    by (auto intro: ubeta.uappR)
next
  case beta_lam
  then show ?case
    by (auto intro: ubeta.ulam)
next
  case beta_tabs
  then show ?case
    by auto
next
  case beta_tapp
  then show ?case
    by auto
next
  case (beta_term A M N)
  have root:
    "ubeta (UApp (ULam (f_erase M)) (f_erase N))
      (u_subst0 (f_erase N) (f_erase M))"
    by (rule ubeta.ured)
  then show ?case
    by (simp add: f_erase_tm_subst0 u_subst0_def)
next
  case beta_type
  then show ?case
    by (rule disjI2;
      simp add: f_erase_tm_ty_subst0 f_type_count_tm_ty_subst0)
qed

lemma fSN_reflect:
  assumes "uSN (f_erase M)"
  shows "SN M"
proof -
  have aux: "\<And>U. uSN U \<Longrightarrow>
      \<forall>M. f_erase M = U \<longrightarrow> SN M"
  proof -
    fix U
    assume "uSN U"
    then show "\<forall>M. f_erase M = U \<longrightarrow> SN M"
    proof (induct rule: uSN.induct)
      case (uSN_intro U)
      show ?case
      proof (intro allI impI)
        fix M
        assume eM: "f_erase M = U"
        have type_aux:
          "\<And>n. \<forall>X. f_type_count X = n \<longrightarrow>
            f_erase X = U \<longrightarrow> SN X"
        proof -
          fix n
          show "\<forall>X. f_type_count X = n \<longrightarrow>
            f_erase X = U \<longrightarrow> SN X"
          proof (induct n rule: less_induct)
            case (less n)
            show ?case
            proof (intro allI impI impI)
              fix X
              assume countX: "f_type_count X = n"
              assume eX: "f_erase X = U"
              show "SN X"
              proof (rule SN.SN_intro)
                fix X'
                assume red: "X \<longrightarrow>\<^sub>\<beta> X'"
                have prog:
                  "ubeta (f_erase X) (f_erase X') \<or>
                    f_erase X = f_erase X' \<and>
                      f_type_count X' < f_type_count X"
                  using f_beta_progress[OF red] .
                then show "SN X'"
                proof (elim disjE)
                  assume ured: "ubeta (f_erase X) (f_erase X')"
                  have ured': "U \<longrightarrow>\<^sub>u f_erase X'"
                    using ured by (simp only: eX[symmetric])
                  have ih:
                    "\<forall>R. f_erase X' = f_erase R \<longrightarrow> SN R"
                  proof (intro allI impI)
                    fix R
                    assume eq: "f_erase X' = f_erase R"
                    have eq': "f_erase R = f_erase X'"
                      using eq by simp
                    from uSN_intro(2)[OF ured'] show "SN R"
                      using eq' by blast
                  qed
                  from ih show "SN X'" by blast
                next
                  assume dec:
                    "f_erase X = f_erase X' \<and>
                      f_type_count X' < f_type_count X"
                  have count_lt: "f_type_count X' < n"
                    using countX dec by arith
                  have ih:
                    "\<forall>R. f_type_count R = f_type_count X' \<longrightarrow>
                      f_erase R = U \<longrightarrow> SN R"
                    using less[of "f_type_count X'"] count_lt by blast
                  have eEq: "f_erase X = f_erase X'"
                    using dec by blast
                  have eX': "f_erase X' = U"
                    using eEq eX by simp
                  from ih eX' show "SN X'" by simp
                qed
              qed
            qed
          qed
        qed
        from type_aux[of "f_type_count M"] eM
        show "SN M" by simp
      qed
    qed
  qed
  then show "SN M" using assms by blast
qed

end
