theory Superposition_Example
  imports
    Superposition
    IsaFoR_Term_Copy
begin

(* TODO: Add more examples *)
abbreviation trivial_select :: "'a clause \<Rightarrow> 'a clause" where
  "trivial_select _ \<equiv> {#}"

abbreviation trivial_tiebreakers where
  "trivial_tiebreakers _ _ _ \<equiv> False"

abbreviation unit_types where
  "unit_types _ \<equiv> ([], ())"

interpretation nonground_clause.

interpretation selection_function trivial_select
  by unfold_locales auto

(* TODO: We have to get the ground_critical_pair_theorem into the afp *)
locale superposition_example =
  ground_critical_pair_theorem "TYPE('f :: weighted)"
begin

sublocale
  superposition_calculus
    "trivial_select :: ('f , 'v :: infinite) select"
    less_kbo
    unit_types
    trivial_tiebreakers
proof unfold_locales
  show "\<And>C\<^sub>G. transp (trivial_tiebreakers C\<^sub>G)"
    by simp
next
  show "\<And>C\<^sub>G. asymp (trivial_tiebreakers C\<^sub>G)"
    by auto
next
  show "\<And>C\<^sub>G. wfp (trivial_tiebreakers C\<^sub>G)"
    by simp
next
  show "\<And>\<tau>. \<exists>f. ([], ()) = ([], \<tau>)"
    by simp
next
  show "|UNIV :: unit set| \<le>o |UNIV|"
    unfolding UNIV_unit
    by simp
next
   show "transp less_kbo"
    using KBO.S_trans
    unfolding transp_def less_kbo_def
    by blast
next
  show "asymp less_kbo"
    using wfp_imp_asymp wfP_less_kbo
    by blast
next
  show "wfp_on (range term.from_ground) less_kbo"
    using wfp_on_subset[OF wfP_less_kbo subset_UNIV] .
next
  show "totalp_on (range term.from_ground) less_kbo"
    using less_kbo_gtotal
    unfolding totalp_on_def Term.ground_vars_term_empty term.is_ground_iff_range_from_ground
    by blast
next
  fix
    c :: "('f, 'v) context" and
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo c\<langle>t\<^sub>1\<rangle> c\<langle>t\<^sub>2\<rangle>"
    using KBO.S_ctxt less_kbo_def
    by blast
next
  fix
    t\<^sub>1 t\<^sub>2 :: "('f, 'v) term" and
    \<gamma> :: "('f, 'v) subst"

  assume "less_kbo t\<^sub>1 t\<^sub>2"

  then show "less_kbo (t\<^sub>1 \<cdot>t \<gamma>) (t\<^sub>2 \<cdot>t \<gamma>)"
    using less_kbo_subst by blast
next
  fix
    t :: "('f, 'v) term" and
    c :: "('f, 'v) context"
  assume
    "term.is_ground t"
    "context.is_ground c"
    "c \<noteq> \<box>"

  then show "less_kbo t c\<langle>t\<rangle>"
    by (simp add: KBO.S_supt less_kbo_def nectxt_imp_supt_ctxt)
qed

end

end
