theory Rewriting_LLRG_LV_Mondaic
  imports Rewriting
    Replace_Constant
begin



subsection \<open>Specific results about rewriting under a linear variable-separated system\<close>
(***************** AUX ********************)

lemma card_varposs_ground:
  "card (varposs s) = 0 \<longleftrightarrow> ground s"
  by (simp add: finite_varposs varposs_empty_gound)

lemma poss_of_term_subst_apply_varposs:
  assumes "p \<in> poss_of_term (constT c) (s \<cdot> \<sigma>)" "(c, 0) \<notin> funas_term s"
  shows "\<exists> q. q \<in> varposs s \<and> q \<le>\<^sub>p p" using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by (cases s) (auto simp: poss_of_term_def)
next
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    apply (cases s)
      apply (auto simp: poss_of_term_def)
      apply (metis position_less_eq_Cons)+
    done
qed

lemma poss_of_term_hole_poss:
  assumes "p \<in> poss_of_term t C\<langle>s\<rangle>" and "hole_pos C \<le>\<^sub>p p"
  shows "p -\<^sub>p hole_pos C \<in> poss_of_term t s" using assms
proof (induct C arbitrary: p)
  case (More f ss C ts)
  from More(3) obtain ps where [simp]: "p = length ss # ps" and h: "hole_pos C \<le>\<^sub>p ps"
    by (metis append_Cons hole_pos.simps(2) less_eq_poss_append_itself pos_les_eq_append_diff)
  show ?case using More(1)[OF _ h] More(2)
    by (auto simp: poss_of_term_def)
qed auto

lemma remove_const_subst_from_match:
  assumes "s \<cdot> const_subst c = C\<langle>l \<cdot> \<sigma>\<rangle>" "(c, 0) \<notin> funas_term l" "linear_term l"
  shows "\<exists> D \<tau>. s = D\<langle>l \<cdot> \<tau>\<rangle>" using assms
proof (induct "card (varposs s)" arbitrary: s)
  case (Suc x)
  from Suc(2) obtain p ps where varposs: "varposs s = insert p ps" "p \<notin> ps"
    by (metis card_Suc_eq)
  let ?s = "s[p \<leftarrow> Fun c []]" have vp: "p \<in> varposs s" using varposs by auto
  then have *: "?s \<cdot> const_subst c = s \<cdot>  const_subst c"
    by (induct s arbitrary: p) (auto simp: nth_list_update map_update intro!: nth_equalityI)
  have "varposs ?s = ps" using varposs varposs_ground_replace_at[of p s "constT c"]
    by auto
  from Suc(1)[of ?s] Suc(2-) varposs obtain D \<tau> where split: "s[p \<leftarrow> constT c] = D\<langle>l \<cdot> \<tau>\<rangle>"
    by (metis "*" \<open>varposs s[p \<leftarrow> constT c] = ps\<close> card_insert_if diff_Suc_1 finite_varposs)
  have wit: "s =  D\<langle>l \<cdot> \<tau>\<rangle>[p \<leftarrow> s |_ p]" unfolding arg_cong[OF split, of "\<lambda> t. t[p \<leftarrow> s |_ p]", symmetric]
    using vp by simp
  from vp split have cases: "p \<bottom> hole_pos D \<or> hole_pos D \<le>\<^sub>p p"
    by auto (metis poss_of_term_const_ctxt_apply poss_of_term_replace_term_at varposs_imp_poss)
  show ?case
  proof (cases "p \<bottom> hole_pos D")
    case True then show ?thesis using wit
      by (auto simp: par_hole_pos_replace_term_context_at)
  next
    case False
    then have hole: "hole_pos D \<le>\<^sub>p p" using cases by auto
    from vp split have "p \<in> poss_of_term (constT c) s[p \<leftarrow> constT c]"
      using poss_of_term_replace_term_at varposs_imp_poss by blast
    from poss_of_term_hole_poss[OF this[unfolded split] hole]
    have "p -\<^sub>p hole_pos D \<in> poss_of_term (constT c) (l \<cdot> \<tau>)"
      by simp
    from poss_of_term_subst_apply_varposs[OF this Suc(4)] obtain q where
      q: "q \<in> varposs l" "q \<le>\<^sub>p (p -\<^sub>p (hole_pos D))" by blast
    show ?thesis using wit Suc(5) hole
      using linear_term_varposs_subst_replace_term[OF Suc(5) q, of \<tau> "s |_ p"]
      by auto
  qed
qed (auto simp: card_varposs_ground ground_subst_apply)




(***************** end AUX ********************)

definition "llrg \<R> \<longleftrightarrow> (\<forall> (l, r) \<in> \<R>. linear_term l \<and> ground r)"

definition "lv \<R> \<longleftrightarrow> (\<forall> (l, r) \<in> \<R>. linear_term l \<and> linear_term r \<and> vars_term l \<inter> vars_term r = {})"

definition "monadic \<F> \<longleftrightarrow> (\<forall> (f, n) \<in> \<F>. n \<le> Suc 0)"

\<comment> \<open>NF of ground terms\<close>

lemma ground_NF_srstep_gsrstep:
  "ground s \<Longrightarrow> s \<in> NF (srstep \<F> \<R>) \<Longrightarrow> s \<in> NF (gsrstep \<F> \<R>)"
  by blast

lemma NF_to_fresh_const_subst_NF:
  assumes lin: "linear_sys \<R>" and fresh_const: "(c, 0) \<notin> funas_rel \<R>" "funas_rel \<R> \<subseteq> \<F>"
    and nf_f: "funas_term s \<subseteq> \<F>" "s \<in> NF (srstep \<F> \<R>)"
  shows "s \<cdot> const_subst c \<in> NF (gsrstep \<H> \<R>)"
proof (rule ccontr)
  assume "s \<cdot> const_subst c \<notin> NF (Restr (srstep \<H> \<R>) (Collect ground))"
  then obtain C l r \<sigma> where step: "(l, r) \<in> \<R>" "s \<cdot> const_subst c = C\<langle>l \<cdot> \<sigma>\<rangle>" by fastforce
  from step(1) have l: "(c, 0) \<notin> funas_term l" "linear_term l" using lin fresh_const
    by (auto simp: funas_rel_def)
  obtain D \<tau> where "s = D\<langle>l \<cdot> \<tau>\<rangle>" using remove_const_subst_from_match[OF step(2) l] by blast
  then show False using step(1) nf_f
    by (meson NF_no_trancl_step fresh_const(2) r_into_trancl' rstepI rstep_trancl_sig_step_r)
qed


lemma fresh_const_subst_NF_pres:
  assumes fresh_const: "(c, 0) \<notin> funas_rel \<R>" "funas_rel \<R> \<subseteq> \<F>"
    and nf_f: "funas_term s \<subseteq> \<F>" "\<F> \<subseteq> \<H>" "(c, 0) \<in> \<H>" "s \<cdot> const_subst c \<in> NF (gsrstep \<H> \<R>)"
  shows "s \<in> NF (srstep \<F> \<R>)"
proof (rule ccontr)
  assume "s \<notin> NF (srstep \<F> \<R>)"
  then obtain C l r \<sigma> where step: "(l, r) \<in> \<R>" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" by fastforce
  let ?\<tau> = "\<lambda> x. if x \<in> vars_term l then (\<sigma> x) \<cdot> const_subst c else Fun c []"
  define D where "D = (C \<cdot>\<^sub>c const_subst c)"
  have s: "s \<cdot> const_subst c = D\<langle>l \<cdot> ?\<tau>\<rangle>" unfolding D_def step(2)
    by (auto simp: subst_compose simp flip: subst_subst_compose intro!: term_subst_eq)
  have funas: "funas_ctxt D \<subseteq> \<H>" "funas_term (l \<cdot> ?\<tau>) \<subseteq> \<H>" "funas_term (r \<cdot> ?\<tau>) \<subseteq> \<H>"
    using step nf_f(1 - 3) fresh_const(2) unfolding D_def
    by (auto simp: funas_ctxt_subst_apply_ctxt funas_term_subst funas_rel_def split: if_splits)
  moreover have "ground_ctxt D" "ground (l \<cdot> ?\<tau>)" "ground (r \<cdot> ?\<tau>)" using arg_cong[OF s, of ground] unfolding D_def
    by (auto intro!: ground_substI)
  ultimately have "(D\<langle>l \<cdot> ?\<tau>\<rangle>, D\<langle>r \<cdot> ?\<tau>\<rangle>) \<in> gsrstep \<H> \<R>" using step(1)
    by (simp add: rstepI sig_stepI)
  then show False using nf_f(4) unfolding s[symmetric]
    by blast
qed

lemma linear_sys_gNF_eq_NF_eq:
  assumes lin: "linear_sys \<R>" "linear_sys \<S>"
   and well: "funas_rel \<R> \<subseteq> \<F>" "funas_rel \<S> \<subseteq> \<F>"
   and fresh: "(c, 0) \<notin> funas_rel \<R>" "(c, 0) \<notin> funas_rel \<S>"
   and lift: "\<F> \<subseteq> \<H>" "(c, 0) \<in> \<H>"
   and nf: "NF (gsrstep \<H> \<R>) = NF (gsrstep \<H> \<S>)"
 shows "NF (srstep \<F> \<R>) = NF (srstep \<F> \<S>)"
proof -
  have [simp]: "\<not> funas_term s \<subseteq> \<F> \<Longrightarrow> s \<in> NF (srstep \<F> \<U>)" for s \<U> by (meson NF_I sig_stepE(1)) 
  have d1: "s \<in> NF (gsrstep \<H> \<R>) \<Longrightarrow> s \<in> NF (gsrstep \<H> \<S>)" for s using nf by auto
  have d2: "s \<in> NF (gsrstep \<H> \<S>) \<Longrightarrow> s \<in> NF (gsrstep \<H> \<R>)" for s using nf by auto
  {fix s assume n: "s \<in> NF (srstep \<F> \<R>)" then have "s \<in> NF (srstep \<F> \<S>)"
      using NF_to_fresh_const_subst_NF[OF lin(1) fresh(1) well(1) _ n, THEN d1]
      using fresh_const_subst_NF_pres[OF fresh(2) well(2) _ lift, of s]
      by (cases "funas_term s \<subseteq> \<F>") simp_all}
  moreover
  {fix s assume n: "s \<in> NF (srstep \<F> \<S>)" then have "s \<in> NF (srstep \<F> \<R>)"
      using NF_to_fresh_const_subst_NF[OF lin(2) fresh(2) well(2) _ n, THEN d2]
      using fresh_const_subst_NF_pres[OF fresh(1) well(1) _ lift, of s]
      by (cases "funas_term s \<subseteq> \<F>") simp_all}
  ultimately show ?thesis by blast
qed


\<comment> \<open>Steps of ground\<close>
lemma gsrsteps_to_srsteps:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  by (meson inf_le1 trancl_mono)

lemma gsrsteps_eq_to_srsteps_eq:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>* \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  by (metis gsrsteps_to_srsteps rtrancl_eq_or_trancl)


lemma gsrsteps_to_rsteps:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>+ \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>+"
  using gsrsteps_to_srsteps srstepsD by blast

lemma gsrsteps_eq_to_rsteps_eq:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>*"
  by (metis gsrsteps_eq_to_srsteps_eq rtrancl_eq_or_trancl srstepsD)


lemma gsrsteps_eq_relcomp_srsteps_relcompD:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>* O (gsrstep \<F> \<S>)\<^sup>* \<Longrightarrow> (s, t) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*"
  using gsrsteps_eq_to_srsteps_eq by blast

lemma gsrsteps_eq_relcomp_to_rsteps_relcomp:
  "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>* O (gsrstep \<F> \<S>)\<^sup>* \<Longrightarrow> (s, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
  using gsrsteps_eq_relcomp_srsteps_relcompD
  using gsrsteps_eq_to_rsteps_eq by blast


lemma ground_srsteps_gsrsteps:
  assumes "ground s" "ground t"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>+"
proof -
  let ?\<sigma> = "\<lambda> _. s"
  from assms(3) have f: "funas_term s \<subseteq> \<F>" using srstepsD by blast
  have "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep \<F> \<R>)\<^sup>+" using assms(3, 1) f
  proof (induct)
    case (base t)
    then have "(s \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> gsrstep \<F> \<R>"
      by (auto intro: srstep_subst_closed)
    then show ?case by auto
  next
    case (step t u)
    from step(2, 4, 5) have "(t \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> gsrstep \<F> \<R>"
      by (auto intro: srstep_subst_closed)
    then show ?case using step(3 - 5)
      by (meson Transitive_Closure.trancl_into_trancl) 
  qed
  then show ?thesis using assms(1, 2)
    by (simp add: ground_subst_apply)
qed

lemma ground_srsteps_eq_gsrsteps_eq:
  assumes "ground s" "ground t"
    and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
  shows "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>*"
  using ground_srsteps_gsrsteps
  by (metis assms rtrancl_eq_or_trancl)

lemma srsteps_eq_relcomp_gsrsteps_relcomp:
  assumes "(s, t) \<in> (srstep \<F> \<R>)\<^sup>* O (srstep \<F> \<S>)\<^sup>*"
    and "ground s" "ground t"
  shows "(s, t) \<in> (gsrstep \<F> \<R>)\<^sup>* O (gsrstep \<F> \<S>)\<^sup>*"
proof -
  from assms(1) obtain u where steps: "(s, u) \<in> (srstep \<F> \<R>)\<^sup>*" "(u, t) \<in> (srstep \<F> \<S>)\<^sup>*"
    by blast
  let ?\<sigma> = "\<lambda> x. s"
  have "(s \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> (srstep \<F> \<R>)\<^sup>*" "(u \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (srstep \<F> \<S>)\<^sup>*" using steps
    using srsteps_eq_subst_closed[OF steps(1), of ?\<sigma>]
    using srsteps_eq_subst_closed[OF steps(2), of ?\<sigma>]
    by (metis rtrancl_eq_or_trancl srstepsD)+
  then have  "(s \<cdot> ?\<sigma>, u \<cdot> ?\<sigma>) \<in> (gsrstep \<F> \<R>)\<^sup>*" "(u \<cdot> ?\<sigma>, t \<cdot> ?\<sigma>) \<in> (gsrstep \<F> \<S>)\<^sup>*"
    using assms(2)
    by (auto intro: ground_srsteps_eq_gsrsteps_eq)
  then show ?thesis using assms(2, 3)
    by (auto simp: ground_subst_apply)
qed

\<comment> \<open>Steps of llrg systems\<close>

lemma llrg_ground_rhs:
  "llrg \<R> \<Longrightarrow> (l, r) \<in> \<R> \<Longrightarrow> ground r"
  unfolding llrg_def by auto

lemma llrg_rrsteps_groundness:
  assumes "llrg \<R>" and "(s, t) \<in> (srrstep \<F> \<R>)"
  shows "ground t" using assms(2) ground_vars_term_empty
  by (fastforce simp: llrg_def sig_step_def dest!: llrg_ground_rhs[OF assms(1)] split: prod.splits)

lemma llrg_rsteps_pres_groundness:
  assumes "llrg \<R>" "ground s"
   and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>*"
 shows "ground t" using assms(3, 2)
proof (induct rule: rtrancl.induct)
  case (rtrancl_into_rtrancl s t u)
  then have "ground t" by auto
  then show ?case using rtrancl_into_rtrancl(3)
    by (auto simp: sig_step_def vars_term_ctxt_apply ground_vars_term_empty ground_subst_apply
      dest!: llrg_ground_rhs[OF assms(1)] rstep_imp_C_s_r split: prod.splits)
qed simp

lemma llrg_srsteps_with_root_step_ground:
  assumes "llrg \<R>" and "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
  shows "ground t" using assms llrg_rrsteps_groundness llrg_rsteps_pres_groundness
  unfolding srsteps_with_root_step_def
  by blast

lemma llrg_srsteps_with_root_step_inv_ground:
  assumes "llrg \<R>" and "(s, t) \<in> srsteps_with_root_step \<F> (\<R>\<inverse>)"
  shows "ground s" using assms llrg_rrsteps_groundness llrg_rsteps_pres_groundness
  unfolding srsteps_with_root_step_def
  by (metis (no_types, lifting) converseD relcomp.cases rtrancl_converseD srrstep_converse_dist srstep_converse_dist)

lemma llrg_funas_term_step_pres:
  assumes "llrg \<R>" and "(s, t) \<in> (rstep \<R>)"
  shows "funas_term t \<subseteq> funas_rel \<R> \<union> funas_term s"
proof -
  have [simp]: "(l, r) \<in> \<R> \<Longrightarrow> r \<cdot> \<sigma> = r" for l r \<sigma>  using assms(1) unfolding llrg_def
    by(auto split: prod.splits intro: ground_subst_apply)
  show ?thesis using assms
    by (auto simp: llrg_def funas_rel_def dest!: rstep_imp_C_s_r)
qed

lemma llrg_funas_term_steps_pres:
  assumes "llrg \<R>" and "(s, t) \<in> (rstep \<R>)\<^sup>*"
  shows "funas_term t \<subseteq> funas_rel \<R> \<union> funas_term s"
  using assms(2) llrg_funas_term_step_pres[OF assms(1)]
  by (induct) auto

\<comment> \<open>Steps of monadic llrg systems\<close>


lemma monadic_ground_ctxt_apply:
  "monadic \<F> \<Longrightarrow> funas_ctxt C \<subseteq> \<F> \<Longrightarrow> ground r \<Longrightarrow> ground C\<langle>r\<rangle>"
  by (induct C) (auto simp: monadic_def)

lemma llrg_monadic_rstep_pres_groundness:
  assumes "llrg \<R>" "monadic \<F>"
   and "(s, t) \<in> srstep \<F> \<R>"
  shows "ground t" using assms(3)
proof -
  from assms(3) obtain C l r \<sigma> where r: "(l, r) \<in> \<R>" and t:"t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    using rstep_imp_C_s_r unfolding sig_step_def by blast
  from assms(1, 3) have funas: "funas_term t \<subseteq> \<F>" "ground r"
    by (auto simp: llrg_ground_rhs[OF assms(1) r(1)] dest: srstepD)
  then have *: "r \<cdot> \<sigma> = r" by (simp add: ground_subst_apply) 
  show ?thesis using funas assms(2) unfolding t *
    by (intro monadic_ground_ctxt_apply) auto
qed

lemma llrg_monadic_rsteps_groundness:
  assumes "llrg \<R>" "monadic \<F>"
   and "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "ground t" using assms(3)
  using llrg_monadic_rstep_pres_groundness[OF assms(1 ,2)]
  by (induct rule: trancl.induct) auto

\<comment> \<open>Steps in monadic lv system\<close>

fun monadic_term where
  "monadic_term (Var x) = True"
| "monadic_term (Fun f []) = True"
| "monadic_term (Fun f ts) = (length ts = Suc 0 \<and> monadic_term (hd ts))"

fun monadic_get_leave where
  "monadic_get_leave (Var x) = (Var x)"
| "monadic_get_leave (Fun f []) = Fun f []"
| "monadic_get_leave (Fun f ts) = monadic_get_leave (hd ts)"

fun monadic_replace_leave where
  "monadic_replace_leave t (Var x) = t"
| "monadic_replace_leave t (Fun f []) = t"
| "monadic_replace_leave t (Fun f ts) = Fun f [monadic_replace_leave t (hd ts)]"


lemma monadic_replace_leave_undo_const_subst:
  assumes "monadic_term s"
  shows "monadic_replace_leave (monadic_get_leave s) (s \<cdot> const_subst c) = s" using assms
proof (induct s)
  case (Fun f ts) then show ?case
    by (cases ts) auto
qed auto

lemma monadic_replace_leave_context:
  assumes "monadic_term C\<langle>s\<rangle>"
  shows "monadic_replace_leave t C\<langle>s\<rangle> = C\<langle>monadic_replace_leave t s\<rangle>" using assms
proof (induct C)
  case (More f ss C ts) then show ?case
    by (cases ss; cases ts) auto
qed simp

lemma monadic_replace_leave_subst:
  assumes "monadic_term (s \<cdot> \<sigma>)" "\<not> ground s"
  shows "monadic_replace_leave t (s \<cdot> \<sigma>) = s \<cdot> (\<lambda> x. monadic_replace_leave t (\<sigma> x))" using assms
proof (induct s)
  case (Fun f ts) then show ?case
    by (cases ts) auto
qed auto

lemma monadic_sig:
  "monadic \<F> \<Longrightarrow> (f, length ts) \<in> \<F> \<Longrightarrow> length ts \<le> Suc 0"
  by (auto simp: monadic_def)

lemma monadic_sig_funas_term_mt:
  "monadic \<F> \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> monadic_term s"
proof (induct s)
  case (Fun f ts) then show ?case unfolding monadic_def
    by (cases ts) auto
qed simp

lemma monadic_term_const_pres [intro]:
  "monadic_term s \<Longrightarrow> monadic_term (s \<cdot> const_subst c)"
proof (induct s)
  case (Fun f ts) then show ?case
    by (cases ts) auto
qed simp

lemma remove_const_lv_mondaic_step_lhs:
  assumes lv: "lv \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
   and mon: "monadic \<F>"
   and step: "(s \<cdot> const_subst c, t) \<in> (srstep \<F> \<R>)"
 shows "(s, t) \<in> (srstep \<F> \<R>)"
proof -
  from step obtain C l r \<sigma> where s: "(l, r) \<in> \<R>" "s \<cdot> const_subst c = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    by fastforce
  have lv: "x \<in> vars_term l \<Longrightarrow> x \<notin> vars_term r" for x using s(1) lv
    by (auto simp: lv_def)
  from s(1) fresh have cl: "(c, 0) \<notin> funas_term l" by (auto simp: funas_rel_def)
  have funas: "funas_term s \<subseteq> \<F>" "(c, 0) \<notin> funas_term l" "funas_term t \<subseteq> \<F>" using s(1) fresh
    using step mon funas_term_subst unfolding funas_rel_def
    by (auto dest!: srstepD) blast
  then have mt: "monadic_term s" "monadic_term (s \<cdot> const_subst c)"
    using monadic_sig_funas_term_mt[OF mon] by auto
  then have ml: "monadic_term (l \<cdot> \<sigma>)" unfolding s(2)
    by (metis funas_ctxt_apply le_sup_iff step mon monadic_sig_funas_term_mt s(2) sig_stepE(1))
  show ?thesis
  proof (cases "ground s")
    case True then show ?thesis using step
      by (auto simp: ground_subst_apply)
  next
    case False note ng = this
    then have cs: "(c, 0) \<in> funas_term (s \<cdot> const_subst c)"
      by (auto simp: funas_term_subst vars_term_empty_ground)
    have ngrl: "\<not> ground l" using s(2) cs mt ng
    proof (induct s arbitrary: C)
      case (Var x) then show ?case using cl cs
        by (cases C) (auto simp: funas_rel_def ground_subst_apply)
    next
      case (Fun f ts)
      from Fun(5-) obtain t where [simp]: "ts = [t]" by (cases ts) auto
      show ?case
      proof (cases "C = Hole")
        case True then show ?thesis using Fun(2, 3) cl
          by (auto simp: ground_subst_apply)
      next
        case False
        from this Fun(2, 3) obtain D where [simp]: "C = More f [] D []"
          by (cases C) (auto simp: Cons_eq_append_conv)
        show ?thesis using Fun(1)[of t D] Fun(2-)
          by simp
      qed
    qed
    let ?\<tau> = "\<lambda> x. if x \<in> vars_term l then monadic_replace_leave (monadic_get_leave s) (\<sigma> x) else (\<sigma> x)"
    have "C\<langle>l \<cdot> (\<lambda> x. monadic_replace_leave (monadic_get_leave s) (\<sigma> x))\<rangle> = C\<langle>l \<cdot> ?\<tau>\<rangle>"
      by (auto intro: term_subst_eq)
    then have "s = C\<langle>l \<cdot> ?\<tau>\<rangle>" using arg_cong[OF s(2), of "monadic_replace_leave (monadic_get_leave s)",
      unfolded monadic_replace_leave_undo_const_subst[OF mt(1), of c],
      unfolded monadic_replace_leave_context[OF mt(2)[unfolded s(2)]],
      unfolded monadic_replace_leave_subst[OF ml ngrl]]
      by presburger
    moreover have "t = C\<langle>r \<cdot> ?\<tau>\<rangle>" using lv unfolding s(3)
      by (auto intro!: term_subst_eq)
    ultimately show ?thesis using s(1) funas(1, 3)
      by blast
  qed
qed

lemma remove_const_lv_mondaic_step_rhs:
  assumes lv: "lv \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and mon: "monadic \<F>"
    and step: "(s, t \<cdot> const_subst c) \<in> (srstep \<F> \<R>)"
  shows "(s, t) \<in> (srstep \<F> \<R>)"
proof -
  have inv_v: "lv (\<R>\<inverse>)""(c, 0) \<notin> funas_rel (\<R>\<inverse>)" using fresh lv
    by (auto simp: funas_rel_def lv_def)
  have "(t \<cdot> const_subst c, s) \<in> (srstep \<F> (\<R>\<inverse>))" using step
    by (auto simp: rew_converse_outwards)
  from remove_const_lv_mondaic_step_lhs[OF inv_v mon this]
  have "(t, s) \<in> (srstep \<F> (\<R>\<inverse>))" by simp
  then show ?thesis by (auto simp: rew_converse_outwards)
qed

lemma remove_const_lv_mondaic_steps_lhs:
  assumes lv: "lv \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and mon: "monadic \<F>"
    and steps: "(s \<cdot> const_subst c, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  using remove_const_lv_mondaic_step_lhs[OF lv fresh mon] steps
  by (meson converse_tranclE r_into_trancl trancl_into_trancl2)

lemma remove_const_lv_mondaic_steps_rhs:
  assumes lv: "lv \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and mon: "monadic \<F>"
    and steps: "(s, t \<cdot> const_subst c) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  using remove_const_lv_mondaic_step_rhs[OF lv fresh mon] steps
  by (meson trancl.simps)


lemma remove_const_lv_mondaic_steps:
  assumes lv: "lv \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and mon: "monadic \<F>"
    and steps: "(s \<cdot> const_subst c, t \<cdot> const_subst c) \<in> (srstep \<F> \<R>)\<^sup>+"
  shows "(s, t) \<in> (srstep \<F> \<R>)\<^sup>+"
  using remove_const_lv_mondaic_steps_rhs[OF lv fresh mon remove_const_lv_mondaic_steps_lhs[OF assms]]
  by simp

\<comment> \<open>Steps on lv trs\<close>

lemma lv_root_step_idep_subst:
  assumes "lv \<R>"
    and "(s, t) \<in> srrstep \<F> \<R>"
    and well: "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>" "\<And> x. funas_term (\<tau> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in>  srrstep \<F> \<R>"
proof -
  from assms(2) obtain l r \<gamma> where mid: "s = l \<cdot> \<gamma>" "t = r \<cdot> \<gamma>" "(l, r) \<in> \<R>"
    by (auto simp: sig_step_def)
  from mid(3) assms(1) have vs: "x \<in> vars_term l \<Longrightarrow> x \<notin> vars_term r" for x
    by (auto simp: lv_def)
  let ?\<sigma> = "\<lambda> x. if x \<in> vars_term l then (\<gamma> x) \<cdot> \<sigma> else (\<gamma> x) \<cdot> \<tau>"
  have subst: "s \<cdot> \<sigma> = l \<cdot> ?\<sigma>" "t \<cdot> \<tau> = r \<cdot> ?\<sigma>"
    unfolding mid subst_subst_compose[symmetric]
    unfolding term_subst_eq_conv
    by (auto simp: subst_compose_def vs)
  then show ?thesis unfolding subst
    using assms(2) mid(3) well unfolding mid(1, 2)
    by (auto simp: sig_step_def funas_term_subst)
qed


lemma lv_srsteps_with_root_step_idep_subst:
  assumes "lv \<R>"
    and "(s, t) \<in> srsteps_with_root_step \<F> \<R>"
    and well: "\<And> x. funas_term (\<sigma> x) \<subseteq> \<F>" "\<And> x. funas_term (\<tau> x) \<subseteq> \<F>"
  shows "(s \<cdot> \<sigma>, t \<cdot> \<tau>) \<in> srsteps_with_root_step \<F> \<R>" using assms(2)
  using lv_root_step_idep_subst[OF assms(1) _ well, where ?x1 = id and ?x2 = id]
  using srsteps_eq_subst_closed[OF _ well(1), where ?x1 = id and ?\<R> = \<R>]
  using srsteps_eq_subst_closed[OF _ well(2), where ?x1 = id and ?\<R> = \<R>]
  by (auto simp: srsteps_with_root_step_def) (metis (full_types) relcomp3_I)

end