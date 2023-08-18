theory Replace_Constant
  imports Rewriting
begin

subsection \<open>Removing/Replacing constants in a rewrite sequence that do not appear in the rewrite system\<close>
lemma funas_term_const_subst_conv:
  "(c, 0) \<notin> funas_term l \<longleftrightarrow> \<not> (l \<unrhd> constT c)"
proof (induct l)
  case (Fun f ts) then show ?case
    by auto (metis Fun_supt supteq_supt_conv term.inject(2))+
qed (auto simp add: supteq_var_imp_eq)

lemma fresh_const_single_step_replace:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and occ: "p \<in> poss_of_term (constT c) s" and step: "(s, t) \<in> rstep \<R>"
  shows "(s[p \<leftarrow> u], t) \<in> rstep \<R> \<or>
    (\<exists> q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> rstep \<R>)"
proof -
  from occ have const: "p \<in> poss s \<and> s |_ p = constT c" by auto
  from step obtain C l r \<sigma> where t [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and rule: "(l, r) \<in> \<R>" by blast
  from rule lin have lin: "linear_term l" "linear_term r" by fastforce+
  from fresh rule have nt_lhs: "(c, 0) \<notin> funas_term l" by (auto simp: funas_rel_def)
  consider (par) "p \<bottom> (hole_pos C)" | (below) "hole_pos C \<le>\<^sub>p p" using occ
    by (auto dest: poss_of_term_const_ctxt_apply)
  then show ?thesis
  proof cases
    case par
    then have possc: "p \<in> possc C" using const t possc_def by blast 
    then have "p \<in> poss_of_term (constT c) t" "(s[p \<leftarrow> u], t[p \<leftarrow> u]) \<in> rstep \<R>"
      using const par_hole_pos_replace_term_context_at[OF par]
      using possc_subt_at_ctxt_apply[OF possc par, of "r \<cdot> \<sigma>" "l \<cdot> \<sigma>"] rule
      by auto (metis par par_pos_replace_pres replace_at_hole_pos) 
    then show ?thesis by blast
  next
    case below
    then obtain q where [simp]:"p = hole_pos C @ q" and poss: "q \<in> poss (l \<cdot> \<sigma>)"
      using const position_less_eq_def
      by (metis (full_types) ctxt_at_pos_hole_pos ctxt_at_pos_subt_at_pos poss_append_poss t(1))
    have const: "l \<cdot> \<sigma> |_ q = constT c" using const by auto
    from nt_lhs have "\<exists> r. r \<in> varposs l \<and> r \<le>\<^sub>p q" using const poss
    proof (induct l arbitrary: q)
      case (Var x)
      then show ?case by auto
    next
      case (Fun f ts)
      from Fun(1)[OF nth_mem, of "hd q" "tl q"] Fun(2-) obtain r where
        "r \<in> varposs (ts ! hd q) \<and> r \<le>\<^sub>p tl q"
        by (cases q) auto
      then show ?case using Fun(2- 4)
        by (intro exI[of _ "hd q # r"]) auto
    qed
    then obtain x v where varposs: "v \<in> varposs l" "v \<le>\<^sub>p q" "l |_ v = Var x"
      unfolding varposs_def by blast
    let ?\<tau> = "\<lambda>x. if Var x = l |_ v then (\<sigma> x)[q -\<^sub>p v \<leftarrow> u] else \<sigma> x"
    show ?thesis
    proof (cases "x \<in> vars_term r")
      case True
      then obtain q' where varposs_r: "q' \<in> varposs r" "r |_ q' = Var x"
        by (metis vars_term_varposs_iff)
      have "(s[p \<leftarrow> u], t[(hole_pos C) @ q' @ (q -\<^sub>p v) \<leftarrow> u]) \<in> rstep \<R>"
        using lin varposs rule varposs_r
        by (auto simp: linear_term_varposs_subst_replace_term intro!: rstep_ctxtI)
          (smt (verit, ccfv_SIG) pos_diff_append_itself rrstep.intros rrstep_rstep_mono subset_eq term_subst_eq)
      moreover have "(hole_pos C) @ q' @ q -\<^sub>p v \<in> poss_of_term (constT c) t"
        using varposs_r varposs poss const poss_pos_diffI[OF varposs(2) poss]
        using subt_at_append_dist[of q' "q -\<^sub>p v" "r \<cdot> \<sigma>"]
        by (auto simp: poss_append_poss varposs_imp_poss[THEN subst_subt_at_dist] varposs_imp_poss[THEN subsetD[OF subst_poss_mono]])
          (metis pos_les_eq_append_diff eval_term.simps(1) subst_subt_at_dist subt_at_append_dist varposs_imp_poss)
      ultimately show ?thesis by auto
    next
      case False
      then have [simp]: "r \<cdot> \<sigma> = r \<cdot> ?\<tau>" using varposs
        by (auto simp add: term_subst_eq_conv)
      have "(s[p \<leftarrow> u], t) \<in> rstep \<R>" using rule varposs lin
        by (auto simp: linear_term_varposs_subst_replace_term)
      then show ?thesis by auto
    qed
  qed
qed

lemma fresh_const_steps_replace:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and occ: "p \<in> poss_of_term (constT c) s" and steps: "(s, t) \<in> (rstep \<R>)\<^sup>+"
  shows "(s[p \<leftarrow> u], t) \<in> (rstep \<R>)\<^sup>+ \<or>
    (\<exists> q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> (rstep \<R>)\<^sup>+)"
  using steps occ
proof (induct arbitrary: p rule: converse_trancl_induct)
  case (base s)
  from fresh_const_single_step_replace[OF lin fresh base(2, 1)] show ?case
    by (meson r_into_trancl')
next
  case (step s t)
  from fresh_const_single_step_replace[OF lin fresh step(4, 1)]
  consider (a) "(s[p \<leftarrow> u], t) \<in> rstep \<R>" | (b) "\<exists>q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> rstep \<R>" by blast
  then show ?case
  proof cases
    case a then show ?thesis using step(2)
      by auto
  next
    case b
    then obtain q where "q \<in> poss_of_term (constT c) t" "(s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> rstep \<R>" by blast
    from step(3)[OF this(1)] this(2) show ?thesis
      by (metis trancl_into_trancl2)
  qed
qed

lemma remove_const_lhs_steps:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term t"
    and pos: "p \<in> poss_of_term (constT c) s" 
    and steps: "(s, t) \<in> (rstep \<R>)\<^sup>+"
  shows "(s[p \<leftarrow> u], t) \<in> (rstep \<R>)\<^sup>+" using steps pos const fresh_const_steps_replace
  by (metis fresh funas_term_const_subst_conv lin poss_of_termE subt_at_imp_supteq)


text \<open>Now we can show that we may remove a constant substitution\<close>

definition const_replace_closed where
  "const_replace_closed c U = (\<forall> s t u p.
    p \<in> poss_of_term (constT c) s \<longrightarrow> (s, t) \<in> U \<longrightarrow>
    (\<exists> q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U) \<or> (s[p \<leftarrow> u], t) \<in> U)"

lemma const_replace_closedD:
  assumes "const_replace_closed c U" "p \<in> poss_of_term (constT c) s" "(s, t) \<in> U"
  shows "(s[p \<leftarrow> u], t) \<in> U \<or> (\<exists> q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U)" using assms
  unfolding const_replace_closed_def by blast

lemma const_replace_closedI:
  assumes "\<And> s t u p. p \<in> poss_of_term (constT c) s \<Longrightarrow> (s, t) \<in> U \<Longrightarrow>
       (\<exists> q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U) \<or> (s[p \<leftarrow> u], t) \<in> U"
  shows "const_replace_closed c U" using assms
  unfolding const_replace_closed_def
  by auto

abbreviation const_subst :: "'f \<Rightarrow> 'v \<Rightarrow> ('f, 'v) Term.term" where
  "const_subst c \<equiv> (\<lambda> x. Fun c [])"

lemma lin_fresh_rstep_const_replace_closed:
  "linear_sys \<R> \<Longrightarrow> (c, 0) \<notin> funas_rel \<R> \<Longrightarrow> const_replace_closed c (rstep \<R>)"
  using fresh_const_single_step_replace[of \<R> c]
  by (intro const_replace_closedI) (auto simp: constT_nfunas_term_poss_of_term_empty, blast)

lemma const_replace_closed_symcl:
  "const_replace_closed c U \<Longrightarrow> const_replace_closed c (U\<^sup>=)"
  unfolding const_replace_closed_def
  by (metis Un_iff pair_in_Id_conv)

lemma const_replace_closed_trancl:
  "const_replace_closed c U \<Longrightarrow> const_replace_closed c (U\<^sup>+)"
proof (intro const_replace_closedI)
  fix s t u p
  assume const: "const_replace_closed c U" and wit: "p \<in> poss_of_term (constT c) s"
    and steps :"(s, t) \<in> U\<^sup>+"
  show "(\<exists>q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U\<^sup>+) \<or> (s[p \<leftarrow> u], t) \<in> U\<^sup>+" using steps wit
  proof (induct arbitrary: p rule: converse_trancl_induct)
    case (base s)
    show ?case using const_replace_closedD[OF const base(2, 1)]
      by blast
  next
    case (step s v)
    from const_replace_closedD[OF const step(4, 1)]
    consider (a) "(s[p \<leftarrow> u], v) \<in> U" | (b) "\<exists> q. q \<in> poss_of_term (constT c) v \<and> (s[p \<leftarrow> u], v[q \<leftarrow> u]) \<in> U" by auto
    then show ?case
    proof cases
      case a then show ?thesis using step(2)
        by (meson trancl_into_trancl2)
    next
      case b
      then show ?thesis using step(3, 4) by (meson trancl_into_trancl2) 
    qed
  qed
qed

lemma const_replace_closed_rtrancl:
  "const_replace_closed c U \<Longrightarrow> const_replace_closed c (U\<^sup>*)"
proof (intro const_replace_closedI)
  fix s t u p
  assume const: "const_replace_closed c U" and wit: "p \<in> poss_of_term (constT c) s"
    and steps :"(s, t) \<in> U\<^sup>*"
  show "(\<exists>q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U\<^sup>*) \<or> (s[p \<leftarrow> u], t) \<in> U\<^sup>*"
    using const_replace_closed_trancl[OF const] wit steps
    by (metis const_replace_closedD rtrancl_eq_or_trancl)
qed

lemma const_replace_closed_relcomp:
  "const_replace_closed c U \<Longrightarrow> const_replace_closed c V \<Longrightarrow> const_replace_closed c (U O V)"
proof (intro const_replace_closedI)
  fix s t u p
  assume const: "const_replace_closed c U" "const_replace_closed c V"
   and wit: "p \<in> poss_of_term (constT c) s" and step: "(s, t) \<in> U O V"
  from step obtain w where w: "(s, w) \<in> U" "(w, t) \<in> V" by auto
  from const_replace_closedD[OF const(1) wit this(1)]
  consider (a) "(s[p \<leftarrow> u], w) \<in> U" | (b) "(\<exists>q. q \<in> poss_of_term (constT c) w \<and> (s[p \<leftarrow> u], w[q \<leftarrow> u]) \<in> U)"
    by auto  
  then show "(\<exists>q. q \<in> poss_of_term (constT c) t \<and> (s[p \<leftarrow> u], t[q \<leftarrow> u]) \<in> U O V) \<or> (s[p \<leftarrow> u], t) \<in> U O V"
  proof cases
    case a
    then show ?thesis using w(2) by auto
  next
    case b
    then show ?thesis using const_replace_closedD[OF const(2) _ w(2)]
      by (meson relcomp.simps)
  qed
qed


text \<open>@{const const_replace_closed} allow the removal of a fresh constant substitution\<close>
lemma const_replace_closed_remove_subst_lhs:
  assumes repcl: "const_replace_closed c U"
    and const: "(c, 0) \<notin> funas_term t"
    and steps: "(s \<cdot> const_subst c, t) \<in> U"
  shows "(s, t) \<in> U" using steps
proof (induct "card (varposs s)" arbitrary: s)
  case (Suc n)
  obtain p ps where vl: "varposs s = insert p ps" "p \<notin> ps" using Suc(2)
    by (metis card_le_Suc_iff dual_order.refl)
  let ?s = "s[p \<leftarrow> Fun c []]" have vp: "p \<in> varposs s" using vl by auto
  then have [simp]: "?s \<cdot> const_subst c = s \<cdot> const_subst c"
    by (induct s arbitrary: p) (auto simp: nth_list_update map_update intro!: nth_equalityI)
  have "varposs ?s = ps" using vl varposs_ground_replace_at[of p s "constT c"]
    by auto
  then have "n = card (varposs ?s)" using vl Suc(2) by (auto simp: card_insert_if finite_varposs)
  from Suc(1)[OF this] have IH: "(s[p \<leftarrow> constT c], t) \<in> U" "p \<in> poss_of_term (constT c) s[p \<leftarrow> constT c]"
    using Suc(2, 3) vl poss_of_term_replace_term_at varposs_imp_poss vp
    using \<open>s[p \<leftarrow> constT c] \<cdot> const_subst c = s \<cdot> const_subst c\<close>
    by fastforce+
  show ?case using const_replace_closedD[OF repcl] const IH(2, 1)
    by (metis constT_nfunas_term_poss_of_term_empty empty_iff replace_term_at_same_pos replace_term_at_subt_at_id)
qed (auto simp: ground_subst_apply card_eq_0_iff finite_varposs varposs_empty_gound)


subsubsection \<open>Removal lemma applied to various rewrite relations\<close>

lemma remove_const_subst_step_lhs:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term t"
    and step: "(s \<cdot> const_subst c, t) \<in> (rstep \<R>)"
  shows "(s, t) \<in> (rstep \<R>)"
  using lin_fresh_rstep_const_replace_closed[OF lin fresh, THEN const_replace_closed_remove_subst_lhs] const step
  by blast

lemma remove_const_subst_steps_lhs:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term t"
    and steps: "(s \<cdot> const_subst c, t) \<in> (rstep \<R>)\<^sup>+"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>+"
  using lin_fresh_rstep_const_replace_closed[THEN const_replace_closed_trancl,
    OF lin fresh, THEN const_replace_closed_remove_subst_lhs]
  using const steps
  by blast

lemma remove_const_subst_steps_eq_lhs:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term t"
    and steps: "(s \<cdot> const_subst c, t) \<in> (rstep \<R>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>*" using steps const 
  by (cases "s = t") (auto simp: rtrancl_eq_or_trancl funas_term_subst ground_subst_apply vars_term_empty_ground
      dest: remove_const_subst_steps_lhs[OF lin fresh const] split: if_splits)

lemma remove_const_subst_steps_rhs:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term s"
    and steps: "(s, t \<cdot> const_subst c) \<in> (rstep \<R>)\<^sup>+"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>+"
proof -
  from steps have revs: "(t \<cdot> const_subst c, s) \<in> (rstep (\<R>\<inverse>))\<^sup>+"
    unfolding rew_converse_outwards by auto
  have "(t, s) \<in> (rstep (\<R>\<inverse>))\<^sup>+" using assms
    by (intro remove_const_subst_steps_lhs[OF _ _ _ revs]) (auto simp: funas_rel_def)
  then show ?thesis unfolding rew_converse_outwards by auto
qed

lemma remove_const_subst_steps_eq_rhs:
  assumes lin: "linear_sys \<R>" and fresh: "(c, 0) \<notin> funas_rel \<R>"
    and const: "(c, 0) \<notin> funas_term s"
    and steps: "(s, t \<cdot> const_subst c) \<in> (rstep \<R>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>*"
  using steps const
  by (cases "s = t") (auto simp: rtrancl_eq_or_trancl funas_term_subst ground_subst_apply vars_term_empty_ground
      dest!: remove_const_subst_steps_rhs[OF lin fresh const] split: if_splits)


text \<open>Main lemmas\<close>
lemma const_subst_eq_ground_eq:
  assumes "s \<cdot> const_subst c = t \<cdot> const_subst d" "c \<noteq> d"
    and "(c, 0) \<notin> funas_term t" "(d, 0) \<notin> funas_term s"
  shows "s = t" using assms
proof (induct s arbitrary: t)
  case (Var x) then show ?case by (cases t) auto
next
  case (Fun f ts)
  from Fun(2-) obtain g us where [simp]: "t = Fun g us" by (cases t) auto
  have [simp]: "g = f" and l: "length ts = length us" using Fun(2)
    by (auto intro: map_eq_imp_length_eq)
  have "i < length ts \<Longrightarrow> ts ! i = us ! i" for i
    using Fun(1)[OF nth_mem, of i "us ! i" for i] Fun(2-) l
    by (auto simp: map_eq_conv')
  then show ?case using l
    by (auto intro: nth_equalityI)
qed


lemma remove_const_subst_steps:
  assumes "linear_sys \<R>" and  "(c, 0) \<notin> funas_rel \<R>" and "(d, 0) \<notin> funas_rel \<R>"
    and "c \<noteq> d" "(c, 0) \<notin> funas_term t" "(d, 0) \<notin> funas_term s"
    and "(s \<cdot> const_subst c, t \<cdot> const_subst d) \<in> (rstep \<R>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>*"
proof (cases "s \<cdot> const_subst c = t \<cdot> const_subst d")
  case True
  from const_subst_eq_ground_eq[OF this] assms(4 - 6) show ?thesis by auto
next
  case False
  then have step: "(s \<cdot> const_subst c, t \<cdot> const_subst d) \<in> (rstep \<R>)\<^sup>+" using assms(7)
    by (auto simp: rtrancl_eq_or_trancl)
  then have "(s, t \<cdot> const_subst d) \<in> (rstep \<R>)\<^sup>+" using assms
    by (intro remove_const_subst_steps_lhs[OF _ _ _ step]) (auto simp: funas_term_subst)
  from remove_const_subst_steps_rhs[OF _ _ _ this] show ?thesis using assms
    by auto
qed

lemma remove_const_subst_relcomp_lhs:
  assumes sys: "linear_sys \<R>" "linear_sys \<S>"
    and fr: "(c, 0) \<notin> funas_rel \<R>" and fs:"(c, 0) \<notin> funas_rel \<S>"
    and funas: "(c, 0) \<notin> funas_term t"
    and seq: "(s \<cdot> const_subst c, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*" using seq
  using lin_fresh_rstep_const_replace_closed[OF sys(1) fr, THEN const_replace_closed_rtrancl]
  using lin_fresh_rstep_const_replace_closed[OF sys(2) fs, THEN const_replace_closed_rtrancl]
  using const_replace_closed_relcomp
  by (intro const_replace_closed_remove_subst_lhs[OF _ funas seq]) force

lemma remove_const_subst_relcomp_rhs:
  assumes sys: "linear_sys \<R>" "linear_sys \<S>"
    and fr: "(c, 0) \<notin> funas_rel \<R>" and fs:"(c, 0) \<notin> funas_rel \<S>"
    and funas: "(c, 0) \<notin> funas_term s"
    and seq: "(s, t \<cdot> const_subst c) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
proof -
  from seq have "(t \<cdot> const_subst c,s) \<in> ((rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*)\<inverse>"
    by auto
  then have "(t \<cdot> const_subst c,s) \<in> ((rstep \<S>)\<^sup>*)\<inverse> O ((rstep \<R>)\<^sup>*)\<inverse>"
    using converse_relcomp by blast
  note seq = this[unfolded rtrancl_converse[symmetric] rew_converse_inwards]
  from sys fr fs have "linear_sys (\<S>\<inverse>)" "linear_sys (\<R>\<inverse>)" "(c, 0) \<notin> funas_rel (\<S>\<inverse>)" "(c, 0) \<notin> funas_rel (\<R>\<inverse>)"
    by (auto simp: funas_rel_def)
  from remove_const_subst_relcomp_lhs[OF this funas seq]
  have "(t, s) \<in> (rstep (\<S>\<inverse>))\<^sup>* O (rstep (\<R>\<inverse>))\<^sup>*" by simp
  then show ?thesis
    unfolding rew_converse_outwards converse_relcomp[symmetric]
    by simp
qed


lemma remove_const_subst_relcomp:
  assumes sys: "linear_sys \<R>" "linear_sys \<S>"
    and fr: "(c, 0) \<notin> funas_rel \<R>" "(d, 0) \<notin> funas_rel \<R>"
    and fs:"(c, 0) \<notin> funas_rel \<S>" "(d, 0) \<notin> funas_rel \<S>"
    and diff: "c \<noteq> d" and funas: "(c, 0) \<notin> funas_term t" "(d, 0) \<notin> funas_term s"
    and seq: "(s \<cdot> const_subst c, t \<cdot> const_subst d) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
  shows "(s, t) \<in> (rstep \<R>)\<^sup>* O (rstep \<S>)\<^sup>*"
proof -
  from diff funas(1) have *: "(c, 0) \<notin> funas_term (t \<cdot> const_subst d)"
    by (auto simp: funas_term_subst)
  show ?thesis using remove_const_subst_relcomp_rhs[OF sys fr(2) fs(2) funas(2)
        remove_const_subst_relcomp_lhs[OF sys fr(1) fs(1) * seq]]
    by blast
qed

end