section \<open>Preliminaries\<close>
theory Terms_Positions
  imports 
    Regular_Tree_Relations.Ground_Terms
    First_Order_Rewriting.Trs
begin
subsection \<open>Additional operations on terms and positions\<close>

subsubsection \<open>Linearity\<close>
abbreviation "linear_sys \<R> \<equiv> \<forall> (l, r) \<in> \<R>. linear_term l \<and> linear_term r"

subsubsection \<open>Positions by given subterms\<close>
definition "poss_of_term u t = {p. p \<in> poss t \<and> t |_ p = u}"

lemma var_poss_def: "var_poss s = {p | p. p \<in> poss s \<and> is_Var (s |_ p)}" 
  by (induct s, auto)


subsubsection \<open>Replacing functions symbols that aren't specified in the signature by variables\<close>

abbreviation "funas_rel \<equiv> funas_trs" 

lemma funas_rel_def: "funas_rel \<R> = (\<Union> (l, r) \<in> \<R>. funas_term l \<union> funas_term r)"
  unfolding funas_trs_def funas_rule_def by auto

fun term_to_sig where
  "term_to_sig \<F> v (Var x) = Var x"
| "term_to_sig \<F> v (Fun f ts) =
    (if (f, length ts) \<in> \<F> then Fun f (map (term_to_sig \<F> v) ts) else Var v)"

fun ctxt_well_def_hole_path where
  "ctxt_well_def_hole_path \<F> Hole \<longleftrightarrow> True"
| "ctxt_well_def_hole_path \<F> (More f ss C ts) \<longleftrightarrow> (f, Suc (length ss + length ts)) \<in> \<F> \<and> ctxt_well_def_hole_path \<F> C"

fun inv_const_ctxt where
  "inv_const_ctxt \<F> v Hole = Hole"
| "inv_const_ctxt \<F> v ((More f ss C ts)) 
              = (More f (map (term_to_sig \<F> v) ss) (inv_const_ctxt \<F> v C) (map (term_to_sig \<F> v) ts))"

fun inv_const_ctxt' where
  "inv_const_ctxt' \<F> v Hole = Var v"
| "inv_const_ctxt' \<F> v ((More f ss C ts)) 
              = (if (f, Suc (length ss + length ts)) \<in> \<F> then Fun f (map (term_to_sig \<F> v) ss @ inv_const_ctxt' \<F> v C # map (term_to_sig \<F> v) ts) else Var v)"


subsubsection \<open>Replace term at a given position in contexts\<close>

fun replace_term_context_at :: "('f, 'v) ctxt \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ctxt"
  (\<open>_[_ \<leftarrow> _]\<^sub>C\<close> [1000, 0] 1000) where
  "replace_term_context_at \<box> p u = \<box>"
| "replace_term_context_at (More f ss C ts) (i # ps) u =
    (if i < length ss then More f (ss[i := (ss ! i)[ps \<leftarrow> u]]) C ts
     else if i = length ss then More f ss (replace_term_context_at C ps u) ts
     else More f ss C (ts[(i - Suc (length ss)) := (ts ! (i - Suc (length ss)))[ps \<leftarrow> u]]))"

abbreviation "constT c \<equiv> Fun c []"


subsection \<open>Lemmas for @{const poss} and ordering of positions\<close>

lemma subst_poss_mono: "poss s \<subseteq> poss (s \<cdot> \<sigma>)"
  by (induct s) force+

lemmas par_pos_prefix [simp] = Sublist.parallel_cancel

lemma pos_diff_itself [simp]: "p -\<^sub>p p = []"
  by (simp add: pos_diff_def)

lemma pos_diff_append_itself [simp]: "(p @ q) -\<^sub>p p = q"
  by (simp add: pos_diff_def)

lemma poss_pos_diffI:
  "p \<le>\<^sub>p q \<Longrightarrow> q \<in> poss s \<Longrightarrow> q -\<^sub>p p \<in> poss (s |_ p)"
  using poss_append_poss by fastforce

declare hole_pos_poss_conv[simp]

lemma pos_replace_at_pres:
  "p \<in> poss s \<Longrightarrow> p \<in> poss s[p \<leftarrow> t]"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    by (cases s) auto
qed auto

lemma par_pos_replace_pres:
  "p \<in> poss s \<Longrightarrow> p \<bottom> q \<Longrightarrow> p \<in> poss s[q \<leftarrow> t]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) (auto simp add: nth_list_update)
qed auto

lemma poss_of_termE [elim]:
  assumes "p \<in> poss_of_term u s"
    and "p \<in> poss s \<Longrightarrow> s |_ p = u \<Longrightarrow> P"
  shows "P" using assms unfolding poss_of_term_def
  by blast

lemma poss_of_term_Cons:
  "i # p \<in> poss_of_term u (Fun f ts) \<Longrightarrow> p \<in> poss_of_term u (ts ! i)"
  unfolding poss_of_term_def by auto

lemma poss_of_term_const_ctxt_apply:
  assumes "p \<in> poss_of_term (constT c) C\<langle>s\<rangle>"
  shows "p \<bottom> (hole_pos C) \<or> (hole_pos C) \<le>\<^sub>p p" using assms
proof (induct p arbitrary: C)
  case Nil then show ?case
    by (cases C) auto
next
  case (Cons i p) then show ?case
    by (cases C) (fastforce dest!: poss_of_term_Cons)+
qed


subsection \<open>Lemmas for @{const subt_at} and @{const replace_term_at}\<close>

lemma subt_at_append_dist:
  "p @ q \<in> poss s \<Longrightarrow> s |_ (p @ q) = (s |_ p) |_ q" 
  by simp

lemma ctxt_apply_term_subt_at_hole_pos [simp]:
  "C\<langle>s\<rangle> |_ (hole_pos C @ q) = s |_ q" by simp

lemma replace_term_at_subt_at_id [simp]: "s[p \<leftarrow> (s |_ p)] = s"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) auto
qed auto


lemma replace_term_at_same_pos [simp]:
  "s[p \<leftarrow> u][p \<leftarrow> t] = s[p \<leftarrow> t]"
  using replace_term_at_above by blast

\<comment> \<open>Replacement at under substitution\<close>
lemma subt_at_vars_term:
  "p \<in> poss s \<Longrightarrow> s |_ p = Var x \<Longrightarrow> x \<in> vars_term s"
  by (metis var_poss_iff vars_term_var_poss_iff)

lemma linear_term_var_poss_subst_replace_term:
  "linear_term s \<Longrightarrow> p \<in> var_poss s \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow>
     (s \<cdot> \<sigma>)[q \<leftarrow> u] = s \<cdot> (\<lambda> x. if Var x = s |_ p then (\<sigma> x)[q -\<^sub>p p \<leftarrow> u] else (\<sigma> x))"
proof (induct q arbitrary: s p)
  case (Cons i q)
  show ?case using Cons(1)[of "args s ! i" "tl p"] Cons(2-)
    by (cases s) (auto simp: var_poss_def nth_list_update term_subst_eq_conv
      is_partition_alt is_partition_alt_def disjoint_iff subt_at_vars_term intro!: nth_equalityI)
qed (auto simp: var_poss_def)

\<comment> \<open>Replacement at context parallel to the hole position\<close>
lemma par_hole_pos_replace_term_context_at:
  "p \<bottom> hole_pos C \<Longrightarrow> C\<langle>s\<rangle>[p \<leftarrow> u] = (C[p \<leftarrow> u]\<^sub>C)\<langle>s\<rangle>"
proof (induct p arbitrary: C)
  case (Cons i p)
  from Cons(2) obtain f ss D ts where [simp]: "C = More f ss D ts" by (cases C) auto 
  show ?case using Cons(1)[of D] Cons(2)
    by (auto simp: list_update_beyond list_update_append nth_append_Cons minus_nat.simps(2) split: nat.splits)
qed auto

lemma par_pos_replace_term_at:
  "p \<in> poss s \<Longrightarrow> p \<bottom> q \<Longrightarrow> s[q \<leftarrow> t] |_ p = s |_ p"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    apply (cases s; cases q)
       apply simp_all
    by (metis nth_list_update_eq nth_list_update_neq par_pos_prefix)
qed auto


lemma less_eq_subt_at_replace:
  "p \<in> poss s \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow> s[q \<leftarrow> t] |_ p = (s |_ p)[q -\<^sub>p p \<leftarrow> t]"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) auto
qed auto


lemma greater_eq_subt_at_replace:
  "p \<in> poss s \<Longrightarrow> q \<le>\<^sub>p p \<Longrightarrow> s[q \<leftarrow> t] |_ p = t |_ (p -\<^sub>p q)"
proof (induct p arbitrary: s q)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i" "tl q"] Cons(2-)
    by (cases s; cases q) auto
qed auto

lemma replace_subterm_at_itself [simp]:
  "s[p \<leftarrow> (s |_ p)[q \<leftarrow> t]] = s[p @ q \<leftarrow> t]"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"]
    by (cases s) auto
qed auto


lemma hole_pos_replace_term_at [simp]:
  "hole_pos C \<le>\<^sub>p p \<Longrightarrow> C\<langle>s\<rangle>[p \<leftarrow> u] = C\<langle>s[p -\<^sub>p hole_pos C \<leftarrow> u]\<rangle>"
proof (induct C arbitrary: p)
  case (More f ss C ts) then show ?case
    by (cases p) auto
qed auto

lemmas ctxt_of_pos_term_apply_replace_at_ident = replace_term_at_replace_at_conv

lemma ctxt_apply_term_replace_term_hole_pos [simp]:
  "C\<langle>s\<rangle>[hole_pos C @ q  \<leftarrow> u] = C\<langle>s[q  \<leftarrow> u]\<rangle>"
  by (simp add: pos_diff_def)


subsection \<open>@{const term_to_sig} invariants and distributions\<close>

lemma fuans_term_term_to_sig [simp]: "funas_term (term_to_sig \<F> v t) \<subseteq> \<F>"
  by (induct t) auto

lemma term_to_sig_id [simp]:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> term_to_sig \<F> v t = t"
  by (induct t) (auto simp add: UN_subset_iff map_idI)

lemma term_to_sig_subst_sig [simp]:
  "funas_term t \<subseteq> \<F> \<Longrightarrow> term_to_sig \<F> v (t \<cdot> \<sigma>) = t \<cdot> (\<lambda> x.  term_to_sig \<F> v (\<sigma> x))"
  by (induct t) auto

lemma funas_ctxt_ctxt_inv_const_ctxt_ind [simp]:
  "funas_ctxt C \<subseteq> \<F> \<Longrightarrow> inv_const_ctxt \<F> v C = C"
  by (induct C) (auto simp add: UN_subset_iff intro!: nth_equalityI)

lemma term_to_sig_ctxt_apply [simp]:
  "ctxt_well_def_hole_path \<F> C \<Longrightarrow> term_to_sig \<F> v C\<langle>s\<rangle> = (inv_const_ctxt \<F> v C)\<langle>term_to_sig \<F> v s\<rangle>"
  by (induct C) auto

lemma term_to_sig_ctxt_apply' [simp]:
  "\<not> ctxt_well_def_hole_path \<F> C \<Longrightarrow> term_to_sig \<F> v C\<langle>s\<rangle> = inv_const_ctxt' \<F> v C"
  by (induct C) auto

lemma funas_ctxt_ctxt_well_def_hole_path:
  "funas_ctxt C \<subseteq> \<F> \<Longrightarrow> ctxt_well_def_hole_path \<F> C"
  by (induct C) auto


subsection \<open>Misc\<close>

lemma funas_term_subt_at:
  "(f, n) \<in> funas_term t \<Longrightarrow> (\<exists> p ts. p \<in> poss t \<and> t |_ p = Fun f ts \<and> length ts = n)"
  unfolding funas_term_poss_conv by force

declare ground_substI[intro, simp]
lemma ground_ctxt_substI:
  "(\<And> x. x \<in> vars_ctxt C \<Longrightarrow> ground (\<sigma> x)) \<Longrightarrow> ground_ctxt (C \<cdot>\<^sub>c \<sigma>)"
  by (induct C) auto

lemma var_poss_Fun[simp]:
  "var_poss (Fun f ts) = { i # p| i p. i < length ts \<and> p \<in> var_poss (ts ! i)}"
  by auto

lemma vars_term_empty_ground:
  "vars_term s = {} \<Longrightarrow> ground s"
  unfolding ground_vars_term_empty .

lemma var_poss_empty_gound:
 "var_poss s = {} \<longleftrightarrow> ground s"
  by (induct s) (fastforce simp: in_set_conv_nth)+

lemma funas_term_subterm_atI [intro]:
  "p \<in> poss s \<Longrightarrow> funas_term s \<subseteq> \<F> \<Longrightarrow> funas_term (s |_ p) \<subseteq> \<F>"
  by (meson subset_trans subt_at_imp_supteq' supteq_imp_funas_term_subset)

lemma var_poss_ground_replace_at:
  "p \<in> var_poss s \<Longrightarrow> ground u \<Longrightarrow> var_poss s[p \<leftarrow> u] = var_poss s - {p}"
proof (induct p arbitrary: s)
  case Nil then show ?case
    by (cases s) (auto simp: var_poss_empty_gound)
next
  case (Cons i p)
  from Cons(2) obtain f ts where [simp]: "s = Fun f ts" by (cases s) auto
  from Cons(2) have var: "p \<in> var_poss (ts ! i)" by auto
  from Cons(1)[OF var Cons(3)] have "j < length ts \<Longrightarrow> {j # q| q. q \<in> var_poss (ts[i := (ts ! i)[p \<leftarrow> u]] ! j)} =
           {j # q |q. q \<in> var_poss (ts ! j)} - {i # p}" for j
    by (cases "j = i") (auto simp add: nth_list_update)
  then show ?case by auto 
qed

lemma funas_term_replace_at_upper:
  "funas_term s[p \<leftarrow> t] \<subseteq> funas_term s \<union> funas_term t"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"]
    by (cases s) (fastforce simp: in_set_conv_nth nth_list_update split!: if_splits)+
qed simp

lemma funas_term_replace_at_lower:
  "p \<in> poss s \<Longrightarrow> funas_term t \<subseteq> funas_term (s[p \<leftarrow> t])"
proof (induct p arbitrary: s)
  case (Cons i p)
  show ?case using Cons(1)[of "args s ! i"] Cons(2-)
    by (cases s) (fastforce simp: in_set_conv_nth nth_list_update split!: if_splits)+
qed simp

lemma poss_of_term_possI [intro!]:
  "p \<in> poss s \<Longrightarrow> s |_ p = u \<Longrightarrow> p \<in> poss_of_term u s"
  unfolding poss_of_term_def by blast

lemma poss_of_term_replace_term_at:
  "p \<in> poss s \<Longrightarrow> p \<in> poss_of_term u s[p \<leftarrow> u]"
proof (induct p arbitrary: s)
  case (Cons i p) then show ?case
    by (cases s) (auto simp: poss_of_term_def)
qed auto

lemma constT_nfunas_term_poss_of_term_empty:
  "(c, 0) \<notin> funas_term t \<longleftrightarrow> poss_of_term (constT c) t = {}"
  unfolding poss_of_term_def
  using funas_term_subt_at[of c 0 t]
  using funas_term_subterm_atI[where ?\<F> ="funas_term t" and ?s = t, THEN subsetD]
  by auto

lemma poss_of_term_poss_emptyD:
  assumes "poss_of_term u s = {}"
  shows "p \<in> poss s \<Longrightarrow> s |_ p \<noteq> u" using assms
  unfolding poss_of_term_def by blast

lemma possc_subt_at_ctxt_apply:
  "p \<in> possc C \<Longrightarrow> p \<bottom> hole_pos C \<Longrightarrow> C\<langle>s\<rangle> |_ p = C\<langle>t\<rangle> |_ p"
  by (metis par_pos_replace_term_at poss_imp_possc replace_at_hole_pos)

end